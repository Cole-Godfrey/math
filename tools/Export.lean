import Lean
import LeanExport.Basic

open Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-
the exporter reads kernel declarations, including private imported proof bodies.
dependency lists include types, bodies, and inductive reduction data.
-/

private def obj := Json.mkObj
private def names (ns : Array Name) : Json := toJson (ns.map Name.toString)
private def sorted (ns : Array Name) : Array Name :=
  (ns.foldl (fun s n => s.insert n) ({} : NameSet)).toArray.qsort Name.lt

private partial def levelJson : Level → Json
  | .zero => obj [("tag", toJson "zero")]
  | .succ l => obj [("tag", toJson "succ"), ("of", levelJson l)]
  | .max a b => obj [("tag", toJson "max"), ("left", levelJson a), ("right", levelJson b)]
  | .imax a b => obj [("tag", toJson "imax"), ("left", levelJson a), ("right", levelJson b)]
  | .param n => obj [("tag", toJson "param"), ("name", toJson n.toString)]
  | .mvar n => obj [("tag", toJson "mvar"), ("name", toJson n.name.toString)]

private def binderString : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance_implicit"

private structure ExpressionState where
  ids : ExprMap Nat := {}
  count : Nat := 0
  sink : IO.FS.Handle

private abbrev ExportM := StateRefT ExpressionState IO

/-- share logical subexpressions while retaining all binders and universe arguments. -/
private partial def internExpr (e : Expr) : ExportM Nat := do
  if let .mdata _ body := e then return ← internExpr body
  if let some id := (← get).ids[e]? then return id
  let node ← match e with
    | .bvar n => pure <| obj [("tag", toJson "bvar"), ("index", toJson n)]
    | .fvar n => pure <| obj [("tag", toJson "fvar"), ("name", toJson n.name.toString)]
    | .mvar n => pure <| obj [("tag", toJson "mvar"), ("name", toJson n.name.toString)]
    | .sort l => pure <| obj [("tag", toJson "sort"), ("level", levelJson l)]
    | .const n ls => pure <| obj [("tag", toJson "const"), ("name", toJson n.toString),
        ("levels", toJson (ls.map levelJson))]
    | .app f a => do
      let f ← internExpr f
      let a ← internExpr a
      pure <| obj [("tag", toJson "app"), ("function", toJson f), ("argument", toJson a)]
    | .lam n t b bi | .forallE n t b bi => do
      let t ← internExpr t
      let b ← internExpr b
      let tag := if e.isLambda then "lam" else "forall"
      pure <| obj [("tag", toJson tag), ("name", toJson n.toString),
        ("type", toJson t), ("body", toJson b), ("binder", toJson (binderString bi))]
    | .letE n t v b nondep => do
      let t ← internExpr t
      let v ← internExpr v
      let b ← internExpr b
      pure <| obj [("tag", toJson "let"), ("name", toJson n.toString),
        ("type", toJson t), ("value", toJson v), ("body", toJson b), ("nondependent", toJson nondep)]
    | .lit (.natVal n) => pure <| obj [("tag", toJson "nat"), ("value", toJson n)]
    | .lit (.strVal s) => pure <| obj [("tag", toJson "string"), ("value", toJson s)]
    | .proj n i body => do
      let body ← internExpr body
      pure <| obj [("tag", toJson "proj"), ("name", toJson n.toString),
        ("index", toJson i), ("expression", toJson body)]
    | .mdata _ _ => throw (IO.userError "unexpected expression metadata")
  let id := (← get).count
  let sink := (← get).sink
  if id != 0 then sink.putStr ","
  sink.putStr node.compress
  modify fun s => { s with ids := s.ids.insert e id, count := id + 1 }
  return id

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient_primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def definitionGroup : ConstantInfo → Array Name
  | .defnInfo value => value.all.toArray
  | .thmInfo value => value.all.toArray
  | .opaqueInfo value => value.all.toArray
  | _ => #[]

private def reducibility : ConstantInfo → Json
  | .defnInfo value => match value.hints with
    | .opaque => toJson "opaque"
    | .abbrev => toJson "abbrev"
    | .regular height => obj [("regular", toJson height.toNat)]
  | _ => Json.null

/-- preserve exact logical name components independently of their display strings. -/
private def nameData (env : Environment) (declarations : Array (Name × Json)) : IO Json := do
  let mut all : Array Name := #[]
  for (name, _) in declarations do
    let some info := env.checked.get.constants.find? name
      | throw (IO.userError s!"missing name data declaration: {name}")
    all := all ++ #[name] ++ info.levelParams.toArray ++ definitionGroup info
  let mut seen : Std.HashMap String Name := {}
  let mut result : List (String × Json) := []
  for name in sorted all do
    let text := name.toString
    if let some prior := seen[text]? then
      if prior != name then throw (IO.userError s!"ambiguous logical name display: {text}")
    seen := seen.insert text name
    let parts := name.components.map fun part => match part with
      | .str _ value => obj [("str", toJson value)]
      | .num _ value => obj [("num", toJson value)]
      | .anonymous => Json.null
    result := (text, toJson parts) :: result
  return obj result

private def structuralDeps : ConstantInfo → Array Name
  | .inductInfo v => (v.all ++ v.ctors).toArray
  | .ctorInfo v => #[v.induct]
  | .recInfo v => v.all.toArray ++ v.rules.toArray.flatMap
      (fun r => #[r.ctor] ++ r.rhs.getUsedConstants)
  | _ => #[]

private def structuralJson : ConstantInfo → ExportM Json
  | .inductInfo v => pure <| obj [("mutual", names v.all.toArray), ("constructors", names v.ctors.toArray),
      ("parameters", toJson v.numParams), ("indices", toJson v.numIndices),
      ("nested", toJson v.numNested), ("recursive", toJson v.isRec),
      ("reflexive", toJson v.isReflexive)]
  | .ctorInfo v => pure <| obj [("inductive", toJson v.induct.toString), ("index", toJson v.cidx),
      ("parameters", toJson v.numParams), ("fields", toJson v.numFields)]
  | .recInfo v => do
    let rules ← v.rules.mapM fun r => do
      let rhs ← internExpr r.rhs
      return obj [("constructor", toJson r.ctor.toString), ("fields", toJson r.nfields), ("rhs", toJson rhs)]
    return obj [("mutual", names v.all.toArray), ("parameters", toJson v.numParams),
      ("indices", toJson v.numIndices), ("motives", toJson v.numMotives),
      ("minors", toJson v.numMinors), ("k", toJson v.k),
      ("rules", toJson rules)]
  | .quotInfo v => pure <| obj [("primitive", toJson (match v.kind with
      | .type => "type" | .ctor => "constructor" | .lift => "lift" | .ind => "induction"))]
  | _ => pure Json.null

private def dependencies (info : ConstantInfo) : Array Name :=
  sorted (info.type.getUsedConstants ++
    (info.value? (allowOpaque := true)).toArray.flatMap Expr.getUsedConstants ++ structuralDeps info)

private def moduleName (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""

/-- retain serialized declarations even when another import owns the same name. -/
private def moduleInventories (env : Environment) (selected : Array Name) : IO (Array (Name × Array Name)) := do
  let constants := env.checked.get.constants
  let mut inventory : NameMap NameSet := {}
  for module in selected do
    inventory := inventory.insert module {}
  for h : i in [:env.header.modules.size] do
    let module := env.header.modules[i].module
    if let some members := inventory.find? module then
      let mut members := members
      for name in env.header.moduleData[i]!.constNames do
        if (constants.find? name).isNone then
          throw (IO.userError s!"missing serialized kernel declaration: {module}: {name}")
        members := members.insert name
      inventory := inventory.insert module members
  for (name, _) in constants do
    if let some index := env.getModuleIdxFor? name then
      let module := env.header.moduleNames[index.toNat]!
      if let some members := inventory.find? module then
        inventory := inventory.insert module (members.insert name)
  return (selected.qsort Name.lt).map fun module =>
    (module, sorted ((inventory.find? module).getD {}).toArray)

private def libraryModules (policy : Json) : Except String (Array Name) := do
  let some libraries := (policy.getObjVal? "libraries").toOption | return #[]
  let mut modules := #[]
  for (_, library) in (← libraries.getObj?).toArray do
    for (moduleName, _) in (← (← library.getObjVal? "modules").getObj?).toArray do
      let some name := Syntax.decodeNameLit ("`" ++ moduleName)
        | throw s!"invalid library module: {moduleName}"
      modules := modules.push name
  return sorted modules

private def declarationJson (env : Environment) (n : Name) (info : ConstantInfo)
    (axioms : NameSet) : ExportM Json := do
  let opts := ({} : Options).setBool `pp.fullNames true |>.setBool `pp.universes true
  let ctx : PPContext := { env := env, opts := opts }
  let statement ← ctx.runMetaM do return (← Meta.ppExpr info.type).pretty
  let proof ← (info.value? (allowOpaque := true)).mapM fun e =>
    ctx.runMetaM do return (← Meta.ppExpr e).pretty
  let doc ← findDocString? env n
  let cachedAxioms ← ctx.runCoreM (collectAxioms n)
  let ranges ← ctx.runCoreM (findDeclarationRanges? n)
  let source := ranges.map fun r => obj [
    ("line", toJson r.range.pos.line), ("column", toJson r.range.pos.column),
    ("end_line", toJson r.range.endPos.line), ("end_column", toJson r.range.endPos.column)]
  let type ← internExpr info.type
  let value ← (info.value? (allowOpaque := true)).mapM internExpr
  let structural ← structuralJson info
  return obj [
    ("name", toJson n.toString), ("kind", toJson (kind info)),
    ("module", toJson (moduleName env n)), ("doc", toJson doc), ("source", toJson source),
    ("universes", names info.levelParams.toArray), ("statement", toJson statement),
    ("type", toJson type), ("value", toJson value),
    ("proof", toJson proof), ("structure", structural),
    ("definition_group", names (definitionGroup info)), ("reducibility", reducibility info),
    ("unsafe", toJson info.isUnsafe),
    ("partial", toJson info.isPartial),
    ("meta", toJson (isMarkedMeta env n)),
    ("type_dependencies", names (sorted info.type.getUsedConstants)),
    ("value_dependencies", names (sorted ((info.value? (allowOpaque := true)).toArray.flatMap Expr.getUsedConstants))),
    ("structural_dependencies", names (sorted (structuralDeps info))),
    ("dependencies", names (dependencies info)), ("axioms", names (sorted axioms.toArray)),
    ("lean_axioms", names (sorted cachedAxioms))]

/-- recompute all axiom dependencies without imported summary caches. -/
private def freshAxiomClosure (entries : Array (Name × ConstantInfo)) : NameMap NameSet := Id.run do
  let mut result : NameMap NameSet := {}
  let mut parents : NameMap (Array Name) := {}
  let mut pending : Array Name := #[]
  for (name, info) in entries do
    let axioms := if info.isAxiom then ({} : NameSet).insert name else {}
    result := result.insert name axioms
    if info.isAxiom then pending := pending.push name
    for dependency in dependencies info do
      parents := parents.insert dependency (((parents.find? dependency).getD #[]).push name)
  let mut position := 0
  while position < pending.size do
    let name := pending[position]!
    position := position + 1
    let axioms := (result.find? name).getD {}
    for parent in (parents.find? name).getD #[] do
      let before := (result.find? parent).getD {}
      let after := axioms.toArray.foldl (fun acc ax => acc.insert ax) before
      if after.toArray.size != before.toArray.size then
        result := result.insert parent after
        pending := pending.push parent
  return result

private def exportDeclarations (env : Environment) (roots : Array Name) : ExportM (Array (Name × Json)) := do
  let constants := env.checked.get.constants
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut entries : Array (Name × ConstantInfo) := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := constants.find? n
      | throw (IO.userError s!"missing kernel declaration: {n}")
    entries := entries.push (n, info)
    pending := pending ++ dependencies info
  let axioms := freshAxiomClosure entries
  let mut declarations : Array (Name × Json) := #[]
  for (n, info) in entries do
    declarations := declarations.push (n, ← declarationJson env n info ((axioms.find? n).getD {}))
    if declarations.size % 1000 == 0 then
      IO.eprintln s!"exported {declarations.size} declarations"
  return declarations

/-- copy serialized expressions without retaining the whole array. -/
private def copyExpressions (input : System.FilePath) (output : IO.FS.Handle) : IO Unit :=
  IO.FS.withFile input .read fun source => do
    repeat
      let chunk ← source.read (64 * 1024)
      if chunk.isEmpty then break
      output.write chunk

private unsafe def exportIndex (output replay : String) (expressionPath : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let policy ← IO.ofExcept (Json.parse (← IO.FS.readFile "knowledge.json"))
  let libraries ← IO.ofExcept (libraryModules policy)
  let imports := #[{ module := `Math }] ++ libraries.map (fun n => { module := n : Import })
  let env ← importModules imports {} (loadExts := true) (level := .private)
  let constants := env.checked.get.constants
  let selected := env.header.moduleNames.filter fun module =>
    module == `Math || module.toString.startsWith "Math." || libraries.contains module
  let inventory ← moduleInventories env selected
  let candidates := sorted (inventory.flatMap (·.2))
  let isNonlogical := fun n => (constants.find? n).any (fun info => info.isPartial || info.isUnsafe)
  let nonlogical := candidates.filter isNonlogical
  for (module, members) in inventory do
    if module == `Math || module.toString.startsWith "Math." then
      for name in members do
        if isNonlogical name then
          let classification := if (constants.find? name).any ConstantInfo.isPartial then "partial"
            else "unsafe"
          throw (IO.userError s!"{name}: {classification} declarations are not allowed in project modules")
  let roots := candidates.filter (fun n => !isNonlogical n)
  if candidates.isEmpty then throw (IO.userError "no declarations found")
  IO.eprintln s!"exporting {roots.size} selected declarations"
  let declarations ← IO.FS.withFile expressionPath .write fun sink => do
    let (declarations, _) ← (exportDeclarations env roots).run { sink := sink }
    return declarations
  let logicalNames ← nameData env declarations
  let result := obj [
    ("schema_version", toJson (3 : Nat)), ("lean_version", toJson Lean.versionString),
    ("lean_revision", toJson Lean.githash),
    ("name_data", logicalNames),
    ("roots", names roots),
    ("module_declarations", names candidates),
    ("module_declarations_by_module", obj (inventory.toList.map fun (module, members) =>
      (module.toString, names members))),
    ("nonlogical_declarations", toJson (nonlogical.map fun n => obj [
      ("name", toJson n.toString), ("module", toJson (moduleName env n)),
      ("safety", toJson (if (constants.find? n).any ConstantInfo.isPartial then "partial"
        else if (constants.find? n).any ConstantInfo.isUnsafe then "unsafe" else "safe")),
      ("meta", toJson (isMarkedMeta env n)),
      ("reason", toJson (if isMarkedMeta env n then "metaprogram" else "runtime implementation outside the logic")) ])),
    ("modules", toJson (env.header.modules.mapIdx fun i m => obj [
      ("name", toJson m.module.toString),
      ("imports", names (env.header.moduleData[i]!.imports.map (·.module))),
      ("docs", toJson (((getModuleDoc? env m.module).getD #[]).map fun doc => obj [
        ("text", toJson doc.doc),
        ("line", toJson doc.declarationRange.pos.line),
        ("end_line", toJson doc.declarationRange.endPos.line)]))])),
    ("declarations", toJson ((declarations.qsort (fun a b => Name.lt a.1 b.1)).map Prod.snd))]
  IO.FS.withFile output .write fun handle => do
    handle.putStr "{\"expressions\":["
    copyExpressions expressionPath handle
    handle.putStr "],"
    handle.putStr (result.compress.drop 1).toString
    handle.putStr "\n"
  IO.FS.withFile replay .write fun handle =>
    IO.withStdout (.ofHandle handle) (LeanExport.dumpEnv env (some roots.toList))

/-- export the transitive closure of all declarations in project modules. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [output, replay] := args
    | throw (IO.userError "usage: lean --run tools/Export.lean INDEX REPLAY")
  let expressionPath : System.FilePath := output ++ ".expressions"
  try
    exportIndex output replay expressionPath
    return 0
  finally
    if ← expressionPath.pathExists then IO.FS.removeFile expressionPath
