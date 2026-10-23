# Native Metamath proofs

`metamath-lock.json` pins the mathematical sources and both native verifier implementations. Verification includes nine databases from that exact `set.mm` repository revision: `set.mm`, `iset.mm`, `nf.mm`, `hol.mm`, `ql.mm`, `peano.mm`, `miu.mm`, `demo0.mm`, and `big-unifier.mm`. Together they contain 71,837 proved statements and 4,571 `$a` rules.

Each database has its own namespace. For example, `metamath:set.mm:id` and `metamath:iset.mm:id` retain separate identities. The databases include classical and intuitionistic set theories, New Foundations, higher-order logic, quantum logic, and small formal systems. The actual assumptions of a result come from its retained rules and dependency closure. In particular, the main `set.mm` database contains additional axioms and mathboxes; membership in that file does not establish that a result uses only ZFC.

`$a` statements declare rules, including syntax rules and definitions. Their use remains explicit in each theorem's axiom closure. `$p` statements have checked proofs. Floating hypotheses, essential hypotheses, their order, and disjoint-variable restrictions remain in each assertion's frame. A proof with no `$a` dependencies can still depend on its stated local hypotheses. `peano.mm` at this revision declares 48 rules and no `$p` theorems.

## Verification

`make check` and `make verify` check the native databases before publishing the Lean snapshot. Native checking requires a C compiler and Rust 1.94.1:

```sh
rustup toolchain install 1.94.1 --profile minimal
make check
```

The original C Metamath verifier and the independent Rust `metamath-knife` implementation must accept every proof. The C process can return zero for a verification error, so acceptance also requires its explicit successful proof summary and no error lines. `metamath-knife` must report zero diagnostics, with one precisely recorded exception: `big-unifier.mm` has a documentation-marker warning at line 345, column 5. The warning is accepted only for the pinned source digest and that exact diagnostic; its original source and warning are retained.

The proof exporter instruments the pinned Rust verifier to retain each rule invocation, its ordered argument references, and the digest of its exact substituted expression. It retains compressed proof text, saved-step sharing, complete assertion frames, and every original source byte through ordered source spans.

An independent Python implementation parses and replays every original proof. It checks substitutions, hypothesis order and types, scoped hypothesis access, disjoint-variable conditions, and the final expression. It separately replays the exported proof DAG and requires the same derivation digest and rule dependencies as the original proof. Every reported source token, source line range, assertion frame, and final count is checked. Preloaded unused hypotheses in compressed proofs are checked against the exact source roster. Missing proofs, altered terms, circular or forward references, incomplete compressed numbers, and changed source spans fail verification.

The query snapshot preserves every named hypothesis, rule, and theorem. Its edges include assertion frames and every rule application. Integration checks reconstruct the axiom closure from all 2,545,549 native dependency edges and require agreement with every assertion's source replay. Local premises remain separate from global `$a` rules.

Native proofs retain the Metamath substitution calculus and the explicit rules of their source database. The MIU translation below constructs a Lean derivation in an explicit inductive interpretation of that one calculus.

## Queries

Native queries use the same repository installation:

```sh
python3 -m repository.metamath stats
python3 -m repository.metamath search pm2.43 --database set.mm
python3 -m repository.metamath show metamath:set.mm:pm2.43
python3 -m repository.metamath proof metamath:set.mm:pm2.43
python3 -m repository.metamath source metamath:set.mm:pm2.43
python3 -m repository.metamath assumptions metamath:set.mm:pm2.43
python3 -m repository.metamath deps metamath:set.mm:pm2.43 --transitive
python3 -m repository.metamath hierarchy metamath:set.mm:pm2.43
python3 -m repository.metamath trace metamath:set.mm:pm2.43 metamath:set.mm:ax-1
```

`proof` returns the native proof tokens, exact rule-application DAG, and assertion frame. `source` returns the archived source bytes for the declaration; add `--full` for the complete source database. `assumptions` distinguishes the theorem's own hypotheses and disjoint conditions from its transitive `$a` rules. `hierarchy` includes every prerequisite in source order. Queries use database-qualified identities throughout. Terminal search retains every matching result unless `--limit` is specified. Default queries reject snapshots whose verification inputs or upstream source bytes have changed; `--snapshot DIRECTORY` explicitly opens a retained archive independently of the current worktree.

## MIU interpretation in Lean

`Math/Logic/Miu.lean` interprets the pinned `miu.mm` alphabet, initial word, and four rewriting rules as an inductive derivability relation. It proves the complete criterion: a word is derivable exactly when it starts with M, contains exactly one M, and its number of I symbols is nonzero modulo three. The proof constructs suitable pure-I words, reduces their lengths in steps of three, and replaces triples by U. This gives a decision procedure and proves that MU is not derivable.

Export the checked native theorem as a Lean derivation:

```sh
python3 -m repository.metamath translate-lean metamath:miu.mm:theorem1 > /tmp/miu-proof.lean
lake env lean /tmp/miu-proof.lean
```

The exporter requires the reviewed MIU source digest and exact rule frames. It reconstructs the native proof DAG and translates its seven logical steps, in order, to Lean rule constructors. The output retains source and checked proof digests. Lean checks the resulting derivation of MUIIU independently. Changing its conclusion to MU fails checking. Translation requests for other databases, unproved declarations, changed source bytes, or unresolved symbols are rejected. The remaining databases retain their native foundations and proof artifacts.

## Source primitives

The native index also retains every constant, variable declaration, lexical scope, and disjoint-variable clause. Their identities include the source database and statement ordinal. Redeclaring a variable after its scope closes gives it a distinct identity. A symbol within a multi-symbol declaration also records its position.

Each named statement has a source binding with every ordered token occurrence, its enclosing scope, ordered mandatory hypotheses, frame variables, and disjoint restrictions. Each disjoint restriction links to an active original source clause. Nested duplicate clauses preserve a valid outer witness when the nested scope closes. Source relationships have explicit relation names and their own index. Theorem assumptions continue to come from the original assertion frames and proof graph.

```sh
python3 -m repository.metamath primitives wff --database set.mm --kind constant
python3 -m repository.metamath primitive metamath:set.mm:pm2.43
python3 -m repository.metamath primitive-context metamath:set.mm:pm2.43
python3 -m repository.metamath primitive-relations metamath:set.mm:pm2.43
python3 -m repository.metamath primitive-source metamath:set.mm:pm2.43
```

Use the returned `metamath-symbol:`, `metamath-scope:`, and `metamath-disjoint:` identities with the same commands. `primitive-relations --reverse` finds all incoming source relationships, preserving repeated symbol occurrences and their positions. `--relation` filters the relationship type. Searches and relationship queries return all matches unless `--limit` is specified; `--offset` supports pagination. Source downloads return the exact declaration bytes or the complete enclosing scope block. `--full` returns the complete database.

The source index is stored inside the content-addressed native SQLite artifact. Its counts appear under `source_primitives` in the manifest and native summary. These counts are separate from proved assertions, declared rules, and local hypotheses.

## Browser

Choose **Metamath** in the explorer's proof-library selector to search all nine databases. Names, local hypotheses, and declared rules remain database-qualified. A proved assertion has a Proof tab; declared rules and local hypotheses explicitly have no proof.

The native Proof tab reconstructs each substituted expression from its rule and ordered arguments. Argument links preserve repeated references to shared steps. The inspector checks every expression digest and requires the same final derivation digest as the independently replayed source. The original proof tokens, assertion frame, and proof-local hypotheses remain available.

Foundations shows ordered local hypotheses, mandatory disjoint-variable restrictions, and every transitive declared rule with a dependency path. Hierarchy levels retain all prerequisites. The global graph atlas explores Lean; native assertions have complete individual hierarchies and graph downloads.

Source pages retain access to every line, and **Download complete database** returns the original bytes. **Complete native archive** downloads a portable archive with the snapshot pointer, manifest, database, source files, and proof exports. References retains the declaration's original documentation comment.

The server admits native browser data only when the checked Lean catalog binds the same native snapshot and both archives record the same verification inputs. Library selection preserves one combined snapshot identity through queries and downloads. Refresh validates both archives before switching them together.

## Artifacts

`build/metamath/index.json` points to the current native snapshot. The addressed directory contains the immutable query database, each original mathematical source, each proof export, and a manifest with their digests, input hashes, pinned source provenance, verifier outputs, compiler versions, and license notices. The Lean catalog records the native snapshot digest accepted in that verification run.

The current native snapshot and its complete addressed directory suffice for its retained proofs. Prior snapshot directories can be removed once no reader needs them. Rebuilding requires the reviewed repository sources, pinned upstream sources, toolchains, and dependency locks. The native query reader checks the manifest and every archived artifact before opening the database.
