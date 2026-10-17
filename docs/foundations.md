# Foundations

The foundation is Lean 4.35.0's dependent type theory. Its kernel checks universe-polymorphic dependent functions, inductive families and their elimination rules, definitional equality, proof irrelevance, and impredicative propositions. Quotient types have primitive formation and reduction rules. These rules are part of the declared foundation even when a theorem has no additional axioms. See the [Lean language reference](https://lean-lang.org/doc/reference/4.35.0/).

Three additional axioms are declared in `knowledge.json`:

| Axiom | Assumption |
| --- | --- |
| `propext` | Equivalent propositions are equal. |
| `Quot.sound` | Related elements have equal quotient representatives. |
| `Classical.choice` | An inhabited type has a chosen element. |

The kernel cannot prove these assumptions or their consistency. Their use is recorded per declaration. See [Lean's axiom documentation](https://lean-lang.org/doc/reference/4.35.0/Axioms/).

Constructive logic, functions, and natural number arithmetic allow no additional axioms. Extensional equality of functions uses `Quot.sound`; equality of predicates also uses `propext`. Classical logic allows all three. The algebra module allows `propext` because Lean generates constructor injectivity lemmas stated as equalities of propositions; its authored monoid and group results use no additional axioms.

## Verification

`make verify` clears the local package's build products and compiles every project module and registered library module. The pinned Lean toolchain checks source declarations. `tools/Export.lean` then imports the private kernel environment with trust level zero and retains theorem and opaque bodies. Export roots are all logical constants belonging to project modules and registered library modules, regardless of namespace or documentation.

For each declaration, the exporter records its type and body in a shared expression graph. It gathers dependencies from both expressions and from inductive blocks, constructors, and recursor reduction rules. Projection expressions include their parent type. Axioms' own types are traversed too. Bound hypotheses and universe parameters remain in the expressions. Sharing does not change binder scope: each declaration's type, body, and reduction rules must remain closed in their own context.

Selected roots include every declaration serialized in a registered module and every kernel constant canonically attributed to it. Imported modules can share generated helper declarations, and Lean's canonical ownership can point to a different module. The index records every selecting module, retains the canonical source origin, and applies every selecting module's axiom budget. Shared helpers therefore remain selected when further imports change canonical ownership.

The exporter recomputes axiom dependencies to a fixed point over the actual kernel declarations without imported summary caches. The Python audit independently collects expression references, checks that every dependency exists, and computes the same full axiom closure. Both results must agree. It rejects unresolved variables, missing bodies, unsafe or partial declarations, undeclared axioms, and module policy violations. Admissions such as `sorryAx` cannot be added to the policy. Native evaluation proofs introduce undeclared axioms and are rejected.

The Python audit checks reported declaration graphs, axiom summaries, and every selecting module's budget before allocating expression audit state. Acceptance also requires validating every expression and matching every reported dependency to its type, body, and structural data.

`lean_axioms` also preserves Lean's cached `collectAxioms` listing. Those cached axioms must occur in the full dependency closure. Cached listings can be smaller because the complete graph includes whole inductive blocks and reduction rules, and imported summaries can lose dependencies across cycles. For example, the complete dependencies of `T2Space` include the Boolean algebra structure used in its constructor's type. The published `axioms` field and module budgets use the complete closure; differences from cached summaries remain visible in the index.

Upstream modules may also contain partial or unsafe runtime implementations, such as `Nat.minFacAux._unsafe_rec` and `Real.instRepr`. The export records their kernel safety and compiler phase in a separate nonlogical inventory, checks that the module inventory is complete, and rejects any occurrence in a mathematical dependency closure. The terminating logical definition `Nat.minFacAux`, the construction of the real numbers, and their proofs remain fully checked. Local mathematical modules reject unsafe and partial definitions.

The `meta` annotation identifies compile-time declarations, including generated implicit arguments and safe metaprograms. It does not disable logical type checking. Safe meta declarations and their dependencies remain in the graph and undergo the same kernel and independent checks as other definitions. The annotation is retained for inspection.

Inductive declarations and their constructors can depend on one another. Those cycles represent a single kernel-checked inductive block. Traversal and axiom propagation handle cycles; project module imports must remain acyclic. The module hierarchy comes from Lean's actual imports.

The `hierarchy` explorer follows all type, body, and structural dependencies of a declaration. It computes strongly connected components to group inductive cycles, then orders the resulting groups with every prerequisite first. No dependency edges are discarded from its JSON representation. Subject categories provide a separate browsing hierarchy and do not supply proof assumptions.

The same kernel environment is also exported in the standard lean4export JSONL format. A separate `leanchecker --from-export` process reconstructs the dependency closure in an empty kernel environment. The independent Rust checker nanoda checks that export with the declared axiom allowlist. These passes check actual proof types and terms, including declarations that a metaprogram might have inserted without kernel checking.

An independent Python reader also compares every indexed declaration with that exact checker input. It reconstructs logical fingerprints from the standard export's separate name, universe, and expression tables and matches them against the index. The comparison covers kinds, ordered universe parameters, types, bodies, exact name components, definition groups, reduction hints, inductive metadata, constructor fields, quotient primitives, and every recursor reduction rule. Expression identifiers can differ. Binder labels and visibility, metadata wrappers, and let optimization hints are normalized because they do not change logical term identity. Missing declarations or altered logical terms abort verification.

The `proof_binding` audit binds this comparison to the retained proof file digest. Both checkers must accept the same file, and its digest is checked again before publication. Artifact readers require matching binding coverage and provenance. A structurally valid but ill-typed replacement body is rejected by comparison with the checked export.

The audit atomically publishes `build/knowledge.json` only after every check succeeds. The artifact contains hashes of verification inputs, declaration records, and the retained proof export. Explorer commands reject artifacts whose content or inputs have changed or whose proof export is missing or altered. Hashes detect changes; they are not signatures. Rebuild from reviewed source to verify an artifact.

The browser query store is a lossless projection created after both proof checkers succeed. Publication checks every expression and dependency role and reconstructs the byte-identical complete catalog. Its content-addressed receipt binds it to the proof export and verification inputs. Browser startup and refresh repeat source and artifact integrity checks. A running explorer holds one immutable snapshot and reads its archived sources. Search pages and hierarchy levels provide access to the complete stored closure; downloads retain the complete index and replayable proofs.

## Trust and scope

Mathematical checking uses the pinned Lean kernel and the independent nanoda implementation of Lean's type theory. It still assumes the declared logical foundation and the integrity of the tools and host. Dependency reporting additionally trusts the exporter and Python audit. CI builds project sources from a fresh checkout; local clean verification rebuilds them. Imported library declarations are rechecked when reachable from indexed declarations.

The mathlib registry and Lake lockfile must identify the same exact repository commit. Verification checks every locked dependency's checkout, repository identity, and tracked bytes against the commit's Git objects. The index retains commit identities, source digests, module notices, and dependency license texts. Explorer commands repeat the source checks before serving an artifact. Upstream cache files supply elaborated terms for replay; cache download success does not replace proof checking.

Readable statements and proof terms may use notation. Structured index expressions retain constants, universe arguments, binders, literals, projections, and recursor data; nonlogical expression metadata is omitted. The separate lean4export artifact is used for kernel replay. See [Lean's proof validation guidance](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/) for the distinction between proof checking and reviewing the meaning of a formal statement.

Types record local assumptions. A theorem with a hypothesis `False` is a conditional statement with that hypothesis. An empty axiom set means the proof uses only the kernel foundation and its bound assumptions. The current library does not claim to formalize all mathematics or establish the consistency of its foundation.
