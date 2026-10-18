# Remaining work

The objective remains a universal, living repository covering mathematical axioms, definitions, objects, theorems, and proofs through the research frontier, with complete machine-checked derivations and collaborative expansion.

The current implementation supplies a seed library and registered mathlib modules, transitive dependency extraction, explicit axiom policy, shared expression storage, a local browser explorer with immutable query snapshots, subject browsing, complete dependency hierarchies, replayable proof downloads, archived source attribution, and contribution checks. Mathematical coverage includes number systems through complex numbers, cardinality, Sylow theorems, rank-nullity, commutative algebra, finite and infinite Galois correspondence, normal bases, the Nullstellensatz, topology, the fundamental theorems of algebra and calculus, measure theory, Pythagoras, extremal graph theory, categories, discrete probability, recursive functions, halting undecidability, oracle reductions, and Turing machine simulations. Lean and nanoda verification are required for publication. See [representative results](coverage.md).

Every indexed logical declaration is bound to the exact proof export accepted by both checkers. Lossless name identities, reduction hints, definition groups, and recursor rules are retained and compared; packed fingerprints and shared immutable universe requirements limit verification overhead. Catalog reading streams records and shares repeated JSON field names while retaining every value.

Number theory now includes modular arithmetic, quadratic reciprocity, Pell equations, Dedekind ideal factorization, finite ideal class groups, Minkowski bounds, Dirichlet units, regulators, the product formula, and the Kummer-Dedekind criterion.

Browser and terminal queries share immutable query snapshots. Terminal search, dependency, and export commands retain complete results while avoiding the full proof expression array. Catalog-only terminal use remains available when a query receipt was not retained.

The browser inspects exact term occurrences with their binder contexts, ordered application arguments, local definitions, referenced declarations, and recursor reduction rules. Structured navigation reads each requested path from the immutable snapshot and retains full term downloads.

Pinned upstream bibliographies and compiled module documentation connect explicit citation keys to retained records, publication links, and source locations. The browser distinguishes declaration citations from module references and preserves the complete bibliography for reconstruction.

Probability coverage includes laws and distributions, independence and conditional independence, conditional expectations, Borel-Cantelli lemmas, the strong laws of large numbers, the real central limit theorem, stopping times, optional sampling, and martingale convergence. Statement checks retain the precise integrability, independence, boundedness, and convergence hypotheses.

Work still required:

- Expand registered mathlib coverage across further fields and research results, and integrate other established formal libraries while preserving upstream declarations, licenses, references, and proof dependencies.
- Extend mathematical coverage across number systems, relations, order, algebra, analysis, geometry, topology, probability, computation, and research results.
- Connect further informal statements and references to precise formal declarations, support project bibliographies, and record competing formulations and generalizations.
- Extend browser proof inspection to explanatory proof steps, informal references, and contribution history.
- Publish reproducible verification artifacts and compare formal statements with trusted reference specifications and additional proof checkers.
- Extend shared expression storage to incremental indexing, stable identifiers across renames, larger-scale storage and search, and additional versioned library imports.
- Establish mathematical review, attribution, release policies, and collaborative contribution workflows beyond CI validation.
- Represent alternative foundations and conditional assumptions with explicit boundaries and formally verified translations where available.

Each expansion must retain the complete dependency closure and make its foundational assumptions inspectable. Passing the current checks does not complete the universal coverage objective.
