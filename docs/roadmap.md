# Remaining work

The objective remains a universal, living repository covering mathematical axioms, definitions, objects, theorems, and proofs through the research frontier, with complete machine-checked derivations and collaborative expansion.

The current implementation supplies a seed library and registered mathlib modules, transitive dependency extraction, explicit axiom policy, shared expression storage, a local browser explorer with immutable query snapshots, subject browsing, complete dependency hierarchies, replayable proof downloads, archived source attribution, and contribution checks. Mathematical coverage includes number systems through complex numbers, cardinality, Sylow theorems, rank-nullity, topology, the fundamental theorems of algebra and calculus, measure theory, Pythagoras, extremal graph theory, categories, discrete probability, recursive functions, halting undecidability, oracle reductions, and Turing machine simulations. Lean and nanoda verification are required for publication. See [representative results](coverage.md).

Every indexed logical declaration is bound to the exact proof export accepted by both checkers. Lossless name identities, reduction hints, definition groups, and recursor rules are retained and compared; packed fingerprints and shared immutable universe requirements limit verification overhead.

Work still required:

- Expand registered mathlib coverage across further fields and research results, and integrate other established formal libraries while preserving upstream declarations, licenses, references, and proof dependencies.
- Extend mathematical coverage across number systems, relations, order, algebra, analysis, geometry, topology, probability, computation, and research results.
- Connect informal statements and bibliographic references to precise formal declarations and record competing formulations and generalizations.
- Extend browser proof inspection to explanatory proof steps, informal references, and contribution history.
- Publish reproducible verification artifacts and compare formal statements with trusted reference specifications and additional proof checkers.
- Extend shared expression storage to incremental indexing, stable identifiers across renames, larger-scale storage and search, and additional versioned library imports.
- Establish mathematical review, attribution, release policies, and collaborative contribution workflows beyond CI validation.
- Represent alternative foundations and conditional assumptions with explicit boundaries and formally verified translations where available.

Each expansion must retain the complete dependency closure and make its foundational assumptions inspectable. Passing the current checks does not complete the universal coverage objective.
