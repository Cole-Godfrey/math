# Contributing

1. Add a Lean declaration in the relevant `Math/` module. State hypotheses as explicit or implicit binders and give a complete proof or definition. Add a short docstring.
2. Import earlier results. For a new module, add its import to `Math.lean` and an entry in `knowledge.json` with its title and allowed axioms. Assign it to a subject.
3. Run `make check`. Inspect the statement with `show --proof` and its assumptions with `trace`.
4. Open a pull request describing the mathematical statement, its source or reference, and any changed assumptions. CI must pass before merging.

Do not use `sorry`, `admit`, unsafe or partial definitions, or computation tactics that introduce native evaluation axioms. Safe compile-time definitions remain subject to kernel checking. Kernel-reduced proofs such as `decide` are permitted. An inconsistent statement supplied as a hypothesis remains an explicit conditional assumption; it is never promoted to an unconditional theorem.

New foundational axioms require an explicit declaration, an entry in `knowledge.json` explaining the assumption and its reference, and a module policy allowing it. Review these changes as changes to the foundation. Existing modules should retain their axiom budgets. Lean-generated declarations are subject to the same policy as authored declarations.

Keep informal descriptions faithful to the formal type. A successful build verifies that type and proof; reviewers must still check that the formal statement expresses the intended mathematics.

The index is generated. Commit Lean sources, policy, and tests; leave `.lake/`, `.tools/`, and `build/` untracked. Changes to verification inputs invalidate the local index until verification runs again.

To index another upstream mathlib module, add its title and axiom budget under `libraries.mathlib.modules` in `knowledge.json`, assign it to a subject, then run `make check`. The module need not be copied or renamed, and every logical declaration it defines is included. Its complete dependency closure is checked even when dependencies belong to modules not selected as search roots.

Subject parent links organize browsing and must be acyclic. Every selected module must have a subject assignment. The `hierarchy` command derives logical prerequisites from kernel declarations independently of this classification.

Library upgrades must pin a full commit in `lakefile.toml`, update the Lake lockfile, and match the revision in `knowledge.json`. Preserve the library's license attribution. Verification compares tracked dependency bytes with their Git objects and rejects changed, missing, or untracked sources. `make verify` cleans the local package while retaining dependency caches; it rechecks their reachable proof terms.

An upstream library can register a `bibliography` path relative to its pinned checkout. The file must be tracked at that revision. Cite an entry with `[bibkey]` or `[Author, Title][bibkey]` in documentation. The source library's entries take precedence; `library:bibkey` selects another registered bibliography explicitly. The explorer keeps declaration citations and module references distinct.
