# math

A growing repository of formal mathematics with Lean-checked proofs and explicit foundational dependencies.

The goal is a universal, living account of mathematics, from logical foundations to contemporary research. Current coverage includes logic, relations, orders, cardinality, number systems through complex numbers, groups, primality, vector spaces, topology, calculus, measure theory, geometry, extremal graph theory, categories, probability mass functions, recursive functions, and Turing machines. The full goal remains open. See [representative results and their scope](docs/coverage.md).

Install [Lean and elan](https://lean-lang.org/install/), then run:

```sh
make check
python3 -m repository serve
python3 -m repository search Pythagorean --subject geometry
python3 -m repository show Math.Natural.mul_assoc --proof
python3 -m repository trace Math.Logic.Classical.excluded_middle
python3 -m repository deps Math.Sets.union_comm --transitive
python3 -m repository show Complex.exists_root --proof
python3 -m repository show Sylow.exists_subgroup_card_pow_prime
python3 -m repository subjects
python3 -m repository search "mean value" --subject analysis
python3 -m repository search "halting" --subject computation
python3 -m repository show ComputablePred.rice₂ --proof
python3 -m repository hierarchy Math.Natural.mul_comm --format json
```

`lean-toolchain` pins Lean 4.35.0. Python 3.10 or newer is required; no Python packages are needed. `MATH_LAKE` can select a local Lake executable.

`serve` runs a local explorer at http://127.0.0.1:8000. Browse subjects, search declarations, inspect statements and complete proof terms, follow prerequisites and axiom paths, and read the source retained with each snapshot. Hierarchy levels and pages retain access to every dependency. Downloads include expression graphs, complete dependency graphs, the complete index, and replayable proofs. Use `--port PORT` to select another port.

After changing mathematical or verification sources, run `make check`, then choose **Refresh snapshot**. The explorer serves one immutable verified snapshot until refreshed; startup and refresh reject stale inputs or changed artifacts.

`make fetch` materializes locked dependencies and downloads the caches for registered mathlib modules. `make check` fetches these dependencies, verifies the library, and tests the extractor, policy checks, CLI, and adversarial contributions. GitHub Actions runs it for pushes and pull requests and retains the verified index and proof export as an artifact.

`make verify` rebuilds project proofs, replays the complete proof dependency closure through Lean's kernel and the independent nanoda checker, and writes `build/knowledge.json` with a content-addressed proof export and SQLite query snapshot. `build/index.json` binds the query snapshot to the checked artifacts and inputs. Both checkers ship with the pinned Lean distribution. Upstream sources must match the exact commits in `lake-manifest.json`; reachable upstream proofs are rechecked alongside local proofs.

Every logical declaration in project modules and registered library modules enters the index, including generated declarations and names outside the `Math` namespace. The exporter follows types, proof terms, definitions, constructors, and recursor rules through their complete dependency closure. The index includes source locations, universe parameters, readable terms, shared expression graphs, axiom sets, and content hashes. Unsafe or partial upstream runtime implementations are inventoried separately and cannot occur in mathematical proof dependencies. Project modules reject unsafe and partial definitions. Safe compile-time declarations retain their `meta` annotation and undergo the same proof checks.

Lean and Python independently recompute complete axiom sets from the dependency graph. Lean's cached axiom summaries are retained separately so omitted dependencies through inductive blocks remain inspectable.

Every indexed type, body, universe parameter, and inductive reduction rule is also matched against the exact proof export consumed by both checkers. Schema 3 retains lossless logical name components, definition groups, reduction hints, and the resulting `proof_binding` audit. Term downloads include the exact names needed to interpret their expression graphs.

The mathlib integration retains upstream declaration names, docstrings, author notices, exact source links, and dependency license notices. Register additional modules in `knowledge.json`; their declarations become searchable after fetching and verification. See [third-party sources](THIRD_PARTY.md).

Search includes selected local and upstream declarations by default. Search prioritizes exact names, public declarations, and documentation matches while retaining every result. Use `search --all` for verified dependencies, `--axiom-free` for declarations using no additional axioms, or `--subject`, `--module`, and `--kind` to filter. A subject search includes child subjects; adding `--all` searches its complete prerequisite closure. `subjects --json` exposes coverage counts and module assignments.

`hierarchy NAME` orders every prerequisite before the result and groups inductive dependency cycles. Its JSON output includes every declaration, every dependency edge with its role, group levels, and paths to all foundational axioms. `--format dot` produces a Graphviz diagram of the dependency groups. Subject parent links classify topics; logical ordering comes from the extracted proof dependencies.

`show --json` exposes expression and structural data. `deps --reverse` finds dependent declarations; `trace --to NAME` finds a path to any dependency. `export --format dot` produces a graph of the whole index; `export` emits the complete JSON index. `export --format lean` emits the replayable lean4export JSONL proof artifact.

See [foundations](docs/foundations.md), [index format](docs/index-format.md), [contributing](CONTRIBUTING.md), and [remaining work](docs/roadmap.md).
