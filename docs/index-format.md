# Index format

`build/knowledge.json` uses schema version 3. `knowledge.json`, the reviewed foundation and library policy, uses policy schema version 1. Rebuild older indexes with the current verifier; schema 3 requires lossless logical names and proof binding metadata.

The index contains declarations, selected roots, all imported module names and their imports, the selected module hierarchy, subject categories, foundation rules, axiom budgets, source origins, and verification provenance. `module_declarations` inventories every constant from selected modules. It is exactly the union of mathematical `roots` and separately recorded `nonlogical_declarations`. `module_declarations_by_module` records each selected module's complete serialized declaration names together with constants canonically owned by that module. A generated declaration can belong to several serialized modules even when Lean attributes its canonical origin to another import. Selection, subject coverage, and axiom budgets use every selecting module; declaration `module` and source attribution retain the canonical origin. Nonlogical entries retain their kernel safety classification and explicit `meta` status. Unsafe or partial programs are excluded from mathematical proof dependencies. Safe compile-time declarations remain checked; their `meta` flag identifies compiler phase.

Module `docs` records contain text and source line ranges obtained from Lean's module-documentation environment extension. `bibliographies` maps registered libraries to their retained BibTeX source, file digest, pinned revision, license, source URL, and parsed entries. Entries retain their exact keys, kinds, fields, original record text, and line ranges. Bibliography data is source metadata; logical assumptions remain in declaration types and foundational axiom sets.

`/api/citations?name=NAME` returns explicit citations in a declaration's documentation and references in its module documentation as separate lists. Known reference keys outside code spans resolve first within the source library, then across unique registered keys. Qualified `library:key` citations select a bibliography explicitly. Ambiguous cross-library keys retain their candidate identities. `/api/bibliography?package=LIBRARY` downloads the complete retained file. Both endpoints enforce snapshot identity.

Declaration `axioms` are the full transitive dependency closure, recomputed independently by Lean and Python. `lean_axioms` retains Lean's cached summary and must be a subset of that closure. `axiom_audit` records the method and the number of declarations whose complete dependencies exceed the cached listing. Module axiom budgets apply to the full closure.

`subjects` maps subject identifiers to titles, parent identifiers, and selected module assignments. Parents form an acyclic browsing hierarchy; assignments cover every selected module. Logical dependencies remain the declaration edges extracted from Lean. `subjects --json` reports the selected coverage and full prerequisite closure of each subject, including descendants.

`hierarchy NAME --format json` gives a complete dependency subgraph for one declaration. Its `groups` array orders strongly connected components with prerequisites first. Each group records its members, dependency group identifiers, longest prerequisite level, and cycle status. The `edges` array retains every original declaration edge and identifies whether it occurs in a type, value, or inductive structure. The response also includes the kernel foundation and paths to each axiom.

## Expressions

`expressions` is a topologically ordered array of logical expression records. Declaration `type` and `value` fields, and recursor rule `rhs` fields, reference array indices. A missing body is JSON `null`. Each expression child references an earlier array entry; cycles and forward references are rejected.

| Tag | Contents |
| --- | --- |
| `sort` | A universe level. |
| `const` | A declaration name and its universe arguments. |
| `bvar` | A de Bruijn index for a bound variable. |
| `app` | `function` and `argument` references. |
| `lam`, `forall` | Binder name and visibility, `type`, and `body` references. |
| `let` | Binder name, `type`, `value`, `body`, and nondependence annotation. |
| `proj` | Parent structure name, field index, and expression reference. |
| `nat`, `string` | A kernel literal. |

Universe levels retain zero, successor, maximum, impredicative maximum, and named parameters. Unresolved universe variables and expression variables are rejected. The audit computes required binder depth and universe parameters through the graph, then checks each declaration root independently. It includes projection parents when collecting constant references.

`name_data` maps each logical name identifier to its ordered components. Each component is either `{"str":"component"}` or `{"num":0}`; the empty array represents the anonymous name. Numeric components remain distinct from string components containing digits, and quoted components can contain dots. These identities cover declaration names, constants, projection parents, universe parameters, and definition groups. Binder labels remain display metadata; bound references use de Bruijn indices.

`definition_group` retains the ordered mutual-definition names for definitions, theorems, and opaque declarations. `reducibility` is `"abbrev"`, `"opaque"`, or `{"regular":HEIGHT}` for definitions and `null` for other declaration kinds.

`show --json` includes the declaration's reachable expression subgraph as an object keyed by the original array indices, together with the required `name_data`. Browser expression downloads also retain universe parameters, definition groups, and reduction hints. `export` includes the complete array. Readable statements and proof terms accompany the graph.

The extractor spools expression records to a temporary file as their identifiers are assigned, then streams the complete array into the export. Publication, content hashing, and CLI exports stream canonical JSON records. Array order, expression sharing, and canonical bytes remain unchanged; these operations avoid allocating another serialized copy of the entire index.

## Integrity and provenance

`expression_hashes` contains SHA-256 hashes of canonical expression records with child references replaced by child hashes. Their values are independent of array numbering. Declaration hashes substitute these expression hashes for type, body, and recursor rule references before hashing the record. Other declaration metadata remains part of that record hash.

`sources` maps modules to local source hashes or upstream repositories, commits, source paths, license notices, and original module headers. `provenance.dependencies` records exact package commits, source digests, and retained license texts. Toolchain source identity, license, verifier names, local input hashes, and the proof export digest are also retained.

The top-level `content_digest` hashes the entire index with that field omitted. The content-addressed `proofs-<sha256>.jsonl` file uses the separate standard lean4export format. Lean's kernel and nanoda replay that file before publication. Hashes identify content and detect changes; mathematical validity comes from the proof checks and declared assumptions.

`proof_binding` records a complete comparison against that same proof file. Its schema version 1 audit includes indexed and matched declaration counts, expression counts, the proof file digest, and a `logical_digest`. SHA-256 fingerprints cover exact name identities, declaration kinds, ordered universe parameters, types, values, definition groups, reduction hints, and inductive, constructor, quotient, and recursor data. Missing or changed indexed declarations abort publication. Extra declarations introduced by the standard exporter's inductive packages are checked by the proof checkers too.

Logical fingerprints are independent of expression numbering. They ignore binder labels, binder visibility, expression metadata wrappers, and let nondependence optimization hints, which do not change logical term identity. Those annotations remain in the index where applicable. The separate `expression_hashes` and `declaration_hashes` continue to cover the retained records and metadata.

## Query snapshots

Verification also publishes `index-<sha256>.sqlite` and a schema version 1 `build/index.json` receipt. The receipt binds the database bytes, complete JSON artifact bytes, catalog content digest, and verification provenance. It is published last, after input and package source checks repeat.

Keep `build/index.json`, `build/knowledge.json`, and the database and proof export named by the receipt. This snapshot retains the complete proof dependency closure; earlier builds are not dependencies. Delete older database and proof export files after readers and comparison checks release them. Git retains the sources and dependency locks for rebuilding earlier revisions.

The SQLite database retains every complete declaration record, expression record, expression hash, declaration hash, dependency edge role, source origin, and catalog metadata field. A separate `selections` table retains every selecting module, including shared generated declarations. The `names` table retains exact logical identities and supplies the names required by individual term downloads. Declaration identifiers preserve the original array order. Additional source text is archived by module. The builder checks expression bytes and hashes, edge roles, selecting modules, foreign keys, counts, and the SHA-256 of the reconstructed complete JSON artifact before publication. The reconstructed artifact must be byte-identical to `build/knowledge.json`.

The explorer uses read-only immutable SQLite connections. Startup and refresh verify database, index, and proof export hashes, current verification inputs, and exact dependency sources. A running snapshot retains its archived source text; later worktree edits cannot change that view.

Terminal queries use the same integrity-checked snapshot. Statistics count stored declarations; search, dependency lists, and graph exports stream complete result sets. Statement inspection reads one declaration, and `show --json` reads its complete reachable expression graph with exact name identities. Subject coverage, hierarchy, and trace commands load the declaration dependency graph without loading the proof expression array. JSON and proof exports retain the original artifact bytes. Terminal commands retain the complete catalog reader when `build/index.json` is absent; an invalid existing receipt is rejected.

`/api/term` reads one expression occurrence from a declaration's statement (`root=type`), body (`root=value`), or recursor reduction rule (`root=rule&rule=0`). Its `path` follows expression fields: `t` for type, `b` for body, `f` for function, `a` for argument, `v` for a let value, and `e` for a projection's expression. The empty path selects the root. Every step must be a child of the current expression. The response retains the stored expression digest, exact logical name components, immediate children, all arguments in application order, and the local binder context. Binder depths identify their occurrences; bound variable indices count outward from the innermost binding. A binder's type and a let's value use the surrounding context; only its body enters the new scope.

Natural literal values in this inspector endpoint are decimal strings so browser number conversion preserves every digit. The underlying expression digest and complete expression download retain the original indexed representation. Inspector requests carry the same snapshot identity checks as other browser queries and read the requested path and its immediate neighbours from the query store.

The repository disables Python's limit on decimal conversion. Natural literals retain every digit through parsing, hashing, proof binding, storage, and downloads; they remain JSON integers in complete expression records. Tests replay a literal with 5,001 digits through both checkers and reject an altered value.

The local HTTP interface provides `/api/summary`, `/api/search`, `/api/declaration`, `/api/dependencies`, `/api/hierarchy`, `/api/source`, `/api/expressions`, and `/api/guide`. Search, dependency, and hierarchy pages include totals and offsets; complete graph downloads retain all edges. `/api/catalog` streams the complete original JSON artifact from SQLite, and `/api/proof-export` streams its content-addressed replayable proof export. Requests can pin a catalog digest with `snapshot`; responses identify it with `X-Math-Snapshot`. An obsolete digest is rejected. `POST /api/reload` validates and selects the latest published snapshot.

Reviewed citation aliases are registered in `libraries.PACKAGE.citation_aliases`. An alias must target an existing entry in the pinned bibliography and cannot replace a canonical key or form a chain. Citation responses preserve the original spelling in `citation_key` and the unchanged bibliography entry in `key`, `raw`, and `source_url`.

When the Lean catalog binds a native Metamath snapshot, `system=lean|metamath` selects the proof library. Database-qualified native names select their own interpreter. Both libraries share a combined `X-Math-Snapshot` pin while retaining their own proof calculus and foundational assumptions. Native `/api/expressions` returns exact substituted proof steps, `/api/native-proof` inspects an individual step, `/api/native-foundations` pages through declared rules and their dependency paths, and `/api/native-source` downloads the complete original source database. Native `/api/proof-export` streams a portable archive containing every retained source and proof artifact. Native source pages use the newline bytes recorded by the source-span audit and provide access to every line.

Native source primitives are stored in `primitive_objects` and `primitive_edges` inside the same addressed database. The manifest records `source_primitives.schema_version` and per-database counts. `/api/native-primitives?system=metamath` searches constants, variables, scopes, and disjoint clauses; `kind=assertion_symbols` retrieves named-statement bindings. `/api/native-primitive`, `/api/native-primitive-context`, and `/api/native-primitive-relations` take a qualified `name`. Relationship pages preserve token positions and report their complete total. `/api/native-primitive-source` downloads the exact declaration or scope block; `full=1` selects the original database. All these requests use the same combined snapshot pin. Source relationships retain their own kinds, including expression symbols, mandatory hypotheses, frame variables, and original disjoint-clause witnesses.
