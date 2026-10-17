"""search and inspect verified mathematical knowledge from the terminal."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from .build import fetch, load_catalog, proof_export_path, verify
from .core import RepositoryError, canonical_chunks, declaration_expressions, dependency_path, expression_names, require
from .explore import KnowledgeGraph


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description="Verify and explore mathematical declarations.")
    result.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    sub = result.add_subparsers(dest="command", required=True)
    check = sub.add_parser("verify", help="compile proofs and audit their dependency closure")
    check.add_argument("--clean", action="store_true", help="rebuild every project module")
    sub.add_parser("fetch", help="fetch locked library sources and registered mathlib caches")
    sub.add_parser("stats", help="summarize verified mathematical coverage")
    browser = sub.add_parser("serve", help="open a local explorer for the verified snapshot")
    browser.add_argument("--port", type=int, default=8000)
    subjects = sub.add_parser("subjects", help="browse subject coverage and its dependencies")
    subjects.add_argument("--json", action="store_true")
    search = sub.add_parser("search", help="search names, statements, and documentation")
    search.add_argument("query", nargs="?", default="")
    search.add_argument("--all", action="store_true", help="include all verified dependency declarations")
    search.add_argument("--module")
    search.add_argument("--subject")
    search.add_argument("--kind")
    search.add_argument("--axiom-free", action="store_true")
    show = sub.add_parser("show", help="inspect a statement and its assumptions")
    show.add_argument("name")
    show.add_argument("--proof", action="store_true", help="include the elaborated proof term")
    show.add_argument("--json", action="store_true")
    deps = sub.add_parser("deps", help="list dependencies or dependent declarations")
    deps.add_argument("name")
    deps.add_argument("--transitive", action="store_true")
    deps.add_argument("--reverse", action="store_true")
    trace = sub.add_parser("trace", help="trace dependency paths to foundational axioms")
    trace.add_argument("name")
    trace.add_argument("--to", help="trace to any particular declaration")
    hierarchy = sub.add_parser("hierarchy", help="reconstruct a complete foundational dependency hierarchy")
    hierarchy.add_argument("name")
    hierarchy.add_argument("--format", choices=["text", "json", "dot"], default="text")
    export = sub.add_parser("export", help="write the complete verified index to stdout")
    export.add_argument("--format", choices=["json", "dot", "lean"], default="json")
    return result


def statistics(catalog: dict) -> str:
    nodes = {n["name"]: n for n in catalog["declarations"]}
    roots = [nodes[name] for name in catalog["roots"]]
    theorems = sum(n["kind"] == "theorem" for n in roots)
    documented = sum(bool(n["doc"]) for n in roots)
    free = sum(not n["axioms"] for n in roots)
    local = sum(node["module"] in catalog["local_modules"] for node in roots)
    return (f"{len(roots)} indexed declarations ({local} local, {len(roots) - local} upstream; "
            f"{theorems} theorems, {documented} documented)\n"
            f"{len(nodes)} declarations in the complete dependency closure\n"
            f"{free} indexed declarations use no additional axioms\n"
            f"Lean {catalog['lean_version']}; {len(catalog['module_policy']) - 1} subject modules")


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    root = args.root.resolve()
    try:
        if args.command == "fetch":
            fetch(root)
            return 0
        if args.command == "verify":
            catalog = verify(root, clean=args.clean)
            print(statistics(catalog))
            return 0
        if args.command == "serve":
            from .server import serve
            serve(root, args.port)
            return 0
        catalog = load_catalog(root)
        nodes = {n["name"]: n for n in catalog["declarations"]}
        if args.command == "stats":
            print(statistics(catalog))
        elif args.command == "search":
            results = KnowledgeGraph(catalog).search(args.query, args.subject, args.all,
                                                   args.module, args.kind, args.axiom_free)
            for node in results:
                print(f"{node['name']} [{node['kind']}]\n  {(node['doc'] or node['statement']).strip()}")
        elif args.command == "subjects":
            coverage = KnowledgeGraph(catalog).subject_coverage()
            if args.json:
                print(json.dumps(coverage, ensure_ascii=False, indent=2))
            else:
                records = {item["id"]: item for item in coverage}
                pending = [(name, 0) for name in reversed(sorted(records)) if records[name]["parent"] is None]
                while pending:
                    name, depth = pending.pop()
                    item = records[name]
                    print(f"{'  ' * depth}{item['title']} [{name}]: {item['selected_declarations']} selected, "
                          f"{item['dependency_declarations']} including dependencies")
                    pending.extend((child, depth + 1) for child in reversed(sorted(records))
                                   if records[child]["parent"] == name)
        elif args.command == "hierarchy":
            graph = KnowledgeGraph(catalog).hierarchy(args.name)
            if args.format == "json":
                print(json.dumps(graph, ensure_ascii=False, indent=2))
            elif args.format == "dot":
                print("digraph derivation {\n  rankdir=BT;")
                for group in graph["groups"]:
                    label = json.dumps("\n".join(group["members"]), ensure_ascii=False)
                    print(f"  g{group['id']} [label={label}];")
                    for dependency in group["dependencies"]:
                        print(f"  g{group['id']} -> g{dependency};")
                print("}")
            else:
                print(f"{args.name}: {len(graph['declarations'])} declarations, {len(graph['groups'])} dependency groups")
                print("Foundation: " + graph["foundation"]["id"])
                print("Axioms: " + (", ".join(graph["axioms"]) or "none beyond kernel rules"))
                for group in sorted(graph["groups"], key=lambda item: (item["level"], item["id"])):
                    suffix = " [inductive cycle]" if group["cyclic"] else ""
                    print(f"{group['level']}: {', '.join(group['members'])}{suffix}")
        elif args.command in {"show", "deps", "trace"}:
            require(args.name in nodes, f"unknown declaration: {args.name}")
            node = nodes[args.name]
            if args.command == "show":
                origin = catalog.get("sources", {}).get(node["module"], {})
                if args.json:
                    expressions = declaration_expressions(catalog, node)
                    print(json.dumps({**node, "origin": origin,
                                      "expressions": expressions,
                                      "name_data": {key: catalog["name_data"][key]
                                                    for key in sorted(expression_names(node, expressions.values()))}},
                                     ensure_ascii=False, indent=2))
                else:
                    print(f"{node['name']} [{node['kind']}]\n{node['statement']}")
                    if node["doc"]:
                        print(node["doc"].strip())
                    print("Axioms: " + (", ".join(node["axioms"]) or "none beyond kernel rules"))
                    if set(node["axioms"]) != set(node["lean_axioms"]):
                        print("Cached Lean summary: " + (", ".join(node["lean_axioms"]) or "none"))
                    print("Foundation: " + catalog["foundation"]["id"])
                    source = origin.get("url", node["module"].replace(".", "/") + ".lean")
                    if node["source"]:
                        source += ("#L" if origin.get("url") else ":") + str(node["source"]["line"])
                    print("Source: " + source)
                    if origin.get("revision"):
                        print(f"Origin: {origin['package']}@{origin['revision']}")
                        if origin.get("license"):
                            print("License: " + origin["license"])
                    if args.proof:
                        print("Term: " + (node["proof"] or "kernel primitive; inspect structural data"))
            elif args.command == "deps":
                edges = {name: set(n["dependencies"]) for name, n in nodes.items()}
                if args.reverse:
                    reverse = {name: set() for name in nodes}
                    for name, dependencies in edges.items():
                        for dep in dependencies:
                            reverse[dep].add(name)
                    edges = reverse
                reached = set()
                pending = list(edges[args.name])
                while pending:
                    name = pending.pop()
                    if name not in reached:
                        reached.add(name)
                        if args.transitive:
                            pending.extend(edges[name])
                for name in sorted(reached - {args.name}):
                    print(name)
            else:
                targets = [args.to] if args.to else sorted(node["axioms"])
                if not targets:
                    print("No additional axioms. Foundation: " + catalog["foundation"]["id"])
                for target in targets:
                    path = dependency_path(nodes, args.name, target)
                    require(path is not None, f"{target} is not a dependency of {args.name}")
                    print(" -> ".join(path))
        elif args.command == "export":
            if args.format == "json":
                for chunk in canonical_chunks(catalog):
                    sys.stdout.write(chunk.decode())
                sys.stdout.write("\n")
            elif args.format == "lean":
                with proof_export_path(root, catalog).open() as handle:
                    for chunk in iter(lambda: handle.read(64 * 1024), ""):
                        sys.stdout.write(chunk)
            else:
                print("digraph mathematics {")
                for name, node in sorted(nodes.items()):
                    for dep in sorted(node["dependencies"]):
                        print(f"  {json.dumps(name)} -> {json.dumps(dep)};")
                print("}")
        return 0
    except (RepositoryError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
