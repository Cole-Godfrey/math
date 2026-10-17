"""read complete verified artifacts when a query snapshot was not retained."""

from pathlib import Path

from .build import load_catalog
from .core import canonical_chunks, declaration_expressions, expression_names, require
from .explore import KnowledgeGraph


def catalog_statistics(catalog: dict) -> dict:
    nodes = {node["name"]: node for node in catalog["declarations"]}
    roots = [nodes[name] for name in catalog["roots"]]
    return {"selected": len(roots), "declarations": len(nodes),
            "local": sum(node["module"] in catalog["local_modules"] for node in roots),
            "theorems": sum(node["kind"] == "theorem" for node in roots),
            "documented": sum(bool(node["doc"]) for node in roots),
            "axiom_free": sum(not node["axioms"] for node in roots),
            "lean_version": catalog["lean_version"], "subject_modules": len(catalog["module_policy"]) - 1}


class CatalogSnapshot:
    """retain the complete artifact reader for catalogs without a query receipt."""

    def __init__(self, root: Path):
        self.metadata = load_catalog(root)
        self.graph = KnowledgeGraph(self.metadata)
        self.proof_path = root / "build" / f"proofs-{self.metadata['provenance']['proof_export_digest']}.jsonl"

    def statistics(self):
        return catalog_statistics(self.metadata)

    def iter_search(self, query="", subject=None, include_dependencies=False, kind=None, axiom_free=False, module=None):
        yield from self.graph.search(query, subject, include_dependencies, module, kind, axiom_free)

    def declaration(self, name, proof=False):
        require(name in self.graph.nodes, f"unknown declaration: {name}")
        record = dict(self.graph.nodes[name])
        if not proof:
            record.pop("proof", None)
        return {**record, "origin": self.metadata.get("sources", {}).get(record["module"], {})}

    def expressions(self, name):
        node = self.declaration(name)
        expressions = declaration_expressions(self.metadata, node)
        names = expression_names(node, expressions.values())
        return {"expressions": expressions, "name_data": {name: self.metadata["name_data"][name] for name in names}}

    def dependency_names(self, name, reverse=False, transitive=False):
        require(name in self.graph.nodes, f"unknown declaration: {name}")
        edges = self.graph.edges
        if reverse:
            edges = {name: set() for name in self.graph.nodes}
            for source, targets in self.graph.edges.items():
                for target in targets:
                    edges[target].add(source)
        reached, pending = set(), list(edges[name])
        while pending:
            child = pending.pop()
            if child not in reached:
                reached.add(child)
                if transitive:
                    pending.extend(edges[child])
        yield from sorted(reached - {name})

    def iter_edges(self):
        for name in sorted(self.graph.nodes):
            for dependency in sorted(self.graph.edges[name]):
                yield name, dependency

    def catalog_chunks(self):
        yield from canonical_chunks(self.metadata)
        yield b"\n"
