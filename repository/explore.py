"""explore subjects and complete logical dependency hierarchies."""

from __future__ import annotations

from collections import Counter
import heapq

from .core import dependency_path, require, selected_module_roots


class KnowledgeGraph:
    def __init__(self, catalog: dict):
        self.catalog = catalog
        self.nodes = {node["name"]: node for node in catalog["declarations"]}
        self.roots = set(catalog["roots"])
        self.edges = {name: set(node["dependencies"]) for name, node in self.nodes.items()}
        self.subjects = catalog.get("subjects", {})
        self.module_roots = selected_module_roots(catalog)

    def closure(self, names: set[str]) -> set[str]:
        require(names <= self.nodes.keys(), "unknown declaration in dependency query")
        reached = set()
        pending = list(names)
        while pending:
            name = pending.pop()
            if name not in reached:
                reached.add(name)
                pending.extend(self.edges[name])
        return reached

    def subject_modules(self, subject: str) -> set[str]:
        require(subject in self.subjects, f"unknown subject: {subject}")
        modules = set()
        pending = [subject]
        while pending:
            current = pending.pop()
            modules.update(self.subjects[current]["modules"])
            pending.extend(name for name, info in self.subjects.items() if info["parent"] == current)
        return modules

    def subject_coverage(self) -> list[dict]:
        result = []
        for name, subject in sorted(self.subjects.items()):
            modules = self.subject_modules(name)
            roots = set().union(*(self.module_roots.get(module, set()) for module in modules))
            closure = self.closure(roots)
            result.append({
                "id": name, "title": subject["title"], "parent": subject["parent"],
                "modules": sorted(modules), "selected_declarations": len(roots),
                "dependency_declarations": len(closure),
                "theorems": sum(self.nodes[n]["kind"] == "theorem" for n in roots),
                "axioms": sorted({axiom for n in roots for axiom in self.nodes[n]["axioms"]}),
            })
        return result

    def search(self, query: str = "", subject: str | None = None, include_dependencies: bool = False,
               module: str | None = None, kind: str | None = None, axiom_free: bool = False) -> list[dict]:
        eligible = set(self.nodes) if include_dependencies else self.roots.copy()
        if subject:
            modules = self.subject_modules(subject)
            selected = set().union(*(self.module_roots.get(module, set()) for module in modules))
            eligible &= self.closure(selected) if include_dependencies else selected
        terms = query.casefold().split()
        result = []
        for name in sorted(eligible):
            node = self.nodes[name]
            text = " ".join([name, node["statement"], node["doc"] or ""]).casefold()
            if (all(term in text for term in terms)
                    and (not module or node["module"] == module or name in self.module_roots.get(module, set()))
                    and (not kind or node["kind"] == kind)
                    and (not axiom_free or not node["axioms"])):
                result.append(node)
        def relevance(node: dict) -> tuple:
            name = node["name"]
            documentation = (node["doc"] or "").casefold()
            return (name.casefold() != query.strip().casefold(), name.startswith("_private."),
                    -sum(term in documentation for term in terms), name)

        return sorted(result, key=relevance)

    def hierarchy(self, name: str) -> dict:
        """collapse inductive cycles into groups and order every prerequisite first."""
        require(name in self.nodes, f"unknown declaration: {name}")
        closure = self.closure({name})
        parents = {node: set() for node in closure}
        for node in closure:
            for dependency in self.edges[node]:
                parents[dependency].add(node)
        visited = set()
        finished = []
        for start in sorted(closure):
            if start in visited:
                continue
            visited.add(start)
            stack = [(start, iter(sorted(self.edges[start])))]
            while stack:
                node, children = stack[-1]
                child = next(children, None)
                if child is None:
                    finished.append(node)
                    stack.pop()
                elif child not in visited:
                    visited.add(child)
                    stack.append((child, iter(sorted(self.edges[child]))))
        visited.clear()
        components = []
        for start in reversed(finished):
            if start in visited:
                continue
            component = set()
            pending = [start]
            while pending:
                node = pending.pop()
                if node in visited:
                    continue
                visited.add(node)
                component.add(node)
                pending.extend(parents[node] - visited)
            components.append(sorted(component))
        components.sort()
        owner = {member: index for index, members in enumerate(components) for member in members}
        dependencies = [set() for _ in components]
        dependents = [set() for _ in components]
        for node in closure:
            source = owner[node]
            for dependency in self.edges[node]:
                target = owner[dependency]
                if source != target:
                    dependencies[source].add(target)
                    dependents[target].add(source)
        remaining = [len(items) for items in dependencies]
        ready = [index for index, count in enumerate(remaining) if count == 0]
        heapq.heapify(ready)
        levels = [0] * len(components)
        order = []
        while ready:
            index = heapq.heappop(ready)
            order.append(index)
            for parent in sorted(dependents[index]):
                levels[parent] = max(levels[parent], levels[index] + 1)
                remaining[parent] -= 1
                if remaining[parent] == 0:
                    heapq.heappush(ready, parent)
        require(len(order) == len(components), "dependency groups still contain a cycle")
        groups = [{
            "id": index, "members": components[index], "level": levels[index],
            "dependencies": sorted(dependencies[index]),
            "cyclic": len(components[index]) > 1 or any(n in self.edges[n] for n in components[index]),
        } for index in order]
        edges = []
        for source in sorted(closure):
            node = self.nodes[source]
            roles = {"type": set(node["type_dependencies"]), "value": set(node["value_dependencies"]),
                     "structure": set(node["structural_dependencies"])}
            for target in sorted(self.edges[source]):
                edges.append({"from": source, "to": target,
                              "roles": [role for role, dependencies in roles.items() if target in dependencies]})
        return {
            "declaration": name, "foundation": self.catalog["foundation"],
            "axioms": self.nodes[name]["axioms"],
            "axiom_paths": {axiom: dependency_path(self.nodes, name, axiom)
                            for axiom in sorted(self.nodes[name]["axioms"])},
            "groups": groups, "edges": edges,
            "declarations": [{"name": node, "kind": self.nodes[node]["kind"],
                              "module": self.nodes[node]["module"], "group": owner[node]}
                             for node in sorted(closure)],
            "levels": [{"level": level, "groups": count} for level, count in sorted(Counter(levels).items())],
            "kinds": dict(sorted(Counter(self.nodes[n]["kind"] for n in closure).items())),
        }
