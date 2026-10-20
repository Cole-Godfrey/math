"""derive the layered dependency atlas drawn by the explorer graph.

the atlas shows selected theorems, definitions and structures. auxiliary and
generated declarations stay hidden, and every edge passes through hidden
declarations to the nearest shown prerequisite, so each drawn edge is an exact
dependency. foundations (axioms and quotient primitives) form the bottom row.
"""

from __future__ import annotations

import re
from collections import Counter

from .core import require
from .explore import KnowledgeGraph

ROOT = "mathematics"
FOUNDATION_KINDS = {"axiom", "quotient_primitive"}
SHOWN_KINDS = {"theorem", "definition", "inductive", "opaque"}
GENERATED = {"casesOn", "recOn", "rec", "below", "brecOn", "binductionOn", "ibelow", "noConfusion",
             "noConfusionType", "sizeOf_spec", "injEq", "inj", "congr_simp", "ctorIdx", "toCtorIdx",
             "ctorElim", "ctorElimType", "eq_def", "eq_unfold", "induct", "mutual_induct"}
GENERATED_PATTERN = re.compile(r"^(eq|match|proof|fun|unfold)_\d+$")


def auxiliary(name: str) -> bool:
    """recognize compiler-generated and private helper declarations."""
    if "._@." in name or "_hyg" in name:
        return True
    parts = name.split(".")
    return (any(part.startswith("_") for part in parts) or parts[-1] in GENERATED
            or GENERATED_PATTERN.match(parts[-1]) is not None)


def components(nodes, successors) -> list[list[int]]:
    """return strongly connected components with prerequisites first (iterative tarjan)."""
    index, low, active, stack, result = {}, {}, set(), [], []
    for start in nodes:
        if start in index:
            continue
        index[start] = low[start] = len(index)
        stack.append(start)
        active.add(start)
        work = [(start, iter(successors[start]))]
        while work:
            node, children = work[-1]
            child = next(children, None)
            if child is not None:
                if child not in index:
                    index[child] = low[child] = len(index)
                    stack.append(child)
                    active.add(child)
                    work.append((child, iter(successors[child])))
                elif child in active:
                    low[node] = min(low[node], index[child])
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])
            if low[node] == index[node]:
                component = []
                while True:
                    member = stack.pop()
                    active.discard(member)
                    component.append(member)
                    if member == node:
                        break
                result.append(sorted(component))
    return result


class Atlas:
    """group shown declarations by subject and module, with projected dependencies."""

    def __init__(self, graph: KnowledgeGraph):
        self.subjects = graph.subjects
        policy = graph.catalog.get("module_policy", {})
        self.module_titles = {name: info.get("title") or name for name, info in policy.items()}
        depth = {}
        for subject in self.subjects:
            chain, current = 0, self.subjects[subject]["parent"]
            while current is not None:
                chain, current = chain + 1, self.subjects[current]["parent"]
            depth[subject] = chain
        # a module listed by several subjects lives under the most specific one.
        self.module_subject = {}
        for subject in sorted(self.subjects, key=lambda item: (-depth[item], item)):
            for module in self.subjects[subject]["modules"]:
                self.module_subject.setdefault(module, subject)
        self.names = sorted(graph.nodes)
        self.position = {name: index for index, name in enumerate(self.names)}
        self.kinds = [graph.nodes[name]["kind"] for name in self.names]
        selecting = {}
        for module, members in graph.module_roots.items():
            if module in self.module_subject:
                for name in members:
                    selecting.setdefault(name, []).append(module)
        self.home = {}
        for name, modules in selecting.items():
            if graph.nodes[name]["kind"] in SHOWN_KINDS and not auxiliary(name):
                defining = graph.nodes[name]["module"]
                self.home[self.position[name]] = defining if defining in modules else min(modules)
        self.foundations = sorted((self.position[name] for name, node in graph.nodes.items()
                                   if node["kind"] in FOUNDATION_KINDS),
                                  key=lambda item: (self.kinds[item] != "axiom", self.names[item]))
        visible = set(self.foundations) | set(self.home)
        dependencies = [[self.position[item] for item in graph.edges[name]] for name in self.names]
        # hidden declarations pass their nearest shown prerequisites upward.
        nearest: list[frozenset] = [frozenset()] * len(self.names)
        shared: dict[frozenset, frozenset] = {}
        hidden = [[] if item in visible else [target for target in dependencies[item] if target not in visible]
                  for item in range(len(self.names))]
        for component in components(range(len(self.names)), hidden):
            if component[0] in visible:
                continue
            members, reached = set(component), set()
            for member in component:
                for target in dependencies[member]:
                    if target in visible:
                        reached.add(target)
                    elif target not in members:
                        reached |= nearest[target]
            value = shared.setdefault(frozenset(reached), frozenset(reached))
            for member in component:
                nearest[member] = value
        self.prerequisites = {}
        for unit in self.home:
            reached = set()
            for target in dependencies[unit]:
                if target in visible:
                    reached.add(target)
                else:
                    reached |= nearest[target]
            reached.discard(unit)
            self.prerequisites[unit] = sorted(reached)
        self.module_units: dict[str, list[int]] = {}
        for unit, module in sorted(self.home.items()):
            self.module_units.setdefault(module, []).append(unit)
        self.subject_children = {subject: [] for subject in self.subjects}
        for subject, info in sorted(self.subjects.items(), key=lambda item: item[1]["title"].casefold()):
            if info["parent"] is not None:
                self.subject_children[info["parent"]].append(subject)
        self.subject_modules = {subject: [] for subject in self.subjects}
        for module, subject in sorted(self.module_subject.items(), key=lambda item: self.title("m:" + item[0]).casefold()):
            if module in self.module_units:
                self.subject_modules[subject].append(module)
        self.paths = {}
        for subject in self.subjects:
            chain, current = [], subject
            while current is not None:
                chain.append("s:" + current)
                current = self.subjects[current]["parent"]
            self.paths["s:" + subject] = tuple(reversed(chain))
        for module, subject in self.module_subject.items():
            self.paths["m:" + module] = self.paths["s:" + subject] + ("m:" + module,)
        self.unit_paths = {unit: self.paths["m:" + module] for unit, module in self.home.items()}
        foundation_set = set(self.foundations)
        self.units, self.theorems, self.foundation_use = {}, {}, {}
        for key in self.paths:
            units = self.collect(key)
            self.units[key] = units
            self.theorems[key] = sum(self.kinds[unit] == "theorem" for unit in units)
            self.foundation_use[key] = {target for unit in units for target in self.prerequisites[unit]
                                        if target in foundation_set}

    def collect(self, key: str) -> list[int]:
        if key.startswith("m:"):
            return self.module_units.get(key[2:], [])
        subject = key[2:]
        result = []
        for child in self.subject_children[subject]:
            result.extend(self.collect("s:" + child))
        for module in self.subject_modules[subject]:
            result.extend(self.module_units[module])
        return result

    def title(self, key: str) -> str:
        if key.startswith("s:"):
            return self.subjects[key[2:]]["title"]
        if key.startswith("m:"):
            return self.module_titles.get(key[2:], key[2:])
        return key[2:]

    def summary(self, key: str) -> dict:
        return {"id": key, "title": self.title(key), "units": len(self.units[key]), "theorems": self.theorems[key]}

    def node(self, key: str, role: str, level: int) -> dict:
        if key.startswith("d:"):
            return {"id": key, "title": key[2:], "kind": self.kinds[self.position[key[2:]]], "role": role, "level": level}
        result = {**self.summary(key), "kind": "module" if key.startswith("m:") else "subject", "role": role, "level": level}
        if key.startswith("m:"):
            result["module"] = key[2:]
        return result

    def view(self, key: str = "") -> dict:
        """lay one level of the atlas out by exact prerequisite depth."""
        focus = None
        key = key or "s:" + ROOT
        if key.startswith("d:"):
            unit = self.position.get(key[2:])
            require(unit is not None, f"unknown declaration: {key[2:]}")
            require(unit in self.home or unit in self.foundations, "this declaration is not drawn in the graph")
            focus, key = key, "m:" + self.home[unit] if unit in self.home else "s:" + ROOT
        require(key in self.paths and bool(self.units[key]), "unknown graph node")
        path = self.paths[key]
        if key.startswith("m:"):
            children = ["d:" + self.names[unit] for unit in self.units[key]]
            member = {unit: index for index, unit in enumerate(self.units[key])}
        else:
            subject = key[2:]
            children = ["s:" + item for item in self.subject_children[subject] if self.units["s:" + item]]
            children += ["m:" + item for item in self.subject_modules[subject]]
            member = {unit: index for index, child in enumerate(children) for unit in self.units[child]}
        foundation_index = {unit: index for index, unit in enumerate(self.foundations)}
        group_index: dict[str, int] = {}
        # weights count the declaration-level edges behind each drawn edge.
        weights: list[Counter] = [Counter() for _ in children]
        outside: list[Counter] = [Counter() for _ in children]
        bottom: list[Counter] = [Counter() for _ in children]
        for unit, child in member.items():
            for target in self.prerequisites[unit]:
                if target in foundation_index:
                    bottom[child][foundation_index[target]] += 1
                elif target in member:
                    if member[target] != child:
                        weights[child][member[target]] += 1
                else:
                    # an outside prerequisite is grouped under the branch it shares with this view.
                    other = self.unit_paths[target]
                    shared = 0
                    while shared < len(path) and other[shared] == path[shared]:
                        shared += 1
                    outside[child][group_index.setdefault(other[shared], len(group_index))] += 1
        externals = sorted(group_index, key=lambda item: self.title(item).casefold())
        renumber = {group_index[item]: index for index, item in enumerate(externals)}
        outside = [Counter({renumber[item]: count for item, count in edges.items()}) for edges in outside]
        backward = set()
        for group in components(range(len(children)), [sorted(edges) for edges in weights]):
            if len(group) > 1:
                backward |= cyclic_order(group, weights)
        forward = [[target for target in weights[child] if (child, target) not in backward] for child in range(len(children))]
        base = 2 if externals else 1
        level = [0] * len(children)
        for child in topological(forward):
            level[child] = max([base] + [level[target] + 1 for target in forward[child]])
        first_external = len(children)
        first_foundation = first_external + len(externals)
        reach = [0] * len(children)
        external_reach = []
        for item in externals:
            bits = 0
            for target in self.foundation_use[item]:
                bits |= 1 << (first_foundation + foundation_index[target])
            external_reach.append(bits)
        drawn = set()
        for child in sorted(range(len(children)), key=lambda item: level[item]):
            ordered = [(target, reach[target]) for target in sorted(forward[child], key=lambda item: -level[item])]
            ordered += [(first_external + item, external_reach[item]) for item in sorted(outside[child])]
            ordered += [(first_foundation + item, 0) for item in sorted(bottom[child])]
            # nearer targets come first, so a target already covered is implied by another path.
            covered = 0
            for target, closure in ordered:
                if not covered >> target & 1:
                    drawn.add((child, target))
                    covered |= 1 << target | closure
            reach[child] = covered
        nodes = [self.node(child, "child", level[index]) for index, child in enumerate(children)]
        nodes += [self.node(item, "external", 1) for item in externals]
        nodes += [self.node("d:" + self.names[unit], "foundation", 0) for unit in self.foundations]
        edges = []
        for child in range(len(children)):
            for target, count in weights[child].items():
                edges.append((child, target, count, 2 if (child, target) in backward else int((child, target) in drawn)))
            for item, count in outside[child].items():
                edges.append((child, first_external + item, count, int((child, first_external + item) in drawn)))
            for item, count in bottom[child].items():
                edges.append((child, first_foundation + item, count, int((child, first_foundation + item) in drawn)))
        for index, bits in enumerate(external_reach):
            for item in range(len(self.foundations)):
                if bits >> (first_foundation + item) & 1:
                    edges.append((first_external + index, first_foundation + item, 1, 1))
        used = {target for _, target, _, _ in edges}
        keep = [index for index in range(len(nodes)) if index < first_foundation or index in used]
        renumbered = {old: new for new, old in enumerate(keep)}
        return {"id": key, "title": self.title(key), "focus": focus,
                "trail": [{"id": item, "title": self.title(item)} for item in path],
                "units": len(self.units[key]), "theorems": self.theorems[key],
                "nodes": [nodes[index] for index in keep],
                "edges": sorted([renumbered[source], renumbered[target], count, flag]
                                for source, target, count, flag in edges)}


def topological(prerequisites: list[list[int]]) -> list[int]:
    """order an acyclic graph so every prerequisite precedes its dependents."""
    pending = [len(targets) for targets in prerequisites]
    dependents = [[] for _ in prerequisites]
    for node, targets in enumerate(prerequisites):
        for target in targets:
            dependents[target].append(node)
    ready = [node for node, count in enumerate(pending) if count == 0]
    result = []
    while ready:
        node = ready.pop()
        result.append(node)
        for parent in dependents[node]:
            pending[parent] -= 1
            if pending[parent] == 0:
                ready.append(parent)
    require(len(result) == len(prerequisites), "graph layering left a cycle")
    return result


def cyclic_order(group: list[int], weights: list[Counter]) -> set[tuple[int, int]]:
    """order a cyclic group so the lightest dependencies point upward; return those edges.

    small groups are ordered exactly by a subset program over the least upward
    weight; larger groups use repeated best insertion. the returned edges are
    exact dependencies that run against the layering.
    """
    nodes = sorted(group)
    size = len(nodes)
    weight = [[weights[source].get(target, 0) for target in nodes] for source in nodes]
    if size <= 12:
        # cost[subset] is the least upward weight with those members placed lowest.
        cost: list[int | None] = [None] * (1 << size)
        last = [0] * (1 << size)
        cost[0] = 0
        for subset in range(1 << size):
            if cost[subset] is None:
                continue
            for node in range(size):
                if subset >> node & 1:
                    continue
                value = cost[subset] + sum(weight[other][node] for other in range(size) if subset >> other & 1)
                grown = subset | 1 << node
                if cost[grown] is None or value < cost[grown]:
                    cost[grown], last[grown] = value, node
        order, subset = [], (1 << size) - 1
        while subset:
            order.append(last[subset])
            subset &= ~(1 << last[subset])
        order.reverse()
    else:
        order = sorted(range(size), key=lambda node: sum(weight[node]) - sum(row[node] for row in weight))
        improved = True
        while improved:
            improved = False
            for node in list(order):
                rest = [item for item in order if item != node]
                # the node's upward weight when inserted at each position of the rest.
                value = sum(weight[node][item] for item in rest)
                best, where = value, 0
                for index, item in enumerate(rest):
                    value += weight[item][node] - weight[node][item]
                    if value < best:
                        best, where = value, index + 1
                current = order.index(node)
                if where != current and best < sum(weight[item][node] for item in order[:current]) + \
                        sum(weight[node][item] for item in order[current + 1:]):
                    order = rest[:where] + [node] + rest[where:]
                    improved = True
    position = {nodes[node]: index for index, node in enumerate(order)}
    return {(source, target) for source in group for target in weights[source]
            if target in position and position[target] > position[source]}
