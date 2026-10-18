"""inspect exact subterms with the binder context of a declaration occurrence."""

from __future__ import annotations

from .core import CHILD_FIELDS, require


PATH_FIELDS = {"t": "type", "b": "body", "f": "function", "a": "argument",
               "v": "value", "e": "expression"}
FIELD_PATHS = {field: step for step, field in PATH_FIELDS.items()}


def inspect_term(node: dict, read, root: str = "value", path: str = "", rule: int | None = None) -> dict:
    """follow an occurrence path without loading unrelated proof expressions."""
    require(isinstance(path, str) and all(step in PATH_FIELDS for step in path), "invalid term path")
    require(root in {"type", "value", "rule"}, "unknown term root")
    require(rule is None or root == "rule", "rule index requires a reduction rule root")
    roots = [{"root": "type", "rule": None, "id": node["type"], "label": "Statement"}]
    if node["value"] is not None:
        roots.append({"root": "value", "rule": None, "id": node["value"],
                      "label": "Proof" if node["kind"] == "theorem" else "Definition"})
    if node["kind"] == "recursor":
        roots.extend({"root": "rule", "rule": index, "id": item["rhs"],
                      "label": "Reduction for " + item["constructor"]}
                     for index, item in enumerate(node["structure"]["rules"]))
    require(root != "rule" or type(rule) is int and rule >= 0, "invalid reduction rule index")
    selected = next((item for item in roots if item["root"] == root and item["rule"] == rule), None)
    require(selected is not None, "term root is unavailable for this declaration")
    current = selected["id"]
    context, ancestors = [], []
    for depth, step in enumerate(path):
        expression = read(current)
        tag, field = expression["tag"], PATH_FIELDS[step]
        require(field in CHILD_FIELDS.get(tag, ()), f"invalid term path at step {depth + 1}: {tag} has no {field}")
        if field == "body" and tag in {"lam", "forall", "let"}:
            context.append({"name": expression["name"], "kind": tag, "depth": depth,
                            "type": expression["type"], "value": expression.get("value"),
                            "binder": expression.get("binder")})
        ancestors.append({"id": current, "tag": tag, "field": field, "step": step})
        current = expression[field]
    expression = read(current)

    def child(identifier, child_path, field):
        item = read(identifier)
        result = {"id": identifier, "tag": item["tag"], "digest": item["digest"],
                  "path": child_path, "field": field}
        for key in ("name", "index", "level", "levels"):
            if key in item:
                result[key] = item[key]
        if item["tag"] in {"nat", "string"}:
            result["literal"] = str(item["value"]) if item["tag"] == "nat" else item["value"]
        if item["tag"] == "bvar":
            require(item["index"] < len(context), "unbound variable in stored term")
            result["binding"] = context[-1 - item["index"]]
        return result

    children = []
    for field in CHILD_FIELDS.get(expression["tag"], ()):
        # a binder body has one more local variable than its other children.
        target = read(expression[field])
        if target["tag"] == "bvar" and field == "body" and expression["tag"] in {"lam", "forall", "let"}:
            binding = {"name": expression["name"], "kind": expression["tag"], "depth": len(path),
                       "type": expression["type"], "value": expression.get("value"),
                       "binder": expression.get("binder")}
            context.append(binding)
            children.append(child(expression[field], path + FIELD_PATHS[field], field))
            context.pop()
        else:
            children.append(child(expression[field], path + FIELD_PATHS[field], field))
    application = None
    if expression["tag"] == "app":
        head, head_path, arguments = current, path, []
        while read(head)["tag"] == "app":
            item = read(head)
            arguments.append(child(item["argument"], head_path + "a", "argument"))
            head, head_path = item["function"], head_path + "f"
        application = {"function": child(head, head_path, "function"), "arguments": list(reversed(arguments))}
    for index, binding in enumerate(context):
        binding["index"] = len(context) - index - 1
    binding = None
    if expression["tag"] == "bvar":
        require(expression["index"] < len(context), "unbound variable in stored term")
        binding = context[-1 - expression["index"]]
    focused = {"id": current, **expression}
    if expression["tag"] == "nat":
        focused["value"] = str(expression["value"])
    return {"declaration": node["name"], "root": root, "rule": rule, "path": path,
            "roots": roots, "expression": focused, "children": children,
            "context": context, "binding": binding, "ancestors": ancestors, "application": application,
            "universes": node["universes"]}
