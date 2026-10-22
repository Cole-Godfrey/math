"use strict";

/* retain native formulas, ordered premises and scoped variable restrictions. */
window.MathNative = (() => {
  function pathLinks(names) {
    const path = element("div", null, "path");
    names.forEach((name, index) => {
      if (index) path.append(element("span", "→", "path-arrow"));
      path.append(nameLink(name));
    });
    return path;
  }

  function stepLink(name, index, text) {
    const link = element("a", text, "small-button");
    link.href = href({name, tab: "proof", step: index});
    return link;
  }

  function disjoint(body, pairs) {
    body.append(element("h3", "Disjoint variables"));
    body.append(element("pre", pairs.length ? pairs.map(pair => pair.join(" ")).join("\n")
      : "No mandatory disjoint-variable restrictions.", "native-formula"));
  }

  function premises(body, hypotheses) {
    body.append(element("h3", "Ordered hypotheses"));
    if (!hypotheses.length) {
      body.append(element("p", "No hypotheses in this assertion's frame.", "muted"));
      return;
    }
    const list = element("ol", null, "native-premises");
    for (const hypothesis of hypotheses) {
      const item = element("li");
      item.append(nameLink(hypothesis.name), element("span", kindLabels[hypothesis.kind] || hypothesis.kind, "badge"),
        element("pre", hypothesis.statement, "native-formula"));
      list.append(item);
    }
    body.append(list);
  }

  async function statement(body, node) {
    body.append(element("pre", node.statement, "statement"));
    if (node.native_kind === "Axiom") body.append(element("p", "Declared $a rule. Its use is an explicit assumption; this declaration has no proof.", "notice"));
    else if (node.bound_assumption) body.append(element("p", node.native_kind === "Floating"
      ? "Local $f typing hypothesis, used within its active source scope."
      : "Local $e hypothesis, used within its active source scope.", "notice"));
    const list = element("dl", null, "facts");
    const add = (label, value) => { const cell = element("dd"); cell.append(value); list.append(element("dt", label), cell); };
    add("Database", element("span", node.foundation.database, "mono"));
    add("Hypotheses", element("span", count(node.hypotheses.length)));
    const assumptions = element("div", null, "chip-list");
    for (const name of node.axioms.slice(0, 8)) assumptions.append(nameLink(name));
    const all = element("a", `${count(node.axioms.length)} declared rules`, "facts-more");
    all.href = href({name: node.name, tab: "foundations"});
    assumptions.append(all);
    add("Assumptions", assumptions);
    const dependencies = element("a", `${count(node.dependencies.length)} prerequisites`, "facts-more");
    dependencies.href = href({name: node.name, tab: "dependencies"});
    add("Rests on", dependencies);
    body.append(list);
    if (node.doc) body.append(element("pre", node.doc, "documentation native-documentation"));
  }

  async function proof(body, node, request, parameters) {
    const data = await api("/api/native-proof", {name: node.name, step: parameters.get("step")});
    if (request !== activeRequest) return;
    if (!data.focused) {
      body.append(element("h2", node.bound_assumption ? "Local hypothesis" : "Declared rule"),
        element("p", "This declaration has no proof steps.", "notice"), element("pre", node.statement, "statement"));
      return;
    }
    const tools = element("div", null, "section-tools");
    tools.append(element("p", "Each step applies a retained rule to its ordered arguments."),
      downloadLink("Download all steps", "/api/expressions", node.name));
    const navigation = element("form", null, "native-step-navigation");
    const previous = button("Previous", () => route({step: data.focused.index - 1}));
    previous.disabled = data.focused.index === 0;
    const next = button("Next", () => route({step: data.focused.index + 1}));
    next.disabled = data.focused.index + 1 === data.step_count;
    const label = element("label", "Step ");
    const input = element("input");
    input.type = "number"; input.min = "1"; input.max = String(data.step_count); input.step = "1";
    input.value = String(data.focused.index + 1); input.required = true;
    label.append(input, document.createTextNode(` of ${count(data.step_count)}`));
    const go = button("Go", () => {}); go.type = "submit";
    navigation.append(previous, label, go, next, stepLink(node.name, data.root, "Conclusion"));
    navigation.addEventListener("submit", event => { event.preventDefault(); if (input.checkValidity()) route({step: Number(input.value) - 1}); });
    const focused = data.focused;
    const card = element("article", null, "term-card");
    card.append(element("h2", `Step ${count(focused.index + 1)}`), nameLink(focused.reference),
      element("pre", focused.expression_tokens.join(" "), "native-formula"));
    const children = element("div", null, "term-children");
    data.arguments.forEach((argument, index) => {
      const row = element("div", null, "term-child");
      row.append(stepLink(node.name, argument.index, `Argument ${index + 1} · step ${argument.index + 1}`),
        element("pre", argument.expression_tokens.join(" "), "native-formula"));
      children.append(row);
    });
    if (!data.arguments.length) children.append(element("p", "This step is a hypothesis or a rule with no arguments.", "muted"));
    card.append(children);
    body.append(tools, navigation, card);
    const context = element("section", null, "term-context");
    context.append(element("h3", "Active proof hypotheses"));
    if (!data.context.length) context.append(element("p", "No local hypotheses.", "muted"));
    const list = element("ol", null, "native-premises");
    for (const binding of data.context) {
      const row = element("li");
      row.append(nameLink(binding.name), element("span", `${binding.kind === "Floating" ? "Typing" : "Essential"} · ${binding.mandatory ? "assertion frame" : "proof-local"}`, "badge"),
        element("pre", binding.expression_tokens.join(" "), "native-formula"));
      list.append(row);
    }
    context.append(list);
    disjoint(context, data.frame.proof_disjoint);
    const exact = element("details", null, "term-exact");
    exact.append(element("summary", "Exact step and assertion frame"),
      element("pre", JSON.stringify({focused, frame: data.frame, context: data.context}, null, 2), "proof-code"));
    const source = element("details", null, "term-preview");
    source.append(element("summary", "Original proof tokens"), element("pre", data.proof_tokens.join(" "), "proof-code"));
    body.append(context, exact, source);
  }

  async function foundations(body, node, request) {
    let pageRequest = 0;
    let frameLoaded = false;
    const rules = element("div");
    const pages = element("div", null, "pagination");
    const introduction = element("section", null, "native-frame");
    introduction.append(element("h2", node.bound_assumption ? "Local source scope" : "Assertion frame"),
      element("p", node.bound_assumption ? "Local typing and essential hypotheses apply within their original source scopes."
        : "Local hypotheses and variable restrictions are part of the assertion.", "muted"));
    if (node.bound_assumption) introduction.append(element("pre", node.statement, "native-formula"), sourceLink(node));
    const ruleSection = element("section", null, "native-foundations");
    ruleSection.append(element("h2", "Declared rules"), element("p", "Every $a dependency remains an assumption, including syntax rules and definitions.", "muted"), rules, pages);
    ruleSection.hidden = node.bound_assumption;
    const layout = element("div", null, node.bound_assumption ? "native-local-scope" : "native-foundations-layout");
    layout.append(introduction, ruleSection);
    body.append(layout);
    async function load(offset = 0) {
      const current = ++pageRequest;
      const data = await api("/api/native-foundations", {name: node.name, offset, limit: 30});
      if (request !== activeRequest || current !== pageRequest) return;
      if (!frameLoaded) {
        frameLoaded = true;
        if (!node.bound_assumption) {
          premises(introduction, data.hypotheses);
          disjoint(introduction, data.disjoint);
        }
        const calculus = element("details");
        const list = element("ul", null, "kernel-rules");
        for (const rule of data.foundation.rules) list.append(element("li", rule));
        calculus.append(element("summary", "Substitution calculus"), list, externalLink("Metamath reference ↗", data.foundation.reference));
        introduction.append(calculus);
      }
      rules.replaceChildren(element("p", `${count(data.total)} declared rules in the complete dependency chain`, "muted"));
      for (const rule of data.items) {
        const card = element("section", null, "foundation-card");
        const heading = element("h3"); heading.append(nameLink(rule.name));
        card.append(heading, element("pre", rule.statement, "native-formula"),
          element("div", "Dependency path", "path-heading"), pathLinks(rule.path));
        rules.append(card);
      }
      pageButtons(pages, data.total, data.offset, data.limit, offset => load(offset).catch(error => status(error.message, true)));
    }
    await load();
  }

  async function source(body, node, request) {
    const tools = element("div", null, "section-tools");
    const download = downloadLink("Download complete database", "/api/native-source", node.name);
    download.download = node.foundation.database;
    tools.append(element("p", "Original source retained with the verified snapshot."), sourceLink(node), download);
    const content = element("div", null, "source-code native-source");
    const metadata = element("p", null, "source-meta");
    const pages = element("div", null, "pagination");
    const jump = element("form", null, "native-step-navigation");
    const label = element("label", "Line ");
    const input = element("input"); input.type = "number"; input.min = "1"; input.step = "1"; input.required = true;
    label.append(input);
    const go = button("Go", () => {}); go.type = "submit";
    jump.append(label, go, button("Declaration", () => load().catch(error => status(error.message, true))));
    body.append(tools, jump, content, pages, metadata);
    let pageRequest = 0;
    async function load(line = null) {
      const current = ++pageRequest;
      const data = await api("/api/source", {name: node.name, line});
      if (request !== activeRequest || current !== pageRequest) return;
      content.replaceChildren();
      data.lines.forEach((text, index) => {
        const number = data.start_line + index;
        const row = element("div", null, "source-line");
        if (number >= data.declaration_range.line && number <= data.declaration_range.end_line) row.classList.add("highlight");
        row.append(element("span", number, "line-number"), element("span", text, "source-text"));
        content.append(row);
      });
      input.max = String(data.total_lines); input.value = String(data.start_line);
      metadata.textContent = `${data.module} · ${count(data.total_lines)} lines · SHA-256 ${data.sha256}`;
      const previous = button("Previous", () => load(data.previous_line).catch(error => status(error.message, true)));
      previous.disabled = data.previous_line === null;
      const next = button("Next", () => load(data.next_line).catch(error => status(error.message, true)));
      next.disabled = data.next_line === null;
      pages.replaceChildren(element("span", `Lines ${count(data.start_line)}–${count(data.start_line + data.lines.length - 1)} of ${count(data.total_lines)}`, "page-range"), previous, next);
    }
    jump.addEventListener("submit", event => { event.preventDefault(); if (input.checkValidity()) load(Number(input.value)).catch(error => status(error.message, true)); });
    await load();
  }

  async function references(body, node, request) {
    const data = await api("/api/citations", {name: node.name});
    if (request !== activeRequest) return;
    body.append(element("h2", "Source documentation"), sourceLink(node));
    if (data.declaration_doc) body.append(element("pre", data.declaration_doc, "documentation native-documentation"));
    else body.append(element("p", "No documentation comment precedes this declaration.", "muted"));
  }

  return {statement, proof, foundations, source, references};
})();
