"use strict";

const $ = id => document.getElementById(id);
const tabs = ["Statement", "Proof", "Dependencies", "Foundations", "Hierarchy", "References", "Source"];
const views = ["home", "search", "detail", "graph", "guide"];
const graphKinds = new Set(["theorem", "definition", "inductive", "opaque", "axiom", "quotient_primitive"]);
const kindLabels = {theorem: "Theorem", definition: "Definition", inductive: "Structure", axiom: "Axiom",
  constructor: "Constructor", recursor: "Recursor", opaque: "Opaque", quotient_primitive: "Quotient primitive"};
let summary = null;
let bibliographyKeys = new Set();
let activeRequest = 0;
let searchTimer;
let ringStarted = false;

function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined && text !== null) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function formatted(node, text, declaration = null) {
  for (const part of text.split(/(`[^`]+`|\*\*[^*]+\*\*|\[[^\]]+\]\(https?:\/\/[^\s)]+\)|\[[^\]]+\]\[[A-Za-z0-9_:-]+\]|\[[A-Za-z0-9_:-]+\](?!\())/g)) {
    if (part.startsWith("`")) node.append(element("code", part.slice(1, -1)));
    else if (part.startsWith("**")) node.append(element("strong", part.slice(2, -2)));
    else if (part.startsWith("[")) {
      const match = part.match(/^\[([^\]]+)\]\((https?:\/\/[^)]+)\)$/);
      const citation = part.match(/^\[([^\]]+)\](?:\[([A-Za-z0-9_:-]+)\])?$/);
      const key = citation && (citation[2] || citation[1]);
      if (match) node.append(externalLink(match[1], match[2]));
      else if (declaration && bibliographyKeys.has(key)) {
        const link = nameLink(declaration, "reference-link");
        link.textContent = citation[2] ? citation[1] : part;
        const parameters = new URLSearchParams(link.hash.slice(1));
        parameters.set("tab", "references"); parameters.set("reference", key);
        link.hash = parameters.toString();
        node.append(link);
      } else node.append(document.createTextNode(part));
    } else node.append(document.createTextNode(part));
  }
  return node;
}

/** merge a patch into the current location. */
function route(patch) {
  const parameters = new URLSearchParams(location.hash.slice(1));
  for (const [key, value] of Object.entries(patch)) {
    if (value === null || value === "" || value === undefined) parameters.delete(key);
    else parameters.set(key, String(value));
  }
  location.hash = parameters.toString();
}

/** build a fresh location from only these parameters. */
function href(values) {
  const parameters = new URLSearchParams();
  for (const [key, value] of Object.entries(values)) {
    if (value !== null && value !== "" && value !== undefined) parameters.set(key, String(value));
  }
  return "#" + parameters.toString();
}

function nameLink(name, className = "node-chip") {
  const link = element("a", name, className);
  link.href = href({name, tab: "statement"});
  return link;
}

function externalLink(text, url) {
  let target;
  try { target = new URL(url, location.origin); }
  catch { return element("span", text); }
  if (!["https:", "http:"].includes(target.protocol)) return element("span", text);
  const link = element("a", text);
  link.href = target.href;
  link.target = "_blank";
  link.rel = "noopener noreferrer";
  return link;
}

function button(text, action, className = "small-button") {
  const node = element("button", text, className);
  node.type = "button";
  node.addEventListener("click", action);
  return node;
}

function status(text = "", error = false) {
  $("status").textContent = text;
  $("status").classList.toggle("error", error);
}

function count(value) {
  return Number(value || 0).toLocaleString();
}

async function api(path, parameters = {}, options = {}) {
  if (summary && path !== "/api/summary" && path !== "/api/reload") {
    parameters = {...parameters, snapshot: summary.catalog_digest};
  }
  const query = new URLSearchParams(Object.entries(parameters).filter(([, value]) => value !== undefined && value !== null));
  const response = await fetch(path + (query.size ? "?" + query : ""), options);
  const value = await response.json();
  if (!response.ok) throw new Error(value.error || "The request could not be completed.");
  const digest = response.headers.get("X-Math-Snapshot");
  if (summary && digest && digest !== summary.catalog_digest && path !== "/api/summary" && path !== "/api/reload") {
    throw new Error("The snapshot changed. Refresh the explorer to continue.");
  }
  return value;
}

function pageButtons(container, total, offset, limit, change) {
  container.replaceChildren();
  if (total <= limit) return;
  const previous = button("Previous", () => change(Math.max(0, offset - limit)));
  previous.disabled = offset === 0;
  const next = button("Next", () => change(offset + limit));
  next.disabled = offset + limit >= total;
  container.append(element("span", `${count(offset + 1)}–${count(Math.min(offset + limit, total))} of ${count(total)}`, "page-range"), previous, next);
}

function showView(name) {
  for (const view of views) $(view + "-view").hidden = view !== name;
  document.body.dataset.view = name;
  const section = name === "search" || name === "detail" ? "browse" : name;
  for (const link of document.querySelectorAll("[data-nav]")) {
    const current = link.dataset.nav === section;
    link.classList.toggle("active", current);
    if (current) link.setAttribute("aria-current", "page");
    else link.removeAttribute("aria-current");
  }
}

/* home */

function percentText(value, decimals) {
  return value.toLocaleString(undefined, {minimumFractionDigits: decimals, maximumFractionDigits: decimals}) + "%";
}

/** fill the ring clockwise to the recorded share of mathematics, once per visit. */
async function renderRing() {
  if (ringStarted) return;
  ringStarted = true;
  let percent = 0;
  try {
    const response = await fetch("/progress.json", {cache: "no-store"});
    percent = Number((await response.json()).percent);
  } catch { percent = NaN; }
  const number = $("ring-number");
  const arc = $("ring-value");
  if (!Number.isFinite(percent)) { number.textContent = "–"; return; }
  const target = Math.min(100, Math.max(0, percent));
  const decimals = Math.min(2, (String(percent).split(".")[1] || "").length);
  const final = () => {
    arc.style.strokeDasharray = `${target} 100`;
    number.textContent = percentText(target, decimals);
  };
  if (matchMedia("(prefers-reduced-motion: reduce)").matches) {
    $("ring").classList.add("ring-done");
    final();
    return;
  }
  const ring = $("ring");
  ring.classList.remove("ring-done");
  ring.classList.add("ring-drawing");
  const started = performance.now();
  const duration = 1800;
  function frame(now) {
    const progress = Math.min(1, (now - started) / duration);
    const eased = 1 - Math.pow(1 - progress, 4);
    arc.style.strokeDasharray = `${target * eased} 100`;
    number.textContent = percentText(target * eased, decimals);
    if (progress < 1) requestAnimationFrame(frame);
    else { final(); ring.classList.add("ring-done"); }
  }
  requestAnimationFrame(frame);
}

function subjectLink(subject, className) {
  const link = element("a", null, className);
  link.href = href({view: "browse", subject: subject.id});
  link.append(element("span", subject.title, "label"), element("span", count(subject.selected_declarations), "num"));
  return link;
}

function renderHome() {
  showView("home");
  renderRing();
  const checker = (summary.checkers[1] || "").replace("nanoda_bin", "nanoda");
  const facts = $("home-facts");
  facts.replaceChildren(
    element("span", `${count(summary.declarations)} declarations checked by Lean ${summary.lean_version}${checker ? " and " + checker : ""}`));
  const graph = element("a", "Dependency graph", "facts-link");
  graph.href = href({view: "graph"});
  facts.append(graph);
  const children = new Map();
  for (const subject of summary.subjects) {
    if (!children.has(subject.parent)) children.set(subject.parent, []);
    children.get(subject.parent).push(subject);
  }
  const byTitle = (a, b) => a.title.localeCompare(b.title);
  const areas = $("areas");
  areas.replaceChildren();
  for (const area of (children.get("mathematics") || []).sort(byTitle)) {
    const block = element("section", null, "area");
    const heading = element("h3");
    heading.append(subjectLink(area, "area-title"));
    block.append(heading);
    const list = element("ul");
    for (const child of (children.get(area.id) || []).sort(byTitle)) {
      const item = element("li");
      item.append(subjectLink(child, "area-link"));
      list.append(item);
    }
    if (list.children.length) block.append(list);
    areas.append(block);
  }
  const axioms = $("axioms");
  axioms.replaceChildren();
  for (const [name, info] of Object.entries(summary.axiom_policy).sort()) {
    const item = element("li");
    item.append(nameLink(name, "axiom-name"), element("span", info.description, "axiom-text"));
    axioms.append(item);
  }
}

/* browse */

function renderSubjects(selected) {
  const list = $("subjects");
  list.replaceChildren();
  const records = new Map(summary.subjects.map(item => [item.id, item]));
  const open = new Set();
  for (let current = records.get(selected); current; current = records.get(current.parent)) open.add(current.id);
  function append(parent, depth) {
    for (const item of summary.subjects.filter(item => item.parent === parent).sort((a, b) => a.title.localeCompare(b.title))) {
      const link = subjectLink(item, `subject-link depth-${Math.min(depth, 3)}`);
      if (item.id === "mathematics") {
        link.href = href({view: "browse"});
        link.querySelector(".label").textContent = "All subjects";
      }
      const current = (selected || "mathematics") === item.id;
      link.classList.toggle("active", current);
      if (current) link.setAttribute("aria-current", "page");
      list.append(link);
      if (depth === 0 || open.has(item.id)) append(item.id, depth + 1);
    }
  }
  append(null, 0);
}

async function showSearch(parameters, request) {
  showView("search");
  const subject = summary.subjects.find(item => item.id === parameters.get("subject"));
  renderSubjects(subject?.id);
  $("subject-title").textContent = subject && subject.id !== "mathematics" ? subject.title : "All subjects";
  $("query").value = parameters.get("q") || "";
  $("kind").value = parameters.get("kind") || "";
  $("all").checked = parameters.get("all") === "1";
  $("axiom-free").checked = parameters.get("axiom_free") === "1";
  const data = await api("/api/search", {q: parameters.get("q") || "", subject: parameters.get("subject"),
    kind: parameters.get("kind"), all: parameters.get("all"), axiom_free: parameters.get("axiom_free"),
    offset: parameters.get("offset") || 0, limit: 30});
  if (request !== activeRequest) return;
  $("result-count").textContent = `${count(data.total)} ${data.total === 1 ? "result" : "results"}`;
  const results = $("results");
  results.replaceChildren();
  if (!data.items.length) results.append(element("p", "Nothing matches these filters.", "empty-state"));
  for (const item of data.items) {
    const card = element("article", null, "result-card");
    const top = element("div", null, "result-top");
    top.append(nameLink(item.name, "result-name"), element("span", kindLabels[item.kind] || item.kind, "badge"));
    card.append(top);
    if (item.doc) card.append(formatted(element("p", null, "result-doc"), item.doc.trim().split("\n").slice(0, 2).join(" "), item.name));
    card.append(element("pre", item.statement, "result-type"));
    const metadata = element("div", null, "result-meta");
    metadata.append(element("span", item.module), element("span", item.axioms.length ? item.axioms.join(", ") : "No axioms"));
    if (!item.selected) metadata.append(element("span", "Prerequisite"));
    card.append(metadata);
    results.append(card);
  }
  pageButtons($("search-pages"), data.total, data.offset, data.limit, offset => { route({offset}); scrollTo(0, 0); });
}

/* declaration */

function sourceLink(node) {
  if (!node.origin.url) return element("span", node.origin.path || node.module);
  const suffix = node.source ? "#L" + node.source.line : "";
  return externalLink("Source ↗", node.origin.url + suffix);
}

function renderHeading(node, tab) {
  const heading = $("declaration-heading");
  const crumbs = element("nav", null, "crumbs");
  crumbs.setAttribute("aria-label", "Location");
  const browse = element("a", "Browse");
  browse.href = href({view: "browse"});
  crumbs.append(browse, element("span", node.module));
  const title = element("h1", node.name, "declaration-name");
  const origin = element("div", null, "declaration-origin");
  origin.append(element("span", kindLabels[node.kind] || node.kind, "badge"), sourceLink(node));
  if (node.origin.license) origin.append(element("span", node.origin.license));
  if (graphKinds.has(node.kind) && (node.selected || ["axiom", "quotient_primitive"].includes(node.kind))) {
    const graph = element("a", "View in graph");
    graph.href = href({view: "graph", at: "d:" + node.name});
    origin.append(graph);
  }
  heading.replaceChildren(crumbs, title, origin);
  const navigation = $("tabs");
  navigation.replaceChildren();
  for (const label of tabs) {
    const name = label.toLowerCase();
    const control = button(label, () => route({tab: name, group: null, level: null, term_root: null, term_rule: null, term_path: null}),
      "tab" + (tab === name ? " active" : ""));
    if (tab === name) control.setAttribute("aria-current", "page");
    navigation.append(control);
  }
  const selected = navigation.querySelector(".active");
  if (selected) {
    const offset = selected.getBoundingClientRect().left - navigation.getBoundingClientRect().left;
    navigation.scrollLeft += offset - (navigation.clientWidth - selected.offsetWidth) / 2;
  }
}

function downloadLink(text, path, name) {
  const link = element("a", text, "small-button");
  link.href = path + "?" + new URLSearchParams({name, format: "json", snapshot: summary.catalog_digest});
  link.download = name.replace(/[^a-z0-9_.-]/gi, "_") + ".json";
  return link;
}

function termLink(text, data, path, className = "small-button") {
  const link = element("a", text, className);
  const parameters = new URLSearchParams(location.hash.slice(1));
  parameters.set("tab", "proof");
  parameters.set("term_root", data.root);
  if (data.rule === null) parameters.delete("term_rule");
  else parameters.set("term_rule", data.rule);
  if (path) parameters.set("term_path", path);
  else parameters.delete("term_path");
  link.href = "#" + parameters.toString();
  return link;
}

function binderLabel(name) {
  if (!name) return "_";
  return !name.includes("«") && name.includes("._hygCtx._hyg.") ? name.split("._@.")[0] : name;
}

function termDescription(item) {
  if (item.tag === "const" || item.tag === "proj") return item.name;
  if (item.tag === "bvar") return `${binderLabel(item.binding.name)} · bound variable ${item.index}`;
  if (item.tag === "lam" || item.tag === "forall" || item.tag === "let") return binderLabel(item.name);
  return {app: "Application", sort: "Universe", nat: "Natural number", string: "String"}[item.tag] || item.tag;
}

function renderTerm(body, data) {
  const focused = data.expression;
  const section = element("section", null, "term-inspector");
  section.setAttribute("aria-label", "Checked term inspector");
  const controls = element("div", null, "section-tools");
  const select = element("select");
  select.id = "term-root";
  select.setAttribute("aria-label", "Term root");
  for (const [index, root] of data.roots.entries()) {
    const option = element("option", root.label);
    option.value = index;
    option.selected = root.root === data.root && root.rule === data.rule;
    select.append(option);
  }
  select.addEventListener("change", () => {
    const root = data.roots[select.value];
    route({term_root: root.root, term_rule: root.rule, term_path: null});
  });
  controls.append(select);
  if (data.path) {
    const parent = termLink("Parent", data, data.path.slice(0, -1));
    parent.id = "term-parent";
    controls.append(parent, termLink("Root", data, ""));
  }
  controls.append(element("span", data.path ? `${data.path.length} steps from the root` : "Root expression", "muted"));
  section.append(controls);
  const card = element("article", null, "term-card");
  const titles = {app: "Application", lam: "Function", forall: "Dependent function type", let: "Local definition",
    const: "Referenced declaration", bvar: "Bound variable", sort: "Universe", proj: "Projection",
    nat: "Natural number literal", string: "String literal"};
  const explanations = {
    app: "The function is applied to the arguments in order.",
    lam: "The function binds this variable with the specified type.",
    forall: "The body may depend on the variable with the specified type.",
    let: "The body may refer to this local definition.",
    bvar: "This occurrence refers to the binding identified below.",
    const: "Follow the declaration to inspect its statement, proof, and foundations.",
    proj: "This expression selects a field from a structure.",
  };
  card.append(element("h2", titles[focused.tag] || focused.tag));
  if (explanations[focused.tag]) card.append(element("p", explanations[focused.tag], "muted"));
  if (["const", "proj"].includes(focused.tag)) card.append(nameLink(focused.name));
  else if (["lam", "forall", "let"].includes(focused.tag)) {
    card.append(element("p", `${binderLabel(focused.name)}${focused.binder ? " · " + focused.binder.replaceAll("_", " ") : ""}`, "term-binding-name"));
  } else if (focused.tag === "bvar") {
    card.append(element("p", `${binderLabel(data.binding.name)} · bound variable ${focused.index}`, "term-binding-name"));
  } else if (["nat", "string"].includes(focused.tag)) {
    card.append(element("pre", focused.tag === "string" ? JSON.stringify(focused.value) : String(focused.value), "term-literal"));
  } else if (focused.tag === "sort") {
    card.append(element("pre", focused.level.tag === "zero" ? "Prop" : "Sort " + JSON.stringify(focused.level), "term-literal"));
  }
  if (focused.levels?.length) card.append(element("p", "Universe arguments: " + JSON.stringify(focused.levels), "term-universes"));
  if (focused.tag === "proj") card.append(element("p", `Field index: ${focused.index} (starting at zero)`, "muted"));
  const children = element("div", null, "term-children");
  function addChild(label, child) {
    const row = element("div", null, "term-child");
    row.append(termLink(label, data, child.path), child.tag === "const"
      ? nameLink(child.name, "term-child-description")
      : element("span", termDescription(child), "term-child-description"));
    children.append(row);
  }
  if (data.application) {
    addChild("Function", data.application.function);
    data.application.arguments.forEach((item, index) => addChild(`Argument ${index + 1}`, item));
  } else {
    const labels = {type: "Type", body: "Body", value: "Value", expression: "Structure", function: "Function", argument: "Argument"};
    for (const child of data.children) addChild(labels[child.field], child);
  }
  card.append(children);
  section.append(card);
  if (data.context.length) {
    const context = element("section", null, "term-context");
    context.append(element("h3", "Bound assumptions and variables"));
    const list = element("ol");
    for (const binding of data.context) {
      const row = element("li");
      if (data.binding?.depth === binding.depth) row.classList.add("term-binding-active");
      const label = `${binderLabel(binding.name)} · ${binding.kind === "let" ? "local definition" : (binding.binder || "explicit").replaceAll("_", " ")} · index ${binding.index}`;
      row.append(element("span", label, "term-binding-name"),
        termLink("Inspect type", data, data.path.slice(0, binding.depth) + "t"));
      if (binding.kind === "let") row.append(termLink("Inspect value", data, data.path.slice(0, binding.depth) + "v"));
      list.append(row);
    }
    context.append(list);
    section.append(context);
  }
  const exact = element("details", null, "term-exact");
  exact.append(element("summary", "Exact expression and logical names"),
    element("pre", JSON.stringify({root: data.root, rule: data.rule, path: data.path,
      expression: focused, context: data.context, names: data.name_data, universes: data.universes}, null, 2), "proof-code"));
  section.append(exact);
  body.append(section);
}

async function proofView(body, node, request, parameters) {
  const tools = element("div", null, "section-tools");
  tools.append(element("p", "Follow the checked term through its arguments and bound assumptions."),
    downloadLink("Download expressions", "/api/expressions", node.name));
  body.append(tools);
  const data = await api("/api/term", {name: node.name, root: parameters.get("term_root") || (node.value === null ? "type" : "value"),
    rule: parameters.get("term_rule"), path: parameters.get("term_path") || ""});
  if (request !== activeRequest) return;
  renderTerm(body, data);
  if (node.value !== null) {
    const preview = element("details", null, "term-preview");
    preview.append(element("summary", "Readable preview"), element("p", "Lean's readable preview may abbreviate subterms. The inspector and expression download retain their exact structure.", "muted"));
    let loaded = false;
    preview.addEventListener("toggle", async () => {
      if (!preview.open || loaded) return;
      loaded = true;
      try {
        const result = await api("/api/declaration", {name: node.name, proof: 1});
        if (request === activeRequest) preview.append(element("pre", result.proof, "proof-code"));
      } catch (error) { loaded = false; if (request === activeRequest) status(error.message, true); }
    });
    body.append(preview);
  }
}

async function dependenciesView(body, node, request) {
  const controls = element("div", null, "section-tools");
  const direction = element("select");
  direction.setAttribute("aria-label", "Dependency direction");
  for (const [value, label] of [["", "Prerequisites"], ["1", "Dependent declarations"]]) {
    const option = element("option", label); option.value = value; direction.append(option);
  }
  const role = element("select");
  role.setAttribute("aria-label", "Dependency role");
  for (const [value, label] of [["", "All roles"], ["type", "Type"], ["value", "Proof or definition"], ["structure", "Inductive structure"]]) {
    const option = element("option", label); option.value = value; role.append(option);
  }
  const checkbox = element("input"); checkbox.type = "checkbox";
  const label = element("label", null, "check"); label.append(checkbox, document.createTextNode(" Transitive"));
  controls.append(direction, role, label);
  const results = element("div", null, "results");
  const pages = element("div", null, "pagination");
  body.append(controls, results, pages);
  let loadRequest = 0;
  async function load(offset = 0) {
    const current = ++loadRequest;
    const data = await api("/api/dependencies", {name: node.name, reverse: direction.value,
      role: role.value, transitive: checkbox.checked ? 1 : 0, offset, limit: 30});
    if (request !== activeRequest || current !== loadRequest) return;
    results.replaceChildren(element("p", `${count(data.total)} declarations`, "muted"));
    for (const item of data.items) {
      const card = element("article", null, "result-card");
      const top = element("div", null, "result-top");
      top.append(nameLink(item.name, "result-name"), element("span", kindLabels[item.kind] || item.kind, "badge"));
      card.append(top, element("pre", item.statement, "result-type"), element("div", item.roles.join(" · "), "result-meta"));
      results.append(card);
    }
    pageButtons(pages, data.total, data.offset, data.limit, offset => load(offset).catch(error => status(error.message, true)));
  }
  for (const input of [direction, role, checkbox]) input.addEventListener("change", () => load().catch(error => status(error.message, true)));
  await load();
}

async function foundationsView(body, node, request) {
  body.append(element("h2", "Axioms"));
  if (!node.axioms.length) body.append(element("p", "No axioms beyond the kernel rules and bound assumptions.", "notice"));
  const graph = await api("/api/hierarchy", {name: node.name, limit: 1});
  if (request !== activeRequest) return;
  for (const name of node.axioms) {
    const info = summary.axiom_policy[name];
    const card = element("section", null, "foundation-card");
    card.append(element("h3", name), element("p", info.description), externalLink("Reference ↗", info.reference),
      element("div", "Dependency path", "path-heading"));
    const path = element("div", null, "path");
    for (const [index, item] of graph.axiom_paths[name].entries()) {
      if (index) path.append(element("span", "→", "path-arrow"));
      path.append(nameLink(item));
    }
    card.append(path); body.append(card);
  }
  if (node.lean_axioms.join("|") !== node.axioms.join("|")) {
    body.append(element("p", `The full dependency graph uses ${node.axioms.join(", ") || "no additional axioms"}. Lean's cached listing reports ${node.lean_axioms.join(", ") || "none"}. Full inductive-block and reduction dependencies are included above.`, "notice"));
  }
  body.append(element("h2", "Kernel"));
  const list = element("ul", null, "kernel-rules");
  for (const rule of summary.foundation.rules) list.append(element("li", rule));
  body.append(list, externalLink("Lean's logical foundation ↗", summary.foundation.reference));
}

async function hierarchyView(body, node, request, parameters) {
  const data = await api("/api/hierarchy", {name: node.name, limit: 30, level: parameters.get("level")});
  if (request !== activeRequest) return;
  const tools = element("div", null, "section-tools");
  tools.append(element("p", `${count(data.declarations)} declarations · ${count(data.groups)} dependency groups`),
    downloadLink("Download graph", "/api/hierarchy", node.name));
  const select = element("select", null, "level-select");
  select.setAttribute("aria-label", "Dependency level");
  for (const level of data.levels) {
    const option = element("option", `Level ${level.level} · ${count(level.groups)} groups`);
    option.value = level.level; select.append(option);
  }
  select.value = parameters.get("level") || data.levels[data.levels.length - 1].level;
  const results = element("div");
  const pages = element("div", null, "pagination");
  body.append(tools, element("p", "Prerequisites occupy earlier levels. Mutually dependent inductive declarations share one group.", "notice"), select, results, pages);
  function groupCard(group, expandable = true) {
    const card = element("section", null, "group-card");
    const title = element("div", null, "group-title");
    title.append(element("strong", group.cyclic ? "Inductive block" : "Declaration"), element("span", `Level ${group.level}`));
    const members = element("div", null, "chip-list");
    for (const member of group.members) members.append(nameLink(member));
    card.append(title, members);
    if (expandable && group.dependencies.length) card.append(button(`${group.dependencies.length} prerequisite groups`, () => route({group: group.id})));
    return card;
  }
  async function load(offset = 0) {
    const page = await api("/api/hierarchy", {name: node.name, level: select.value, offset, limit: 30});
    if (request !== activeRequest) return;
    results.replaceChildren();
    for (const group of page.items) results.append(groupCard(group));
    pageButtons(pages, page.total, page.offset, page.limit, offset => load(offset).catch(error => status(error.message, true)));
  }
  select.addEventListener("change", () => route({group: null, level: select.value}));
  if (parameters.has("group")) {
    const group = await api("/api/hierarchy", {name: node.name, group: parameters.get("group")});
    if (request !== activeRequest) return;
    select.value = group.level;
    results.append(groupCard(group, false), element("h3", "Prerequisite groups"));
    for (const prerequisite of group.prerequisites) results.append(groupCard(prerequisite));
    if (!group.prerequisites.length) results.append(element("p", "This group rests directly on the kernel rules.", "muted"));
  } else await load();
}

async function sourceView(body, node, request) {
  const tools = element("div", null, "section-tools");
  tools.append(element("p", "Source retained with the verified snapshot."), sourceLink(node));
  const source = element("div", null, "source-code");
  const metadata = element("p", "", "source-meta");
  body.append(tools, source, metadata);
  async function load(full = false) {
    const data = await api("/api/source", {name: node.name, full: full ? 1 : 0});
    if (request !== activeRequest) return;
    source.replaceChildren();
    for (const [index, text] of data.lines.entries()) {
      const number = data.start_line + index;
      const row = element("div", null, "source-line");
      if (data.declaration_range && number >= data.declaration_range.line && number <= data.declaration_range.end_line) row.classList.add("highlight");
      row.append(element("span", number, "line-number"), element("span", text, "source-text"));
      source.append(row);
    }
    metadata.textContent = `${data.module} · ${count(data.total_lines)} lines · SHA-256 ${data.sha256}`;
  }
  tools.append(button("Full module", () => load(true).catch(error => status(error.message, true))));
  await load();
}

async function referencesView(body, node, request, parameters) {
  const data = await api("/api/citations", {name: node.name});
  if (request !== activeRequest) return;
  const tools = element("div", null, "section-tools");
  tools.append(element("p", "References retained from the pinned upstream documentation."));
  for (const bibliography of data.bibliographies) {
    const link = element("a", `${bibliography.package} bibliography`, "small-button");
    link.href = "/api/bibliography?" + new URLSearchParams({package: bibliography.package, snapshot: summary.catalog_digest});
    link.download = bibliography.package + "-references.bib";
    tools.append(link);
  }
  body.append(tools);
  const cards = [];
  function section(title, entries, empty) {
    body.append(element("h2", title));
    if (!entries.length) body.append(element("p", empty, "muted"));
    for (const item of entries) {
      const card = element("article", null, "reference-card");
      card.dataset.reference = item.citation_key;
      if (item.ambiguous) {
        card.append(element("h3", item.citation_key), element("p", "This citation key occurs in several bibliographies."));
        for (const candidate of item.candidates) card.append(element("p", candidate.package + ":" + candidate.key));
      } else {
        const fields = item.fields;
        card.append(element("span", item.package + " · " + item.key, "reference-key"),
          element("h3", fields.title || item.key));
        const authors = fields.author || fields.editor;
        if (authors) card.append(element("p", authors, "reference-authors"));
        const publication = [fields.journal || fields.booktitle || fields.publisher, fields.year].filter(Boolean);
        if (publication.length) card.append(element("p", publication.join(" · "), "muted"));
        const links = element("div", null, "section-tools");
        if (fields.url) links.append(externalLink("Publication ↗", fields.url));
        else if (fields.doi) links.append(externalLink("DOI ↗", "https://doi.org/" + fields.doi));
        links.append(externalLink("Bibliography entry ↗", item.source_url));
        card.append(links);
        const raw = element("details");
        raw.append(element("summary", "BibTeX"), element("pre", item.raw, "proof-code"));
        card.append(raw);
      }
      if (item.citation_key === parameters.get("reference")) card.classList.add("reference-selected");
      cards.push(card);
      body.append(card);
    }
  }
  section("Cited here", data.declaration_citations, "No citations in this declaration's documentation.");
  section("Module references", data.module_citations, "No citations in this module's documentation.");
  if (data.module_docs.length) {
    const docs = element("details", null, "reference-module-docs");
    docs.append(element("summary", "Module documentation"));
    for (const doc of data.module_docs) {
      if (data.origin.url) docs.append(externalLink(`Source · line ${doc.line} ↗`, data.origin.url + "#L" + doc.line));
      docs.append(formatted(element("div", null, "documentation"), doc.text.trim(), node.name));
    }
    body.append(docs);
  }
  cards.find(card => card.classList.contains("reference-selected"))?.scrollIntoView({block: "nearest"});
}

/** the declaration's axioms, direct prerequisites and module, each a way onward. */
function facts(node) {
  const list = element("dl", null, "facts");
  const row = (term, ...values) => {
    const value = element("dd");
    value.append(...values);
    list.append(element("dt", term), value);
  };
  const axioms = node.axioms.map((name, index) => {
    const link = nameLink(name, "mono");
    return index ? [document.createTextNode(", "), link] : [link];
  }).flat();
  row("Axioms", ...(axioms.length ? axioms : [document.createTextNode("None beyond the kernel rules")]));
  const prerequisites = element("a", `${count(node.dependencies.length)} direct`);
  prerequisites.href = href({name: node.name, tab: "dependencies"});
  row("Prerequisites", prerequisites);
  row("Module", element("span", node.module, "mono"));
  return list;
}

async function showDeclaration(parameters, request) {
  showView("detail");
  const node = await api("/api/declaration", {name: parameters.get("name")});
  if (request !== activeRequest) return;
  $("detail-body").replaceChildren();
  const tab = parameters.get("tab") || "statement";
  renderHeading(node, tab);
  const body = $("detail-body");
  if (tab === "statement") {
    body.append(element("pre", node.statement, "statement"), facts(node));
    if (node.doc) body.append(formatted(element("div", null, "documentation"), node.doc.trim(), node.name));
  } else if (tab === "proof") await proofView(body, node, request, parameters);
  else if (tab === "dependencies") await dependenciesView(body, node, request);
  else if (tab === "foundations") await foundationsView(body, node, request);
  else if (tab === "hierarchy") await hierarchyView(body, node, request, parameters);
  else if (tab === "references") await referencesView(body, node, request, parameters);
  else if (tab === "source") await sourceView(body, node, request);
  else throw new Error("Unknown declaration section.");
}

/* contribute */

function renderGuide(text) {
  const content = $("guide-text");
  content.replaceChildren();
  for (const block of text.trim().split(/\n\n+/)) {
    if (block.startsWith("# ")) continue;
    const lines = block.split("\n");
    if (lines.every(line => /^\d+\. /.test(line))) {
      const list = element("ol");
      for (const line of lines) list.append(formatted(element("li"), line.replace(/^\d+\. /, "")));
      content.append(list);
    } else content.append(formatted(element("p"), lines.join(" ")));
  }
}

/* routing */

function browsing(parameters) {
  return parameters.get("view") === "browse" || ["q", "subject", "kind", "all", "axiom_free", "offset"].some(key => parameters.has(key));
}

async function render() {
  if (!summary) return;
  const request = ++activeRequest;
  const parameters = new URLSearchParams(location.hash.slice(1));
  const view = parameters.get("view");
  let slow = setTimeout(() => status("Loading…"), 300);
  try {
    if (view === "guide") {
      showView("guide");
      const data = await api("/api/guide");
      if (request === activeRequest) renderGuide(data.text);
    } else if (view === "graph") {
      showView("graph");
      await window.MathGraph.open(parameters.get("at") || "", {api, request: () => request === activeRequest});
    } else if (parameters.has("name")) await showDeclaration(parameters, request);
    else if (browsing(parameters)) await showSearch(parameters, request);
    else renderHome();
    if (request === activeRequest) { clearTimeout(slow); status(); }
  } catch (error) {
    clearTimeout(slow);
    if (request === activeRequest) status(error.message, true);
  }
}

function search(query, extra = {}) {
  const parameters = new URLSearchParams(location.hash.slice(1));
  const values = {view: "browse", q: query};
  if (browsing(parameters)) {
    for (const key of ["subject", "kind", "all", "axiom_free"]) values[key] = parameters.get(key);
  }
  location.hash = href({...values, ...extra});
}

function snapshotLabels() {
  bibliographyKeys = new Set(summary.bibliography_keys || []);
  $("snapshot-label").textContent = `Snapshot ${summary.catalog_digest.slice(0, 12)} · ${summary.checkers.join(" · ").replace("nanoda_bin", "nanoda")}`;
  $("catalog-download").href = "/api/catalog?" + new URLSearchParams({snapshot: summary.catalog_digest});
  $("proof-download").href = "/api/proof-export?" + new URLSearchParams({snapshot: summary.catalog_digest});
}

async function initialize() {
  // the home frame needs no snapshot data, so it appears at once.
  if (!location.hash.slice(1)) { showView("home"); renderRing(); }
  const slow = setTimeout(() => status("Opening the verified snapshot…"), 300);
  try {
    summary = await api("/api/summary");
    clearTimeout(slow);
    status();
    snapshotLabels();
    await render();
  } catch (error) { clearTimeout(slow); status(error.message, true); }
}

$("search-home").addEventListener("submit", event => { event.preventDefault(); search($("home-query").value); });
$("bar-search").addEventListener("submit", event => { event.preventDefault(); search($("bar-query").value); $("bar-query").blur(); });
$("search-form").addEventListener("submit", event => { event.preventDefault(); clearTimeout(searchTimer); filter(); });
$("query").addEventListener("input", () => { clearTimeout(searchTimer); searchTimer = setTimeout(filter, 250); });
for (const id of ["kind", "all", "axiom-free"]) $(id).addEventListener("change", filter);

function filter() {
  route({view: "browse", q: $("query").value, kind: $("kind").value, all: $("all").checked ? 1 : null,
    axiom_free: $("axiom-free").checked ? 1 : null, offset: null});
}

$("reload").addEventListener("click", async () => {
  $("reload").disabled = true; status("Checking the latest verified snapshot…");
  try {
    summary = await api("/api/reload", {}, {method: "POST"});
    snapshotLabels();
    status();
    await render();
  } catch (error) { status(error.message, true); }
  finally { $("reload").disabled = false; }
});
window.addEventListener("hashchange", () => { clearTimeout(searchTimer); render(); });
document.addEventListener("keydown", event => {
  if (event.key !== "/" || event.metaKey || event.ctrlKey || ["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement.tagName)) return;
  event.preventDefault();
  const view = document.body.dataset.view;
  (view === "home" ? $("home-query") : view === "search" ? $("query") : $("bar-query")).focus();
});
initialize();
