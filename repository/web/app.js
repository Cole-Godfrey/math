"use strict";

const $ = id => document.getElementById(id);
const tabs = ["Statement", "Proof", "Dependencies", "Foundations", "Hierarchy", "Source"];
let summary = null;
let activeRequest = 0;
let searchTimer;
let focusSearch = false;

function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined && text !== null) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function formatted(node, text) {
  for (const part of text.split(/(`[^`]+`|\*\*[^*]+\*\*|\[[^\]]+\]\(https?:\/\/[^\s)]+\))/g)) {
    if (part.startsWith("`")) node.append(element("code", part.slice(1, -1)));
    else if (part.startsWith("**")) node.append(element("strong", part.slice(2, -2)));
    else if (part.startsWith("[")) {
      const match = part.match(/^\[([^\]]+)\]\((https?:\/\/[^)]+)\)$/);
      node.append(match ? externalLink(match[1], match[2]) : document.createTextNode(part));
    } else node.append(document.createTextNode(part));
  }
  return node;
}

function route(patch) {
  const parameters = new URLSearchParams(location.hash.slice(1));
  for (const [key, value] of Object.entries(patch)) {
    if (value === null || value === "") parameters.delete(key);
    else parameters.set(key, String(value));
  }
  location.hash = parameters.toString();
}

function nameLink(name, className = "node-chip") {
  const link = element("a", name, className);
  const parameters = new URLSearchParams(location.hash.slice(1));
  parameters.set("name", name);
  parameters.set("tab", "statement");
  parameters.delete("group");
  parameters.delete("level");
  link.href = "#" + parameters.toString();
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
  if (!total) return;
  const previous = button("Previous", () => change(Math.max(0, offset - limit)));
  previous.disabled = offset === 0;
  const next = button("Next", () => change(offset + limit));
  next.disabled = offset + limit >= total;
  container.append(previous, element("span", `${offset + 1} to ${Math.min(offset + limit, total)} of ${total.toLocaleString()}`), next);
}

function renderSubjects(selected) {
  const records = new Map(summary.subjects.map(item => [item.id, item]));
  const list = $("subjects");
  list.replaceChildren();
  function append(parent, depth) {
    for (const item of summary.subjects.filter(item => item.parent === parent).sort((a, b) => a.title.localeCompare(b.title))) {
      const parameters = new URLSearchParams();
      if (item.id !== "mathematics") parameters.set("subject", item.id);
      const link = element("a", null, `subject-link depth-${Math.min(depth, 4)}`);
      link.href = "#" + parameters.toString();
      const current = (selected || "mathematics") === item.id;
      link.classList.toggle("active", current);
      if (current) link.setAttribute("aria-current", "page");
      link.append(element("span", item.title), element("span", item.selected_declarations.toLocaleString(), "subject-count"));
      list.append(link);
      append(item.id, depth + 1);
    }
  }
  append(null, 0);
  const subject = records.get(selected);
  $("subject-title").textContent = subject ? subject.title : "Mathematics, with its foundations in view.";
  $("coverage").textContent = subject
    ? `${subject.selected_declarations.toLocaleString()} selected declarations · ${subject.dependency_declarations.toLocaleString()} with their full prerequisites`
    : `${summary.declarations.toLocaleString()} verified declarations · ${summary.selected.toLocaleString()} selected results and objects`;
}

async function showSearch(parameters, request) {
  $("search-view").hidden = false;
  $("detail-view").hidden = true;
  $("guide-view").hidden = true;
  if (focusSearch) { $("query").focus(); focusSearch = false; }
  $("query").value = parameters.get("q") || "";
  $("kind").value = parameters.get("kind") || "";
  $("all").checked = parameters.get("all") === "1";
  $("axiom-free").checked = parameters.get("axiom_free") === "1";
  const data = await api("/api/search", {q: parameters.get("q") || "", subject: parameters.get("subject"),
    kind: parameters.get("kind"), all: parameters.get("all"), axiom_free: parameters.get("axiom_free"),
    offset: parameters.get("offset") || 0, limit: 30});
  if (request !== activeRequest) return;
  $("result-count").textContent = `${data.total.toLocaleString()} matches`;
  const results = $("results");
  results.replaceChildren();
  if (!data.items.length) results.append(element("p", "No declarations match these filters.", "empty-state"));
  for (const item of data.items) {
    const card = element("article", null, "result-card");
    const top = element("div", null, "result-top");
    top.append(nameLink(item.name, "result-name"), element("span", item.kind, "badge"));
    card.append(top);
    if (item.doc) card.append(formatted(element("p", null, "result-doc"), item.doc.trim().split("\n").slice(0, 2).join(" ")));
    card.append(element("pre", item.statement, "result-type"));
    const metadata = element("div", null, "result-meta");
    metadata.append(element("span", item.module), element("span", item.axioms.length ? `${item.axioms.length} foundational axioms` : "Kernel rules only"));
    if (!item.selected) metadata.append(element("span", "Prerequisite"));
    card.append(metadata);
    results.append(card);
  }
  pageButtons($("search-pages"), data.total, data.offset, data.limit, offset => route({offset}));
}

function sourceLink(node) {
  if (!node.origin.url) return element("span", node.origin.path || node.module);
  const suffix = node.source ? "#L" + node.source.line : "";
  return externalLink("Pinned source ↗", node.origin.url + suffix);
}

function renderHeading(node, tab) {
  const heading = $("declaration-heading");
  heading.replaceChildren(element("span", node.kind, "eyebrow"), element("h1", node.name, "declaration-name"));
  const origin = element("div", null, "declaration-origin");
  origin.append(element("span", node.module), sourceLink(node));
  if (node.origin.license) origin.append(element("span", node.origin.license));
  heading.append(origin);
  const navigation = $("tabs");
  navigation.replaceChildren();
  for (const label of tabs) {
    const name = label.toLowerCase();
    const control = button(label, () => route({tab: name, group: null}), "tab" + (tab === name ? " active" : ""));
    if (tab === name) control.setAttribute("aria-current", "page");
    navigation.append(control);
  }
}

function downloadLink(text, path, name) {
  const link = element("a", text, "small-button");
  link.href = path + "?" + new URLSearchParams({name, format: "json", snapshot: summary.catalog_digest});
  link.download = name.replace(/[^a-z0-9_.-]/gi, "_") + ".json";
  return link;
}

async function proofView(body, node, request) {
  const tools = element("div", null, "section-tools");
  tools.append(element("p", "Term preview. Download expressions for the complete checked term."),
    downloadLink("Download expressions", "/api/expressions", node.name));
  body.append(tools);
  const data = await api("/api/declaration", {name: node.name, proof: 1});
  if (request !== activeRequest) return;
  body.append(element("pre", data.proof || "This is a kernel primitive or structural declaration. Its reduction data is included in the expression download.", "proof-code"));
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
  const label = element("label", null, "check-label"); label.append(checkbox, document.createTextNode(" All transitive dependencies"));
  controls.append(direction, role, label);
  const results = element("div");
  const pages = element("div", null, "pagination");
  body.append(controls, results, pages);
  let loadRequest = 0;
  async function load(offset = 0) {
    const current = ++loadRequest;
    const data = await api("/api/dependencies", {name: node.name, reverse: direction.value,
      role: role.value, transitive: checkbox.checked ? 1 : 0, offset, limit: 30});
    if (request !== activeRequest || current !== loadRequest) return;
    results.replaceChildren(element("p", `${data.total.toLocaleString()} declarations`, "muted"));
    for (const item of data.items) {
      const card = element("article", null, "result-card");
      card.append(nameLink(item.name, "result-name"), element("div", [item.kind, ...item.roles].join(" · "), "result-meta"),
        element("pre", item.statement, "result-type"));
      results.append(card);
    }
    pageButtons(pages, data.total, data.offset, data.limit, offset => load(offset).catch(error => status(error.message, true)));
  }
  for (const input of [direction, role, checkbox]) input.addEventListener("change", () => load().catch(error => status(error.message, true)));
  await load();
}

async function foundationsView(body, node, request) {
  body.append(element("h2", "Foundational axioms"));
  if (!node.axioms.length) body.append(element("p", "This declaration uses no additional axioms beyond the kernel rules and its bound assumptions.", "notice"));
  const graph = await api("/api/hierarchy", {name: node.name, limit: 1});
  if (request !== activeRequest) return;
  for (const name of node.axioms) {
    const info = summary.axiom_policy[name];
    const card = element("section", null, "foundation-card");
    card.append(element("h3", name), element("p", info.description), externalLink("Foundation reference ↗", info.reference),
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
  body.append(element("h2", "Kernel foundation"));
  const list = element("ul", null, "kernel-rules");
  for (const rule of summary.foundation.rules) list.append(element("li", rule));
  body.append(list, externalLink("Lean's logical foundation ↗", summary.foundation.reference));
}

async function hierarchyView(body, node, request, parameters) {
  const data = await api("/api/hierarchy", {name: node.name, limit: 30, level: parameters.get("level")});
  if (request !== activeRequest) return;
  const tools = element("div", null, "section-tools");
  tools.append(element("p", `${data.declarations.toLocaleString()} declarations · ${data.groups.toLocaleString()} dependency groups`),
    downloadLink("Download complete graph", "/api/hierarchy", node.name));
  const select = element("select", null, "level-select");
  select.setAttribute("aria-label", "Dependency level");
  for (const level of data.levels) {
    const option = element("option", `Level ${level.level} · ${level.groups.toLocaleString()} groups`);
    option.value = level.level; select.append(option);
  }
  select.value = parameters.get("level") || data.levels[data.levels.length - 1].level;
  const results = element("div");
  const pages = element("div", null, "pagination");
  body.append(tools, element("p", "Prerequisites occupy earlier levels. Mutually dependent inductive declarations share one group.", "notice"), select, element("div", null, "section-tools"), results, pages);
  function groupCard(group, expandable = true) {
    const card = element("section", null, "group-card");
    const title = element("div", null, "group-title");
    title.append(element("strong", group.cyclic ? "Inductive dependency block" : "Declaration"), element("span", `Level ${group.level}`));
    const members = element("div", null, "chip-list");
    for (const member of group.members) members.append(nameLink(member));
    card.append(title, members);
    if (expandable && group.dependencies.length) card.append(button(`Follow ${group.dependencies.length} prerequisite groups`, () => route({group: group.id})));
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
    if (!group.prerequisites.length) results.append(element("p", "This group is grounded directly in the declared kernel rules.", "muted"));
  } else await load();
}

async function sourceView(body, node, request) {
  const tools = element("div", null, "section-tools");
  tools.append(element("p", "Source text retained with the verified snapshot."), sourceLink(node));
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
    metadata.textContent = `${data.module} · ${data.total_lines.toLocaleString()} lines · SHA-256 ${data.sha256}`;
  }
  tools.append(button("Full module", () => load(true).catch(error => status(error.message, true))));
  await load();
}

async function showDeclaration(parameters, request) {
  $("search-view").hidden = true;
  $("detail-view").hidden = false;
  $("guide-view").hidden = true;
  $("detail-body").replaceChildren();
  const node = await api("/api/declaration", {name: parameters.get("name")});
  if (request !== activeRequest) return;
  const tab = parameters.get("tab") || "statement";
  renderHeading(node, tab);
  const body = $("detail-body");
  if (tab === "statement") {
    body.append(element("pre", node.statement, "statement"));
    if (node.doc) body.append(formatted(element("div", null, "documentation"), node.doc.trim()));
    body.append(element("p", node.axioms.length ? `Foundational axioms: ${node.axioms.join(", ")}` : "No additional axioms beyond the kernel rules and bound assumptions.", "notice"));
  } else if (tab === "proof") await proofView(body, node, request);
  else if (tab === "dependencies") await dependenciesView(body, node, request);
  else if (tab === "foundations") await foundationsView(body, node, request);
  else if (tab === "hierarchy") await hierarchyView(body, node, request, parameters);
  else if (tab === "source") await sourceView(body, node, request);
  else throw new Error("Unknown declaration section.");
}

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

async function render() {
  if (!summary) return;
  const request = ++activeRequest;
  const parameters = new URLSearchParams(location.hash.slice(1));
  renderSubjects(parameters.get("subject"));
  status("Loading…");
  try {
    if (parameters.get("view") === "guide") {
      $("search-view").hidden = true; $("detail-view").hidden = true; $("guide-view").hidden = false;
      const data = await api("/api/guide");
      if (request === activeRequest) renderGuide(data.text);
    } else if (parameters.has("name")) await showDeclaration(parameters, request);
    else await showSearch(parameters, request);
    if (request === activeRequest) status();
  } catch (error) { if (request === activeRequest) status(error.message, true); }
}

function search() {
  route({q: $("query").value, kind: $("kind").value, all: $("all").checked ? 1 : null,
    axiom_free: $("axiom-free").checked ? 1 : null, offset: null, name: null, tab: null, group: null, view: null});
}

async function initialize() {
  status("Opening the verified snapshot…");
  try {
    summary = await api("/api/summary");
    snapshotLabels();
    await render();
  } catch (error) { status(error.message, true); }
}

function snapshotLabels() {
  $("checker-label").textContent = `Lean ${summary.lean_version} + nanoda`;
  $("binding-label").textContent = `${summary.proof_binding.matched_declarations.toLocaleString()} declarations matched to verified terms`;
  $("snapshot-id").textContent = summary.catalog_digest.slice(0, 16);
  $("catalog-download").href = "/api/catalog?" + new URLSearchParams({snapshot: summary.catalog_digest});
  $("proof-download").href = "/api/proof-export?" + new URLSearchParams({snapshot: summary.catalog_digest});
}

$("search-form").addEventListener("submit", event => { event.preventDefault(); search(); });
$("query").addEventListener("input", () => { clearTimeout(searchTimer); searchTimer = setTimeout(search, 250); });
for (const id of ["kind", "all", "axiom-free"]) $(id).addEventListener("change", search);
$("back").addEventListener("click", () => route({name: null, tab: null, group: null}));
$("guide").addEventListener("click", () => route({view: "guide"}));
$("guide-back").addEventListener("click", () => route({view: null}));
$("reload").addEventListener("click", async () => {
  $("reload").disabled = true; status("Checking the latest verified snapshot…");
  try {
    summary = await api("/api/reload", {}, {method: "POST"});
    snapshotLabels();
    await render();
  } catch (error) { status(error.message, true); }
  finally { $("reload").disabled = false; }
});
window.addEventListener("hashchange", () => { clearTimeout(searchTimer); render(); });
document.addEventListener("keydown", event => {
  if (event.key === "/" && !["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement.tagName)) {
    event.preventDefault(); focusSearch = true;
    route({name: null, tab: null, group: null, level: null, view: null});
    if (!$("search-view").hidden) { $("query").focus(); focusSearch = false; }
  }
});
initialize();
