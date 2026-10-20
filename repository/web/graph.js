"use strict";

/**
 * the dependency graph: one level of the atlas at a time, foundations at the
 * bottom, every drawn edge an exact prerequisite. subjects and modules open
 * into their contents with a zoom; declarations open their pages.
 */
(() => {
  const $ = id => document.getElementById(id);
  const canvas = $("graph-canvas");
  const stage = $("graph-stage");
  const context = canvas.getContext("2d");
  const kindLabels = {subject: "Subject", module: "Module", theorem: "Theorem", definition: "Definition",
    inductive: "Structure", opaque: "Opaque definition", axiom: "Axiom", quotient_primitive: "Quotient primitive"};
  const fonts = {sans: "Geist, system-ui, sans-serif", mono: "JuliaMono, ui-monospace, Menlo, monospace"};
  const views = new Map();
  const statements = new Map();
  let api = null;
  let current = null;
  let camera = {x: 0, y: 0, k: 1};
  let alpha = 1;
  let palette = {};
  let hover = null;
  let selected = null;
  let highlight = null;
  let animation = null;
  let pointer = null;
  const touches = new Map();
  let digest = null;
  let prefetchTimer = null;
  let width = 0;
  let height = 0;

  /* data */

  function load(at) {
    if (!views.has(at)) {
      const request = api("/api/atlas", {node: at}).catch(error => { views.delete(at); throw error; });
      views.set(at, request);
    }
    return views.get(at);
  }

  function drillable(node) {
    return node.kind === "subject" || node.kind === "module";
  }

  function graphHash(id) {
    return !id || id === "s:mathematics" ? "#view=graph" : "#" + new URLSearchParams({view: "graph", at: id});
  }

  function target(node) {
    return drillable(node) ? graphHash(node.id) : "#" + new URLSearchParams({name: node.id.slice(2), tab: "statement"});
  }

  /* layout */

  function measure(text, font) {
    context.font = font;
    return context.measureText(text).width;
  }

  function ellipsize(text, font, limit) {
    if (measure(text, font) <= limit) return text;
    let low = 0, high = text.length;
    while (low < high) {
      const middle = Math.ceil((low + high) / 2);
      if (measure(text.slice(0, middle) + "…", font) <= limit) low = middle;
      else high = middle - 1;
    }
    return text.slice(0, low) + "…";
  }

  /** find the namespace most declarations share, so labels can drop it. */
  function sharedPrefix(nodes) {
    const names = nodes.filter(node => node.role === "child" && node.id.startsWith("d:")).map(node => node.title);
    if (names.length < 4) return "";
    const counts = new Map();
    for (const name of names) {
      const parts = name.split(".");
      for (let index = 1; index < parts.length; index++) {
        const prefix = parts.slice(0, index).join(".") + ".";
        counts.set(prefix, (counts.get(prefix) || 0) + 1);
      }
    }
    let best = "";
    for (const [prefix, total] of counts) {
      if (total >= names.length * 0.6 && prefix.length > best.length) best = prefix;
    }
    return best;
  }

  function layout(view) {
    const prefix = sharedPrefix(view.nodes);
    const declarations = view.nodes.some(node => node.role === "child" && node.id.startsWith("d:"));
    const nodes = view.nodes.map((node, index) => {
      const compact = node.id.startsWith("d:");
      const item = {...node, index, compact, prerequisites: [], dependents: [], links: [], users: [], weights: new Map()};
      if (compact) {
        const name = node.role === "child" && prefix && node.title.startsWith(prefix) ? node.title.slice(prefix.length) : node.title;
        item.font = `400 13px ${fonts.mono}`;
        item.label = ellipsize(name, item.font, 220);
        item.w = Math.max(56, measure(item.label, item.font) + 24);
        item.h = 30;
      } else {
        item.font = `${node.kind === "subject" ? 600 : 500} 14px ${fonts.sans}`;
        item.label = ellipsize(node.title, item.font, 240);
        item.sub = node.units.toLocaleString();
        item.subFont = `400 12px ${fonts.sans}`;
        item.w = measure(item.label, item.font) + measure(item.sub, item.subFont) + 44;
        item.h = 40;
      }
      return item;
    });
    for (const [source, destination, weight, flag] of view.edges) {
      nodes[source].links.push({node: destination, weight, flag});
      nodes[destination].users.push({node: source, weight, flag});
      if (flag === 1) {
        nodes[source].weights.set(destination, weight);
        nodes[source].prerequisites.push(destination);
        nodes[destination].dependents.push(source);
      }
    }
    const levels = new Map();
    for (const node of nodes) {
      if (!levels.has(node.level)) levels.set(node.level, []);
      levels.get(node.level).push(node);
    }
    const order = [...levels.keys()].sort((a, b) => a - b);
    for (const level of order) levels.get(level).sort((a, b) => a.title.localeCompare(b.title));
    // barycentre sweeps reduce crossings between neighbouring rows.
    const rank = new Map();
    const reindex = () => { for (const level of order) levels.get(level).forEach((node, index, row) => rank.set(node.index, (index + 0.5) / row.length)); };
    reindex();
    for (let sweep = 0; sweep < 6; sweep++) {
      const upward = sweep % 2 === 0;
      for (const level of upward ? order : [...order].reverse()) {
        const row = levels.get(level);
        const score = new Map();
        for (const node of row) {
          const neighbours = upward ? node.prerequisites : node.dependents;
          score.set(node.index, neighbours.length ? neighbours.reduce((sum, item) => sum + rank.get(item), 0) / neighbours.length : rank.get(node.index));
        }
        row.sort((a, b) => score.get(a.index) - score.get(b.index));
        row.forEach((node, index) => rank.set(node.index, (index + 0.5) / row.length));
      }
    }
    const gap = declarations ? 10 : 16;
    const rowGap = declarations ? 14 : 16;
    // level gaps shrink so a tall, narrow view still fits the screen at a readable size.
    const rowHeights = order.reduce((sum, level) => sum + Math.max(...levels.get(level).map(node => node.h)), 0);
    const room = (height - 96 - rowHeights) / Math.max(1, order.length - 1);
    const levelGap = Math.round(Math.min(declarations ? 64 : 72, Math.max(declarations ? 40 : 30, room)));
    const total = nodes.reduce((sum, node) => sum + (node.w + gap) * (node.h + rowGap), 0);
    // on narrow screens a subject view wraps its rows so it still reads at fit.
    const limit = declarations ? Math.max(900, Math.sqrt(total) * 1.7)
      : Math.min(Math.max(1100, Math.sqrt(total) * 1.7), Math.max(260, (width - 40) / 0.8));
    let y = 0;
    for (const level of [...order].reverse()) {
      const rows = [[]];
      let used = 0;
      for (const node of levels.get(level)) {
        if (used && used + node.w > limit) { rows.push([]); used = 0; }
        rows[rows.length - 1].push(node);
        used += node.w + gap;
      }
      rows.forEach((row, index) => {
        const rowWidth = row.reduce((sum, node) => sum + node.w, 0) + gap * (row.length - 1);
        const rowHeight = Math.max(...row.map(node => node.h));
        let x = -rowWidth / 2;
        for (const node of row) {
          node.x = x;
          node.y = y + (rowHeight - node.h) / 2;
          x += node.w + gap;
        }
        y += rowHeight + (index < rows.length - 1 ? rowGap : levelGap);
      });
    }
    const bounds = {left: Infinity, right: -Infinity, top: Infinity, bottom: -Infinity};
    for (const node of nodes) {
      bounds.left = Math.min(bounds.left, node.x);
      bounds.right = Math.max(bounds.right, node.x + node.w);
      bounds.top = Math.min(bounds.top, node.y);
      bounds.bottom = Math.max(bounds.bottom, node.y + node.h);
    }
    return {view, nodes, bounds, prefix, declarations};
  }

  /* camera */

  function fit(scene, scale = 1) {
    const {bounds} = scene;
    const k = Math.min((width - 64) / (bounds.right - bounds.left), (height - 64) / (bounds.bottom - bounds.top), 1.15);
    return {x: (bounds.left + bounds.right) / 2, y: (bounds.top + bounds.bottom) / 2, k: Math.max(0.04, k) * scale};
  }

  function around(node, fill = 0.5) {
    return {x: node.x + node.w / 2, y: node.y + node.h / 2, k: Math.min(width * fill / node.w, height * fill / node.h, 6)};
  }

  function toScreen(x, y) {
    return [(x - camera.x) * camera.k + width / 2, (y - camera.y) * camera.k + height / 2];
  }

  function toWorld(x, y) {
    return [(x - width / 2) / camera.k + camera.x, (y - height / 2) / camera.k + camera.y];
  }

  const reduced = () => matchMedia("(prefers-reduced-motion: reduce)").matches;

  /** move the camera (and the scene's opacity) with an eased tween. */
  function tween(to, duration, easing, opacity = alpha) {
    if (animation) animation.cancel();
    if (reduced()) duration = 0;
    const from = {...camera, alpha};
    return new Promise(resolve => {
      const started = performance.now();
      let cancelled = false;
      animation = {cancel() { cancelled = true; resolve(); }};
      function frame(now) {
        if (cancelled) return;
        const progress = duration ? Math.min(1, (now - started) / duration) : 1;
        const eased = easing(progress);
        // interpolate zoom geometrically so the motion feels even at every scale.
        camera.k = from.k * Math.pow(to.k / from.k, eased);
        camera.x = from.x + (to.x - from.x) * eased;
        camera.y = from.y + (to.y - from.y) * eased;
        alpha = from.alpha + (opacity - from.alpha) * eased;
        draw();
        if (progress < 1) requestAnimationFrame(frame);
        else { animation = null; resolve(); }
      }
      requestAnimationFrame(frame);
    });
  }

  const easeOut = t => 1 - Math.pow(1 - t, 3);
  const easeIn = t => t * t * t;
  const easeInOut = t => t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;

  /* drawing */

  function readPalette() {
    const style = getComputedStyle(document.documentElement);
    const value = name => style.getPropertyValue(name).trim();
    palette = {ground: value("--ground"), surface: value("--surface"), raised: value("--raised"), border: value("--border"),
      strong: value("--control"), text: value("--text"), muted: value("--muted"), accent: value("--accent"),
      edge: value("--edge"), accentText: value("--accent-text")};
  }

  function resize() {
    const box = stage.getBoundingClientRect();
    const ratio = window.devicePixelRatio || 1;
    width = box.width;
    height = box.height;
    canvas.width = Math.round(width * ratio);
    canvas.height = Math.round(height * ratio);
    canvas.style.width = width + "px";
    canvas.style.height = height + "px";
    context.setTransform(ratio, 0, 0, ratio, 0, 0);
    draw();
  }

  function closure(scene, start, field) {
    const reached = new Set([start]);
    const pending = [start];
    while (pending.length) {
      for (const item of scene.nodes[pending.pop()][field]) {
        if (!reached.has(item)) { reached.add(item); pending.push(item); }
      }
    }
    return reached;
  }

  function setHighlight(node) {
    if (!current || !node) { highlight = null; return; }
    highlight = {node: node.index, below: closure(current, node.index, "prerequisites"), above: closure(current, node.index, "dependents")};
  }

  function roundRect(x, y, w, h, r) {
    context.beginPath();
    context.roundRect(x, y, w, h, r);
  }

  function nodeStyle(node) {
    if (node.role === "foundation") return {fill: palette.accent, stroke: null, text: palette.accentText};
    if (node.role === "external") return {fill: palette.ground, stroke: palette.strong, line: 1, dash: true, text: palette.muted};
    if (node.kind === "definition" || node.kind === "opaque") return {fill: palette.raised, stroke: null, text: palette.text};
    if (node.kind === "inductive") return {fill: palette.surface, stroke: palette.text, line: 1.5, text: palette.text};
    if (node.kind === "subject") return {fill: palette.surface, stroke: palette.strong, line: 1, text: palette.text};
    return {fill: palette.surface, stroke: palette.border, line: 1, text: palette.text};
  }

  function draw() {
    context.clearRect(0, 0, width, height);
    if (!current) return;
    const k = camera.k;
    context.save();
    context.globalAlpha = alpha;
    context.translate(width / 2, height / 2);
    context.scale(k, k);
    context.translate(-camera.x, -camera.y);
    const view = {left: camera.x - width / 2 / k, right: camera.x + width / 2 / k, top: camera.y - height / 2 / k, bottom: camera.y + height / 2 / k};
    const visible = node => node.x < view.right && node.x + node.w > view.left && node.y < view.bottom && node.y + node.h > view.top;
    const active = highlight;
    const tone = (a, b) => {
      if (!active) return "base";
      if (active.below.has(a) && active.below.has(b)) return "below";
      if (active.above.has(a) && active.above.has(b)) return "above";
      return "dim";
    };
    // edges run from a node's foot down to the head of each prerequisite.
    // edges among outside prerequisites and foundations are context, so they stay faint.
    const passes = {context: [], base: [], dim: [], above: [], below: []};
    for (const node of current.nodes) {
      for (const item of node.prerequisites) {
        const pass = tone(node.index, item);
        passes[pass === "base" && node.role === "external" ? "context" : pass].push([node, current.nodes[item]]);
      }
    }
    const heavy = !current.declarations;
    for (const pass of ["context", "dim", "base", "above", "below"]) {
      const edges = passes[pass];
      if (!edges.length) continue;
      context.strokeStyle = pass === "below" ? palette.accent : pass === "above" ? palette.text : palette.edge;
      context.globalAlpha = alpha * (pass === "dim" ? 0.35 : pass === "context" ? 0.4 : 1);
      for (const [source, destination] of edges) {
        const x1 = source.x + source.w / 2, y1 = source.y + source.h;
        const x2 = destination.x + destination.w / 2, y2 = destination.y;
        if (Math.max(x1, x2) < view.left || Math.min(x1, x2) > view.right || y2 < view.top || y1 > view.bottom) continue;
        const base = heavy ? 1 + Math.min(2.5, Math.log10(source.weights.get(destination.index) || 1) / 2) : 1;
        context.lineWidth = (pass === "below" || pass === "above" ? base + 0.5 : base) / Math.max(k, 0.5);
        const bend = Math.max(24, (y2 - y1) * 0.5);
        context.beginPath();
        context.moveTo(x1, y1);
        context.bezierCurveTo(x1, y1 + bend, x2, y2 - bend, x2, y2);
        context.stroke();
      }
    }
    const labels = k * 13 >= 7;
    for (const node of current.nodes) {
      if (!visible(node)) continue;
      const style = nodeStyle(node);
      const dim = active && !active.below.has(node.index) && !active.above.has(node.index);
      context.globalAlpha = alpha * (dim ? 0.25 : 1);
      roundRect(node.x, node.y, node.w, node.h, node.compact ? 6 : 8);
      context.fillStyle = style.fill;
      context.fill();
      const emphasised = active && active.node === node.index;
      const focused = current.view.focus === node.id;
      if (emphasised || focused) {
        context.lineWidth = 2 / Math.max(k, 0.5);
        context.strokeStyle = focused ? palette.accent : palette.text;
        context.stroke();
      } else if (active && active.below.has(node.index)) {
        context.lineWidth = 1.5 / Math.max(k, 0.5);
        context.strokeStyle = palette.accent;
        context.stroke();
      } else if (style.stroke) {
        context.lineWidth = style.line / Math.max(k, 0.75);
        context.strokeStyle = style.stroke;
        if (style.dash) context.setLineDash([4 / Math.max(k, 0.75), 3 / Math.max(k, 0.75)]);
        context.stroke();
        context.setLineDash([]);
      }
      if (!labels) continue;
      context.fillStyle = style.text;
      context.textBaseline = "middle";
      if (node.compact) {
        context.font = node.font;
        context.textAlign = "center";
        context.fillText(node.label, node.x + node.w / 2, node.y + node.h / 2 + 0.5);
      } else {
        context.textAlign = "left";
        context.font = node.font;
        context.fillText(node.label, node.x + 16, node.y + node.h / 2 + 0.5);
        context.textAlign = "right";
        context.font = node.subFont;
        context.fillStyle = palette.muted;
        context.fillText(node.sub, node.x + node.w - 14, node.y + node.h / 2 + 0.5);
      }
    }
    context.restore();
  }

  /* chrome */

  function element(tag, text, className) {
    const node = document.createElement(tag);
    if (text !== undefined && text !== null) node.textContent = text;
    if (className) node.className = className;
    return node;
  }

  /** the drawn declarations of a subject or module, as theorems and definitions. */
  function split(item) {
    const definitions = item.units - item.theorems;
    return `${item.theorems.toLocaleString()} ${item.theorems === 1 ? "theorem" : "theorems"} · ${definitions.toLocaleString()} ${definitions === 1 ? "definition" : "definitions"}`;
  }

  function renderChrome(scene) {
    const {view} = scene;
    const trail = $("graph-trail");
    trail.replaceChildren();
    view.trail.slice(0, -1).forEach(item => {
      const link = element("a", item.title);
      link.href = graphHash(item.id);
      trail.append(link);
    });
    $("graph-title").textContent = view.title;
    const children = view.nodes.filter(node => node.role === "child");
    const parts = [split(view)];
    if (view.id.startsWith("m:")) parts.unshift(view.id.slice(2));
    $("graph-meta").textContent = parts.join(" · ");
    const legend = $("graph-legend");
    legend.replaceChildren();
    const kinds = new Set(children.map(node => node.kind));
    const entries = [["subject", "Subject"], ["module", "Module"], ["theorem", "Theorem"], ["definition", "Definition"], ["inductive", "Structure"]]
      .filter(([kind]) => kinds.has(kind));
    if (view.nodes.some(node => node.role === "external")) entries.push(["external", "Outside prerequisite"]);
    if (view.nodes.some(node => node.role === "foundation")) entries.push(["foundation", "Axiom or primitive"]);
    for (const [kind, label] of entries) {
      const item = element("span", null, "legend-item");
      item.append(element("i", null, "swatch swatch-" + kind), document.createTextNode(label));
      legend.append(item);
    }
    const list = $("graph-list");
    list.replaceChildren();
    for (const node of scene.nodes) {
      const item = element("li");
      const link = element("a", `${node.title} (${kindLabels[node.kind] || node.kind})`);
      link.href = target(node);
      item.append(link);
      list.append(item);
    }
  }

  function linkList(scene, entries, heading) {
    if (!entries.length) return null;
    const block = element("div", null, "card-links");
    block.append(element("h3", heading));
    const list = element("ul");
    const sorted = [...entries].sort((a, b) => b.weight - a.weight || scene.nodes[a.node].title.localeCompare(scene.nodes[b.node].title));
    for (const entry of sorted.slice(0, 6)) {
      const other = scene.nodes[entry.node];
      const item = element("li");
      const link = element("a", other.title, other.compact ? "mono" : "");
      link.href = target(other);
      item.append(link);
      if (!scene.declarations && entry.weight > 1) item.append(element("span", entry.weight.toLocaleString(), "num"));
      list.append(item);
    }
    block.append(list);
    if (sorted.length > 6) block.append(element("p", `${(sorted.length - 6).toLocaleString()} more`, "card-more"));
    return block;
  }

  /** describe the whole view, its outside prerequisites and its foundations. */
  function summaryCard(scene) {
    const card = $("graph-card");
    const {view} = scene;
    card.classList.add("summary");
    card.replaceChildren(element("p", view.id.startsWith("m:") ? "Module" : view.trail.length > 1 ? "Subject" : "All subjects", "card-kind"),
      element("h2", view.title, "card-title"),
      element("p", split(view), "card-meta"));
    const bottom = (role, heading) => {
      const entries = scene.nodes.filter(node => node.role === role).map(node => ({node: node.index,
        weight: node.users.reduce((sum, item) => sum + (scene.nodes[item.node].role === "child" ? item.weight : 0), 0)}));
      const block = linkList(scene, entries, heading);
      if (block) card.append(block);
    };
    bottom("external", "Rests on, outside this view");
    bottom("foundation", "Axioms and primitives");
    card.append(element("p", "Hover to trace prerequisites. Click to open.", "card-hint"));
  }

  function showCard(node, touch = false) {
    const card = $("graph-card");
    if (!current) return;
    if (!node) { summaryCard(current); return; }
    const scene = current;
    card.classList.remove("summary");
    card.replaceChildren();
    const kind = node.role === "external" ? `Outside prerequisite · ${kindLabels[node.kind] || node.kind}` : kindLabels[node.kind] || node.kind;
    card.append(element("p", kind, "card-kind"), element("h2", node.title, node.compact ? "card-title mono" : "card-title"));
    if (!node.compact) {
      card.append(element("p", split(node), "card-meta"));
    } else {
      const statement = element("pre", statements.get(node.id) || "", "card-statement");
      card.append(statement);
      if (!statements.has(node.id)) {
        api("/api/declaration", {name: node.id.slice(2)}).then(record => {
          statements.set(node.id, record.statement);
          if (current === scene) statement.textContent = record.statement;
        }).catch(() => {});
      }
    }
    // on touch the action leads, since the card is short and scrolls.
    if (touch) {
      const action = element("a", drillable(node) ? "Open" : "View declaration", "card-action");
      action.href = target(node);
      card.append(action);
    }
    const below = linkList(scene, node.links, "Rests on");
    const above = linkList(scene, node.users, "Used by");
    if (below) card.append(below);
    if (above) card.append(above);
    if (!below && node.role === "child") card.append(element("p", "Rests on the kernel rules alone.", "card-meta"));
    if (!touch) card.append(element("p", drillable(node) ? "Click to open" : "Click to view the declaration", "card-hint"));
  }

  /* interaction */

  function hit(x, y) {
    if (!current) return null;
    const [wx, wy] = toWorld(x, y);
    for (let index = current.nodes.length - 1; index >= 0; index--) {
      const node = current.nodes[index];
      if (wx >= node.x && wx <= node.x + node.w && wy >= node.y && wy <= node.y + node.h) return node;
    }
    return null;
  }

  function setHover(node) {
    if (node === hover) return;
    hover = node;
    canvas.style.cursor = node ? "pointer" : pointer?.moved ? "grabbing" : "grab";
    setHighlight(node || selected);
    // the card keeps the last node so its links stay reachable.
    if (node) showCard(node);
    draw();
    clearTimeout(prefetchTimer);
    if (node && drillable(node)) prefetchTimer = setTimeout(() => load(node.id).catch(() => {}), 120);
  }

  function activate(node) {
    if (!node) return;
    location.hash = target(node);
  }

  function zoomAt(x, y, factor) {
    const [wx, wy] = toWorld(x, y);
    const k = Math.min(6, Math.max(0.03, camera.k * factor));
    camera = {k, x: wx - (x - width / 2) / k, y: wy - (y - height / 2) / k};
    draw();
  }

  function local(event) {
    const box = canvas.getBoundingClientRect();
    return [event.clientX - box.left, event.clientY - box.top];
  }

  canvas.addEventListener("pointerdown", event => {
    canvas.setPointerCapture(event.pointerId);
    const [x, y] = local(event);
    touches.set(event.pointerId, [x, y]);
    if (touches.size === 1) pointer = {x, y, camera: {...camera}, moved: false, type: event.pointerType};
    else pointer = {pinch: Math.hypot(...[...touches.values()].reduce((a, b) => [a[0] - b[0], a[1] - b[1]])), k: camera.k, moved: true};
  });
  canvas.addEventListener("pointermove", event => {
    const [x, y] = local(event);
    if (touches.has(event.pointerId)) touches.set(event.pointerId, [x, y]);
    if (!pointer) { if (event.pointerType === "mouse") setHover(hit(x, y)); return; }
    if (pointer.pinch && touches.size === 2) {
      const points = [...touches.values()];
      const distance = Math.hypot(points[0][0] - points[1][0], points[0][1] - points[1][1]);
      const centre = [(points[0][0] + points[1][0]) / 2, (points[0][1] + points[1][1]) / 2];
      zoomAt(centre[0], centre[1], pointer.k * distance / pointer.pinch / camera.k);
      return;
    }
    if (!pointer.moved && Math.hypot(x - pointer.x, y - pointer.y) > 4) {
      pointer.moved = true;
      canvas.style.cursor = "grabbing";
    }
    if (pointer.moved && !pointer.pinch) {
      camera.x = pointer.camera.x - (x - pointer.x) / camera.k;
      camera.y = pointer.camera.y - (y - pointer.y) / camera.k;
      draw();
    }
  });
  function release(event) {
    const [x, y] = local(event);
    touches.delete(event.pointerId);
    const press = pointer;
    if (touches.size === 0) pointer = null;
    if (!press || press.moved || event.type === "pointercancel") { canvas.style.cursor = hover ? "pointer" : "grab"; return; }
    const node = hit(x, y);
    if (press.type !== "mouse") {
      // the first tap selects and explains; the card's action opens.
      if (node && selected === node) activate(node);
      selected = node;
      hover = null;
      setHighlight(node);
      showCard(node, true);
      draw();
      return;
    }
    if (node) activate(node);
    else { selected = null; setHighlight(null); showCard(null); draw(); }
  }
  canvas.addEventListener("pointerup", release);
  canvas.addEventListener("pointercancel", release);
  canvas.addEventListener("pointerleave", event => { if (event.pointerType === "mouse" && !pointer) setHover(null); });
  canvas.addEventListener("wheel", event => {
    event.preventDefault();
    const [x, y] = local(event);
    // pinches and mouse wheels zoom; two-finger trackpad scrolls pan.
    const wheel = event.deltaMode === 1 || (event.deltaX === 0 && Number.isInteger(event.deltaY) && Math.abs(event.deltaY) >= 50);
    if (event.ctrlKey || event.metaKey) zoomAt(x, y, Math.exp(-event.deltaY * 0.01));
    else if (wheel) zoomAt(x, y, Math.exp(-event.deltaY * (event.deltaMode === 1 ? 0.06 : 0.0022)));
    else {
      camera.x += event.deltaX / camera.k;
      camera.y += event.deltaY / camera.k;
      draw();
    }
  }, {passive: false});
  $("zoom-in").addEventListener("click", () => tween({...camera, k: Math.min(6, camera.k * 1.4)}, 220, easeOut));
  $("zoom-out").addEventListener("click", () => tween({...camera, k: Math.max(0.03, camera.k / 1.4)}, 220, easeOut));
  $("zoom-fit").addEventListener("click", () => current && tween(fit(current), 320, easeInOut));
  document.addEventListener("keydown", event => {
    const typing = ["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement.tagName);
    if (!current || $("graph-view").hidden || typing || event.metaKey || event.ctrlKey || event.altKey) return;
    const step = 80 / camera.k;
    const moves = {ArrowLeft: [-step, 0], ArrowRight: [step, 0], ArrowUp: [0, -step], ArrowDown: [0, step]};
    if (moves[event.key]) { camera.x += moves[event.key][0]; camera.y += moves[event.key][1]; draw(); }
    else if (event.key === "+" || event.key === "=") zoomAt(width / 2, height / 2, 1.25);
    else if (event.key === "-") zoomAt(width / 2, height / 2, 0.8);
    else if (event.key === "0") tween(fit(current), 320, easeInOut);
    else if (event.key === "Escape" && !$("graph-card").classList.contains("summary")) { selected = null; setHighlight(hover); showCard(null); draw(); }
    else if (event.key === "Escape" && current.view.trail.length > 1) {
      location.hash = graphHash(current.view.trail[current.view.trail.length - 2].id);
    } else return;
    event.preventDefault();
  });
  new ResizeObserver(() => { if (!$("graph-view").hidden) resize(); }).observe(stage);
  new MutationObserver(() => { readPalette(); draw(); }).observe(document.documentElement, {attributes: true, attributeFilter: ["data-theme"]});

  /* navigation */

  /** show a level of the atlas, zooming through the node that leads to it. */
  async function open(at, options) {
    api = options.api;
    if (options.digest !== digest) {
      // a refreshed snapshot invalidates every cached view and statement.
      views.clear();
      statements.clear();
      digest = options.digest;
    }
    readPalette();
    resize();
    await document.fonts.load(`13px JuliaMono`).catch(() => {});
    await document.fonts.load(`600 14px Geist`).catch(() => {});
    const previous = current;
    const doorway = previous?.nodes.find(node => node.id === at && drillable(node));
    const upward = previous && previous.view.trail.some(item => item.id === at || (!at && item.id === "s:mathematics")) && previous.view.id !== (at || "s:mathematics");
    const pending = load(at);
    if (doorway) await tween(around(doorway, 0.9), 420, easeIn, 0);
    else if (upward) await tween({...camera, k: camera.k * 0.45}, 300, easeIn, 0);
    let view;
    try { view = await pending; }
    catch (error) {
      // keep the previous level on screen when the next one cannot load.
      if (previous) await tween(fit(previous), 240, easeOut, 1);
      throw error;
    }
    if (!options.request()) return;
    const scene = layout(view);
    current = scene;
    hover = selected = null;
    setHighlight(null);
    renderChrome(scene);
    showCard(null);
    let goal = fit(scene);
    const focus = view.focus && scene.nodes.find(node => node.id === view.focus);
    if (focus) {
      selected = focus;
      setHighlight(focus);
      showCard(focus);
      goal = {x: focus.x + focus.w / 2, y: focus.y + focus.h / 2, k: Math.max(goal.k, 1)};
    }
    if (doorway) {
      camera = {...goal, k: goal.k * 0.3};
      alpha = 0;
      await tween(goal, 520, easeOut, 1);
    } else if (upward) {
      const child = scene.nodes.find(node => previous.view.trail.some(item => item.id === node.id) || node.id === previous.view.id);
      camera = child ? around(child, 0.9) : {...goal, k: goal.k * 2};
      alpha = 0;
      await tween(goal, 520, easeOut, 1);
    } else if (!previous || previous.view.id !== view.id) {
      camera = {...goal, k: goal.k * 0.94};
      alpha = 0;
      await tween(goal, 320, easeOut, 1);
    } else {
      camera = goal;
      alpha = 1;
      draw();
    }
  }

  window.MathGraph = {open};
})();
