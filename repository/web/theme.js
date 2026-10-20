/* theme: a stored choice wins, otherwise the system preference applies; loaded before the stylesheet to avoid a flash */
(() => {
  const root = document.documentElement;
  const system = matchMedia("(prefers-color-scheme: dark)");
  let choice = null;
  try { choice = localStorage.getItem("theme"); } catch {}
  if (choice !== "light" && choice !== "dark") choice = null;

  /** set the effective theme on the root element. */
  const apply = () => { root.dataset.theme = choice || (system.matches ? "dark" : "light"); };
  apply();
  system.addEventListener("change", apply);

  document.addEventListener("DOMContentLoaded", () => {
    const toggle = document.getElementById("theme-toggle");
    const label = () => toggle.setAttribute("aria-label", `Switch to ${root.dataset.theme === "dark" ? "light" : "dark"} theme`);
    label();
    new MutationObserver(label).observe(root, {attributes: true, attributeFilter: ["data-theme"]});
    toggle.addEventListener("click", () => {
      choice = root.dataset.theme === "dark" ? "light" : "dark";
      try { localStorage.setItem("theme", choice); } catch {}
      apply();
    });
  });
})();
