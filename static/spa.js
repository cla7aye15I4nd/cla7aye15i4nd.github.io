(() => {
  const cache = new Map();
  const parser = new DOMParser();
  let navigating = false;

  const samePath = (a, b) =>
    a.origin === b.origin && a.pathname === b.pathname && a.search === b.search;

  const isHtmlNavigation = (url) => {
    const ext = url.pathname.split("/").pop().split(".").pop();
    return !url.pathname.includes("/static/") && (!ext || ext === url.pathname.split("/").pop() || ext === "html");
  };

  const eligibleLink = (link, event) => {
    if (!link || event.defaultPrevented || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) {
      return false;
    }
    if (link.target || link.download || link.hasAttribute("data-no-spa")) {
      return false;
    }
    const url = new URL(link.href, window.location.href);
    if (url.origin !== window.location.origin || !/^https?:$/.test(url.protocol)) {
      return false;
    }
    if (samePath(url, window.location) && url.hash) {
      return false;
    }
    return isHtmlNavigation(url);
  };

  const fillCurrentYear = () => {
    const year = String(new Date().getFullYear());
    document.querySelectorAll("[data-current-year]").forEach((node) => {
      node.textContent = year;
    });
  };

  const normalizeUrl = (url) => {
    const next = new URL(url, window.location.href);
    next.hash = "";
    return next.href;
  };

  const fetchPage = async (url) => {
    const key = normalizeUrl(url);
    if (cache.has(key)) {
      return cache.get(key);
    }
    const response = await fetch(key, {
      credentials: "same-origin",
      headers: { "X-Requested-With": "spa-navigation" },
    });
    if (!response.ok) {
      throw new Error(`Navigation failed: ${response.status}`);
    }
    const html = await response.text();
    cache.set(key, html);
    return html;
  };

  const isBaseHeadNode = (node) => {
    if (node.nodeType !== Node.ELEMENT_NODE) {
      return true;
    }
    const tag = node.tagName.toLowerCase();
    if (tag === "title") {
      return true;
    }
    if (tag === "meta") {
      const attr = node.getAttribute("charset") || node.getAttribute("name");
      return attr === "UTF-8" || attr === "viewport";
    }
    if (tag === "link" && node.getAttribute("href")?.includes("static/style.css")) {
      return true;
    }
    if (tag === "script") {
      const src = node.getAttribute("src") || "";
      return src.includes("static/spa.js") || src.includes("googletagmanager.com");
    }
    return false;
  };

  const appendScript = (script) =>
    new Promise((resolve) => {
      const src = script.getAttribute("src");
      if (src) {
        const absoluteSrc = new URL(src, document.baseURI).href;
        const existing = [...document.scripts].find((node) => node.src === absoluteSrc);
        if (existing) {
          resolve();
          return;
        }
      }

      const clone = document.createElement("script");
      [...script.attributes].forEach((attr) => clone.setAttribute(attr.name, attr.value));
      clone.dataset.spaExtra = "true";
      if (!src) {
        clone.textContent = script.textContent;
        document.head.appendChild(clone);
        resolve();
        return;
      }
      clone.onload = () => resolve();
      clone.onerror = () => resolve();
      document.head.appendChild(clone);
    });

  const syncHead = async (nextDocument) => {
    document.title = nextDocument.title;
    document.documentElement.lang = nextDocument.documentElement.lang || document.documentElement.lang;

    const nextDescription = nextDocument.head.querySelector('meta[name="description"]');
    document.head.querySelectorAll('meta[name="description"]').forEach((node) => node.remove());
    if (nextDescription) {
      document.head.appendChild(nextDescription.cloneNode(true));
    }

    document.head.querySelectorAll("[data-spa-extra]").forEach((node) => node.remove());

    for (const node of nextDocument.head.children) {
      if (isBaseHeadNode(node)) {
        continue;
      }
      if (node.tagName.toLowerCase() === "script") {
        await appendScript(node);
      } else {
        const clone = node.cloneNode(true);
        clone.dataset.spaExtra = "true";
        document.head.appendChild(clone);
      }
    }
  };

  const runPageEnhancements = () => {
    fillCurrentYear();
    initTocToggle();
    if (window.hljs) {
      window.hljs.highlightAll();
    }
    if (window.MathJax?.typesetPromise) {
      window.MathJax.typesetPromise().catch(() => {});
    }
  };

  const swapBody = (nextDocument) => {
    document.body.innerHTML = nextDocument.body.innerHTML;
    document.body.id = nextDocument.body.id || "";
    document.body.className = nextDocument.body.className || "";
  };

  const initTocToggle = () => {
    const page = document.querySelector(".blog-article-page");
    const toggle = document.querySelector(".toc-toggle");
    if (!page || !toggle) {
      return;
    }

    const setCollapsed = (collapsed) => {
      page.classList.toggle("is-toc-collapsed", collapsed);
      toggle.textContent = collapsed ? "Show" : "Hide";
      toggle.setAttribute("aria-expanded", String(!collapsed));
      try {
        window.localStorage.setItem("toc-collapsed", collapsed ? "true" : "false");
      } catch {
        // Ignore storage failures in private browsing or locked-down contexts.
      }
    };

    let collapsed = false;
    try {
      collapsed = window.localStorage.getItem("toc-collapsed") === "true";
    } catch {
      collapsed = false;
    }
    setCollapsed(collapsed);
    toggle.addEventListener("click", () => {
      setCollapsed(!page.classList.contains("is-toc-collapsed"));
    });
  };

  const navigate = async (url, { history = true } = {}) => {
    if (navigating) {
      return;
    }
    navigating = true;
    document.documentElement.dataset.spaLoading = "true";
    try {
      const target = new URL(url, window.location.href);
      const html = await fetchPage(target.href);
      const nextDocument = parser.parseFromString(html, "text/html");
      await syncHead(nextDocument);
      swapBody(nextDocument);
      runPageEnhancements();
      if (history) {
        window.history.pushState({ spa: true }, "", target.href);
      }
      if (target.hash) {
        document.getElementById(decodeURIComponent(target.hash.slice(1)))?.scrollIntoView();
      } else {
        window.scrollTo({ top: 0, left: 0, behavior: "auto" });
      }
      window.dispatchEvent(new CustomEvent("spa:navigation", { detail: { url: target.href } }));
    } catch (error) {
      window.location.href = url;
    } finally {
      document.documentElement.dataset.spaLoading = "false";
      navigating = false;
    }
  };

  document.addEventListener("click", (event) => {
    const link = event.target.closest("a[href]");
    if (!eligibleLink(link, event)) {
      return;
    }
    event.preventDefault();
    navigate(link.href);
  });

  window.addEventListener("popstate", () => {
    navigate(window.location.href, { history: false });
  });

  document.addEventListener("DOMContentLoaded", runPageEnhancements);
})();
