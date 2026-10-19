// Turns on wasm threads where the host can't send the headers for them (GitHub Pages): browsers only allow
// SharedArrayBuffer on cross-origin isolated pages (COOP + COEP headers). Loaded by the page, this registers itself as
// a service worker that adds those headers to every response, then reloads once so the page runs under it. Where the
// page is already isolated (tools/serve_web.py), or service workers aren't allowed (a sandboxed preview), it does
// nothing and the demo runs its single-thread engine.
if (typeof window === "undefined") {
  // ---- as the service worker
  self.addEventListener("install", () => self.skipWaiting());
  self.addEventListener("activate", (e) => e.waitUntil(self.clients.claim()));
  self.addEventListener("fetch", (e) => {
    const r = e.request;
    if (r.cache === "only-if-cached" && r.mode !== "same-origin") return;
    e.respondWith(fetch(r).then((res) => {
      if (res.status === 0) return res;  // opaque: can't be changed (the page asks for everything with CORS)
      const headers = new Headers(res.headers);
      headers.set("Cross-Origin-Embedder-Policy", "require-corp");
      headers.set("Cross-Origin-Opener-Policy", "same-origin");
      headers.set("Cross-Origin-Resource-Policy", "cross-origin");
      return new Response(res.body, { status: res.status, statusText: res.statusText, headers });
    }));
  });
} else {
  // ---- as the page's script
  (() => {
    if (window.crossOriginIsolated || !window.isSecureContext) return;
    let sw;
    try { sw = navigator.serviceWorker; } catch { return; }
    if (!sw) return;
    // Reload at most once per tab, so a browser that won't isolate the page doesn't loop.
    const once = () => {
      try {
        if (sessionStorage.getItem("coiReloaded")) return;
        sessionStorage.setItem("coiReloaded", "1");
      } catch { return; }
      window.location.reload();
    };
    sw.register(document.currentScript.src).then((reg) => {
      if (sw.controller) return;  // already under it, yet not isolated: this browser won't, run single-thread
      if (reg.active) once();
      else sw.addEventListener("controllerchange", once);
    }, () => { /* not allowed here: single-thread */ });
  })();
}
