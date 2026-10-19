# Destruction Test Range

A playable demo of a destruction engine: pick something to hit with and a material or object, then tap, throw or
swing at it. Works on phones.

**Play it:** https://gavinjamesme.github.io/destruction-engine-demo/

This repository holds only the built demo (the page and the compiled engine). The engine's source is private.
All rights reserved.

## How it runs

- The page draws; the destruction engine and the physics run in a separate thread (`sim-worker.js`), so a big
  break never stalls the drawing.
- On browsers that allow it, the engine also spreads its heavy work over a few more threads (`destruct-mt.js`).
  GitHub Pages can't send the headers browsers want for that, so `coi.js` adds them through a service worker and
  reloads the page once. Elsewhere the single-thread engine (`destruct.js`) runs.
- Physics: [Rapier](https://rapier.rs) (Apache-2.0). Drawing: [three.js](https://threejs.org) (MIT). Both load
  from public CDNs.
