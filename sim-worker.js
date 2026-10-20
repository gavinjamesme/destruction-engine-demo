// The test range's simulation, off the page's thread: the destruction engine and the physics (Rapier) run here, the
// page only draws, plays the effects and reads the fingers. Like a game on Quest: the render thread never waits on a
// break, and the engine spreads its own heavy work over a small pool of threads when the browser allows it
// (destruct-mt.js; otherwise the single-thread destruct.js).
//
// Page -> here: init, build, step (n steps of 1/60 s), strike, throw, swingStart / swingMove / swingEnd, blast,
// setting. Here -> page: ready (the catalog), then one "frame" per step request and per build: what changed (chunk
// meshes, bodies), where moving bodies are, events, effects, thrown things, the log line and timings.
import RAPIER from "https://cdn.jsdelivr.net/npm/@dimforge/rapier3d-compat@0.12.0/rapier.es.js";

const KIND = ["blunt", "edge", "pointed", "blast"];
const EVENT_NAMES = ["break", "crumble", "debris_hit", "collapsed", "deform", "crater"];
const ROUND = new Set(["baseball", "fist", "kick", "baseball_bat", "wrecking_ball", "grenade", "firecracker"]);
const PANES = new Set(["glass", "mirror"]);
const SHEETS = new Set(["drywall", "cardboard", "paper", "tile", "sheet_metal", "tin", "leather", "pcb", "tempered_glass", "acrylic", "aluminum_foil"]);
// How many threads the engine's pool gets in the threaded build: leave room for the page and this worker. Must match
// PTHREAD_POOL_SIZE in tools/build_web.ps1 (the threads are started ahead, at load).
const POOL = Math.min(4, Math.max(1, (self.navigator.hardwareConcurrency || 2) - 2));

let M, world, phys, queue, threads = 0;
let PHONE = false, HULL_POINTS = 64, COMMAND_BUDGET_MS = 8;
const L = {};
const state = { budget: 1, soft: false, detail: 1, scale: 1, hold: -1 };
// Every object on the range: object id -> { info (its material), label, size, at (where its own origin stands) }.
const objects = new Map();
// Chunk and body ids are each object's own, so the maps below key them by object too.
const key = (o, id) => o * 4294967296 + id;
const IMPACTS = [], FAMILIES = [], MATERIALS = new Map(), PRESETS = new Map();
const bodies = new Map();      // key(object, body) -> { rb, object, id, static, reactive, particle, fresh }
const chunks = new Map();      // key(object, chunk) -> { collider, body (its key), points, mass, ... }
const byCollider = new Map();  // collider handle -> body key
const perf = { steps: 0, physics: 0, engine: 0, commands: 0, geometry: 0, colliders: 0, chunkMeshes: 0, worstStep: 0, hit: 0 };

// ---------------------------------------------------------------- the engine's memory
// Views over the wasm heap, made again when it grows (with threads, any thread can grow it).
let mem = null;
const H = { u8: null, i32: null, u32: null, f32: null };
function views() {
  const b = mem ? mem.buffer : M.HEAPU8.buffer;
  if (H.u8 && H.u8.byteLength === b.byteLength && H.u8.byteLength > 0) return;
  H.u8 = new Uint8Array(b); H.i32 = new Int32Array(b); H.u32 = new Uint32Array(b); H.f32 = new Float32Array(b);
}
const f32 = (p) => H.f32[p >> 2];
const i32 = (p) => H.i32[p >> 2];
const u32 = (p) => H.u32[p >> 2];
const u64 = (p) => H.u32[p >> 2] + H.u32[(p >> 2) + 1] * 4294967296;
const str = (p) => (p ? M.UTF8ToString(p) : "");
function withString(s, fn) {
  const p = M.stringToNewUTF8(s);
  try { return fn(p); } finally { M._free(p); }
}
const heapScratch = { ptr: 0, floats: 0 };
function scratchFloats(n) {
  if (heapScratch.floats < n) {
    if (heapScratch.ptr) M._free(heapScratch.ptr);
    heapScratch.floats = Math.max(n, 2 * heapScratch.floats, 4096);
    heapScratch.ptr = M._malloc(heapScratch.floats * 4);
  }
  return heapScratch.ptr;
}

// ---------------------------------------------------------------- what goes back to the page
let out = fresh();
function fresh() { return { ops: [], transfer: [], events: [], markers: [], fx: [], log: null }; }
function marker(type, x, y, z, intensity) { out.markers.push([type, x, y, z, intensity]); }
function flush(extra) {
  // Moving bodies only: a settled piece keeps the pose the page already has.
  const poses = [];
  for (const [id, b] of bodies) {
    if (b.static || b.rb.isSleeping()) continue;
    const t = b.rb.translation(), q = b.rb.rotation();
    poses.push(id, t.x, t.y, t.z, q.x, q.y, q.z, q.w);
  }
  const proj = [];
  for (const item of thrown) {
    const t = item.rb.translation(), q = item.rb.rotation();
    proj.push(item.id, t.x, t.y, t.z, q.x, q.y, q.z, q.w, item.age);
  }
  const p = new Float64Array(poses), j = new Float64Array(proj), fx = new Float32Array(out.fx);
  let loose = 0;
  for (const b of bodies.values()) if (!b.static) loose++;
  self.postMessage({ type: "frame", ops: out.ops, poses: p, proj: j, fx, events: out.events, markers: out.markers, log: out.log,
    loose, pending: queued.length / (L.cmd || 1), perf: { ...perf }, ...extra }, [p.buffer, j.buffer, fx.buffer, ...out.transfer]);
  out = fresh();
}

// ---------------------------------------------------------------- start
async function init(msg) {
  PHONE = msg.phone;
  HULL_POINTS = PHONE ? 24 : 64;
  COMMAND_BUDGET_MS = PHONE ? 4 : 8;
  await RAPIER.init();
  let DestructModule = null;
  if (msg.threaded) {
    try { DestructModule = (await import("./destruct-mt.js")).default; } catch (err) { console.warn("threaded engine didn't load", err); }
  }
  if (DestructModule) {
    try { M = await DestructModule(); threads = POOL; } catch (err) { console.warn("threaded engine didn't start", err); M = null; }
  }
  if (!M) { M = await (await import("./destruct.js")).default(); threads = 0; }
  mem = M.wasmMemory || null;
  M._destruct_web_set_threads(threads);
  threads = M._destruct_web_threads();
  views();
  const lay = M._malloc(256);
  M._destruct_web_layout(lay);
  views();
  const v = (i) => H.i32[(lay >> 2) + i];
  Object.assign(L, {
    cmd: v(0), object: v(1), type: v(2), body: v(3), chunk: v(4), source: v(5), isStatic: v(6), reactive: v(7), flag: v(8),
    mass: v(9), placeLike: v(10), addLin: v(11), addAng: v(12), particle: v(13), evt: v(14), evType: v(15), evObject: v(16),
    evPos: v(17), evMass: v(18), evEnergy: v(19), evIntensity: v(20), evPieces: v(21), evMaterial: v(22), evDeform: v(23), evCause: v(24),
    fx: v(25), fxKind: v(26), fxPos: v(27), fxDir: v(28), fxSpread: v(29), fxCount: v(30), fxSize: v(31), fxSpeed: v(32), fxLife: v(33), fxColor: v(34),
  });
  M._free(lay);
  world = M._destruct_world_create();
  M._destruct_web_use_poses(world);
  phys = new RAPIER.World({ x: 0, y: -9.81, z: 0 });
  queue = new RAPIER.EventQueue(true);
  const groundBody = phys.createRigidBody(RAPIER.RigidBodyDesc.fixed().setTranslation(0, -0.5, 0));
  phys.createCollider(RAPIER.ColliderDesc.cuboid(100, 0.5, 100).setFriction(0.9), groundBody);
  catalog();
  self.postMessage({
    type: "ready", version: str(M._destruct_version()), threads,
    impacts: IMPACTS, families: FAMILIES, materials: [...MATERIALS.keys()], presets: [...PRESETS].map(([name, p]) => ({ name, label: p.label })),
  });
}

// The engine's libraries: what hits things, the materials and the ready-made objects.
function catalog() {
  const info = M._malloc(64);
  for (let i = 0; i < M._destruct_impactor_count(); i++) {
    const name = str(M._destruct_impactor_name(i));
    withString(name, (np) => M._destruct_impactor_get_info(np, info));
    views();
    IMPACTS.push({ name, label: name.replace(/_/g, " ").replace("bmg 50", ".50 BMG").replace("rifle 762", "7.62 rifle").replace("rifle 556", "5.56 rifle").replace("pistol 9mm", "9 mm pistol"),
      kind: KIND[i32(info + 8)], mass: f32(info + 12), speed: f32(info + 16), energy: f32(info + 20), faceW: f32(info + 24), faceH: f32(info + 28),
      description: str(u32(info + 4)) });
  }
  M._free(info);
  // The short list the demo offers: kinds of hit, each at a few strengths (index into IMPACTS, and a speed scale).
  const pr = M._malloc(32);
  for (let f = 0; f < M._destruct_impact_family_count(); f++) {
    const presets = [];
    for (let k = 0; k < M._destruct_impact_family_preset_count(f); k++) {
      if (!M._destruct_impact_family_preset(f, k, pr)) continue;
      views();
      const name = str(u32(pr + 4));
      presets.push({ label: str(u32(pr)), imp: IMPACTS.findIndex((x) => x.name === name), scale: f32(pr + 8), energy: f32(pr + 12) });
    }
    FAMILIES.push({ name: str(M._destruct_impact_family_name(f)), label: str(M._destruct_impact_family_label(f)), presets,
      def: M._destruct_impact_family_default(f) });
  }
  M._free(pr);
  for (let i = 0; i < M._destruct_material_count(); i++) {
    const name = str(M._destruct_material_name(i));
    MATERIALS.set(name, { pane: PANES.has(name), sheet: SHEETS.has(name) });
  }
  for (let i = 0; i < M._destruct_object_preset_count(); i++) {
    const name = str(M._destruct_object_preset_name(i));
    const d = M._malloc(256);
    M._destruct_object_desc_init(d);
    withString(name, (np) => M._destruct_object_desc_preset(d, np));
    views();
    // box_min / box_max sit after 7 pointer/int fields (vertices .. triangle_materials): offset 28
    const size = [f32(d + 40) - f32(d + 28), f32(d + 44) - f32(d + 32), f32(d + 48) - f32(d + 36)];
    M._free(d);
    PRESETS.set(name, { size, label: name.replace(/_/g, " ") });
  }
}

function materialInfo(object) {
  const p = M._malloc(64);
  M._destruct_object_material(world, object, p);
  views();
  const info = {
    name: str(u32(p)), family: str(u32(p + 4)), density: f32(p + 8), friction: f32(p + 12), bounce: f32(p + 16), opacity: f32(p + 28),
    tint: [f32(p + 36), f32(p + 40), f32(p + 44)], yieldPa: f32(p + 48), wobble: f32(p + 56),
  };
  M._free(p);
  return info;
}

// ---------------------------------------------------------------- chunks and colliders
// A chunk's finished vertex buffer (position, normal, uv and a tag per vertex: destruct_chunk_render_mesh) goes to the
// page as is; the collider points and bounds stay here.
function chunkGeometry(o, c) {
  const g0 = performance.now();
  perf.chunkMeshes++;
  const info = M._malloc(32);
  M._destruct_chunk_get_info(world, o, c, info);
  views();
  const mass = f32(info);
  M._free(info);
  const count = M._destruct_chunk_render_mesh(world, o, c, 0, 0);
  const buf = scratchFloats(count * 9);
  M._destruct_chunk_render_mesh(world, o, c, buf, count);
  views();
  const verts = H.f32.slice(buf >> 2, (buf >> 2) + count * 9);
  const pts = scratchFloats(HULL_POINTS * 3);
  const np = M._destruct_chunk_hull_points(world, o, c, pts, HULL_POINTS);
  views();
  const points = H.f32.slice(pts >> 2, (pts >> 2) + np * 3);
  // Bounds, for the cheap colliders (the same as three.js would compute: box centre, farthest vertex).
  const lo = [Infinity, Infinity, Infinity], hi = [-Infinity, -Infinity, -Infinity];
  for (let v = 0; v < count; v++) for (let k = 0; k < 3; k++) { const x = verts[v * 9 + k]; if (x < lo[k]) lo[k] = x; if (x > hi[k]) hi[k] = x; }
  const centre = count ? [(lo[0] + hi[0]) / 2, (lo[1] + hi[1]) / 2, (lo[2] + hi[2]) / 2] : [0, 0, 0];
  let r2 = 0;
  for (let v = 0; v < count; v++) {
    const dx = verts[v * 9] - centre[0], dy = verts[v * 9 + 1] - centre[1], dz = verts[v * 9 + 2] - centre[2];
    r2 = Math.max(r2, dx * dx + dy * dy + dz * dz);
  }
  perf.geometry += performance.now() - g0;
  return { verts, points, mass, centre, radius: Math.sqrt(r2), size: count ? [hi[0] - lo[0], hi[1] - lo[1], hi[2] - lo[2]] : [0, 0, 0] };
}

// Collision groups (membership << 16 | what it collides with). Pieces fresh from a break pass through each other and
// out of the standing structure they broke from until the engine says they are clear (SetBodyFresh), but still hit
// the ground and everything settled.
const SOLID_GROUPS = (0x0001 << 16) | 0xffff, FRESH_GROUPS = (0x0002 << 16) | 0x0001, STANDING_GROUPS = (0x0004 << 16) | 0xffff;
function makeCollider(entry, body) {
  const k0 = performance.now();
  // Particles (tiny debris, removed in a few seconds) get a cheap ball; everything else its convex hull.
  let desc = null;
  const [cx, cy, cz] = entry.centre;
  if (body.particle) desc = RAPIER.ColliderDesc.ball(Math.max(entry.radius * 0.6, 0.004)).setTranslation(cx, cy, cz);
  else if (entry.points.length >= 12) desc = RAPIER.ColliderDesc.convexHull(entry.points);
  if (!desc) {
    const s = entry.size;
    desc = RAPIER.ColliderDesc.cuboid(Math.max(s[0] / 2, 0.002), Math.max(s[1] / 2, 0.002), Math.max(s[2] / 2, 0.002)).setTranslation(cx, cy, cz);
  }
  const info = objects.get(body.object).info;
  desc.setMass(Math.max(entry.mass, 0.001)).setFriction(info.friction).setRestitution(info.bounce)
    .setCollisionGroups(body.static ? STANDING_GROUPS : body.fresh ? FRESH_GROUPS : SOLID_GROUPS);
  if (!body.static && body.reactive && !body.particle) {
    desc.setActiveEvents(RAPIER.ActiveEvents.CONTACT_FORCE_EVENTS).setContactForceEventThreshold(5);
  }
  const collider = phys.createCollider(desc, body.rb);
  byCollider.set(collider.handle, entry.body);
  perf.colliders += performance.now() - k0;
  return collider;
}
function dropCollider(entry) {
  if (!entry.collider) return;
  byCollider.delete(entry.collider.handle);
  if (phys.getCollider(entry.collider.handle)) phys.removeCollider(entry.collider, true);
  entry.collider = null;
}
function keepGeometry(entry, g) {
  entry.points = g.points; entry.mass = g.mass; entry.centre = g.centre; entry.radius = g.radius; entry.size = g.size;
}

// ---------------------------------------------------------------- carrying out the engine's commands
// A big break hands over hundreds of commands at once. They are carried out in order within a time budget per step;
// the rest wait for the next steps, so a grenade costs a few steps of a little work instead of one long stall.
let queued = new Uint8Array(0);
const queueBuf = { ptr: 0, bytes: 0 };
// A spinning body's pieces each move as their own point of it did: its velocity plus its spin times their offset
// from its centre of mass (docs/CODEBASE_REVIEW.md, R1). Rapier keeps a body's centre velocity when its mass changes
// and a new body only copies the velocity it is given, so the spin's share is added once the queue is drained (the
// bodies have all their pieces by then).
const spinFix = new Map();  // body key -> { com: [x, y, z] (world, before), w: {x, y, z} }
function bodyCom(bodyKey, rb) {
  let m = 0, x = 0, y = 0, z = 0;
  for (const e of chunks.values()) {
    if (e.body !== bodyKey || !e.centre) continue;
    const k = Math.max(e.mass || 0, 1e-6);
    m += k; x += k * e.centre[0]; y += k * e.centre[1]; z += k * e.centre[2];
  }
  if (m <= 0) return null;
  // Object space (the body's own frame) to world: rotate by its orientation (v + 2w(q x v) + 2q x (q x v)), then move.
  const q = rb.rotation(), t = rb.translation(), px = x / m, py = y / m, pz = z / m;
  const tx = 2 * (q.y * pz - q.z * py), ty = 2 * (q.z * px - q.x * pz), tz = 2 * (q.x * py - q.y * px);
  return [t.x + px + q.w * tx + (q.y * tz - q.z * ty), t.y + py + q.w * ty + (q.z * tx - q.x * tz), t.z + pz + q.w * tz + (q.x * ty - q.y * tx)];
}
function noteSpin(bodyKey, from) {  // remember where `from` (a body or the one a new body comes from) was centred
  if (spinFix.has(bodyKey) || !from || from.static) return;
  const w = from.rb.angvel();
  if (w.x * w.x + w.y * w.y + w.z * w.z < 1e-6) return;
  const com = bodyCom(from.key ?? bodyKey, from.rb);
  if (com) spinFix.set(bodyKey, { com, w });
}
function applySpinFix() {
  for (const [bodyKey, s] of spinFix) {
    const b = bodies.get(bodyKey);
    if (!b || b.static) continue;
    const now = bodyCom(bodyKey, b.rb);
    if (!now) continue;
    const r = [now[0] - s.com[0], now[1] - s.com[1], now[2] - s.com[2]], w = s.w, v = b.rb.linvel();
    b.rb.setLinvel({ x: v.x + w.y * r[2] - w.z * r[1], y: v.y + w.z * r[0] - w.x * r[2], z: v.z + w.x * r[1] - w.y * r[0] }, true);
  }
  spinFix.clear();
}
function runCommands() {
  const taken = M._destruct_take_commands(world);
  views();
  if (taken > 0) {
    const start = M._destruct_commands(world);
    const both = new Uint8Array(queued.length + taken * L.cmd);
    both.set(queued);
    both.set(H.u8.subarray(start, start + taken * L.cmd), queued.length);
    queued = both;
  }
  const n = queued.length / L.cmd;
  if (n <= 0) return;
  if (queueBuf.bytes < queued.length) {
    if (queueBuf.ptr) M._free(queueBuf.ptr);
    queueBuf.bytes = Math.max(queued.length, 2 * queueBuf.bytes, 65536);
    queueBuf.ptr = M._malloc(queueBuf.bytes);
  }
  views();
  H.u8.set(queued, queueBuf.ptr);
  const base = queueBuf.ptr, start = performance.now();
  let done = 0;
  for (let i = 0; i < n; i++, done++) {
    if (i >= 16 && performance.now() - start > COMMAND_BUDGET_MS) break;
    views();
    const p = base + i * L.cmd;
    const type = i32(p + L.type), o = u32(p + L.object), chunk = u32(p + L.chunk), id = u64(p + L.body);
    const c = key(o, chunk), body = key(o, id);
    switch (type) {
      case 0: {  // ChunkAdded
        const g = chunkGeometry(o, chunk);
        const e = { collider: null, body: 0 };
        keepGeometry(e, g);
        chunks.set(c, e);
        out.ops.push({ op: "add", c, o, verts: g.verts });
        out.transfer.push(g.verts.buffer);
        break;
      }
      case 1: {  // RetireChunk
        const e = chunks.get(c);
        if (!e) break;
        dropCollider(e);
        chunks.delete(c);
        out.ops.push({ op: "retire", c, fade: i32(p + L.flag) !== 0 });  // flag: tidied away (fade it), not replaced
        break;
      }
      case 2: {  // CreateBody
        const isStatic = i32(p + L.isStatic) !== 0;
        const like = bodies.get(key(o, u64(p + L.placeLike)));
        const at = objects.get(o)?.at || [0, 0, 0];  // a new body not like another: where the object stands
        // (A loose object starts 2 mm up and settles: one starting exactly on the ground along a seam between two of
        // its pieces' colliders can get a wild first contact in Rapier, flinging it.)
        let t = { x: at[0], y: at[1] + (isStatic ? 0 : 0.002), z: at[2] }, q = { x: 0, y: 0, z: 0, w: 1 }, v = { x: 0, y: 0, z: 0 }, w = { x: 0, y: 0, z: 0 };
        if (like) {
          t = like.rb.translation(); q = like.rb.rotation();
          if (!like.static) { v = like.rb.linvel(); w = like.rb.angvel(); }
        }
        // Air barely slows a tumbling piece (its drag torque is tiny at these speeds), so pieces keep their spin in flight
        // and contact friction stops them. Crumbs drawn as balls get more, so they don't roll away like marbles.
        const crumb = i32(p + L.particle) !== 0;
        const desc = (isStatic ? RAPIER.RigidBodyDesc.fixed()
          : RAPIER.RigidBodyDesc.dynamic().setLinearDamping(0.01).setAngularDamping(crumb ? 1.5 : 0.05))
          .setTranslation(t.x, t.y, t.z).setRotation(q);
        const rb = phys.createRigidBody(desc);
        if (!isStatic) {
          rb.setLinvel({ x: v.x + f32(p + L.addLin), y: v.y + f32(p + L.addLin + 4), z: v.z + f32(p + L.addLin + 8) }, true);
          rb.setAngvel({ x: w.x + f32(p + L.addAng), y: w.y + f32(p + L.addAng + 4), z: w.z + f32(p + L.addAng + 8) }, true);
        }
        bodies.set(body, { rb, object: o, id, static: isStatic, reactive: i32(p + L.reactive) !== 0, particle: i32(p + L.particle) !== 0,
          fresh: !isStatic && i32(p + L.flag) !== 0 });
        if (like && !isStatic) noteSpin(body, { ...like, key: key(o, u64(p + L.placeLike)) });
        out.ops.push({ op: "body", id: body, o, static: isStatic, pose: [t.x, t.y, t.z, q.x, q.y, q.z, q.w] });
        break;
      }
      case 3: {  // AttachChunk
        const e = chunks.get(c), b = bodies.get(body);
        if (!e || !b) break;
        if (e.body && e.body !== body) { const was = bodies.get(e.body); if (was) noteSpin(e.body, { ...was, key: e.body }); }
        dropCollider(e);
        e.body = body;
        e.collider = makeCollider(e, b);
        out.ops.push({ op: "attach", c, id: body });
        break;
      }
      case 4: {  // DestroyBody
        const b = bodies.get(body);
        if (!b) break;
        phys.removeRigidBody(b.rb);
        bodies.delete(body);
        M._destruct_web_forget_pose(o, id);
        out.ops.push({ op: "unbody", id: body });
        break;
      }
      case 8: {  // PushBody (a blast wave passed)
        const b = bodies.get(body);
        if (!b || b.static) break;
        const v = b.rb.linvel(), w = b.rb.angvel();
        b.rb.setLinvel({ x: v.x + f32(p + L.addLin), y: v.y + f32(p + L.addLin + 4), z: v.z + f32(p + L.addLin + 8) }, true);
        b.rb.setAngvel({ x: w.x + f32(p + L.addAng), y: w.y + f32(p + L.addAng + 4), z: w.z + f32(p + L.addAng + 8) }, true);
        break;
      }
      case 9: {  // DeformChunk: dented or bent, same body
        const e = chunks.get(c);
        if (!e) break;
        const g = chunkGeometry(o, chunk);
        keepGeometry(e, g);
        const b = bodies.get(e.body);
        if (b) { dropCollider(e); e.collider = makeCollider(e, b); }
        out.ops.push({ op: "deform", c, o, verts: g.verts });
        out.transfer.push(g.verts.buffer);
        break;
      }
      case 6: {  // SetBodyFresh: clear of its siblings, solid to them again
        const b = bodies.get(body);
        if (!b) break;
        views();
        b.fresh = i32(p + L.flag) !== 0;
        for (let k = 0; k < b.rb.numColliders(); k++) b.rb.collider(k).setCollisionGroups(b.fresh ? FRESH_GROUPS : SOLID_GROUPS);
        break;
      }
      default: break;  // SetBodyMass (the colliders carry the mass), SetBodyCanSleep
    }
  }
  queued = queued.slice(done * L.cmd);
  if (queued.length === 0) applySpinFix();
}

function readEvents() {
  const n = M._destruct_take_events(world);
  const base = M._destruct_event_list(world);
  views();
  const lines = [];
  for (let i = 0; i < n; i++) {
    const p = base + i * L.evt;
    const type = EVENT_NAMES[i32(p + L.evType)] || "event";
    const info = objects.get(u32(p + L.evObject))?.info;
    // [type, x, y, z, intensity, family, mass kg, energy J]: the last three for sound.
    out.events.push([type, f32(p + L.evPos), f32(p + L.evPos + 4), f32(p + L.evPos + 8), f32(p + L.evIntensity),
      info?.family || "", f32(p + L.evMass), f32(p + L.evEnergy)]);
    if (type === "break") lines.push(`break: ${f32(p + L.evMass).toFixed(0)} kg in ${i32(p + L.evPieces)} pieces`);
    if (type === "deform") lines.push(`${info && info.yieldPa > 0 ? "dent" : "chip"}: ${(f32(p + L.evDeform) * 100).toFixed(1)} cm`);
    if (type === "collapsed") lines.push("collapsed");
  }
  if (lines.length) out.log = lines.slice(-2).join("  ·  ");
  return n;
}

// Effects: 16 numbers each (kind, count, position, direction, spread, size, speed, lifetime, colour, mass); the page
// draws. (The mass follows the colour in destruct_effect.)
function readEffects() {
  const n = M._destruct_take_effects(world);
  if (n <= 0) return;
  const base = M._destruct_effect_list(world);
  views();
  for (let i = 0; i < n; i++) {
    const p = base + i * L.fx;
    out.fx.push(i32(p + L.fxKind), i32(p + L.fxCount),
      f32(p + L.fxPos), f32(p + L.fxPos + 4), f32(p + L.fxPos + 8), f32(p + L.fxDir), f32(p + L.fxDir + 4), f32(p + L.fxDir + 8),
      f32(p + L.fxSpread), f32(p + L.fxSize), f32(p + L.fxSpeed), f32(p + L.fxLife),
      f32(p + L.fxColor), f32(p + L.fxColor + 4), f32(p + L.fxColor + 8), f32(p + L.fxColor + 12));
  }
}

// ---------------------------------------------------------------- building the range
// The range holds one or more objects: a scene (build) replaces them all, add puts one more beside them.
function clearScene() {
  for (const b of bodies.values()) phys.removeRigidBody(b.rb);
  bodies.clear(); chunks.clear(); byCollider.clear();
  for (const o of objects.keys()) M._destruct_remove_object(world, o);
  objects.clear();
  M._destruct_take_commands(world);
  M._destruct_take_events(world);
  M._destruct_take_effects(world);
  clearProjectiles();
  M._destruct_web_clear_poses();
  queued = new Uint8Array(0);
  out = fresh();
}

// The size an item comes in (a preset's own; a material as a wall, a panel or a sheet, or the size asked for).
function itemSize(item) {
  const [kind, name] = item.target.split(":");
  if (item.size) return item.size;
  if (kind === "object") return PRESETS.get(name).size;
  const info = MATERIALS.get(name);
  if (info.pane) return [3, 2, 0.04];
  if (info.sheet) return [3, 2, name === "sheet_metal" ? 0.004 : name === "aluminum_foil" ? 0.001 : 0.04];
  return [5, 3, 0.6];
}

// Makes one object, standing with its own origin (the middle of its base) at item.at.
function makeObject(item, seed) {
  const [kind, name] = item.target.split(":");
  const size = itemSize(item);
  let shell = -1, anchor = item.anchor ?? -1, preset = "", material = "";
  if (kind === "object") preset = name;
  else {
    material = name;
    const info = MATERIALS.get(name);
    if (item.anchor === undefined && info.pane) anchor = 3;
    else if (item.anchor === undefined && info.sheet) anchor = 2;
  }
  // The page's Hold setting (free 1, base held 2, pinned 4; -1: as the object was made).
  if (item.anchor === undefined && state.hold >= 0) anchor = state.hold;
  const custom = kind !== "object" || item.size;
  const o = withString(name, (np) => withString(material, (mp) => withString(preset, (pp) =>
    M._destruct_web_make(world, np, mp, pp, custom ? size[0] : 0, custom ? size[1] : 0, custom ? size[2] : 0, shell, anchor,
      state.detail, seed))));
  if (!o) return null;
  const at = item.at || [0, 0, 0];
  // Where it stands: the object itself (body 0) is placed there, and its first bodies start there.
  const r = M._malloc(36);
  views();
  H.f32.set([1, 0, 0, 0, 1, 0, 0, 0, 1], r >> 2);
  M._destruct_web_set_pose(o, 0, r, at[0], at[1], at[2]);
  M._free(r);
  const info = materialInfo(o);
  // Phones: full crumbling, but fewer loose pieces at once and crumbs as particles sooner.
  if (PHONE && state.detail > 0) M._destruct_object_set_debris_lod(world, o, 150, 0.0006);
  const label = kind === "object" ? PRESETS.get(name).label : name.replace(/_/g, " ");
  objects.set(o, { info, label, size, at, item: { ...item, at } });
  return { o, info, label, size, at };
}

// Everything the page needs about the objects now on the range.
function objectList() {
  return [...objects].map(([o, v]) => ({ o, info: v.info, label: v.label, size: v.size, at: v.at, item: v.item }));
}
function rangeScale() {
  let span = 0;
  for (const v of objects.values()) span = Math.max(span, ...v.size);
  return Math.min(1, span / 3);
}

function build(msg) {
  clearScene();
  state.detail = msg.detail; state.budget = msg.budget; state.soft = msg.soft; state.hold = msg.hold ?? -1;
  M._destruct_world_set_energy_budget(world, state.budget);
  M._destruct_world_set_soft_sim(world, state.soft ? 1 : 0);
  msg.items.forEach((item, i) => makeObject(item, msg.seed + i * 7919));
  state.scale = rangeScale();
  runCommands();
  flush({ built: { objects: objectList(), scale: state.scale, replaced: true } });
}

// One more object beside the others: to the right of whatever is there, a little apart.
function addItem(msg) {
  state.hold = msg.hold ?? state.hold;
  const size = itemSize(msg.item);
  let right = -Infinity;
  for (const v of objects.values()) right = Math.max(right, v.at[0] + v.size[0] / 2);
  const x = objects.size ? right + 0.3 + size[0] / 2 : 0;
  makeObject({ ...msg.item, at: [x, 0, 0] }, msg.seed + objects.size * 7919);
  state.scale = rangeScale();
  runCommands();
  flush({ built: { objects: objectList(), scale: state.scale, replaced: false } });
}

// ---------------------------------------------------------------- stepping
const rot = { p: 0 };
function step(dt) {
  // Air drag (0.5 rho Cd A v^2), from each piece's mass and its material's density: dust slows fast, bricks hardly.
  for (const b of bodies.values()) {
    if (b.static) continue;
    const density = Math.max(objects.get(b.object)?.info.density || 1000, 1);
    const v = b.rb.linvel(), speed = Math.hypot(v.x, v.y, v.z);
    if (speed < 0.01) continue;
    const m = Math.max(b.rb.mass(), 1e-4), area = Math.pow(m / density, 2 / 3);
    const dv = Math.min(0.5 * 1.2 * 1.05 * area * speed * speed / m * dt, speed);
    const k = 1 - dv / speed;
    b.rb.setLinvel({ x: v.x * k, y: v.y * k, z: v.z * k }, false);
  }
  phys.timestep = dt;
  let t0 = performance.now();
  for (const item of thrown) { const v = item.rb.linvel(); item.prevVel = [v.x, v.y, v.z]; }  // how fast each was going into this step
  phys.step(queue);
  updateProjectiles(dt);
  perf.physics += performance.now() - t0;
  queue.drainContactForceEvents((ev) => {
    const mag = ev.totalForceMagnitude();
    for (const h of [ev.collider1(), ev.collider2()]) {
      const id = byCollider.get(h), b = id && bodies.get(id);
      if (!b || b.static || !b.reactive) continue;
      const m = b.rb.mass();
      const impulse = mag * dt, energy = (impulse * impulse) / (2 * Math.max(m, 0.01));
      if (energy < 20) continue;
      const t = b.rb.translation();
      M._destruct_web_contact(world, b.object, b.id, t.x, t.y, t.z, energy);
    }
  });
  // Tell the engine where every body is now (rotation row-major, from the quaternion), then step it.
  const r = rot.p || (rot.p = M._malloc(36));
  for (const b of bodies.values()) {
    if (b.posed && (b.static || b.rb.isSleeping())) continue;  // the engine still has where it lies
    const t = b.rb.translation(), q = b.rb.rotation();
    const { x, y, z, w } = q;
    views();
    const a = r >> 2, F = H.f32;
    F[a] = 1 - 2 * (y * y + z * z); F[a + 1] = 2 * (x * y - z * w); F[a + 2] = 2 * (x * z + y * w);
    F[a + 3] = 2 * (x * y + z * w); F[a + 4] = 1 - 2 * (x * x + z * z); F[a + 5] = 2 * (y * z - x * w);
    F[a + 6] = 2 * (x * z - y * w); F[a + 7] = 2 * (y * z + x * w); F[a + 8] = 1 - 2 * (x * x + y * y);
    M._destruct_web_set_pose(b.object, b.id, r, t.x, t.y, t.z);
    b.posed = true;
  }
  t0 = performance.now();
  M._destruct_step(world, dt);
  perf.engine += performance.now() - t0;
  t0 = performance.now();
  runCommands();
  readEvents();
  readEffects();
  perf.commands += performance.now() - t0;
}

// ---------------------------------------------------------------- hitting things
function strike(msg) {
  const h0 = performance.now();
  const imp = IMPACTS[msg.imp], [px, py, pz] = msg.p, [dx, dy, dz] = msg.d;
  const target = objects.get(msg.o);
  if (!target) return;
  const o = M._malloc(28);
  const force = msg.force || 1;  // the preset's speed scale
  withString(imp.name, (np) => M._destruct_web_strike(world, msg.o, np, px, py, pz, dx, dy, dz, force, o));
  views();
  const pushed = f32(o + 24) !== 0;
  if (imp.kind === "pointed" || imp.kind === "edge") {
    const stopped = f32(o + 4) !== 0, left = f32(o + 20);
    marker("debris_hit", f32(o + 8), f32(o + 12), f32(o + 16), 0.25);
    out.log = imp.kind === "edge" ? `${imp.label} bit in` : stopped ? `${imp.label}: stopped inside` : `${imp.label}: went through, ${left.toFixed(0)} J left`;
  } else if (imp.kind === "blast") {
    marker("break", px, py, pz, 1);
  } else if (pushed) {
    out.log = `${imp.label} knocked it back`;
  }
  M._free(o);
  runCommands();
  const happened = readEvents();
  if (!happened && imp.kind !== "pointed" && imp.kind !== "blast" && !pushed) {
    // Say so, rather than leave the player guessing.
    out.log = `${imp.label} (${energyLabel(imp.energy * force * force)}): no damage. ${target.info.name.replace(/_/g, " ")} is tougher than that; keep hitting it to wear it down`;
  }
  perf.hit = performance.now() - h0;
}
function energyLabel(j) {
  return j >= 1e6 ? `${(j / 1e6).toFixed(1)} MJ` : j >= 1000 ? `${(j / 1000).toFixed(j >= 10000 ? 0 : 1)} kJ` : `${j.toFixed(0)} J`;
}
// A blast wave in front of the range (the page says where: the middle of everything, a little in front).
function blast(msg) {
  const imp = IMPACTS[msg.imp].kind === "blast" ? IMPACTS[msg.imp] : IMPACTS.find((x) => x.name === "grenade");
  const [x, y, z] = msg.p;
  M._destruct_web_detonate(world, x, y, z, imp.energy * (msg.force || 1) ** 2, 6 * Math.max(state.scale, 0.2));
  marker("break", x, y, z, 1);
}

// ---------------------------------------------------------------- throwing and swinging
// Thrown things and the held tool are real bodies here; the page draws them from the poses sent back (its own ids).
function impactorShape(imp) {
  // Its body: a ball for round things, a box the size of the face (a few cm deep) for flat ones.
  const w = Math.max(imp.faceW, 0.02), h = Math.max(imp.faceH, 0.02);
  if (imp.kind === "blast") return { ball: 0.04 };
  if (ROUND.has(imp.name)) return { ball: 0.5 * Math.max(w, h) };
  return { box: [0.5 * w, 0.5 * h, 0.5 * Math.max(Math.min(w, h), 0.04)] };
}
const thrown = [];                      // things in flight or lying where they landed
const projectileColliders = new Map();  // collider handle -> thrown thing or the held tool
function throwImpactor(msg) {
  if (thrown.length >= 12) dropThrown(thrown[0]);
  const imp = IMPACTS[msg.imp], s = impactorShape(imp), [fx, fy, fz] = msg.from, [vx, vy, vz] = msg.v;
  const rb = phys.createRigidBody(RAPIER.RigidBodyDesc.dynamic().setTranslation(fx, fy, fz)
    .setLinvel(vx, vy, vz).setAngvel({ x: Math.random() * 6 - 3, y: Math.random() * 6 - 3, z: Math.random() * 6 - 3 })
    .setCcdEnabled(true).setLinearDamping(0.01).setAngularDamping(0.3));
  const desc = (s.ball ? RAPIER.ColliderDesc.ball(s.ball) : RAPIER.ColliderDesc.cuboid(...s.box))
    .setMass(Math.max(imp.kind === "blast" ? 0.4 : imp.mass, 0.01)).setRestitution(imp.name === "baseball" ? 0.45 : 0.15).setFriction(0.6)
    .setActiveEvents(RAPIER.ActiveEvents.COLLISION_EVENTS);
  const collider = phys.createCollider(desc, rb);
  const item = { id: msg.id, imp, rb, collider, age: 0, fuse: imp.kind === "blast" ? 2.2 : 0, cooldown: new Map(), prevVel: [vx, vy, vz] };
  projectileColliders.set(collider.handle, item);
  thrown.push(item);
  out.log = `threw a ${imp.label} at ${Math.hypot(vx, vy, vz).toFixed(0)} m/s`;
}
function dropThrown(item) {
  projectileColliders.delete(item.collider.handle);
  if (phys.getRigidBody(item.rb.handle)) phys.removeRigidBody(item.rb);
  const i = thrown.indexOf(item);
  if (i >= 0) thrown.splice(i, 1);
}

// The held tool: a kinematic body following the finger (the page works out where: in front of the target, pushing
// in as the drag goes on).
let tool = null;
function startSwing(msg) {
  if (tool) endSwing();
  const imp = IMPACTS[msg.imp], s = impactorShape(imp), [x, y, z] = msg.p, [qx, qy, qz, qw] = msg.q;
  const rb = phys.createRigidBody(RAPIER.RigidBodyDesc.kinematicPositionBased().setTranslation(x, y, z).setRotation({ x: qx, y: qy, z: qz, w: qw }));
  const desc = (s.ball ? RAPIER.ColliderDesc.ball(s.ball) : RAPIER.ColliderDesc.cuboid(...s.box))
    .setActiveEvents(RAPIER.ActiveEvents.COLLISION_EVENTS)
    .setActiveCollisionTypes(RAPIER.ActiveCollisionTypes.DEFAULT | RAPIER.ActiveCollisionTypes.KINEMATIC_FIXED);
  const collider = phys.createCollider(desc, rb);
  tool = { imp, rb, collider, last: [x, y, z], velocity: [0, 0, 0], lastT: performance.now(), cooldown: new Map(), held: true,
    force: msg.force || 1 };
  projectileColliders.set(collider.handle, tool);
}
function moveSwing(msg) {
  if (!tool) return;
  const [x, y, z] = msg.p, now = performance.now(), dt = Math.max((now - tool.lastT) / 1000, 1 / 240);
  tool.velocity = [(x - tool.last[0]) / dt, (y - tool.last[1]) / dt, (z - tool.last[2]) / dt];
  tool.last = [x, y, z]; tool.lastT = now;
  tool.rb.setNextKinematicTranslation({ x, y, z });
}
function endSwing() {
  if (!tool) return;
  const t = tool;
  tool = null;
  projectileColliders.delete(t.collider.handle);
  setTimeout(() => { if (phys.getRigidBody(t.rb.handle)) phys.removeRigidBody(t.rb); }, 250);
}

// After each physics step: what thrown things and the tool ran into. The strike's energy is the real impact's: how
// fast they were closing, with the impactor's mass.
function strikeFrom(item, otherHandle, velocity) {
  const id = byCollider.get(otherHandle);
  if (id === undefined) return;  // the ground, or another projectile
  const now = performance.now();
  if ((item.cooldown.get(id) || 0) > now) return;
  let point = null, normal = null;
  const other = phys.getCollider(otherHandle);
  phys.contactPair(item.collider, other, (manifold, flipped) => {
    if (manifold.numSolverContacts() > 0) point = manifold.solverContactPoint(0);
    const n = manifold.normal(), k = flipped ? -1 : 1;
    normal = [n.x * k, n.y * k, n.z * k];
  });
  const body = bodies.get(id);
  const ov = body && !body.static ? body.rb.linvel() : { x: 0, y: 0, z: 0 };
  const rel = [velocity[0] - ov.x, velocity[1] - ov.y, velocity[2] - ov.z];
  const speed = Math.hypot(rel[0], rel[1], rel[2]);
  const closing = normal ? Math.abs(rel[0] * normal[0] + rel[1] * normal[1] + rel[2] * normal[2]) : speed;
  if (closing < 1.5 || speed <= 0) return;
  item.cooldown.set(id, now + 150);
  const at = point || item.rb.translation();
  const o = M._malloc(28);
  if (!body) return;
  withString(item.imp.name, (np) => M._destruct_web_strike(world, body.object, np, at.x, at.y, at.z, rel[0] / speed, rel[1] / speed, rel[2] / speed,
    (item.force || 1) * closing / item.imp.speed, o));
  M._free(o);
  marker("debris_hit", at.x, at.y, at.z, 0.2);
  out.log = `${item.imp.label} hit at ${closing.toFixed(1)} m/s (${energyLabel(0.5 * item.imp.mass * closing * closing)})`;
}
function updateProjectiles(dt) {
  for (const item of thrown) item.age += dt;
  queue.drainCollisionEvents((h1, h2, started) => {
    if (!started) return;
    for (const [mine, other] of [[h1, h2], [h2, h1]]) {
      const item = projectileColliders.get(mine);
      if (!item || item.imp.kind === "blast") continue;
      strikeFrom(item, other, item.held ? item.velocity : item.prevVel);
    }
  });
  for (let i = thrown.length - 1; i >= 0; i--) {
    const item = thrown[i], t = item.rb.translation();
    if (item.fuse > 0 && item.age >= item.fuse) {
      // The grenade goes off where it lies.
      M._destruct_web_detonate(world, t.x, t.y, t.z, item.imp.energy, 6 * Math.max(state.scale, 0.2));
      marker("break", t.x, t.y, t.z, 1);
      dropThrown(item);
      continue;
    }
    // Lies where it landed for a while (the page fades it), then goes.
    if (item.age > 10 || t.y < -5) dropThrown(item);
  }
}
function clearProjectiles() {
  while (thrown.length) dropThrown(thrown[0]);
  if (tool) endSwing();
}

// ---------------------------------------------------------------- messages from the page
const handlers = {
  init,
  build,
  add: addItem,
  step(msg) {
    for (let i = 0; i < msg.n; i++) {
      const s0 = performance.now();
      step(msg.dt);
      perf.steps++;
      perf.worstStep = Math.max(perf.worstStep, performance.now() - s0);
    }
    flush({ stepped: msg.n });
  },
  strike,
  blast,
  throw: throwImpactor,
  swingStart: startSwing,
  swingMove: moveSwing,
  swingEnd: endSwing,
  setting(msg) {
    if (msg.soft !== undefined) { state.soft = msg.soft; M._destruct_world_set_soft_sim(world, msg.soft ? 1 : 0); }
    if (msg.budget !== undefined) { state.budget = msg.budget; M._destruct_world_set_energy_budget(world, msg.budget); }
    if (msg.threads !== undefined) {  // profiling: the pool's size (no more than the threads started at load)
      M._destruct_web_set_threads(Math.min(Math.max(msg.threads, 0), threads > 0 ? POOL : 0));
      self.postMessage({ type: "threads", threads: M._destruct_web_threads() });
    }
  },
  resetPerf() { for (const k of Object.keys(perf)) perf[k] = 0; },
};
// One message at a time, in order (init is async: everything after it waits for it).
let chain = Promise.resolve();
self.onmessage = (e) => {
  chain = chain.then(() => handlers[e.data.type]?.(e.data)).catch((err) => {
    console.error(err);
    self.postMessage({ type: "error", message: String(err && err.message || err), during: e.data.type });
  });
};
