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
const EVENT_NAMES = ["break", "crumble", "debris_hit", "collapsed", "deform"];
const ROUND = new Set(["baseball", "fist", "kick", "baseball_bat", "wrecking_ball", "grenade", "firecracker"]);
const PANES = new Set(["glass", "mirror"]);
const SHEETS = new Set(["drywall", "cardboard", "paper", "tile", "sheet_metal", "tin", "leather", "pcb", "tempered_glass", "acrylic", "aluminum_foil"]);
// How many threads the engine's pool gets in the threaded build: leave room for the page and this worker. Must match
// PTHREAD_POOL_SIZE in tools/build_web.ps1 (the threads are started ahead, at load).
const POOL = Math.min(4, Math.max(1, (self.navigator.hardwareConcurrency || 2) - 2));

let M, world, phys, queue, threads = 0;
let PHONE = false, HULL_POINTS = 64, COMMAND_BUDGET_MS = 8;
const L = {};
const state = { object: 0, info: null, size: [5, 3, 0.6], scale: 1, budget: 1, soft: false, detail: 1 };
const IMPACTS = [], MATERIALS = new Map(), PRESETS = new Map();
const bodies = new Map();      // body id -> { rb, static, reactive, particle, fresh }
const chunks = new Map();      // chunk id -> { collider, body, points, mass, sphere, box }
const byCollider = new Map();  // collider handle -> body id
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
    impacts: IMPACTS, materials: [...MATERIALS.keys()], presets: [...PRESETS].map(([name, p]) => ({ name, label: p.label })),
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
function chunkGeometry(c) {
  const g0 = performance.now();
  perf.chunkMeshes++;
  const info = M._malloc(32);
  M._destruct_chunk_get_info(world, state.object, c, info);
  views();
  const mass = f32(info);
  M._free(info);
  const count = M._destruct_chunk_render_mesh(world, state.object, c, 0, 0);
  const buf = scratchFloats(count * 9);
  M._destruct_chunk_render_mesh(world, state.object, c, buf, count);
  views();
  const verts = H.f32.slice(buf >> 2, (buf >> 2) + count * 9);
  const pts = scratchFloats(HULL_POINTS * 3);
  const np = M._destruct_chunk_hull_points(world, state.object, c, pts, HULL_POINTS);
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

// Collision groups (membership << 16 | what it collides with). Pieces fresh from a break pass through each other
// until the engine says they are clear (SetBodyFresh), but still hit the ground and everything settled.
const SOLID_GROUPS = (0x0001 << 16) | 0xffff, FRESH_GROUPS = (0x0002 << 16) | 0x0001;
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
  desc.setMass(Math.max(entry.mass, 0.001)).setFriction(state.info.friction).setRestitution(state.info.bounce)
    .setCollisionGroups(body.fresh ? FRESH_GROUPS : SOLID_GROUPS);
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
    const type = i32(p + L.type), c = u32(p + L.chunk), body = u64(p + L.body);
    switch (type) {
      case 0: {  // ChunkAdded
        const g = chunkGeometry(c);
        const e = { collider: null, body: 0 };
        keepGeometry(e, g);
        chunks.set(c, e);
        out.ops.push({ op: "add", c, verts: g.verts });
        out.transfer.push(g.verts.buffer);
        break;
      }
      case 1: {  // RetireChunk
        const e = chunks.get(c);
        if (!e) break;
        dropCollider(e);
        chunks.delete(c);
        out.ops.push({ op: "retire", c });
        break;
      }
      case 2: {  // CreateBody
        const isStatic = i32(p + L.isStatic) !== 0;
        const like = bodies.get(u64(p + L.placeLike));
        let t = { x: 0, y: 0, z: 0 }, q = { x: 0, y: 0, z: 0, w: 1 }, v = { x: 0, y: 0, z: 0 }, w = { x: 0, y: 0, z: 0 };
        if (like) {
          t = like.rb.translation(); q = like.rb.rotation();
          if (!like.static) { v = like.rb.linvel(); w = like.rb.angvel(); }
        }
        // Air and rough ground take energy out: a little linear damping, more on spin (pieces roll to a stop).
        const desc = (isStatic ? RAPIER.RigidBodyDesc.fixed() : RAPIER.RigidBodyDesc.dynamic().setLinearDamping(0.02).setAngularDamping(0.6))
          .setTranslation(t.x, t.y, t.z).setRotation(q);
        const rb = phys.createRigidBody(desc);
        if (!isStatic) {
          rb.setLinvel({ x: v.x + f32(p + L.addLin), y: v.y + f32(p + L.addLin + 4), z: v.z + f32(p + L.addLin + 8) }, true);
          rb.setAngvel({ x: w.x + f32(p + L.addAng), y: w.y + f32(p + L.addAng + 4), z: w.z + f32(p + L.addAng + 8) }, true);
        }
        bodies.set(body, { rb, static: isStatic, reactive: i32(p + L.reactive) !== 0, particle: i32(p + L.particle) !== 0,
          fresh: !isStatic && i32(p + L.flag) !== 0 });
        out.ops.push({ op: "body", id: body, static: isStatic, pose: [t.x, t.y, t.z, q.x, q.y, q.z, q.w] });
        break;
      }
      case 3: {  // AttachChunk
        const e = chunks.get(c), b = bodies.get(body);
        if (!e || !b) break;
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
        M._destruct_web_forget_pose(state.object, body);
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
        const g = chunkGeometry(c);
        keepGeometry(e, g);
        const b = bodies.get(e.body);
        if (b) { dropCollider(e); e.collider = makeCollider(e, b); }
        out.ops.push({ op: "deform", c, verts: g.verts });
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
}

function readEvents() {
  const n = M._destruct_take_events(world);
  const base = M._destruct_event_list(world);
  views();
  const lines = [];
  for (let i = 0; i < n; i++) {
    const p = base + i * L.evt;
    const type = EVENT_NAMES[i32(p + L.evType)] || "event";
    out.events.push([type, f32(p + L.evPos), f32(p + L.evPos + 4), f32(p + L.evPos + 8), f32(p + L.evIntensity)]);
    if (type === "break") lines.push(`break: ${f32(p + L.evMass).toFixed(0)} kg in ${i32(p + L.evPieces)} pieces`);
    if (type === "deform") lines.push(`${state.info.yieldPa > 0 ? "dent" : "chip"}: ${(f32(p + L.evDeform) * 100).toFixed(1)} cm`);
    if (type === "collapsed") lines.push("collapsed");
  }
  if (lines.length) out.log = lines.slice(-2).join("  ·  ");
  return n;
}

// Effects: 15 numbers each (kind, count, position, direction, spread, size, speed, lifetime, colour); the page draws.
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
      f32(p + L.fxColor), f32(p + L.fxColor + 4), f32(p + L.fxColor + 8));
  }
}

// ---------------------------------------------------------------- building a target
function clearScene() {
  for (const b of bodies.values()) phys.removeRigidBody(b.rb);
  bodies.clear(); chunks.clear(); byCollider.clear();
  if (state.object) M._destruct_remove_object(world, state.object);
  M._destruct_take_commands(world);
  M._destruct_take_events(world);
  M._destruct_take_effects(world);
  clearProjectiles();
  M._destruct_web_clear_poses();
  queued = new Uint8Array(0);
  out = fresh();
}

function build(msg) {
  clearScene();
  state.detail = msg.detail; state.budget = msg.budget; state.soft = msg.soft;
  const [kind, name] = msg.target.split(":");
  let size = [5, 3, 0.6], shell = -1, anchor = -1, preset = "", material = "";
  if (kind === "object") {
    preset = name;
    size = PRESETS.get(name).size;
  } else {
    material = name;
    const info = MATERIALS.get(name);
    if (info.pane) { size = [3, 2, 0.04]; anchor = 3; }
    else if (info.sheet) { size = [3, 2, name === "sheet_metal" ? 0.004 : name === "aluminum_foil" ? 0.001 : 0.04]; anchor = 2; }
  }
  state.size = size;
  state.object = withString(name, (np) => withString(material, (mp) => withString(preset, (pp) =>
    M._destruct_web_make(world, np, mp, pp, kind === "object" ? 0 : size[0], kind === "object" ? 0 : size[1],
      kind === "object" ? 0 : size[2], shell, anchor, state.detail, msg.seed))));
  state.info = materialInfo(state.object);
  M._destruct_world_set_energy_budget(world, state.budget);
  M._destruct_world_set_soft_sim(world, state.soft ? 1 : 0);
  // Phones: full crumbling, but fewer loose pieces at once and crumbs as particles sooner.
  if (PHONE && state.detail > 0) M._destruct_object_set_debris_lod(world, state.object, 150, 0.0006);
  state.scale = Math.min(1, Math.max(size[0], size[1], size[2]) / 3);
  runCommands();
  flush({ built: { info: state.info, size, label: kind === "object" ? PRESETS.get(name).label : name.replace(/_/g, " "), scale: state.scale } });
}

// ---------------------------------------------------------------- stepping
const rot = { p: 0 };
function step(dt) {
  // Air drag (0.5 rho Cd A v^2), from each piece's mass and its material's density: dust slows fast, bricks hardly.
  const density = Math.max(state.info?.density || 1000, 1);
  for (const b of bodies.values()) {
    if (b.static) continue;
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
      M._destruct_web_contact(world, state.object, id, t.x, t.y, t.z, energy);
    }
  });
  // Tell the engine where every body is now (rotation row-major, from the quaternion), then step it.
  const r = rot.p || (rot.p = M._malloc(36));
  for (const [id, b] of bodies) {
    if (b.posed && (b.static || b.rb.isSleeping())) continue;  // the engine still has where it lies
    const t = b.rb.translation(), q = b.rb.rotation();
    const { x, y, z, w } = q;
    views();
    const a = r >> 2, F = H.f32;
    F[a] = 1 - 2 * (y * y + z * z); F[a + 1] = 2 * (x * y - z * w); F[a + 2] = 2 * (x * z + y * w);
    F[a + 3] = 2 * (x * y + z * w); F[a + 4] = 1 - 2 * (x * x + z * z); F[a + 5] = 2 * (y * z - x * w);
    F[a + 6] = 2 * (x * z - y * w); F[a + 7] = 2 * (y * z + x * w); F[a + 8] = 1 - 2 * (x * x + y * y);
    M._destruct_web_set_pose(state.object, id, r, t.x, t.y, t.z);
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
  const o = M._malloc(28);
  withString(imp.name, (np) => M._destruct_web_strike(world, state.object, np, px, py, pz, dx, dy, dz, 1, o));
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
    out.log = `${imp.label} (${energyLabel(imp.energy)}): no damage. ${state.info.name.replace(/_/g, " ")} is tougher than that; keep hitting it to wear it down`;
  }
  perf.hit = performance.now() - h0;
}
function energyLabel(j) {
  return j >= 1e6 ? `${(j / 1e6).toFixed(1)} MJ` : j >= 1000 ? `${(j / 1000).toFixed(j >= 10000 ? 0 : 1)} kJ` : `${j.toFixed(0)} J`;
}
function blast(msg) {
  const s = state.size, d = Math.max(s[2], 0.1) / 2 + Math.max(0.6, Math.max(s[0], s[1]) * 0.6);
  const imp = IMPACTS[msg.imp].kind === "blast" ? IMPACTS[msg.imp] : IMPACTS.find((x) => x.name === "grenade");
  M._destruct_web_detonate(world, 0, s[1] * 0.5, d, imp.energy, 6 * Math.max(state.scale, 0.2));
  marker("break", 0, s[1] * 0.5, d, 1);
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
  tool = { imp, rb, collider, last: [x, y, z], velocity: [0, 0, 0], lastT: performance.now(), cooldown: new Map(), held: true };
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
  withString(item.imp.name, (np) => M._destruct_web_strike(world, state.object, np, at.x, at.y, at.z, rel[0] / speed, rel[1] / speed, rel[2] / speed,
    closing / item.imp.speed, o));
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
