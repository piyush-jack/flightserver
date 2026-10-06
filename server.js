'use strict';
/*
  Open Skies Arena server. Zero dependencies (Node 18+).
  Run:  node server.js        (PORT=8080 by default)
  Serves public/index.html and the game WebSocket on the same port.
*/
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const PORT = +process.env.PORT || 8080;
const MAX_PLAYERS = 10;
const ARENA = { r: 9000, ceil: 6500 };          // combat zone: radius and ceiling in metres
const OOB_LIMIT_MS = 8000;                      // time allowed outside the zone
const MAP_IDS = ['archipelago', 'crown', 'dunes'];
const SPAWN_ALT = { crown: [4300, 1000], archipelago: [1600, 1400], dunes: [1300, 1400] }; // base, random range (metres)
const HP = 100, DMG = 7, HIT_R = 10, BULLET_SPEED = 650, BULLET_LIFE = 1.6, FIRE_GAP = 66;
const RESPAWN_MS = 4000, INV_MS = 3000, SNAP_HZ = 20, TICK_HZ = 30;
const MAX_PER_IP = +process.env.MAX_PER_IP || 20;

const rooms = new Map();
let nextId = 1;
const ipCount = new Map();

/* ---------- minimal WebSocket ---------- */
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
function frame(op, payload) {
  const len = payload.length; let h;
  if (len < 126) h = Buffer.from([0x80 | op, len]);
  else if (len < 65536) { h = Buffer.alloc(4); h[0] = 0x80 | op; h[1] = 126; h.writeUInt16BE(len, 2); }
  else { h = Buffer.alloc(10); h[0] = 0x80 | op; h[1] = 127; h.writeBigUInt64BE(BigInt(len), 2); }
  return Buffer.concat([h, payload]);
}
function upgrade(req, socket) {
  const key = req.headers['sec-websocket-key'];
  const ip = req.socket.remoteAddress;
  if (!key || (ipCount.get(ip) || 0) >= MAX_PER_IP) { socket.destroy(); return; }
  ipCount.set(ip, (ipCount.get(ip) || 0) + 1);
  const acc = crypto.createHash('sha1').update(key + GUID).digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + acc + '\r\n\r\n');
  socket.setNoDelay(true);
  const ws = {
    socket, open: true, lastRx: Date.now(), msgs: 0, msgWin: Date.now(),
    send(obj) { if (!this.open) return; try { socket.write(frame(1, Buffer.from(JSON.stringify(obj)))); } catch (e) { } },
    close() { if (!this.open) return; this.open = false; try { socket.end(frame(8, Buffer.alloc(0))); } catch (e) { } },
    onmessage: null, onclose: null
  };
  let buf = Buffer.alloc(0), frags = [];
  const finish = () => {
    if (ws.dead) return; ws.dead = true; ws.open = false;
    ipCount.set(ip, Math.max(0, (ipCount.get(ip) || 1) - 1));
    if (ws.onclose) ws.onclose();
  };
  socket.on('data', d => {
    buf = Buffer.concat([buf, d]);
    while (buf.length >= 2) {
      const b0 = buf[0], b1 = buf[1], fin = !!(b0 & 0x80), op = b0 & 15, masked = !!(b1 & 0x80);
      let len = b1 & 127, off = 2;
      if (len === 126) { if (buf.length < 4) break; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (buf.length < 10) break; len = Number(buf.readBigUInt64BE(2)); off = 10; }
      if (len > 16384 || !masked) { ws.close(); socket.destroy(); return; }
      if (buf.length < off + 4 + len) break;
      const mask = buf.subarray(off, off + 4), payload = Buffer.from(buf.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < len; i++) payload[i] ^= mask[i & 3];
      buf = buf.subarray(off + 4 + len);
      ws.lastRx = Date.now();
      if (op === 8) { ws.close(); return; }
      if (op === 9) { try { socket.write(frame(10, payload)); } catch (e) { } continue; }
      if (op === 10) continue;
      if (op === 1 || op === 2 || op === 0) {
        frags.push(payload);
        if (fin) { const full = Buffer.concat(frags); frags = []; if (ws.onmessage) ws.onmessage(full.toString('utf8')); }
      }
    }
  });
  socket.on('close', finish); socket.on('error', finish);
  onConnect(ws);
}

/* ---------- helpers ---------- */
const now = () => Date.now();
const num = (a, n) => Array.isArray(a) && a.length === n && a.every(x => typeof x === 'number' && isFinite(x) && Math.abs(x) < 1e6);
const r1 = x => Math.round(x * 10) / 10, r4 = x => Math.round(x * 10000) / 10000;
function codeGen() { const c = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; let s = ''; for (let i = 0; i < 4; i++) s += c[Math.floor(Math.random() * c.length)]; return s; }
function fwd(q) { // (0,0,-1) rotated by quaternion q = [x,y,z,w]
  const [x, y, z, w] = q;
  return [-(2 * (x * z + w * y)), -(2 * (y * z - w * x)), -(1 - 2 * (x * x + y * y))];
}
function broadcast(room, obj, except) { const s = obj; for (const p of room.players.values()) if (p !== except) p.ws.send(s); }
function rosterOf(room) { return [...room.players.values()].map(p => ({ id: p.id, name: p.name, c: p.color, k: p.k, d: p.d })); }
function sendRoster(room) { broadcast(room, { t: 'roster', ps: rosterOf(room) }); }

function spawnPose(room) {
  const [alt0, altR] = SPAWN_ALT[room.map] || [1500, 1500];
  let best = null, bestD = -1;
  for (let i = 0; i < 12; i++) {
    const a = Math.random() * Math.PI * 2, r = ARENA.r * (0.55 + Math.random() * 0.2), y = alt0 + Math.random() * altR;
    const p = [Math.cos(a) * r, y, Math.sin(a) * r];
    let md = 1e9;
    for (const o of room.players.values()) if (o.alive) md = Math.min(md, Math.hypot(o.p[0] - p[0], o.p[1] - p[1], o.p[2] - p[2]));
    if (md > bestD) { bestD = md; best = { a, p }; }
  }
  const phi = Math.PI / 2 - best.a;
  return { p: best.p.map(r1), q: [0, r4(Math.sin(phi / 2)), 0, r4(Math.cos(phi / 2))], v: [r1(-Math.cos(best.a) * 200), 0, r1(-Math.sin(best.a) * 200)] };
}

/* ---------- rooms ---------- */
function getRoom(map, code) {
  if (code) {
    let r = rooms.get(code);
    if (!r) { r = newRoom(map, code, false); }
    return r;
  }
  for (const r of rooms.values()) if (r.pub && r.map === map && r.players.size < MAX_PLAYERS) return r;
  let c; do c = codeGen(); while (rooms.has(c));
  return newRoom(map, c, true);
}
function newRoom(map, code, pub) {
  const r = { code, map, pub, players: new Map(), bullets: [], ev: { f: [], h: [] }, emptySince: now() };
  rooms.set(code, r); return r;
}

function onConnect(ws) {
  let P = null;
  ws.onmessage = txt => {
    const t = now();
    if (t - ws.msgWin > 1000) { ws.msgWin = t; ws.msgs = 0; }
    if (++ws.msgs > 120) return;
    let m; try { m = JSON.parse(txt); } catch (e) { return; }
    if (!m || typeof m.t !== 'string') return;
    if (m.t === 'ping') { ws.send({ t: 'pong', c: m.c }); return; }
    if (m.t === 'join') {
      if (P) return;
      const name = String(m.name || 'Pilot').replace(/[^\w .\-]/g, '').trim().slice(0, 14) || 'Pilot';
      const map = MAP_IDS.includes(m.map) ? m.map : 'crown';
      const code = typeof m.room === 'string' && /^[A-Za-z0-9]{3,8}$/.test(m.room) ? m.room.toUpperCase() : null;
      const room = getRoom(map, code);
      if (room.players.size >= MAX_PLAYERS) { ws.send({ t: 'err', msg: 'That room is full (' + MAX_PLAYERS + '/' + MAX_PLAYERS + '). Try Quick match or another room code.' }); return; }
      const used = new Set([...room.players.values()].map(p => p.color));
      let color = 0; while (used.has(color)) color++;
      const sp = spawnPose(room);
      P = { id: nextId++, ws, room, name, color, k: 0, d: 0, hp: HP, alive: true, inv: t + INV_MS, p: sp.p, q: sp.q, v: sp.v, thr: .4, ts: t, lastFire: 0, oob: 0, respawnAt: 0, ramCd: 0 };
      room.players.set(P.id, P);
      ws.send({ t: 'welcome', id: P.id, room: room.code, map: room.map, arena: ARENA, max: MAX_PLAYERS, color, spawn: sp, roster: rosterOf(room) });
      sendRoster(room);
      return;
    }
    if (!P) return;
    const room = P.room;
    if (m.t === 's') {
      if (!P.alive || !num(m.p, 3) || !num(m.q, 4) || !num(m.v, 3)) return;
      P.p = m.p; P.q = m.q; P.v = m.v; P.thr = typeof m.h === 'number' ? Math.max(0, Math.min(1, m.h)) : P.thr; P.ts = t;
    } else if (m.t === 'fire') {
      if (!P.alive || t - P.lastFire < FIRE_GAP) return;
      P.lastFire = t;
      let p = P.p, q = P.q, v = P.v;
      if (num(m.p, 3) && num(m.q, 4) && num(m.v, 3) && Math.hypot(m.p[0] - P.p[0], m.p[1] - P.p[1], m.p[2] - P.p[2]) < 200) { p = m.p; q = m.q; v = m.v; }
      const f = fwd(q), l = Math.hypot(f[0], f[1], f[2]) || 1;
      const d = [f[0] / l, f[1] / l, f[2] / l];
      const b = { x: p[0] + d[0] * 10, y: p[1] + d[1] * 10, z: p[2] + d[2] * 10, vx: v[0] + d[0] * BULLET_SPEED, vy: v[1] + d[1] * BULLET_SPEED, vz: v[2] + d[2] * BULLET_SPEED, life: BULLET_LIFE, owner: P };
      room.bullets.push(b);
      room.ev.f.push([P.id, r1(b.x), r1(b.y), r1(b.z), r1(b.vx), r1(b.vy), r1(b.vz)]);
    } else if (m.t === 'dead') {
      if (P.alive) kill(room, P, null, typeof m.why === 'string' ? m.why.slice(0, 30) : 'crashed');
    }
  };
  ws.onclose = () => {
    if (!P) return;
    const room = P.room; room.players.delete(P.id);
    broadcast(room, { t: 'leave', id: P.id, name: P.name });
    sendRoster(room);
    if (!room.players.size) room.emptySince = now();
  };
}

function kill(room, victim, killer, why) {
  victim.alive = false; victim.hp = 0; victim.d++; victim.respawnAt = now() + RESPAWN_MS; victim.oob = 0;
  if (killer && killer !== victim) killer.k++;
  broadcast(room, { t: 'kill', v: victim.id, k: killer && killer !== victim ? killer.id : 0, why: why || 'shot' });
  sendRoster(room);
}

/* ---------- simulation ---------- */
function predicted(p, t) { const age = Math.min(0.2, (t - p.ts) / 1000); return [p.p[0] + p.v[0] * age, p.p[1] + p.v[1] * age, p.p[2] + p.v[2] * age]; }
function tick(dt) {
  const t = now();
  for (const [code, room] of rooms) {
    if (!room.players.size) { if (t - room.emptySince > 30000) rooms.delete(code); continue; }
    // bullets
    for (let i = room.bullets.length - 1; i >= 0; i--) {
      const b = room.bullets[i];
      const ax = b.x, ay = b.y, az = b.z;
      b.x += b.vx * dt; b.y += b.vy * dt; b.z += b.vz * dt; b.life -= dt;
      let hit = false;
      const dx = b.x - ax, dy = b.y - ay, dz = b.z - az, L2 = dx * dx + dy * dy + dz * dz || 1e-6;
      for (const p of room.players.values()) {
        if (p === b.owner || !p.alive || t < p.inv) continue;
        const c = predicted(p, t);
        let s = ((c[0] - ax) * dx + (c[1] - ay) * dy + (c[2] - az) * dz) / L2; s = s < 0 ? 0 : s > 1 ? 1 : s;
        const ex = ax + dx * s - c[0], ey = ay + dy * s - c[1], ez = az + dz * s - c[2];
        if (ex * ex + ey * ey + ez * ez < HIT_R * HIT_R) {
          p.hp -= DMG; hit = true;
          room.ev.h.push([p.id, b.owner.id, Math.max(0, p.hp), r1(c[0]), r1(c[1]), r1(c[2])]);
          if (p.hp <= 0) kill(room, p, b.owner, 'shot');
          break;
        }
      }
      if (hit || b.life <= 0 || b.y > 8000) room.bullets.splice(i, 1);
    }
    const list = [...room.players.values()];
    for (const p of list) {
      if (!p.alive) {
        if (t >= p.respawnAt) {
          const sp = spawnPose(room); p.alive = true; p.hp = HP; p.inv = t + INV_MS; p.p = sp.p; p.q = sp.q; p.v = sp.v; p.ts = t; p.oob = 0;
          p.ws.send({ t: 'respawn', p: sp.p, q: sp.q, v: sp.v });
        }
        continue;
      }
      // combat-zone limit
      const out = Math.hypot(p.p[0], p.p[2]) > ARENA.r || p.p[1] > ARENA.ceil;
      if (out) { p.oob += dt * 1000; if (p.oob > OOB_LIMIT_MS) kill(room, p, null, 'left the combat zone'); }
      else p.oob = Math.max(0, p.oob - dt * 2000);
    }
    // mid-air collisions
    for (let i = 0; i < list.length; i++) for (let j = i + 1; j < list.length; j++) {
      const a = list[i], b = list[j];
      if (!a.alive || !b.alive || t < a.inv || t < b.inv || t < a.ramCd || t < b.ramCd) continue;
      if (Math.hypot(a.p[0] - b.p[0], a.p[1] - b.p[1], a.p[2] - b.p[2]) < 14) {
        a.ramCd = b.ramCd = t + 600; a.hp -= 50; b.hp -= 50;
        room.ev.h.push([a.id, b.id, Math.max(0, a.hp), r1(a.p[0]), r1(a.p[1]), r1(a.p[2])], [b.id, a.id, Math.max(0, b.hp), r1(b.p[0]), r1(b.p[1]), r1(b.p[2])]);
        if (a.hp <= 0) kill(room, a, b, 'collision'); if (b.hp <= 0) kill(room, b, a, 'collision');
      }
    }
  }
}
function snapshots() {
  const t = now();
  for (const room of rooms.values()) {
    if (!room.players.size) continue;
    const ps = [...room.players.values()].map(p => [p.id, r1(p.p[0]), r1(p.p[1]), r1(p.p[2]), r4(p.q[0]), r4(p.q[1]), r4(p.q[2]), r4(p.q[3]), r1(p.v[0]), r1(p.v[1]), r1(p.v[2]), Math.max(0, p.hp), Math.round(p.thr * 100), (p.alive ? 1 : 0) | (t < p.inv ? 2 : 0) | (p.oob > 0 ? 4 : 0)]);
    const msg = { t: 'snap', ps, f: room.ev.f, h: room.ev.h };
    room.ev = { f: [], h: [] };
    broadcast(room, msg);
  }
}
let last = now();
setInterval(() => { const n = now(), dt = Math.min(.1, (n - last) / 1000); last = n; tick(dt); }, 1000 / TICK_HZ);
setInterval(snapshots, 1000 / SNAP_HZ);
setInterval(() => { // drop dead connections
  const t = now();
  for (const room of rooms.values()) for (const p of room.players.values()) if (t - p.ws.lastRx > 30000) p.ws.close();
}, 5000);

/* ---------- HTTP ---------- */
const PUB = path.join(__dirname, 'public');
const server = http.createServer((req, res) => {
  const url = req.url.split('?')[0];
  if (url === '/rooms') {
    const maps = {}; MAP_IDS.forEach(id => maps[id] = { players: 0, rooms: 0 });
    for (const r of rooms.values()) { if (!r.players.size) continue; maps[r.map].players += r.players.size; maps[r.map].rooms++; }
    res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify({ max: MAX_PLAYERS, maps })); return;
  }
  if (url === '/health') { res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('ok'); return; }
  if (url === '/' || url === '/index.html') {
    // index.html may sit next to server.js or inside public/
    fs.readFile(path.join(__dirname, 'index.html'), (e1, d1) => {
      if (!e1) { res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' }); res.end(d1); return; }
      fs.readFile(path.join(PUB, 'index.html'), (e, d) => {
        if (e) { res.writeHead(404); res.end('index.html not found next to server.js or in public/'); return; }
        res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' }); res.end(d);
      });
    }); return;
  }
  res.writeHead(404); res.end('not found');
});
server.on('upgrade', (req, socket) => upgrade(req, socket));
server.listen(PORT, () => console.log('Open Skies Arena listening on http://localhost:' + PORT + '  (max ' + MAX_PLAYERS + ' per room)'));
