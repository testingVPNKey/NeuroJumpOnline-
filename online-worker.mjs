// NeuroJump Online — Cloudflare Worker
//   • accounts: registration through a separate Telegram bot, login with the key, session tokens (D1)
//   • Lobby (Durable Object): lobby chat, room list, create / quick play
//   • Room (Durable Object): one shared map for everybody, chat, positions, modifiers, win at WIN_SCORE
//
// HTTP:  POST /api/login {key,username?}  POST /api/me {token}  POST /api/nickname {token,username}
//        GET  /api/version   GET /health   POST /telegram/webhook
// WS:    /ws/lobby?token=..&v=..      /ws/room/<CODE>?token=..&v=..
//
// Game logic lives in RoomCore / LobbyCore (no Cloudflare APIs) so it can be tested on its own.

// ---- Settings (tune these) ----------------------------------------------------------------------
const C = {
  MIN_CAP: 10, MAX_CAP: 20, DEFAULT_CAP: 20,       // players per room (the creator picks 10..20)
  WIN_SCORE: 100000,                               // reaching this restarts the room
  WIN_BANNER_MS: 8000,                             // how long the winner is shown before the restart
  MOD_MS: 5 * 60 * 1000,                           // every modifier lasts 5 minutes
  TICK_MS: 100,                                    // positions are batched and sent 10 times per second
  // Anti-cheat "budgets": height may grow no faster than the modifier's `rise` px/s on average (a short burst
  // of RISE_BURST px is allowed for springs/trampolines); score may exceed 0.5*height only by enemy bonuses.
  RISE_BURST: 1500,
  KILL_RATE: 300, KILL_BURST: 1500,
  RESET_GRACE_MS: 1500,                            // after a reset, stale updates from the client are just ignored
  MAX_STRIKES: 8, STRIKE_FORGIVE_MS: 10000,        // implausible updates before a player is kicked (1 forgiven per 10 s)
  STATE_MAX_PER_SEC: 20,
  CHAT_MAX_LEN: 200, CHAT_BURST: 5, CHAT_WINDOW_MS: 10000, CHAT_HISTORY: 40,
  MAX_MSG_BYTES: 2048,
  NICK_RE: /^[A-Za-z0-9_]{3,16}$/,
  ROOM_NAME_MAX: 24,
  EMPTY_ROOM_TTL_MS: 60000,
  SESSION_TTL_MS: 30 * 24 * 3600 * 1000,
  AUTH_CHECK_MS: 15000,
  ROOM_CHAT_HISTORY: 40,                            // how often live connections are re-checked against the ban list
};
// Modifiers ("усложнения"). `forbid` lists what a player may NOT do; doing it sends the player back to the start.
// `rise` = the fastest believable climb in px/s while the modifier is active (server-side sanity check).
const MODS = {
  no_bonus: { name: 'Без бонусов', desc: 'Пружины, батуты, пропеллер и ранец запрещены', forbid: ['spring', 'flight'], rise: 450 },
  no_flight: { name: 'Без полётов', desc: 'Пропеллер и реактивный ранец запрещены', forbid: ['flight'], rise: 750 },
  no_spring: { name: 'Без пружин', desc: 'Пружины и батуты запрещены', forbid: ['spring'], rise: 1600 },
  no_shoot: { name: 'Без стрельбы', desc: 'Стрелять нельзя', forbid: ['shoot'], rise: 2300 },
  one_hit: { name: 'Одно касание', desc: 'Любой урон от врагов — и ты начинаешь сначала', forbid: ['hit'], rise: 2300 },
};
const MOD_IDS = Object.keys(MODS);
const DEFAULT_MIN_APP_VERSION = 1;
// -------------------------------------------------------------------------------------------------

const enc = new TextEncoder();
const clamp = (n, lo, hi) => Math.min(hi, Math.max(lo, n));
const isNum = (n) => typeof n === 'number' && Number.isFinite(n) && Math.abs(n) < 1e7;
const randomSeed = () => crypto.getRandomValues(new Uint32Array(1))[0];
const ROOM_ALPHABET = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const randomCode = () => [...crypto.getRandomValues(new Uint8Array(4))].map((x) => ROOM_ALPHABET[x % ROOM_ALPHABET.length]).join('');
const randomId = () => [...crypto.getRandomValues(new Uint8Array(4))].map((x) => x.toString(16).padStart(2, '0')).join('');
const hex = (bytes) => [...new Uint8Array(bytes)].map((x) => x.toString(16).padStart(2, '0')).join('');
function unhex(str) {
  if (typeof str !== 'string' || str.length % 2 || !/^[0-9a-f]+$/.test(str)) return null;
  const out = new Uint8Array(str.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(str.slice(i * 2, i * 2 + 2), 16);
  return out;
}
function sanitizeText(s, max) {
  if (typeof s !== 'string') return '';
  return s.normalize('NFKC')
    .replace(/[\u0000-\u001f\u007f-\u009f\u200b-\u200f\u2028-\u202e\u2060-\u206f\ufeff]/g, ' ')
    .replace(/\s+/g, ' ').trim().slice(0, max);
}
function rateOk(stamps, now, windowMs, max) {
  while (stamps.length && now - stamps[0] > windowMs) stamps.shift();
  if (stamps.length >= max) return false;
  stamps.push(now);
  return true;
}
const send = (p, obj) => p.sendRaw(JSON.stringify(obj));
function mulberry32(a) {
  return () => { a |= 0; a = (a + 0x6d2b79f5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}
// The order of modifiers in a run is a shuffle of all of them, derived from the run's seed (same for everybody).
function modOrder(seed) {
  const rnd = mulberry32(seed >>> 0), a = [...MOD_IDS];
  for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; }
  return a;
}
function modAt(seed, runStart, now) {
  const order = modOrder(seed);
  const idx = Math.max(0, Math.floor((now - runStart) / C.MOD_MS));
  const id = order[idx % order.length], next = order[(idx + 1) % order.length];
  return { idx, id, next, endsAt: runStart + (idx + 1) * C.MOD_MS };
}
const modInfo = (id) => ({ id, name: MODS[id].name, desc: MODS[id].desc });

// =================================================================================================
// RoomCore
// =================================================================================================
class RoomCore {
  constructor(cfg) {
    this.id = cfg.id;
    this.name = sanitizeText(cfg.name || '', C.ROOM_NAME_MAX) || 'Комната ' + cfg.id;
    this.cap = clamp(Number(cfg.cap) || C.DEFAULT_CAP, C.MIN_CAP, C.MAX_CAP);
    this.priv = !!cfg.priv;
    this.created = cfg.created || 0;
    this.players = new Map();
    this.history = [];
    this.phase = 'play';            // play | win
    this.seed = 0; this.runNo = 0; this.runStart = 0; this.winEnd = 0; this.winner = null;
    this.modIdx = -1;
    this.dirty = new Set();
    this.kick = () => {};           // set by the wrapper: kick(player, code)
  }
  cfg() { return { id: this.id, name: this.name, cap: this.cap, priv: this.priv, created: this.created }; }
  info() { return { id: this.id, name: this.name, cap: this.cap, priv: this.priv }; }
  mod(now) { return modAt(this.seed, this.runStart, now); }
  summary(now) {
    let top = 0;
    for (const p of this.players.values()) top = Math.max(top, p.s);
    const m = this.players.size ? this.mod(now || Date.now()).id : null;
    return { ...this.info(), players: this.players.size, phase: this.phase, mod: m, top };
  }
  playersList() {
    return [...this.players.values()].map((p) => ({ id: p.id, nick: p.nick, s: p.s }));
  }
  bcast(obj, exceptId) {
    const raw = JSON.stringify(obj);
    for (const p of this.players.values()) if (p.id !== exceptId) p.sendRaw(raw);
  }
  broadcastPlayers() { this.bcast({ t: 'players', players: this.playersList() }); }
  runPayload(now) {
    return { t: 'run', seed: this.seed, round: this.runNo, startAt: this.runStart, winScore: C.WIN_SCORE, phase: this.phase, winner: this.winner, now };
  }
  modPayload(now) {
    const m = this.mod(now);
    return { t: 'mod', ...modInfo(m.id), endsAt: m.endsAt, next: modInfo(m.next), duration: C.MOD_MS, now };
  }
  pushHistory(m) {
    this.history.push(m);
    if (this.history.length > C.ROOM_CHAT_HISTORY) this.history.shift();
  }
  onChat(p, raw, now) {
    const text = sanitizeText(raw, C.CHAT_MAX_LEN);
    if (!text) return;
    if (text === p.lastChat && now - p.lastChatAt < C.CHAT_WINDOW_MS) return;   // identical repeat
    if (!rateOk(p.chatTs, now, C.CHAT_WINDOW_MS, C.CHAT_BURST)) return send(p, { t: 'err', code: 'chat_slow' });
    p.lastChat = text; p.lastChatAt = now;
    const m = { t: 'chat', id: p.id, from: p.nick, text, ts: now };
    this.pushHistory(m);
    this.bcast(m);
  }
  resetPlayer(p, now) {
    p.s = 0; p.h = 0; p.pos = null; p.lastState = now; p.pStart = now; p.attDirty = true;
    p.riseBudget = C.RISE_BURST; p.killBudget = C.KILL_BURST; p.grace = now + C.RESET_GRACE_MS;
    this.dirty.delete(p.id);
    p.progDirty = false;
    if (this.onReset) this.onReset(p);            // a reset must reach the database at once (no reconnect may restore the old score)
  }
  startRun(now) {
    this.runNo++;
    this.seed = randomSeed();
    this.runStart = now;
    this.phase = 'play'; this.winner = null; this.winEnd = 0;
    this.modIdx = 0;
    for (const p of this.players.values()) { this.resetPlayer(p, now); p.strikes = 0; }
    this.dirty.clear();
    this.bcast(this.runPayload(now));
    this.bcast(this.modPayload(now));
    this.broadcastPlayers();
  }

  join(p, now, restored) {
    if (!restored) {
      for (const q of [...this.players.values()]) if (q.acc === p.acc) this.kick(q, 'other_device'); // one connection per account
      if (this.players.size >= this.cap) return { err: 'room_full' };
    }
    p.s = p.s || 0; p.h = p.h || 0; p.strikes = p.strikes || 0; p.pStart = p.pStart || now;
    p.chatTs = []; p.lastChat = ''; p.lastChatAt = 0; p.stateTs = []; p.lastState = restored ? now : 0; p.pos = null;
    p.riseBudget = C.RISE_BURST; p.killBudget = C.KILL_BURST; p.grace = 0; p.strikeAt = now;
    const wasEmpty = this.players.size === 0;
    this.players.set(p.id, p);
    if (restored) return { ok: true };
    send(p, { t: 'welcome', id: p.id, nick: p.nick, room: this.info(), now });
    send(p, { t: 'history', msgs: this.history });
    if (wasEmpty || this.runNo === 0) this.startRun(now);
    else {
      this.resetPlayer(p, now);
      send(p, this.runPayload(now));
      send(p, this.modPayload(now));
    }
    this.broadcastPlayers();
    return { ok: true };
  }
  leave(id, now) {
    const p = this.players.get(id);
    if (!p) return;
    this.players.delete(id);
    this.dirty.delete(id);
    if (this.players.size === 0) { this.phase = 'play'; this.winner = null; return; }
    this.broadcastPlayers();
  }
  // Disconnects every connection of an account (ban, deleted account). The player sees "session expired".
  // Puts the saved position back after a reconnect, but only inside the same run (a new run starts from zero).
  applyProgress(p, row, now) {
    if (this.phase !== 'play' || !this.players.has(p.id)) return false;
    p.h = row.h; p.s = row.s; p.pStart = now - (row.elapsed_ms || 0); p.lastState = now;
    p.pos = [row.x, row.y, row.vx, row.vy, 0]; p.attDirty = true; p.progDirty = false;
    this.dirty.add(p.id);
    send(p, { t: 'restore', x: row.x, y: row.y, vx: row.vx, vy: row.vy, h: row.h, s: row.s, now });
    return true;
  }
  kickAccount(acc, code) { for (const p of [...this.players.values()]) if (p.acc === acc) this.kick(p, code || 'session_expired'); }
  deadline() { return this.phase === 'win' ? this.winEnd : null; }
  tick(now) {
    if (!this.players.size) return;
    if (this.phase === 'win') { if (now >= this.winEnd) this.startRun(now); return; }
    const m = this.mod(now);
    if (m.idx !== this.modIdx) { this.modIdx = m.idx; this.bcast(this.modPayload(now)); }
    this.flushPositions();
  }
  flushPositions() {
    if (!this.dirty.size) return;
    const all = [];
    for (const id of this.dirty) {
      const q = this.players.get(id);
      if (q && q.pos) all.push([id, ...q.pos, q.h, q.s]);
    }
    const dirtyIds = this.dirty;
    this.dirty = new Set();
    if (!all.length) return;
    const full = JSON.stringify({ t: 'snap', p: all });
    for (const p of this.players.values()) {
      if (!dirtyIds.has(p.id)) { p.sendRaw(full); continue; }
      const others = all.filter((e) => e[0] !== p.id);
      if (others.length) send(p, { t: 'snap', p: others });
    }
  }

  handle(id, msg, now) {
    const p = this.players.get(id);
    if (!p || !msg || typeof msg !== 'object') return;
    switch (msg.t) {
      case 'chat': return this.onChat(p, msg.text, now);
      case 'state': return this.onState(p, msg, now);
      case 'use': return this.onUse(p, msg.kind, now);
      case 'died':
        if (this.phase !== 'play') return;
        this.resetPlayer(p, now);
        this.bcast({ t: 'reset', id: p.id, nick: p.nick, why: 'died' });
        return;
      case 'ping': return send(p, { t: 'pong', c: msg.c, now });
      default: return;
    }
  }
  onUse(p, kind, now) {
    if (this.phase !== 'play' || typeof kind !== 'string') return;
    const m = this.mod(now);
    if (!MODS[m.id].forbid.includes(kind)) return;
    this.resetPlayer(p, now);
    this.bcast({ t: 'reset', id: p.id, nick: p.nick, why: 'mod', kind, mod: m.id });
  }
  onState(p, m, now) {
    if (this.phase !== 'play') return;
    if (!rateOk(p.stateTs, now, 1000, C.STATE_MAX_PER_SEC)) return;
    if (!isNum(m.x) || !isNum(m.y) || !isNum(m.vx) || !isNum(m.vy) || !isNum(m.h) || !isNum(m.s)) return;
    const dtS = Math.min(Math.max(0, now - (p.lastState || p.pStart)), 10000) / 1000;
    p.lastState = now;
    const rate = MODS[this.mod(now).id].rise;
    let h = Math.max(0, Math.floor(m.h)), s = Math.max(0, Math.floor(m.s)), bad = false;
    // height: leaky bucket
    p.riseBudget = Math.min(C.RISE_BURST, p.riseBudget + rate * dtS);
    const rise = h - p.h;
    if (rise > p.riseBudget) { h = p.h + Math.floor(p.riseBudget); p.riseBudget = 0; bad = true; }
    else if (rise > 0) p.riseBudget -= rise;
    // score: 0.5 per px of height plus enemy bonuses (their own bucket)
    p.killBudget = Math.min(C.KILL_BURST, p.killBudget + C.KILL_RATE * dtS);
    const hh = Math.max(h, p.h), prevExtra = p.s - 0.5 * p.h, extra = s - 0.5 * hh;
    if (extra - prevExtra > p.killBudget) { s = Math.floor(0.5 * hh + prevExtra + p.killBudget); p.killBudget = 0; bad = true; }
    else if (extra > prevExtra) p.killBudget -= extra - prevExtra;
    if (bad) {
      if (now < p.grace) return;                               // stale update right after a reset: ignore, no strike
      p.strikes = Math.max(0, p.strikes - Math.floor((now - p.strikeAt) / C.STRIKE_FORGIVE_MS));
      p.strikeAt = now;
      if (++p.strikes > C.MAX_STRIKES) { this.kick(p, 'cheating'); return; }
    }
    if (h > p.h) { p.h = h; p.attDirty = true; }
    if (s > p.s) { p.s = s; p.attDirty = true; }
    p.pos = [Math.round(m.x), Math.round(m.y), Math.round(m.vx), Math.round(m.vy), m.f ? 1 : 0];
    this.dirty.add(p.id);
    p.progDirty = true;
    if (p.s >= C.WIN_SCORE) this.win(p, now);
  }
  win(p, now) {
    this.phase = 'win';
    this.winEnd = now + C.WIN_BANNER_MS;
    this.winner = { id: p.id, nick: p.nick, score: p.s };
    this.dirty.clear();
    this.bcast({ t: 'win', id: p.id, nick: p.nick, score: p.s, round: this.runNo, restartAt: this.winEnd, now });
  }
}

// =================================================================================================
// LobbyCore
// =================================================================================================
class LobbyCore {
  constructor() {
    this.players = new Map();
    this.rooms = new Map();
    this.history = [];
    this.roomsDirty = false;
    this.removed = [];
    this.kick = () => {};
  }
  listRooms() {
    return [...this.rooms.values()]
      .filter((r) => !r.priv)
      .sort((a, b) => b.players - a.players || a.created - b.created)
      .map((r) => ({ id: r.id, name: r.name, players: r.players, cap: r.cap, mod: r.mod || null, top: r.top || 0 }));
  }
  bcast(obj) {
    const raw = JSON.stringify(obj);
    for (const p of this.players.values()) p.sendRaw(raw);
  }
  roomsPayload() { return { t: 'rooms', online: this.players.size, rooms: this.listRooms() }; }
  join(p, now, restored) {
    if (!restored) for (const q of [...this.players.values()]) if (q.acc === p.acc) this.kick(q, 'other_device');
    p.chatTs = []; p.lastChat = ''; p.lastChatAt = 0; p.muted = false;
    this.players.set(p.id, p);
    if (!restored) {
      send(p, { t: 'welcome', id: p.id, nick: p.nick, now });
      send(p, { t: 'history', msgs: this.history });
      send(p, this.roomsPayload());
    }
    this.roomsDirty = true;
    return { ok: true };
  }
  leave(id) { if (this.players.delete(id)) this.roomsDirty = true; }
  kickAccount(acc, code) { for (const p of [...this.players.values()]) if (p.acc === acc) this.kick(p, code || 'session_expired'); }
  registerRoom(r, now) {
    this.rooms.set(r.id, { id: r.id, name: r.name, cap: r.cap, priv: !!r.priv, players: 0, mod: null, top: 0, created: now, updated: now });
    this.roomsDirty = true;
  }
  roomUpdate(s, now) {
    const r = this.rooms.get(s.id);
    if (!r) return;
    Object.assign(r, { players: s.players, name: s.name, cap: s.cap, mod: s.mod, top: s.top, updated: now });
    this.roomsDirty = true;
  }
  tick(now) {
    for (const [id, r] of this.rooms) {
      if (r.players === 0 && now - r.updated > C.EMPTY_ROOM_TTL_MS) { this.rooms.delete(id); this.removed.push(id); this.roomsDirty = true; }
    }
    if (this.roomsDirty) { this.roomsDirty = false; this.bcast(this.roomsPayload()); }
  }
  handle(id, msg, now) {
    const p = this.players.get(id);
    if (!p || !msg || typeof msg !== 'object') return null;
    switch (msg.t) {
      case 'chat': {
        const text = sanitizeText(msg.text, C.CHAT_MAX_LEN);
        if (!text || p.muted) return null;
        if (text === p.lastChat && now - p.lastChatAt < C.CHAT_WINDOW_MS) return null;
        if (!rateOk(p.chatTs, now, C.CHAT_WINDOW_MS, C.CHAT_BURST)) { send(p, { t: 'err', code: 'chat_slow' }); return null; }
        p.lastChat = text; p.lastChatAt = now;
        const m = { t: 'chat', id: p.id, from: p.nick, text, ts: now };
        this.history.push(m);
        if (this.history.length > C.CHAT_HISTORY) this.history.shift();
        this.bcast(m);
        return null;
      }
      case 'rooms': send(p, this.roomsPayload()); return null;
      case 'ping': send(p, { t: 'pong', c: msg.c, now }); return null;
      case 'create': {
        const cap = clamp(Math.floor(Number(msg.cap)) || C.DEFAULT_CAP, C.MIN_CAP, C.MAX_CAP);
        return { action: 'create', playerId: id, room: { id: randomCode(), name: sanitizeText(msg.name, C.ROOM_NAME_MAX), cap, priv: !!msg.priv } };
      }
      case 'quick': {
        const open = this.listRooms().find((r) => r.players < r.cap);
        if (open) { send(p, { t: 'go', room: open.id }); return null; }
        return { action: 'create', playerId: id, room: { id: randomCode(), name: '', cap: C.DEFAULT_CAP, priv: false } };
      }
      default: return null;
    }
  }
}

// =================================================================================================
// Accounts, sessions, Telegram bot
// =================================================================================================
const json = (data, status = 200) => new Response(JSON.stringify(data), { status, headers: JSON_HEADERS });
const JSON_HEADERS = {
  'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
  'Access-Control-Allow-Headers': 'Content-Type', 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store',
};
const nowIso = () => new Date().toISOString();
async function sha256(value) { return hex(await crypto.subtle.digest('SHA-256', enc.encode(value))); }
function randomKey() {
  const b = crypto.getRandomValues(new Uint8Array(32));
  return 'NJO-' + btoa(String.fromCharCode(...b)).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/g, '');
}
function normalizeNick(v) {
  if (typeof v !== 'string') return null;
  const n = v.trim();
  return C.NICK_RE.test(n) ? n : null;
}
const sessionSecret = (env) => env.SESSION_SECRET || env.TELEGRAM_WEBHOOK_SECRET || null;
async function hmacKey(secret, usage) { return crypto.subtle.importKey('raw', enc.encode(secret), { name: 'HMAC', hash: 'SHA-256' }, false, [usage]); }
async function signToken(secret, accId, exp) {
  const sig = await crypto.subtle.sign('HMAC', await hmacKey(secret, 'sign'), enc.encode(`${accId}.${exp}`));
  return `${accId}.${exp}.${hex(sig)}`;
}
async function verifyToken(secret, token, now) {
  if (typeof token !== 'string' || token.length > 200) return null;
  const parts = token.split('.');
  if (parts.length !== 3) return null;
  const [accId, expRaw, sigHex] = parts, exp = Number(expRaw), sig = unhex(sigHex);
  if (!/^[A-Za-z0-9-]{8,64}$/.test(accId) || !Number.isSafeInteger(exp) || !sig || exp < now) return null;
  const ok = await crypto.subtle.verify('HMAC', await hmacKey(secret, 'verify'), sig, enc.encode(`${accId}.${exp}`));
  return ok ? { id: accId, exp } : null;
}
async function accountFromKey(db, key) {
  if (typeof key !== 'string' || key.length < 20 || key.length > 100) return null;
  return db.prepare('SELECT id, telegram_id, username, banned, ban_reason FROM accounts WHERE key_hash = ?').bind(await sha256(key.trim())).first();
}
async function revokedAccounts(db, ids) {
  const out = [];
  for (let i = 0; i < ids.length; i += 50) {
    const chunk = ids.slice(i, i + 50);
    const { results } = await db.prepare(`SELECT id FROM accounts WHERE id IN (${chunk.map(() => '?').join(',')}) AND (banned = 1 OR username IS NULL)`).bind(...chunk).all();
    for (const r of results || []) out.push(r.id);
  }
  return out;
}
// ---- D1 helpers: the room registry and each player's last saved point. Failures never break the game.
const dbRun = (env, sql, args) => Promise.resolve().then(() => env.DB.prepare(sql).bind(...args).run())
  .catch((e) => console.error('db write failed:', e && e.message));
const SAVE_PROGRESS_SQL = 'INSERT INTO progress (account_id, room_id, run_no, x, y, vx, vy, h, s, elapsed_ms, updated_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?) ON CONFLICT(account_id, room_id) DO UPDATE SET run_no = excluded.run_no, x = excluded.x, y = excluded.y, vx = excluded.vx, vy = excluded.vy, h = excluded.h, s = excluded.s, elapsed_ms = excluded.elapsed_ms, updated_at = excluded.updated_at';
const SAVE_ROOM_SQL = 'INSERT INTO rooms (id, name, cap, priv, created_at, updated_at, closed) VALUES (?, ?, ?, ?, ?, ?, 0) ON CONFLICT(id) DO UPDATE SET name = excluded.name, cap = excluded.cap, priv = excluded.priv, updated_at = excluded.updated_at, closed = 0';
// Tells the lobby (and through it every room) to disconnect an account right now.
async function kickAccount(env, acc, code) {
  if (!env.LOBBY) return;
  try { await env.LOBBY.get(env.LOBBY.idFromName('main')).fetch('https://lobby/internal/kick', { method: 'POST', body: JSON.stringify({ acc, code: code || 'session_expired' }) }); }
  catch { /* connections are also re-checked every few seconds */ }
}
const bodyJson = async (request) => { try { return await request.json(); } catch { return null; } };

async function telegramCall(env, method, payload) {
  if (!env.TELEGRAM_BOT_TOKEN) throw new Error('Missing TELEGRAM_BOT_TOKEN secret');
  const r = await fetch(`https://api.telegram.org/bot${env.TELEGRAM_BOT_TOKEN}/${method}`, {
    method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(payload),
  });
  const data = await r.json();
  if (!r.ok || !data.ok) throw new Error(`Telegram API error: ${method}`);
  return data.result;
}
const telegramSend = (env, chatId, text, markup) => telegramCall(env, 'sendMessage', { chat_id: chatId, text, ...(markup ? { reply_markup: markup } : {}) });
const isAdmin = (env, tgId) => String(env.ADMIN_TELEGRAM_IDS || '').split(',').map((s) => s.trim()).filter(Boolean).includes(String(tgId));

async function registerTelegramAccount(db, telegramId) {
  const existing = await db.prepare('SELECT id FROM accounts WHERE telegram_id = ?').bind(String(telegramId)).first();
  if (existing) return { existing: true };
  const id = crypto.randomUUID(), key = randomKey();
  try {
    await db.prepare('INSERT INTO accounts (id, telegram_id, key_hash, created_at) VALUES (?, ?, ?, ?)').bind(id, String(telegramId), await sha256(key), nowIso()).run();
  } catch {
    const raced = await db.prepare('SELECT id FROM accounts WHERE telegram_id = ?').bind(String(telegramId)).first();
    if (raced) return { existing: true };
    throw new Error('Could not register account');
  }
  return { existing: false, key, accountId: id };
}
async function findByNick(db, nick) {
  if (!nick) return null;
  return db.prepare('SELECT id, telegram_id, username, banned, ban_reason, created_at FROM accounts WHERE username = ? COLLATE NOCASE').bind(nick).first();
}
const UNBAN_BUTTON = (id) => ({ inline_keyboard: [[{ text: 'Разбанить', callback_data: 'unban:' + id }]] });

async function handleAdminCommand(env, chatId, text) {
  const [cmd, nickRaw, ...rest] = text.split(/\s+/);
  const nick = normalizeNick(nickRaw || '');
  if (!nick) return telegramSend(env, chatId, 'Формат: ' + (cmd === '/ban' ? '/ban ник причина' : cmd + ' ник'));
  const acc = await findByNick(env.DB, nick);
  if (!acc) return telegramSend(env, chatId, `Игрок «${nick}» не найден.`);
  if (cmd === '/ban') {
    const reason = rest.join(' ').slice(0, 200) || null;
    await env.DB.prepare('UPDATE accounts SET banned = 1, ban_reason = ?, banned_at = ?, updated_at = ? WHERE id = ?').bind(reason, nowIso(), nowIso(), acc.id).run();
    await kickAccount(env, acc.id, 'session_expired');
    return telegramSend(env, chatId, `Забанен: ${acc.username}${reason ? ' — ' + reason : ''}\nЕсли игрок сейчас в игре, он будет отключён сразу («время сессии истекло»), войти заново не сможет.`, UNBAN_BUTTON(acc.id));
  }
  if (cmd === '/unban') {
    await env.DB.prepare('UPDATE accounts SET banned = 0, ban_reason = NULL, banned_at = NULL, updated_at = ? WHERE id = ?').bind(nowIso(), acc.id).run();
    return telegramSend(env, chatId, `Разбанен: ${acc.username}`);
  }
  if (cmd === '/who') {
    return telegramSend(env, chatId, `Ник: ${acc.username}\nСтатус: ${acc.banned ? 'ЗАБАНЕН' + (acc.ban_reason ? ' (' + acc.ban_reason + ')' : '') : 'активен'}\nСоздан: ${acc.created_at || '—'}\nTelegram ID: ${acc.telegram_id}`, acc.banned ? UNBAN_BUTTON(acc.id) : undefined);
  }
}
// Gives the player a fresh key (the old one stops working). Used when the key was lost.
async function reissueKey(db, telegramId) {
  const acc = await db.prepare('SELECT id FROM accounts WHERE telegram_id = ?').bind(String(telegramId)).first();
  if (!acc) return null;
  const key = randomKey();
  await db.prepare('UPDATE accounts SET key_hash = ?, updated_at = ? WHERE id = ?').bind(await sha256(key), nowIso(), acc.id).run();
  return key;
}
const KEY_TEXT = (key, fresh) => `${fresh ? 'Новый ключ NeuroJump Online (старый больше не работает)' : 'Аккаунт NeuroJump Online создан!\n\nТвой ключ (сохрани его)'}:\n${key}\n\nВведи ключ в игре и выбери ник: 3–16 символов, латинские буквы, цифры и _.\n\nНе отправляй ключ другим людям.`;
async function processTelegramUpdate(update, env) {
  if (update.callback_query) {
    const cq = update.callback_query;
    try { await telegramCall(env, 'answerCallbackQuery', { callback_query_id: cq.id }); } catch (e) { console.error('answerCallbackQuery failed:', e && e.message); }
    const chatId = cq.message?.chat?.id;
    if (!chatId || !cq.from?.id) return;
    if (cq.data === 'nj_register') {
      const r = await registerTelegramAccount(env.DB, cq.from.id);
      if (r.existing) {
        await telegramSend(env, chatId, 'У тебя уже есть аккаунт NeuroJump Online. Если ключ потерян, нажми кнопку ниже: старый ключ перестанет работать, а ник и вход сохранятся.',
          { inline_keyboard: [[{ text: 'Получить новый ключ', callback_data: 'nj_newkey' }]] });
      } else {
        try { await telegramSend(env, chatId, KEY_TEXT(r.key, false)); }
        catch (e) { await env.DB.prepare('DELETE FROM accounts WHERE id = ?').bind(r.accountId).run(); throw e; } // the key never reached the player: undo, so they can retry
      }
    } else if (cq.data === 'nj_newkey') {
      const key = await reissueKey(env.DB, cq.from.id);
      await telegramSend(env, chatId, key ? KEY_TEXT(key, true) : 'Аккаунта ещё нет. Нажми /start и создай его.');
    } else if (cq.data?.startsWith('unban:') && isAdmin(env, cq.from.id)) {
      await env.DB.prepare('UPDATE accounts SET banned = 0, ban_reason = NULL, banned_at = NULL, updated_at = ? WHERE id = ?').bind(nowIso(), cq.data.slice(6)).run();
      await telegramSend(env, chatId, 'Аккаунт разбанен.');
    }
    return;
  }
  const msg = update.message;
  if (msg?.text && msg.chat?.id) {
    const text = msg.text.trim();
    if (text === '/start' || text.startsWith('/start ')) {
      await telegramSend(env, msg.chat.id, 'Регистрация NeuroJump Online теперь на сайте: ' + (env.SITE_URL || 'https://neurojump-online.tanyayuryi.workers.dev') + '/register\n\nПосле регистрации введите ключ в игре.');
    } else if (text === '/help') {
      await telegramSend(env, msg.chat.id, 'Команды:\n/start — регистрация\n/help — помощь\n\nКлюч нужен для входа в игру. Не публикуй его.');
    } else if (/^\/(ban|unban|who)(\s|$)/.test(text) && msg.from?.id && isAdmin(env, msg.from.id)) {
      await handleAdminCommand(env, msg.chat.id, text);
    } else {
      await telegramSend(env, msg.chat.id, 'Используй /start для регистрации.');
    }
  }
}
// Always answer 200 to Telegram (otherwise it keeps re-sending the update). Failures are logged and reported in the chat.
async function handleTelegramUpdate(request, env) {
  const expected = env.TELEGRAM_WEBHOOK_SECRET;
  if (!expected || request.headers.get('X-Telegram-Bot-Api-Secret-Token') !== expected) return json({ error: 'forbidden' }, 403);
  const update = await bodyJson(request);
  if (!update) return json({ ok: true });
  try {
    await processTelegramUpdate(update, env);
  } catch (e) {
    console.error('telegram update failed:', e && e.message);
    const chatId = update.callback_query ? update.callback_query.message?.chat?.id : update.message?.chat?.id;
    const fromId = update.callback_query ? update.callback_query.from?.id : update.message?.from?.id;
    if (chatId) {
      const detail = isAdmin(env, fromId) ? '\n\n[для админа] ' + String((e && e.message) || e).slice(0, 300) : '';
      try { await telegramSend(env, chatId, 'Не получилось. Попробуй ещё раз чуть позже.' + detail); } catch { /* nothing more to do */ }
    }
  }
  return json({ ok: true });
}
// What is configured (never shows secret values) — open /status in a browser to find setup mistakes.
async function statusReport(env) {
  const s = { ok: true, db: !!env.DB, lobby: !!env.LOBBY, room: !!env.ROOM, secrets: {
    TELEGRAM_BOT_TOKEN: !!env.TELEGRAM_BOT_TOKEN, TELEGRAM_WEBHOOK_SECRET: !!env.TELEGRAM_WEBHOOK_SECRET, SESSION_SECRET: !!env.SESSION_SECRET, ADMIN_TELEGRAM_IDS: !!env.ADMIN_TELEGRAM_IDS } };
  if (env.DB) {
    try { await env.DB.prepare('SELECT COUNT(*) AS n FROM accounts').first(); s.accounts_table = true; }
    catch (e) { s.accounts_table = false; s.db_error = String((e && e.message) || e).slice(0, 200); }
  }
  if (env.TELEGRAM_BOT_TOKEN) {
    try { const w = await telegramCall(env, 'getWebhookInfo', {}); s.webhook = { url: w.url || null, pending: w.pending_update_count || 0, last_error: w.last_error_message || null }; }
    catch (e) { s.webhook = { error: String((e && e.message) || e).slice(0, 100) }; }
  }
  return s;
}

// Текст документов. Реквизиты в {{…}} заполняет владелец сервиса. Документы нужно проверить юристом.
const PRIVACY_VERSION = '2026-11-18';
const TERMS_VERSION = '2026-11-18';
const OPERATOR = '{{ИМЯ_ВЛАДЕЛЬЦА}}';
const CONTACT = '{{EMAIL_ДЛЯ_ВОПРОСОВ}}';
const PRIVACY_HTML = `
<h1>Политика конфиденциальности NeuroJump Online</h1>
<p>Версия от ${PRIVACY_VERSION}. Оператор сервиса: ${OPERATOR}. Контакт: ${CONTACT}.</p>
<h2>1. Какие данные мы храним</h2>
<ul>
<li>Никнейм, который вы выбрали при регистрации.</li>
<li>Хеш ключа доступа. Сам ключ мы не храним: он показывается вам один раз при регистрации.</li>
<li>Результаты игры: лучший счёт, высота, позиция персонажа в текущем забеге, сообщения в чате комнаты.</li>
<li>Идентификатор устройства, созданный игрой (нужен для защиты от накрутки).</li>
<li>Дата и время регистрации, а также версии документов, которые вы приняли.</li>
</ul>
<h2>2. Зачем</h2>
<p>Чтобы вы могли входить в аккаунт, участвовать в таблице и комнатах, сохранять прогресс при переподключении и защищать игру от читов.</p>
<h2>3. Что мы не делаем</h2>
<p>Мы не показываем рекламу, не продаём данные и не передаём их третьим лицам, кроме случаев, которые требует закон.</p>
<h2>4. Хранение и защита</h2>
<p>Данные хранятся на платформе Cloudflare. Ключ хранится только в виде хеша. Серверные журналы может вести хостинг-провайдер в объёме, который он использует для работы сервиса.</p>
<h2>5. Ваши права</h2>
<p>Вы можете удалить аккаунт в настройках игры: ник и результаты будут очищены, а ключ перестанет давать доступ к прежнему профилю. Вы можете запросить полное удаление данных, написав по адресу ${CONTACT}.</p>
<h2>6. Дети</h2>
<p>Сервис не предназначен для детей младше возраста, установленного законодательством страны пользователя. Если вы считаете, что ребёнок зарегистрировался без согласия родителей, напишите нам.</p>
<h2>7. Изменения</h2>
<p>При изменении документа мы обновим дату версии. Продолжая пользоваться сервисом после изменения, вы соглашаетесь с новой версией, а при существенных изменениях попросим подтвердить её.</p>
`;
const TERMS_HTML = `
<h1>Условия использования NeuroJump Online</h1>
<p>Версия от ${TERMS_VERSION}. Оператор сервиса: ${OPERATOR}. Контакт: ${CONTACT}.</p>
<h2>1. Общие положения</h2>
<p>Регистрируясь, вы подтверждаете, что прочли и принимаете эти условия и политику конфиденциальности.</p>
<h2>2. Аккаунт</h2>
<p>Ключ доступа — ваша ответственность. Не передавайте его другим людям. Ник не должен быть оскорбительным, выдавать себя за другого человека или нарушать права третьих лиц. Мы можем изменить или освободить ник, нарушающий эти правила.</p>
<h2>3. Честная игра</h2>
<p>Запрещено использовать программы, изменяющие игру, эксплуатировать ошибки, накручивать результаты и мешать другим игрокам. За нарушения аккаунт может быть заблокирован, и блокировка действует без возврата.</p>
<h2>4. Чат</h2>
<p>В сообщениях запрещены оскорбления, угрозы, спам и незаконный контент. Мы можем удалять такие сообщения и блокировать аккаунты.</p>
<h2>5. Сервис</h2>
<p>Сервис предоставляется «как есть». Мы можем изменять правила, усложнения и функции, а также временно приостанавливать работу для обслуживания.</p>
<h2>6. Ответственность</h2>
<p>В пределах, разрешённых законом, оператор не отвечает за потерю прогресса вследствие сбоев связи или действий пользователя.</p>
<h2>7. Прекращение</h2>
<p>Вы можете удалить аккаунт в любой момент. Мы можем заблокировать аккаунт при нарушении этих условий.</p>
`;

// ---- Website: registration, privacy policy, terms (served by this Worker, no external scripts) ----
const PAGE_CSS = `body{margin:0;font-family:"Trebuchet MS","Segoe UI",Roboto,system-ui,sans-serif;background:#f7f3e8;color:#2d2a32;line-height:1.5}
main{max-width:620px;margin:0 auto;padding:18px}
h1{color:#ff7a3d;font-size:28px;text-shadow:0 2px 0 #2d2a32;margin:10px 0 14px}
h2{font-size:18px;margin:18px 0 6px}
.card{background:#fff;border:4px solid #2d2a32;border-radius:22px;padding:16px;box-shadow:0 6px 0 #2d2a32}
label{display:block;font-weight:700;margin:12px 0 6px}
input[type=text]{box-sizing:border-box;width:100%;padding:12px;border:3px solid #2d2a32;border-radius:14px;font-family:inherit;font-size:17px;font-weight:600;background:#f7f3e8}
.chk{display:flex;gap:10px;align-items:flex-start;margin:12px 0;font-weight:600}
.chk input{width:24px;height:24px;margin:2px 0 0}
.btn{display:block;width:100%;box-sizing:border-box;text-align:center;text-decoration:none;padding:14px;margin:10px 0;border:4px solid #2d2a32;border-radius:999px;background:#ffc83c;color:#2d2a32;font-size:18px;font-weight:800;box-shadow:0 5px 0 #2d2a32;cursor:pointer}
.btn.green{background:#5cc15a;color:#fff}.btn.blue{background:#4fb5e8;color:#fff}.btn.orange{background:#ff7a3d;color:#fff}
.btn:disabled{opacity:.5;cursor:not-allowed}
.msg{min-height:24px;margin:10px 0;font-weight:700;color:#d9363e}
.key{word-break:break-all;font:700 16px monospace;background:#fff3c4;border:3px solid #2d2a32;border-radius:14px;padding:12px;margin:10px 0}
.note{font-size:14px;color:#6a6573}
.docs{display:grid;gap:4px}`;
const PAGE = (title, body) => `<!doctype html><html lang="ru"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>${title}</title><style>${PAGE_CSS}</style></head><body><main>${body}</main></body></html>`;
const htmlResp = (body, status = 200) => new Response(body, { status, headers: { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache', 'Content-Security-Policy': "default-src 'none'; style-src 'unsafe-inline'; script-src 'unsafe-inline'; connect-src 'self'; base-uri 'none'; form-action 'self'" } });

const DOC_LINKS = `<div class="docs">
<a class="btn blue" href="/privacy" target="_blank" rel="noopener">Политика конфиденциальности</a>
<a class="btn blue" href="/terms" target="_blank" rel="noopener">Условия использования</a></div>`;

function registerPage() {
  return PAGE('Регистрация NeuroJump Online', `
<h1>NeuroJump Online</h1>
<div class="card" id="form-card">
<h2>Создать аккаунт</h2>
<p class="note">Ник видят другие игроки. Ключ, который вы получите, нужен для входа в игру — сохраните его, он показывается один раз.</p>
<form id="f" autocomplete="off">
<label for="nick">Никнейм (3–16 символов: латиница, цифры, _)</label>
<input id="nick" type="text" maxlength="16" autocapitalize="off" spellcheck="false" required>
<label class="chk"><input id="ca" type="checkbox"> <span>Я прочёл(а) и принимаю <a href="/privacy" target="_blank" rel="noopener">политику конфиденциальности</a></span></label>
<label class="chk"><input id="cb" type="checkbox"> <span>Я прочёл(а) и принимаю <a href="/terms" target="_blank" rel="noopener">условия использования</a></span></label>
<div class="msg" id="msg" aria-live="polite"></div>
<button class="btn green" id="go" type="submit" disabled>Создать аккаунт</button>
</form>
${DOC_LINKS}
</div>
<div class="card" id="done" hidden>
<h2>Аккаунт создан</h2>
<p>Ваш ключ входа:</p>
<div class="key" id="key"></div>
<button class="btn blue" id="copy" type="button">Копировать ключ</button>
<p class="note">Введите ключ в игре: «Аккаунт» → вставьте ключ. Ник уже выбран. Ключ больше нигде не показывается — сохраните его.</p>
</div>
<script>
(function(){
var f=document.getElementById('f'),go=document.getElementById('go'),ca=document.getElementById('ca'),cb=document.getElementById('cb'),msg=document.getElementById('msg');
function sync(){go.disabled=!(ca.checked&&cb.checked)}
ca.addEventListener('change',sync);cb.addEventListener('change',sync);sync();
var ERR={invalid_username:'Ник: 3–16 символов, латиница, цифры и _.',consent_required:'Нужно принять оба документа.',documents_changed:'Документы обновились. Обновите страницу и прочтите их заново.',username_taken:'Этот ник уже занят.'};
f.addEventListener('submit',function(e){
  e.preventDefault();
  if(!(ca.checked&&cb.checked)){msg.textContent=ERR.consent_required;return}
  go.disabled=true;msg.textContent='Создаём аккаунт…';
  fetch('/api/register',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:document.getElementById('nick').value.trim(),accept_privacy:ca.checked,accept_terms:cb.checked,privacy_version:'${PRIVACY_VERSION}',terms_version:'${TERMS_VERSION}'})})
  .then(function(r){return r.json().then(function(j){return {ok:r.ok,j:j}},function(){return {ok:false,j:{}}})})
  .then(function(x){
    if(x.ok&&x.j.key){document.getElementById('key').textContent=x.j.key;document.getElementById('form-card').hidden=true;document.getElementById('done').hidden=false;return}
    msg.textContent=ERR[x.j.error]||'Не получилось создать аккаунт. Попробуйте ещё раз чуть позже.';go.disabled=false;sync();
  },function(){msg.textContent='Нет связи с сервером.';go.disabled=false;sync()});
});
document.getElementById('copy').addEventListener('click',function(){var t=document.getElementById('key').textContent;if(navigator.clipboard)navigator.clipboard.writeText(t).then(function(){document.getElementById('copy').textContent='Скопировано'});});
})();
</script>`);
}
const documentPage = (title, html) => PAGE(title, html + `<p><a class="btn orange" href="/register">Назад к регистрации</a></p>`);

// Creates an account from the website. Both documents must be accepted, and the versions must be the current ones.
async function handleRegister(request, env) {
  const body = await bodyJson(request);
  const nick = normalizeNick(body?.username);
  if (!nick) return json({ error: 'invalid_username' }, 400);
  if (body?.accept_privacy !== true || body?.accept_terms !== true) return json({ error: 'consent_required' }, 400);
  if (body?.privacy_version !== PRIVACY_VERSION || body?.terms_version !== TERMS_VERSION) return json({ error: 'documents_changed' }, 409);
  if (!env.DB) return json({ error: 'server_misconfigured' }, 500);
  const id = crypto.randomUUID(), key = randomKey(), now = nowIso();
  try {
    await env.DB.prepare('INSERT INTO accounts (id, telegram_id, key_hash, username, created_at, updated_at, privacy_version, terms_version, accepted_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)')
      .bind(id, 'web:' + id, await sha256(key), nick, now, now, PRIVACY_VERSION, TERMS_VERSION, now).run();
  } catch (e) {
    if (/UNIQUE/i.test(String((e && e.message) || ''))) return json({ error: 'username_taken' }, 409);
    throw e;
  }
  return json({ ok: true, key, username: nick });
}

const SITE_PAGES = {
  '/': registerPage,
  '/register': registerPage,
  '/privacy': () => documentPage('Политика конфиденциальности', PRIVACY_HTML),
  '/terms': () => documentPage('Условия использования', TERMS_HTML),
};

// ---- HTTP API ----
const intVar = (v, d) => { const n = Number.parseInt(v, 10); return Number.isFinite(n) ? n : d; };
const accountPublic = (a) => ({ id: a.id, username: a.username });
async function handleApi(request, env, url) {
  const secret = sessionSecret(env);
  if (!secret) return json({ error: 'server_misconfigured' }, 500);
  if (url.pathname === '/api/login' && request.method === 'POST') {
    const body = await bodyJson(request);
    const acc = await accountFromKey(env.DB, body?.key);
    if (!acc) return json({ error: 'invalid_key' }, 401);
    if (acc.banned) return json({ error: 'account_banned', reason: acc.ban_reason || null }, 403);
    let username = acc.username;
    if (!username) {
      const nick = normalizeNick(body?.username);
      if (!nick) return json({ error: 'username_required', rules: '3-16 characters: Latin letters, digits, underscore' }, 400);
      try {
        await env.DB.prepare('UPDATE accounts SET username = ?, updated_at = ? WHERE id = ? AND username IS NULL').bind(nick, nowIso(), acc.id).run();
      } catch { return json({ error: 'username_taken' }, 409); }
      username = nick;
    }
    const token = await signToken(secret, acc.id, Date.now() + C.SESSION_TTL_MS);
    return json({ ok: true, token, account: { id: acc.id, username } });
  }
  if (url.pathname === '/api/me' && request.method === 'POST') {
    const body = await bodyJson(request);
    const t = await verifyToken(secret, body?.token, Date.now());
    if (!t) return json({ error: 'invalid_token' }, 401);
    const acc = await env.DB.prepare('SELECT id, username, banned FROM accounts WHERE id = ?').bind(t.id).first();
    if (!acc) return json({ error: 'invalid_token' }, 401);
    if (acc.banned) return json({ error: 'account_banned' }, 403);
    return json({ ok: true, account: accountPublic(acc) });
  }
  if (url.pathname === '/api/nickname' && request.method === 'POST') {
    const body = await bodyJson(request);
    const t = await verifyToken(secret, body?.token, Date.now());
    if (!t) return json({ error: 'invalid_token' }, 401);
    const acc = await env.DB.prepare('SELECT id, username, banned FROM accounts WHERE id = ?').bind(t.id).first();
    if (!acc) return json({ error: 'invalid_token' }, 401);
    if (acc.banned) return json({ error: 'account_banned' }, 403);
    const nick = normalizeNick(body?.username);
    if (!nick) return json({ error: 'invalid_username', rules: '3-16 characters: Latin letters, digits, underscore' }, 400);
    try { await env.DB.prepare('UPDATE accounts SET username = ?, updated_at = ? WHERE id = ?').bind(nick, nowIso(), acc.id).run(); }
    catch { return json({ error: 'username_taken' }, 409); }
    return json({ ok: true, username: nick });
  }
  if (url.pathname === '/api/delete-account' && request.method === 'POST') {
    // Frees the nickname and signs the player out everywhere. The key from the bot keeps working: logging in again starts a fresh profile.
    const body = await bodyJson(request);
    const t = await verifyToken(secret, body?.token, Date.now());
    if (!t) return json({ error: 'invalid_token' }, 401);
    const acc = await env.DB.prepare('SELECT id, username, banned FROM accounts WHERE id = ?').bind(t.id).first();
    if (!acc) return json({ error: 'invalid_token' }, 401);
    if (acc.banned) return json({ error: 'account_banned' }, 403);
    await env.DB.prepare('UPDATE accounts SET username = NULL, updated_at = ? WHERE id = ?').bind(nowIso(), acc.id).run();
    await kickAccount(env, acc.id, 'session_expired');
    return json({ ok: true });
  }
  return json({ error: 'not_found' }, 404);
}

// =================================================================================================
// Cloudflare wrappers (thin: sockets <-> cores)
// =================================================================================================
function safeSend(ws, raw) { try { ws.send(raw); } catch { /* socket already closed */ } }
function pubAtt(p) { return { id: p.id, acc: p.acc, nick: p.nick, s: p.s, h: p.h, strikes: p.strikes, pStart: p.pStart }; }
function identityFrom(request) {
  const acc = request.headers.get('X-NJ-Acc'), nick = request.headers.get('X-NJ-Nick');
  if (!acc || !nick || !/^[A-Za-z0-9-]{8,64}$/.test(acc) || !C.NICK_RE.test(nick)) return null;
  return { acc, nick };
}
// Accept the socket, tell the client why, and close it — so the game can show a proper message.
function rejectSocket(code) {
  const pair = new WebSocketPair();
  const [client, server] = Object.values(pair);
  server.accept();
  server.send(JSON.stringify({ t: 'err', code }));
  server.close(1008, code);
  return new Response(null, { status: 101, webSocket: client });
}
function rejectAccepted(server, client, code) {
  safeSend(server, JSON.stringify({ t: 'err', code }));
  try { server.close(1008, code); } catch { /* already closed */ }
  return new Response(null, { status: 101, webSocket: client });
}

export class Room {
  constructor(ctx, env) {
    this.ctx = ctx; this.env = env;
    this.core = null;
    this.wsById = new Map(); this.idByWs = new Map();
    this.timer = null; this.reportTimer = null; this.lastPhase = null; this.alarmAt = 0;
    this.lastAuthCheck = 0; this.lastHistLen = 0;
    ctx.blockConcurrencyWhile(async () => {
      const meta = await ctx.storage.get('meta');
      if (meta) this.restore(meta);
    });
  }
  makeCore(cfg) {
    const core = new RoomCore(cfg);
    core.onReset = (p) => this.saveProgress(p);
    core.kick = (p, code) => {
      const ws = this.wsById.get(p.id);
      if (ws) { safeSend(ws, JSON.stringify({ t: 'err', code })); try { ws.close(1008, code); } catch { /* closed */ } }
      this.onLeave(p.id);
    };
    return core;
  }
  restore(meta) {
    const core = this.core = this.makeCore(meta.cfg);
    Object.assign(core, { phase: meta.phase, seed: meta.seed, runNo: meta.runNo, runStart: meta.runStart, winEnd: meta.winEnd, winner: meta.winner, modIdx: meta.modIdx });
    core.history = meta.history || [];
    for (const ws of this.ctx.getWebSockets()) {
      const a = ws.deserializeAttachment();
      if (!a) continue;
      const p = { ...a, sendRaw: (s) => safeSend(ws, s) };
      core.join(p, Date.now(), true);
      this.wsById.set(p.id, ws); this.idByWs.set(ws, p.id);
    }
    this.lastPhase = core.phase;
    this.ensureTimers();
  }
  persist() {
    const c = this.core;
    if (!c) return Promise.resolve();
    return this.ctx.storage.put('meta', {
      cfg: c.cfg(), phase: c.phase, seed: c.seed, runNo: c.runNo, runStart: c.runStart, winEnd: c.winEnd, winner: c.winner, modIdx: c.modIdx, history: c.history,
    });
  }
  async fetch(request) {
    const url = new URL(request.url);
    if (url.pathname === '/internal/init' && request.method === 'POST') {
      const cfg = await request.json();
      if (!this.core) { this.core = this.makeCore(cfg); await this.persist(); }
      return new Response('ok');
    }
    if (url.pathname === '/internal/kick' && request.method === 'POST') {
      const b = await request.json();
      if (this.core) this.core.kickAccount(b.acc, b.code);
      return new Response('ok');
    }
    if (request.headers.get('Upgrade') !== 'websocket') return new Response('expected websocket', { status: 426 });
    if (!this.core) return rejectSocket('no_such_room');
    const who = identityFrom(request);
    if (!who) return rejectSocket('bad_identity');
    const id = randomId();
    const pair = new WebSocketPair();
    const [client, server] = Object.values(pair);
    const p = { id, acc: who.acc, nick: who.nick, sendRaw: (s) => safeSend(server, s) };
    this.ctx.acceptWebSocket(server);                // must be accepted before anything is sent to it
    const res = this.core.join(p, Date.now(), false);
    if (res.err) return rejectAccepted(server, client, res.err);
    server.serializeAttachment(pubAtt(p));
    this.wsById.set(id, server); this.idByWs.set(server, id);
    await this.restoreProgress(p);
    this.after();
    return new Response(null, { status: 101, webSocket: client });
  }
  webSocketMessage(ws, data) {
    try {
      if (typeof data !== 'string' || data.length > C.MAX_MSG_BYTES) return;
      const id = this.idByWs.get(ws);
      if (!id || !this.core) return;
      let msg;
      try { msg = JSON.parse(data); } catch { return; }
      this.core.handle(id, msg, Date.now());
      this.after();
    } catch (e) { console.error('room message failed:', e && e.stack || e); }
  }
  webSocketClose(ws) { const id = this.idByWs.get(ws); if (id) this.onLeave(id); try { ws.close(); } catch { /* closed */ } }
  webSocketError(ws) { this.webSocketClose(ws); }
  onLeave(id) {
    const ws = this.wsById.get(id);
    this.wsById.delete(id); if (ws) this.idByWs.delete(ws);
    const leaving = this.core && this.core.players.get(id);
    if (leaving) this.saveProgress(leaving);          // the last point is kept for a reconnect
    if (this.core) this.core.leave(id, Date.now());
    this.after(true);
  }
  flushAttachments() {
    for (const p of this.core.players.values()) {
      if (!p.attDirty) continue;
      p.attDirty = false;
      const ws = this.wsById.get(p.id);
      if (ws) { try { ws.serializeAttachment(pubAtt(p)); } catch { /* closed */ } }
    }
  }
  ensureTimers() {
    const c = this.core;
    if (!c) return;
    const need = c.players.size > 0;
    if (need && !this.timer) this.timer = setInterval(() => this.onTick(), C.TICK_MS);
    if (!need && this.timer) { clearInterval(this.timer); this.timer = null; }
    const dl = c.deadline();
    if (dl && dl !== this.alarmAt) { this.alarmAt = dl; this.ctx.storage.setAlarm(dl).catch(() => {}); }
  }
  onTick() {
    this.core.tick(Date.now());
    this.flushAttachments();
    this.checkAccounts();
    this.flushProgress();
    this.after();
  }
  progressRow(p) {
    const pos = p.pos || [0, 0, 0, 0, 0];
    return [p.acc, this.core.id, this.core.runNo, pos[0], pos[1], pos[2], pos[3], p.h || 0, p.s || 0, Math.max(0, Date.now() - (p.pStart || Date.now())), nowIso()];
  }
  saveProgress(p) { if (this.env.DB && this.core) dbRun(this.env, SAVE_PROGRESS_SQL, this.progressRow(p)); }
  // Saves each changed player at most every 3 s (D1 writes are not free).
  flushProgress() {
    if (!this.env.DB || !this.core) return;
    const now = Date.now();
    for (const p of this.core.players.values()) {
      if (p.progDirty && now - (p.progAt || 0) >= 3000) { p.progDirty = false; p.progAt = now; this.saveProgress(p); }
    }
  }
  async restoreProgress(p) {
    if (!this.env.DB || !this.core || this.core.phase !== 'play') return;
    try {
      const row = await this.env.DB.prepare('SELECT run_no, x, y, vx, vy, h, s, elapsed_ms FROM progress WHERE account_id = ? AND room_id = ?').bind(p.acc, this.core.id).first();
      if (row && row.run_no === this.core.runNo && (row.h > 0 || row.s > 0)) this.core.applyProgress(p, row, Date.now());
    } catch (e) { console.error('progress restore failed:', e && e.message); }
  }
  // Safety net: banned / deleted accounts are disconnected even if the instant kick was missed.
  async checkAccounts() {
    const now = Date.now();
    if (now - this.lastAuthCheck < C.AUTH_CHECK_MS || !this.env.DB || !this.core || !this.core.players.size) return;
    this.lastAuthCheck = now;
    try {
      for (const acc of await revokedAccounts(this.env.DB, [...new Set([...this.core.players.values()].map((p) => p.acc))])) this.core.kickAccount(acc, 'session_expired');
    } catch { /* the next check will retry */ }
  }
  async alarm() {
    if (!this.core) return;
    this.core.tick(Date.now());
    this.after();
  }
  after(immediate) {
    this.ensureTimers();
    this.flushAttachments();
    const hl = this.core.history.length;
    if (this.core.phase !== this.lastPhase || immediate || hl !== this.lastHistLen) { this.lastPhase = this.core.phase; this.lastHistLen = hl; this.persist(); }
    this.report(immediate);
  }
  report(immediate) {
    const send_ = async () => {
      this.reportTimer = null;
      if (!this.core || !this.env.LOBBY) return;
      try {
        const lobby = this.env.LOBBY.get(this.env.LOBBY.idFromName('main'));
        await lobby.fetch('https://lobby/internal/room', { method: 'POST', body: JSON.stringify(this.core.summary(Date.now())) });
      } catch { /* the lobby will catch up on the next update */ }
    };
    if (immediate) { clearTimeout(this.reportTimer); send_(); return; }
    if (!this.reportTimer) this.reportTimer = setTimeout(send_, 1000);
  }
}

export class Lobby {
  constructor(ctx, env) {
    this.ctx = ctx; this.env = env;
    this.core = new LobbyCore();
    this.core.kick = (p, code) => {
      const ws = this.wsById.get(p.id);
      if (ws) { safeSend(ws, JSON.stringify({ t: 'err', code })); try { ws.close(1008, code); } catch { /* closed */ } }
      this.core.leave(p.id); this.wsById.delete(p.id); if (ws) this.idByWs.delete(ws);
    };
    this.wsById = new Map(); this.idByWs = new Map();
    this.timer = null; this.lastAuthCheck = 0; this.lastRoomsSnapshot = null;
    ctx.blockConcurrencyWhile(async () => {
      const rooms = await ctx.storage.get('rooms');
      if (rooms) for (const r of rooms) this.core.rooms.set(r.id, r);
      if (this.env.DB) {
        try {
          const { results } = await this.env.DB.prepare('SELECT id, name, cap, priv, created_at FROM rooms WHERE closed = 0 ORDER BY created_at DESC LIMIT 100').all();
          for (const r of results || []) if (!this.core.rooms.has(r.id)) this.core.rooms.set(r.id, { id: r.id, name: r.name || '', cap: r.cap, priv: !!r.priv, players: 0, mod: null, top: 0, created: Date.parse(r.created_at) || 0, updated: Date.now() });
        } catch (e) { console.error('room registry load failed:', e && e.message); }
      }
      for (const ws of ctx.getWebSockets()) {
        const a = ws.deserializeAttachment();
        if (!a) continue;
        const p = { id: a.id, acc: a.acc, nick: a.nick, sendRaw: (s) => safeSend(ws, s) };
        this.core.join(p, Date.now(), true);
        this.wsById.set(p.id, ws); this.idByWs.set(ws, p.id);
      }
      this.ensureTimer();
    });
  }
  ensureTimer() {
    const need = this.core.players.size > 0 || this.core.rooms.size > 0;
    if (need && !this.timer) this.timer = setInterval(() => this.onTick(), 1000);
    if (!need && this.timer) { clearInterval(this.timer); this.timer = null; }
  }
  onTick() {
    this.core.tick(Date.now());
    const snapshot = JSON.stringify([...this.core.rooms.values()]);
    if (snapshot !== this.lastRoomsSnapshot) { this.lastRoomsSnapshot = snapshot; this.ctx.storage.put('rooms', JSON.parse(snapshot)).catch(() => {}); }
    for (const id of this.core.removed.splice(0)) if (this.env.DB) dbRun(this.env, 'UPDATE rooms SET closed = 1, updated_at = ? WHERE id = ?', [nowIso(), id]);
    this.checkAccounts();
    this.ensureTimer();
  }
  async checkAccounts() {
    const now = Date.now();
    if (now - this.lastAuthCheck < C.AUTH_CHECK_MS * 2 || !this.env.DB || !this.core.players.size) return;
    this.lastAuthCheck = now;
    try {
      for (const acc of await revokedAccounts(this.env.DB, [...new Set([...this.core.players.values()].map((p) => p.acc))])) this.core.kickAccount(acc, 'session_expired');
    } catch { /* the next check will retry */ }
  }
  async fetch(request) {
    const url = new URL(request.url);
    if (url.pathname === '/internal/room' && request.method === 'POST') {
      this.core.roomUpdate(await request.json(), Date.now());
      this.ensureTimer();
      return new Response('ok');
    }
    if (url.pathname === '/internal/kick' && request.method === 'POST') {
      const b = await request.json();
      this.core.kickAccount(b.acc, b.code);
      // ... and in every room the lobby knows about
      await Promise.all([...this.core.rooms.keys()].map((id) =>
        this.env.ROOM.get(this.env.ROOM.idFromName(id)).fetch('https://room/internal/kick', { method: 'POST', body: JSON.stringify(b) }).catch(() => {})));
      return new Response('ok');
    }
    if (request.headers.get('Upgrade') !== 'websocket') return new Response('expected websocket', { status: 426 });
    const who = identityFrom(request);
    if (!who) return rejectSocket('bad_identity');
    const id = randomId();
    const pair = new WebSocketPair();
    const [client, server] = Object.values(pair);
    const p = { id, acc: who.acc, nick: who.nick, sendRaw: (s) => safeSend(server, s) };
    this.ctx.acceptWebSocket(server);
    this.wsById.set(id, server); this.idByWs.set(server, id);
    const res = this.core.join(p, Date.now(), false);
    if (res.err) return rejectAccepted(server, client, res.err);
    server.serializeAttachment({ id, acc: p.acc, nick: p.nick });
    this.ensureTimer();
    return new Response(null, { status: 101, webSocket: client });
  }
  async webSocketMessage(ws, data) {
    try { await this.handleMessage(ws, data); }
    catch (e) { console.error('lobby message failed:', e && e.stack || e); }
  }
  async handleMessage(ws, data) {
    if (typeof data !== 'string' || data.length > C.MAX_MSG_BYTES) return;
    const id = this.idByWs.get(ws);
    if (!id) return;
    let msg;
    try { msg = JSON.parse(data); } catch { return; }
    const act = this.core.handle(id, msg, Date.now());
    if (act && act.action === 'create') {
      const p = this.core.players.get(act.playerId);
      try {
        const room = this.env.ROOM.get(this.env.ROOM.idFromName(act.room.id));
        const cfg = { ...act.room, created: Date.now() };
        const res = await room.fetch('https://room/internal/init', { method: 'POST', body: JSON.stringify(cfg) });
        if (!res || !res.ok) throw new Error('room init answered ' + (res && res.status));
        this.core.registerRoom(cfg, Date.now());
        if (this.env.DB) dbRun(this.env, SAVE_ROOM_SQL, [cfg.id, cfg.name || '', cfg.cap, cfg.priv ? 1 : 0, nowIso(), nowIso()]);
        if (p) send(p, { t: 'go', room: act.room.id });
      } catch (e) {
        console.error('room create failed:', e && e.message);
        if (p) send(p, { t: 'err', code: 'create_failed', why: String((e && e.message) || e).slice(0, 160) });
      }
    }
  }
  webSocketClose(ws) {
    const id = this.idByWs.get(ws);
    if (id) { this.core.leave(id); this.wsById.delete(id); this.idByWs.delete(ws); }
    try { ws.close(); } catch { /* closed */ }
    this.ensureTimer();
  }
  webSocketError(ws) { this.webSocketClose(ws); }
}

// =================================================================================================
// Entry point
// =================================================================================================
async function authSocket(request, env, url) {
  const secret = sessionSecret(env);
  if (!secret) return { err: 'server_misconfigured' };
  const t = await verifyToken(secret, url.searchParams.get('token'), Date.now());
  if (!t) return { err: 'bad_token' };
  const acc = await env.DB.prepare('SELECT id, username, banned FROM accounts WHERE id = ?').bind(t.id).first();
  if (!acc || !acc.username) return { err: 'bad_token' };
  if (acc.banned) return { err: 'banned' };
  return { acc };
}
function withIdentity(request, acc) {
  const headers = new Headers(request.headers);
  headers.delete('X-NJ-Acc'); headers.delete('X-NJ-Nick');
  headers.set('X-NJ-Acc', acc.id); headers.set('X-NJ-Nick', acc.username);
  return new Request(request, { headers });
}
export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    if (request.method === 'OPTIONS') return new Response(null, { status: 204, headers: JSON_HEADERS });
    try {
      if (url.pathname === '/health') return json({ ok: true, service: 'NeuroJump Online' });
      if (request.method === 'GET' && SITE_PAGES[url.pathname]) return htmlResp(SITE_PAGES[url.pathname]());
      if (url.pathname === '/api/register' && request.method === 'POST') return await handleRegister(request, env);
      if (url.pathname === '/status') return json(await statusReport(env));
      if (url.pathname === '/telegram/webhook' && request.method === 'POST') return await handleTelegramUpdate(request, env);
      const min = intVar(env.MIN_APP_VERSION, DEFAULT_MIN_APP_VERSION);
      if (url.pathname === '/api/version') return json({ ok: true, min_version: min, update_url: env.UPDATE_URL || null, notes: env.UPDATE_NOTES || null });
      const v = intVar(url.searchParams.get('v'), 0);
      if (v < min) return json({ error: 'update_required', min_version: min, update_url: env.UPDATE_URL || null, notes: env.UPDATE_NOTES || null }, 426);
      if (url.pathname.startsWith('/api/')) return await handleApi(request, env, url);
      const isLobby = url.pathname === '/ws/lobby';
      const m = url.pathname.match(/^\/ws\/room\/([A-Z2-9]{4})$/);
      if (isLobby || m) {
        if (request.headers.get('Upgrade') !== 'websocket') return new Response('expected websocket', { status: 426 });
        const a = await authSocket(request, env, url);
        if (a.err) return rejectSocket(a.err);
        const req2 = withIdentity(request, a.acc);
        return isLobby
          ? env.LOBBY.get(env.LOBBY.idFromName('main')).fetch(req2)
          : env.ROOM.get(env.ROOM.idFromName(m[1])).fetch(req2);
      }
      return new Response('not found', { status: 404 });
    } catch (err) {
      console.error('request failed:', err && err.stack || err);
      return json({ error: 'internal_error' }, 500);
    }
  },
};
