const express = require("express");
const http = require("http");
const path = require("path");
const { Server } = require("socket.io");

const app = express();
const server = http.createServer(app);
const io = new Server(server, { transports: ["websocket", "polling"] });
app.get("/", (_req, res) => res.sendFile(path.join(__dirname, "index.html")));

const BUY_IN = 3_000_000;
const ANTE = 10_000;
const ADMIN_PASSWORD = "8959";
const seats = Array(10).fill(null);
const admins = new Set();
let deck = [];
let pot = 0;
let currentBet = 0;
let round = 0;
let phase = "idle";
let message = "참가자를 기다립니다";
let busy = false;
let pending = new Set();
let resultText = "";

const wait = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
const cleanName = (value) => String(value || "").trim().slice(0, 8);
const activeSeats = () => seats.map((p, i) => p && !p.fold && p.cash >= 0 ? i : -1).filter((i) => i >= 0);

function freshDeck() {
  const cards = [];
  const special = {
    "1-0": { g: true, sp: "g1" }, "1-1": { sp: "ribbon1" },
    "2-0": { sp: "bird2" }, "2-1": { sp: "ribbon2" },
    "3-0": { g: true, sp: "g3" }, "3-1": { sp: "ribbon3" },
    "4-0": { sp: "bird4" }, "4-1": { sp: "ribbon4" },
    "5-0": { sp: "bridge5" }, "5-1": { sp: "ribbon5" },
    "6-0": { sp: "butterfly6" }, "6-1": { sp: "ribbon6" },
    "7-0": { sp: "boar7" }, "7-1": { sp: "ribbon7" },
    "8-0": { g: true, sp: "g8" }, "8-1": { sp: "bird8" },
    "9-0": { sp: "cup9" }, "9-1": { sp: "ribbon9" },
    "10-0": { sp: "deer10" }, "10-1": { sp: "ribbon10" }
  };
  for (let m = 1; m <= 10; m++) {
    for (let v = 0; v < 2; v++) cards.push({ m, v, ...(special[`${m}-${v}`] || {}) });
  }
  for (let i = cards.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [cards[i], cards[j]] = [cards[j], cards[i]];
  }
  return cards;
}

function hand(cards) {
  if (!cards || cards.length < 2) return "";
  const [a, b] = cards;
  const ms = [a.m, b.m].sort((x, y) => x - y);
  const key = ms.join("");
  if (a.g && b.g) {
    if (key === "38") return "38광땡";
    if (key === "13" || key === "18") return `${key}광땡`;
  }
  if (a.m === b.m) return a.m === 10 ? "장땡" : `${a.m}땡`;
  const special = { 12: "알리", 14: "독사", 19: "구삥", 110: "장삥", 410: "장사", 46: "세륙" };
  if (special[key]) return special[key];
  const n = (a.m + b.m) % 10;
  return n === 9 ? "갑오" : n === 0 ? "망통" : `${n}끗`;
}

function score(player, field) {
  const h = hand(player.cards);
  let value = 0;
  if (h === "38광땡") value = 1000;
  else if (/광땡/.test(h)) value = 950;
  else if (h === "장땡") value = 900;
  else if (/땡$/.test(h)) value = 800 + Number.parseInt(h, 10) * 5;
  else value = ({ 알리: 700, 독사: 690, 구삥: 680, 장삥: 670, 장사: 660, 세륙: 650, 갑오: 609, 망통: 600 })[h] ?? 600 + Number.parseInt(h, 10);
  const hasGwang = field.some((p) => /^(13|18)광땡$/.test(hand(p.cards)));
  const hasDdang = field.some((p) => /^([1-9])땡$/.test(hand(p.cards)));
  if (player.cards.some((c) => c.sp === "bird4") && player.cards.some((c) => c.sp === "boar7") && hasGwang) value = 975;
  if (player.cards.some((c) => c.sp === "g3") && player.cards.some((c) => c.sp === "boar7") && hasDdang) value = 925;
  return value;
}

function publicState(socketId) {
  const revealAll = phase === "reveal" || phase === "result";
  return {
    round, phase, message, resultText, pot, currentBet, busy,
    youSeat: seats.findIndex((p) => p?.socketId === socketId),
    canAct: pending.has(socketId),
    seats: seats.map((p) => p && ({
      name: p.name, character: p.character, cash: p.cash, bet: p.bet,
      fold: p.fold, connected: true,
      cards: revealAll || p.socketId === socketId ? p.cards : p.cards.map(() => null),
      hand: p.cards.length === 2 && (revealAll || p.socketId === socketId) ? hand(p.cards) : ""
    }))
  };
}

function broadcast() {
  for (const socket of io.sockets.sockets.values()) socket.emit("state", publicState(socket.id));
}

function invest(player, amount) {
  const value = Math.min(Math.max(0, Math.round(amount / 1000) * 1000), player.cash);
  player.cash -= value;
  player.bet += value;
  pot += value;
  currentBet = Math.max(currentBet, player.bet);
}

async function dealOneEach() {
  for (const index of activeSeats()) {
    seats[index].cards.push(deck.pop());
    broadcast();
    await wait(430);
  }
}

function beginBetting(nextPhase) {
  phase = nextPhase;
  busy = false;
  message = nextPhase === "bet1" ? "첫 패 · 1차 베팅" : "두 패 · 최종 베팅";
  pending = new Set(activeSeats().map((i) => seats[i].socketId));
  broadcast();
  if (!pending.size) settle();
}

async function startRound() {
  if (busy || !seats.some(Boolean)) return;
  busy = true;
  round += 1;
  phase = "deal1";
  resultText = "";
  message = "첫 패를 돌립니다";
  pot = 0;
  currentBet = ANTE;
  deck = freshDeck();
  for (const p of seats) if (p) {
    p.cards = []; p.bet = 0; p.fold = p.cash <= 0;
    if (!p.fold) invest(p, ANTE);
  }
  broadcast();
  await dealOneEach();
  beginBetting("bet1");
}

async function advance() {
  const live = activeSeats();
  if (live.length <= 1) return settle();
  if (phase === "bet1") {
    busy = true; phase = "deal2"; message = "두 번째 패를 돌립니다"; broadcast();
    await dealOneEach();
    beginBetting("bet2");
  } else if (phase === "bet2") {
    settle();
  }
}

async function settle() {
  if (busy && phase === "result") return;
  busy = true;
  phase = "reveal";
  message = "패를 공개합니다";
  broadcast();
  await wait(900);
  const live = activeSeats().map((i) => seats[i]);
  if (!live.length) {
    resultText = "승자 없음";
  } else {
    const best = Math.max(...live.map((p) => score(p, live)));
    const winners = live.filter((p) => score(p, live) === best);
    const share = Math.floor(pot / winners.length);
    winners.forEach((p) => { p.cash += share; });
    resultText = `${winners.map((p) => p.name).join(" · ")} · ${hand(winners[0].cards)} 승리 · ₩${share.toLocaleString("ko-KR")}`;
  }
  pot = 0;
  phase = "result";
  message = resultText;
  busy = false;
  broadcast();
}

io.on("connection", (socket) => {
  socket.emit("state", publicState(socket.id));

  socket.on("sit", (data, ack = () => {}) => {
    const name = cleanName(data?.name);
    const seat = Number(data?.seat);
    const character = Number(data?.character);
    if (!name || !Number.isInteger(seat) || seat < 0 || seat > 9 || !Number.isInteger(character) || character < 0 || character > 5) return ack({ ok: false, error: "입력 정보를 확인해주세요" });
    if (seats[seat]) return ack({ ok: false, error: "이미 사용 중인 자리입니다" });
    const old = seats.findIndex((p) => p?.socketId === socket.id);
    if (old >= 0) seats[old] = null;
    seats[seat] = { socketId: socket.id, name, character, cash: BUY_IN, cards: [], bet: 0, fold: false };
    ack({ ok: true });
    broadcast();
  });

  socket.on("bet", (type, ack = () => {}) => {
    const index = seats.findIndex((p) => p?.socketId === socket.id);
    const p = seats[index];
    if (!p || !["bet1", "bet2"].includes(phase) || !pending.has(socket.id) || p.fold) return ack({ ok: false });
    const need = Math.max(0, currentBet - p.bet);
    if (type === "fold") p.fold = true;
    else if (type === "check") { if (need > 0) invest(p, need); }
    else if (type === "call") invest(p, need);
    else if (type === "ddang") invest(p, need + Math.max(ANTE, currentBet));
    else if (type === "half") invest(p, need + Math.max(ANTE, pot / 2));
    else return ack({ ok: false });
    pending.delete(socket.id);
    ack({ ok: true });
    broadcast();
    if (!pending.size || activeSeats().length <= 1) advance();
  });

  socket.on("admin-login", (password, ack = () => {}) => {
    if (String(password) !== ADMIN_PASSWORD) return ack({ ok: false });
    admins.add(socket.id); ack({ ok: true });
  });
  socket.on("admin-start", () => { if (admins.has(socket.id)) startRound(); });
  socket.on("admin-restart", () => {
    if (!admins.has(socket.id)) return;
    busy = false; phase = "idle"; pending.clear(); resultText = ""; message = "게임이 재시작되었습니다";
    for (const p of seats) if (p) { p.cash = BUY_IN; p.cards = []; p.bet = 0; p.fold = false; }
    pot = 0; currentBet = 0; round = 0; broadcast();
  });
  socket.on("admin-explode", () => {
    if (!admins.has(socket.id)) return;
    for (let i = 0; i < seats.length; i++) seats[i] = null;
    busy = false; phase = "idle"; pending.clear(); resultText = ""; message = "방이 종료되었습니다";
    pot = 0; currentBet = 0; round = 0; broadcast(); io.emit("room-exploded");
  });

  socket.on("disconnect", () => {
    admins.delete(socket.id);
    const index = seats.findIndex((p) => p?.socketId === socket.id);
    if (index >= 0) { pending.delete(socket.id); seats[index] = null; broadcast(); if (["bet1", "bet2"].includes(phase) && !pending.size) advance(); }
  });
});

const port = process.env.PORT || 3000;
server.listen(port, () => console.log(`Basan Seotda server listening on ${port}`));
