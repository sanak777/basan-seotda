const express = require("express");
const http = require("http");
const path = require("path");
const { Server } = require("socket.io");

const app = express();
const server = http.createServer(app);
const io = new Server(server, { transports: ["websocket", "polling"] });
app.get("/", (_req, res) => res.sendFile(path.join(__dirname, "index.html")));
app.get("/bgm.mp3", (_req, res) => res.sendFile(path.join(__dirname, "bgm.mp3")));

const BUY_IN = 3_000_000;
const ANTE = 10_000;
const ADMIN_PASSWORD = "8959";
const BETTING_SECONDS = 15;
const MAX_MISSED_BETS = 10;
const DISCONNECT_ACTION_GRACE = 20_000;
const LOBBY_CLEANUP_GRACE = 5 * 60_000;
const seats = Array(10).fill(null);
const admins = new Set();
const connections = new Map();
const cleanupTimers = new Map();
const actionTimers = new Map();
let deck = [];
let pot = 0;
let currentBet = 0;
let round = 0;
let phase = "idle";
let message = "참가자를 기다립니다";
let busy = false;
let pending = new Set();
let resultText = "";
let bettingDeadline = 0;
let bettingTimer = null;
let nextRoundTimer = null;
let dealerSeat = -1;
let turnSeat = -1;
let raceRound = 0;
let gameRunning = false;

const wait = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
const cleanName = (value) => String(value || "").trim().slice(0, 8);
const cleanToken = (value) => String(value || "").replace(/[^a-zA-Z0-9_-]/g, "").slice(0, 80);
const tokenOf = (socket) => socket.data.playerToken;
const isConnected = (token) => (connections.get(token)?.size || 0) > 0;
const activeSeats = () => seats.map((p, i) => p && !p.eliminated && !p.fold ? i : -1).filter((i) => i >= 0);
const tournamentSeats = () => seats.map((p, i) => p && !p.eliminated && p.cash > 0 ? i : -1).filter((i) => i >= 0);

function clearBettingTimer() {
  if (bettingTimer) clearTimeout(bettingTimer);
  bettingTimer = null;
  bettingDeadline = 0;
}

function clearNextRoundTimer() {
  if (nextRoundTimer) clearTimeout(nextRoundTimer);
  nextRoundTimer = null;
}

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
  // Keep every normal hand in a non-overlapping score band.  In particular,
  // even 1땡 must always beat 알리/끗, so 4땡 can never lose to 8끗.
  let value = 0;
  if (h === "38광땡") value = 1300;
  else if (/광땡/.test(h)) value = 1100;
  else if (h === "장땡") value = 1000;
  else if (/^[1-9]땡$/.test(h)) value = 900 + Number.parseInt(h, 10);
  else value = ({ 알리: 800, 독사: 790, 구삥: 780, 장삥: 770, 장사: 760, 세륙: 750, 갑오: 709, 망통: 700 })[h] ?? 700 + Number.parseInt(h, 10);
  const hasGwang = field.some((p) => /^(13|18)광땡$/.test(hand(p.cards)));
  const hasDdang = field.some((p) => /^([1-9])땡$/.test(hand(p.cards)));
  if (player.cards.some((c) => c.sp === "bird4") && player.cards.some((c) => c.sp === "boar7") && hasGwang) value = 1200;
  if (player.cards.some((c) => c.sp === "g3") && player.cards.some((c) => c.sp === "boar7") && hasDdang) value = 1050;
  return value;
}

function isFourNine(player) {
  const months = player.cards.map((card) => card.m).sort((a, b) => a - b);
  return months[0] === 4 && months[1] === 9;
}

function isMungFourNine(player) {
  return isFourNine(player)
    && player.cards.some((card) => card.sp === "bird4")
    && player.cards.some((card) => card.sp === "cup9");
}

function fourNineRematchPlayer(field) {
  const candidates = field.filter(isFourNine);
  if (!candidates.length || field.length < 2) return null;
  return candidates.find((candidate) => {
    const opponents = field.filter((player) => player !== candidate);
    const opponentBest = Math.max(...opponents.map((player) => score(player, field)));
    // 일반 구사: 알리 이하. 멍텅구리 구사: 1땡~9땡까지(장땡 제외).
    return isMungFourNine(candidate) ? opponentBest <= 909 : opponentBest <= 800;
  }) || null;
}

function publicState(socketId) {
  const viewer = io.sockets.sockets.get(socketId);
  const viewerToken = viewer ? tokenOf(viewer) : "";
  const revealAll = phase === "reveal" || phase === "result";
  return {
    round, phase, message, resultText, pot, currentBet, busy,
    dealerSeat, turnSeat, raceRound, gameRunning,
    bettingDeadline, bettingSeconds: BETTING_SECONDS,
    adminActive: admins.size > 0, isAdmin: admins.has(socketId),
    youSeat: seats.findIndex((p) => p?.playerToken === viewerToken),
    canAct: turnSeat >= 0 && seats[turnSeat]?.playerToken === viewerToken && pending.has(viewerToken),
    seats: seats.map((p) => p && ({
      name: p.name, character: p.character, cash: p.cash, bet: p.bet,
      fold: p.fold, eliminated: p.eliminated, missedBets: p.missedBets,
      connected: isConnected(p.playerToken),
      cards: revealAll || p.playerToken === viewerToken ? p.cards : p.cards.map(() => null),
      hand: p.cards.length === 2 && (revealAll || p.playerToken === viewerToken)
        ? (isFourNine(p) ? "사구·구사 재경기" : hand(p.cards))
        : ""
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
  return value;
}

async function dealOneEach() {
  for (const index of activeSeats()) {
    seats[index].cards.push(deck.pop());
    broadcast();
    await wait(430);
  }
}

function nextPendingSeat(afterSeat) {
  for (let step = 1; step <= seats.length; step++) {
    const index = (afterSeat + step + seats.length) % seats.length;
    const player = seats[index];
    if (player && !player.fold && !player.eliminated && pending.has(player.playerToken)) return index;
  }
  return -1;
}

function turnMessage() {
  const player = seats[turnSeat];
  if (!player) return "베팅 진행 중";
  const stage = phase === "bet1" ? "1차 베팅" : "최종 베팅";
  return `${stage} · 레이스 ${raceRound} · ${turnSeat + 1}번 ${player.name} 차례`;
}

function startTurnTimer() {
  clearBettingTimer();
  if (turnSeat < 0 || !seats[turnSeat]) return;
  message = turnMessage();
  bettingDeadline = Date.now() + BETTING_SECONDS * 1000;
  const timedSeat = turnSeat;
  bettingTimer = setTimeout(() => {
    bettingTimer = null;
    bettingDeadline = 0;
    if (turnSeat !== timedSeat || !["bet1", "bet2"].includes(phase)) return;
    const player = seats[timedSeat];
    if (player && !player.fold) {
      player.fold = true;
      player.missedBets = (player.missedBets || 0) + 1;
      if (player.missedBets >= MAX_MISSED_BETS) {
        player.eliminated = true;
        player.cash = 0;
      }
      pending.delete(player.playerToken);
      io.emit("bet-action", { seat: timedSeat, type: "fold", amount: 0, automatic: true });
    }
    message = `${timedSeat + 1}번 · 시간 초과 자동 다이`;
    broadcast();
    continueRace(timedSeat);
  }, BETTING_SECONDS * 1000);
  broadcast();
}

function continueRace(afterSeat) {
  clearBettingTimer();
  if (activeSeats().length <= 1) return settle();
  turnSeat = nextPendingSeat(afterSeat);
  if (turnSeat < 0) {
    pending.clear();
    return advance();
  }
  startTurnTimer();
}

function beginBetting(nextPhase) {
  clearBettingTimer();
  phase = nextPhase;
  busy = false;
  raceRound = 1;
  pending = new Set(activeSeats().filter((i) => seats[i].cash > 0).map((i) => seats[i].playerToken));
  turnSeat = nextPendingSeat(dealerSeat);
  if (turnSeat < 0) return settle();
  startTurnTimer();
}

function announceLastSurvivor() {
  const remaining = tournamentSeats();
  const joined = seats.filter(Boolean).length;
  if (joined < 2 || remaining.length !== 1) return false;
  clearBettingTimer();
  pending.clear();
  const winner = seats[remaining[0]];
  gameRunning = false;
  clearNextRoundTimer();
  phase = "result";
  busy = false;
  resultText = `최후의 1인 · ${winner.name} 우승`;
  message = resultText;
  broadcast();
  return true;
}

function chooseNextDealer() {
  for (let step = 1; step <= seats.length; step++) {
    const index = (dealerSeat + step + seats.length) % seats.length;
    const player = seats[index];
    if (player && !player.eliminated && player.cash > 0 && isConnected(player.playerToken)) return index;
  }
  return -1;
}

async function startRound(options = {}) {
  if (busy || !gameRunning || !seats.some(Boolean) || announceLastSurvivor()) return;
  clearNextRoundTimer();
  clearBettingTimer();
  busy = true;
  round += 1;
  phase = "deal1";
  resultText = "";
  message = "첫 패를 돌립니다";
  if (!options.keepPot) pot = 0;
  currentBet = ANTE;
  deck = freshDeck();
  dealerSeat = chooseNextDealer();
  const rematchTokens = options.rematchTokens || null;
  for (const p of seats) if (p) {
    // Keep a temporarily disconnected player's seat, but never let an offline
    // seat block a newly started betting round.
    const offline = !isConnected(p.playerToken);
    if (offline && !p.eliminated && p.cash > 0) {
      p.missedBets = (p.missedBets || 0) + 1;
      if (p.missedBets >= MAX_MISSED_BETS) {
        p.eliminated = true;
        p.cash = 0;
      }
    }
    p.cards = []; p.bet = 0;
    p.fold = p.eliminated || p.cash <= 0 || offline || (rematchTokens && !rematchTokens.has(p.playerToken));
    if (!p.fold) invest(p, ANTE);
  }
  broadcast();
  await dealOneEach();
  beginBetting("bet1");
}

async function advance() {
  clearBettingTimer();
  turnSeat = -1;
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
  clearBettingTimer();
  turnSeat = -1;
  // A timeout/disconnect can arrive at nearly the same time as the final bet.
  // Never settle the same hand twice or create competing next-round timers.
  if (busy && (phase === "reveal" || phase === "result")) return;
  busy = true;
  phase = "reveal";
  message = "패를 공개합니다";
  broadcast();
  await wait(900);
  const live = activeSeats().map((i) => seats[i]);
  if (!live.length) {
    resultText = "승자 없음";
  } else {
    const rematchPlayer = fourNineRematchPlayer(live);
    if (rematchPlayer && live.length > 1) {
      const rematchTokens = new Set(live.map((p) => p.playerToken));
      phase = "result";
      busy = false;
      resultText = `${isMungFourNine(rematchPlayer) ? "멍텅구리 구사" : "사구·구사"} · 판돈 ₩${pot.toLocaleString("ko-KR")} 재경기`;
      message = resultText;
      broadcast();
      if (gameRunning) nextRoundTimer = setTimeout(() => startRound({ keepPot: true, rematchTokens }), 3500);
      return;
    }
    const best = Math.max(...live.map((p) => score(p, live)));
    const winners = live.filter((p) => score(p, live) === best);
    const share = Math.floor(pot / winners.length);
    winners.forEach((p) => { p.cash += share; });
    resultText = winners
      .map((p) => `${p.name} · ${hand(p.cards)} · ₩${share.toLocaleString("ko-KR")}`)
      .join("\n");
  }
  pot = 0;
  for (const player of seats) {
    if (player && !player.eliminated && player.cash <= 0) player.eliminated = true;
  }
  phase = "result";
  message = resultText;
  busy = false;
  broadcast();
  if (announceLastSurvivor()) return;
  if (gameRunning) nextRoundTimer = setTimeout(() => startRound(), 3500);
}

io.on("connection", (socket) => {
  let playerToken = cleanToken(socket.handshake.auth?.playerToken);
  if (!playerToken) playerToken = `guest_${socket.id.replace(/[^a-zA-Z0-9]/g, "")}`;
  socket.data.playerToken = playerToken;
  if (!connections.has(playerToken)) connections.set(playerToken, new Set());
  connections.get(playerToken).add(socket.id);
  if (cleanupTimers.has(playerToken)) {
    clearTimeout(cleanupTimers.get(playerToken));
    cleanupTimers.delete(playerToken);
  }
  if (actionTimers.has(playerToken)) {
    clearTimeout(actionTimers.get(playerToken));
    actionTimers.delete(playerToken);
  }
  socket.emit("state", publicState(socket.id));
  broadcast();

  socket.on("sit", (data, ack = () => {}) => {
    const name = cleanName(data?.name);
    const seat = Number(data?.seat);
    const character = Number(data?.character);
    if (!name || !Number.isInteger(seat) || seat < 0 || seat > 9 || !Number.isInteger(character) || character < 0 || character > 5) return ack({ ok: false, error: "입력 정보를 확인해주세요" });
    const old = seats.findIndex((p) => p?.playerToken === playerToken);
    if (old >= 0) {
      ack({ ok: true, restored: true, seat: old });
      return broadcast();
    }
    if (gameRunning) return ack({ ok: false, error: "게임 진행 중에는 새로 참여할 수 없습니다" });
    if (seats[seat]) return ack({ ok: false, error: "이미 사용 중인 자리입니다" });
    seats[seat] = { playerToken, name, character, cash: BUY_IN, cards: [], bet: 0, fold: false, eliminated: false, missedBets: 0 };
    ack({ ok: true });
    broadcast();
  });

  socket.on("bet", (type, ack = () => {}) => {
    const index = seats.findIndex((p) => p?.playerToken === playerToken);
    const p = seats[index];
    if (!p || index !== turnSeat || !["bet1", "bet2"].includes(phase) || !pending.has(playerToken) || p.fold) return ack({ ok: false, error: "현재 베팅 차례가 아닙니다" });
    const need = Math.max(0, currentBet - p.bet);
    const beforeCurrentBet = currentBet;
    let amount = 0;
    if (type === "fold") p.fold = true;
    else if (type === "check") {
      if (need > 0) return ack({ ok: false, error: "받아야 할 금액이 있어 체크할 수 없습니다" });
    }
    else if (type === "call") amount = invest(p, need);
    else if (type === "ddang") amount = invest(p, need + Math.max(ANTE, currentBet));
    else if (type === "half") amount = invest(p, need + Math.max(ANTE, pot / 2));
    else return ack({ ok: false, error: "알 수 없는 베팅입니다" });
    pending.delete(playerToken);
    const raised = currentBet > beforeCurrentBet;
    if (raised) {
      raceRound += 1;
      pending = new Set(activeSeats()
        .filter((seatIndex) => seatIndex !== index && seats[seatIndex].cash > 0)
        .map((seatIndex) => seats[seatIndex].playerToken));
    }
    io.emit("bet-action", { seat: index, type, amount, automatic: false });
    ack({ ok: true, amount, raised });
    broadcast();
    continueRace(index);
  });

  socket.on("admin-login", (password, ack = () => {}) => {
    if (String(password) !== ADMIN_PASSWORD) return ack({ ok: false });
    admins.add(socket.id); ack({ ok: true }); broadcast();
  });
  socket.on("admin-start", () => {
    if (!admins.has(socket.id)) return;
    gameRunning = true;
    if (["idle", "result"].includes(phase)) startRound();
  });
  socket.on("admin-restart", () => {
    if (!admins.has(socket.id)) return;
    for (const timer of actionTimers.values()) clearTimeout(timer);
    actionTimers.clear();
    clearBettingTimer();
    clearNextRoundTimer();
    gameRunning = false; turnSeat = -1; dealerSeat = -1; raceRound = 0;
    busy = false; phase = "idle"; pending.clear(); resultText = ""; message = "게임이 재시작되었습니다";
    for (const p of seats) if (p) { p.cash = BUY_IN; p.cards = []; p.bet = 0; p.fold = false; p.eliminated = false; p.missedBets = 0; }
    pot = 0; currentBet = 0; round = 0; broadcast();
  });
  socket.on("admin-explode", () => {
    if (!admins.has(socket.id)) return;
    for (const timer of cleanupTimers.values()) clearTimeout(timer);
    for (const timer of actionTimers.values()) clearTimeout(timer);
    cleanupTimers.clear(); actionTimers.clear();
    clearBettingTimer();
    clearNextRoundTimer();
    gameRunning = false; turnSeat = -1; dealerSeat = -1; raceRound = 0;
    for (let i = 0; i < seats.length; i++) seats[i] = null;
    busy = false; phase = "idle"; pending.clear(); resultText = ""; message = "방이 종료되었습니다";
    pot = 0; currentBet = 0; round = 0; broadcast(); io.emit("room-exploded");
  });

  socket.on("admin-kick", (seatValue, ack = () => {}) => {
    if (!admins.has(socket.id)) return ack({ ok: false, error: "관리자 권한이 없습니다" });
    const seat = Number(seatValue);
    if (!Number.isInteger(seat) || seat < 0 || seat >= seats.length || !seats[seat]) {
      return ack({ ok: false, error: "강퇴할 참가자가 없습니다" });
    }
    const kicked = seats[seat];
    const wasTurn = turnSeat === seat;
    pending.delete(kicked.playerToken);
    if (actionTimers.has(kicked.playerToken)) {
      clearTimeout(actionTimers.get(kicked.playerToken));
      actionTimers.delete(kicked.playerToken);
    }
    if (cleanupTimers.has(kicked.playerToken)) {
      clearTimeout(cleanupTimers.get(kicked.playerToken));
      cleanupTimers.delete(kicked.playerToken);
    }
    for (const kickedSocketId of connections.get(kicked.playerToken) || []) {
      io.to(kickedSocketId).emit("kicked", { message: "관리자에 의해 강퇴되었습니다" });
    }
    seats[seat] = null;
    ack({ ok: true, name: kicked.name });
    broadcast();
    if (["bet1", "bet2"].includes(phase)) {
      if (activeSeats().length <= 1) return settle();
      if (wasTurn) return continueRace(seat);
    }
  });

  socket.on("disconnect", () => {
    admins.delete(socket.id);
    const set = connections.get(playerToken);
    if (set) {
      set.delete(socket.id);
      if (!set.size) connections.delete(playerToken);
    }
    if (isConnected(playerToken)) return broadcast();
    broadcast();
    if (pending.has(playerToken)) {
      const actionTimer = setTimeout(() => {
        actionTimers.delete(playerToken);
        if (!isConnected(playerToken) && pending.delete(playerToken)) {
          const index = seats.findIndex((p) => p?.playerToken === playerToken);
          if (index >= 0 && seats[index]) {
            seats[index].fold = true;
            seats[index].missedBets = (seats[index].missedBets || 0) + 1;
            if (seats[index].missedBets >= MAX_MISSED_BETS) {
              seats[index].eliminated = true;
              seats[index].cash = 0;
            }
          }
          broadcast();
          if (!pending.size || activeSeats().length <= 1) advance();
        }
      }, DISCONNECT_ACTION_GRACE);
      actionTimers.set(playerToken, actionTimer);
    }
    const cleanupTimer = setTimeout(() => {
      cleanupTimers.delete(playerToken);
      if (isConnected(playerToken)) return;
      if (gameRunning) return broadcast();
      const index = seats.findIndex((p) => p?.playerToken === playerToken);
      if (index >= 0) seats[index] = null;
      pending.delete(playerToken);
      broadcast();
    }, LOBBY_CLEANUP_GRACE);
    cleanupTimers.set(playerToken, cleanupTimer);
  });
});

const port = process.env.PORT || 3000;
server.listen(port, () => console.log(`Basan Seotda server listening on ${port}`));
