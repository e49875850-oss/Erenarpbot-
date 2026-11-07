require('dotenv').config();
const { Bot, InlineKeyboard } = require('grammy');
const WebSocket = require('ws');
const Database = require('better-sqlite3');
const crypto = require('crypto');
const fs = require('fs');
const { createSecureClient, relayerApiKey, OrderSide } = require('@polymarket/client');
const { privateKey } = require('@polymarket/client/viem');

const BOT_TOKEN = process.env.BOT_TOKEN;
const GROUP_ID = Number(process.env.GROUP_ID);
const KALSHI_KEY_ID = process.env.KALSHI_API_KEY_ID;
const KALSHI_PRIVATE_KEY_PATH = process.env.KALSHI_PRIVATE_KEY_PATH;
const KALSHI_ENV = (process.env.KALSHI_ENV || 'prod').toLowerCase();
const POLY_PRIVATE_KEY = process.env.POLY_PRIVATE_KEY || null;
const POLYMARKET_WALLET_ADDRESS = process.env.POLYMARKET_WALLET_ADDRESS || null;
const RELAYER_API_KEY = process.env.RELAYER_API_KEY || null;
const RELAYER_API_KEY_ADDRESS = process.env.RELAYER_API_KEY_ADDRESS || null;
const POLY_CLOB_HOST = 'https://clob.polymarket.com';
const TRADING_ENABLED = !!POLY_PRIVATE_KEY;

const KALSHI_HOSTS = {
  prod: { rest: 'https://api.elections.kalshi.com/trade-api/v2', ws: 'wss://api.elections.kalshi.com/trade-api/ws/v2' },
  demo: { rest: 'https://demo-api.kalshi.co/trade-api/v2', ws: 'wss://demo-api.kalshi.co/trade-api/ws/v2' },
};
const KALSHI_REST = KALSHI_HOSTS[KALSHI_ENV].rest;
const KALSHI_WS_URL = KALSHI_HOSTS[KALSHI_ENV].ws;
const GAMMA_API = 'https://gamma-api.polymarket.com';
const POLY_MARKET_WS = 'wss://ws-subscriptions-clob.polymarket.com/ws/market';
const BINANCE_WS = 'wss://stream.binance.com:9443/stream?streams=btcusdt@trade';
const BINANCE_KLINES = 'https://api.binance.com/api/v3/klines';
const BINANCE_TICKER = 'https://api.binance.com/api/v3/ticker/price?symbol=BTCUSDT';
const KALSHI_SERIES = 'KXBTCD';

const RISK_LIMITS = {
  maxDailyLoss: parseFloat(process.env.MAX_DAILY_LOSS || '100'),
  maxPositionSize: parseFloat(process.env.MAX_POSITION_SIZE || '50'),
  maxSlippage: parseFloat(process.env.MAX_SLIPPAGE || '0.02'),
  minLiquidity: parseFloat(process.env.MIN_LIQUIDITY || '100'),
  maxSpread: parseFloat(process.env.MAX_SPREAD || '0.03'),
  polyMakerFee: 0.00,
  kalshiMakerFee: 0.005,
  kalshiTakerFee: 0.015,
  minMarketMinutes: parseFloat(process.env.MIN_MARKET_MINUTES || '5'),
  maxMarketMinutes: parseFloat(process.env.MAX_MARKET_MINUTES || '45'),
  rebalanceMaxAttempts: 3,
  rebalancePriceIncrement: 0.03,
  maxStrikeDiffPct: parseFloat(process.env.MAX_STRIKE_DIFF_PCT || '0.05'),
  maxStrikeDiffUsd: parseFloat(process.env.MAX_STRIKE_DIFF_USD || '50'),
  maxCloseTimeDiffSec: parseFloat(process.env.MAX_CLOSE_TIME_DIFF_SEC || '60'),
  maxPriceImpactPct: parseFloat(process.env.MAX_PRICE_IMPACT_PCT || '0.01'),
  minDepthMultiplier: parseFloat(process.env.MIN_DEPTH_MULTIPLIER || '5'),
  maxBookLevelsToCheck: 30,
  legTimeoutMs: parseInt(process.env.LEG_TIMEOUT_MS || '8000'),
  atomicWindowMs: parseInt(process.env.ATOMIC_WINDOW_MS || '1500'),
  maxLegTimeDiffMs: parseInt(process.env.MAX_LEG_TIME_DIFF_MS || '2000'),
  flattenOnSingleLeg: process.env.FLATTEN_ON_SINGLE_LEG !== 'false',
  requireBothBooksFreshMs: parseInt(process.env.REQUIRE_BOOKS_FRESH_MS || '3000'),
};

class RateLimiter {
  constructor(maxRequests, windowMs) { this.maxRequests = maxRequests; this.windowMs = windowMs; this.requests = []; }
  async waitForSlot() {
    const now = Date.now();
    this.requests = this.requests.filter(t => now - t < this.windowMs);
    if (this.requests.length >= this.maxRequests) {
      const oldestRequest = this.requests[0];
      const waitTime = oldestRequest + this.windowMs - now;
      if (waitTime > 0) await new Promise(r => setTimeout(r, waitTime));
    }
    this.requests.push(now);
  }
  getStatus() {
    const now = Date.now();
    this.requests = this.requests.filter(t => now - t < this.windowMs);
    return { current: this.requests.length, limit: this.maxRequests };
  }
}
const polyRateLimiter = new RateLimiter(50, 60000);
const kalshiRateLimiter = new RateLimiter(40, 60000);

class CacheManager {
  constructor() { this.cache = new Map(); this.ttls = new Map(); this.timestamps = new Map(); this.cleanupInterval = setInterval(() => this.cleanup(), 60000); }
  set(key, value, ttl = 5000) { this.cache.set(key, value); this.ttls.set(key, Date.now() + ttl); this.timestamps.set(key, Date.now()); }
  get(key) {
    const expiry = this.ttls.get(key);
    if (!expiry || Date.now() > expiry) { this.cache.delete(key); this.ttls.delete(key); this.timestamps.delete(key); return null; }
    return this.cache.get(key);
  }
  getAge(key) { const t = this.timestamps.get(key); return t ? Date.now() - t : Infinity; }
  isFresh(key, maxAgeMs) { return this.getAge(key) <= maxAgeMs && this.get(key) !== null; }
  cleanup() { const now = Date.now(); for (const [key, expiry] of this.ttls) { if (now > expiry) { this.cache.delete(key); this.ttls.delete(key); this.timestamps.delete(key); } } }
  getSize() { return this.cache.size; }
}
const cacheManager = new CacheManager();

class VolatilityTracker {
  constructor() { this.priceHistory = []; this.maxHistory = 100; }
  addPrice(price) { this.priceHistory.push({ price, timestamp: Date.now() }); if (this.priceHistory.length > this.maxHistory) this.priceHistory.shift(); }
  calculateVolatility() {
    if (this.priceHistory.length < 10) return 0;
    const prices = this.priceHistory.map(p => p.price);
    const returns = [];
    for (let i = 1; i < prices.length; i++) returns.push((prices[i] - prices[i-1]) / prices[i-1]);
    const mean = returns.reduce((s, r) => s + r, 0) / returns.length;
    const variance = returns.reduce((s, r) => s + Math.pow(r - mean, 2), 0) / returns.length;
    return Math.sqrt(variance);
  }
}
const volatilityTracker = new VolatilityTracker();

const bot = new Bot(BOT_TOKEN);
const db = new Database('arb_bot.db');
db.pragma('journal_mode = WAL');
db.exec(`
  CREATE TABLE IF NOT EXISTS config (key TEXT PRIMARY KEY, value TEXT);
  CREATE TABLE IF NOT EXISTS opportunities (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    hour_key TEXT, combo TEXT, total_cost REAL, profit_pct REAL,
    poly_price REAL, kalshi_price REAL,
    poly_liquidity REAL, kalshi_liquidity REAL,
    spread REAL, vwap_price REAL, fees REAL, net_profit_pct REAL,
    volatility REAL, created_at DATETIME DEFAULT CURRENT_TIMESTAMP
  );
  CREATE TABLE IF NOT EXISTS trades (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    hour_key TEXT, combo TEXT, contracts INTEGER, total_cost REAL, mode TEXT,
    poly_side TEXT, poly_token_id TEXT, poly_price REAL,
    poly_order_id TEXT, poly_status TEXT, poly_error TEXT,
    poly_filled_size REAL, poly_filled_price REAL,
    kalshi_side TEXT, kalshi_ticker TEXT, kalshi_price REAL,
    kalshi_order_id TEXT, kalshi_status TEXT, kalshi_error TEXT,
    kalshi_filled_count REAL, kalshi_filled_price REAL,
    gross_pnl REAL, fees REAL, net_pnl REAL,
    execution_time_ms INTEGER, volatility REAL,
    rebalance_attempts INTEGER, rebalance_success INTEGER,
    leg_time_diff_ms INTEGER, flattened INTEGER DEFAULT 0, flatten_pnl REAL DEFAULT 0,
    strike_diff_pct REAL, close_time_diff_sec REAL, price_impact_pct REAL,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
  );
  CREATE TABLE IF NOT EXISTS risk_rejects (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    hour_key TEXT, combo TEXT, reason TEXT, total_cost REAL, profit_pct REAL, created_at DATETIME DEFAULT CURRENT_TIMESTAMP
  );
`);

function getConfig(key, def) { const row = db.prepare('SELECT value FROM config WHERE key=?').get(key); return row ? row.value : def; }
function setConfig(key, value) { db.prepare('INSERT INTO config (key,value) VALUES (?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value').run(key, String(value)); }

const SEP = '━━━━━━━━━━━━━━━━━━';
const fmtCents = (x) => `${(x * 100).toFixed(1)}¢`;
const fmtUsd = (x) => `$${Number(x).toFixed(2)}`;
function nowHourKey() { const d = new Date(); return `${d.getUTCFullYear()}-${d.getUTCMonth()}-${d.getUTCDate()}-${d.getUTCHours()}`; }
function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }

const kalshiPrivateKey = crypto.createPrivateKey(fs.readFileSync(KALSHI_PRIVATE_KEY_PATH, 'utf8'));
function kalshiSign(method, path) {
  const timestamp = String(Date.now());
  const message = `${timestamp}${method}${path}`;
  const signature = crypto.sign('sha256', Buffer.from(message), { key: kalshiPrivateKey, padding: crypto.constants.RSA_PKCS1_PSS_PADDING, saltLength: crypto.constants.RSA_PSS_SALTLEN_DIGEST });
  return { 'KALSHI-ACCESS-KEY': KALSHI_KEY_ID, 'KALSHI-ACCESS-TIMESTAMP': timestamp, 'KALSHI-ACCESS-SIGNATURE': signature.toString('base64') };
}
async function kalshiRest(path, method = 'GET', body = null) {
  await kalshiRateLimiter.waitForSlot();
  const headers = kalshiSign(method, `/trade-api/v2${path}`);
  const options = { method, headers };
  if (body) { options.headers['Content-Type'] = 'application/json'; options.body = JSON.stringify(body); }
  const r = await fetch(`${KALSHI_REST}${path}`, options);
  if (!r.ok) throw new Error(`Kalshi REST ${path} -> ${r.status}`);
  return r.json();
}

function kalshiPriceToDollars(market, side, book = 'ask') {
  const dollarsKey = `${side}_${book}_dollars`;
  const centsKey = `${side}_${book}`;
  if (market[dollarsKey] != null) return parseFloat(market[dollarsKey]);
  if (market[centsKey] != null) return market[centsKey] / 100;
  return null;
}

async function findKalshiHourlyMarket(refPrice) {
  const data = await kalshiRest(`/markets?series_ticker=${KALSHI_SERIES}&status=open&limit=200`);
  const markets = data.markets || [];
  if (!markets.length) return null;
  const minClose = markets.reduce((min, m) => { const t = new Date(m.close_time).getTime(); return t < min ? t : min; }, Infinity);
  const sameWindow = markets.filter(m => new Date(m.close_time).getTime() === minClose);
  let m;
  if (refPrice != null && !Number.isNaN(refPrice)) {
    m = sameWindow.reduce((best, cur) => {
      const curStrike = cur.floor_strike != null ? cur.floor_strike : cur.cap_strike;
      const bestStrike = best.floor_strike != null ? best.floor_strike : best.cap_strike;
      if (curStrike == null) return best;
      if (bestStrike == null) return cur;
      return Math.abs(curStrike - refPrice) < Math.abs(bestStrike - refPrice) ? cur : best;
    }, sameWindow[0]);
  } else m = sameWindow[0];
  return {
    ticker: m.ticker,
    strike: m.floor_strike != null ? m.floor_strike : m.cap_strike,
    closeTime: m.close_time,
    openTime: m.open_time,
    yesPrice: kalshiPriceToDollars(m, 'yes', 'ask'),
    noPrice: kalshiPriceToDollars(m, 'no', 'ask'),
    floorStrike: m.floor_strike,
    capStrike: m.cap_strike,
    raw: m,
  };
}

function isHourlyTitle(title) {
  if (!/^Bitcoin Up or Down/i.test(title)) return false;
  if (/AM-|PM-/.test(title)) return false;
  return /\d{1,2}(AM|PM) ET$/i.test(title);
}

async function findPolyHourlyEvent() {
  const r = await fetch(`${GAMMA_API}/events?closed=false&active=true&limit=100&order=endDate&ascending=true&tag_slug=bitcoin`);
  const events = await r.json();
  const list = Array.isArray(events) ? events : (events.events || []);
  const now = Date.now();
  const candidates = list.filter(e => isHourlyTitle(e.title || '') && new Date(e.endDate).getTime() > now);
  if (!candidates.length) return null;
  candidates.sort((a, b) => new Date(a.endDate) - new Date(b.endDate));
  const event = candidates[0];
  const market = (event.markets || [])[0];
  if (!market) return null;
  let outcomes = market.outcomes; if (typeof outcomes === 'string') outcomes = JSON.parse(outcomes);
  let prices = market.outcomePrices; if (typeof prices === 'string') prices = JSON.parse(prices);
  let tokenIds = market.clobTokenIds; if (typeof tokenIds === 'string') tokenIds = JSON.parse(tokenIds);
  const upIdx = outcomes.findIndex(o => /up/i.test(o));
  const downIdx = outcomes.findIndex(o => /down/i.test(o));
  return {
    slug: event.slug,
    title: event.title,
    endDate: event.endDate,
    startDate: event.startDate,
    tokenIds,
    upTokenId: tokenIds[upIdx], downTokenId: tokenIds[downIdx],
    upPrice: parseFloat(prices[upIdx]), downPrice: parseFloat(prices[downIdx]),
  };
}

async function fetchHourOpenPrice() {
  const r = await fetch(`${BINANCE_KLINES}?symbol=BTCUSDT&interval=1h&limit=1`);
  const d = await r.json();
  return parseFloat(d[0][1]);
}

async function getOrderBookCached(tokenId) {
  const cached = cacheManager.get(`poly:orderbook:${tokenId}`);
  if (cached) return cached;
  await polyRateLimiter.waitForSlot();
  const response = await fetch(`${POLY_CLOB_HOST}/book?token_id=${tokenId}`);
  if (!response.ok) throw new Error(`Order book alınamadı: ${response.status}`);
  const book = await response.json();
  cacheManager.set(`poly:orderbook:${tokenId}`, book, 2000);
  return book;
}

async function getPolyBestAsk(tokenId, fallbackPrice = null) {
  try {
    const book = await getOrderBookCached(tokenId);
    const asks = book?.asks || [];
    if (asks.length > 0) {
      const best = asks.reduce((min, a) => Number(a.price) < Number(min.price) ? a : min, asks[0]);
      return parseFloat(best.price);
    }
  } catch (e) {}
  return fallbackPrice;
}

async function getKalshiOrderBookCached(ticker) {
  const cached = cacheManager.get(`kalshi:orderbook:${ticker}`);
  if (cached) return cached;
  const orderbook = await kalshiRest(`/markets/${ticker}/orderbook`);
  cacheManager.set(`kalshi:orderbook:${ticker}`, orderbook, 5000);
  return orderbook;
}

function calculateVWAP(orders, targetSize) {
  let totalCost = 0, totalSize = 0, optimalPrice = null;
  for (const order of orders) {
    const size = Number(order.size || order.count || 0);
    const price = Number(order.price);
    if (totalSize + size >= targetSize) {
      const remaining = targetSize - totalSize;
      totalCost += remaining * price; totalSize = targetSize; optimalPrice = price; break;
    }
    totalCost += size * price; totalSize += size;
  }
  return { vwap: totalSize > 0 ? totalCost / totalSize : null, optimalPrice, totalSize, totalCost };
}

function simulateLiquidityImpact(orders, targetSize) {
  if (!orders || orders.length === 0) return { vwap: null, worstPrice: null, impactPct: 1, filled: 0, fullFill: false, depthAtBest: 0, depthTotal: 0 };
  const bestPrice = Number(orders[0].price);
  const v = calculateVWAP(orders, targetSize);
  const filled = v.totalSize;
  const fullFill = filled >= targetSize * 0.999;
  const impactPct = v.vwap && bestPrice > 0 ? (v.vwap - bestPrice) / bestPrice : 1;
  const depthTotal = orders.slice(0, RISK_LIMITS.maxBookLevelsToCheck).reduce((s, o) => s + Number(o.size || o.count || 0), 0);
  const depthAtBest = Number(orders[0].size || orders[0].count || 0);
  return { vwap: v.vwap, worstPrice: v.optimalPrice, impactPct, filled, fullFill, depthAtBest, depthTotal };
}

function analyzeOrderBookDepth(book, targetSize) {
  const bids = [...(book.bids || [])].sort((a, b) => Number(b.price) - Number(a.price));
  const asks = [...(book.asks || [])].sort((a, b) => Number(a.price) - Number(b.price));
  const bestBid = bids.length > 0 ? Number(bids[0].price) : 0;
  const bestAsk = asks.length > 0 ? Number(asks[0].price) : 0;
  const oneSidedBook = bestBid === 0 || bestAsk === 0;
  const spread = bestAsk - bestBid;
  const bidDepth = bids.slice(0, 20).reduce((sum, b) => sum + Number(b.size), 0);
  const askDepth = asks.slice(0, 20).reduce((sum, a) => sum + Number(a.size), 0);
  const vwapData = calculateVWAP(asks, targetSize);
  const slippage = vwapData.vwap && bestAsk > 0 ? (vwapData.vwap - bestAsk) / bestAsk : 0;
  const sim = simulateLiquidityImpact(asks, targetSize);
  const deepDepth = asks.slice(0, RISK_LIMITS.maxBookLevelsToCheck).reduce((s, a) => s + Number(a.size), 0);
  return {
    bestBid, bestAsk, spread, bidDepth, askDepth,
    vwap: vwapData.vwap, optimalPrice: vwapData.optimalPrice, slippage,
    sufficientLiquidity: askDepth >= Math.max(targetSize * RISK_LIMITS.minDepthMultiplier, RISK_LIMITS.minLiquidity) && sim.fullFill && deepDepth >= targetSize * RISK_LIMITS.minDepthMultiplier,
    acceptableSpread: !oneSidedBook && spread <= RISK_LIMITS.maxSpread,
    acceptableSlippage: slippage <= RISK_LIMITS.maxSlippage && sim.impactPct <= RISK_LIMITS.maxPriceImpactPct,
    oneSidedBook, priceImpactPct: sim.impactPct, fullFill: sim.fullFill, deepDepth, depthTotal: sim.depthTotal,
  };
}

function buildKalshiAskLevels(bidLevels) {
  const sorted = [...(bidLevels || [])].sort((a, b) => Number(b[0]) - Number(a[0]));
  return sorted.map(([priceDollars, count]) => ({ price: 1 - Number(priceDollars), size: Number(count) }));
}

function analyzeKalshiOrderBookDepth(orderbook, side, targetSize) {
  const oppositeSide = side === 'yes' ? 'no' : 'yes';
  const book = orderbook?.orderbook_fp || {};
  const askLevels = buildKalshiAskLevels(book[`${oppositeSide}_dollars`]);
  const ownBidLevels = book[`${side}_dollars`] || [];
  const bestAsk = askLevels.length > 0 ? askLevels[0].price : 0;
  const bestBid = ownBidLevels.length > 0 ? ownBidLevels.reduce((max, l) => Math.max(max, Number(l[0])), 0) : 0;
  const oneSidedBook = bestBid === 0 || bestAsk === 0;
  const spread = bestAsk - bestBid;
  const askDepth = askLevels.slice(0, 20).reduce((sum, a) => sum + a.size, 0);
  const vwapData = calculateVWAP(askLevels, targetSize);
  const slippage = vwapData.vwap && bestAsk > 0 ? (vwapData.vwap - bestAsk) / bestAsk : 0;
  const sim = simulateLiquidityImpact(askLevels, targetSize);
  const deepDepth = askLevels.slice(0, RISK_LIMITS.maxBookLevelsToCheck).reduce((s, a) => s + a.size, 0);
  return {
    bestBid, bestAsk, spread, askDepth,
    vwap: vwapData.vwap, optimalPrice: vwapData.optimalPrice, slippage,
    sufficientLiquidity: askDepth >= Math.max(targetSize * RISK_LIMITS.minDepthMultiplier, RISK_LIMITS.minLiquidity) && sim.fullFill && deepDepth >= targetSize * RISK_LIMITS.minDepthMultiplier,
    acceptableSpread: !oneSidedBook && spread <= RISK_LIMITS.maxSpread,
    acceptableSlippage: slippage <= RISK_LIMITS.maxSlippage && sim.impactPct <= RISK_LIMITS.maxPriceImpactPct,
    oneSidedBook, priceImpactPct: sim.impactPct, fullFill: sim.fullFill, deepDepth, depthTotal: sim.depthTotal,
  };
}

function validateStrikeAlignment(polyStrike, kalshiStrike, polyEnd, kalshiClose) {
  const reasons = [];
  if (polyStrike == null || kalshiStrike == null) { reasons.push('Strike bilgisi eksik'); return { valid: false, reasons, diffPct: null, diffUsd: null, closeDiffSec: null }; }
  const diffUsd = Math.abs(polyStrike - kalshiStrike);
  const diffPct = (diffUsd / polyStrike) * 100;
  if (diffPct > RISK_LIMITS.maxStrikeDiffPct) reasons.push(`Strike farki cok buyuk: %${diffPct.toFixed(3)} (${fmtUsd(diffUsd)}) limit %${RISK_LIMITS.maxStrikeDiffPct}`);
  if (diffUsd > RISK_LIMITS.maxStrikeDiffUsd) reasons.push(`Strike farki USD limit ustu: ${fmtUsd(diffUsd)} limit ${fmtUsd(RISK_LIMITS.maxStrikeDiffUsd)}`);
  let closeDiffSec = null;
  if (polyEnd && kalshiClose) {
    closeDiffSec = Math.abs(new Date(polyEnd).getTime() - new Date(kalshiClose).getTime()) / 1000;
    if (closeDiffSec > RISK_LIMITS.maxCloseTimeDiffSec) reasons.push(`Kapanis saati uyusmazligi: ${closeDiffSec.toFixed(0)}sn limit ${RISK_LIMITS.maxCloseTimeDiffSec}sn`);
  }
  const polyHour = polyEnd ? new Date(polyEnd).getUTCHours() : null;
  const kalshiHour = kalshiClose ? new Date(kalshiClose).getUTCHours() : null;
  if (polyHour != null && kalshiHour != null && polyHour !== kalshiHour) reasons.push(`Saat dilimi uyusmazligi: Poly ${polyHour} Kalshi ${kalshiHour}`);
  return { valid: reasons.length === 0, reasons, diffPct, diffUsd, closeDiffSec };
}

function validateBooksFresh(polyTokenId, kalshiTicker) {
  const polyFresh = cacheManager.isFresh(`poly:orderbook:${polyTokenId}`, RISK_LIMITS.requireBothBooksFreshMs);
  const kalshiFresh = cacheManager.isFresh(`kalshi:orderbook:${kalshiTicker}`, RISK_LIMITS.requireBothBooksFreshMs);
  return { polyFresh, kalshiFresh, bothFresh: polyFresh && kalshiFresh };
}

class PositionManager {
  constructor() { this.positions = new Map(); this.history = []; }
  openPosition(positionData) {
    const id = `${positionData.hourKey}:${positionData.combo}`;
    const position = { id, ...positionData, status: 'OPEN', entryTime: Date.now(), legs: { poly: { status: 'PENDING', filled: 0, price: null }, kalshi: { status: 'PENDING', filled: 0, price: null } }, rebalanceAttempts: 0, maxRebalanceAttempts: RISK_LIMITS.rebalanceMaxAttempts };
    this.positions.set(id, position); return position;
  }
  updateLeg(positionId, leg, status, filled, price) {
    const pos = this.positions.get(positionId); if (!pos) return { needsRebalance: false };
    pos.legs[leg].status = status; pos.legs[leg].filled = filled; pos.legs[leg].price = price;
    if (this.isSingleLeg(pos)) return { needsRebalance: true, position: pos };
    if (this.isComplete(pos)) { pos.status = 'COMPLETE'; this.history.push(pos); this.positions.delete(positionId); }
    return { needsRebalance: false, position: pos };
  }
  isSingleLeg(position) { const polyFilled = position.legs.poly.status === 'FILLED'; const kalshiFilled = position.legs.kalshi.status === 'FILLED'; return polyFilled !== kalshiFilled; }
  isComplete(position) { return position.legs.poly.status === 'FILLED' && position.legs.kalshi.status === 'FILLED'; }
  getMissingLeg(position) { if (position.legs.poly.status !== 'FILLED') return 'poly'; if (position.legs.kalshi.status !== 'FILLED') return 'kalshi'; return null; }
  getAllOpenPositions() { return [...this.positions.values()]; }
}
const positionManager = new PositionManager();

let state = { hourKey: null, poly: null, kalshi: null, polyStrike: null, active: null, btcPrice: null, consecutiveFailures: 0, isCircuitBreakerOpen: false, lastStrikeCheck: null };

let polyClobClient = null;
let polyClobReady = null;
async function getPolyClobClient() {
  if (polyClobClient) return polyClobClient;
  if (!POLY_PRIVATE_KEY) throw new Error('POLY_PRIVATE_KEY tanimli degil');
  if (!POLYMARKET_WALLET_ADDRESS) throw new Error('POLYMARKET_WALLET_ADDRESS tanimli degil');
  if (!RELAYER_API_KEY || !RELAYER_API_KEY_ADDRESS) throw new Error('RELAYER_API_KEY / RELAYER_API_KEY_ADDRESS tanimli degil');
  if (!polyClobReady) {
    polyClobReady = (async () => {
      polyClobClient = await createSecureClient({ wallet: POLYMARKET_WALLET_ADDRESS, signer: privateKey(POLY_PRIVATE_KEY), apiKey: relayerApiKey({ key: RELAYER_API_KEY, address: RELAYER_API_KEY_ADDRESS }) });
      return polyClobClient;
    })();
  }
  return polyClobReady;
}
async function getTickSizeCached(tokenId) {
  const cached = cacheManager.get(`poly:ticksize:${tokenId}`);
  if (cached) return cached;
  const book = await getOrderBookCached(tokenId);
  const tickSize = parseFloat(book.tick_size) || 0.01;
  cacheManager.set(`poly:ticksize:${tokenId}`, tickSize, 60000);
  return tickSize;
}

async function placePolyOrderSmart(tokenId, targetSize, referencePrice) {
  const startTime = Date.now();
  const book = await getOrderBookCached(tokenId);
  const analysis = analyzeOrderBookDepth(book, targetSize);
  if (!analysis.sufficientLiquidity) throw new Error(`Yetersiz likidite: ${analysis.askDepth.toFixed(2)} derinlik ${analysis.deepDepth.toFixed(2)} fullFill:${analysis.fullFill}`);
  if (!analysis.acceptableSpread) { if (analysis.oneSidedBook) throw new Error(`Kitap tek tarafli (bid: ${fmtCents(analysis.bestBid)}, ask: ${fmtCents(analysis.bestAsk)})`); throw new Error(`Spread cok genis: ${fmtCents(analysis.spread)}`); }
  if (!analysis.acceptableSlippage) throw new Error(`Yuksek slippage / price impact: %${(analysis.slippage * 100).toFixed(2)} impact %${(analysis.priceImpactPct * 100).toFixed(2)}`);
  const tickSize = await getTickSizeCached(tokenId);
  const optimalPrice = analysis.vwap + 0.002;
  const buyPrice = Math.ceil(optimalPrice / tickSize) * tickSize;
  const decimals = String(tickSize).includes('.') ? String(tickSize).split('.')[1].length : 2;
  const finalPrice = parseFloat(Math.min(0.99, buyPrice).toFixed(decimals));
  const client = await getPolyClobClient();
  const resp = await client.placeLimitOrder({ tokenId, side: OrderSide.BUY, price: String(finalPrice), size: String(targetSize) });
  const executionTime = Date.now() - startTime;
  if (resp.status === 'live' || resp.status === 'unmatched') { const orderId = resp.orderId || resp.orderID; if (orderId) await client.cancelOrder({ orderId }).catch(() => {}); throw new Error(`Poly emri dolmadi (${executionTime}ms)`); }
  if (resp.success === false || resp.ok === false) throw new Error(resp.errorMsg || resp.message || 'Poly emri reddedildi');
  return { ...resp, executionTime, analysis };
}

async function placeKalshiOrderSmart(ticker, side, count, referencePrice) {
  const startTime = Date.now();
  let market = cacheManager.get(`kalshi:market:${ticker}`);
  if (!market) { const marketInfo = await kalshiRest(`/markets/${ticker}`); market = marketInfo.market; cacheManager.set(`kalshi:market:${ticker}`, market, 10000); }
  if (market.status !== 'active') throw new Error(`Kalshi market kapali (status: ${market.status})`);
  const closeTime = new Date(market.close_time).getTime();
  const minutesUntilClose = (closeTime - Date.now()) / 60000;
  if (minutesUntilClose < RISK_LIMITS.minMarketMinutes) throw new Error(`Kapanisa cok az kaldi (${minutesUntilClose.toFixed(1)} dk)`);
  if (minutesUntilClose > RISK_LIMITS.maxMarketMinutes) throw new Error(`Market cok yeni (${minutesUntilClose.toFixed(1)} dk)`);
  const orderbook = await getKalshiOrderBookCached(ticker);
  const kalshiAnalysis = analyzeKalshiOrderBookDepth(orderbook, side, count);
  if (!kalshiAnalysis.sufficientLiquidity) throw new Error(`Kalshi yetersiz likidite: ${kalshiAnalysis.askDepth.toFixed(2)} derinlik ${kalshiAnalysis.deepDepth.toFixed(2)} fullFill:${kalshiAnalysis.fullFill}`);
  if (!kalshiAnalysis.acceptableSpread) throw new Error(`Kalshi spread cok genis: ${fmtCents(kalshiAnalysis.spread)}`);
  if (!kalshiAnalysis.acceptableSlippage) throw new Error(`Kalshi yuksek slippage: %${(kalshiAnalysis.slippage * 100).toFixed(2)} impact %${(kalshiAnalysis.priceImpactPct * 100).toFixed(2)}`);
  const optimalPrice = (kalshiAnalysis.vwap || referencePrice) + 0.002;
  const bookSide = side === 'yes' ? 'bid' : 'ask';
  const rawPrice = Math.min(0.99, Math.max(0.01, optimalPrice));
  const price = Math.ceil(rawPrice * 100) / 100;
  const gtcOrder = { ticker, client_order_id: crypto.randomUUID(), side: bookSide, count: count.toFixed(2), price: price.toFixed(2), time_in_force: 'good_till_canceled', self_trade_prevention_type: 'maker_at_cross' };
  const path = '/portfolio/events/orders';
  const headers = kalshiSign('POST', `/trade-api/v2${path}`);
  let r = await fetch(`${KALSHI_REST}${path}`, { method: 'POST', headers: { ...headers, 'Content-Type': 'application/json' }, body: JSON.stringify(gtcOrder) });
  let data = await r.json().catch(() => ({}));
  if ((Number(data.fill_count) || 0) === 0) {
    await sleep(2000);
    if (data.order_id) { const cancelPath = `/portfolio/events/orders/${data.order_id}`; await kalshiRest(cancelPath, 'DELETE').catch(() => {}); }
    const iocOrder = { ...gtcOrder, client_order_id: crypto.randomUUID(), time_in_force: 'immediate_or_cancel', self_trade_prevention_type: 'taker_at_cross' };
    r = await fetch(`${KALSHI_REST}${path}`, { method: 'POST', headers: { ...headers, 'Content-Type': 'application/json' }, body: JSON.stringify(iocOrder) });
    data = await r.json().catch(() => ({}));
  }
  if (!r.ok) throw new Error(`Kalshi order hatasi (${r.status}): ${data.message || data.code || JSON.stringify(data)}`);
  if ((Number(data.fill_count) || 0) === 0) throw new Error('Kalshi emri dolmadi');
  return { ...data, fill_count: Number(data.fill_count) || 0, average_fill_price: Number(data.average_fill_price) || 0, executionTime: Date.now() - startTime, usedGTC: (data.time_in_force === 'good_till_canceled') };
}

async function flattenPolyLeg(tokenId, size, sideLabel) {
  try {
    const client = await getPolyClobClient();
    const book = await getOrderBookCached(tokenId);
    const bids = [...(book.bids || [])].sort((a, b) => Number(b.price) - Number(a.price));
    if (!bids.length) return { success: false, error: 'Poly flatten icin bid yok' };
    const price = Number(bids[0].price);
    const resp = await client.placeLimitOrder({ tokenId, side: OrderSide.SELL, price: String(price), size: String(size) });
    return { success: true, resp, price };
  } catch (e) { return { success: false, error: e.message }; }
}

async function flattenKalshiLeg(ticker, side, count) {
  try {
    const bookSide = side === 'yes' ? 'ask' : 'bid';
    const opposite = side === 'yes' ? 'no' : 'yes';
    const orderbook = await getKalshiOrderBookCached(ticker);
    const levels = orderbook?.orderbook_fp?.[`${opposite}_dollars`] || [];
    if (!levels.length) return { success: false, error: 'Kalshi flatten icin kitap yok' };
    const best = Math.max(...levels.map(l => Number(l[0])));
    const price = Math.floor(best * 100) / 100;
    const path = '/portfolio/events/orders';
    const headers = kalshiSign('POST', `/trade-api/v2${path}`);
    const order = { ticker, client_order_id: crypto.randomUUID(), side: bookSide, count: count.toFixed(2), price: price.toFixed(2), time_in_force: 'immediate_or_cancel', self_trade_prevention_type: 'taker_at_cross' };
    const r = await fetch(`${KALSHI_REST}${path}`, { method: 'POST', headers: { ...headers, 'Content-Type': 'application/json' }, body: JSON.stringify(order) });
    const data = await r.json().catch(() => ({}));
    if (!r.ok) return { success: false, error: data.message || `status ${r.status}` };
    return { success: Number(data.fill_count || 0) > 0, data, price };
  } catch (e) { return { success: false, error: e.message }; }
}

async function flattenSingleLeg(position, filledLeg, contracts, entryPrice) {
  if (!RISK_LIMITS.flattenOnSingleLeg) return { flattened: false, reason: 'flatten kapali' };
  let result = null;
  if (filledLeg === 'poly') {
    result = await flattenPolyLeg(position.polyTokenId, contracts, position.polySide || 'UP');
  } else {
    result = await flattenKalshiLeg(position.kalshiTicker, position.kalshiSide, contracts);
  }
  const flattenPnl = result?.success ? (result.price != null ? (result.price - entryPrice) * contracts : 0) : 0;
  return { flattened: !!result?.success, result, flattenPnl };
}

async function autoRebalance(position, missingLeg) {
  for (let attempt = 1; attempt <= RISK_LIMITS.rebalanceMaxAttempts; attempt++) {
    try {
      if (missingLeg === 'kalshi') {
        const side = position.combo.includes('YES') ? 'yes' : 'no';
        const newPrice = position.kalshiPrice + (RISK_LIMITS.rebalancePriceIncrement * attempt);
        await placeKalshiOrderSmart(position.kalshiTicker, side, position.contracts, newPrice);
        positionManager.updateLeg(position.id, 'kalshi', 'FILLED', position.contracts, newPrice);
        return { success: true, attempt };
      }
      if (missingLeg === 'poly') {
        const newPrice = position.polyPrice + (RISK_LIMITS.rebalancePriceIncrement * attempt);
        await placePolyOrderSmart(position.polyTokenId, position.contracts, newPrice);
        positionManager.updateLeg(position.id, 'poly', 'FILLED', position.contracts, newPrice);
        return { success: true, attempt };
      }
    } catch (err) { console.log(`Rebalans deneme ${attempt} basarisiz: ${err.message}`); }
  }
  return { success: false, attempt: RISK_LIMITS.rebalanceMaxAttempts };
}

function calculateNetProfit(totalCost, contracts) {
  const grossPnl = (1 - totalCost) * contracts;
  const polyFee = totalCost * contracts * RISK_LIMITS.polyMakerFee * 0.5;
  const kalshiFee = totalCost * contracts * RISK_LIMITS.kalshiMakerFee * 0.5;
  const totalFees = polyFee + kalshiFee;
  const netPnl = grossPnl - totalFees;
  return { grossPnl, totalFees, netPnl, netProfitPct: netPnl / (totalCost * contracts) };
}

function getTodayNetPnl() { const row = db.prepare(`SELECT COALESCE(SUM(net_pnl), 0) as pnl FROM trades WHERE date(created_at) = date('now')`).get(); return row.pnl; }
function isDailyLossLimitHit() { return getTodayNetPnl() <= -RISK_LIMITS.maxDailyLoss; }

let lastBlockLogKey = null;
let lastBlockLogTime = 0;
let evalLock = Promise.resolve();
function evaluateArbitrage() { evalLock = evalLock.then(() => evaluateArbitrageInner()).catch(e => console.error('evaluateArbitrage:', e.message)); return evalLock; }

async function evaluateArbitrageInner() {
  if (!state.poly || !state.kalshi || state.polyStrike == null) return;
  if (state.isCircuitBreakerOpen) return;
  const strikeCheck = validateStrikeAlignment(state.polyStrike, state.kalshi.strike, state.poly.endDate, state.kalshi.closeTime);
  state.lastStrikeCheck = strikeCheck;
  if (!strikeCheck.valid) {
    const key = `STRIKE|${strikeCheck.reasons.join(',')}`;
    if (key !== lastBlockLogKey || Date.now() - lastBlockLogTime > 30000) {
      console.log(`STRIKE ENGEL: ${strikeCheck.reasons.join(', ')}`);
      lastBlockLogKey = key; lastBlockLogTime = Date.now();
      try { await bot.api.sendMessage(GROUP_ID, `⛔ <b>STRIKE UYUSMAZLIĞI - İŞLEM ENGELLENDİ</b>\n${strikeCheck.reasons.map(r=>`❌ ${r}`).join('\n')}\n🎯 Poly Strike: $${state.polyStrike}\n🎯 Kalshi Strike: $${state.kalshi.strike}`, { parse_mode: 'HTML' }); } catch(e){}
      db.prepare(`INSERT INTO risk_rejects (hour_key, combo, reason, total_cost, profit_pct) VALUES (?,?,?,?,?)`).run(state.hourKey, 'STRIKE_CHECK', strikeCheck.reasons.join('; '), 0, 0);
    }
    return;
  }
  const [polyUp, polyDown] = await Promise.all([ getPolyBestAsk(state.poly.upTokenId, state.poly.upPrice), getPolyBestAsk(state.poly.downTokenId, state.poly.downPrice) ]);
  const { yesPrice: kalshiYes, noPrice: kalshiNo, strike: kalshiStrike, closeTime } = state.kalshi;
  if ([polyUp, polyDown, kalshiYes, kalshiNo].some(v => v == null || Number.isNaN(v))) return;
  state.poly.upPrice = polyUp; state.poly.downPrice = polyDown;
  let combo, total;
  if (state.polyStrike > kalshiStrike) { combo = 'Poly DOWN + Kalshi YES'; total = polyDown + kalshiYes; } else { combo = 'Poly UP + Kalshi NO'; total = polyUp + kalshiNo; }
  const thresholdCost = getThresholdCost();
  const profitPct = (1 - total) * 100;
  const isOpportunity = total < thresholdCost;
  if (isOpportunity) {
    const blockReasons = [];
    if (isDailyLossLimitHit()) blockReasons.push(`Günlük zarar limiti aşıldı: ${fmtUsd(getTodayNetPnl())} (limit: -${fmtUsd(RISK_LIMITS.maxDailyLoss)})`);
    const volatility = volatilityTracker.calculateVolatility();
    if (volatility > 0.005) blockReasons.push(`Yüksek volatilite: %${(volatility * 100).toFixed(2)}`);
    const minutesUntilClose = (new Date(closeTime).getTime() - Date.now()) / 60000;
    if (minutesUntilClose < RISK_LIMITS.minMarketMinutes) blockReasons.push(`Kapanışa az kaldı: ${minutesUntilClose.toFixed(1)} dk`);
    if (minutesUntilClose > RISK_LIMITS.maxMarketMinutes) blockReasons.push(`Market çok yeni: ${minutesUntilClose.toFixed(1)} dk`);
    const tokenId = combo.includes('DOWN') ? state.poly.downTokenId : state.poly.upTokenId;
    const sizeUsd = getTradeSizeUsd();
    const targetSize = sizeUsd > 0 ? sizeUsd / total : 10;
    if (sizeUsd > RISK_LIMITS.maxPositionSize) blockReasons.push(`Pozisyon boyutu limiti aşıldı: ${fmtUsd(sizeUsd)} (limit: ${fmtUsd(RISK_LIMITS.maxPositionSize)})`);
    const fresh = validateBooksFresh(tokenId, state.kalshi.ticker);
    if (!fresh.bothFresh) blockReasons.push(`Kitap taze degil Poly:${fresh.polyFresh} Kalshi:${fresh.kalshiFresh} (max ${RISK_LIMITS.requireBothBooksFreshMs}ms)`);
    let analysis = null;
    try {
      const book = await getOrderBookCached(tokenId);
      analysis = analyzeOrderBookDepth(book, targetSize);
      if (!analysis.sufficientLiquidity) blockReasons.push(`Yetersiz likidite: ask ${analysis.askDepth.toFixed(2)} derin ${analysis.deepDepth.toFixed(2)} fullFill:${analysis.fullFill} (min ${Math.max(targetSize * RISK_LIMITS.minDepthMultiplier, RISK_LIMITS.minLiquidity).toFixed(2)})`);
      if (!analysis.acceptableSpread) blockReasons.push(`Spread geniş: ${fmtCents(analysis.spread)} (max: ${fmtCents(RISK_LIMITS.maxSpread)})`);
      if (!analysis.acceptableSlippage) blockReasons.push(`Slippage / Impact yüksek: slippage %${(analysis.slippage * 100).toFixed(2)} impact %${(analysis.priceImpactPct * 100).toFixed(2)}`);
      if (!analysis.fullFill) blockReasons.push(`Kitap hedef boyutu doldurmuyor: hedef ${targetSize.toFixed(1)} dolan ${analysis.askDepth.toFixed(1)}`);
    } catch (e) { blockReasons.push(`Order book hatası (Poly): ${e.message}`); }
    const kalshiSide = combo.includes('YES') ? 'yes' : 'no';
    let kalshiAnalysis = null;
    try {
      const kalshiBook = await getKalshiOrderBookCached(state.kalshi.ticker);
      kalshiAnalysis = analyzeKalshiOrderBookDepth(kalshiBook, kalshiSide, targetSize);
      if (!kalshiAnalysis.sufficientLiquidity) blockReasons.push(`Kalshi yetersiz likidite: ask ${kalshiAnalysis.askDepth.toFixed(2)} derin ${kalshiAnalysis.deepDepth.toFixed(2)} fullFill:${kalshiAnalysis.fullFill}`);
      if (!kalshiAnalysis.acceptableSpread) blockReasons.push(`Kalshi spread geniş: ${fmtCents(kalshiAnalysis.spread)}`);
      if (!kalshiAnalysis.acceptableSlippage) blockReasons.push(`Kalshi slippage / impact yüksek: %${(kalshiAnalysis.slippage * 100).toFixed(2)} impact %${(kalshiAnalysis.priceImpactPct * 100).toFixed(2)}`);
      if (!kalshiAnalysis.fullFill) blockReasons.push(`Kalshi kitap hedefi doldurmuyor`);
    } catch (e) { blockReasons.push(`Order book hatası (Kalshi): ${e.message}`); }
    const contracts = sizeUsd > 0 ? Math.floor(sizeUsd / total) : 0;
    const feeCheck = calculateNetProfit(total, contracts);
    if (contracts > 0 && feeCheck.netPnl <= 0) blockReasons.push(`Fee sonrası kârsız: ${fmtUsd(feeCheck.netPnl)}`);
    const worstImpact = Math.max(analysis?.priceImpactPct || 0, kalshiAnalysis?.priceImpactPct || 0);
    if (worstImpact > RISK_LIMITS.maxPriceImpactPct) blockReasons.push(`Price Impact cok yuksek: %${(worstImpact*100).toFixed(2)} limit %${(RISK_LIMITS.maxPriceImpactPct*100).toFixed(2)}`);
    if (blockReasons.length > 0) {
      const logKey = `${combo}|${blockReasons.join(',')}`;
      const now = Date.now();
      if (logKey !== lastBlockLogKey || now - lastBlockLogTime > 30000) { console.log(`Fırsat engellendi: ${combo} (Kâr: %${profitPct.toFixed(2)})`); console.log(`   Nedenler: ${blockReasons.join(', ')}`); lastBlockLogKey = logKey; lastBlockLogTime = now; }
      if (!state.active || state.active.combo !== combo) {
        const message = buildBlockedMessage(combo, total, profitPct, blockReasons, volatility);
        try { const sent = await bot.api.sendMessage(GROUP_ID, message, { parse_mode: 'HTML' }); state.active = { combo, message_id: sent.message_id, last_total: total, blocked: true }; } catch (e) { console.error('Engel bildirimi hatası:', e.message); }
      }
      return;
    }
    if (!state.active || state.active.blocked) {
      const mode = getTradeMode();
      let keyboard;
      if (TRADING_ENABLED && mode === 'manuel' && contracts >= 1 && feeCheck.netPnl > 0) keyboard = new InlineKeyboard().text(`✅ İşlemi Aç (${contracts} kontrat)`, 'execute_trade');
      const message = buildOpportunityMessage(combo, total, profitPct, analysis, feeCheck, volatility);
      const sent = await bot.api.sendMessage(GROUP_ID, message, { parse_mode: 'HTML', reply_markup: keyboard });
      state.active = { combo, message_id: sent.message_id, last_total: total, blocked: false };
      if (TRADING_ENABLED && mode === 'otomatik' && feeCheck.netPnl > 0) executeTrade('otomatik').catch(e => console.error('executeTrade:', e.message));
    }
  }
}

function buildBlockedMessage(combo, total, profitPct, reasons, volatility) {
  const lines = ['🟡 <b>ARBİTRAJ VAR AMA ENGELLİ!</b>', SEP, `₿ <b>${combo}</b>`, `💰 Maliyet: <b>${fmtUsd(total)}</b>`, `📈 Kâr: <b>%${profitPct.toFixed(2)}</b>`, SEP, '<b>İşlem Yapılmama Nedenleri:</b>', ...reasons.map(r => `❌ ${r}`), SEP, `🔵 Poly: UP ${fmtCents(state.poly.upPrice)} · DOWN ${fmtCents(state.poly.downPrice)}`, `🟣 Kalshi: YES ${fmtCents(state.kalshi.yesPrice)} · NO ${fmtCents(state.kalshi.noPrice)}`, `🎯 Poly Strike: $${state.polyStrike?.toLocaleString() || 'YOK'}`, `🎯 Kalshi Strike: $${state.kalshi.strike?.toLocaleString() || 'YOK'}`, `📉 Volatilite: %${(volatility * 100).toFixed(2)}`];
  return lines.join('\n');
}

function buildOpportunityMessage(combo, total, profitPct, analysis, feeCheck, volatility) {
  const lines = ['🟢 YENİ ARBİTRAJ FIRSATI', SEP, `₿ <b>${combo}</b>`, `💰 Maliyet: <b>${fmtUsd(total)}</b>`, `📈 Brüt: %${profitPct.toFixed(2)}`, `💸 Fee: ${fmtUsd(feeCheck.totalFees)}`, `🎯 Net: <b>${feeCheck.netPnl > 0 ? '✅' : '❌'} ${fmtUsd(feeCheck.netPnl)}</b>`];
  if (analysis) lines.push(SEP, '📊 <b>Order Book:</b>', `Spread: ${fmtCents(analysis.spread)}`, `Derinlik: ${analysis.askDepth.toFixed(2)}`, `Derin Derinlik: ${analysis.deepDepth.toFixed(2)}`, `VWAP: ${fmtCents(analysis.vwap)}`, `Slippage: %${(analysis.slippage * 100).toFixed(2)}`, `Impact: %${(analysis.priceImpactPct * 100).toFixed(2)}`);
  lines.push(SEP, `📉 Volatilite: %${(volatility * 100).toFixed(2)}`, `🔵 Poly: UP ${fmtCents(state.poly.upPrice)} · DOWN ${fmtCents(state.poly.downPrice)}`, `🟣 Kalshi: YES ${fmtCents(state.kalshi.yesPrice)} · NO ${fmtCents(state.kalshi.noPrice)}`, `💵 BTC: $${state.btcPrice?.toLocaleString() || '...'}`);
  return lines.join('\n');
}

const executedThisHour = new Set();
async function executeTrade(triggeredBy) {
  if (!TRADING_ENABLED || state.isCircuitBreakerOpen) return;
  if (!state.active || !state.poly || !state.kalshi) return;
  const key = `${state.hourKey}:${state.active.combo}`;
  if (executedThisHour.has(key)) return;
  const sizeUsd = getTradeSizeUsd();
  if (!sizeUsd || sizeUsd <= 0) return;
  if (isDailyLossLimitHit()) { await bot.api.sendMessage(GROUP_ID, `🚫 Günlük zarar limiti aşıldı: ${fmtUsd(getTodayNetPnl())} (limit: -${fmtUsd(RISK_LIMITS.maxDailyLoss)})\nİşlem açılmadı.`, { parse_mode: 'HTML' }); return; }
  if (sizeUsd > RISK_LIMITS.maxPositionSize) { await bot.api.sendMessage(GROUP_ID, `🚫 Pozisyon boyutu limiti aşıldı: ${fmtUsd(sizeUsd)} (limit: ${fmtUsd(RISK_LIMITS.maxPositionSize)})\nİşlem açılmadı, /miktar ile düşürün.`, { parse_mode: 'HTML' }); return; }
  const strikeCheck = validateStrikeAlignment(state.polyStrike, state.kalshi.strike, state.poly.endDate, state.kalshi.closeTime);
  if (!strikeCheck.valid) { await bot.api.sendMessage(GROUP_ID, `⛔ <b>STRIKE UYUSMAZLIĞI - İŞLEM İPTAL</b>\n${strikeCheck.reasons.map(r=>`❌ ${r}`).join('\n')}`, { parse_mode: 'HTML' }); return; }
  const total = state.active.last_total;
  const contracts = Math.floor(sizeUsd / total);
  const feeCheck = calculateNetProfit(total, contracts);
  if (feeCheck.netPnl <= 0) { await bot.api.sendMessage(GROUP_ID, `❌ Kârsız işlem reddedildi (fee sonrası)`, { parse_mode: 'HTML' }); return; }
  const minutesUntilCloseCheck = (new Date(state.kalshi.closeTime).getTime() - Date.now()) / 60000;
  if (minutesUntilCloseCheck < RISK_LIMITS.minMarketMinutes || minutesUntilCloseCheck > RISK_LIMITS.maxMarketMinutes) { await bot.api.sendMessage(GROUP_ID, `🚫 Market süre dışı (${minutesUntilCloseCheck.toFixed(1)} dk, izin verilen: ${RISK_LIMITS.minMarketMinutes}-${RISK_LIMITS.maxMarketMinutes} dk)\nİşlem açılmadı, hiçbir bacak gönderilmedi.`, { parse_mode: 'HTML' }); return; }
  const isDownYes = state.active.combo.includes('DOWN');
  const polyTokenId = isDownYes ? state.poly.downTokenId : state.poly.upTokenId;
  const polySideLabel = isDownYes ? 'DOWN' : 'UP';
  const polyPrice = isDownYes ? state.poly.downPrice : state.poly.upPrice;
  const kalshiSide = isDownYes ? 'yes' : 'no';
  const kalshiPrice = isDownYes ? state.kalshi.yesPrice : state.kalshi.noPrice;
  const fresh = validateBooksFresh(polyTokenId, state.kalshi.ticker);
  if (!fresh.bothFresh) { await bot.api.sendMessage(GROUP_ID, `⛔ Kitaplar taze değil, işlem iptal. Poly:${fresh.polyFresh} Kalshi:${fresh.kalshiFresh}`, { parse_mode: 'HTML' }); return; }
  try {
    const polyBook = await getOrderBookCached(polyTokenId);
    const polyAnalysis = analyzeOrderBookDepth(polyBook, contracts);
    const kalshiBook = await getKalshiOrderBookCached(state.kalshi.ticker);
    const kalshiAnalysis = analyzeKalshiOrderBookDepth(kalshiBook, kalshiSide, contracts);
    if (!polyAnalysis.sufficientLiquidity || !kalshiAnalysis.sufficientLiquidity) { await bot.api.sendMessage(GROUP_ID, `⛔ Son kontrolde likidite yetersiz. Poly derinlik ${polyAnalysis.deepDepth.toFixed(1)} Kalshi ${kalshiAnalysis.deepDepth.toFixed(1)} İşlem açılmadı.`, { parse_mode: 'HTML' }); return; }
    if (!polyAnalysis.acceptableSlippage || !kalshiAnalysis.acceptableSlippage) { await bot.api.sendMessage(GROUP_ID, `⛔ Son kontrolde slippage / impact yüksek. İşlem açılmadı.`, { parse_mode: 'HTML' }); return; }
  } catch (e) { await bot.api.sendMessage(GROUP_ID, `⛔ Son kontrol hatası: ${e.message} İşlem açılmadı.`, { parse_mode: 'HTML' }); return; }
  executedThisHour.add(key);
  const position = positionManager.openPosition({ hourKey: state.hourKey, combo: state.active.combo, contracts, totalCost: total, polyTokenId, polyPrice, kalshiTicker: state.kalshi.ticker, kalshiPrice, kalshiSide, polySide: polySideLabel });
  const startTime = Date.now();
  await bot.api.sendMessage(GROUP_ID, `⏳ İşlem başlıyor: <b>${contracts} kontrat</b> · ${state.active.combo} · Atomik pencere ${RISK_LIMITS.atomicWindowMs}ms`, { parse_mode: 'HTML' });
  const polyStart = Date.now();
  const kalshiStart = Date.now();
  const [polyResult, kalshiResult] = await Promise.allSettled([ placePolyOrderSmart(polyTokenId, contracts, polyPrice), placeKalshiOrderSmart(state.kalshi.ticker, kalshiSide, contracts, kalshiPrice) ]);
  const polyEnd = Date.now();
  const kalshiEnd = Date.now();
  const legTimeDiffMs = Math.abs(polyEnd - kalshiEnd);
  let polyResp = null, polyErr = null;
  let kalshiResp = null, kalshiErr = null;
  if (polyResult.status === 'fulfilled') polyResp = polyResult.value; else polyErr = polyResult.reason.message;
  if (kalshiResult.status === 'fulfilled') kalshiResp = kalshiResult.value; else kalshiErr = kalshiResult.reason.message;
  const totalExecutionTime = Date.now() - startTime;
  const { grossPnl, totalFees, netPnl } = calculateNetProfit(total, contracts);
  if (!polyErr) positionManager.updateLeg(position.id, 'poly', 'FILLED', contracts, polyPrice); else positionManager.updateLeg(position.id, 'poly', 'FAILED', 0, null);
  if (!kalshiErr) positionManager.updateLeg(position.id, 'kalshi', 'FILLED', contracts, kalshiPrice); else positionManager.updateLeg(position.id, 'kalshi', 'FAILED', 0, null);
  let rebalanceResult = null;
  let flattenResult = { flattened: false, flattenPnl: 0 };
  let flattened = 0;
  if ((!polyErr && kalshiErr) || (polyErr && !kalshiErr)) {
    const missingLeg = !polyErr ? 'kalshi' : 'poly';
    const filledLeg = !polyErr ? 'poly' : 'kalshi';
    const filledEntryPrice = !polyErr ? polyPrice : kalshiPrice;
    rebalanceResult = await autoRebalance(position, missingLeg);
    if (!rebalanceResult.success) {
      const flat = await flattenSingleLeg(position, filledLeg, contracts, filledEntryPrice);
      flattenResult = flat;
      if (flat.flattened) {
        flattened = 1;
        positionManager.positions.delete(position.id);
        await bot.api.sendMessage(GROUP_ID, `🛡️ <b>TEK BACAK FLATTEN EDİLDİ</b>\n${filledLeg} bacağı piyasa fiyatından kapatıldı, tek taraflı risk taşnmadı.\nFlatten PnL: ${fmtUsd(flat.flattenPnl)}`, { parse_mode: 'HTML' });
      } else {
        await bot.api.sendMessage(GROUP_ID, `🚨 <b>FLATTEN BAŞARISIZ - MANUEL MÜDAHALE GEREK!</b>\n${filledLeg} bacağı açık kaldı. Lütfen platformdan manuel kapatın!\nHata: ${flat.result?.error || 'bilinmiyor'}`, { parse_mode: 'HTML' });
      }
    }
  }
  if (legTimeDiffMs > RISK_LIMITS.maxLegTimeDiffMs) {
    await bot.api.sendMessage(GROUP_ID, `⚠️ Bacaklar arası süre farkı yüksek: ${legTimeDiffMs}ms (limit ${RISK_LIMITS.maxLegTimeDiffMs}ms) - Sonraki işlemlerde dikkat`, { parse_mode: 'HTML' });
  }
  db.prepare(`INSERT INTO trades (hour_key, combo, contracts, total_cost, mode, poly_side, poly_token_id, poly_price, poly_order_id, poly_status, poly_error, poly_filled_size, poly_filled_price, kalshi_side, kalshi_ticker, kalshi_price, kalshi_order_id, kalshi_status, kalshi_error, kalshi_filled_count, kalshi_filled_price, gross_pnl, fees, net_pnl, execution_time_ms, volatility, rebalance_attempts, rebalance_success, leg_time_diff_ms, flattened, flatten_pnl, strike_diff_pct, close_time_diff_sec, price_impact_pct) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)`).run(
    state.hourKey, state.active.combo, contracts, total, getTradeMode(),
    polySideLabel, String(polyTokenId), polyPrice, polyResp?.orderID || null, polyErr ? 'HATA' : 'OK', polyErr, polyResp?.size_matched || 0, polyResp?.price || 0,
    kalshiSide, state.kalshi.ticker, kalshiPrice, kalshiResp?.order_id || null, kalshiErr ? 'HATA' : 'OK', kalshiErr, kalshiResp?.fill_count || 0, kalshiResp?.average_fill_price || 0,
    grossPnl, totalFees, netPnl, totalExecutionTime, volatilityTracker.calculateVolatility(), rebalanceResult?.attempt || 0, rebalanceResult?.success ? 1 : 0, legTimeDiffMs, flattened, flattenResult.flattenPnl || 0, strikeCheck.diffPct || 0, strikeCheck.closeDiffSec || 0, Math.max(0, 0)
  );
  if (polyErr || kalshiErr) {
    if (polyErr) console.error(`[executeTrade] Poly hatası: ${polyErr}`);
    if (kalshiErr) console.error(`[executeTrade] Kalshi hatası: ${kalshiErr}`);
    if (rebalanceResult?.success) {
      await bot.api.sendMessage(GROUP_ID, `✅ <b>İşlem tamamlandı (rebalans ile)</b>\n${contracts} kontrat · ${state.active.combo}\n🔄 Rebalans: ${rebalanceResult.attempt} denemede başarılı\n⚡ Süre: ${totalExecutionTime}ms`, { parse_mode: 'HTML' });
    } else if (flattened) {
      state.consecutiveFailures++;
    } else {
      state.consecutiveFailures++;
      if (state.consecutiveFailures >= 3) { state.isCircuitBreakerOpen = true; setTimeout(() => { state.isCircuitBreakerOpen = false; state.consecutiveFailures = 0; }, 60000); }
      const bothFailed = polyErr && kalshiErr;
      const title = bothFailed ? '❌ <b>İŞLEM AÇILAMADI (iki bacak da reddedildi)</b>' : '🚨 <b>TEK BACAK RİSKİ!</b>';
      const riskNote = bothFailed ? 'Pozisyon açılmadı, tek taraflı risk yok.' : 'Lütfen platformları kontrol edin!';
      await bot.api.sendMessage(GROUP_ID, `${title}\nPoly: ${polyErr ? `❌ ${polyErr}` : '✅'}\nKalshi: ${kalshiErr ? `❌ ${kalshiErr}` : '✅'}\nRebalans: ${rebalanceResult ? '❌ Başarısız' : 'Denenmedi'}\nFlatten: ${flattened ? '✅ Yapıldı' : '❌ Yapılamadı'}\n${riskNote}`, { parse_mode: 'HTML' });
    }
  } else {
    state.consecutiveFailures = 0;
    await bot.api.sendMessage(GROUP_ID, `✅ <b>İşlem tamamlandı</b>\n${contracts} kontrat · ${state.active.combo}\n💰 Brüt: ${fmtUsd(grossPnl)}\n💸 Fee: ${fmtUsd(totalFees)}\n🎯 Net: <b>${fmtUsd(netPnl)}</b>\n⚡ Süre: <b>${totalExecutionTime}ms</b>\n⏱️ Bacak farkı: ${legTimeDiffMs}ms`, { parse_mode: 'HTML' });
  }
}

class AnalyticsEngine {
  async getDetailedStats() {
    const trades = db.prepare('SELECT * FROM trades').all();
    const totalPnl = trades.reduce((s, t) => s + (t.net_pnl || 0), 0);
    const totalFees = trades.reduce((s, t) => s + (t.fees || 0), 0);
    const wins = trades.filter(t => (t.net_pnl || 0) > 0).length;
    const losses = trades.filter(t => (t.net_pnl || 0) < 0).length;
    const winRate = trades.length ? (wins / trades.length * 100) : 0;
    const hourlyStats = {};
    trades.forEach(t => { const hour = t.created_at?.substring(11, 13) || '??'; if (!hourlyStats[hour]) hourlyStats[hour] = { count: 0, pnl: 0 }; hourlyStats[hour].count++; hourlyStats[hour].pnl += t.net_pnl || 0; });
    const sortedHours = Object.entries(hourlyStats).sort((a, b) => b[1].pnl - a[1].pnl);
    const bestHours = sortedHours.filter(([, v]) => v.pnl > 0).slice(0, 3);
    const worstHours = sortedHours.filter(([, v]) => v.pnl < 0).sort((a, b) => a[1].pnl - b[1].pnl).slice(0, 3);
    const avgTime = trades.length ? trades.reduce((s, t) => s + (t.execution_time_ms || 0), 0) / trades.length : 0;
    return { totalPnl, totalFees, totalTrades: trades.length, wins, losses, winRate, bestHours, worstHours, avgTime };
  }
}
const analytics = new AnalyticsEngine();

async function isGroupAdmin(chatId, userId) {
  if (!userId) return false;
  const cacheKey = `tg:admin:${chatId}:${userId}`;
  const cached = cacheManager.get(cacheKey);
  if (cached !== undefined && cached !== null) return cached;
  let isAdmin = false;
  try { const member = await bot.api.getChatMember(chatId, userId); isAdmin = member.status === 'creator' || member.status === 'administrator'; } catch (e) { isAdmin = false; }
  cacheManager.set(cacheKey, isAdmin, 60000);
  return isAdmin;
}
bot.use(async (ctx, next) => {
  if (ctx.chat?.id !== GROUP_ID) return;
  const userId = ctx.from?.id;
  const allowed = await isGroupAdmin(GROUP_ID, userId);
  if (!allowed) {
    if (ctx.callbackQuery) return ctx.answerCallbackQuery({ text: '⛔ Bu işlem için yetkiniz yok.', show_alert: true }).catch(() => {});
    return;
  }
  return next();
});

bot.command('start', async (ctx) => {
  await ctx.reply('₿ <b>ULTIMATE Arbitraj Botu</b>\n\n/esik yuzde - Eşik\n/miktar usd - Pozisyon\n/mod manuel|otomatik - Mod\n/al - Manuel işlem\n/durum - Durum\n/pnl - P&L\n/analiz - Analiz\n/pozisyonlar - İşlemler\n/dur - Durdur\n/ping - Test', { parse_mode: 'HTML' });
});
bot.command('durum', async (ctx) => {
  if (ctx.chat.id !== GROUP_ID) return;
  if (!state.poly || !state.kalshi) return ctx.reply('🔍 Market verisi yok.');
  const volatility = volatilityTracker.calculateVolatility();
  const minutesUntilClose = (new Date(state.kalshi.closeTime).getTime() - Date.now()) / 60000;
  let combo, total, profitPct;
  if (state.polyStrike > state.kalshi.strike) { combo = 'Poly DOWN + Kalshi YES'; total = state.poly.downPrice + state.kalshi.yesPrice; } else { combo = 'Poly UP + Kalshi NO'; total = state.poly.upPrice + state.kalshi.noPrice; }
  profitPct = (1 - total) * 100;
  const isOpportunity = total < getThresholdCost();
  const strikeCheck = state.lastStrikeCheck || validateStrikeAlignment(state.polyStrike, state.kalshi.strike, state.poly.endDate, state.kalshi.closeTime);
  const lines = [`₿ <b>Durum</b>`, SEP, `🔵 Poly: UP ${fmtCents(state.poly.upPrice)} · DOWN ${fmtCents(state.poly.downPrice)}`, `🟣 Kalshi: YES ${fmtCents(state.kalshi.yesPrice)} · NO ${fmtCents(state.kalshi.noPrice)}`, SEP, '<b>Arbitraj Hesabı:</b>', `🎯 Combo: <b>${combo}</b>`, `💰 Toplam: ${fmtUsd(total)}`, `📈 Kâr: ${isOpportunity ? '✅' : '❌'} %${profitPct.toFixed(2)}`, SEP, `🎯 Poly Strike: $${state.polyStrike?.toLocaleString() || 'YOK'}`, `🎯 Kalshi Strike: $${state.kalshi.strike?.toLocaleString() || 'YOK'}`, `📏 Strike Farkı: %${(strikeCheck.diffPct||0).toFixed(3)} ${strikeCheck.valid ? '✅' : '❌'}`, `⏰ Kapanış Farkı: ${(strikeCheck.closeDiffSec||0).toFixed(0)}sn`, `⏰ Market: ${minutesUntilClose.toFixed(0)} dk kaldı`, `💵 BTC: $${state.btcPrice?.toLocaleString() || '...'}`, `📉 Volatilite: %${(volatility * 100).toFixed(2)}`, `🟢 Fırsat: ${state.active ? (state.active.blocked ? '⚠️ Engelli' : state.active.combo) : 'yok'}`, `🔄 Devre Kesici: ${state.isCircuitBreakerOpen ? '🔴' : '🟢'}`, `📅 Günlük P&L: ${fmtUsd(getTodayNetPnl())} / -${fmtUsd(RISK_LIMITS.maxDailyLoss)} limit ${isDailyLossLimitHit() ? '🚫' : '🟢'}`, `⚙️ Mod: ${getTradeMode()} · ${fmtUsd(getTradeSizeUsd())}`];
  await ctx.reply(lines.join('\n'), { parse_mode: 'HTML' });
});
bot.command('analiz', async (ctx) => {
  if (ctx.chat.id !== GROUP_ID) return;
  const stats = await analytics.getDetailedStats();
  const lines = ['📊 <b>DETAYLI ANALİZ</b>', SEP, `💰 Net: ${fmtUsd(stats.totalPnl)}`, `🎯 Win Rate: %${stats.winRate.toFixed(1)}`, SEP, '<b>En Kârlı Saatler:</b>', ...(stats.bestHours.length ? stats.bestHours.map(([h, d]) => `${h}:00 → ${fmtUsd(d.pnl)}`) : ['(kârlı saat yok)']), SEP, '<b>En Zararlı Saatler:</b>', ...(stats.worstHours.length ? stats.worstHours.map(([h, d]) => `${h}:00 → ${fmtUsd(d.pnl)}`) : ['(zararlı saat yok)'])];
  await ctx.reply(lines.join('\n'), { parse_mode: 'HTML' });
});
bot.command('mod', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; const arg = ctx.match?.trim().toLowerCase(); if (!arg) return ctx.reply(`⚙️ Mod: ${getTradeMode()}`); if (!['otomatik', 'manuel'].includes(arg)) return ctx.reply('⚠️ Geçersiz.'); setTradeMode(arg); await ctx.reply(`✅ Mod: ${arg}`); });
bot.command('miktar', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; const arg = ctx.match?.trim(); if (!arg) return ctx.reply(`💰 Miktar: ${fmtUsd(getTradeSizeUsd())}`); const val = parseFloat(arg.replace(',', '.')); if (Number.isNaN(val) || val <= 0) return ctx.reply('⚠️ Geçersiz.'); setTradeSizeUsd(val); await ctx.reply(`✅ Miktar: ${fmtUsd(val)}`); });
bot.command('al', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; await executeTrade('manuel'); });
bot.command('pozisyonlar', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; const rows = db.prepare('SELECT * FROM trades ORDER BY id DESC LIMIT 10').all(); if (!rows.length) return ctx.reply('📭 İşlem yok.'); const lines = rows.map(r => `${r.created_at} · ${r.combo} · ${r.contracts} · Net: ${fmtUsd(r.net_pnl || 0)} · ${r.execution_time_ms}ms` + (r.rebalance_success ? ' · 🔄 Rebalans' : '') + (r.flattened ? ' · 🛡️ Flatten' : '')); await ctx.reply(['📋 <b>İşlemler</b>', SEP, ...lines].join('\n'), { parse_mode: 'HTML' }); });
bot.command('pnl', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; const stats = await analytics.getDetailedStats(); await ctx.reply(`📊 <b>P&L</b>\n${SEP}\n💰 Net: ${fmtUsd(stats.totalPnl)}\n💸 Fee: ${fmtUsd(stats.totalFees)}\n📈 İşlem: ${stats.totalTrades} | Win: ${stats.wins}\n🎯 Win Rate: %${stats.winRate.toFixed(1)}\n⚡ Ort. Süre: ${stats.avgTime.toFixed(0)}ms`, { parse_mode: 'HTML' }); });
bot.command('dur', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; setTradeMode('manuel'); await ctx.reply('🛑 Durduruldu.'); });
bot.command('sifirla', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; const arg = ctx.match?.trim(); if (arg !== 'onayla') return ctx.reply('⚠️ Bu komut TÜM işlem geçmişini, PnL istatistiklerini ve açık pozisyon takibini kalıcı olarak siler.\nKalshi/Polymarket\'teki gerçek pozisyonlarınızı ETKİLEMEZ, sadece bu botun kaydını sıfırlar.\n\nOnaylamak için: <code>/sifirla onayla</code>', { parse_mode: 'HTML' }); db.prepare('DELETE FROM trades').run(); db.prepare('DELETE FROM opportunities').run(); positionManager.positions.clear(); positionManager.history = []; executedThisHour.clear(); state.consecutiveFailures = 0; await ctx.reply('✅ Tüm PnL, işlem geçmişi ve pozisyon takibi sıfırlandı.'); });
bot.command('esik', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; const arg = ctx.match?.trim(); if (!arg) return ctx.reply(`📊 Eşik: %${getThresholdPct()}`); const val = parseFloat(arg.replace(',', '.')); if (Number.isNaN(val) || val < 0 || val > 50) return ctx.reply('⚠️ Geçersiz.'); setConfig('threshold_pct', val); await ctx.reply(`✅ Eşik: %${val}`); });
bot.command('ping', async (ctx) => { if (ctx.chat.id !== GROUP_ID) return; const t0 = Date.now(); const sent = await ctx.reply('🏓 Ping...'); await ctx.api.editMessageText(ctx.chat.id, sent.message_id, `🏓 Pong! (${Date.now() - t0}ms)`); });
bot.on('callback_query:data', async (ctx) => { if (ctx.chat?.id !== GROUP_ID) return; if (ctx.callbackQuery.data !== 'execute_trade') return; await ctx.answerCallbackQuery({ text: 'İşlem gönderiliyor...' }); await executeTrade('buton').catch(e => console.error('Hata:', e.message)); });

function getThresholdPct() { return parseFloat(getConfig('threshold_pct', '1')); }
function getThresholdCost() { return 1 - getThresholdPct() / 100; }
function getTradeMode() { return getConfig('trade_mode', 'manuel'); }
function setTradeMode(m) { setConfig('trade_mode', m); }
function getTradeSizeUsd() { return parseFloat(getConfig('trade_size_usd', '0')); }
function setTradeSizeUsd(v) { setConfig('trade_size_usd', v); }

class FastWebSocket {
  constructor(url, name, options = {}) { this.url = url; this.name = name; this.headers = options.headers; this.ws = null; this.retries = 0; this.maxRetries = 10; this.listeners = new Map(); }
  connect() { this.ws = new WebSocket(this.url, this.headers ? { headers: this.headers } : undefined); this.ws.on('open', () => { console.log(`${this.name} WS bağlandı`); this.retries = 0; this.emit('connected'); }); this.ws.on('message', (data) => this.emit('message', data)); this.ws.on('close', () => { console.log(`${this.name} WS kapandı`); this.reconnect(); }); this.ws.on('error', () => {}); }
  reconnect() { if (this.retries >= this.maxRetries) return; this.retries++; setTimeout(() => this.connect(), 1000 * this.retries); }
  on(event, callback) { if (!this.listeners.has(event)) this.listeners.set(event, []); this.listeners.get(event).push(callback); }
  emit(event, data) { const cbs = this.listeners.get(event); if (cbs) cbs.forEach(cb => cb(data)); }
  send(data) { if (this.ws && this.ws.readyState === WebSocket.OPEN) this.ws.send(typeof data === 'string' ? data : JSON.stringify(data)); }
}
const polyWs = new FastWebSocket(POLY_MARKET_WS, 'Polymarket');
const kalshiWs = new FastWebSocket(KALSHI_WS_URL, 'Kalshi', { headers: kalshiSign('GET', '/trade-api/ws/v2') });
let kalshiCmdId = 1;
let kalshiSubscribedTicker = null;
function subscribeKalshiTicker(ticker) { if (!ticker || ticker === kalshiSubscribedTicker) return; kalshiWs.send({ id: kalshiCmdId++, cmd: 'subscribe', params: { channels: ['ticker'], market_tickers: [ticker] } }); kalshiSubscribedTicker = ticker; }
kalshiWs.on('connected', () => { kalshiSubscribedTicker = null; if (state.kalshi?.ticker) subscribeKalshiTicker(state.kalshi.ticker); });
const binanceWs = new FastWebSocket(BINANCE_WS, 'Binance');
polyWs.on('message', async (data) => {
  const raw = data.toString(); if (raw === 'PONG') return;
  try {
    const msg = JSON.parse(raw); const events = Array.isArray(msg) ? msg : [msg];
    for (const ev of events) {
      if (ev.event_type === 'book') { const assetId = String(ev.asset_id || ''); if (assetId) cacheManager.set(`poly:orderbook:${assetId}`, { bids: ev.bids, asks: ev.asks }, 2000); continue; }
      if (ev.event_type !== 'last_trade_price' && ev.event_type !== 'price_change') continue;
      const assetId = String(ev.asset_id || ''); if (!state.poly || !assetId) continue;
      const price = parseFloat(ev.price ?? (ev.best_bid ?? ev.best_ask)); if (Number.isNaN(price)) continue;
      if (assetId === String(state.poly.upTokenId)) state.poly.upPrice = price; else if (assetId === String(state.poly.downTokenId)) state.poly.downPrice = price; else continue;
      await evaluateArbitrage();
    }
  } catch (e) {}
});
kalshiWs.on('message', async (data) => {
  try { const msg = JSON.parse(data.toString()); if (msg.type !== 'ticker') return; const m = msg.msg || {}; if (!state.kalshi || m.market_ticker !== state.kalshi.ticker) return; const yes = m.yes_ask_dollars != null ? parseFloat(m.yes_ask_dollars) : null; const no = m.no_ask_dollars != null ? parseFloat(m.no_ask_dollars) : null; if (yes != null) state.kalshi.yesPrice = yes; if (no != null) state.kalshi.noPrice = no; await evaluateArbitrage(); } catch (e) {}
});
binanceWs.on('message', (data) => { try { const msg = JSON.parse(data); const price = msg.data?.p || msg.p; if (price) { state.btcPrice = Number(price); volatilityTracker.addPrice(Number(price)); } } catch (e) {} });
setInterval(async () => { try { const r = await fetch(BINANCE_TICKER); const d = await r.json(); if (d.price) { state.btcPrice = Number(d.price); volatilityTracker.addPrice(Number(d.price)); } } catch (e) {} }, 10000);

async function refreshMarkets() {
  const hk = nowHourKey();
  try {
    const openPrice = await fetchHourOpenPrice();
    const [poly, kalshi] = await Promise.all([ findPolyHourlyEvent(), findKalshiHourlyMarket(openPrice) ]);
    if (!poly || !kalshi) return;
    const check = validateStrikeAlignment(openPrice, kalshi.strike, poly.endDate, kalshi.closeTime);
    if (!check.valid) { console.log(`refreshMarkets STRIKE RED: ${check.reasons.join(', ')}`); }
    state.hourKey = hk; state.polyStrike = openPrice; state.poly = poly; state.kalshi = kalshi; state.lastStrikeCheck = check;
    subscribeKalshiTicker(kalshi.ticker);
    polyWs.send({ assets_ids: [poly.upTokenId, poly.downTokenId], type: 'market', custom_feature_enabled: true });
    await evaluateArbitrage();
  } catch (e) { console.error('refreshMarkets:', e.message); }
}

async function start() {
  console.log('🚀 ULTIMATE Arbitraj Botu başlatılıyor...');
  polyWs.connect(); kalshiWs.connect(); binanceWs.connect();
  await refreshMarkets();
  setInterval(refreshMarkets, 60 * 1000);
  await bot.start();
}
process.on('uncaughtException', (e) => console.error('uncaughtException:', e));
process.on('unhandledRejection', (e) => console.error('unhandledRejection:', e));
start();
