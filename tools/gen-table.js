#!/usr/bin/env node
/**
 * 用区间 DP 生成 / 校验 homo.js 的 Nums 表
 *
 *   node tools/gen-table.js [homo.js] [数字串]
 *
 * 语法: 每个数字用且只用一次 + 保持原顺序 + 可拼接 + - * / + 括号 + 一元负号
 * 代价: 渲染后的字符数（保留 3 种优先级形态，保证最优）
 * 输出: 可达值统计、表里缺失/可缩短的条目、以及增补后的实测效果
 */
const fs = require("fs");

const file = process.argv[2] || "homo.js";
const BASE = process.argv[3] || "114514";
const src = fs.readFileSync(file, "utf8");

const table = {};
for (const m of src.matchAll(/^\s*"?(⑨|\d+)"?\s*:\s*"([^"]*)"/gm)) table[m[1]] = m[2];

// ---------- 有理数 ----------
function gcd(a, b) { while (b) { const t = a % b; a = b; b = t; } return a < 0n ? -a : a; }
function F(n, d) { if (d === undefined) d = 1n; if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; this.n = n / g; this.d = d / g; }
F.prototype.key = function () { return this.n + "/" + this.d; };
const fadd = (a, b) => new F(a.n * b.d + b.n * a.d, a.d * b.d);
const fsub = (a, b) => new F(a.n * b.d - b.n * a.d, a.d * b.d);
const fmul = (a, b) => new F(a.n * b.n, a.d * b.d);
const fdiv = (a, b) => (b.n === 0n ? null : new F(a.n * b.d, a.d * b.n));

// ---------- 最小字符数区间 DP，3 种优先级形态 ----------
const PREC = [3, 1, 2]; // 0 原子 / 1 加减 / 2 乘除
function wrapT(t, cls, pop, right) {
  const pp = (pop === "+" || pop === "-") ? 1 : 2;
  return (PREC[cls] < pp || (right && PREC[cls] === pp && (pop === "-" || pop === "/"))) ? "(" + t + ")" : t;
}
function dpChars(s) {
  const n = s.length;
  const dp = Array.from({ length: n + 1 }, () => Array(n + 1).fill(null));
  const slot = (m, k) => { let v = m.get(k); if (!v) { v = [undefined, undefined, undefined]; m.set(k, v); } return v; };
  for (let i = 0; i < n; i++) for (let j = i + 1; j <= n; j++) dp[i][j] = new Map();
  for (let i = 0; i < n; i++) for (let j = i + 1; j <= n; j++) {
    const t = s.slice(i, j);
    if (t.length > 1 && t[0] === "0") continue;
    slot(dp[i][j], new F(BigInt(t)).key())[0] = t;
  }
  for (let len = 2; len <= n; len++) for (let i = 0; i + len <= n; i++) {
    const j = i + len, cur = dp[i][j];
    for (let k = i + 1; k < j; k++) {
      const L = [...dp[i][k].entries()], R = [...dp[k][j].entries()];
      for (const la of L) for (const rb of R) {
        const a = new F(BigInt(la[0].split("/")[0]), BigInt(la[0].split("/")[1]));
        const b = new F(BigInt(rb[0].split("/")[0]), BigInt(rb[0].split("/")[1]));
        const cands = [["+", fadd(a, b)], ["-", fsub(a, b)], ["*", fmul(a, b)], ["/", fdiv(a, b)]];
        for (const c of cands) {
          const op = c[0], v = c[1];
          if (!v) continue;
          let best;
          for (let ca = 0; ca < 3; ca++) {
            if (!la[1][ca]) continue;
            const left = wrapT(la[1][ca], ca, op, false);
            for (let cb = 0; cb < 3; cb++) {
              if (!rb[1][cb]) continue;
              const t = left + op + wrapT(rb[1][cb], cb, op, true);
              if (!best || t.length < best.length) best = t;
            }
          }
          if (!best) continue;
          const cls = (op === "+" || op === "-") ? 1 : 2;
          const sl = slot(cur, v.key());
          if (!sl[cls] || best.length < sl[cls].length) sl[cls] = best;
        }
      }
    }
    for (const kv of [...cur.entries()]) for (let cls = 0; cls < 3; cls++) {
      if (!kv[1][cls]) continue;
      const t = kv[1][cls], negT = cls === 1 ? "-(" + t + ")" : "-" + t, negCls = cls === 1 ? 0 : cls;
      const sl = slot(cur, new F(-BigInt(kv[0].split("/")[0]), BigInt(kv[0].split("/")[1])).key());
      if (!sl[negCls] || negT.length < sl[negCls].length) sl[negCls] = negT;
    }
  }
  return dp;
}

// ---------- finisher 的清理规则（与 homo.js 保持一致，含一元负号修复） ----------
function cleanup(expr) {
  while (expr.match(/[\*|\/]\([^\+\-\(\)]+\)/)) expr = expr.replace(/([\*|\/])\(([^\+\-\(\)]+)\)/, (m, a, b) => a + b);
  while (expr.match(/[\d)][\+\-]\([^\(\)]+\)[\+\-|)]/)) expr = expr.replace(/([\d)])([\+\-])\(([^\(\)]+)\)([\+\-|)])/, (m, a, b, c, d) => a + b + c + d);
  while (expr.match(/[\d)][\+\-]\(([^\(\)]+)\)$/)) expr = expr.replace(/([\d)])([\+\-])\(([^\(\)]+)\)$/, (m, a, b, c) => a + b + c);
  if (expr.match(/^\([^\(\)]+?\)$/)) expr = expr.replace(/^\(([^\(\)]+)\)$/, "$1");
  return expr.replace(/\+-/g, "-");
}

function makeHomo(Nums) {
  const keys = Object.keys(Nums).map(Number).filter(x => x > 0);
  const getMinDiv = (num) => { for (let i = keys.length - 1; i >= 0; i--) if (num >= keys[i]) return keys[i]; };
  const demolish = (num) => {
    if (typeof num !== "number") return "";
    if (!Number.isFinite(num)) return "x";
    if (num < 0) return "(⑨)*(" + demolish(-num) + ")";
    if (!Number.isInteger(num)) return "x";
    if (Nums[num]) return String(num);
    const div = getMinDiv(num);
    return (div + "*(" + demolish(Math.floor(num / div)) + ")+(" + demolish(num % div) + ")").replace(/\*\(1\)|\+\(0\)$/g, "");
  };
  return (num) => cleanup(demolish(num).replace(/\d+|⑨/g, (n) => Nums[n]).replace("^", "**"));
}

// ---------- 主流程 ----------
const t0 = Date.now();
const dp = dpChars(BASE);
const ms = Date.now() - t0;
const total = dp[0][BASE.length];
const ints = new Map();
for (const kv of total.entries()) {
  const num = BigInt(kv[0].split("/")[0]);
  if (!kv[0].endsWith("/1") || num < 0n || num > 1000000n) continue;
  let best, len = 1e9;
  for (let cls = 0; cls < 3; cls++) {
    if (!kv[1][cls]) continue;
    const t = kv[1][cls], full = cls === 1 ? "(" + t + ")" : t;   // 顶层是加减就必须包起来，才能安全替换
    if (full.length < len) { len = full.length; best = full; }
  }
  if (best) ints.set(Number(num), best);
}
console.log('数字串 "' + BASE + '"');
console.log("  可达值 " + total.size + " 个，非负整数 " + ints.size + " 个，耗时 " + ms + " ms");
console.log("  手写表 " + Object.keys(table).length + " 项；可达整数中表里没有的 " + [...ints.keys()].filter(k => !table[String(k)]).length + " 个");

const base = makeHomo(table);
const add = [], shorten = [];
for (const kv of ints) {
  const key = String(kv[0]);
  const shown = cleanup(kv[1]);
  const cur = table[key] !== undefined ? cleanup(table[key]) : base(kv[0]);
  if (shown.length < cur.length) {
    // 存的是带安全括号的完整形式；shown 只用于展示和比较（cleanup 会剥掉最外层括号）
    if (table[key] === undefined) add.push([kv[0], cur, kv[1]]);
    else shorten.push([kv[0], cur, kv[1]]);
  }
}
console.log("  建议新增 " + add.length + " 条，建议缩短已有条目 " + shorten.length + " 条");
const show = (title, list) => {
  console.log("  " + title + "（示例）:");
  for (const r of list.slice(0, 8)) console.log("    " + r[0] + ": " + r[1] + "  ->  " + r[2]);
};
show("新增", add);
show("缩短", shorten);

const next = Object.assign({}, table);
for (const r of add) next[String(r[0])] = r[2];
for (const r of shorten) next[String(r[0])] = r[2];
const hNew = makeHomo(next);
const NS = [];
for (let n = 1; n <= 20000; n++) NS.push(n);
let lenA = 0, lenB = 0, better = 0, worse = 0, bad = 0;
for (const n of NS) {
  const a = base(n), b = hNew(n);
  lenA += a.length; lenB += b.length;
  if (b.length < a.length) better++; else if (b.length > a.length) worse++;
  let v; try { v = eval("(" + b + ")"); } catch (e) { v = NaN; }
  if (v !== n) bad++;
}
console.log("  增补后在 1..20000 的实测: 平均 " + (lenA / NS.length).toFixed(3) + " -> " + (lenB / NS.length).toFixed(3) +
            " 字符；变短 " + better + " 条，变长 " + worse + " 条，求值错误 " + bad + " 条");
if (process.argv.indexOf("--emit") > 0) {
  console.log("\n// 可直接并入 Nums 的条目");
  for (const r of add.concat(shorten)) console.log('  ' + r[0] + ': "' + r[2] + '",');
}
