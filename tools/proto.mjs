// 恶臭数字论证器 · 求解器原型验证脚本 v2
// 变更（相对 v1）：
//   1. 一元负号加入闭包（对齐旧表语义，补齐 86 个 miss 键）
//   2. 面额扩展：大值两两乘积作为多块面额（自身块数 cd 计入代价）
//   3. cost 双指标：块数优先、表达式长度 tie-break（消除 ×1 / 1^x 冗余）
//   4. 验证器对分数加相对容差（浮点求值误差非生成错误）
//   5. 对拍标准按旧键实际块数（数字字符数/6）分级验证
// 运行：node tools/proto.mjs

import { readFileSync } from 'node:fs';

const DIGITS = [1, 1, 4, 5, 1, 4];
const LIMIT = 2 ** 53;
const BIG_LIMIT = BigInt(LIMIT);

// ---------- 基础数论工具 ----------

const gcdInt = (a, b) => {
  a = Math.abs(a); b = Math.abs(b);
  while (b) { const t = a % b; a = b; b = t; }
  return a || 1;
};

const isqrt = (n) => {
  if (n < 0) return null;
  let x = Math.floor(Math.sqrt(n));
  while (x * x > n) x--;
  while ((x + 1) * (x + 1) <= n) x++;
  return x;
};

const safeMul = (a, b) =>
  Math.abs(a) > LIMIT / Math.abs(b) ? null : a * b;
const safeAdd = (a, b) =>
  (a > 0 && b > 0 && a > LIMIT - b) || (a < 0 && b < 0 && a < -LIMIT - b) ? null : a + b;

const norm = (p, q) => {
  if (q < 0) { p = -p; q = -q; }
  const g = gcdInt(p, q);
  return [p / g, q / g];
};

// ---------- 四则 ----------

const fAdd = (p1, q1, p2, q2) => {
  const d = safeMul(q1, q2); if (d === null) return null;
  const a = safeMul(p1, q2); if (a === null) return null;
  const b = safeMul(p2, q1); if (b === null) return null;
  const n = safeAdd(a, b); if (n === null) return null;
  return norm(n, d);
};
const fSub = (p1, q1, p2, q2) => fAdd(p1, q1, -p2, q2);
const fMul = (p1, q1, p2, q2) => {
  const n = safeMul(p1, p2); if (n === null) return null;
  const d = safeMul(q1, q2); if (d === null) return null;
  return norm(n, d);
};
const fDiv = (p1, q1, p2, q2) => (p2 === 0 ? null : fMul(p1, q1, p2, q2));

// ---------- 一元算子（extended） ----------

const FACT = [1, 1];
for (let i = 2; i <= 18; i++) FACT[i] = FACT[i - 1] * i;

const uNeg = (p, q) => [-p, q];
const uFact = (p, q) => (q === 1 && p >= 0 && p <= 18) ? [FACT[p], 1] : null;
const uSqrt = (p, q) => {
  if (p < 0) return null;
  const sp = isqrt(p), sq = isqrt(q);
  return (sp * sp === p && sq * sq === q) ? [sp, sq] : null;
};
// floor 的精确整数实现：JS % 是截断语义，负数须再减 1 才是 floor
const uFloor = (p, q) => {
  if (q === 1) return null;
  const r = p % q;
  const n = (p - r) / q - (r < 0 ? 1 : 0);
  return [n, 1];
};

const UNARY = [
  { f: uFact, wrap: (e) => `(${e})!`, vwrap: (e) => `F(${e})` },
  { f: uSqrt, wrap: (e) => `√(${e})`, vwrap: (e) => `SQ(${e})` },
  { f: uFloor, wrap: (e) => `⌊${e}⌋`, vwrap: (e) => `FL(${e})` },
];

const bPow = (p1, q1, p2, q2) => {
  if (q2 !== 1 || Math.abs(p2) > 40) return null;
  let e = p2;
  if (e === 0) return p1 === 0 ? null : [1, 1];
  if (p1 === 0) return e > 0 ? [0, 1] : null;
  let base = [p1, q1];
  if (e < 0) { base = [q1, p1]; e = -e; }
  let neg = false;
  if (base[0] < 0) {
    if (base[1] !== 1) return null;
    base[0] = -base[0];
    neg = (e % 2) === 1;
  }
  let P = 1, Q = 1;
  for (let i = 0; i < e; i++) {
    P = safeMul(P, base[0]); if (P === null) return null;
    Q = safeMul(Q, base[1]); if (Q === null) return null;
  }
  return norm(neg ? -P : P, Q);
};

// ---------- 区间 DP ----------

const buildTable = (extended) => {
  const t0 = performance.now();
  const n = DIGITS.length;
  const S = Array.from({ length: n }, () => Array(n));

  const setIfShorter = (m, k, rec) => {
    const cur = m.get(k);
    if (!cur || rec.e.length < cur.e.length) { m.set(k, rec); return !cur; }
    return false;
  };

  const close = (m) => {
    const stack = [...m.keys()];
    while (stack.length) {
      const k = stack.pop();
      const { p, q, e, v } = m.get(k);
      for (const u of UNARY) {
        const r = u.f(p, q);
        if (!r) continue;
        const nk = r[0] + '/' + r[1];
        if (setIfShorter(m, nk, { p: r[0], q: r[1], e: u.wrap(e), v: u.vwrap(v) }))
          stack.push(nk);
      }
    }
  };

  // 一元负：仅对正整数取负（对齐旧表"前导负"语义），产物不回流一元闭包（防 neg∘floor 链爆炸）
  const closeNeg = (m) => {
    for (const [k, rec] of [...m]) {
      if (rec.q === 1 && rec.p > 0) {
        const nk = (-rec.p) + '/1';
        setIfShorter(m, nk, { p: -rec.p, q: 1, e: `-(${rec.e})`, v: `-(${rec.v})` });
      }
    }
  };

  const combine = (m, A, B) => {
    const put = (r, e, v) => setIfShorter(m, r[0] + '/' + r[1], { p: r[0], q: r[1], e, v });
    for (const a of A.values()) for (const b of B.values()) {
      let r = fAdd(a.p, a.q, b.p, b.q);
      if (r) put(r, `(${a.e})+(${b.e})`, `(${a.v})+(${b.v})`);
      r = fSub(a.p, a.q, b.p, b.q);
      if (r) put(r, `(${a.e})-(${b.e})`, `(${a.v})-(${b.v})`);
      r = fMul(a.p, a.q, b.p, b.q);
      if (r) put(r, `(${a.e})*(${b.e})`, `(${a.v})*(${b.v})`);
      r = fDiv(a.p, a.q, b.p, b.q);
      if (r) put(r, `(${a.e})/(${b.e})`, `(${a.v})/(${b.v})`);
      if (extended) {
        r = bPow(a.p, a.q, b.p, b.q);
        if (r) put(r, `(${a.e})^(${b.e})`, `POW(${a.v},${b.v})`);
      }
    }
  };

  for (let i = 0; i < n; i++) {
    const m = new Map();
    const lit = DIGITS[i];
    m.set(lit + '/1', { p: lit, q: 1, e: String(lit), v: String(lit) });
    if (extended) close(m);
    closeNeg(m);
    S[i][i] = m;
  }
  for (let len = 2; len <= n; len++) {
    for (let i = 0, j = i + len - 1; j < n; i++, j = i + len - 1) {
      const m = new Map();
      const cat = Number(DIGITS.slice(i, j + 1).join(''));
      m.set(cat + '/1', { p: cat, q: 1, e: String(cat), v: String(cat) });
      if (extended) close(m);
      for (let k = i; k < j; k++) combine(m, S[i][k], S[k + 1][j]);
      if (extended) close(m);
      closeNeg(m);
      S[i][j] = m;
    }
  }
  return { full: S[0][n - 1], ms: performance.now() - t0 };
};

// ---------- eval 验证环境 ----------
// SQ 用容差版：精确有理 √(1/1936) 类值在浮点链路下不是精确平方数（如 44^-2 ≠ 精确 1/1936）
const F = (n) => { if (n < 0 || n !== Math.floor(n) || n > 170) throw new Error('bad !'); let r = 1; for (let i = 2; i <= n; i++) r *= i; return r; };
const SQ = (x) => {
  if (x < 0) throw new Error('bad √');
  const r = Math.sqrt(x), rr = Math.round(r);
  return Math.abs(r - rr) <= 1e-9 * Math.max(1, Math.abs(rr)) ? rr : r;
};
const FL = Math.floor;
const POW = (a, b) => a ** b;
const evalExpr = (v) => (new Function('F', 'SQ', 'FL', 'POW', `"use strict";return (${v});`))(F, SQ, FL, POW);
// 分数容差放宽到 1e-6 相对：灾难性抵消（如 1-(1+4·5^-14)）会把相对误差放大到 ~1e-7 量级，属浮点本性
const relClose = (a, b) => Math.abs(a - b) <= 1e-6 * Math.max(Math.abs(a), Math.abs(b), 1e-300);

// ---------- 旧表 ----------

const loadOldTable = () => {
  const src = readFileSync(new URL('../homo.js', import.meta.url), 'utf8');
  const m = new Map();
  for (const [, k, e] of src.matchAll(/(?:^|\n)\t(\d+|⑨): "([^"]+)"/g)) m.set(k, e);
  return m;
};

// ---------- 最短表示求解器 ----------
//
// 图模型：节点 = 非负整数（BigInt）；目标 = 最小化 (块数, 表达式长度) 字典序
//   乘法边   n = d·q + r     代价 cd(d) + c(q) + c(r)
//   借位边   n = d·(q+1) − (d−r)
//   加减边   n = v ± m       代价 cd(v) + c(m)（限与 n 最近 K 个面额，深度受限）
// 面额 = 单块值 ∪ 大值两两乘积（多块面额）

const buildSolver = (table) => {
  // 面额字段：val = BigInt 值, cd = 自身块数, pe = 展示表达式, ev = eval 表达式
  const best = new Map();
  for (const { p, q, e, v } of table.values()) {
    if (q !== 1 || p < 0 || p > LIMIT) continue;
    const k = BigInt(p);
    const cur = best.get(k);
    if (!cur || e.length < cur.pe.length) best.set(k, { val: k, cd: 1, pe: e, ev: v });
  }
  // 乘积面额：top-64 单块值两两相乘（≤ 2^53）
  const singles = [...best.values()].filter((x) => x.val > 1n)
    .sort((a, b) => (a.val < b.val ? 1 : a.val > b.val ? -1 : 0)).slice(0, 64);
  for (let i = 0; i < singles.length; i++) {
    for (let j = i; j < singles.length; j++) {
      const r1 = singles[i], r2 = singles[j];
      const prod = r1.val * r2.val;
      if (prod > BIG_LIMIT) continue;
      const cur = best.get(prod);
      const cd = r1.cd + r2.cd;
      if (!cur || cd < cur.cd || (cd === cur.cd && r1.pe.length + r2.pe.length + 6 < cur.pe.length))
        best.set(prod, { val: prod, cd, pe: `(${r1.pe})*(${r2.pe})`, ev: `(${r1.ev})*(${r2.ev})` });
    }
  }
  // 求解器专用精选面额（降序）：大值优先截断 + 小整数全保留
  const allVals = [...best.values()]
    .sort((a, b) => (a.val < b.val ? 1 : a.val > b.val ? -1 : 0));
  const SMALL = 4096n, TOP = 12288;
  const vals = allVals.filter((x) => x.val < SMALL || x.val <= allVals[Math.min(TOP, allVals.length - 1)].val);
  const byVal = new Map(allVals.map((x) => [x.val, x]));

  // 块数下界：最大面额为基数的对数阶
  const maxVal = allVals[0]?.val ?? 1n;
  const logMax = Math.log2(Number(maxVal) || 2);
  const lb = (m) => {
    if (m === 0n) return 0;
    if (m <= maxVal) return 1;
    return 1 + Math.ceil(Math.log2(Number(m)) / (logMax || 1));
  };

  const memo = new Map();
  let budget = 60000;
  const deadline = performance.now() + 4000; // 时间保险丝：超时后全部走贪心
  const timedOut = () => performance.now() > deadline;

  const mulSafe = (s) => /[+\-]/.test(s) ? `(${s})` : s; // 乘法操作数需防 +-

  // 二分：vals 降序中找 ≤ key 的最大面额下标
  const bisect = (key) => {
    let lo = 0, hi = vals.length - 1, r = -1;
    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      if (vals[mid].val <= key) { r = mid; hi = mid - 1; } else lo = mid + 1;
    }
    return r;
  };

  const solveRec = (nn, depth) => {
    const hitM = memo.get(nn);
    if (hitM) return hitM;
    const hit = byVal.get(nn);
    if (hit) { const r = { c: hit.cd, len: hit.pe.length, e: hit.pe, v: hit.ev }; memo.set(nn, r); return r; }
    if (--budget < 0 || timedOut()) { const g = greedy(nn); memo.set(nn, g); return g; }

    let bestR = greedy(nn); // 以贪心解为初始上界（分支限界）
    const ubC = () => bestR.c;
    const consider = (cand) => {
      if (!cand) return;
      if (cand.c < bestR.c || (cand.c === bestR.c && cand.len < bestR.len)) bestR = cand;
    };

    // 乘法边（面额降序 = d 递减 = q 递增，lb 剪枝随遍历单调转劣，可提前终止）
    for (const { val: d, cd, pe, ev } of vals) {
      if (d <= 1n) break;
      if (d > nn) continue;
      const q = nn / d, r = nn % d;
      if (q < 1n) continue;
      const lbQ = lb(q) + (r === 0n ? 0 : lb(r));
      if (cd + lbQ >= ubC()) continue;
      if (lb(q) + lb(r === 0n ? 0n : r) + cd > 60) continue;
      const s1 = solveRec(q, depth);
      if (r === 0n) {
        consider({ c: cd + s1.c, len: cd + s1.len + pe.length + 1, e: `${pe}*${mulSafe(s1.e)}`, v: `${ev}*${mulSafe(s1.v)}` });
      } else {
        const s2 = solveRec(r, depth);
        consider({
          c: cd + s1.c + s2.c, len: cd + s1.len + s2.len + pe.length + 2,
          e: `${pe}*${mulSafe(s1.e)}+(${s2.e})`, v: `${ev}*${mulSafe(s1.v)}+(${s2.v})`,
        });
        if (r * 2n > d && q + 1n < d) { // 借位
          const sQ = solveRec(q + 1n, depth), sB = solveRec(d - r, depth);
          consider({
            c: cd + sQ.c + sB.c, len: cd + sQ.len + sB.len + pe.length + 2,
            e: `${pe}*${mulSafe(sQ.e)}-(${sB.e})`, v: `${ev}*${mulSafe(sQ.v)}-(${sB.v})`,
          });
        }
      }
    }

    // 加减边：二分定位 n，取左右最近 K 个面额
    if (depth > 0) {
      const K = 64;
      const idx = bisect(nn);
      for (let t = Math.max(0, idx - 1); t <= Math.min(vals.length - 1, idx + K); t++) {
        const x = vals[t];
        if (x.val === 0n || x.val === nn) continue;
        const diff = x.val > nn ? x.val - nn : nn - x.val;
        if (lb(diff) + x.cd >= ubC()) continue;
        const sub = solveRec(diff, depth - 1);
        const head = x.val > nn ? `${x.pe}-(${sub.e})` : `${x.pe}+(${sub.e})`;
        const headV = x.val > nn ? `${x.ev}-(${sub.v})` : `${x.ev}+(${sub.v})`;
        consider({ c: x.cd + sub.c, len: x.cd + sub.len + x.pe.length + 1, e: head, v: headV });
      }
    }

    memo.set(nn, bestR);
    return bestR;
  };

  const greedy = (nn) => {
    const hit = byVal.get(nn);
    if (hit) return { c: hit.cd, len: hit.pe.length, e: hit.pe, v: hit.ev };
    const idx = bisect(nn);
    const pick = idx >= 0 && vals[idx].val > 1n ? vals[idx] : byVal.get(1n);
    if (!pick || pick.val === 1n) { const one = byVal.get(1n); return { c: one.cd, len: one.pe.length, e: one.pe, v: one.ev }; }
    const q = nn / pick.val, r = nn % pick.val;
    if (r === 0n) {
      const s = greedy(q);
      return { c: pick.cd + s.c, len: pick.pe.length + s.len, e: `${pick.pe}*${mulSafe(s.e)}`, v: `${pick.ev}*${mulSafe(s.v)}` };
    }
    const s1 = greedy(q), s2 = greedy(r);
    return { c: pick.cd + s1.c + s2.c, len: pick.pe.length + s1.len + s2.len, e: `${pick.pe}*${mulSafe(s1.e)}+(${s2.e})`, v: `${pick.ev}*${mulSafe(s1.v)}+(${s2.v})` };
  };

  return (n) => solveRec(BigInt(n), 2);
};

// ---------- 主流程 ----------

const fmt = (x) => x.toLocaleString('en-US');

console.log('=== baseline（四则 + 一元负） ===');
const base = buildTable(false);
console.log(`值集 ${fmt(base.full.size)}, 耗时 ${base.ms.toFixed(0)}ms`);

console.log('\n=== extended（+ ! ⌊⌋ √ ^） ===');
const ext = buildTable(true);
console.log(`值集 ${fmt(ext.full.size)}, 耗时 ${ext.ms.toFixed(0)}ms`);

for (const [name, t] of [['baseline', base], ['extended', ext]]) {
  let ints = 0, negs = 0, fracs = 0, maxI = 0;
  for (const { p, q } of t.full.values()) {
    if (q === 1) { ints++; if (p > maxI) maxI = p; } else fracs++;
  }
  console.log(`${name}: 整数 ${fmt(ints)}（最大 ${fmt(maxI)}）, 分数 ${fmt(fracs)}`);
}

// 旧表对拍（按旧键块数分级）
const old = loadOldTable();
const oldBlocks = (e) => Math.ceil(((e.match(/\d/g) || []).length) / 6);
{
  let single = 0, singleMiss = [], multi = 0, multiBad = [];
  for (const [k, e] of old) {
    if (k === '⑨') continue;
    const n = Number(k);
    if (ext.full.has(n + '/1')) {
      if (oldBlocks(e) === 1) single++;
      else multi++;
      continue;
    }
    if (oldBlocks(e) === 1) singleMiss.push(n);
    else multiBad.push(n);
  }
  console.log(`\n旧表对拍 extended: 单块键命中 ${single}/${single + singleMiss.length}, 多块键单块化 ${multi}/${multi + multiBad.length}`);
  console.log(`  单块 miss: ${singleMiss.join(', ') || '无'}`);
  console.log(`  多块键(合法不命中): ${multiBad.join(', ') || '无'}`);
}

// extended 抽查求值
{
  let checked = 0, bad = [];
  for (const [k, { p, q, v }] of ext.full) {
    if (!/[FSPL]/.test(v)) continue;
    try {
      const ev = evalExpr(v);
      if (!(q === 1 ? ev === p : relClose(ev, p / q))) bad.push([k, v, ev]);
    } catch (err) { bad.push([k, v, String(err)]); }
    if (++checked >= 500) break;
  }
  console.log(`extended 扩展算子表达式抽查: ${checked}, 异常 ${bad.length}`);
  for (const b of bad.slice(0, 5)) console.log('  BAD', ...b);
}

// ---------- 求解器样例 ----------
console.log('\n=== 求解器样例（blocks, 长度） ===');
const solveBase = buildSolver(base.full);
const solveExt = buildSolver(ext.full);
const samples = [1919, 1919810, 229027, 1145141919810, 9007199254740991];
for (const n of samples) {
  const rb = solveBase(n), re_ = solveExt(n);
  const vb = evalExpr(rb.v), ve = evalExpr(re_.v);
  console.log(`n=${fmt(n)}: baseline ${vb === n ? '✓' : '✗'} ${rb.c}块/${rb.len}字 | extended ${ve === n ? '✓' : '✗'} ${re_.c}块/${re_.len}字`);
  console.log('  base :', rb.e.slice(0, 150));
  console.log('  ext  :', re_.e.slice(0, 150));
}

// 旧贪心块数对比
const oldGreedyBlocks = (nn) => {
  const keys = [...old.keys()].filter((k) => k !== '⑨').map(Number).sort((a, b) => b - a);
  const cnt = (n) => {
    if (old.has(String(n))) return 1;
    const d = keys.find((x) => x <= n) ?? 1;
    const q = Math.floor(n / d), r = n % d;
    return 1 + cnt(q) + (r ? cnt(r) : 0);
  };
  return cnt(nn);
};
console.log('\n=== 块数对比（n / 旧贪心 / baseline / extended） ===');
for (const n of samples)
  console.log(`${fmt(n)}: ${oldGreedyBlocks(n)} / ${solveBase(n).c} / ${solveExt(n).c}`);

// 采样质量统计
{
  let oldSum = 0, baseSum = 0, extSum = 0, N = 0;
  for (let n = 1; n <= 100000; n += 499) {
    oldSum += oldGreedyBlocks(n);
    baseSum += solveBase(n).c;
    extSum += solveExt(n).c;
    N++;
  }
  console.log(`\n[1,1e5] 采样 ${N} 个: 平均块数 旧贪心 ${(oldSum / N).toFixed(2)} → baseline ${(baseSum / N).toFixed(2)} → extended ${(extSum / N).toFixed(2)}`);
}
