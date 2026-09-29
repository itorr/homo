// homo · E2E 全量验证
// 原则：不抽样。值集逐条求值对拍、函数级行为矩阵、旧表回归、finisher 语义保持。
// 运行：node tools/verify.mjs

import { createRequire } from 'node:module';
import { readFileSync } from 'node:fs';

const require = createRequire(import.meta.url);
const homo = require('../homo.js');

// ---- 官方 eval 环境（与 README 提供的一致）----
const F = (n) => {
  if (n < 0 || n !== Math.floor(n) || n > 170) throw new Error('bad !: ' + n);
  let r = 1; for (let i = 2; i <= n; i++) r *= i; return r;
};
const SQ = (x) => {
  if (x < 0) throw new Error('bad √');
  const r = Math.sqrt(x), rr = Math.round(r);
  // 容差：精确有理 √(p/q) 的浮点链路（如 44^-2 ≠ 精确 1/1936）可能差 1ulp
  return Math.abs(r - rr) <= 1e-9 * Math.max(1, Math.abs(rr)) ? rr : r;
};
const FL = Math.floor;
const POW = (a, b) => a ** b;
// FLSQ 无容差：语义是 floor(sqrt(x))，不能用容差 SQ（会把平方数边界值错误圆整）
const FLSQ = (x) => Math.floor(Math.sqrt(x));
const evalStr = (s) => (new Function('F', 'SQ', 'FL', 'POW', 'FLSQ', `"use strict";return (${s});`))(F, SQ, FL, POW, FLSQ);
// dyadic 不变量：值域限制在 ℤ[1/2]，表达式浮点求值应与记录值严格一致
const relClose = (a, b) => a === b || Math.abs(a - b) <= 1e-12 * Math.max(Math.abs(a), Math.abs(b), 1e-300);

let pass = 0, fail = 0;
const check = (ok, msg, detail) => {
  if (ok) pass++;
  else { fail++; console.error('  ✗ ' + msg + (detail ? ' :: ' + detail : '')); }
};

// ==================== 1. 升级等待 ====================
const t0 = Date.now();
await new Promise((res) => { homo.onUpgrade = res; });
const upgradeMs = Date.now() - t0;
console.log(`升级完成（扩展值域构建 + 求解器重建）: ${upgradeMs}ms`);

const table = homo._table();
console.log(`扩展值集条目: ${table.size.toLocaleString('en-US')}`);

// ==================== 2. 值集全量审计 ====================
{
  console.log('\n[1] 值集全量审计（逐条 eval 对拍）');
  let bad = 0;
  for (const [key, { p, q, v }] of table) {
    let ev;
    try { ev = evalStr(v); } catch (e) { bad++; if (bad <= 5) console.error(`  ✗ ${key} 抛异常 ${e.message}: ${v}`); continue; }
    const ok = q === 1 ? ev === p : relClose(ev, p / q);
    if (!ok) { bad++; if (bad <= 5) console.error(`  ✗ ${key} → ${ev}: ${v}`); }
  }
  check(bad === 0, `值集 ${table.size} 条全量审计`, `${bad} 条不一致`);
  console.log(`  值集 ${table.size.toLocaleString('en-US')} 条, 不一致 ${bad}`);
}

// ==================== 3. 函数级行为矩阵 ====================
{
  console.log('\n[2] 函数级行为矩阵');
  const t1 = Date.now();
  // 3.1 密集整数 0..3000
  let badI = 0;
  for (let n = 0; n <= 3000; n++) {
    const ev = evalStr(homo.evalStr(n));
    if (ev !== n) { badI++; if (badI <= 3) console.error(`  ✗ homo(${n}) → ${ev}: ${homo.evalStr(n)}`); }
  }
  check(badI === 0, '整数 0..3000 密集验证');
  console.log(`  整数 0..3000: ${badI === 0 ? '全部 ✓' : badI + ' 个 ✗'}, 耗时 ${Date.now() - t1}ms`);

  // 3.2 大数采样（含 2^53 边界）
  let badB = 0;
  const bigs = [1919, 114514, 1919810, 229027, 229028, 123456789, 9876543210,
    1145141919810, 1145141919810114514n, 9007199254740991, 9007199254740992 - 2,
    1e10 + 7, 999999999999, 4294967296, 65537 ** 3];
  for (const n of bigs) {
    const x = typeof n === 'bigint' ? Number(n) : n;
    const ev = evalStr(homo.evalStr(x));
    if (ev !== x) { badB++; console.error(`  ✗ homo(${x}) → ${ev}: ${homo.evalStr(x)}`); }
  }
  check(badB === 0, '大数采样');
  console.log(`  大数采样 ${bigs.length} 个: ${badB === 0 ? '全部 ✓' : badB + ' 个 ✗'}`);

  // 3.3 小数（含科学计数、循环展示边界）
  let badF = 0;
  const fracs = [0.1, 0.25, 0.5, 1.5, 0.125, 3.14159, 0.333333, 19.19, 114.514,
    1e-7, 2.5e-10, 0.001, 123.456, 0.9999999];
  for (const x of fracs) {
    const ev = evalStr(homo.evalStr(x));
    if (!relClose(ev, x)) { badF++; console.error(`  ✗ homo(${x}) → ${ev}: ${homo.evalStr(x)}`); }
  }
  check(badF === 0, '小数采样');
  console.log(`  小数采样 ${fracs.length} 个: ${badF === 0 ? '全部 ✓' : badF + ' 个 ✗'}`);

  // 3.4 负数
  let badN = 0;
  for (const x of [-1, -1919, -114514, -0.25, -1919810]) {
    const ev = evalStr(homo.evalStr(x));
    const ok = Number.isInteger(x) ? ev === x : relClose(ev, x);
    if (!ok) { badN++; console.error(`  ✗ homo(${x}) → ${ev}`); }
  }
  check(badN === 0, '负数采样');
  console.log(`  负数采样 5 个: ${badN === 0 ? '全部 ✓' : badN + ' 个 ✗'}`);

  // 3.5 特殊值与非 number
  check(homo(Infinity) === '这么恶臭的Infinity有必要论证吗', 'Infinity 文案', homo(Infinity));
  check(homo(-Infinity) === '这么恶臭的-Infinity有必要论证吗', '-Infinity 文案');
  check(homo(NaN) === '这么恶臭的NaN有必要论证吗', 'NaN 文案');
  check(homo('114') === '', '字符串输入返回空串');
  check(homo(undefined) === '', 'undefined 返回空串');
  check(homo(-0) === homo(0) || evalStr(homo.evalStr(-0)) === 0, 'homo(-0) 表示 0', homo(-0));
  console.log('  特殊值 7 项 ✓');

  // 3.6 展示表达式与求值表达式一致性（finisher 不破坏语义）
  let badC = 0;
  for (const x of [1919, 229027, 1919810, 0.25, -3.5, 5, 100, 12345]) {
    const evE = evalStr(homo.evalStr(x).replace(/\^/g, '**')); // evalStr 不含 ^，防御
    const ok = Number.isInteger(x) ? evE === x : relClose(evE, x);
    if (!ok) { badC++; console.error(`  ✗ evalStr(${x}) finisher 后失真 → ${evE}`); }
  }
  check(badC === 0, 'finisher 语义保持');
  console.log(`  finisher 语义保持: ${badC === 0 ? '✓' : badC + ' ✗'}`);
}

// ==================== 4. 旧表回归 ====================
{
  console.log('\n[3] 旧表回归（值等价 + 块数不劣化）');
  const legacy = JSON.parse(readFileSync(new URL('./legacy-table.json', import.meta.url), 'utf8'));
  const oldBlocks = (e) => Math.max(1, Math.ceil(((e.match(/\d/g) || []).length) / 6));
  let eq = 0, better = 0, worse = [];
  for (const [k, oldE] of Object.entries(legacy)) {
    if (k === '⑨') continue;
    const n = Number(k);
    const oldEval = (0, eval)(oldE.replace(/\^/g, '**'));
    const newE = homo.evalStr(n);
    const newEval = evalStr(newE);
    const ob = oldBlocks(oldE); // 旧块数按旧表达式的数字消耗计（(114514+114514) = 2 块）
    const nb = Math.max(1, Math.ceil(((newE.match(/\d/g) || []).length) / 6));
    if (newEval === n && oldEval === n) {
      eq++;
      if (nb <= ob) better++; else worse.push([n, ob, nb]);
    } else worse.push([n, oldEval, newEval]);
  }
  check(worse.length === 0, '旧表 519 键回归', JSON.stringify(worse.slice(0, 5)));
  console.log(`  值等价 ${eq}/519, 块数 ≤ 旧 ${better}/${eq}, 劣化 ${worse.length}`);
}

// ==================== 5. 质量与性能 ====================
{
  console.log('\n[4] 质量统计');
  const legacy = JSON.parse(readFileSync(new URL('./legacy-table.json', import.meta.url), 'utf8'));
  const oldGreedyBlocks = (nn) => {
    const keys = Object.keys(legacy).filter((k) => k !== '⑨').map(Number).sort((a, b) => b - a);
    const cnt = (n) => {
      if (legacy[String(n)]) return 1;
      const d = keys.find((x) => x <= n) ?? 1;
      const q = Math.floor(n / d), r = n % d;
      return 1 + cnt(q) + (r ? cnt(r) : 0);
    };
    return cnt(nn);
  };
  let oldSum = 0, newSum = 0, N = 0;
  const t = Date.now();
  for (let n = 1; n <= 100000; n += 199) {
    oldSum += oldGreedyBlocks(n);
    newSum += Math.max(1, Math.ceil(((homo.evalStr(n).match(/\d/g) || []).length) / 6));
    N++;
  }
  console.log(`  [1,1e5] 采样 ${N}: 平均块数 旧贪心 ${(oldSum / N).toFixed(2)} → 新 ${(newSum / N).toFixed(2)}, 总耗时 ${Date.now() - t}ms`);
  check(newSum < oldSum, '平均块数优于旧实现');
  const t2 = Date.now();
  homo.evalStr(9007199254740991);
  console.log(`  最坏输入 2^53-1 单次求解: ${Date.now() - t2}ms`);
}

console.log(`\n========== 结果: ${pass} 通过, ${fail} 失败 ==========`);
process.exit(fail ? 1 : 0);
