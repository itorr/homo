/*! homo · 恶臭数字论证器
 * 将任意数字分解为由 114514 数字序列（顺序固定、每块用尽全部六个数字）构成的算式。
 *
 * 算法（数论视角，详见 docs/researches/01-number-theory-solver.md）：
 *   1. 值域生成 —— 区间动态规划：S(i,j) 为子串 d_i..d_j 经全部切分/四则/一元算子
 *      （! ⌊⌋ √ 前导负）与整数次幂可精确表出的有理数集。全程 Number 对上的
 *      精确分数运算（每步 gcd 归约 + 溢出界检查），无浮点误差。
 *   2. 最短表示 —— 将"任意大整数"形式化为带面额的最短表示问题（coin problem 的
 *      加权推广）：节点为整数，边为带余除法（含借位变体）与最近面额加减，
 *      分支限界求 (块数, 表达式长度) 字典序最优，贪心解为初始上界与兜底。
 *   3. 非整数 —— 按十进制语义解析为最简分数 p/q，分别求解后拼接 (p)/(q)。
 *
 * 加载策略：先同步构建四则基线（~15ms），再异步升级扩展算子值域（! ⌊⌋ √ ^，
 * ~600ms），完成后触发 homo.onUpgrade 回调供 UI 重算。
 *
 * homo(num)            → 展示用表达式（含 ^ ! √ ⌊⌋ 记号）
 * homo.evalStr(num)    → 可直接 eval 的表达式（需先注入 F/SQ/FL/POW，见 README）
 * homo.onUpgrade       → 升级完成回调（可赋值）
 */
const homo = ((DIGITS) => {
	'use strict';

	const LIMIT = 2 ** 53;          // IEEE-754 精确整数界限
	const BIG_LIMIT = BigInt(LIMIT);

	// ==================== §1 数论工具 ====================

	// 欧几里得辗转相除（Number 精确域：|a|,|b| < 2^53）
	const gcdInt = (a, b) => {
		a = Math.abs(a); b = Math.abs(b);
		while (b) { const t = a % b; a = b; b = t; }
		return a || 1;
	};

	// 精确整数平方根（Math.sqrt 在 2^53 附近失真，Newton 精化兜底）
	const isqrt = (n) => {
		if (n < 0) return null;
		let x = Math.floor(Math.sqrt(n));
		while (x * x > n) x--;
		while ((x + 1) * (x + 1) <= n) x++;
		return x;
	};

	// 防溢出安全运算：越界返回 null
	// 值域证据：最终值 |p| ≤ 229028（见研究文档 §2.3），未归约中间积不超过 LIMIT²，
	// 故每步运算前检查即可保证全程精确
	const safeMul = (a, b) =>
		Math.abs(b) === 0 ? 0 : (Math.abs(a) > LIMIT / Math.abs(b) ? null : a * b);
	const safeAdd = (a, b) =>
		(a > 0 && b > 0 && a > LIMIT - b) || (a < 0 && b < 0 && a < -LIMIT - b) ? null : a + b;

	const gcdBig = (a, b) => {
		if (a < 0n) a = -a;
		if (b < 0n) b = -b;
		while (b) { const t = a % b; a = b; b = t; }
		return a || 1n;
	};

	// ==================== §2 精确分数四则 ====================
	// 值域限制在二进分数环 ℤ[1/2]（dyadic rationals）：分母为 2 的幂的分数与整数
	// 在 IEEE-754 下封闭，组合全程零舍入 ⇒ 值集条目与表达式浮点求值严格一致。
	// 非二进分母的中间分数（如 11/4514）一律丢弃——由此损失的"分数→整数"转换
	// 由复合算子 divFloor / floorSqrt 以纯整数运算补回（见 §3）。

	// 2 的幂判定：不可用位运算（JS & 将操作数截断为 32 位，q > 2^32 时误判）
	const isDyadic = (q) => {
		if (q <= 0) return false;
		while (q % 2 === 0) q /= 2;
		return q === 1;
	};

	// 分数规范化 + 二进性检查：非 dyadic 返回 null
	const normD = (p, q) => {
		if (q < 0) { p = -p; q = -q; }
		if (!isDyadic(q)) return null;
		const g = gcdInt(p, q);
		return [p / g, q / g];
	};
	// 仅整数的规范化（一元算子出口）
	const normI = (p) => [p, 1];

	const fAdd = (p1, q1, p2, q2) => {
		const d = safeMul(q1, q2); if (d === null) return null;
		const a = safeMul(p1, q2); if (a === null) return null;
		const b = safeMul(p2, q1); if (b === null) return null;
		const n = safeAdd(a, b); if (n === null) return null;
		return normD(n, d);
	};
	const fSub = (p1, q1, p2, q2) => fAdd(p1, q1, -p2, q2);
	const fMul = (p1, q1, p2, q2) => {
		const n = safeMul(p1, p2); if (n === null) return null;
		const d = safeMul(q1, q2); if (d === null) return null;
		return normD(n, d);
	};
	// (p1/q1) ÷ (p2/q2) = (p1·q2) / (q1·p2)
	const fDiv = (p1, q1, p2, q2) =>
		p2 === 0 ? null : fMul(p1, q1, q2, p2);

	// ⌊(p1/q1) ÷ (p2/q2)⌋：纯整数实现。
	// 浮点商与最近整数的距离 ≥ 1/|q1·p2|，相对舍入误差 ≤ |n|·2⁻⁵²/|d|（n 为未约分分子），
	// 故 |n| < 2⁵¹ 时 floor 无歧义（安全系数 2）
	const bDivFloor = (p1, q1, p2, q2) => {
		if (p2 === 0) return null;
		const n = safeMul(p1, q2); if (n === null || Math.abs(n) > LIMIT / 4) return null;
		const d = safeMul(q1, p2); if (d === null) return null;
		const r = n % d;
		const t = (n - r) / d; // 截断商
		// floor 修正：非整除且商为负（分子分母异号）时 floor = trunc − 1
		return normI(r !== 0 && (n < 0) !== (d < 0) ? t - 1 : t);
	};

	// ==================== §3 一元算子 ====================

	// n! 上限 18：18! ≈ 6.4e15 < 2^53 保持精确
	const FACT = [1, 1];
	for (let i = 2; i <= 18; i++) FACT[i] = FACT[i - 1] * i;

	// √ 仅保留有理结果 ⇔ 分子分母均为完全平方数（p/q 已最简）
	const uFact = (p, q) => (q === 1 && p >= 0 && p <= 18) ? [FACT[p], 1] : null;
	const uSqrt = (p, q) => {
		if (p < 0) return null;
		const sp = isqrt(p), sq = isqrt(q);
		return (sp * sp === p && sq * sq === q) ? [sp, sq] : null;
	};
	// ⌊p/q⌋ 的精确整数实现：JS % 为截断语义，负数须再减 1 才是 floor
	const uFloor = (p, q) => {
		if (q === 1) return null;
		const r = p % q;
		return normI((p - r) / q - (r < 0 ? 1 : 0));
	};

	// ⌊√n⌋（n 非完全平方数，n > 15 才有产出意义）：浮点 √n 距最近平方数边界
	// ≥ 1/(2√n) >> ulp（n ≤ 2⁵¹），floor 无歧义；非 dyadic 域的取整语义由此补回。
	// 标记 aux：产物不回流组合（防值集平方爆炸），仅作最终面额。
	const uFloorSqrt = (p, q) => {
		if (q !== 1 || p < 16 || p > LIMIT / 4) return null;
		const s = isqrt(p);
		return s * s === p ? null : [s, 1];
	};

	const UNARY = [
		{ f: uFact, wrap: (e) => `(${e})!`, vwrap: (e) => `F(${e})` },
		{ f: uSqrt, wrap: (e) => `√(${e})`, vwrap: (e) => `SQ(${e})` },
		{ f: uFloor, wrap: (e) => `⌊${e}⌋`, vwrap: (e) => `FL(${e})` },
		{ f: uFloorSqrt, aux: true, wrap: (e) => `⌊√(${e})⌋`, vwrap: (e) => `FLSQ(${e})` },
	];

	// 整数次幂。底限定整数：浮点 pow 对分数底走 exp/log 路径不保证精确；
	// 整数底整数指按乘法语义精确（值 ≤ 2⁵³ 由溢出界检查保证）。
	// 负指数仅 2 的幂底可保 dyadic（2⁻ᵏ）。
	const bPow = (p1, q1, p2, q2) => {
		if (q2 !== 1 || Math.abs(p2) > 40 || q1 !== 1) return null;
		let e = p2;
		if (e === 0) return p1 === 0 ? null : [1, 1]; // 0^0 语义不明，跳过
		if (p1 === 0) return e > 0 ? [0, 1] : null;
		const neg = p1 < 0 && (Math.abs(e) % 2) === 1; // 负指数时 e%2 为 -1，须取绝对值判奇偶
		const bp = Math.abs(p1);
		if (bp !== 1 && Math.log2(bp) * Math.abs(e) > 53) return null;
		let P = 1, Q = 1;
		const k = Math.abs(e);
		for (let i = 0; i < k; i++) {
			if (e > 0) { P = safeMul(P, bp); if (P === null) return null; }
			else { Q = safeMul(Q, bp); if (Q === null) return null; }
		}
		if (e < 0 && bp !== 1 && !isDyadic(Q)) return null;
		return [neg ? -P : P, Q];
	};

	// ==================== §4 区间 DP 值域生成 ====================
	//
	// S(i,j) = 用子串 d_i..d_j 可精确表出的有理数 → 最短表达式（双轨：展示/求值）
	// 双池架构：
	//   core —— 四则/幂的组合结果 + 一元闭包（! √ ⌊⌋）+ 前导负。回流：作为更大
	//           区间组合的操作数（完备性：任何表达式树按"一元子树落入某一侧"取分裂点）
	//   aux  —— divFloor/FLSQ 复合算子产物。不回流（防值集平方爆炸），仅作最终面额
	// 最终值域 = 顶层 core ∪ aux（冲突取更短表达式）。

	const buildTable = (extended) => {
		const n = DIGITS.length;
		const S = Array.from({ length: n }, () => Array(n));

		const setIfShorter = (m, k, rec) => {
			const cur = m.get(k);
			if (!cur || rec.e.length < cur.e.length) { m.set(k, rec); return !cur; }
			return false;
		};

		// 一元闭包至不动点（值域有界 ⇒ 收敛）；FLSQ 落 aux
		const close = (core, aux) => {
			const stack = [...core.keys()];
			while (stack.length) {
				const k = stack.pop();
				const { p, q, e, v } = core.get(k);
				for (const u of UNARY) {
					const r = u.f(p, q);
					if (!r) continue;
					const rec = { p: r[0], q: r[1], e: u.wrap(e), v: u.vwrap(v) };
					if (u.aux) setIfShorter(aux, r[0] + '/' + r[1], rec);
					else if (setIfShorter(core, r[0] + '/' + r[1], rec)) stack.push(r[0] + '/' + r[1]);
				}
			}
		};

		// 前导负：仅 core 正整数，产物回流 core（作操作数），不回流一元闭包（防链爆炸）
		const closeNeg = (core) => {
			for (const rec of [...core.values()]) {
				if (rec.q === 1 && rec.p > 0)
					setIfShorter(core, (-rec.p) + '/1',
						{ p: -rec.p, q: 1, e: `-(${rec.e})`, v: `-(${rec.v})` });
			}
		};

		const combine = (core, aux, A, B) => {
			for (const a of A.core.values()) for (const b of B.core.values()) {
				let r = fAdd(a.p, a.q, b.p, b.q);
				if (r) setIfShorter(core, r[0] + '/' + r[1],
					{ p: r[0], q: r[1], e: `(${a.e})+(${b.e})`, v: `(${a.v})+(${b.v})` });
				r = fSub(a.p, a.q, b.p, b.q);
				if (r) setIfShorter(core, r[0] + '/' + r[1],
					{ p: r[0], q: r[1], e: `(${a.e})-(${b.e})`, v: `(${a.v})-(${b.v})` });
				r = fMul(a.p, a.q, b.p, b.q);
				if (r) setIfShorter(core, r[0] + '/' + r[1],
					{ p: r[0], q: r[1], e: `(${a.e})*(${b.e})`, v: `(${a.v})*(${b.v})` });
				r = fDiv(a.p, a.q, b.p, b.q);
				if (r) setIfShorter(core, r[0] + '/' + r[1],
					{ p: r[0], q: r[1], e: `(${a.e})/(${b.e})`, v: `(${a.v})/(${b.v})` });
				r = bDivFloor(a.p, a.q, b.p, b.q);
				if (r) setIfShorter(aux, r[0] + '/' + r[1],
					{ p: r[0], q: r[1], e: `⌊(${a.e})/(${b.e})⌋`, v: `FL((${a.v})/(${b.v}))` });
				if (extended) {
					r = bPow(a.p, a.q, b.p, b.q);
					if (r) setIfShorter(core, r[0] + '/' + r[1],
						{ p: r[0], q: r[1], e: `(${a.e})^(${b.e})`, v: `POW(${a.v},${b.v})` });
				}
			}
		};

		for (let i = 0; i < n; i++) {
			const core = new Map(), aux = new Map();
			const lit = DIGITS[i];
			core.set(lit + '/1', { p: lit, q: 1, e: String(lit), v: String(lit) });
			if (extended) close(core, aux);
			closeNeg(core);
			S[i][i] = { core, aux };
		}
		for (let len = 2; len <= n; len++) {
			for (let i = 0, j = i + len - 1; j < n; i++, j = i + len - 1) {
				const core = new Map(), aux = new Map();
				const cat = Number(DIGITS.slice(i, j + 1).join(''));
				core.set(cat + '/1', { p: cat, q: 1, e: String(cat), v: String(cat) });
				if (extended) close(core, aux);
				for (let k = i; k < j; k++) combine(core, aux, S[i][k], S[k + 1][j]);
				if (extended) close(core, aux);
				closeNeg(core);
				S[i][j] = { core, aux };
			}
		}
		// 合并顶层双池：冲突取更短表达式
		const { core, aux } = S[0][n - 1];
		const full = new Map(aux);
		for (const [k, rec] of core)
			if (!full.has(k) || rec.e.length < full.get(k).e.length) full.set(k, rec);
		return full;
	};

	// ==================== §5 最短表示求解器 ====================
	//
	// 图模型：节点 = 非负整数（BigInt）；最小化 (块数, 表达式长度) 字典序
	//   乘法边  n = d·q + r          代价 cd(d) + c(q) + c(r)
	//   借位边  n = d·(q+1) − (d−r)  余数接近 d 时的减法变体
	//   加减边  n = v ± m            代价 cd(v) + c(m)（最近 K 个面额，深度受限）
	// 面额 = 单块整数 ∪ 大值两两乘积（多块面额，cd 计入因子块数）
	// 分支限界：贪心解为初始上界，块数下界 lb(m) = 1 + ⌈log_{maxVal} m⌉ 剪枝；
	// 时间/节点保险丝超限后全程退化为贪心（1 ∈ 面额 ⇒ 永远有解，最坏不劣于旧实现）

	const buildSolver = (table) => {
		// 面额字段：val = BigInt 值, cd = 自身块数, e = 展示表达式, v = 求值表达式
		const best = new Map();
		for (const { p, q, e, v } of table.values()) {
			if (q !== 1 || p < 0 || p > LIMIT) continue;
			const k = BigInt(p);
			const cur = best.get(k);
			if (!cur || e.length < cur.e.length) best.set(k, { val: k, cd: 1, e, v });
		}
		// 多块乘积面额：top 大值 × {小值面额 ∪ top 大值}。
		// 覆盖两类关键组合："大×大"（radix 上限）与"大×小"（如 114514×2 = 229028）。
		const bigs = [...best.values()].filter((x) => x.val > 1n)
			.sort((a, b) => (a.val < b.val ? 1 : a.val > b.val ? -1 : 0)).slice(0, 24);
		const smalls = [...best.values()].filter((x) => x.val > 1n && x.val < 4096n)
			.sort((a, b) => (a.val < b.val ? 1 : a.val > b.val ? -1 : 0));
		const addProd = (r1, r2) => {
			const prod = r1.val * r2.val;
			if (prod > BIG_LIMIT) return;
			const cur = best.get(prod);
			const cd = r1.cd + r2.cd;
			if (!cur || cd < cur.cd)
				best.set(prod, { val: prod, cd, e: `(${r1.e})*(${r2.e})`, v: `(${r1.v})*(${r2.v})` });
		};
		for (let i = 0; i < bigs.length; i++) {
			for (let j = i; j < bigs.length; j++) addProd(bigs[i], bigs[j]);
			for (const s of smalls) addProd(bigs[i], s);
		}
		const allVals = [...best.values()]
			.sort((a, b) => (a.val < b.val ? 1 : a.val > b.val ? -1 : 0));
		// 求解器扫描集：小面额全保留 + top 大面额截断（防扩展值域下全量扫描超时）
		const SMALL = 4096n, TOP = 12288;
		const vals = allVals.filter((x, i) =>
			x.val < SMALL || (allVals.length <= TOP || i < TOP));
		const byVal = new Map(allVals.map((x) => [x.val, x]));

		const maxVal = allVals.length ? allVals[0].val : 1n;
		const logMax = Math.max(1, Math.log2(Number(maxVal) || 2));
		const lb = (m) => {
			if (m === 0n) return 0;
			if (m <= maxVal) return 1;
			return 1 + Math.ceil(Math.log2(Number(m)) / logMax);
		};

		const memo = new Map();
		let budget = 60000;
		const deadline = Date.now() + 5000; // 时间保险丝
		const outOfBudget = () => budget < 0 || Date.now() > deadline;

		const mulSafe = (s) => /[+\-]/.test(s) ? `(${s})` : s; // 乘法操作数防 +-

		// 降序 vals 中二分找 ≤ key 的最大面额下标
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
			if (hit) { const r = { c: hit.cd, len: hit.e.length, e: hit.e, v: hit.v }; memo.set(nn, r); return r; }
			if (outOfBudget()) { const g = greedy(nn); memo.set(nn, g); return g; }
			budget--;

			let bestR = greedy(nn); // 初始上界（分支限界）
			const ubC = () => bestR.c;
			const consider = (cand) => {
				if (cand && (cand.c < bestR.c || (cand.c === bestR.c && cand.len < bestR.len))) bestR = cand;
			};

			// 乘法边：面额降序 ⇒ q 递增 ⇒ 下界单调转劣
			for (const { val: d, cd, e: de, v: dv } of vals) {
				if (d <= 1n) break;
				if (d > nn) continue;
				const q = nn / d, r = nn % d;
				if (q < 1n) continue;
				if (cd + lb(q) + (r === 0n ? 0 : lb(r)) >= ubC()) continue;
				const s1 = solveRec(q, depth);
				if (r === 0n) {
					consider({
						c: cd + s1.c, len: cd + s1.len + de.length + 1,
						e: `${mulSafe(de)}*${mulSafe(s1.e)}`, v: `${mulSafe(dv)}*${mulSafe(s1.v)}`,
					});
				} else {
					const s2 = solveRec(r, depth);
					consider({
						c: cd + s1.c + s2.c, len: cd + s1.len + s2.len + de.length + 2,
						e: `${mulSafe(de)}*${mulSafe(s1.e)}+(${s2.e})`, v: `${mulSafe(dv)}*${mulSafe(s1.v)}+(${s2.v})`,
					});
					if (r * 2n > d && q + 1n < d) { // 借位
						const sQ = solveRec(q + 1n, depth), sB = solveRec(d - r, depth);
						consider({
							c: cd + sQ.c + sB.c, len: cd + sQ.len + sB.len + de.length + 2,
							e: `${mulSafe(de)}*${mulSafe(sQ.e)}-(${sB.e})`, v: `${mulSafe(dv)}*${mulSafe(sQ.v)}-(${sB.v})`,
						});
					}
				}
			}

			// 加减边：自 idx 起双侧指针按 |n−x| 升序全扫（覆盖"半值面额"如 114514+114514）；
			// |n−x| 单调不减 ⇒ 块数下界单调不减 ⇒ 满足剪枝即可终止
			if (depth > 0) {
				const idx = bisect(nn);
				let li = idx, ri = idx + 1;
				while (li >= 0 || ri < vals.length) {
					const dl = li >= 0 ? nn - vals[li].val : null;
					const dr = ri < vals.length ? vals[ri].val - nn : null;
					let x;
					if (dl !== null && (dr === null || dl <= dr)) x = vals[li--];
					else x = vals[ri++];
					if (x.val === 0n || x.val === nn) continue;
					const diff = x.val > nn ? x.val - nn : nn - x.val;
					if (x.cd + lb(diff) >= ubC()) break;
					const sub = solveRec(diff, depth - 1);
					const head = x.val > nn ? `${x.e}-(${sub.e})` : `${x.e}+(${sub.e})`;
					const headV = x.val > nn ? `${x.v}-(${sub.v})` : `${x.v}+(${sub.v})`;
					consider({ c: x.cd + sub.c, len: x.cd + sub.len + x.e.length + 1, e: head, v: headV });
				}
			}

			memo.set(nn, bestR);
			return bestR;
		};

		// 贪心兜底（等价于旧实现 demolish 的整数部分，但带借位变体）
		const greedy = (nn) => {
			const hit = byVal.get(nn);
			if (hit) return { c: hit.cd, len: hit.e.length, e: hit.e, v: hit.v };
			const idx = bisect(nn);
			let pick = null;
			if (idx >= 0 && vals[idx].val > 1n) pick = vals[idx];
			if (!pick) { const one = byVal.get(1n); return { c: 1, len: one.e.length, e: one.e, v: one.v }; }
			const q = nn / pick.val, r = nn % pick.val;
			if (r === 0n) {
				const s = greedy(q);
				return {
					c: pick.cd + s.c, len: pick.e.length + s.len + 1,
					e: `${mulSafe(pick.e)}*${mulSafe(s.e)}`, v: `${mulSafe(pick.v)}*${mulSafe(s.v)}`,
				};
			}
			const s1 = greedy(q), s2 = greedy(r);
			return {
				c: pick.cd + s1.c + s2.c, len: pick.e.length + s1.len + s2.len + 2,
				e: `${mulSafe(pick.e)}*${mulSafe(s1.e)}+(${s2.e})`, v: `${mulSafe(pick.v)}*${mulSafe(s1.v)}+(${s2.v})`,
			};
		};

		return (nn) => solveRec(nn, 2);
	};

	// ==================== §6 输入语义 ====================

	// 十进制语义解析：Number → 最简分数 [p, q]（BigInt）
	// String(number) 给出最短 round-trip 十进制表示，尊重用户输入意图（0.1 → 1/10 而非其二进制精确值）
	const parseDecimalToFraction = (num) => {
		const m = /^(-?)(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?$/.exec(String(num));
		if (!m) return null;
		const [, sign, ip, fp = '', ex = '0'] = m;
		const shift = Number(ex) - fp.length;
		let p = BigInt(ip + fp), q = 1n;
		if (shift >= 0) p *= 10n ** BigInt(shift);
		else q = 10n ** BigInt(-shift);
		if (sign === '-') p = -p;
		const g = gcdBig(p, q);
		return [p / g, q / g];
	};

	// ==================== §7 finisher（输出净化） ====================
	// AST 级打印器：解析 → 恒等简化 → 按优先级上下文打印最少括号。
	// （正则方案只能覆盖运算符单侧，左侧/嵌套/一元外层的冗余括号均无法触达。）
	// 注：块内每个数字必须消耗，×1 类"恒等式"是子区间数字消耗的合法方式，
	// 不能在生成端跳过；冗余仅在输出端化简。

	const tokenize = (s) => {
		const toks = [];
		for (let i = 0; i < s.length;) {
			const c = s[i];
			if (c >= '0' && c <= '9') {
				let j = i;
				while (j < s.length && s[j] >= '0' && s[j] <= '9') j++;
				toks.push({ t: 'num', v: s.slice(i, j) });
				i = j;
			} else if ('+-*/^()!'.includes(c) || c === '√' || c === '⌊' || c === '⌋') {
				toks.push({ t: c });
				i++;
			} else if (c === ' ') i++;
			else throw new Error('bad token: ' + c);
		}
		return toks;
	};

	// 递归下降解析（优先级：+ − < * / < ^（右结合）< 一元负 < 后缀 ! < √ ⌊⌋ 原子）
	let _toks, _pos;
	const parseExpr = () => {
		let l = parseTerm();
		while (_toks[_pos] && (_toks[_pos].t === '+' || _toks[_pos].t === '-'))
			l = { t: 'bin', op: _toks[_pos++].t, l, r: parseTerm() };
		return l;
	};
	const parseTerm = () => {
		let l = parsePow();
		while (_toks[_pos] && (_toks[_pos].t === '*' || _toks[_pos].t === '/'))
			l = { t: 'bin', op: _toks[_pos++].t, l, r: parsePow() };
		return l;
	};
	// 幂：右结合（指数递归取幂层级，可含前导负）
	const parsePow = () => {
		const b = parseUnary();
		if (_toks[_pos] && _toks[_pos].t === '^') {
			_pos++;
			return { t: 'bin', op: '^', l: b, r: parsePow() };
		}
		return b;
	};
	const parseUnary = () =>
		_toks[_pos] && _toks[_pos].t === '-'
			? (_pos++, { t: 'neg', x: parseUnary() })
			: parsePostfix();
	const parsePostfix = () => {
		let x = parsePrimary();
		while (_toks[_pos] && _toks[_pos].t === '!') { _pos++; x = { t: 'fac', x }; }
		return x;
	};
	const parsePrimary = () => {
		const p = _toks[_pos];
		if (!p) throw new Error('unexpected end');
		if (p.t === 'num') { _pos++; return { t: 'num', v: p.v }; }
		if (p.t === '(') {
			_pos++;
			const e = parseExpr();
			if (!_toks[_pos] || _toks[_pos++].t !== ')') throw new Error('expect )');
			return e;
		}
		if (p.t === '√') {
			_pos++;
			if (!_toks[_pos] || _toks[_pos++].t !== '(') throw new Error('expect ( after √');
			const e = parseExpr();
			if (!_toks[_pos] || _toks[_pos++].t !== ')') throw new Error('expect )');
			return { t: 'sqrt', x: e };
		}
		if (p.t === '⌊') {
			_pos++;
			const e = parseExpr();
			if (!_toks[_pos] || _toks[_pos++].t !== '⌋') throw new Error('expect ⌋');
			return { t: 'floor', x: e };
		}
		throw new Error('unexpected ' + p.t);
	};
	const parseAst = (s) => {
		_toks = tokenize(s); _pos = 0;
		const ast = parseExpr();
		if (_pos !== _toks.length) throw new Error('trailing tokens');
		return ast;
	};

	// 恒等简化（全部为精确恒等，无浮点陷阱）
	const simplify = (n) => {
		if (n.t === 'bin' || n.t === 'fac' || n.t === 'sqrt' || n.t === 'floor') {
			if (n.l) { n.l = simplify(n.l); n.r = simplify(n.r); }
			else n.x = simplify(n.x);
		} else if (n.t === 'neg') n.x = simplify(n.x);
		if (n.t === 'fac') {
			if (n.x.t === 'num' && (n.x.v === '0' || n.x.v === '1')) return { t: 'num', v: '1' };
			return n;
		}
		if (n.t !== 'bin') return n;
		const { op, l, r } = n;
		const isNum = (x, v) => x.t === 'num' && (v === undefined || +x.v === v);
		if (op === '*') {
			if (isNum(l, 1)) return r;
			if (isNum(r, 1)) return l;
			if (isNum(l, 0) || isNum(r, 0)) return { t: 'num', v: '0' };
		} else if (op === '+') {
			if (isNum(l, 0)) return r;
			if (isNum(r, 0)) return l;
		} else if (op === '-') {
			if (isNum(r, 0)) return l;
		} else if (op === '/') {
			if (isNum(r, 1)) return l;
		} else if (op === '^') {
			if (isNum(r, 1)) return l;
			if (isNum(r, 0)) return { t: 'num', v: '1' };
			if (isNum(l, 1)) return { t: 'num', v: '1' };
		}
		return n;
	};

	// 优先级：+ − = 1，* / = 2，一元负 = 0.5（非加法左操作数位置一律加括号），
	// ^ = 3，! / √ / ⌊⌋ / 数字 = 4（原子）
	const pr = (n) =>
		n.t === 'bin' ? (n.op === '+' || n.op === '-' ? 1 : n.op === '^' ? 3 : 2)
		: n.t === 'neg' ? 0.5
		: 4;

	const print = (n) => {
		switch (n.t) {
			case 'num': return n.v;
			// 一元负：操作数原子则裸，否则括号；作父操作数时的隔离由父节点决定
			case 'neg': return '-' + (pr(n.x) === 4 ? print(n.x) : `(${print(n.x)})`);
			case 'fac':
				return (n.x.t === 'num' || n.x.t === 'fac' ? print(n.x) : `(${print(n.x)})`) + '!';
			case 'sqrt': return `√(${print(n.x)})`;
			case 'floor': return `⌊${print(n.x)}⌋`;
			case 'bin': {
				// 左结合（^ 右结合）：左裸需 pr ≥ 父（^ 严格大于），右裸需 pr > 父（^ ≥）
				const p = pr(n);
				const needL = n.op === '^' ? pr(n.l) <= p : pr(n.l) < p;
				const needR = n.op === '^' ? pr(n.r) < p : pr(n.r) <= p;
				// neg 作左操作数：分配律下 + − * / 均值同，仅 ^ 底必须括号；
				// 作右操作数：恒括号（防 a--b，且 a+-b / a*-b 难读）
				const lParen = n.l.t === 'neg' ? n.op === '^' : needL;
				const rParen = n.r.t === 'neg' ? true : needR;
				return (lParen ? `(${print(n.l)})` : print(n.l))
					+ n.op
					+ (rParen ? `(${print(n.r)})` : print(n.r));
			}
		}
	};

	const finisher = (expr) => {
		try {
			return print(simplify(parseAst(expr)));
		} catch (_) {
			return expr; // 解析失败原样返回（eval 轨语义不受影响）
		}
	};

	// ==================== §8 组装 ====================

	let table = buildTable(false);          // 基线：四则 + 前导负（同步，~15ms）
	let solver = buildSolver(table);
	let ready = false;

	const core = (num) => {
		if (typeof num !== 'number') return null;
		if (num !== num || num === Infinity || num === -Infinity)
			return { special: `这么恶臭的${num}有必要论证吗` };
		if (num < 0) {
			const r = core(-num);
			return r && !r.special && { e: `-(${r.e})`, v: `-(${r.v})` };
		}
		if (Number.isInteger(num)) {
			const hit = table.get(num + '/1');
			if (hit) return hit;
			const r = solver(BigInt(num));
			return { e: r.e, v: r.v };
		}
		// 非整数：最简分数
		const pq = parseDecimalToFraction(num);
		if (!pq) return null;
		const [p, q] = pq;
		const hit = table.get(Number(p) + '/' + Number(q));
		if (hit) return hit;
		const P = solver(p), Q = solver(q);
		return { e: `(${P.e})/(${Q.e})`, v: `(${P.v})/(${Q.v})` };
	};

	const main = (num) => {
		const r = core(num);
		if (!r) return '';
		if (r.special) return r.special;
		return finisher(r.e); // 展示轨：AST 解析 + 恒等简化 + 优先级打印
	};
	main.evalStr = (num) => {
		const r = core(num);
		if (!r) return '';
		if (r.special) return r.special;
		return r.v; // 求值轨：生成端模板自带括号，原样返回（函数调用式，AST 打印器不适用）
	};
	main.ready = () => ready;
	main.onUpgrade = null;
	main._table = () => table; // 调试/验证接口（私有，勿依赖）

	// 异步升级：扩展算子值域（! ⌊⌋ √ ^）替换基线
	const upgrade = () => {
		try {
			table = buildTable(true);
			solver = buildSolver(table);
			ready = true;
			if (typeof main.onUpgrade === 'function') main.onUpgrade();
		} catch (_) { /* 保持基线 */ }
	};
	if (typeof setTimeout === 'function') setTimeout(upgrade, 0);

	return main;
})([1, 1, 4, 5, 1, 4]);

if (typeof module === 'object' && module.exports)
	module.exports = homo;
