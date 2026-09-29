# 恶臭数字论证器
一个将任意数字分解成 114514 构成的公式的工具。

数值分解由**数论求解器**完成：区间 DP 运行时生成值域（全程精确有理数运算，值域限制在二进分数环保证浮点求值零舍入），任意大数经分支限界求**最短块数表示**。算法研究与实验数据见 [docs/researches](./docs/researches/01-number-theory-solver.md)。

## 项目首页
[https://lab.magiconch.com/homo/](https://lab.magiconch.com/homo/)

## 引用方式
```HTML
<script src="homo.js"></script>
<script>
let 恶臭 = homo(1919810);
// "(((11)+((4)*((5)!)))*((1)+4))*(((11)-45)*((1)-((4)!)))"
</script>
```
### CDN
```HTML
<script src="https://cdn.jsdelivr.net/gh/itorr/homo@master/homo.js"></script>
```

## API
- `homo(num)` → 展示用表达式，含 `!`、`√`、`⌊⌋`、`^` 记号
- `homo.evalStr(num)` → 可直接 `eval` 的表达式，需先注入下列函数：

```js
const F = n => { let r = 1; for (let i = 2; i <= n; i++) r *= i; return r; }; // n!
const SQ = x => Math.sqrt(x);        // √
const FL = Math.floor;               // ⌊⌋
const POW = (a, b) => a ** b;        // ^
const FLSQ = x => Math.floor(Math.sqrt(x)); // ⌊√⌋
```

- `homo.onUpgrade = fn` → 扩展算子值域（`!` `⌊⌋` `√` `^`，页面加载约 0.7s 后就绪）构建完成时回调，供 UI 重算获得更短表示

## 验证
```sh
node tools/verify.mjs
```
值集 11 万条全量浮点求值对拍 + 行为矩阵 + 旧表回归。

## 仓库地址
[https://github.com/itorr/homo](https://github.com/itorr/homo)

## 协议
MIT
