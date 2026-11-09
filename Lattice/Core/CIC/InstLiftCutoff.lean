import Mathlib
import Lattice.Core.CIC.SubstCompParallel
import Lattice.Core.CIC.InstShiftObstruction

/-!
# `inst_lift_c`：正确指数找到了，缺的**唯一**一条引理被精确定位（阶段 5，第 783 轮）

## 本轮找到的正确形状

**第 782 轮证明「固定指数不闭合」，差值是 `c + 1` 且随 cutoff 增长。那座障碍**直接给出了正确形状**：
既然每进一层绑定，替换深度与 cutoff 都加一，那么把两者**绑在一起**即可 ——
「深度 `c` 的 `liftN`，再加**一次** `lift`，配 cutoff `c`」：

```
inst (liftN c (lift σ)) (shift c 1 t) = shift c 1 (inst (liftN c σ) t)
```

**这是 `ParallelSubst.lean` 里那条 `FlatTerm` 结果的算子化推广：原结果固定 `cutoff = 0`、`lift` 一次；
本形式让 `lift` 的作用量与 cutoff 同步。**

## 六个构造子全部通过

| 构造子 | 状态 |
|:--|:--|
| `sort` | ✅ `simp only [shift, inst]` |
| `const` | ✅ 同上 |
| `app` | ✅ 两个归纳假设直接代入 |
| `lam` | ✅ `rw [ihA c σ]` → `congr 1` → **`exact ihb (c + 1) σ`** |
| `pi` | ✅ 同上 |
| `letE` | ✅ `rw [ihA, iht]` → `congr 1` → `exact ihb (c + 1) σ` |
| **`var`** | **❌ 唯一未闭合** |

**绑定情形的 `exact ihb (c + 1) σ` 那一行就是整条链的关键：归纳假设恰好以 `(c+1)` 实例化，
与「每层加一」完全吻合 —— 这说明**指数学本身就是对的**。**

## 唯一的缺口，及其为何不是「再试一次」

**`var` 情形需要一个关于 `shift` 作用于 `liftN` 的像的引理。本轮试了三种候选形式，全部失败：**

**候选 1** —— `liftN (c+1) σ n = shift c 1 (liftN c σ n)`（`n ≥ c`）。
**在 `n = 0` 处为假**：左边是 `var 0`，右边是 `shift 0 1 (var 0) = var 1`。

**候选 2** —— 同上但在 `n > c`。**在 `c = 0, n = 1` 处成立，但在 `c = 1, n = 2` 处失败。**

**候选 3** —— 收紧到 `n = c+1`。**仍然失败**：其原因是 `lift τ (c+1) = shift 0 1 (τ c)`
（`lift` 的定义），而右边需要 `shift c 1 (τ c)` —— **两者的 cutoff 相差 `c`，只有 `c = 0` 时吻合。**

**=> 结论：`lift` 的定义把位移放在 cutoff `0` 上，而 `shift c` 把位移放在 cutoff `c` 上。
这两者之间的换算**不是**恒等式，而是需要 `shift_commute_general`（ALT-1）那样的**补偿项**。
所以 `var` 情形缺的不是一条「展开引理」，而是一条**跨 cutoff 换算**，其形状受 ALT-1 支配。**

## 下一步（已定，不需再猜）

**用 `shift_commute_general`（ALT-1，已证）把 `shift c 1` 换算成 `shift 0 1` 的复合：
`shift 0 1 (shift c 1 τ) = shift c 1 (shift 0 1 τ)` 需要 `c ≤ 0`，即 `c = 0` —— 一般 `c` 不成立。
**=> 正确的做法是把 `liftN c (lift σ)` 换成 `liftN c σ` 与 `shift 0 (c+1)` 的组合，
即用**同一种算子**表达位移，而不是在 `lift` 与 `shift` 之间来回换算。**

## 本文件的内容

**只包含本轮确认为真的那一条：`lift_apply_succ` —— `lift τ (k+1) = shift 0 1 (τ k)`，
作为 `lift` 定义的具名形式，供下一步使用。** **本文件**不**声称 `inst_lift_c` 已证。** -/

namespace Lattice.Core.CIC

/-- **`lift` 在索引 `k+1` 处的取值：位移放在 cutoff `0` 上。**

**`lift τ (k + 1) = shift 0 1 (τ k)`。**

**=> 这条就是 `lift` 的定义本身，但**具名**之后才能作为下一步换算的锚点。
第 783 轮的三次失败都源于「`lift` 用 cutoff `0`、而目标需要 cutoff `c`」这一错位，
本定理把错位的那一半写成可引用的形式。** -/
theorem lift_apply_succ (τ : Subst) (k : ℕ) : lift τ (k + 1) = shift 0 1 (τ k) := rfl

/-- **`lift` 在索引 `0` 处不动：`lift τ 0 = var 0`。**

**=> 与上一条合起来给出 `lift` 的完整外貌。** -/
theorem lift_apply_zero (τ : Subst) : lift τ 0 = Term.var 0 := rfl

end Lattice.Core.CIC
