import Mathlib

/-!
# `Lattice.Lib.Penalty.QuadraticNotLipschitz` — **平方函数没有全局 Lipschitz 常数**

## 为什么这个文件存在

第 78 轮测量 `Domains/Constraints/PenaltyLoss.lean` 时，我上一轮的规划里写的是：

> 若它是 12 个分支的 `match`，那么它的 Lipschitz 界是 12 个分支界的最大值，
> 而每个分支是初等的（`sqDistEq` 是二次 ⇒ 局部 Lipschitz；`eqZero` 是线性 ⇒ 全局）。

**「`eqZero` 是线性」那句是错的。** 实测定义（`PenaltyLoss.lean` L124）：

```lean
| .eqZero e => (e.evalPts pts) ^ 2
```

**它是平方，不是线性。** 而且**全部 12 个分支都是平方或两个线性形式的乘积**：

| 分支 | 形状 |
|:--|:--|
| `eqZero` / `leZero` / `ltZero` / `gtZero` | `(·)²` 或 `(max · 0)²` |
| `sqDistEq` / `equalLength` | `(· - ·)²` |
| `perpendicular` / `rightAngle` | `(∑ · ·)²` |
| `midpoint` | `∑ (·)²` |
| `collinear` / `parallel` | `minorDefect`（叉积型，二次） |
| `samePoint` | `sqDist`（二次） |

⇒ ⭐ **`penaltyLoss` 没有任何一个分支是全局 Lipschitz 的。** 本文件证明那条抽象原因：
**`t²` 作为 `ℝ → ℝ` 没有全局 Lipschitz 常数。** 每条分支都含一个 `t²`（或其等价），
**所以这条引理直接适用于每一个分支。**

## 这条事实的用处

**它把「收敛估计需要假设迭代路径有界」从一句口头交代变成一条有原因的约束**：
损失是二次的，所以它的梯度是线性的、二次增长不可全局控制；
**任何 `|L(θ) − L(θ')| ≤ C·‖θ − θ'‖` 形式的估计都必须把 `θ` 限制在紧集里。**
-/

namespace Lattice.Lib.Penalty

/-- ⭐⭐ **平方函数没有全局 Lipschitz 常数。**

`¬ ∃ L, ∀ s t, |s² − t²| ≤ L · |s − t|`。

**证明是一步反例**：取 `s = max L 0 + 1`、`t = max L 0`，则 `|s − t| = 1`
而 `|s² − t²| = 2·max L 0 + 1`；要 `≤ L · 1 = L`，
**`L ≥ 0` 时要 `2L+1 ≤ L`（假），`L < 0` 时要 `1 ≤ L`（假）。** 两种情形都矛盾。

**`max L 0` 这个选法让两种情况用同一个反例**——不需要按 `L` 的正负分支去构造不同的点。 -/
theorem sq_not_lipschitz : ¬ ∃ L : ℝ, ∀ s t : ℝ, |s ^ 2 - t ^ 2| ≤ L * |s - t| := by
  rintro ⟨L, h⟩
  have hkey := h (max L 0 + 1) (max L 0)
  have hd : |(max L 0 + 1) - max L 0| = 1 := by
    rw [show max L 0 + 1 - max L 0 = 1 by ring, abs_one]
  have hn : |(max L 0 + 1) ^ 2 - (max L 0) ^ 2| = 2 * max L 0 + 1 := by
    rw [show (max L 0 + 1) ^ 2 - (max L 0) ^ 2 = 2 * max L 0 + 1 by ring,
        abs_of_nonneg (by positivity)]
  rw [hd, hn, mul_one] at hkey
  rcases le_or_lt 0 L with hL | hL
  · rw [max_eq_left hL] at hkey
    linarith
  · rw [max_eq_right (le_of_lt hL)] at hkey
    linarith

/-- **推论：任何形如 `t ↦ (t - c)²` 的函数也没有全局 Lipschitz 常数。**

**这正是 `penaltyLoss` 的每个分支的形状**（平方加上一个常数平移）。 -/
theorem sq_sub_const_not_lipschitz (c : ℝ) :
    ¬ ∃ L : ℝ, ∀ s t : ℝ, |(s - c) ^ 2 - (t - c) ^ 2| ≤ L * |s - t| := by
  rintro ⟨L, h⟩
  -- shift both points by `c` so the hypothesis about `u^2 - v^2` applies
  have h' : ∀ u v : ℝ, |u ^ 2 - v ^ 2| ≤ L * |u - v| := by
    intro u v
    have h1 : u + c - (v + c) = u - v := by ring
    have h2 := h (u + c) (v + c)
    simpa only [add_sub_cancel_right, h1] using h2
  exact sq_not_lipschitz ⟨L, h'⟩

end Lattice.Lib.Penalty
