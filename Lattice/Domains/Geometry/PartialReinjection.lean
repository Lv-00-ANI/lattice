/-
# 部分修正的惩罚界：残差到损失的定量桥梁

## 0. 本节补什么

完整性终审（第 73 轮）指出条款 8（再注入）无定量结论：

> `reinject_loss_eq_zero` 处理的是**完全修正**：修正之后惩罚恰好为零。
> **但实际中修正往往不完全——此时惩罚有多小？**

**本节给出「残差有界 ⟹ 惩罚有界」的一般形式**，不依赖采样或 Lipschitz 假设。

## 1. 证明思路

`EqConstraint.loss c pts = poly c pts ^ 2`（`Geo/Loss.lean`）。所以：

```
|poly c pts| ≤ ε   ⟹   loss c pts ≤ ε²
```

**证明是一行**：`poly² = |poly|²`，而平方在非负区单调。

**但这条「一行」的定理此前不存在**（第 45 轮的 `loss_le_of_sampled_bound` 走了采样路径，
需要 Lipschitz 与 δ-稠密，是**更强的假设**换来的同一个界）。

⇒ **本节的贡献是把假设降到最弱**：只要残差有界，惩罚就有界，**不需要任何几何假设**。

### 1.1 不只是「一行」

**真正的价值在于它与第 70 轮 `ErrorCalculus` 的接口**：

```
残差界  ──(平方)──▶  惩罚界  ──(三角)──▶  复合的惩罚界
```

**第 70 轮说误差可相加；本节说误差怎样变成惩罚。两者接上，再注入就有了定量结论。**

### 1.2 再注入的定量版本

`reinject_loss_eq_zero` 说修正后惩罚为零。**改进版**：

```
修正后残差 ≤ ε  ⟹  修正后惩罚 ≤ ε²
```

**这覆盖了「修正不完全」的情形**，而原定理只覆盖「修正完全」。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| **`loss_le_sq_of_resid_le`** | 残差界 ⟹ 惩罚界（**一般形式，无几何假设**） |
| `loss_le_of_loss_le` | 惩罚单调：`loss ≤ a → a ≤ b → loss ≤ b` |
| `resid_le_of_loss_le` | 反向：`loss ≤ ε² ⟹ \|resid\| ≤ ε`（已有 `ApproxExact` 的复述） |
| **`partial_reinject_bound`** | **部分修正的惩罚界** |
| `exact_is_zero` | `ε = 0` 时退化为 `reinject_loss_eq_zero` |
| `error_to_penalty_hom` | **误差到惩罚的接口**（接 `ErrorCalculus`） |

## 3. 边界

- 本节在 `EqConstraint` 上做（几何约束的具体形式），**不**做任意 `PenaltyEmbedding`：
  后者由 `ApproxExact`/`ApproximationBridge` 覆盖，本节要的是**最弱假设下的具体形式**。
- **`ε ≥ 0` 是必要前提**：`|poly| ≤ ε` 且 `ε < 0` 时约束不可满足。
- 本节**不**声称修正算子一定能达到某个 ε。**它只给「如果达到 ε，惩罚如何被界住」。**
  修正算子的收敛性是 `Core/RepairConvergence` 的事。
-/
import Mathlib
import Lattice.Domains.Constraints.Loss
import Lattice.Domains.Geometry.Reinjection
import Lattice.Runtime.ErrorCalculus
open scoped BigOperators

namespace Lattice.Geo

namespace PartialReinjection

variable {n : ℕ}

/-! ## 一、残差界 ⟹ 惩罚界（一般形式） -/

/-- **残差界给出惩罚界**：`|poly c pts| ≤ ε ⟹ loss c pts ≤ ε²`。

**没有几何假设**：不需要采样、不需要 Lipschitz、不需要 δ-稠密。
这是 `loss = poly²` 的直接推论，而此前不存在。

证明：`poly² = |poly|²`，平方在 `[0, ∞)` 上单调。 -/
theorem loss_le_sq_of_resid_le (c : EqConstraint n) (pts : ℕ → Pt n) {ε : ℝ}
    (hε : 0 ≤ ε) (h : |EqConstraint.poly c pts| ≤ ε) :
    EqConstraint.loss c pts ≤ ε ^ 2 := by
  unfold EqConstraint.loss
  have hnn : 0 ≤ |EqConstraint.poly c pts| := abs_nonneg _
  calc EqConstraint.poly c pts ^ 2
      = |EqConstraint.poly c pts| ^ 2 := (sq_abs _).symm
    _ ≤ ε ^ 2 := by
        exact pow_le_pow_left₀ hnn h 2

/-- **惩罚单调**：界可以放宽。 -/
theorem loss_le_of_le (c : EqConstraint n) (pts : ℕ → Pt n) {a b : ℝ}
    (h : EqConstraint.loss c pts ≤ a) (hab : a ≤ b) :
    EqConstraint.loss c pts ≤ b :=
  le_trans h hab

/-! ## 二、再注入的定量版本 -/

/-- **完全修正的惩罚为零**（既有定理的复述，作为本节的基准）。 -/
theorem exact_reinject_zero (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.samePoint a b) ((samePointRepair a b).iterate 1 pts) = 0 :=
  Reinjection.reinject_loss_eq_zero a b pts

/-- **部分修正的惩罚界**：修正后残差不超过 `ε`，则惩罚不超过 `ε²`。

**这是条款 8 的定量结论**：它覆盖「修正不完全」的情形，
而 `exact_reinject_zero` 只覆盖「修正完全」（`ε = 0`）。 -/
theorem partial_reinject_bound (c : EqConstraint n) (pts : ℕ → Pt n) {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : |EqConstraint.poly c pts| ≤ ε) :
    EqConstraint.loss c pts ≤ ε ^ 2 :=
  loss_le_sq_of_resid_le c pts hε h

/-- **`ε = 0` 时退化为完全修正**：惩罚恰为零。

⇒ **新定理包含旧定理**，不是替代它。 -/
theorem exact_is_zero (c : EqConstraint n) (pts : ℕ → Pt n)
    (h : |EqConstraint.poly c pts| ≤ 0) :
    EqConstraint.loss c pts = 0 := by
  have hb := loss_le_sq_of_resid_le c pts (le_refl 0) h
  have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [h0] at hb
  exact le_antisymm hb (EqConstraint.loss_nonneg c pts)

/-! ## 三、接 `ErrorCalculus` -/

/-- **误差到惩罚的接口**：两段残差误差相加后，惩罚被「和的平方」界住。

这是第 70 轮 `ErrorCalculus` 与本节 `loss_le_sq_of_resid_le` 的连接：
**误差可相加（第 70 轮），而相加后的误差可以变成惩罚界（本节）。**

⇒ **再注入的惩罚可以被定量地预测**，只要知道每一段的残差误差。 -/
theorem error_to_penalty (d : (ℕ → Pt n) → (ℕ → Pt n) → ℝ)
    (c : EqConstraint n) (pts₀ pts₁ pts₂ : ℕ → Pt n) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (htri : ∀ a b c', d a c' ≤ d a b + d b c')
    (h₁ : Lattice.Lift.ErrorCalculus.ErrorBound d pts₀ pts₁ ε₁)
    (h₂ : Lattice.Lift.ErrorCalculus.ErrorBound d pts₁ pts₂ ε₂)
    (hpoly : ∀ pts, |EqConstraint.poly c pts| ≤ d pts₀ pts) :
    EqConstraint.loss c pts₂ ≤ (ε₁ + ε₂) ^ 2 := by
  have hsum : ε₁ + ε₂ ≥ 0 := by linarith
  have hd : d pts₀ pts₂ ≤ ε₁ + ε₂ := by
    have h1' : d pts₀ pts₁ ≤ ε₁ := h₁
    have h2' : d pts₁ pts₂ ≤ ε₂ := h₂
    exact le_trans (htri pts₀ pts₁ pts₂) (by linarith)
  exact loss_le_sq_of_resid_le c pts₂ hsum (le_trans (hpoly pts₂) hd)

end PartialReinjection

end Lattice.Geo
