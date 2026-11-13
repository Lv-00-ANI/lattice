/-
# The `Domains.Constraints.Tokens` plugin's proofs -- MOVED from `Lattice/Domains/Constraints/LossExtraction.lean`

**The DECLARATIONS do not change -- same names, same statements, same proofs, same
namespace -- so no downstream file needs editing for the move itself.**
The old path is now a facade that imports this file and contains no proof.
-/

/-
Copyright: LATTICE

# 损失的不可抽取性：为什么「从损失反推约束」不可能

## 本文件要回答的问题

**逆向方向（权重 → 符号）最字面的形式化是**：

    ∃ extract, ∀ c, extract (penaltyLoss c) = c

**即「损失是约束的单射编码，因此可以从中恢复约束」。**

**本文件证明这个命题是【假**的，而且是【结构性】的假，不是技术困难：

**`leZero e` 与 `ltZero e` 的损失【完全相同**——都是 `(max (evalPts e Φ) 0)²`——
**而它们是两个不同的约束。**

**⇒ 损失映射不是单射，所以任何 `extract` 都不可能同时恢复两者。**

## 这不是缺陷，而是必要

**第 150 轮已经指出**：**`penaltyLoss` 必须是【连续】的（那正是它可微的原因），
而 `Holds .ltZero` 在 `evalPts = 0` 处不连续。**
**⇒ 严格不等号在连续损失里【无法】与闭区间区分开。**

**⇒ 逆向方向不能建立在「从损失值恢复约束」之上。
它必须建立在别的对象上（例如：从损失值恢复【可行配置集合】，而不是约束本身）。**
-/
import Mathlib
import Lattice.Plugins.Domains.Constraints.Penalty.PenaltyLoss
open Lattice.Core

namespace Lattice.Geo

open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss

/-- ⭐⭐⭐ **`leZero` 与 `ltZero` 的损失完全相同**——**都是 `(max (evalPts e Φ) 0)²`。**

**这是「损失不可抽取」的根源。** -/
theorem penaltyLoss_leZero_eq_ltZero {n : ℕ} (e : GeoExpr n) (Φ : ℕ → Pt n) :
    penaltyLoss (.leZero e) Φ = penaltyLoss (.ltZero e) Φ := by
  simp only [penaltyLoss]

/-- ⭐ **两个约束是【不同】的**——**构造子不同。** -/
theorem leZero_ne_ltZero {n : ℕ} (e : GeoExpr n) :
    (.leZero e : GeoConstraint n) ≠ .ltZero e := by
  intro h
  exact GeoConstraint.noConfusion h

/-- ⭐⭐⭐ **损失映射不是单射**——**`penaltyLoss` 把两个不同的约束映到同一个函数。**

**⚠ 这是【否定性结果**，但它确定了逆向方向【不能】走哪条路。** -/
theorem penaltyLoss_not_injective {n : ℕ} (e : GeoExpr n) :
    ¬ Function.Injective (fun c : GeoConstraint n => (penaltyLoss c : (ℕ → Pt n) → ℝ)) := by
  intro hinj
  have heq : penaltyLoss (.leZero e) = penaltyLoss (.ltZero e) :=
    funext (penaltyLoss_leZero_eq_ltZero e)
  exact leZero_ne_ltZero e (hinj heq)

/-- ⭐⭐⭐ **不存在「从损失恢复约束」的左逆**——**逆向方向最字面的形式化是假的。**

**`∃ extract, ∀ c, extract (penaltyLoss c) = c` 不成立：
`leZero e` 与 `ltZero e` 的损失相同，所以 `extract` 在那一个参数上只能给出一个值。** -/
theorem no_loss_to_constraint_section {n : ℕ} (e : GeoExpr n) :
    ¬ ∃ extract : ((ℕ → Pt n) → ℝ) → GeoConstraint n,
        ∀ c : GeoConstraint n, extract (penaltyLoss c) = c := by
  rintro ⟨extract, h⟩
  have h1 : extract (penaltyLoss (.leZero e)) = .leZero e := h _
  have h2 : extract (penaltyLoss (.ltZero e)) = .ltZero e := h _
  have heq : penaltyLoss (.leZero e) = penaltyLoss (.ltZero e) :=
    funext (penaltyLoss_leZero_eq_ltZero e)
  rw [heq] at h1
  rw [h1] at h2
  exact leZero_ne_ltZero e h2

end Lattice.Geo
