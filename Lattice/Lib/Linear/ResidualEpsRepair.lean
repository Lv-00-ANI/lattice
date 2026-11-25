import Lattice.Lib.Linear.Residual
import Lattice.Runtime.ApproxExact
import Lattice.Runtime.PenaltyEmbedding

/-!
# **ε-判据**也有**一个真 `Repair`**：死区版线性修复

## 这一条补的是什么

**第 1135 轮测出 `EpsSat`（ε-验证）与 `Repair`（修复）从未同现。第 1136 轮建了桥并证明「ε-判据只给谓词，不给测度」。**
**⇒ 但那一轮的语境里，`Repair` 的测度**已经存在**：`linearRepair` 的 `μ x = if residual = 0 then 0 else 1`，且有一条
真下降定理 `linearRepair_measure_drops`。**

**⇒ 故缺的**不是测度**，而是**判据**：`linearRepair` 要求残差**恰为零**，而验证给的是 `|残差| ≤ ε`。**

## 本文件做的事

**⇒ 把判据从「恰为零」换成「在 ε 内」，其余**不动**——即一个**死区**修复：**
**⇒ 已在 ε 内 ⇒ 不动（`fix x = x`）；在 ε 外 ⇒ 跳到零。**

**⇒ 于是 `Repair` 的四个字段全部成立，且 `Sat` 正是 ε-判据。⇒ 这就是「ε-世界也有修复」的构造性证据。**
-/

namespace Lattice.Lib.Linear.ResidualEpsRepair

open Lattice.Core

/-- **⭐⭐ 死区版线性修复：判据是 ε，测度与 `linearRepair` 同形。**

**⇒ `Sat`：`|residual a b x| ≤ ε`。**
**⇒ `fix`：ε 内不动，ε 外跳到线性修复的零点。**
**⇒ `μ`：ε 内 0，ε 外 1。**

**⇒ 关键在 `decreases`：`¬Sat` 即 `|resid| > ε`，而修复后残差恰为 `0 ≤ ε`，故测度从 1 掉到 0。** -/
noncomputable def epsLinearRepair (a b : ℚ) (ha : a ≠ 0) (ε : ℚ) (hε : 0 ≤ ε) : Repair ℚ where
  Sat := fun x => |residual a b x| ≤ ε
  fix := fun x => if |residual a b x| ≤ ε then x else linearFix a b x
  μ := fun x => if |residual a b x| ≤ ε then 0 else 1
  absorbs := by
    intro x hx
    show (if |residual a b x| ≤ ε then x else linearFix a b x) = x
    rw [if_pos hx]
  decreases := by
    intro x hx
    have hout : ¬ |residual a b x| ≤ ε := hx
    have hfix : (if |residual a b x| ≤ ε then x else linearFix a b x) = linearFix a b x :=
      if_neg hout
    have hzero := linearFix_residual a b x ha
    show (if |residual a b (if |residual a b x| ≤ ε then x else linearFix a b x)| ≤ ε then 0 else 1)
        < (if |residual a b x| ≤ ε then 0 else 1)
    rw [hfix, hzero, if_neg hout]
    have habs : |(0 : ℚ)| ≤ ε := by
      rw [abs_zero]; exact hε
    rw [if_pos habs]
    norm_num
  atomic := by
    intro x hx
    by_contra hns
    simp only [if_neg hns] at hx
    exact absurd hx (by norm_num)

/-- **⭐ 判据同一：这条 `Repair` 的 `Sat` 就是 ε-判据本身。** -/
theorem epsLinearRepair_sat_iff (a b : ℚ) (ha : a ≠ 0) (ε : ℚ) (hε : 0 ≤ ε) (x : ℚ) :
    (epsLinearRepair a b ha ε hε).Sat x ↔ |residual a b x| ≤ ε :=
  Iff.rfl

/-- **⭐ 且在 ε 外**必然**下降——死区不是空转。** -/
theorem epsLinearRepair_drops_outside (a b : ℚ) (ha : a ≠ 0) (ε : ℚ) (hε : 0 ≤ ε) (x : ℚ)
    (hx : ¬ |residual a b x| ≤ ε) :
    (epsLinearRepair a b ha ε hε).μ ((epsLinearRepair a b ha ε hε).fix x)
      < (epsLinearRepair a b ha ε hε).μ x :=
  (epsLinearRepair a b ha ε hε).decreases x hx

/-- **⭐⭐ 线性惩罚嵌入：`loss` 就是残差，`Sat` 就是恰为零。**

**⇒ 它使 `EpsSat`（验证语言）能说到**本文件的残差**上。** -/
def linearPenaltyEmbedding : Lattice.Lift.PenaltyEmbedding (ℚ × ℚ) ℚ where
  loss := fun p x => ((residual p.1 p.2 x : ℚ) : ℝ)
  Sat := fun p x => residual p.1 p.2 x = 0

/-- **⭐⭐⭐ 两个世界的**判据是同一个**：本文件那个 `Repair` 的 `Sat`
恰是 `EpsSat`。**

**⇒ 这是全树**第一次**有一条定理同时提到 `EpsSat` 与一个**具体 `Repair` 实例的判据**。
⇒ 故它就是 `3.2 → 3.3` 接缝的真连接器。** -/
theorem epsLinearRepair_sat_is_epsSat (a b : ℚ) (ha : a ≠ 0) (ε : ℚ) (hε : 0 ≤ ε) (x : ℚ) :
    (epsLinearRepair a b ha ε hε).Sat x ↔
      Lattice.Lift.EpsSat linearPenaltyEmbedding (a, b) (ε : ℝ) x := by
  show |residual a b x| ≤ ε ↔ |((residual a b x : ℚ) : ℝ)| ≤ (ε : ℝ)
  constructor <;> intro h <;> exact_mod_cast h

/-- **⭐⭐⭐ 再注入定理：一步修复之后，ε-判据**仍成立**。**

**⇒ 这是 `closed_loop_reinject_vanishes` 的**宽容差版本**：原条要求「终点目标**为零**」，
而ε-判据只能给「终点目标**在 ε 内**」。**
**⇒ 故原条是**本条在 `ε = 0` 的特例**，而本条才是对ε-验证可用的形式。**

**⇒ 分两支：**在 ε 内 ⇒ 不动，故仍在 ε 内；在 ε 外 ⇒ 跳到零，故 `|0| = 0 ≤ ε`。**** -/
theorem epsLinearRepair_reinject_within (a b : ℚ) (ha : a ≠ 0) (ε : ℚ) (hε : 0 ≤ ε) (x : ℚ) :
    |residual a b ((epsLinearRepair a b ha ε hε).fix x)| ≤ ε := by
  by_cases hin : |residual a b x| ≤ ε
  · have : (epsLinearRepair a b ha ε hε).fix x = x := by
      show (if |residual a b x| ≤ ε then x else linearFix a b x) = x
      rw [if_pos hin]
    rw [this]
    exact hin
  · have : (epsLinearRepair a b ha ε hε).fix x = linearFix a b x := by
      show (if |residual a b x| ≤ ε then x else linearFix a b x) = linearFix a b x
      rw [if_neg hin]
    rw [this, linearFix_residual a b x ha, abs_zero]
    exact hε

/-! ## 六、**ε = 0 的退化**：容差为零的 ε-修复**就是**精确修复**

**⇒ 这是本文件的泛化与 `linearRepair` 这个特例之间的**连接**。**

**⇒ **三个数据字段分别相等**（`Sat`、`fix`、`μ`）——`Repair` 的三个 `Prop` 字段是证明，
按 proof irrelevance 不需要单独比。** -/

/-- **⭐⭐ 在 `ε = 0` 处，两个 `Repair` 的**判据相同**。**

**⇒ `|residual| ≤ 0 ↔ residual = 0`——容差为零就是精确。** -/
theorem epsLinearRepair_zero_sat_iff (a b : ℚ) (ha : a ≠ 0) (x : ℚ) :
    (epsLinearRepair a b ha 0 (le_refl 0)).Sat x ↔ (linearRepair a b ha).Sat x := by
  show |residual a b x| ≤ 0 ↔ residual a b x = 0
  simp [abs_nonpos_iff]

/-- **⭐⭐ 在 `ε = 0` 处，两个 `Repair` 的**修正步相同**。**

**⇒ 关键在 `linearFix_absorbs`：**若已在容差内（此处即零），精确修复**也**不动。** -/
theorem epsLinearRepair_zero_fix_eq (a b : ℚ) (ha : a ≠ 0) (x : ℚ) :
    (epsLinearRepair a b ha 0 (le_refl 0)).fix x = (linearRepair a b ha).fix x := by
  show (if |residual a b x| ≤ 0 then x else linearFix a b x) = linearFix a b x
  by_cases h : |residual a b x| ≤ 0
  · rw [if_pos h]
    have hz : residual a b x = 0 := by
      simpa [abs_nonpos_iff] using h
    exact (linearFix_absorbs a b x hz).symm
  · rw [if_neg h]

/-- **⭐⭐ 在 `ε = 0` 处，两个 `Repair` 的**测度相同**。** -/
theorem epsLinearRepair_zero_mu_eq (a b : ℚ) (ha : a ≠ 0) (x : ℚ) :
    (epsLinearRepair a b ha 0 (le_refl 0)).μ x = (linearRepair a b ha).μ x := by
  show (if |residual a b x| ≤ 0 then 0 else 1) = (if residual a b x = 0 then 0 else 1)
  by_cases h : residual a b x = 0
  · have habs : |residual a b x| ≤ 0 := by
      simp [h]
    rw [if_pos habs, if_pos h]
  · have habs : ¬ |residual a b x| ≤ 0 := by
      simp [h]
    rw [if_neg habs, if_neg h]

/-- **⭐⭐⭐ 三项合取：容差为零的 ε-修复**就是**精确修复。**

**⇒ 这是会话里第一次把两个**不同的** `Repair` 实例用一条定理连起来。** -/
theorem epsLinearRepair_zero_is_linearRepair (a b : ℚ) (ha : a ≠ 0) (x : ℚ) :
    ((epsLinearRepair a b ha 0 (le_refl 0)).Sat x ↔ (linearRepair a b ha).Sat x) ∧
      (epsLinearRepair a b ha 0 (le_refl 0)).fix x = (linearRepair a b ha).fix x ∧
      (epsLinearRepair a b ha 0 (le_refl 0)).μ x = (linearRepair a b ha).μ x :=
  ⟨epsLinearRepair_zero_sat_iff a b ha x,
   epsLinearRepair_zero_fix_eq a b ha x,
   epsLinearRepair_zero_mu_eq a b ha x⟩

end Lattice.Lib.Linear.ResidualEpsRepair