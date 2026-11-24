import Lattice.Lib.Compiler.WriteBack
import Lattice.Core.RepairModule.RepairProduct

/-!
# **两段斜率同时修复：乘积实例在 `ℕ → Segment` 上的落地**

## 为什么这个实例有意义

**`slopeRepair a` 修的是**第 0 段**的斜率。但真实产物有多段，而「只修第一段、其余不动」只是一个约束。**
**⇒ 若要**同时**修两段的斜率，需要两个 `fix` 一起跑——这正是 `RepairProduct.repairProd` 提供的。**

**⇒ 而它的三条义务不是自动的：`decreases` 需要「未失败的那一侧被 `absorbs` 保持」这个细节，
否则「另一侧不动」会让总测度**不下降**。⇒ 乘积实例把这个细节证掉了，故本文件可以直接用它。**
-/

namespace Lattice.Lib.Compiler.RepairPair

open Lattice.Lib.Compiler.WriteBack
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Core

/-- **⭐⭐ 两段斜率同时修复**：状态是**两个载荷**的积。 -/
noncomputable def twoSlopeRepair (a b : ℝ) : Repair ((ℕ → Segment) × (ℕ → Segment)) :=
  Lattice.Core.RepairModule.RepairProduct.repairProd (slopeRepair a) (slopeRepair b)

/-- **⭐⭐ 两侧都满足时，合并修复**不动状态**（再注入的稳定性）。** -/
theorem twoSlopeRepair_absorbs (a b : ℝ) (p : (ℕ → Segment) × (ℕ → Segment))
    (h : (twoSlopeRepair a b).Sat p) : (twoSlopeRepair a b).fix p = p :=
  (twoSlopeRepair a b).absorbs p h

/-- **⭐⭐⭐ 只要**任一侧**失败，总测度就严格下降。**

**⇒ 这正是乘积实例的 `decreases`：它已经处理了「另一侧未失败」的情形。** -/
theorem twoSlopeRepair_decreases (a b : ℝ) (p : (ℕ → Segment) × (ℕ → Segment))
    (h : ¬ (twoSlopeRepair a b).Sat p) :
    (twoSlopeRepair a b).μ ((twoSlopeRepair a b).fix p) < (twoSlopeRepair a b).μ p :=
  (twoSlopeRepair a b).decreases p h

/-- **⭐⭐⭐ 同步推进：`n` 步之后两侧各走 `n` 步**，而不是「先修完一侧再修另一侧」。** -/
theorem twoSlopeRepair_iterate (a b : ℝ) (n : ℕ) (p : (ℕ → Segment) × (ℕ → Segment)) :
    (twoSlopeRepair a b).fix^[n] p = ((slopeRepair a).fix^[n] p.1, (slopeRepair b).fix^[n] p.2) :=
  Lattice.Core.RepairModule.RepairProduct.repairProd_iterate (slopeRepair a) (slopeRepair b) n p

/-- **⭐⭐ **一步就达标**：乘积修复一步后两侧都满足。

**⇒ 两侧各自由 `slopeFix_sat` 立即满足；乘积只是把它们放在一起。**
**⇒ 这条说明「同时修复」**不需要多轮**，而 `repairProd_iterate` 保证它也不会因为并行而需要更多轮。** -/
theorem twoSlopes_sat_after_fix (a b : ℝ) (p : (ℕ → Segment) × (ℕ → Segment)) :
    (twoSlopeRepair a b).Sat ((twoSlopeRepair a b).fix p) := by
  show (slopeRepair a).Sat ((slopeRepair a).fix p.1)
    ∧ (slopeRepair b).Sat ((slopeRepair b).fix p.2)
  exact ⟨slopeFix_sat a p.1, slopeFix_sat b p.2⟩

/-- **⭐⭐⭐ 两侧同时改变一个**可观察量**。

**⇒ 这是第 1047 轮 `repair_changes_observable` 的**乘积提升**：两侧各自在自己的见证点上改变。**
**⇒ 两个见证点可以**不同**，因为两侧是**独立的载荷**——这正是乘积状态的意义。** -/
theorem twoSlopes_change_two_observables (a b b₁ c₁ b₂ c₂ : ℝ)
    (hba₁ : b₁ ≠ a) (hba₂ : b₂ ≠ b) (n : ℕ)
    (x₁ x₂ : ℝ) (hx₁ : x₁ ≠ 0) (hidx₁ : segmentIndex n x₁ = 0)
    (hx₂ : x₂ ≠ 0) (hidx₂ : segmentIndex n x₂ = 0) :
    gridEval ((twoSlopeRepair a b).fix (constFamily b₁ c₁, constFamily b₂ c₂)).1 n x₁
        ≠ gridEval (constFamily b₁ c₁) n x₁
      ∧ gridEval ((twoSlopeRepair a b).fix (constFamily b₁ c₁, constFamily b₂ c₂)).2 n x₂
        ≠ gridEval (constFamily b₂ c₂) n x₂ := by
  show gridEval (slopeFix a (constFamily b₁ c₁)) n x₁ ≠ gridEval (constFamily b₁ c₁) n x₁
      ∧ gridEval (slopeFix b (constFamily b₂ c₂)) n x₂ ≠ gridEval (constFamily b₂ c₂) n x₂
  exact ⟨repair_changes_observable a b₁ c₁ hba₁ n x₁ hx₁ hidx₁,
         repair_changes_observable b b₂ c₂ hba₂ n x₂ hx₂ hidx₂⟩

end Lattice.Lib.Compiler.RepairPair