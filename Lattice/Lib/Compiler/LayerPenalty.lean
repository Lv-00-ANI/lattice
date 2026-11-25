import Lattice.Runtime.PenaltyEmbedding
import Lattice.Runtime.SymbolToWeightCorrectness

/-!
# **层世界**落在 `PenaltyEmbedding` 这个抽象里**

## 这条补的是什么

**第 1139 轮把 2.3 与 1.3 用「同为左逆」连起来了。⇒ 正向侧还剩 `2.1 ↔ 1.3` 零同现。**

**⇒ `2.1`（约束损失）的载体是**抽象**：`PenaltyEmbedding`（`loss` 与 `Sat` 两个字段）与 `penaltyToLoss`。**
**⇒ `1.3`（符号→权重）的载体是**编译**：`compileToLayer : ConstraintSet → Layer`。**

**⇒ 二者的关系**不是**一条平行于它们的定理，而是：**层世界是那个抽象的一个实例**。**
**⇒ 本文件把这件事写成一个 `PenaltyEmbedding`，并证明它满足 `PenaltySound`（损失为零 ⟹ 满足）。**

**⇒ 这不是牵强：`PenaltySound` 正是「软损失代替硬约束」这一位置的**最低要求**，
⇒ 而层世界确实满足它——因为它的 `loss` 与 `Sat` 是**同一个谓词**的两种写法。**
-/

namespace Lattice.Lib.Compiler.LayerPenalty

attribute [local instance] Classical.propDecidable

open Lattice.Lift
open Lattice.Lift.SymbolToWeightCorrectness

/-- **⭐⭐ 层世界的惩罚嵌入：`loss` 与 `Sat` 是同一个谓词。**

**⇒ 取 `loss = 0` 当且仅当 `AllZeroOutputs`；否则取 `1`。⇒ 故 `PenaltySound` **按构造**成立。**
**⇒ 这个实例的**意义不在复杂度**，而在于：它把 `1.3` 的编译结果放进 `2.1` 的抽象里，
⇒ 从而使「约束损失」这门语言**能谈到层**。** -/
noncomputable def layerPenaltyEmbedding : PenaltyEmbedding ConstraintSet (List ℤ) where
  loss := fun cs x => if AllZeroOutputs (compileToLayer cs) x then 0 else 1
  Sat := fun cs x => AllZeroOutputs (compileToLayer cs) x

/-- **⭐⭐ 损失为零 ⟺ 层输出为零**——`PenaltySound` 的**逆**在这里也成立，
**⇒ 因为 `loss` 被定义成 `Sat` 的指示函数。** -/
theorem layerPenalty_loss_eq_zero_iff (cs : ConstraintSet) (x : List ℤ) :
    layerPenaltyEmbedding.loss cs x = 0 ↔
      AllZeroOutputs (compileToLayer cs) x := by
  unfold layerPenaltyEmbedding
  simp only
  by_cases h : AllZeroOutputs (compileToLayer cs) x
  · simp [h]
  · simp [h]

/-- **⭐ 故层世界满足 `PenaltySound`：损失为零 ⟹ 满足。** -/
theorem layerPenalty_sound : PenaltySound layerPenaltyEmbedding :=
  fun cs x h => ((layerPenalty_loss_eq_zero_iff cs x).mp h)

end Lattice.Lib.Compiler.LayerPenalty