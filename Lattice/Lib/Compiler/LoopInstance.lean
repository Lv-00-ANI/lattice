import Lattice.Lib.Compiler.RepairPair
import Lattice.Runtime.VerificationLoop

/-!
# **把闭环回路**实例化到产物载荷上**：`Lib/Compiler` 首次消费主链的回路定理**

## 本轮做了什么，以及为什么这是**连接**而不是又一座岛

**第 1083 轮之后，`Lib/Compiler` 的修复链（`slopeRepair` → `repairProd` → 乘积观察）仍然只在岛内。
⇒ 而主链的 `Runtime/VerificationLoop.lean` 是**对任意 `α` 泛型**的：**

```lean
structure VerificationLoop (α : Type) where
  repair : Repair α
  objective : α → ℝ
-- 以及 step / run / step_fixed_of_sat / loop_end_sat，全部以 `{α : Type}` 为变量
```

**⇒ 因此它可以**直接实例化**到 `(ℕ → Segment) × (ℕ → Segment)`——不需要任何桥、不需要任何新语义。**

**⇒ 这不是「相似」，是**同一批定理在另一个载体上的实例**：
⇒ `twoSlopeLoop_ends_sat` 的**证明就是** `VerificationLoop.loop_end_sat`，
故 `Lib/Compiler` 的这条定理**消费** Runtime 的定理——第 1080 轮计划里「让新旧真正相连」的那一步。**

## 目标函数取什么

**`VerificationLoop` 需要一个 `objective : α → ℝ`。⇒ 本文件取「**第一个载荷在观察点的值**」：**

```lean
objective := fun p => gridEval p.1 n x
```

**⇒ 这个选择是**可解释的**：闭环每轮「修一次、看一次」，而看的就是产物在某个可求值点的输出。
⇒ 故它是「再注入后观测」的最小实例，而不是一个占位函数。**
-/

namespace Lattice.Lib.Compiler.LoopInstance

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.WriteBack
open Lattice.Lib.Compiler.RepairPair
open Lattice.Core
open Lattice.Runtime

/-- **⭐⭐ 产物载荷上的闭环**：修复是乘积实例，观测是第一个载荷在某点的网格求值。** -/
noncomputable def twoSlopeLoop (a b : ℝ) (n : ℕ) (x : ℝ) :
    VerificationLoop ((ℕ → Segment) × (ℕ → Segment)) where
  repair := twoSlopeRepair a b
  objective := fun p => gridEval p.1 n x

/-- **⭐⭐⭐ 回路终止时两侧都满足**——**直接引用主链的 `loop_end_sat`。**

**⇒ 这条是本文件的目的：它是 `Lib/Compiler` 里**第一条以 Runtime 定理为证明的定理**。**
**⇒ 步数由测度决定：`μ p` 轮（本实例里 `μ` 是两侧测度之和，故两侧同时到达）。** -/
theorem twoSlopeLoop_ends_sat (a b : ℝ) (n : ℕ) (x : ℝ)
    (p : (ℕ → Segment) × (ℕ → Segment)) :
    (twoSlopeLoop a b n x).repair.Sat
      ((twoSlopeLoop a b n x).run ((twoSlopeLoop a b n x).repair.μ p) p) :=
  VerificationLoop.loop_end_sat (twoSlopeLoop a b n x) p

/-- **⭐⭐ 停在满足点时，一轮就是恒等**——同样直接引用主链定理。

**⇒ 这是「闭合」的含义：下一轮的输入与本轮相同，故回路不会在达标后继续扰动。** -/
theorem twoSlopeLoop_step_fixed (a b : ℝ) (n : ℕ) (x : ℝ)
    {p : (ℕ → Segment) × (ℕ → Segment)} (h : (twoSlopeRepair a b).Sat p) :
    (twoSlopeLoop a b n x).step p = (p, (twoSlopeLoop a b n x).objective p) :=
  VerificationLoop.step_fixed_of_sat (twoSlopeLoop a b n x) h

/-- **⭐⭐⭐ 回路的 `k` 轮**逐分量**展开**（主链 `run` + 乘积迭代定理的合成）。**

**⇒ `run k p` 就是两侧各修 `k` 次。这与 `twoSlopeLoop_ends_sat` 合起来说明：
回路不是在两侧之间**轮流**，而是**同步**推进。** -/
theorem twoSlopeLoop_run_components (a b : ℝ) (n : ℕ) (x : ℝ) (k : ℕ)
    (p : (ℕ → Segment) × (ℕ → Segment)) :
    (twoSlopeLoop a b n x).run k p
      = ((slopeRepair a).fix^[k] p.1, (slopeRepair b).fix^[k] p.2) := by
  show (twoSlopeRepair a b).iterate k p = _
  show (twoSlopeRepair a b).fix^[k] p = _
  exact Lattice.Core.RepairModule.RepairProduct.repairProd_iterate (slopeRepair a) (slopeRepair b) k p

/-! ## 三、以**缺陷函数**为目标：终点为零 -/

/-- **⭐⭐以「两侧斜率与目标的偏差平方和」为目标的闭环。**

**⇒ 与上一个实例的区别是本质的：`gridEval` 在达标点**不**为零（它是 `a·x + c`），
而偏差函数在达标点**恰好为零**——这才能接上
`closed_loop_reinject_vanishes`。**
**⇒ 故本实例的目标函数不是占位而是**误差度量**。** -/
noncomputable def twoSlopeDefectLoop (a b : ℝ) :
    VerificationLoop ((ℕ → Segment) × (ℕ → Segment)) where
  repair := twoSlopeRepair a b
  objective := fun p => ((p.1 0).m - a) ^ 2 + ((p.2 0).m - b) ^ 2

/-- **⭐⭐ 目标在达标处为零**（本实例的 `hobj`）。** -/
theorem twoSlopeDefectLoop_objective_at_sat (a b : ℝ)
    {p : (ℕ → Segment) × (ℕ → Segment)} (h : (twoSlopeRepair a b).Sat p) :
    (twoSlopeDefectLoop a b).objective p = 0 := by
  obtain ⟨h1, h2⟩ := h
  show ((p.1 0).m - a) ^ 2 + ((p.2 0).m - b) ^ 2 = 0
  have e1 : ((p.1 0).m - a) ^ 2 = 0 := by rw [h1]; ring
  have e2 : ((p.2 0).m - b) ^ 2 = 0 := by rw [h2]; ring
  rw [e1, e2]
  ring

/-- **⭐⭐⭐ 闭环终点目标**为零**——**直接引用主链的 `closed_loop_reinject_vanishes`。**

**⇒ 这就是规划里「再注入」的实体：经过 `μ p` 轮修正后，产物两侧的斜率**偏差平方和为零**，
即两侧斜率分别等于目标 `a`、`b`。**
**⇒ 而证明只有一行：把本实例的 `hobj` 喂给主链定理。** -/
theorem twoSlopeLoop_objective_vanishes (a b : ℝ)
    (p : (ℕ → Segment) × (ℕ → Segment)) :
    (twoSlopeDefectLoop a b).objective
      ((twoSlopeDefectLoop a b).run ((twoSlopeDefectLoop a b).repair.μ p) p) = 0 :=
  VerificationLoop.closed_loop_reinject_vanishes (twoSlopeDefectLoop a b) p
    (fun y hy => twoSlopeDefectLoop_objective_at_sat a b hy)

end Lattice.Lib.Compiler.LoopInstance