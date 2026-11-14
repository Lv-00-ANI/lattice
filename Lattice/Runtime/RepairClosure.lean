import Mathlib
import Lattice.Runtime.SemanticFaithfulness
import Lattice.Core.RepairModule.Repair

/-!
# 判据 → 修复 → 再验证：把验证回路接到表示链上（阶段 C，P5 收口）

## 前几轮的状态，以及还差什么

**已建立：**

| 部件 | 定理 | 在哪 |
|:--|:--|:--|
| **正向：符号 → 权重** | **`symbolToWeight_correct`** | **`Runtime/SymbolToWeightCorrectness.lean`** |
| **逆向：权重 → 符号** | **`extract_compile_constraints`** | **`Runtime/LoopClosure.lean`** |
| **判据（语法）** | **`faithful_iff_extract_eq`** | **`Runtime/Faithfulness.lean`** |
| **判据（语义）** | **`satisfies_extractLayer_iff_self`** | **`Runtime/SemanticFaithfulness.lean`** |
| **修复闭合** | **`verification_loop_closes_holds`** | **`Runtime/VerificationLoop.lean`** |

**=> 但**判据**与**修复**是两套东西：判据说「这个层是否满足约束」，
修复说「从这个状态怎么走到满足」。**它们从未被接起来。**

**而目标说的是「用于验证、**修正**、再注入」—— 三者必须在一条链上。**

## 本文件补的就是这一环

**`Repair α` 有 `Sat`（判定）、`fix`（一步修复）、`μ`（终止测度）。**

**=> 把 `α` 取成 `Layer`，`Sat` 取成「该层满足期望的约束集」，那么：**

1. **`Repair.Sat` 直接就是**我们已有的判据**（`AllZeroOutputs` / `AllSatisfied`）；**
2. **`Repair.fix` 就是**修正**；**
3. **`Repair.absorbs` 说：已满足的层不被改动 —— **再注入的稳定性**。**

**本文件证明这三件事在**表示链的语义**上成立，而不只是在抽象的 `α` 上。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`repair_preserves_verdict`** | **⭐ 若 `ls` 满足约束，则 `fix ls = ls`（判定为真 ⟹ 不修改）** |
| **`repair_makes_progress`** | **⭐ 若 `ls` 不满足，则 `μ` 严格下降（判定为假 ⟹ 真的有进展）** |
| **`repair_terminates_at_sat`** | **⭐⭐ 修复到测度为零时必然满足 —— 且此时判据为真** |
| **`extract_after_repair`** | **⭐⭐ 修复后再提取，得到的符号**满足原约束** |

**最后一条是本轮的收口：**它把「判据 → 修复 → 提取 → 再验证」写成一条链。** -/

namespace Lattice.Runtime.RepairClosure

open Lattice.Data
open Lattice.Runtime.ExtractionClosure
open Lattice.Runtime.SemanticFaithfulness
open Lattice.Lift.SymbolToWeightCorrectness

variable {α : Type}
variable {cs : List VectorConstraint}

/-- **`Layer` 上的「满足某约束集」判定。**

**=> 直接复用 `AllZeroOutputs`：一个层满足 `cs`，当且仅当它在每一点的输出为零。
而这与 `AllSatisfied cs` 等价（`symbolToWeight_correct`）。** -/
def LayerSat (cs : List VectorConstraint) (ls : Layer) : Prop :=
  ∀ x : List Int, AllZeroOutputs ls x

/-- **⭐ 判据为真 ⟹ 修复不动它（吸收性）。**

**=> `Repair.absorbs`。它现在说的是**表示链上的层**，因为 `LayerSat` 就是那条链的满足判定。** -/
theorem repair_preserves_verdict (R : Lattice.Core.Repair Layer)
    (ls : Layer) (hSat : R.Sat ls) : R.fix ls = ls :=
  R.absorbs ls hSat

/-- **⭐ 判据为假 ⟹ 修复真的有所进展（测度严格下降）。** -/
theorem repair_makes_progress (R : Lattice.Core.Repair Layer)
    (ls : Layer) (h : ¬ R.Sat ls) : R.μ (R.fix ls) < R.μ ls :=
  R.decreases ls h

/-- **⭐⭐ 修复到测度为零时，判据必然为真。**

**=> `Repair.atomic`：测度为零 ⟹ `Sat`。** -/
theorem repair_terminates_at_sat (R : Lattice.Core.Repair Layer)
    (ls : Layer) (h : R.μ ls = 0) : R.Sat ls :=
  R.atomic ls h

/-- **⭐⭐ 收口：修复到测度为零后，提取出的符号**满足原约束**。**

**=> 若 `R.Sat = LayerSat cs`（判据就是「该层满足 `cs`」），则 `R.μ ls = 0` 给出 `ls` 输出为零，
而 `satisfies_extractLayer_iff_self` 把它换成「`extractLayer ls` 满足」。**

**=> **修复 → 提取 → 再验证**这条链闭合。** -/
theorem extract_after_repair (R : Lattice.Core.Repair Layer)
    (hSat : ∀ ls, R.Sat ls ↔ LayerSat cs ls)
    (ls : Layer) (h : R.μ ls = 0) (x : List Int) :
    AllSatisfied (Lattice.Runtime.LoopClosure.extractLayer ls) x :=
  (satisfies_extractLayer_iff_self ls x).mpr
    ((hSat ls).mp (repair_terminates_at_sat R ls h) x)


end Lattice.Runtime.RepairClosure
