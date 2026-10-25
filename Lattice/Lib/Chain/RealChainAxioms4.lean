import Lattice.Lift.ConvertLinear
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lib.Attention.RealMaskFamily
import Lattice.Lib.LearningTheory.RealConstrainedDecoding
import Lattice.Lib.LearningTheory.RealConstrainedDecodingVerify
/-!
# LATTICE: chain-core axiom probes, fourth batch (W05) —— 约束解码轴（L2⇄L3 推理期）

## ⚠ 本文件是**有意的终端叶**（not wired / zero in-degree by design）
`scripts/check-new-roots-indegree.py` 会把本文件报为 `[BARE]`。
这是**预期的**，不是缺陷：axiom-probe 收集器的**全部**职责就是在自己环境里
`#print axioms` 别处的定理，它**按定义**没有下游消费者。
⭐ 实测证据（本项目自己的读数）：**同一族的 `RealChainAxioms` 与
`RealChainAxioms2` 迄今同样是 `[BARE]`** —— 该族**结构性**终端。
⚠ 反面对照：`RealConstrainedDecoding`（交付模块）**不得**用同一条豁免，
它必须留在"已接线"侧；实测其 in-degree = 2（见 §三）。

## 为什么这个文件存在

前三批（`RealChainAxioms.lean` 17 条 / `RealChainAxioms2.lean` 20 条 /
`RealChainAxioms3.lean` 30 条）覆盖的是**训练期**链（L0⇄L1⇄L2⇄L3 的编译/提取）。
U03 §2.2 判定：`doc/02:90` 声明的 L2⇄L3「**编译方向**」在此前**只有训练期落点**，
**没有推理期落点**。本批次补的就是该落点 —— 约束解码（logits 可行性掩码）。

## ⭐ 本批次的定位（与前三批的差异）

| 批次 | 覆盖轴 | 载体 |
|:--|:--|:--|
| 1–3 | 编译/提取/往返（**训练期**） | `convertVec` / `extractVec` / 环等 |
| **4（本文件）** | ⭐ **约束解码（推理期）** | `constrainedSoftmax` / `FeasibleMask` |

## 覆盖（19 条，全部实测通过）

`RealConstrainedDecoding`（14 条）+ `RealConstrainedDecodingVerify`（5 条）。
⭐ **与前三批去重实测交集 = 0**（前三批不含 `Constrained` 前缀的任何声明）。

## ⚠ 本文件**不**声称的内容

* **不**声称全库无 `sorryAx` —— 只覆盖这 19 条。
* **不**声称这些定理「有内容」—— 公理干净是**必要条件**，不是**充分条件**。
  ⭐ 反例已在本仓两例：`closed_loop_adds_nothing`（零公理而内容为空）、
  `roundtrip_extractVec`（全仓引用最高，却是 `rfl`）。
  ⭐ 本批次的**内容判据**见下：`mask_actually_changes_distribution` /
  `empty_allowed_row_sum_ne_one` 是**带数值见证的反驳型**定理，
  而 `constrained_via_maskedSoftmax` 是 `rfl` ——**已如实标注为「桥」而非「内容」**。
* ⚠ **`#print axioms` 也会撒谎**：编译失败的文件仍会打印看似干净的条目（V05 负对照 2 实测）。
  故本文件的价值**取决于**同批次 `lake build RealChainAxioms4` 返回 `exit 0` —— **双条件不可拆**。
* ⚠ **本文件同时是 `RealConstrainedDecoding` 的消费者**（见 §三说明）：
  它使后者的 in-degree 由 **0 → 1**，避免 U03 发现 3 记录的「出厂即孤岛」形态
  （同型实例：`RealSSDBridge`，438 行、exit 0、公理干净、in-degree = 0）。
-/

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、约束解码核心（`RealConstrainedDecoding`，14 条）
这是 U03 §2.2 给定模板 `RealMaskFamily.maskedSoftmax:46-48` 的一维（token 维）对应物。 -/

#print axioms constrainedDenom_nonneg
#print axioms constrainedDenom_pos
#print axioms constrainedSoftmax_eq_zero_of_not_allowed
#print axioms constrainedSoftmax_pos_of_allowed
#print axioms constrainedSoftmax_nonneg
#print axioms constrainedSoftmax_sum_one
#print axioms constrainedSoftmax_support_iff_allowed
#print axioms constrained_via_maskedSoftmax
#print axioms constrained_sum_one_via_realMaskFamily
#print axioms posMask_row_is_dummy
#print axioms empty_allowed_row_sum_ne_one
#print axioms mask_actually_changes_distribution
#print axioms nonempty_allowed_row_sum_eq_one_witness
#print axioms constrained_agrees_with_constraint_set

/-! ## 二、消费者侧推论（`RealConstrainedDecodingVerify`，5 条）
全部是**下游推论**，不重复定义掩码载体。 -/

#print axioms not_allowed_contribution_zero
#print axioms mass_concentrated_on_allowed
#print axioms allowed_is_convex_weights
#print axioms support_from_decoded_constraints
#print axioms feasibility_is_caller_obligation

/-! ## 三、本文件为何 import `RealConstrainedDecoding` 而非只 `#print` 它
`#print axioms Foo.bar` 要求 `Foo` 在本文件的**环境**中已声明。
故 `import` 不是装饰，是**内联探测的必要条件**。
⭐ 由此产生的副作用是**正向**的：该 `import` 使 `RealConstrainedDecoding`
的 in-degree 由 0 变为 1（实测，见 W05 报告 §三-发现 2）。
⚠ 但**不得**据此声称「本文件消费了约束解码的数学内容」——
真正的内容消费在 `RealConstrainedDecodingVerify`（它**证明**了新推论）。
本文件消费的是**署名级**依赖（axiom probe）。
-/

end Lattice
