import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.ConvertLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Runtime.ConstraintEmbeddingSoundness
import Lattice.Lift.TotalLoss
import Lattice.Runtime.VerifyLoopProgress
import Lattice.Lib.Lift.VerifyLoopConvergence
import Lattice.Runtime.RealTokenization
import Lattice.Runtime.RealTokenSymbolLink
import Lattice.Lib.Editing.RealEditSemantics
import Lattice.Lib.Optim.RealListFinBridge
import Lattice.Lib.Optim.RealCrossUniverseBridge
import Lattice.Lib.Chain.RealCrossUniverseConsumer
import Lattice.Lib.LearningTheory.RealRecoverEndpoint
import Lattice.Lib.Chain.RealEndToEnd
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Editing.RealChainEdit
/-!
# LATTICE: chain-core axiom probes, second batch (V05)

## 为什么这个文件存在

`RealChainAxioms.lean`（B452/B453）对 **17** 条链承重定理加了 `#print axioms` 探测。
链相关定理总数实测为 **168** 条（口径见下），故仍有 **151 条未探测**。

本文件是第一轮**机械排产**后的增量：从 168 条中按三维判据选出 **20 条**最该优先探测的定理。

## 分母口径（可复现）

**链相关定理** = 声明落在这 21 个模块里的 `theorem`/`lemma`：

```
L0⇄L1  ConvertLinear, ConvertVectorLinear, SymbolToWeightCorrectness,
       WeightToSymbolEquivalence, ConstraintEmbeddingSoundness, TotalLoss,
       VerifyLoopProgress, VerifyLoopConvergence
L1     RealTokenization, RealTokenSymbolLink
L2⇄L3  RealListFinBridge, RealCrossUniverseBridge, RealCrossUniverseConsumer
L3→B   RealEditSemantics
B→Rec  RealRecoverEndpoint, RealEndToEnd
链     RealChain, RealChainEdit, RealNegativeCore, RealSSDBridge, RealAttentionCoreBridge
```

实测：**168** 条。B452/B453 已探 17 条，其中 **12** 条落在本集合内
（另 5 条 `dot_eq_dotProduct`/`recover_readback`/`e2e_path_exists`/`convertVec_preserves_solution_set`/
`vectorConstraintSat_iff_clm` 的声明不在上述链模块，属外围）。

⇒ **本文件覆盖 20/168 ≈ 11.9%；两批合计 37/168 ≈ 22.0%。**

## ⭐ 为什么是这 20 条（判据）

对 168 条逐条计算**跨模块被引用次数**（在全部 527 个 roots 模块中出现、且出现处不是自己的声明模块），
再按 **承重（跨模块引用）/ 是否主定理 / 是否环的关键边** 三维取 Top20。

最高一条 `roundtrip_extractVec` 被 **23 个不同模块**引用（全仓最高），
次高 `scaleVec_preserves`（**已在** `RealContractAxioms.lean:91` 探过）。详见 `notes/sweep9/V05-*.md`。

## ⚠ 本文件**不**声称的内容

* **不**声称全库无 `sorryAx` —— 只覆盖这 20 条。
* **不**声称这些定理「有内容」—— 公理干净是**必要条件**。
  ⭐ 反例已在本仓：`closed_loop_adds_nothing` 零公理而内容为空（见 `RealChainAxioms.lean`）。
* ⚠ **`#print axioms` 也会撒谎**：编译失败的文件仍会打印看似干净的条目。
  故价值**取决于**同批次 `lake build RealChainAxioms2` 返回 `exit 0` —— **双条件不可拆**。

## ⚠ 与前一批的去重（硬要求）

本文件**不**重复 `RealChainAxioms.lean` 已有的 17 条。已实测：
与本文件 20 条的交集 = **0**。
-/

open Lattice.Lib.Chain.RealEndToEnd

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、L2⇄L3 环：抽出/往返侧主定理（1 条） -/

#print axioms roundtrip_extractVec

/-! ## 二、链核心 `ConvertVectorLinear` / `ConvertLinear`（3 条） -/

#print axioms foldl_init_add
#print axioms dot_map_mul
#print axioms convert_preserves_semantics

/-! ## 三、L0⇄L1：分词与编解码环（6 条） -/

#print axioms decode_encode
#print axioms encode_injective
#print axioms tokenize_never_none
#print axioms tokenize_detok
#print axioms tokenize_not_injective
#print axioms detokenize_left_inverse_on_quotient

/-! ## 四、链的误差界与编辑局部性（2 条） -/

#print axioms chain_edit_locality
#print axioms chainN_error_bound

/-! ## 五、约束嵌入可靠性内核与损失（1 条） -/

#print axioms int_sq_eq_zero_iff

/-! ## 六、链尾：Recover → EndToEnd（3 条） -/

#print axioms extractVec_injective_recover
#print axioms compileToLayer_injective
#print axioms semantic_not_injective

/-! ## 七、跨宇宙桥 L2⇄L3（4 条） -/

#print axioms layerOut_cast_eq_clm
#print axioms layerToCLM_apply
#print axioms symDot_eq_realDot
#print axioms realDot_eq_symDot_cast

end Lattice
