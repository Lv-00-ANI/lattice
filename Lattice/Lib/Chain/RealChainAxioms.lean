import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lib.Optim.RealListFinBridge
import Lattice.Lib.LearningTheory.RealRecoverEndpoint
import Lattice.Lib.Chain.RealEndToEnd
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Meta.RealNegativeCore
import Lattice.Lib.Editing.RealEditSemantics
import Lattice.Lib.Chain.RealCrossUniverseConsumer
import Lattice.Lib.LearningTheory.RealSCMIdentification
import Lattice.Lib.Editing.RealReversibilityBoundary
import Lattice.Lift.RealTokenization
import Lattice.Lift.RealTokenSymbolLink
/-!
# LATTICE: chain-core axiom probes (U06 judgement C)

## 为什么这个文件存在

本项目确立的验收判据是**双条件**：`lake build <Module>` 返回 `exit 0`，**且**该模块的定理
`#print axioms` 不出现 `sorryAx`。⭐ **但第二条从未对链的核心定理执行过** ——
实测（U06 @B443）：全 roots 共 **230 条** `#print axioms` 探测，其中**链核心定理只有 1 条**。

判据写了、工具有了、**没有任何东西把它们连起来**。

## 覆盖（17 条，全部实测通过）

### 六条主链承重定理
```
symbolToWeight_correct          [propext, Quot.sound]
convertVec_preserves_semantics  [propext]
dot_eq_dotProduct               [propext, Classical.choice, Quot.sound]
recover_injective               [propext]
recover_readback                [propext, Quot.sound]
e2e_path_exists                 [propext, Classical.choice, Quot.sound]
```

### 十一条环/边界定理（与下文 §二 的条数一致）
```
convertVec_preserves_solution_set   [propext, Quot.sound]
foldBlanks_idem                     [propext]
mkConstraint_append_singleton       ⭐ 零公理
closed_loop_adds_nothing            ⭐ 零公理
activated_closure_iff_zeroFixing    [propext, Quot.sound]
no_extractor_preserves_both         [propext]
layerOut_not_injective              [propext, Quot.sound]
editSemantics_layer_zero_iff        [propext, Classical.choice, Quot.sound]
vectorConstraintSat_iff_clm         [propext, Classical.choice, Quot.sound]
no_function_recovers_do             [propext, Classical.choice, Quot.sound]
semantic_layer_not_injective        [propext, Classical.choice, Quot.sound]
```

**全部 ⊆ `{propext, Classical.choice, Quot.sound}`，无一含 `sorryAx`。**
与 mathlib 官方判据 <https://leanprover-community.github.io/did_you_prove_it.html> 一致。

⭐ **两条零公理**（`mkConstraint_append_singleton` / `closed_loop_adds_nothing`）
是**真**的「不依赖任何公理」，与「依赖一个小的标准集」是不同强度的事实。

## ⚠ 本文件**不**声称的内容

* **不**声称全库无 `sorryAx` —— 只覆盖这 17 条；链相关定理约 187 条，覆盖率 **17/187 ≈ 9.1%**。
* **不**声称这些定理「有内容」—— 公理干净是**必要条件**，不是**充分条件**。
  ⭐ 本文件探测的 `closed_loop_adds_nothing` **正是反例**：它零公理，而其内容是
  「闭环陈述 ⟺ 单向陈述」= **不携带新信息**。⟹ **公理卫生说明证明没作弊，
  不说定理是否值得陈述。两者是独立的问题。**
* ⚠ **`#print axioms` 也会撒谎**（本会话实测）：编译失败的文件仍会列出定理且公理看似干净。
  故本文件的价值**取决于**同批次 `lake build` 也返回 `exit 0` —— **双条件不可拆**。
-/

open Lattice.Lib.Chain.RealEndToEnd

open Lattice.Lib.Editing.RealReversibilityBoundary

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice
/-! ## 一、主链承重定理（6 条） -/

#print axioms symbolToWeight_correct
#print axioms convertVec_preserves_semantics
#print axioms dot_eq_dotProduct
#print axioms recover_injective
#print axioms recover_readback
#print axioms e2e_path_exists

/-! ## 二、环与边界定理（11 条，含 2 条零公理） -/

#print axioms convertVec_preserves_solution_set
#print axioms foldBlanks_idem
#print axioms mkConstraint_append_singleton
#print axioms closed_loop_adds_nothing
#print axioms activated_closure_iff_zeroFixing
#print axioms no_extractor_preserves_both
#print axioms layerOut_not_injective
#print axioms editSemantics_layer_zero_iff
#print axioms vectorConstraintSat_iff_clm
#print axioms no_function_recovers_do
#print axioms semantic_layer_not_injective

end Lattice

-- rebuild-forced probe (removed by scripts/rebuild-forced.ps1)
