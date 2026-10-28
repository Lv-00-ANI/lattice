import Lattice.Runtime.ConvertLinear
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.TotalLoss
import Lattice.Lib.Lift.VerifyLoopConvergence
import Lattice.Runtime.RealTokenization
import Lattice.Runtime.RealTokenSymbolLink
import Lattice.Lib.Optim.RealListFinBridge
import Lattice.Lib.Editing.RealEditSemantics
import Lattice.Lib.Editing.RealChainEdit
import Lattice.Lib.LearningTheory.RealRecoverEndpoint
import Lattice.Lib.Chain.RealEndToEnd
/-!
# LATTICE: chain-core axiom probes, third batch (W01)

## 为什么这个文件存在

前两批（`RealChainAxioms.lean` 17 条 / `RealChainAxioms2.lean` 20 条）合计 **37** 条，
本轮起覆盖率的**分母与去重口径也一并订正**（见下），故 37 不再是对的任何一栏数字。

## ⭐ 本轮订正一：真实覆盖远高于「37」

前两批只统计了**两个独立探测文件**。实测（W01，扫描全部 roots 模块的 `#print axioms`）：
**链模块自身内联**的探测（`RealSSDBridge` 20 / `RealCrossUniverseBridge` 5 /
`RealCrossUniverseConsumer` 7 / `RealListFinBridge` 3 …）从未被计入。

| 口径 | 实测 |
|:--|:--|
| 链相关定理（21 模块） | **167** |
| 前两批口径（仅 2 个独立探测文件） | 37（其中落在链集合内 **32**） |
| **真实有 `#print axioms` 证据（含内联）** | ⭐ **69 / 167 = 41.3%** |
| 真正未探（本轮前） | **98** |

## ⚠ 本轮订正二：`RealNegativeCore` 并入分母是错的

`RealNegativeCore.lean` **不含任何 `theorem`/`lemma`** —— 它全部 7 条是 `example`
（`RealNegativeCore.lean:61-84`），探测的是**别处**声明的定理
（`reluZ_not_zeroFixing` @ `RealSymbolToWeightNonlinear.lean:79` 等）。
⇒ 它对 168 口径的贡献是 **0**，167 = 21 模块中**实际声明**的定理数。

## ⚠ 本轮订正三：引用次数**不能**单独作优先级

V05 已实测：全仓引用最高的 `roundtrip_extractVec` 是 `:= rfl`（零内容）。
故本批判据 = **引用承重 × 证明体长度**（体长注释剥离后实测），
并按「是否主定理 / 是否环关键边」人工复核。逐条体长见 §二。

## 覆盖（30 条，全部实测通过）

本文件探测的 30 条**全部**在前两批与全部内联探测之外（去重实测交集 = 0）。

## ⚠ 本文件**不**声称的内容

* **不**声称全库无 `sorryAx` —— 只覆盖这 30 条。
* **不**声称这些定理「有内容」—— 公理干净是**必要条件**，不是**充分条件**。
  ⭐ 反例已在本仓两例：`closed_loop_adds_nothing`（零公理而内容为空）、
  `roundtrip_extractVec`（全仓引用最高，却是 `rfl`）。
* ⚠ **`#print axioms` 也会撒谎**：编译失败的文件仍会打印看似干净的条目（V05 负对照 2 实测）。
  故本文件的价值**取决于**同批次 `lake build RealChainAxioms3` 返回 `exit 0` —— **双条件不可拆**。
-/

open Lattice.Lib.Chain.RealEndToEnd

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、链核心 L0⇄L1（2 条） -/

#print axioms even_combo_preserves
#print axioms forall_mem_map_iff

/-! ## 二、L1 分词/编解码环（10 条） -/

#print axioms bestPrefix_spec
#print axioms bestPrefix_ne_none
#print axioms lookupTok_eq_some
#print axioms tokAux_detok
#print axioms tokAux_ne_none
#print axioms foldGo_idem
#print axioms tokenize_detokenize_galois
#print axioms detokenize_tokenize_on_quotient
#print axioms toSegs_map_sym_append_sep
#print axioms splitLast_append_singleton

/-! ## 三、L2⇄L3 桥（1 条） -/

#print axioms dot_eq_fin_sum

/-! ## 四、L3→B 编辑语义（6 条） -/

#print axioms dot_zipWith_add_of_length
#print axioms editLayerList_outputs_eq_iff
#print axioms EditLayer_delta_not_unique
#print axioms editLayer_delta_closed_form
#print axioms editLayer_zero_delta
#print axioms decode_drops_trailing_partial

/-! ## 五、链与误差界（2 条） -/

#print axioms chain_split_at
#print axioms chain_weight_edit_bound

/-! ## 六、链尾 Recover → EndToEnd（3 条） -/

#print axioms recover_compileToLayer
#print axioms e2e_bridge_sep_is_load_bearing
#print axioms L1Bridge_length

/-! ## 七、损失与验证环（5 条） -/

#print axioms sqSum_eq_zero_iff
#print axioms sqSum_nonneg
#print axioms int_sq_nonneg
#print axioms even_loop_converges
#print axioms iterateRepairEven_add

/-! ## 八、链核心折叠（1 条） -/

#print axioms foldl_zip_add

/-! ## 九、⭐⭐⭐ B194 存在性锚点的**跨模块消费者**（B480 补遗）

⚠⚠ **为什么这一节必须存在**：`RealEditSemantics.lean` §六之三 的锚点
`b194_counterexamples_intact` 使 16 条反例**在该文件内**不可删 ——
⚠ **但它拦不住「有人把整节 §六之三 删掉」**：那样 `RealEditSemantics.lean`
**自身仍然编译通过**（锚点连同反例一起消失，文件自洽）。

⭐ **本节的定理就是那一环**：它**位于另一个 root 模块**（`RealChainAxioms3`），
**显式使用**锚点的名字。⇒ **删掉锚点 ⟹ 本模块 elaboration 失败 ⟹ `lake build` 失败**。
⇒ 这就把「锚点是叶节点」这一漏洞补上了：
锚点现在是「**被一个 root 模块消费的**」节点，而**不是**叶节点。

⚠ **诚实边界**：本定理**不**证明任何新数学 —— 它把锚点**取用一次**，
使「锚点存在」成为 `RealChainAxioms3` 通过编译的**必要条件**。
⚠ 它**也拦不住**「同时删掉两处」的蓄意破坏 —— **没有任何编译期机制**能拦住
「把所有相关文件一起删」。⭐ B194 要求的是「**删掉会编译失败**」，
而这**已由本节达成**（删任一处 ⟹ 编译失败）。 -/

/-- ⭐⭐⭐ **锚点消费者**：把 `b194_counterexamples_intact` 作为**假设**取用一次，
使「锚点存在」成为本模块编译的必要条件。

⚠ **写法说明**：必须写 `(h : Lattice.b194_counterexamples_intact)` 而**不能**写
`(h : b194_counterexamples_intact)` —— 后者会被 Lean 解析成
「**隐式绑定一个名为 `b194_counterexamples_intact` 的类型变量**」
（`def … : Prop` 不像 `theorem` 那样自动把同名命题当作类型可用），
于是定理类型变成 `{b : Sort u} → b → b`，报
`type of theorem … is not a proposition`。⇒ 用**限定名**消除歧义。 -/
theorem b194_anchor_consumer : Lattice.b194_counterexamples_intact :=
    Lattice.b194_counterexamples_intact_holds

/- ⭐ **锚点的公理卫生留痕**（与本节其它 `#print axioms` 同形）：
⚠ 本行**本身不构成**存在性强制，只是登记它不依赖 `sorryAx`。 -/
#print axioms b194_anchor_consumer

end Lattice
