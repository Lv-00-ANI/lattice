# 端到端普查（**按内容**，不是按名字）

> 由 `gov/check_endtoend_content.py` 生成。**这是普查，不是门禁**：
> 只碰一层的定理**不是缺陷**；声称跨层而没跨才是，那由 `gate.py` 的 I5 抓。

## 为什么需要它

I5 **已经**做内容分析（传递解析短名到层），**但它只对名字匹配 `e2e` / `end_to_end` 的定理跑**。
第 219 轮实测：8,501 条里 **36 条**按名字命中，**全在 `Lib`，`Geo` 零条**——
所以链路真正的跨层工作**不在 I5 的覆盖内**，不是因为它是层内的，而是**因为没人给它起那个名字**。

本脚本对**每条**定理跑同一套分析，给出分布。

## 分布（去掉定理自己所在的那一层）

| 触及的其他层数 | 定理数 | 占比 |
|--:|--:|--:|
| 0 | 5363 | 62.6% |
| 1 | 1270 | 14.8% |
| 2 | 797 | 9.3% |
| 3 | 477 | 5.6% |
| 4 | 514 | 6.0% |
| 5 | 137 | 1.6% |
| 6 | 4 | 0.0% |
| **合计** | **8562** | |

## 跨 ≥ 2 层（按层数降序，最多 60 条）

| 层数 | 定理 | 触及的层 |
|--:|:--|:--|
| 6 | `decode_encode` (`Runtime/EndToEnd.lean`) | Audit, Core, Geo, Lib, Lift, root |
| 6 | `encode_injective` (`Runtime/EndToEnd.lean`) | Audit, Core, Geo, Lib, Lift, root |
| 6 | `Text.encode_injective` (`Runtime/RealTokenizationEntry.lean`) | Audit, Core, Geo, Lib, Lift, root |
| 6 | `tokenizeStr_detok` (`Runtime/RealTokenizationEntry.lean`) | Audit, Core, Geo, Lib, Lift, root |
| 5 | `no_redundant_hypotheses` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `chainAudit_length` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `every_judgement_carries_a_reason` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `commutativeBlock_trivial` (`Audit/PredicateWitnesses.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `census_length` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `repair_is_densest` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `total_obligations` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `no_zero_obligation_structure` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `eqConstraint_loss_le_sq_of_resid_le` (`Geo/ApproxEmbedding.lean`) | Core, Lib, Lift, Semantics, root |
| 5 | `codegenLadder_forward` (`Geo/CodegenLadder.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `codegenLadder_satW_iff` (`Geo/CodegenLadder.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `codegenLadder_l2l3_changes_representation` (`Geo/CodegenLadder.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `eqConstraintListTokenizer_two` (`Geo/EqConstraintListTokens.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `eqConstraintTokenizer_nontrivial` (`Geo/EqConstraintTokens.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `eqConstraintTokenizer_roundtrip` (`Geo/EqConstraintTokens.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `eqConstraintTokenizer_roundtrip_expr` (`Geo/EqConstraintTokens.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `geoLadder_forward` (`Geo/GeoLadder.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `ladder_crosses_geo_layer` (`Geo/GeoLadder.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `l1l2_is_real_tokenizer` (`Geo/GeoLadder.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `linearLadder_l1l2_roundtrip` (`Geo/LadderInstance.lean`) | Audit, Core, Lib, Lift, root |
| 5 | `loss_le_sq_of_resid_le` (`Geo/PartialReinjection.lean`) | Core, Lib, Lift, Semantics, root |
| 5 | `partial_reinject_bound` (`Geo/PartialReinjection.lean`) | Core, Lib, Lift, Semantics, root |
| 5 | `exact_is_zero` (`Geo/PartialReinjection.lean`) | Core, Lib, Lift, Semantics, root |
| 5 | `error_to_penalty` (`Geo/PartialReinjection.lean`) | Core, Lib, Lift, Semantics, root |
| 5 | `structural_loss_propagates_but_symbol_layer_is_lossless` (`Lib/Chain/RealE2EComposite.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `losses_are_not_mutually_reducible` (`Lib/Chain/RealE2EComposite.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `e2e_loss_compound` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `e2e_L1L2_is_lossless` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `recover_readback` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `recover_is_load_bearing` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `d41_e2e_length_conservation` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `d41_e2e_length_conservation_is_ts_only` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `d41_e2e_neurons_bounded_by_data` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `d41_two_scale_loss_coexist` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `d41_loss_locality` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `e2e_loss_strictly_compounds` (`Lib/Chain/RealEndToEndStrict.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `e2e_L1L2_cannot_absorb_L2L3_loss` (`Lib/Chain/RealEndToEndStrict.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `e2e_sameLayer_comp_is_wellTyped` (`Lib/Chain/RealEndToEndStrict.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `compile_program_append` (`Lib/Compiler/RealLv00CompilerReal.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `compile_program_contains_compiled_constraints` (`Lib/Compiler/RealLv00CompilerReal.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `compile_program_vars_subset` (`Lib/Compiler/RealLv00CompilerSat.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `compile_append_satisfiable` (`Lib/Compiler/RealLv00CompilerSat.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `compile_preserves_satisfiability` (`Lib/Compiler/RealLv00CompilerSpec.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `compile_preserves_satisfiability_hypothesis_unused` (`Lib/Compiler/RealLv00CompilerSpec.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `three_rings_quotient_dichotomy` (`Lib/Editing/RealClosureReversibility.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `cEx_actAllZero_neg5` (`Lib/Editing/RealCompileExtractClosed.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `activated_loop_breaks` (`Lib/Editing/RealCompileExtractClosed.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `activated_extract_cannot_repair` (`Lib/Editing/RealCompileExtractClosed.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `activated_closure_iff_zeroFixing` (`Lib/Editing/RealCompileExtractClosed.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `honesty_register` (`Lib/Editing/RealCompileExtractClosed.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `compileToLayer_append_assoc` (`Lib/Editing/RealConversionComposition.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `compileToLayer_append_assoc_layer` (`Lib/Editing/RealConversionComposition.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `edit_breaks_zeroing_generically` (`Lib/Editing/RealEditInvariantCatalog.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `edited_activated_zero_iff_residual` (`Lib/Editing/RealEditInvariantCatalog.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `any_edit_relation_gives_symbol_preimage` (`Lib/Editing/RealEditToSymbol.lean`) | Core, Geo, Lift, Semantics, root |
| 5 | `compile_commutes_symEdit_iff_nil` (`Lib/Editing/RealEditTwoSidedSquare.lean`) | Audit, Core, Geo, Lift, root |

## ⚠ 层数高**不等于**更端到端

按层数排在最前面的那批是**审计自指**（`census_length`、`repair_is_densest`、`total_obligations`……），
它们经由审计自己的依赖图传递触及四层。**审计已经把它们判为 `register` 债**，理由正是
「这是审计**自指**，不是审计结果」。

**所以本表不能按层数排序当作「链路完整度」读。** 它度量的是「依赖图的深度」，
而审计机器本身会人为加深依赖图。**真正的链路内容要看具体定理在说什么，不是看它的 `k`。**

## 这份普查自己的边界

- **层取自定义模块的顶层目录**。声明在层间移动会改变普查——那是有意的。
- **传递性意味着「依赖」而不是「陈述关于」**。一条定理可以通过辅助引理触及三层，
  而它自己的陈述只关于一层。**这是跨层程度的上界。**
- **不要把它接成门禁**：0 层定理是合法的（纯 `Mathlib` 陈述）。
