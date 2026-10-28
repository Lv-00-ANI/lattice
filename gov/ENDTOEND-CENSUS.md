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
| 0 | 5471 | 64.2% |
| 1 | 1348 | 15.8% |
| 2 | 865 | 10.1% |
| 3 | 727 | 8.5% |
| 4 | 107 | 1.3% |
| 5 | 8 | 0.1% |
| **合计** | **8526** | |

## 跨 ≥ 2 层（按层数降序，最多 60 条）

| 层数 | 定理 | 触及的层 |
|--:|:--|:--|
| 5 | `compose_sound` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_strength` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_coverage` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_run` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_run_assoc` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `identity_compose_run` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `Primitive.withCoverage_sound` (`Compose/Primitive.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `fullRegistry_wellFormed` (`Slots.lean`) | Audit, Core, Geo, Lib, Lift |
| 4 | `no_redundant_hypotheses` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift |
| 4 | `chainAudit_length` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift |
| 4 | `every_judgement_carries_a_reason` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift |
| 4 | `commutativeBlock_trivial` (`Audit/PredicateWitnesses.lean`) | Core, Geo, Lib, Lift |
| 4 | `census_length` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift |
| 4 | `repair_is_densest` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift |
| 4 | `total_obligations` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift |
| 4 | `no_zero_obligation_structure` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift |
| 4 | `compose_act` (`Core/VariableNet.lean`) | Geo, Lib, Lift, root |
| 4 | `eqConstraint_loss_le_sq_of_resid_le` (`Geo/ApproxEmbedding.lean`) | Core, Lib, Lift, Semantics |
| 4 | `codegenLadder_forward` (`Geo/CodegenLadder.lean`) | Audit, Core, Lib, Lift |
| 4 | `codegenLadder_satW_iff` (`Geo/CodegenLadder.lean`) | Audit, Core, Lib, Lift |
| 4 | `codegenLadder_l2l3_changes_representation` (`Geo/CodegenLadder.lean`) | Audit, Core, Lib, Lift |
| 4 | `eqConstraintListTokenizer_two` (`Geo/EqConstraintListTokens.lean`) | Audit, Core, Lib, Lift |
| 4 | `eqConstraintTokenizer_nontrivial` (`Geo/EqConstraintTokens.lean`) | Audit, Core, Lib, Lift |
| 4 | `eqConstraintTokenizer_roundtrip` (`Geo/EqConstraintTokens.lean`) | Audit, Core, Lib, Lift |
| 4 | `eqConstraintTokenizer_roundtrip_expr` (`Geo/EqConstraintTokens.lean`) | Audit, Core, Lib, Lift |
| 4 | `geoLadder_forward` (`Geo/GeoLadder.lean`) | Audit, Core, Lib, Lift |
| 4 | `ladder_crosses_geo_layer` (`Geo/GeoLadder.lean`) | Audit, Core, Lib, Lift |
| 4 | `l1l2_is_real_tokenizer` (`Geo/GeoLadder.lean`) | Audit, Core, Lib, Lift |
| 4 | `linearLadder_l1l2_roundtrip` (`Geo/LadderInstance.lean`) | Audit, Core, Lib, Lift |
| 4 | `loss_le_sq_of_resid_le` (`Geo/PartialReinjection.lean`) | Core, Lib, Lift, Semantics |
| 4 | `partial_reinject_bound` (`Geo/PartialReinjection.lean`) | Core, Lib, Lift, Semantics |
| 4 | `exact_is_zero` (`Geo/PartialReinjection.lean`) | Core, Lib, Lift, Semantics |
| 4 | `error_to_penalty` (`Geo/PartialReinjection.lean`) | Core, Lib, Lift, Semantics |
| 4 | `structural_loss_propagates_but_symbol_layer_is_lossless` (`Lib/Chain/RealE2EComposite.lean`) | Audit, Core, Geo, Lift |
| 4 | `losses_are_not_mutually_reducible` (`Lib/Chain/RealE2EComposite.lean`) | Audit, Core, Geo, Lift |
| 4 | `e2e_loss_compound` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift |
| 4 | `e2e_L1L2_is_lossless` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift |
| 4 | `recover_readback` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift |
| 4 | `recover_is_load_bearing` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift |
| 4 | `d41_e2e_length_conservation` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift |
| 4 | `d41_e2e_length_conservation_is_ts_only` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift |
| 4 | `d41_e2e_neurons_bounded_by_data` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift |
| 4 | `d41_two_scale_loss_coexist` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift |
| 4 | `d41_loss_locality` (`Lib/Chain/RealEndToEndNontrivial.lean`) | Audit, Core, Geo, Lift |
| 4 | `e2e_loss_strictly_compounds` (`Lib/Chain/RealEndToEndStrict.lean`) | Audit, Core, Geo, Lift |
| 4 | `e2e_L1L2_cannot_absorb_L2L3_loss` (`Lib/Chain/RealEndToEndStrict.lean`) | Audit, Core, Geo, Lift |
| 4 | `e2e_sameLayer_comp_is_wellTyped` (`Lib/Chain/RealEndToEndStrict.lean`) | Audit, Core, Geo, Lift |
| 4 | `chainLift_two` (`Lib/Chain/RealGaloisChainLift.lean`) | Core, Geo, Lift, root |
| 4 | `go_hypotheses_pushes_aux` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift |
| 4 | `go_hypotheses_pushes` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift |
| 4 | `trivialProofTrace_passes` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift |
| 4 | `go_hypotheses_eq` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift |
| 4 | `evidenceCheck_accepts_unsatisfiable` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift |
| 4 | `evidenceCheck_unsound_exists` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift |
| 4 | `run_append` (`Lib/Compiler/RealCompilerCorrectness.lean`) | Audit, Core, Geo, Lift |
| 4 | `compile_correct` (`Lib/Compiler/RealCompilerCorrectness.lean`) | Audit, Core, Geo, Lift |
| 4 | `compile_correct_empty` (`Lib/Compiler/RealCompilerCorrectness.lean`) | Audit, Core, Geo, Lift |
| 4 | `run_append` (`Lib/Compiler/RealConcurrentSemantics.lean`) | Audit, Core, Geo, Lift |
| 4 | `compile_program_go_append` (`Lib/Compiler/RealLv00CompilerReal.lean`) | Audit, Core, Geo, Lift |
| 4 | `compile_program_append` (`Lib/Compiler/RealLv00CompilerReal.lean`) | Audit, Core, Geo, Lift |

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
