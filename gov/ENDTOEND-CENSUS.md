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
| 0 | 5450 | 63.7% |
| 1 | 1346 | 15.7% |
| 2 | 669 | 7.8% |
| 3 | 377 | 4.4% |
| 4 | 597 | 7.0% |
| 5 | 120 | 1.4% |
| 6 | 2 | 0.0% |
| **合计** | **8561** | |

## 跨 ≥ 2 层（按层数降序，最多 60 条）

| 层数 | 定理 | 触及的层 |
|--:|:--|:--|
| 6 | `edit_apply_idempotent_of_no_add` (`Semantics/Annotations.lean`) | Audit, Core, Geo, Lib, Lift, root |
| 6 | `edit_apply_not_idempotent_of_add` (`Semantics/Annotations.lean`) | Audit, Core, Geo, Lib, Lift, root |
| 5 | `preserves_iterate` (`Audit/ChainTransitivity.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `loop_preserves` (`Audit/ChainTransitivity.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `no_redundant_hypotheses` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `chainAudit_length` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `every_judgement_carries_a_reason` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `commutativeBlock_trivial` (`Audit/PredicateWitnesses.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `census_length` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `repair_is_densest` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `total_obligations` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `no_zero_obligation_structure` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_sound` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `composeWith_sound` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_run` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `composeWith_run` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_strength` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_coverage` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_run_assoc` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `identity_compose_run` (`Compose/Combinators.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `descentStep_sound` (`Compose/ForwardChain.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `forward_chain_capstone` (`Compose/ForwardChain.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `forward_chain_at_solution` (`Compose/ForwardChain.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `Reaches.meas_add_le` (`Compose/Iterate.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `Reaches.length_le` (`Compose/Iterate.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `loop_done` (`Compose/Iterate.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `loop_step` (`Compose/Iterate.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `loop_zero_none` (`Compose/Iterate.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `loop_mono` (`Compose/Iterate.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `iterate_sound` (`Compose/Iterate.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `iterate_strength` (`Compose/Iterate.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `parallel_run` (`Compose/Laws.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `parallel_comm_run` (`Compose/Laws.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `parallel_identity_run` (`Compose/Laws.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `choice_self_run` (`Compose/Laws.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `optional_true_run` (`Compose/Laws.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `optional_false_run` (`Compose/Laws.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_identity_right` (`Compose/Laws.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `compose_choice_distrib_run` (`Compose/Laws.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `parallel_sound` (`Compose/More.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `parallel_strength` (`Compose/More.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `parallel_coverage` (`Compose/More.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `choice_sound` (`Compose/More.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `choice_strength` (`Compose/More.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `choice_coverage` (`Compose/More.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `optional_sound` (`Compose/More.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `optional_strength` (`Compose/More.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `Primitive.withCoverage_sound` (`Compose/Primitive.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `MatrixRow.strength_eq` (`Compose/Registry.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `foldStrength_le_of_mem` (`Compose/Registry.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `exact_of_foldStrength_exact` (`Compose/Registry.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `applySgd_run` (`Compose/Steps.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `applyMomentum_velocity` (`Compose/Steps.lean`) | Core, Geo, Lib, Lift, root |
| 5 | `losses_are_not_mutually_reducible` (`Lib/Chain/RealE2EComposite.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `e2e_loss_compound` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `all_twelve_discharged` (`Lib/Chain/RealLv00AxiomDischargeSummary.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `go_hypotheses_pushes_aux` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `go_hypotheses_pushes` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `trivialProofTrace_passes` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift, root |
| 5 | `go_hypotheses_eq` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Core, Geo, Lift, root |

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
