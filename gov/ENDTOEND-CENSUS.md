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
| 0 | 5337 | 62.3% |
| 1 | 1398 | 16.3% |
| 2 | 674 | 7.9% |
| 3 | 838 | 9.8% |
| 4 | 301 | 3.5% |
| 5 | 14 | 0.2% |
| **合计** | **8562** | |

## 跨 ≥ 2 层（按层数降序，最多 60 条）

| 层数 | 定理 | 触及的层 |
|--:|:--|:--|
| 5 | `activationLadder_forward` (`Runtime/ActivationLadder.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `activationLadder_l2l3_is_a_split` (`Runtime/ActivationLadder.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `decode_encode` (`Runtime/EndToEnd.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `encode_injective` (`Runtime/EndToEnd.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `residue_bound_of_zero_sample` (`Runtime/EndToEndApproximation.lean`) | Core, Geo, Lib, Semantics, root |
| 5 | `loss_le_sq_of_resid_le` (`Runtime/EndToEndApproximation.lean`) | Core, Geo, Lib, Semantics, root |
| 5 | `encode_cons_eq` (`Runtime/RealTokenSymbolLink.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `decode_encode` (`Runtime/RealTokenSymbolLink.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `encode_injective` (`Runtime/RealTokenSymbolLink.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `decode_encode_sat_iff` (`Runtime/RealTokenSymbolLink.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `Text.encode_injective` (`Runtime/RealTokenizationEntry.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `tokenizeStr_detok` (`Runtime/RealTokenizationEntry.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `edit_apply_idempotent_of_no_add` (`Semantics/Annotations.lean`) | Audit, Core, Geo, Lib, root |
| 5 | `edit_apply_not_idempotent_of_add` (`Semantics/Annotations.lean`) | Audit, Core, Geo, Lib, root |
| 4 | `preserves_iterate` (`Audit/ChainTransitivity.lean`) | Core, Geo, Lib, root |
| 4 | `loop_preserves` (`Audit/ChainTransitivity.lean`) | Core, Geo, Lib, root |
| 4 | `no_redundant_hypotheses` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, root |
| 4 | `chainAudit_length` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, root |
| 4 | `every_judgement_carries_a_reason` (`Audit/Hypotheses.lean`) | Core, Geo, Lib, root |
| 4 | `commutativeBlock_trivial` (`Audit/PredicateWitnesses.lean`) | Core, Geo, Lib, root |
| 4 | `census_length` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, root |
| 4 | `repair_is_densest` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, root |
| 4 | `total_obligations` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, root |
| 4 | `no_zero_obligation_structure` (`Audit/StructureCensus.lean`) | Core, Geo, Lib, root |
| 4 | `compose_sound` (`Compose/Combinators.lean`) | Core, Geo, Lib, root |
| 4 | `composeWith_sound` (`Compose/Combinators.lean`) | Core, Geo, Lib, root |
| 4 | `compose_run` (`Compose/Combinators.lean`) | Core, Geo, Lib, root |
| 4 | `composeWith_run` (`Compose/Combinators.lean`) | Core, Geo, Lib, root |
| 4 | `compose_strength` (`Compose/Combinators.lean`) | Core, Geo, Lib, root |
| 4 | `compose_coverage` (`Compose/Combinators.lean`) | Core, Geo, Lib, root |
| 4 | `compose_run_assoc` (`Compose/Combinators.lean`) | Core, Geo, Lib, root |
| 4 | `identity_compose_run` (`Compose/Combinators.lean`) | Core, Geo, Lib, root |
| 4 | `descentStep_sound` (`Compose/ForwardChain.lean`) | Core, Geo, Lib, root |
| 4 | `forward_chain_capstone` (`Compose/ForwardChain.lean`) | Core, Geo, Lib, root |
| 4 | `forward_chain_at_solution` (`Compose/ForwardChain.lean`) | Core, Geo, Lib, root |
| 4 | `Reaches.meas_add_le` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `Reaches.length_le` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `loop_done` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `loop_step` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `loop_zero_none` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `loop_mono` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `loop_witness` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `iterate_sound` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `iterate_strength` (`Compose/Iterate.lean`) | Core, Geo, Lib, root |
| 4 | `parallel_run` (`Compose/Laws.lean`) | Core, Geo, Lib, root |
| 4 | `parallel_comm_run` (`Compose/Laws.lean`) | Core, Geo, Lib, root |
| 4 | `parallel_identity_run` (`Compose/Laws.lean`) | Core, Geo, Lib, root |
| 4 | `choice_self_run` (`Compose/Laws.lean`) | Core, Geo, Lib, root |
| 4 | `optional_true_run` (`Compose/Laws.lean`) | Core, Geo, Lib, root |
| 4 | `optional_false_run` (`Compose/Laws.lean`) | Core, Geo, Lib, root |
| 4 | `compose_identity_right` (`Compose/Laws.lean`) | Core, Geo, Lib, root |
| 4 | `compose_choice_distrib_run` (`Compose/Laws.lean`) | Core, Geo, Lib, root |
| 4 | `parallel_sound` (`Compose/More.lean`) | Core, Geo, Lib, root |
| 4 | `parallel_strength` (`Compose/More.lean`) | Core, Geo, Lib, root |
| 4 | `parallel_coverage` (`Compose/More.lean`) | Core, Geo, Lib, root |
| 4 | `choice_sound` (`Compose/More.lean`) | Core, Geo, Lib, root |
| 4 | `choice_strength` (`Compose/More.lean`) | Core, Geo, Lib, root |
| 4 | `choice_coverage` (`Compose/More.lean`) | Core, Geo, Lib, root |
| 4 | `optional_sound` (`Compose/More.lean`) | Core, Geo, Lib, root |
| 4 | `optional_strength` (`Compose/More.lean`) | Core, Geo, Lib, root |

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
