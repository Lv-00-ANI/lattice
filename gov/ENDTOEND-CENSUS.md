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
| 0 | 5410 | 62.9% |
| 1 | 1369 | 15.9% |
| 2 | 628 | 7.3% |
| 3 | 545 | 6.3% |
| 4 | 443 | 5.2% |
| 5 | 185 | 2.2% |
| 6 | 16 | 0.2% |
| **合计** | **8596** | |

## 跨 ≥ 2 层（按层数降序，最多 60 条）

| 层数 | 定理 | 触及的层 |
|--:|:--|:--|
| 6 | `abiTable_length` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `abiTable_names_nodup` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `abiTable_errors_wellFormed` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `abiTable_returns_a_value` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `primitiveNames_eq_abi` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `preserves_iterate` (`Evidence/ChainTransitivity.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `loop_preserves` (`Evidence/ChainTransitivity.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `no_redundant_entries_in_audit_table` (`Evidence/Hypotheses.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `chainAudit_length` (`Evidence/Hypotheses.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `every_judgement_carries_a_reason` (`Evidence/Hypotheses.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `bidir_steps` (`Primitives/MultistepLoop.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `multistep_geometric_exists` (`Primitives/MultistepLoop.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `edit_apply_idempotent_of_no_add` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `edit_apply_not_idempotent_of_add` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `post_train_preserves_holds` (`Semantics/PostTrain.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `post_train_preserves_set` (`Semantics/PostTrain.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 5 | `descentStep_sound` (`Compose/ForwardChain.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `forward_chain_capstone` (`Compose/ForwardChain.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `forward_chain_at_solution` (`Compose/ForwardChain.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `Reaches.meas_add_le` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `Reaches.length_le` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `loop_done` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `loop_step` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `loop_zero_none` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `loop_mono` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `loop_witness` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `iterate_sound` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `iterate_strength` (`Compose/Iterate.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `optional_true_run` (`Compose/Laws.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `optional_false_run` (`Compose/Laws.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `optional_sound` (`Compose/More.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `optional_strength` (`Compose/More.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `IdempotentOn.iterate` (`Core/Idempotent.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `iterate_comp_of_leftInverse` (`Core/Idempotent.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `preserves_of_sat` (`Core/Invariant.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `oneStepRepair_converges` (`Core/OneStepBridge.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `oneStepRepair_one_step` (`Core/OneStepBridge.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `natCountdownAsRepair_converges` (`Core/OneStepBridge.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `bridge_exists` (`Core/OneStepBridge.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `iterate_succ` (`Core/Repair.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `progress` (`Core/Repair.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `preserves` (`Core/Repair.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `parity_terminates` (`Core/Repair.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `down_stays_neg` (`Core/Repair.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `down_no_progress` (`Core/Repair.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `converges_within` (`Core/RepairConvergence.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `converges_within_steps` (`Core/RepairConvergence.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `progress_of_rate` (`Core/RepairConvergence.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `countdown_iterate` (`Core/RepairMultistep.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `countdown_converges_in` (`Core/RepairMultistep.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `no_uniform_bound` (`Core/RepairMultistep.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `converges_within_is_tight` (`Core/RepairMultistep.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `iterate_succ` (`Core/RepairWF.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `iterate_shift` (`Core/RepairWF.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `progress_on_wf` (`Core/RepairWF.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `preserves_of_sat` (`Core/RepairWF.lean`) | Compose, Domains, Lib, Runtime, root |
| 5 | `repair_then_reinject` (`Domains/Geometry/ClauseComposition.lean`) | Compose, Core, Lib, Runtime, root |
| 5 | `rate_then_repair` (`Domains/Geometry/ClauseComposition.lean`) | Compose, Core, Lib, Runtime, root |
| 5 | `geometric_loop_fixed_point` (`Domains/Geometry/ClosedLoop.lean`) | Compose, Core, Lib, Runtime, root |
| 5 | `geometric_loop_reaches_satisfied` (`Domains/Geometry/ClosedLoop.lean`) | Compose, Core, Lib, Runtime, root |

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
