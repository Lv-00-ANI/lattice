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
| 0 | 5559 | 61.0% |
| 1 | 1420 | 15.6% |
| 2 | 755 | 8.3% |
| 3 | 624 | 6.8% |
| 4 | 525 | 5.8% |
| 5 | 204 | 2.2% |
| 6 | 27 | 0.3% |
| **合计** | **9114** | |

## 跨 ≥ 2 层（按层数降序，最多 60 条）

| 层数 | 定理 | 触及的层 |
|--:|:--|:--|
| 6 | `abiTable_length` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `abiTable_names_nodup` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `abiTable_errors_wellFormed` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `abiTable_returns_a_value` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `abiTable_names_eq_verified` (`CInterface/ABI.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `conformance_length` (`CInterface/Conformance.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `conformance_names_dedup_length` (`CInterface/Conformance.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `conformance_names_eq_abi` (`CInterface/Conformance.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `conformance_iff_abi` (`CInterface/Conformance.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `every_primitive_has_boundary` (`CInterface/Conformance.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `boundaryPrimitives_nodup` (`CInterface/Conformance.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `interior_length` (`CInterface/Conformance.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `abiTable_compose_args` (`CInterface/ContractBoundary.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `exists_abi_entry_without_data_parameter` (`CInterface/ContractBoundary.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `seven_primitives_float_inputs_have_no_f64_slot` (`CInterface/ContractBoundary.lean`) | Compose, Core, Domains, Lib, Runtime, root |
| 6 | `three_primitives_have_too_few_f64_slots` (`CInterface/ContractBoundary.lean`) | Compose, Core, Domains, Lib, Runtime, root |
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
| 5 | `encoded_layer_size` (`CInterface/LayoutBytes.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `valuePrimitives_length` (`Compose/AdapterMatrix.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `combinatorPrimitives_length` (`Compose/AdapterMatrix.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `descentStep_sound` (`Compose/ForwardChain.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `descentStepCol_sound` (`Compose/ForwardChain.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `forward_chain_capstone_n` (`Compose/ForwardChain.lean`) | Core, Domains, Lib, Runtime, root |
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
| 5 | `primitiveNames_length` (`Compose/PrimitiveShape.lean`) | Core, Domains, Lib, Runtime, root |
| 5 | `primitiveNames_nodup` (`Compose/PrimitiveShape.lean`) | Core, Domains, Lib, Runtime, root |
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
- **不要按它的计数设门禁**：0 层定理是合法的（纯 `Mathlib` 陈述）。

⚠ **第 26 轮补充**：上面那条说的是**不要按绝对计数**设门禁。**下降**是另一件事——
`gov/check_endtoend_floor.py` 只对「某条定理**不再**跨 >= 2 层」失败，
而对「新增跨层定理」放行。**增长是改进，下降是回归**，两者不该用同一把尺子。
