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
| 0 | 4439 | 43.8% |
| 1 | 1568 | 15.5% |
| 2 | 1127 | 11.1% |
| 3 | 253 | 2.5% |
| 4 | 162 | 1.6% |
| 5 | 2122 | 21.0% |
| 6 | 456 | 4.5% |
| **合计** | **10127** | |

## 跨 ≥ 2 层（按层数降序，最多 60 条）

| 层数 | 定理 | 触及的层 |
|--:|:--|:--|
| 6 | `abiTable_length` (`CInterface/ABI.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `abiTable_names_nodup` (`CInterface/ABI.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `abiTable_errors_wellFormed` (`CInterface/ABI.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `abiTable_returns_a_value` (`CInterface/ABI.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `abiTable_names_eq_verified` (`CInterface/ABI.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `loadAll_preserves_observe_of_forall_mem` (`CInterface/Bootstrap.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `loadAll_reify_idempotent` (`CInterface/Bootstrap.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `conformance_length` (`CInterface/Conformance.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `conformance_names_dedup_length` (`CInterface/Conformance.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `conformance_names_eq_abi` (`CInterface/Conformance.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `conformance_iff_abi` (`CInterface/Conformance.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `every_primitive_has_boundary` (`CInterface/Conformance.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `boundaryPrimitives_nodup` (`CInterface/Conformance.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `interior_length` (`CInterface/Conformance.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `composeArgs_has_no_data_parameter` (`CInterface/ContractBoundary.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `abiTable_compose_args` (`CInterface/ContractBoundary.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `exists_abi_entry_without_data_parameter` (`CInterface/ContractBoundary.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `seven_primitives_float_inputs_have_no_f64_slot` (`CInterface/ContractBoundary.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `three_primitives_have_too_few_f64_slots` (`CInterface/ContractBoundary.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `encoded_layer_size` (`CInterface/LayoutBytes.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `abiTable_certificate` (`CInterface/PrerequisiteCensus.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `abiTable_signature_only` (`CInterface/PrerequisiteCensus.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `preserves_foldl` (`Evidence/ChainTransitivity.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `preserves_iterate` (`Evidence/ChainTransitivity.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `iterate_from_fold` (`Evidence/ChainTransitivity.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `loop_preserves` (`Evidence/ChainTransitivity.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `bridgedCount_append` (`Evidence/CompositionAlgebra.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `bridgedCount_empty` (`Evidence/CompositionAlgebra.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `bridgedCount_hom` (`Evidence/CompositionAlgebra.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `no_redundant_entries_in_audit_table` (`Evidence/Hypotheses.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `chainAudit_length` (`Evidence/Hypotheses.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `every_judgement_carries_a_reason` (`Evidence/Hypotheses.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `census_length` (`Evidence/StructureCensus.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `repair_is_densest` (`Evidence/StructureCensus.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `total_obligations` (`Evidence/StructureCensus.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `no_zero_obligation_in_census_table` (`Evidence/StructureCensus.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `census_env_agrees` (`Evidence/StructureCensus.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `verdict_lub_of_length_eq` (`Evidence/VerdictLattice.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `manifest_nonempty` (`Plugins/Architectures/Attention/Manifest.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `proof_holds` (`Plugins/Architectures/Attention/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `verified_manifest` (`Plugins/Architectures/Attention/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `verified_obligations` (`Plugins/Architectures/Attention/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `archCarrierAdditions_holds` (`Plugins/Architectures/CarrierAdditions.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `conv_props_hold` (`Plugins/Architectures/Conv/Manifest.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `manifest_nonempty` (`Plugins/Architectures/Conv/Manifest.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `convWindowDeterminesOutputProp_holds` (`Plugins/Architectures/Conv/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `proof_holds` (`Plugins/Architectures/Conv/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `verified_manifest` (`Plugins/Architectures/Conv/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `verified_obligations` (`Plugins/Architectures/Conv/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `conv_window_determines_output` (`Plugins/Architectures/Conv/Proofs.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `manifest_nonempty` (`Plugins/Architectures/DAG/Manifest.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `dagEvalMonoidActionProp_holds` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `dagConfluenceProp_holds` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `dagDenoteSeqProp_holds` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `dagDenoteParProp_holds` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `dagRecoveryProp_holds` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `dagEquivarianceProp_holds` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `proof_holds` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `verified_manifest` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |
| 6 | `verified_obligations` (`Plugins/Architectures/DAG/Plugin.lean`) | Compose, Core, Lib, Runtime, Semantics, root |

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
