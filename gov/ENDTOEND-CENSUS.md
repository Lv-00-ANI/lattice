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
| 0 | 5460 | 63.8% |
| 1 | 1339 | 15.6% |
| 2 | 666 | 7.8% |
| 3 | 494 | 5.8% |
| 4 | 543 | 6.3% |
| 5 | 57 | 0.7% |
| 6 | 3 | 0.0% |
| **合计** | **8562** | |

## 跨 ≥ 2 层（按层数降序，最多 60 条）

| 层数 | 定理 | 触及的层 |
|--:|:--|:--|
| 6 | `edit_apply_idempotent_of_no_add` (`Semantics/Annotations.lean`) | Audit, Compose, Core, Domains, Lib, Runtime |
| 6 | `edit_apply_not_idempotent_of_add` (`Semantics/Annotations.lean`) | Audit, Compose, Core, Domains, Lib, Runtime |
| 6 | `fullRegistry_wellFormed` (`Slots.lean`) | Audit, Compose, Core, Domains, Lib, Runtime |
| 5 | `preserves_iterate` (`Audit/ChainTransitivity.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `loop_preserves` (`Audit/ChainTransitivity.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `no_redundant_hypotheses` (`Audit/Hypotheses.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `chainAudit_length` (`Audit/Hypotheses.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `every_judgement_carries_a_reason` (`Audit/Hypotheses.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `losses_are_not_mutually_reducible` (`Lib/Chain/RealE2EComposite.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `e2e_loss_compound` (`Lib/Chain/RealEndToEnd.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `all_twelve_discharged` (`Lib/Chain/RealLv00AxiomDischargeSummary.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `go_hypotheses_pushes_aux` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `go_hypotheses_pushes` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `trivialProofTrace_passes` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `go_hypotheses_eq` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `evidenceCheck_accepts_unsatisfiable` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `evidenceCheck_unsound_exists` (`Lib/Chain/RealLv00Systems.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `all_twelve_discharged` (`Lib/Chain/RealN2AxiomDischargeJia.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `compile_program_go_append` (`Lib/Compiler/RealLv00CompilerReal.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `compile_program_append` (`Lib/Compiler/RealLv00CompilerReal.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `compile_program_go_contains` (`Lib/Compiler/RealLv00CompilerReal.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `compile_program_contains_compiled_constraints` (`Lib/Compiler/RealLv00CompilerReal.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `compile_program_vars_subset` (`Lib/Compiler/RealLv00CompilerSat.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `compile_append_satisfiable` (`Lib/Compiler/RealLv00CompilerSat.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `compile_preserves_satisfiability` (`Lib/Compiler/RealLv00CompilerSpec.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `compile_preserves_satisfiability_hypothesis_unused` (`Lib/Compiler/RealLv00CompilerSpec.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `preservation` (`Lib/Compiler/RealTypeSoundness.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `preservation_multistep` (`Lib/Compiler/RealTypeSoundness.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `type_soundness` (`Lib/Compiler/RealTypeSoundness.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `type_preservation_add` (`Lib/Compiler/RealTypeSoundness.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `preservation` (`Lib/Compiler/RealTypeSoundnessSTLC.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `multistep_preservation` (`Lib/Compiler/RealTypeSoundnessSTLC.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `soundness` (`Lib/Compiler/RealTypeSoundnessSTLC.lean`) | Audit, Compose, Core, Domains, Runtime |
| 5 | `any_edit_relation_gives_symbol_preimage` (`Lib/Editing/RealEditToSymbol.lean`) | Compose, Core, Domains, Runtime, Semantics |
| 5 | `edit_frame` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `holdsSet_member` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `edit_frame_holds` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `edit_realizes` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `annotation_realizes` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `edit_undo_restores_removed` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `edit_undo_drops_add` (`Semantics/Annotations.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `holdsSet_samePoint_single` (`Semantics/CompileSound.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `holdsSet_midpoint_single` (`Semantics/CompileSound.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `compile_sound` (`Semantics/CompileSound.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `compile_sound_midpoint` (`Semantics/CompileSound.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `holdsSet_of_sublist` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `merged_sublist` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `holdsSet_flatMap_experts` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `merge_parts` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `merge_sound` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `rejected_absent` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `conflict_loser_absent` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `conflicts_not_automatic` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `merge_sound_cons` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `merge_sound_append_experts` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `merge_sound_add_global` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `merge_sound_not_composable` (`Semantics/Merge.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `holdsSet_meaning_equiv` (`Semantics/Stage1.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `holdsSet_equiv_append_left` (`Semantics/Stage1.lean`) | Compose, Core, Domains, Lib, Runtime |
| 5 | `constraintVocab_denote_sound` (`Semantics/Stage1.lean`) | Compose, Core, Domains, Lib, Runtime |

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
