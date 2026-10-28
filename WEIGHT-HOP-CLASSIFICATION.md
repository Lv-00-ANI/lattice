# 符号⇄权重 这一跳上的 `register` 债：分类与处置计划

> **第 9 轮。** 来源：`agent-tmp/review/verdicts_*.jsonl` 的 `register` 判定，
> 按 `B_missing`/`E_coverage`/`note` 是否落在「符号⇄权重」这一跳上筛出 **17 条**（其中 3 条已在第 6–8 轮处理）。
> **本文档只做分类与排序，不改代码。** 每条都给了**可执行的下一个动作**。

---

## 0. 为什么先分类再动手

前三轮的做法是「挑一条 `B_missing` → 试着做」。三轮之后可以总结出规律：

**同一条 `B_missing` 里常常同时有两种东西**——一个**真的缺失的定理**，和一个**doc 措辞问题**。
`sgd_rate_bound` 就是典型：`B_missing` 要一条新引理，而**那条引理在该接口下不可证**，
于是真正的修法是**改 doc** 并把「缺的基础设施」记成新债。

**所以先分类，再批量处理同类。**

---

## 1. 分类结果

| 类 | 条数 | 特征 | 处置 |
|:--|--:|:--|:--|
| **A. 别名 / 重复** | 7 | 陈述与既有定理**同型同义**，或同一命题的第二/第三/第四份证明 | **收敛成一处**：`alias` 或删副本，不新增定理 |
| **B. doc / 表** | 6 | 定理本体可用，**doc 声称的比证的多**，或表里的数字与结构不符 | **改 doc 或改表**，并把「无机器核对」写明 |
| **C. 需新定理** | 3 | 真的缺一条数学内容 | **估工后做**，或写清为何在现接口下不可做 |
| **D. 过期判定** | 1 | `B_missing` 或 `note` 引用的位置**已经不存在** | **注销该判定** |

---

## 2. A 类：别名 / 重复（7 条）

| # | 位置 | 定理 | 重复的权威版 | 下一个动作 |
|--:|:--|:--|:--|:--|
| 1 | `Lib/Linear/PenaltyPerturb.lean` | `localMin_of_feasible` | 同名 3 份（`Penalty:87`、`PenaltyMatrix:230`、`PenaltyPerturbN:187`） | **全仓零引用**；第四份手写证明。删，或从 `PenaltyPerturbN` 的 n 版 transport 一行导出 |
| 2 | `Lib/Editing/RealEditInvariantCatalog.lean` | `dot_append_sub` | `RealConstraintEdit.dot_append_sub` | doc 已自认逐字相同；改直接引用，删副本 |
| 3 | `Lib/Editing/RealEditInvariantCatalog.lean` | `dot_append_of_length_eq` | `RealSymbolToWeightWidened:304` 同名同义 | 两文件**互不 import**，且**文件内无证明使用**；收敛为一份 |
| 4 | `Lib/LearningTheory/RealConstrainedDecoding.lean` | `constrained_sum_one_via_realMaskFamily` | 同文件 `constrainedSoftmax_sum_one` | 同命题第二份证明；改 `alias` |
| 5 | `Lib/LearningTheory/RealConstrainedDecodingVerify.lean` | `allowed_is_convex_weights` | 两条既有定理的**合取打包** | 合取包不是数学内容；删或标 convenience alias |
| 6 | `Lib/LearningTheory/RealConstrainedDecodingVerify.lean` | `support_from_decoded_constraints` | `constrained_agrees_with_constraint_set` | 逐字别名；改 `alias` |
| 7 | `Semantics/Annotations.lean` | `holdsSet_member` | `Domains/Constraints/ConstraintSet.holdsSet_mem` | **零消费者**（见 §5），改为直接引用 |

⚠ **共同风险**：改 `alias` 或删副本会动 API 名，而 `Evidence/Hypotheses.lean` 的表里有几条**以名字为键**
（`abs_le_of_sq_le`、`epsSat_of_loss_le_sq` 等）。**每改一条都要重跑 `check_proof_debt_orphans` 与 `audit_tables`。**

---

## 3. B 类：doc / 表（6 条）

| # | 位置 | 定理 | 过度声称的是什么 | 下一个动作 |
|--:|:--|:--|:--|:--|
| 8 | `Lib/Chain/RealModelFamilyChainWiring.lean` | `convertVec_bias_eq_convertRealVec_bias` | doc 称「链核心语义可抬升到 ℝ」，而证明是 `rfl`，只钉了**偏置字段** | doc 降级为「字段相等，语义交换**未证**」；「语义交换方块」记成新债 |
| 9 | `Lib/Editing/RealCompileExtractClosed.lean` | `compile_extract_end_to_end` | doc 标「**★端到端闭环★**」，实为 `symbolToWeight_correct` 经 `extract∘compile = id` 换形 | doc 降级；「真端到端需要非平凡 `extract`」记成新债 |
| 10 | `Lift/CompilerScheme.lean` | `scheme_covers_all` | 证明是 `⟨rfl,rfl,rfl⟩`，而 `Slots.lean:195-200` 把它当 `lift.compile.single_item_sound` 的 **CLOSED 凭证** | doc 与 `Slots` 措辞限定为「**结构性**关闭，不新增语义保证」 |
| 11 | `Lift/CompilerScheme.lean` | `backend_sound` | 字段投影；同上 `Slots:200` 的 `.discharged` | 与 #10 同一处修 |
| 12 | `Evidence/StructureCensus.lean` | `census_length` | doc 称「**实测**清册」，而 `decide` 只核表内算术 | **本轮已修**：`Representation` 行 `8` → **`7`**（真值来自 `Runtime/Extraction.lean:58`），并写明「人工录入、未经核对」 |
| 13 | `Evidence/Hypotheses.lean` | `chainAudit_length` | doc 写「审计覆盖了**七**条定理」，而 `chainAudit` 是 **10** 行 | 改 doc 为 10，并把 4 行散文证据标为「未机器核对」 |

---

## 4. C 类：需新定理（3 条）

| # | 位置 | 定理 | 缺什么 | 可做性判断 |
|--:|:--|:--|:--|:--|
| 14 | `Lib/Compiler/RealLv00CompilerSpec.lean` | `compile_constraint_degenerately_satisfied` | `compile_constraint_sound`：**任意 env** 的可靠性/完备性 | **可做但工作量大**：12 条 IR 形状 × 语义，且当前退化版恒真 |
| 15 | `Lib/Distill` 一系（`chain_distill_bound_lipschitz`） | 由**网络结构**导出层常数 `Ls` | 当前 `Ls` 是**自由参数**，doc 用「取 max」人工补 | **可做**：`Ls` 从权重范数导出，需要线性层的算子范数链 |
| 16 | `Lib/Quantization/RealMixedPrecision.lean` | `accumulation_error_bound` | `_hM` **未使用**，且可由 `hmag 0` 推出 | **清理级**：删 `_hM`，下游少传一个参数 |

---

## 5. D 类：过期判定（1 条）

| # | 位置 | 定理 | 判定写的什么 | 实测 |
|--:|:--|:--|:--|:--|
| 17 | `Semantics/Annotations.lean` | `holdsSet_member` | 「唯一跨文件引用 `Semantics/Merge.lean:142` 写的是裸名 `holdsSet_member`」 | ⚠ **该行现在是 `merge_parts`，根本不提这个名字**。`Merge.lean` 只 import `ConstraintSet`/`Constraint`，**既没 import 本文件也没 open 本 namespace** |

**所以 #17 的真实状态是**：`holdsSet_member` **零消费者**，是 `holdsSet_mem` 的无用副本。
**它的 `register` 判定应注销**（它其实是 #7，即 A 类），而**判定里那条引用不存在**——
这说明 `verdicts_*.jsonl` 也**会随代码演进过期**，而**没有任何门禁在核对它们**。

---

## 6. 这批分类暴露的两个结构性问题

### 6.1 `decide` 定理证明不了它看起来在证明的东西

`census_length`、`no_zero_obligation_in_census_table`、`repair_is_densest` 全部 `decide` 于一张
**人工维护**的表。**它们核对表内算术，不核对表与库的一致性。**
本轮找到一个错的数字（`Representation` 8 vs 7），而**三条 `decide` 定理照旧为真**。

**要真正锁住，需要反射取字段数**（Lean 元编程），不是 `decide`。在那之前这些数字只能按「人工录入」读。

### 6.2 判定文件本身会过期，且没有门禁

`verdicts_*.jsonl` 的行号与结论都写于某一轮，**之后代码搬动、文件改写，判定不会更新**。
第 5 轮修 `gen_proof_debt.py` 的「计数降不下来」时已经见过一次后果（11 条已修条目仍在计数）；
本轮的 #17 是第二种后果：**判定的依据本身失效**。

**建议**（未做）：给 `gen_proof_debt.py` 加一项**新鲜度检查**——
判定里引用的 `文件:行号` 若已不存在或不再包含该名字，就**标为 `stale` 并计入一个新桶**，
而不是继续用旧理由把它算作 `register`。

---

## 7. 建议的执行顺序（按「确定性 × 影响」排）

| 优先 | 条目 | 理由 |
|--:|:--|:--|
| **1** | #12（已做）、#13 | **文档与事实矛盾**，改动最小、最确定 |
| **2** | #17 → 并入 #7 | 零消费者，删或改引用；顺便注销过期判定 |
| **3** | #8、#9、#10、#11 | doc 降级；每处都是「把声称缩到证得到的范围」 |
| **4** | #16 | 清理级，删一个未用前提 |
| **5** | #1–#6 | 别名收敛；**每一条都要重跑 `audit_tables` 与 `check_proof_debt_orphans`** |
| **6** | #14、#15 | 需要新数学，单独成轮 |

**不做**：不会为了让数字好看而删掉有内容的定理；A 类的「删副本」只在**确认零消费者**后执行。
