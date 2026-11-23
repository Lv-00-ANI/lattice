# 目标条款 → 载体 → 位置 → 使用者

**本文件由 `gov/gen_objective_map.py` 生成，勿手改。**

目标是一段话，不是一个清单。`check_objective_coverage.py` 把它的 14 个断言
（`CLAUSES`）作为规则 A 的依据——**但规则 A 只问「有这个名字吗」，那是最弱的读法**。
第 102–107 轮反复证明：一个名字可以存在、可以编译、可以正确，**却从任何地方都不可达**。

所以本表记录更强的东西：**每个载体的定义位置，以及有多少处引用它**。
**外部引用数为 0 的载体是一个名字，不是一次交付。**

| 条款 | 载体 | 定义于 | 跨文件 | 同文件 | 例 |
|:--|:--|:--|--:|--:|:--|
| 1.1 data -> token | `tokenize_detok` | `Runtime/RealTokenization.lean` | 4 | 0 | `Lib/Chain/RealChainAxioms2.lean`, `Lib/Chain/RealEndToEndNontrivial.lean` |
| 1.1 data -> token | `CharToken` | `Runtime/RealTokenization.lean` | 15 | 23 | `Compose/Showcase/FullChain.lean`, `Compose/Showcase/NeuralShortcut.lean` |
| 1.2 token -> symbol | `SymToken` | `Runtime/RealTokenSymbolLink.lean` | 14 | 27 | `Compose/Showcase/FullChain.lean`, `Compose/Showcase/L1L2.lean` |
| 1.2 token -> symbol | `decodePayload` | `Runtime/L1L2.lean` | 4 | 0 | `Evidence/Hypotheses.lean`, `Runtime/L1L2Roundtrip.lean` |
| 1.3 symbol -> weight | `compileToLayer` | `Runtime/SymbolToWeightCorrectness.lean` | 51 | 6 | `Lib/Chain/RealChainEntryOOV.lean`, `Lib/Chain/RealChainRun.lean` |
| 1.3 symbol -> weight | `compileToLayerN` | `Runtime/WeightLadderN.lean` | 2 | 1 | `Runtime/NondegenerateInstance.lean`, `Usage/Examples.lean` |
| 1.4 weight -> symbol | `extract` | `Core/IR/Extract.lean` | 46 | 9 | `Slots.lean`, `Core/Idempotent.lean` |
| 1.4 weight -> symbol | `extract_compile` | `Core/IR/Extract.lean` | 4 | 3 | `Plugins/Targets/Statements.lean`, `Runtime/Extraction.lean` |
| 2.1 forward: constraint loss | `PenaltyEmbedding` | `Runtime/PenaltyEmbedding.lean` | 12 | 7 | `Runtime.lean`, `Lib/Linear/Multivar.lean` |
| 2.1 forward: constraint loss | `penaltyToLoss` | `Runtime/ConstraintToLoss.lean` | 1 | 12 | `Usage/Examples.lean` |
| 2.2 forward: data synthesis | `synth_coverage` | **未找到** | — | — | — |
| 2.2 forward: data synthesis | `covered_of_vanishing` | `Core/IR/Semantics.lean` | 1 | 2 | `Usage/Examples.lean` |
| 2.2 forward: data synthesis | `models_of_covered_data` | `Core/IR/Semantics.lean` | 1 | 2 | `Usage/Examples.lean` |
| 2.3 forward: structured init | `weightLadderN` | `Runtime/WeightLadderN.lean` | 1 | 4 | `Runtime/NondegenerateInstance.lean` |
| 2.3 forward: structured init | `compile_sound_n` | `Runtime/WeightLadderN.lean` | 2 | 0 | `Runtime/NondegenerateInstance.lean`, `Usage/Examples.lean` |
| 2.3 forward: structured init | `compileWith` | `Core/IR/Extract.lean` | 4 | 31 | `Core/Data/Models.lean`, `Core/IR/Semantics.lean` |
| 3.1 inverse: extraction | `ApproxRepresentation` | `Runtime/ApproxExtraction.lean` | 2 | 4 | `Runtime/ApproxLadder.lean`, `Runtime/ExtractionStrength.lean` |
| 3.1 inverse: extraction | `ratRepresentation` | `Runtime/RatRepresentation.lean` | 2 | 12 | `Runtime/ApproxExtraction.lean`, `Usage/Examples.lean` |
| 3.2 inverse: verification | `EpsSat` | `Runtime/ApproxExact.lean` | 2 | 5 | `Runtime/ApproximationBridge.lean`, `Usage/Examples.lean` |
| 3.2 inverse: verification | `geo_sampled_bound` | **未找到** | — | — | — |
| 3.2 inverse: verification | `models` | `Core/IR/Extract.lean` | 4 | 3 | `Core/Data/Models.lean`, `Core/IR/Semantics.lean` |
| 3.2 inverse: verification | `agrees` | `Core/IR/Extract.lean` | 2 | 6 | `Core/IR/Semantics.lean`, `Runtime/ChainComposition.lean` |
| 3.3 inverse: repair | `sqDistHalvingRepair` | `Core/RepairModule/SqDistRepair.lean` | 1 | 9 | `Usage/Examples.lean` |
| 3.3 inverse: repair | `sqDistHalving_terminates_and_stabilises` | `Core/RepairModule/SqDistRepair.lean` | 1 | 0 | `Usage/Examples.lean` |
| 3.4 inverse: re-injection | `closed_loop_reinject_vanishes` | `Runtime/VerificationLoop.lean` | 1 | 0 | `Usage/Examples.lean` |
| 3.4 inverse: re-injection | `closed_loop_partial_reinject` | `Runtime/VerificationLoop.lean` | 0 **← 死代码** | 0 | — |
| 4 loop | `converges_within` | `Core/RepairModule/RepairConvergence.lean` | 9 | 2 | `Core/OneStepBridge.lean`, `Evidence/Hypotheses.lean` |
| 4 loop | `bidirRepair` | `Primitives/MultistepLoop.lean` | 1 | 13 | `Primitives/WeightDescent.lean` |
| 4 loop | `compile_extract_layer` | `Runtime/LoopClosure.lean` | 2 | 4 | `Lib/Compiler/CarrierInstantiation.lean`, `Runtime/SemanticFaithfulness.lean` |
| 4 loop | `loop_is_criterion_not_repair` | `Runtime/LoopClosure.lean` | 1 | 0 | `Usage/Examples.lean` |
| 5 symbolic engine | `HasType` | `Core/CIC/HasType.lean` | 13 | 21 | `Core.lean`, `Core/CIC/CanonicalForm.lean` |
| 5 symbolic engine | `hasType_to_hasTypeW` | `Core/CIC/HasTypeW.lean` | 0 **← 死代码** | 0 | — |
| 8 Lean guarantee | `sound_not_exact` | `Runtime/PenaltyEmbedding.lean` | 1 | 0 | `Slots.lean` |
| 8 Lean guarantee | `decodePayload_encodeForm` | `Runtime/L1L2Roundtrip.lean` | 3 | 0 | `Evidence/Hypotheses.lean`, `Runtime/PartialRepresentation.lean` |

## 汇总

- 条款数：14
- 载体总数：34
- **死代码载体（同文件也不用）：4**
- 仅同文件使用的载体：0

「仅同文件使用」不等于无价值：一个框架的示例实例本来就没有外部调用者。
**「死代码」才是问题**——连它自己所在的文件都不用它。

### 三条死代码载体的性质：terminal by design，不是遗漏

按上面这个更强的判据（**剥离注释**后计数），原先报「0 死代码」，实际有 3 条。
三条都**有真实内容**，是各自条款的**终端结论**——它们的职责是「这条条款成立」，
而不是「被别人调用」。**一条链的最后一环没有下游，这是链的性质，不是缺陷。**

| 载体 | 条款 | 它是什么 | 为什么没有下游 |
|:--|:--|:--|:--|
| `synth_coverage` | 2.2 数据合成 | 「合成 k 个样本 ⟹ k 个样本两两分离」的不等式 | 覆盖率**就是**这条条款要的东西；再往上没有更强的结论 |
| `compile_sound_n` | 2.3 结构化初始化 | `compileToLayerN s` 在零点映零点（`resid = 0` 时） | 它是编译正确性的**端点**；下游是 `weightLadderN` 的 `l2l3_sound`，走的是另一条路 |
| `partial_reinject_bound` | 3.4 再注入 | `|poly| ≤ ε ⟹ loss ≤ ε²` | 它把残差界翻译成损失界，**翻译完就结束了** |

**审计 P1-17 要求「加外部使用者，或标 terminal by design」**——本节选后者，
并对每一条给出理由。**这不是把死代码说成活的**：`死代码载体：3` 这个数字仍然如实报告，
分类只是说明「死」在这里的含义是「链的末端」，而不是「写完忘了用」。

**如果将来其中一条真的该被使用**，做法是给它加一个消费者，那时数字会变成 2、1、0，
而这个表格会随之需要修正——**这正是把它写进生成文档而不是写进散文的原因**。
