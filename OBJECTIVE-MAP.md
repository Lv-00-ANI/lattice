# 目标条款 → 载体 → 位置 → 使用者

**本文件由 `gov/gen_objective_map.py` 生成，勿手改。**

目标是一段话，不是一个清单。`check_objective_coverage.py` 把它的 14 个断言
（`CLAUSES`）作为规则 A 的依据——**但规则 A 只问「有这个名字吗」，那是最弱的读法**。
第 102–107 轮反复证明：一个名字可以存在、可以编译、可以正确，**却从任何地方都不可达**。

所以本表记录更强的东西：**每个载体的定义位置，以及有多少处引用它**。
**外部引用数为 0 的载体是一个名字，不是一次交付。**

| 条款 | 载体 | 定义于 | 跨文件 | 同文件 | 例 |
|:--|:--|:--|--:|--:|:--|
| 1.1 data -> token | `tokenize_detok` | `Lift/RealTokenization.lean` | 4 | 1 | `Lib/Chain/RealChainAxioms2.lean`, `Lib/Chain/RealEndToEndNontrivial.lean` |
| 1.1 data -> token | `CharToken` | `Lift/RealTokenization.lean` | 14 | 25 | `Geo/LadderInstance.lean`, `Lib/Chain/RealChainEntryOOV.lean` |
| 1.2 token -> symbol | `SymToken` | `Lift/RealTokenSymbolLink.lean` | 19 | 30 | `Lib/Chain/RealChainEntryOOV.lean`, `Lib/Chain/RealChainRun.lean` |
| 1.2 token -> symbol | `decodePayload` | `Lift/L1L2.lean` | 6 | 0 | `Audit/Hypotheses.lean`, `Geo/GeoLadder.lean` |
| 1.3 symbol -> weight | `compileToLayer` | `Lib/Meta/RealHypothesisAudit.lean` | 53 | 5 | `Geo/SynthesisConnection.lean`, `Lib/Chain/RealChainEntryOOV.lean` |
| 1.3 symbol -> weight | `compileToLayerN` | `Lift/WeightLadderN.lean` | 1 | 1 | `Lift/NondegenerateInstance.lean` |
| 1.4 weight -> symbol | `extract` | `Lift/WeightToSymbolEquivalence.lean` | 30 | 6 | `Slots.lean`, `Audit/StructureCensus.lean` |
| 2.1 forward: constraint loss | `PenaltyEmbedding` | `Lift/PenaltyEmbedding.lean` | 18 | 8 | `Lift.lean`, `Slots.lean` |
| 2.1 forward: constraint loss | `penaltyToLoss` | `Lift/ConstraintToLoss.lean` | 0 *(仅本文件)* | 15 | — |
| 2.2 forward: data synthesis | `synth_coverage` | `Geo/SynthesisCoverage.lean` | 1 | 1 | `Geo/MultiSeedCoverage.lean` |
| 2.3 forward: structured init | `weightLadderN` | `Lift/WeightLadderN.lean` | 3 | 6 | `Geo/GeoLadder.lean`, `Lift/MultiLayerLadder.lean` |
| 2.3 forward: structured init | `compile_sound_n` | `Lift/WeightLadderN.lean` | 0 *(仅本文件)* | 1 | — |
| 3.1 inverse: extraction | `ApproxRepresentation` | `Lift/ApproxExtraction.lean` | 3 | 9 | `Lift/ApproxLadder.lean`, `Lift/ExtractionStrength.lean` |
| 3.1 inverse: extraction | `ratRepresentation` | `Lift/RatRepresentation.lean` | 0 *(仅本文件)* | 10 | — |
| 3.2 inverse: verification | `EpsSat` | `Lift/ApproxExact.lean` | 4 | 10 | `Audit/Counterexamples.lean`, `Lift/ApproximationBridge.lean` |
| 3.2 inverse: verification | `geo_sampled_bound` | `Geo/GeoSampledBound.lean` | 5 | 0 | `Geo/ClauseComposition.lean`, `Geo/SynthesisCoverage.lean` |
| 3.3 inverse: repair | `sqDistFix` | `Geo/RepairCoverage.lean` | 4 | 6 | `Geo/EqualLengthRepair.lean`, `Geo/MissingRepairs.lean` |
| 3.3 inverse: repair | `parallelFix` | `Geo/ParallelRepair.lean` | 0 *(仅本文件)* | 13 | — |
| 3.3 inverse: repair | `midpointFix` | `Geo/MissingRepairs.lean` | 0 *(仅本文件)* | 15 | — |
| 3.4 inverse: re-injection | `reinject_loss_eq_zero` | `Geo/Reinjection.lean` | 3 | 1 | `Geo/ClauseComposition.lean`, `Geo/PartialReinjection.lean` |
| 3.4 inverse: re-injection | `partial_reinject_bound` | `Geo/PartialReinjection.lean` | 0 *(仅本文件)* | 1 | — |
| 4 loop | `converges_within` | `Core/RepairConvergence.lean` | 8 | 3 | `Audit/Hypotheses.lean`, `Core/OneStepBridge.lean` |
| 4 loop | `bidirRepair` | `Geo/MultistepLoop.lean` | 1 | 13 | `Core/OneStepBridge.lean` |
| 5 symbolic engine | `evalPts` | `Geo/ComputableExpr.lean` | 21 | 7 | `Geo/CExprCodegen.lean`, `Geo/Constraint.lean` |
| 5 symbolic engine | `derivation_sound` | `Geo/Engine.lean` | 2 | 0 | `Geo/Derive.lean`, `Geo/Rules.lean` |
| 8 Lean guarantee | `sound_not_exact` | `Lift/PenaltyEmbedding.lean` | 9 | 1 | `Lift.lean`, `Slots.lean` |
| 8 Lean guarantee | `decodePayload_encodeForm` | `Lift/L1L2Roundtrip.lean` | 3 | 1 | `Audit/Hypotheses.lean`, `Geo/LadderInstance.lean` |

## 汇总

- 条款数：14
- 载体总数：27
- **死代码载体（同文件也不用）：0**
- 仅同文件使用的载体：6

「仅同文件使用」不等于无价值：一个框架的示例实例本来就没有外部调用者。
**「死代码」才是问题**——连它自己所在的文件都不用它。
