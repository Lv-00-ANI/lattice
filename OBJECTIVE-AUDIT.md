# 目标原文逐句对照：哪些是定理、哪些是检查、哪些是定位声明

**本文件由 `gov/gen_objective_audit.py` 生成，勿手改。**

目标是一段话。`OBJECTIVE-MAP.md` 按 14 个条款列出载体；本文件按**原句**列出
**每一句的性质**——这比载体清单更重要，因为**有些句子不是数学命题**。

## 为什么要分三类

把「所有 LLM 都可落在这条链路上」写成 Lean 定理会是**假的**：它是关于外部世界的
声明，不是关于本库结构的声明。**一份诚实的审计必须说清哪句是定理、哪句是检查、
哪句是定位**——否则「目标达成」就成了自我评价。

| 类别 | 含义 |
|:--|:--|
| **定理** | 有 Lean 声明，内核检查过 |
| **检查** | 有 `gov/` 脚本强制执行，能失败 |
| **定位声明** | 关于外部世界的判断；本库提供其**可验证的部分**，并明说其余不可形式化 |

## 逐句

| 目标原句 | 类别 | 证据 | 备注 |
|:--|:--|:--|:--|
| 做一条端到端的表示链路：数据 ⇄ token ⇄ 符号模型 ⇄ 权重 | **theorem** | `Ladder` + `ladder_forward` + `geoLadder` 的四跳 |  |
| 正向把符号知识编译成权重（约束损失、数据合成、结构化初始化） | **theorem** | `compileToLayer` / `PenaltyEmbedding` / `synth_coverage` / `weightLadderN` | 三个正向手段各有一个载体 |
| 逆向把权重行为提取回符号，用于验证、修正、再注入 | **theorem** | `extract` / `EpsSat` / `sqDistFix` / `reinject_loss_eq_zero` | 四个逆向用途各有一个载体 |
| 闭环就是验证回路 | **theorem** | `loop_fixed_point`（满足 ∧ 修正稳定 ∧ 往返固定，同一点） |  |
| 符号模型直接跑在符号引擎上，不另设中间层 | **theorem** | `evalPts` / `derivation_sound` | 符号侧不经过 token 或权重即可求值与推导 |
| 真正的难点只有 符号⇄权重 这一跳 | **theorem** | `no_extractor_both_layers` / `Extraction.layers_conflict` | 「难」的形式化内容是：不可能有一个提取器同时对参数层与语义层忠实 |
| 不绑定任何厂商或框架 | **check** | `check_objective_coverage.py` 规则 C（外部 vendor import 数为 0） | 「不 import」可机器检查 |
| 不实现引擎、模型和训练框架 | **check** | `check_scope_boundary.py`（无训练循环 / 优化器结构 / Module 式 forward） | 「不写训练循环」可机器检查；第 158 轮补上 |
| 正确性由 Lean 4 形式化保证 | **theorem** | 全库 9,100 条定理，`gate.py` 的 I1（无 axiom）/ I2（无 sorry） | 「保证」的含义是：无 axiom、无 sorry、内核检查通过 |
| 所有 LLM 的训练与后训练都可落在这条链路上 | **positioning** | `Ladder` / `Representation` / `Compiler` / `Repair` 全部参数化（规则 E），且各有 Core 之外的实例（规则 F） | **这是关于外部世界的声明，Lean 不证明它**。可形式化的部分是「结构不特殊化 + 有实例」，两项都有守卫。**把它写成定理会是假的。** |
| 项目的定位是通用基础设施 | **positioning** | 同上；另加规则 G 的四跳都「被外部使用」 | 同上：**可验证的部分已守卫，整体是定位声明** |
| 其余都是成熟技术 | **positioning** | — | **这是对领域的判断，不是数学命题**。本库不对它作任何形式化声明，也不应假装它被证明了。 |

## 汇总

- theorem：7 句
- check：2 句
- positioning：3 句

**「彻底做完」的含义因此是明确的**：

- 所有**定理**句都有 Lean 载体，且 `gate.py` 保证无 axiom / 无 sorry；
- 所有**检查**句都有能失败的脚本；
- 所有**定位**句的可验证部分都有守卫，**不可形式化的部分被明说，而不是被含糊过去**。

**没有任何一句是被跳过的。**
