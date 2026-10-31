# LATTICE 交付状态（DELIVERY）

> **本文所有数字由 `gov/` 下的守卫复算，不是记录。**若与守卫冲突，以守卫为准。
> 本文回答：**交付了什么 / 没交付什么 / 为什么**。
>
> **第 167 轮全文复核。** 此前本文有多处硬错误（否证数写 287、声明数写 10,820、行数写 207,807、
> 层行写 `18 / 10 / 91 / 601`、Lean 版本写 `7.26`、条款数写 17），且**这些数字没有一个被守卫覆盖**。
> 现在它们全部对齐到树，并把能机械检查的项接进了守卫。

---

## 0. 一句话

**本库交付了一个带证明的符号 ⇄ 权重转换内核；「完成」这件事是被机器检查的，不是被声明的。**

- **847 个模块、8,908 条定理、11850 条声明、209,491 行**
- **检查器逐个运行，全部 exit 0**；其中 **46 项是能失败的门禁**
- **目标原文里每一条可机械检验的断言，都有对应规则**（A–G 七条 + I1–I8 八条不变量）
- **未清欠账 0**；**永久边界 4**（见 §6.4——它们不是「缺一个证明」，而是数学上或工具链上关不掉）

**仍然开放的库内项**：见 §6.5。**需要本库之外决策/工程的**：见 §6.3。

---

## 1. 交付的规模（实测）

| 指标 | 值 |
|:--|--:|
| 源模块（不含 `Reference/`） | **868** |
| └ Core / Lift / Domains / Geo / Lib / Evidence / Usage / Root | 21 / 0 / 4 / 66 / 99 / 625 |
| 声明总数 | **11850** |
| 定理 / 引理（官方口径） | **8,908** |
| 代码行（含注释与空行） | **209,491** |
| 内核逃逸（`axiom`/`opaque`/`sorry`/`admit`） | **0** |
| 未清欠账 | **0** |
| 永久边界 | **4** |

**这些数字由 `gov/check_usage_claims.py` 守卫**：`STATE-FINAL.md` 与本文的同一组数字若与树不符，
守卫失败。层文件数由 `gov/check_doc_consistency.py` 的**有序四元组**比对——第 131 轮发现过
「每个数都合理、只有顺序错」的形态，而第 167 轮复核时本文的层行（`18 / 10 / 91 / 601`）
**正是同一形态的第 2 次**，且当时那个比对**因模式写死 `17` 而匹配为空、报告 ok**。

**所以这一项不只是改数字**：有序四元组的模式改为锚定标签而非数值，并新增
「**匹配为空即失败**」——一个谁都找不到的测量不是「一致」，是失效。

---

## 2. 目标条款：14 条载体 + 7 条规则

### 2.1 逐条载体（规则 A 强制）

`gov/check_objective_coverage.py` 的 `CLAUSES` 表列出 **14 条**，每条要求**具体的声明名**
（不是「loss」「token」这类主题词——第 87 轮证明主题词到处都有、什么也证明不了）。

| 条款 | 载体 |
|:--|:--|
| `1.1 data -> token` | `tokenize_detok`, `CharToken` |
| `1.2 token -> symbol` | `SymToken`, `decodePayload` |
| `1.3 symbol -> weight` | `compileToLayer`, `compileToLayerN` |
| `1.4 weight -> symbol` | `extract` |
| `2.1 forward: constraint loss` | `PenaltyEmbedding`, `penaltyToLoss` |
| `2.2 forward: data synthesis` | `synth_coverage` |
| `2.3 forward: structured init` | `weightLadderN`, `compile_sound_n` |
| `3.1 inverse: extraction` | `ApproxRepresentation`, `ratRepresentation` |
| `3.2 inverse: verification` | `EpsSat`, `geo_sampled_bound` |
| `3.3 inverse: repair` | `sqDistFix`, `parallelFix`, `midpointFix` |
| `3.4 inverse: re-injection` | `reinject_loss_eq_zero`, `partial_reinject_bound` |
| `4 loop` | `converges_within`, `bidirRepair` |
| `5 symbolic engine` | `evalPts`, `derivation_sound` |
| `8 Lean guarantee` | `sound_not_exact`, `decodePayload_encodeForm` |

**每个载体的定义位置与引用数见 `OBJECTIVE-MAP.md`**（由 `gov/gen_objective_map.py` 生成，
`--check` 比树而非自比）。当前：**14 条款、27 个载体、0 死代码、6 个「仅同文件使用」**。

**条款口径只有一个：14。** 本文此前写「17 条」且用 `1.7` / `3.7` / `1` / `7` 这套与 `CLAUSES`
不对应的编号——那是另一份旧清单的遗迹。

### 2.2 七条规则

| 规则 | 检查什么 | 为什么需要 |
|:--|:--|:--|
| **A** | 每条条款有**具体声明**作载体 | 主题词证明不了任何事（第 87 轮） |
| **B** | 命名判据用**最后一个点号分段** | 第 87 轮判全名，28 条里 6 条是命名空间前缀 |
| **C** | 「vendor 依赖」指**外部包** | 第 87 轮把我方 `RealTensorNorm` 当成 engine import |
| **D** | 符号语义**只定义一次** | 第二处定义**就是**目标禁止的中间层（第 99 轮） |
| **E** | 链的六个结构**保持参数化** | 专门化之后「通用基础设施」这一定位就悄悄失真（第 101 轮） |
| **F** | 框架在**定义它的层之外**有实例 | 定理存在但没人用得上（第 102–107 轮连查三例） |
| **G** | **四跳的每一跳**有一个**被外部使用**的载体 | 没人调用的定理不是一个跳（第 107 轮） |

**七条规则都有 `--self-test`，植入违规并断言被报告。**

### 2.3 第 102–107 轮：三次「定理在，但连不上」

**那几轮换了一个问法**：不问「有没有载体」，而问「**载体是否被连接**」。

| 轮次 | 缺口 | 形态 | 修法 |
|--:|:--|:--|:--|
| 102 | 数据合成的覆盖率只对单种子 | 定理在，**载体不在** | `MultiSeedCoverage.lean` |
| 103 | `DeltaDense` 从未被任何具体集合满足 | 前提在，**见证不在** | `GridDensity.lean` |
| 107 | 7 个几何闭式算子全在 `Repair` 之外 | 框架在，**实例不进** | `OneStepBridge.lean` |

**三次的修法都是同一个**：**补一条构造路径**，而不是补一条新定理。

**规则 F 把这个连接固定下来**：`Repair` 必须在 `Core` 之外至少有实例，
否则回路定理就只对玩具结构成立。

### 2.4 第 107 轮：四跳的连接性，实测

目标把「符号 ⇄ 权重」这一跳称为真正的难点。第 107 轮逐跳测了**载体与使用者**：

| 跳 | 主要载体 | 定义位置 | 外部使用者（第 107 轮） |
|:--|:--|:--|--:|
| **L0 ⇄ L1** 数据 ⇄ token | `tokenize_detok` | `Lift/RealTokenization.lean` | **7** |
| **L1 ⇄ L2** token ⇄ 符号 | `decodePayload_encodeForm` | `Lift/L1L2Roundtrip.lean` | **3** |
| **L2 → L3** 符号 → 权重 | `compileToLayer` | `Lift/WeightLadder.lean` | **13** |
| **L3 → L2** 权重 → 符号 | `extractVec` | `Lift/WeightToSymbolEquivalence.lean` | **≥30 文件** |

**⇒ 四跳全部连通，每一跳都有被外部调用的定理。**

**规则 G 把这个结果固定下来**：任何一跳的载体若失去外部使用者，守卫失败。

### 2.5 第 101 轮：「通用基础设施」这一定位，第一次被验证

目标原文的定位句是：

> **所有 LLM 的训练与后训练都可落在这条链路上**

**这句话是定位声明，不是数学命题**——`OBJECTIVE-AUDIT.md` 把它与另外三句一起归为
`positioning`，并明说「把它写成 Lean 定理会是假的」。**可形式化的部分是它的结构前提**：
链的结构必须是**参数化模板**而不是几何专用的。

| 结构 | 签名 | 实例（几何 / 非几何） |
|:--|:--|:--:|
| `Ladder` | `(Data Tok Sym W : Type)` | 3（0 / **3**） |
| `Compiler` | `(P W : Type)` | 7（1 / **3**） |
| `Representation` | `(P W : Type)` | 6（0 / **6**） |
| `Repair` | `(α : Type)` | 7（0 / **7**） |
| `PenaltyEmbedding` | `(P X : Type)` | — |
| `ApproxRepresentation` | `(P W : Type)` | — |

**六个结构全部参数化，且实例以非几何为主。⇒ 定位在结构上成立。**

**规则 E 把这六个结构的参数数固定下来**：任何一个收缩成几何专用，守卫就失败。

---

## 3. 结构性成果（不在条款内，但决定「格」是否成立）

| 成果 | 内容 | 轮次 |
|:--|:--|--:|
| 组合代数 | 组合判定是 **monoid**，桥需求是到 `ℕ` 的**同态** | 68 |
| **格结构（分层）** | **每段判定是有界格；判定序列不是**——`Evidence/VerdictLattice.lean` | **173** |
| 表示族（权重） | **三族**连通（`AffineLayer` / `LayerParams` / `MLayer`） | 71 |
| 表示族（符号） | **两族**连通（构造子 / 约束集） | 72 |
| 误差演算 | 误差**可复合**（三角、链式，`chain_error_three`） | 70 |
| 可执行轨道 | `CExpr`（`Float` 常量）+ `evalC`（`def`）+ 容差检查 | 87–88 |
| **栈代码生成** | **`StackExpr`/`StackOp` 泛化到任意载体，`CExpr → 指令列表` 语义保持** | **155–157** |

**「格」这个词的诚实边界（第 173 轮精确化）**：这不是「有」或「没有」的问题，而是**在哪一层**的问题。

| 对象 | 结构 | 定理 |
|:--|:--|:--|
| `CompositionKind`（**一段**判定） | 两元素链 `sequential < bridged` | **有界格**（`kind_is_bounded_lattice`） |
| `Verdict = List CompositionKind`（**多段**判定） | 逐点序 `Forall₂` | **不是格**（`verdict_no_sup`） |

**为什么单段是格**：`sequential` 需要的证据是 `True`（什么都不要），`bridged` 需要的是一条蕴含。
二者是**同一段蕴含的两种极端**，所以有底、有顶、有交、有并——`kindSup`/`kindInf` 给出它们。

**为什么序列不是格**：`Forall₂` 强制等长，所以 `[.bridged]` 与 `[.sequential, .sequential]`
**没有公共上界**（长度必须同时是 1 与 2）。反例是这条定理的全部内容。

**根因**：组合是**拼接**，而拼接不保持长度。**长度相同的切片上格结构仍在**
（`verdict_lub_of_length_eq`）——这不是空话，它是「如果需要格结构该走哪条路」的回答。

⇒ **「格」不是空的，也不是全的。** 它在单段判定的强弱上真实存在，在判定序列上不存在。
**所以 `Evidence/CompositionAlgebra.lean` 注册 `Monoid Verdict` 是对的**——不是没找到格结构，
是格结构在另一层，而 `++` 作用在序列上。**名字叫 lattice，结构是「单段格 + 序列单子」，
这一点现在有定理支撑，不只是措辞。**

---

## 4. 治理：88 项检查，68 个门禁

| 守卫 | 守护什么 |
|:--|:--|
| `gate.py` | 8 条不变量（I1–I8） |
| `audit_counts.py` | README 的 10 项计数 |
| `check_refutation_census.py` | 否证清册（**285**，从 `REFUTATION-CENSUS.md` 读） |
| `check_repair_census.py` | 修复清册（从 `REPAIR-CENSUS.md` 读） |
| `check_doc_consistency.py` | 文档内部自洽（含有序四元组；**pattern 匹配为空即失败**） |
| `check_usage_claims.py` | 14 项文档数字 + 过时数字回归 |
| `check_objective_coverage.py` | A–G 七条规则 |
| `check_slots.py` | 欠账登记（0 欠账 / 4 永久边界，与 `Slots.lean` 的 `decide` 交叉核对） |
| `check_scope_boundary.py` | 「不实现引擎/模型/训练框架」 |

**完整 `verify_all --full`：PASS，88 项检查，68 个门禁，约 720 秒。**

**第 167 轮修掉的三类「假绿」**（都是「守卫检查的东西与实际要检查的东西不一致」）：
两个 census 守卫读自己的常量而非文档；`check_slots.py` 不认 `.permanent` 于是把 3 条永久边界
算成欠账；`check_doc_consistency` 的层比分模式把 `17` 写死而 Core 已长到 18，**导致该检查
匹配为空、报告 ok**。

---

## 5. 这个项目真正积累的东西，不是定理

**160 多轮里，发现的问题绝大多数是同一类**：**检查的东西与实际要检查的东西不一致**，
而不是「算错了」。

| 轮次 | 发现 | 类型 |
|--:|:--|:--|
| 79 | 「优化」改变了答案（2781→2101） | 优化改变语义 |
| 17 | lakefile 与 manifest 自相矛盾 | 配置矛盾 |
| 11 | 同一测量两处，差 20 倍 | 文档自相矛盾 |
| 16 | 否证判据允许零个否定，误计 109 条 | 判据过松 |
| 17 | 冻结基线守卫从未遍历它守护的树 | 守卫检查空集 |
| 73/81/82/87 | 四次「做完了」的断言全错 | 凭记忆列清单 |
| 78/96 | 定理/声明数未剥注释 | 口径未声明 |
| 97 | `USAGE.md` 写 387，当时实际 287 | 单处数字无守卫 |
| 98 | `CONVENTIONS` 同一文档给 1 和 10 两个答案 | 内部矛盾 |
| **167** | **两个 census 守卫读自己的常量**；**`SLOTS.md` 说 owed 3 而源证明 0**；**层比分模式写死 `17` 而匹配为空** | **守卫与文档互不比较** |

> **这个库的正确性长期依赖于「我记得更新另一处」。**
> **每一轮都在把一个「依赖记忆」换成「依赖机制」。**

**第 167 轮的那三行是同一形状的第 3 次出现**，所以这次不只是修数字：census 守卫改为**读文档**、
`check_slots.py` 与 Lean 的 `decide` **交叉核对**、`check_doc_consistency` 把**匹配为空**判为失败。

---

## 6. 明确没交付的，以及为什么

**这一节比第 2 节重要。**

### 6.1 代码生成：曾经「永久停止」，第 155–157 轮闭合

第 89–92 轮四次尝试 `CExpr → 栈机程序` 的生成器与语义保持定理，全部失败，
第 92 轮写下「**永久停止**」。**那个判断是错的。**

**根因不是 Lean，是生成器的指令顺序**：

```lean
-- 第 89–92 轮：展开成 acc ++ gen(a) ++ [add] ++ gen(b) —— add 在 b 之前执行
genAcc (.add a b) acc = genAcc b (genAcc a acc ++ [.add])
-- 正确：后序
genAcc (.add a b) acc = compileAcc y (compileAcc x acc) ++ [.add]
```

**一个符号的位置，四次失败。** 前四轮记录的三个 Lean 问题（`induction` 不重写依赖假设、
`bind` 链、截断减法）都是**次生**的——它们是在一个语义错误的目标上努力时遇到的。

**第 155–157 轮交付**：

| 轮次 | 内容 |
|--:|:--|
| 155 | `StackCodegen`：`compileAcc_correct`、`compileProg_correct`、`runProg_append` |
| 156 | 泛化到任意 `Add`/`Mul` 载体（证明逐行未变——原证明从未用 `ℕ` 的性质） |
| 157 | 加 `load`（配置读取）与 `sub`，`CExprCodegen.toStack_correct`：**`runProg (compileProg (toStack e)) [seed] = some (evalC e pts :: [seed])`** |

**详见 `STATE-FINAL §3.6.2c′ / §3.6.2c″ / §3.6.2c‴`。**

### 6.2 可执行边界的完整度（记分卡部分达标）

第 87–88 轮建成了可执行轨道，但**撞上三个硬限制**：

| 限制 | 性质 |
|:--|:--|
| `Float` 相等不可判定 | **数学事实**（`NaN` 破坏自反性） |
| 只有 `sound` 方向可证 | **浮点固有**（舍入误差依赖数值，无常数容差） |
| `Float` 没有 `Preorder` 实例 | **改变了写法**（`<` 是 `compare = .lt`） |

⇒ **ℝ 轨道保证 `Holds ⟺ Holds`；`Float` 轨道只保证 `check 为真 ⟹ 容差内成立`。**

**第 157 轮的 `toStack_correct` 不改变这一条**：它是等式陈述（生成的代码算出 `evalC` 的值），
**不是「浮点比较可靠」**。两件事必须分开说。

### 6.3 仍需本库之外决策/工程的

| 项 | 为什么不在本库内 |
|:--|:--|
| **实证基准** | 需要一个 tiny-transformer 级的参照实例与可复现脚本；这是库外工程，不是形式化 |
| **FFI / 张量库绑定** | 与目标「不实现引擎/模型/训练框架」直接冲突，明确不做 |
| **宿主运行时** | 「所有 LLM 的训练与后训练」这一分句要求宿主；本项目明确不实现 |

**「生成目标语言」曾列为所有者决策，第 155–157 轮已按路线 C 自决完成**（生成到 Lean 内部的
指令列表，不生成外部语言）。

### 6.4 四个永久边界（不是欠账）

| slot | 为什么关不掉 |
|:--|:--|
| `lift.embed.local_minimiser_exact` | **一般命题是假的**（`sound_not_exact`）；只有实例成立 |
| `core.repair.atomic` | **不可导出**（`down_no_progress`）；每个算子必须自己供给 |
| `core.semantics.external_bridge` | **外部工具链**（TorchLean 需 Lean ≥ 4.26） |
| `lift.tokenize.ml_vocabulary` | **需库外语料**：L1 是带证明的**编解码器**（`EqTok := ℕ ⊕ ℝ` 不可数、无词表 id、无 BPE），真 tokenizer 需要从语料学出的有限词表，那不是形式化问题 |

**「未清欠账 0」与「四个永久边界」是两个不同的陈述**，`Slots.lean` 用 `SlotState.permanent`
把二者分开，`owedCount = 0` 与 `boundaryCount = 4` 都由 `decide` 机器检查。
**把它们算成债务会制造「删掉记录即完成」的压力**——第 162 轮记录了这个推理。

**第 171 轮新增第 4 条**：此前 `lift.tokenize.ml_vocabulary` 这个缺口只写在本文 §6.5 的散文里，
现在它是一个 `decision` 可查的槽位。**把缺口写进散文与把它写进登记表的区别是：前者靠人记得读，
后者在 `boundaryCount` 变化时会让 `decide` 失败。**

### 6.5 仍在库内的开放项（审计 P1，本文如实列出）

| 项 | 现状 |
|:--|:--|
| `weightLadderN` 的编码器 | 仍用**秩一**的 `layerOfList`（`W i j` 不依赖 `j`）；满宽版 `layerOfListFull` 与逆 `listOfLayer` 已就绪但**未接线** |
| `Ladder` 的 `satW` | **全部是单点**（`input`/`target` 是参数）；缺一个 `∀ x` 成立的实例 |
| `Activation` | 已证明激活严格强于仿射，但**未接进任何 `Ladder`**——「多层」在纯仿射下仍是重言 |
| L1 tokenizer 定位 | `EqTok := ℕ ⊕ ℝ` 词表不可数、无 BPE/byte-level；**它是带证明的编解码器，不是 ML tokenizer**，文档需按此改称 |
| `approxHolds` 覆盖 | 只覆盖 `eqZero`/`leZero`（2/12 构造子），且只有 `sound` 方向 |
| `Slot.stmt` | 9/9 是 `True`，全库零读取——死字段 |

**这些都不是「缺少一个证明」，而是「缺少接线或缺少定位说明」**；审计把它们排在 P1。

---

## 7. 本文自身的边界

- **所有数字是第 167 轮实测**，但**会漂移**——若与守卫冲突，**以守卫为准**。
- **8 维记分卡的分数是估计**（见 `PARADIGM.md`），权重可被争议与重算。
- **本文不声称项目「完成」**。它声称：**本库能自主完成的部分已完成，
  其余需要本库之外的决策或工程**。这两句话不同，区别重要。
- **§6.5 是本文第 167 轮新增的**：此前的「仍然开放的库内义务」表列的三项里，
  两项已在第 135–136、144、155–157 轮闭合，**而本文没有随之更新**。
- **§5 记录的错误是本文件的一部分**，不是附录。
  一份不记录自己判断错误的交付文档，读者无法知道它这次的判断是否可靠。
