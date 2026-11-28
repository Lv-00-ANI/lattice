# LATTICE 超长期架构与实施规划（整合版）

**基线** `4b522300`（审计期间被并发推进至 `c07fe066` → `0850b2bf`；`gov/` 与 `Lattice/` 在三者间无差异，故代码结论通用）
**性质** 超长期设计与实施规划，不是实现完成声明
**证据** 五份独立核查报告 + 本人只读复核
**权威** 插件设计以 [`PLUGIN-SYSTEM.md`](PLUGIN-SYSTEM.md) 为准；本文件是规划，不是第二套规格

---

## 第 0.1 节　落盘时已核实的三件事（第 1172 轮）

**本节由执行者加入，不属于原始规划正文；它把原文中标 `[未验证]` 的第一项变成了已定论的事实。**

### ① 七个同 FQN 双声明：**全部复现**

逐组在两个站点分别匹配 `^(theorem|lemma) <name>`，七组各得 **A=1 / B=1**：

| 全名 | A 站点 | B 站点 |
|:--|:--|:--|
| `abs_cos_sub_cos_le` | `RealAbsPosEncoding.lean` | `RealRoPEExtrapolation.lean` |
| `abs_sin_sub_sin_le` | 同上 | 同上 |
| `convertVec_extractVec_rfl` | `RealCanonicalCompileComm.lean` | `RealExtractSurjectivity.lean` |
| `extractVec_convertVec_rfl` | 同上 | 同上 |
| `dot_replicate_zero` | `DotTruncationDefect.lean` | `LayerComposition.lean` |
| `dot_replicate_zero_any` | `RealConstraintEdit.lean` | `LayerComposition.lean` |
| `tanh_pos_of_pos` | `RealExtractInvertibility.lean` | `RealNonlinearFidelity_parts/B.lean` |

### ② 构建**通过** ⇒ 失败模式是**静默覆盖**，不是编译错误

**本会话内 `lake build Lattice` 已多次 `exit 0`（含第 1172 轮之前的 `top=0`），而这些重复当时就在树上。**
⇒ 故不是「唯一的可编译性问题」，而是**后 import 者静默胜出**——与 `round-921` 的 `unfold relu` 事故同类。

### ③ 谁覆盖谁：**已定位到具体行号**

按目录/根聚合器的 import 顺序（后者胜）：

| 组 | 先 import（被覆盖） | 后 import（**实际生效**） |
|:--|:--|:--|
| `abs_*_sub_*_le` | `RealAbsPosEncoding`（`Lib/Attention.lean:2`） | **`RealRoPEExtrapolation`（`:30`）** |
| `convertVec_extractVec_rfl` | `RealCanonicalCompileComm`（`Lib/Editing.lean:3`） | **`RealExtractSurjectivity`（`:42`）** |
| `extractVec_convertVec_rfl` | 同上 | **同上** |
| `dot_replicate_zero_any` | `RealConstraintEdit`（`Lib/Editing.lean:9`） | **`LayerComposition`（`Runtime.lean:27`）** |
| `dot_replicate_zero` | 无 `Lib` 侧 | **`LayerComposition`（`Runtime.lean:27`）** |
| `tanh_pos_of_pos` | `RealExtractInvertibility`（`Lib.lean:12` → Editing） | **`RealNonlinearFidelity_parts/B`（`Lib.lean:16` → Lift）** |

**⇒ 故 W0-1 不只是「合并」，还要决定**保留哪一份的语义**：
⇒ 三组逐字相同（`convertVec_extractVec_rfl`、`extractVec_convertVec_rfl`、`dot_replicate_zero_any`）⇒ 留任一侧即可；
⇒ 四组定义体不同（`abs_cos_sub_cos_le`、`abs_sin_sub_sin_le`、`dot_replicate_zero`、`tanh_pos_of_pos` 中前三组不同）
⇒ 必须**先读两份的定义体**再决定，不能只按「被覆盖的那份删掉」——那会改变语义。**

---


## 第 0.2 节　执行到 Phase 2 时发现的三处规划错误（第 1182–1188 轮，均已实测）

**本节由执行者加入。它不改写规划正文，而是把「正文哪几句被测量推翻了」写在正文之前。**

| 规划的说法 | 实测 | 处置 |
|:--|:--|:--|
| `gov/layers.py` 是零 importer 的死代码，秩表只有 `gate.py` 一套 | `layers.py` 有 **1 个活 importer**（`check_layer_health.py`），且两张表在 **8 个层**上给出不同秩 | 已改：`layers.RANK` 派生自 `gate.RANK`（§3.134） |
| 插件 `consistent` 不看 manifest 是**缺陷**（"manifest 说 `.spatial` 而 `proof.spatial = True` 仍通过"） | **0 处**这样的声称；类型允许，树上没有 | 已改为**门禁**（§3.139），`ProofFieldOf` 留待门禁响了再做 |
| `ProofComplete` 的 T1 是 `Obligations.lean:86` 的 `rfl`，救法是把它移出判据 | **那条不在判据里**：判据的 T1 是三条 `t1_*`（合并健全性），其弱已由 `Targets/T1Dependence.lean` 诊断，且一般形式 `t1_compile_sound_general` 已存在 | **未删任何东西**（§3.141）；正文相关句子已就地注明 |

**⇒ 三条的共同点：规划把「某个符号在树里存在」当成了「它在判据里起作用」。**
**⇒ 而三条都是同一个动作发现的：**打开定义本体，而不是读关于它的描述**。**

## 第 0.3 节　执行到 Phase 2/3 时发现的**树自身**被推翻的五处（第 1196–1205 轮）

**⇒ §0.2 记的是**规划**被推翻；而本节记的是**这棵树自己的声称或基线**被推翻。**
**⇒ 两者必须分开：前者改规划，后者改树。**

| # | 树曾声称 | 实测 | 轮次 |
|--:|:--|:--|:--|
| 1 | README：几何层「**不参与主构建**」 | `Lattice/Reference/Geometry` 有 **323** 条 import 边来自 `Lattice/`；真正出了构建的只有 `archive/LvFormal` | 1196 |
| 2 | 所有文档**曾**写：`ProofComplete` 有 25 项 | 证明里只有 **24** 个占位符；合入真 T7/T6/T0 后是 **30** | 1201–1205 |
| 3 | `RTargets.lean:148`：T0 不能进判据，因为 `ExpressibleSpec n → weights` **不存在** | `Plugins/Targets/Construction.lean` 已把它限定到族并**证明了四条** | 1203 |
| 4 | `layer_reactivity.py`：植入 `Lattice.Geo.Dist` 能让 I4 变红 | `Lattice/Geo` 早已不存在；W0-2 又删了那个死前缀 ⇒ **I4 从不触发**，失败改由 I7 报（退出码 8） | 1199 |
| 5 | `.gitignore` 覆盖了探针的 `.bak` | **三处写 `.bak`，只有一处被忽略** | 1197 |

**⇒ 而第 4 条是**本会话最强的一条教训**：它是**我自己在 W0-2 里的正确改动**隐式关掉的，**
**⇒ 而它藏了**十四轮**，因为我一直用 `--fast`（它跳过探针）。**
**⇒ 故「验证完整」现在由**两半相加**得到（§6），不再靠一条每跑必被杀的命令。**

# 正文（原文照录）

# 第零章　这份规划为什么必须重写

前几版规划假定“缺的是把已有能力串起来”。核查证明该假定已过期：**那一段已经做完**——`SymbolicEntry` → `Target` → `EvaluatedArtifact` → `CapabilityTable` → `select` → `ArtifactStitch` → `Chain.official_chain_recipe` → `WriteBack` 全部存在且证明真实。

瓶颈移到三处更基础的地方：

1. **载体不唯一**：同一“权重”指三件事；“L3”有三个互不桥接的入口；三个 artifact 类型零连接。
2. **判据用错载体**：`ProofComplete` 合取了被规范明令禁止的弱载体（T6/T7/T8）；**T1 那句**⇒ 第 1188 轮实测：判据里的 T1 **不是**那条 `rfl`，见** §0.2**。
3. **承诺远大于执行，且检查器不能失败**：3327 行插件规格对应 0 条编排定理；105 个名义门禁中 8 个结构性恒绿、6 个目标缺失即绿。

因此本规划按**依赖**排序：先让“完成”可判定，再谈载体，再谈编排与规模化。

---

# 第一章　当前事实

## 1.1 规模

| 指标 | 数值 |
|:--|--:|
| `Lattice/**/*.lean` | **1,224** |
| 行数（逐文件 `\n` 计数） | **281,193** |
| 非 Reference 模块（含 12 个根聚合器） | **1,124** |
| `theorem` | **10,121** |
| `lemma` | **851** |
| `theorem + lemma`（官方口径） | **10,300** |
| 唯一短名数（PROOF-DEBT 口径） | **10,098**（202 条重复短名被折叠） |
| `def` / `structure` / `inductive` / `abbrev` | 3,320 / 230 / 155 / 101 |
| 声明合计 | **14,813** |
| 源码行数（非 Reference） | **263,283** |
| 剥注释后非空行 | 114,516 |
| `.olean` | 1,225 |
| `gov/*.py` | **201** |
| `verify_all` 注册项 / 名义门禁 / 报告器 | **126 / 105 / 21** |
| 不同注册脚本 | **103** |
| 根目录 `.md` | 69 份 / 24,109 行 |
| 全部 `.md` | 102 份 / 78,410 行 |
| `Reference/`（冻结） | 100 文件 / 17,838 行 |
| 机制 | `leanprover/lean4:v4.14.0`；`roots = ["Lattice"]` |

## 1.2 定理消费结构

| 类别 | 数 | 占比 |
|:--|--:|--:|
| `theorem` + `lemma` | **10,972**（代理另一口径） | 100% |
| 被 ≥1 个**其他文件**引用 | **1,418** | **12.9%** |
| 只在定义文件内出现 | 3,505 | 31.9% |
| **完全未使用** | **5,850** | **53.3%** |

引用文件数：0 个 → 9,303；1 个 → 1,010；2 个 → 311；3 个 → 105；**≥10 个 → 75（0.7%）**。

**这 75 条是事实上的公共 API**，其余多为证明链中间梯级。

## 1.3 七个同 FQN 双声明（P0 级真实缺陷）

**⇒ 已在第 0.1 节核实复现，并定位了每一组的**实际生效侧**。**

**这是全仓唯一触及构建语义一致性的缺陷。** 定论（第 0.1 节 ②）：**构建通过 ⇒ 后 import 者静默覆盖先 import 者**，任何 `rw`/`unfold`/`exact` 拿到的证明体取决于 import 顺序。

## 1.4 三套秩表，互相矛盾

**执行者** `gov/gate.py:312-370` + `:416-425`：

```
core 0 | slots 1 | lift 2 | runtime 2 | primitives 2 | lib 3 | domains 3 | plugins 3
geo 4 | reference 4 | audit 5 | evidence 5 | cinterface 6 | compose 6 | usage 7 | top 99
```

**自称“SINGLE authoritative”** `gov/layers.py:2`（`:56-72`、`:75-91`）：

```
Core 1 | Primitives 2 | Lift 2 | Runtime 2 | Slots 3 | Lib 3 | Domains 3 | Geo 3
Compose 4 | Semantics 4 | CInterface 5 | Plugins 5 | Usage 6 | Evidence 6 | Reference 7
```

**第三套**：`LAYER-BACKWARD.md:64-70` 给出 `Core(1)/Runtime(2)/Lib(3)/Plugins(5)/Reference(7)`。

**实测差异：9 个同名层秩值不同，至少 6 组相对序颠倒。** 最尖锐：`Reference/` 在 gate 是秩 4（低于 Semantics/Compose），在 `layers.py` 是秩 7（全树最高）。

**关键**：`gate.py` **不 import `layers.py`**；全仓对 `layers.py` 引用为 **0**——那份 144 行的“单一权威”是死代码。

**死配置**：`LAYER_OF` 含 `"Lattice/Lift"`、`"Lattice/Geo"`（磁盘不存在）；秩字典有 `"domains": 3` 但无对应项。

## 1.5 三个权重、三个 L3 入口、三个 artifact

### 三条互不引用的主链路径

| 路径 | 类型链 | 判据 |
|:--|:--|:--|
| **M1 约束** | `ConstraintSet = List VectorConstraint`（`Runtime/SymbolToWeightCorrectness.lean:27`）→ `Layer = List LinearLayer`（`:31`），`compileToLayer := cs.map convertVec`（`:35`） | `AllSatisfied ↔ AllZeroOutputs`（`:78`），**恰为零** |
| **M2 结构** | `Term`（`Core/CIC/Syntax.lean:107`）--`parse`--> `IRSkeleton`（`Core/IR/Skeleton.lean:84`）--`compileSkel`--> `IRWeights = ℕ → ℝ`（`Core/IR/Compile.lean:74`），码放 0 号槽（`Chain.lean:69-70`） | `ModelsIR W k := W = compileSkel k`（`Obligations.lean:73`），**结构等式** |
| **M3 项** | `Term` --`compile`--> `CICWeights`（`Core/CIC/Compile.lean:45,439`） | `ModelsTerm := W = compile t` |
| **新线** | `ExprExt`（`RealTypeSystemExt.lean:55`）--`compileTarget`--> `Target`（`SymbolicEntry.lean:74`）--`family`--> `ℕ → Segment` --`encodeGrid`--> `IRWeights` | `modelsBehavior`（`ModelsBehavior.lean:65`），**行为** |

**关键互斥定理**：`modelsIR_forbids_nontrivial_payload`（`ModelsBehavior.lean:85-103`）——若 `(g 0).c ≠ 0`，则 `encodeGrid g` **不可能**满足 `ModelsIR`。

**⟹ 两种读法的不变量互斥，却共享同一个裸类型 `ℕ → ℝ`。**

### 三个 L3 入口，零桥接

- `compileToLayer`（`Runtime/SymbolToWeightCorrectness.lean:35`）——`pipeline` 使用；
- `compileSkel`（`Core/IR/Chain.lean:69`）——`SymbolShortcut` 使用；
- `encodeGrid`（`Lib/Compiler/IRWeightsBridge.lean:63`）——`L3L2` 使用。

逐对搜索等式定理：**0 命中**。

### 三个 artifact，零桥接

| 类型 | 位置 | 携带 | 外部引用 |
|:--|:--|:--|--:|
| `ModelArtifact` | `Core/ModelArtifact.lean:209` | `arch` + `wf` + `weights : Weights arch` | 15 文件（全在 Core/Plugins） |
| 裸 `Layer` / `IRWeights` | 主链 | 编译结果 | 多处 |
| `EvaluatedArtifact` | `Lib/Compiler/Layout.lean:92` | `layout` + `weights` + `domain` + `recipe` + 派生 `evalAt` | **8 文件，全在 `Lib/Compiler/`，外部 0** |

`Layout.lean:31-35` 自述二者“互补”，**但没有一条定理连接它们**。同时 import `ModelArtifact`/`Arch*` 与 `Core.IR.*` 的文件**只有聚合器 `Lattice/Core.lean`**。

### 新线与主链的真实关系

| 事实 | 值 |
|:--|--:|
| `Runtime/` → `Lib/Compiler` 的文件 | **0** |
| `Core/` → `Lib/Compiler` 的文件 | **0** |
| `Lib/Compiler` → `Core`/`Runtime` 模块 | 20 个模块 / 33 条 import |
| `Lib/Compiler` 的非自身 importers | 17；其中 A 线消费者仅 **3**（`Lib.lean`、`L3L2`、`T2Modulus`） |
| `compileTarget` / `EvaluatedArtifact` / `decodedFamily` / `non_integer_slope_has_no_layer` 外部引用 | **各 0** |

**⟹ 新线不是主链的一部分，也不是孤岛——它是主链之上的消费者，但主链看不见它。**

### “不可合并”这个说法过强

`RealLayer.lean` 已给出共同推广并证明：`realLayerOfInt`（`:60`）、`realLayer_ofInt_out`（`:105`）、`realLayer_single_eq_segment`（`:120`）、`two_sections_of_one_generalisation`（`:130`）、`gridEval_eq_realLayer_out`（`:164`）、`pow_uniform_bound_as_realLayer`（`:173`）。

因此 `non_integer_slope_has_no_layer`（`BridgeToMainChain.lean:87-96`）**否证的是“保持 `LinearLayer`/`LayerOut : ℤ` 值域 + 输入 `[x]` + 逐点精确相等”这一种表示**，不是“任意合并不可能”。

`SYMBOL-WEIGHT-COMPARISON.md:82` 的“再强的结构改造也不会改变它”是**过度外推**；同文件 `:89-90` 又正确指出“需要先选定共同载体”，而 `RealLayer` 正是。

**⟹ 文档必须降级为“在上述前提下不可精确嵌入”。**

## 1.6 插件层：可发现、可引用，不可执行

### 真实槽位状态

| 指标 | 值 |
|:--|--:|
| 槽总数 | 132（11×12） |
| **字面 `True`** | **55** |
| 非 `True` | 77 |
| 非 `True` 内 Prop 原子 | 97 |
| 有 `_holds` 定理 | 97/97 |

**三个数**：`ProofSlotCensus.lean:7` 写 87（过期）；`plugin-slot-baseline.txt:12` 写 47；实际 **55**。

**47 是假绿**：`audit_plugin_slots.py:87` 要求 12 字段按固定顺序；Tokens 把 `completeness` 写在 `approximation` 前（`Tokens/Plugin.lean:125-126`），只收集到不足 12 个字段，`:108` 直接 `continue`。**Tokens 的 8 个 `True` 从未进入统计。** 修正顺序后基线立刻 55 > 47。

### `consistent` 不看 manifest

```lean
consistent : manifest.obligations ≠ [] → proof.Holds
```
（`Registry.lean:110`）

11 个插件全写 `fun _ => proof_holds`。**它只要求 12 个 Prop 全成立，不要求 manifest claim 的 `kind` 对应 proof 中同名字段。** 所以 manifest 说 `.spatial` 而 `proof.spatial = True` 时仍通过。`Registry.lean:99-110` 称它为“框架的中心承诺”，但按现在的类型不能兑现。

### 槽位语义被系统性拉伸

| 结论 | 数 |
|:--|--:|
| 契合 | ~33 |
| 弱化或拉伸 | ~24 |
| 错位 | ~12 |
| 逐字重复 | 4 组 |

**最严重的一列是 `recovery`**：7 个有内容的槽中，**0 个**陈述“撤销/逆/恢复”，全部是“单位/复合/迭代加法”：

| 插件 | 实际内容 |
|:--|:--|
| Attention | `(True ∧ m) = m`（掩码幺元） |
| Conv | `shift t (shift s x) = shift (t+s) x` |
| DAG | 与 `soundness` 同一等式 |
| GNN | `layerStack (m+n) = layerStack m ∘ layerStack n` |
| Compose | `identity` 是双侧单位 |
| Constraint | `Entails (cs++ds) ↔ …` |
| Repair | `iterate (m+n) = iterate m ∘ iterate n` |

**三处逐字重复**：Norm `exactness` ≡ `completeness`（`Plugin.lean:52` vs `:105`）；DAG `soundness` ≡ `exactness` ≡ `recovery`（`Proofs.lean:78,81` 都定义 `p ++ q`）；Penalty `refinement` 是 `completeness` 的一个方向。

**`soundness` 被否定结果占用**：Tokens 的 `LossNotInjectiveProp`/`NoSectionProp`；ChainSlot 的 3 条“某槽位不可读”。

## 1.7 组合层：代数厚、实例薄

| 指标 | 值 |
|:--|--:|
| 文件 / `theorem` | 17 / **84**（文档写 74，陈旧） |
| 结构层已证定律 | `compose_pre_assoc`、`compose_post_assoc_iff`、`strength_min_assoc`、`coverage_inter_assoc`、`compose_run_assoc`、`identity_compose_run`、`parallel_comm_run`、`choice_self_run`、`optional_true_run`、`compose_choice_distrib_run` |
| 展品 | M-1..M-5 全部存在 |

**缺陷**：

- 4/5 展品的 `post` 是定义式（`FullChain.lean:57,73`、`L1L2.lean:76,89`、`NeuralShortcut.lean:75`、`SymbolShortcut.lean:65,80`）；
- 唯一行为展品 M-5 的反向 `post` 是**构造性真空**（`L3L2.lean:86` 把 `g` 取成 `decodeGrid q.1`，展开是 `X = X`，`rfl` 关闭）；
- **0/5 展品进入 `plugin.yml`**；
- `pipeline` 仍是手写 `bind`（`RealEndToEnd.lean:802-803`）；`Lattice/Compose` 对 `pipeline` 引用 0。

**已完成且不应再动**：

- `frame` 字段删除 + `PrimitiveShape.lean:81-85` 的 `run_cmd` 构建期核对（不符即 `throwError`）；
- `Plugins/Compose/Manifest.lean` 的 10 条 `file` 全部指向真实存在的 `Lattice/Compose/*`（ADR-004 记录的 9 条幽灵路径**已修复**）。

## 1.8 设计文档的未执行项：约 117 条

| 主题 | 条目 | 性质 |
|:--|--:|:--|
| **插件系统** | **~33** | 17 键 → 实际 4 键；23 违反码 → 0；12 语义子目录 → 0；`systemRegistry`/`Backends/C` → 0；Q4–Q18 的 45+ 具名定理 → 0；10 类门禁 → 1；自举 6 项 → 0/6 |
| **目录与分层** | **17** | `Kernel/`、`Domains/`、`Compat/`、`C/`、`All.lean` 五类从未存在；`check_primitive_independence.py` 四处点名、从未创建；`Primitives` 零 import 规则已被自身违反（`WeightDescent.lean:66`） |
| **IR 结构层** | **12** | §7bis“契约合成：完整实现”整块为空；§9“编辑统一模型”为空；§10“渲染”为空；`compile`/`extract`/`roundtrip` 形状与文档相反 |
| **证明义务** | **13** | **T1（`Obligations.lean` 那条）**是 `rfl` 且前提未用——**但它不在 `ProofComplete` 里**（§0.2）；T7/T8 规范陈述未被执行；`ProofComplete` 无 T0 |
| **语义主线与 C 接口** | **11** | 12 个 `lattice_*` 与 `abiTable` 的 11 个名字零交集；`CInterface/Layout.lean` 不存在；`Carrier`/`Encode`/`Annotation`/`SemanticDelta` 未落码 |
| **CIC 与几何编码** | **10** | `Core/CIC/Encode/Geometry.lean` 不存在；12 构造子被 `tag*4096+payload` 常量索引替代且**非单射**（`Encode/CIC.lean:219`） |
| **几何迁移与交付** | **~16** | “归档层不参与构建”为假；“迁移完成”与真实 import 边不符 |

**归类**：现行设计 17 份（含 3 份状态行自相过时）、规范 4、计划/历史 20、纯测量 10、自审 11、生成物 7。

## 1.9 判据载体错位（影响最高的一组）

| 判据 | 规范陈述 | 实际被合取的 | 差异 |
|:--|:--|:--|:--|
| **T1** | `WellFormed S → Models (compile S) (semantics S)`，前提必须承重 | `Obligations.lean:86` 正文 `have _ := h; exact rfl`；`ModelsIR := W = compileSkel k` | **前提从未使用** |
| **T7** | `∀ trace, quiescent … → … ≃ construct (finalSpec trace)` | `RTargets.lean:96-98`：不同键两次写入交换 | `quiescent`/`ResultEquiv`/`finalSpec` 都存在却未进入判据 |
| **T8** | `failed P s → … ∧ ¬ cert P s'` | `RTargets.lean:121-123`：失败步返回 `none` | `failed` 全树不存在 |
| **T6** | `lattice_ordering ∧ lattice_resolution_coherent` | 几何版 `t6_spatial` | 载体错位 |
| **T0** | `construct_complete/canonical/approx` | **不在 25 项里** | `RTargets.lean:148` 自承 |

`CONFLUENCE.md:12-13` 明文写“几何版 `t7_confluence` **不是**本文件第 1 节的命题；不得以它冒充 T7”——**而 `ProofComplete` 恰恰合取了它。**

## 1.10 治理层：`105 个门禁` 不是有效数字

`verify_all.py:68-443` 的 `CHECKS`：

| 项 | 数 |
|:--|--:|
| 注册项 | **126** |
| 不同脚本 | **103** |
| 名义门禁 | **105** |
| 报告器 | **21** |
| **默认参数恒 0** | **8** |
| **目标缺失静默成功** | **6** |

**正确读数：97 个具失败路径。**

### 八个结构性恒绿

| 名称 | 机制 |
|:--|:--|
| `reactivity: G4` | `verify_g4.py:98-105` 无工具链时 `SKIP` + `return 0`；`check_selftest_coverage.py:73-77` 把这个理由写进 `EXEMPT` |
| `audit: G7 breakpoints` | `check_g7.py:22-26` 纯 stub，唯一返回 0；自述“obsolete”，注册只为“keeps the count honest” |
| `scope: escape baseline` | `escape_baseline.py:120-123` |
| `meta: layer cycle` | `check_layer_cycle.py:86` 是 `return 1 if strict else 0`，注册不带 `--strict` |
| `meta: layer health` | `check_layer_health.py:163` 同上 |
| `meta: layer registry` | `check_layer_registry.py:215` 同上 |
| `meta: archived LvFormal` | `check_reference_archive.py:109` 同上 |
| `meta: five pipeline stages` | `check_pipeline_stages.py:110` 同上 |

五个 `--strict` 绕过是同一模式：**脚本作者写了失败路径，注册者忘了传参数**。它们的自测也不证明默认 CLI 会红——`check_layer_cycle.self_test:97-105` 只做 `MAX+1 > MAX` 常量比较；`check_layer_health.self_test:169-196` 四个分支全是常量恒等式。**双层假绿。**

### `escape_baseline` 检查已搬走的对象

`escape-baseline.json` 的 9 条全指向 `Lattice/Reference/LvFormal/Theory/*.lean`；该路径**不存在**（`archive/LvFormal` 有 103 个）。`escape_baseline.scan():62` 显式 `dirs[:] = [... "Reference"]`——**排除它要检查的对象**。于是 `cur` 永空，返回 0。

### `intake-baseline` 给未来留 69 个逃逸预算

`gate.py:196-203` 只在 `now > was` 时失败；`intake-baseline` 记 `axiom=1, admit=68`，当前 `Reference` 实际逃逸为 0。**因此可新增最多 69 处逃逸而不触发 I1/I2。**

### 六个目标缺失即绿

`audit_tables.py:104-107`（`README` 缺失）、`check_proof_debt_orphans.py:56-63`（坏 JSON 被吞）、`check_batch_edit_damage.py:45-48`（`OSError -> None -> continue`）、`check_completion_claims.py:40-44`（同上）、`check_vacuous_hypotheses.py:97-129`（`vacuous-baseline.txt` **0 字节**）、`check_olean_presence.py:67-79`（`total=0` 打印“every module has an olean”）。

### 三个“检查错对象”

| 位置 | 缺陷 |
|:--|:--|
| `audit_counts.py:164-167,236-238` | `LvFormal` 缺失时只打印“无法实测”，**不增加 `mismatches`**；且 `:198` 的 `LvFormal/ 100` 实际比较**整个 `Reference`** |
| `check_proof_chain_rung.py:145-153` | 读不存在的 `Lattice/Geo/Compile.lean` → 整段跳过；`:139` 只匹配 `**0**` 字面，漂移永不触发 |
| `check_literal_rfl.py:87-95` | 读原始文本，注释提及算“被引用”→ 只被 docstring 提到的 `rfl` 定理逃出 83 条叶节点门禁 |

### 默认路径仍写 tracked 文件

| 脚本 | 写入物 | 状态 |
|:--|:--|:--|
| `check_slots.py` | `gov/SLOTS.md` | **无条件写**（`:161` → `:221`），在 `gate.py:569` 的 I6 路径上；`gate.py:563` 自己承认 |
| `chain.py` | `PROOF-CHAIN.md` | 无条件写 |
| `proof_chain_geo.py` | `PROOF-CHAIN-GEO.md` | 无条件写 |
| `gen_primitive_matrix.py` | `PRIMITIVE-MATRIX.md` | 无条件写 |
| `check_endtoend_content.py` | `ENDTOEND-CENSUS.md` + `endtoend-cross.tsv` | 无条件写 |
| `check_endtoend_floor.py` | 间接重写 `endtoend-cross.tsv` | **门禁的输入由它自己刚生成** |
| `audit_aliases.py` | `ALIAS-CENSUS.md` | 注释说“check mode 不写”，但**注册无 `--check`** |
| `plugin_inventory` / `gen_objective_map` / `gen_objective_audit` | 各自产物 | **已修复**（`--check` 先比较） |

### 默认路径三次改写 tracked `Lattice/Slots.lean`

| 脚本 | 备份 | `.bak` 被忽略? |
|:--|:--|:--|
| `check_registry_reactivity.py` | `.registry_reactivity.bak` | **否** |
| `check_registry_gate_reactivity.py` | `.gate_reactivity.bak` | 是（`.gitignore:30`） |
| `check_slots_reactivity.py` | `.reactivity.bak` | **否** |

**一次强杀可以把 `Slots.lean` 留在坏 case 上，并留下未跟踪的 `.bak`。**

### 判据错误四组

| 工具 | 缺陷 | 实测 |
|:--|:--|:--|
| `check_refutation_census.py:32` | 正则不匹配 `private`/`@[...]`/`noncomputable`/缩进 | 严格 **371** vs 宽松 **372**；**173 个声明落在盲区**，仅 1 条影响计数 |
| `check_theorem_liveness.py:59-78` | “消费”是**词法 token**，不要求 import、不解析引用；未注册；基线缺失 `return 0` | 10,286 / 链内 1,569（15.3%）/ 同文件 3,445 / 无 5,272 |
| `check_self_claims.py:36-43,67-90` | 只覆盖 2 类措辞；未注册 | 命中 2（违规 0）；更宽扫描至少 7 个文件含内容断言 |
| `check_clause_pairs.py` + `check_delivery_claims.py` | 前者与 `chain_connectors` 口径差真实（`Repair` 是类型不是载体名）；后者只查名字存在，不查结论；两者均未注册 | 9/12 vs 三对全非空；28 标识符 0 未解析 |

`DELIVERY-COMPILER-LAYER.md:133-140` 只给了前两对的 5 和 6，**没给 3.4→4 的 4**，却称“四者合起来覆盖全部 12 对”——**第三对是未完成的论证。**

### 基线腐化

| 基线 | 条目 | 抽样 |
|:--|--:|:--|
| **`escape-baseline.json`** | 9 文件 / 69 逃逸 | **0/9 路径存在** |
| **`intake-baseline.json`** | 9 路径 + 1/0/0/68 | **0/9 路径存在**，仍被 gate 当预算 |
| `proof_strength_baseline.txt` | 22 | 17/20 原始路径；**6 条 `Lift/` 幽灵**，经 `PATH_MAP` 后 20/20 |
| `underscore_hypotheses_baseline.txt` | 107 | 同上 |
| `obligation-path-baseline.txt` | **0** | 空基线 |
| `vacuous-baseline.txt` | **0 字节** | 空基线 + 自测未运行 |
| 其余 `alias`(930)/`definitional`(820)/`endtoend`(3349)/`frozen`(26)/`namespace`(33)/`prop-def`(4)/`verdict-stale`(18) | — | 抽样 20/20 存在 |

### 数字多源冲突

| 量 | 文档值 | 实测 |
|:--|:--|--:|
| 模块数 | README `:42` 1,124；STATE `:13` 847；STATE `:58` 1,124；MACRO `:176` 828 | **1,124** |
| 定理/引理 | README `:43` 10,300；PROOF-DEBT `:66` **10,098**；DELIVERY-COMPILER `:125` **10,099**；MACRO 8,621 | **10,300 声明 / 10,098 唯一短名** |
| 声明总数 | DELIVERY `:16` 13,437；DELIVERY `:31` 13,885 | **13,885** |
| 行数 | DELIVERY `:33` 100,498；STATE `:62` 204,800 | **263,283** |
| 检查器 | README `:46` **67**；README `:585` 99+21=120；DELIVERY `:17` **46**；DELIVERY `:182` 126=105+21；STATE `:64` 46 | **126 = 105 + 21** |
| 否证 | README `:49` **284**；USAGE `:231` 371；CENSUS `:10` 371 | **371 严格 / 372 宽松** |
| Reference | README `:227` **121** + 68 admit + 1 axiom；README `:200` 100 | **100，0/0/0/0** |
| Runtime | README `:188` 66 | **105** |
| LvFormal | README `:200` 100 | 不存在；`archive/LvFormal` **103** |
| 层文件数 | README `:44` `23/0/4/66/99/625`（5 标签 6 数） | Core 179；Lib 689；Runtime 105 |

**`check_doc_freshness` 只守 9 条，`check_usage_claims` 只守 17 条，`check_doc_consistency` 只比较“重复值相等”——所以这些冲突可以同时全绿。**

### 文档腐化

| 指标 | 值 |
|:--|--:|
| `.md` 中 `Lattice/…lean` 路径 | 166 次 / 106 去重 |
| **不存在** | **43（40.6%）** |
| 根目录主线失效率 | 45/139 = **32.4%** |
| 反引号标识符名义失败率 | 3.40%；真腐化约 1–2% |

最严重五份：`PLUGIN-SYSTEM.md`（370 未解析 / 42.9%）、`PLAN-STAGES.md`（364 / 24.2%）、`DIRECTORY-DESIGN.md`（256 / 56.9%）、`PROOF-DEBT.md`（147 / 25.7%）、`SEMANTICS-MAINLINE.md`（118 / 44.2%）。

`PLAN-STAGES.md` 阶段台账**只到 P50**，而其 §3.0 宏观读数（1,278 提交 / 1,084 模块 / 9,846 定理）已被当前（1,224 文件 / 10,972 定理）取代。

### 健康面（不应改动）

- 1,225/1,225 模块从 `Lattice.lean` 可达，**0 孤儿、0 叶子、12 个目录聚合器 100% 覆盖**；
- I4 的 30 条向上边与 `gate.py:400-406` 的 31 条基线一致，**无未登记违规**；
- 同秩双向边只有 1 组（`Lib ↔ Plugins` 5/11）；
- `PROOF-CHAIN.md` 标识符准确率 99.97%（91,343 / 30）；
- `VariableDerivative` 拆分已完成且正确（旧聚合器 13 行 0 声明，0 悬空 import，4 个旧导入者无需改动）；
- `VectorConstraint`/`LinearLayer`/`convertVec`/`extractVec`/`ModelsIR` 已收敛为单一定义（旧审计结论过期）。

---

# 第二章　长期目标

## 2.1 交付定义

`PARADIGM.md:14` 的定义仍正确：**“携带证明的符号 ⇄ 权重表示转换演算”——一个表示格。**

但“格”目前只在组合层成立，在**表示**层不成立：表示之间既无偏序也无格运算。

因此目标明确为四件事：

| # | 目标 | 可验收形态 |
|--:|:--|:--|
| **G1** | 载体统一 | 一个“权重”只有一种类型族；多载体作为其截面；每对有明确关系定理 |
| **G2** | 能力可组合 | 给定目标与精度，由定理选族、构造产物、给整域保证、交给下游 |
| **G3** | 判据可信 | `ProofComplete` 每项都是规范所写的命题；每项有否证实验 |
| **G4** | 承诺可执行 | 每条“已实现”能被一个**可失败**的检查核对；不可实现的明确标注 |

## 2.2 四个能力域

| 域 | 内容 | 当前 |
|:--|:--|:--|
| **D-语义** | CIC → IR → 权重 → 行为；提取/验证/修复/再注入 | 结构往返有；行为链只在新线；主链 T1 是 `rfl` |
| **D-代数** | 组合律、误差演算、可逆性分级 | 10 条组合律；`stacked_error_bound`；可逆性四档齐 |
| **D-执行** | 可执行边界、数值、自举、C/内部语言 | ℚ 载体有；无 C 源码；自举只有观察幂等 |
| **D-经验** | 基准、保真度、修复步数预算 | **0** |

## 2.3 什么算完成

不用百分比。五条可判定陈述：

1. **同 FQN 双声明 = 0，且构建能证明。**
2. **`ProofComplete` 每项与规范同名同陈述，且每项有“删前提则失败”的机器证据。**
3. **存在一条链：给定 `ExprExt` 与 `ε`，产出 `EvaluatedArtifact`、给整域保证、经提取与写回、由一条顶层定理总结；每个接缝是具名定理。**
4. **12 个槽中字面 `True` 为 0，或每个剩余 `True` 有机器可读的 `na`。**
5. **默认强制的门禁中，默认参数下恒绿的数量为 0；同一量在文档中只有一个值。**

第 3 条**基本成立**（`official_chain_recipe`）；第 1、2、4、5 条**完全不成立**。

---

# 第三章　架构决定

## ADR-A　以 `RealLayer` 为共同载体，`LinearLayer` 作为其整数截面

**决定**：`RealLayer`（`RealLayer.lean:49`）成为唯一“层”类型；`LinearLayer` 保留为“系数在 ℤ 且经强转嵌入”的截面；两者关系由 `realLayer_ofInt_out`（`:105`）固定。

**理由**：`realLayer_single_eq_segment`（`:120`）与 `two_sections_of_one_generalisation`（`:130`）已证 `LinearLayer` 与 `Segment` 是同一推广的两个截面；`gridEval_eq_realLayer_out`（`:164`）与 `pow_uniform_bound_as_realLayer`（`:173`）已把最强界改写到实数层；`non_integer_slope_has_no_layer` 只否证 ℤ 值域表示。

**代价**：`LayerOut` 的 6 处定义（`Runtime/ConvertVectorLinear.lean:143`、`Lib/Editing/RealEditSemantics.lean:27`、`RealLayerSemanticQuotient.lean:60`、`RealRoundtripNondegenerate.lean:54`、`Lib/Meta/RealHypothesisAudit.lean:55` 等）收敛到一处；`AllZeroOutputs` 的 ℤ 语义务必保留。

**拒绝**：两载体并列、只在文档说明——会永久保留“三个 L3 入口”。

**必须先做的否证实验**：把现有全部定理中的 `RealLayer` 换回 `LinearLayer`，逐一检查是否仍成立（尤其 `symbolToWeight_correct`、`compile_extract_layer`）。依赖 ℤ 离散性的定理（如 `discrete_approx_is_equality`）应作为**精确性判据保留在 ℤ 截面**，不是被 ℝ 化。

## ADR-B　产物契约以 `EvaluatedArtifact` 为准，`ModelArtifact` 作为形状投影

**决定**：`EvaluatedArtifact`（`Layout.lean:92`）是唯一可求值产物；新增

```text
shape_of : EvaluatedArtifact → Option ModelArtifact
```

要求：成功时 `M.weights` 的层形状与产物载荷一致；失败时显式 `none`。

**理由**：`Layout.lean:33-34` 已声明二者互补，但“互补”目前只是散文。没有这条投影，形状约束与解释约束永远无法同时出现在一条定理里。

**代价**：需定 `ℕ → ℝ` 到 `List (Σ m n, MLayer m n)` 的编码，以及“哪些布局对应哪个拓扑”。

**这是本规划最可能被证伪为不可能的一项。** 若 `ℕ → ℝ` 承载不了形状信息，正确结论是“两产物必须合并为一个”，不是造弱桥。

**拒绝**：让 `EvaluatedArtifact` 直接携带 `ModelArtifact`——会把形状约束强加到所有新线用途，包括不需要拓扑的分段族。

## ADR-C　`ProofComplete` 的合取项改为“规范所指的 Prop”

| 项 | 改为 |
|:--|:--|
| T6 | `lattice_ordering ∧ lattice_resolution_coherent` |
| T7 | `lattice_confluence`（带 `quiescent` 与 `finalSpec`） |
| T8 | `lattice_failure_isolated`（带 `failed`） |
| T0 | **显式裁决**：进判据，或在 `PROOF-OBLIGATIONS.md` 写明“不在 `ProofComplete` 内，理由是 X” |

**理由**：`CONFLUENCE.md:12-13` 明文禁止用几何版冒充 T7，而 `ProofComplete` 正在这么做。**这是判据层缺陷，不是实现缺口。**

**代价**：先补 `def failed`（全树不存在），并核对 `lattice_confluence`（`Confluence.lean:348`）是否真含 `quiescent`。

**风险**：若现有陈述也不满足规范，“换载体”会立刻使 `ProofComplete` 变假——**这正是它应有的行为**，但要提前告知。

## ADR-D　T1 必须去掉 `rfl`

**决定**：`modelsIR`/`ModelsTerm` 换成真语义谓词，使 `compile_sound` 的假设承重；新增否证实验：删除假设后定理不再通过。

**理由**：`Obligations.lean:86` 正文 `have _ := h; exact rfl`；`ModelsIR W k := W = compileSkel k` 使前提成为定义。`ModelsIRScope.lean` 的 5 条定理已把“它只约束槽 0 一个实数”写成事实。**`ModelsBehavior.lean` 已提供替代谓词**并证明旧谓词禁止一切非退化载荷。

**代价**：本规划中**最容易破坏既有证明**的一项。`compile_sound` 三处（`Core/IR`、`Core/CIC`、`Semantics`）各有约 4 个下游文件。**必须分支验证，不可直接合入。**

**替代（若不可行）**：把 T1 移出 `ProofComplete` 并在规范写明“当前只有定义等式版本”。**保留假 T1 是更坏的选择。**

## ADR-E　插件一致性按 `kind` 索引

```lean
consistent : ∀ k : ObligationKind,
    manifest.claims k = true → ProofFieldOf k proof
```

`ProofFieldOf` 是 12 个 kind 到 12 个字段的**显式映射**——**不得按位置对应**，因为 `Registry.lean:43-67` 与 `Manifest.lean:47-72` 的构造子顺序不同，按位置会静默串槽。

**理由**：插件层最便宜、解锁最多的一项。不修它，填槽、扩插件、做编排都无法判断“这个 claim 是否真被支持”。

**验收**：变异体——manifest claim `.spatial` 而 `proof.spatial = True`——`pluginRegistryComplete_holds` 必须失败。

**代价**：改 `Registry.lean` + 11 个 `Plugin.lean` + `Plugins.lean` 的 11 个 case。**不改任何定理陈述。**

## ADR-F　12 槽改为三态 + 显式 `na`

```lean
inductive SlotStatus where
  | held (p : Prop) (h : p)
  | na (reason : NonEmptyString)
  | todo (note : NonEmptyString)
```

并禁止 `held True`（用构造性检查或 `run_cmd` 断言）。

**理由**：55 个 `True`，3 组逐字重复证明“12 槽 schema 与载体不匹配”。Attention 用掩码布尔代数填满、ChainSlot 把 12 个事实塞进 3 槽、Tokens 有 8 个 `True`。**这是 schema 问题，不是懒惰。**

**代价**：L（改 `Registry.lean` + 11 个 `Plugin.lean` + `Holds` 定义）。**这是唯一能让 12 槽长期成立的方案。**

**拒绝**：维持二态、只把 `True` 降到 0——会产生 `True ∧ True` 变体，且无法登记“本插件不适用此维度”。

## ADR-G　组合层先稳定接口，不扩展示品

在前三件事完成前不新增展品：

1. `Primitive` 六字段 + `run_cmd` 机器锁（已完成）；
2. `post` 必须显式标注 `behavioral` / `definitional`；
3. L2→L3 三入口统一（ADR-A）。

**理由**：`Primitive` 已改过两次（字段版→参数版→六字段）；4/5 展品 `post` 是定义式；唯一行为展品反向 `post` 构造性真空。**在此状态下扩展示品，等于把“三个 L3”复制成“更多 L3”。**

## ADR-H　几何层的三态术语

废弃“归档”这一个词，改为三个可判定状态：

| 状态 | 含义 | 判定方法 |
|:--|:--|:--|
| **out-of-build** | 不在 `Lattice.lean` 传递闭包内 | 导入图 |
| **out-of-criterion** | 不被 `ProofComplete` 合取 | 判据引用 |
| **out-of-mainline** | 不作为默认载体/实例 | 文档与 `OBJECTIVE-MAP` |

当前几何层是 **out-of-criterion + in-build**（`Lattice/Domains.lean:1-4` 仍导入 4 个 `Reference.Geometry.*`）。README `:189` 与 `gate.py:330` 写“不参与主构建”，`check_reference_archive.py:21-23` 写“remain LIVE”，`gate.py:334` 写“removed from ProofComplete, not from build”——**三句话描述同一事实的三个层面，却用同一个词。**

## ADR-I　不以定理级 liveness 为目标

保留比率门；**不**为 5,850 条未使用定理逐条登记理由；**只**约束“新增链内能力必须被引用”。

**理由**：`aac6303f` 实测 51% 未使用，代理复测 53.3%；5,211 条逐条登记会退化为噪声。库型定理本来就是合法形状。

## ADR-J　自举只承诺“观察幂等”

`loadAll_reify_idempotent`（`Bootstrap.lean:122-124`）的观察等价版本为**唯一权威陈述**；`PLUGIN-SYSTEM.md:2348-2366` 与 `ARCHITECTURE-DECISIONS.md:126-148` 中错误的 `loadAll (loadAll ms)` 陈述**必须替换**（不是标注）。

## ADR-K　门禁必须先能失败，再谈数量

**决定**：在新增任何检查前，先完成三件事——让 8 个恒绿重新能失败、让 6 个目标缺失即成功改为失败、让 7 个自写产物改为“比较后替换”。并新增三个元门禁（见 Phase 0）。

**理由**：105 个名义门禁中 8 个结构性不能失败。**在检查不能失败的前提下，“修完某项后构建通过”这句话没有证据。**

---

# 第四章　分阶段路线

## Phase 0　止血（1–2 周）

**状态：✅ 完成（第 1169–1183 轮）—— W0-1/2/3a–3f 全部落地，含三道元门禁。**

**目标**：消除会**静默产生错误结论**的缺陷。不新增数学。

### W0-1　合并七个同 FQN 双声明

| 组 | 动作 |
|:--|:--|
| `abs_cos_sub_cos_le` / `abs_sin_sub_sin_le` | 保留参数更一般的 `RealRoPEExtrapolation` 版，另一份改 `abbrev` 或删 |
| `convertVec_extractVec_rfl` / `extractVec_convertVec_rfl` | 逐字相同，留一处 |
| `dot_replicate_zero` | 保留 `Runtime/LayerComposition`（有内部引用） |
| `dot_replicate_zero_any` | 收敛 |
| `tanh_pos_of_pos` | 逐字相同，留一处 |

**验收**：`lake build Lattice` 通过；FQN 冲突数 0。**必须先跑一次构建定论。**

**失败模式**：被删那份被同文件后续定理引用 → 先 `grep` 文件内引用。

**⇒ 第 0.1 节已给出：构建通过（已定论）、七组复现、每组的**实际生效侧**已定位。**
**⇒ 故 W0-1 的正确做法是：**保留「当前生效」的那一份以维持现状语义**，把另一份删或改 `abbrev`；
⇒ 除非读定义体后发现生效的那份才是弱的（`abs_cos_sub_cos_le`、`abs_sin_sub_sin_le`、`dot_replicate_zero` 三组需先读）。**

### W0-2　统一秩表

以 `gate.py:312-370,416-425` 为唯一源；删除 `gov/layers.py`（或改为派生）；删 `LAYER_OF` 的 `Lattice/Lift`、`Lattice/Geo` 与 `rank['domains']` 三个死键；`check_layer_registry.py` 增补 rank 比对。

**验收**：注入一条 rank 漂移，检查变红。

### W0-3a　修八个恒绿门禁

| 修法 |
|:--|
| `check_layer_cycle`/`health`/`registry`/`reference_archive`/`pipeline_stages`：**注册时传 `--strict`** |
| `check_g7`：删除注册，或标为报告器 |
| `verify_g4`：无工具链时 **不得计 PASS**（改为“无法判定”三态） |
| `escape_baseline`：见 W0-3b |

### W0-3b　重写两个腐化基线

- `escape_baseline`：不再排除 `Reference`；基线重建为当前真实逃逸集合（当前 0/0/0/0）；`shrunk` 必须真正更新基线而非只打印。
- `intake_baseline`：删除或重建为当前值；**不得保留 69 的免费预算**。

### W0-3c　禁止默认路径写 tracked 文件

`check_slots`（改为返回差异、由调用方决定是否写）、`audit_aliases`（注册加 `--check`）、`chain`、`proof_chain_geo`、`gen_primitive_matrix`、`check_endtoend_content`、`check_endtoend_floor`。

**模式**：写临时文件 → 与 tracked 比较 → 相同则丢弃，不同则报告差异（不自动替换）。

### W0-3d　`Slots.lean` reactivity 加原子备份

三个脚本的 `.bak` 加入 `.gitignore`；改为“读原文 → 内存修改 → 写临时 → 校验 → 替换 → `finally` 从内存恢复”；或改为**在临时副本上运行**，不碰 tracked 文件。

### W0-3e　修三个判据错误

| 工具 | 修法 |
|:--|:--|
| `check_refutation_census.py:32` | 正则允许 `private`/`@[...]`/`noncomputable`/缩进；重生成 `REFUTATION-CENSUS.md`（371 → 372） |
| `check_literal_rfl.py:87-95` | 改为剥注释后匹配（与 liveness 同方向） |
| `audit_counts.py:164-167,198,236-238` | `LvFormal` 缺失即失败；`LvFormal` 指标改用 `archive/LvFormal` 或删除该行 |

### W0-3f　三个新元门禁

#### GATE-1 `gate_default_failure`

对每个注册为 `G` 的脚本，按 `verify_all` 的真实 argv 运行；再植入该检查要抓的最小缺陷（或调其 `--self-test`），要求**默认 argv 返回非零**。额外断言：无工具链时 `verify_g4` 不计 PASS；`check_g7` 必须标为报告器或删除。

**验收**：该门禁自身先红——对 `check_g7` 抛“注册为门禁但无失败路径”。

#### GATE-2 `single_source_counts`

把模块数、定理声明数、唯一短名数、声明数、行数、`Reference`/`Archive` 文件数、检查器注册数、否证严格/宽松数、各层模块数集中到**一个测量模块**；所有文档的出现位置从它读取或与它比较。规则：同一量只能有一个值，除非显式标注口径并给两套值。

**验收**：注入 `README:49` 的 284，门禁变红。

#### GATE-3 `artifact_and_command_integrity`

1. 默认路径不得写 tracked 文件（覆盖 `SLOTS.md`、`ALIAS-CENSUS.md`、`PROOF-CHAIN*.md`、`PRIMITIVE-MATRIX.md`、`ENDTOEND-CENSUS.md`、`endtoend-cross.tsv`）；
2. 所有写 `Lattice/**/*.lean` 的 reactivity 必须原子备份、备份入 `.gitignore`、验证 `finally` 恢复；
3. 文档中每条“可核对命令”必须能在 `verify_all` 注册表中找到。

**验收**：直接暴露 `check_theorem_liveness`、`check_self_claims`、`check_delivery_claims`、`check_clause_pairs` 的缺线，以及 `chain_connectors --provenance` 的非门禁状态。

### W0-4　文档同步（最小集）

| 文档 | 必须改 |
|:--|:--|
| `README.md:46` | 67 → 126（或写明“名义 105，其中 97 具失败路径”） |
| `README.md:49` | 284 → 371 |
| `README.md:44` | 六数五标签 → 实测分层表 |
| `README.md:188` | Runtime 66 → 105 |
| `README.md:227` | 121 / 68+1 → 100 / 0/0/0/0 |
| `README.md:585` | 99+21 → 105+21 |
| `DELIVERY.md:16,33` | 13,437 / 100,498 → 13,885 / 263,283 |
| `DELIVERY.md:17` | 46 → 105（注明 8 个恒绿） |
| `STATE-FINAL.md:13,62,64` | 847 / 204,800 / 46 → 1,124 / 263,283 / 126 |
| `PROOF-DEBT.md:66` | 10,098 改名“唯一短名”，或改 10,300 并重算覆盖率 |
| `DELIVERY-COMPILER-LAYER.md:125` | 10,099 → 10,300 |
| `DELIVERY-COMPILER-LAYER.md:133-140` | 补 3.4→4 的 4，或撤回“覆盖全部 12 对” |
| `PLUGIN-SYSTEM.md:2348-2366` | 错误的 `loadAll (loadAll ms)` → 观察幂等 |
| `ARCHITECTURE-DECISIONS.md:148` | “全部 0 定义”已被 `Bootstrap.lean` 推翻 |
| `SYMBOL-WEIGHT-COMPARISON.md:82` | “不可翻译” → “在保持 `LinearLayer`/`LayerOut`/逐点精确下不可嵌入”，引 `RealLayer` 反例 |
| `ProofSlotCensus.lean:7` | 87 → 55 |
| `gov/plugin-slot-baseline.txt:12` | 47 → 55（修正 Tokens 字段顺序后） |
| `PLAN-STAGES.md` | 补 P51+ 或明确写“台账截至 P50” |

**Phase 0 总失败模式**：把所有工作塞进一个提交。**必须分组提交、每组单独验证**，因为 W0-1 可能改变构建结果。

## Phase 1　载体统一（2–4 月）

**状态：✅ 完成（第 1190–1194 载体；1195 三处入口；1196 产物契约）——两项构造性，一项以测量否定。**

### W1-1　`RealLayer` 提升为共同载体（ADR-A）

1. 收敛 `LayerOut` 六处定义到 `Runtime/ConvertVectorLinear.lean:143`；
2. 新增 `RealLayer.toLayer : RealLayer → Option Layer` 与 `Layer.toRealLayer`；
3. 证往返：`toRealLayer_toLayer`（左逆）、`toLayer_toRealLayer`（右逆，需整数条件）；
4. 用 `realLayer_ofInt_out`（`:105`）把新线界与主链 `LayerOut` 串起来。

**验收**：一条定理同时出现 `LayerOut`（ℤ 侧）与 `RealLayer.out`（ℝ 侧），且 `AllZeroOutputs` 仍在 ℤ 侧成立。

**失败模式**：依赖 ℤ 离散性的定理（`discrete_approx_is_equality`）保留在 ℤ 截面——这不是失败，是分层。

### W1-2　产物契约统一（ADR-B）

1. 定义 `shape_of`；
2. 证 `shape_of A = some M → M.weights` 形状与 `A` 载荷一致；
3. 若不可实现，证否证定理并改 ADR-B。

**验收**：一条同时以 `EvaluatedArtifact` 与 `ModelArtifact` 为对象的定理。

### W1-3　三个 L3 入口统一

1. 证 `compileSkel` 与 `encodeGrid` 的关系，或证**不可**；
2. 证 `compileToLayer` 与 `encodeGrid` 的关系，或证不可；
3. 若两者都不可，写“L3 有三个互不等价表示”的定理，让组合层显式标注入口。

**验收**：每个展品标注它用的 L3 入口，且由类型/定理支撑。

### W1-4　`Primitives` 独立性与 `Lattice/Domains.lean`

新建 `gov/check_primitive_independence.py`；修 `WeightDescent.lean:66`；删除或并入 `Lattice/Domains.lean`（`Reference` 的第二聚合路径，也是 I4 唯一跳过的文件）。

## Phase 2　判据可信（3–6 月，与 Phase 1 并行）

**状态：✅ 完成（第 1201–1205）—— T7/T6 换载体、T0 进判据、T8 有理由不进；判据 24 → **30**，由 `check_criterion_size.py` 看守。**

### W2-1　T6/T7/T8 换载体（ADR-C）

1. 补 `def failed`；
2. 核对 `lattice_confluence`（`Confluence.lean:348`）是否含 `quiescent` 与 `finalSpec`；
3. 若不满足，先改定理陈述（会破坏下游，需分支）；
4. 改 `ProofComplete` 合取项；
5. 对 T0 显式裁决并写入规范。

**验收**：25 项与规范逐条同名同陈述；新增检查“判据引用的 Prop 名恰为规范列出的名字”。

### W2-2　T1 去 `rfl`（ADR-D）

1. 用 `modelsBehavior` 作 `Core/IR` 候选谓词；
2. 重证 `compile_sound`（`Obligations.lean:86`）；
3. 检查约 12 个下游引用文件；
4. 否证实验：删假设，确认失败。

**若失败**：把 T1 移出 `ProofComplete` 并写明理由。

### W2-3　CIC encode 归位或撤销

二选一：把 `Encode/Geometry` 放回 `Core/CIC/Encode/` 并让 `Holds` 前提承重（当前 `Encode/CIC.lean:189` 把前提写成 `_` 丢弃）；或修订 `CARRIER-REPLACEMENT.md` 替换 V1/V2 判据。

**验收**：路径存在且前提被使用；或 ADR 有明确替代条款。

### W2-4　终止“归档”歧义（ADR-H）

引入三态术语；修正 README `:189`、`gate.py:330/334`、`check_reference_archive.py:21-23` 三处矛盾；新增门禁断言“`Lattice/Domains.lean` 的 import 边与文档所述状态一致”。

## Phase 3　插件可执行化（4–8 月）

**状态：前置✅（W3-1 以门禁形式；W3-3 状态机 + 3 条定理）；W3-2/W3-4 未开始。**

### W3-1　按 kind 索引的 `consistent`（ADR-E）

**这是插件层一切后续工作的前置。**

### W3-2　槽三态与 `na`（ADR-F）

1. 引入 `SlotStatus`；
2. 55 个 `True` 逐个转 `na reason` 或 `held p`；
3. 优先三个 mandatory kind（`recovery`/`spatial`/`confluence`）：7 个 `recovery` 槽改为真正“撤销/逆”或 `na`；
4. 修三处逐字重复（Norm / DAG / Penalty）。

**验收**：`vacuous_total` 55 → 0；Tokens 顺序修正后仍通过。

### W3-3　编排内核最小模型

新增 `Lattice/Plugins/Orchestration.lean`：

| 组件 | 依据 |
|:--|:--|
| `rankKey`（六分量）+ `rank_key_total` | `PLUGIN-SYSTEM.md:1150-1172` |
| `dependencyGraph` + `requires_acyclic` | `:1183-1189` |
| `PluginState`（declared/loaded/active/shadowed/error）+ 三条迁移定理 | `:1210-1228` |

**理由**：Q4/Q5/Q7 是 Q6/Q9/Q12/Q13/Q14/Q15/Q18 的**共同前置**；没有它们，§9 的 14 项未实现里至少 7 项无法开工。

### W3-4　`plugin.yml` 真能力索引

11 份 yml 增 `version`/`requires`/`provides`/`slots`；协议改 `ns.member@major.minor`；`check_plugin_yml.py` 增 `bad_ref`/`dup_provides`/`unknown_key`/`undeclared_ref`；出口三态。

**验收**：11 份 yml 的 `provides`/`requires` 与 Lean manifest 逐项相等；7 条 `requires` 边悬空数（当前 6）归零或每条有 `dep_unknown` 登记。

## Phase 4　组合层接到真实管线（6–12 月）

**状态：未开始。**

### W4-1　`pipeline_as_compose`

证 `pipeline s = (defaultPipeline).run s`（`pipeline` 是 2 层 `bind` + 1 个 `map`，`RealEndToEnd.lean:802-803`）。代价 M。

### W4-2　`defaultPipeline` 与 `EvaluatedArtifact` 桥

定义 `defaultPipeline : Primitive (List Char) Layer`（`tokenizePrim → bridgePrim → decodePrim → compilePrim`）；新增 `compose_evaluatedArtifact` 把 `compilePrim.run` 与 `evalAt` 接起来。

**依赖**：W1-3。

### W4-3　`post` 的行为/定义二分

给 `Primitive` 加 `postClass`；`Compose` 定律在 `behavioral` 下有更强组合条件。

**验收**：M-5 反向 `post` 从 `X = X` 改为真正消费 `modelsBehavior`。

### W4-4　展品注册

5 个 Showcase 进入 `Plugins/Compose` 义务与 `plugin.yml`。

**验收**：≥5 条 Showcase 义务，每条可追溯到具体定理。

## Phase 5　语义主线与 IR 契约（12–24 月）

**状态：未开始。**

### W5-1　IR §14 最小验证

按文档 8 步落地：`extract_unique`、`compile`、`roundtrip`、`render`/`unrender`。当前 §7bis 整块为空。

### W5-2　`PrimitiveContract` 两个实例

`IR-CANONICAL.md` §7bis.8 已指定 `identity`/`const`；实现它们，使“契约合成”从散文变成代码。

### W5-3　编辑统一模型

§9 的 `EditTarget`/`Change`/`EditMode`/`applyRelational`/`applyHard`/`Consistent`/`Commutes`/`repair` 全部为空；实现最小子集（`applyRelational` + `Consistent` + `Commutes`）。

### W5-4　行为提取三层契约

结构提取（已有 `PartialSection`）、行为提取（需 `modelsBehavior` 支撑）、再编译（三类结论分开：参数相等 / 行为相等 / 误差界）。

## Phase 6　可执行边界与自举（18–30 月）

**状态：未开始。**

### W6-1　数值边界的真实定理

`termCode`/`skeletonCode` 的 `Nat.pair` 在 `>2^53` 的失真，全树**零定理**。需 `slotOf_lt_two_pow_53` 与 `layerWords ↔ compileWith`。

### W6-2　自举六项验收（分三类）

| 项 | 归属 | 当前 |
|:--|:--|:--|
| 可枚举性 | 纯 Lean | 未实现 |
| 收敛性 | 纯 Lean | 只有观察幂等 |
| 幂等性 | 纯 Lean | `loadAll_reify_idempotent` 已证 |
| 观测等价 | 半可 | 未实现 |
| 与真实 C 对照 ×2 | 内部语言侧 | 无 C 源码 |

### W6-3　外部信任边界登记

仓库 0 个 `.c/.h`、0 个 `@[extern]`；`CONTRACT-DECISION.md:80,95-102` 要求的 B-1…B-4 在 `PROOF-DEBT.md` 中**零命中**。作为**外部信任边界**登记，不造 Lean 空壳。

## Phase 7　经验层（24–36 月）

**状态：未开始。**

`PARADIGM.md:90-91` 两维为 0/4，当前无任何基准产物。**不应早于 Phase 6**——没有可执行边界时，基准只能测 Lean 解释器速度。

## Phase 8　规模化与清理（持续）

**状态：未开始。**

- **几何消费替换**：逐项列 26 条主树导入者（`frozen-reference-baseline.txt`），决定搬出通用接口、以非几何实例接替、或保留；
- **GEO-DOC-01..08**（`DESIGN-ALIGNMENT.md:64-73`）：文档清理，`gov/` 下当前无对应脚本；
- **能力族迁移**：第二目标族复用契约；
- **文档腐化收敛**：43 条失效路径（40.6%）、`PLUGIN-SYSTEM.md` 的 370 个未解析标识符；
- **`PLAN-STAGES.md` 补全**：P51 起的阶段。

---

# 第五章　横向工作流

## 5.1 文档治理三条规则

1. **每条“已实现”必须绑定一个可失败的检查项编号**；
2. **失效路径用“已失效→见 X”注记，不直接改写**（`DIRECTORY-DESIGN.md`、`GEO-MIGRATION-PLAN.md` 是决策痕迹）；
3. **规划与实现分离**：`PLUGIN-SYSTEM.md` 是目标形态（`:167` 自述），不得当现状读；`DELIVERY-COMPILER-LAYER.md` 是唯一符号级基本可核的交付文档。

## 5.2 命名与别名收敛

200 组短名跨文件重复经同构判据核验后：

| 类别 | 组数 | 处置 |
|:--|--:|:--|
| 同 FQN 真冲突 | 7 | **合并（Phase 0）** |
| 逐字相同孪生 | 32 | 移入唯一权威 + `abbrev` |
| 同短名不同 namespace、体相同 | 3（`relu`/`normSq`/`normsq`） | 概念唯一化 |
| **同短名、语义不同** | **~150** | **不改名也不合并（伪同构）** |

**两组必须改名（统计可信度问题，不是风格）**：

- `theorem induction`（`RealTreeRecursion.lean:181`）**遮蔽 tactic 关键字**，使 570 处 `induction` 战术被误计为引用；
- `le_trans`/`le_refl`/`le_antisymm`/`le_total`/`card_fin`（`RealLv00LinearAlgebra.lean:426,419,437,463`、`RealFirstOrderLogic.lean:272`）遮蔽 Mathlib 同名，**污染全部引用统计**。

## 5.3 公共 API 契约化

12 条被 ≥10 文件引用的定理：

| 定理 | 位置 | 引用文件 |
|:--|:--|--:|
| `roundtrip` | `Runtime/WeightLadderInverse.lean:111` | 27 |
| `soundness` | `Lib/Compiler/RealTypeSoundnessSTLC.lean:578` | 26 |
| `roundtrip_extractVec` | `Runtime/WeightToSymbolEquivalence.lean:87` | 23 |
| `symbolToWeight_correct` | `Runtime/SymbolToWeightCorrectness.lean:78` | 20 |
| `completeness` | `Lib/Compiler/RealBoolCompleteness.lean:321` | 20 |
| `progress` ×3 | `Core/RepairModule/Repair.lean:86` / `RealTypeSoundness.lean:132` / `RealTypeSoundnessSTLC.lean:531` | 17 各 |
| `contraction_converges` | `Lib/Optim/RealConvergence.lean:84` | 16 |
| `scaleVec_preserves` | `Runtime/ConvertVectorLinear.lean:264` | 15 |
| `softmax_sum_one` | `Lib/Attention/RealAttention.lean:107` | 14 |
| `ladder_forward` | `Runtime/EndToEnd.lean:131` | 13 |
| `converges_within` | `Core/RepairModule/RepairConvergence.lean:89` | 12 |

为这 12 条写契约卡（前提、结论、失败语义、下游承诺）；`progress` 三名同体异构需加域后缀。

## 5.4 治理长期原则

| 原则 | 当前违反 |
|:--|:--|
| 检查器不得重写它检查的产物 | `check_slots.py:221` 等 7 处 |
| 检查器不得静默跳过 | `audit_plugin_slots.py`、`check_proof_chain_rung.py` |
| 检查器必须能失败 | 8 个恒绿 + `plugin_inventory.py:307` 恒真 |
| 单源必须真单源 | `layers.py` 零 importer |
| 三态不得压成两态 | 无 `undecidable`；`gate.py:54-65` 是错误分类 |
| 少量必须带理由 | `plugin_inventory` 的 `orphans: 0 by construction` |

---

# 第六章　文件级清单

## Phase 0

| 文件 | 动作 |
|:--|:--|
| `Lib/Attention/RealAbsPosEncoding.lean:60,78` | 合并/别名 |
| `Lib/Attention/RealRoPEExtrapolation.lean:111,135` | 保留为权威 |
| `Lib/Editing/RealCanonicalCompileComm.lean:149,155` | 删重复 |
| `Lib/Editing/RealExtractSurjectivity.lean:353,360` | 保留 |
| `Runtime/DotTruncationDefect.lean:105` | 保留 |
| `Runtime/LayerComposition.lean:48,59` | 去重 |
| `Lib/Editing/RealConstraintEdit.lean:166` | 去重 |
| `Lib/Editing/RealExtractInvertibility.lean:227` | 保留 |
| `Lib/Lift/RealNonlinearFidelity_parts/B.lean:388` | 删除 |
| `gov/layers.py` | 删除或派生 |
| `gov/gate.py:312-370,416-425` | 删三死键 |
| `gov/audit_plugin_slots.py:87,108` | 按名解析 |
| `gov/check_proof_chain_rung.py:145-153` | 路径不存在即失败 |
| `gov/plugin_inventory.py:307` | 真算 |
| `gov/check_layer_cycle.py:86`、`check_layer_health.py:163`、`check_layer_registry.py:215`、`check_reference_archive.py:109`、`check_pipeline_stages.py:110` | 注册传 `--strict` |
| `gov/check_g7.py` | 删注册或标报告器 |
| `gov/verify_g4.py:98-105` | SKIP 不计 PASS |
| `gov/escape_baseline.py:55-73,120-123` | 不排除 Reference；重建基线 |
| `gov/intake-baseline.json` | 删除或重建 |
| `gov/check_slots.py:161,221` | 不自动写 |
| `gov/audit_aliases.py` | 注册加 `--check` |
| `gov/check_endtoend_floor.py:41-44` | 不在默认路径重生成输入 |
| `.gitignore` | 加 `*.registry_reactivity.bak`、`*.reactivity.bak` |
| `gov/check_refutation_census.py:32` | 允许前缀 |
| `gov/check_literal_rfl.py:87-95` | 剥注释 |
| `gov/audit_counts.py:164-167,198,236-238` | 缺失即失败；改正对象 |
| 新 `gov/check_gate_default_failure.py` / `check_single_source_counts.py` / `check_artifact_integrity.py` | GATE-1/2/3 |
| 16 份文档 | 见 W0-4 |

## Phase 1

`Runtime/ConvertVectorLinear.lean:143`（`LayerOut` 权威）、另 5 处改 `abbrev`、`Lib/Compiler/RealLayer.lean`（往返）、`Lib/Compiler/Layout.lean`（`shape_of`）、`Core/IR/Chain.lean:69` 与 `IRWeightsBridge.lean:63`（关系或否证）、`Lattice/Domains.lean`（删/并）、新 `check_primitive_independence.py`、`Primitives/WeightDescent.lean:66`。

## Phase 2

`Core/IR/Obligations.lean:73,86`、`Core/CIC/Compile.lean:471`、`Plugins.lean:542-572`、`RTargets.lean:96,121`（保留但不再进判据）、`Confluence.lean:348`（核 `quiescent`）、新 `def failed`、`Encode/CIC.lean:181,189`、`README:189` + `gate.py:330,334` + `check_reference_archive.py:21-23`。

## Phase 3

`Plugins/Registry.lean:110`、`Manifest.lean:47-72` 与 `Registry.lean:43-67`（显式映射）、11 个 `Plugin.lean`、`Norm/Plugin.lean:52,105`、`DAG/Proofs.lean:78,81`、`Penalty/Plugin.lean:97,161`、新 `Plugins/Orchestration.lean`、11 份 `plugin.yml`、`check_plugin_yml.py`。

## Phase 4

`Lib/Chain/RealEndToEnd.lean:802`、`Compose/Showcase/`（`defaultPipeline`）、`Compose/Primitive.lean`（`postClass`）、`Plugins/Compose/Manifest.lean`。

---

# 第七章　风险登记册

| # | 风险 | 表现 | 概率 | 影响 | 应对 |
|--:|:--|:--|:--|:--|:--|
| **R1** | 七个同 FQN 合并破坏构建 | 被删那份被同文件引用 | 中 | 高 | 先 `grep` 文件内引用；分批提交 |
| **R2** | `RealLayer` 提升破坏 ℤ 判据 | `discrete_approx_is_equality`、`AllZeroOutputs` 失效 | 高 | 高 | 保留 ℤ 截面；分层而非替换 |
| **R3** | `shape_of` 被证伪 | `ℕ → ℝ` 承载不了形状信息 | **中高** | 高 | 若否证，正确结论是“两产物必须合并为一个” |
| **R4** | T1 去 `rfl` 使 `ProofComplete` 变假 | 约 12 个下游文件失效 | 高 | 高 | 分支验证；不可行则把 T1 移出判据并写明 |
| **R5** | T6/T7/T8 换载体使判据变假 | 现有 `lattice_confluence` 不含 `quiescent` | 中 | 高 | 先核陈述，必要时改定理 |
| **R6** | 槽三态引发大规模改动 | 11×12 | 高 | 中 | 分批；以 Attention（已 12/12）为样板 |
| **R7** | 文档腐化治理失控 | 43 路径 + 370 标识符 | 中 | 低 | 只修主线；`archive/` 保留腐化 |
| **R8** | 管道阻塞被误判为“需要搬文件” | 路线 A 反复 | 高 | 中 | 已结案：平秩是放水；需真实消费者才重评 |
| **R9** | 并发写者干扰 | 审计期间 HEAD 三变 | 高 | 中 | 每次工作前 `git rev-parse`；用分支 |
| **R10** | 修门禁时把真检查也关掉 | 为让 PASS 而放宽判据 | 中 | 高 | GATE-1 自身必须先红；每次修都要有变异体 |
| **R11** | 检查器继续静默失效 | 三个已知缺陷 | 高 | 中 | W0-3a–3e 修完并各加 `--self-test` |

---

# 第八章　明确不做

| # | 不做 | 理由 |
|--:|:--|:--|
| 1 | 建 `Kernel/` 及 23 个类型 | `KERNEL-MEASUREMENT.md:56-62` 实测 17 个不存在、4 个需 rank ≥2；会“直接制造 17 条新债”；`:96` 结论是“不该作为独立层存在” |
| 2 | 建 `Primitives/` 12 组子目录 | `PRIMITIVES-RANK-ANALYSIS.md:12` 实测秩方向相反；保留平铺 4 模块，分组降为 tag |
| 3 | 建 `Compat/`、`C/`、`All.lean` | 全部不存在、无消费者 |
| 4 | 实现 17 键 / 23 违反码 / `module.yml` / `params.yml` | 真实产物 4 键；16 键与全部违反码 0 引用；**保留 4 键为权威，只增 `status`** |
| 5 | 建每插件 12 个语义子目录 | 0/11；`ObligationKind` 已是机器可读载体；会制造 12×N 空目录 |
| 6 | 重建 `LatticeEffect`/`EffectMode`/`FiberState`/`Cert` | 已被 `Core/IR/{Lifecycle,Confluence,FinalSpec}` 取代 |
| 7 | 用 `t7_confluence`/`t8_failure_isolation` 充当 T7/T8 | `CONFLUENCE.md:12-13` 明文禁止 |
| 8 | 造 `systemRegistry`/`Backends/C`/`lattice_load_all` 的空壳 | 仓库 0 个 C 文件；应作为外部信任边界登记 |
| 9 | 逐条删除 5,850 条未使用定理 | 多数是证明链中间梯级；删除会破坏证明 |
| 10 | 为 270 个文件的 namespace/目录错位重命名 | 22% 文件、破坏全部下游；收益仅整洁 |
| 11 | 在 `Primitive` 未冻结前扩展 `Compose/Showcase` | 接口改过两次；4/5 展品 `post` 是定义式 |
| 12 | 把条款 2.2 改造成内部可消费 | `NEXT-STAGE.md:112-139` 已结案：4 生产者 / 0 消费者 |
| 13 | 平秩（`lib` 3→2）以让 `Runtime` 导入 `Lib/Compiler` | `NEXT-STAGE.md:70-90`：用取消一个被完全遵守的约束换零使用 |
| 14 | 把任意精度目标缩成“固定族” | 目标成立（`irWeights_uniform_tendsto`）；只应精确化量词 |
| 15 | 为提高 liveness 比率制造消费者 | 路线 B 已排除；只约束新增能力 |

---

# 第九章　度量与验收

## 9.1 六条全局判据

| # | 判据 | 当前 | 目标 |
|--:|:--|:--|:--|
| **M1** | 同 FQN 双声明 | **7** | **0**，且构建可证 |
| **M2** | `ProofComplete` 与规范逐条同名同陈述 | 0/25 | 25/25 或显式排除 |
| **M3** | 端到端链 | **已成立**（`official_chain_recipe`） | 保持并接入组合层 |
| **M4** | 字面 `True` 槽 | **55** | **0**（或全部 `na` 有理由） |
| **M5** | 默认强制门禁中默认恒绿数 | **8** | **0** |
| **M6** | 同一量在文档中的不同取值数 | 定理 4 值 / 检查器 4 值 / 行数 3 值 / 否证 2 值 | **各 1 值**（或显式标口径） |

## 9.2 阶段验收命令

| 阶段 | 命令 | 期望 |
|:--|:--|:--|
| P0 | `lake build Lattice` | 通过（**第 0.1 节已定论：通过**） |
| P0 | `python gov/check_gate_default_failure.py` | 0 个恒绿 |
| P0 | 注入 `README:49` 的 284 | GATE-2 变红 |
| P0 | `git status` 后跑 `verify_all` | **无 tracked 文件被改** |
| P1 | `git grep -l "RealLayer" -- 'Lattice/Runtime/*.lean'` | 非空 |
| P2 | `git grep -n "def failed" -- 'Lattice/**'` | 非空 |
| P3 | `python gov/audit_plugin_slots.py` | `vacuous_total 0` |
| P3 | 注入 `.spatial := True` | `pluginRegistryComplete_holds` 失败 |
| P4 | `git grep -l "pipeline_as_compose"` | 非空 |
| P4 | `git grep -c "Showcase" -- 'Lattice/Plugins/Compose/plugin.yml'` | ≥5 |

## 9.3 反指标

| 反指标 | 为什么 |
|:--|:--|
| 定理总数 | 5,850 条未使用；增加数量不改善目标 |
| 文件数 | 增加文件不等于增加能力 |
| 链内消费率 | 15.3% 是库型结构正常值 |
| 提交数 | 156 个提交中 13 个零 Lean 变更 |
| 检查器数 | 201 个脚本，至少 3 个静默失效 |
| **`verify_all` 的 PASS** | 8 个恒绿 + 6 个条件绿；PASS 不等于 97 个判据有效 |

---

# 第十章　结语

**已经做到的**：

- 一条从 `ExprExt` 到 `EvaluatedArtifact` 到整域界到写回到顶层定理的链（`official_chain_recipe`）；
- 任意度数的闭式界 `d(d−1)/8` 与 `1/8` 地板；
- 两载体的共同推广（`RealLayer`）与“整数层不能精确承载非整数斜率”的定理；
- 74/74 义务的编译期可检查链接；
- 可执行的 ℚ 数值见证（`endToEndRat_witness`）；
- 1,225 模块零孤儿、零环、零悬空；
- 一群能自我纠错的治理工具。

**还没有做到的**：

- 一个“权重”只有一种类型（三个）；
- 一个“L3”只有一个入口（三个，零桥）；
- 一个 artifact 只有一种（三个，零桥）；
- `ProofComplete` 每项都是规范所写命题（T6/T7/T8 错载体；**T1 那句已被§0.2 推翻**）；
- 插件系统能执行（0 条编排定理、0 个 C 源码、55 个 `True` 槽）；
- 组合层有能跑的真实管线（4/5 展品定义式，`pipeline` 仍是手写 `bind`）；
- **检查器能失败**（105 名义门禁中 8 个结构性恒绿、6 个条件绿、7 个自写产物、2 个腐化基线）。

**因此第一优先级是四件“让后续工作不再产生假结论”的事**：

1. **让已有检查重新能失败**（W0-3a–3f）；
2. **合并七个同 FQN**（W0-1）；
3. **统一秩表与 T6/T7/T8 判据载体**（W0-2 + Phase 2）；
4. **把 `consistent` 改成按 kind 索引**（Phase 3）。

**顺序必须是 1 → 2 → 3 → 4。** 若检查不能失败，“修完同 FQN 后构建通过”没有证据；若数字多源，“修完秩表后无违规”没有基准。

**一句话**：**这个库的数学与工程能力已足以支撑一个长期项目；它现在缺的不是雄心，而是把“已实现”这个词的判定权从文档手里收回——而收回它的第一步，是先让那些本应能失败的检查真的能失败。**