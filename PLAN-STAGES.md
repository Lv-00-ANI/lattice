# 阶段台账（PLAN-STAGES）

**本文件是**执行规划的持久记录**：记录每个阶段做了什么、证据在哪、哪些还没做。**

**=> 目的：即使对话上下文丢失，也能从本文件**准确判断执行到哪一步**。**

**=> 数字不写死在这里——需要数字时运行 `gov/audit_counts.py` 与 `gov/check_coverage_claim.py`，
本文件只记录**结构**与**证据**。**

---

## 1. 阶段台账

| 阶段 | 内容 | 状态 | 证据（提交） |
|:--|:--|:--|:--|
| **P8 核心** | 第一个下界：`x²` 对线性族有 `1/8` 地板 | **完成** | `382830cf` |
| **P8 载体** | 下界接入载体；离散上 `ε<1` 即相等 | **完成** | `382830cf` |
| **P8 机制** | 二阶差分：割线误差 `≤ h²/4` | **完成** | `8ab3b156` |
| **P8 Archimedes** | `1/(4n²) → 0`（`push_cast` 收尾） | **完成** | `62544f6a` |
| **P8 判决** | `hop_verdict`：四步判决合一 | **完成** | `3fdb23c7` |
| **P8 R2** | 收敛序列存在（R2 从 0 条变 1 条） | **完成** | `2e32005b` |
| **P8 权重族** | `Segment` + `chordSegment` 承载误差界 | **完成** | `6d82278a`, `93947cab` |
| **P8 单一函数** | `piecewiseWeights : ℕ → ℝ → ℝ` | **完成** | `fe54eb8d` |
| **P8 R3** | `ε<1` 时 R3 ≡ R4（可达性） | **完成** | `bd160824` |
| **P8 边界 2 修正** | 「`ε≥1` 平凡」是**假**断言，已证否 | **完成** | `26bc754e` |
| **P8 文档** | `P8-LOWER-BOUNDS.md` 权威入口 | **完成** | `0e7b2e92`, `2ba740ba` |
| **P9 模数** | `√δ` 从几何层抽象到 `Lib`；`T2Modulus` 成实例 | **完成** | `275f78b0` |
| **P10 一致逼近** | 闭区间上 `∀ε ∃n ∀x` 成立（R1 对分段族为真） | **完成** | `675a3813` |
| **P11 一般弦** | `chordOf f`；`x²` 是特例；仿射精确 | **完成** | `892484e1` |
| **P12 一般误差界** | 帐篷假设 ⟹ `M(b-a)²/4`；旧界被重推 | **完成** | `aa8391a1` |
| **P13 凸性路线** | `convex_le_chord` + `tent_of_semiconvex` | **完成** | `58884c30` |
| **P14 经典界** | `\|f''\| ≤ M` ⟹ `M(b-a)²/8`，链条闭合 | **完成** | `9c4f9cf9` |
| **P15 网格代数** | 向量空间封闭 + 堆叠误差预算律 | **完成** | `d540aca5` |
| **P16 真实载体** | `IRWeights` 交织编码（单射）+ 误差界 | **完成** | `2e0264a3` |
| **P17 台账落盘** | `PLAN-STAGES.md`：阶段台账成为文件 | **完成** | `17d5cc5c` |
| **P18 审计自检** | 审计表引用 P8；生成器加「引用必须存在」自检 + `--self-test` | **完成** | `d25ec17b` |
| **P19 审计去假阳性** | `audit_duplicate_names` 先剥注释；基线 541 → 367；撤回一条假记录 | **完成** | `b171df4f` |
| **P20 去重收敛** | `gov/tools/lean_source.py` 权威；5 站点切换；21 → 16 | **完成** | `be7ba42c` |
| **P21 拒绝错误合并** | 查明 `sorry_axiom_census` 是**更强**实现，明确不合并并钉进自检 | **完成** | `20bf5de2` |
| **P22 判据上真实链路** | `ReversibilityChain`：编码**可逆**（正）、行为**不可提取权重**（负） | **完成** | `1076bfaa` |
| **P23 信息锐化** | `ReversibilitySharpness`：可恢复集**恰为 `{0,…,n−1}`**（行为依赖 `{0..n}`，但 `g n` 只给 `m_n+c_n`） | **完成** | 第 971 轮 |
| **P24 台账纠错** | O-2 的真实含义（P1-8 是**一个函数**）；记录一次破坏性覆盖险情 | **完成** | `c4b50b8b` |
| **P25 P1-8 反向证否** | `DecodeFaithful`：`decodeTensorShape` **不忠实**（只看第一分量） | **完成** | `c7c76c0b` |
| **P26 P1-8 规格层交付** | `DecodeSpec`：`decodeSpec`（`Classical.choose`）**逐字满足**审计要求；算法层明确留作方案 A | **完成** | `50d64a4d` |
| **P27 通用严格化** | `DecodeStrict`：`strictly`（解码后按编码回验）——忠实性成**构造**而非待证性质；张量形状层已实例化 | **完成** | `ef241e5b` |
| **P28 严格化传播到六层** | `DecodeStrictAll`：`strictly_of_code` 统一六层；**`decodeSkeletonStrict` 是 P1-8 的**可计算**答案** | **完成** | `1de57bd5` 后 |
| **P29 修掉过期文档** | `T3-DECODE-DESIGN.md` 增 §17：P1-8 闭合、十二轮缺的是「回验」而非算术、状态行同步 | **完成** | `ec6dd4e8` |
| **P30 可逆性证据地图** | `REVERSIBILITY-MAP.md` + `gov/audit_reversibility_coverage.py`（`--report` 盘点、`--check` 守护、`--self-test`）；**并修好仪器本身** | **完成** | `a9c579b2` |
| **P31 可执行边界** | `ExecutableBoundary`：`ℚ` 上可执行求值 + `gridEvalRat_coe` 与 `ℝ` 一致；数见证由 `norm_num` 算出 | **完成** | `91824fc3` |
| **P32 可执行边界到权重与整链** | `ExecutableWeights`：`IRWeightsRat`、`encodeGridRat`、`decodeGridRat`、`encodeGridRat_coe`、**`endToEndRat_witness`（整链算出数值）** | **完成** | 第 979 轮 |
| **P33 插件义务 provenance 门禁复活** | `check_obligation_proofs.py` 的 `verifiedObligation` 分支**只计数不校验**；修复后暴露 **34/74** 条义务的 `file` 指向不存在的路径；登记 shrink-only 基线 | **完成** | 第 980 轮 |
| **P34 删 `frame` 字段** | `Primitive` 第 7 字段删除（无自身定律、9/11 字面 `True`、零消费者、与 `post` 重复）；分支做、验证、合并回 | **完成** | `f5ecf6d4` |
| **P35 插件能力索引** | 11 份 `plugin.yml` + `check_plugin_yml.py`：**逐字段与 Lean manifest 对照**，且每条定理必须**声明在它指名的文件里** | **完成** | 第 982 轮 |
| **P36 自审证书纠错** | `ProofSlotCensus` 的「42」→ 实测 **87/132**（72 `True.intro` + 15 `trivial`），逐插件表 + 三层交叉验证 | **完成** | `6f51065f` |
| **P37 E2 的失败面已测出（未实施）** | **链接见证 `(_proof : h)` 的设计可行，但 11 处 `thmName` 在 manifest 命名空间里不解析** | **已完成（第 985 轮）** | `465a06d4` |
| **P38 官方展品 M-1** | `Compose/Showcase/FullChain.lean`：L0→L1→L2 写成一条 `compose` 链，`fullChain_run` 证明它等于手写管线 | **完成** | `73321255` |
| **P39 官方展品 M-4** | `Compose/Showcase/L1L2.lean`：L2→L1→L2 写成一条 `compose` 链，**`l1l2Roundtrip_run` 证明它闭合于恒等**；并撞出「`ConstraintSet` 两份在同一文件相遇」 | **完成** | `1022f1cf` |
| **P40 官方展品 M-3** | `Compose/Showcase/SymbolShortcut.lean`：知识→L2→权重，**绕过 token**；`parse` 实测为全函数，故 `pre := True` | **完成** | `2f8b6d20` |
| **P41 官方展品 M-2** | `Compose/Showcase/NeuralShortcut.lean`：数据→token→权重，**绕过符号层**；并**把它的上限定理化**（`tokenShapeVector_no_identity`） | **完成** | `bc9a92d3` |
| **P42 `ModelsIR` 的约束范围** | `Core/IR/ModelsIRScope.lean`：把「`compile_sound` 重言」拆成 5 条定理——**它只约束槽 0 一个实数**，其余坐标恒 0，且只依赖码 | **完成** | `670da9f3` |
| **P43 行为性模型化 + 不共存定理** | `Lib/Compiler/ModelsBehavior.lean`：`modelsBehavior`（经 `decodeGrid` 读权重）+ 正向实例 + **`modelsIR_forbids_nontrivial_payload`（旧 `ModelsIR` 禁止一切非退化载荷）** | **完成** | `2b411eba` |
| **P44 官方展品 M-5** | `Compose/Showcase/L3L2.lean`：L3⇄L2 闭环，**两段 `post` 都是 `modelsBehavior`**；`l3l2Roundtrip_run` 证明闭环回到原网格 | **完成** | `f4e0aa8e` |
| **P45 类型重复的实测与纠正** | `audit_type_duplication.py`：三类各**恰好 1 处**真实定义（审计的 4/8/3 是 docstring 引用）；并**更正 M-4 里我自己写错的诊断** | **完成** | `0fc1085e` |
| **P46 填槽前的判据** | `audit_plugin_slots.py`：**120 槽 / 79 个字面 `True`**；且**所有具名槽位都有 `_holds` 定理**。填槽前先有判据，避免「`True` 换成 `na`」 | **完成** | `c82addd7` |
| **P47 第一个虚槽排空** | `Attention.spatial := True` → **`AttentionSpatialProp`**（掩蔽的局部性），由 `maskedSoftmax_eq_zero_of_not_mask` 证明；**79 → 78** | **完成** | `e7a0cd2e` |
| **P48 Attention 一次排空三槽** | `approximation`/`invariants`/`refinement` 三槽换成有证明的命题；**78 → 75**，Attention 12 槽中 8 槽有内容 | **完成** | `167da41b` |
| **P49 掩码代数 + 再排三槽** | 新建 `Lib/Attention/RealMaskAlgebra.lean`（单位/交换/幂等/结合 + 输出层推论）；`recovery`/`confluence`/`idempotence` 三槽填充；**75 → 72**，Attention 12 槽中 11 槽有内容 | **完成** | `195714d8` |
| **P50 Attention 满格 + Norm 首槽** | `Attention.completeness` 填充 ⇒ **Attention 12/12**；`Norm.completeness` 填充；**72 → 70**。并**拒绝**用 `rfl` 命题填 `Norm.refinement` | **完成** | 第 999 轮 |

## 1.1 一次**真实丢失**：`ShiftSubstOffsetProbe.lean`（第 1013 轮，不可恢复）

**第 1012 轮我的 `gov/clean_probes.py` 用「未被 git 跟踪」作为残骸判据，删掉了
`Lattice/Core/CIC/ShiftSubstOffsetProbe.lean`。下一次全库构建失败——`Lattice/Core.lean:11` 与
`ShiftSubstOffset.lean:2` 都 import 它。**

**⇒ 判据被它自己的第一次「成功」证伪：`.gitignore:38` 是 `*Probe.lean`，所以**真实的探针模块同样未被跟踪**。**
**⇒ 现行判据：一个探针源是残骸，当且仅当它**未被跟踪**且**没有任何被跟踪文件 import 它**（`git grep -l -F "import <模块>"`）。**

**损失：4 条定理（`theorem+lemma` 9844 → 9840）。文件是 gitignored 的，无法从历史恢复，**
**其定理名与陈述已不可知，故**无法重建**——本台账记录它曾存在、含 4 条定理、已丢失，**
**而不是伪造一次「恢复」。**

**恢复过程中确认「无被跟踪模块失去引用」：`ShiftSubstOffset.lean` 全文 61 行只用到
`shift`/`subst`/`.var`，故两行 import 是残留；删掉后全库构建通过。**

**⇒ 教训：我把一个未经测试的定义（「残骸」）当成了已确立的判据，并据此**删除**文件。
删文件的工具必须先有能抓住误删的自检，而它的自检当时只覆盖了「孤儿构件」，没有覆盖「已导入的探针」。**

**=> P8 的 §10 四条边界：1 已闭合（P16）、2 已证否并修正、3 已闭合（P11–P15）、4 已闭合（P8 单一函数）。**

---

## 2. 仍然开放的项（具名，未开始）

| # | 项 | 为什么没做 | 下一步形态 |
|--:|:--|:--|:--|
| **O-1** | ~~`Core/IR` 里 IR 权重类型的短名**重复定义**~~ | **已闭合（第 967 轮）——**这是误判** | 查明：`FinSupport.lean` 那处位于**模块 docstring 的代码块**，不是定义；全库真实定义只有 `Compile.lean:74` 一处。根因是 `audit_duplicate_names` **未剥注释**。已修（先剥注释与 docstring 再匹配），基线从 541 重测为 **367**（即旧基线中 174 个、32% 是 docstring 假阳性） |
| **O-2** | ~~P1-8 迁移（约 38 个文件 / 217 处）~~**——**该描述是错的**。P1-8 是**一件事**：`decode : ℕ → Option IRSkeleton`，对非骨架码返回 `none` | **两个方向都已交付（第 972–976 轮）** | 正向：`decodeSkeleton_code`。反向：**`decodeSkeletonStrict_faithful` + `decodeSkeletonStrict_none_of_not_code`（`Core/IR/DecodeStrictAll.lean`）——且解码器**可计算**。规格层的非可计算版本另在 `DecodeSpec`。**⇒ O-2 闭合；余下可选的推广是把 `strictly` 用到 `decodeList` 之外的其它载体** |
| **O-3** | P6 剩余（可逆性判据的更多实例） | **已闭合（第 977 轮实测）** | 四跳的证据**全部齐全**（见 `REVERSIBILITY-MAP.md`）：符号⇄权重有往返+忠实+丢失；张量形状三列齐；token⇄符号有往返+丢失；数据⇄token 的丢失**就写在** `decode_encode_shape` 的结论里（只恢复个数与顺序）。**⇒ 工具列出的「候选缺口」经逐条裁定**都不是缺口**（左逆已蕴含单射；`decodeList` 是总函数）** |
| **O-5** | **`gov/` 里 **21 份** `strip_comments`（含 1 份 `strip_comments_keep_docs`）** | **部分闭合（第 968–969 轮）** | 实测：21 份 → **8 种不同行为**（1169 真实 Lean 文件 + 2 边界用例）。最大簇 **9 站点逐字节相同**。已建权威 `gov/tools/lean_source.py`，切换其中 **5 个**非 `repro` 站点（21 → 16）。**第 969 轮查明 `tools/sorry_axiom_census` 那份不是重复而是**更强**实现**（块注释内**保留换行**，故诊断行号不漂移；并与本权威在 1152/1171 输入上不同），**且它被记忆化供热路径 `gate.py` 使用** ⇒ **明确决定不收敛**，并把该差异钉进 `lean_source.py --self-test`（防止后人误合并）。余下站点均有记录理由 |
| **O-4** | 会话早期规划的 P0 组（7 项中完成 6 项，剩余 1 项未在文件中具名） | **已闭合（第 966 轮）** | 该项已失传，故按「不可恢复即不可悬挂」处理：改为一个**可导出**的等价项——**审计表对 P8 过时**。`gen_objective_audit.py` 的「符号⇄权重」一行原本只引 P8 之前的声明；现已补入 P8 判决，并给生成器加了**引用必须存在**的自检（`--self-test`，双向：真实引用全命中 + 伪造引用被抓） |

**=> O-4 的处置方式本身是本文件的教训：一个无法命名的项，应当被**替换为可导出的项**，
而不是留在台账里当幽灵义务。**

**=> O-4 是本文件要解决的核心问题：一个没有落到文件里的计划项，等于不存在。**

---

## 3. 下一轮队列（第 59 轮宏观复核后重写）

### 3.0 本轮测量的宏观状态

| 维度 | 实测 |
|:--|:--|
| 提交 / 模块 / theorem+lemma | **1278 / 1,084 / 9,846** |
| 承重审计 | **1056 / 1056 = 100%** |
| 插件虚槽 | **47 / 120**，其中 **21 个已测为诚实空集** |
| 验证 | **`VERIFY ALL [fast]`: PASS**（86 门禁 / 377 秒）；完整版 11 项 reactivity 未跑 |
| 门禁 / 报告器 | **97 / 21** |

**⇒ 填槽战役已到边际递减：16 轮从 87 降到 47，剩余 26 个里多数已判定为「拒绝」或「空集」。**

### 3.1 **真正的缺口：目标原话里三个「只有名字」的载体**

**`OBJECTIVE-MAP.md` 的判据是「跨文件引用数为 0 的载体是一个名字，不是一次交付」。**
**按它测量，目标原话「正向把符号知识编译成权重（约束损失、数据合成、结构化初始化）」**
**对应的三个载体是全表最弱的：**

| 条款 | 载体 | 跨文件引用 | 已测得的真相 |
|:--|:--|--:|:--|
| **2.1 约束损失** | `penaltyToLoss` | **0** | **有 4 条定理，含 `sound_holds`——它不是桩，而是**无消费者**** |
| **2.2 数据合成** | `covered_of_vanishing` | **0** | 仅本文件 2 处引用 |
| **2.3 结构化初始化** | `compile_sound_n` | 1（同文件 0） | 只被 `NondegenerateInstance` 用一次 |

**⇒ 缺口**不是「再证一点」**，而是**接线**：把这三处接到 `Lib/`、`Usage/` 或一个可执行展品上。**

### 3.2 队列（按价值排序）

1. **Q-1（最高）**：为 `penaltyToLoss` 建立**第一个跨文件消费者**——最自然的是
   「`penaltyToLoss E` 编译出的损失在极小点处满足 `E.satP`」，并把它接进 `Usage/Examples.lean`
   或 `Compose/Showcase/`。**判据：`OBJECTIVE-MAP.md` 中 2.1 的跨文件引用从 0 变成 ≥1。**
2. **Q-2**：同样为 `covered_of_vanishing`（2.2 数据合成）建立消费者；若它在语义上无法被消费，
   **则记录原因并把该条款重述为「已证不可达」**。
3. **Q-3**：`compile_sound_n`（2.3 结构化初始化）——它已被 `NondegenerateInstance` 用一次，
   **若要提升，需要让那条使用产生一个可引用的结论**（而不是只在实例里出现）。
4. **Q-4（低）**：继续填槽，但**只填有非平凡事实的**；`Penalty` 剩 2 个已判定为「假」与「平凡」，
   `Norm`/`DAG`/`GNN`/`Constraint`/`Conv` 的剩余项逐个先测再决定。

**⇒ 理由：Q-1..Q-3 直接对应目标原话的三个括号，而 Q-4 是在一个已经降到 47/120、
且 21 个已证为空的维度上继续投入。**

### 3.3 **第 65 轮的重大发现：闭环的后两步在主树里没有载体**

**`OBJECTIVE-MAP.md` 的 31 个载体中有 **9 个「未找到」**，且不是仪器故障——`sqDistFix` 在
`Primitives/MultistepLoop.lean:10` 只是**docstring 里的提及**，`evalPts` 在
`Lib/Penalty/QuadraticNotLipschitz.lean:16` 只是**字段访问**，二者都**不是声明**。**

| 条款 | 无载体的名字 | 后果 |
|:--|:--|:--|
| 2.2 数据合成 | `synth_coverage` | 尚有 `covered_of_vanishing`（已接消费者） |
| 3.2 逆向验证 | `geo_sampled_bound` | 尚有 `EpsSat`（已接消费者） |
| **3.3 逆向修正** | `sqDistFix` `parallelFix` `midpointFix` | **整条款零主树载体** |
| **3.4 逆向再注入** | `reinject_loss_eq_zero` `partial_reinject_bound` | **整条款零主树载体** |
| **5 符号引擎** | `evalPts` `derivation_sound` | **整条款零主树载体** |

**⇒ 这些名字的真实声明只在**已归档的几何层**（`Reference/`）。第 265 轮的 STAGE 0 归档了几何层，
并在 `check_objective_coverage.py` 的注释里写明「载体的定义必须位于主树，归档层不在判据之内」，
但**当时为受影响条款补的替代载体，只覆盖了 2.2/2.3/3.2，没有覆盖 3.3/3.4/5**。**

**⇒ 而 `check_objective_coverage.py` 仍然 PASS，因为它只问「名字在自己的 `CLAUSES` 列表里吗」——
这正是 `OBJECTIVE-MAP.md` 开头自己警告的**最弱读法**。本轮把一个更弱的事实摆出来了：
**这些名字在主树里连声明都没有。** **

**⇒ 结论：目标的闭环「验证 → 修正 → 再注入」中，**「验证」有主树载体，「修正」与「再注入」没有**。
「符号模型直接跑在符号引擎上」这一条款同样没有。**

**⇒ 下一轮的队列因此重排：`A-1` 为 3.3/3.4/5 建立**主树载体**，优先于任何引用数或虚槽工作。**



---

## 4. 纪律（本会话反复验证过的，写下来以免重犯）

### 4.1 先 probe，再实现

**每次遇到形状敏感的证明，先写 `Lattice/Probe/*.lean` 单独编译，确定 tactic 形态后再移植。**

**=> 已连续四轮奏效（第 949、955、960、962、965 轮）。**

### 4.2 文档数字按**文档**分别同步

**至少存在**两套**「定理数」度量：**
- `audit_counts.py` 的「定理总数」；
- `check_coverage_claim.py` 的「theorem+lemma」。

**=> 且 `STATE-FINAL` / `DELIVERY` / `CONVENTIONS` 用第三套口径。
=> 必须**按文档分别**写，不能全局替换。**

### 4.3 含星平面字符的文件，绝不经 Python 写入

**`𝓝`、`𝔸`、`𝕜` 等会让 Python 写入崩溃（`surrogates not allowed`），且**先把文件截断为 0 字节**。
**=> 更糟：**空文档仍能通过全部文档门禁**（门禁查错误内容，不查内容缺失）。**

**=> 规则：这类文件用 `write`/`edit` 工具；若已被截断，`git checkout --` 还原后重做。**

### 4.4 `audit_duplicate_names` 会扫描**注释里的代码块**

**它的正则按行匹配 `def|theorem|lemma|structure|inductive|abbrev|instance` + 名字。**
**=> 在 docstring 里引用 `abbrev X` 会被计为一次**定义**，使短名计数超基线。**

**=> 规则：散文里**转述**此类片段，或去掉关键字。**

### 4.5 杀掉 `verify_all` 后要先清理**三个**探针

**反应性测试会在真实树里**植入探针**来证明门禁会红，正常结束时会自行恢复。**
**=> 作业被杀时它们**同时**存活，各自触发不同的不变量：**

| 探针文件 | 植入者 | 触发 |
|:--|:--|:--|
| `Lattice/G4Probe.lean` | `verify_g4.py` | I7（无 olean）+ 别名计数 |
| `Lattice/Core/Probe.lean` | `gate_reactivity.py` | I7（无 olean） |
| `Lattice/Runtime/LayeringProbe.lean` | `layer_reactivity.py` | **I4（分层违规 runtime → geo）** + I7 |

**=> 第 970 轮我被 `LayeringProbe.lean` 困住：`gate.py` 报 `FAIL(4)`（I4），
而我先去查自己的新文件，实际是残留探针。**

**=> 规则：杀掉任何 `verify_all` 之后，先删这三个文件再重新测量。**

**⚠ 第 975 轮的补充（我在这上面栽了两次）：**

| 错误 | 后果 | 正确做法 |
|:--|:--|:--|
| **只删源码，留下 `.olean`** | **I7 报 `stale artifact`（有 olean 无源），`gate` 退出码 **8**——看起来像真实的门禁失败** | **源码与其 `.olean`/`.ilean`/`.trace` 必须**成对**删除** |
| **用通配符 `*Probe*` 删产物** | **误删了 `Lattice/Core/CIC/ShiftSubstOffsetProbe` 的 olean——它的**源码仍在**（gitignore 覆盖），于是 I7 报「有源无 olean」** | **只按**精确路径**删那三个探针，不要通配** |

**=> 判据：`gate` 退出码 **8** = I7 有问题，**先把 `.lake/build` 里的探针产物与探针对齐**，再去怀疑代码。**

### 4.5b 诊断前先看**机器资源**

**同一次会话里，`gate.py` 先报 `FAIL(4)`，再报 `exit=-1`，再报正常——三次同一份代码。**
**=> 真因是**可用内存降到 0.7 GB**（共 15.7 GB）：进程被系统杀掉，`-1` 与随机截断都是假象。**

**=> 规则：出现「同一命令时好时坏」时，先查 `FreePhysicalMemory` 与残留进程，
再去怀疑代码。**

### 4.10 写新文件前必须查它**是否已被跟踪**

**第 972 轮我用 `write` 在 `Lattice/Core/IR/Decode.lean` 上「新建」文件，
而它**早已是被跟踪的 317 行文件**（第 206 轮的燃料式解码链）。**

**=> 后果：`DecodeRelations.lean` 立刻失去 `decodeList`，`lake build Lattice.Core` 失败。
=> 唯一发现途径就是这次构建失败。**
**=> 恢复靠 `git checkout --`，但我已在这条路上浪费了一轮的大部分预算。**

**=> 规则（强制）：写任何路径前先 `git ls-files <path>`；非空则**读后编辑**，不得 `write` 整个替换。**

### 4.11 台账项若「连续多轮不可执行」，先怀疑**记录本身是错的**

**同类事件第三次：**

| 轮次 | 台账原文 | 实测真相 |
|:--|:--|:--|
| 967 | O-1「IR 权重类型短名重复定义」 | 是扫描器假阳性，**不存在** |
| 970 | O-4「P0 组剩余 1 项」 | 无法命名，已替换为可导出项 |
| **972** | **O-2「P1-8 迁移 38 文件 / 217 处」** | **完全记错：P1-8 是**一个函数**，且**早已交付** |

**=> 规则：动手前先花几分钟**核实台账条目的真实含义**（用 `git grep` 找原始出处），
不要相信自己在旧轮次写下的概括。**

### 4.6 断言先写成定理，再写进文档

**第 954 轮我把一条**假断言**写进 `P8-LOWER-BOUNDS.md`，全部文档门禁仍绿。**
**=> 抓到它的是第 955 轮**试图把它变成定理**时失败。**

**=> 唯一能抓到错误数学断言的检查器是证明器。**

### 4.7 文档里的**引用**也需要守卫

**第 966 轮发现：`OBJECTIVE-AUDIT.md` 的证据列是一份**硬编码**的声明名清单，
而**没有任何东西检查这些名字还存在**。**
**=> 它在 P8 完成 21 个文件之后仍然只引 P8 之前的声明——**静默过期**。**
**=> 现在 `gen_objective_audit.py` 在生成前校验引用，且 `--self-test` 证明该校验**能失败**。**

**=> 规则：任何「引用了某处声明」的表格，都必须有一个能失败的存在性检查。**

### 4.8 数字改动要**实测**，不要推算

**第 966 轮新增一项检查后，文档里关于「检查数/门禁数」的表述互相矛盾
（`105 = 84 + 22`、`105 = 69 + 21` 都不成立）。**
**=> 直接 import `verify_all` 数出来：`CHECKS=106`、`REPORT_ONLY=21`、门禁 `85`，一次对齐。**

**=> 规则：改计数前先跑一次能打印**权威数字**的脚本，别在文档间互推。**

### 4.9 「测量出来的」也要核对被测对象

**第 965 轮我「测量」出 IR 权重类型的短名在 `Core/IR` 里被定义了两处，并把这个结论**写进了 Lean 文件与台账**。**

**=> 第 967 轮查明那是 `audit_duplicate_names` 的**假阳性**：其中一处其实在模块 docstring 的代码块里。**

**=> 于是我从「台账」里删掉了一个**不存在**的义务，并把 Lean 文件里那条假记录改成了纠正说明。**

**=> 规则：测量工具的结论与被测对象本身，两者都要看。一个不做**剥注释**的扫描器，
会把文档里的示例当成事实。**

---

**生成于第 965 轮。**

### 3.4 **第 1032 轮：定义式重言的量化普查**

**`check_proof_strength.py` 抓三种形状（自反陈述、`exact h`、`True` 状 def），但**不抓**第四种：**

```lean
def ModelsTerm (W : CICWeights) (t : Term) : Prop := W = compile t
theorem compile_sound (h : Typable K Γ t) : ModelsTerm (compile t) t := by
  have := h
  exact rfl
```

**⇒ 结论在展开后恒真，假设 `h` 是**装饰性**的。这一形状已在**两层**出现：
`Core/IR/Obligations.lean` 与 `Core/CIC/Compile.lean`。**

**⇒ 新工具 `gov/audit_definitional_proofs.py` 编码两种窄形状（零假阳性、带自测）：
`rfl_only`（整证明是一个 `rfl`）与 `haves_then_rfl`（`have` 行 + `rfl` 收尾）。**

| 实测 | 值 |
|:--|--:|
| 定义式证明总数 | **661** |
| 其中 `rfl_only` | 659 |
| 其中 `haves_then_rfl` | **2**（即那两条 `compile_sound`，入度各 3） |
| 其中**承重**（入度 ≥ 1） | **146** |

**⇒ 判读：661 条里绝大多数是**递归定义的展开引理**（`size_var : size (var x) = 1 := rfl`），
这是惯用写法、不是缺陷。真正的缺陷形状只有 `haves_then_rfl` 那 2 条，而它们正是
「谓词把自身参数钉死」的例子。**

**⇒ 基线 `gov/definitional-proof-baseline.txt` 已接入 `verify_all.py`（两项：`--check` 与 `--self-test`），
且 `--check` 对**陈旧条目**也报错，使基线只能收缩、不会悄悄失效。**
### 3.5 **第 1034 轮：几何层归档——测出来的结论是「不能物理归档，只能冻结」**

**用户指令：把几何相关的归档掉，不要浪费时间。⇒ 先测量，再执行。**

| 实测 | 值 |
|:--|--:|
| 几何层模块数 | **100** |
| 行数 | **~17,838** |
| 主树直接导入者 | **26** |
| 使用 `Lattice.Geo.*` 符号的主树文件 | **43** |
| 这些导入的传递闭包 | **100**（= 全部） |
| 簇外导入进该层的文件 | **0**（该层封闭） |

**⇒ 结论：**部分归档不可行**。我从「被使用的符号」反推，得出 68/100 可归档，实际搬到 `_archive/`
后**构建失败**（主树直接导入的 26 个模块传递依赖剩下的全部）。恢复后构建正常；该尝试只留在分支
历史里，不再重复。**

**⇒ 所以在治理层归档，并把它变成可执行的门禁：**

- **`gov/check_frozen_reference.py`**：几何层的**主树导入者集合**是基线（26 条）；**新增导入者失败**，
  **基线条目消失也失败**——故该集合**只能收缩**。
- **`gov/frozen-reference-baseline.txt`** 记录那 26 条。
- **`CLAUSES` 删除了两个只存在于几何层的名字**（`synth_coverage`、`geo_sampled_bound`），
  **⇒ 目标表「未找到」从 2 降到 0**，后续轮次不会再被它们误导去追几何。

**⇒ 这不是「几何是错的」，而是「几何是例子**：**在它上面花的时间就是在链上没花的时间**。**
### 3.6 **第 1039 轮：连接矩阵——「闭环缺接口」是错的，而且我连续三轮都猜错**

**连续三轮我假设链条上有缺口，每次都被测量推翻：**

| 轮 | 我的假设 | 实际已有 |
|--:|:--|:--|
| 76 | 闭环没有被形式化 | **`Runtime/LoopClosure.lean` 就是闭环**（`extractLayer` 31 个文件引用） |
| 78 | `extract` 的 `none` 分支没有消费者 | **`decodeSpec_none_of_not_code`、`hop_verdict` 第 1 项、`relu_not_reversible`** |
| 79 | 提取与修正之间没有接口 | **`RepairClosure.extract_after_repair`（修复 → 提取 → 再验证）** |

**⇒ 这不是运气差，而是**模式**：**关于缺口的假设不可靠，因为树比我的猜测更密**。
**⇒ 正确方法是**枚举**，不是猜。**

**⇒ 新工具 `gov/chain_connectors.py`：对目标的 8 个阶段两两求交，只数**陈述**里同时出现两侧标记的定理
（不数证明——证明提到什么都是噪声）。**

**第一版词表给出两个空格：`3.2 verify → 3.3 repair` 与 `3.4 reinject → 4 loop`。
补上树自己用的词（`AllSatisfied`、`LayerSat`、`V.run`）后，两个空格都**闭合**。**

**⇒ 结论：那两个空格是**我词表的缺陷**，不是树的缺口。7 个相邻链节现在**全部**有连接定理。**
**⇒ 并且这条结论被做成了门禁：`chain_connectors.py --check` —— **相邻链节不得变空**。
它不要求数量（一条就够构成一个链节），也不管非相邻格（那两个阶段本就不该直接相遇）。**
### 3.7 **第 1041 轮：链节的「年龄」——两个链节只由最近几轮支撑**

**`chain_connectors.py --provenance`（新增）：把每条连接定理的**声明行** blame 出来，
统计它早于最近 `K` 次提交（默认 30）的比例。**

| 链节 | 连接数 | old | recent | 判定 |
|:--|--:|--:|--:|:--|
| 1.1 → 1.2 | 6 | 5 | 0 | OK |
| 1.2 → 1.3 | 7 | 7 | 0 | OK |
| 1.3 → 1.4 | 55 | 48 | 4 | OK |
| 1.4 → 3.2 | 19 | 18 | 0 | OK |
| 3.2 → 3.3 | 2 | 2 | 0 | OK |
| **3.3 → 3.4** | 3 | **0** | **3** | **FRESH-ONLY** |
| **3.4 → 4** | 3 | **0** | **3** | **FRESH-ONLY** |

**⇒ 那两个链节的连接**全部**是我最近若干轮写的（`closed_loop_reinject_vanishes`、`closed_loop_ends_verified_and_zero`、
`one_round_is_one_repair_step`）。它们是**证明过的**，所以不是错误；但这个链节**没有更早的独立支撑**。**

**⇒ 而且这一点**无法通过再写定理修好**：任何我现在写的定理都会是新提交，`fresh-only` 依旧。
唯一能改变它的是**找到既有定理**，而矩阵说明不存在。所以这是一个**关于树的性质**，不是待修的缺陷。**

**⇒ 一个方法学上的限制也记下来：`K` 是「新旧」的**代理**，不是「是否我写的」。
`closed_loop_reinject_vanishes` 在第 66 轮创建、距今 21 次提交，按 `K=30` 算「新」——虽然它确实也是我写的。
所以 `FRESH-ONLY` 应读作「没有比最近 K 次提交更早的支撑」，而不是「作者是同一人」。**
### 3.8 **第 1042 轮：为什么那两个链节是 FRESH-ONLY——根因不是支撑薄，而是那一段曾长期只是字段**

**测量（第 1042 轮）：**

| 事实 | 数值 |
|:--|--:|
| 主树里 `V.step` 的消费者 | **0** |
| 使用 `objective` 字段的**定理** | **2**（均为第 66、77 轮新增） |
| 同一文件里 6 条旧定理（`loop_terminates_sat` 等）的年龄 | **508 次提交前** |
| 这 6 条旧定理谈论的对象 | **只有 `run` / `Sat` / `μ`，没有 `objective`** |

**⇒ 结论：再注入这一段在 508 次提交里是「一个字段 + 一个没人用的 `step`」。**
**⇒ 所以 `3.3 → 3.4` 与 `3.4 → 4` 的 `FRESH-ONLY` 不是「我的支撑薄」，而是**「这一段本身就直到最近才被交付」**。
这是一个**关于树的性质**，而且**不能靠再写定理改变**：任何新写的定理都是新提交。**

**⇒ 本轮顺手修掉一处**声称但未证**：`step` 的 docstring 写着「下一轮的输入与本轮相同——这正是『闭合』要求的」，
但没有对应定理。现在补上：**

```lean
theorem step_fixed_of_sat (h : V.repair.Sat x) : V.step x = (x, V.objective x)
```

**⇒ 由 `Repair.absorbs` 得出，不是定义展开；且 `step` 不再是死定义。**

**⇒ 另修工具一处误分类：**未提交行**的 blame 是全零 sha，原先被归为 `old`——于是**正在被审的工作把自己算作自己的支撑**。
现在单独归为 `pending`。**
### 3.9 **第 1043 轮（规划 P0-a）：产物契约落地——布局就是截面，求值是派生的且**部分**的**

**规划 §4.1 要求产物携带 `layout` / `weights` / `domain` / `eval` / `recipe`，并规定
「`eval` 必须与 `layout` 一致；只有 `weights` 而缺 `layout` 与 `recipe` 的产物不得进入行为级定理」。**

**⇒ 实现于 `Lattice/Lib/Compiler/Layout.lean`（不是 `Core/`，见下）：**

| 契约项 | 实现 | 关键点 |
|:--|:--|:--|
| `layout` | `gridLayout : PartialSection (ℕ → Segment) (ℕ → ℝ)` | **布局 = 第 1036 轮那个抽象的一个实例**：编码全（`encodeGrid`）、解码部分（包装成 `some`）、像上往返（`decodeGrid_encodeGrid`）、编码单射（`encodeGrid_injective`） |
| `weights` | `weights : ℕ → ℝ` | 未解释的数值载荷 |
| `domain` | `SemDomain`（`lo ≤ hi`） | 只承诺比较范围 |
| **`eval`** | **派生 `evalAt : Option ℝ`** | **不是字段**——由 `layout.extract` 与 `recipe.n` 算出 |
| `recipe` | `CompileRecipe`（`n` + `0 < n` 证据） | 边界条件写进产物，不留给调用者 |

**⇒ 两条实质性定理：**

```lean
theorem evalAt_ofSegments : (ofSegments g dom r).evalAt x = some (gridEval g r.n x)
theorem evalAt_isSome_iff_payload_isSome : (A.evalAt x).isSome ↔ A.payload.isSome
```

**⇒ 第二条是规划 §4.2「失败语义」的答案：`evalAt = none` 的**唯一**解释是
「按该产物自己的布局，其权重解不出分段族」；域外、参数非法、实现未完成都不可能造成失败
（`n > 0` 由 `recipe.hn` 保证，域不限制求值）。**

**⇒ 为什么把 `eval` 写成派生而**不是字段**：`Runtime/VerificationLoop.objective` 曾是自由字段，
于是「再注入」在 508 次提交里是一个没人用的定义（§3.8 实测）。派生写法让同一错误**在类型层不可重复**。**

**⇒ 两处被门禁抓到并修正（都是我造成的）：**

1. **I3「定义唯一」**：`eval` 与既有定义同名 3 次 ⇒ 改名 `evalAt`（约定：带点的求值）。
2. **I4「分层」**：文件原放在 `Core/`，而它依赖 `Lib.Compiler.*`——**分层方向是 Lib → Core**，
   故 `Core` 不得导入 `Lib`。⇒ 文件移到 `Lattice/Lib/Compiler/Layout.lean`，命名空间相应为
   `Lattice.Lib.Compiler`。
3. 移动后 I7 报**旧构建产物**（`Lattice.Core.Layout` 的 `.olean` 源已不在）；用
   `clean_probes.py --clean` 按其设计用途清掉 5 个文件。

**⇒ P0-a 尚缺（记入下一轮）：**「两个不同布局不能混用」的**具体反例**——即存在同一 `weights`
在两个合法布局下得到不同 `payload`。现在结构上已保证「必须携带布局」，但**还没有一条定理**给出
混用会改变行为的见证。
### 3.10 **第 1044 轮：P0-a 收尾——同一权重在两个**合法**布局下解出不同载荷（见证）**

**§3.9 记录的唯一缺口是「结构强制携带布局，但**没有定理**说明换布局会改变载荷」。本轮给出见证。**

**做法（复用第 1036 轮的抽象，不新造语义）：**

1. `shiftOffset : ℕ → ℝ := fun i => if i = 0 then 1 else 0`——**只在位置 0 加 1**。
   选它是因为 `decodeGrid w k = ⟨w (2k), w (2k+1)⟩`，位置 0 恰是第 0 段的**斜率**，
   故它**只影响一个可观察分量**。
2. `shiftEncode g := fun i => encodeGrid g i + shiftOffset i`，并证明它**仍单射**
   （逐点消去偏移，再用 `encodeGrid_injective`）。
3. `shiftLayout := PartialSection.of_injective shiftEncode shiftEncode_injective`
   ——**与 `gridLayout` 同类型、同四条义务**的第二个合法布局。

**⇒ 见证定理：**

```lean
theorem layouts_disagree_on_shared_weights :
    ∃ W : ℕ → ℝ, gridLayout.extract W ≠ shiftLayout.extract W
```

**取 `W := shiftEncode z`（`z` 是常零分段族）：**
- 按 `shiftLayout`：`W` 正是 `z` 的编码 ⇒ 解码回 `z`（用 `extract_eq_some_of_compile_eq`）；
- 按 `gridLayout`：`decodeGrid W` 第 0 段斜率 = `W 0 = 0 + 1 = 1`，而 `z` 第 0 段斜率 = `0`。

**⇒ 两条解码结果不同（`Segment.m` 分量差 1）。**

**⇒ 这条不是「某个实现有 bug」，而是规划 D1 的必要性证据：同一串数在两个**都满足 `PartialSection` 义务**的
布局下**确实**指向不同分段族。所以「解释必须随产物携带」不是形式要求，而是**语义要求**。**
### 3.11 **第 1045 轮（规划 P0-b）：两个样例产物，以及「由 ε 定 n」的可判定条件**

**文件：`Lattice/Lib/Compiler/Samples.lean`。四个定理，全部落在产物自己的 `evalAt` 上。**

| 定理 | 内容 |
|:--|:--|
| `gridEval_affineFamily` | 常分段族的网格求值就是该仿射函数 |
| **`affineSample_exact`** | **产物求值处处 = `a·x + b`（误差为零）** |
| **`xSquaredSample_bound`** | **`∃ v, evalAt x = some v ∧ \|x² − v\| ≤ 1/(4n²)`，`x ∈ [0,1]` 全域** |
| `budget_of_sq` | **`1/(4ε) ≤ n²` ⟹ 误差 ≤ ε**（可判定的选择条件） |
| `exists_grid_for_eps` | 对任意 `ε > 0`，**存在**满足该不等式的 `n` |

**⇒ 三点值得单说：**

1. **仿射样例的零误差**走的是 `evalAt_ofSegments`（用 `PartialSection.retract`）——
   即**编译-解码往返的结果**，而不是「把两件事定义成同一件」。
2. **`x²` 的界陈述在 `evalAt` 上**，不是在一个平行定义的 `gridEval` 上：
   `evalAt_ofSegments` 把产物求值换成 `gridEval`，再由 `irWeights_error_bound` 给界。
3. **「由 ε 定 n」被落实为一条不等式**（`budget_of_sq`），并证明它**总有解**
   （`exists_grid_for_eps` 用阿基米德性质取 `n > √(1/(4ε))`）。
   **⇒ 我**没有**假装构造出 `⌈1/(2√ε)⌉`——那需要 `Nat.ceil`；本文件把选择条件写成不等式并证明可满足，
   比「存在某个合适的 `n`」强，且不虚报。**

**⇒ 尚未做的（下一轮）：把 `ExprExt` 的符号项**真的**喂进这条链**——
即定义一个从 `ExprExt`（含 `mul`）到分段族的编译函数，并证明「仿射项 → 仿射族」「`mul (var 0) (var 0)` → `x²` 的近似族」。
本轮的两个样例**已经是产物级**的，但它们的输入仍是**分段族**，不是符号项。**
### 3.12 **第 1047 轮（规划 P0-c）：真实写回——`Repair` 第一次作用在**权重载荷**上**

**文件：`Lattice/Lib/Compiler/WriteBack.lean`。规划 §3.3 的 C.2 要求最终定理同时给出四项，本轮逐项交付：**

| 规划要求 | 实现 |
|:--|:--|
| **改到的部分** | 第 0 段斜率被置为目标值 `a`（`slopeFix_sat`） |
| **保留的部分** | 第 0 段截距不变（`slopeFix_keeps_intercept`）、其余**逐段不变**（`slopeFix_preserves_rest`） |
| **到达方式** | **有限一步**（`slopeMeasure` 取 `ℕ` 值，正因为不存在需要数步的情形） |
| **失败分支** | 本实例**没有**：`slopeFix` 对任意族都有定义 |

**⇒ 载体是 `ℕ → Segment`（载荷），并给出 `Repair (ℕ → Segment)` 实例 `slopeRepair`，三条义务全部证明。**

**⇒ 两条实质定理：**

```lean
theorem repair_changes_observable (hba : b ≠ a) (hx0 : x ≠ 0) (hidx : segmentIndex n x = 0) :
    gridEval (slopeFix a (constFamily b c)) n x ≠ gridEval (constFamily b c) n x

theorem write_back_verifies_and_changes ... :
    slopeSat a (slopeFix a (constFamily b c))
      ∧ (writeBack (slopeFix a (constFamily b c)) dom r).evalAt x
          ≠ (writeBack (constFamily b c) dom r).evalAt x
```

**⇒ 第二条是规划 C.5 的验收：**修复确实改变了至少一个可观察量**，而且落在**写回后的产物**上
（`writeBack` 把修好的载荷重新编码进权重），不是只改内部表示。**

**⇒ 诚实边界：可观察变化**要求调用者给出一个「第 0 段内且 `x ≠ 0`」的点**（前提 `hidx` 与 `hx0`）。
把它作为前提而不是在定理里假设 `r.n = 1`，是因为「哪个 `x` 落在第 0 段」取决于 `r.n`——
把条件写成交给调用者**更强也更诚实**。**

**⇒ 三处被编译器抓到的问题（都是我造成的）：**
1. `slopeMeasure` 需 `noncomputable`（实数等式判定依赖 `Classical`）；
2. `rw [if_pos h]` 在条件**定义等价但非同形**时失败 ⇒ 改 `exact if_pos h`；
3. `simp` 会把 `if` 的条件化约成 `True` 却**不化约 `if` 本身**，于是任何手写 `show` 都不匹配
   ⇒ 改为**先算两条求值等式**（`e1`、`e2`）再比较实数，把工作留给 `linarith` 而不是留给我猜形状。
### 3.13 **第 1048 轮（规划 P1-a）：官方配方的单一陈述，且新增了**提取接缝**这一条真定理**

**文件：`Lattice/Lib/Compiler/Chain.lean`。规划 §5.2 要求「手工列出配方、机器检查每一步」。**
**本文件的每个接缝都是既有定理，新增的只有**接缝本身**与顶层陈述。**

| 节点 | 提供方 | 目标 |
|:--|:--|:--|
| 源语义 | `evalSym_squareTerm` | `evalSym x squareTerm = some (x·x)` |
| 编译 | `compileTarget_squareTerm` | `= some (.squareApprox r.n r.hn)` |
| 构造 | `ofSegments` + `Target.family` | 产物 |
| 求值 | `evalAt_ofSegments` | `evalAt x = some (gridEval …)` |
| 保证 | `irWeights_error_bound` | `\|x² − v\| ≤ (1/n)²/4` |
| **提取** | **`decodedFamily_ofSegments`**（新） | **提取回的族就是被证明有界的那个族** |
| 修复 | `slopeRepair` | 三条义务 |
| 写回 | `writeBack` + `writeBack_evalAt` | 重新编码进权重 |
| 重验 | `write_back_verifies_and_changes` | 判据成立 ∧ 可观察值改变 |

**⇒ 唯一的新定理是提取接缝：`decodedFamily_ofSegments g dom r : (ofSegments g dom r).decodedFamily = some g`，
由 `gridLayout.retract` 得出。**

**⇒ 它补的是一个**实质缺口**：此前 `square_path_bound` 只说「产物求值有界」，
**没有说「提取回的东西就是那个有界的族」**。而没有后一句，「提取 → 验证」在产物层其实没接上——
读者得自己相信「产物里的载荷就是那个族」。**

**⇒ 顶层定理 `official_chain_recipe` 把 A 段（源语义 + 编译 + 整域界 + 提取接缝）与
C 段（修复 + 写回 + 重验 + 可观察变化）并置为一条可引用陈述。**

**⇒ 明确**不**承诺：本定理不声称「修复后的产物仍满足 `x²` 的误差界」——修复改变斜率，
那条界**确实不再成立**。分开陈述正是为了避免这种误读。**

**⇒ 三处我造成的错误，都被门禁或类型系统抓到：**
1. verdict JSON 里写了 `\|`——**JSON 非法转义**，`check_coverage_claim` 直接报 `Invalid \escape`；
2. verdict 把 `square_path_bound` 指到 `Samples.lean`，而它在 `SymbolicEntry.lean`
   ——`check_verdict_freshness` 判为 **NEW STALE**；
3. `repair_chain` 是转发 ⇒ 别名普查报 NEW forward（已按「有意转发」登记）。
### 3.14 **第 1049 轮（规划 P1-b）：自举装载规格——重复装载**观察保持**

**背景测量：`loadAll` / `LoaderState` / `Manifest` 在整个仓库里**0 个定义**（文档自己承认），
故规划 §6.1 的自举是**真正的空白**，不是「已做待整理」。**

**文件：`Lattice/CInterface/Bootstrap.lean`。三个建模判断都写进了文件头，理由如下：**

| 判断 | 理由 |
|:--|:--|
| **必须有 `LoaderState`** | 「重复装载」只有在**状态**里才能定义；若 `loadAll : List → List`，「重复」无从表述——这正是原规格 `loadAll (loadAll ms)` 写错的根源 |
| **重复判定用**名字**，不用结构相等** | 同名不同版在真实装载器里是同一个条目，故 `insertManifest` 用 `x.name = m.name`；**这使「已在表中」与「同名已在表中」成为两个不同条件**，文件把它们分开陈述 |
| **观察只含 `loaded`，不含 `rounds`** | 规划要求「定义『同一观察』包含哪些状态；不是全部内部状态相等」；把 `rounds` 放进结构、排除在观察外，使这个差别**可见** |

**⇒ 四条定理：**

```lean
insertManifest_noop_of_mem      m ∈ loaded → insertManifest m s = s      （状态全等）
insertManifest_new_changes      名字皆不同 → observe 变成 m :: loaded
loadAll_reify_idempotent        observe (loadAll s (reifyLoader s)) = observe s   ← 规格
load_changes_observe_of_new     装载**新**清单确实改变观察              ← 使「保持」非空
```

**⇒ 第三条是原规格的**正确形式**：结论只能是**观察**相等，不是状态相等；
第四条与之配对，界定「保持」只在重复时成立。**

**⇒ 明确不做：**「实际执行对应」（真实 C 加载器与规格的关系、失败与部分成功如何呈现）
**不在本文件**——它需要 CIC 内核的 C 实现，而规划 §6.1 把它列为**独立交付物**。**
**⇒ 本文件只交付前两项，并把第三项**显式留空**，而不是用一条形式化的 `allok : Bool` 假装它已被覆盖。**

**⇒ 三处我造成的错误：`List.exists_mem_of_mem` 不存在（改用 `any_eq_true` 的直接见证）、
`any_eq_false` 期望 `≠ true` 而非 `= false`、以及把判据误当清单相等（`x.name = m.name` 与 `x = m` 不同）。**
### 3.15 **第 1050 轮（规划 P1-b 的可做部分）：「可复现」档的真实边界**

**规划 §6.3 的第四档是「可复现：在干净环境中复核依赖、构建、示例与证明」。
完整冷构建在本机**不可行**（需要重建 mathlib）。⇒ 本轮把**可检查的那一半**钉住，并写明边界。**

**⇒ 新工具 `gov/audit_reproducible_numbers.py`：对每个「文档声称的数字」，判定其**生产者**
只读**被跟踪的源文件**，还是读 `.lake/` 下的构建产物（而产物**不在仓库里**）。**

**分类必须先区分「读」与「跳过」：**`gov/` 下几乎每个工具都提到 `.lake`，因为标准遍历是
`dirs[:] = [d for d in dirs if d != ".lake"]`——那是**跳过**。把提及当依赖会把整棵树误判为产物依赖。**

**⇒ 实测结果（`--check` 全部自洽）：**

| 指标 | 生产者 | 判定 |
|:--|:--|:--|
| 模块数 / 声明数 / 定理+引理数 | `audit_counts.py` | **源派生**（4 处跳过、0 处读取） |
| 承重审计 | `check_coverage_claim.py` | **源派生**（1 跳过、0 读） |
| 否证数 | `check_refutation_census.py` | **源派生**（0 提及） |
| 检查/门禁/报告器数 | `verify_all.py` | **源派生** |
| 目标载体 / 死代码 | `gen_objective_map.py` | **源派生** |
| 插件虚槽 | `audit_plugin_slots.py` | **源派生** |
| **olean 存在性（gate I7）** | `check_olean_presence.py` | **产物依赖**（真读 `.lake/build/lib/Lattice`） |

**⇒ 于是「可复现」档有了**可检查的边界**：8 个头条数字在**仅 `git archive` 的环境里可复算**；
olean 存在性不行，而它恰好是唯一一个**本来就该**关于产物的检查。**

**⇒ 门禁：`--check` 在「声称 source 但代码读产物」或「声称 artifact 但代码不读」时失败——
即我这条分类**自己也会过期**，过期就会被抓住。已接入 `verify_all`（124 → **126** 项，门禁 103 → **105**）。**
### 3.16 **第 1051 轮（规划 P2）：能力选择规则——「选哪一族」被地板逼出来，而不是偏好**

**文件：`Lattice/Lib/Compiler/Capability.lean`。规划 §1.6 要求「能力选择必须有规则：
在给定目标与精度下，应当选可越过地板的族。该判据不是能力上限」。**

**⇒ 两条定理，第一条是**排除**、第二条是**可达**：**

```lean
theorem affine_target_cannot_meet (hε : ε < 1/8) :
    ¬ (∀ x ∈ [0,1], ∃ v, (产物 .affine a b).evalAt x = some v ∧ |x² − v| ≤ ε)

theorem grid_target_meets_of_budget (hbudget : 1/(4ε) ≤ n²) :
    ∃ v, (产物 .squareApprox r.n r.hn).evalAt x = some v ∧ |x² − v| ≤ ε
```

**⇒ 合起来（`capability_rule`）：`ε < 1/8` 时仿射族**被排除**，而预算满足时离散化族**可达**。
**⇒ 其中 `1/8` 不是本轮给的，是 `LowerBound.target_not_attainable` 早就算出的；
本轮做的只是把它**接到产物层**（经 `evalAt_ofSegments` 一次往返）。**

**⇒ 为什么这算「复用契约」（规划 P2 的验收）：本文件**没有**修改
`Target`（未加构造子）、`EvaluatedArtifact`（未加字段）、`evalAt`（未改定义）、`writeBack`、`official_chain_recipe`。
新增的只有**关于已有构造子的判定定理**。于是「第二个族」不是平行实现，而是同一 `Target` 里的另一格。**

**⇒ 明确不声称：「离散化族是唯一可行的」。**那会是一个未被证明、也不该假定的断言
（未来的非线性族可能更好）。文件把这句话写在定理注释里，而不是留给读者猜。**

**⇒ 两处机械性后果，都按流程处理：**
- `affine_target_cannot_meet` 是 `¬` 定理 ⇒ 否证普查 `362 → 363`（`Lib` 250 → 251）、`USAGE.md` 同步；
- `no_uniform_linear_approximation` 因被本轮消费而**首次成为承重**，已登记 verdict。
### 3.17 **第 1053 轮（规划 §3.1 A.5）：编译器**真正用上**一般族，且新族**继承**既有界**

**第 1052 轮把 `Target` 推广成「一个族」，但只证了它在仿射上退化与产物层逐点精确。
⇒ 一个族要真的可用，还缺两条，本轮补齐：**

**文件：`Lattice/Lib/Compiler/InterpAlgebra.lean`（4 条定理）**

| 定理 | 内容 |
|:--|:--|
| `endpoints_ne` | `n > 0` 时 `k/n ≠ (k+1)/n`（所有弦引理的共同前提，单独立名免重复 `field_simp`） |
| **`chordOf_add`** | **弦是可加的**：`chordOf (f+g) a b` 的两分量等于两支弦分量之和 ⇒ **误差预算可拆** |
| **`interpFamily_add`** | 插值族可加，逐点等于 `gridAdd`——与既有 `gridEval_add` 配对 |
| **`interpFamily_sq`** | **`x²` 的插值族**就是** `piecewiseIRWeights` 解码出的族** |
| **`interpFamily_sq_error`** | **该族满足 `\|x² − gridEval\| ≤ 1/(4n²)`——与既有 `irWeights_error_bound` 逐字相同** |

**⇒ 第四条是关键：它证明「推广没有变弱」不是承诺，而是**一条等式 + 一次引用**。
新族在最重要的特例上**正好同一条界**。**

**⇒ 编译器侧的改动（`SymbolicEntry.lean`）：**

```lean
| .add (.mul (.var 0) (.var 0)) e =>      -- 二次项独立成支
    match compileTarget r e with
    | some (.affine p q) => some (.interp (fun x => x * x + (p * x + q)))
    | _ => none
```

**⇒ 加上 `quadTerm p q := x·x + (p·x + q)`、`evalSym_quadTerm`、`compileTarget_quadTerm`。
⇒ 在此之前 `interp` **只能被手工构造**；现在编译器对二次项**确实产出它**。**

**⇒ 明确尚未做：二次项的**整域误差界**（`|x²+p·x+q − 插值| ≤ …`）。
路线有两条：(a) 对 `deriv^[2]` 实例化 `chord_error_of_second_deriv_bound`（需算导数）；
(b) 用 `interpFamily_add` + `gridEval_add` + `pow_two` 把误差拆成「x² 部分 + 仿射部分（零）」。
**（b）更短且已有一半零件**，但本轮**未做**，故不作声称。**
### 3.18 **第 1054 轮（规划 §3.1 A.5）：从「一个样例」到「一类」——二次项的整域界**

**规划 A.5 的原话是「对具有二阶导上界的函数族，复用弦误差引理」。
本轮走**最短路线**完成这一步：不实例化 `chord_error_of_second_deriv_bound` 的可微假设（那要算导数），
而是用**可加性 + 既有 `x²` 界**。**

**两条新定理：**

```lean
interpFamily_quad_error (0 < n) (x ∈ [0,1]) :
    |(x·x + (p·x+q)) − gridEval (interpFamily n (fun y => y·y + (p·y+q))) n x| ≤ (1/n)²/4

quad_artifact_bound :
    ∃ v, 产物.evalAt x = some v ∧ |(x·x + (p·x+q)) − v| ≤ (1/n)²/4
```

**⇒ 装配是三步**引用**，没有一步是新的分析：**
1. `interpFamily_add`——把二次项拆成「`x·x` 部分」与「仿射部分」；
2. `interpFamily_affine` + `gridEval_affineFamily`——**仿射部分插值精确，误差为零**；
3. `interpFamily_sq_error`——剩下那支的界。

**⇒ 于是总误差**正好退化**为 `x²` 的界；这**不是**「至多两项误差之和」那种弱说法，因为仿射项贡献为零。**

**⇒ 第二条是可用形式：它落在产物的 `evalAt` 上，消费者不必自己重建「是哪个族的网格求值」。**

**⇒ 两处 `x·x` 与 `x^2` 的对齐**（`pow_two` 用了两次：一次改函数参数，一次改左侧标量）。
第一次尝试失败正是因为**只改了函数位置**——编译器的类型不符直接指出了这点。**

**⇒ 一处 import 遗漏**：`affineFamily` / `gridEval_affineFamily` 在 `Samples` 命名空间，`InterpAlgebra` 未 `open`。**
### 3.19 **第 1056 轮：把前三轮的共同结构提出来——弦是**线性泛函**

**第 1053、1054、1055 三轮证的是同一件事的三个实例（`x²`、`x·x+仿射`、`a·x·x+仿射`），
每次都重做装配。⇒ 本文件（`Lattice/Lib/Compiler/LinearComb.lean`）把它提一次。**

| 定理 | 内容 |
|:--|:--|
| `segSum` / `segSum_eval` | 有限个分段之和，且**求和与求值交换** |
| `linComb s c b` | `x ↦ ∑ c i · b i x` |
| **`chordSlope_linComb`** | 弦的**斜率**对线性组合是线性的 |
| **`chordOf_linComb`** | 弦本身由各支弦**加权求和**给出（分段级） |

**⇒ 收益：新增一族不再需要自己的装配——给出基函数与各自界，组合的弦就已经算好，误差预算按系数加权即得。
⇒ 前三轮由「先例」变成「实例」。**

**⇒ 两处证明细节值得记：**
1. **`Finset.sum_div` 的模式是**右手**形式**，故在左端为商的目标上 `rw` 不触发；
   改用 `div_eq_mul_inv` + `Finset.sum_mul` 把逆元推进求和内，再逐项 `ring`。
2. **`Segment.ext` 在本树里不存在**；组件式证明走**结构 eta**（`⟨x.m, x.c⟩ = x`）加两个具名分量事实。

**⇒ 明确未做（故不声称）：加权误差界的推论——**
```
(∀ i ∈ s, ∀ x ∈ [a,b], |b i x − (chordOf (b i) a b).eval x| ≤ B i)
  ⟹ ∀ x ∈ [a,b], |linComb s c b x − (chordOf (linComb s c b) a b).eval x| ≤ ∑ |c i| · B i
```
**所需的代数已全在本文件；剩下的一步是对和式用三角不等式。⇒ 这是下一轮最直接的活。**

**⇒ 而 `|c i|` 而非 `c i` 的理由与第 1055 轮的 `|a|` 相同：误差非负、系数可负，
写成 `∑ c i · B i` 对某些系数**是假命题**。**

**⇒ 本轮我的编辑脚本被自身断言拦下**四次**（缩进锚点、`Segment.ext` 不存在、`sum_div` 方向、
替换后残留 5 行），最终改为**行索引 + 边界断言**。
⇒ 这是本会话反复出现的同一模式：**先断言、再写入**；没有一次留下半改文件。**
### 3.20 **第 1057 轮：加权误差界落地，并**重推出**旧界（复用的判据）**

**两条定理，第二条是第一轮的**检验**：**

```lean
theorem linComb_error {ι} (s : Finset ι) (c : ι → ℝ) (b : ι → ℝ → ℝ) (B : ι → ℝ)
    (h : a ≠ bnd)
    (hB : ∀ i ∈ s, ∀ x ∈ [a,b], |b i x − (chordOf (b i) a b).eval x| ≤ B i) :
    ∀ x ∈ [a,b], |linComb s c b x − (chordOf (linComb s c b) a b).eval x| ≤ ∑ i ∈ s, |c i| · B i
```

**⇒ 装配三步，全部是引用：`chordOf_linComb`（弦→加权和）、`segSum_eval`（求值→和式）、
三角不等式 + `abs_mul` + 逐项放缩。**

```lean
theorem sq_chord_error_via_linComb (u v : ℝ) (huv : u < v) (x ∈ [u,v]) :
    |(t ↦ t·t) x − (chordOf (t ↦ t·t) u v).eval x| ≤ (v−u)²/4
```

**⇒ 第二条**没有**用 `sq_chord_error_eq_tent` 之类的直接证法，而是把 `x²` 当作「单支线性组合」
（`Unit` 索引、系数 1、`B = (v−u)²/4`）喂给 `linComb_error`。⇒ 结论与既有
`chord_error_sq_rederived` **逐字相同**。**

**⇒ 这就是「可复用」与「另写一条」的分野：前者能**重推出**旧结果，后者只是并列陈述。
⇒ 我把这条检验单独命名，而不是把新定理直接说成「更一般」——**检验本身必须是可引用的**。**

**⇒ 一处工程教训（第三次同类）：**`Fin 2` 索引 + `if i = 0` 的写法在 `simp` 下的形状很难控制；
改用**单元素**（`Unit`）索引后，`simp [linComb, c, b]` 一次闭合。**⇒ 若一个证明要靠猜 `simp` 的
归一化形状，那是因为陈述的形状选错了。**
### 3.21 **第 1058 轮：分段界 → 整域界的桥（「一族一装」的入口）**

**前两轮的界都在**单区间**层面（`linComb_error`、弦引理），而产物走 `gridEval`——按 `segmentIndex` **选一段**。
⇒ 两层之间缺一条桥，本轮补上。文件：`Lattice/Lib/Compiler/GridBound.lean`。**

```lean
segmentIndex_bounds (0 < n) (0 ≤ x) :
    x ∈ Icc (segmentIndex n x / n) ((segmentIndex n x + 1) / n)

gridEval_bound_of_segmentwise (0 < n)
    (hseg : ∀ k < n, ∀ y ∈ [k/n, (k+1)/n], |f y − (g k).eval y| ≤ B)
    (x ∈ Ico 0 1) : |f x − gridEval g n x| ≤ B
```

**⇒ 域取 `Ico 0 1` 而不是 `Icc 0 1` 是**有意的**：`x = 1` 时 `segmentIndex n 1 = n`，
而**第 `n` 段不存在**。把这个界写进陈述，而不是在证明里偷偷假设 `x < 1`。**

**⇒ 复用验证（本轮要点）：**

```lean
sq_gridEval_error_via_segmentwise (x ∈ Ico 0 1) :
    |x·x − gridEval (interpFamily n (t ↦ t·t)) n x| ≤ (1/n)²/4
```

**它**经桥**证明：逐段的界来自既有 `chord_error_sq_rederived`，再做幅度归一化 `(k+1)/n − k/n = 1/n`。
结论与既有 `interpFamily_sq_error` **逐字相同**，但**路径不同**——这正是它的证据价值。**

**⇒ `chord_error_sq_rederived` 因此**首次成为承重**（现在是逐段输入），已登记 verdict。**

**⇒ 三处小错：`le_div_iff` 而非 `lt` 版（目标上端是 `≤`）；`gridEval` 需 `GridAlgebra` 的 `open`；
`apply` 把域假设留成**第二个目标**（`case hx`）。**
### 3.22 **第 1059 轮：二次项走一遍新入口，重推出的仍是那个数**

**两条定理（`Lattice/Lib/Compiler/GridBound.lean`）：**

```lean
-- 任意区间上的弦误差：两支线性组合 + linComb_error
quadFun_chord_error_on_interval (u < v) (y ∈ [u,v]) :
    |quadFun y − (chordOf (quadFun) u v).eval y| ≤ |a| · (v−u)²/4

-- 整域界：桥 + 上一条
quadFun_gridEval_error_via_bridge (x ∈ Ico 0 1) :
    |quadFun x − gridEval (interpFamily n (quadFun)) n x| ≤ |a| · (1/n)²/4
```

**⇒ 第二条的界与第 1055 轮 `interpFamily_quadFun_error` **逐字相同**，但**路径完全不同**：
旧条走「`interpFamily` 的可加 + 数乘」在**族层**装配；本条走「两支 `linComb` → 单区间界 → 桥」。
**⇒ 两种路径给出同一个数，那就不是巧合，而是**这个数是对的**。**这正是「复用入口」要提供的保证。****

**⇒ 索引机制的教训（第二次同类，这次选对了）：上一轮用 `Fin 2` + `if i = 0` 卡在 `simp` 形状上；
本轮改用 `Finset ℕ` 的 `{0, 1}` + `Finset.sum_pair`，`simp only [...]` 后 `ring` 一次闭合。
⇒ 结论：**`Finset` 具体元素比 `Fin` 索引更稳**，因为 `sum_pair` 是结构化引理而不是「形状知识」。**

**⇒ 两处 `if`/lambda 的坑：`simp only` 必须显式给 `if_true`/`if_neg`；`rw` 不会 beta 归约 lambda，
需先 `change`。⇒ 两者都是「`rw` 只做语法替换」的同一件事。**

**⇒ `linComb_error` 因此成为承重，verdict 已登记（承重 1090，100% 已审）。**
### 3.23 **第 1060 轮：第三个族（三次）——**成本检查**：「新增一族只写一条单区间界」**

**第 1059 轮只是对**已有**族做二次验证。本轮用同一个入口加**真正的新族**，并结算成本。**

**文件 `Lattice/Lib/Compiler/CubicFamily.lean`：**

```lean
cube_sub_chord (a ≠ b) : x³ − chord(x) = (x − a)(x − b)(x + a + b)
tent_le                : |(x − a)(b − x)| ≤ (b − a)²/4
cube_chord_error       : (0 ≤ a < b, x ∈ [a,b]) |x³ − chord| ≤ 3b(b−a)²/4
cube_uniform_bound     : ∀ x ∈ Ico 0 1, |x³ − gridEval (interpFamily n (t ↦ t³)) n x| ≤ 3·(1/n)²/4
```

**⇒ 为什么**不需要分析**：三次函数的「函数减弦」是三次多项式且在两端为零 ⇒ **可分解**。
最后一个因子由 `x²` 项系数定出：右侧是 `−(a+b+r)`，左侧是 `0`，故 `r = −(a+b)`。
⇒ 有了分解式，界只剩**两个初等乘积估计**（尖顶估计 + `x+a+b ≤ 3b`）——**无导数、无凸性、无中值定理**。

**⇒ 成本结算（本轮要点）：整域界只用了**一条引用链**——新的 `cube_chord_error` + 第 1058 轮的桥。
其余一行未写。⇒ 这就是「入口对**先前不存在的族**也确实按宣称的方式工作」。**

**⇒ 符号侧：`cubeTerm := x·x·x`、`evalSym_cubeTerm`、`compileTarget_cubeTerm`（新规则放在通配分支之前）。**

**⇒ 四处小错：**
1. 我的 `| _ => none` 锚点**子串匹配**到了内层分支（缩进有别，锚点需带前导换行）；
2. **`abs_neg` 在负号位于乘积内部时不触发** ⇒ 需显式 `abs_mul` 拆开；
3. **`simp only` 留下嵌套 `if`/`Option.bind` 未化约** ⇒ 先算到 `some (x·x·x)`，再用 `ring` 与 `x³` 对齐；
4. **`apply` 又把域假设留成第二个目标**（第二次遇到，已是可预测的）。
### 3.24 **第 1061 轮：去掉半开限制——右端点插值是**精确**的**

**桥（第 1058 轮）只能写 `Ico 0 1`，因为 `x = 1` 时段号是 `n`（`segmentIndex_at_one`），
第 `n` 段在「逐段」假设之外。⇒ 这使得新入口**无法与既有定理相遇**——后者全写在 `Icc 0 1` 上，
域不一致会让两条路**永久分开**。**

**⇒ 修法是一个**事实**，不是权宜：**

```lean
interpFamily_eval_at_one (0 < n) : gridEval (interpFamily n f) n 1 = f 1
```

**⇒ 因为第 `n` 段是 `[n/n, (n+1)/n]` 上的弦，而 `n/n = 1`，故 `chordOf_eval_left` 直接给出 `f 1`。
⇒ 于是**半开域从来不是插值的限制**，只是段号落点的一个假象。**

```lean
gridEval_bound_of_segmentwise_Icc : 逐段界 + 边界点界 ⟹ 闭区间 [0,1] 上的界
```

**⇒ 对插值族，`hone` 由精确性定理**自动**消掉（变成 `0 ≤ B`）。**

**⇒ 已应用：`cube_uniform_bound` 现在写 `Icc 0 1`，与 `interpFamily_sq_error`、
`interpFamily_quadFun_error` **同域**。逐段论证抽成 `cube_segmentwise`，两个域版本共用。**

**⇒ 两个流程教训：**
1. **同一个 JSON 错误犯了两次**（字符串内裸换行）。两次都是**响亮失败**（`Invalid escape`）
   而不是静默跳过某行——这正是它被抓住的原因。⇒ **新规则：verdict 字符串一律单行。**
2. **`PROOF-DEBT.md` 必须在 verdict 落地**之后**再生成**，否则文档表会比测量**晚一个 verdict**。
### 3.25 **第 1062 轮：能力表——每个族压成一行，而**每个字段都是证明****

**此前三个族的能力散在三个文件、三个定理名、三种域、三种常数写法。⇒ **散落的清单只能被读，不能被引用。**
⇒ 规划 §5.2 要「手工列出配方」，§1.6 要「能力选择必须有规则」。**文件：`Lattice/Lib/Compiler/CapabilityTable.lean`**

```lean
structure CapabilityRow where
  degree, term, fn, target
  semantics  : ∀ x, evalSym x term = some (fn x)
  compiled   : ∀ r, compileTarget r term = some target
  family_eq  : ∀ r k, Target.family r target k = interpFamily r.n fn k
  constant
  bound      : ∀ n > 0, ∀ x ∈ Icc 0 1, |fn x − gridEval (interpFamily n fn) n x| ≤ constant · (1/n)²
```

| 行 | degree | 常数 | 到达方式 |
|:--|:--|:--|:--|
| `squareRow` | 2 | **1/4** | `.squareApprox`（专用离散化） |
| `cubeRow` | 3 | **3/4** | `.interp (t ↦ t³)`（一般插值） |

**⇒ 为什么一行里要带 `target` 而不只是 `fn`：两个族**到达方式不同**。若只记 `fn`，
就丢掉「编译器是怎么到达的」；而 `family_eq` 正是把**到达的目标**与 `fn` 的插值族**接起来**的那一步。
⇒ 对 `squareRow`，该字段**不是 `rfl`**：它需要第 1056 轮的 `interpFamily_sq` 说两族一致。**

**⇒ 三条顶层定理：**
- **`row_gives_bound`**：一行**就是**它的界 ⇒ **能力可以传参、可以遍历、可以逐行引用**；
- **`table_has_two_rows`**：度数 2 与 3，常数 1/4 与 3/4；
- **`cube_constant_exceeds_square`**：**`1/4 < 3/4`**。

**⇒ 第三条刻意写成定理而不是注释：「同一 `n` 下三次比二次更粗」是**两个有理数的比较**，
现在它是**可引用的事实**。**

**⇒ 三处小修：`decodeGrid`/`interpFamily_sq` 需两个 `open`；`(fun t => t^2) x` 需 beta 归约（`show`/`ring` 能做，`rw` 不能）；
界要**写成既有定理的形状**——`(1/n)²/4` 与 `1/4·(1/n)²` 相等但不同形，用 `ring` 对齐而非混为一谈。**

**⇒ `row_gives_bound` 是转发（重新暴露本行的字段），已按「有意转发」登记。**
### 3.26 **第 1063 轮：参数化仿射行——常数 0，**精确而非近似****

**表原有两行都是**无参常数**。加入仿射族是表结构的第一次真实压力测试，结果：结构够用。**
**文件：`Lattice/Lib/Compiler/CapabilityTable.lean`**

```lean
affineRow (a b : ℝ) : CapabilityRow
  degree 1, term affineTerm a b, fn (t ↦ a·t + b), target .affine a b, constant 0
```

**⇒ 这一行最容易被忽略：它是**唯一**一档「族是精确的」。表里的常数 0 **不是缺失数据，而是最强的声明**。
⇒ `bound` 字段仍然成立（`|fn − 插值| ≤ 0·(1/n)²`），而 `affineRow_exact` 把它加强为**等式**——
去掉绝对值与不等号。**

**⇒ `family_eq` 这一行也**不是 `rfl`**，理由与二次行不同：目标族是**常族** `affineFamily a b`，
而右侧是同一仿射函数的**插值族**；`interpFamily_affine` 正是「两者重合」这句话。**

**⇒ 两条顶层定理：**

```lean
affineRow_exact : fn x − gridEval (interpFamily n fn) n x = 0
constants_ordered (a b) : (affineRow a b).constant ≤ squareRow.constant ∧ squareRow.constant < cubeRow.constant
```

**⇒ 第二条把表中能力的**强弱顺序**变成一条可引用链：精确（0）不弱于二次（1/4），
二次在同一 `n` 下**严格**优于三次（3/4）。**
**⇒ 第一段写 `≤` 而非 `<`：它的作用只是「常数 0 是最低档」；严格性只在两个**近似**族之间才有意义。**

**⇒ 一处**我自己需要清理的东西**：`constants_ordered` 初版的注释是**自问自答的啰嗦**
（“……不，它们是不同族的常数，写 ≤ 是因为……”）。那不是论证，是论证的样子。⇒ 已换成两句真正的理由。**
### 3.27 **第 1064 轮：能力表变成**选择器**，而且选择自带证明**

**表此前能「陈述每族达到什么」，但不能**选择**。⇒ 规划 §2.1 第 4 层正是「能力与证明编排」，本轮把表变成判定过程。**

```lean
structure Request where eps : ℝ; n : ℕ; hn : 0 < n

sufficient row req := row.constant * (1/n)² ≤ req.eps      -- 表所能证明的充分条件

-- 有界性 → 整域达标本
sufficient_implies_meets : sufficient row req → ∀ x ∈ [0,1], |fn x − 插值| ≤ req.eps

-- 选择器
select req rows := rows.find? (fun row => decide (sufficient row req))
select_sound            : select req rows = some row → sufficient row req
select_gives_precision  : select req rows = some row → ∀ x ∈ [0,1], |fn x − 插值| ≤ req.eps
select_affine_first     : 0 ≤ eps → select req (affineRow a b :: tail) = some (affineRow a b)
```

**⇒ `sufficient` **不是**弱化：它就是每行 `bound` 字段**直接产出**的那个不等式，把常数提出而已。
⇒ 因此选择器诚实：它每行只比较**一个有理数**，而不重新推导界；`sufficient_implies_meets` 只有一步 `le_trans`。**

**⇒ 「首个匹配」是**刻意的**：列表顺序**就是**优先级。把精确行（常数 0）放在最前，则 `0 ≤ eps` 时它必被选中——
⇒ `select_affine_first` 使「精确优于近似」成为**可执行的规则**，而不是一句评价。**

**⇒ `select_sound` **不**声称最优：`find?` 只保证返回的行满足谓词。要说「选得最好」需要行间序关系与
「后者更差」的证明——两者都不在，故都不声称。**

**⇒ 两个 Lean 细节：实数比较的 `Decidable` 需 `classical`；`List.find?_some` 必须**显式给谓词**
`(p := …)`，否则 `@decide` 的实例是元变量、合一挑错。**

**⇒ `select_gives_precision` 是转发（两条定理的复合），已登记。**
### 3.28 **第 1065 轮：选择器的**真缺陷**——只比较常数，不检查「行是否适用于该目标」**

**缺陷是这样暴露的：问一句「它在**不该选**的目标上会怎么选」。**

**⇒ 此前 `Request` 只有 `eps` 与 `n`，`sufficient` 只比较 `row.constant * (1/n)² ≤ eps`。
⇒ 于是 `affineRow a b`（常数 0）对**任何** `eps ≥ 0` 都「充分」——**包括目标 `x²`**。
⇒ 选择器会把一个关于 `a·t+b` 的行交给一个关于 `t²` 的问题。**那不是优先级，那是错答。****

**⇒ 修正：请求必须指明目标，行必须匹配它。**
```lean
structure Request where goal : ℝ → ℝ; eps; n; hn
applicable row req := row.fn = req.goal
sufficient row req := applicable row req ∧ row.constant * (1/n)² ≤ req.eps
```
**⇒ `sufficient_implies_meets` 现在结论说的是 `req.goal`（不是 `row.fn`），故它**不可能**被用来对该行并不表示的目标作任何声称。**

**⇒ 两种行为现在都**被证明**（这才是关键）：**
```lean
affine_not_sufficient_for_square : goal = t² → ¬ sufficient (affineRow a b) req
select_square_row                : goal = t², 1/4·(1/n)² ≤ eps → select [affine, square] = some square
select_affine_first              : goal = a·t+b, 0 ≤ eps       → select [affine, …] = some affine
```
**⇒ 同一个选择器，在二次目标下**跳过**仿射行，在仿射目标下**选中**它。
⇒ 这个对照才使「选择正确」成立，而不只是「类型正确」。**

**⇒ `affine_fn_ne_square` 是三点论证：过 `(0,b)`、`(1,1)`、`(2,4)` 的直线会同时要求 `b=0`、`a=1`、`2a+b=4`。**

**⇒ 三个 Lean 细节：`rw` 无法在 `(fun t => a*t+b) 0` 内部改写（已被 beta 归约）⇒ 用 `congrFun h 0` + `simpa`；
`List.find?_cons_of_neg` 要的是 `≠ true` 而非 `= false` ⇒ `simpa` 转换；
两处适用性目标需要最后一步 `rfl`——`show` 后 `rw` 不会自动关闭结构投影的定义性相等。**

**⇒ 一处流程漏检：本轮我在门禁清单里**漏了 `check_refutation_census.py`**，于是新否证定理（364 条）在
`verify_all` 才被抓到。⇒ **新的否证定理会改变普查，故该检查必须留在清单里。**
### 3.29 **第 1066 轮（第三次表结构压力测试）：一行覆盖一**族**，仿射族变成**无参行****

**⇒ 这次**确实需要重构**，正如上一轮预判。**

**缺陷：第 1065 轮用 `applicable := row.fn = req.goal` 修好选择器，但那是**函数等式**——
极强也极窄，只能匹配**恰好那一个**函数。而规划 §1.6 要的是按**族**声明能力。**

**⇒ 重构：一行同时带**符号代表项**与**它覆盖的族**：**

```lean
covers        : (ℝ → ℝ) → Prop
covers_self   : covers fn                  -- 代表项属于自己覆盖的族
covers_bound  : ∀ g, covers g → 界对 g 成立   -- 不是只对 fn
```

| 行 | `covers` |
|:--|:--|
| `squareRow` / `cubeRow` | `g = 那一个函数`（单元素族） |
| `affineRow a b` | `g = fun t => a·t+b`（仍带参） |
| **`affineFamilyRow`** | **`∃ c d, g = fun t => c·t+d`（所有仿射函数，**无参**）** |

**⇒ 为什么代表项与族**两者都要**：`semantics`/`compiled`/`family_eq` 描述的是**符号路径**（哪个项到达哪个目标），
而 `covers`/`covers_bound` 描述的是**族的范围**。两者互不包含——`affineFamilyRow` 的代表项取 `affineTerm 0 0`，
正因为它的符号路径**不是**它在族层面所声称的东西。**

**⇒ 一个新的否证结果，只有族表述才让它有意义：**

```lean
square_not_affine : ¬ ∃ c d, (fun t => t²) = fun t => c·t+d
```

**⇒ 于是 `affineFamily_not_sufficient_for_square`：**族行也会拒绝二次目标**——
而拒绝的理由是「`t²` 不是仿射函数」，**不是**「这一行碰巧写了另一个函数」。
⇒ 这就是**正确的拒绝**与**偶然的拒绝**的差别。**

**⇒ 三种选中行为齐备：**
```lean
select_affineFamily_row : 目标仿射, 0 ≤ eps → 选中族行
select_affine_first     : 目标 a·t+b, 0 ≤ eps → 选中具体行
select_square_row       : 目标 t², 1/4·(1/n)² ≤ eps → 选中二次行
```

**⇒ 三处错误：`write` 工具把我写的 `\uXXXX` 转义**原样**写进 Lean 文件（编译器报 576 次 `unexpected token '\'`），
一次解码全部修好；两处证明方向错——`covers` 现在展开为 `req.goal = …` 而非 `row.fn = req.goal`，
故 `hgoal` 与覆盖假设的合成顺序要反过来。</**

**⇒ 另一处：重构删掉了 `row_gives_bound`，其别名基线条目随即变成**STALE**。
⇒ 我选择**删除条目**而不是恢复该定理：消费路径现在是 `sufficient_implies_meets` + `select_gives_precision`，
它们在族表述下覆盖同一用途。**

**⇒ 否证普查 `364 → 365`（`Lib` 252 → 253）。**
### 3.30 **第 1067 轮：否定路径——`none` 现在带**理由**，且地板与归属被**明确区分****

**`select` 此前只能给「一行」或 `none`，而 `none` **不携带任何信息**。规划 §2.1 要求失败有原因，故本轮补否定方向。**

```lean
affine_family_row_never_sufficient_for_square :
    目标 = t² → 任何**族限于仿射**的行都不充分 —— 对**任意** eps
select_none_of_affine_table :
    目标 = t²，表里每行都仿射 → select req rows = none
```

**⇒ 本轮存在的意义就是这条区分：`LowerBound.no_uniform_linear_approximation`（`1/8` 地板）说的是**逼近**：
`eps < 1/8` 时没有仿射函数能一致地 `eps`-逼近 `x²`。而本框架的 `covers` 要求的是**恰好属于该族**。
⇒ **故这里的拒绝**不**靠地板，而靠更强的事实：「`x²` 根本不是仿射函数」（`square_not_affine`，三点论证）。**
⇒ **把两者混为一谈会得出一个**看起来对、推理却错**的证明——所以文件头明写区别，而不是让读者去假定地板起了作用。**

**⇒ `select_none_of_affine_table` 用 `List.find?_eq_none` + 逐行否定 ⇒ **`none` 是由理由**推出**的，不是作为「缺失」被观察到的。**

**⇒ 又一个 Lean 形状不对称（第 1065 轮那次同型）：`List.find?_eq_none` 留下的目标是 `\u2260 true`，
而 `decide_eq_false` 产生的是 `= false` ⇒ 需要 `simpa` 转换，而不是 `apply`。**

**⇒ 两处编辑事故（都是机械的、都由编译器抓到而非靠阅读）：**
1. 我又用了 raw Python 字符串，`\uXXXX` **字面**进了 Lean 文件；
2. 我插入的 `/-!` 段注释**没有闭合** ⇒ `unterminated comment`。

**⇒ 否证普查 `365 \u2192 366`（`Lib` 253 \u2192 254）。**
### 3.31 **第 1068 轮：表变成**按度数索引**，于是选择是**阶梯**而不是查找**

**`CapabilityTable.select` 只在一个固定列表里查。规划 §2.1 第 4 层要「能力与证明编排」，
而编排的前提是能力**可(indexed by a parameter)**，从而「先试小的，再试大的」可以表达。**
**文件：`Lattice/Lib/Compiler/PolyTable.lean`**

```lean
polyRow : ℕ → Option CapabilityRow
  | 1 => some affineFamilyRow   | 2 => some squareRow   | 3 => some cubeRow   | _ => none

polyRow_one / _two / _three / _zero / _four      -- 皆为 rfl：表就是它定义的样子
polyRow_none_iff (d) : polyRow d = none ↔ d = 0 ∨ 4 ≤ d

selectByDegree req := select req [affineFamilyRow, squareRow, cubeRow]
```

**⇒ 为什么返回 `Option` 而不是一行：库**并不覆盖所有度数**。`Option` 把「未覆盖」放进**类型**里，
而不是留给调用者去猜；而 `polyRow_none_iff` **证明**了未覆盖的恰好是 `0` 与 `≥ 4`。**
**⇒ 因此 `polyRow_four` 是一条**如实的边界**：不是「四次不可能」，而是「本库没有它的界」——
这也正是「将来加一族只需在此函数加一支、其余不动」的理由。**

**⇒ 阶梯需要它的**拒绝**，故新增三条否证事实（皆为三点论证）：**
```lean
cube_not_affine : t³ 不是仿射（0,1,2 → 0,1,8 推出 b=0, a=1, 2a+b=8）
square_ne_cube  : t² ≠ t³（在 t = 2 处不同）
square_not_cube_row / cube_not_square_row / affineFamily_not_sufficient_for_cube
```
**⇒ 没有它们，「按度数递增尝试」就只是一次**没有理由的扫描**。**

**⇒ 两处机械修正：**
1. `CapabilityRow` 含函数与 `Prop`，**无 `DecidableEq`** ⇒ `polyRow_none_iff` 里 `by decide` 的那些分支
   改为用 rfl 引理重写；
2. `polyRow` 的通配分支需要**登记理由**——它的理由是「库不覆盖该度数」，而这个范围由
   `polyRow_none_iff` **证明**，不是要求读者假定。

**⇒ 两处基线被**裁定**而非绕开：定义式证明基线 810 → **815**（五条表等式）。
⇒ 这里 `rfl` 是**正确**的而非空洞的：**表的条目定义上就是它写的那个东西**。
⇒ 通配分支登记与否证普查（`366 → 369`，`Lib` 254 → 257）同样处理。**
### 3.32 **第 1069 轮：度数上界成为**参数**——选择是生成的，不是手写的**

**上一轮的 `selectByDegree` 仍硬写三元列表，**从未咨询 `polyRow`**。本轮让生成器成为唯一真相源。**

```lean
noncomputable def degreeList : ℕ → List CapabilityRow
  | 0 => []
  | (n+1) => degreeList n ++ (polyRow n).toList

degreeList_one  : degreeList 1 = []                     -- 只覆盖度数 0，而 polyRow 0 = none
degreeList_two  : degreeList 2 = [affineFamilyRow]
degreeList_four : degreeList 4 = [affineFamilyRow, squareRow, cubeRow]

selectUpTo req dmax := select req (degreeList dmax)
selectByDegree_eq_selectUpTo : selectByDegree req = selectUpTo req 4
select_nil / selectUpTo_zero : selectUpTo req 0 = none
```

**⇒ 最后一条是关键：它使硬写列表**不再**是第二个真相源。`selectByDegree` 现在**被证明**是生成器在 `dmax = 4` 处的实例，
故「表里有什么」只有**一个**定义。**

**⇒ `degreeList_one` 是**更正**，不是形式：`degreeList dmax` 覆盖 `0 .. dmax-1`，故 `dmax = 1` 得到**空表**
（度数 0 未被覆盖），仿射行只在 `dmax = 2` 出现。我第一版写的是 `degreeList 1 = [affineFamilyRow]`，
**编译器直接指出该等式为假**。⇒ 「上界差一位」正是定理会拒绝、而注释会放过的错误。**

**⇒ 为什么用递归而非 `List.range`：`List.range` 的等式不按 `rfl` 化简（本体递归定义），
而这一层需要等式能**定义性地算出来**，使三条具体列表引理都能 `simp` 一行闭合。**

**⇒ 一条**被删除的复述**：我曾为对称加入 `selectUpTo_gives_precision`，重复审计把它标了出来——
同一结论公式、转发证明、无新内容。⇒ **删除而非入基线**：只为了镜像另一条而存在的定理，是同一事实的第二个名字。**

**⇒ 定义式证明基线 815 → 816**（`degreeList_zero := rfl`，这里 `rfl` 同样正确：空表**定义上**就是空）。
### 3.33 **第 1070 轮：度数上界成为**被选中行的保证**，而不只是过滤条件**

**上一轮把 `dmax` 变成参数，但**没有任何定理说这个参数意味着什么**——`selectUpTo` 过滤了一个列表，
而调用者无法对自己拿到的行引用任何东西。三条定理补上这个缺口。**

```lean
polyRow_degree (d) (row ∈ (polyRow d).toList) : row.degree = d
degreeList_degree_lt (dmax) : ∀ row ∈ degreeList dmax, row.degree < dmax
selectUpTo_degree_bound : selectUpTo req dmax = some row → row.degree < dmax
```

**⇒ 为什么 `polyRow_degree` 要先证：对 `dmax` 的归纳把表拆成「旧表」与「度数为 `n` 的那一行」，
第二部分需要**索引与字段一致**。没有这条，界就是关于**索引**而不是关于**行**的陈述——
也就是关于调用者无法使用的某种东西。**
**⇒ 它由五个度数分支给出，每个分支用第 1068 轮的 rfl 引理重写，`≥ 4` 那支用 `polyRow_none_iff`。**

**⇒ 为什么这条界是本轮要点：`dmax` 现在是**可引用的承诺**，而不仅仅是过滤条件。
一个只愿意承担二次族的调用者传 `dmax = 3`，随后可以**引用**「任何返回行的度数 < 3」——
这就把三次族排除在**定理**层面，而不是靠调用者自己去看列表。**

**⇒ `List.mem_of_find?_eq_some` 提供成员性那一步：`select` 建立在 `find?` 上，故返回的行属于该列表，
再由 `degreeList_degree_lt` 得界。两条方向都在树里，都没有靠默认。**
### 3.34 **第 1071 轮：阶梯**落在最小可行度数**上——选择器不越级**

**第 1070 轮给了度数界，第 1059 轮给了精度，但**没有任何定理说选择器会停在第一个可用的族**。
本轮两条定理在**真实的生成表**上做到了这一点。**

```lean
select_quadratic_goal_lands_on_square :
    目标 = t², 1/4·(1/n)² ≤ eps → selectUpTo req 4 = some squareRow
select_cubic_goal_lands_on_cube :
    目标 = t³, 3/4·(1/n)² ≤ eps → selectUpTo req 4 = some cubeRow
```

**⇒ 为什么这**不是** `select_square_row` 的重述：那条用的是**两元表** `[affineRow a b, squareRow]`；
本轮用的是**真实表** `[affineFamilyRow, squareRow, cubeRow]`。**

**⇒ 因此新内容是：`find?` 在**第二个元素就停下**——对二次目标，三次行**从未被咨询**。
⇒ 「按度数递增尝试」正是「不为了不需要的族付费」这一断言，而它现在有证明而不是意图。**

**⇒ 机制是同一对引理的**不同形状**：`find?_cons_of_neg` 跳过表头（仿射族不适用于非仿射目标），
`find?_cons_of_pos` 取匹配。对三次目标，跳过发生**两次**，故那条证明是嵌套的——
而两次跳过都由**具名否定定理**给出理由（`affineFamily_not_sufficient_for_cube`、`cube_not_square_row`），
**不是靠求值一个谓词然后指望它**。**

**⇒ `affineFamily_not_sufficient_for_square` 因此**首次成为承重**（落点定理消费它来为第一次跳过给出理由），verdict 已登记。**
### 3.35 **第 1072 轮：「表**不是上限**」成为定理——四次族作见证**

**规划 §1.6 末句是「该判据**不是能力上限**」。此前它只是设计声明：我证明了**表内如何选**，
从未证明**表外也行**。本轮以 `t⁴` 为见证把它变成定理。**

**⇒ 表内：无一行覆盖 `t⁴`。**
```lean
quartic_not_affine / quartic_ne_square / quartic_ne_cube     -- 三条三点分离
quartic_not_covered (row ∈ degreeList 4) : ¬ row.covers (fun t => t⁴)
selectUpTo_none_of_quartic_goal : selectUpTo req 4 = none
```
**⇒ 注意它**不是**「我们没写四次行所以它不在表里」——那只是列表的**缺口**。
⇒ 三个分支各由一条**具名**的函数事实与 `t⁴` 分离，**故拒绝是关于族的陈述，而不是关于我写作进度的陈述**。**

**⇒ 表外：一般插值族可达它。**
```lean
quartic_sub_chord : x⁴ − chord(x) = (x−a)(x−b)(x² + (a+b)x + (a²+ab+b²))
quartic_chord_error   : ≤ 3(b−a)²/2     （0 ≤ a < b ≤ 1）
quartic_uniform_bound : ≤ 3(1/n)²/2     （x ∈ [0,1)）
```
**⇒ 分解式仍是纯代数：`f − chord` 的 `x³`、`x²` 系数为零 ⇒ `p = a+b`、`q = a²+ab+b²`。
⇒ 界仍只需尖顶估计 + 「第三因子 ≤ 6」——**无导数，与三次族同一路线**。**

**⇒ 收口定理：**
```lean
table_is_not_a_ceiling (0 < n) :
    selectUpTo (目标 := t⁴, eps := 3/(2n²)) 4 = none
    ∧ ∀ x ∈ [0,1), |t⁴ − gridEval (interpFamily n (t ↦ t⁴)) n x| ≤ 3/(2n²)
```
**⇒ 两半**都不可省**，且互不为推论：前者关于三个具体族，后者关于一个它们都不覆盖的函数的插值族。**

**⇒ 且本条**不**声称「四次不能被加入表」——**恰恰相反**：填 `polyRow 4` 只需**一支**，
而那一支的依据已经在本文件里。**

**⇒ 两处基线裁定：`cube_sub_chord` 与 `quartic_sub_chord` 结构同构，重复普查把两条都标了出来；
⇒ 按「有意并行」登记——**各是各自的代数恒等式，合并会变成一个带两个分支的引理**。
⇒ 否证普查 `369 → 370`（`Lib` 257 → 258）；`degreeList_four` 首次承重，verdict 已登记。**
### 3.36 **第 1073 轮：上限**被推高一格**——四次族进表**

**第 1072 轮证明了「表不是上限」。本轮把上限提高，这是证明上一轮那句「填 `polyRow 4` 只需一支」为真的**唯一诚实方式**。**

```lean
SymbolicEntry: quarticTerm := x·x·x·x、源语义、编译规则、compileTarget_quarticTerm
QuarticFamily: quartic_uniform_bound_Icc（闭区间，3·(1/n)²/2）、quarticRow（degree 4，常数 3/2）
PolyTable:     polyRow 4 = some quarticRow、degreeList_five、落点定理

select_quartic_goal_lands_on_quartic :
    目标 = t⁴, 3/2·(1/n)² ≤ eps → selectUpTo req 5 = some quarticRow
```

**⇒ 与上一轮的结果并读：`dmax = 4` 时四次目标得 `none`（`selectUpTo_none_of_quartic_goal`），
`dmax = 5` 时同一目标落在 `quarticRow`。⇒ **差别只在参数上，而表只长了一支**——
选择器、桥、精度保证、度数界**一行未动**。这正是能力层自 1059 轮以来一直朝向的那个断言。**

**⇒ 为此必须**打断一个依赖**：`QuarticFamily` 原先导入 `PolyTable`（「表拒绝 `t⁴`」那组用 `degreeList`），
而 `PolyTable` 现在需要 `QuarticFamily` 的 `quarticRow`。⇒ 环按真实分界解开：
`QuarticFamily` 供给**族**（界 + 行），`PolyTable` 供给**表的事实**（拒绝、落点）。
两个文件各自只依赖它真正用到的东西。**

**⇒ 两处错误值得点名：**
1. 我的解耦脚本**算出**要移动的块却**没有写回任何地方**，于是 `quarticRow` 直接消失了——
   **是下一次构建抓到的，不是靠阅读**；
2. 我为避免「结论同形」的重复而删除半开版本的界时，切除**连带**把夹在两段注释之间的三条分离定理一并切走。
   ⇒ 两处都按产生它们的同一推理恢复。**

**⇒ 基线裁定：半开版本**删除**而非入基线（Icc 蕴含 Ico，保留两者等于给同一事实两个名字）；
`quartic_not_affine`、`quartic_ne_square`、`quartic_ne_cube` 成为承重，verdict 已登记。**
### 3.37 **第 1074 轮：四档常量**严格递增**，且历史默认被证明**陈旧****

```lean
constants_strictly_increasing (a b) :
    (affineRow a b).constant < squareRow.constant
    ∧ squareRow.constant < cubeRow.constant
    ∧ cubeRow.constant < quarticRow.constant
```

**⇒ 即 `0 < 1/4 < 3/4 < 3/2`。⇒ 这是「先小后大」的**定量**依据：不同度数的族在同一 `n` 下**代价确实不同**，
且差**严格递增**。⇒ 故「先试小的」不是关于优雅的偏好，而是一条定理陈述的**代价序**。**

**⇒ 旧的三档 `constants_ordered`（`0 ≤ 1/4 < 3/4`）**被删除**而非并存——它被新链条**取代**，
若保留则几乎同一事实有两个名字。**

```lean
legacy_default_refuses_where_current_table_succeeds (目标 = t⁴, 3/2·(1/n)² ≤ eps) :
    selectByDegree req = none ∧ selectUpTo req 5 = some quarticRow
```

**⇒ `selectByDegree` 写死为 `selectUpTo req 4`——那是**表只有三行时**的默认。**
**⇒ 在四次目标上它现在返回 `none`，而显式传 `dmax = 5` 能找到 `quarticRow`。**
**⇒ 把这件事写成定理，使「默认会陈旧」成为**可引用的事实**而非评论：调用者应显式传 `dmax`，**理由是一条定理，而不是一个约定**。**

**⇒ 一次**切得过远**的删除，这次是**普查**抓到的：**
**⇒ 为删除 `constants_ordered`，我从它的注释切到命名空间末尾，**连带删掉了随其后的两条否定定理**
（`affine_family_row_never_sufficient_for_square`、`select_none_of_affine_table`）。
⇒ 构建**仍然通过**（因为无消费者），是**否证普查**发现它：`370 → 369`。⇒ 两条已恢复，普查回到 370。**

**⇒ 这是三轮内**第二次**「删一条定理」把邻居一起带走。⇒ 结论不是「要小心」，而是：
**无法精确说出邻域范围的删除，应当替换那一条定理的正文，而不是切一个区段。**
### 3.38 **第 1075 轮：能力层的输出变成**可求值的产物**，不再只是一个行**

**此前能力层的输出是一个 `CapabilityRow`——一堆证明，没有可求值的内容。而 `select_gives_precision`
直接跳到 `gridEval`，**完全跳过了产物的 `evalAt`**。本轮补上这一针。文件：`Lattice/Lib/Compiler/ArtifactStitch.lean`**

```lean
gridEval_congr : 逐点相等的族有相同的网格求值

selected_row_artifact_bound :
    由选中行的 target 造出的产物，其 evalAt 返回的每个值都满足**该行自己的**界

selected_row_artifact_meets_request (row.fn = req.goal) :
    ……若该行的代表项**就是**请求的目标，则该值满足 req.eps

square_artifact_meets_request :
    目标 = t², 1/4·(1/n)² ≤ eps
    → 由 squareRow 造出的产物在每一点满足 req.eps
```

**⇒ 一个必须**说清而不是抹平**的边界：`covers` 不一定是单元素族。**
**⇒ `affineFamilyRow` 覆盖**所有**仿射函数，而它的代表项是 `0·t+0`，故由它造出的产物求值的是 `0·t+0`——
**不是**调用者的 `c·t+d`，尽管两者都是仿射。**

**⇒ 这就是本文**证两条**而不是一条的原因：行的界**总能**转移；请求的精度**只在**代表项等于目标时转移。
⇒ 把两者并成一条，会让「族行」冒充「具体行」——而那正是第 1065 轮修掉的缺陷。**

**⇒ 而**实例才是要点**：`square_artifact_meets_request` 是规划要的端到端形状——目标、选择、产物、精度
在**一条**陈述里——且其中每一步都是引用：落点定理决定哪一行，缝合定理给出产物，`select_sound` 给出代价条件。**

**⇒ 两处机械修正：`hsome : gridEval … = v` 必须**从右到左**用（`rw [← hsome]`）才能替换 `v`；
`gridEval_congr` 的 `n`、`x` 是隐式的，合一挑不出来，必须显式给。**
### 3.39 **第 1076 轮：一条界覆盖所有度数，常数恰为 `d(d−1)/8`**

**前三轮各手工推一个常量：`x²` 的 `1/4`、`x³` 的 `3/4`、`x⁴` 的 `3/2`。本轮从**这些数的一个观察**出发，而不是从新的构造出发：**

```
2·1/8 = 1/4     3·2/8 = 3/4     4·3/8 = 3/2
```

**⇒ 故三者是 `d(d−1)/8` 的实例。而树里已有 `chord_error_of_second_deriv_bound`（`|f''| ≤ M ⟹ 弦误差 ≤ M(b−a)²/8`），
⇒ 一般情形不需要做**第四次**手工分解——只需要**一次求导**。**

**文件 `Lattice/Lib/Compiler/PowChord.lean`：**

```lean
deriv_pow_fun    : deriv (fun t => t^d) = fun t => d · t^(d−1)
deriv_deriv_pow  : deriv (fun t => d · t^(d−1)) = fun t => ↑(d·(d−1)) · t^(d−2)
deriv2_pow       : deriv^[2] (fun t => t^d) = fun t => ↑(d·(d−1)) · t^(d−2)
pow_chord_error  : (0 ≤ a, a < b, b ≤ 1) |x^d − chord| ≤ d(d−1)(b−a)²/8
pow_uniform_bound: ∀ x ∈ [0,1), |x^d − gridEval (interpFamily n (t↦t^d)) n x| ≤ d(d−1)(1/n)²/8
constant_two / constant_three / constant_four
general_formula_matches_hand_derived
```

**⇒ 为什么走二阶导而不是继续分解：手工分解要把 `Q_d` 写成双和（见 `x²`、`x³`、`x⁴` 的系数规律），
对任意 `d` 需要有限和与几何级数的机器。⇒ 二阶导路线只需**一次**导数计算 + 在 `(a,b) ⊂ [0,1]` 上压 `|t^{d−2}| ≤ 1`。**
**⇒ 代价是界写成 `M(b−a)²/8` 而非尖顶估计；但在 `d = 2,3,4` 上两条路线**完全一致**，
⇒ 故一般界的常数**不是**松的。而这个「一致」在本轮**不是假定**：最后三条定理就是它的证明。**

**⇒ `d(d−1)` 写成**自然数乘积再强转**，使定理里的常数**字面上**就是 `d(d−1)/8`，而不是等价改写。**

**⇒ 两条 API 教训：`Function.iterate_two` 不存在，故 `deriv^[2] f = deriv (deriv f)` 用 `show` 陈述；
`deriv_const_mul` 需要**显式可微性参数** `(c) (hd)`，`rw` 必须写全。**

**⇒ 命名门禁抓到撇号**：我的第一个名字 `deriv_pow'` 被目标覆盖门禁拒绝（撇号超出豁免表）。
⇒ 改名为 `deriv_pow_fun` 而非豁免——与第 1043 轮 `compile_injective'` 同一决定。**
### 3.40 **第 1077 轮（第四次表结构压力测试）：解析能力与符号证据解耦，于是**任意度数**可入表**

**第 1076 轮证出了覆盖所有度数的界，却**进不了表**。原因不是数学，而是**结构**：**
**⇒ `CapabilityRow` 要求 `term : ExprExt` 与 `compiled` 的证明，而 `ExprExt` 只能写**有限嵌套**的 `mul`，
故 `x^d` 对任意 `d` **不可表示**。⇒ **界是一般的，行不是。****

**⇒ 修法是两层划分：**

```lean
structure AnalyticRow where        -- 函数、族、常数、界；**没有**符号项
  degree, fn, constant, covers, covers_self, covers_bound

CapabilityRow = AnalyticRow + 符号证据（term、compiled、family_eq、target）

analytic_of_capability : CapabilityRow → AnalyticRow     -- 符号层是解析层的**加细**
powAnalyticRow (d) (2 ≤ d) : AnalyticRow                 -- **对每个度数**存在
pow_uniform_bound_Icc                                     -- 该行所需的闭区间形式
```

**⇒ 为什么这是**正确的分界**而不是绕道：选择比较的是 `covers` 与 `constant`，两者都在解析层；
符号证据只在**把行追溯到源语言**时才需要。**
**⇒ 把它们放进同一个结构与界并列，混淆了两个**作用域不同**的断言：
「这一族近似到 `C/n²`」与「并且我们能说出哪个表面项编译到它」。**

**⇒ 回报是具体且**从未手工推导过**的：**
```lean
quintic_bound      : x^5   ≤ 5/2·(1/n)²      (5·4/8)
tenth_power_bound  : x^10  ≤ 45/4·(1/n)²     (10·9/8)
```
**⇒ 这两个度数在本项目中**从未被处理**，它们从 `powAnalyticRow` 直接落下，**没有新的分解、没有新的求导**。
⇒ 这才使「任意度数的覆盖」这句话值得说。**

**⇒ 我的编辑脚本**两次**弄坏了这个文件：一次剥离 `have h := …` 时留下了悬空的 `rwa`，
一次补丁因注释里的星号已解码而找不到锚点。⇒ 两次都用**按行区间替换**修复——
区间由 `next(...)` 从**精确的定理名**定位，这正是文本锚点失败时一直奏效的做法。**
### 3.41 **第 1078 轮：选择逻辑上提到解析层，能力层被**证明**为它的实例**

**第 1077 轮拆了两层，却把选择逻辑留在强的一层：`sufficient` 与 `select` 的类型都是 `CapabilityRow`。**
**⇒ 后果是荒谬的：解析层覆盖**任意度数**，却**无法被选择**。**

**文件 `Lattice/Lib/Compiler/AnalyticSelection.lean`：**

```lean
structure AnalyticRequest where goal, eps, n, hn          -- 无符号项、无配方
analyticSufficient row req := row.covers req.goal ∧ row.constant * (1/n)² ≤ req.eps
analytic_sufficient_implies_meets
analyticSelect req rows := rows.find? (fun row => decide (analyticSufficient row req))
analytic_select_sound / analytic_select_gives_precision

analyticSufficient_of_capability (row) (req) :
    analyticSufficient (analytic_of_capability row) (toAnalyticReq req) ↔ sufficient row req

capability_select_is_analytic (req) (rows) :
    (select req rows).map analytic_of_capability
      = analyticSelect (toAnalyticReq req) (rows.map analytic_of_capability)
```

**⇒ **最后一条是全部意义所在**。没有它，「符号层是解析层的加细」只是一句评价。
有了它，**在能力表上选择** 与 **在加细后的解析表上选择** 是**同一个操作**——
并且它被陈述为 `Option AnalyticRow` 的**等式**，由列表归纳 + 表头 `sufficient` 分支证明。**

**⇒ 为什么这次上提不是**装饰**：`analyticSufficient_of_capability` 是 `Iff.rfl`，
而那正是「解析层 = 能力层去掉符号字段」这句话的内容。
⇒ 故弱层的选择规则**不是重新推导**，而是**同一条规则在更弱假设下可用**。**

**⇒ 一处重复被**裁定**而非忽略：重复门禁标出两对**跨层平行**定理
（`sufficient_implies_meets`/`analytic_sufficient_implies_meets` 与两条精度定理）。
⇒ 计数基线 `192 → 194`，理由**写进工具源码**：它们是有意跨越一次**加细**的平行，
而加细本身是一条定理。⇒ 另一条路（删除能力层版本）会去掉**产物缝合所消费的那一层**，故平行保留。**

**⇒ 两处机械修正：`List.map` 必须放进第一分支的 simp 集（否则加细列表从未展开，只化约了左边）；
`decide` 值必须以 `= true`/`= false` 显式给出，因为 **`Bool` 的 `if` 条件与 `Prop` 的 `decide` 改写不是同一件事**。**
### 3.42 **第 1079 轮：任意度数现在不仅**有界**，而且**确实被选中****

**第 1078 轮把选择器上提到解析层，并证明能力层是它的实例。缺的是让「任意度数」**可操作**的东西：
一张按度数索引的解析表，以及「选择器确实**落在**一个本项目从未处理过的度数上」的证明。**

```lean
noncomputable def powRowsTo : ℕ → List AnalyticRow
  | 0 => []
  | (n+1) => powRowsTo n ++ (if h : 2 ≤ n then [powAnalyticRow n h] else [])

powRowsTo_six : powRowsTo 6 = [row 2, row 3, row 4, row 5]
five_ne_two / five_ne_three / five_ne_four      -- 三点分离
quintic_lands :
    analyticSelect (目标 := t⁵, 5·4/8·(1/n)² ≤ eps) (powRowsTo 6)
      = some (powAnalyticRow 5 _)
```

**⇒ 为什么从度数 2 起：度数 0 与 1 在这里**没有逼近的意义**——仿射族是**精确**的，它在能力层。
⇒ 故解析层只记录**近似**族，从二次起。**

**⇒ `quintic_lands` 是这条线的**最后一块**：1076 证明了对每个度数的界存在；1077 证明承载那些界的层不被符号证据束缚；
1078 证明两层选择方式相同；本条则证明选择器在**跳过三个更低的族之后**返回五次行。**
**⇒ 而它用的正是能力层落点定理那套「三次 `find?_cons_of_neg` + 一次 `find?_cons_of_pos`」——
**这本身就是两层是同一套机械的证据**。**

**⇒ `powRowsTo_six` 需要 `Nat.reduceLeDiff`**：`if h : 2 ≤ n` 是**依赖的 `dif`**，
故在具体数字上求值需要**带减法的归约引理**，普通 `simp` 不够。
### 3.43 **第 1080 轮：宏观认知重建（一次只用**文件与工具输出**、不依赖记忆的盘点）**

**本轮不写新定理。⇒ 目的是回答一个问题：**第 1043–1079 轮（37 轮）在与整体目标的关系上，到底做成了什么、处在什么位置。**

#### 一、用工具测出的第一个事实：新线是一座**孤岛**

| 名字 | 引用文件数 | `Lib/Compiler/` **之外** |
|:--|--:|--:|
| `compileTarget` | 4 | **0** |
| `EvaluatedArtifact` | 8 | **0** |
| `decodedFamily` | 2 | **0** |
| `CapabilityRow` | 6 | **0** |
| `AnalyticRow` | 2 | **0** |
| `pow_uniform_bound` | 2 | **0** |
| `piecewiseIRWeights` | 6 | **0** |
| `irWeights_error_bound` | 6 | **0** |
| `encodeGrid` | 6 | **1**（`Compose/Showcase/L3L2.lean`） |
| `gridLayout` | 2 | **0** |

**⇒ 也就是说：这 37 轮的全部产物（10,027 定理中的约 120 条新定理）在 `Lib/Compiler/` 之外**零引用**。
⇒ 用 `OBJECTIVE-MAP` 自己的判据（「外部引用数为 0 的载体是一个名字，不是一次交付」），
**新线在**目标层面**是不可见的。**（它内部交叉引用极密，但那是**同一座岛**内的引用。）**

#### 二、第二个事实：目标条款的载体全部是**旧模块**

`OBJECTIVE-MAP.md` 的 14 个条款的载体位于 `Runtime/`、`Core/`、`Semantics/`、`Usage/`、`Plugins/`。
**⇒ 其中**没有**一条来自 `Lib/Compiler/`。⇒ 故 `check_objective_coverage` 的规则 A（每条款有具名载体）
**从未**因新线而改变。**

#### 三、第三个事实：八阶段链的接缝**全部 `old`**

`chain_connectors --provenance` 的后三段：

| 接缝 | total | old | recent |
|:--|--:|--:|--:|
| 3.2 verify → 3.3 repair | 2 | **2** | 0 |
| 3.3 repair → 3.4 reinject | 4 | **4** | 0 |
| 3.4 reinject → 4 loop | 3 | **3** | 0 |

**⇒ 新线**一次也没有**触碰这些接缝。⇒ 第 83 轮记录的「FRESH-ONLY：这些接缝只在 fresh 下连通」的问题**依然存在**。**
⇒ 新线补的是**另一条**链（符号项 → 产物 → 精度 → 选择），**不是**官方八阶段链。

#### 四、第四个事实：17 个**弱载体**（跨文件引用 ≤ 1）

包括 `penaltyToLoss`（1）、`covered_of_vanishing`（1）、`models_of_covered_data`（1）、
`weightLadderN`（1）、`sqDistHalvingRepair`（1）、`sqDistHalving_terminates_and_stabilises`（1）等。
**⇒ 这些是条款 2.1、2.2、2.3、3.3 的**唯一**载体，而它们几乎只被 `Usage/Examples.lean` 消费。
⇒ 即：**这些条款的“证据”实际是示例文件在支撑，而不是链在支撑。**

#### 五、结论与重新规划

**结论（一句话）：第 1043–1079 轮把「符号 ⇄ 权重」这一跳做**深**了（能力选择、任意度数、产物缝合、修复写回），
但做成了一个**自洽的孤岛**；目标层与八阶段链**都没有搬到它**。**

**⇒ 因此下一阶段的第一要务不是继续加深该岛，而是**把它接入**。具体三步，按依赖排序：**

1. **找到两套 `符号 → 权重` 的交点并给出桥定理。**
   主链用 `Runtime/SymbolToWeightCorrectness.lean::compileToLayer`（约束 → 层参数）；
   新线用 `Lib/Compiler/SymbolicEntry.lean::compileTarget`（符号项 → 目标 → 分段族 → 权重）。
   **⇒ 需要一条定理说明：在某个共同片段上，两者给出**同一个**权重（或至少同一族）。**
   **⇒ 若找不到共同片段，那就必须**如实记录「这是两种不同的表示」，并说明各自覆盖什么**——
   而不是假装它们是一条链。**

2. **让新名字成为目标条款的载体。** 在 `gov/check_objective_coverage.py` 的 `CLAUSES` 中，
   为条款 1.3（符号 → 权重）与 1.4/3.1（权重 → 符号）**新增**新线的载体
   （`compileTarget`、`EvaluatedArtifact`、`decodedFamily`），并在 `OBJECTIVE-MAP` 里记下跨文件引用数。
   **⇒ 这一步会让规则 A 第一次**真的**看见新线；若引用数为 0，它就诚实地显示为弱载体。**

3. **再接八阶段链的 3.2→3.3→3.4 接缝。** 这三段的 `old` 状态意味着它们的连通性只在 fresh 下成立。
   **⇒ 修法不是再写一条定理，而是让**既有**定理被**新的**下游消费**（这样 `git blame` 的声明就变 recent）。
   **⇒ 具体地：让 `Lib/Compiler` 的修复/写回（`write_back_verifies_and_changes`）被 `Runtime/VerificationLoop`
   的某条定理消费，或反过来。这是**真实**的连接，而不是文档声明。**

**⇒ 本轮之后立即执行第 1 步**：先测量 `compileToLayer` 与 `compileTarget` 是否存在共同片段——
若存在就写桥；若不存在就先写「为何不同」的记录。**这是**测量优先于施工**的同一原则在本层的应用。**
### 3.44 **第 1081 轮：测量两套「符号 → 权重」，证明其**唯一真实交点**，并把新线登记为条款载体**

**第 1080 轮测出新线在 `Lib/Compiler/` 之外**零引用**。本轮执行它给出的计划的前两步。**

#### 一、先测量：两套实现**不是同一个对象**

| | 主链（`Runtime/ConvertVectorLinear.lean`） | 新线（`Lib/Compiler/`） |
|:--|:--|:--|
| 载体 | `LinearLayer = ⟨w : List ℤ, b : ℤ⟩`（`:138`） | `Segment = ⟨m : ℝ, c : ℝ⟩` |
| 求值 | `LayerOut l x = dot l.w x + l.b`（`:143`） | `Segment.eval s x = s.m * x + s.c` |
| 语义 | **精确**：约束满足 ⟺ 输出为零 | **逼近**：`\|f − 插值\| ≤ C/n²` |

**⇒ 故宣称「一条链」会是假的：`ℤ→ℝ` 不是同构，而「输出为零」与「误差有界」是**两个不同判据**。**
**⇒ 唯一真实交点是**标量仿射片段**，且只到这个程度：**

```lean
segment_eval_eq_scalar_layer_out (w b x : ℤ) :
    (⟨w, b⟩ : Segment).eval (x : ℝ) = ((LayerOut ⟨[w], b⟩ [x] : ℤ) : ℝ)
scalar_layer_out_eq_segment_eval    -- 同一等式的反向读法
bridge_sample                       -- 一个具体实例，读者可手算核对
```

**⇒ 文件头明确写出桥**不覆盖**的三件事：非整数系数、非标量宽度、「零 vs ε」语义。三者皆不声称。**

#### 二、让孤岛**可见**

`gov/check_objective_coverage.py` 的 `CLAUSES` 现在登记了新线：
```python
"1.3 symbol -> weight": [..., "compileTarget", "EvaluatedArtifact"]
"1.4 weight -> symbol": [..., "decodedFamily"]
```
**⇒ 重新生成的 `OBJECTIVE-MAP` 立刻显示它们**实测的强弱**：**

| 载体 | 跨文件 | 同文件 |
|:--|--:|--:|
| `compileTarget` | **2** | 20 |
| `EvaluatedArtifact` | **7** | 7 |
| `decodedFamily` | **1** | 7 |

**⇒ 这些跨文件引用**仍然全部在 `Lib/Compiler/` 内部**。⇒ 而这正是登记它们的意义：
**地图现在记录这座岛的内部密度，而不是让它不可见。跨文件为 0 的载体在那张表里是一个**诚实的条目**；藏起来则不是。**

#### 三、一个层次规则的核实

**`Lib/Compiler/BridgeToMainChain.lean` 导入了一个 `Runtime/` 模块，这是合法的：**
**⇒ `Lib/Compiler/` 下已有五个文件这样做（`CarrierApproximation`、`CarrierClosure`、`CarrierCoverage`、
`CarrierInstantiation`、`CarrierReproduction`），而 gate I4 只禁止 **Core 导入 Lib/Lift**。**

**⇒ `bridge_sample` 是转发（一般定理的具体实例），已按「有意转发」登记。**
### 3.45 **第 1082 轮：`Repair` 的**乘积实例**——两个约束可以**同时**修复**

**第 1081 轮的计划说下一步是「把两个 `Repair` 实例接起来」。⇒ 本轮**先测量**，而测量**排除了**那条路：**

| 实例 | 载体 | 判据 |
|:--|:--|:--|
| `Runtime/RepairClosure.lean` | `Repair Layer`（`ℤ`） | 提取后的符号满足约束 |
| `Lib/Compiler/WriteBack.lean` | `Repair (ℕ → Segment)`（`ℝ`） | 第 0 段斜率等于目标 |

**⇒ 载体不同、判据不同，**无可证交换律**。⇒ 硬做「合成一条链」正是本项目反复抓到的错误。**

**⇒ 但两者共享**接口**，而接口层有一条真正可推广的东西：**

```lean
def repairProd (R : Repair α) (S : Repair β) : Repair (α × β) where
  Sat p := R.Sat p.1 ∧ S.Sat p.2
  fix p := (R.fix p.1, S.fix p.2)
  μ p   := R.μ p.1 + S.μ p.2
  -- absorbs / decreases / atomic 三条全部证明
```

**⇒ `decreases` **不是白给的**，而它正是本轮的实质内容：当**只有一侧**失败时，另一侧的测度**不下降**，
故若不是失败侧的严格下降能带动总和，总和就不会降。⇒ 证明按「哪一侧失败」三分，并用 `absorbs` 把通过的一侧固定住。**

**⇒ 而 `repairProd_iterate` 是「并行」这个词的内容：**
```lean
(repairProd R S).fix^[n] p = (R.fix^[n] p.1, S.fix^[n] p.2)
```
**⇒ `n` 轮让**两侧各走 `n` 步**，而不是「修完一侧再修另一侧」；总和单调下降才使「同时收敛」合法。**

**⇒ `Lib/Compiler/RepairPair.lean` 把它落到真实载体上：**
```lean
twoSlopeRepair a b : Repair ((ℕ → Segment) × (ℕ → Segment))
twoSlopeRepair_absorbs / _decreases / _iterate
```

**⇒ 两处基线裁定：三个定义性投影是 `rfl`/`Iff.rfl`，对新定义而言**正确**（与能力表的 rfl 等式同一判断），
定义式证明基线 `816 → 819`；`twoSlopeRepair_iterate` 是转发，已登记。**
**⇒ 修复普查 `A: 10→11 文件 / 30→35 声明`，`B: 18→19 / 50→54`。**
### 3.46 **第 1083 轮：把「修复改变可观察量」**提升到乘积状态****

**第 1082 轮造了 `repairProd`，但一个结构实例本身不是可观察的断言。⇒ 本轮把第 1047 轮的观察定理提升到乘积态。**

```lean
twoSlopes_sat_after_fix (a b) (p) :
    (twoSlopeRepair a b).Sat ((twoSlopeRepair a b).fix p)

twoSlopes_change_two_observables (b₁ ≠ a) (b₂ ≠ b)
    (x₁ ≠ 0) (segmentIndex n x₁ = 0) (x₂ ≠ 0) (segmentIndex n x₂ = 0) :
    gridEval (fix p).1 n x₁ ≠ gridEval (constFamily b₁ c₁) n x₁
  ∧ gridEval (fix p).2 n x₂ ≠ gridEval (constFamily b₂ c₂) n x₂
```

**⇒ 两个见证点**可以不同**，而这不是便利，是**内容**：两侧是**独立的载荷**，
故每一侧都必须在**它自己的**第 0 段被选中的点上读数。共用同一个见证点会**默默假定两侧是同一个对象**。**

**⇒ `twoSlopes_sat_after_fix` 为什么也要有：它说**一步**在两侧**同时**达标（两侧各是 `slopeFix_sat`）。**
**⇒ 与 `repairProd_iterate` 合起来：并行修复既不更慢，也没有被串行化。⇒ 没有这条，「一步」就是假定。**

**⇒ 两条都是**推论**，这一点写明白：第一条是两个 `slopeFix_sat` 的合取，第二条是两个 `repair_changes_observable` 的合取。
⇒ 新东西是**到乘积状态的提升**（`.fix` 逐分量作用），不是新的分析事实。**

**⇒ 两处机械修正：`twoSlopes_sat_after_fix` 初版里我留了个占位符 `exact ⟨——⟩`（我打的破折号从未被解析）；
`segmentIndex`/`gridEval` 不在作用域（补两个 `open`）。**

**⇒ 两条因此成为承重的定理已登记 verdict：`repair_changes_observable`、`slopeFix_sat`。
⇒ 修复普查 `B: 54 → 55`。**
### 3.47 **第 1084 轮：闭环回路**实例化到产物载荷**，且一条**休眠定理获得首个消费者****

**第 1083 轮的计划问：主链的回路是否泛型？⇒ **是**：`VerificationLoop` 以 `variable {α : Type}` 声明，
`step`/`run`/`step_fixed_of_sat`/`loop_end_sat` 全部以 `α` 为载体。**
**⇒ 故它可以在新线的状态上**直接实例化**——不需要桥，也不需要新语义：**同一批定理在另一个载体上**。**

**文件 `Lattice/Lib/Compiler/LoopInstance.lean`：**

```lean
twoSlopeLoop (a b : ℝ) (n) (x) : VerificationLoop ((ℕ → Segment) × (ℕ → Segment))
  repair    := twoSlopeRepair a b
  objective := fun p => gridEval p.1 n x

twoSlopeLoop_ends_sat      -- 由 `VerificationLoop.loop_end_sat` 证明
twoSlopeLoop_step_fixed    -- 由 `VerificationLoop.step_fixed_of_sat` 证明
twoSlopeLoop_run_components -- 主链 `run` 与乘积迭代定理的合成
```

**⇒ `objective := gridEval p.1 n x` 的选择理由：回路每轮「修一次、看一次」，这就是最小的可解释观测——
产物在观察点的输出。一个常值目标函数会让实例化在**精神上**空转。**

#### 测量出的消费者数（本轮中途我不得不**更正**自己的说法）

| 定理 | 此前消费者 | 现在 |
|:--|:--|:--|
| `loop_end_sat` | `Primitives/MultistepLoop`、`Usage/Examples` | **3**（首个在 Primitives/Usage 之外） |
| **`step_fixed_of_sat`** | **其自身文件之外：零** | **1，首次被使用** |

**⇒ 我在工作笔记里先写了「这是 `Lib/Compiler` 第一次消费 Runtime 定理」——那是**假的**：
`Lib/Compiler/` 下已有 **17** 个文件导入 Runtime 模块，而 `CarrierReproduction` 早就调用了
`Lattice.Runtime.LoopClosure.extractLayer`。**
**⇒ 真实而更窄的事实是上表那一条：`step_fixed_of_sat` 在第 1042 轮为「让 `step` 的 docstring 可引用」而写，
此**前零消费者**；本轮是它的**首次使用**——**一条休眠定理被唤醒**，而不是发明了一个新连接。**
### 3.48 **第 1085 轮：闭环回路的**消失定理**，配一个有意义的**缺陷目标****

**第 1084 轮把回路实例化了，但用 `objective := gridEval p.1 n x`——它在不动点**不为零**，
故接不上 `closed_loop_reinject_vanishes`。⇒ 本轮**改目标函数**，而不是放弃那条定理。**

```lean
closed_loop_reinject_vanishes (x) (hobj : ∀ y, V.repair.Sat y → V.objective y = 0) :
    V.objective (V.run (V.repair.μ x) x) = 0
```

**⇒ 目标改成**缺陷**而非**取值**：**

```lean
twoSlopeDefectLoop (a b) : VerificationLoop (载荷 × 载荷)
  repair    := twoSlopeRepair a b
  objective := fun p => ((p.1 0).m - a)² + ((p.2 0).m - b)²

twoSlopeDefectLoop_objective_at_sat : Sat p → objective p = 0
twoSlopeLoop_objective_vanishes :
    objective (run (μ p) p) = 0        -- 一行：把本实例的 hobj 喂给主链定理
```

**⇒ 为什么是**平方和**而不是差：两条斜率可以朝相反方向出错，故**带符号的和可能在错误状态上相互抵消为零**。
⇒ 平方消除这种可能，而和恰好**在两侧都正确时**为零。⇒ 这正是 `hobj` 要求的性质；
**若选带符号差，就会满足类型而不满足主张。**

**⇒ 终点陈述说的是什么：经过 `μ p` 轮后，产物两条斜率**恰好等于目标 `a`、`b`**——平方偏差为零。」
⇒ 这就是此处「再注入」的含义，而且它陈述的是**产物**，不是抽象变量。**

**⇒ 我第 1084 轮的那个目标函数**保留**：它诚实地做它做的事（回路观测产物的输出），但它**不在不动点消失**，
故**不是**接再注入定理的那一个。⇒ 两个实例并存；只有一者携带「消失」这一主张。**

**⇒ `twoSlopeLoop_objective_vanishes` 是一行转发，已登记。**
### 3.49 **第 1086 轮：逆向链在**产物层闭合**——修复 → 写回 → 提取 → 验证 + 可观察变化**

**规划 §3.3 的四项在第 1047 轮已为**正向**交付。而**逆向**方向（权重 → 符号，用于验证、修正、再注入）
此前散在三条独立定理里。⇒ 本轮把它们装到**同一个产物**上。**

```lean
reverse_chain_twoSlope (b₁ ≠ a) (b₂ ≠ b) (x₁ ≠ 0) (segmentIndex r.n x₁ = 0)
                                          (x₂ ≠ 0) (segmentIndex r.n x₂ = 0) :
    (writeBack (slopeFix a …) dom₁ r).decodedFamily = some (slopeFix a …)   -- 提取忠实
  ∧ (writeBack (slopeFix b …) dom₂ r).decodedFamily = some (slopeFix b …)
  ∧ slopeSat a (slopeFix a …) ∧ slopeSat b (slopeFix b …)                  -- 判据成立
  ∧ (writeBack (slopeFix a …) dom₁ r).evalAt x₁ ≠ (writeBack …) .evalAt x₁ -- 可观察变化
  ∧ (writeBack (slopeFix b …) dom₂ r).evalAt x₂ ≠ (writeBack …) .evalAt x₂
```

**⇒ 为什么这不是三条平行的事实：每个合取项都是**既有**定理
（`decodedFamily_ofSegments`、`slopeFix_sat`、`write_back_verifies_and_changes.2`），**这样说很清楚：
新内容是六项**都关于同一次 `writeBack` 调用**。⇒ 调用者需要的是「**一个**产物同时忠实提取、达标、并且可观察地变了」，
而不是关于三个对象的三条事实。**

**⇒ 提取那两个合取项正是**此前缺的那一半**：第 1044 轮的 `decodedFamily_ofSegments` 说产物里的载荷
**就是**它构造自的那个族，故「提取返回的东西」与「被修好的东西」是**同一个对象**，
而不是读者必须假定相同的两个东西。**

**⇒ 两处机械错误：我引用了一个**自己编的名字** `write_back_verifies_and_changes_obs`，
而可观察变化其实是 `write_back_verifies_and_changes` 的**第二分量**；
`decodedFamily_ofSegments` 不在作用域，因为 `LoopInstance` **没有导入** `Chain`——文件需要那个 import。**

**⇒ `decodedFamily_ofSegments` 因此成为承重，verdict 已登记。**
### 3.50 **第 1087 轮：把「同一条款下两套互不引用的实现」**登记**下来**

**条款 1.3（符号 → 权重）与 1.4（权重 → 符号）各有**两套**实现，且互不引用。**
**⇒ 规划允许按能力族声明，但**同一条款下两个互不引用的实现必须被登记**，否则「实现了」这句话就有两个意思。**

**⇒ 新文件 `SYMBOL-WEIGHT-COMPARISON.md`（**每个数字都来自 `gov/` 的工具输出**，文末给出重新测量命令）：**

| 载体 | 条款 | 定义于 | 跨文件 | 同文件 |
|:--|:--|:--|--:|--:|
| `compileToLayer` | 1.3 | `Runtime/SymbolToWeightCorrectness.lean` | **52** | 6 |
| `extract` | 1.4 | `Core/IR/Extract.lean` | **51** | 9 |
| **`compileTarget`** | 1.3 | `Lib/Compiler/SymbolicEntry.lean` | **2** | 20 |
| **`EvaluatedArtifact`** | 1.3 | `Lib/Compiler/Layout.lean` | **7** | 7 |
| **`decodedFamily`** | 1.4 | `Lib/Compiler/Layout.lean` | **2** | 7 |

**⇒ 且本轮**再次核实**：新线三个载体在 `Lib/Compiler/` 之外**零引用**（第 1080 轮的测量仍成立）。**

**⇒ 文档还写明三件**必须说清**的事：**
1. **唯一可证的**交点**：长度为 1 的整数标量仿射（`segment_eval_eq_scalar_layer_out` + 可手算实例）；
2. **各自覆盖什么**（主链：多约束、整数精确、插件治理；新线：任意精度、任意幂次、表面语法、产物契约）；
3. **不合并的三条**测量理由**：数的域不同（`ℤ` vs `ℝ`）、判据不同（恰为零 vs 有界）、组织轴不同（按约束 vs 按段）。

**⇒ 第三条是本文的重点。「不可合并的一对」应当被**如此记录**，而不是用一条看起来像桥的弱定理把它们粘起来。**
**⇒ 而若做真正的统一，需要先**选定共同载体**——那是一次**架构级改动**，按纪律须在分支上尝试、
验证后 `--no-ff` 合并，且先证旧结果在新载体上仍成立。**

**⇒ 文档**不**声称哪一套「更正确」：它们在不同判据下都正确，而判据不同正是它们需要并存的原因。**
### 3.51 **第 1088 轮（**架构级尝试**，分支 `feat-real-layer`）：一个推广，两个截面**

**第 1087 轮的对照文档记录了「两套实现**不可合并**」。⇒ 但「不可合并」不等于「无法解释」。**
**⇒ 本轮在**分支**上尝试更弱但更有用的一件事：**两者是同一个推广的两个截面**。**

```lean
structure RealLayer where  w : List ℝ ;  b : ℝ
dotR / RealLayer.out / realLayerOfInt / castI

realLayer_ofInt_out (l : LinearLayer) (x : List ℤ) :
    castI (LayerOut l x) = (realLayerOfInt l).out (x.map castI)     -- 主链 = **整数截面**

realLayer_single_eq_segment (m c x : ℝ) :
    RealLayer.out ⟨[m], c⟩ [x] = (⟨m, c⟩ : Segment).eval x          -- 新线 = **单段截面**

two_sections_of_one_generalisation (w b x : ℤ)                     -- 两者并读（标量片段）
```

**⇒ 算术内核是两条**结构归纳**引理，且两条都必需：**
- `zip_map_cast`：逐元素强转后再 `zip` = 先 `zip` 再强转；
- `zip_fold_cast`：**带任意整数累加器**的 `foldl` 与强转可交换。

**⇒ 第二条是真正的实质：`ℤ` 的和能强转成 `ℝ` 的和，**只因为累加器可以被一起带过去**——
这就是那条引理必须以 `accZ` 而非 `0` 陈述的原因。**

**⇒ **什么都没改**：`LinearLayer`、`Segment`、`dot`、`LayerOut` 及其全部证明**逐字未动**。
⇒ 这是**并列新增**，故主链那 52 处 `compileToLayer` 相关引用**字节相同**。
⇒ 这一点使它成为**解释**而非**迁移**：没有任何既有消费者被搬动。**

**⇒ 它解决与不解决什么：它说明两套实现是**同一个对象在两个截面上的像**，故二义性**被解释**了；
它**不**统一两者的判据——`AllZeroOutputs` 与 ε 界仍是两个谓词，本文件不作相反声称。**

**⇒ 按纪律在**分支**上构建，合并前分支自身 `--fast` 全过（382.3 秒），再 `--no-ff` 合并，
故分支点与它的两个提交在历史里可见。**

**⇒ 三次机械失败，都是我的，都已修：**
1. 匿名 `(fun z => (z : ℝ))` 在打印里呈单子形式，破坏了 `zip` 引理的模式匹配 ⇒ 改为命名 `castI`；
2. `castI 0` **不**与 `0` 定义相等 ⇒ 折叠引理需 `simpa` 而非 `exact`；
3. 用匿名 lambda 构造的 `ofInt` **不**规约其投影 ⇒ 改为 `realLayerOfInt` 用 `castI`，使投影规约成为定义相等。

**⇒ 还有一条**流程**教训：我的手工门禁清单里 `audit_duplicate_names.py` 与 `check_duplicate_classes.py`
**漏了 `--check`**，故我这边全过而 `verify_all` 报 2 处失败。⇒ 这与本项目历史上同类的遗漏是**第二次**。
⇒ 结论：**跑 `verify_all` 用的那条确切命令行，而不是记忆里的近似。****
### 3.52 **第 1089 轮：推广**被消费**了——`gridEval` 就是实数层上的求值**

**第 1088 轮造了 `RealLayer` 并证明两套实现是它的截面，但**没人用它**：一个没有消费者的推广是另一座小岛。**
**⇒ 本轮让它**承重**，且**不改任何既有定义**。**

```lean
segmentToRealLayer (s : Segment) : RealLayer  := ⟨[s.m], s.c⟩
familyToRealLayers (g : ℕ → Segment) : ℕ → RealLayer
familyToRealLayers_out : (familyToRealLayers g k).out [x] = (g k).eval x

gridEval_eq_realLayer_out (g) (n) (x) :
    gridEval g n x = (familyToRealLayers g (segmentIndex n x)).out [x]
```

**⇒ 最后一条是重点：`gridEval`——新线的核心求值、出现在它每一条精度定理里——现在被写成
「先选段号，再对一个实数层求值」。⇒ **什么都没重新定义**；那条等式使两种读法可以互相代入。**

**⇒ 回报是一条**定理**而不是一句主张：**

```lean
pow_uniform_bound_as_realLayer (d) (2 ≤ d) (n) (0 < n) :
    ∀ x ∈ [0,1), |x^d − (familyToRealLayers (interpFamily n (t↦t^d)) (segmentIndex n x)).out [x]|
                      ≤ d(d−1)(1/n)²/8
```

**⇒ 这就是第 1076 轮的一般度数界**改写为关于 `RealLayer` 输出的陈述**。
⇒ 故推广不是一个平行结构：新线最强的精度结果是**关于实数层求值**的陈述，
而下游读者可以用一条等式在两种词汇间移动。**

**⇒ 仍**不**声称的：主链自己的界**没有**这样改写，因为 `LayerOut` 取 `List ℤ` 而它的判据是**精确**而非 ε。
⇒ 只有新线一侧被搬到推广上；主链只通过 `realLayer_ofInt_out` 相连。**

**⇒ 三处机械失败：`gridEval`/`segmentIndex` 不在作用域（需要两个 import + 两个 open：
`GridAlgebra` 与 `PiecewiseWeights`）；`gridEval` 那条等式需要 `segmentToRealLayer_out` 的 `.symm` 方向，花了一次构建。**
### 3.53 **第 1090 轮：正向三项载体的**实测消费者**——并更正地图的分类**

**第 1080 轮把「跨文件引用 ≤ 1」记为**弱载体**。⇒ 本轮按**引用文件的实际分布**重测，结论需要更正。**
（测量方式：`git grep -l <名字>`，再扣除 `Usage/` 与**定义处自身**。）

| 载体 | 条款 | 总文件 | **非示例且非定义处** | 判断 |
|:--|:--|--:|--:|:--|
| `PenaltyEmbedding` | 2.1 约束损失 | 19 | **17** | **强** |
| `penaltyToLoss` | 2.1 | 4 | **2**（`StructuredInit`、`RepairPenalty`） | 中 |
| `weightLadderN` | 2.3 结构化初始化 | 6 | **5** | 强 |
| `compileWith` | 2.3 | 6 | **5** | 强 |
| `compile_sound_n` | 2.3 | 3 | **1**（`NondegenerateInstance`） | 弱但不孤 |
| **`covered_of_vanishing`** | **2.2 数据合成** | 2 | **0** | **真孤儿** |
| **`models_of_covered_data`** | **2.2 数据合成** | 2 | **0** | **真孤儿** |

**⇒ 故「正向三项都只有示例级证据」是**错的**：2.1 与 2.3 的载体有 5–17 个真实消费者。**
**⇒ 真正的孤儿只有**条款 2.2（数据合成）的两条**：它们除了自身定义处之外，**只被 `Usage/Examples.lean` 引用**。**

**⇒ 为什么这个更正重要：若不更正，我会去「修」2.1/2.3——那是**不存在的问题**，
而真正的空洞（2.2）会继续被 17 个别的引用数字掩盖。**

**⇒ 2.2 的两条说什么（读自 `Core/IR/Semantics.lean:381` 与 `:488`）：**
- `models_of_covered_data`：若 `f` 在所有**未被命名**的位置取零，则 `f` 是 `compileSkel k` 所编译骨架的模型；
- `covered_of_vanishing`：同一前提下，`materializeWith k f` 的每个张量都被 `shapesOf` 覆盖。

**⇒ 缺失的是什么：这两条**描述了**合成数据的性质，但**没有任何一步用它**。
⇒ 要让 2.2 接入，需要的是一条**消费者**——最自然的候选是「用合成数据做**验证**」：
若 `f` 满足上述消失条件，则从编译权重提取出的符号**在该数据上**与原骨架一致。
⇒ 但 `extract_compile`（1.4 的回程）**已经**给出更强的东西（无需 `f` 的任何假设），
故这条候选**不会**带来新信息——**这就是 2.2 至今没有消费者的真实原因：它的结论被更强的事实覆盖了。**

**⇒ 结论（本轮的实质判断）：条款 2.2 的孤儿状态**不是接线遗漏，而是它的定理被 `extract_compile` 蕴含**。
⇒ 若如此，诚实的处理**不是**造一条弱消费者，而是：
1. 证明 `models_of_covered_data` / `covered_of_vanishing` **与** `extract_compile` 的关系（蕴含？互补？）；
2. 若确认被蕴含，就在 `OBJECTIVE-MAP` 里把 2.2 的载体标注为「被 1.4 的更强事实覆盖」——
   **那是一句可核对的话，而不是一个装饰性的消费者。**
#### **附：对上一段「被更强事实覆盖」这一假设的**更正**（同一轮内）**

**我读了 `Core/IR/Extract.lean:80` 与 `Core/IR/Semantics.lean:228` 之后确认：那个假设是**错的**。**

```lean
theorem extract_compile (k) : extract (compileSkel k) = some k          -- 提取回程
def ModelsIRSWith W k f := W = compileSkel k ∧ covered (materializeWith k f).tensors …
covered_of_vanishing / models_of_covered_data                            -- 数据覆盖
```

**⇒ 两者是**不同谓词**：一条谈「提取能否回到原骨架」，另一条谈「合成出的数据是否被形状覆盖」。
⇒ **互不蕴含**，故「被覆盖」这一解释不成立。**

**⇒ 真实原因更简单也更尴尬：`ModelsIRSWith` 的两个合取项里，`W = compileSkel k` 是 `rfl`，
而 `covered (…)` 是关于**调用者提供的数据函数 `f`** 的性质。**
**⇒ 也就是说，2.2 的两条是**「如果你这样合成数据，覆盖性就成立」——一个**供使用时才需要的前提**。
⇒ 而树里**没有任何组件需要这个前提**（没有训练步骤、也没有下游判据消费 `covered`）。**

**⇒ 故 2.2 的空洞原因是「**下游不存在**」，而不是「定理不够强」。**
**⇒ 要真正让它承重，需要的不是一条新定理，而是**一个需要覆盖性的下游**——例如
「以合成数据训练后，权重仍满足骨架关系」这样的步骤。⇒ 而本项目**不实现训练框架**（定位明确），
故**这个下游在 LATTICE 内部不可能存在**。**

**⇒ 结论（这才是诚实的最终判断）：条款 2.2 的孤儿状态是**定位决定的**，不是缺陷。
⇒ 正确的处理是把它标注为「**接口性条款**：定理已证，消费者按定位在框架外**」，
而不是给它造一个内部消费者。**
### 3.54 **第 1094 轮：`Repair` 的三条义务**强制** `Sat` 非空——故失败分支**不存在****

**本轮原计划是补 §3.3 第 4 项（失败分支）：把 `no_loop_fixes_unsatisfiable` 实例化到产物载荷上。
⇒ 但**先读那条定理**之后，任务变了：**

```lean
no_loop_fixes_unsatisfiable (hempty : ∀ x, ¬ V.repair.Sat x) (x) : False
```

**⇒ 它的前提说「`Sat` 无居住者」。⇒ 而 `Repair` **根本不可能**有空的 `Sat`，理由就是那个接口本身。**

```lean
exists_sat_iterate_aux (R) : ∀ n, ∀ y, R.μ y = n → ∃ k, R.Sat (R.iterate k y)
exists_sat_iterate (R) (x) : ∃ k, R.Sat (R.iterate k x)
sat_not_empty (R) [Nonempty α] : ¬ (∀ x, ¬ R.Sat x)
```

**⇒ 论证是**一句意识形态 + 一页算术**：若 `Sat` 处处不成立，则 `decreases` 在**每一点**给出
`μ (fix x) < μ x`——而 `μ : α → ℕ` **不可能无限下降**。⇒ 证明是对 `μ x` 的强归纳：
`x` 已满足则取 `k = 0`；否则 `R.fix x` 测度更小，对它用归纳假设，并用 `R.iterate k (R.fix x) = R.iterate (k+1) x`。**

**⇒ 这对「失败分支」意味着什么：在这个抽象里它**不存在**。
⇒ 故 `no_loop_fixes_unsatisfiable` 为真但是**空洞地真**——它永远无法被任何实际的 `Repair` 实例引用。
⇒ 「回路正确但不是魔法」这句话，经检查**什么也没说**：魔法那一情形被结构性地排除了。**

**⇒ 一个值得直说的推论：一个 `Repair` 实例**就是「该目标可达」这一断言**。
⇒ 接口不只是**检查**可达性，它**假定**了可达性。
⇒ 故「这个要求无法满足」的诚实记录处**不是**一个空 `Sat` 的 `Repair`（那是**不可构造的**），
而是一条表明该要求**自身不一致**的定理。⇒ 那比我原计划的纪律**更强**。**

**⇒ 两处机械失败：`induction hn : … using Nat.strong_induction_on` 不被接受（情形名是 `h`，不是 `ind`）；
`sat_not_empty` 初版对**空类型**为假——`[Nonempty α]` 是**必需的**，不是装饰。**

**⇒ `exists_sat_iterate` 是转发（已登记）；`sat_not_empty` 是否定，故否证普查 `370 → 371`、Core `59 → 60`。**
### 3.55 **第 1095 轮：**显式轮数界**——一次修复就够，故抽象测度是**过估计****

**规划 §3.3 第 3 项「到达方式」此前只有抽象答案：回路在 `μ p` 轮后到达 `Sat`。本轮把它变成一个**数字**。**

```lean
twoSlopeRepair_measure_le_two (a b) (p) : (twoSlopeRepair a b).μ p ≤ 2
twoSlopeLoop_sat_after_one (a b) (n) (x) (p) : Sat (run 1 p)
twoSlopeLoop_ends_sat_in_two (a b) (n) (x) (p) : Sat (run 2 p)
```

**⇒ 因为每侧测度是 `if (g 0).m = a then 0 else 1`，故乘积测度之和至多 2。**

**⇒ 有意思的不是推论而是**一个不一致**：一次 `fix` **同时**修好两侧，故**一步**就够；
而抽象定理承诺 `μ p` 轮，而 `μ p` 可以是 2。**
**⇒ 测度数的是**缺陷数**（两侧都错则为 2），**不是步数**——因为一次并行修复把两者一起清掉。**
**⇒ 故抽象界**同时是正确的和松的**；这正是两条陈述都保留的原因：
「`μ p` 轮」真，「2 轮」真，「1 轮」也真且**严格最锐**。**

**⇒ 这才是一个诚实叙述里「到达」应有的样子：一个数字，加上一句提醒——
当一般定理里的那个量**不是**读者会以为是那个量时。**
### 3.56 **第 1096 轮：修复**保留**什么，逐段陈述**——规划 §3.3 第 2 项，精确化**

**第 2 项此前只有弱答案：「已达标的一侧不被改」。⇒ 那句话对**其余各段**什么也没说。**
**⇒ 本轮四条把它钉死：**

```lean
slopeFix_preserves_other_segments (hk : k ≠ 0) : slopeFix a g k = g k
slopeFix_preserves_intercept : (slopeFix a g 0).c = (g 0).c
slopeFix_changes_slope : (slopeFix a g 0).m = a
twoSlopeRepair_preserves_other_segments : 两侧、所有 k ≠ 0，均不变
```

**⇒ 合起来读，改动被**完全定位**：第 `0` 段的**斜率**变成 `a`，第 `0` 段的**截距**不动，
**其余每一段逐段相同**。⇒ 故「修复保留什么」不再是保证，而是一个**读者可逐段核对的等式**。**

**⇒ 为什么这在实例之外也重要：一个**悄悄改了邻段**的修复仍然满足 `Sat`（判据只看第 0 段），
也仍然使 `μ` 下降。⇒ 测量**看不见附带损害**，故保留性必须**单独证明**——
而这正是「只看判据」的叙述会漏掉的东西。**

**⇒ 修复普查 `B: 57 → 61`。**
### 3.57 **第 1097 轮：一次**被自己的架构规则否决**的尝试，以及它解释了什么**

**上一轮的计划是：让 `Runtime/RepairClosure.lean` 消费 `Lib/Compiler/` 的保留性定理，
从结构上把 3.2→3.3 接缝接上。⇒ 我在分支上做了，`lake build` 通过，`--fast` 未跑；然后手工门禁报 5 处失败。**

**其中一条是**决定性的**：**

```
I4   layering respected   1 finding(s)
```

**⇒ `gate.py` 的分层表：`Lattice/Runtime` 秩 **2**，`Lattice/Lib` 秩 **3**，而导入只能**向下**。
⇒ 故 `Runtime/` 导入 `Lib/Compiler/` 是**向上导入**，被规则**禁止**。**

**⇒ 该分支已**删除**（未合并）。⇒ 这不是失败，而是一个**结构性答案**：**

**⇒ 「让主链消费新线」在当前分层下**不可能**。可供选择的路只有三条：**
1. **把新线搬到 `Runtime/`（或其上方）** —— 一次**真正的迁移**，须证全部旧定理仍成立；
2. **在同时位于两者之上的层（`Compose/` 等）写桥** —— 但八阶段接缝指向的是 `Runtime/` 里的声明，
   上层桥**不会**刷新接缝（本轮已测：接缝年龄量的是**被引声明的撰写时间**，不是活跃度）；
3. **改 `LAYER_OF` 的秩** —— 那是**架构决策**，须写明理由并接受「`Lib` 不再是基础层」的后果。

**⇒ 第二条还有一条**同轮测出的事实**要记住：即使加了消费者，接缝仍是
`3.2 → 3.3: total 2, old 2, recent 0`。⇒ 故**「接缝旧」与「没有消费者」是两个独立的指标**，
第 1080 轮把二者混为一谈是**错的**——这与第 1091 轮 `Usage/` 的混淆是同一类错误：**一个数字承担了两个意思**。**

**⇒ 另有三处**我自己的**错误（都已随分支删除而不存在）：**
1. **重名**：我在 `Runtime/` 里又命名了一个 `twoSlopeRepair_preserves_other_segments`，
   与被消费的 `Lib` 定理**同名** ⇒ 短名冲突 `367 → 368`；正确做法是加层前缀（如 `artifact_…`）；
2. **一处转发未登记**（`twoSlopeRepair_sat_after_one`）；
3. **修复普查** `61 → 63` 未更新。

**⇒ 结论：本轮**没有产生新定理**，但产生了一个**比新定理更有用的否决**：
它把「为什么八阶段链引不到新线」从「也许是遗漏」变成了「**架构规则不允许**」。
⇒ 下一次要动这个方向，必须先在 `PLAN-STAGES` 里选定上面三条路之一，而不是再试一次同样的导入。**
### 3.58 **第 1098 轮：八阶段链表增加**活跃度**列，而它与**年龄**列**不一致****

**第 1097 轮测出：一个接缝即便获得新消费者，仍是 `old 2, recent 0`。**
**⇒ 故「年龄」量的是连接器**被写下**的时间，不是「是否有人用」。⇒ 第 1080 与 1097 两轮都把「old」读成了「断开」，这是错的。**

**⇒ `--provenance` 现在每个接缝**同时**打印：有多少连接器有**链内消费者**（剥注释、排除 `Usage/`、排除定义处——
与目标图的「链内」列**同一判据**），并**列出**没有的那些。**

**⇒ 它立刻显示出一件比「旧」更糟的事：**

| 接缝 | 活跃度 | 零消费者 |
|:--|:--|:--|
| **3.2 → 3.3** | **0/2** | `carrier_covers_whole_chain`、`extract_after_repair` |
| 3.3 → 3.4 | 2/5 | — |
| 3.4 → 4 | 1/4 | — |
| 1.4 → 3.2 | 2/19 | — |

**⇒ 故后三个接缝**不只是陈旧**：它们的连接器**在链内根本没有消费者**。**
**⇒ 两列**都为真且意思不同**——这正是必须并排打印、而不许用一个代表另一个的原因。**

**⇒ 已记录的**已知局限**（而不是隐瞒）：`Compose/Showcase/` 目前**仍算作链**，尽管它和 `Usage/` 一样是演示层。
⇒ 若将来判定展示层等同示例，这些数字会**进一步下降**——工具对**它当前划的边界**是诚实的，对**边界是否正确**不声称。**
### 3.59 **第 1099 轮：`3.2 → 3.3` 的 0/2 不是接线遗漏，而是**载体没有实例****

**上一轮的活跃度列显示：`3.2 → 3.3` 的两个连接器**零链内消费者**。⇒ 本轮测量它们的**原因**。**

#### 一、两个连接器，各自的原因

| 连接器 | 定义处 | 引用它的文件 |
|:--|:--|:--|
| `extract_after_repair` | `Runtime/RepairClosure.lean:90` | **只有它自己**（`:44` 还是文档提及） |
| `carrier_covers_whole_chain` | `Lib/Compiler/CarrierReproduction.lean:162` | **只有它自己** |

**⇒ 两者都不是「被示例消费」：它们**根本没有被任何代码消费**（连 `Usage/` 也没有）。**

#### 二、`extract_after_repair` 为什么无法被使用

**⇒ 它的签名是：**

```lean
theorem extract_after_repair (R : Lattice.Core.Repair Layer) (hSat : ∀ ls, R.Sat ls ↔ LayerSat cs ls)
    (ls : Layer) (h : R.μ ls = 0) (x : List Int) : AllSatisfied (extractLayer ls) x
```

**⇒ 故要**应用**它，必须先有一个**具体的 `R : Repair Layer`**。⇒ 而实测：**

| 文件 | 实例的载体 |
|:--|:--|
| `Core/RepairModule/Repair.lean` | `parityRepair : Repair ℕ` |
| `Core/RepairModule/RepairAtomicity.lean` | `Repair α`（由一个等价条件**构造**，不是具体载体） |
| `Core/RepairModule/RepairMultistep.lean` | `countdown : Repair ℕ` |
| `Core/RepairModule/SqDistRepair.lean` | `sqDistHalvingRepair : Repair ℕ` |
| `Core/RepairModule/RepairProduct.lean` | `repairProd : Repair (α × β)`（产品构造） |
| `Lib/Compiler/WriteBack.lean` | **`slopeRepair : Repair (ℕ → Segment)`** |
| `Lib/Linear/Multivar.lean` | `multivarRepair : Repair (ι → F)` |
| `Lib/Linear/Residual.lean` | `linearRepair : Repair ℚ` |
| `Primitives/MultistepLoop.lean` | `bidirRepair : Repair ℤ` |
| `Usage/Examples.lean` | `natRepair : Repair ℕ` |

**⇒ **没有一个是 `Repair Layer`**。**

**⇒ 故 `Runtime/RepairClosure.lean` 的四条定理（`repair_preserves_verdict`、`repair_makes_progress`、
`repair_terminates_at_sat`、`extract_after_repair`）是一个**参数化理论，而其载体没有实例**——
它们**永远无法被应用**，因此**不可能有消费者**。**

#### 三、这改变了问题的性质

**⇒ 上一轮我把它记为「也许接线遗漏」。⇒ 现在不是：`3.2 → 3.3` 的空洞是一个**具体缺口**——
**「主链的层载体（`Layer`）上没有修复实例」**。**

**⇒ 而修法也只有一条：**构造一个 `Repair Layer`**。⇒ 它的形态是可以定的：**
- `Sat ls` := 该层的所有权重与偏置都为零（**与输入无关**，故可作为修复判据）；
- `fix` := 逐个把非零坐标清零；
- `μ` := 非零坐标的个数；
- `atomic` := 计数为零 ⟺ 全零 ⟹ 对**任意**输入输出都为零。

**⇒ 若这样做成，则：**
1. `extract_after_repair` **第一次可被应用**（接缝首次有消费者）；
2. 并且可以证一条**新的**桥：`layerZeroRepair.Sat ls → ∀ x, AllZeroOutputs ls x`——
   **即「层被判据接受」⟹「对所有输入输出为零」**，这正是 `compileToLayer` 语义的**另一侧**。

**⇒ 这属于**补一个缺失的实例**，而不是「再写一条定理」；它同时服务三个目标（接缝、语义桥、条款 3.3）。
⇒ 下一轮执行它。若它在 `Layer` 上遇到技术困难（`List` 上的扫描与计数），就在分支上试，失败则退回并记录原因。**
### 3.60 **第 1100 轮：构造 `Repair Layer` 的一次**未完成尝试**（已退回，未合并）**

**上一轮确定了修法：构造一个 `Repair Layer`。⇒ 本轮在分支 `feat-layer-repair` 上写了约 120 行，
`lake build` **未通过**，三次修正后仍有三处失败。⇒ **分支已删除、文件已移除**，主树回到 `1d61ea5e`。**

#### 一、设计（仍然成立，供下一轮直接用）

```lean
def allZeroLayer (ls : Layer) : Prop := ∀ l ∈ ls, (∀ z ∈ l.w, z = 0) ∧ l.b = 0
def zeroLayer (ls : Layer) : Layer := ls.map (fun l => ⟨l.w.map (fun _ => 0), 0⟩)
noncomputable def layerZeroRepair : Repair Layer where
  Sat := allZeroLayer ; fix := zeroLayer ; μ := fun ls => if allZeroLayer ls then 0 else 1
```

**⇒ 判据**与输入无关**，且蕴含「对任意输入输出为零」——这正是 `AllZeroOutputs` 所需的另一侧。**

#### 二、三处**具体的**技术障碍（这是本轮真正的产出）

| # | 目标 | 障碍 |
|:--|:--|:--|
| 1 | `zeroLayer_eq_self : allZeroLayer ls → zeroLayer ls = ls` | 需要**逐点为零的列表 `map` 恒等**。⇒ `induction w` 会把 `hl`（其类型提到 `w`）**一并泛化**，导致类型失配；`clear hl` 后仍有 `application type mismatch`。**正确路径**：先把 `∀ z ∈ w, z = 0` 取成独立假设，再对 `w` 归纳，最后 `rw [hw, hb]`。 |
| 2 | `dot l.w x = 0`（全零权重） | 需对 `zip` 后的列表带**任意累加器**归纳；`0 + q.1*q.2 = 0` 这一步必须**先**用 `hq` 化简**再**用归纳假设。 |
| 3 | `decreases`/`atomic` 里的 `if` | `μ` 是 `if Sat then 0 else 1`，在 `show` 目标里**需要 `Decidable` 实例**；我加了 `classical` 仍报 `failed to synthesize`，说明问题不在实例而在**`show` 的类型与 `μ` 的定义不同形**。⇒ 应先 `unfold`/`change` 到 `μ` 的定义形，再 `rw [if_pos/if_neg]`。 |

**⇒ 三条都不是「不可做」，而是**我没在当轮做完**。⇒ 记录在此，避免下一轮从零重来。**

#### 三、本轮**没有**产生新定理，这本身要说清

**⇒ 一次失败的构造**不是**一次交付。⇒ 但它也不是零产出：**
1. 上轮的「缺口」论断被**具体化**成三条可执行的障碍；
2. 主树**未被污染**（分支删除、文件移除、工作区回到只剩他人改动）。

**⇒ 下一轮重试时，顺序应当是：先 (1) 的列表引理 → 再 (2) 的点积 → 最后 (3) 的 `if`，
每步单独 `lake build`，而不是一次写完 120 行再编译。**
### 3.61 **第 1101 轮：**第一个 `Repair Layer`** 已落地——但接缝仍未变活，原因已定位**

#### 一、做了什么（分支 `feat-layer-repair`，两提交，`--no-ff` 合并）

```lean
def allZeroLayer (ls : Layer) : Prop := ∀ l ∈ ls, (∀ z ∈ l.w, z = 0) ∧ l.b = 0
def zeroLayer (ls : Layer) : Layer := ls.map (fun l => ⟨l.w.map (fun _ => 0), 0⟩)
theorem map_zero_eq_self_of_all_zero / zeroLayer_allZero / zeroLayer_eq_self
theorem dot_eq_zero_of_pointwise_zero
noncomputable def layerZeroRepair : Repair Layer      -- **全树第一个**
theorem layerZeroRepair_sat_zero_outputs : allZeroLayer ls → ∀ x, AllZeroOutputs ls x
```

**⇒ **四步，每步单独编译**——这正是上轮失败的直接反例。⇒ 上轮我一次写完 120 行，四处错误同时在场。**

#### 二、三个技术点的**正确解法**（供复用）

1. **列表引理的假设必须先取出再归纳**：`induction w` 会把提到 `w` 的假设一并泛化；解法是先 `have hw0 := …` 再归纳。
2. **点积的全零证明要对 `w` 归纳，不是对 `zip` 后的表**：`List.mem_zip` 不是正确引理（名字不存在），
   而 `List.zip_cons_cons` + `foldl_cons` 足够。
3. **`if` 型测度**：`noncomputable def … where` 里 `if` 需要 `Decidable` ⇒ 在文件顶部
   `attribute [local instance] Classical.propDecidable`。**注意**：文档注释**不能**夹在 `attribute` 与声明之间
   （Lean 要求 docstring 紧邻声明），故 `attribute` 必须放在**所有** `where` 实例的文档之前。

#### 三、**普查的教训**：语法选择导致度量错误

**⇒ 我最初写成 `:= by classical exact {…}`：编译通过，但修复普查的模式是 `: Repair … where`，
⇒ 于是**本轮新增了一个实例，普查却把它记成 B 类（"提到 Repair 但没定义实例"）**。**
**⇒ 改为 `where` 形式后普查立刻正确：A 类 `11 → 12` 文件、`35 → 37` 声明。**
**⇒ 结论：当一个工具按语法模式度量时，**用规范形式书写本身就是度量的一部分**。**

#### 四、**接缝为什么仍然 0/2**（本轮测出、必须写清）

**⇒ `chain_connectors --provenance` 现在仍报：**
```
3.2 verify -> 3.3 repair  total 2  old 2  recent 0
live 0/2 connectors have a chain-internal consumer; NO CONSUMER: carrier_covers_whole_chain, extract_after_repair
```

**⇒ 因为我只**造了实例**，还**没有应用** `extract_after_repair`。⇒ 而应用它需要：**
```lean
(hSat : ∀ ls, R.Sat ls ↔ LayerSat cs ls)
```
**⇒ 我的判据是**「所有坐标为零**，而 `LayerSat cs ls` 是**「满足给定约束集 `cs`」**——**两者不等价**。**
⇒ 故 `extract_after_repair` **不能**直接套用；需要的是它的一条**兄弟定理**：
「全零层 ⇒ 提取出的符号满足**任何**约束」（因为零层的每个约束都是 `0 = 0`）。

#### 五、下一轮

**⇒ 写那条兄弟定理：**
```lean
theorem extract_after_zero_repair (ls : Layer) (h : allZeroLayer ls) (x : List Int) :
    AllSatisfied (extractLayer ls) x
```
**⇒ 它会让 `extractLayer` 与 `AllSatisfied` **首次被“修复后”语境消费**，并把 `LayerRepair` 与 `RepairClosure`
两个文件真正连起来（同属 `Runtime/`，**不违反 I4**）。**
**⇒ 而 `extract_after_repair` 本身的 0 消费者将**继续**——因为它的 `hSat` 前提在树里没有实例。
⇒ 若下一轮后它仍是 0，则正确结论是：**那条定理的前提过强，应被这条兄弟定理取代，并在文档里说明。**
### 3.62 **第 1102 轮：为全零实例写 `extract_after_repair` 的**兄弟定理****

**⇒ 上轮末尾定位了接缝 0/2 的精确原因：`extract_after_repair` 需要 `hSat : ∀ ls, R.Sat ls ↔ LayerSat cs ls`，
而全零判据与「满足给定约束集」**不等价**。⇒ 故它不是「缺消费者」，而是**前提过强**。**

**⇒ 本轮写它**能支持**的那一条：**

```lean
theorem extract_after_zero_repair (ls : Layer) (h : allZeroLayer ls) (x : List Int) :
    AllSatisfied (Lattice.Runtime.LoopClosure.extractLayer ls) x
```

**⇒ 理由是一行：全零层提取出的每个约束都是 `0 = 0`，故提取出的符号**对任意输入、任意约束集**成立。**
**⇒ 而这正是零实例**真正能支撑**的「修复后再提取」陈述。**

**⇒ 它还使 `extractLayer` 与 `AllSatisfied` **首次进入「修复后」语境**，并把 `LayerRepair` 与 `LoopClosure` 连起来
（同属 `Runtime/`，**不违反 I4**）。**

**⇒ 修复普查 `A_decls: 37 → 38`。**
### 3.63 **第 1103 轮：前提**减弱**再**使用**——`3.2 → 3.3` 接缝从 `0/2` 变成 `1/3`**

**⇒ `extract_after_repair` 要求 `hSat : ∀ ls, R.Sat ls ↔ LayerSat cs ls`，即**等价**。
**⇒ 而一个判据通常只能被证**蕴含**「零输出」，不能被证**等价**——这就是它在树里永远无法被应用的根因。**

```lean
extract_after_repair_weak (himp : ∀ ls, R.Sat ls → LayerSat cs ls) : AllSatisfied (extractLayer ls) x
layerZeroRepair_extract : 用 layerZeroRepair_sat_zero_outputs 作 himp 的实例
```

**⇒ `LayerSat cs ls` 定义上就是 `∀ x, AllZeroOutputs ls x`（**不查 `cs`**），恰是零实例的桥所证。
⇒ 故实例化只是**一次应用**，不是新的论证。**

**⇒ 实测效果——全链条表中**第一次**出现活跃度改善：**

| 接缝 | 前 | 后 |
|:--|:--|:--|
| `3.2 → 3.3` | total 2，**live 0/2** | **total 3，live 1/3** |

**⇒ 旧条 `extract_after_repair` 仍 0 消费者，而这是一个**已结论化**的事实**（不是待办）**：
它的等价前提在这里无法被满足。**

**⇒ 一条**前提阶梯**被**登记**而不是去重：三条结论相同、强度递减（等价 / 蕴含 / 实例）。
⇒ 重复门禁只比较结论，故基线 `194 → 196`，并把这条阶梯写进工具源码。
⇒ 删掉中间那条会**移走调用者唯一能履行的陈述**。**

**⇒ 一处我自己的错误：普查 `B_decls` 我在两次编辑中**改反了方向**（文件 61、实测 62），下一个提交把它改正。**
### 3.64 **第 1104 轮：名字**不得夸大内容**——`carrier_covers_whole_chain` 改名**

**⇒ 它其实是**三条事实的合取**（编译保语义、提取回程、修复终止），而它**自己的 docstring 早就说了实话**：
「抽象覆盖**两段加一个方向**」。—— 名字却说「整条链」。**

**⇒ 一个**夸大的名字**与一份夸大的文档是同一种缺陷**；而本树有门禁管后者，**没有**管前者。**
**⇒ 故本轮改名（定理 + 生成器 + 生成物）：**

```
carrier_covers_whole_chain  →  carrier_covers_two_segments_plus_one_direction
gov/gen_proof_chain.py 的标签「抽象覆盖全链」 → 「抽象覆盖两段加一个方向」
```

**⇒ 它仍然是**零链内消费者**，而这现在是**正确状态**：它是一个**总述**，故「没有消费者」是**它是什么**的性质，不是缺口。**

#### **`3.2 → 3.3` 接缝至此**完整交代****

| 连接器 | 状态 | 原因 |
|:--|:--|:--|
| `extract_after_repair` | **死** | 等价前提在此无法满足（第 1103 轮） |
| `carrier_covers_two_segments_plus_one_direction` | **死** | **它是总述，按构造即终态** |
| `extract_after_repair_weak` | **活** | 由全零实例实例化（第 1103 轮） |

**⇒ 该接缝里**没有任何名字再声称多于其证明所证**。⇒ 接缝数字现在是 `total 3 / old 1 / recent 1 / pending 1`、`live 1/3`，
且三个数的含义各自清楚。**
### 3.65 **第 1105 轮：把「死连接器」**分类**——以及分类器**自身的局限****

**⇒ 上一轮说下一步先分类再动手。⇒ 本轮用工具做了，而**工具的边界也被测出来了**。**

#### 一、全局数字（`chain_connectors.statements()` + 剥注释 + 排除 `Usage/`）

| 类（正则启发式） | 数量 | 含义 |
|:--|--:|:--|
| **D 需阅读** | **65** | 三条启发式都不匹配 |
| A 提到 `↔` | 27 | 可能前提可减弱，但 **`↔` 也可能在结论里** |
| **B 总述（顶层合取）** | **12** | 按构造即终态 |
| **C 参数化于 `Repair`** | **11** | 缺实例 |
| **合计** | **115** | |

**⇒ 所以「分类」这一步本身**不是决定**：65/115 落进「需阅读」。
⇒ 而 A 类的 27 个里，`carrier_covers_two_segments_plus_one_direction` 正是**结论含 `↔`** 的例子——
⇒ 故 **A 类不可信**，只能当**待读清单**，不能当裁定。**

#### 二、三个目标接缝的现状（本轮实测）

| 接缝 | 死连接器 |
|:--|:--|
| `3.2 → 3.3` | **0**（承接第 1103/1104 轮） |
| `3.3 → 3.4` | **3** |
| `3.4 → 4` | **0** |

**⇒ `3.3 → 3.4` 的三条：**
- `closed_loop_ends_verified_and_zero`（`Usage/Examples.lean` 所有）
- `one_round_is_one_repair_step`（同上）
- **`twoSlopeLoop_objective_vanishes`** —— **我自己第 1085 轮的定理**。

#### 三、关于**我自己那条**

**⇒ 它是 `closed_loop_reinject_vanishes` 在产物载荷上的实例，陈述「回路终点缺陷为零」。**
**⇒ 它在链内零消费者——因为没有下游阶段**读取缺陷值**。**
**⇒ 按本轮的分类，它属于**B 类（终态）**：它是一个**结论**，不是一步。⇒ 正确处置是**登记为终态**，
而不是给它找一个装出来的消费者。**
**⇒ 而这也是**第一次**我发现自己的承重定理落进这张表——记录比辩护有用。**

#### 四、本轮的方法结论

**⇒ 正则分类只能**缩圈**，不能**裁定**。⇒ 想真正裁定，必须读陈述——而 115 条里 65 条要读，
⇒ 故**逐条做不是一轮的事**，应当**按接缝分批**：一次只吃一个接缝的死连接器，读完给出三选一
（登记终态 / 减弱前提 / 补实例）。

**⇒ 下一轮按这个粒度做 `3.3 → 3.4`（3 条，最小、且包含我自己的那条）。**
### 3.66 **第 1106 轮：示例的定理**不是**链的连接器——`Usage/` 也从**生产者**端被排除**

**⇒ 第 1091 轮让 `Usage/` **不再算目标载体的消费者**；而连接器扫描**仍把它算作链事实的生产者**。
⇒ 后果可测：**定义在 `Usage/Examples.lean` 的 4 个连接器被报成「死」**，而 `3.3 → 3.4` 那三条里**有两条正是它们**。
⇒ 故那个「3 死」其实是「**2 个度量假象 + 1 个真问题**」。**

**⇒ 修正后两个接缝的读数是：**

| 接缝 | total | live | 唯一的死 |
|:--|--:|:--|:--|
| `3.3 → 3.4` | 3 | **2/3** | `twoSlopeLoop_objective_vanishes` |
| `3.4 → 4` | 2 | **1/2** | 同上 |

**⇒ 相邻接缝上**唯一**剩下的死连接器是**我自己的**，而读它就能裁定：**
**⇒ 它是 `closed_loop_reinject_vanishes` 的一行实例（「回路终点缺陷为零」）。树里没有下游读取缺陷值
⇒ 故它是该接缝的**结论**，不是缺失的一环。属于**终态**。**

#### 一次**被放弃的**改动，以及为什么放弃

**⇒ 我本想在同一提交里加 `TERMINAL_CONNECTORS` 登记表 + 门禁。⇒ 但它**改坏了文件缩进**（`IndentationError`）。
⇒ 我没有去修补一个已坏掉的扫描器，而是**从 HEAD 还原**、只重新应用**已通过验证**的那一部分。
⇒ 登记表属于**它自己的一轮**，带自己的构建。**

**⇒ 这又是「不要一次改两件事」的同一条纪律——第 1100/1101 轮的教训在工具层复现了一次。**
### 3.67 **第 1107 轮：死连接器必须**登记理由**，或落在**只减不增的预算**里**

**⇒ 一个没有链内消费者的连接器，要么是 (a) **终态结论**（下游不读它），要么是 (b) **缺口**。⇒ 表里两者长得一样，
故每一轮都要重新发现哪些 0 是发现。⇒ 本轮把它做成**状态**。**

**⇒ 新增 `TERMINAL_CONNECTORS`，先登记三条（理由都**已由测量确立**）：**

| 名字 | 理由 |
|:--|:--|
| `twoSlopeLoop_objective_vanishes` | 回路终点缺陷为零；树里没有下游读取缺陷值 |
| `extract_after_repair` | 其**等价前提**在此不可达（第 1103 轮） |
| `carrier_covers_two_segments_plus_one_direction` | **总述**，按构造即终态（第 1104 轮） |

**⇒ 并加**预算**（因为要求一次登记全部是不可采纳的）：实测相邻接缝上**未登记**的死连接器为 **69**
（`1.4 → 3.2` 一条就有 17；写十七个没读过的理由是这些纪律明确禁止的编造）。**
**⇒ 故 `UNREGISTERED_BUDGET = 69`：使状态可见且**单调**——每轮裁定一个接缝就降低；**永不增长**。**

**⇒ **双向验证（不是声称）**：**

| 情形 | 结果 |
|:--|:--|
| 恰在预算（69） | **exit 0** |
| 预算改为 68 | **exit 1**，并打印 "The budget grew: adjudicate a seam or register a reason" |

**⇒ 分四步构建、每步一检查**（登记表 → 门禁 → 登记前三条 → 预算），因为第 1106 轮一次性做同样的改动**把文件改坏了**。

**⇒ 这条线与目标图那条（第 1091–1093 轮）现在讲**同一种语言**：链内消费者 = 0 ⇒ 必须登记，或落在预算里。**
### 3.68 **第 1108 轮：裁定 `1.1 → 1.2`——预算 `69 → 64`**

**⇒ 先按**接缝**测量未登记死数，挑**最小**的做：**

| 接缝 | 未登记死数 |
|:--|--:|
| **1.1 → 1.2** | **4**（最小） |
| 1.2 → 1.3 | 7 |
| 1.4 → 3.2 | 17 |
| 1.3 → 1.4 | 41 |
| 3.2 → 3.3 / 3.3 → 3.4 / 3.4 → 4 | **0 / 0 / 0** |

**⇒ 逐条读那四条，**全是终态**，各有具体理由：**

| 连接器 | 理由 |
|:--|:--|
| `E1Bridge_cons` | 桥的 cons 分支的 `rfl` 定义式展开 |
| `E1BridgeNoSep_cons` | 丢 `sep` 的桥的 `rfl` 定义式展开 |
| `E8_source_count_exactly_one` | **关于树的断言**（有见证地存在一处来源；1.3 上不存在） |
| `d41_L1Bridge_not_injective` | **否定**——分离定理按性质即终态 |

**⇒ 登记而非删除：每一条都是**真陈述**，其职责是**作为该断言**，而不是喂给某一步。**

**⇒ 预算 `69 → 64`，而测量顺带**纠正了我自己的算术**：我以为会到 65（登记了四个名字），
但 `E8_source_count_exactly_one` **同时落在两个接缝上**，在 69 里被算了两次。**
**⇒ 故预算取**实测值**，不取预测值。**

**⇒ 双向验证：`64` ⇒ exit 0；`63` ⇒ exit 1。**
### 3.69 **第 1109 轮：裁定 `1.2 → 1.3`（6 条）+ 我自己的那条——预算 `64 → 57`**

**⇒ 本轮读完全部 6 条，并加上 `1.4 → 3.2` 里属于我的 `extract_after_zero_repair`。**

#### 一、这条接缝的**实质发现**：其中三条是**非依赖见证**

**⇒ `e2e_vacuous_composition`、`e2e_extract_hypothesis_is_not_load_bearing`、`extract_to_weights`
陈述的是**同一个编译保语义事实**，但各带一个**未使用**的参数（一个 token 列表，或一个 `Extract` 假设）。**
**⇒ 它们的**名字就把这件事说出来了**（vacuous / not load bearing）。**
**⇒ **记录「这一跳不查某物」就是它们的内容**——故删除它们等于删除一个断言，而不是删除一份副本。**

**⇒ 另外三条：`e2e_contribution_of_L1L2`（关于复合的断言）、`e2e_loss_compound`（存在性合取：两种损失会叠加）、
`E8_load_bearing_summary`（哪些映射会合并、哪些不会）。**

#### 二、**我自己的那条**

**⇒ `extract_after_zero_repair`（第 1102 轮）死在 `1.4 → 3.2`。⇒ 登记为终态，不作辩护：
树里没有人读取「全零层提取出的约束被满足」这一事实。**

#### 三、预算

**⇒ `64 → 57`，仍然取**实测值**（登记表 +7，计数恰好 −7）。⇒ 双向验证：`57` ⇒ 0；`56` ⇒ 1。**

**⇒ 递减链至此：`69 → 64 → 57`。⇒ 每一步的减量都可核对，且每一步的理由都是**读出来的**，不是猜的。**
### 3.70 **第 1110 轮：按**结论形状**裁定 `1.4 → 3.2`（16 条）——预算 `57 → 33`**

**⇒ 读了十六条，并按**陈述内容**（不是名字）分成五组：**

| 组 | 条数 | 成员 | 理由 |
|:--|--:|:--|:--|
| **重述** | 5 | `compile_extract_end_to_end`、`_semantics_closed`、`roundtrip_preserves_semantics`、`extract_compile_semantically_equal`、`satisfies_iff_extractLayer` | 各自是**同一条往返语义引理**在拥有该定义的模块处被复述；一条理由覆盖五条，且本轮**核对了结论确实是那条引理**（不只是名字像） |
| **成对** | 2 | `rt1_is_instance_of_branch_B`、`rt1_matches_existing` | **结论相同**，一者包装另一者，使该等价能以 vacuity 论证所用的名字被引用 |
| **否定** | 2 | `activated_extract_cannot_repair`、`not_agrees_of_disagreement` | 按性质即终态 |
| **总述** | 5 | `honesty_register`、`structured_init_complete`、`parse_chain_summary`、`models_structure`（一个方向）、**我自己的 `layerZeroRepair_extract`** | 总述/方向，按构造即终态 |
| **梯子** | 2 | `approx_ladder_forward`、`roundingLadder_forward` | 各一个方向的前向事实 |

**⇒ 预算 `57 → 33`（实测：登记表 `14 → 30`，死数 `57 → 33`）。⇒ 双向验证：`33` ⇒ 0；`32` ⇒ 1。**

#### 一次**失败后还原**的编辑

**⇒ 首次尝试用 `repr()` 生成重复理由再替换引号，产生 `SyntaxError`（`"tree"s`）。**
**⇒ 处理方式：**从 HEAD 还原**，保留 `repr` 的引号原样重做——不是给坏文件打补丁。**

**⇒ 预算递减链：`69 → 64 → 57 → 33`。⇒ 四步，每步的理由都是读出来的，减量都可核对。**
### 3.71 **第 1111 轮：「本文件内被使用」不等于「死」——连接器度量也需要第 1092 轮的区分**

**⇒ 在**读任何陈述之前**先测量了相邻接缝上 33 条未登记连接器的分布：**
- **9 条在**自己的文件内**被使用**（`extractWith_absent` 被同文件三行之后的 `extractWith_spec` 消费；
  `extractWith_overwrite` 被 `_overwrite_footprint` 消费……）；
- **24 条**哪里都没被用过。

**⇒ 这是目标图第 1092 轮那个混淆在**上一层**的重演：`chain_users` **按设计排除定义文件**
（一条定理不消费自己），而这同时**掩盖了「定义处自己的文件在用」**。
⇒ 新增 `used_in_place()`，并在**活跃度行**与**门禁**两处都应用。**

**⇒ 实测效果：**

| 指标 | 前 | 后 |
|:--|--:|--:|
| 相邻接缝未登记 | **33** | **24** |
| `1.1 → 1.2` 活跃度 | — | **5/6** |
| `1.3 → 1.4` 活跃度 | — | **22/54** |

**⇒ 预算取**实测 24**，双向验证（24 ⇒ 0；23 ⇒ 1）。**

**⇒ 这同时**更正了本轮的初始计划**：我本打算把六条 `extractWith_*` 都当死的来写理由，
而其中**两条正是消费另外四条的那个摘要**。⇒ 若按原计划做，我会写下六条**互相矛盾**的理由。**
### 3.72 **第 1112 轮：裁定三条**真死**的 `extractWith_*`——预算 `24 → 21`**

**⇒ 第 1111 轮已确立：六条 `extractWith_*` 里三条**在文件内被使用**（摘要消费基引理）。⇒ 剩下三条**哪里都没用**，
而它们的陈述分成**一条基事实 + 两条摘要**：**

| 名字 | 类别 | 理由 |
|:--|:--|:--|
| `extractWith_collision` | **基事实** | 一条**方程**：两个张量共用 id 时，读某一位置返回另一个 id 的单元 |
| `extractWith_overwrite_footprint` | **摘要** | `extractWith_overwrite` 与 `_overwrite_local` 的**合取** |
| `extractWith_spec` | **摘要** | `extractWith_compileWith` 与 `extractWith_absent` 的**合取**——一对算子的**规格** |

**⇒ 三条都不是「一步」：两条是已登记引理的摘要，一条是没有任何东西会复合的情形方程。**
**⇒ 登记而非删除：**规格**与**情形方程**本身就是断言。**

**⇒ 预算 `24 → 21`（实测：登记 `30 → 33`）。⇒ 双向验证：`21` ⇒ 0；`20` ⇒ 1。**

**⇒ 预算链：`69 → 64 → 57 → 33 → 24 → 21`。⇒ 六步，每一步的减量都有**读过的理由**支撑。**
### 3.73 **第 1113 轮：`compile_extract_*` 三条都是**往返对**的重述——预算 `21 → 18`**

**⇒ 三条都指向**同一对**（`compileToLayer` / `extractLayer`），且各自是它的摘要或重述：**

| 名字 | 类别 | 理由 |
|:--|:--|:--|
| `compile_extract_invertible_pair` | **摘要** | `LeftInverse` 与 `RightInverse` 的**合取**，由已陈述各方向的两条引理组装 |
| `compile_extract_mutually_refines` | **摘要** | 两条 `fibreRefines` 的**合取**（互为加细）——往返在纤维层面的结构摘要 |
| `compile_extract_weight_side` | **重述** | 零输出经「编译再提取」保持不变，靠 `compileToLayer_extractLayer` 改写得到 |

**⇒ 第三条是**权重侧的重述**，而这是**该有的**：一个用权重词汇思考的读者，
不应为了用往返定理而切换词汇。**

**⇒ 预算 `21 → 18`（实测：登记 `33 → 36`）。⇒ 双向验证：`18` ⇒ 0；`17` ⇒ 1。**

**⇒ 预算链：`69 → 64 → 57 → 33 → 24 → 21 → 18`。**
### 3.74 **第 1114 轮：五个名字，**一个方程**——预算 `18 → 14`**

**⇒ 读了「逆/不动点」族五条，其中**四条是同一内容的四种写法**：**

| 名字 | 形式 |
|:--|:--|
| `extractLayer_leftInverse` | `Function.LeftInverse extractLayer compileToLayer` |
| `extractLayer_rightInverse` | `Function.RightInverse extractLayer compileToLayer` |
| `rt1_leftInverse` | `extractLayer_compileToLayer`（为 vacuity 文件**再导出**） |
| `compiled_roundTrip_fixed` | 原始方程 `compileToLayer (extractLayer ls) = ls` |

**⇒ 每种形式都因**不同的消费词汇**而存在，故四条都**该保留**——但它是**一个事实**，
而登记里**如实这么说**，不把四个名字装成四个发现。**

**⇒ 第五条 `compiled_roundTrip_fixed_iff` 是唯一**增加信息**的：对单层而言，「是不动点」⟺「是某约束的像」。**
**⇒ 它是**刻画**而非**改拼**。**

**⇒ 这也是**陈述重复门禁看不见**的一类近乎重复：四种形式在语法上不同（`Function.LeftInverse` vs 一个方程），
故按结论文本分组会漏掉它们。⇒ 这条观察就活在这张登记表里。**

**⇒ 预算 `18 → 14`（实测：登记 `36 → 41`）。⇒ 双向验证：`14` ⇒ 0；`13` ⇒ 1。**

**⇒ 预算链：`69 → 64 → 57 → 33 → 24 → 21 → 18 → 14`。⇒ 剩 14 条，两轮可清。**
### 3.75 **第 1115–1116 轮：最后 14 条清空——预算降到 **0****

**⇒ 两轮做完：**
- **第 1115 轮**：回路性质族 5 条（4 幂等 + 1 局部性），预算 `14 → 9`；
- **第 1116 轮**：最后 9 条，预算 `9 → 0`。

#### 最后 9 条的类别

| 类别 | 条数 | 成员 |
|:--|--:|:--|
| **摘要**（顶层合取） | 4 | `compileWith_roundtrip`、`recover_is_load_bearing`、`s02_list_realization_witness_is_mechanical`、`layer_partial_section_never_fails` |
| **恢复** | 1 | `reinject_restores`（往返在**数据词汇**里的说法） |
| **往返推论** | 2 | `compiled_weights_extract`、`extract_witness_is_preimage` |
| **幂等** | 1 | `verify_loop_stable_on_image`（`closed_loop_idempotent` 在另一侧） |
| **刻画** | 1 | `unfaithful_iff_extract_ne`（命名「不忠实」**是什么**） |

#### 预算到 0 的含义

**⇒ `UNREGISTERED_BUDGET = 0` 是这条规则的最严形式：**相邻接缝上**每一条**死连接器都必须带书面理由。**
**⇒ 双向验证：**

| 情形 | 结果 |
|:--|:--|
| 在 0 | **exit 0**（无未登记） |
| 删掉一条登记 | **exit 1** + "The budget grew: adjudicate a seam or register a reason" |

#### 预算的完整历史（**每一步都是测出来的，不是预测的**）

```
69（建立） → 64（1.1→1.2） → 57（1.2→1.3） → 33（1.4→3.2） → 24（度量修正：在文件内使用 ≠ 死）
→ 21（extractWith） → 18（compile_extract） → 14（逆族：五个名字一个方程） → 9（回路族） → 0（本轮）
```

**⇒ 共 **55 条登记**，每一条的理由都是**读过陈述与证明形状之后**写的。**

**⇒ 这条线（度量诚实性）至此**收束**：目标图（14 条款 / 55 载体）与八阶段链（7 接缝 / 连接器）**讲同一种语言**：
**「不被消费」必须带理由，或落在只减不增的预算里；而预算是**0**。**
### 3.76 **第 1117 轮：条款 5（符号引擎 / CIC）的实测——它不是孤岛**

**⇒ 上一轮我猜「条款 5 可能像 `Lib/Compiler` 那样是孤立的子链」。⇒ 测量**否证了**这个猜测。**

#### 一、规模与形状

| 项 | 值 |
|:--|:--|
| `Core/CIC/*` 文件数 | **90** |
| 其中 theorem+lemma | **306** |
| 条款 5 的载体 | `HasType`（跨文件 14 / 同文件 21，**强**）、`hasType_to_hasTypeW`（**死**，已登记终态） |

#### 二、**决定性的分离与连接**

**⇒ 在 `Core/CIC/*` 内部，对这五个名字的引用是**零**：**

```
compileToLayer 0 · extractLayer 0 · IRWeights 0 · Layer 0 · ConstraintSet 0
```

**⇒ 故 CIC 核心与权重世界**完全分离**——这正是「不另设中间层」的字面实现：符号引擎不认识权重。**

**⇒ 而桥在 `Runtime/`，方向是**单向**的（Runtime 导入 CIC）：**
`Runtime/CICToConstraint.lean`、`CICToConstraintSet.lean`、`DataToConstraint.lean`、
`EndToEndComposite.lean`、`EngineFirst.lean`、`EngineReduces.lean`、`EngineSemantics.lean`。

#### 三、贯穿定理存在，**而且被消费**

```lean
cic_loop_reaches_weight (ctx) (x) :
    (∀ t ∈ ctx, ∀ v, cicToConstraint t = some v → VectorConstraintSat v x)
      ↔ AllZeroOutputs (compileToLayer (cicCtxToConstraintSet ctx)) x
```
**⇒ 一条定理把**CIC 的类型约束**与**编译后的层输出**连起来。**

**实测其链内消费者：**

| 定理 | 链内消费者 | 判断 |
|:--|--:|:--|
| `cic_loop_reaches_weight` | **2**（`DataToConstraint`、`EndToEndComposite`） | **活** |
| `data_to_weight_iff` | **1**（`TypedNumericAlignment`） | **活** |
| `symbolToWeight_correct` | **20** | **极强** |
| **`data_to_weight_honest`** | **0** | **终态（收官定理）** |

**⇒ 故条款 5 **有端到端证据**：数据语料 → 约束 → CIC → 层 → 零输出。
⇒ 而那条**收官定理** `data_to_weight_honest`（「覆盖语料 + 零宽样本 ⟹ 编译层输出为零」）
**没有任何消费者**——它是**整条链的终点**，故这符合「终态」而非「缺口」。**

#### 四、这条线的结论

**⇒ 条款 5 **不需要工程**。⇒ 需要做的只有一件：把 `data_to_weight_honest` 作为**收官定理**登记，
⇒ 并注明「它的消费者按定义在链外」——与条款 2.2 同一处置。**

**⇒ 而更重要的一句：**我上一轮的猜测是错的**。⇒ 若按猜测去「修孤岛」，会去动一个本来就连好的子系统。**
**⇒ 这是本会话第 **5 次**「假设缺口」被测量推翻（前四次：第 76/78/79 轮与第 1090 轮）。**
### 3.77 **第 1118 轮：按**条款**的端到端证据表——35 个载体 / 27 个被链消费**

**⇒ 用 `CLAUSES` + 剥注释语料 + 三分类（链内 / 仅本文件 / 全无）逐条核对：**

| 条款 | 载体 | 链内 | 仅本文件 | 全无 |
|:--|--:|--:|--:|--:|
| 1.1 data → token | 2 | **2** | 0 | 0 |
| 1.2 token → symbol | 2 | **2** | 0 | 0 |
| 1.3 symbol → weight | 4 | **4** | 0 | 0 |
| 1.4 weight → symbol | 3 | **3** | 0 | 0 |
| 2.1 约束损失 | 2 | 1 | 1 | 0 |
| **2.2 数据合成** | 2 | **0** | **2** | 0 |
| 2.3 结构化初始化 | 3 | **3** | 0 | 0 |
| 3.1 提取 | 2 | **2** | 0 | 0 |
| 3.2 验证 | 3 | **3** | 0 | 0 |
| **3.3 修复** | 3 | **0** | **2** | 1 |
| 3.4 再注入 | 2 | 1 | 0 | 1 |
| 4 闭环 | 4 | **3** | 0 | 1 |
| 5 符号引擎 | 2 | 1 | 0 | 1 |
| 8 Lean 保证 | 2 | **2** | 0 | 0 |
| **合计** | **35** | **27** | **5** | **4** |

**⇒ **27/35 = 77%** 的载体被链内消费；**8 个条款**的全部载体都被链消费。**
**⇒ **4 个「全无」全部已在 `END_OF_CHAIN` 登记理由**；**5 个「仅本文件」** 是本轮新增的 fifth（`layerZeroRepair`）。

#### 本轮的一处**实质**修正

**⇒ 表格发现：条款 3.3 的两个载体**都是演示材料**（`ℕ` 上的 `Repair` 及其收敛），
而**真正的**修复实例——第 1101 轮造的 `layerZeroRepair`（主链 `Layer` 载体上的）——**根本没被登记为该条款的载体**。**
**⇒ 已登记。⇒ 这**不改变**它的「仅本文件」状态（它被同文件的 `layerZeroRepair_extract` 使用），
但使该条款的证据**指向链真正修复的那个东西**。**

#### 结论：只有 **2.2** 与 **3.3** 没有链内消费者，而两者原因不同

| 条款 | 原因 |
|:--|:--|
| **2.2** | 判据是**调用者提供的数据函数**、下游（训练）**按定位在框架外**——接口性条款（第 1090/1092 轮定论） |
| **3.3** | 修复**应用**与**结论**都在同一个文件内完成（`layerZeroRepair` 被 `layerZeroRepair_extract` 消费）——**自足**，非缺失 |

**⇒ 故「条款有端到端证据」这件事，在本树里是**可核对的**：27/35 有，且余下 8 个各有不涉及「缺失」的理由。**
### 3.78 **第 1119 轮：为一个**没有入口**的层写入口**

**⇒ 本会话在 `Lib/Compiler` 与 `Runtime/` 下新增约 40 个文件，而它们**没有一处是**入口**：
⇒ 唯一记录它们立了什么的地方是 `PLAN-STAGES`，而那是**过程日志**——读者要靠读日记才能找到结果。**

**⇒ 新文件 `DELIVERY-COMPILER-LAYER.md`（一页，6325 字节），只写**可核对的结论 + 承载它的定理**：**

| 节 | 结论 | 承载定理 |
|:--|:--|:--|
| 2.1 | 一条界覆盖**所有度数**，常数 `d(d−1)/8`；且**重推出**前三轮手工推的 `1/4`、`3/4`、`3/2` | `pow_uniform_bound`、`general_formula_matches_hand_derived` |
| 2.2 | 任意度数**可被选中**；`t⁵`、`t¹⁰` 从未被单独处理而直接落下 | `quintic_lands`、`quintic_bound`、`tenth_power_bound` |
| 2.3 | 两套实现是**同一推广的两个截面**，且推广**被新线消费** | `realLayer_ofInt_out`、`gridEval_eq_realLayer_out` |
| 2.4 | 全树**第一个** `Repair Layer`，使 `RepairClosure` 四条首次可被应用 | `layerZeroRepair`、`layerZeroRepair_sat_zero_outputs` |
| 2.5 | 产物载荷上的闭环，且**轮数有锐界**（一轮即够） | `twoSlopeLoop_objective_vanishes`、`_sat_after_one`、`_ends_sat_in_two` |

**⇒ 并写清三件**不该被当成承诺**的事：§3「不提供训练/引擎/框架/统一判据」、
§5「`Runtime` **不能**导入 `Lib`（I4）」、§6「三条重测命令；**与工具不符时以工具为准**」。**

**⇒ 已登记进 `README.md` 的入口列表（与 `USAGE` / `PROOF-DEBT` / `MACRO-STATUS` 并列）。**

**⇒ 这是「**该分文件的分文件**」的具体落实：一页入口，指向约 40 个文件的结论。**
### 3.79 **第 1119 轮：独立复核入口文档——它引用了一个**不存在的标识符****

**⇒ 复核方式：**不读自己的散文**，只用工具。⇒ 从 `DELIVERY-COMPILER-LAYER.md` 抽出**每一个**反引号标识符，
逐个对照树里的声明。**

**⇒ 第一次结果：24 个标识符，其中 `evaluate` **在任何地方都没有声明**。**
**⇒ 这正是 `check_doc_names.py` 要在 Lean docstring 里抓的缺陷，被我在自己的**入口文档**里复制了一遍：
**一个落在「unknown identifier」上的引用。****
**⇒ 另两个（`AnalyticRow`、`CapabilityRow`）看似缺失，只是因为我第一遍的扫描器只收 theorem/lemma；
换成覆盖 `def`/`structure`/`inductive` 的扫描后，它们都在。**

**⇒ 修正：**
1. §3 改成真话——**唯一**的可求值入口是 `EvaluatedArtifact.evalAt`，**没有第二个求值函数**；
2. 不再把 `fix` 当顶层声明反引号（它是结构字段），改写成散文里的 `Repair.fix`。

**⇒ 修正后（覆盖面更全的扫描器）：**

| 检查 | 结果 |
|:--|:--|
| 反引号标识符 | **21** |
| 其中不是声明 | **0** |
| 引用的定理名 | **22** |
| 其中缺失 | **0** |
| §4 条款归属 | 四个载体**全部**如页面所述 |

**⇒ 结论：入口文档现在**每一句都可被引用到一处声明**。⇒ 而这是靠**工具**发现的，不是靠重读。**
### 3.80 **第 1120 轮：语句级核对 + 把「引用可解析」做成**工具****

#### 一、语句级核对（存在 ≠ 内容相符）

**⇒ 上一轮的复核只证明「定理**存在**」。本轮核对**内容**：把每条结论的**关键算子**与对应定理的**实际陈述**做比对。**

| 项 | 结果 |
|:--|:--|
| 核对的定理陈述 | **18** |
| 与文档不一致 | **0** |

**⇒ 例：`pow_uniform_bound` 的陈述里确实有 `d * (d - 1)`、`8`、`(1 / (n : ℝ)) ^ 2`、`x ^ d`；
`quintic_lands` 确实以 `some (powAnalyticRow 5` 为结论；`twoSlopeLoop_run_components` 确实逐分量为 `fix^[k]`。**

#### 二、把「引用可解析」做成工具：`gov/check_delivery_claims.py`

**⇒ 第 1119 轮那处假引用修好之后，**仪器仍然缺失**。⇒ 本轮补上。**

**⇒ 它把文档里每个反引号标识符对树里的声明解析（`def`/`theorem`/`lemma`/`abbrev`/`structure`/`inductive`/`class`，
剥注释），路径名走白名单。⇒ 并在**自己的 docstring 里写明它不检查什么**：它不判断**关于该声明的断言是否为真**。**
**⇒ 存在与内容是**两个问题**，第 1120 轮单独测了内容（18 条，0 处不一致），其期望算子在那一轮记录，不在工具里。**

**⇒ 双向验证：**

| 情形 | 结果 |
|:--|:--|
| 真文档 | 20 个标识符，0 未解析 ⇒ **exit 0** |
| 临时副本注入 `evaluate_this_nothing` | **exit 1** |

**⇒ 已写进入口文档自己的 §6，故**文档现在点名了守护它的仪器**。**

#### 三、门禁逼出的两处收尾

1. **§6 不再把**它正在讨论的那个不存在的名字**加反引号**——**工具抓到了我自己的散文**；
2. `CONVENTIONS.md` 的 gov 脚本计数 `164 → 165`。

**⇒ 注意第 1 条：新工具在**第一次运行**就抓到了作者在**解释这个缺陷时**又犯的同一个缺陷。**
**⇒ 这比任何「我会小心」的承诺都更有说服力。**
### 3.81 **第 1121 轮：一次**自查**——我的提交习惯扫进了一份共享文档，以及三个「门禁数」**

#### 一、自查对象：我是否提交过**他人的**改动？

**⇒ 发现：`MACRO-COGNITION.md` 出现在**我最近 6 个提交**里**（`0e830281`、`5bd234be`、`d2164d30`、`6823cf5f`、`5a000a1d`、`78fdbe93`），
而该文件在**他人未提交改动**清单里。**

**⇒ 逐个量化后结论是**否**：六次的改动都是 **2 行（一行增、一行删）**，且**全部是计数行**（`合计：1111/1112 模块…`）。**
**⇒ 根因已定位：`gov/sync_counts.py` **会写**该文件的计数行**——故那一行是**我的工具生成的**，不是别人的手写。
⇒ 我加它的原因是我**每轮都用一个固定的文档清单**去 `git add`，而那张清单里包含它。**

**⇒ 但习惯仍然不安全：**若那次他人的手写改动恰好也在同一文件里，`git add` 会一并暂存。**
**⇒ 新规则（立即生效）：`git add` 之前必须看 `--numstat` 与 diff，只加**我确实编辑过**的文件。**
**⇒ 我不能改自己的历史，但可以不让它再发生，并把规则写在这里。**

#### 二、第二个发现：三个「门禁数」在流通

**⇒ `verify_all --fast` 实际输出：**

```
registered           : 126 checks = 105 gating + 21 reporters
gating checks passed : 94
```

**⇒ 而文档里写的是：**
- `DELIVERY.md`：「126 项检查，**99** 个门禁」——**陈旧**（已改为 105 + 21）；
- `MACRO-COGNITION.md`：「126 项检查（**99** 门禁 + 21 报告）」——**陈旧且自己算不平**（99+21=120≠126）。

**⇒ 后者是**他人所有**，本轮**未动**——只记录。**
**⇒ 而 94 是 `--fast` 下通过的门禁数（105 − 11 个 reactivity），它是**运行结果**而非**登记数**，
故「94」与「105」都对，但**必须说清是哪一个**。**

**⇒ 三个数字各有其义：126 = 105 + 21（登记）；105 = 门禁总数；94 = `--fast` 下通过数。**

#### 三、为什么 `check_usage_claims` 没抓到

**⇒ 它核对的文档清单是 `USAGE` / `STATE-FINAL` / `CONVENTIONS` / `DELIVERY`，而「99 门禁」这件事**不在它的检查式**里。**
**⇒ 故这是一个**真实的检查缺口**：一个可核对的数字（门禁数）没有任何门禁在核对。**
**⇒ 记入待办：把它加进 `check_usage_claims` 的可测清单——但需先决定**以 105 还是 94 为准**（答案：两个都要，但要标注语境）。**
### 3.82 **第 1122 轮：门禁数终于**有了检查器**——两份文档差了六**

**⇒ 第 1121 轮发现「门禁数」没有任何东西核对它。⇒ 本轮在 `check_usage_claims` 里加**三条带标签**的断言，
每条都从 `verify_all` **自己的登记表**（`CHECKS`、`REPORT_ONLY`）测量，而不是从常量：**

| 断言 | 实测 | 结果 |
|:--|--:|:--|
| `DELIVERY: verify_all total checks` | **126** | ok |
| `DELIVERY: verify_all gating checks` | **105** | ok |
| `DELIVERY: verify_all reporters` | **21** | ok |

**⇒ 之所以分开标三条：流通的是**三个不同**的数字——126（登记总数）、105（门禁）、94（`--fast` 下**通过**的门禁数，
即 105 − 11 个 reactivity）。⇒ 最后一个是**运行结果**，取决于模式，故**故意不**作为文档断言：
**「文档断言」与「运行结果」是两类不同的陈述。****

**⇒ 双向验证：把 105 改成 104 ⇒ **exit 1**（"1 claim disagrees"）；恢复 105 ⇒ **exit 0**。**

#### 两处机械失败（都已修，且修完**逐条**重跑）

1. **第一版正则没有捕获组** ⇒ `findall` 返回整段匹配 ⇒ `int('126 项检查')` 抛错；
2. **两条正则写成双反斜杠 `\\u`** ⇒ 匹配的是**字面文本** `\u9879` 而非汉字。

**⇒ 教训与第 1111/1120 轮一致：**一次只改一处、每次改完立刻用工具确认**，而不是攒完再跑。**

#### 这条「一个数字一个意思」的线，五次治疗到此

| 轮 | 病灶 | 治法 |
|:--|:--|:--|
| 1090–1093 | 「跨文件引用」= 被用 vs 被示例提及 | 加**链内**列 + 强制登记 |
| 1098 | 「接缝旧」vs「无消费者」 | 加**活跃度**列 |
| 1106 | 「连接器」= 链事实 vs 示例演示 | 排除 `Usage/` 生产端 |
| 1111 | 「本文件内使用」= 死 vs 在用 | `used_in_place` |
| 1121–1122 | 「门禁数」= 登记 vs 通过数；且无人核对 | **三条带标签断言 + 双向验证** |
### 3.83 **第 1123 轮：把「**他人所有但已知陈旧**」做成机器可读的登记——而**不动其文件****

**⇒ 第 1121 轮发现 `MACRO-COGNITION.md` 写着「99 门禁 + 21 报告」，而 `verify_all` 打印 **105 门禁 + 21**。
⇒ 该文件**属他人**，故正确处置既不是改它，也不是把这件事留在某一轮的笔记里。**

**⇒ 新增 `gov/other-owned-stale.txt`，每行一条：**

```
file | stale text that is still present | the value measured by the toolchain
```

**⇒ 与 `check_delivery_claims.py` 的新模式 `--foreign`：逐条报告 **STILL STALE** 或 **RESOLVED**（由其作者改好）。**

**⇒ 它**永不失败**：关于他人文件的报告**不得阻塞**本写者。⇒ 这与 `verify_all` 区分 reporter 与 gate 是同一条推理：
**退出码不可能变的检查就是报告，不是门禁**。**

**⇒ 双向验证（用真实登记表）：**

| 情形 | 结果 |
|:--|:--|
| 如登记所载 | **STILL STALE**，still stale: 1，resolved: 0，**exit 0** |
| 换成一段不存在的文本 | **RESOLVED**，still stale: 0，resolved: 1，**exit 0** |
| 恢复登记表 | **STILL STALE** 再现 |

**⇒ 当作者修好那一行，下次运行会转为 RESOLVED，该行即可删除。**

**⇒ 这条纪律与第 1121 轮的自查结论一致：**边界不是靠意志维持的，是靠**把边界外的状态登记在边界内可读的地方**。**
### 3.84 **第 1124 轮：写「下一阶段入口」——三条路线，各自带成本、判据与**未做的原因****

**⇒ 新文件 `NEXT-STAGE.md`（并登记进 README）。⇒ 写法遵循一个判据：**入口清单只在它写明「什么算做完」与「为什么还没开始」时才有用**。**

| 路线 | 动机（缺口） | 成本（实测） | 判据 |
|:--|:--|:--|:--|
| **A** 搬 `Lib/Compiler` → `Runtime/` | I4 秩 2 vs 3 禁止该导入；`Runtime/` 引用它为 **0** | **109 文件 / 1,017 定理 / 23,008 行** | **三条**命令：`git grep` 非空 + `gate.py` I4 ok + `--fast` PASS |
| **B** 让 2.2 的判据可由链内产生 | 2.2 两个载体**零链内消费者** | 低 | `gen_objective_map` 里 2.2 的「链内」列 > 0 |
| **C** 把任意度数接进 `compileToLayer` | 新线有 `d(d−1)/8` 覆盖任意 `d`，主链只有约束表 | 中（1 条翻译 + 1 条定理） | 一条把界与 `LayerOut` 连起来的定理 |

#### 排序不是按大小，而是按**「它能推翻什么」**

**⇒ C **排第一**：它有机会**证伪**对照文档里「两者不可翻译」这一判断，⇒ 而那是本会话**唯一未验证的结构性怀疑**。**
**⇒ A 只是搬运**（成本已量化，可独立成一轮工程）。**
**⇒ B **可能根本不该做**：若其消费者按定位在框架外，强行造内部消费者就是**造假**；故它自带「可能应保持原样」的结论。**

#### 两处刻意写下的**风险**

1. **A**：**「编译通过」不等于「搬对了」**——漏改的导入断在**别处**（`Lib.lean`），故判据必须三条。
2. **B**：把接口性条款改成内部可消费，**会削弱它**——判据一旦由内部产生，它就不再约束「调用者必须提供零宽数据」。

**⇒ 这正是本会话一贯的做法：**把「下一步」写成可失败的假设，而不是写成任务清单**。**
### 3.85 **第 1125 轮：路线 C 以**否证**收束——翻译不可能，而现在是**定理****

**⇒ `NEXT-STAGE.md` 给路线 C 的判据是二选一：桥成立，或「不可翻译」**被证实**。⇒ 结果是后者，且理由是**算术**而非结构。**

```lean
half_is_not_an_integer_weight : ¬ ∃ z : ℤ, (z : ℝ) = 1/2

non_integer_slope_has_no_layer (m) (hm : ∀ z, (z:ℝ) ≠ m) :
    ¬ ∃ l : LinearLayer, ∀ x : ℤ,
        (⟨m, 0⟩ : Segment).eval (x : ℝ) = ((LayerOut l [x] : ℤ) : ℝ)

half_slope_has_no_layer : m = 1/2 的实例
```

**⇒ 论证只有一行：`LinearLayer` 在整数输入上的输出是一个**整数**；而斜率 `1/2` 的分段在那里给出 `1/2`。**
**⇒ 任何编码都桥不过它——**障碍在数的域里，不在代码形状里**。**
**⇒ 故对照文档的第 1 条理由从**判断**升为**定理**，并在文中引用它。**

**⇒ 这比造一条弱桥更有价值**：整数片段上的桥**已经存在**（第 1081 轮 `segment_eval_eq_scalar_layer_out`），
⇒ 假装它能延伸才是真正的失败。**

**⇒ 两处机械记录：`h1` 的左边是 `eval ↑(1:ℤ)` 而 `hev` 陈述在 `eval 1` ⇒ 必须**对齐强转**而不是绕开目标；
`half_slope_has_no_layer` 是转发，已登记。**

#### 对 `NEXT-STAGE.md` 的影响

**⇒ 路线 C **已完成**（以否证形式）。⇒ 三条路线剩两条，且**排序规则得到验证**：
⇒ 「按它能推翻什么排序」是对的——C 确实推翻了一个**判断**，而它只花了**三条定理**。**
### 3.86 **第 1126 轮：先测量，发现计划**错了**；顺手削掉两处「借传递导入」**

**⇒ `NEXT-STAGE.md` 写的「两文件最小闭环」是**错的**。⇒ 实测递归导入闭包：**

| 子图 | 闭包模块数 | 其中 `Lib/Compiler` |
|:--|--:|--:|
| `AnalyticRow` | **83** | **42** |
| `PowChord` | **80** | **39** |

**⇒ 故最小可搬单元约 **40 个模块**，不是 2 个。⇒ 两文件它会拖进 `ChordGeneral`、`GridAlgebra`、`GridBound`、`SymbolicEntry` 及其依赖。**

#### 顺手削掉的两处（都编译通过、都实测）

1. **`PowChord` 为**传递效应**而导入 `ArtifactStitch`**——我逐符号核对：**它一个都没用到**。
   ⇒ 改为**直接导入它真正用的四个** ⇒ **`86/44 → 80/39`**。
2. **`AnalyticRow` 导入 `PolyTable` 却只用 `CapabilityRow`**（在 `CapabilityTable`）⇒ **`85/44 → 83/42`**。

**⇒ 第一次尝试是**直接删除**那条导入——**构建失败**，报 `unknown namespace GridAlgebra`。**
**⇒ 那个错误正是证据：那条导入**在干活**，只是干的不是它自称的活。⇒ **依赖你用到的，而不是恰好把你要的东西拖进来的那个。****

#### 计划因此**新增了一条更便宜的替代**

**⇒ 改 `gate.py` 的 `LAYER_OF`：`Lattice/Lib` 秩 3 → 2。⇒ 代价：**一行**，对 **40–109 个文件的导入改写**。**
**⇒ 它的价格也写明了：**「`Lib` 是基础层」这个结构承诺**失效**。**
**⇒ 而支持这笔交易的**测量**是：`Runtime` 目前引用 `Lib/Compiler` 的文件数为 **0**——即那个秩**从未被行使过**。**
### 3.87 **第 1127 轮：A1 的**实测成本**，以及一处我**没能调平**的数**

**⇒ 计划写的是「改 `LAYER_OF` 的秩：**一行**」。⇒ 本轮在分支上真的改了：**

```python
"Lattice/Lib/Compiler": "compiler",      # \u66f4\u5177\u4f53\u7684\u524d\u7f00\u5fc5\u987b\u5728\u524d\uff08`layer_of` \u53d6**\u9996\u4e2a\u5339\u914d**\uff09
"Lattice/Lib": "lib",
...
"runtime": 2, "primitives": 2, "compiler": 2, "lib": 3,
```

**⇒ 门禁立刻给出**确切**代价：**

```
I4   layering respected   1 finding(s)
     NEW layering violation compiler -> lib: 200 (registered 0)
```

**⇒ 即：把编译层降到秩 2 之后，`compiler → lib` 出现 **200 条违规边**（原先 0 条，因为不存在 `compiler` 层）。**

#### 一、**与我静态计数不一致——这处我没解平**

**⇒ 我用静态扫描得到：**8 个文件、11 条直接导入边**（`Lattice.Lib.Architectures.RealLoop`、`Lattice.Lib.Chain.RealChain` 等 10 个模块）。**
**⇒ 而门禁报 **200**。⇒ 两者相差 189，我在本轮时间内**没有调平**。**

**⇒ 已有的线索（但未证实）：门禁的计数是 `seen[(from,to)] = 边数`，而它统计的是**逐条 `import` 行**；
⇒ 若 200 为真，则说明还有**大量**被我看漏的 `Lib.*` 导入（例如经 `open`/`abbrev` 的间接引用不计数，
但**注释剥离**后的路径匹配可能比我的正则宽）。**

**⇒ 处置：**分支已删除**，主树未改（`gate.py` = 0）。⇒ 而这条差异**记在此处**，因为：
⇒ **一个我不能复现的数，不能当作计划的依据**——这与本会话对 `94/105/99` 的处理是同一条纪律。**

#### 二、由此得到的**精炼路线**（比 A1 与 A2 都更可行）

**⇒ A1（1 行）** ⇒ **200 条违规**，不可直接用。
**⇒ A2（搬 40–109 文件）** ⇒ 太大。
**⇒ 精炼 A3：先搬那 **8 个依赖 `lib` 的文件**（静态计数）到 `Runtime/`，再改秩。**
**⇒ 代价：8 个文件 + 1 行**（若 200 那条能被解释，则代价可能是 1 行 + 「把这些文件的依赖倒过来」）。**

**⇒ 下一步必须先做的事：**把门禁的 `seen` 字典**打印出来**（而不是猜），
⇒ 即给 `gate.py` 加一个 `--dump-layering` 开关，输出每条违规边（文件、被导入模块、层对）。
⇒ **那是唯一能把 200 与 11 调平的办法，且它只需要几行脚本。**
### 3.88 **第 1128 轮：把 200 拆开——**144 + 45 + 11**，并修掉一处门禁**不对称****

**⇒ 上轮那个「200 vs 11」没调平。⇒ 本轮**倒出门禁自己的数据**（复现它的循环并打印），不猜。**

#### 一、200 的**精确**分解

| 来源 | 边数 |
|:--|--:|
| **同目录**（`Lib/Compiler/X` 导入 `Lib/Compiler/Y`） | **144** |
| **聚合器** `Lib/Compiler.lean`（它的 `rel` 是 `Lib/Compiler.lean`，**也**匹配 `Lattice/Lib/Compiler` 前缀） | **45** |
| **真·跨层**（导入 `Lib` 其余部分） | **11** |
| **合计** | **200** ✓ |

#### 二、根因：门禁内部的**不对称**

**⇒ 源层用 `layer_of`，它返回**首个**匹配前缀；而目标层那个循环**没有 `break`**，所以保留了**最后**一个匹配。**
**⇒ 于是我加入的 `"Lattice/Lib/Compiler": "compiler"` 只对**源**生效；**每一个目标**仍落到 `Lattice/Lib` ⇒ `lib`。**
**⇒ 后果：155 条同层/聚合器导入被计成违规。**

**⇒ 修法：目标层循环加 `break`，两侧一致。**

**⇒ 回归检查：master 上 `I4` 仍 **ok**。**
**⇒ 那处不对称过去**无害**，只是因为没有哪个层前缀曾经是另一个的**严格前缀**——我的改秩是**第一个**触发它的改动。**

#### 三、修好后重测 A1：**11 条边，8 个文件**——与我的静态计数**完全一致**

```
NEW layering violation compiler -> lib: 11
```

**⇒ 故 A1 的真实代价是 **11**，不是 200。⇒ A3（先搬 8 个文件再改秩）现在是**精确可估**的：8 个文件 + 1 行。**

#### 四、仍然**不合并**改秩，理由具体

**⇒ 8 个文件仍依赖 `Lib` 其余部分 ⇒ 改秩会把 11 条边变成违规。**
**⇒ 且搬这 8 个文件还要处理**它们的消费者**（谁 import 它们）——那是**级联**，本轮未测。**
**⇒ 故下一步是：**测这 8 个文件的消费者数**，再决定搬移顺序。⇒ **测量先于施工，第 7 次。**
### 3.89 **第 1129 轮：A3 的**确切成本 = 32 次机械编辑**（不是 40–109 个文件）**

**⇒ 测得那 8 个文件的消费者与 `Lib` 依赖：**

| # | 文件 | 消费者 | 依赖 `Lib` 模块 |
|--:|:--|--:|--:|
| 1 | `FloatMulBoundDischarged` | 1 | 1 |
| 2 | `RealConcurrentSemantics` | 1 | 1 |
| 3 | `RealCompileFloatCorrectness` | 2 | 1 |
| 4 | `ReluClosure` | 2 | 1 |
| 5 | `RealAbstractInterpretation` | 2 | 2 |
| 6 | `RealRecursiveSemantics` | 2 | 3 |
| 7 | `RealWP` | 3 | 1 |
| 8 | `RealNonlinearCompile` | **10** | 1 |

**⇒ 级联编辑数 = 消费者之和 = **23**。⇒ 整体成本：**

```
8 次搬移 + 23 处消费者导入更新 + 1 行改秩 = 32 次机械编辑
```

**⇒ 而 `NEXT-STAGE.md` 之前估的是「40–109 个文件」。⇒ 现改为**实测的 32**，并把**顺序**一并写进去：**
**⇒ 先动消费者为 1 的（第 1–2），最后动消费者为 10 的 `RealNonlinearCompile`。**
**⇒ 每步之后必须 `lake build Lattice`——**级联错误会在下一个消费者处爆发**，这正是 A 的风险条目所警告的。**

**⇒ 这条测量把「大工程」变成了「32 次机械编辑」：不需要新的架构判断，只需要按顺序做并每步验证。**
### 3.90 **第 1130 轮：**否证我自己上轮给的方案**，并得到一个更强的结构性结论**

**⇒ 第 1129 轮建议「把 8 个依赖 `Lib` 的文件搬上去，再改秩」。⇒ 本轮测了**它们的消费者住在哪一层**，结果推翻该方案：**

| 文件 | 消费者 | 其中在 `Lib/Compiler` 内 |
|:--|--:|--:|
| `FloatMulBoundDischarged` | 1 | 0 |
| `RealConcurrentSemantics` | 1 | 0 |
| `RealCompileFloatCorrectness` | 2 | **1** |
| `ReluClosure` | 2 | **1** |
| `RealAbstractInterpretation` | 2 | 0 |
| `RealRecursiveSemantics` | 2 | 0 |
| `RealWP` | 3 | **2** |
| `RealNonlinearCompile` | 10 | **3** |

- **搬到 `Lib/`（秩 3）** ⇒ 它们在 `Lib/Compiler`（秩 2）里的消费者变成**向上**（7 条）；
- **搬到 `Runtime/`（秩 2）** ⇒ 它们**自己**对 `Lib` 的 11 条导入变成向上。

**⇒ 故**无论搬到哪一层都会产生新违规**。⇒ 而这个否证提升为一条**结构性结论**：**

> **只要 `Lib/Compiler` 依赖 `Lib`，就**不存在**一个秩使它既能被 `Runtime`（2）引用、又不引入新违规。
> ⇒ 因为「被 Runtime 引用」要求秩 ≤ 2，而「导入 `Lib`（3）」要求秩 ≥ 3。**

**⇒ 真正的选项只剩两个，且**都不是搬文件**：**
1. **消除那 11 条 `Lib` 依赖**——**证明级**重写 8 个文件（不再用 `Lib.Architectures.RealLoop` 等）；
2. **把 `Runtime` 与 `Lib` 平秩**——**一行**，代价是这一对的**方向约束完全消失**。

**⇒ `NEXT-STAGE.md` 已据此重写（含修正排序表里仍写着「109 文件」的那行）。**

**⇒ 本轮没有产生新定理，但产生了一个**更硬的判断**：路线 A 从来不是「搬文件」的问题，而是「依赖方向」与「秩」的两难。**
### 3.91 **第 1131 轮：路 A **结案**——平秩是「放水」，不是「承认」**

**⇒ 上一轮留下的问题是：平秩（把 `Runtime` 与 `Lib` 同秩）究竟是**承认既成事实**，还是**放水**？**
**⇒ 本轮实测：**

```
Lib -> Runtime : 246 条边，跨 108 个文件
```

**⇒ 关键在于这些边**本来就合法**：秩低 = 层低，而导入只能**向下**。⇒ `lib(3) → runtime(2)` 是向下 ✓。**
**⇒ 故平秩**不改变**这 246 条的合法性——它们已合法；平秩只础开**反方向** `runtime(2) → lib(3)`。**
**⇒ 而那个方向目前有 **0** 个使用者（否则 I4 就会报）。**

> **故平秩 = 用「取消一个**当前被完全遵守**的约束」去换「一个**目前为零**的使用」。⇒ 那是**放水**，不是**承认**。**

#### 路线 A 的**最终结论**

**⇒ 没有便宜选项**——不是「还没找到」，而是「**两个可选项各自的代价都已量化**」：**
1. **消除 11 条 `Lib` 依赖** ⇒ 证明级重写 8 个文件；
2. **平秩** ⇒ 取消一个零使用的方向约束。

**⇒ 而什么时候才值得动它：**当主链**真的需要**读新线的定理时**。⇒ 目前它**不需要**：
主链的精度结论已经存在（`symbolToWeight_correct` 等，20 个消费者）。**

**⇒ 故 `NEXT-STAGE.md` 的排序表把 A 改为「**已结案：没有便宜选项**」。**

**⇒ 这使 `NEXT-STAGE.md` 从「三条待做路线」变成「一条已结案（A）、一条已完成（C）、一条待判定（B）」。**
### 3.92 **第 1132 轮：路 B **判定**——2.2 的前提内部可满足，缺口在下游**

**⇒ 路线 B 的问题：条款 2.2 的前提（「数据函数在所有未命名位置取零」）能否**由内部产生**？**

**⇒ 答案：**能，而且平凡**——取 `f := fun _ _ => 0`，它在**每一点**取零。**

```lean
zero_data_models (k) (hnd) : ModelsIRSWith (compileSkel k) k (fun _ _ => 0)
zero_data_covered (k) (hnd) : covered (materializeWith k 0).tensors (shapesOf (materializeWith k 0))
```

**⇒ 目标图实测：条款 2.2 的载体现在读作**

| 载体 | 跨文件 | **链内** | 同文件 |
|:--|--:|--:|--:|
| `covered_of_vanishing` | 2 | **1** | 2 |
| `models_of_covered_data` | 2 | **1** | 2 |

**⇒ 2.2 是第 1118 轮测出的**唯一**零链内载体的条款；当时给的解释是「其判据关于调用者提供的数据」。**
**⇒ 那个解释**不完整**：前提是可产生的；缺的是**想要**「零数据是模型」这一结论的下游。**

#### 修正后的判断（比两种旧读法都更窄）

**⇒ 2.2 **不再是**零活跃条款**（新消费者是 `Runtime/ZeroDataSynthesis.lean`）；
**⇒ 但那个新消费者**自身也是终态**——没有东西读「零数据是模型」，因为读它的那一步是**训练**。**
**⇒ 故缺口在**下游**，不在前提；而下游那一部分**确实**由定位决定。**

**⇒ 两处机械记录：命名空间是 `Lattice.Core.IR`（不是 `Lattice.Core`）；
`hzero` 的最后一个参数是**蕴含**，故证明项要比元数多一层 lambda。**
### 3.93 **第 1133 轮：回路里那五条**零消费者**的定理——四条重述、一条**空洞****

**⇒ 实测 `Runtime/VerificationLoop.lean` 的五个零链内消费者：**

| 定理 | 形状 |
|:--|:--|
| `loop_decreases` | `Repair.decreases` 在 `iterate 1` 处的重述（`simpa`） |
| `loop_terminates_sat` | `Repair.atomic` 在 `run 0` 处的重述（`simpa`） |
| `loop_end_atomic` | `Repair.atomic` 作用在终点 |
| `closed_loop_partial_reinject` | `iterate 1 = fix`，按定义 |
| **`no_loop_fixes_unsatisfiable`** | **否定**，而其**前提可被反驳** |

**⇒ 四条是 `Repair` 接口自身字段的重述。⇒ 第五条比冗余更糟：第 1094 轮的 `sat_not_empty` 证明了**
**「`Sat` 无居住者」对任何 `Repair` 都不成立——它的前提**不可能**。***

```lean
no_unsatisfiable_objective (V) [Nonempty α] : ¬ ∀ x, ¬ V.repair.Sat x
```

**⇒ 这条把那份空洞**写在回路层面**（即它评论的那条定理所在的层），并消费 `sat_not_empty`。**

#### 门禁**当场**抓到我自己新加的定理

**⇒ `no_unsatisfiable_objective` 落在 `3.3 → 3.4` 接缝上，且零消费者 ⇒ 在**同一轮**里，
`chain_connectors --check` 因 `UNREGISTERED_BUDGET = 0` 而**失败**。**
**⇒ 已按规则在 `TERMINAL_CONNECTORS` 登记理由——**这正是「预算为 0」被造出来要强制的事**。**
### 3.94 **第 1134 轮：把**治理的边界**写成一句明说的话，并给密度**

**⇒ 本会话建了两张登记表，而它们**不覆盖全树**——这一点此前只是**隐含**的。⇒ 本轮写进入口文档 §3.1：**

| 表 | 覆盖什么 | 条目 | 零必须带理由 |
|:--|:--|--:|:--|
| `END_OF_CHAIN` | 目标的 **14** 条款的 **36** 个载体 | **9** | 是 |
| `TERMINAL_CONNECTORS` | 八阶段链**相邻接缝**的连接器 | **56** | 是（预算 **0**） |
| — | **其余约 10,000 条定理** | — | **不受管辖** |

**⇒ 最后一行是**设计**，不是遗漏**：无法为每条定理登记理由，而一个装满理由的表与没有表一样无用。**
**⇒ 故本文件**声明这条边界**，而不留白——因为「不受管辖」与「漏管」在读者眼里长得一样。**

**⇒ 密度：10,079 条 theorem/lemma 中 **65** 条（**0.6%**）被两张表直接命名。**
**⇒ 这个数字小得诚实：表的作用不是覆盖全树，而是**钉住两类可命名的空洞**。**

#### 工具**立刻**对这段新文字给出反应

**⇒ `check_delivery_claims` 报 2 处不可解析：`END_OF_CHAIN`、`TERMINAL_CONNECTORS`——它们是 **Python 登记表**，
不是 Lean 声明。**
**⇒ 修法：解析器扩展到 `gov/*.py` 的模块级赋值与字典键——**一条登记项正是这个检查所关心的那种「已命名之物」**。**
**⇒ 双向验证（再次）：真文档 **22 标识符 / 0 未解析**；注入 `no_such_thing_anywhere` ⇒ **exit 1**。**

**⇒ 这又是同一模式的第 N 次：**写下一个可核对的说法，然后由工具来核对它**；而这次工具**核对了我写下的**元数据**（那张表本身）。**
### 3.95 **第 1135 轮：测「条款之间的实际连通」——发现一处**真实断裂****

**⇒ 此前所有测量都是「某载体有没有消费者」。⇒ 本轮换问题：**两个相邻条款之间，是否存在一条**同时提到两方**的定理？**
⇒ 用 14 条款的载体名建 12 个相邻对的计数。**

| 相邻对 | 同现定理数 |
|:--|--:|
| `1.1 ↔ 1.2` | **6** |
| `1.2 ↔ 1.3` | **7** |
| `1.3 ↔ 1.4` | **6** |
| `1.4 ↔ 3.2` | **2** |
| **`3.2 ↔ 3.3`** | **0** |
| **`3.3 ↔ 3.4`** | **0** |
| **`3.4 ↔ 4`** | **0** |
| 2.1 / 2.2 / 2.3 / 5 / 8 ↔ 1.3 / 3.2 | **0** |

**⇒ 8 个「空」。⇒ 但这个数字**可能是词表过窄**造成的假象，故我**手工核查了最关键的一对**（`3.2 ↔ 3.3`）。**

#### 核查结果：**断裂是真的**

| 查询 | 结果 |
|:--|--:|
| 陈述中同时提到 `EpsSat` 与 `Repair` 的定理 | **0** |
| 提到 `EpsSat` 的定理（全树） | **4** |
| 提到 `Repair` 的定理（全树） | **53** |

**⇒ 这是**词表无关**的证据：两个名字在整个开发中**从未同一句话出现**。**
**⇒ 故**逆向侧的「验证 → 修复」这一跳**，在形式上**不存在**——它们各自有定理，但彼此**不相通**。**

**⇒ 这解释了为什么 `3.2 → 3.3` 接缝只有一个活连接器（`extract_after_repair` 死、`extract_after_repair_weak` 活）：
⇒ 那条接缝**本来就没有东西可连**。**

#### 修法（下一步，具体且小）

**⇒ 定义一个 `Repair` 实例，使其 `Sat` **就是** `EpsSat`：**

```lean
noncomputable def epsRepair : Repair X := { Sat := fun x => EpsSat ε f x, ... }
```

**⇒ 一旦存在，`3.2 ↔ 3.3` 就有了**一条**同现定理（哪怕只是 `def` 的字段等式），
⇒ 而更重要的是：**它把「验证判据」与「修复判据」变成同一个谓词**——那才是闭环的定义所需要的。**
**⇒ 目前闭环的 `Repair` 与验证的 `EpsSat` 是两个世界，而**闭环 = 验证回路**要求它们是同一个。**

**⇒ 其余 7 个「空」保留**词表下界**的地位，不宣称断裂**——⇒ 但 `3.3 ↔ 3.4`、`3.4 ↔ 4` 的空**应当被单独核查**（同法）。**
### 3.96 **第 1136 轮：把 `EpsSat` 与 `Repair` 接上——并把**接不上**的地方证出来**

**⇒ 第 1135 轮找到断裂：`EpsSat` 与 `Repair` 从未同现。⇒ 本轮**建桥**，并证明桥在哪里停：**

```lean
eps_repair_requires_descent          -- 若 Repair 的 Sat 就是 EpsSat，则 ε-不满足处测度严格下降
eps_repair_not_constant_measure      -- 且若 ε-满足不处处成立，该测度必非常值

sat_of_constant_measure              -- 常数测度迫使处处 Sat（否则 decreases 给出 k < k）
not_constant_measure_of_unsat        -- 逆否：修复**要求**下降结构
```

**⇒ 故缺口有了**形式位置**：不是「没人想到」，而是「**ε-判据只给谓词，不给测度**」。
⇒ 用 `def` 定义一个 `epsRepair` 是**不可能**的，而这条不可能**被证明了**。**

#### 一处**自我更正**（本节最重要）

**⇒ 桥建好后，我那个一次性脚本仍打印 `3.2 ↔ 3.3 = 0`——因为它数的是 `CLAUSES` 的**载体名**，
而桥说的是**类型** `Repair`。**
**⇒ 权威工具**立刻**看见了它们：两条定理正是 `3.2 verify → 3.3 repair` 的连接器——
⇒ 由于预算为 0，`chain_connectors --check` 在**同一轮**失败，直到我登记理由。**

**⇒ 结论：**工具是对的，一次性脚本太窄**。⇒ 我把那个 0 **保留**在记录里作为**下界**，而不是悄悄改脚本让它好看。**
### 3.97 **第 1137 轮：ε-判据得到了**一个真 `Repair` 实例**——缺的是判据，不是测度**

**⇒ 第 1136 轮证明了「ε-判据的 `Repair` 不能只靠 `def`，因为常数测度会迫使处处 Sat」。**
**⇒ 本轮发现：**测度从来不是问题**——树里**早有**一个真实的：`linearRepair` 的
`μ x = if residual = 0 then 0 else 1`，且有 `linearRepair_measure_drops`。**

**⇒ 差的只是**判据**：`linearRepair` 要求残差**恰为零**，而验证说的是 `|残差| ≤ ε`。**

**⇒ 故实例是一个**死区**修复，只改判据：**

```lean
epsLinearRepair (a b) (ha) (ε) (h : 0 ≤ ε) : Repair ℚ
  Sat := |residual a b x| ≤ ε
  fix := if 在 ε 内 then x else linearFix a b
  μ   := if 在 ε 内 then 0 else 1
```

**⇒ 四个字段全部成立，理由一行：**在 ε 外修复后的残差恰为 `0`，而 `0 ≤ ε`。故 `decreases` 是 `1 → 0`，不是空话。**

#### 与验证词汇的桥是一条**定理**，不是注释

```lean
epsLinearRepair_sat_is_epsSat :
    (epsLinearRepair …).Sat x ↔ EpsSat linearPenaltyEmbedding (a,b) ε x
```

**⇒ 经由 `linearPenaltyEmbedding`（其 `loss` **就是**残差）。**
**⇒ 这是全树**第一条**同时命名 `EpsSat` 与**具体 `Repair` 实例的 `Sat`** 的陈述——**
**⇒ 即 `3.2 → 3.3` 接缝现在有了**构造性见证**，而不只是判据同一。*

**⇒ 两处连带登记（门禁要求的）：`epsLinearRepair_sat_iff` 按构造就是定义式（`Iff.rfl` 于 `Sat` 字段），
基线**有意**记录它；`REPAIR-CENSUS` 的 A 行 `12/39 → 13/43`。**
### 3.98 **第 1138 轮：再注入定理本是 `ε = 0` 的特例——故写出**一般形式****

**⇒ `closed_loop_reinject_vanishes` 要求「在每个 `Sat` 点 `objective = 0`」。⇒ 在 ε-判据下这是**假的**：
`EpsSat` 只给 `|objective| ≤ ε`。⇒ 坚持 `= 0` 等于说**ε-路径永远无法报告成功**。**

**⇒ 两条新增（一条一般、一条具体）：**

| 定理 | 内容 |
|:--|:--|
| `closed_loop_reinject_within` | 若目标在 `Sat` 处被 ε 界住，则它在**终点**也被 ε 界住 |
| `closed_loop_reinject_vanishes_from_within` | 原条是它的 `ε = 0` 情形（**这条推导本身也是定理**，故关系在树里而非在提交信息里） |
| `epsLinearRepair_reinject_within` | 对**具体**死区修复的同一陈述：一步落入容差（内 ⇒ 不变；外 ⇒ 残差 0） |

#### 实测：本轮要连的那条接缝

| 接缝 | 连接器 |
|:--|--:|
| `3.2 verify → 3.3 repair` | **5** OK（两轮前为 **0**） |
| `3.3 repair → 3.4 reinject` | **6** OK |
| `3.4 reinject → 4 loop` | 也带上新推导 |

**⇒ 即：逆向链的三段（verify → repair → reinject）现在**都有真连接器**。**
**⇒ 而这是**三行定理**换来的：不是新建抽象，而是发现原条**少了一个参数**。**

**⇒ 两处连带登记（预算 0 当场逼出）：推导定理（终态：它存在是为了让推广可见）、`REPAIR-CENSUS` A_decls `43 → 44`。**
### 3.99 **第 1139 轮：两个编译器是**同一个左逆**——写成一条定律**

**⇒ 实测：条款 2.3（结构化初始化）与 1.3（符号→权重）**零同现**。⇒ 但它们**不是无关**：**
- `compileWith` 是 `extract` 的左逆；
- `compileToLayer` 是 `extractLayer` 的左逆（且双向）。

**⇒ 各半分别写在各自文件里，而**共同形状只活在读者眼里**。⇒ 新文件 `Lib/Editing/CompileLaw.lean`：**

```lean
compile_round_trip_law :
    (∀ k f, extract (compileWith k f) = some k) ∧
    (∀ cs, extractLayer (compileToLayer cs) = cs) ∧
    (∀ ls, compileToLayer (extractLayer ls) = ls)
```

**⇒ 实测效果：`2.3 ↔ 1.3` 同现数 **0 → 1**。**

#### 一处**真实**的技术障碍（记录而非绕过）

**⇒ 树里有**两套同名 `abbrev`**：`Lattice.{ConstraintSet,Layer}` 与
`Lattice.Lift.SymbolToWeightCorrectness.{ConstraintSet,Layer}`，两者都落到 `List VectorConstraint` / `List LinearLayer`。**
**⇒ 提它们的定理**类型正确**，但同时 `open` 两个命名空间会使名字**歧义**。**
**⇒ 故本文件**全用全限定名**，两边都不 `open`。⇒ 而这处不对称**本身就是**「为何此前没有定理同时提到两者」的一部分原因。**

**⇒ 已按预算 0 登记为连接器理由：**它是**定律**，不是**一步**。**
### 3.100 **第 1140 轮：`2.1 ↔ 1.3` 的连接**不是定理，而是**实例****

**⇒ 实测 2.1（约束损失）与 1.3（符号→权重）零同现。⇒ 而候选 `sat_iff_loss_zero` 说的是**第三个**编译族
（`compileNeurons` / `listLoss`），不是 `compileToLayer`。**

**⇒ 故连接不是平行定理，而是**实例**：**

```lean
layerPenaltyEmbedding : PenaltyEmbedding ConstraintSet (List ℤ)
  loss := if AllZeroOutputs (compileToLayer cs) x then 0 else 1
  Sat  := AllZeroOutputs (compileToLayer cs) x

layerPenalty_loss_eq_zero_iff : loss = 0 ↔ AllZeroOutputs (compileToLayer cs) x
layerPenalty_sound            : PenaltySound layerPenaltyEmbedding
```

**⇒ 这不牵强：`PenaltySound` 正是「软损失代替硬约束」这一位置的**最低要求**，
⇒ 而层世界满足它——因为它的 `loss` 与 `Sat` 是**同一个谓词的两种写法**。**
**⇒ 实例带来的，是「损失」这门语言**现在能谈到层**。**

**⇒ 实测效果：`2.1 ↔ 1.3` 同现数 **0 → 1**（在把 `layerPenaltyEmbedding` 登记为 2.1 载体之后——
⇒ 因为度量数的是**语句里的名字**，而实例是一个 `def`，它的**名字**才是出现的那个）。**

**⇒ 两处机械记录：定义需要 `noncomputable`（经 `Classical.propDecidable`）；局部实例必须写在命名空间入口处——
⇒ 与第 1101 轮**同一个形状**。**

#### 由此浮现的一个**更强的**结构观察

**⇒ 树里有**三个**同形的编译族：`compileWith → IRWeights`、`compileToLayer → Layer`、`compileNeurons → Neuron 序列`，**
**⇒ 每个都有自己的 `sat ↔ loss = 0` 律，而**族与族之间没有一条连接定理**（除本轮与上轮各写的一条）。**
**⇒ 这解释了为什么「条款之间」的同现如此之少：不是没写，而是**每族各自成岛**，岛与岛之间只由**我这两轮**搭了两座桥。**
### 3.101 **第 1141 轮：两个条款被**少计**——它们的数据级载体从未登记**

**⇒ 2.1 ↔ 1.3 上轮用**实例**接上了。⇒ 2.2 ↔ 1.3 **不需要新定理**：**

**⇒ 树的**收官定理** `data_to_weight_honest` 早已陈述「覆盖语料 + 零宽样本 ⟹ 编译层输出为零」，
⇒ 其语句命名 `CoversCorpus` 与 `corpusToLayer`。⇒ 而**两者都不是任何条款的载体**，故图看不见这条连接。**

**⇒ 登记后，图立刻显示出它们**本来就很活跃**：**

| 载体 | 跨文件 | **链内** | 同文件 |
|:--|--:|--:|--:|
| `corpusToLayer` | 3 | **3** | 5 |
| `CoversCorpus` | 5 | **5** | 3 |

**⇒ 即：它们在**数据级**上**早已是活的**；载体清单只是**写在符号级**上而已。**
**⇒ 故这次是**度量在少计自己的概念**，而修法是**往下看一层**，不是多写定理。**

**⇒ 实测：`2.2 ↔ 1.3` 同现数 **0 → 1**，用的是**已有之物**。**

#### 现在只剩一处

**⇒ 条款连通仅剩 `5 ↔ 1.3`（符号引擎 ↔ 符号→权重）零同现。⇒ 而第 1117 轮已测：`cic_loop_reaches_weight` **正是**
它——那条定理把 CIC 的类型约束与编译层的零输出连起来，且**有 2 个链内消费者**。**
**⇒ 下轮把它登记为 5 的载体（它是 CIC 一方的陈述）与 1.3 的连接，条款连通即**全部闭合**。**
### 3.102 **第 1142 轮：条款 5 拿到了桥载体——而**名字度量仍然看不见那一对****

**⇒ 把 `cic_loop_reaches_weight` 登记为条款 5 的载体。⇒ 它是**正确的**载体：第 1117 轮测出它是
唯一把 CIC 类型约束与编译层零输出连起来的陈述，且有 **2 个链内消费者**（图中现在读作 跨文件 2 / 链内 2）。**

**⇒ 但 `5 ↔ 1.3` 的同现数**仍是 0**——原因在**度量**，不在树：**
**⇒ 该定理的语句说的是 `cicToConstraint` / `VectorConstraintSat` / `AllZeroOutputs`，**
**⇒ 而**没有**任何条款 5 的载体名（它不叫 `HasType`，也不提到 `HasType`）。**

> **一个在**同一语句里找两个条款名字**的度量，看不见一个**用两个条款的概念说话**的桥。**

**⇒ 这是本会话**第三次**名字度量低估语义连接（第 1136、1140、1142 轮）。**
**⇒ 而我**没有**为了让它动而编造一句含载体名的陈述。**

#### 诚实的终态

| 口径 | 结果 |
|:--|:--|
| **按名字** | **10 / 11** 相邻条款对在同一语句中同现 |
| **按语义** | **11 / 11** 都有**有据可查**的桥，最后一条即本轮的定理 |

**⇒ 而通用的修法已写明：**不要数标识符，要数**类型与值****——
⇒ 那是一条**可执行**的后续方向，而不是一句抱怨。
### 3.103 **第 1143 轮：把「条款成对」做成工具——而它**与接缝工具的分歧是有信息的****

**⇒ 登记 CIC 侧载体：`CICCtx`（链内 **24**）、`cicToConstraint`（链内 **7**）⇒ `5 ↔ 1.3` 从 0 变 **2**。**

**⇒ 工具 `gov/check_clause_pairs.py`（**只报告**）报告 12 对中 **8 对相连**，**4 对为空**：**

```
3.2<->3.3    3.3<->3.4    3.4<->4    8<->3.2
```

**⇒ 而 `chain_connectors` 的接缝视图是 `3.2→3.3 = 5`、`3.3→3.4 = 6`。⇒ 两者**分歧**，而分歧是**有信息的**：**
**⇒ 接缝工具按**概念词**（`verify`/`repair`/`reinject`）计，条款工具按**载体名**计。**
**⇒ 第 1136/1138 轮建的桥**用概念说话**，故一个工具看得见，另一个看不见。**

#### 而有一对**在两种口径下都为空**

**⇒ `8 Lean 保证 ↔ 3.2 验证`——这不是度量假象，而是**真的少一句陈述**。**

**⇒ 这一对更值得注意，因为它是**整个项目最强的承诺**（Lean 保证）与**验证环节**之间：
⇒ 若两者没有任何共现，那么「正确性由 Lean 保证」与「验证回路」在形式上**是两句话**。**

**⇒ 结论：本轮工具的**主要产出不是那个 8/12**，而是**它指出了唯一一处两口径皆空的地方**。**
### 3.104 **第 1144 轮：`8 ↔ 3.2`**补上了**——而那个缺口是**可构造的****

**⇒ `8 Lean 保证 ↔ 3.2 验证` 是唯一在**两种口径**下都为空的条款对。⇒ 而它最要紧：
⇒ 它是「正确性由 Lean 保证」与「验证回路」相遇的地方。**

**⇒ 桥不是口号：`sound_not_exact` 的见证 `constEmbedding` 有 `loss = 1`、`Sat = False`，
⇒ 故在 `ε = 1` 时它**满足 `EpsSat`，而其约束**不成立**。**

```lean
sound_not_exact_gives_epsilon_gap :
    (PenaltySound constEmbedding ∧ ¬PenaltyExact constEmbedding)
      ∧ EpsSat constEmbedding () 1 () ∧ ¬ constEmbedding.Sat () ()

epsSat_passing_is_not_correctness :
    ∃ E p x ε, 0 ≤ ε ∧ EpsSat E p ε x ∧ ¬ E.Sat p x
```

**⇒ 故「ε-验证通过」**不蕴含**「约束成立」——这正是「健全但不精确」在**验证词汇**里的样子，**
**⇒ 也是**容差存在的理由**：精确判据不可得，故验证只能在 ε 里说话；而读 ε-判据的人必须知道**它没说什么**。**

**⇒ 实测：`8 ↔ 3.2` **0 → 2**；空对 **4 → 3**（其余三对是接缝度量看得见的逆向侧对，故**无一对真的没有桥**）。**

**⇒ 同一条教训的**第三次**（第 1141、1143 轮）：一对看似为空，只因为该条款的词汇**登记得太窄**。**
**⇒ 这次是 `PenaltySound`/`PenaltyExact`——而它们就是「健全但不精确」的**原词**。**
### 3.105 **第 1145 轮：连通性写进入口文档 §3.2——**四个口径、各自终值、各自停因****

**⇒ 入口文档此前只讲「这一层立了什么」，没回答读者真正的问题：**这条链连通吗？****
**⇒ 而答案不是一个数字，是**四个独立口径**，每个都有自己的停因：**

| 口径 | 终值 | 停因 |
|:--|:--|:--|
| 载体消费者 | 36 载体 / **32 链内** | 余者由**定位**决定 |
| 接缝连接器 | **56** 登记，预算 **0** | 死的必须带理由 |
| 条款对（**载体名**） | **9 / 12** | 名字度量对「用**概念**说话」的桥**失明** |
| 条款对（**接缝概念**） | **3 / 3** 逆向侧 | 只覆盖八阶段链 |

**⇒ 四者**合起来覆盖全部 12 对**。⇒ 故正确读法不是「9/12，有三个缺口」，**
**⇒ 而是「9/12 **加**三对只能用另一种词汇看见」。**

**⇒ 同节还列了本会话写的**六座桥**，各带「为何此前不存在」：**
**⇒ `eps_repair_requires_descent`、`closed_loop_reinject_within`、`compile_round_trip_law`、
`layerPenaltyEmbedding`、`sound_not_exact_gives_epsilon_gap`、`cic_loop_reaches_weight`。**
**⇒ **没有一座需要新抽象**；每一座要么是几行定理，要么是把**已有之物**登记对。**

**⇒ 工具核对：新 §3.2 里 **28 个标识符 / 0 未解析**；`check_clause_pairs.py` 已登记进 §6 作为复现命令。**
### 3.106 **第 1146 轮：路线 B **结案**——抽象有 4 个生产者、**0 个消费者**，且原因可证**

**⇒ 第 1132 轮留下的问题是：2.2 的缺口在「下游」，那**下游能否造出来**？**

**⇒ 本轮测量的是 `ModelsIRSWith` 这个抽象在两处的出现：**

| 位置 | 条数 |
|:--|--:|
| 作为**前提**（`(h : ModelsIRSWith …)`） | **0** |
| 作为**结论** | **4**（`pointSkeleton_models`、`models_of_covered_data`、`parse_models`、`zero_data_models`） |

**⇒ 即：**4 个生产者、0 个消费者**。⇒ 下游**不是**「没人写」，而是**没有任何定理需要这个前提**。**

**⇒ 而原因**可证**：提取律**无条件**成立（`extract (compileWith k f) = some k` 对**任意** `f`），
⇒ 故「`f` 是 `k` 的模型」这一前提在下游**永远用不上**。**
**⇒ 这使 `ModelsIRSWith` 成为一种**以 `Prop` 形式写下的说明**：它有三个实例、能证明某事、而**没有一处需要它**。**

**⇒ 路线 B 由此结案：**不是「可能不该做」，而是**做不了也不需要做**——缺口的位置被证在「前提永不被需要」处。**
**⇒ `NEXT-STAGE.md` 的 B 行已改为「已结案：4 生产者 / 0 消费者」。**
### 3.107 **第 1147 轮：`ε = 0` 的 ε-修复**就是**精确修复——两个 `Repair` 实例第一次被一条定理连起来**

**⇒ `Repair` 抽象现在有**四个实例**（`sqDistHalvingRepair`、`layerZeroRepair`、`twoSlopeRepair`、`epsLinearRepair`），
⇒ 而此前**没有任何定理把其中两个连起来**：每一对都在各自文件里、各有各的局部事实。**

**⇒ 本轮证：`ε = 0` 时的 `epsLinearRepair` **就是** `linearRepair`：**

```lean
epsLinearRepair_zero_sat_iff  -- |residual| ≤ 0 ↔ residual = 0
epsLinearRepair_zero_fix_eq   -- 死区在 ε = 0 处等于 linearFix（关键：linearFix_absorbs）
epsLinearRepair_zero_mu_eq    -- 两个测度相同
epsLinearRepair_zero_is_linearRepair  -- 三者合取
```

**⇒ 为什么要分**三个数据字段**：`Repair` 的三个 `Prop` 字段是**证明**，按 proof irrelevance 不需要单独比。**
**⇒ 而 `fix` 的等式要有一个**非平凡**的输入：**`linearFix_absorbs`**——即**精确修复**对一个**已经为零**的点
**也不动**。没有那条，两侧在 ε=0 不会相等。**

**⇒ 故「泛化」与「基准例」现在由**一条定理**连接，而不是由读者的辨认连接——与本会话一贯的模式相同：
⇒ **树里两物都在，缺的是把它们写在一起的陈述。**
### 3.108 **第 1148 轮：我上一轮的预测**错了**——`b = 0` 不能退化，因为载体不同**

**⇒ 上轮我打算证「`twoSlopeRepair` 在 `b = 0` 时退化为单侧 `slopeRepair`」，从而把四个实例连成一条链。**
**⇒ 读定义后：`twoSlopeRepair a b = repairProd (slopeRepair a) (slopeRepair b)`——它是**乘积**，载体是**对**。
⇒ 故 `b = 0` **不可能**退化到单侧：**退化要求同一载体**。**

**⇒ 实测五个实例 / 四个载体：**

| 实例 | 载体 |
|:--|:--|
| `sqDistHalvingRepair` | `ℕ` |
| `layerZeroRepair` | `Layer` |
| `twoSlopeRepair a b` | `(ℕ → Segment) × (ℕ → Segment)`（**乘积**） |
| `linearRepair a b` | `ℚ`（精确判据） |
| `epsLinearRepair a b ε` | `ℚ`（**ε-判据**，死区） |

**⇒ **只有一对共享载体**（`ℚ` 上的两个），而那一对**已在第 1147 轮被定理连上**。**

**⇒ 其余三个**不能互相退化**，因为**类型不同**——而这不是缺口：它们回答**不同载体**上的问题。**

**⇒ 另外查实：`twoSlopeRepair` 的**分量事实**已由 `repairProd_fix` / `repairProd_measure` / `repairProd_sat` 提供，
⇒ 故「对角版」只会是**重述**。⇒ **查了，没写**。**

**⇒ 本节把这些写进 `REPAIR-CENSUS.md`：一个只数数目的普查，看不出一件数不出来的事——**可比性取决于载体**。**
### 3.109 **第 1149 轮：收尾复核——入口文档**陈旧了四处和八处****

**⇒ 用四个工具**重跑**本会话声称的每个终值，逐项与入口页对照。⇒ 两处陈旧，都是因为**本节写完之后我又加了东西**：**

| 项 | 页面写的 | 实测 |
|:--|--:|--:|
| `TERMINAL_CONNECTORS` | 56 | **60**（本会话又登记 4 条） |
| 目标载体 | 36 | **44**（数据级/ CIC 级/ 惩罚级共 +8） |
| 链内消费 | 32 | **36 / 44**（36 链内 + 4 仅本文件 + 4 全无） |
| 密度 | 65 / 10,079（0.6%） | **69 / 10,099（0.7%）** |

**⇒ 这正是复核的意义：一个写着**可核对数字**的页面，会在树一移动时**立刻腐烂**，**
**⇒ 而它唯一可靠的读者是**工具**。⇒ 现在每个数字背后都有 §6 里的一条命令。**

**⇒ 而这次复核**自己的产出**是一个反例：**文档在写完后两小时内就陈旧了**——
⇒ 故「文档不享有权威」不是谦辞，是**操作事实**。**
### 3.110 **第 1150 轮：最后自检——本会话的**每条主张**是否仍在树上**

**⇒ 本轮**不测量新东西**：只抽查本会话 10 项**核心主张**，确认其声明**仍在 HEAD 且仍在我说的文件里**。**

| 主张 | 声明 | 位置 | 结果 |
|:--|:--|:--|:--|
| 统一两套实现 | `realLayer_ofInt_out` | `Lib/Compiler/RealLayer.lean` | **OK** |
| 主链首个 `Repair Layer` | `layerZeroRepair` | `Runtime/LayerRepair.lean` | **OK** |
| 闭环实例 | `twoSlopeLoop` | `Lib/Compiler/LoopInstance.lean` | **OK** |
| 载体总述更名 | `carrier_covers_two_segments_plus_one_direction` | `Lib/Compiler/CarrierReproduction.lean` | **OK** |
| 单向开放式提取 | `extract_after_repair_weak` | `Runtime/RepairClosure.lean` | **OK** |
| 路线 C 否证 | `non_integer_slope_has_no_layer` | `Lib/Compiler/BridgeToMainChain.lean` | **OK** |
| ε-修复实例 | `epsLinearRepair` | `Lib/Linear/ResidualEpsRepair.lean` | **OK** |
| 再注入宽容版 | `closed_loop_reinject_within` | `Runtime/VerificationLoop.lean` | **OK** |
| 两编译器同一律 | `compile_round_trip_law` | `Lib/Editing/CompileLaw.lean` | **OK** |
| `8 ↔ 3.2` 缺口 | `sound_not_exact_gives_epsilon_gap` | `Runtime/EpsGap.lean` | **OK** |

**⇒ **10 / 10**。⇒ 没有被后续改动覆盖的，也没有**只在提交信息里存在**的。**

**⇒ 这条自检的意义：本会话有 100+ 次提交、100+ 节记录。⇒ 而「我做过什么」的最终依据不是那些文字，
⇒ 而是**这些声明此刻是否还在树上**——**这是唯一无法自欺的检验**。**
### 3.111 **第 1151 轮：不带预设的宏观重测——三条**新事实**，与一条**从数据得出**的路线**

**⇒ 按用户明示：**在不清楚如何做时，单独花一轮建立宏观认知，不依赖先前的笔记**。⇒ 我只用树的数据。**

#### 一、规模（全新实测）

| 桶 | 文件 | 定理 | 行数 |
|:--|--:|--:|--:|
| `Core` | 175 | 1,059 | 28,381 |
| `Lib/Compiler` | **110** | **1,090** | **23,075** |
| `Runtime` | 105 | 602 | 16,472 |
| `Reference` | 100 | 685 | 17,834 |
| `Lib/Chain` | 77 | 886 | 20,557 |
| `Plugins` | 76 | 643 | 13,975 |
| `Lib/Editing` | 70 | **1,017** | **25,743** |
| \u2026\uff08\u5171 18 \u6876\uff09 | | | |
| **合计（前 18）** | **1,118** | **10,317** | **260,170** |

#### 二、**枢纽全在 `Runtime/`**（这条最要紧）

| 模块 | fan-in |
|:--|--:|
| `Lattice.Runtime.ConvertVectorLinear` | **76** |
| `Lattice.Runtime.SymbolToWeightCorrectness` | **64** |
| `Lattice.Runtime.WeightToSymbolEquivalence` | **38** |
| `Lattice.Runtime.Extraction` | **25** |
| `Lattice.Core.RepairModule.Repair` | **33** |
| `Lattice.Lib.Editing.RealCompileExtractClosed` | 29 |

**⇒ 四个 Runtime 模块合计 **203** 条 fan-in。⇒ 即：**`Runtime/` 才是这棵树的**结构中心**，而不是 `Lib`。**
**⇒ 这**重新诠释**了路线 A：主链要引用 `Lib/Compiler` 之所以难，不是因为「秩」，而是因为**中心本身在被 203 条边靠着**，
⇒ 任何「让中心去引用卫星」的改动都要**从中心一侧**动。**
**⇒ 故 A 的**真正**形态应是：**把 `Lib/Compiler` 中被需要的那部分**下沉到 `Runtime` 的既有中心旁边**，
⇒ 而不是把 `Runtime` 抬高去引用一个 23,000 行的卫星。**

#### 三、**全树最大的文件是一个**多主题聚集体****

| 文件 | 行 | 定理 | 第二大倍数 |
|:--|--:|--:|--:|
| **`Core/RepairModule/VariableDerivative.lean`** | **5,523** | **217** | **3.75×** |

**⇒ 它有 **72 个二级标题**，主题从「`Chain` 参数空间可微」到「差分阶数随深度增长」⇒ **多主题聚集体**。**
**⇒ 这正是用户指令「该分文件的分文件」所指的情形。⇒ 新**路线 D**（见 `NEXT-STAGE.md`）：**
⇒ **按节边界四分，1,401 / 1,391 / 1,404 / 1,327 行（均衡在 3% 内）；判据三条；风险是先编译验证切点。**

#### 四、这条重测**推翻了什么**

**⇒ 它推翻了我一直以来的**隐含假设**：「`Lib/Compiler` 是这条链的主角，`Runtime` 是配角」。**
**⇒ 数据显示相反：`Runtime` 是中心（203 fan-in），`Lib/Compiler` 是**卫星**（它的 23,075 行里能被主链用到的极少）。**
**⇒ 故「让主链用上新编译器」的正确方向**不是抬高主链**，而是**把可用的部分下沉**。**
### 3.112 **第 1152 轮：路线 D **第一步已做，但**不合并**——拆分本身成功，级联比预估大**

**⇒ 在分支 `split-variable-derivative` 上执行拆分。⇒ **拆分本身是干净的**：**

| 项 | 结果 |
|:--|:--|
| 静态探测 | 72 个节边界中 **44 个零反向引用**；选中的三个切点都在其中 ⇒ **无需重排，只需 import** |
| 新文件 | Params **1,341** / Quadratic **1,261** / Degree **1,534** / Difference **1,325** 行 |
| 聚合器 | `VariableDerivative.lean` 只余四条 `import` ⇒ **33+ 导入者（含插件 12 条义务）无需改动** |
| 构建 | `VariableDerivative` **通过**，`Lattice` **通过** |

#### 而未完成的是**级联**，且比我的估计大：**五个按路径索引的登记表**，各有一套格式

| 登记表 | 条数 | 状态 |
|:--|--:|:--|
| `gov/alias-baseline.txt` | 2 | **已修** |
| `agent-tmp/review/*.jsonl` | **18** | **已修** |
| `gov/definitional-proof-baseline.txt` | **29** | **已修** |
| `gov/literal-rfl-baseline.txt` | 4 | **路径形式仍不对** |
| `ChainSlot/plugin.yml` | **12** | **前缀不对（报 24 处）** |

**⇒ 故该分支**不合并**：两条门禁仍失败（`check_literal_rfl`、`check_plugin_yml`）。⇒ **master 未受影响**。**

#### 一处我**自己造成又修好**的问题

**⇒ checkout 回 master 时，分支编出的 4 个 `.olean` 成了 master 上的**陈旧产物**，I7 报 4 处。**
**⇒ 我删掉它们——但**连 master 仍需的聚合器产物一起删了**，I7 随即报 1 处。**
**⇒ 重新 `lake build` 该模块后 **ok**。⇒ 教训：**删产物前先确认哪一侧需要它**。**

#### 一处**他人的并发改动**（我不动）

**⇒ `USAGE.md` 出现章节重编号（`## 6 → ## 7`）——那是**另一位写者**的工作，我一字未改。**
### 3.113 **第 1153 轮：路线 D **完成并合并**——6 个登记表全部对齐**

**⇒ 上轮剩下的两个登记表，本轮**读工具**而不是**猜格式**，一次修好：**

| 登记表 | 条数 | 上轮错在哪 | 修法 |
|:--|--:|:--|:--|
| `gov/literal-rfl-baseline.txt` | 4 | 缺 `Lattice/` 前缀（`rel` 相对**仓库根**） | 加前缀 |
| `ChainSlot/plugin.yml` | 12 | 同上 | 加前缀 |
| **`ChainSlot/Manifest.lean`** | **12** | **我根本不知道它存在** | YAML 校验报「YAML ≠ Lean」才暴露 |

**⇒ 第三个是**真正的发现**：插件有**两份**清单（YAML 与 Lean 的 `Manifest.lean`），
⇒ 而校验器**交叉比对它们**。⇒ 这解释了为什么修好 YAML 后错误数**从 12 变 24**——两侧都错。**

#### 合并（按纪律：分支 → 分支自身全绿 → `--no-ff` → 删分支）

**⇒ 分支上：门禁 **0**、`VERIFY ALL [fast] PASS`（371.8 秒 / 94）。⇒ 合并后 master 复验：同为 **0** 与 **PASS**（437.4 秒）。**

| 项 | 结果 |
|:--|:--|
| 新文件 | Params **1,341** / Quadratic **1,261** / Degree **1,534** / Difference **1,325** 行 |
| 聚合器 | 只余 4 条 `import` ⇒ **33+ 导入者与插件 12 条义务零改动** |
| 切点 | 44/72 零反向引用中选 3 个 ⇒ **无需重排** |
| 文件数 | `Core/RepairModule` 由 10 → **14**（全树 1,118 → **1,122**） |
| 最大文件 | 由 **5,523** 行降到 **1,534** 行（**第二大之下**） |

**⇒ 全树最大的文件不再是**离群体**：最大 1,534 行，而第二大为 1,472 行 ⇒ **离群消失**。**

#### 一条**方法**结论

**⇒ 失败的门禁是**规格**，不是障碍**。⇒ 猜路径形式花掉一轮，读工具花掉一轮——
⇒ 而**两次都记在这一节里**，因为「省下的那一步」正是下一次会重复的那一步。**
### 3.114 **第 1154 轮：判据修正——**大小不是判据，节密度才是**；且**采集物不该拆****

**⇒ 上轮计划的下一个目标是 `Lib/Chain/RealLv00Solver.lean`（1,472 行）。⇒ 读它的文件头后**撤回**：**

**⇒ 它开头写着**采集来源**（`level0000x/Lv-00`、上游四个模块、toolchain 对照）⇒ **它是采集物，不是自写物**。
⇒ 拆它会**破坏与源本的一一对应**。**

#### 实测：全树 **22 个采集文件 / 9,196 行**，**1,202 个自写文件 / 271,913 行**

**⇒ 而在**自写文件**中，最大六个是：**

| 文件 | 行 | 定理 | **节** |
|:--|--:|--:|--:|
| `VariableDerivativeDegree`（我拆出来的） | 1,553 | 41 | **29** |
| `VariableDerivativeParams`（同上） | 1,359 | 61 | **12** |
| `VariableDerivativeDifference`（同上） | 1,344 | 48 | **14** |
| `Reference/…/PenaltyLossDerivative` | 1,287 | 44 | **17** |
| `VariableDerivativeQuadratic`（同上） | 1,280 | 63 | **17** |
| `Lib/InfoTheory/RealInformationGeometry` | 1,192 | 35 | **6** |

**⇒ 关键对照：`RealInformationGeometry` 1,192 行却只有 **6 节**（每节 ≈200 行）⇒ **内聚** ⇒ **不该拆**。**

#### 故判据改为

**⇒ 节 ≥ ~15 **且** 行 ≥ ~1,200 ⇒ 多主题，值得拆。**
**⇒ 节 ≤ ~6 ⇒ 内聚，**不拆**（无论多长）。**
**⇒ 采集物（文档头有来源）⇒ **一律不拆**。**

**⇒ 这条修正**推翻了我上一轮的目标**，而它的依据只是一次 `head -30` 的阅读——
⇒ **数据判据也要看**内容**，不能只看尺寸。****

#### 修正后的下一个目标

**⇒ `Core/RepairModule/VariableDerivativeDegree.lean`（1,553 行 / **29 节**）——我自己拆分的产物，现在是最大自写文件。**
**⇒ 它应**再拆一刀**（两份 ≈750 行）或与 `Params` **重平衡**。⇒ 这是**我的拆分留下的**不均衡，应由我修。**
### 3.115 **第 1155 轮：全树**38.2% 是注释**——以及由此得出的第三条判据**

**⇒ 拆完 `VariableDerivative` 后，我回头测它最大的一支 `Degree`（1,553 行 / **29 节**）的**节结构**：
⇒ 发现其中 **10 节是 `⚠⚠` 障碍记录，合计约 640 行**（占该文件 41%），而它们是**纯叙述**（不含声明）。**

**⇒ 于是测了全树的注释比例：**

```
全树 282,333 行 · 代码 174,364 · 注释/空行 107,969 = 38.2%
```

**⇒ 而 500 行以上文件里**注释占比最高**的八个：**

| 文件 | 行 | 注释占比 |
|:--|--:|--:|
| `Primitives/TokenizeStrategy.lean` | 518 | **71.0%** |
| `Lib/Chain/RealEndToEnd.lean` | 954 | 66.5% |
| `Lib/Attention/RealTemporalLayerExt.lean` | 966 | 64.3% |
| `Lib/Editing/RealLayerSemanticQuotient.lean` | 681 | 62.1% |
| `Lib/Attention/RealTemporalLayer.lean` | 529 | 61.2% |
| `Lib/Editing/RealRoundtripNondegenerate.lean` | 674 | 60.2% |
| `Lib/Editing/RealClosureReversibility.lean` | 800 | 59.5% |
| `Lib/Editing/RealQuotientReversibility.lean` | 821 | 59.2% |

#### 两面读法（都必须写下来）

**⇒ **好的一面**：树记录了**为什么**（失败路径、被否证的做法），这正是本会话一贯重视的。**
**⇒ **风险面**：在一个 **71% 是散文**的文件里，**证明被散文埋住了**；而注释会**腐烂**——它描述的是会变的代码。**
**⇒ 已知的守卫（`check_doc_names`、`audit_docs`）**通过**，故这些注释至少**与现存名称一致**——但一致性不等于**仍为真**。**

#### 第三条判据（由数据得出）

**⇒ 对**行数大**的文件，先看两件事：**节数**（多主题？）与**注释占比**（是证明还是文档？）。**
**⇒ 若注释 > ~60%，则该文件**首先是一份文档**——拆分它的正确形式是**把散文与证明分开**，
⇒ 而**可测的完成判据**是：**`⚠⚠`/叙述性节 = 0**，且每份仍有自己的证明主体。**

**⇒ 我**没有**在本轮执行那次拆分：它需要 29 处编辑且必须逐处验证（每个 `⚠⚠` 节抽出后要留指针）。
⇒ **记录判据而不仓促动手**——这是本会话对「该分文件的分文件」的**第三次**应用，而这次**先测了比例再决定**。**
### 3.116 **第 1156 轮：那个「71% 注释」的文件——**它自述为假****

**⇒ 上轮我要做的「散文/证明分离」，在读到文件头第一句时就变了：**

> **「本文是一个**只含注释的 Lean 文件**：它不含任何声明，因此对构建、对任何定理都零影响。」**

**⇒ 而第 284 行起有**五条探针定理**（`encLen_ge_two` 等）。⇒ **那句话在写下时是真的，加了定理之后没人改它。**

**⇒ 没有任何工具能抓到它**：`check_doc_names` 查**名字是否存在**，`audit_docs` 比对**文档表与树**——
⇒ 而一个**关于文件自身**的声称**没有东西可查**。**

#### 于是做两件事

**1. 改正那句话**——现在它说真话：前 ~280 行是**探针报告**，其后五条定理是**该报告的落地形式**，二者都在本文件内。
**2. 把普查做成工具** `gov/check_self_claims.py`。**

#### 而工具的第一版**误报**了

**⇒ 它匹配到 `RealRecoverEndpoint.lean:21`：「全库 `def recover` **0 命中**」——那是**历史陈述**，
⇒ 紧接着下一行就说「**本文件补上** `recover`」。⇒ 故**不是**自述，**不该修**。**
**⇒ 修法：模式要求**同一行内有自指**（本文/本文件）。⇒ **收窄本身就是工具的真正内容。****

**⇒ 双向验证：把旧句重新注入 ⇒ 报 **1 违规 / exit 1**；改正后的树 ⇒ **0 声称 / 0 违规**。**
**⇒ 而它还**抓到了我自己的修正**——因为我**引用了**那句旧话。⇒ 故修正改为**描述**旧声称，而非**复述**它。**

**⇒ 这是本会话第三次「工具先抓到自己」**（第 1119 轮假引用、第 1134 轮 `evaluate` 复述、本轮）。**
### 3.117 **第 1157 轮：七/八个高注释文件的自述**全部为真**——并引出第二类可核对声明**

**⇒ 逐个读那八个高注释文件的**第一句**：多为主题描述（不可核对），但**三条可核对**：**

| 声称 | 核对 | 结果 |
|:--|:--|:--|
| `RealQuotientReversibilityToken.lean`「已并入本文件」 | 该文件是否存在 | **不存在** ⇒ **真** |
| `RealTemporalLayerExt`「补完 A 类 A1–A7」 | 七项是否都出现 | A1–A7 各出现 7–14 处，文件 40 条定理 ⇒ **一致** |
| `RealLayerSemanticQuotient`「一对一假」 | 是否有反例定理 | 见其正文（该文件即反例的载体） |

**⇒ 故 **38.2% 的注释在**可核对之处是可靠的**——这是一条**正面结论**，不是零结果。**
**⇒ 而它与此前的反例（`TokenizeStrategy` 的自述）**并不矛盾**：那条陈旧是因为**加了定理后没改自述**，
⇒ 而不是「注释不可信」。**

#### 由此引出第二类**可核对**的自述：**并入声明**

**⇒ 一句「`X.lean` 已并入本文件」断言 **X 不再存在**——那是关于树的事实，故**也会腐烂**。**
**⇒ 工具现在检查它：当前 **2 条声称 / 0 条陈旧**。**

#### 而**测试抓到了我自己的检查**

**⇒ 我注入一条「并入一个**存在**的文件」的声明：它被**计入**（3 条），却**未被标记为陈旧**。**
**⇒ 原因：声明给的是**裸文件名**，而我的存在检查把它拼到 `Lattice/` 下——那里没有该路径。**
**⇒ 修成**按基名搜索整棵树**：同一注入现在报 **STALE MERGE** 并 exit 1；干净的树 exit 0。**

**⇒ 这是本会话**第三次**：给检查器写测试，暴露的是**检查器**的 bug，而不是树的。**
### 3.118 **第 1158 轮：唯一那条**数学自述**——核对为真，并被**锚定到三条定理****

**⇒ 上轮的正面结论留下一条**未核对**的自述：`RealLayerSemanticQuotient` 的
「**穿过商单射的两个读法，一对一假**」。⇒ 本轮**逐条读定理**：**

| 声称 | 定理 | 陈述 |
|:--|:--|:--|
| 读法 A、朴素单射**为假** | `naive_injectivity_is_false` | `¬ (∀ c c', SemEqL (convertVec c) (convertVec c') → c = c')` |
| 读法 B、下降映射**单射真** | `semConv_injective` | `Function.Injective semConv` |
| 结构形式**为真** | `structural_form_is_true` | `∀ c c', convertVec c = convertVec c' → c = c'` |

**⇒ 三条都说了那句话所说的。⇒ 故**该自述准确**。**

#### 但「今天准确」不是「可核对」

**⇒ 陈旧的自述**今天也是准确的**——区别只在于读者**能不能核对它**。**
**⇒ 故把那三个定理名**写进自述**。⇒ 而 `check_doc_names` 已经会在「文档引用了不存在的名字」时失败。**
**⇒ 于是「自述这么说」变成「自述指着一个**工具链在看着的**东西」。**

**⇒ 这正是本会话的规则：**每一个可核对的说法，都应指向一个可核对的物**——而不是停在一句话上。**
### 3.119 **第 1159 轮：Lean 文件里的数字主张——**不值得做检查器**，而理由是可核对的**

**⇒ 普查：**110 个文件的**首段**含具体数字**（「N 行」「N 条定理」「N 处」）。**
**⇒ 天真检查给出 **105 处不一致**；加上**自指范围**后仍有 **22 处**，其中 **21 处「错」**。**

**⇒ 而逐例读实际句子后，**三例全是三类误报**：**

| 文件 | 原句 | 类别 |
|:--|:--|:--|
| `Runtime/ConvertVectorLinear.lean` | 「本文件**第 1 行**就是 `import Mathlib`」 | **行号引用**，不是计数 |
| `Lib/Editing/RealConversionStability.lean` | 「本文件**原先**含 58 个声明、约 **1922 行**」，「已拆入 4 个子模块」 | **历史记录**（下一句就说已拆） |
| `Lib/Convex/RealFarkas.lean` | 「本文件补上 …（**221–230 行**）显式登记的两处缺口」 | **范围引用**，不是本文件计数 |

**⇒ 故结论是**否定**的，而否定结论也是结论：**Lean 文件首段的数字，绝大多数是**历史**或**引用**，
⇒ 而不是**当前状态的自述**。⇒ 故**不该**为它们建检查器——那会造出一台专门误报的机器。****

#### 这与 `check_usage_claims` 的边界一致

**⇒ `check_usage_claims` 检查 **4 份用户文档**里的数字——那些是**当前状态**文档，数字必须现在为真。**
**⇒ 而 Lean 文件头是**记录**：它记的是**当时**为什么这样做。⇒ 二者**不是同一类文本**，故**不同治理**。**
**⇒ 这条区分写在这里，因为它此前从未被明说——而它解释了为什么 38.2% 的注释**并不需要**一个检查器。**

**⇒ 至此「可核对主张」这条线**收束**：四类已核对（零声明声称、并入声明、A1–A7 完整性、数学断言），
⇒ 第五类（数字）**判定为不该查**，且理由可核对。**
### 3.120 **第 1160 轮：我自己的定理**也是死的**——而纪律不该取决于工具往哪里看**

**⇒ 测本会话最后一批定理的链内消费者：**

| 定理 | 链内 | 同文件 |
|:--|--:|--:|
| `extract_after_repair_weak` | **1**（`LayerRepair`） | 0 |
| `sound_not_exact_gives_epsilon_gap` | 0 | 2 |
| `closed_loop_reinject_within` | 0 | 1 |
| 其余六条 | **0** | 0 |

**⇒ **9 条里 8 条链内为 0**。⇒ 而其中六条**不在相邻接缝上**，故 `TERMINAL_CONNECTORS`（门禁只管接缝）**覆盖不到它们**。**
**⇒ 即：**我自己的死定理处于未治理状态，而树的死定理都在治理之下。****

#### 修法：**第二张**、独立的登记表

**⇒ `chain_connectors.py` 新增 `SESSION_TERMINAL`（**7 条**，各带理由）+ `--session` 报告模式。**
**⇒ 它**不改变任何门禁**（其中的条目**不可能失败**）——它的唯一用途是：**理由活在树里，而不是在某一轮的笔记里。**

| 定理 | 终态理由 |
|:--|:--|
| `epsLinearRepair_sat_is_epsSat` | **判据同一**——链引用它，不复合它 |
| `epsLinearRepair_zero_is_linearRepair` | **两个对象之间的关系**，不是一步 |
| `sound_not_exact_gives_epsilon_gap` | **那条桥本身**，已在同文件内被消费 |
| `epsSat_passing_is_not_correctness` | **一条警告**：读者在相信容差判据前必须知道 |
| `layerPenalty_sound` | **实例是一个位置**，不是一步 |
| `twoSlopeLoop_run_components` | `iterate` 已定义 run，这条只说它在乘积上怎么分 |
| `closed_loop_reinject_within` | **容差形式**，已被其自身的 `ε = 0` 推导消费 |

**⇒ 验证：`--check` ok、`--self-test` ok、`--session` 打印 7 条、**22 项门禁 0 失败**。**

**⇒ 这条修正的意义：**纪律的适用范围不能由工具的盲区决定**。⇒ 工具看不到的地方，**人要把理由写下来**。**
### 3.121 **第 1211 轮：全树普查——**51% 的定理哪里都不用**，故「逐条登记」在数量上不可能**

**⇒ 用倒排索引一次遍历全树（10,286 条 theorem/lemma）：**

| 类别 | 数量 | 占比 |
|:--|--:|--:|
| **链内被消费**（别的文件用它） | **1,569** | **15%** |
| **仅本文件使用** | **3,445** | **33%** |
| **哪里都不用** | **5,272** | **51%** |
| 其中**已在三张登记表里** | **61** | — |
| **未登记** | **5,211** | **51%** |

**⇒ 故「逐条登记理由」在**数量上不可能**——5,211 条，任何表都会变成噪音。**
**⇒ 而这不是缺陷：本树是一座**陈述库**，其中一半是**叶子**：它们各自证明一个事实，被**散文引用**或**备引**，而不被复合。**
**⇒ 这也与 mathlib 同构：那里的绝大多数定理同样不被任何东西消费。**

#### 故治理的**正确形式**不是清单，而是**量**

**⇒ 本会话已用过这个形式两次：**`UNREGISTERED_BUDGET`（第 1107 轮）与**目标图的「链内」列**。**
**⇒ 对本类，可度量的不变量是**比例**：`链内 ≥ 15%`、`仅本文件 + 链内 ≥ 48%`。**
**⇒ 若某次改动把「链内」比例压到 15% 以下，那是**真的**退化（有人在造死定理），而**个别的**叶子不是退化。**

**⇒ 我没有在本轮建这个比例门禁**：它需要先确定**基线**与**容差**，而那要有一次**跨分支的测量**才可信。
**⇒ 但结论已可写：**治理到此为止用的不是「每条都有理由」，而是「每类都有量」**。**
### 3.122 **第 1162 轮：定理活性成为**比例门禁**——治理的最后一块**

**⇒ 本轮建工具 `gov/check_theorem_liveness.py` + 基线 `gov/theorem-liveness-baseline.txt`：**

```
链内 1,569（15.3%）· 仅本文件 3,445（33.5%）· 无使用 5,272（51.3%）
```

**⇒ **只有第一个**比率参与门禁**：它**不得跌破基线 − 2 点**（15.3 − 2 = 13.3%）。**
**⇒ 另两个**只打印、不判失败**——叶子是合法形状，门禁要抓的是**趋势**，不是叶子。**

**⇒ 为什么用**比率**而不是**计数**：库会长。⇒ 写三十条、其中五条被消费，是正常的；**
**⇒ 写三十条、**一条都不被消费**，才是退化——而**只有比率**能显示这个差别。**

#### 双向验证

| 情形 | 结果 |
|:--|:--|
| 现状（基线 15.3%） | **exit 0** |
| 基线抬到 18.0%（floor 16.0%） | **exit 1**：「15.3% fell 2.7 points below the baseline — the tree is producing theorems nothing consumes」 |

**⇒ 基线已写入；复现命令已加进入口文档 §6。**

#### 治理至此的**完整形态**

| 形式 | 覆盖 | 条目 |
|:--|:--|--:|
| **清单** | 目标载体 | 9 |
| **清单** | 接缝连接器 | 60 |
| **清单** | 本会话终态定理 | 7 |
| **清单** | 定义式证明 | 820（另有门禁） |
| **量** | **全树 10,286 条定理的活性比例** | **1 个** |

**⇒ 前四张表管「具体的洞」，最后一张管「**趋势**」。⇒ 而只有后者**能覆盖全树**。**
### 3.123 **第 1163 轮：基线也要被核对——两法对比，而它**支持了门禁的形式****

**⇒ 基线是我一手测的，故它本身是一个**未核对的声称**。⇒ 本轮用**独立实现**重测同一比例：**

| 方法 | 总数 | 链内 | 比率 |
|:--|--:|--:|--:|
| **读原文**（集合，非剥注释） | 11,105 | 2,604 | **23.4%** |
| **剥注释**（集合，独立实现） | 10,978 | 1,766 | **16.1%** |
| **本工具**（剥注释 + 倒排索引） | 10,286 | 1,569 | **15.3%** |

#### 差异**被解释**，而不是被忽略

**⇒ 第一行说明**读散文**会怎样：**+819 条幻影声明**（docstring 里提到 `theorem X`）与 **+1,035 个「消费者」**
（其实只是注释里的提及）。⇒ 这与第 1091/1106 轮的教训**同源**。**
**⇒ 第二行才是诚实的对照：**比率与本工具差 **0.8 点**（在 2 点容差内），而**计数差 692**——**
**⇒ 因为两个实现的**声明提取器**不同。**

#### 这恰是**门禁形式的实证**

**⇒ **比率对方法稳健，计数不稳健**。⇒ 故若当初用计数做门禁，它会**随提取器漂移**；**
**⇒ 而比率只在**真的**趋势变化时才动。⇒ **这不是理论偏好，而是一次两法对比给出的证据。**

**⇒ 已把这三行写进 `check_theorem_liveness.py` 的 docstring——**工具自己承载它的交叉验证记录**。**
### 3.124 **第 1164 轮：逆向链的**方向性**——**只有 3.2↔3.3 是双向的，而这是对的****

**⇒ 问题：闭环是「验证回路」，故形式上应当是**双向**的。⇒ 本轮测三对的方向。**

**⇒ 文本启发式**不足**（结果多为 `both/ambiguous`：`eps_repair_requires_descent` 的 `¬` 放在结论里，
⇒ 使「最后连接词」判据失真）。⇒ 故**逐条读**：**

| 定理 | 假设（来自） | 结论（关于） | 方向 |
|:--|:--|:--|:--|
| `eps_repair_requires_descent` | `Sat ↔ EpsSat`（3.2 判据） | 测度下降（3.3） | **3.2 → 3.3** |
| `extract_after_repair_weak` | `R.Sat ls`、`R.μ ls = 0`（3.3） | `AllSatisfied (extractLayer ls)`（3.2） | **3.3 → 3.2** |
| `step_fixed_of_sat` | `Sat x`（3.3） | `step x = (x, objective x)`（3.4） | **3.3 → 3.4** |
| `closed_loop_reinject_within` | `Sat y → \|objective y\| ≤ ε` | `\|objective (run …)\| ≤ ε`（3.4） | **3.3 → 3.4** |

**⇒ 故：`3.2 ↔ 3.3` **双向**（两条定理各取一侧作假设）；`3.3 → 3.4` **单向**（4 条全是这个方向）；**
**⇒ 而 `3.4 → 3.3` **没有任何**定理。**

#### 而这**不是缺口**，而是定义的方向

**⇒ 再注入是**派生操作**：它由「修复 + 写回 + 测量」组成，故**必然**从修复导出。**
**⇒ 反向（「验证写回」）**正是链路本身**——闭环就是那个**复合**，不是一条平行的反向定理。**
**⇒ 故「闭环是双向的」这句话只在**复合层面**成立：`repair → 写回 → 验证`，而**每一段是单向的**。**

**⇒ 结论：方向性**由设计决定，不是遗漏**。⇒ 而这条判断是**读出来的**，不是启发式猜出来的。**

**⇒ 本轮的方法记录：**文本启发式在此**失效**（`¬` 的位置骗过了它）——与第 1120 轮的教训同类：
⇒ **一个能读到语句、读不出意图的判据，不能用来判定方向。**'
### 3.125 **第 1165 轮：收官盘点——**19 个新文件全部可达**，而我的 grep 又撒了一次谎****

#### 一、终值（四工具重跑）

| 项 | 值 |
|:--|--:|
| `END_OF_CHAIN` | **9** |
| `TERMINAL_CONNECTORS` | **60** |
| `SESSION_TERMINAL` | **7** |
| `UNREGISTERED_BUDGET` | **0** |
| 条款 / 载体 | **14 / 44** |
| 定理活性 | **15.3% 链内 · 33.5% 仅本文件 · 51.3% 无使用** |
| 相邻条款对 | **9/12**（余 3 由接缝口径覆盖） |

#### 二、本会话新增 **19 个文件**，逐个核对可达性

**⇒ 其中 **11 个 Lean 文件** —— 我第一步用 `git grep "import …"  -- 'Lattice/**/*.lean'` 判它们「未接线」，**
**⇒ 而**六个被判死**。⇒ 复查发现：**那个通配不匹配根级的 `Lattice/Lib.lean` 与 `Lattice/Runtime.lean`。**
**⇒ 直接查根聚合器：**

```
Runtime.lean:103–105   ZeroDataSynthesis · EpsRepairBridge · EpsGap
Lib.lean:88–91         ZeroDataSynthesis · ResidualEpsRepair · CompileLaw · LayerPenalty
```

**⇒ 故 **11/11 全部接线**，`lake build Lattice` 会编译它们。⇒ **被判死的六个是**我的 grep**，不是树。**

**⇒ 另 8 个（2 文档 + 4 工具 + 2 数据）全部进入 `README` 或 §6 命令表。**

#### 三、`NEXT-STAGE.md` 三条路线**仍全为结案态**

| 路线 | 状态 |
|:--|:--|
| A 分层阻塞 | **结案：无便宜选项**（11 边 / 平秩=放水） |
| B 2.2 判据 | **结案：4 生产者 / 0 消费者** |
| C 任意度数接主链 | **完成（以否证）** |
| **D** 拆分最大文件 | **完成并合并**（5,523 → 4 文件，最大 1,534 行） |

**⇒ 而路线 D 是本会话**新增**的，且**已完成**——故入口清单从「三路线」变成「三结案 + 一完成」。**

#### 四、**方法**记录：这是本会话**第四次**「工具/检查自身有 bug**

| 次 | 谁错 | 表现 |
|--:|:--|:--|
| 1119 | **我的文档** | 引用不存在的 `evaluate`，被工具抓到 |
| 1134/1156 | **我的散文** | 复述了那句已被判假的话 |
| 1157 | **我的检查器** | 裸文件名拼成路径 ⇒ 漏报 |
| **1165** | **我的 grep** | 通配不匹配根级文件 ⇒ 六个「死」 |

**⇒ 四次的共同点：**被判定为问题的，往往先是我看它的方式**。**
⇒ 而**每次都是靠**换一种查法**发现的——不是靠想得更仔细。**
### 3.126 **W0-3a 完成：八个结构性恒绿，现在**能变红**（第 1172 轮）**

**⇒ 按规划的第一优先级执行。⇒ 三处缺陷，各修在**病因**上：**

**1. 五个 `--strict` 注册。** `check_layer_cycle` / `check_layer_health` / `check_layer_registry` /
`check_reference_archive` / `check_pipeline_stages` 都写着 `return 1 if strict else 0`，
**而五个注册**都没带那个参数**——作者写了失败路径，注册者从未到达它。**
**⇒ 先测量：带 `--strict` 五个**仍全部 exit 0** ⇒ 它们有真实内容、当前成立。⇒ 加参数**零代价**，只是给了牙齿。**

**2. 三态裁决。** `verify_g4` 在无工具链时 **exit 77**；`verify_all` 把 77 当 **SKIP**：
**打印、单独计数、**永不**计入「gating checks passed」**。⇒ 它原来的 `return 0` 等于「无法执行」被算成「过了一道门禁」。

**3. `check_g7` 改为报告器。** 它唯一的返回值是 0，而它自己的 docstring 论证过「删注册会让计数悄悄变小」。
**⇒ 两个约束可以同时满足：计数保留，且不再虚增门禁数。**

#### 改动**当场**暴露的两处连带缺陷（都已修）

| 暴露者 | 现象 | 修法 |
|:--|:--|:--|
| `check_selftest_coverage` | 立刻报 `check_g7` 的 **EXEMPTION ROT**：「豁免了但已不是门禁」 | 删该豁免项 |
| `check_usage_claims` | 两条正则把**字面数字**写死（`(105) 个门禁`）⇒ 文档改 104 后**匹配不到** | 改为 `(\d+)`——声称「文档写了 N」，N 必须**捕获**而非假定 |

**⇒ 实测：`VERIFY ALL [fast] PASS`，`126 = 104 门禁 + 22 报告器`，`--fast` 下 `93 = 104 − 11`。**
**⇒ `DELIVERY.md` 两句已改 104/22；三条带标签断言（126/104/22）全部 ok。**

**⇒ 这一步的意义正在于它**小**：没有新增数学，只是让**已有的检查真的能失败**——而规划自己说了，
⇒ **在检查不能失败之前，「修完某项后构建通过」这句话没有证据。**
### 3.127 **W0-3b 完成：两个腐化基线重建，**69 条免费逃逸预算取消**（第 1173 轮）**

**1. `escape_baseline` 扫描了**除自己主题外的一切**。** `scan()` 把 `"Reference"` 从 walk 里过滤掉
（第 265 轮的理由：archive 带 111 个 `admit`，计入会把「归档」本身报成回归）。
**⇒ 然后它拿**空集**去比**九文件**的基线** ⇒ `new`/`grown` 永空 ⇒ **只能返回 0**。
**⇒ 现在实测（**含** Reference）：全树**零逃逸文件**。⇒ 那条理由已过期（archive 已到 `archive/`，在 `Lattice/` 之外）
⇒ **删掉过滤器，让它走自己命名的那个区。**

**2. `intake-baseline` 在**发放 69 条免费逃逸**。** 它记着 `axiom=1, admit=68` 与**已不存在的文件**，
而 `gate.py` 只在**增长**时失败 ⇒ **最多可新增 69 处逃逸而不触发 I1/I2**。⇒ 重建成实测真相：**0/0/0/0 + 空列表**。

**3. 两处都**被证明能变红**。** 注入一个 `admit` 到 `Lattice/Reference/ZZProbe.lean`：
**⇒ `escape_baseline` exit 1 并点名该文件与其计数；`gate.py` I2 报 1 处；删除后两者恢复绿色。**

**4. README 两处陈旧（第一处由 `audit_counts` 抓到）⇒ 改为：**
- 「冻结 escape 基线条目 **69** 处历史逃逸」→ **0**；
- 第 57 轮那条「『全树 0 逃逸』是**错的**说法」——**现在它是对的**：全树确实 0，**含 Reference**。

**⇒ 实测：29 项门禁全绿，`VERIFY ALL [fast] PASS`（430.1 秒），`126 = 104 + 22`，`--fast` 下 93 通过。**
### 3.128 **W0-3c 起步：第一个「网关却写自己产物」的生成器改为**比较而非写入**（第 1174 轮）**

**⇒ 规划 W0-3c：七个生成器在**默认路径**重写自己的产物。⇒ 动手前先测量：**
**⇒ 七个在干净树上跑一遍，`git status` **为空** ⇒ 它们是**幂等**的。**
**⇒ 故缺陷不是「每次改」，而是**权威**：默认路径重写会**静默覆盖手改**，
⇒ 而 `check_slots.py` 正是在 `gate.py` I6 的路径上这么做的——**检查者撰写了自己的输入。**

#### 共享守卫 `gov/artifact_guard.py`

```
sync(path, text, allow_write) -> "unchanged"（不写）
                              -> "stale"    （不写；打印首个差异行）
                              -> "written"  （仅当 allow_write）
require_synced(results, script) -> exit 1，并给出修复指令
```

**⇒ `check_slots.py` 已接入，且 stale 已接到退出码。⇒ **三步验证**：**

| 步骤 | 结果 |
|:--|:--|
| 干净树 | 默认 **exit 0**，`SLOTS.md` 未被触碰 |
| 追加一行 | **`STALE gov/SLOTS.md -- line 39 differs`**，**exit 1** |
| `--write` | 恢复；其后的默认运行 **exit 0**，`git status` 干净 |

**⇒ 其余六处（`check_endtoend_content` 2 处、`audit_aliases` 2 处、`chain`、`proof_chain_geo`、
`gen_primitive_matrix`、`check_endtoend_floor`）**已登记为下一个增量**——
⇒ 一个共享规则建好了，剩下的是把九处调用点逐个接上，而不是六个各写一遍。**

**⇒ 实测：`VERIFY ALL [fast] PASS`（482.3 秒），`126 = 104 + 22`，93 通过；且**跑完后 `git status` 为空**——
⇒ 这正是规划给 W0-3c 的验收判据：「`git status` 后跑 `verify_all` ⇒ 无 tracked 文件被改」。**
### 3.129 **W0-3c 完成：六处默认路径生成器全部改为**比较而非覆盖**（第 1175 轮）**

| \u811a\u672c | \u4ea7\u7269 |
|:--|:--|
| `chain.py` | `gov/PROOF-CHAIN.md` |
| `proof_chain_geo.py` | `gov/PROOF-CHAIN-GEO.md` |
| `gen_primitive_matrix.py` | **`PRIMITIVE-MATRIX.md`\uff08\u4ed3\u5e93\u6839\uff0c**\u88ab\u8ffd\u8e2a**\uff09** |
| `check_endtoend_content.py` | `gov/ENDTOEND-CENSUS.md` |
| `audit_aliases.py` | `gov/ALIAS-CENSUS.md` |
| `check_slots.py` | `gov/SLOTS.md`\uff08\u4e0a\u8f6e\uff09 |

**⇒ `check_endtoend_floor.py` **不需要改**：它的写在 `--write-baseline` 之后（显式请求）。
⇒ 规划把它列为默认路径写者——**实测不是**。**

#### \u4e24\u5904**\u6d4b\u91cf\u903c\u51fa\u6765**\u7684\u4e8b\uff08\u89c4\u5212\u6ca1\u9884\u6599\u5230\uff09

1. **`PRIMITIVE-MATRIX.md` \u5728\u4ed3\u5e93\u6839\u4e14**\u88ab\u8ffd\u8e2a**\uff1b`gov/PRIMITIVE-MATRIX.md` \u662f\u53e6\u4e00\u4e2a**\u672a\u8ffd\u8e2a**\u8def\u5f84\uff08\u6211\u5148\u524d\u6d4b\u9519\u4e86\u5bf9\u8c61\uff09\u3002**
\ufe0f\u21d2 **\u4ea7\u7269\u4f4d\u7f6e\u5fc5\u987b\u4ece `OUT` \u8bfb\uff0c\u4e0d\u80fd\u4ece\u5176\u4ed6\u516d\u4e2a\u63a8\u65ad\u3002**
2. **\u5b88\u536b\u56e0\u6b64\u589e\u4e86 `expect_tracked`**\uff1a\u5bf9**\u4ece\u672a\u5165\u5e93**\u7684\u4ea7\u7269\uff0c\u300c\u7f3a\u5931\u300d\u4e0d\u662f\u7f3a\u9677\u3002
\u21d2 \u6ca1\u6709\u5b83\uff0c\u9ed8\u8ba4\u8def\u5f84\u4f1a\u5728**\u5e72\u51c0\u6811**\u4e0a\u5931\u8d25\u2014\u2014\u6b63\u597d\u53cd\u4e86\u610f\u56fe\u3002**

#### \u9010\u5904\u9a8c\u8bc1 + \u6574\u4f53\u9a8c\u8bc1

**\u21d2 \u9010\u5904\uff1a\u6270\u52a8\u88ab\u8ffd\u8e2a\u4ea7\u7269 \u2192 `STALE <file> -- line N differs` + **exit 1**\uff1b`--write` \u6062\u590d\uff1b\u968f\u540e\u9ed8\u8ba4 exit 0\u3002**
**\u21d2 \u6574\u4f53\uff1a`VERIFY ALL [fast] PASS`\uff08527.2 \u79d2\uff09\uff0c`126 = 104 + 22`\uff0c93 \u901a\u8fc7\uff1b**
**\u21d2 **\u8dd1\u5b8c\u540e `git status` \u53ea\u663e\u793a\u672c\u6b21\u811a\u672c\u6539\u52a8\u2014\u2014\u65e0\u4efb\u4f55\u4ea7\u7269\u88ab\u6539**\u3002\u21d2 \u8fd9\u6b63\u662f\u89c4\u5212\u7ed9 W0-3c \u7684\u9a8c\u6536\u5224\u636e\u3002**
### 3.130 **W0-3e (1/3)：否证普查的盲区已修——**+193 声明 / +3 否证**（第 1176 轮）**

**\u21d2 \u65e7\u6b63\u5219 `^(?:theorem|lemma)` \u4e0d\u5bb9\u4efb\u4f55\u524d\u7f00\u3002\u21d2 \u653e\u5bbd\u540e\u5b9e\u6d4b\uff1a**

| \u53e3\u5f84 | \u53ef\u89c1\u58f0\u660e | \u5426\u8bc1 |
|:--|--:|--:|
| \u65e7 | 10,098 | **371** |
| \u65b0 | 10,291\uff08**+193**\uff09 | **374**\uff08**+3**\uff09 |

**\u21d2 \u800c\u65b0\u589e\u7684\u4e09\u6761\u662f**\u771f**\u7684\uff0c\u4e0d\u662f\u566a\u58f0\uff1a**

| \u4f4d\u7f6e | \u540d\u5b57 | \u4e3a\u4f55\u6b64\u524d\u4e0d\u53ef\u89c1 |
|:--|:--|:--|
| `Compose/ComposeObligation.lean` | `blocked_pre` | **`private theorem`** |
| `Lib/Compiler/RealTreeDecidable.lean` | `isoList_nil_cons` | **`@[simp] theorem`** |
| \u540c\u4e0a | `isoList_cons_nil` | **`@[simp] theorem`** |

**\u21d2 \u6545\u76f2\u533a\u6b63\u662f\u89c4\u5212\u70b9\u540d\u7684\u4e24\u7c7b\uff08\u5c5e\u6027\u3001\u4fee\u9970\u7b26\uff09\uff0c\u800c\u8ba1\u6570\u5c11\u4e86\u4e09\u3002**

**\u21d2 `REFUTATION-CENSUS.md` \u540c\u6b65\uff1a\u603b 371\u2192374\u3001`Lib` 258\u2192260\u3001`Compose` 1\u21922\u3002**

**\u21d2 \u53e6\u52a0 **BOM \u5bb9\u5fcd**\uff08\u5e76\u9644\u5b9e\u6d4b\uff1a1,124 \u4e2a\u6587\u4ef6\u4e2d **0** \u4e2a\u4ee5 BOM \u5f00\u5934\uff09\u2014\u2014**
**\u21d2 \u5b83\u662f**\u9632\u5fa1\u6027**\u7684\uff1a\u82e5\u67d0\u6587\u4ef6\u5e26 BOM\uff0c\u5b83\u7684**\u7b2c\u4e00\u6761\u58f0\u660e**\u4f1a\u9759\u9ed8\u5730\u4e0d\u88ab\u770b\u89c1\u3002**

**\u21d2 **\u53cc\u5411\u9a8c\u8bc1\uff1a**\u65e0 BOM \u63a2\u9488\u58f0\u660e `private theorem zz_ref_probe : \u00ac (True = False)` \u2192 \u666e\u67e5\u4e0d\u4e00\u81f4\u3001**exit 1**\uff1b**
**\u21d2 \u5220\u9664\u540e **exit 0**\u3002\uff08\u7b2c\u4e00\u6b21\u7528 PowerShell \u5199\u7684\u63a2\u9488**\u5e26 BOM**\uff0c\u6545\u672a\u88ab\u8ba1\u5165\u2014\u2014BOM \u95ee\u9898\u6b63\u662f\u8fd9\u6837\u53d1\u73b0\u7684\u3002\uff09**

**\u21d2 \u800c `check_usage_claims` **\u5f53\u573a**\u6293\u5230 `USAGE.md` \u5199 371\uff08\u5b9e\u6d4b 374\uff09\u2192 \u5df2\u6539\u3002**
**\u21d2 README:49 \u7684 **284** \u540c\u5c5e\u4e00\u6570\uff0c\u4ecd\u9519\uff1b\u5df2\u5728\u89c4\u5212 W0-4 \u6e05\u5355\u91cc\uff0c\u4e14**\u4e0d**\u5728 `check_usage_claims` \u7684\u8986\u76d6\u8303\u56f4\u5185\u2014\u2014\u6545\u5b83\u6d3b\u5230\u4eca\u5929\u3002**
### 3.131 **W0-3e 完成：一项**真修**、一项**实测为零**（第 1177 轮）**

**1. `check_literal_rfl` \u5f15\u7528\u4e86**\u6563\u6587**\u3002**\u21d2 `citations()` \u8bfb\u539f\u6587\uff0c\u6545**\u53ea\u88ab docstring \u63d0\u5230**\u7684\u5b9a\u7406\u88ab\u5f53\u4f5c\u300c\u88ab\u5f15\u7528\u300d\u3001\u56e0\u800c\u7b97\u4f5c API\u3001\u9003\u51fa\u53f6\u8282\u70b9\u95e8\u7981\u3002
\u21d2 \u73b0\u5728\u8bfb**\u5265\u6ce8\u91ca**\u540e\u7684\u6e90\u7801\uff08\u4e0e liveness \u540c\u4e00\u4e2a\u6743\u5a01\uff1a`tools.lean_source.strip_comments`\uff09\u3002

**\u21d2 \u800c**\u5b9e\u6d4b\u5dee\u5f02 = **0**\uff1a**116 \u627f\u91cd / 83 \u88ab\u95e8\u7981 / 38 \u5176\u4ed6**\uff0c\u524d\u540e**\u5b8c\u5168\u76f8\u540c**\u3002**
**\u21d2 \u6545\u89c4\u5212\u63cf\u8ff0\u7684\u90a3\u6761**\u9003\u51fa\u8def\u5f84\u5728\u672c\u6811\u4e0a\u4e0d\u5b58\u5728**\u3002\u21d2 \u4fee\u6cd5\u4fdd\u7559\uff08\u539f\u7406\u4e0a\u300c\u628a\u6563\u6587\u5f53\u8bc1\u636e\u300d\u5c31\u9519\uff09\uff0c\u4f46\u5982\u5b9e记为**\u9884\u9632\u6027**\u3002**

**2. `audit_counts` \u4e24\u5904**\u91cf\u9519\u4e86\u5bf9\u8c61**\u3002**\u21d2 \u5b83\u67e5 `Lattice/Reference/LvFormal`\uff08**\u4e0d\u5b58\u5728**\uff0c\u5f52\u6863\u5df2\u5230 `archive/LvFormal`\uff09\u21d2 \u8fd4\u56de `None` \u21d2 \u6253\u5370\u300c\u65e0\u6cd5\u5b9e\u6d4b\u300d\u21d2 **\u9759\u9ed8\u5730\u4e0d\u8ba1 mismatch**\u3002
**\u21d2 \u800c\u300cLvFormal \u6587\u4ef6\u6570\u300d\u90a3\u884c\u5bf9\u6bd4\u7684\u662f `ref`\uff08**\u6574\u4e2a `Reference`** = 100\uff09\uff1b\u6070\u597d\u7b49\u4e8e\u58f0\u79f0\u503c\uff0c**\u4e8e\u662f\u5de7\u5408\u88ab\u5f53\u6210\u4e00\u81f4\u3002**

**\u21d2 \u73b0\u5728\uff1a\u76ee\u5f55\u663e\u5f0f\u67e5\uff08`archive/LvFormal` \u2192 \u65e7\u8def\u5f84\uff09\uff1b\u7f3a\u5931\u8fd4\u56de **-1** = **MISMATCH**\uff1b\u6587\u4ef6\u6570\u884c\u6539\u6bd4**\u5b83\u81ea\u5df1**\u3002**

| \u5b9e\u6d4b | \u503c |
|:--|--:|
| `archive/LvFormal` .lean | **103** |
| \u60ac\u7a7a `Zero.*` import | **0** |

**\u21d2 README \u7684\u300c0\u300d\u662f**\u5bf9**\u7684\uff1b\u300c100\u300d\u662f**\u91cf\u9519\u4e86\u603b\u4f53**\u3002\u21d2 \u5df2\u6539 100 \u2192 **103**\u3002**
**\u21d2 \u53cc\u5411\u9a8c\u8bc1\uff1a\u628a\u76ee\u5f55\u6539\u540d\u79fb\u8d70 \u2192 \u4e24\u884c\u5747 **\u5b9e\u6d4b -1 MISMATCH**\u3001**exit 1**\uff1b\u6539\u56de \u2192 **exit 0**\u3002**

**\u21d2 \u6545 W0-3e \u7684\u4e09\u9879\u91cc\uff1a\u4e00\u9879**\u771f\u4fee**\uff08\u5426\u8bc1\u666e\u67e5\u6b63\u5219\uff0c+3 \u5426\u8bc1\uff09\u3001\u4e00\u9879**\u5b9e\u6d4b\u4e3a\u96f6**\u3001\u4e00\u9879**\u771f\u4fee**\uff08LvFormal \u5bf9\u8c61\u9519\uff09\u3002**
### 3.132 **W0-1 完成：七组同 FQN 双声明全部消除（第 1179 轮，分支 `merge-fqn-duplicates`）**

**⇒ 七对名字在**两个文件**里各声明一次，两侧都在 `Lattice.lean` 的闭包内 ⇒ 任何 `rw`/`unfold` 看到的**证明体取决于 import 顺序**。**
**⇒ 第 1172 轮已定论失败模式（构建通过、**后 import 者静默胜出**）并定位每组胜者；本轮**删掉重复**。**

#### 为什么安全

**⇒ 四组「定义体不同」的，实测**命题完全相同**：`abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`/`dot_replicate_zero` 只差**绑定名与证明**；**
**⇒ `tanh_pos_of_pos` 是**逐字相同**。⇒ 故这是**去重**，不是语义合并。**

#### 处置规则：**保留「被导入更少」的文件**（新增 import 的爆炸半径更小）

| 名字 | 保留 | 新 import |
|:--|:--|:--|
| `dot_replicate_zero` | `Runtime/DotTruncationDefect`（1 importer） | `LayerComposition` → 它 |
| `tanh_pos_of_pos` | `Lib/Lift/…_parts/B`（2） | `RealExtractInvertibility` → 它 |
| `extractVec_convertVec_rfl` | `Lib/Editing/RealExtractSurjectivity`（2） | `RealCanonicalCompileComm` → 它 |
| `abs_cos_sub_cos_le` / `abs_sin_sub_sin_le` | `Lib/Attention/RealRoPEExtrapolation`（1） | `RealAbsPosEncoding` → 它 |
| `dot_replicate_zero_any` | `Runtime/LayerComposition` | `RealConstraintEdit` → 它 |
| `convertVec_extractVec_rfl` | `RealExtractSurjectivity` | （另一侧只散文引用） |

**⇒ 第一组的注释**自己写着「本文件不 import `LayerComposition`」——**实测 `Lib → Runtime` 是向下、且无环** ⇒ **理由过期了，重复没过期。**

#### 删声明逼出的记账（**每一处都是门禁抓到的，不是靠记忆**）

| 项 | 变化 |
|:--|:--|
| 定理 / 声明 | **10,300 → 10,293** / **13,885 → 13,878**（5 份文档） |
| `PROOF-DEBT` 覆盖表 | 承重 1117→**1120**、已审 1105→**1108**、零入度 8981→**8978**、抽审 403→**400** |
| `duplicate-name-classes.txt` | 删 7 行（已不再共享） |
| `verdict-stale-baseline.txt` | **7 条判决记为 RESOLVED**，各写明存活文件 |
| 别名基线 | 930 → **927** |
| 端到端地板 | 重生成，并**写明两条「LOST」是**同名移位**（`RealConstraintEdit→LayerComposition`、`LayerComposition→DotTruncationDefect`） |

**⇒ 地板按 **(文件, 名字)** 计，故**移位看起来像丢失**——这恰是它该做的、也是从它**不该**得出的结论（其自己的 docstring 已警告同类）。**

#### 规划**不知道**的两份额外副本

**⇒ `extractVec_convertVec_rfl` 全树有 **4** 处，不是 2 处。⇒ 其中**两处是 `/-! … -/` 文档里的 Markdown 代码块引用**，**
**⇒ **根本不是声明**——是**原文 `git grep` 数出来的**。⇒ 真实定义点：**1**。**

**⇒ 实测：`lake build Lattice` exit 0；分支 `VERIFY ALL [fast] PASS`（605.7 秒）；master 复验 `PASS`（686.5 秒），工作区干净。**
### 3.133 **W0-3f GATE-1：把「每个门禁都能失败」变成树上的一条门禁（第 1180 轮）**

**⇒ 第 1172 轮那八个结构性恒绿，是我**读源码读出来的**——那是**我注意力的属性**，不是树的属性。本轮把它变成树的属性。**

```
门禁通过 ⟺ 它的退出表达式中至少有一个不是字面 0 / None / False
```

**⇒ 实扫 **104** 个门禁注册，全部通过；`check_g7` 那种「唯一退出是 `return 0`」的形态会失败。**

#### 两个版本先后被推翻（**都是本会话的老形状**）

| 版本 | 错在哪 |
|:--|:--|
| v1 | 用 **`tools.lean_source.strip_comments`（Lean 的剥离器）**处理 **Python** ⇒ `audit_aliases.py` 从 11,233 字节被切成 2,407 ⇒ **12 处假报**。⇒ 剥离器是**语言特定**的。现改用 `tokenize`（语法错误时退回原文，只可能更宽松） |
| v2 | 找**失败字面量** ⇒ 误判 `gate.py`，它的失败是**从字典取值**：`return EXIT["AXIOM"]`。⇒ 逐个拼写去堵是打地鼠。⇒ 故**把性质写在另一侧**：「**不是**全是字面零退出」——这恰好就是 stub 的形状，别无其他 |

**⇒ 自测植入三种形态，含**打脸 v2 的字典取值**。⇒ 3/3 正确。**

#### 它证明什么、不证明什么

**⇒ **必要不充分**，docstring 写明：一个脚本可以在**没有任何树状态能到达的分支**上写 `return 1`——**
**⇒ 那正是**藏了几十轮的 `--strict` 形状**。⇒ 逐个植入缺陷是规划的下一步；本轮闭合的是「**完全没有失败路径**」这一类。**

#### 注册后计数连带暴露的三处同族缺陷

| 处 | 现象 |
|:--|:--|
| `check_usage_claims` | **总检查数**的正则仍写死字面 `(126) 项检查`——**两轮前刚为门禁/报告器修过同一处，漏了它** |
| `check_doc_consistency` | `PLAN-STAGES` 与 `MACRO-COGNITION-148` 仍写 126 ⇒ 二者都是**按轮冻结的快照** ⇒ 与 `ROADMAP-v*` 一同入 `FROZEN`（**理由写在下一读者能找到的地方**） |
| `MACRO-COGNITION.md`（现行那份） | 写「126 项检查（99 门禁 + 21 报告）」——**三处全错** ⇒ 改为实测值；其余陈旧数仍登记为他人所有 |

**⇒ 实测：`VERIFY ALL [fast] PASS`（655.7 秒），`127 = 105 + 22`，94 通过；自测 3/3。**
### 3.134 **W0-2 完成：三套秩表合一，层清单不再靠「记住」（第 1181 轮）**

**⇒ 规划说 `layers.py` 是零 importer 的死代码。⇒ 实测它有**一个** importer：`check_layer_health.py` 用 `layers.RANK`。**
**⇒ 故真实缺陷比规划描述的**更严重**——**两张都活着的表**，双双自称权威，在**十四个层里八个不同**：**

```
Semantics 5 vs 4   Reference 4 vs 7   Plugins 3 vs 5   Usage 7 vs 6
Evidence 5 vs 6    Compose 6 vs 4     CInterface 6 vs 5  Slots 1 vs 3
```

**⇒ `layers.py` 自称「SINGLE AUTHORITATIVE」，而**执行者**（`gate.py` 的 I4）读的是另一张。**
**⇒ **两张都声称权威 = 文档里一个计数两个值**，同一个病。**

#### 做了什么

| 处 | 动作 |
|:--|:--|
| `gate.py` | 秩字典提为模块级 `RANK`——**唯一那张**；`check_layering` 读它，不再留第二份 |
| `gate.py` | 删 **3 个死键** `lift`/`geo`/`domains`（实测：`LAYER_OF` 能返回的 14 个 zone 恰是剩下那些；`domains` **没有任何前缀**，`lift`/`geo` 只来自**不存在的两个目录**）+ 删那两个死前缀。`top` **保留**（它是落空值，第 889 轮的注释记着把它误当真实层的后果） |
| `layers.py` | `RANK` **派生**自 `gate.RANK`（经显式 zone→namespace 映射；`audit` 覆盖 `Audit` **与** `Semantics`，因为 `LAYER_OF` 把 `Lattice/Semantics` 映到 `audit`） |
| `layers.py` | `LAYER_ORDER` 派生并按秩排序；`CANONICAL` **从磁盘读**——旧字面列的三个目录**都已不存在**（`Lattice/` 有 11 个子目录，`Slots` 是**文件**，故追加） |
| 4 个 audit 脚本 | 同一份八字面 → 改为 `from layers import CANONICAL` |

#### 为什么派生强于「比较门禁」

**⇒ 规划要求加一条「两表必须一致」的检查。⇒ 改完之后**只有一张表**，那样的检查等于**拿同一个东西比自己**。**
**⇒ 结构事实比那条检查更强。⇒ 而 `check_layer_registry.py` 仍在跑：它抓到最后两处不一致**
**⇒ （`CANONICAL` 对磁盘、`LAYER_ORDER` 对 `RANK`），现在 `--strict` 通过。**

#### 回归

**⇒ `gate.py` 前后打印**同样八条判定**、全 ok——**删死键没有改变任何 finding**。**
**⇒ 实测：手工 25 项门禁全绿；`VERIFY ALL [fast] PASS`（661.8 秒），`127 = 105 + 22`，94 通过。**
### 3.135 **GATE-2 落地：一个被文档引用的计数，只在**一处**测量（第 1182 轮）**

**⇒ 三份文档引同样的九个量，而三个工具各测一遍。⇒ `check_usage_claims.py` 曾自带 `measure_modules`、**
**⇒ `measure_theorems`、`measure_decls`，与 `audit_counts.py` 的同名者**并存**——「有多少模块」「有多少定理」各两份实现。**
**⇒ 当天它们恰好一致。⇒ **恰好一致不是一致**。**

#### 做了什么

| 处 | 动作 |
|:--|:--|
| `audit_counts.py` | 新增 `total_declarations()`——该量原本**只有一个家**（`check_usage_claims`），这是同一缺陷的**反面伪装**：一个只有一个家的量**根本无法被交叉核对** |
| `check_usage_claims.py` | 删掉三个本地定义，**直接调用**那个家（顶层 import，**不是**包装 `def`） |
| `check_single_source_counts.py` | 门禁本身：其余 `gov/*.py` **不得定义**任何测量名；`--self-test` 植入一个重实现并要求被标记 |

#### 两处**自己的错**被自己的自测抓到

1. **包装式 `def` 仍是第二个定义。** 第一版委托留下了
   `def measure_modules(): from audit_counts import module_total; return module_total()`——**三行包装**，
   **⇒ 能骗过读者、骗不过性质**。⇒ 该情形已**永久写入**自测，失败信息也写明。
2. **搬一个测量必须搬它的**定义**，不只是它的名字。** 我第一版 `total_declarations()` 用了更宽的正则
   （多含 `instance`/`example`）⇒ 返回 **13,951** 而文档是 **13,878**——**73 条从未被计入的声明**。
   **⇒ 正则已改成**逐字照抄**，差异记录在函数所在处。**

#### 注册与连带

**⇒ `128 = 106 门禁 + 22 报告器`（原 127 = 105 + 22）。⇒ 四条计数声称随之更新，而 `check_doc_consistency` 又抓到最后一个**
**⇒（`MACRO-COGNITION` 仍写 127）。**

**⇒ 实测：手工 29 项门禁全绿；`VERIFY ALL [fast] PASS`（758.5 秒），`128 = 106 + 22`，95 通过；GATE-2 自测 PASS。**
### 3.136 **GATE-3 落地：三件「我手工验过的事」变成树的性质（第 1183 轮）**

**⇒ W0-3c 那六处是**一个下午里逐处扰动验过的**。那是**那六个下午的性质**，不是树的性质。**

| # | 断言 | 实测发现 |
|--:|:--|:--|
| 1 | **默认路径不得写 tracked 产物** | 八个生成器逐一登记；须 **import `artifact_guard` 并调 `sync(`**，或提供**比较式 `--check`** |
| 2 | **每个 `.bak` 必须被忽略** | **三处写 `.bak`，只有一处被忽略** ⇒ `.gitignore` 补全三式；**glob 写法**，故第四个脚本的备份**由构造覆盖** |
| 3 | **§6 的命令必须存在** | 只限**§6**——那里是文档说「跑这条来检查我」的唯一位置；散文里提到脚本只是**引用** |

#### 我第一版里的四处假报（**全是本会话的老形状**）

| 假报 | 根因 |
|:--|:--|
| 六个生成器「从不调 `sync(`」 | `tokenize` 剥注释后用**空格连接 token** ⇒ `sync(` 变 `sync (` ⇒ **它自己造的空格骗了自己** |
| 门禁**扫到自己** | 自测字符串里含 `.bak` 名字 |
| `gate_reactivity.bak` 未忽略 | glob 构造 `"*" + name` **丢了前导点** |
| `chain_connectors` 被拒 | 我加了 `"argparse" not in src`——**一个与 `--check` 毫无关系的条件** |

**⇒ 实测：手工 30 项门禁全绿；`VERIFY ALL [fast] PASS`（605.1 秒），`129 = 107 + 22`，96 通过；GATE-3 自测 PASS。**
### 3.137 **W0-4（6/16）：六处陈旧断言按实测改正，而最大那条现在**有人看守**（第 1184 轮）**

| 处 | 改动 | 依据 |
|:--|:--|:--|
| `README:49` | 否证 **284 → 374**，**并纳入 `check_usage_claims`** | 该行**自称**由 `check_refutation_census.py` 看守，**而那个工具只读普查文档**，从不读 README |
| `DELIVERY-COMPILER:125` | 10,099 → **10,293** | 密度句的分母 |
| `PROOF-DEBT:66` | 保留 10,098，**标明是「唯一短名」**，并在旁给出官方 **10,293** | 两个数是**不同总体**，且各自别处都在用 |
| `PLUGIN-SYSTEM:2348` | 那句 Lean 代码是**错的**：`loadAll (loadAll ms)` | 实测 `loadAll : (s : LoaderState) (ms : List LoaderManifest) : LoaderState`（`Bootstrap.lean:62`）；幂等是**观察**幂等（`:122`） |
| `ARCHITECTURE-DECISIONS:148` | 「`loadAll`/`LoaderState`/`Manifest` 全部 0 定义」**已推翻** | 三者**都存在**（`:62` / `:47` / `:39`） |
| `SYMBOL-WEIGHT-COMPARISON:82` | 「再强的改造也不会改变它」**收窄** | `RealLayer.lean` **已给共同推广**（`:120` / `:130`）⇒ 不可嵌入只在**整数精确截面** |

**⇒ 最重要的一条是 `README:49`：它证明了**一个数字若其被引用的工具并不读它，就没有人看守它**。**
**⇒ 故修法是**先加断言并让它红**（284 vs 374，exit 1），**再**改文档。**

**⇒ 而 `ARCHITECTURE-DECISIONS:148` 那条暴露了另一件事：我第一次 `git grep` 那三个名字得到「0 定义」，**
**⇒ 而 `Bootstrap.lean:62` 明明有 `def loadAll`——**是我的模式坏了，不是树**。⇒ 文档里现在引的是改正后的测量。**

**⇒ 六处中三处属他人文件：每条都**引一个实测的 Lean 事实与行号**，而不是判断，并在原处写明为何改。**

**⇒ 实测：手工 30 项门禁全绿；`VERIFY ALL [fast] PASS`（573.5 秒），`129 = 107 + 22`，96 通过。**
### 3.138 **W0-4（\u7ee7）：**插件槽收集器漏掉了一整个插件**，而规划的一条是**错的**（第 1185 轮）**

#### 1. `audit_plugin_slots.py` **\u6309\u4f4d\u7f6e\u6536\u96c6\u5b57\u6bb5**

```python
if field != FIELDS[len(out)]: continue
```

**\u21d2 \u5b57\u6bb5\u987a\u5e8f\u4e0d\u540c\u7684\u63d2\u4ef6\u4f1a\u88ab\u9759\u9ed8\u4e22\u5f03\u90a3\u4e00\u4e2a\uff1b\u800c\u4e0d\u8db3 12 \u4e2a\u65f6\uff0c`measure()` \u76f4\u63a5 `continue` \u8df3\u8fc7**\u6574\u4e2a\u63d2\u4ef6**\u3002**
**\u21d2 `Tokens` \u628a `completeness` \u5199\u5728 `approximation` \u4e4b\u524d \u21d2 **\u5b83\u7684\u516b\u4e2a\u5b57\u9762 `True` \u4ece\u672a\u88ab\u8ba1\u5165**\u3002**

**\u21d2 \u4fee\u540e\u5b9e\u6d4b\uff1a**132 \u69fd\uff0811 \u4e2a\u63d2\u4ef6\uff09\u3001**55 \u4e2a\u5b57\u9762 `True`**\uff1b\u5de5\u5177\u539f\u62a5 120 \u69fd / 47\u3002**
**\u21d2 \u6536\u96c6\u5df2\u6539\u4e3a**\u6309\u540d\u5b57**\uff1b\u7f3a\u5931\u7684\u5b57\u6bb5\u4ea4\u7ed9\u8c03\u7528\u8005\u62a5\u544a\uff0c\u800c\u4e0d\u662f\u88ab\u9759\u9ed8\u91cd\u6392\u3002**
**\u21d2 \u57fa\u7ebf 47 \u2192 **55**\uff0c\u63d2\u4ef6\u6570\u4ece 10 \u6539\u4e3a **11**\uff0c\u7406\u7531\u5199\u5728\u6570\u5b57\u6240\u5728\u5904\u3002**

#### 2. \u89c4\u5212\u7684\u300c`ProofSlotCensus` 87 \u2192 55\u300d**\u662f\u9519\u7684**\u2014\u2014**\u800c\u57fa\u7ebf\u6587\u4ef6\u81ea\u5df1\u65e9\u5c31\u8bf4\u4e86\u4e3a\u4ec0\u4e48**

**\u21d2 \u5b83\u7684\u5934\u90e8\u5199\u660e\uff1a87 \u8ba1\u7684\u662f `proof_holds` \u9879\u91cc `True.intro` **\u4e0e** `trivial` \u7684**\u95ed\u5408**\uff0c\u4e14\u542b\u591a\u4e00\u4e2a\u63d2\u4ef6\u6587\u4ef6\uff1b**
**\u21d2 \u800c\u672c\u8ba1\u6570\u8bf4\u7684\u662f\u69fd\u4f4d**\u503c**\u3002\u21d2 **\u4e24\u4e2a\u4e0d\u540c\u95ee\u9898\uff0c\u4e24\u4e2a\u90fd\u5bf9\u3002**
**\u21d2 \u82e5\u6309\u89c4\u5212\u6539\uff0c\u5c31\u662f**\u62ff\u4e00\u4e2a\u6b63\u786e\u7684\u6570\u53bb\u6362\u4e00\u4e2a\u5b9a\u4e49\u4e0d\u540c\u7684\u6570**\u3002\u21d2 \u521a\u597d\u8bb0\u5f55\u5728\u539f\u5904\u3002**

#### 3. README \u4e09\u884c

| \u884c | \u65e7 | \u65b0 |
|:--|:--|:--|
| \u5c42\u6587\u4ef6\u6570 | `23 / 0 / 4 / 66 / 99 / 625`\uff08**\u4e94\u4e2a\u6807\u7b7e\u5bf9\u516d\u4e2a\u6570**\uff0c\u4e14\u56db\u4e2a\u63cf\u8ff0\u5df2\u4e0d\u5b58\u5728\u7684\u76ee\u5f55\uff09 | **`179 / 0 / 0 / 0 / 689`**\uff0c\u65e7\u503c\u4f5c\u4e3a\u6821\u6b63\u4fdd\u7559 |
| \u68c0\u67e5\u5668\u6ce8\u518c\u9879 | 67 | **129**\uff08107 + 22\uff09\uff0c\u4e14\u6539\u6307\u771f\u6b63\u6d4b\u5b83\u7684\u5de5\u5177 |
| Lv-00 | \u300c121 \u4e2a\u6a21\u5757\u4e2d **56 \u4e2a\u6784\u5efa\u5931\u8d25**\u300d | **103 \u4e2a\u6587\u4ef6 / 0 \u4e2a\u60ac\u7a7a import** \u2014\u2014**\u4e24\u4e2a\u6570\u90fd\u9519** |

**\u21d2 \u5b9e\u6d4b\uff1a\u624b\u5de5 28 \u9879\u95e8\u7981\u5168\u7eff\uff1b`VERIFY ALL [fast] PASS`\uff08665.4 \u79d2\uff09\uff0c`129 = 107 + 22`\uff0c96 \u901a\u8fc7\u3002**
### 3.139 **\u5148\u6d4b\u91cf\u518d\u52a8\u624b\uff1a\u89c4\u5212 ADR-E \u7684\u524d\u63d0**\u4e0d\u6210\u7acb**\u2014\u2014\u6545\u7528\u95e8\u7981\u4ee3\u66ff\u91cd\u6784\uff08\u7b2c 1186 \u8f6e\uff09**

**\u21d2 \u89c4\u5212\u628a\u300c\u63d2\u4ef6 `consistent` \u6309 kind \u7d22\u5f15\u300d\u5217\u4e3a**\u7b2c\u56db\u4f18\u5148\u7ea7**\uff0c\u5e76\u63cf\u8ff0\u4e3a**\u7f3a\u9677**\uff1a**
**\u300cmanifest \u8bf4 `.spatial` \u800c `proof.spatial = True` \u65f6\u4ecd\u901a\u8fc7\u300d\u3002**

**\u21d2 \u5728\u5199\u90a3\u4e2a\u8de8 `Registry.lean` + 11 \u4e2a `Plugin.lean` + `Plugins.lean` \u7684 `ProofFieldOf` \u6620\u5c04\u4e4b\u524d\uff0c\u5148\u6d4b\u4e86\u5b83\u662f\u5426\u5b58\u5728\u3002**

#### \u5b83\u4e0d\u5b58\u5728

| \u63d2\u4ef6 | \u58f0\u79f0\u7684 kind \u6570 |
|:--|--:|
| Attention / Conv / DAG | 3 / 3 / 3 |
| GNN / Norm | 11 / 6 |
| Compose / Constraint / Repair | 10 / 4 / 8 |
| Penalty / Tokens / ChainSlot | 7 / 7 / 12 |

**\u21d2 \u5b9e\u6d4b\uff1a**0 \u5904\u300c\u58f0\u79f0\u4f46\u7a7a\u300d**\u3002\u21d2 \u6bcf\u4e2a\u58f0\u79f0\u7684 kind \u90fd\u6709**\u975e `True`** \u7684\u8bc1\u660e\u5b57\u6bb5\u3002**

**\u21d2 \u800c**\u771f\u7684**\u90a3\u53e5\u8bdd\u66f4\u5f31\u4e5f\u66f4\u51c6\u786e\uff1a`Registry.lean:110` \u662f `obligations \u2260 [] \u2192 proof.Holds`\uff0c**
**\u21d2 \u800c `Holds` \u8981\u6c42\u5168\u90e8\u5341\u4e8c\u4e2a\u5b57\u6bb5\uff0c\u6545**\u4e00\u4e2a `True` \u5b57\u6bb5\u88ab\u767d\u9001**\u2014\u2014**
**\u21d2 **\u7c7b\u578b\u5141\u8bb8\u8fd9\u4e2a\u9519\uff1b\u6811\u4e0a\u6ca1\u6709\u8fd9\u4e2a\u9519**\u3002\u21d2 \u6545\u5de5\u4f5c\u7684\u6027\u8d28\u662f**\u9884\u9632**\uff0c\u4e0d\u662f**\u4fee\u590d**\u3002**

#### \u6545\u505a\u7684\u662f**\u95e8\u7981**\uff0c\u4e0d\u662f\u91cd\u6784

**\u21d2 `check_plugin_claims.py` \u628a\u7c7b\u578b\u672c\u5e94\u627f\u8f7d\u7684\u90a3\u53e5\u8bdd**\u7528\u4e09\u5341\u884c**\u5b9e\u73b0\uff1a**
**\u300c\u58f0\u79f0\u7684\u4e49\u52a1\u4e0d\u80fd\u662f\u4e00\u4e2a**\u4ec0\u4e48\u90fd\u6ca1\u8bf4\u7684\u69fd\u4f4d**\u300d\uff1b\u81ea\u6d4b\u690d\u5165\u90a3\u4e2a\u786e\u5207\u5f62\u72b6\u5e76\u8981\u6c42\u88ab\u6807\u8bb0\u3002**
**\u21d2 `ProofFieldOf` \u4ecd\u5728\u6e05\u5355\u4e0a\uff1a**\u7b49\u8fd9\u9053\u95e8\u7981**\u54cd**\u4e86\u518d\u505a\uff0c\u800c\u4e0d\u662f\u4ee3\u66ff\u8fd9\u9053\u95e8\u7981\u3002**
**\u21d2 \u4e3a\u4e00\u4ef6**\u4ece\u672a\u53d1\u751f**\u7684\u4e8b\u505a\u5927\u578b\u91cd\u6784\uff0c\u662f\u53e6\u4e00\u7b14\u4e70\u5356\u3002**

#### \u4e00\u4e2a\u987a\u5e26\u7684\u4e8b\u5b9e

**\u21d2 \u4e3a\u6b64\u91cd\u8bfb\u4e86 manifest\uff1a\u6bcf\u6761\u4e49\u52a1\u662f `verifiedObligation "<\u540d>" .<kind> "<\u6587\u4ef6>" "<\u5b9a\u7406>" <Prop> (by \u2026)`\uff0c**
**\u21d2 **\u5b83\u81ea\u5e26\u547d\u9898**\uff08\u7b2c 767 \u8f6e\uff09\u3002\u21d2 \u6545 kind \u662f**\u4e00\u4e2a\u5df2\u8bc1\u547d\u9898\u4e0a\u7684\u6807\u7b7e**\uff0c\u800c\u4e0d\u662f\u5341\u4e8c\u5b57\u6bb5\u8bb0\u5f55\u7684\u6307\u9488\u3002**
**\u21d2 **\u4e8c\u8005\u4eca\u5929\u53ea\u9760\u300c\u975e\u7a7a\u300d\u76f8\u8fde**\u2014\u2014**\u800c\u90a3\u6b63\u662f\u8fd9\u9053\u95e8\u7981\u770b\u5b88\u7684\u7f3a\u53e3**\u3002**

**\u21d2 \u5b9e\u6d4b\uff1a`VERIFY ALL [fast] PASS`\uff08605.2 \u79d2\uff09\uff0c`130 = 108 + 22`\uff0c97 \u901a\u8fc7\u3002**
### 3.140 **Phase 2 的入口测量：`ModelsIR` 的**结构成本很小，但语义成本是整个 Phase 1**（第 1187 轮）**

**⇒ 规划 ADR-D：「把 `modelsIR`/`ModelsTerm` 换成真语义谓词，用 `modelsBehavior` 作候选」，并把 R4 风险评为**
**⇒ 「约 12 个下游文件失效，概率高、影响高」。⇒ 本轮**只读测量**了这两条。**

#### 结构成本：**只有 4 处把它当假设**

| 指标 | 实测 |
|:--|--:|
| 签名中提到 `ModelsIR` 的声明 | **20** |
| **作为假设**出现 | **4** |
| 其中属于 `ModelsIRScope.lean`（**专门讲它弱**的那三条） | **3** |
| 另一处 | `modelsIRS_implies_modelsIR`（桥） |
| `ModelsTerm`（CIC 孪生） | **1 个文件 / 2 处** ⇒ 近乎休眠 |

**⇒ 故「12 个下游文件」这个概念是**把「签名里提到」当成了「依赖它」**。⇒ 真正会被影响的声明约 **7 条**：**
**⇒ `ModelsIR` 定义、`compile_sound`、`construct_sound`、`construct_sound_wf`、四条 scope 定理、一条桥。**

#### 语义成本：**ADR-D 的替换件在类型上就不成立**

**⇒ `ModelsIR : IRWeights → IRSkeleton → Prop`（`Obligations.lean:73`）**
**⇒ `modelsBehavior : IRWeights → (ℕ → Segment) → ℕ → Prop`（`ModelsBehavior.lean:35/65`）**

**⇒ **第二个参数类型不同**：`IRSkeleton` vs `ℕ → Segment`。⇒ 二者之间**没有桥**——而那正是「L3 三个入口」的缺口。**

**⇒ 故「用 `modelsBehavior` 替换 `ModelsIR`」不是重构，而是**研究**：**
**⇒ 它需要先给 `IRSkeleton` 一个**行为语义**（把骨架映到 `ℕ → Segment`），**而这正是 Phase 1 要做的事**。**

#### 因此 T1 的正确处置（与规划的 fallback 一致）

**⇒ 规划自己在 ADR-D 里写了「替代（若不可行）：把 T1 移出 `ProofComplete` 并在规范写明『当前只有定义等式版本』」。**
**⇒ **测量支持那条 fallback，不支持主方案**：主方案在类型上不可实施，而 fallback 是**小、诚实、可立即做**的。**

**⇒ 而 `modelsBehavior` 自身的使用范围**只有 2 个文件（它自己 + `Compose/Showcase/L3L2.lean`）⇒ **它也不是现成的替代品。**

**⇒ 本轮不改任何代码：这是**规划层的修正**，其依据是三条实测（4 / 7 / 类型不同）。**
### 3.141 **又一次先测量：规划的「T1 移出 `ProofComplete`」会删错东西**（第 1188 轮）

**⇒ 规划 ADR-D 说：`ProofComplete` 的 T1 是 `Obligations.lean:86` 的 `have _ := h; exact rfl`，**
**⇒ 救法是把「它」移出判据。⇒ **本轮打开了 `ProofComplete` 的定义本体。**

#### 实测

**⇒ `ProofComplete`（`Lattice/Plugins.lean:542`）的 **25 项**里，与 T1 相关的是**三条 `t1_*`**：**

| 名字 | 陈述（实读 `Targets/Statements.lean:123`） |
|:--|:--|
| `t1_compile_sound_instance` | 关于 `MergeRecord` / `samePointLadder` / `satW` ——**合并健全性** |
| `t1_merge_sound_unrejected` | 同家族 |
| `t1_compile_sound_general` | 同家族的**一般形式**（已证，靠 `SemanticRep` 的两个映射） |

**⇒ 而 `Obligations.lean` 的 `compile_sound` **不在这 25 项里**——块内只有上面三个名字。**

**⇒ 故「把 T1 移出 `ProofComplete`」若按字面执行，会删去**并非琐疾的三条真内容**。**

#### 而树上早已诊断过这件事

**⇒ `Targets/T1Dependence.lean` 开头写着：`t1_compile_sound_instance` 的**结论不提到 `R`**，**
**⇒ 因为 `hR : R.merged = […]` 把唯一被消耗的字段**钉死**了；**
**⇒ 并且它自己说：「**That is not a bug in the proof; it is a bug in what `ProofComplete` was conjoining.**」**

**⇒ 故树上已经知道这一层弱——而且**修法不是删除，是 `t1_compile_sound_general`**（它已存在）。**

#### 结论

**⇒ **规划的 ADR-D 射错了目标**：它说的那条 `rfl` 定理在 `Core/IR`，不在判据里；**
**⇒ 判据里的 T1 是另一个东西，而它的弱已被一个专门文件记录并给出了一般形式。**

**⇒ **本轮不删任何东西**。⇒ 要改的是**文档**：凡写「`ProofComplete` 的 T1 是 `rfl`」的地方都错了。**
### 3.142 **W3-3 入口测量：规格清楚，但**第一条定理的陈述是假的**（第 1198 轮）**

**⇒ 规划说 W3-3 是「Q6/Q9/Q12/Q13/Q14/Q15/Q18 的共同前置」，规格在 `PLUGIN-SYSTEM.md:1150-1228`。**
**⇒ 本轮**只读**测了两件事，然后**没有写代码**。**

#### 一、树里没有任何部分实现

| 名字 | 出现文件数 |
|:--|--:|
| `rankKey` | **0** |
| `PluginState` | **0** |
| `dependencyGraph` | **0** |
| `requires_acyclic` | **0** |
| `rank_key_total` | **0** |

**⇒ 故这不是「补一段」，而是**从零建**。⇒ 而规格（六分量、字典序、逐分量方向）写得足够清楚。**

#### 二、但规格里的 `rank_key_total` **按字面是假的**

```
theorem rank_key_total : ∀ a b, a.rankKey ≠ b.rankKey
```

**⇒ 取 `a = b`，则两边是同一个键 ⇒ 定理断言 `k ≠ k` ⇒ **假**。**
**⇒ 故这行**不能照抄**；它想说的必然是**更窄**的一句，最可能是：**

**⇒ **「键上的序是**全序**」**（三分律：`<` / `=` / `>`）**，或**
**⇒ **「**不同插件**的键不同」**（`a ≠ b → a.rankKey ≠ b.rankKey`，而这**需要 id 打破并列**那一条来撑）。**

**⇒ 两条里，前者是**关于序**的，后者是**关于键不同**的——规格把它们压成了一句，而压出来的那句是假的。**

#### 三、因此本轮**不写** `Orchestration.lean`

**⇒ 若照字面实现，第一条定理就必须**证一个假命题**——而唯一「能过」的写法是把它改成**恒真**的变体，**
**⇒ 那正是本会话反复在治的病：**定理看起来在，其实什么都没说**。**

**⇒ 故下一轮的前置是**先修规格**（把 `rank_key_total` 拆成两句，并明确 id 的角色），再写代码。**
**⇒ 这符合用户明示的顺序：**先完善规划，再执行规划**。**

**⇒ 而 tree 里已有一条同族的**反面教材**在 CI 之外被记录过：`Registry.lean:110` 的 `consistent`**
**⇒ 也是把两件事压成一句（`obligations ≠ [] → proof.Holds`），到第 1186 轮才被量出「类型允许、树里没有」（§3.139）。**
### 3.143 **11 个反应性探针逐个跑完：**全绿**，而「完整验证」可以**组合**得到**（第 1200 轮）**

**⇒ 上一轮（1199）发现 `reactivity: layering` 因**植入物已失效**而失败，并指出 `--fast` 把这 11 个探针全部跳过。**
**⇒ 本轮**逐个跑完**它们：**

| 探针 | 结果 |
|:--|:--|
| `gate_reactivity.py` | **ALL PASS** |
| `layer_reactivity.py` | **ALL PASS** |
| `check_slots_reactivity.py` | **ALL PASS** |
| `check_comments_reactivity.py` | **ALL PASS** |
| `check_i8_reactivity.py` | **ALL PASS** |
| `check_registry_reactivity.py` | **ALL PASS** |
| `check_registry_gate_reactivity.py` | **PASS** |
| `verify_g4.py` | **PASS** |
| `audit_tables_reactivity.py` | **PASS** |
| `audit_counts_reactivity.py` | **ALL PASS** |
| `check_ci_workflow_reactivity.py` | **ALL PASS** |

**⇒ 故 1199 那条是**唯一**一个「植入物已失效」的探针——其余十处的植入仍然真的能触发。**
**⇒ 而这本身是一个**信息**：探针的**衰减是逐处的**，不能靠抽查一处推断其余。**

#### 「完整验证」的**获取方式**已经改变

**⇒ `verify_all`（完整）需 **1484 秒**，而环境窗口约 **600 秒** ⇒ 两次都被中途杀掉，**无法一次拿到**。**
**⇒ 但完整套件 = `--fast`（461.2 秒，97 通过）+ 11 个探针（本轮逐个跑，全绿）** ⇒ **两者都可单独完成。**
**⇒ 故「完整绿」现在是一个**可组合的证据**，而不是一个每跑必被杀的命。**

**⇒ 而这件事本身值得记：**一个无法一次跑完的验证命令，在实践上等于**半条命令**；**
**⇒ 而把它拆成可完成的两半，才让「完整」重新成为一个**能拿到**的事实。**
### 3.144 **W3-4 判定：`plugin.yml` 的 Lean 载体**早已存在**——这一项**不需要做**（第 1223 轮）

**⇒ 规划 W3-4 的前提是「Lean 侧没有 `plugin.yml` 的载体」。⇒ 实测：载体存在，且在**使用中**。**

| 测什么 | 结果 |
|:--|:--|
| `plugin.yml` 文件数 | **11** |
| 字段（全部 11 份一致） | `id` / `module` / `layer` / `obligations[{name, kind, theorem, file}]` |
| 共享类型所在 | `Lattice/Plugins/Manifest.lean` |
| 已有声明 | `ObligationKind`（**12** 种）· `PluginLayer`（**8** 层）· `Obligation` · **`PluginManifest`** · `mandatoryKinds` · `Version` |
| `PluginManifest` 使用面 | **15 个文件**，**含每个插件的 `Manifest.lean`** |
| YAML ↔ Lean 的对比 | `gov/check_plugin_yml.py` **逐字段**比 `id` / `module` / `layer` / `obligations`（同长度、同 name、同 kind、同 theorem、同 file） |

**⇒ 故「能力索引」这件事**已经做完**：数据结构在 Lean、真值在 Lean 的 manifest、而 YAML 是**第二份描述**，由门禁强制与第一份一致。**
**⇒ 若再去写一个 Lean 侧 YAML 解析器，它只会**重复**那道门禁——而本会话有一半工作是在**消除**这种重复。**

**⇒ 这是**第五处**规划前提被测量推翻，也是一个**减少**工作量的推翻（前四处多是让工作变多或变难）。**

**⇒ 而 W3-2（槽三态）仍未开始：它需要 `SlotClaim`/`SlotState` 这类**树里不存在**的类型，故不能照抄。**

### 3.145 **Phase 4 的**假阻断**被解除：`pipeline` 建在 `compileToLayer` 上，不碰 `compileSkel`**（第 1226 轮）

**⇒ `HANDOFF.md` 与 `LONG-TERM-PLAN.md` 都把「Phase 4 依赖 W1-3」当作阻断，理由是第 1195 轮的**
**⇒ `encodeGrid_ne_compileSkel`：第三处 L3 入口与另两处**可证不等价**。**

**⇒ 本轮读了 `pipeline` 的本体，结论相反：**

```lean
def pipeline (s : List Char) :=
  (tokenize s).bind (fun ts => (decode (L1Bridge ts)).map compileToLayer)
```

**⇒ 整条流水线的最后一环是 **`compileToLayer`**——即**函数形入口**，而那两处**已经逐段与全域接通**（1193、1194）。**
**⇒ 它**从不调用** `compileSkel`。⇒ 故第三入口的不等价**不构成** Phase 4 的阻断。**

| 测什么 | 结果 |
|:--|:--|
| `pipeline` 定义位置 | `Lattice/Lib/Chain/RealEndToEnd.lean:802`（**正是**规划所引处） |
| 它用的入口 | **`compileToLayer`**（函数形） |
| 它是否用 `compileSkel` | **否** |
| `Primitive` 类型 | **存在**（`Compose/Primitive.lean`，5 处声明） |
| `defaultPipeline` | **不存在**（0） ⇒ W4-1/W4-2 仍是真的待做，但那是**组装**，不是**新语义** |
| `compilePrim` | **不存在**（0） ⇒ 需先从 `compileToLayer` 包一层 |

**⇒ 故 Phase 4 **可以开始**，且它的第一个动作是具体的：把 `tokenize`/`decode∘L1Bridge`/`compileToLayer` 三个**普通函数**
**⇒ 包成 `Primitive`，组装 `defaultPipeline`，再证 `pipeline s = defaultPipeline.run s`（W4-1）。**
**⇒ 这三步**都不需要新语义**——它们只需要 `Primitive.run` 的复合律，而 `Compose` 那一层已有定律。**

**⇒ 这是第六处规划前提被测量推翻，也是**第二处**让工作量变少的推翻。**

### 3.146 **Phase 4 的真正门槛不是「不等价」，而是 `compose` 的那条**副作用条件**（第 1227 轮）

**⇒ 上轮证明「第三入口不等价」不阻断 Phase 4（`pipeline` 建在 `compileToLayer` 上）。⇒ 本轮去找**真正的**门槛，找到了。**

#### 一、实测：`Primitive.compose` **不是**自由串联

```lean
def compose {I M O} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ x y, f.post x y → g.pre y) : Primitive I O
```

**⇒ 它**多要一个参数 `h`**：`f` 的后置必须蕴含 `g` 的前置。⇒ 源码自己的注释写明：**
**⇒ 「`h` 仍在：`f` 的后置必须蕴含 `g` 的前置，**这是语义义务，不是类型产物**」。**

#### 二、而流水线的三段都是**部分**函数（实测到的形态）

| 阶段 | 形态 |
|:--|:--|
| `tokenize` | `Option` 值（文件里 `tokenize s = some ts` 的**前提**写法，`RealEndToEnd.lean:516`） |
| `decode ∘ L1Bridge` | `Option` 值（同上，`L1Bridge ts` 的可用性以 `ts` 为条件） |
| `compileToLayer` | **全**函数（`ConstraintSet → Layer`，无非 `Option`） |

**⇒ 故 `compose` 需要的 `h`（「上一段成功后下一段必接受」）**不是免费的**：**
**⇒ 它要么是一条**领域事实**（「`tokenize` 的每个输出都被 `decode ∘ L1Bridge` 接受」），要么根本不成立。**

#### 三、所以 W4-1/W4-2 的两条路，**一条是空的、一条是真活**

1. **把 `defaultPipeline.run` 定义成 `pipeline` 本身** ⇒ `pipeline s = defaultPipeline.run s` 是 `rfl`，
   **⇒ 但那是「流水线等于流水线」——空洞定理**，正是本会话一直在治的病。**故不取。**
2. **用 `compose` 真串三段的 `Primitive`** ⇒ 就必须先证**领域事实**：中间阶段接受前一段的输出。
   **⇒ 这是**真活**，且它才是 Phase 4 的核心内容——不是「接线」，而是**证明这条链的每一跳都不落空**。**

#### 四、这改变了 Phase 4 的性质，值得写明

**⇒ 规划把 Phase 4 描述成「把组合层接到真实管线」（**接线工作**）。⇒ 实测表明它的实质是：**
**⇒ **证明三段 `Option` 值函数的**定义域嵌套**，再用 `compose` 的 `h` 把它接起来。**
**⇒ 而**这件事**才是「数据 ⇄ token ⇄ 符号 ⇄ 权重」这条链在形式上的真难点——不是类型接线，是**不落空的证明**。**

**⇒ 故下一轮的第一件事**不是写 `defaultPipeline`**，而是：**
**⇒ 测 `tokenize` 的值域与 `decode ∘ L1Bridge` 的定义域**能否**证明包含**（若不能，则这条链上**存在一个真实的可达失败**，**
**⇒ 而那**本身**就是一条必须记录的结论——比一条空定理有价值得多）。**

### 3.147 **修正 §3.146：那条 `h` 是**平凡**的——因为 `decode` 由构造即全函数**（第 1228 轮）

**⇒ 上节（3.146）说 `compose` 的 `h` 是「一条目前无处证明的领域事实」。⇒ 本轮实测表明：**那句话过强，须修正**。**

#### 一、证据：`Compose/Showcase/L1L2.lean` **已经**这么做过一次

```lean
def decodePrim : Primitive (List SymToken) ConstraintSet where
  pre   := fun _ => True
  post  := fun ts cs => Lattice.decode ts = some cs
  run   := fun ts => Lattice.decode ts
  sound := by intro ts _; exact ⟨_, rfl, rfl⟩

def l1l2Roundtrip := compose encodePrim decodePrim (by intro cs ts _; trivial)
```

**⇒ 它的 docstring 直接给了理由：「`decode` 的定义本身就是 `some (…)`，所以它也是**全函数**」。**
**⇒ 故 `pre := True` 合法，而 `compose` 的 `h` 由 `intro …; trivial` 关闭。**

#### 二、故 §3.146 的正确版本是

| \u4e0a\u4e00\u8f6e\u7684\u8bf4\u6cd5 | \u672c\u8f6e\u5b9e\u6d4b\u540e |
|:--|:--|
| `h` 是「无处证明的领域事实」 | **`h` 平凡**——只要每段的 `pre := True` 且其 `run` 在**定义上**总返回 `some` |
| Phase 4 因此是真活（证明不落空） | **仍有一部分是真活**：`tokenize` **不是**全函数（`List Char → Option …`），故**它的 `pre` 必须非平凡** |

**⇒ 也就是说：整条链里**只有 `tokenize` 一段**需要非平凡的 `pre`，其余三段（`L1Bridge`、`decode`、`compileToLayer`）都是全函数。**

#### 三、于是 W4-2 的**正确形状**已经确定

```lean
def tokenizePrim  : Primitive (List Char) (List CharToken) where
  pre   := fun s => (tokenize s).isSome     -- **只因这一段部分**
  post  := fun s ts => tokenize s = some ts
  run   := tokenize
  sound := by intro s h; cases hrun : tokenize s with
             | none   => simp [hrun] at h
             | some y => exact ⟨y, rfl, rfl⟩
def bridgePrim    : Primitive (List CharToken) ConstraintSet where
  pre := fun _ => True                       -- L1Bridge 与 decode 都全
  …
def compilePrim   : Primitive ConstraintSet Layer where
  pre := fun _ => True                       -- compileToLayer 全
  …
def defaultPipeline := (tokenizePrim.compose bridgePrim (by simp)).compose compilePrim (by simp)
```

**⇒ 而 `pipeline s = defaultPipeline.run s` 应当是 `rfl` 或一条 `simp [Option.bind_assoc]`——**
**⇒ 因为两边都是**同一串 `bind`**；这与 §3.146 担心的「空洞」不同：**
**⇒ 空洞的是**把 `run` 定义成 `pipeline` 本身**；这里 `run` 由 `compose` **从三段拼出**，等式是**两条不同的构造**偶然相等。**

**⇒ 故本轮的结论是：**路径清楚、模板现成、只剩一段需要非平凡 `pre`**。⇒ 下一轮就写它。**

#### 四、这也修正了 §3.146 对 Phase 4「性质」的判断

**⇒ 上一轮说「Phase 4 的实质是证明每一跳不落空」。⇒ 更准确的说法是：**
**⇒ **只有 `tokenize` 那一跳可能落空**，而其余三跳的不落空由**定义即全函数**免费给出。**
**⇒ ⇒ Phase 4 因此**比上一轮估计的小**，而它仍然**不是空的**（`tokenize` 的 `pre` 是真的）。**
