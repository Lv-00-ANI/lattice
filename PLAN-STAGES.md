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