# 编译器层（`Lib/Compiler`）交付说明

**本文是**入口**，不是**过程日志**。⇒ 过程记录在 [`PLAN-STAGES.md`](PLAN-STAGES.md)；
本文只写**能被核对**的结论，以及每条结论**对应的定理**在哪里。**

**⇒ 所有计数都带一条**重新测量**的命令（见 §6），因为静态数字会腐烂。**

---

## 1. 这一层是什么

**它是 `符号 ⇄ 权重` 这一跳的**一个完整实现**：**

```
符号项 (ExprExt)
   │  compileTarget
   ▼
Target ──family──▸ 分段族 (ℕ → Segment) ──encodeGrid──▸ 权重载荷
   │                                                    │
   └──── 界（每族一条）◂── 能力表 ◂── 选择器 ────────────┘
                                │
                        EvaluatedArtifact ──evalAt──▸ 精度
```

**⇒ 三个概念层，层间关系**都是定理**（不是注释）：**

| 层 | 结构 | 层间关系 |
|:--|:--|:--|
| **解析** | `AnalyticRow`（任意函数族） | `analytic_of_capability : CapabilityRow → AnalyticRow` |
| **能力** | `CapabilityRow`（+ 符号证据） | `capability_select_is_analytic`（两层选择是同一次操作，**等式**） |
| **产物** | `EvaluatedArtifact` | `gridEval_congr`（族相等 ⇒ 求值相等） |

---

## 2. 五条可核对的结论

### 2.1 一条界覆盖**所有**度数，常数是闭式

**`Lib/Compiler/PowChord.lean`**

```lean
pow_uniform_bound (d) (2 ≤ d) (n) (0 < n) :
    ∀ x ∈ Ico 0 1, |x^d − gridEval (interpFamily n (t↦t^d)) n x| ≤ d(d−1)·(1/n)²/8
```

**⇒ 它**重推出**了此前三轮各自手工推的常数：`constant_two`（`1/4`）、`constant_three`（`3/4`）、
`constant_four`（`3/2`），并由 `general_formula_matches_hand_derived` 把三者并列陈述。**

### 2.2 任意度数都能被**选中**，不只被界住

**`Lib/Compiler/AnalyticSelection.lean`**

```lean
powRowsTo_six : powRowsTo 6 = [row 2, row 3, row 4, row 5]
quintic_lands (5·4/8·(1/n)² ≤ eps) : analyticSelect ⟨t⁵⟩ (powRowsTo 6) = some (powAnalyticRow 5 _)
```

**⇒ 即：选择器在**跳过三个更低度数**之后，确实返回五次行。`t⁵` 与 `t¹⁰` **在本项目里从未被单独处理过**，
它们从一般定理直接落下（`quintic_bound`、`tenth_power_bound`）。**

### 2.3 两套「符号→权重」实现是**同一个推广的两个截面**

**`Lib/Compiler/RealLayer.lean`**

```lean
realLayer_ofInt_out (l : LinearLayer) (x : List ℤ) :
    castI (LayerOut l x) = (realLayerOfInt l).out (x.map castI)          -- 主链 = 整数截面
realLayer_single_eq_segment (m c x : ℝ) :
    RealLayer.out ⟨[m], c⟩ [x] = (⟨m, c⟩ : Segment).eval x              -- 新线 = 单段截面
```

**⇒ 且该推广**被新线消费**：`gridEval_eq_realLayer_out` 把新线的核心求值改写成实数层求值，
而 `pow_uniform_bound_as_realLayer` 是最强那条界的改写形式。**

**⇒ 两套实现的差异（数域 / 判据 / 组织轴）见 [`SYMBOL-WEIGHT-COMPARISON.md`](SYMBOL-WEIGHT-COMPARISON.md)。**

### 2.4 主链**第一次**有了具体的 `Repair Layer` 实例

**`Runtime/LayerRepair.lean`（round 1101）**

```lean
layerZeroRepair : Repair Layer                       -- 全树第一个
layerZeroRepair_sat_zero_outputs : allZeroLayer ls → ∀ x, AllZeroOutputs ls x
```

**⇒ 在此之前，`Runtime/RepairClosure.lean` 的四条定理以 `R : Repair Layer` 为参数，而**全树没有该载体的实例**，
故它们**永远无法被应用**。⇒ 该实例使它们**第一次可被应用**，并让 `3.2 → 3.3` 接缝**首次有活的连接器**。**

**⇒ `extract_after_repair` 本身仍无消费者：它要求**等价**前提（`Sat ↔ LayerSat`），
而实例只能给出**蕴含**。⇒ 其**单向**兄弟 `extract_after_repair_weak` 才是被应用的那一条。**

### 2.5 闭环在产物载荷上是**具体的**，且轮数有界

**`Lib/Compiler/LoopInstance.lean`**

```lean
twoSlopeLoop_objective_vanishes : objective (run (μ p) p) = 0      -- 终点缺陷为零
twoSlopeLoop_sat_after_one      : Sat (run 1 p)                    -- 一轮即达标
twoSlopeLoop_ends_sat_in_two    : Sat (run 2 p)                    -- 两轮的上界
twoSlopeLoop_run_components     : run k p 逐分量 = (fix^[k] p₁, fix^[k] p₂)
```

**⇒ 一次并行修复（即 `Repair.fix`）同时修好两侧，故**一轮**即够；而抽象定理承诺的 `μ p` 是**缺陷数**（最多 2），
⇒ 故抽象界**同时对且松**。两者都保留，因为一个是通例、一个是本实例的锐值。**

---

## 3. 「不具备」的部分（写清楚，免得被当成承诺）

**⇒ 本层**不**提供：训练、优化器、推理引擎、任何框架绑定。**
**⇒ 本层**不**声称任何语义。可求值的入口**只有一个**：`EvaluatedArtifact.evalAt`；它之外没有第二个求值函数。**
**⇒ 本层**不**统一主链与新线的判据：`AllZeroOutputs` 与 ε-界是两个谓词（见对照文档）。**

### 3.1 治理覆盖到哪一层（**边界是有意的，不是遗漏**）

| 表 | 覆盖什么 | 当前条目 | 零必须带理由？ |
|:--|:--|--:|:--|
| `END_OF_CHAIN` | 目标的 **14** 个条款的 **44** 个载体 | **9** | 是 |
| `TERMINAL_CONNECTORS` | 八阶段链的**相邻接缝**连接器 | **60** | 是（预算 = **0**） |
| — | **其余约 10,000 条定理** | — | **不受管辖** |

**⇒ 最后一行是**设计**，不是遗漏**：无法为每条定理登记理由，而一个装满理由的表与没有表一样无用。**
**⇒ 故本文件**声明这条边界**，而不留白——因为“不受管辖”与“漏管”在读者眼里长得一样。**

**⇒ 密度参考**：本树 **10,293** 条 theorem/lemma 中有 **69** 条被上表两张表直接命名（0.7%）。**这个数字小得诚实**——表的作用不是覆盖全树，而是**钉住两类可命名的空洞**：载体不被消费、接缝连接器不被消费。**

---

## 3.2 链的连通性：**四个口径与它们各自的盲点**

**⇒ 「这条链是否真的连通」不能用一个数字回答。⇒ 下表是**四个独立口径**，每个都有的**终值**与**停因**。**

| 口径 | 问题 | 终值 | 停因（为何不是更大） |
|:--|:--|:--|:--|
| **载体消费者** | 每个目标载体是否被链内使用 | **44** 载体 / **36 链内** | 余 4 仅本文件 + 4 全无（已登记） |
| **接缝连接器** | 相邻阶段之间是否有连接定理 | **60** 登记，预算 **0** | 死连接器**必须带理由**，故不能再增 |
| **条款对（载体名）** | 相邻条款是否在**同一语句**中出现 | **9 / 12** | 名字度量对「用**概念**说话」的桥**失明** |
| **条款对（接缝概念）** | 逆向侧三对是否有连接器 | `3.2→3.3` **5** / `3.3→3.4` **6** | 只覆盖八阶段链，故不能覆盖正向侧 |

**⇒ 四者**合起来覆盖全部 12 对**，且每一处「看不见」都有**具名原因**。**
**⇒ 故正确的读法不是「9/12，有缺口」，而是「9/12 加三对只能用另一种词汇看见」。**

### 本会话为此写下的**四条桥**（每条都有理由登记）

| 桥 | 连的是 | 为何此前不存在 |
|:--|:--|:--|
| `eps_repair_requires_descent` | `3.2` ↔ `3.3` | 两世界从未**同句** |
| `closed_loop_reinject_within` | `3.3` ↔ `3.4` | 原条要求 `= 0`，ε-判据下**假** |
| `compile_round_trip_law` | `2.3` ↔ `1.3` | 各写一半，**形状只在读者眼里** |
| `layerPenaltyEmbedding` | `2.1` ↔ `1.3` | 关系是**实例**，不是平行定理 |
| `sound_not_exact_gives_epsilon_gap` | `8` ↔ `3.2` | 缺口是**可构造**的，而非修辞 |
| `cic_loop_reaches_weight` | `5` ↔ `1.3` | 隔在两个**词汇**之间 |

**⇒ 都是**已有之物或几行定理**：没有一条需要新的抽象。**

**⇒ `ProofComplete`（`Lattice/Plugins.lean`）需 **30 项**——这个数字由 `gov/check_criterion_size.py` **从源码数出来**，不是重录的。**
**⇒ 而它在本会话里错过两次：先是所有文档写 25 而那个证明的 refine 只有 24 个占位符，**
**⇒ 后是合入真 T7/T6/T0 后变成 30 而文档仍写 25。⇒ 故它现在是**一条门禁**。**

## 4. 目标条款的覆盖（可核对）

**⇒ 条款 1.3 / 1.4 的载体中，本层提供 `compileTarget`、`EvaluatedArtifact`、`decodedFamily`（第 1081 轮登记）。
⇒ 条款 3.3 的载体中，本层提供 `layerZeroRepair`（第 1118 轮登记，此前该条款只指向演示材料）。
⇒ 逐条款的「链内消费者」计数见 `OBJECTIVE-MAP.md`（生成物）与 `PLAN-STAGES.md §3.77`。**

---

## 5. 与既有主链的**唯一**非法方向

**⇒ `Runtime/` **不能**导入 `Lib/Compiler/`：`gate.py` 的 I4 分层规则禁止向上导入
（`Runtime` 秩 2、`Lib` 秩 3），该尝试在分支 `feat-runtime-consumes-compiler` 上被门禁否决（第 1097 轮）。
⇒ 故若要让主链引用本层，必须先**搬**本层或**改秩**——那是**架构决策**，不是编辑。**
---

## 6. 如何重新测量本文的每一句

```powershell
cd gov
python gen_objective_map.py --check      # 载体与引用数（§4）
python chain_connectors.py --provenance  # 接缝活跃度（§2.4、§5）
python check_doc_freshness.py            # 全树数字与文档的一致性
python check_delivery_claims.py --check  # 本文每个反引号标识符都必须是一处声明
python check_clause_pairs.py              # §3.2 的四个口径之一（只报告）
python check_self_claims.py --check      # 自述性声明（「本文件零声明」）必须与事实一致
python check_theorem_liveness.py --check  # 全树定理活性比例（链内 ≥ 基线 − 2 点）
python measure_eight.py                      # **一次性重量八个量**（模块/定理/声明/文件/行/门禁/接缝/条款/判据项数）
python -c "import sys; sys.path.insert(0,'gov'); import gen_objective_map as G, chain_connectors as C; print(len(G.END_OF_CHAIN), len(C.TERMINAL_CONNECTORS), C.UNREGISTERED_BUDGET)"   # §3.1 的三个数
```

**⇒ 整套验证要**两半才能拿到**（第 1200 轮实测）：完整套件需 **1484 秒**，**

**⇒ 而本环境的单命令窗口约 **600 秒** ⇒ 两次完整运行都**被中途杀掉**。**

**⇒ 故「完整绿」现在由**两半相加**得到，两半都可单独完成：**

```bash
python verify_all.py --fast      # 第一半：约 461 秒，97 通过（跳过 11 个探针）
# 第二半：那 11 个探针逐个跑（每个约 90 秒，合计约 17 分钟）
for f in gate_reactivity layer_reactivity check_slots_reactivity check_comments_reactivity \
         check_i8_reactivity check_registry_reactivity check_registry_gate_reactivity \
         verify_g4 audit_tables_reactivity audit_counts_reactivity check_ci_workflow_reactivity; do
  python "$f.py" || echo "PROBE FAILED: $f"
done
```

**⇒ 第 1200 轮实测：这 11 个探针**全部 exit 0**；而它们是这棵树里**唯一会测试「检查本身」**的那批。**

**⇒ 故请**不要只跑 `--fast`**：它是一个**预算决定**，而预算决定会安静地变成**覆盖决定**。**

**⇒ 最后一条是本文**自己**的守卫：第 1119 轮它捕到本文曾引用一个**未声明的标识符**（一个不存在的求值名字）。
⇒ 故本文的结论**不依赖作者**：不能解析的引用会被工具拓下来。

**⇒ 若某条结论与工具输出不符，**以工具为准**，并修正本文——本文没有「作者权威」。**

---

## 7. 本会话做了什么、没做什么、为什么停

### 7.1 做了什么（一句）

**⇒ 把一棵**有 10,000 多条定理、但条款之间互不相通**的树，变成一条**
**⇒ 每个相邻环节都有具名桥、每个空洞都有登记理由、每个数字都能被工具核对**的链路。**

**⇒ 而所有桥都是**已有之物被写在一起**：没有一座需要新抽象。**

### 7.2 没做什么，为什么停

| 未做 | 为什么 |
|:--|:--|
| 条款 2.2 的**下游** | 测得抽象有 **4 个生产者、 0 个消费者**；提取律**无条件**成立 ⇒ 前提永不被需要 |
| 主链引用 `Lib/Compiler` | 层级两难：被 `Runtime`（秩 2）引用要求秩 ≤ 2，而它导入 `Lib`（秩 3）要求秩 ≥ 3 |
| 拆 22 个采集文件 | 它们的文档头记明上游来源；拆开会破坏与源本的一一对应 |
| 逐条登记 5,211 条死定理 | 数量上不可能；故改用**比例**（链内 15.3%，门禁不得跌破基线 − 2 点） |
| 为 Lean 文件头的**数字**建检查器 | 实测证明那些数字是**历史记录或行号引用**，建检查器只会制造误报 |

### 7.3 读者如何核对（六条命令，全在 §6）

**⇒ 这一页的**每个数字**都对应 §6 里一条命令。⇒ 若工具与本文不符，**以工具为准**。**

**⇒ 而本文最后一句（也是最该记住的一句）：**
**⇒ 本会话有**四次**——文档、散文、检查器、grep——被判为问题的那个东西，**
**⇒ 最后都是**我看它的方式**有错。⇒ 而每一次都是靠**换一种查法**发现的。**

### 7.4 按规划编号：已完成什么，什么还没开始（第 1207 轮更新）

**⇒ 上面 7.1–7.3 写于 Phase 2 之前，故它们仍成立但不完整。⇒ 本节按规划的阶段编号给现状。**

| 阶段 | 交付了什么 | 证据 |
|:--|:--|:--|
| **Phase 0** | 五个 `--strict` 注册、**三态裁决**（SKIP 不再算通过）、check_g7 转为报告器、两腐化基线重建、六处默认写改为比较、**GATE-1/2/3**、七组同 FQN 合并、三秩表合一 | 恒绿 **8 → 0**；`131 = 109 + 22`，**98 通过** |
| **Phase 1** | `realLayerOfInt` **单射**、整数**预像 + 左逆**、**精确边界**（两系数皆整 ⇔ 有层）、两条编码**逐段与全域**一致、第三处入口**以定理判定不等价**；产物契约 W1-2 **以测量否定** | 定理 **10,311**；`GridRealAgreement.lean` 新建 |
| **Phase 2** | T7/T6 **换载体并追加**；T0 **裁决为进判据**；T8 **裁决为不进**（插件级 vs 步骤级） | 判据 **24 → 30**，由 `check_criterion_size.py` 看守 |
| **Phase 3 前置** | 一致性谓词按 kind（**以门禁形式**，实测 0 处声称却空）；`PluginState` 状态机 + 3 条定理 | `Orchestration.lean`；`check_plugin_claims.py` |
| **Phase 3 其余** | **未开始**：W3-2（槽三态）、W3-3 其余（排序键与依赖图）、W3-4（`plugin.yml` 能力索引） | — |
| **Phase 4–8** | **未开始**：管线层、IR 契约、执行边界、经验层、规模化 | — |

**⇒ 而 Phase 3 其余里的排序键那一块有一个**已测量的障碍**：**
**⇒ 规范的 rank_key_total : ∀ a b, a.rankKey ≠ b.rankKey **按字面为假**（取 `a = b`），**
**⇒ 故该块需**先修规范**（拆成「全序」与「不同插件键不同」两句）再写代码。**

**⇒ 而本会话最该记住的一条，是下面这个形状的四次重复：**
**⇒ **被判为问题的东西，最后都是我看它的方式有错**——文档、散文、检查器、grep、以及第**五次**：**
**⇒ 我在 W0-2 里的**正确改动**（删死前缀）**静默关掉了一个探针**，而它藏了十四轮，**
**⇒ 因为我一直用 `--fast`——那恰好跳过了唯一会测试「检查本身」的那批。**

### 7.5 一页结语：从哪到哪，哪些是构造，哪些是否证，哪些停住了

#### 一、从哪到哪

**⇒ 起点（第 1160 轮左右）：**10,300 条定理，但**条款之间互不相通**——每对相邻环节之间没有具名桥，**
**⇒ 而**105 个名义门禁里有 8 个结构性恒绿**（它们**不可能**变红，因此「检查通过」在那 8 处没有证据价值）。**

**⇒ 终点（第 1209 轮）：**

| 量 | 值 |
|:--|--:|
| 模块（内核） | **1,126** |
| 定理 / 声明 | **10,314 / 13,910** |
| `.lean` 文件 / 行 | **1,226 / 281,539** |
| 检查项 | **131 = 109 门禁 + 22 报告器**（`--fast` 下 98 通过） |
| 反应性探针 | **11，全绿** |
| 接缝 / 连接器 / 未登记预算 | **9 / 60 / 0** |
| 条款 / 载体 | **14 / 44** |
| `ProofComplete` 项数 | **30**（由 `check_criterion_size.py` 看守） |

**⇒ **恒绿从 8 降到 0**；而「一次跑完的完整验证」被拆成**两半**（`--fast` + 11 个探针），因为整条命令超出环境窗口。**

#### 二、哪些是**构造**

| 定理 / 工具 | 说了什么 |
|:--|:--|
| `realLayerOfInt_injective` | 整数层嵌入实数层**不压扁** |
| `toLayerOf` + `realLayerOfInt_toLayerOf` | 整系数时可**取回**整数原像（左逆） |
| `segment_has_layer_iff_integral` | **精确边界**：两系数皆整 ⟺ 有整数层 |
| `familyToRealLayers_out_eq_encodeGrid` | 两条编码**逐段**求值一致 |
| `gridEval_eq_encodeGrid` | **全域**：段读法与扁读法是同一个函数 |
| `PluginState` 状态机 + 3 条定理 | 编排的最小骨架（error 终态、不许跳过 `loaded`、error 可达） |
| 真 T7 / 真 T6 / T0 进判据 | 判据**24 → 30**，且三处都是**追加**而非替换 |
| gov/artifact_guard.py + GATE-1/2/3 | 生成器**比较**而非覆盖；门禁**能失败**；计数**单源** |
| `measure_eight.py` | 八个量**一次重测**，不读记录值 |

#### 三、哪些是**否证**（测量推翻的东西）

| 被推翻的 | 实测 |
|:--|:--|
| 规划：`layers.py` 是零 importer 的死代码 | **1 个活 importer**，且两表在 **8 个层**上冲突 |
| 规划：插件「声称却空」是缺陷 | **0 处**；类型允许，树里没有 ⇒ 改为**门禁** |
| 规划：ProofComplete 的 T1 是 rfl，救法是移出 | **那条不在判据里**；判据的 T1 是三条合并健全性，且一般形式已存在 |
| 规划：T1 可用 `modelsBehavior` 替换 | **类型不同**（`IRSkeleton` vs `ℕ → Segment`）⇒ 不可实施 |
| 规划：「六处 `LayerOut` 定义」 | **只有 1 处真声明**，其余四处是 docstring 引用 |
| 规划：shape_of 可写 | **欠定**：产物不携带 `width`，故它会**猜**宽度 |
| 规划：`rank_key_total : ∀ a b, a.rankKey ≠ b.rankKey` | 取 `a = b` 即 **为假** |
| 树：T0 不能进判据（构造器不存在） | `Construction.lean` **已证四条** ⇒ T0 **进判据** |
| 树：layer_reactivity.py 的植入仍有效 | `Lattice/Geo` 早不在；W0-2 删死前缀后 **I4 从不触发**（藏了十四轮） |
| 文档：几何层「不参与主构建」 | **323** 条 import 边来自 `Lattice/` |

#### 四、哪些**停住了，以及为什么**

| 未做 | 为什么（测量） |
|:--|:--|
| **Phase 3 其余**（槽三态、排序键、`plugin.yml` 能力索引） | 排序键那条**规范本身为假**；`plugin.yml` 在 Lean 侧**没有载体** |
| **Phase 4**（组合层接真实管线） | 依赖 W1-3 的第三入口，而它与另两处**已证不等价** |
| **Phase 5**（IR 契约、编辑统一模型） | 需要新增载体（EditTarget / Change / EditMode 全部为空） |
| **Phase 6**（执行边界、自举） | 需 `.c/.h` 或 `@[extern]`，仓库里 **0 个** |
| **Phase 7**（经验层） | 前置于 Phase 6；没有可执行边界时基准只能测解释器速度 |
| **Phase 8**（规模化与清理） | 持续项；其中「文档腐化收敛」在 Phase 0 已做了一部分 |
| **T8 换载体** | 规范要**插件级** `failed`，树里只有**步骤级** `Step.run = none` |

**⇒ 故本会话**没有**把 lattice 做完。⇒ 它把 Phase 0–3 前置做**闭环**，并把**为什么做不完**写成可核对的理由，**
**⇒ 而不是把「做完了 Phase 0–3」当成「项目完成」。**

#### 五、最后一句

**⇒ 六次「被判为问题」的东西，最后都是**我看它的方式**有错：文档、我的散文、两个检查器、一个 grep，**
**⇒ 以及第六次——**我在 W0-2 里的一处正确改动，静默关掉了一个探针，而它藏了十四轮**，因为 `--fast` 恰好跳过**
**⇒ 「唯一会测试检查本身」的那批。**
**⇒ 而每一次都是靠**换一种查法**发现的，不是靠想得更仔细。⇒ 故本文的每条结论都带一个**能重跑的命令**。**