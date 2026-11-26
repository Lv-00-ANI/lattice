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

**⇒ 密度参考**：本树 **10,099** 条 theorem/lemma 中有 **69** 条被上表两张表直接命名（0.7%）。**这个数字小得诚实**——表的作用不是覆盖全树，而是**钉住两类可命名的空洞**：载体不被消费、接缝连接器不被消费。**

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
python -c "import sys; sys.path.insert(0,'gov'); import gen_objective_map as G, chain_connectors as C; print(len(G.END_OF_CHAIN), len(C.TERMINAL_CONNECTORS), C.UNREGISTERED_BUDGET)"   # §3.1 的三个数
```

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
