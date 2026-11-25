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
| `END_OF_CHAIN` | 目标的 **14** 个条款的 **36** 个载体 | **9** | 是 |
| `TERMINAL_CONNECTORS` | 八阶段链的**相邻接缝**连接器 | **56** | 是（预算 = **0**） |
| — | **其余约 10,000 条定理** | — | **不受管辖** |

**⇒ 最后一行是**设计**，不是遗漏**：无法为每条定理登记理由，而一个装满理由的表与没有表一样无用。**
**⇒ 故本文件**声明这条边界**，而不留白——因为“不受管辖”与“漏管”在读者眼里长得一样。**

**⇒ 密度参考**：本树 **10,079** 条 theorem/lemma 中有 **65** 条被上表两张表直接命名（0.6%）。**这个数字小得诚实**——表的作用不是覆盖全树，而是**钉住两类可命名的空洞**：载体不被消费、接缝连接器不被消费。**

---

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
python -c "import sys; sys.path.insert(0,'gov'); import gen_objective_map as G, chain_connectors as C; print(len(G.END_OF_CHAIN), len(C.TERMINAL_CONNECTORS), C.UNREGISTERED_BUDGET)"   # §3.1 的三个数
```

**⇒ 最后一条是本文**自己**的守卫：第 1119 轮它捕到本文曾引用一个**未声明的标识符**（一个不存在的求值名字）。
⇒ 故本文的结论**不依赖作者**：不能解析的引用会被工具拓下来。

**⇒ 若某条结论与工具输出不符，**以工具为准**，并修正本文——本文没有「作者权威」。**