# LATTICE 完善规划（ROADMAP-v3）

> 生成时点：2026-10-25。**所有数字与定理名均为实测**，附证据。
> 本文是**规划**，不是完成报告。凡未实现项，本文一律标注「未做」，不写成「进行中」。
>
> 前置文档：`README.md` §3.3（方向性决定：精确 → 逼近精确）、`gov/SLOTS.md`（空位登记）、
> `archive/CORRECTIONS.md`（冻结更正登记）。

---

## 0. 一页纸概览

| 编号 | 事项 | 类别 | 规模 | 状态 |
|:--|:--|:--|:--|:--|
| P1 | 逼近精确的桥（(i)+(ii)，含 `ResidualEmbedding` 结构） | 数学主线 | S×2 | **探针已实测通过**，待入库 |
| P1' | 近似极小 ⟹ 残差界（原候选 (iii)） | 数学 | L | **探针失败，未证成** |
| P2 | ε 的紧化：证明界可压小 / 或给反例 | 数学主线 | L | **未做** |
| P3 | 6 个 owed slot 逐个清偿或明确降级 | 数学 + 治理 | M | 未做 |
| P4 | T4 的多步收敛（当前只证「一步」） | 数学 | L | 已登记为 slot |
| P5 | Cv00 段处置（原文路线） | 方向论证 | S | 已论证不做，需固化 |
| **P3b** | **门禁真实强度**：16 个检查恒返回 0；I3/I4/I7/G7 无反应性测试 | **治理（已发现真缺陷）** | M | **部分已修**（见 §4b） |
| P6 | 可复现构建（mathlib `path` → `git` + rev） | 工程 | M | **未做**，阻塞 CI |
| P7 | CI 实际可跑（5 处致命缺陷） | 工程 | M | **未做**，从未执行过 |
| P8 | `archive/` 无失效声明；B481–B498 断链 | 治理 | S | **未做** |
| P8b | 本地提交门禁**无法安装**（sh 钩子阻断提交，实测） | 工程 | — | **已实测并处置**：钩子移除，提交路径恢复 |
| P9 | 证明承重性重扫（超出四条靶定理的部分） | 数学 | L | **未做** |
| **P10** | **`CONVENTIONS.md`**：命名 / 分文件 / 学术化 / 证明链四套规范 | **规范（此前完全缺失）** | S | **未做**（见 §8） |
| **P11** | **撇号名收敛**（60 个 `'`） | 规范 | S | **未做** |
| **P12** | **超大文件拆分**（8 个文件 > 60 声明） | 结构 | M | **未做** |
| **P13** | **`PROOF-CHAIN-RUNG.md`**：四跳承重链，含否证实验 | **证明链** | M | **未做** |
| **P14** | **106 个「声称结论性」定理的注释统一** | 学术化 | M | **未做** |
| **P15** | camelCase 定义收敛（2,201 中的定义部分） | 规范 | L | **未做**（最大改动面，最后做） |

> **读法提示**：P1 是「逼近精确」的落地；**P3b / P6 / P7 / P8b 是本轮审计发现的真缺陷**，
> 它们不是新功能，而是「本库当前声称的强度高于实际强度」这件事的修补。
> **P10–P15 是本轮用户明确要求、此前规划完全没有覆盖的部分**（证明链梳理、学术化、
> 分文件、命名标注）。

---

## 1. 方向：为什么是「逼近精确」

### 1.1 原方案已证否（不是未证）

`Lattice/Lift/PenaltyEmbedding.lean`：

```lean
theorem sound_not_exact : PenaltySound constEmbedding ∧ ¬ PenaltyExact constEmbedding
```

反例 `constEmbedding`（常数正损失 + 恒假谓词）：A 层（零损失 ⟹ 满足）**空洞成立**，
B 层（局部极小 ⟹ 满足）**处处失败**，因为常数函数在每点都是极小。
⇒ **A 推不出 B，嵌套严格。** 这是命题为假，不是「还没证出来」。

### 1.2 精确性在具体载体上成立（可复用的结构）

| 载体 | 定理 | 位置 |
|:--|:--|:--|
| 标量 `n = 1` | `sq_penalty_exact` | `Lattice/Lib/Linear/Penalty.lean:110` |
| 任意 `n`，对角 | `sq_penalty_exact_finN` | `Lattice/Lib/Linear/PenaltyPerturbN.lean:217` |
| 满射矩阵 | `sq_penalty_exact_matrix` | `Lattice/Lib/Linear/PenaltyMatrix.lean:269` |
| 垂直约束 | `perpResid_localMin_of_nondegenerate` | `Lattice/Geo/Nondegenerate.lean:297` |

**每个精确性定理都由两半组成**（这是逼近版本的施工模板）：

```
正向：localMin_of_feasible     可行点 → 极小（用「平方 ≥ 0」）
反向：feasible_of_localMin      极小 → 可行（用 Fermat：IsLocalMin.hasDerivAt_eq_zero）
```

**逼近版本只需替换反向半**：把「梯度 = 0 ⟹ 残差 = 0」弱化为
「近似极小 ⟹ 残差有界」。正向半完全不动。

### 1.3 已有的逼近基础设施（不是从零开始）

| 部件 | 定理 | 给了什么 |
|:--|:--|:--|
| 函数逼近关系 | `Approx` / `ApproxOn`（`Lattice/Lib/Optim/RealApprox.lean:22,27`） | 全域 / 受限域上的 ε-接近 |
| 传递律 | `approx_trans` / `approxOn_trans_same`（:33,:127） | 逼近可以复合 |
| 域单调 | `approxOn_mono_domain`（:146） | 缩域保持界 |
| **扰动下的损失容差** | `loss_tolerance_under_perturbation`（:79） | **原约束满足 ⟹ 候选平方损失 ≤ (ε₁X+ε₂)²** ← 已经是「精确 → 带界」的实例 |
| 采样验证 → 全域 | `verifier_reliable_clean`（`Lattice/Lift/RealVerifierReliable.lean:41`） | `ε₀ + (L+L')·δ` |

`RealApprox` 已被 **6 个模块**复用（Optim / NonlinCompile / RoundtripBound / Distill /
FloatFormat / MixedPrecision / QAT），说明它是活的基础设施，不是孤立定义。

### 1.4 mathlib 4.14 的能力（决定 C 层可行性）

| 需要 | mathlib 有没有 | 证据 |
|:--|:--|:--|
| 局部极小 | ✅ `IsLocalMin` | `Mathlib/Topology/Order/LocalExtr.lean` |
| Fermat（极小 ⟹ 导数为 0） | ✅ `IsLocalMin.hasDerivAt_eq_zero` | 已被 `Penalty.lean:68` 使用 |
| 强凸 | ✅ `StrongConvexOn` | `Mathlib/Analysis/Convex/Strong.lean` |
| 强凸刻画 | ✅ `strongConvexOn_iff_convex` | 同文件 :165 |
| 一致凸 | ✅ `UniformConvexOn` | 同文件 :36 |

⇒ **C 层（强凸 + 梯度界 ⟹ 距离界）不是不可行，mathlib 有底座。**

---

## 2. P1：逼近精确的桥（第一优先）

> **本节已按探针实测重写**（`agent-tmp/bridge/Bridge1|Bridge5|Bridge10|Bridge34.lean`，
> 全部 `lake env lean` EXIT=0 且无 `sorryAx`）。原稿的三个候选里，一个被证成、
> 一个换了形态、一个**未证成**。

### 2.0 两个改变方案结构的实测发现

**发现一：障碍是结构，不是引理。**
`PenaltyEmbedding`（`Lattice/Lift/PenaltyEmbedding.lean:61-65`）只有两个字段：

```lean
structure PenaltyEmbedding (P X : Type) [TopologicalSpace X] where
  loss : P → X → ℝ
  Sat  : P → X → Prop
```

**它不记录 `loss = resid²`。** 因此「`loss ≤ ε²` ⟹ 残差 `≤ ε`」对**任意** `loss`
是**假命题**（`loss ≤ ε² ⟹ loss ≤ ε` 只在 `ε ≥ 1` 成立）。
⇒ 必须先补一个**向后兼容的字段**，而不是去找新引理：

```lean
structure ResidualEmbedding (P X : Type) [TopologicalSpace X] extends PenaltyEmbedding P X where
  resid : P → X → ℝ
  loss_eq_sq : ∀ p x, loss p x = resid p x ^ 2
```

这个结构 + 3 行证明**已实测通过**（`Bridge10.lean`）。

**发现二：`ε = 0` 退化时必须带 `PenaltySound`。**
把 `EpsSat 0` 退化成 `PenaltyExact` 时，若不带 `PenaltySound`，Lean 报
`expected E.Sat p x` —— 这**不是证明难，是命题缺失**：`EpsSat 0` 只说 `loss = 0`，
与 `Sat` 无关。这正好从另一条路径复现了 README §3.3 的 A/B 层区分。

### 2.1 四载体的共同落点（桥的入口）

四个精确性定理（`Penalty` / `PenaltyPerturbN` / `PenaltyMatrix` / `Nondegenerate`）
**全部走 Fermat 路线**，且落到同一个引理：

- `Lattice/Lib/Penalty/PolyExact.lean:112` `sq_eq_zero_of_localMin`
- 其核心是 `:81` `sq_localMin_dichotomy`：**`f x = 0 ∨ f' = 0`**

⇒ 这条二分法就是桥的入口。逼近版只需把它弱化为
「**要么残差小，要么梯度小**」，而后者可证。

### 2.2 候选清单（按实测状态，不是按设想）

| 候选 | 内容 | 工作量 | 实测 | ε→0 是否退化回精确 |
|:--|:--|:--|:--|:--|
| **(i)** | 总损失界 ⟹ 逐分量残差界 | **S** | ✅ **通过** | ✅ 退化回 A 层 |
| **(ii)** | 残差嵌入 ⟹ `\|resid\| ≤ ε` | **S**（需加上面的结构字段） | ✅ **通过** | ✅ 即 A 层 |
| **(iii)** | 近似极小 ⟹ 残差界 | L | ❌ **未证成** | ⚠️ 不退化 |
| **(iv)** | 强凸 + **值差** ⟹ 距离界 | S/M | ✅ 通过（**仅一维**） | ✅ `η=0` 即精确唯一性 |
| **(v)** | 采样验证 ⟹ 残差界 | S | ✅ 通过 | ⚠️ 仅 `δ=0` 退化 |

**(iii) 必须如实标注为未完成**：探针里 6 次 `nlinarith` 均失败；
其前提 `hmono`（方向下降率下界）在 mathlib 4.14 **没有供给者**，需要
`HasFDerivAt` 的定量形式，那是**新设施**，不是组合现有引理。

### 2.3 第一优先项（建议）

**(i) + (ii) 合并，落位 `Lattice/Lift/ApproxExact.lean`**，内容 6 条：

```lean
def EpsSat (E : PenaltyEmbedding P X) (ε : ℝ) (p : P) (x : X) : Prop   -- 带 ε 的满足
structure ResidualEmbedding ... extends PenaltyEmbedding                -- loss = resid²
theorem epsSat_zero_iff          : EpsSat E 0 p x ↔ E.loss p x = 0
theorem penaltyExact_of_epsSat_zero : PenaltySound E → (∀ p x, EpsSat E 0 p x → E.Sat p x)
theorem abs_resid_le_of_loss_le_sq  : E.loss p x ≤ ε^2 → |E.resid p x| ≤ ε
theorem geo_eps_bridge            : HasFDerivAt f f' x → f' ≠ 0 → IsLocalMin (·^2 ∘ f) x → |f x| ≤ ε
```

**为什么是它**（三条理由都是实测支撑的）：

1. (i) 与 (ii) **都是 S 级且已实测通过**，互不冲突：(i) 给「总损失 → 逐约束」，
   (ii) 给「损失 → 残差」。
2. **在 `ε = 0` 处严格退化、无余量**，正好通过 README 设的相容性自检
   （`component_eq_zero_of_totalLoss_eq_zero` 逐字复现 `realTotalLoss_zero_iff_all_outputs`）。
   **(iii) 恰恰通不过这一检验**——这是它不该做第一优先的技术理由，不只是难度理由。
3. 唯一需要的新东西是**一个结构字段**，不是新分析。

**附带白捡**：`geo_eps_bridge`（S 级）——直接组合 `PolyExact.sq_eq_zero_of_localMin`。

### 2.4 mathlib 4.14 实测能力（探针核实）

| 需要 | 是否存在 | 位置 |
|:--|:--|:--|
| `IsLocalMin.hasFDerivAt_eq_zero` | ✅ | `Analysis/Calculus/LocalExtr/Basic.lean:193` |
| `IsLocalMin.hasDerivAt_eq_zero` | ✅ | 同文件 `:256` |
| `IsCompact.exists_isMinOn` / `exists_isMaxOn` | ✅ | `Topology/Order/Compact.lean:250/:268` |
| `sq_le_sq` | ✅ | `Algebra/Order/Ring/Abs.lean:104`（⚠️ 不能 `rw` 匹配 `\|·\|`，须 `rw [abs_le]; nlinarith`） |
| `StrongConvexOn` / `strongConvexOn_iff_convex` | ✅ | `Analysis/Convex/Strong.lean` |
| `HasFDerivAt.pow` | ❌ **无** | 仓库 `RealVectorStationarity.lean:61` 已记录 |
| `RealStrongConvex.strong_convex_gap_le_grad_sq` | ✅（本库） | `:130-142`，可用**值差界替换梯度范数界** |

### 2.5 验收标准

- `lake build Lattice` 绿、`gate.py` I1–I8 绿、`verify_all.py` 全绿；
- **每条新定理都要过「ε → 0 退化回精确版」的相容性自检**（这是界紧性的判据）；
- ⚠️ 入库前必须检查命名冲突（`Lattice.Lift.EpsSat` 等是否与既有声明重名）——
  探针**未跑全量 build**，故这一条尚未验证。

---

## 3. P2：ε 的紧化

「逼近精确」若不能说明 ε 可压小，就只是把要求换了个说法。

**当前状态**：`RealVerifierReliable.lean:72` 自己写明——
> 这不是收敛率命题——`ε₀`、`δ` 在本文件中是自由参数，未证明它们可任意调小。

**可做的两件事**：

1. **给出紧化路径**：证明某个具体机制的 ε 随某参数（步长 / 迭代次数 / 采样密度）趋于 0
2. **给出不可紧化的反例**：若某载体的 ε 有正下界，证明这个下界存在——这同样有价值，它划定了「逼近」的极限

**注意**：不要用「证明 ε 可任意小」这种无法证伪的表述；要么给具体的 `ε ≤ g(k)` 且 `g(k) → 0`，要么给反例。

---

## 4. P3：6 个 owed slot

见 `gov/SLOTS.md`。逐个清偿或明确降级。

| slot | 它要什么 | 现状 |
|:--|:--|:--|
| `lift.compile.single_item_sound` | 单个编译项保语义 | 线性片段已还，一般后端未还 |
| `lift.embed.local_minimiser_exact` | 惩罚的极小点 = 满足点 | 若干载体已证，一般情形**已证否**（→ P1 接管） |
| `lift.extract.roundtrip` | 提取往返 | — |
| `core.repair.atomic` | 度量为 0 ⟹ 满足 | — |
| `core.semantics.external_bridge` | TorchLean 工具链桥 | 工具链债（需 Lean ≥ 4.26） |
| `geo.loop.convergence_is_single_step` | 多步收敛 | 已登记为 weakened |

**处置原则**：能还的还；命题本身有问题的**改写为逼近版**（不是删掉）；
工具链债**保持登记**并写明阻塞条件。

---

## 4b. P3b：门禁体系的真实强度（**实测发现的严重缺陷**）

> 这一节来自独立审计 + 我方复核。它改变了「本库门禁全绿」这句话的含义，
> 因此必须单列，不能埋在脚注里。

### 4b.1 「32/32 PASS」的真实含义

独立脚本 `agent-tmp/verify_always_zero.py` 扫描 `verify_all.py` 注册的全部检查，
解析各自 `main()` 的返回值，实测结果：

| 类别 | 数量 | 说明 |
|:--|--:|:--|
| **能失败的检查** | **15** | `gate` / `gate --selftest` / `registry` / 5 个 reactivity / `audit_geo` / `check_g7` / `escape_baseline` / `corrections-count` / `comments` |
| **恒返回 0（不可能失败）** | **16** | `reverify.py`、`reverify_chain.py`、`reverify_islands.py`、`audit_duplicates/bodies/docs_vs_code/reach/claims/liveness/region/tables/counts/abstraction/duplicate_statements/untracked`、`chain.py` |

**这些恒 0 的脚本多数是自认的「报告器」**（`audit_untracked.py:131` 写 `Exit 0 is deliberate`，
`audit_region.py:28` 写 `report only`，`audit_reach.py` 写 `human reading`）。
⇒ 设计上可以接受，但**汇总成一行 `PASS` 是误导**：它把「15 个能红的检查通过」
与「16 个不会红的进程退出码是 0」混成同一个数字。

**已修**：`verify_all.py` 引入 `REPORT_ONLY` 集合，输出改为两行分开计数：

```
VERIFY ALL [full]: PASS  (…s total)
  gating checks passed : 15  (these CAN fail)
  report-only checks   : 18  (these print findings; exit code is not a verdict)
```

**未做**：把某个报告器**升级为门禁**（需要先定义「什么算 finding → exit 1」，
这是改变它声称的内容，不是一行改动）。逐个待决，见 §4b.3。

### 4b.2 已修的实际 bug（有复现）

| # | 缺陷 | 证据 | 状态 |
|--:|:--|:--|:--|
| 1 | **`gate.py` 退出码映射缺 `I8`**：`:622` 遍历 `I1..I8`，但 `:625-626` 的映射表只到 `I7` ⇒ **I8 一旦报警就 `KeyError` 崩溃**（traceback + exit 1），被调用方读成「gate 崩了」而非「注释损坏」 | `agent-tmp/repro_i8_keyerror.py` 复现 `I8 -> KeyError 'I8'` | ✅ **已修**，并补 `check_i8_reactivity.py` 证明它现在返回 `COMMENT(9)` |
| 2 | **`gate_reactivity.py` 探针落在 kernel 区外** ⇒ `verify_all --fast` 下四个用例全报 `got 0`（门禁没看那个文件，不是门禁瞎了） | 修前 `REACTIVITY: 4 FAILURE(S)`；修后两种 scope 全 PASS | ✅ 已修 |
| 3 | **`SLOW_ONLY` 曾让两条「证明门禁会红」的检查在推荐命令下跳过** | 已改为空集 | ✅ 已修 |

### 4b.3 待决：报告器升级为门禁

对 16 个恒 0 的检查，逐个决定「保持报告器」还是「升级为门禁」。判据：

- **能机械判定**的（如 `audit_duplicates` 找到重复即算 finding）→ **升级**
- **需要人读**的（如 `audit_reach` 的「无人消费的定理」）→ **保持报告器**，但输出里必须
  明确标注，且不得计入 PASS 数

### 4b.3b 独立审计发现的其它门禁脆弱点（**均待修**）

| # | 症状 | 证据 | 影响 |
|--:|:--|:--|:--|
| 1 | **`intake_baseline.json` 恒为真**：它声明 `admit:0, axiom:0, sorry:0`，而 Reference 区实有 **68 `admit` + 1 `axiom`**（10 个文件） | `gate.py:139-145` 的 `tally` 只在 `zone=="intake"` 时累加，而 `zone_of()` 对本树只产出 `kernel`/`reference`/`root` | **I1/I2 在 intake 区从未真正工作**；同时给「Reference 不含逃逸」提供假证据。注意 `escape-baseline.json` 记录的 69 条是**对的**，两份基线自相矛盾 |
| 2 | **`geo_coverage.py` 已失效** | 实跑 `FileNotFoundError: _archive\GEO-COVERAGE.md` | 覆盖率工具是孤儿，不在 `verify_all` |
| 3 | **`gate_reactivity.py` 在 Windows 上可能崩** | 审计实跑：4 用例 OK 后 `os.remove(PROBE)` 抛 `PermissionError [WinError 32]`（进程自己正持有句柄） | 我的实测**未复现**（本机 4 次全 PASS），故记为**间歇性**，需加 try/except 与重试 |
| 4 | **`verify_all` 注册 33 项，README 曾写 32** | 已随 `check_i8_reactivity.py` 新增而变为 33，文档已同步 | 已修 |
| 5 | **`Core/Syntax.lean` + `Core/Semantics.lean` 零定理** | 实测：`Core/` 13 模块合计 51 theorem / 18 lemma，这两个是纯定义+接口 | 决策 1「符号模型实现在 Core 上」目前**没有可证的后果** |
| 6 | **`Lattice.Lv00.*` 第三套命名空间** | `Lib/Chain/RealLv00*.lean`、`Lib/Compiler/RealLv00*.lean` 的声明仍用 `Lattice.Lv00.*` | 与「`Lattice.<层>.<领域>.<模块>`」叙事不一致，也是 `audit_duplicates` 718 组重复的主要来源 |
| 7 | **`Lift/` 里两套符号侧类型并存** | `ConvertLinear.lean` 等 22 个模块用裸 `namespace Lattice` + 旧 `LinearConstraint`/`LinearNeuron`，与 `Core.LinearForm` 并列 | **与 I3 同类的问题换了类型名**：单一语义概念仍有两处定义 |
| 8 | **`Lib/LinearAlgebra/RealSparseCoding.lean`**：172 行 / 6 行代码，docstring 描述三项成果，**0 定理** | 实测 | 疑似 docstring 说谎，需人工复核 |
| 9 | **2446 条无消费者定理 / 49 个模块级孤岛** | `audit_reach.py` / `audit_islands.py` | 均为 advisory，**不阻断**。是否算缺陷取决于「库」还是「应用」定位 |

### 4b.4 反应性覆盖表（哪些不变量被证明过会红）

**本节的结论来自实际注入，不是读代码推断**（脚本：`agent-tmp/inject_i3.py`、
`agent-tmp/diagnose_i3_abbrev.py`，注入后按 SHA256 校验还原）。

| 不变量 | 注入的缺陷 | 实测结果 | 结论 |
|:--|:--|:--|:--|
| **I3**（语义概念） | 在 `Core/Semantics.lean` 加一个重复的 `def eval` | **exit 3，I3 报警** | ✅ **真的会红** |
| **I3**（`abbrev` 同文件重复） | 同一文件内重复 `abbrev Star` | **exit 0，不报** | ⚠️ 判据是 `prev_file != r`，**同文件重复被有意放过**（由 Lean 自己报错兜底）。行为合理，但**未记录** |
| **I3**（`abbrev` 跨文件重复） | 两个不同文件各声明 `abbrev Star` | **exit 3，I3 报警** | ✅ 会红 |
| I4 分层 | 注入跨层 import | exit 4 | ✅（审计实测） |
| I5 端到端 | `gate_reactivity.py` 的 `e2e_fake` | exit 5 | ✅ |
| I6 空位 | 审计注入 `discharged "no_such_decl_xyz"` | **exit 8，只报 I7，I6 静默** | ❌ **未证实**：探针放在 `Lattice/Core/` 时 I7 先触发，掩盖了 I6 |
| I7 产物 | 新增未编译的 `.lean` | exit 8 | ✅ 会红 |
| I8 注释 | `check_i8_reactivity.py` 三种形态 | exit 9 | ✅（本次新增） |

**修正此前的说法**：本文件早期版本写「I3/I4/I7 从未被证明会红」。实测后必须更正为：
**I3 和 I4 会红，且已证实**；真正未证实的是 **I6**，以及 I3 的「同文件重复」这一边界。

**仍缺的反应性测试**：I6（需要把探针放进已编译路径再注入，避开 I7 抢占）、
I3 的同文件边界（应写成文档化行为而非缺陷）、`check_g7.py`（零测试，且 `:61` 的
`ok &= found2` 把「缺陷存在」当「检查成立」）。

---

## 5. P5：Cv00 段（已论证不做，需固化）

`gov/check_g7.py` 实测 5 个断点，且「复现结果: 全部一致」：

| # | 断点 | 实测 |
|--:|:--|:--|
| 1 | `compile_constraint` 的 `\| _ => none` | 12 处（兜底，非缺分支） |
| 2 | `eval_expr .var` 只取 `ptX` | 语义错（env 是 ℝ×ℝ 却只取 x） |
| 3 | `CompilerCorrectness` 出现 `Cv00` | **0 次** |
| 4 | `exec_stmt` 实现比例 | **2/9**，7 个静默跳过 |
| 5 | LvFormal 提到 `Weight` 的文件 | **0 个** |

**处置**：不修。理由已写入 README §3.1。**需要做的事是把「不修」的理由与证据固化到
治理层**，使后来者不会误以为这是遗漏。

---

## 6. 工程项（P6–P8）

### P6：可复现构建

**问题（实测）**：`lake-manifest.json` 里 mathlib 是 `type=path`、**无 rev**；
其余 8 个包（plausible / LeanSearchClient / importGraph / proofwidgets / aesop / Qq /
batteries / Cli）都是 `type=git` 且**有** rev。
旧库 `lattice/lean/lake-manifest.json` 的 mathlib 是 `type=git`、
rev = `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`。

⇒ **新库无法在另一台机器上确定地复现出同一个 mathlib。**
当前任何一个 `lake build` 的成功，都是相对于 `../lattice/lean/.lake/packages/mathlib`
这个**本地目录**而言的，而该目录不受任何 rev 约束。

**方案**（需决策，二选一）：
- (a) 改为 `require git` + `rev = "4bbdccd9…"`，本地用 `.lake/packages` 缓存复用
  —— 需先验证 Lake 在已有缓存时是否还联网
- (b) 保留 path，但把 rev **写进 `lake-manifest.json` 之外的地方**（README + 一个
  bootstrap 脚本），并在 `lakefile.toml` 注释里显式声明「本工程假定该 rev 已就位」

**验收**：另起一个干净目录，按文档步骤能从零构建出**同一组** olean。

### P7：CI 实际可跑

当前 `.github/workflows/lattice.yml` **YAML 通过（`yaml.safe_load` 校验）、但从未在任何 CI 上执行过**。

**实测的致命缺陷**（逐行推演 + 路径验证）：

| # | 缺陷 | 证据 | 后果 |
|--:|:--|:--|:--|
| 1 | `lattice.yml:72` 读 `lattice/lean/lake-manifest.json` | 该文件在 `lattice-new/` 下 **不存在**（实测 `Test-Path` = False） | `set -euo pipefail` 下 **step 立即 exit 1**，后续全挂 |
| 2 | 只 clone mathlib，不 clone 8 个兄弟包（aesop/batteries/…） | mathlib 自身 lakefile 需要它们 | `lake update` 失败 |
| 3 | `:82 lake update` 会按浮动的 inputRev 重解析（`Qq=master`、`plausible=main`、`proofwidgets=v0.0.47`） | manifest 里这些是浮动标签 | **破坏 `:64-66` 注释声称的「same revision」** |
| 4 | `:88 hashFiles('lattice/lean/lake-manifest.json')` 输入不存在 | 同上 | 缓存 key 退化，永不命中 |
| 5 | `lake build Lattice` 的 target 名可能应为小写 `lattice` | 旧库有专门注释记过这个坑 | **未验证**（需跑 lake） |

⇒ **CI 的「绿」目前只等于「21 秒的文本门禁绿」**，而「683 olean 编译通过」在 CI 里**没有证据**。

**修法**：先做 P6（改 git require 带 rev），再一并修上表 5 点。
**验收**：CI 上 `build-and-verify` job 真实跑通；若暂时做不到，必须在 README 里
**明确写「CI 未验证」**（当前 README 未写，属文档缺口）。

### P8：CORRECTIONS B481–B498

`archive/PROCESS.md` 引用了 B481–B498，`archive/CORRECTIONS.md` 正文只到 B480。
**冻结档案不改**，因此处置只能是：在**非冻结**文档里登记这个断链。

**另发现的相关缺口**：`archive/` 下 **没有任何 README 或失效声明**，而其中
`CORRECTIONS.md` 有约 **745 处**路径指向旧库（`lean/`、`scripts/`、`zero/`、`verify.ps1`），
`HANDOFF.md:178` 甚至写着 `cd …\lattice\lean` —— 新接手者照做会直接失败。

**建议处置**（原文字节零改动）：
新增 `archive/README.md`，三块内容：
(a) **坐标系声明**：本目录所有路径以旧库 `lattice/` 为根，在新库一律失效；
(b) **新旧名称对照**：`lean/<M>.lean` → `Lattice/<层>/<域>/<M>.lean`、
`scripts/verify.ps1` → `gov/gate.py`+`gov/verify_all.py`；
(c) **每份文档的有效性标注**：「结论仍有效 / 已被 X 取代 / 仅历史记录」。

### P8b：本地提交门禁**无法安装**（比「没装」更严重，已实测）

**⚠️ 本节结论推翻了一个想当然的判断。** 审计建议是「修 1 行路径 + 装钩子」。
实际动手后实测发现：**修好路径反而会让仓库完全无法提交。**

| 步骤 | 实测结果 |
|:--|:--|
| `gov/install_hook.py:14` 的 `SRC` 指向不存在的 `Lattice/gov/pre-commit` | 确实错，**已修**为 `gov/pre-commit` |
| `gov/pre-commit` 内容全是旧路径（`zero/`、`$ZERO/gov/gate.py`） | 确实过时，**已改**为 `gov/gate.py` |
| 安装钩子后**手工执行** `sh .git/hooks/pre-commit` | ❌ `sh.exe: fatal error - couldn't create signal pipe, Win32 error 5` |
| 安装钩子后**真的 `git commit`** | ❌ 同一错误，**提交被拒绝（exit 1）** |

**根因**：msys 的 `sh.exe` 在本环境的沙箱下无法创建信号管道。
旧库 `HANDOFF.md` §5.3 已记录同一现象，并称之为「**已安装 ≠ 在提交路径上生效**」。
但实际情况比那句话更糟：**它不只是不生效，它会阻断提交**。

**处置（已完成）**：
- 钩子**已移除**，提交路径恢复（实测 `git commit --allow-empty` 成功）；
- `install_hook.py` 改为**默认不安装**，并打印实测原因；`--force` 才安装并提示如何自检；
- **本库当前的状态是：提交路径上没有门禁**，README 必须如实这样写。

**未做的替代方案**（需决策）：
1. **`core.hooksPath` 指向一个纯 Python 钩子**（git 对有 shebang 的脚本仍会经 sh 启动，
   故需实测是否可行——**未验证**）；
2. 用编辑器/IDE 的保存钩子或任务运行器；
3. 接受现状：门禁只在 **CI 与手工运行**时生效（最诚实的做法，前提是 P7 修好）。

---

## 6b. P9：证明承重性与空壳模块

### 6b.1 已实测的空壳与零定理模块

脚本口径：去注释后统计 `theorem`/`lemma` 数量，并排除聚合器
（`Lattice.lean`、`Lattice/Lib/<Topic>.lean` 等）。

| 类别 | 数量 | 例子 |
|:--|--:|:--|
| **真空壳**（去注释后 ≤ 6 行代码，无定义也无定理） | **2** | `Lib/Convex/RealInfConvAttain.lean`（4 行，文件第 6 行自认「本文件当前没有任何定理」）、`Lib/LinearAlgebra/RealSparseCoding.lean`（6 行） |
| **零定理但有定义** | 18 | `Chain/RealChainAxioms{,2,4}`、`Chain/RealChainEntryOOVAxioms`、`Chain/RealChainRun`、`Chain/RealLv00Geometry`、`Compiler/RealLv00Compiler{,Codegen,Language}`、`Lib/Lift/RealContractAxioms`、`Lib/Meta/RealNegativeCore`、`Lib/Editing/RealConversionStability` 等 |

**判断**：
- `Core/Syntax.lean`、`Core/Semantics.lean` 零定理是**正常**的：它们是语言层定义，
  定理在 `Core/Check.lean` 与 `Core/Logic.lean`。
- **`RealInfConvAttain` 是第一顺位**：它占一个模块位，在构建里什么都不贡献。
  两个选择：补齐计划的三条定理，或**移出构建并登记为未做**（不能留着当已完成）。
- 其余 17 个需逐个判断「定义本身就是交付物」（如 Axioms 类）还是「只写了一半」。

### 6b.2 承重性扫描器的现状（工具已建，但还不能当判据）

`agent-tmp/detect_loadbearing.py` 实现三种形态的机械检测，本次实测命中：

| 形态 | 命中 | 读法 |
|:--|--:|:--|
| S1 证明体是另一条定理的直接引用 | **1141** | 绝大多数是正常 API 包装（`rfl` 等式、`_nonneg`），**不能当缺陷数** |
| S2 声明的前提在证明体中未出现 | **2238** | 含大量 `rfl` 类定义等式，同样需人工过滤 |

⇒ **机械判据无法直接给出缺陷清单。** 要做 P9，必须先**收窄判据**：
只对名字声称结论性的定理（`_exact` / `_sound` / `_converges` / `e2e_`）做 S1/S2 检测。
这正是旧库 `check-rfl-vacuity` / `check-trivial-proofs` 有效的理由——它们**只针对特定形态**，
而不是扫全库。

---

## 7. 执行纪律

1. **不写桩**：任何「未做」必须显式登记，不得用返回 `true` 的占位。
2. **不动冻结档案**：`archive/` 内 6 份文件逐字节冻结（SHA256 校验）。
3. **每项改动都过门禁**：`lake build` + `gate.py` + `verify_all.py` 三件套。
4. **命名如实**：定理名声称的范围必须是它证明的范围（I5 会查）。
5. **界要紧**：任何逼近定理必须能通过「ε → 0 退化回精确版」的相容性自检。
6. **证明先写思路再动手**：每一条新定理先在文件头写「要证什么 / 为什么成立 /
   依赖哪条已有引理 / 与精确版如何相容」，写完思路再去查 mathlib 与文献。
7. **学术化表述**：文档与证明注释用标准数学语言（定义—命题—证明），
   不用口语、不用「大约/基本上」这类无法核验的修饰。
8. **可在不引起歧义时泛化**：定理能对更弱的假设成立，就不要绑死在特例上
   （例：`sq_penalty_exact` 对任意 `LinearOrderedRing` 成立，不只 `ℝ`）。
9. **一次只做一件事并声明处在第几步**：每轮开始写「本轮做什么、依据规划第几节」。

---

## 8. 语言、结构、命名与证明链（**用户明确要求，此前规划缺失**）

> 这一节回答四件在旧规划里没有的事：**证明链梳理、学术化、按需分文件、命名标注**。
> 全部以实测的现状数字为依据。

### 8.1 命名：现状与目标规范

**实测口径**（`agent-tmp/naming_census.py`，**先剥注释再统计**，嵌套感知）；
注意第一版统计未剥注释，把 docstring 里的 "theorem that consumes it" 误当成声明。

| 指标 | 实测 |
|:--|--:|
| 内核声明总数（theorem/lemma/def/abbrev） | **10,105** |
| 其中 theorem 6,999 / def 2,184 / lemma 851 / abbrev 71 | — |
| **未采用 snake_case** | **2,201**（多为 camelCase 的 `def`/`abbrev`，如 `compileSingleItemSound`） |
| 名字带撇号 `'` | **60**（`progress'`、`relu_of_nonneg'`…） |
| 带 `_aux` / `_example` 后缀 | 15 / 5 |
| **名字声称结论性**（`_exact`/`_sound`/`_converges`/`end_to_end`/`_correct`） | **106** ← 承重性审计的靶群 |

**目标规范**（写入 `CONVENTIONS.md`，并由门禁检查）：

| 对象 | 规范 | 理由 |
|:--|:--|:--|
| 定理 / 引理 | `snake_case`，**性质在后** | 与 mathlib 一致；`progress'` 这类撇号名无法检索 |
| 定义 | `camelCase`（Lean 惯例）或 `snake_case`，**同一文件内不混用** | Lean 标准库用 camelCase 定义、snake_case 定理 |
| 结论文 | 名字必须**限定**：`sq_penalty_exact` 而非 `penalty_exact` | 与 I5「名字如实」互补 |
| 撇号 `'` | **禁用**；用 `_v2` 或改语义名 | `'` 在 grep/URL/表格里都难处理 |
| `_aux` / `_example` | 禁止进入公开表面；`example` 不命名 | 这些是脚手架，不应出现在 API |

**分阶段推进**（改名有风险，必须小步）：
1. **先禁新增**：门禁加一条 advisory「新文件不得含撇号名 / camelCase 定理名」；
2. **再收敛撇号**（60 个，S 级）；
3. **最后处理 camelCase 定义**（2,201 个中的定义部分）——这一批改动面最大，
   必须逐文件改名并构建验证。

### 8.2 文件结构：该分的分

**实测最大的 8 个文件**（按声明数）：

| 文件 | 声明数 |
|:--|--:|
| `Lib/Chain/RealN2AxiomDischargeJia.lean` | 165 |
| `Lib/Chain/RealLv00Solver.lean` | 104 |
| `Lib/Compiler/RealMutualRecursion.lean` | 87 |
| `Lib/Lift/RealNonlinearFidelity.lean` | 86 |
| `Lib/Chain/RealLv00AxiomDischargePerPackage.lean` | 84 |
| `Lib/Chain/RealNumericChainOrder.lean` | 66 |
| `Lib/Quantization/RealIEEE754.lean` | 66 |
| `Lib/LearningTheory/RealCausalDoCalculus.lean` | 62 |

**判据（写入 `CONVENTIONS.md`）**：
- **单文件 ≤ 500 行**且 **≤ 60 个声明**（旧库同款预算，但从未被门禁执行）；
- 超过则按**主题**拆分，拆出的文件名必须说明主题（`…AxiomDischarge.lean` +
  `…AxiomDischargeAux.lean` 不算，要 `…AxiomDischarge/PerPackage.lean` 这类）；
- **拆文件不改名字**：`import` 路径变，声明全限定名必须保持一致，否则下游全断。

### 8.3 证明链：从「谁引用了谁」变成「一条可读的链」

现状：`gov/chain.py` 生成 `gov/PROOF-CHAIN.md`（**1.36 MB**，已 tracked），
`gov/proof_chain_geo.py` 生成 `PROOF-CHAIN-GEO.md`。两个都是**机器生成的引用图**，
不是「链路文档」。

**缺的是**：一条从 L0 到 L3 的**人工可读**证明链——每一跳由哪条定理承担、
它的前提是什么、前提由谁供给。实测已有的事实：
- `Geo/Pipeline` 的两个定理**前提不承重**（`_hdec` 未使用，见 README §7 G1）；
- `Lift/` 的 `Compiler.sound` / `Representation.roundtrip` 是**结构字段**，
  **没有内核实例**（见 §4 A1/A3）；
- 真正串起来的是 `Lib/Chain/RealEndToEnd`（旧树口径），而它的 `e2e_sound`
  证明体逐字是 `symbolToWeight_correct`。

⇒ **`PROOF-CHAIN-RUNG.md`（新建）** 应按四跳组织，每跳一节，每节必须回答：
1. 这一跳的**义务**是什么（一句精确的 Lean 命题）；
2. **谁承担**它（定理名，或「无人承担 — 登记为 slot」）；
3. 它的**前提**由谁供给（递归到公理层）；
4. **是否承重**（前提去掉后命题是否仍成立——用 Lean 实测）。

第 4 条是这份文档与现有两个生成物的根本区别：它记录**否证实验**，不只是引用关系。

### 8.4 学术化表述

| 现状问题 | 实测 | 规范 |
|:--|:--|:--|
| 文件头大量口语化说明（「要点」「注意」「白捡」） | 全库普遍 | 改为「接口 / 契约 / 边界 / 已知限制」，保留判断、去掉修辞 |
| 数字散落在注释里（`12/12`、`683`、`451`） | 多处 | 数字必须注明**测量口径与时点**，或改为由脚本生成 |
| 定理注释只写「已证」 | 常见 | 必须写：**命题、为何成立、依赖、适用边界** |

**分阶段**：
1. 先对 **106 个「声称结论性」的定理**统一注释格式（它们最容易被误读）；
2. 再对 `Core` + `Lift` 两层（承重层）统一；
3. `Lib` 的 588 个按需（触碰到才改），**不做无差别重写**——那会制造大量无意义 diff。

---

## 9. 优先级建议

| 顺序 | 事项 | 理由 |
|--:|:--|:--|
| **1** | **P10：写 `CONVENTIONS.md`** | 后面所有改动（P11–P15、P1 入库）都要遵守它；没有规范就改，等于再制造一次混乱。**成本 S，收益最大** |
| **2** | **P11：撇号名收敛（60 个）** | 独立、可机械验证、不涉及外部语义；是「命名标注」里最便宜的一步 |
| **3** | **P1：把 (i)+(ii) 入库** | 探针已实测通过（S 级×2），是「逼近精确」唯一的落地点；且 ε=0 处严格退化 |
| **4** | **P13：`PROOF-CHAIN-RUNG.md`** | 证明链梳理；**必须含否证实验**（去掉前提看命题是否仍成立），这一步会顺带把 G1 那类问题全找出来 |
| **5** | **P7 + P6：CI 修好并真跑** | 「683 olean 编译通过」目前在 CI 里**没有证据**；5 处缺陷是确定的 |
| **6** | **P3b：报告器 vs 门禁逐个定性** | 「PASS」曾把 15 个能红的检查与 18 个不会红的进程混成一个数（汇总已改，逐项待决） |
| **7** | **P3b-2：补齐 I6 / G7 的反应性测试** | 实测 I3/I4/I7 会红；**I6 仍未被证实**；`check_g7` 把「缺陷存在」打印成「一致」 |
| **8** | **P3：owed slot 清理** | 债务必须结清或降级；`lift.embed.local_minimiser_exact` 由 P1 接管改写 |
| **9** | **P12：超大文件拆分** | 8 个文件超 60 声明；拆文件改 import 路径，风险中等，应在语义稳定后做 |
| **10** | **P14：106 个结论文注释统一** | 学术化；靶群明确（`_exact`/`_sound`/`_converges`/`end_to_end`） |
| **11** | **P2：ε 的紧化** | 决定「逼近」是否只是换说法 |
| **12** | **P8：`archive/README.md` 失效声明** | 约 745 处死路径会误导每个新接手者 |
| **13** | **P1'（原候选 iii）：近似极小 ⟹ 残差界** | 探针失败，需新设施。**不可宣称已完成** |
| **14** | **P4 / P9** | 长期项，需要新的分析基础设施 |
| **15** | **P15：camelCase 定义收敛** | 2,201 个中定义部分改动面最大，放最后 |
| **16** | **P5：Cv00 固化** | 工作量小，应在新架构稳定后再写 |

> **P8b 已关闭**：实测发现 sh 钩子会**阻断提交**（`git commit` exit 1），
> 已移除钩子、并把安装器改为默认不安装。本库当前**提交路径上没有门禁**——
> 这是已记录的状态，不是遗漏。

---

## 附：本文的证据来源

- 定理与行号：`grep` 实测（脚本 `agent-tmp/check_readme_claims.py` 的同类方法）
- mathlib 能力：`Mathlib/Analysis/Convex/Strong.lean`、`Mathlib/Topology/Order/LocalExtr.lean` 实读
- G7 断点：`python gov/check_g7.py` 输出「复现结果: 全部一致」
- Slots：`gov/SLOTS.md`（由 `gate.py` 生成，非手写）
- 构建与门禁状态：`lake build Lattice` / `python gov/gate.py` / `python gov/verify_all.py`
