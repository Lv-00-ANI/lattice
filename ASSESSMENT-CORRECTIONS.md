# 评估核对备忘（第 30 轮更新）

> **目的**：正式评估以 `acbdf6b`（344 提交）为基线，且**已被重发多次**。本备忘把它与
> **当前 HEAD（360 提交）** 对齐，列出**已关闭的条目**、**剩余的条目**、以及**已失效的路径**。
>
> **只记增量与状态，不重算百分比**——见 §5。

---

## 1. 数字：相对评估基线的增量

| 指标 | 相对评估 | 说明 |
|:--|--:|:--|
| 提交 | **+16** | |
| 定理 / 引理 | **+9** | 新增集中在治理仪器上，不是新数学 |
| 检查器 | **+13** | 67 → **80**（**61 门禁** / 19 报告器） |
| 模块 | 0 | 834 |
| 欠账 / 永久边界 | 0 / 0 | 与评估一致（0 / 4） |

**当前绝对值以 `README.md` 的计数行为准**（`audit_counts.py` 核对它）。

---

## 2. ✅ 评估列为「未做」，而已关闭的条目

| ID | 评估写的 | 现在 | 提交 |
|:--|:--|:--|:--|
| **L0-1** | 「只差一个 `omega`」 | ✅ **`layerWords_injective` 已证**（走解码器，不做依赖重写） | `05144eb` |
| **L0-2** | 「无 decoder」 | ✅ **`wordsLayer_layerWords` 已证** | `05144eb` |
| **L4-1** | 682/872 = 78.2% | ✅ **885 / 885 = 100.0%**，由 `check_coverage_claim.py` 计算、门禁核对 | `c23b007`…`d23b120` |
| **L4-2** | 5.1%，无协议 | ✅ **抽样协议写成可证伪的断言**：样本**偏向「曾看起来重要」**；不声称已审、不声称不必审、不声称有可证优先级 | `c3b0073` |
| **L4-5** | 「判定会过期，无门禁」 | ✅ **`check_verdict_freshness.py`**：12 条判定指向已不存在的声明，全部登记并**在 `PROOF-DEBT` 里逐条列出** | `f07e2a5` |
| **L4-6** | 「只 3 语法形状」 | ✅ **实测已覆盖** `:= h`（26 条全在 `known` 集）；评估暗含的缺口不成立 | `c49d94a` |
| **L4-7** | 「0.4%」 | ✅ **`check_endtoend_floor.py`**：内容跨层 **1,826 条**设下限，下降失败、增长放行 | `c49d94a` |
| **L4-4** | 「`decide` 表与库一致性」 | ✅ **构建期 `run_cmd`** 从 `Lean` 环境取 `StructureInfo.fieldNames.size`，不等即 `throwError`；**实测会失败** | `269a9ae` |

**评估的 P4 现在只剩 L4-3（账本本身）与 L4-8（未用前提）未处理。**

---

## 3. ⚠ 两个评估**没有**提到、但本轮发现的缺陷

**这两条比 P4 里任何一条都更接近「评估自己会漏掉什么」。**

### 3.1 `PROOF-DEBT` 用三种方式说了同一个覆盖率

表格 **78.2%**、正文 **100%**、更正段 **839**。**三个数都来自手写或过期的入度，没有一个能复算。**
新增仪器后三者合一，且**生成器与门禁共用同一个测量函数**，所以不可能再漂。

### 3.2 12 条判定在评判**已经不存在的定理**

`check_proof_debt_orphans` 只核**文件**、从不核**名字**。全树扫描确认这 12 个名字**一处声明都没有**。
现在有门禁，且在文档里逐条列出。

**评估的「证明债承重覆盖 78.2%」这一行，正是 3.1 的下游**——它读的是那张没人核对的表。

---

## 3.3 第 45 轮：清单的「310 个陈旧 olean」是 **mtime 假象**，不是缺陷

清单 `P0-11` 写「310 个 olean 早于源文件」并把它当缺陷。**实测数字完全正确**（964 个源、310 个 mtime 更旧、
533 个不旧），**但那个数字不是缺陷**：

`lake` 决定重建什么用的是**内容哈希**，不是 mtime。一个 olean 的 mtime 比源文件旧，**完全可能仍然是从那个源
产生的**。**证明它不是正确性问题的，是 `lake build Lattice` 在 310 个原样保留的情况下通过。**

**按 mtime 设门禁会在每次 `git checkout`、每次 `touch`、每次时钟变动后误报**——那本身就是一种坏掉的检查。

**真正的那一条是另外 121 个：它们完全没有 olean，而且全部在 `Reference/` 下**——那棵子树从不构建
（清单的 `P0-17`）。**它是已知边界，不是回归**，所以 `check_olean_presence.py` **报告它、不为它失败**：
**一条会对没人会去动的边界持续失败的门禁，最终只会被基线静音。**

**被门禁的是**：非 `Reference` 模块没有 olean——那意味着它**从未进入任何构建**。**今天这个数是 0。**

---

## 3.4 第 51 轮：`e2e_sound` 的「可陈述性承重」辩护是**错的**

清单 `P0-13` 说 `e2e_sound`「不能是单级重述」。**实测（第 51 轮）：**

```lean
theorem e2e_sound {s : List Char} {ts : List CharToken} {cs : ConstraintSet}
    (h0 : tokenize s = some ts) (h1 : Extract (L1Bridge ts) cs) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x :=
  symbolToWeight_correct cs x
```

**证明体就是 `symbolToWeight_correct cs x`，一个字没改。** `h0`/`h1` **在证明里没出现**（Lean 报两条
`unused variable` 警告——实测确认过这条 linter 对这种形状会报）。

**文件原来给出的辩护是**：「`h1` 提供 `cs`，**删掉它 `cs` 就没有来源，结论无法陈述**」。

⭐ **这个辩护是错的**：`cs : ConstraintSet` 与 `x : List Int` **本身就是参数**。删掉 `h1`，
结论 `AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x` **照样可以陈述**，而且**更强**（少了假设）。
**`h0` 同理**：它只把 `s` 与 `ts` 绑在一起，而这两者不出现在结论里。

**⇒ 精确结论**：`e2e_sound` 的**类型**里出现 L0/L1（经 `h0`/`h1` 的绑定），
但**内容与 `symbolToWeight_correct` 完全相同**——L0/L1 的绑定**不约束结论**。
**「e2e」在名字里，不在陈述里。**

**端到端的内容在别的定理里**：`e2e_path_exists`（通路非空，**这是让上面那条不空洞的那一条**）、
`e2e_loss_at_L2L3` / `e2e_loss_at_L0L1` / `e2e_loss_compound`（链路**在哪里丢信息**）、
`e2e_not_injective` / `e2e_no_left_inverse`、`e2e_bridge_sep_is_load_bearing`。

**为什么 L0→L3 的强陈述不存在，而不是没做**：要让 `AllSatisfied` 成为 `s` 的**性质**，需要 `Extract` 是
**函数**；**而 `Extract` 是关系**，同一个 `ts` 可以有多个 `cs` 满足它。**那是可陈述性的障碍，不是工作量。**

---

## 3.5 第 51 轮：`check_vacuous_hypotheses` 把 Class A **委托给了一个没人读的输出**

`check_vacuous_hypotheses.py` 的文件头写着：

> **Class A -- dead hypothesis.** ... Lean's own `linter.unusedVariables` reports it, so this file does NOT
> reimplement it: **the compiler already found all 182 of them** and `PROOF-DEBT.md` tracks the count.

⭐ **「tracks the count」是全部**：**182 条被计数、从未失败**。**没有任何门禁读编译器的输出**——
而编译器只在**重新编译**时才吐警告，所以连「读一次」都不稳定。

**这是本会话那个模式的最外层变体**：不是「检查器不能失败」，而是「**检查器把工作交给了另一个检查器，
而那个的输出没进判决**」。

**第 51 轮量到的候选**：**139 条定理的某个绑定变量既没传给证明所用的引理、也没出现在结论里**
（249 个绑定）。**那是待审清单，不是判决**——解析器在含类型归属的绑定上会误判。**未做成门禁。**

---

## 3.6 第 54 轮：**撤回**第 53 轮对 `audit_counts` 的一次错误指控

第 53 轮的提交信息里写了：

> 一条位于该文件高处的定理**对计数器是隐形的**。（`audit_counts` 报总数不变 8,688，移到 L595 才 8,689。）

⭐ **那句话是错的，本轮撤回。** 真相：

`RealEndToEnd.lean` 的 L29–39 是 **docstring 里的一个 Markdown 围栏代码块**，里面**引用了**
`extract_to_weights`（含 `:= symbolToWeight_correct cs x`）。第 53 轮用**字符串锚点**插入新定理，
锚点命中**那段引文**，于是新定理**落在注释里**。

- **构建通过**（注释文本不参与 elaborate）；
- **`audit_counts` 正确地没有数它**——它的 `strip_comments` 就是为此而写，文件里写着
  「a `theorem` mentioned inside a docstring is not a declaration」。

**⇒ 计数器是对的，插入是错的。** 我把一次**自己的编辑事故**记成了**仪器的盲区**。

**真正的缺口不是「计数器看不看得见」**（它看得见，而且看得对），**而是「我的文本有没有落在注释里」——
没有任何东西报告这件事**。

**新增 `gov/check_comment_shadow_declarations.py`（report-only）**，按落点分三类：
代码里 **8,687**、注释里的围栏引用 **61**、注释里但不在围栏中 **17**（多为散文，如「theorem that」）。

⚠ **注意 8,687 与官方 8,689 差 2**：本文件的注释边界处理比 `audit_counts` 简单。
**权威是 `audit_counts`**；这条普查的用途是**按落点分类**，不是提供第二个计数口径。

**纪律**（写下来，因为它是这次事故唯一可迁移的教训）：
> **加了一条声明之后，声明计数必须变动。** 没动，先去看它是不是落进了注释。

---

## 4. 失效路径：评估里的 `Geo/`、`Lift/` 引用

三次搬迁（`Lift`→`Runtime`、`Geo`→`Domains`、`Audit`→`Evidence`）之后，评估里这些引用**在树里不存在**：

| 评估里的引用 | 现在的路径 |
|:--|:--|
| `Lattice/Geo/ConstraintDescent.lean` | `Lattice/Domains/Geometry/ConstraintDescent.lean` |
| `Lattice/Geo/NetLoss.lean` | `Lattice/Domains/Constraints/NetLoss.lean` |
| `Lattice/Geo/PenaltyLoss.lean` | `Lattice/Domains/Constraints/PenaltyLoss.lean` |
| `Lattice/Geo/GeoLadder.lean` | `Lattice/Domains/Geometry/GeoLadder.lean` |
| `Lattice/Lift/ProgramAST.lean` | `Lattice/Runtime/ProgramAST.lean` |
| `Lattice/Audit/*` | `Lattice/Evidence/*` |

⚠ **namespace 未改**（§2.8 零轮规则），所以**定理名一律不变**——`GeoLadder.lean:129` 这类内容引用仍然成立，
只是路径要换。**建议用 `gov/_debt_path_map.py` 的 `PATH_MAP` 机械替换**，那是本会话十次路径事故的教训。

---

## 5. 本备忘**没有**做的事

- **没有重算 70–75% / 50–55% / 30–35%。** 这三个是人工估计，而「到 C 核心规格闭环的百分比」**没有定义**。
  能数的是 **P4 的 8 项里 6 项已关**，那个我给了。
- **没有把 `decide` 定理说成变强了**：它们仍然只陈述表自身的性质；现在旁边多了一个关于库的仪器。
- **没有重判那 12 条失效判定**：它们的实质是否在新名字下成立，是对**新声明**的问题。
