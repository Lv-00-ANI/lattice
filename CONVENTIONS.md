# LATTICE 表述与结构规范（CONVENTIONS）

> 本文件规定 **命名、文件划分、证明注释、证明链记录** 四类规范。
> 每条规则要么**可机械检查**，要么明确写出「本规则不可机械检查，由评审把关」。
> 凡不可执行却写成仿佛可执行的规则，本身就是本仓一直在治理的那类缺陷。
>
> 适用对象：`Lattice/` 下全部源码（`Reference/` 是上游资产，不适用）。
> 数字均为实测（2026-10-25），口径见文末 §6。

---

## 0. 一句话

**名字要说明它证明了什么；文件要说明它承载什么；注释要说明为什么成立。**
三者缺一，读者就只能靠猜，而猜出来的结论会变成下一轮的「文档说谎」。

---

## 1. 命名

### 1.1 规则

| # | 对象 | 规则 | 可机检 |
|--:|:--|:--|:--|
| N1 | **定理 / 引理** | `snake_case`；**性质写在最后**（`sq_penalty_exact`，不是 `exact_penalty`） | ✅ |
| N2 | **定义 / 结构 / 归纳类型** | `camelCase`（Lean 与 mathlib 惯例：`WeightSemantics`、`netAct`） | ✅ |
| N3 | **混用禁止** | 同一文件内，定理名一律 snake、定义名一律 camel；不得出现 camelCase 的定理或 snake_case 的结构 | ✅ |
| N4 | **撇号 `'` 禁用**（**例外**见 §1.4） | 用语义化后缀（`_strict` / `_alt` / `_of_lt`）代替 | ✅ |
| N5 | **结论文必须限定范围** | 名字不得比证明更强：`_exact` 只在真能给出「⟺」时用；`_sound` 只在真能给出可靠性时用 | ⚠️ 半机检（I5 查跨层声称，语义强弱需人判） |
| N6 | **禁止脚手架名进公开表面** | `_aux`、`_tmp`、`_test`、`_probe`、`_example` 不出现在导出声明里 | ✅ |
| N7 | **空位名** | `<域>.<对象>.<性质>`，如 `core.repair.atomic` | ✅（I6 已查） |
| N8 | **模块名** | `Lattice.<层>.<域>.<模块>`；文件名与模块名逐段对应 | ✅ |

### 1.2 为什么禁撇号（N4）

三个具体理由，不是审美：

1. **无法检索**：`grep "extractLayer'"` 在不同 shell 里要不同转义，`'` 在 PowerShell 里
   是字符串定界符。本仓的审计脚本已经因为这一点出过错。
2. **无法进表格**：Markdown 表格里 `'` 与反引号混用会破格式，`archive/CORRECTIONS.md`
   的 5,696 行表格就是例子。
3. **它掩盖语义**：`progress'` 与 `progress` 的区别（更强的假设？不同的域？）名字里
   一个字符都没说。改名成本是每个 1 行，收益是每次检索都省一次猜。

### 1.3 现状与迁移

| 指标 | 实测 | 目标 |
|:--|--:|:--|
| 内核声明总数 | 10,105 | — |
| 撇号名 | **60**（`Core` 2 / `Lib` 58） | **0** |
| camelCase 定理 | **70** | **0** |
| camelCase 定义 | **1,778** | 保留（符合 N2） |

**迁移顺序**（每批都必须 `lake build` + `gate.py` 绿）：

1. **禁新增**：门禁加 advisory——新文件中出现 N3/N4/N6 违规即报告；
2. **撇号收敛**：60 个，逐文件改名（`progress'` → `progress_strict`，
   `extractLayer'` → `extractLayer_alt`，**名必须说明差在哪**）；
3. **camelCase 定理收敛**：70 个；
4. **camelCase 定义**：**不改**——见 N2，Lean 惯例就是 camelCase。

> 第 4 条与第 3 条看似矛盾，其实是同一原则的两个方向：**约定按「种类」分，
> 不按「文件」分**。定理是命题，mathlib 里全是 snake；定义是项，mathlib 里全是 camel。

### 1.4 N4 的例外：语言层带撇号的标识符

`'` 在 Lean 里是合法标识符字符，且**有时承载语言设计含义**：

| 用法 | 例子 | 处置 |
|:--|:--|:--|
| **关键字变体** | `while'`（`Cmd` 的「已求值守卫」构造子，`Lib/Compiler/RealBigStepSmallStep.lean:95`） | **保留**。它与关键字 `while` 对应；改名会连带改 `BigStep` 构造子，属语义变更而非规范整理 |
| 用户定义的**定理 / 引理 / def** | `progress'`、`extractLayer'`、`rowEditCexW'` | **禁用**，必须改 |

判据：**撇号是否承载语言层含义**。`while'` 里它表示「这是关键字 `while` 的变体」，
是设计的一部分；`progress'` 里它只是「后来又写了一个」的记号，不承载语义。

### 1.5 撇号名的三种情形与处置（实测分类，60 个）

| 情形 | 判据 | 处置 | 实测例 |
|:--|:--|:--|:--|
| **(a) 真重复** | 同文件内已有同名同义的 base | **删除**重复者 | `softmax_fin_one_eq_one'` 与 `softmax_fin_one_eq_one` **逐字相同** |
| **(b) 语义变体** | 有 base，但签名确有差异 | 按**实际差异**改名 | `sel_tight_state_eq'` 把假设 `ρ ≠ 1` 换成 `0 ≤ ρ` + `ρ < 1` → `_of_bounded`；`zoh_bridge_mul'` 是 `zohGain * A` 而 base 是 `A * zohGain` → `_comm` |
| **(c) 无 base 的孤名** | 文件内不存在同名 base | 直接去撇号 | `trace_sub'`、`geom_sum_eq'`、`sum_range_sub_id'` |

**禁止的做法**：机械地把 `'` 换成 `_prime` 或 `_v2`——那只是把「不知道差在哪」
换成了另一种写法，规范要解决的是「读者必须靠猜」。

---

## 2. 文件划分

### 2.1 规则

| # | 规则 | 可机检 |
|--:|:--|:--|
| F1 | 单文件 **≤ 500 行** 且 **≤ 60 个声明** | ✅ |
| F2 | 超过则按**主题**拆分，文件名必须说明主题 | ⚠️ 半机检（行数可查，主题质量需人判） |
| F3 | **拆分不改声明名**：`import` 路径变，全限定名保持不变 | ✅（改名会让下游全断，构建即报错） |
| F4 | 一个文件一个关切；聚合器（`Lattice/Lib/<Topic>.lean`）只 import，不声明 | ✅ |
| F5 | 探针与临时文件**不得**进 `Lattice/`（`.gitignore` 已有 `Lattice/Core/Probe.lean`） | ✅ |

### 2.2 现状

**超 60 声明的文件（8 个）**：

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

**拆分方法（必须遵守）**：
1. 先按 §1 规范**改好名**，再拆——否则拆完要改两遍；
2. 拆出的每个文件必须有**自己的文件头**说明它承载哪个子主题；
3. 拆分提交与改名提交**分开**，便于二分定位构建失败；
4. 拆完立刻跑全量 `lake build`——F3 的违反只会在构建时暴露。

**为什么不当场就拆**：拆文件改 import 路径，若同时还有语义改动，
构建失败时无法判断是拆错了还是证错了。所以拆文件排在语义稳定之后（规划 P12）。

---

## 2b. `Lib` 内部不设层序（已登记的事实）

`I4` 强制 `Core < Lift < Lib`，**但 `Lib` 内部任意 import 都合法**。这是已知且**有意保留**的状态，
不是遗漏。它有两个可观察的后果，读者需要知道：

| 现象 | 实测 | 含义 |
|:--|:--|:--|
| `Lib/Architectures` 位于 `Lib/LinearAlgebra` **下方** | `RealSVD`、`RealEckartYoung` 等都 import `Architectures.RealMatrixNorm` | 目录名「Architectures」暗示应用层，实际是**数值基础设施** |
| `Lib/Lift` 与 `Lattice/Lift` 层**无关** | `Lib/Lift` 是 `Lib` 里的一个主题 | 名字雷同，容易误读成层 |

**为什么不立即加层序**：`Lib` 有 588 个文件，一个内部序需要先测出真实依赖图，
且可能与 `I3`（定义唯一）、`I5`（端到端）冲突。在依赖图测出来之前定规则，
只会定出一条与代码不符的规则——这正是本仓反复记录的那类失败。

**已考虑的三个选项**（`STATE-2026-10.md` §5.4）：

| 选项 | 做法 | 代价 |
|:--|:--|:--|
| **(a) 登记不约束** | 本节的写法：把事实写下来，不假装修好了 | **S** |
| (b) 重命名主题 | `Architectures` → `Numerics`；`Lib/Lift` → `Lib/ChainLift` | M（87 条 import 路径） |
| (c) 建立 `Lib` 内层序 | 主题分级 + `I4` 检查 | L（需先测依赖图） |

当前采取 (a)。若将来做 (b) 或 (c)，本节应随之更新而不是留下两条互相矛盾的说明。

---

## 3. 证明注释

### 3.1 规则

每条**导出**的定理/引理，其 docstring 必须包含四项（缺一项即不合规）：

```
/-- <一句话命题>：用数学语言写清「什么条件下，什么成立」。

<为何成立>：一两句指出机制（Fermat 一阶条件 / 平方非负 / 单调性 / 归纳…）。

<依赖>：用到的关键引理（可带模块名）。
<边界>：假设不可去掉的理由，或「本命题在 X 情形下为假」。
-/
```

| # | 规则 | 可机检 |
|--:|:--|:--|
| D1 | 四项齐全（命题 / 机制 / 依赖 / 边界） | ⚠️ 半机检（可查有无 `边界`/`Limit` 标记，内容需人判） |
| D2 | 有非平凡假设时，**必须**说明它为什么不能省 | ⚠️ 同上 |
| D3 | 数字必须注明**口径与时点**（`683 olean（2026-10-25，本机）`），否则不写 | ✅（可扫裸数字） |
| D4 | 不用「基本上 / 大约 / 应该」这类不可核验的修饰 | ⚠️ 可扫词表 |
| D5 | 已证否的命题**不得**以「未证」表述——写「已证否」并给反例定理名 | ⚠️ 人判 |

### 3.2 优先修复群

**106 个名字声称结论性的定理**（`_exact` / `_sound` / `_converges` / `end_to_end` /
`_correct` / `_complete`）是第一批：它们最容易被误读成「整条链已经通了」。
实测已知的两处正是这一群：

- `Geo/Pipeline.token_to_weight` 的 `_hdec` 未使用（G1 因此降级）；
- `Lib/Chain/RealEndToEnd.e2e_sound` 的证明体逐字是更弱的定理。

---

## 4. 证明链记录

### 4.1 现有生成物与缺口

`gov/chain.py` 与 `gov/proof_chain_geo.py` 生成的是**引用图**（1.36 MB），
它回答「谁 import 谁」，**不回答**「这一跳由谁承担、前提由谁供给、前提是否承重」。

### 4.2 `PROOF-CHAIN-RUNG.md` 的格式（新建，规划 P13）

按四跳组织，每跳一节，**每节必须回答四问**：

```
## 跳 L<k> → L<k+1>：<这一跳做什么>

1. 义务（Obligation）：<一句精确的 Lean 命题，写成签名>
2. 承担者（Carrier）：<定理全名> 或 <「无人承担」+ 对应 slot 名>
3. 前提供给（Warrant）：<每个前提由哪条定理供给，递归到底>
4. 承重性（Load-bearing）：<去掉每个前提后，命题是否仍成立？>
   — 附**实测**：在暂存文件里删掉该前提，`lake env lean` 是否通过。
```

**第 4 问是本文件与现有生成物的根本区别**：它记录**否证实验**，不只是引用关系。
一个前提若删掉后命题仍通过，就必须在文档里写明「该前提不承重」，并说明它是
装饰还是给读者的约束。

### 4.3 已实测的否证结论（本节随文档一起维护）

| 命题 | 被删的前提 | 实测 |
|:--|:--|:--|
| `Geo/Pipeline.token_to_weight` | `_hdec : decodePayload n rs = some c`，及 `rs` 参数 | **仍通过**；Lean 报 `unused variable 'h'` |

---

## 5. 术语表（学术化，避免口语）

| 不用 | 用 | 理由 |
|:--|:--|:--|
| 「要点」「注意」「白捡」 | 「接口」「契约」「边界」「附带结论」 | 修辞不增加信息 |
| 「基本上成立」 | 「在 <条件> 下成立；<条件> 之外有反例」 | 可核验 |
| 「已经能用了」 | 「<定理名> 已证；<未证项> 登记为 slot <名>」 | 可追溯 |
| 「完成」 | 「<编号> 已达成，验收见 <命令与输出>」 | 可复现 |
| 「这是难点」 | 「这是唯一未解决的技术障碍；已尝试 <方法>，失败原因 <原因>」 | 可推进 |

---

## 6. 数字口径（本文件所有计数）

- **声明计数**：先剥注释（嵌套感知 `/- -/` 与 `--`），再按行首匹配
  `theorem|lemma|def|abbrev`（可带 `private`/`protected`/`noncomputable`/`@[...]`）。
  **不剥注释会误报**——实测第一次统计把 docstring 里的 "theorem that consumes it"
  当成了声明。
- **行数**：`[System.IO.File]::ReadAllLines($f, UTF8-no-BOM).Count`。
  **不用 `Get-Content`**：本仓文件含中文与混合换行，`Get-Content` 会少报行数。
- 脚本：`agent-tmp/naming_census.py`、`agent-tmp/conventions_inventory.py`。

---

## 7. 执行状况（**实测，第 33 轮重新测量**）

本节此前记录的数字**全部已经漂移**：二十多轮里不断新增文件，而没人重测。
下表是 `agent-tmp/measure_conventions.py` 的实测结果，任何人可以重跑。

| 规则 | 本轮实测 | 上一版记录 | 变化 | 状态 |
|:--|--:|--:|:--|:--|
| N4 撇号 | **3** | 3 | 持平 | ✅ 全在 §1.4 例外内 |
| N3 camelCase 定理 | **36**（35 真违规 + 1 别名） | 70 | **-34** | ⚠️ 未清理 |
| N3 camelCase 定义 | **1,959** | 1,778 | +181 | ✅ N2 允许 |
| F1 超 60 声明 | **10** | 8 | +2 | ⚠️ 未拆分 |

### 7.1 本轮修掉的一条

`abs_coord_sub_le_rho'`（`Geo/RhoMetric.lean`）**是我在第 9 轮自己写下的**，
违反 N4 且不在 §1.4 例外清单里。已改名为 `abs_coord_sub_le_rho_singlePoint`——
后缀说明了它与 `rho_le_iff` 的区别（它是单点形式）。

⇒ 违规数 4 → 3，现在全部是上游强制的例外。

### 7.2 N3 camelCase 定理：36 条的真实性质（**此处修正了一次错误判断**）

本节初稿写「36 条里大部分是正则误判，指向类型别名」。**这个判断是错的。**
实测（`agent-tmp/verify_conv_claims.py`，逐条看定理体）：

| 分类 | 数量 |
|:--|--:|
| 真正的 camelCase 定理 | **35** |
| 别名（`:= 类型名`） | **1**（`GeneralizationBound`） |

**35 条是真实的命名违规**，不是误判。典型例子：

| 名字 | 文件 | 实际是什么 |
|:--|:--|:--|
| `IdempotentOn` | `Core/Idempotent.lean` | 幂等性的定理 |
| `GeoExpr` / `GeoConstraint` | `Geo/Shape.lean` | 结构性定理（与类型同名，但是定理） |
| `twoHopMsg` | `Lib/Architectures/RealGNN.lean` | 图消息传递的定理 |
| `klChainRule` | `Lib/InfoTheory/RealKLChainRule.lean` | KL 链式法则 |
| `firstOrderMAML` | `Lib/LearningTheory/RealMAML.lean` | MAML 一阶展开 |

**为什么这条修正重要**：我在写这一段时只抽查了前 10 个，看到 `GeoExpr` 这类名字
就推断"大部分是别名"。实际只有 1 个。**在一个讨论「如何验证」的文档里，
凭抽样下结论是最不应该犯的错。**

**当前处置**：这 35 条**未改名**。改名需要逐条判断命名意图（`IdempotentOn` 是
幂等性的什么性质？），是 P11 之后的工作，不在本轮范围。已如实记录数量与样例。

### 7.3 F1 超 60 声明：10 个文件

| 文件 | 声明数 |
|:--|--:|
| `Lib/Chain/RealN2AxiomDischargeJia.lean` | 168 |
| `Lib/Chain/RealLv00Solver.lean` | 127 |
| `Lib/Compiler/RealMutualRecursion.lean` | 89 |
| `Lib/Lift/RealNonlinearFidelity.lean` | 86 |
| `Lib/Chain/RealLv00AxiomDischargePerPackage.lean` | 84 |
| `Lib/Quantization/RealIEEE754.lean` | 71 |
| `Lib/Chain/RealLv00LinearAlgebra.lean` | 66 |
| `Lib/Chain/RealNumericChainOrder.lean` | 66 |
| `Lib/LearningTheory/RealCausalDoCalculus.lean` | 64 |
| `Lib/Chain/RealLv00GeometryDifferential.lean` | 62 |

**全部在 `Lib`，零个在 `Core`/`Lift`/`Geo`**——承重层没有超大文件。

### 7.4 D1 注释四项齐全：仍**未测**

规范要求了四项（命题 / 机制 / 依赖 / 边界）。把「是否四项齐全」变成可判定规则需要
定义格式，那会**规定**注释怎么写而不是**检查**它写得好不好。所以这一项**保持未测**，
并记录理由，而不是假装测过。

### 7.5 测量方法（可重跑）

```python
# agent-tmp/measure_conventions.py
# N4: 声明名含撇号
# N3: 定理名无下划线且有小写->大写转换
# F1: 单文件声明数 > 60
# 排除 Lattice/Reference/
```

**每次数字变化都应重跑**，并在本表记录。这是本节的自我维护要求。
