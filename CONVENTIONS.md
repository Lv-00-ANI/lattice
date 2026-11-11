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

  #   对象   规则   可机检  
 --: :-- :-- :-- 
  N1   **定理 / 引理**   `snake_case`；**性质写在最后**（`sq_penalty_exact`，不是 `exact_penalty`）   ✅  
  N2   **定义 / 结构 / 归纳类型**   `camelCase`（Lean 与 mathlib 惯例：`WeightSemantics`、`netAct`）   ✅  
  N3   **混用禁止**   同一文件内，定理名一律 snake、定义名一律 camel；不得出现 camelCase 的定理或 snake_case 的结构   ✅  
  N4   **撇号 `'` 禁用**（**例外**见 §1.4）   用语义化后缀（`_strict` / `_alt` / `_of_lt`）代替   ✅  
  N5   **结论文必须限定范围**   名字不得比证明更强：`_exact` 只在真能给出「⟺」时用；`_sound` 只在真能给出可靠性时用   ⚠️ 半机检（I5 查跨层声称，语义强弱需人判）  
  N6   **禁止脚手架名进公开表面**   `_aux`、`_tmp`、`_test`、`_probe`、`_example` 不出现在导出声明里   ✅  
  N7   **空位名**   `<域>.<对象>.<性质>`，如 `core.repair.atomic`   ✅（I6 已查）  
  N8   **模块名**   `Lattice.<层>.<域>.<模块>`；文件名与模块名逐段对应   ✅  

### 1.2 为什么禁撇号（N4）

三个具体理由，不是审美：

1. **无法检索**：`grep "extractLayer'"` 在不同 shell 里要不同转义，`'` 在 PowerShell 里
   是字符串定界符。本仓的审计脚本已经因为这一点出过错。
2. **无法进表格**：Markdown 表格里 `'` 与反引号混用会破格式，`archive/CORRECTIONS.md`
   的 5,696 行表格就是例子。
3. **它掩盖语义**：`progress'` 与 `progress` 的区别（更强的假设？不同的域？）名字里
   一个字符都没说。改名成本是每个 1 行，收益是每次检索都省一次猜。

### 1.3 现状与迁移

| 指标 | 实测（内核） | 目标 |
|:--|--:|:--|
| 内核声明总数 | 13107 | — |
| 撇号名 | **3** | **0**（三个全部属 §1.4 例外） |
| camelCase 定理 | **4**（全部豁免，见 §7.6） | — |
| camelCase 定义 | **1,747** | 保留（符合 N2） |

> **本节此前的数字是错的（第 55 轮修正）**：撇号写 **60**、camelCase 定理写 **70**，
> 那是**旧库**的数字，迁移后从未复测。`§7.4` 独立测量给出 3（现为 4），
> **同一份文档里两个数相差 20 倍**，持续了数十轮。现统一采用本节实测值，
> 与 `§7` 一致；`gov/repro/naming_census.py` 可重跑。
>
> **测量口径记录（第 55 轮，两次出错）**：修正本节的数字时我先后犯了两个口径错误——
> 先用了「含大写字母」判据（得 3,475），再用「遍历仓库根」扫到了 `.lake/packages/mathlib`
> 里的上游 Mathlib 源码。**正确判据是本节 §7.5 写的「无下划线 且 有小写→大写转换」，
> 正确范围是 `Lattice/`（排除 `Reference/` 与 `.lake/`）。** 用正确口径得 36。
> 两次都靠与文档自述的判据对照发现，不是靠推理。
> `gov/repro/naming_census.py` 已加 `.lake/` 排除。

> 第 4 个撇号 `exists_delta_of_eps'`（`Lift/VerifierRate.lean`）是**第 50 轮我自己加的**，
> 使「3 个全属例外」的说法失效——这是本轮如实记录的事实，不是历史遗留。

**迁移顺序**（每批都必须 `lake build` + `gate.py` 绿）：

1. **禁新增**：门禁加 advisory——新文件中出现 N3/N4/N6 违规即报告；
2. **撇号收敛**：3 个，逐文件改名（`while'` → `while_strict`，
   `StrictMono'` → `StrictMono_strict`，`exists_delta_of_eps'` → `exists_delta_of_eps_ge`，
   **名必须说明差在哪**）；
3. **camelCase 定理收敛**：**已完成（15 → 4，余 4 条按 §7.6 豁免）**；
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
| F1 | 单文件 **≤ 500 行** 且 **≤ 60 个声明** | ✅ 两个维度分开测，见 §2.2 |
| F2 | 超过则按**主题**拆分，文件名必须说明主题 | ⚠️ 半机检（行数可查，主题质量需人判） |
| F3 | **拆分不改声明名**：`import` 路径变，全限定名保持不变 | ✅（改名会让下游全断，构建即报错） |
| F4 | 一个文件一个关切；聚合器（`Lattice/Lib/<Topic>.lean`）只 import，不声明 | ✅ |
| F5 | 探针与临时文件**不得**进 `Lattice/`（`.gitignore` 用 `*Probe.lean` 兜住全部生成探针） | ✅ |

### 2.2 现状（两个维度分开，因为它们的结论不同）

| 维度 | 内核实测 | 判定 |
|:--|--:|:--|
| **声明数 > 60** | **6 个**：`Lib` 层 5 个 + `Domains/Constraints/PenaltyLossDerivative.lean`（61） | 接近达标；`Lib` 的 5 个有结构障碍，`PenaltyLossDerivative` 是第 128–147 轮逐支累积的结果 |
| **行数 > 500** | **92 个**（排除模块文档块后仍 87 个） | **未达标，如实记录** |

**行数维度为什么没拆。** 我测过「行数是不是被模块文档膨胀的」这个假设：**不是**。
把每个文件开头的模块文档块整段去掉后，超预算的从 92 个只降到 87 个；
最大的几个（`Lib/Chain/RealLv00Solver.lean` 1317 行代码 / 1477 行总长，
`Lib/Chain/RealN2AxiomDischargeJia.lean` 1312 行）本来就是长文件，不是注释堆出来的。

**所以审计提出的「500 行 vs 只测声明的冲突」不成立**：这些文件同时都超。
它们是真的超预算，不是被文档推过线的。

**本轮仍然不拆**，理由是拆的代价与收益不成比例，而且这个决定要能被检验：

- 87 个文件分布在 `Lib` 的 12 个主题目录里，机械拆分会产生大量一行转发模块
  （`Foo.lean` 只 `import Foo.Part1, Foo.Part2`），**把「一个文件一个关切」换成「一个关切两个文件」**；
- F3 保证拆分不改声明名，所以拆分**不改变任何定理**——**它是组织问题，不是正确性问题**；
- 真正该拆的是**声明数超 60** 的那 6 个（`Lib` 层 5 个 + `PenaltyLossDerivative` 1 个），那一维已接近达标，且能指出具体结构障碍。

**⇒ 我选择如实记录未达标，而不是做一次看起来达标的机械重排。**
一个把 87 个文件各切一刀的提交会让这张表变绿，而库的可读性不会变好。

具体清单与实测声明数**只在 `§7.3` 出现一次**（`gov/repro/measure_conventions.py` 可重跑）。

> **第 55 轮修正**：本节此前自己列了一张 8 个文件的表，声明数（165/104/87）也是旧的，
> 而 `§7.3` 列出 10 个、声明数（168/131/92）与树一致。
> **同一份文档两张表，数字互相矛盾，持续了数十轮。**
>
> 根因不是数字抄错，而是**同一测量被写了两遍**。现在本节不再重复那张表：
> 超限文件数在这里只说明「10 个、全在 Lib」，明细单一来源在 §7.3。

### 3.1 规则

每条**导出**的定理/引理，其 docstring 必须包含四项（缺一项即不合规）：

```
/-- <一句话命题>：用数学语言写清「什么条件下，什么成立」。

<为何成立>：一两句指出机制（Fermat 一阶条件 / 平方非负 / 单调性 / 归纳…）。

<依赖>：用到的关键引理（可带模块名）。
<边界>：假设不可去掉的理由，或「本命题在 X 情形下为假」。
-/
```

  #   规则   可机检  
 --: :-- :-- 
  D1   四项齐全（命题 / 机制 / 依赖 / 边界）   ⚠️ 半机检（可查有无 `边界`/`Limit` 标记，内容需人判）  
  D2   有非平凡假设时，**必须**说明它为什么不能省   ⚠️ 同上  
  D3   数字必须注明**口径与时点**（`683 olean（2026-10-25，本机）`），否则不写   ✅（可扫裸数字）  
  D4   不用「基本上 / 大约 / 应该」这类不可核验的修饰   ⚠️ 可扫词表  
  D5   已证否的命题**不得**以「未证」表述——写「已证否」并给反例定理名   ⚠️ 人判  

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

## 6. 数字口径与来源（**第 39 轮重建**）

本文件的每个数字都必须能回答两个问题：**怎么算的**、**谁保证它不会漂**。
下表由 `agent-tmp/derive_number_sources.py` 从检查器本身反推得出，不是凭记忆填写。

### 6.1 有守卫的数字（能失败）

| 数字 | 出现在 | 守卫 | 能失败 |
|:--|:--|:--|:--|
| Core / Lift / Geo / Lib 模块数 | `README` 分层图 | `audit_counts.py`（门禁） | ✅ |
| 检查器注册数 | `README` | `audit_counts.py`（门禁） | ✅ |
| A/B/C 三类文件数与声明数 | `REPAIR-CENSUS` | `check_repair_census.py`（门禁） | ✅ |
| 否证总数与层分布 | `REFUTATION-CENSUS` | `check_refutation_census.py`（门禁） | ✅ |
| 12 条链层定理的引用数 | `ROADMAP-v9 §1`、`USAGE §1` | `check_chain_deps.py`（门禁） | ✅ |
| 欠账数 | `Slots.fullRegistry` | `example … := by decide` | ✅ |
| 证明链实例普查 | `PROOF-CHAIN-RUNG` | `check_proof_chain_rung.py` | ✅ |

### 6.2 **没有守卫的数字**（本轮实测）

| 文档 | 多位数个数 | 守卫 |
|:--|--:|:--|
| `README` | **78** | 仅上表 2 项受检，其余无 |
| `CONVENTIONS` | 64 | 无 |
| `REPAIR-CENSUS` | 33 | 6 项受检，其余无 |
| `REFUTATION-CENSUS` | 17 | 6 项受检，其余无 |
| `USAGE` | 2 | 无 |

⇒ **`README` 的 78 个多位数里，只有分层图那 5 个受检。**
这是一个事实，不是缺陷：大部分多位数是**日期、版本、轮次号**，不是需要守卫的计数。
但读者无法从文档本身分辨哪些是「受检的计数」、哪些只是"叙述里的数字"。

### 6.3 断言型检查器（**第 47 轮复测修正**，第 167 轮再修正）

> **此前本节写「`gov/` 下 27 个脚本里只有 3 个断言」。两处都错**：
> 实测 `gov/` 有 **141 个 `.py`**。
> 那个数字来自一次**只扫描了匹配某文档引用模式的文件**的统计——
> 与本仓已记录 7 次的「测量口径错误」同类。此处更正。
>
> **「其中 N 个含 `EXPECTED`」不再写成数字**：它从未被任何守卫校验，而数字一旦不被校验就会漂移
> （这正是第 165–166 轮 census 漂移的同一形状）。目前的准确说法是：
> **只有 `gov/check_chain_deps.py` 还持有 `EXPECTED`**；两个 census 守卫改为从
> `REPAIR/REFUTATION-CENSUS.md` 读数字（见 §6.3.1），于是文档漂移会让守卫红，而不是让它继续绿。

| 断言型（含 `EXPECTED`） | 断言什么 |
|:--|:--|
| `check_repair_census.py` | A/B/C 三类的 6 个数 |
| `check_refutation_census.py` | 总数与 5 个层的分布 |
| `check_chain_deps.py` | 12 条定理的引用数 |
| `check_chain_table.py` | 六跳载体存在 |

其余脚本**报告**或**执行其他检查**，不以 `EXPECTED` 常量形式声明期望值。
（例如 `gate.py` 用 8 条不变量规则、`audit_counts.py` 用正则提取 README 中的数字——
它们**是判决性的**，只是不叫 `EXPECTED`。）

⇒ **「断言型」的正确判据不是「有没有 `EXPECTED`」，而是「能否以失败退出」。**
按后者统计见 §6.1：`verify_all` 的 94 项中 **68 项是门禁**。

### 6.4 数字分类（决定是否需要守卫）

| 类别 | 例子 | 需要守卫？ |
|:--|:--|:--|
| **结构性计数** | 模块数、定理数、欠账数 | ✅ 需要 |
| **普查计数** | 否证数、修复算子数 | ✅ 需要 |
| **叙述性数字** | 「第 35 轮」「2026-10」 | ❌ 不需要 |
| **历史记录** | `ROADMAP-v3`–`v10` 里的数字 | ❌ **不应更新**（描述当时的树） |

**最后一行是纪律**：历史规划文档里的数字描述的是**当时的代码树**。
更新它们等于篡改历史。它们不需要守卫，也**不应被"修正"**。

### 6.5 测量口径（可重跑）

```python
# gov/audit_counts.py           README 的 7 项计数
# gov/check_repair_census.py    REPAIR-CENSUS 的 6 项
# gov/check_refutation_census.py REFUTATION-CENSUS 的 6 项
# gov/check_chain_deps.py       12 条定理的依赖数
# 每个都支持 --self-test：植入错误期望，断言它会报错
```

**`--self-test` 不是可选项**：没人见过它失败的规则不算规则。

## 7. 执行状况（**实测，第 33 轮重新测量**）

本节此前记录的数字**全部已经漂移**：二十多轮里不断新增文件，而没人重测。
下表是 `agent-tmp/measure_conventions.py` 的实测结果，任何人可以重跑。

| 规则 | 本轮实测 | 上一版记录 | 变化 | 状态 |
|:--|--:|--:|--:|:--|
| N4 撇号 | **3** | 3 | 持平 | ✅ 全在 §1.4 例外内 |
| N3 camelCase 定理 | **4**（全部豁免） | 36 | **-32** | ✅ 已收敛 |
| N3 camelCase 定义 | **1,747** | 1,993 | -212 | ✅ N2 允许 |
| F1 超 60 声明 | **7** | 10 | **-2** | ⚠️ 余 8 个有结构障碍 |

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

### 7.3 F1 超 60 声明：8 个文件

> **第 63 轮（批量）：10 → 5。** 本批拆了四个，各部分的声明数均降到 43 以内：
>
>   文件   原   拆成  
>  :-- --: :-- 
>   `Lib/Chain/RealLv00AxiomDischargePerPackage.lean`   84   14/21/21/28  
>   `Lib/Compiler/RealMutualRecursion.lean`   92   27/25/37  
>   `Lib/Lift/RealNonlinearFidelity.lean`   86   23/43/20  
>   `Lib/Chain/RealNumericChainOrder.lean`   66   21/22/23  
>
> **每次拆分都核对声明数不变**（84→84、92→92、86→86、66→66，零丢失）。
>
> #### 一次失败的尝试，已回滚
>
> `Lib/LearningTheory/RealCausalDoCalculus.lean` 按节拆成 A/B 后**构建失败**：
> `B` 引用 `FinSCM.pU`、`Adj`、`IsPath`，而这些是**在 `namespace FinSCM` 里后续定义**的，
> 位于原文件的别的节。
>
> ⇒ **教训：`structure S` 的定义与 `namespace S` 里的扩展必须留在同一文件。**
> 按行号切分会把它们分开，而分节边界**跨过了命名空间**。
> 已回滚，文件保持原样，本轮的拆分脚本因此需要一条新的前置检查：
> **切分点不得落在 `namespace X` 与 `structure X` 之间。**
>
> #### 四个不能按节拆的（不是欠账，是结构事实）
>
>   文件   原因  
>  :-- :-- 
>   `Lib/Chain/RealN2AxiomDischargeJia.lean`   单节 60 条——按节拆仍留下一个 60 条的  
>   `Lib/Chain/RealLv00Solver.lean`   4 节，其中一节 72 条  
>   `Lib/Chain/RealLv00LinearAlgebra.lean`   仅 2 节（14/21），过粗  
>   `Lib/Chain/RealLv00GeometryDifferential.lean`   **零分节**——发明边界比不拆更糟  
>
> 这四个若要拆，需要**先补内部结构**（人为的 `/-! ## ... -/` 分节），那是另一类工作。


> **第 62 轮进度：10 → 9。** `Lib/Quantization/RealIEEE754.lean`（637 行、71 声明）
> 按它**自己的十个语义分节**拆成 `RealIEEE754/{Basic,Overflow,BitWidth,Compat}.lean`
> 加一个 umbrella。拆分前测了各节之间的依赖顺序，拆分后**核对声明数 71 → 71，零丢失**。
> 架构级改动走分支 `arch/split-ieee754` 后合回 master。
>
> **可复用的流程**（其余 9 个照此办理）：
> ① 数语义分节；② 测分节间依赖顺序；③ 依顺序拆；④ **核对声明数不变**；⑤ 构建；⑥ 合并。
>
> 拆分**不减少工作量**，只重新分配：模块数 +4，Lib 层 592 → 592。


| 文件 | 声明数 |
|:--|--:|
| `Lib/Chain/RealN2AxiomDischargeJia.lean` | 168 |
| `Lib/Chain/RealLv00Solver.lean` | 131 |
| `Lib/Compiler/RealMutualRecursion.lean` | 92 |
| `Lib/Lift/RealNonlinearFidelity.lean` | 86 |
| `Lib/Chain/RealLv00AxiomDischargePerPackage.lean` | 84 |
| `Lib/Chain/RealLv00LinearAlgebra.lean` | 66 |
| `Lib/Chain/RealNumericChainOrder.lean` | 66 |
| `Lib/LearningTheory/RealCausalDoCalculus.lean` | 64 |
| `Lib/Chain/RealLv00GeometryDifferential.lean` | 62 |

**全部在 `Lib`，零个在 `Core`/`Lift`/`Geo`**——承重层没有超大文件。

### 7.4 D1 注释四项齐全：仍**未测**

规范要求了四项（命题 / 机制 / 依赖 / 边界）。把「是否四项齐全」变成可判定规则需要
定义格式，那会**规定**注释怎么写而不是**检查**它写得好不好。所以这一项**保持未测**，
并记录理由，而不是假装测过。

### 7.6 camelCase 定理：判据修正与豁免（第 61 轮）

**此前本节记 35–36 条，实测 15 条，现为 4 条。** 三个数字的差来自**判据**，不是改名进度：

| 判据 | 数量 | 问题 |
|:--|--:|:--|
| 不按 `.` 分割声明名 | 36 | **`GeoExpr.beqShape_eq` 里的 camelCase 是结构名**，按 N2 正确 |
| 按 `.` 分割，只看末段 | **15** | 正确口径 |
| 15 条中扣除 §7.6 豁免 | **4** | 当前状态 |

#### 豁免规则

以下四条的 camelCase 是 **Mathlib 自己的惯例**——结构的派生事实写作
`Structure.camelCase`。改名会**破坏与 Mathlib 的一致性**，使熟悉上游的人更难读：

| 声明 | 文件 |
|:--|:--|
| `IsStrictLocalMin.toIsLocalMin` | `Lib/Convex/RealKKTSecondOrder.lean` |
| `IsStrictLocalMax.toIsLocalMax` | `Lib/Optim/RealSaddlePoint.lean` |
| `IsClosedExtent.iInter` | `Lib/FCA/RealFCACompleteLattice.lean` |
| `IsClosedExtent.sInf` | `Lib/FCA/RealFCACompleteLattice.lean` |

⇒ **这四条不是欠账，是按规则的豁免。** 下一个审阅者不应再把它们报成待修项。

#### 已改名的 11 条

`twoHopMsg` → `two_hop_msg`、`BetaRedStar.appL/appR/lamBody` → `app_l/app_r/lam_body`、
`editSeqComm` → `edit_seq_comm`、`borelOfTopology` → `borel_of_topology`、
`liftBeta` → `lift_beta`、`klChainRule` → `kl_chain_rule`、
`firstOrderMAML` → `first_order_maml`、`lowRankReparam` → `low_rank_reparam`、
`bfgsParaboloid` → `bfgs_paraboloid`。

**13 个文件被修改，残留引用 0，`lake build` 通过。**

### 7.5 测量方法（可重跑）

```python
# agent-tmp/measure_conventions.py
# N4: 声明名含撇号
# N3: 定理名无下划线且有小写->大写转换
# F1: 单文件声明数 > 60
# 排除 Lattice/Reference/
```

**每次数字变化都应重跑**，并在本表记录。这是本节的自我维护要求。
