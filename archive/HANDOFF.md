# LATTICE 状态交接（轮 40/40 收尾）

> **本文档由 coordinator 在**最后一轮**写下，用于让后续任何接手者（人或代理）无需重建上下文即可继续。**
> 注意 **所有数字均为本文档写作时的实测值**，并附**复现命令**。

---

> ## 注意 **部分作废：§二 / §四 / §七 是【历史快照】，不得作为当前状态读取**（**B409**）
>
> **写作时点**：轮 40/40 收尾（约 **B57** 时代）。**复核时点**：HEAD `36ec3f4`（**B408**）。
> **差距**：约 **350 条登记**、**约 90 个模块**。
>
> **具体失效点**：
> - **§二「实测状态」**的数字整体过期（roots `418 → 511`；无 olean `25 → 0`；
>   `CORRECTIONS` `B1–B57 → B1–B408`；`scripts` 的「31」口径不明，不作数）；
> - 要点**§二末行与 §七第 3 条声称「26 陈旧 + 25 无 olean = 真实的覆盖缺口」** ——
>   **实测为 0 + 0**（内容比对 `python scripts/olean_freshness.py` → `SOURCE CHANGED: 0`）。
>   注意 该句把一个**已不存在**的缺口说成「该模块的声称当前没有内核背书」；
> - **§四「未完成项」是一份【已结束波次】的快照**：§4.1 的 8 个在飞代理**全部已结束**；
>   §4.3-1（B53 链式可达性）与 §4.3-3（`RealGelfand` 孤儿）**均已闭合**。
>
> **仍然有效**（**不要连同上面一起忽略**）：
> - §一 项目定位；§三 本波次产出的**方法论**；要点**§五 操作纪律**（构建走锁 / 零锁自检 / 环境坑 / 归属纪律）；
> - 要点**§六 方法论速查表** —— 这 10 条**与轮次无关**，仍是本仓最有价值的可复用结论之一。
>
> **保留理由**：与 `lean/ROADMAP.md`（**B402** 加 DEPRECATED 横幅）同理 ——
> 它记录了**当时的**缺口分级、成本估计与判据来源，**仍有参考价值**。**但历史不代表当前。**
>
> 要点**当前状态的权威来源**（不要读本文档的 §二）：
> `lean/PROCESS.md §10`（每轮更新）· `lean/STATS.md`（由 `scripts/verify.ps1` **自动重生成**）·
> `python scripts/check-corrections-count.py` · `python scripts/olean_freshness.py`。
>
> **B581（2026-10-08）复核更新**：上述横幅系 `B409` 时点所加，其本身亦已过时。
> 当前 HEAD 为 `dca7f80`（**B582**）；本文档 `:56` 的「`scripts/` 31 个脚本」实测为 **115**（37 个 `.ps1` + 78 个 `.py`），
> `:57` 的「`doc/` 15 篇」实测为 **31**。**二者均须按当前树重测后方可引用。**

---

## 一、项目定位

**LATTICE** = 符号 ⇄ 权重**双向转换框架**的 **Lean 4 形式化**（理论层）。
注意 **当前阶段只要理论**（Lean 证明 + 诚实登记）；**C 工程管线属另一阶段，本轮不做**。

- **仓库**：`C:\Users\xingg\Desktop\agent\lattice`（私有 GitHub `level0000x/lattice`，分支 `main`）
- **Lean 工程**：`lattice\lean`，mathlib `4.14`（`leanprover/lean4:v4.14.0`），Lake 5.0.0

---

## 二、实测状态（复现命令见 §五）

| 指标 | 数值 |
|:--|--:|
| **roots（`lakefile.toml` 白名单）** | **418** |
| 成立 **新鲜 olean** | **349** |
| 注意 **陈旧 olean**（源新于产物） | **26** |
| 不成立 **无 olean**（从未编译成功） | **25** |
| **源码 `.lean`（非探针）** | ~428 |
| **`CORRECTIONS.md`** | **B1–B57** |
| **`STYLE.md`** | **266 条表格行** |
| **`scripts/`** | **31 个脚本** |
| `doc/` | 15 篇 |
| **`sorry`/`axiom`/`admit`/BOM** | **0 / 0 / 0 / 0** |

---

## 三、要点：本轮（v14）最重要的产出

### 3.1 新登记（B53–B57）

| 编号 | 内容 | 严重度 |
|:--|:--|:--|
| **B53** | 要点二级**19 条定理空洞**：`hxdom : ∀ z, c ≤ ‖z‖` 与 `hc : 0 < c` **矛盾**（`z := 0` 给 `c ≤ 0`） | **最高** |
| **B54** | 要点二级**方向契约冲突**：上界被当下界用（`RealMartingaleOptionalStopping` 引 `condexp_hoeffding`）；**同闭包内** `RealDoobInequality:141-143` 明说不可这么用 | **高** |
| **B55** | 死参数 `e0` 传染 **17 处调用** | 中 |
| **B56** | 谱半径归因错误 / `↔` 过强 / 同文件自相矛盾 / "完全一致"过度声称 / 同名双契约 | 中 |
| **B57** | 要点**负面结论**：26 个无 olean 模块**不共享单一成因** | 方法论 |

### 3.2 新工具（2 个）

| 脚本 | 作用 | 验证 |
|:--|:--|:--|
| **`check-unsatisfiable-hypotheses.ps1`** | 检测"`∀z` 范数下界 + 正性"矛盾对（**B53 的检测器**） | 成立 独立复现全部 19 例 |
| **`check-verification-claims.ps1`** | 检测"声称机器验证"但**该定理不存在** | 成立 植入缺陷验证 **0 → 1** |

### 3.3 工具修复（3 处）

| 脚本 | 修复 |
|:--|:--|
| **`check-structure.ps1`** | ① 原先**只查单行** doc-comment ⟹ **多行完全不可见**（**那恰是危险形态**）；② 修后产生**误报**（"找最近的 `-/`"撞上**成对引用**）⟹ 改为**跟踪嵌套深度**；③ 新增第 3 检查（**单个开定界符** vs 成对引用，advisory） |
| **`check-xref.ps1`** | 原先**只索引本仓库** ⟹ **所有 mathlib/core 引理都报 `ABSENT`**（首跑 **822** 条，**绝大多数误报**，**会诱导改正确的引用**）。**并入 mathlib + Lean core 后降到 381（−54%）** |
| **`lake-lock.ps1`** | 新增 **`-Expect`**：**入队↔开编的源码哈希核对**，不一致报 `SOURCE CHANGED SINCE ENQUEUE` 并 **exit 7** |
| **`verify.ps1`** | 新增 **`-StrictOlean`**：陈旧/缺失 olean 时 **exit 5**（原先**只报告不门禁**） |

---

## 四、注意 未完成项（**接手者从这里继续**）

### 4.1 注意 **本波次的 8 个代理（【历史快照】——全部已结束，无人"在飞"）**

| 代理 | 目标 | 最近已知 |
|:--|:--|:--|
| **F1** | `RealConversionStability` | **58 → 3**（第 6 次构建排队中） |
| **F4** | `RealProximalMoreau` | **12 → 7 → 9**（新暴露；构建 3 待出） |
| **F6** | `RealSparseCoding` | **59 → 45 → 27 → 22**（r3 已提交） |
| **F7** | `RealGaussianProcess`(31) + `RealVariationalBayes`(12) | 在飞 |
| **F9** | **11 个无覆盖模块** | 静态审计完成（**14 处 docstring 悬空引用**已确证），**等锁取诊断**。注意 **订正 B409：本条【仍开放】** —— 复核 `scripts\check-xref.ps1 -All` → **exit 5**，逐文件报 `ABSENT`（`RealDecisionTheory` 7 / `RealRoPEExtrapolationFailure` 7 / `RealSuperpositionCapacity` 7 …）。注意 但该工具**自称「审阅清单，不是判决」**，故这是**审阅项**而非已判定的缺陷 |
| **F10** | 要点**19 条空洞链**（B53） | 已派，修复中。注意 **订正 B409：空洞【已消除】，"修复中"已过期** —— 复核 `hreach` 已作为**可满足的显式前提**接入（`RealModelChain` 8 处 / `Hetero` 8 处 / `RealMixedAttention` 15 处代码引用），可满足性见证见 `RealModelChain.lean:57`。注意 **但这不是"证完"**：三文件**逐字自陈不证明真实块链满足 `hreach`**（见 §4.3-1 订正） |
| **G1** | `RealLv00Solver`（`mkROBDD` 变量序前提） | 走 (i) 补 `hv` 前提 |
| **G2** | 3 模块（2 个已归零） | `RealOODDetection` 余 5 条已修 |

### 4.2 已确认归零（**无需再动**）—— 注意 **本表 8 个模块经 B409 复核：源码在 / olean 在 / 在 roots，全部成立**

`RealLv00Compiler`(exit 0) · `RealLv00Systems`(15→0) · `RealSelectiveSSM` · `RealSSMContinuous` ·
**`RealConformalPrediction`**(14→0) · **`RealBanditTheory`**(4→0) ·
**`RealOverSmoothingSharp`**(13→0) · **`RealRegularizedMDP`**(4→0) ·
V1 三模块 · WP13 的 9 个 · Z1 的 6 个 · N4 的 3 个

### 4.3 结构性缺口（**长期项**）

1. 注意 **B53 的链式可达性条件**（要点三级）—— **订正 B409：原表述"需要新的归纳引理"【已过期】**：
   实测三文件**已把可达性【有意降级】为显式可满足前提 `hreach`**（`RealModelChain.lean:234/:283/:342`、`RealModelChainHetero.lean:171/:215/:292`、`RealMixedAttention.lean:623/:669/:773`），可满足性见证逐字见 `RealModelChain.lean:57`「`Fs` 取恒等链、`x = c • e₀` 时每个迭代都等于 `x`」。
   要点**真正的状态是**：三文件**逐字自陈【不证明】**真实块链满足 `hreach`（`RealModelChain.lean:58-60` / `RealModelChainHetero.lean:54-55` / `RealMixedAttention.lean:68`）
   ⟹ 要把它**证明**出来需「**块输出范数下界**」的实质分析，**属后续独立立项**。
   ⇒ **本条【仍开放】，但口径必须改写**（不是"缺一个引理"，是"有意降级为可满足前提"）；
2. **B55 的调用替换**（要点）：`RealConvergence` 是核心导出，**建议单独一批**。
   注意 **订正 B409**：原写「**17 处**」—— 实测**真实 `import` 行**口径下 `RealConvergence` 的
   roots 级 importer = **20**。注意 **两个口径可能不同**（B55 或指【符号级调用点】，
   本报告测的是【文件级 import 边】）⟹ **引用该数时必须标口径**；
3. ~~**`RealGelfand` 只被孤儿 `RealGelfandMathlib` import**（B56.1）⟹ 修归因时可能需补 `import`；~~
   注意 **订正 B409：本条【已闭合】，且原判据为假** —— 实测 `RealGelfand` 有**两个** roots 级 importer：
   `RealGelfandMathlib`（确为孤儿，in-degree **0**）**与 `RealRandomMatrixTheory`（非孤儿）**
   ⟹ 「**只被**孤儿 import」**不成立**，**接线本就不缺**。
   注意 **闭合理由须改为「本就存在第二个消费者」**，不是"补了 import"；
4. ~~**`RealWLRefinement` 只被自引用** ⟹ 可能需下游接线。~~
   注意 **订正 B409：原判据为假** —— 实测其 roots 级 importer = **`RealGraphExpressivity`**，
   **并非其自身** ⟹ 「只被**自**引用」不成立。
   注意 **是否仍算缺口取决于判据**：若判据是「in-degree ≥ 1」则**已闭合**；
   若判据是「被**主线**消费」则**未测**（本报告未算主线闭包）。

---

## 五、要点：接手者必读的操作纪律

### 5.0 要点二级**完整性现在**被强制执行**（v14 起）—— 这是最重要的变更**

**此前**：项目造了完整的零锁检查器集，**但 11/12 未接门禁，且 pre-commit 钩子从未安装**
⟹ **所有检查都靠人记得手动跑**（**这是"能力已建成但从未强制执行"的典型**，已登记 B62）。

**现在**：
1. **`verify.ps1` 无条件运行零锁检查器**并逐个打印状态
   （注意 **本条曾写"4 个"—— 复核时实为 6 个**，见 `scripts/verify.ps1` 的 `$checkers` 数组：
   `check-structure` / `check-verification-claims` / `check-unsatisfiable-hypotheses` /
   `check-xref` / `check-corrections` / `check-goal-truth`。**不要手抄个数，直接读那个数组**）
   （**缺失的检查器报 `MISSING`，不静默跳过**）：
   `check-structure` / `check-verification-claims` / `check-unsatisfiable-hypotheses` / `check-xref -All`；
2. **`-StrictCheckers`** ⟹ 有发现时 **exit 6**；
3. 要点**pre-commit 钩子文件已安装**（`.git/hooks/pre-commit`）——
   注意 **但复核发现它当前【跑不起来】**：它是 `#!/bin/sh` 脚本，而在本环境
   **`sh.exe` 因沙箱限制无法创建命名管道**（`fatal error - couldn't create signal pipe, Win32 error 5`）。
   ⟹ **"已安装" ≠ "在提交路径上生效"**（本项目 B239/B244 同族：文件存在 ≠ 会执行）。

**退出码语义**（**分开是因为补救动作不同**）：
| 码 | 含义 | 补救 |
|--:|:--|:--|
| 1 | sorry/axiom 或构建失败 | 修代码 |
| 2 | 源或 olean **完全缺失** | 写文件 |
| 3 | 锚点漂移 | 修登记 |
| 4 | 生成产物漂移 | **重生成文档** |
| **5** | `-StrictOlean`：陈旧/缺失 olean | **重建模块** |
| **6** | `-StrictCheckers`：结构/登记发现 | **修代码或登记** |

注意 **钩子会拦下你的提交**（若 `check-xref` 等报错）⟹ **`git commit --no-verify`** 可绕过，
**但正当前提是"该发现是先存在的 backlog，不是本次引入"**。

### 5.1 构建（**瓶颈是队位，不是编译时长**）

```powershell
cd C:\Users\xingg\Desktop\agent\lattice\lean
powershell -NoProfile -ExecutionPolicy Bypass -File ..\scripts\lake-lock.ps1 <模块1> <模块2> ...
```
- 注意 **模块名不带 `.lean`**（带了 `exit 65`）；
- 注意 **单次等待可达 45 分钟~2.4 小时** ⟹ **一条命令排多个模块**（等待时间相近）；
- 要点**入队前尽量冻结源码**，并用 **`-Expect "Mod=<sha12>,..."`** 让开编时自动核对；
- 要点**等待期间只做只读工作**（读诊断 / 读 pinned 源码 / 验证命题真假），**不要堆编辑**
  （实测有代理因此让 45 条 error 中 15 条是自己引入的）。

### 5.2 零锁自检（**改完就跑**，毫秒级）

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File ..\scripts\check-structure.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File ..\scripts\check-verification-claims.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File ..\scripts\check-unsatisfiable-hypotheses.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File ..\scripts\check-xref.ps1 -All
```

### 5.3 注意 五个**反复踩中**的环境坑

1. **`EACCES (Win32 5)`** ⟹ **先查文件 `IsReadOnly` 属性**，**不是锁**；
2. **PowerShell 5.1 把无 BOM 的 UTF-8 脚本当 ANSI 读** ⟹
   **脚本里的中文字面量变 `????`**，**检查器静默地什么都没查** ⟹ **用码点构造中文**；
   且**函数名别用 `CP`**（`Copy-Item` 的别名）；
3. **`Get-Content` 在中文 `.lean` 上会丢行** ⟹ 用 `[System.IO.File]::ReadAllLines(...,UTF8Encoding($false))`；
4. **`Select-String` 的正则对含 `?` 的名字静默失配**（`find?_eq_none`）⟹ 用 **`.Contains`**；
5. **`check-xref` 需查**三个域**：本仓库 / mathlib / **Lean core（`~/.elan` 下，不在 `.lake`）**。

### 5.4 归属纪律（**本波次已 3 次事故**）

注意 **改任何文件前，先确认它是否已有 owner**（查 `scripts\who-holds.ps1`、查 mtime、查在飞代理列表）。
**发现别人文件有问题 ⟹ 报 owner，不要直接改。**
**本波次事故**：coordinator 误 `git checkout` 毁掉他人修复；coordinator 派两代理同写一文件；
coordinator 未查归属就改 `RealLv00Solver`。

---

## 六、要点：本波次最有价值的**方法论**（已被工具化，但值得人读）

| # | 教训 | 出处 |
|--:|:--|:--|
| 1 | 要点二级**"同一报错重复出现" = 归因错误的信号**，不是"再修一次"的信号（有**三次归因演进**的完整实例） | STYLE |
| 2 | 要点二级**`omega` 失败时先读报错里的 `where a := … b := …`** —— 它直接告诉你它把哪些项当成了变量 | STYLE |
| 3 | 要点二级**"取倒数/取对数"的变形，先把**等价条件**写成一行，再问"假设里有它吗"** | STYLE |
| 4 | 要点**用精确算术判不等式真伪，不要用浮点搜索**（浮点"反例"多为舍入伪影） | STYLE |
| 5 | 要点**"检查器报 0" ≠ "库里真没有"** —— **上线检查器前必须植入已知缺陷验证它能报** | STYLE |
| 6 | 要点**"grep 不到" ≠ "不存在"** —— 必须问"我查的域覆盖了它可能所在的地方吗" | STYLE |
| 7 | 要点**`unexpected token X` 的报错点是"被挤错位的 token"，不是真凶**（已确认 5 例） | STYLE |
| 8 | 要点**"超时"也是"命题为假"的伪装之一**（与 `linarith failed`/`omega could not prove` 同族） | STYLE |
| 9 | 要点**重复定义的登记应写在**声明端**（扫描器看那里），不是消费端** | CORRECTIONS B50 |
| 10 | 要点**"空洞"与"假"必须以不同方式登记**（内容为零 vs 内容为假） | CORRECTIONS B52 |

---

## 七、诚实边界

- **本文档的数字是写作时点实测**；`olean` 新鲜度会随编辑变化，**接手前请重跑 §五 的自检**；
- **B53/B54 的判定**基于**静态阅读 + 形式化推理**，**未逐一经内核确认**（F10 正在修）；
- ~~**26 个陈旧 olean 与 25 个无 olean 模块**是**真实的覆盖缺口** ——
  **它们的存在意味着"该模块的声称当前没有内核背书"**；~~
  注意 **本条【已作废】（B409）**：复核实测 **陈旧 0 / 无 olean 0**
  （内容比对 `python scripts/olean_freshness.py` → `SOURCE CHANGED: 0`；`roots WITHOUT olean = 0`）。
  **该缺口不存在**，故「没有内核背书」这一推论**不成立**。
  注意 **教训**：**不要用 mtime 判 olean 新鲜度** —— 裸 mtime 判据在此报 **48 个"陈旧"**，
  而**内容比对报 0**；那 48 个是**已知的 mtime 假警报**
  （`verify.ps1` 有专门的 content-aware 段重分类它们）。
- **本文档不代表目标完成** —— 目标是长期目标，**在飞行李与结构性缺口见 §四**。

---

*生成于轮 40/40 收尾；云端已同步（`scripts\sync-cloud.ps1 -NoCommit`）。*
