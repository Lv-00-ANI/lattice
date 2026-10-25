# Divergences from the LATTICE Baseline

本文件登记 LATTICE 中**有意**与基准（"通常意义下的数学陈述 / 教科书口径 / 上游惯例"）
不同的地方，以及**任何以假设形式引入而非证明的东西**。

> **Unless specified here, any divergence between LATTICE and its baseline is a bug.**
> **未在此登记的偏离，一律视为 bug。**

> ⭐ **本表受 `scripts/check-divergences.py` 门禁**（`P0-3`）：
> ① **条数一致性** —— `## 数量统计` 表的**逐类条数与 `合计` 行**必须**同时**等于
> **正文实际条目数**（A/B/C 三类的**声明编号**，**非文本命中数**）；
> ② **锚点存在性** —— 每条 `` `文件.lean:行号` `` 所指的**文件必须存在**且**行号在范围内**。
> ⚠ **本文档 §诚实边界 / §B.4 自身的诚实边界**两节**自认**为**推断 / 未判定**的条目，
> 其**行号按 `advisory` 报告而不阻断**（**不惩罚"如实标注自己边界"的行为**）；
> ⚠ 但**文件不存在仍是阻断项**（**那在任何一节都是笔误**）。
> 运行：`python scripts\check-divergences.py`（`--selftest` 做双向自检）；
> 已接入 `scripts\verify.ps1`（**`-StrictCheckers` 下阻断**）。
> ⚠ **缘由**：`CORRECTIONS.md:530` 已逐字警告「**登记表自身会因"补缺口的文件不回落源条目"
> 而出现同对象双条互斥**」（本文件 **C-11** 引）——**无门禁则该警告必然重演**。

## 范式来源（逐字）

本文件的**形式与默示义务**借自 Lean 生态的两个独立先例：

1. **`lean4lean` 的 `divergences.md`** —— 首句逐字：
   > "# Divergences from the Lean Kernel
   > This is a list of places where lean4lean **deliberately** has different behavior from the kernel.
   > **Unless specified here, any divergence between lean4lean and lean4 is a bug.**"

2. **`tenet`** —— 逐字声明：
   > "**The practice, and the name of this file, is borrowed from [lean4lean](…)**"

⭐ **范式精髓**：**默认 = 完全一致；任何偏离必须【登记在案】；未登记的偏离 = bug。**

⚠ **本文档的登记位置由本仓库自己指定**：`lean/README.md:22` 在对照表中**逐字**记录
—— `lean4lean` 的 `divergences.md`（开篇定基调 *"Unless specified here, any divergence … is a bug."*），
并**点名**：「本项目三表与之同构，**缺的是"与上游/惯例的有意分歧"这一类登记**
（R6 建议 #1：**新增 `DIVERGENCES.md`**）」。⇒ 本文件即该建议 #1 的落地。

## 分类维度（为什么不用"理论 / 实现"二分）

`tenet` 逐字指出：**"Asked to sort these into 'theory' and 'implementation', the honest answer is
that almost none of them are about the type theory"** ⟹ 分类维度**必须选对**。

LATTICE 的对应事实：**504 个 `.lean` 文件中 0 个 `axiom`、0 个 `sorry`**（见 §B 的复核方法），
故偏离**几乎不在"证明是否成立"这一维**，而在**下述五维**：

| 分类 | 含义 |
|:--|:--|
| **System boundary** | 体系自认不可内证 / 不可对象化 ⟹ **原理性**，永不消失 |
| **Axiomatic field** | 性质**作为 `structure` 字段**（数据）而非定理引入 |
| **Explicit hypothesis** | 性质作为**显式前提 `(h : …)`** 传入 |
| **Scope / Resource** | 范围裁剪、工具缺失、版本阻塞 ⟹ 只做子集 |
| **Governance** | 强制/登记/接线层 ⟹ 不产生错误但使错误静默传播 |

⚠ **与实际一致性的核对**：`HONESTY-COVERAGE.md:24-26` 实测 **6740 条声明中仅 618 条（9.2%）**
带诚实关键词 —— 登记**覆盖率本身**是偏离清单的一部分（见 **D-GOV-1**）。
⚠ **但 9.2% 不是正确性度量** —— `HONESTY-COVERAGE.md:6-10` **自己警告**（逐字）：
「**This measures the labelling convention, not correctness.** A declaration with no nearby keyword
is not thereby dishonest, and one with a keyword is not thereby honest. Lean has already accepted
every proof; this table only says how much of the source carries the explicit honesty marking that
STYLE.md section 5.4 requires.」（**度量的是标注惯例，不是正确性**）⟹ 本数字**只可**读作
"多少源码带 `STYLE.md §5.4` 要求的显式诚实标注"，**不可**读作"多少证明是对的"。

---

## A 类：体系边界（System boundary，**原理性不可内证**）

| # | 位置（精确符号） | 偏离内容 | 为什么可接受 | 分类 |
|--:|:--|:--|:--|:--|
| **A1** | `RealTemporalLayer.lean:78`（`inductive Gaze`），docstring `:75-77` | **`Gaze` 是【给定的】，不是【导出的】** —— 对应体系公设 (e)「认知主体能执行意向切换」。**该公设永远无法在系统内证明** | 体系**边界 3** 原文：「追问"目光何以能分化"的操作，已经动用了分化后的目光。**分化的根据不可陈述**」。⇒ 与 mathlib 的 `Decidable` / `Nonempty` 作为**类型类前提**同构：前提不是缺陷 | System boundary |
| **A2** | `RealTemporalLayer.lean:89`（`structure Temporal`），`:48-50` | ⭐ **`Gaze` 不带论域参数** —— 这是**显式选择「目光是外部的」**，而非解决问题 | `实现拓展后还剩哪些问题.md` 新问题 3 已推出：若给 `Gaze` 加域参数 ⟹ **域类型需要域类型 ⟹ 无穷回退**。故「外部」是**唯一不陷入回退的抉择**，**登记为边界** | System boundary |
| **A3** | `RealTemporalLayer.lean:54-58`，`:224-225`（`split_immediately_confers_concept`） | **「归类具有构成效力」不可内证**（体系**边界 2**）。本文件把构成效力做成**定义性**的，**不声称证明了它** | 体系原文：「"归类具有构成效力"不可在体系内部证明，**它是全部内部推演效力的来源**。可执行但不可内证的抉择」。⇒ 诚实形式是**把构成效力作为数据/假设引入**，而非假装证明 | System boundary |
| **A4** | `RealTemporalLayer.lean:44-46`，`:380-398`（发现 1） | **`element_iff_no_upper` 是 `Iff.rfl`，不是实质定理** —— 提案把它列为「用途 3：可证命题」，**措辞过强** | `CORRECTIONS.md:2310-2321` 已核验：`isElementUnderUpGaze` **按定义就是** `¬ hasUpper` ⟹ **不可能有别的证法，也不可能被反驳**。⭐ **精确说法是「可陈述且可判定」**，不是「可证命题」 | System boundary |
| **A5** | `RealTemporalLayer.lean:38-43`（诚实边界 1） | **「向上目光 = `intent`」是【解读】，不是体系原文** —— 体系原文**未提 FCA** | 提案 §7.3：「映射是**解读**，非体系原文……其正确性**由映射后的可证性验证，不由原文权威保证**」。`gazeUp` 是 `intent` 的 `rfl` 级重命名 ⟹ **它不证明** `intent` 就是「向上目光」 | System boundary |
| **A6** | `RealTemporalLayer.lean:47-50`，`:509` | **目光自指、论域本身、操作论域：❌ 不做** | 提案 §6.1 明列「不做」：体系自认边界（边界 1/3/4）。⚠ **不是能力不足，是体系声明不可对象化** | System boundary |

### ⭐ A 类的**净后果**（诚实标注）

⚠ **体系与 LATTICE 的逻辑强度不匹配**（提案 §7.2）：

| 维度 | 体系 | LATTICE |
|:--|:--|:--|
| 性质 | 哲学 / 认知论 | 形式化数学 |
| 可内证性 | **明确承认不可内证**（边界 2） | 只能证**充要条件** |
| 处理方式 | 承认不可公度，不强行还原 | **登记为偏离** |

⇒ ⚠ **不要试图"证明"体系的公设 (a)–(e)**。**它们是前提，不是定理。**
强行形式化公设 (e)（目光分化如何可能）会**撞上体系边界 3**。

⭐ **但边界不是失败** —— 体系在同处说：「**在边界极限处，操作转为承受，判断转为对差异的忠实。**」
⇒ LATTICE 的「诚实降级」**正是这一条的实现**：

| LATTICE 现象 | 位置 | 体系对应 |
|:--|:--|:--|
| `activated_closure_iff_zeroFixing` 只给**充要条件** | `RealSymbolToWeightNonlinear.lean:48`（`ZeroFixing`） | 元裁决不可内证 |
| `closed_loop_adds_nothing`（闭环无新内容） | `RealCompileExtractClosed.lean:193-199` | 边界处操作转为承受 |
| `no_extractor_preserves_both`（严格可逆为假） | **`RealReversibilityBoundary.lean:211`** ✅ 实测 | 身份不附着于基底（原理 1） |
| `RealROME`「其余保持」**非定理** | **`RealROME.lean:16`** ✅ 实测 | 受动维度不可完全对象化 |

---

## B 类：**LATTICE 既有的显式假设**（从代码**提取**，非发明）

> ⭐ **本类是本文档的真正价值所在。**
> **提取方法（可复核）**：`[System.IO.File]::ReadAllLines` + `.Contains` 逐行扫描
> **444 个非探针 `.lean` 文件**（总计 504 个，排除 `_probe*`）。
> ⚠ **不用 `Select-String` / 正则** —— 对含 `?`、`.` 的 Lean 名字会静默失配（本项目硬纪律）。
>
> **复核结论（硬事实）**：
> - `axiom ` 作为**声明**出现：**0 处**（496 次 `axiom` 提及**全部**是 "无 sorry / axiom" 的**声称**）
> - `:= by sorry` / 裸 `sorry`：**0 处**
> - **`structure` 声明：92 个**
> - **`显式假设` / `显式前提` 标注行：300 行**
>
> ⇒ ⭐ **LATTICE 的假设不活在 `axiom` 里，活在【结构字段】与【显式前提】里。**
> ⇒ **这就是为什么"按名字查 axiom"会得到 0 而假设实际有 300+ 处。**

### B.1 公理式**结构字段**（Axiomatic field）

| # | 位置（精确符号） | 偏离内容 | 为什么可接受 | 分类 |
|--:|:--|:--|:--|:--|
| **B-1** | **`RealFloatFormat.lean:99`** `structure RoundOp` —— 字段 `err_bound` `:103`、`idem` `:105` | **舍入算子的两条性质是【字段】不是定理**：`\|round x − x\| ≤ eps·\|x\| + tiny` 与幂等 | `:97-98` 逐字：「**不建模 IEEE 逐位语义**（无舍入模式、无 NaN/Inf、无指数偏置）—— 这是**显式的抽象降级**」；`:21`：「**这不是 Lean `axiom`，而是显式假设的数据**，使用者必须自己给出实例」 | Axiomatic field |
| **B-2** | **`RealIEEE754.lean:119`** `structure IEEERound` —— **7 个字段**：`err_bound:123` / `idem:125` / `monotone:127` / `sign_preserve_pos:129` / `sign_preserve_neg:131` / `subnormal_bound:133` | **IEEE 语义的六条性质全部是字段** | `:117-118`：「**这些性质是结构字段（显式数据）**，本文件不建模位模式、不建模 NaN/Inf」。⚠ **这是比 `RoundOp` 更强的降级面** —— 6 条字段意味着 6 处"使用者必须提供" | Axiomatic field |
| **B-3** | **`RealEYM.lean:247`** `def TraceCrossBound`（**假设谓词**），使用点 `:300` `:378` `:396` `:404` `:414` | **EYM 交叉项界作为 `def` 形式的显式假设谓词** —— `2·trace(A*B) ≤ headEigSq hA.eigenvalues k + trace(B*B)` | `:243-246` **逐字**：「mathlib 4.14 **无**现成的核/像维数交叉引理可用；故本文件把该式**作为显式假设**引入，**不声称已证**」。`:180`：「**它是 `def` 形式的显式假设谓词**」 | Axiomatic field |
| **B-4** | **`RealCausalDoCalculus.lean:502`** `structure BackdoorSet`（`noDesc:504` / `blocks:506`）；桥在 `:585` | **后门准则作为 `Prop` 结构**；`BackdoorBridge` 是**显式假设** | `:585-588` 逐字：「`BackdoorBridge` 是**显式假设**。这是**有意的分解**：「后门准则 ⟹ 桥」的完整图论归纳**未做**，缺口被**精确定位到一条**」；`:695`：「把"未做"写成**有名字的 `Prop`** 比在文档里含糊说"未做"更有价值 —— 它给出了后续工作的**精确接口**」 | Axiomatic field |
| **B-5** | **`RealLv00Systems.lean:688`** `def stepSound`；`:693` `inductive TraceSound`（构造子 `h_step:696`） | **单步/迹语义可靠性是显式假设**，不是定理 | `:687` **逐字**：「**这是显式假设，不是公理。**」；`:692` 同。⚠ **这一条尤其值得登记**：它是**证明系统自身的可靠性**，即**最不该是假设的地方** | Axiomatic field |
| **B-6** | **`RealLv00AxiomPackages.lean:479`** `structure LvAxiomSystem` —— **`eight_rules` 等是字段** | **"八规则"由结构字段承载** | `:439-440` **逐字**：「不含任何 `axiom`；「八规则」由**结构字段显式假设**（`LvAxiomSystem.eight_rules` 等）承载 —— 这是本项目**允许**的显式假设形态」；`:477`：「是**结构字段**，即**显式假设** —— 这正是本项目「**禁止 `axiom`、允许结构字段假设**」」 | Axiomatic field |
| **B-7** | **`RealEvalBridge.lean:190`** `structure PrimApprox`（误差界 `δ`） | 四个超越原语（`exp`/`log`/`sin`/`cos`）的**浮点误差作为显式假设数据** | `:18`：「四个原语近似及其误差 `δ`（**显式假设的数据**，与 `RealFloatFormat.RoundOp` **同一风格**）」；`:435`：「**显式假设数据**而非从 `Float` 实现推出的定理」。⚠ `:58` 明确：「除 `PrimApprox`（显式假设结构）与 ℚ/Float 可执行函数外，全部为定理」 | Axiomatic field |
| **B-8** | **`RealCompileFloatCorrectness.lean:422`** `hMul`（乘法分支的显式假设） | **乘法分支的完整证明未完成**，以显式假设传入 | `:427` **逐字**：「**这不是 Lean `axiom`，而是显式假设的数据**（对齐 `RealFloatFormat.RoundOp`）」；`:30`：「`lit`/`var`/`add`/`neg` 四个构造子是**完整证明**；`mul` 走 `hMul`」。⚠ `:38` 承认：**乘法分支的完整证明未完成** | Axiomatic field |
| **B-9** | **`RealLv00Solver.lean:817`** `structure GroupAxioms`（`mul_assoc`/`one_mul`/`mul_left_inv`） | 群公理被**重新声明为本库结构** | ⚠ `:816` **逐字**：「**与 mathlib `Group` 重复，见文件头。**」；`:813`：「上游此处的 `mul_one` 证明体**有洞，编译不过**」。⇒ ⭐ **这是"与上游重复建设"的一个具体登记点**（README.md:29 承认短板③「与上游重复建设**未被系统追踪**」） | Axiomatic field |
| **B-10** | **`RealConversionStabilityConvergence.lean:323`** `structure IsClosureOperator`（`idem`/`mono`/`extensive`） | 闭包算子三性质作为 `Prop` 结构 | ✅ **与 B-1…B-9 不同**：`:441` `closureOperator_isClosureOperator` **真的由既有定理填充**（`extract_idempotent` / `closureOperator_monotone` / `closureOperator_extensive`）⟹ **这是"接口打包"，不是"假设外置"**。⚠ **登记它以区别于真假设** | Axiomatic field（**良性**） |
| **B-11** | **`RealQATRate.lean:262`** `structure CondGradModel`；**`RealGaussianProcess.lean:135`** `structure IsGaussianVector`；**`RealGeneralizationBound.lean:61`** `structure GeneralizationBound` | 模型条件的结构封装 | 这些结构**混合**了"接口"与"假设"两种成分。⚠ **诚实边界**：本条我**只登记位置，未逐字段判定**哪些字段是假设（见文末诚实边界 §3） | Axiomatic field |
| **B-12** | **`RealLv00Geometry.lean:125`** `[Incidence P L]` 实例参数 | **几何公理以类型类实例参数引入** | `:125` **逐字**：「它们因此是**显式假设**：用 `[Incidence P L]` 这样的实例参数引入，」；另见 `:294` `structure HilbertPlane` | Axiomatic field |

### B.2 ⭐ 反复出现的**显式前提模式**（Explicit hypothesis）—— 按模式归并

⚠ 以下每组是**同一模式在多文件重复**，给**索引式引用**而非逐条罗列。
**全库 300 行 `显式假设/显式前提` 标注**，按模式归并为 12 组：

| # | 模式（假设的**内容类型**） | 代表位置（`文件:行`） | 为什么可接受 | 分类 |
|--:|:--|:--|:--|:--|
| **B-13** | ⭐ **链式可达性 `hreach`** —— 每层的域条件只能由链上实际中间激活给出 | `RealMixedAttention.lean:590-591`、`RealModelChain.lean:208`、`:245`、`RealModelChainHetero.lean:149`、`:181` | ⚠ `CORRECTIONS B53` 系列：旧稿 `hxdom：∀z, c ≤ ‖z‖` 与 `hc : 0 < c` **矛盾**（`z := 0`）⟹ **前提不可满足、定理空洞**。⇒ `hreach` 是**有意传入的可满足前提**（专家明证"恒等链 + `x = c•e₀`"）。⭐ **这是"空洞 → 可满足假设"的修复形态** | Explicit hypothesis ⚠⚠ **订正（B410/C-31，2026-09-27）**：本条**不得读作「缺陷已消除」** —— `hreach` 以**同一见证**（`h = 0`）**同一机制**失败，失败集是原点的**开球**；详见 **C-31**。 |
| **B-14** | **MGF / 条件矩界**（把集中不等式引理本身当假设） | `RealMcDiarmid.lean:77` `hmgf`、`:256`、`:565-568`；`RealHoeffdingInequality.lean:328` `hcond`、`:14`；`RealHoeffdingMeasure.lean:52` | `RealMcDiarmid.lean:203`：「McDiarmid MGF 界在本文件中 **未证**，它作为定理的显式假设出现」；`:256`：「`hmgf` 与 `hmgf_neg` 均为 MGF 型显式假设，**未在本文件**（证明）」。⇒ **把"待证引理"外置为接口**，比伪造证明诚实 | Explicit hypothesis |
| **B-15** | **可交换性 / 独立性**（真实分析里由结构给出） | `RealCrossValidationIID.lean:47-50` `huncorr`/`hvar`；`RealRademacher.lean:37`、`:485` `hswap`；`RealConformalPrediction.lean:73` | `RealCrossValidationIID.lean:49`：「这**避免了伪造独立性**」；`:478`：「诚实地讲：真正跨折的独立性在本文件中是**显式假设** `huncorr`」。⭐ **要点：独立性是"不能伪造"的典型** | Explicit hypothesis |
| **B-16** | **强凸 / 光滑 / 共强制性**（Baillon–Haddad 等经典但本库未证） | `RealStrongConvex.lean:44`、`:224` `GradientCoCoercive`；`RealNesterov.lean:41`；`RealProxGrad.lean:41`；`RealVarianceReduction.lean:61` `GradLip` | `RealStrongConvex.lean:224`：「光滑强凸函数满足此式；本文件以显式假设引入（**不隐藏 gap**）」；`RealVarianceReduction.lean:35`：「现有 `Smooth` 是单侧下降引理」。⇒ `GradientCoCoercive` **在三处重复外置**（同族重复建设的又一例） | Explicit hypothesis |
| **B-17** | **RIP / 稀疏恢复的零空间条件** | `RealCompressedSensing.lean:672` `IsRIP`、`:698`；`RealSparseCoding.lean:76`、`:104` `hNull`、`:1277` | `RealCompressedSensing.lean:698` **逐字**：「RIP 是**显式假设**（不从别的性质推出，**mathlib 无 frame theory**）」；`:17`：「把 RIP 作显式假设引入，只证「RIP + 稀疏 ⟹ 唯一性/稳定性」这一层」。⚠ `RealSuperpositionCapacity.lean:40` 复核：「RIP / compressed sensing / frame theory 全树 **0 命中**」 | Explicit hypothesis |
| **B-18** | **`BddAbove` / `BddBelow`（`sSup`/`sInf` 的 junk 值防护）** | `RealConjugateDuality.lean:77`、`:103`；`RealFenchelMoreau.lean:65`、`:149`；`RealDualTheory.lean:26`、`:39` | ⚠ **这是 ℝ 值 `sSup` 的语义陷阱**：`CORRECTIONS.md:525` **逐字**：「ℝ 值 `sSup` 在集合**无上界时返回 junk 值 0**（不是 `⊤`）……**去掉假设命题为假**」。⇒ **不是"懒得证"，是"不假设它命题就是假的"** | Explicit hypothesis |
| **B-19** | **数据域 / 非退化前提**（防除零、防空分母） | `RealBernstein.lean:63` `V > 0`；`RealAzuma.lean:48`；`RealBanditTheory.lean:103` `hK : 0 < K`；`RealBatchEditClosed.lean:40`；`RealGelfand.lean:179` `hn : 0 < n` | 标准分析簿记。`RealBanditTheory.lean:103`：「`hK : 0 < K` 是显式前提（至少一条臂）：`Fin K` 非空才能取 `sup'`」 | Explicit hypothesis |
| **B-20** | **浮点误差界外置** | `RealMixedPrecision.lean:43` `M`；`RealQAT.lean:46`；`RealSTEError.lean:32`；`RealGeluExact.lean:32`、`:168`；`RealCompressionRate.lean:72` | `RealGeluExact.lean:32`：「本文件只给**条件形式**（把 `δ` 作为显式假设外置）与一个无条件的弱界 `\|x\|`」 | Explicit hypothesis |
| **B-21** | **测度论 / 可积性 / 导数-积分交换** | `RealMeasurePD.lean:23` `DerivIntegralExchange`、`:83`、`:173`；`RealFisherInfo.lean:26`、`:43`；`RealHoeffdingInequality.lean:179` `h_int` | `RealMeasurePD.lean:23`：「**不作为已证定理**：本文件把它写成**显式假设** `DerivIntegralExchange`」；`:173`：「它是主定理二的显式假设**而非隐藏公理**」。⭐ **"而非隐藏公理"是本项目登记语的核心句式** | Explicit hypothesis |
| **B-22** | **递推 / 单步收缩 `hstep`** | `RealCompressionRandom.lean:48`、`:265`；`RealMirrorDescent.lean:30`；`RealQATRate.lean:49`、`:115`；`RealFedAsync.lean:31` `hconv2` | `RealQATRate.lean:115`：把它「当作**显式假设** `hstep`。本文件补上**从滤流结构推出它**的一步」 ⟹ **部分是"从假设升级为定理"的记录** | Explicit hypothesis |
| **B-23** | **有界性 / 范数域 / 完备性** | `RealSSMDiscretization.lean:37-38` `[CompleteSpace 𝔸]`；`RealPAdicNorm.lean:25` `[CompleteSpace K]`；`RealSelectiveSSM.lean:47` `‖A_t‖ ≤ ρ`；`RealReproducingKernelTheory.lean:126` `hKnn` | `RealSSMDiscretization.lean:37-38` **逐字**：「**显式假设 —— 完备性**……这与任务书给出的变量集相比是**新增的显式假设**」（⭐ **主动登记"我比任务书多加了假设"**）；`RealSelectiveSSM.lean:47`：「是**显式前提**而非导出结论」 | Explicit hypothesis |
| **B-24** | **二阶可微 / Hessian 条件** | `RealHessian.lean:31`；`RealNewtonRate.lean:27`、`:31`；`RealKKTSecondOrder.lean:467`、`:470`、`:495`；`RealMAML.lean:38`；`RealMAMLSecondOrder.lean:33`、`:372` | `RealHessian.lean:31`：「故 μ 是**显式假设**（**不隐藏 gap**）。这是本文件唯一的实质性降级」；`RealKKTSecondOrder.lean:467`：「写成**显式假设**（docstring 第 50–54 行说明这是「经典教材的……）」。⚠ `RealSecondOrderUpgrade.lean:49` 有一张**"显式假设 → 可否升级为定理"的审计表** | Explicit hypothesis |

### B.3 ⭐ 提取过程中发现的**此前未集中登记的**结构性事实

> ⚠ **以下五条是本次提取的增量发现** —— 它们**散落在各文件的 docstring 里**，
> 但**没有任何单一登记表把它们并置**。

| # | 发现 | 精确位置 | 为什么重要 |
|--:|:--|:--|:--|
| **B-25** | ⭐ **`GradientCoCoercive`（Baillon–Haddad 共强制性）在 3 个文件独立外置** | `RealStrongConvex.lean:44`、`RealNesterov.lean:41`、`RealProxGrad.lean:41` | 三处**各自**写"本文件以显式假设引入（不隐藏 gap）" ⟹ **同一个数学条件的 3 份并行登记**，无单一权威点。这是 `code-abstraction-governance` 意义上的**重复** |
| **B-26** | ⭐ **`RoundOp` 风格的"公理结构"被至少 4 个模块各自复制** | `RealFloatFormat.lean:99`（`RoundOp`）、`RealIEEE754.lean:119`（`IEEERound`）、`RealEvalBridge.lean:190`（`PrimApprox`）、`RealMixedPrecision.lean:147`（`FPAdder`） | `RealCompileFloatCorrectness.lean:427` 自己承认这是"对齐 `RealFloatFormat.RoundOp`"。⇒ **浮点公理面分散在 4 个结构里**，**总字段数**是真实降级面（`IEEERound` 一项就 6 条） |
| **B-27** | ⭐ **"空洞 → 可满足假设"的修复留下 `hreach`** —— ⚠⚠ **订正 B414：原文「5 个文件」为【口径误用】** | ⭐ **真实使用 `hreach` 的文件 = 3**：`RealMixedAttention.lean`（11 行 / **15 处**）、`RealModelChain.lean`（6 行 / **8 处**）、`RealModelChainHetero.lean`（6 行 / **8 处**）。⚠ **仅为散文提及（活代码 0，非 use site）**：`RealChainLiftGeneral.lean:13/:205/:236/:240`、`RealOperatorSplitCompose.lean:488/:496`、`RealHreachConditional.lean`（12 处全在注释）、`_X-03.lean`（非 roots）。⚠ **原文所列 5 个行号（`:590`/`:208`/`:245`/`:149`/`:181`）经复核【全部失效】** | ⚠⚠ **订正（B414）**：**原文「5 个文件」是把【旧假设 `hxdom` 的分布】误用于【新假设 `hreach`】** —— `CORRECTIONS.md:1577-1584`（B53.2）的 5 文件表统计的是 `hxdom : ∀ z, c ≤ ‖z‖`，其中 `RealBlockInstance`/`RealBlockConstants` **根本没有 `hreach`**。⭐ **协调者复测：全库 `hxdom` 活代码 = 0**（替换已完成），**但两个假设的文件分布【不同】**（`hxdom` 5 文件 / `hreach` 3 文件）。⭐ **口径**：上列 11/6/6 为**行数**；`B410` 的 8/8/15 为**出现数**（一行可含多处）—— **两者都对，引用时必须标口径**。⭐ **B-27 正文的警告仍然成立且重要**：`hreach` 的分布**此前未被单独登记**，本行即为该登记 |
| **B-28** | ⭐⭐⭐ **`stepSound`/`TraceSound`：验证器自身的可靠性是假设** —— ⚠⚠ **且该假设已被证明**不可能成立（**不是"未证"，是"已假"**）** | `RealLv00Systems.lean:688`、`:693`（缝的精确定位在 **`:720` `evidenceCheck_sound_of_sound`**）| ⚠ **这是全库最尖锐的一条**：`VERIFICATION.md:5` 的原则是「**Lean 证明是验证基础**」，而 **Lv-00 验证器的语义可靠性本身就是显式假设**（`:687`：「这是显式假设，不是公理」）。⇒ **"验证基础"与"用它验证的东西"之间存在一条假设缝** —— 该缝**从未被集中登记**。<br>⭐⭐ **【v14 升级】该假设已被**内核验证为假****（**登记 `CORRECTIONS B73` / `B84`**）：<br>• **`transition` 的前 3 个分支**（`.hypothesis`/`.lemma`/`.rewrite`）**对已证集做无语义约束的增删**（**且 `stepOk` 对 `.hypothesis` 恒 `true`**，`:334`）⟹ **取一个使集合不可满足的约束即可证伪**；<br>• **已证定理**：**`not_stepSound_of_unsat`**（`:789`）、**`stepSound_hypothesis_false`**（`:804`）、<br>&nbsp;&nbsp;⭐ **`evidenceCheck_unsound_unless_hypothesis_free`**（**`:823`**，**结论是 `False`** ⟹ **不可能由 `rfl`/`decide` 平凡成立**）；<br>• ⚠ **⇒ 故本条已从"**外置的假设**"变为"**已证的不可能性**"** —— **它是全库**唯一**"假设本身为假"的条目**（其余 `RoundOp`/`IEEERound`/`PrimApprox`/`hMul` 只是**未证**，**可能为真**）。<br>✅ **但当前实际影响有限**：**该接口**零消费者****（全仓仅其声明行出现 1 次）⟹ **缝"目前不漏，因为没接线"**；⚠ **一旦接线就会漏**。<br>⇒ ⭐ **人类可读版见 `VERIFICATION.md §6-bis`**（**条件可靠性声明**）。 |
| **B-29** | ⭐ **`GroupAxioms` 与 mathlib `Group` 重复** | `RealLv00Solver.lean:817`，`:816` 自述「**与 mathlib `Group` 重复，见文件头**」 | 与 `README.md:29` 短板③「与上游重复建设**未被系统追踪**（"3,475 定理里多少上游已有"**没有机制回答**）」**逐字呼应**。⇒ **这是该短板的一个可枚举实例**，但**没有清单** |

### B.4 ⭐ **全库 `structure`/`class` 逐字段分类**（补齐 §诚实边界 3 与 4）

> ⭐ **本节的由来**：本文档 §诚实边界 3 与 4 **自认**「92 个 `structure` 里只逐行核对了 12 个
> ⟹ B.1 不是完整清单，是**已确认代表集**；其余 ~80 个**可能仍藏假设字段**」。
> **本节即该待办的执行结果** —— **逐字段分类全部 95 个真实声明**（312 个字段）。
>
> **方法（可复核）**：`[System.IO.File]::ReadAllLines` + `.Contains` 逐行扫描 **444 个非探针 `.lean`**；
> ⚠ **未用 `Select-String`**（对含 `?`/`.` 的名字会**静默失配** —— 本项目硬纪律）。
> **判据不是「字段类型是 `Prop` 还是 `Type`」**（本文档 §B.1 已指出该判据不充分），
> 而是**该字段是否在别处被**真**填充**：用 `def … : <结构名> where` / `instance : <结构名>` /
> `extends` 三类**构造点**实测（见 **B-31** 的计数）。

| # | 位置（精确符号） | 偏离内容 | 为什么可接受 / 为什么是假设 | 分类 |
|--:|:--|:--|:--|:--|
| **B-30** | ⭐ **`RealLv00GeometryHilbert.lean:59` `class Incidence`（`I1:165`/`I2:167`/`I3:170`）、`:182` `class Betweenness`（`B1:186`/`B2:188`/`B3:190`）、`:194` `class Order`（`density:196`/`extension:198`/`midpoint:200`/`trichotomy:202`）、`:216` `class HCongruence`（`C1:222`/`C2:224`/`C3:227`/`C4_reflexive:230`/`C4_symmetric:232`/`C5_SAS:235`）、`:246` `class Parallel`（`playfair:248`）、`:294` `structure HilbertPlane`（`extends Order/Point + HCongruence + Parallel + Continuity`）** | ⭐ **Hilbert《几何基础》五组公理（合计 19 条）被整体承载为类型类字段**，且**全库 0 个实例**：`I1–I3`(3) + `B1–B3`(3) + `density/extension/midpoint/trichotomy`(4) + `C1–C5`(7) + `playfair`(1) = **18 条公理**（`lies_on`/`between`/`segCong`/`angCong` 是关系**数据**，不计） | ⚠ **这是全库最大的单点假设面，且此前只在 B-12 登记了「`[Incidence P L]` 实例参数」一行**。`:123-126` 逐字：「这些"公理"全部是**类型类字段**……它们因此是**显式假设**」——⚠ **自述诚实，但 B-12 未给出字段数**。**实测 0 个实例**（全库仅 `:242`/`:275`/`:303` 作为**参数**出现在绑定位）⟹ **这些公理从未被任何模型满足过**，`HilbertPlane` 的三个定理（`:303`/`:308`/`:313`）是**条件于公理的** | Axiomatic field |
| **B-31** | ⭐ **全库 93 个结构名中，仅 26 个**曾被真正构造**** | 例：`PositionEncoding`（`RealPosEncodingInterface.lean:146`/`:168`/`:187`）、`Conversion`（`ConvertLinear.lean:83`）、`MAMLChainRule`（`RealMAML.lean:88`）、`RoundOp`（`RealAbstractionRegistry.lean:277`）、`LvBitVec`（`RealLv00Solver.lean:896`）、`IEEERound`（`RealIEEE754.lean:511` 仅**转接**）、`VerifierState`（`RealLv00Systems.lean:279`）；**其余 67 个**（含 `GeneralizationBound`、`PrimApprox`、`FPAdder`、`IEEEDirected`、`ROBDDCanonical`、`CondGradModel`、`BinSCM`、`Theory`、`ConflictSet`、全部 Hilbert 类）**从不被构造，只作参数/字段类型出现** | ⭐ **这是本文档 §B.1 缺失的判别量**：一个结构**若从不被构造**，则其**每个 `Prop` 字段都是纯假设**（永无填充者）；若**被构造**，则需**逐个**核对构造点是否**真由既有定理填充**。⇒ **B-30 的 0 实例、B-1 的 `IEEERound` 仅被 `ieeeToRoundOp` 转接**，正是「无填充者」的两种形态 | Structural fact |
| **B-32** | ⭐ **`RealLv00GeometryHilbert.lean:160` `class Continuity` —— 两条"公理"的结论被写成 `True`**（`archimedes:264` `∃ (n : ℕ), True`；`dedekind:269` `∃ (O : Point), True`） | ⚠ **退化公理：字段类型虽是 `Prop`，但恒真 ⟹ 不约束任何东西**。`:257-260` 逐字自述：「上游把 Archimedes 与 Dedekind 的**结论部分写成了 `True`**……这样的"公理"在逻辑上**不约束任何东西**（**任何类型都满足**），把它当公理是**空的**」 | ⚠ **这是与 `CORRECTIONS B53`（不可满足前提）【方向相反】的失败类**：B53 是「前提**假**⟹ 定理空洞」，本类是新登记的「前提**恒真**⟹ 公理空洞」。⚠ **零锁检查器实测**：`check-unsatisfiable-hypotheses.ps1` **只查一种模式**（范数下界 vs 正性），**实测 0 命中** ⟹ **本类逃过全部现有检查器**（呼应 `CORRECTIONS B62`「11/12 检查器未接门禁」）。本文件已**主动标注为退化形式**并另给 `ContinuityProper` | Axiomatic field（**退化/空**） |
| **B-33** | ⚠ **`RealLv00GeometryHilbert.lean:173` `class ContinuityProper`（`archimedes_nondegenerate:277`）** —— 作为 B-32 的"非退化替代"引入，但**结论是 `∃ (n : ℕ), 0 < n`** | ⚠ **该"非退化"形式仍是恒真的**：对**任意** `Point`、任意 `A B C D`，取 `n := 1` 即证，**与几何无关**。`:271-273` 自述「此处给出**非空**的形式」 | ⇒ ⭐ **"非退化替代"本身未达到其宣称的目的** —— 旧的空洞（`∃ n, True`）换成了新的空洞（`∃ n, 0 < n`）。⚠ **本条的正当性来自"它比上游好"，但按本文档 §方法论纪律 3（反面义务），声称的升级若实际不成立，必须在案** | Axiomatic field（**退化/空**） |
| **B-34** | ⭐ **`RealPosEncodingInterface.lean:72` `structure PositionEncoding` 的 5 个 `Prop` 字段**（`hB:81`/`hL:82`/`bounded:84`/`lipschitz:86`/`shiftLaw_holds:91`） | 表面形如 B-1 的"公理结构"，**实则相反** | ✅ **与 `IsClosureOperator`（B-10）同属【良性】**：`:141` 逐字「**三个实例（每个字段都由既有定理填充）**」，实测 **3 个构造点**（`:146` `absPosEncodingInterface`、`:168` `alibiPosEncodingInterface`、`:187` `ropePosEncodingInterface`），每字段填自**既有定理**（`:153` `abs_pos_bounded`、`:155` `abs_pos_smooth`、`:177` `alibi_is_bounded_perturbation`、`:179` `alibi_bias_lipschitz`、`:194` `Real.abs_cos_le_one`）。⇒ ⭐ **这是"接口打包"，不是"假设外置"** | Axiomatic field（**良性**） |
| **B-35** | ⭐ **`RealLv00Solver.lean:888` `structure LvBitVec`（`valid:892`）；`RealLv00LinearAlgebra.lean:310` `structure LvInterval`（`wf:316`）；`RealAbstractInterpretation.lean:355` `structure IntervalAbstract`（`wf:361`）；`RealLv00GeometrySymbolics.lean:30` `structure RationalNumber`（`den_pos:337`）** | 4 个"良构性字段"（`val < 2^W`、`lo ≤ hi`、`0 < den`）——**形状与 `err_bound`/`idem` 相同，实质不同** | ✅ **良性**：实测**均有真填充**。`LvBitVec.ofNat`（`:896`）以 `Nat.mod_lt` **证明** `val < 2^W`；`LvInterval.point`（`:319`）与 `IntervalAbstract.point`（`:392`）以 `le_rfl` **证明** `lo ≤ hi`。⇒ ⭐ **判据示范：同一"形状"（`Prop` 字段）可以是假设也可以是良性，取决于**有无填充者**（见 B-31） | Axiomatic field（**良性**） |
| **B-36** | ⭐ **`RealGeneralizationBound.lean:61` `structure GeneralizationBound`（`sound:71`）** | ⚠ **把"泛化界成立"这一整个数学内容作为单字段**：`sound : generalizesWith emp pop bound delta` | ⚠ **实测 0 个构造点**（全库仅 `:75` `GeneralizationBound.sound'` 作**消去**用）⟹ **`sound` 永远是假设**。⚠ `:58-60` 自述「把 soundness 的**证明作为结构字段传入**」——⚠ **诚实，但"传入"意味着调用方必须提供，即假设**。⇒ ⭐ **这是 B-11 悬置的三条之一，现判定为【A 类真假设】** | Axiomatic field |
| **B-37** | **`RealQATRate.lean:262` `structure CondGradModel`（`hp0:274`/`hp1:276`/`heta:278`/`hL:280`/`hσ2:282`）** | B-11 悬置的三条之二 | ✅ **大部分良性，但真正的假设不在此结构内**：`p`/`g`/`eta`/`L`/`sigma2` 是**数据**；5 个 `Prop` 字段仅为**簿记**（非负/归一/正）。⭐ **实测：该文件把两条**实质**假设放在结构**外**的 `def`**：`:291` `CondUnbiased`、`:295` `CondVarianceLe`。⇒ **B-11 的"混合"判断正确，但结构字段本身是良性的** | Interface（**良性**） |
| **B-38** | **`RealGaussianProcess.lean:135` `structure IsGaussianVector`（`symm:138`/`psd:140`）** | B-11 悬置的三条之三 | ✅ **是谓词/接口，不是未证假设**：`:131` 逐字「本定义是**代数载体，不是概率断言**：**不声称**存在随机向量以其为分布」。`symm`/`psd` 是**给定矩阵的性质**（对称半正定矩阵**存在**），`RealRKHSKernel.IsPSDKernel` 可直接对接。⇒ **A 类判据不成立** | Interface（**良性**） |
| **B-39** | ⭐ **`RealLv00Solver.lean:288` `structure ROBDDCanonical`（`reduced:292`/`ordered:294`/`key:296`）** | `reduced`/`ordered` 是**证明义务字段**；⚠ `key` 是**数据字段却承载不可证的语义** | ⚠ `:296` 注释逐字：「**同一布尔函数必须给出同一个 `key`**」——⚠ **该性质是注释里的承诺，不是字段里的命题**；`:304` `robdd_canonical` 只证「`b` 与 `key` 都相等 ⟹ 整体相等」（`:301-302` 自述「**以显式的 `key` 字段为前提**，因此证明是诚实的结构化论证」）。⇒ ⭐ **登记点：`key` 的规范性是【注释级假设】，字段类型无法承载它** —— 与 §B.1「假设活在结构字段里」是**同一现象的另一形态** | Axiomatic field（`key` 语义） |
| **B-40** | ⭐ **`RealPAdicNorm.lean:61` `class IsNonarchimedeanNorm`（`norm_add_le_max:62`）** | 非阿基米德范数性质作为类型类 | ⚠ **与 mathlib 重复且上游有更强设施**：`:29` 逐字实测「**`instance : IsUltrametricDist ℚ_[p]`（`:707`）——「强三角不等式」的 **mathlib 官方类型类**」。⇒ ⭐ **本类是"与上游重复建设"的又一实例（同族 B-9/B-29）**，且 `:35`/`:246` 自认「**未接线到 `ℚ_[p]`**」。⚠ **B-40 的假设性在于它是【未被任何具体域实例化的抽象类】** | Axiomatic field |

**B.4 分类计数（实测，非估计）**：

> **口径**：**96 个文本命中**中，`RealPAdicNorm.lean:8` 是 `/-!` **docstring 内的伪声明**
> （真声明在 `:61`）⟹ **真实声明 95 个**（93 个不同名字，`lvPoint`/`IsNonarchimedeanNorm`/
> `PositionEncoding` 三名各有 2 处）。**字段总数 312**。

| 类别 | 字段数 | 说明 |
|:--|--:|:--|
| **D 数据字段** | **225** | 被操作的输入/输出（`Point`、`Constraint`、`a : List Int`、关系载体 `X → Prop` 等） |
| **I 接口字段** | **4** | `toFun`（`RoundOp:101`/`IEEERound:121`/`FPAdder:149` 的裸函数）——**性质由上列 `Prop` 字段承载** |
| ⭐ **A 假设字段** | **47** | **真假设**（`Prop` 型 **且** 该结构**无**任何填充者）⟹ 见下方**完整清单** |
| **B 良性字段** | **36** | `Prop` 型**但确有填充者**（B-34/B-35/B-37/B-38 已示范） |
| **合计** | **312** | ✅ 加总闭合 |

#### ⭐ A 类（真假设）完整清单 —— **本节的产出核心**

⚠ **共 47 个字段，分属 13 个结构**。**「为什么是假设」= 该结构在全库 444 个非探针文件中
【没有任何构造点】**（无 `def … : <结构> where`、无 `instance : <结构>`），
⟹ **该字段永远只能由调用方作为前提提供**。

| # | `文件:行` | 结构 | 字段 | 为什么它是假设 | DIVERG 状态 |
|--:|:--|:--|:--|:--|:--|
| A-1 | `RealLv00GeometryHilbert.lean:59` | `Incidence` | `I1` | **0 个实例**；Hilbert 关联公理，无任何模型满足过 | 部分（B-12 只记 `[Incidence P L]`） |
| A-2 | `RealLv00GeometryHilbert.lean:59` | `Incidence` | `I2` | 同上（唯一性公理） | 部分 |
| A-3 | `RealLv00GeometryHilbert.lean:59` | `Incidence` | `I3` | 同上（非共线三点存在性） | 部分 |
| A-4 | `RealLv00GeometryHilbert.lean:80` | `Betweenness` | `B1` | **0 个实例**；Hilbert 序公理 | ⭐ **新** |
| A-5 | `RealLv00GeometryHilbert.lean:80` | `Betweenness` | `B2` | 同上 | ⭐ **新** |
| A-6 | `RealLv00GeometryHilbert.lean:80` | `Betweenness` | `B3` | 同上 | ⭐ **新** |
| A-7 | `RealLv00GeometryHilbert.lean:92` | `Order` | `density` | **0 个实例**；稠密性公理 | ⭐ **新** |
| A-8 | `RealLv00GeometryHilbert.lean:92` | `Order` | `extension` | 同上 | ⭐ **新** |
| A-9 | `RealLv00GeometryHilbert.lean:92` | `Order` | `midpoint` | 同上 | ⭐ **新** |
| A-10 | `RealLv00GeometryHilbert.lean:92` | `Order` | `trichotomy` | 同上 | ⭐ **新** |
| A-11 | `RealLv00GeometryHilbert.lean:114` | `HCongruence` | `C1` | **0 个实例**；Hilbert 全等公理 | ⭐ **新** |
| A-12 | `RealLv00GeometryHilbert.lean:114` | `HCongruence` | `C2` | 同上（传递性） | ⭐ **新** |
| A-13 | `RealLv00GeometryHilbert.lean:114` | `HCongruence` | `C3` | 同上（可加性） | ⭐ **新** |
| A-14 | `RealLv00GeometryHilbert.lean:114` | `HCongruence` | `C4_reflexive` | 同上 | ⭐ **新** |
| A-15 | `RealLv00GeometryHilbert.lean:114` | `HCongruence` | `C4_symmetric` | 同上 | ⭐ **新** |
| A-16 | `RealLv00GeometryHilbert.lean:114` | `HCongruence` | `C5_SAS` | 同上（**SAS 是 Hilbert 体系的关键公理**） | ⭐ **新** |
| A-17 | `RealLv00GeometryHilbert.lean:144` | `Parallel` | `playfair` | **0 个实例**；Playfair 平行公理 | ⭐ **新** |
| A-18 | `RealLv00GeometryHilbert.lean:160` | `Continuity` | `archimedes` | **0 个实例**；⚠ **且结论为 `True` ⟹ 恒真、不约束任何东西**（退化，见 **B-32**） | ⭐ **新** |
| A-19 | `RealLv00GeometryHilbert.lean:160` | `Continuity` | `dedekind` | 同上（退化） | ⭐ **新** |
| A-20 | `RealIEEE754.lean:119` | `IEEERound` | `err_bound` | **唯一"填充点" `:511` 是反向转接**（`IEEERound → RoundOp`），**不产生 `IEEERound`** ⟹ 仍是假设 | ✅ B-2 |
| A-21 | `RealIEEE754.lean:119` | `IEEERound` | `idem` | 同上 | ✅ B-2 |
| A-22 | `RealIEEE754.lean:119` | `IEEERound` | `monotone` | 同上 | ✅ B-2 |
| A-23 | `RealIEEE754.lean:119` | `IEEERound` | `sign_preserve_pos` | 同上 | ✅ B-2 |
| A-24 | `RealIEEE754.lean:119` | `IEEERound` | `sign_preserve_neg` | 同上 | ✅ B-2 |
| A-25 | `RealIEEE754.lean:119` | `IEEERound` | `subnormal_bound` | 同上 | ✅ B-2 |
| A-26 | `RealIEEE754.lean:324` | `IEEEDirected` | `down_le` | **0 个填充点**；`extends IEEERound` 的子结构，**全库无构造** | ⭐ **新** |
| A-27 | `RealIEEE754.lean:324` | `IEEEDirected` | `le_up` | 同上 | ⭐ **新** |
| A-28 | `RealIEEE754.lean:324` | `IEEEDirected` | `abs_zero` | 同上 | ⭐ **新** |
| A-29 | `RealEvalBridge.lean:190` | `PrimApprox` | `δ_nonneg` | **0 个填充点**；四个超越原语的误差数据外置 | ✅ B-7 |
| A-30 | `RealEvalBridge.lean:190` | `PrimApprox` | `exp_pos` | 同上 | ✅ B-7 |
| A-31 | `RealEvalBridge.lean:190` | `PrimApprox` | `exp_close` | 同上（`exp` 误差界） | ✅ B-7 |
| A-32 | `RealEvalBridge.lean:190` | `PrimApprox` | `log_close` | 同上（`log` 误差界） | ✅ B-7 |
| A-33 | `RealEvalBridge.lean:190` | `PrimApprox` | `cos_close` | 同上（`cos` 误差界） | ✅ B-7 |
| A-34 | `RealEvalBridge.lean:190` | `PrimApprox` | `sin_close` | 同上（`sin` 误差界） | ✅ B-7 |
| A-35 | `RealMixedPrecision.lean:147` | `FPAdder` | `eps_nonneg` | **0 个填充点**；浮点加法误差公理（B-26 已指其为第 4 个复制体，**但未给字段数**） | ⭐ **新（字段级）** |
| A-36 | `RealMixedPrecision.lean:147` | `FPAdder` | `eps_le_one` | 同上 | ⭐ **新（字段级）** |
| A-37 | `RealMixedPrecision.lean:147` | `FPAdder` | `err_bound` | 同上（**每步加法的相对误差界**） | ⭐ **新（字段级）** |
| A-38 | `RealGeneralizationBound.lean:61` | `GeneralizationBound` | `hdelta` | **0 个构造点**（全库仅 `:75` 作消去用） | ⭐ **新**（B-11 悬置） |
| A-39 | `RealGeneralizationBound.lean:61` | `GeneralizationBound` | `sound` | ⭐ **把"泛化界成立"整个数学内容作为单字段**；无填充者 | ⭐ **新**（B-11 悬置） |
| A-40 | `RealCausalDoCalculus.lean:115` | `FinSCM` | `p_nonneg` | 该结构**有** 1 个构造点（`:352` `doModel`），⚠ **但该构造点原样搬运原 `M.p`，不产生新证明** ⟹ 仍是假设 | ⭐ **新** |
| A-41 | `RealCausalDoCalculus.lean:115` | `FinSCM` | `p_sum` | 同上 | ⭐ **新** |
| A-42 | `RealCausalInference.lean:137` | `BinSCM` | `pX_nonneg` | **0 个构造点**；三个噪声分布的非负/归一 | ⭐ **新** |
| A-43 | `RealCausalInference.lean:137` | `BinSCM` | `pY_nonneg` | 同上 | ⭐ **新** |
| A-44 | `RealCausalInference.lean:137` | `BinSCM` | `pZ_nonneg` | 同上 | ⭐ **新** |
| A-45 | `RealCausalInference.lean:137` | `BinSCM` | `pX_sum` | 同上 | ⭐ **新** |
| A-46 | `RealCausalInference.lean:137` | `BinSCM` | `pY_sum` | 同上 | ⭐ **新** |
| A-47 | `RealCausalInference.lean:137` | `BinSCM` | `pZ_sum` | 同上 | ⭐ **新** |

> ⚠ **其中 `BinSCM` / `GeneralizationBound` / `IEEEDirected` / `FPAdder` 四个结构
> 【全库无任何构造点，且此前从未被任何登记表提及】** ⟹ **这是本节的净增量**。
> ⚠ **`Continuity`（A-18/A-19）与 `FinSCM`（A-40/A-41）两类性质不同**：
> 前者是**退化空洞**（恒真），后者是**被搬运而未证明**（见 B-32、B-30 说明）。

---

## C 类：**已知的降级 / 未做**（索引式引用）

⚠ **不重复整篇** —— `CORRECTIONS.md`（2624 行）与 `STYLE.md`（774 行）已是权威源。
本节**只给索引**，便于从"偏离"视角检索。

### C.1 `CORRECTIONS.md`（B1–B70）中**属于偏离登记**的条目

| # | 条目 | 偏离类型 | 为什么可接受 |
|--:|:--|:--|:--|
| **C-1** | **`CORRECTIONS B53`**（`:1552`）—— **19 条 vacuity 链** | **不可满足前提**（新失败类） | `:1588-1590` **逐字**：「**"不可满足的前提"是一个独立且更隐蔽的失败类型**：它比"假设即结论"更难查 —— 因为**结论与假设不同**（不触发重言式判据），**语句也非假**（空洞为真），**且 Lean 会照常接受**」。⭐ **这是本项目发现的最重要的偏离类之一** |
| **C-2** | **`CORRECTIONS B62`**（`:2024`）—— **11/12 检查器未接门禁** | **Governance**（元级） | `:2043` **逐字**：「**它本身不产生错误，但它让所有其它错误类静默传播**」。`:2045-2052` 列出 `lake build` **拦不住**的 6 类。`:2054`：「项目的"完成"信号是"编译通过"，而**编译通过不蕴含任何一条完整性属性**」 |
| **C-3** | **`CORRECTIONS B63`**（`:2088`）—— **孤岛根因归因** | **Governance** | `:2106-2107`：「**174 个零入边模块里，173 个在 `roots` 中、151 个有 `.olean`** ⟹ 它们编译正常，**只是没人消费**」。`:2092`：「问题不是"没证明"，而是"**没接线**"」。⭐ 分类维度选对的例证 |
| **C-4** | **`CORRECTIONS B66`**（`:2291`）—— **时态层 MVP 落地 + 三条对提案的核验** | **System boundary 落地** | `:2297`：交付 **364 行 / 37 声明 / 0 sorry/axiom/admit**。⭐ 三条核验见本文件 **A4 / A2 / A3** 与 **C-6** |
| **C-5** | **`CORRECTIONS B39`**（`:776`）—— **假报内核验证** | **Governance / 声称层** | `:776`：「【**假报内核验证·最严重一类**】docstring 声称的定理在文件里**根本不存在**」。⚠ **这正是本项目硬纪律"用名字的存在性代替定理的存在性已有 6 次失误"的同族** |
| **C-6** | **`CORRECTIONS B69`**（`:2425`）—— **A6 检索：FCA 的 context 扩展** | **Upstream divergence** | ⭐ `:2459-2463` **决定性 mathlib 反证**（逐字）：`Mathlib/Order/Concept.lean:19-22` —— 「Concept lattices are usually defined from a *context* … but the type of `r` determines `α` and `β` already, so **we do not define contexts as a separate object**」。⇒ **mathlib 明确决定不把 context 作为独立对象** |
| **C-7** | **`CORRECTIONS B43`**（`:1051`）、**`B57`**（`:1769`）—— 无 olean 模块 | **Resource / 覆盖面** | `B57`：「26 个"无 olean"模块**不共享单一成因**」⟹ ⚠ **不可归因为单一原因**（反过度归因） |
| **C-8** | **`CORRECTIONS B6/B23/B24/B25/B29`**（`:82`/`:317`/`:345`/`:364`/`:468`） | ⭐ **Upstream defect（反向）** | ⭐ **这五条是"我方判断为缺失、实际上游有"** —— `B24:345` 自述「【工具可用性更正·**第三次**】Fermat 小定理并非缺失，只是**名字不同**」；`CORRECTIONS.md:520` 称之为「**"以名字判有无"（本次是第 6 次）**」。⇒ ⭐ **这是与 `lean4lean` 的 `bugs-found.md` 同构的一类**：**上游没有缺陷，是我的检索有缺陷** |
| **C-9** | **`CORRECTIONS B2`**（`:35`）—— **已撤回的条目本身** | **自我更正留痕** | `:37-38` **逐字**：「本条原标题……是错的，现予撤回。**保留原文与撤回理由**，因为"**诚实登记表里出现过一条假条目**"本身必须留痕——**这比悄悄删掉它更诚实**」。⭐ **这是登记表自身的可信度机制** |
| **C-10** | **`CORRECTIONS C` 节**（`:493-536`）—— **44 行"其他重要诚实降级"** | **Scope / Resource** | 已按 6 类汇总（分析工具缺失 / 概率论缺失 / 常数保守 / 假设外置 / 范围裁剪 / 正性假设）。⚠ `:525` 的 **`sSup` junk 值**（对应 **B-18**）与 `:519` 的 **mathlib 4.14 无 `Real.erf`**（**版本阻塞**）是本节的代表条目 |
| **C-11** | **`CORRECTIONS` 的"已过时"条目**（`:508`、`:520`、`:528`、`:530`） | ⚠ **登记表自身的偏离** | `:530` **逐字**：「登记表**自身**会因"补缺口的文件**不回落源条目**"而出现**同对象双条互斥**——保留此条（划掉而非删除）以**留痕**」。⭐ **这是"登记表与代码脱节、无闭环"（根因 3）的自证实例** |

### C.2 `STYLE.md` / 其他登记表中**属于偏离**的条目

| # | 条目 | 位置 | 偏离类型 |
|--:|:--|:--|:--|
| **C-12** | **`STYLE.md §5.4`** 要求的诚实标注约定 | `STYLE.md:19-24`（文件骨架模板） | **Governance**：模板强制「**诚实边界**（本文件不证 / 不声称的）」段 + 「无 sorry/axiom/admit」句 |
| **C-13** | **`WARNINGS.md`** 的"为何其余不清" | `WARNINGS.md:43-45`、`:60` | **Resource**：`try 'simp' instead of 'simpa'` 12 条「**位置敏感，未做**」；`tac1 <;> tac2` 「**语义敏感，未做**」。`:8-9` v13 实测 **344 模块 / 0 error / 236 warning** |
| **C-14** | **`WARNINGS.md:41`** 的 3 文件回滚 | `WARNINGS.md:41` | **Resource**：`RealCrossAttention` / `RealDynamicRoute` / `RealLinearAttention` **因 `omit` 插入落点错位而回滚** |
| **C-15** | **`HONESTY-COVERAGE.md:24-26`** 标注覆盖率 —— ⭐ **本文档内 `9.2%` / `6740` / `618` 三个数字的【唯一权威索引条目】** | `HONESTY-COVERAGE.md:20-31` | ⭐ **Governance**：**6740 条声明中 618 条（9.2%）**带关键词；**236 个文件有声明但 0 条标注**。⚠⚠ **该文件`自己警告`（`:6-10`，本行加粗为本文档对该数字的规范引用点）：「This measures the labelling convention, not correctness」**（**度量的是标注惯例，不是正确性**）⟹ **凡引用 9.2% 处必须同句附此警告**；同见 `DIVERGENCES.md:44-50` |
| **C-16** | **`RealReversibilityBoundary.lean:45`** | `:45` | **Scope**：「**没有**写出 `canonicalize` 函数及其三条性质」 ⟹ 与 `RealCompileExtractClosed.lean:503`、`RealTemporalLayer.lean:507` **三处独立登记同一未做项** |
| **C-17** | **`RealROME.lean:16`** | `:16` | **Scope**：「"其余保持"的高维近似部分（**经验**）**明确非定理**，留给验证器」 ⟹ 对应残留问题 §4「ROME"其余保持"原理上非定理（**经验命题**）」 |
| **C-18** | **原提案的两处**【已被机器否证】 | `RealTemporalLayer.lean:438-473` | ⭐ **Upstream defect（提案侧）**：提案 §拓展 2 给的 `element_concept_complement` **证明体编译失败**（`:448`「实测：该证明体【**编译失败**】……报 3 条 `unsolved goals`」）；提案 §拓展 3 的 `em` 证法失败（`:475-501`）。⚠ `:470-473`：「本发现**只针对提案稿件里的那一行证明体**，**不影响**提案的**数学判断**」 |

### C.3 ⭐ 通过 A6/B69 得到的**上游结构性分歧**（真正的 "Divergences from upstream"）

> ⚠ 这一节最贴近 `lean4lean` 原范式（**与参照实现的有意分歧**）。

| # | 分歧 | 证据 | 处置 |
|--:|:--|:--|:--|
| **C-19** | **mathlib 不把 context 作为独立对象** | `Mathlib/Order/Concept.lean:19-22`（逐字见 C-6） | ✅ **接受上游**：LATTICE 的 `RealTemporalLayer` 沿用 `{O A : Type*}` 风格（`RealFCA.lean:34`/`:37` 同形） |
| **C-20** | **FCA 规定"同一名字跨 context = 同一对象"（unique name assumption）** | Priss 2006 §4.3 逐字（`CORRECTIONS.md:2432-2434`） | ⚠ **与体系对立**：体系认为身份**由目光/论域决定**。⇒ ⭐ **这是【真】分歧**，但其性质是**理论立场不同**，不是实现 bug ⟹ **显式登记而非"修复"** |
| **C-21** | **mathlib 4.14 无 `Real.erf`（版本阻塞）** | `CORRECTIONS.md:519` | ⏳ **等待上游**（`MIGRATION.md`） |
| **C-22** | **README 口径纪律：不得把"mathlib 缺 X"当长期定位** | `lean/README.md:10-13` | ⚠ **逐字**：「"mathlib 缺 X"只在**我们钉住的 4.14** 成立 —— **mathlib master（2026）已新增 Hoeffding / Azuma–Hoeffding / 次高斯 / KL / DPI**。任何把"上游缺 X"当作**长期定位依据**的说法都会**随上游更新失效**」 |
| **C-23** | ⭐⭐ **`xorC` / `real_xorC` 只在二值化域 `{0,1}` 上成立（全域为假）** | `CombinatorsXorNot.lean`（`xorC_eq_zero_iff_on_domain`）、`RealCombinators.lean`（`real_xorC_eq_zero_iff_on_domain`） | ⭐ **Explicit hypothesis / Scope**：XOR 的零化 `⟺` **必须**带定义域限制 `a ∈ {0,1} ∧ b ∈ {0,1}`。⚠ **去掉它后命题为假**，机器验证反例：`xorC 0 2 = 5 ≠ 0` 而「恰好一个为零」为真（`xorC_offdomain_counterexample` / `real_xorC_offdomain_counterexample`）。⭐ **根因**：XOR 的满足集 `({0}×ℝ*) ∪ (ℝ*×{0})` **不闭**（`(0, 1/n)` 在集内、极限点 `(0,0)` 在集外），而 `andC` 的零集 `{(0,0)}`、`orC` 的零集 `({0}×ℝ) ∪ (ℝ×{0})` **都闭** ⟹ ⭐ **XOR 是既有组合子中唯一【零化范式不适用】的算子**。⚠ **此条同时更正 `00-SYNTHESIS.md:96-106` 的判词**：它只说"XOR 非单调/非负损失类"，**未指出真正的障碍是零集不闭** |
| **C-24** | ⭐ **NOT 走的是 De Morgan 路线，不是零化路线（两条路线【并存互补】）** | `RealImplication.lean:64`（`not_andC_zero_iff`）、`:82`（`not_orC_zero_iff`）**对** `CombinatorsXorNot.lean`（`notC`）、`RealCombinators.lean`（`real_notC`） | ⭐ **Explicit hypothesis / Scope**（P1-3 验收标准 ① 所要求的登记）：既有的 NOT "内容"是**元层重写**（把 `¬(x = 0)` 翻译成 `≠` 的析取），**不产生组合子值**；⚠ **且「非零集」不闭 ⟹ `¬` 不可能以零化等式表达**（与 C-23 同源）。⇒ ⭐ **LATTICE 的 NOT 分裂为两条【不可合并】的路线**：**(i) De Morgan 路线**管「非零判定」（`RealImplication.lean`）；**(ii) 二值化域零化路线**管「取反」（`real_notC`，本文件）。⚠ **两者不是重复实现**：`real_notC_zero_and_self_zero_exclusive` 所断言的「NOT 与恒等互斥」**不可能**由 (i) 给出（它不产生值） |
| **C-25** | ⭐ **XOR 与 NOT 【同源】，按 P1-3 验收标准 ③ 合并为一条登记** | `CombinatorsXorNot.lean`（`notC_eq_xorC_zero`）、`RealCombinators.lean`（`real_notC_eq_real_xorC_zero`） | ⭐ **Governance（去重）**：两条互逆关系成立 —— `notC a = xorC a 0`（NOT 是 XOR 与常量 `0` 的复合）与 `xorC` 的定义（XOR 由 NOT+AND+OR 复合）。⇒ ⭐ **二者共享同一定义域障碍**（都需要 `{0,1}`），故 **C-23 与 C-24 的"二值化域"部分是同一数学事实的两个入口**，**不单独立项**。⚠ **但仍分两条登记**，因为它们的**上游对手不同**（XOR 对手是"AND/OR 范式"，NOT 对手是"De Morgan 路线"） |
| **C-26** | ⚠⚠ **零化编码的固有陷阱：`xorC` 的【零集】编码 XOR，而其【取值】是 XNOR** | `CombinatorsXorNot.lean` §六（`xorC_value_table_on_bool` / `xorC_zero_table_on_bool`）、`RealCombinators.lean`（`real_xorC_value_table_on_bool` / `real_xorC_zero_table_on_bool`） | ⭐⭐ **本次新增的判读规律（从一处真事故中得来）**：`xorC 0 0 = 1`、`xorC 1 1 = 1` ⟹ **取值表是 XNOR**；而 `xorC a b = 0` 在 `(0,1)`/`(1,0)` 成立 ⟹ **零化表是 XOR**。⚠ **根因**：`orC X Y = X·Y` 的**零集**是「`X=0 ∨ Y=0`」（**析取**），而其**数值**「两者都非零时为非零」是**合取**的代数像；两者叠加恰好把 XOR 翻成 XNOR。⚠⚠ **本条的来源**：初稿的 `notC a = xorC a 1` **被 `decide` 否证**（报 `tactic 'decide' proved that the prop…`），coordinator 逐点复现确认。⇒ ⭐ **纪律**：**凡用「组合子取值相等」陈述逻辑等价，必须先在 `{0,1}` 上【逐点验算全部四种情形】**（⚠ 只验一种会漏 —— 本例在**两个点上都反**）；**正确形态是零化命题之间的 `↔`**。⭐ **这是 B222.2（`X ↔ X` 空洞）的对偶面**：「看着像显然等式的 `f a = g a` **实为假**」，而 `decide` 是唯一可靠仲裁者 |
| **C-27** | ⭐⭐ **P1-4：`concept ↦ constraint` 语法侧桥 —— 存在但是【部分】的，全域版本为假** | `_r5_p14_syntax_bridge.lean`（**探针，未进 roots**）：`conceptToConstraint`（`:106`）、`conceptToConstraint_preserves_extent`（保义定理）、`conceptToConstraint_sat_iff`、`no_constraint_has_extent_pair` / `conceptToConstraint_side_condition_is_necessary` | ⭐ **Explicit hypothesis / Scope**：语法侧桥**不是**"不做"，而是**只能做成带侧条件的部分函数**。⚠ **全域版本 `concept ↦ constraint` 为假**，机器验证反例：`O' = {0,1}` 不能是任何 `RealConstraint` 的解集（由其两成员强迫 `a = b = 0`，而零约束满足**所有** `x`，故 `2 ∈ extent` 与该等式矛盾）。⇒ ⭐ **这正是 mathlib 侧同名分歧的镜像**：`Mathlib/Order/Concept.lean:19-22`「**we do not define contexts as a separate object**」（逐字见 **C-6**、处置见 **C-19**）—— 上游**不把 context 作独立对象**，**故 LATTICE 亦无可供全域翻译的 context 载体** ⟹ ⚠ **C-19 的"接受上游"决定【同时】决定了语法侧桥只能是部分的**。⭐ **依赖关系（本轮新增）**：C-27 **不是**新分歧，而是 **C-19 在语法侧的推论**；登记它是为了**防止下一轮把它当"未做的缺口"立项**。⚠ **与 P1-1（FCA soundness）正交**：本桥**语义方向相反**（concept → constraint，非 weights → concepts），**不引用** `SoundAbstract`/`α`/`γ`/行为函子 ⟹ **不受 P2-1 决断影响** |
| **C-28** | ⚠⚠ **P1-5：`VerifyLoopProgress.repair` 是恒等函数 ⟹ 三条定理【平凡真】** | `VerifyLoopProgress.lean:68`（`def repair (_c) (x) := x`）、`:97`（`repair_preserves`）、`:107`（`loop_preserves_semantics`）、`:117`（`verify_stable`）；⭐ **机械证据**：`:83` `iterateRepair_eq_self`（恒等下迭代**恒等于输入**） | ⭐ **Governance / Scope（"名字承诺多于陈述"的机器可验证实例）**：`repair_preserves` 证明体展开后**逐字是 `h` 本身**（`fun h => h` 形态，**B222.2**），`loop_preserves_semantics` 经 `iterateRepair_eq_self` **结论项与假设项是同一个项**，`verify_stable` 即 `rfl`。⚠ **真值不依赖 `repair` 的定义**：把 `repair` 换成 `fun _ y => y + 1`，对约束 `⟨1,0⟩`（解集 `{0}`）**三条全假**（`_r5_p15_repair.lean` `shift_by_one_fails_to_preserve`）⟹ ⭐ **唯一被真正检验的是 `ConstraintSat` 可展开 + 归纳骨架良构**。⭐ **处置（按 P1-5 验收标准 ③）**：**维持恒等**，但**已在文件头与每条定理处【显式标注"平凡真"】**，并新增 `iterateRepair_eq_self` 使平凡性**成为定理而非断言**；另新增 `repair_fixpoint_iff_stationary`（**唯一不含平凡性**的结果）。⚠ **一般收敛定理【未证】，理由是结构性的**：`LinearConstraint` 上的 `ConstraintSat` **未配备任何序/度量** ⟹ "下降性"无量可依 ⟹ **这是"缺一个度量"，不是"缺一个难定理"**。⚠ **已有但受限**：`VerifyLoopConvergence.lean:73 even_loop_converges` 用**真实**修复器 `repairEven`，**但只对"偶数判定"一个实例** |
| **C-29** | ⚠⚠ **`lean/_r9/` 是【未登记的偏离源】：19 个 `.lean` 为【过期副本】，其中 4 个在顶层被订正后未同步；且宣传【已被删除的幽灵定理名】** | `_r9/` 共 **68** 文件（**49 已跟踪**：19 `.lean` + 13 `.olean` + 19 `.log` + 15 `.txt` + 2 `.md`）。⭐ **4 个已漂移副本**（sha256 与顶层不同）= `RealConversionCategorical` / `RealConversionInformation` / `RealConversionMinimality` / `RealConversionRobustness`；其余 15 个**逐字节相同**。⚠⚠ **它们仍宣传被 `B314`/`B318` 删除的幽灵名** —— 机器实测 `weightFunctor_id` / `minimal_element_iff` / `fibre_mul_card_le` / `layerOut_lipschitz_in_x` 在 **511 个 roots 模块中【零声明】** ⟹ ⭐ **`doc/19-dev-session-startup-prompt.md:210` 的「错误传染源」诊断【机器证实】**。⚠ 本项**已被 `CORRECTIONS.md` B287.1–B287.3 部分覆盖**，但 B287 记的「19 个均为逐字副本 ⟹ 可删」**今日已不成立**（4 个已漂移） | ⭐ **C 类（已发生）＋ 显式【永不构建】条款**：`lakefile.toml` 的 **`srcDir = "."`** ⟹ 模块名解析到**顶层同名文件** ⟹ **`_r9/` 副本被遮蔽、从不参与构建**（实测 **`.lake/build/lib` 下无任何 `_r9` 产物**）。⚠ **因此：① 绝不要把 `_r9/` 加进 `roots`（那不会使它构建）；② 绝不要据 `_r9/` 的文本接线或引用其名字（多为幽灵名）；③ 该状态【必须保持】：`_r9/` 仅作历史快照，其内容不得作为规格源。** ⚠ **⚠ 订正（B409）：本条原写「未被 gitignore」，归因有误** —— 真因是 **git 忽略规则对【已跟踪】文件永不生效**（`.gitignore:37` 为 `lean/_*`，对新建未跟踪文件 `check-ignore` 返回 **exit 0**，即规则确实命中）；这 49 个文件系 force-add 纳入 ⟹ **不要去改 `.gitignore`** | **Scope / Governance** |
| **C-30** | ⭐ **`extractLayer` 的「重复定义」是【误判】—— 实为类 (iv) 合法影子副本，**已核查、无需治理** | 全库**仅有 1 个**裸 `def extractLayer`（`RealCompileExtractClosed.lean:99`）。`RealExtractSurjectivity.lean:143` 声明的是 **`extractLayer'`（带撇，异名）**，且 `:150 theorem extractLayer'_eq_extractLayer : extractLayer' = extractLayer := rfl` **给出 `rfl` 桥** ⟹ 按本项目四分判据属 **(iv)「有据影子副本」，合法**。⚠ 正本 `extractLayer` 有 **39 个 importer**，而影子所在文件 `RealExtractSurjectivity` 的 **importer = 0**（其自身即孤儿）⟹ **合并收益 ≈ 0、风险非 0**。⚠ **本条的由来**：2026-09-27 执行轮曾据「3 个 roots 模块各自定义、定义体逐字相同」立项，**该读数系扫描器【丢弃块注释内换行】所致的假阳性**（行号系统性前移，且把 docstring 代码块里的**示例文本**误计为**真实声明**）。⚠ 同时 import 声明模块**不会**冲突（实测**0 个**模块 import ≥2 个），因为名字**不同** | ⭐ **C 类（已核查的事实）＋ 显式【不合并】条款**：**① 不得**以「重复定义」为由合并或重命名 `extractLayer` 与 `extractLayer'`；**② 不得**删除 `RealExtractSurjectivity`（它是 `rfl` 桥的所在地）；**③ 若日后**出现**同名**（而非带撇）的第二处 `def extractLayer`，则本条失效、须重新立项。 | **Scope / Governance** |
| **C-31** | ⚠⚠ **`hreach` 的边界缺陷【存活】：B53 的修复【有效但不完整】** | `DIVERGENCES.md` **B-13**（本文件 `:143`）记：旧形态 `hxdom : ∀z, c ≤ ‖z‖` 与 `hc : 0 < c` 因 `z := 0` **矛盾** ⟹ 不可满足、定理空洞；`hreach` 是**有意传入的可满足前提**。⚠⚠ **但 `hreach` 以【同一见证】【同一机制】失败**：① `hreach` 的量词是 `∀ j ≤ m`，**自 `j = 0` 起**；② `ChainFwd Fs 0 x = x`（`RealChain.lean:36`）⟹ **`j = 0` 访问的正是输入本身**；③ `h = 0` 时括号项 `0 + SoftmaxAttnOp 0 + W 0 = 0`（`V i` 与 `W` 皆是线性映射）⟹ `hreach` 在该点读作 `c ≤ 0`，与 `hc : 0 < c` **矛盾**。⭐ 更强：残差沿射线**精确 1-齐次**（`softmax` 对输入**正**缩放不变）⟹ **失败集是原点的一个【开球】**（`‖x‖ < c/‖I+W‖`），**不是孤立点**。⇒ ⭐⭐ **该修复把「处处不可满足」缩小为「原点小球内不可满足」——边界缺陷存活。**⚠ **但必须同时陈述另一半**：`hreach` **仍然可满足**（实测 3990/4000 随机实例满足 `min_j ‖residual‖ > 0.05`）⟹ **定理不是处处空洞**。⚠ 且项目自陈的见证（恒等链 + `x = c•e₀`）**只在恒等链上成立** —— 它证的是**公式可满足**，**不是「真实 transformer 块满足 `hreach`」** | ⭐ **C 类（已核查的事实）＋ 显式边界条款**：**① 不得**把 B-13（`:143`）读作「缺陷已消除」；**② 引用 `hreach` 时必须同时说明「它在原点附近不可满足」与「它整体可满足」两条**；**③ 不得**以「恒等链见证」声称真实模型满足 `hreach`；**④ 若日后**有载体提供 `I + W` 的**可逆性 / 最小奇异值下界**，则本条可升级为定理（见 B410）。 | **System boundary / Explicit hypothesis** ⭐⭐ **机器已固化（B410 轮）**：本条原为**结构性论证**，现已有**机器验证的定理** —— `lean/RealHreachConditional.lean` 的 `hreach_unconditional_false : ∀ {n k} [NeZero k], ¬∃ c, 0 < c ∧ ∀ h, c ≤ ‖h + SoftmaxAttnOp 0 negActivation h + 0 h‖`（**协调者对真模块跑 `#print axioms` → `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`**）。⚠ **且已证【条件版】需 `M + Lw < 1`**（`residual_lower_bound`），**而该条件对真实 transformer 一般不成立**（值映射与 FFN 权重算子范数通常 ≥ 1，块不是压缩映射）⟹ **条件版【不】establish「真实块满足 `hreach`」**，它给的是「非退化输入上的下界」。⚠ **真正的结构障碍**：`I + W` 奇异时**无载体**提供 `σ_min` 下界（`RealSVD.lean` 有 SVD 结构但**无 `σ_min` 引理**）—— 条件版正是**绕开**它以代替谱估计。⚠ **故 `hreach` 的最终状态 = 【仍开放】，且其升级路径已精确化**：需 (i) `σ_min(I+W)` 下界载体，或 (ii) 一个对真实模型成立的替代条件（替换 `M + Lw < 1`）。 |

---

## X 类：⭐⭐ **明确不做**（Explicit non-goals / 决策否定）
<!-- lattice-register: name=DIVERGENCES.md sec X; row_re=^\|\s*\*\*X-(\d+)\*\*\s*\|; want=1..15; end=### ⭐ X 类的净结论（一句话） -->

> ⭐⭐ **本类存在的唯一目的是【防复活】**。
> **依据**：`A1-可执行待办清单-按优先级.md:264` **逐字**：
> 「**这一节本身是本清单的交付物之一**：ChatGPT 在 15 轮里反复推销，
> **若不写下"不做"的判据，下一轮审计会再次把它当缺口立项**。」
>
> ⚠⚠ **X 类不属于 A/B/C 任何一类**（这是登记维度问题，不是编号问题）：
>
> | 类 | 语义 | 与 X 的区别 |
> |:--|:--|:--|
> | **A** | 体系边界 —— **原理性不可内证** | X 是**工程/架构决策**，**可内证、可执行** |
> | **B** | **既有**的显式假设（从代码**提取**） | X 的方案在代码里**根本不存在** |
> | **C** | **已知的降级 / 未做**（**已发生**） | ⭐ **C 是"已发生"，X 是"未发生且不应发生"** |
>
> ⚠ 把 X 塞进 C 会让"降级"与"决策否定"混同 —— 正是本文档 §分类维度 所反对的"分类维度选错"。

### X.0 本类的判据纪律（**每条必须有可机器验证的判据**）

⚠ 本类**拒绝**"我觉得不需要"式的理由。每条**必须**满足三选一：
**(a) grep 计数**（并合 `0 命中 ≠ 不存在` 的复核要求：**换 ≥3 组关键词**）；
**(b) 成文 ADR / 逐字自述引文**（须给 `file:line`）；
**(c) 项目自证的否定定理**（机器已验证的 `False`/`¬`）。

⚠⭐ **本类**逐条经 R3 代理独立复核**** —— 复核中发现**用户清单里 7 条的原始判据有误**
（计数错 / 引文位置错 / 引文根本不存在）。**下表登记的是【复核后的判据】，不是清单原文。**
⚠ **凡与清单原文数字不符处，一律在"复核订正"列写明。**

| # | 不做项 | ⭐ 复核后的判据（可机器验证） | 复核订正（与清单原文的差异） |
|--:|:--|:--|:--|
| **X-1** | **三层嵌套 IR**（Concept/Logical/Algebra/Neural IR） | ⭐ **(b) 成文 ADR**：`research/uir/UIR-Spec.md:258-262` —— 「### 决策记录（ADR 式）… **备选**：① `.lv`/约束图为 IR（**否决**：改宿主、缺权重侧字段、难序列化/审计）」；`:251` 理由逐字「以 `.lv`/约束图为 IR 意味着**修改 Lv-00 的宿主语言与内部数据结构**，违反边界」。＋ **(a) grep**：`RepIR`/`LatticeIR`/`LIR`/`NIR`/`NeuralIR`/`LogicIR`/`AlgebraIR`/`ConceptIR` 于 `lean/*.lean` **全为 0** | ⚠ 清单说"ADR 在 §10"—— **§10 是「IR 三候选权衡」标题，ADR 是其子标题 `:258`**；结论不变 |
| **X-2** | **`structure Pass` / `CompilerPass`** | ⭐ **(a) grep**：`structure Pass` / `class Pass` / `CompilerPass` 于 `lean/*.lean` **全为 0**；⭐ **命名碰撞**：`Pass ` 命中**全为 GNN 族的 `msgPass` 族**（`RealGNN.lean` 等）—— ⚠⚠ **订正（E4 复核）**：`msgPass` 前缀的变体**不止 `msgPass` 一个**，还有 `sparseMsgPass`/`uniformMsgPass`/`iterMsgPass`。若按"排除字面 `msgPass`"计数，残余 **59** 处（`RealGNNEquivariance` 12 / `RealGraphExpressivity` 45 / `RealOverSmoothingSharp` 2）；⭐ **按"`Pass` 前是 `Msg` 语义前缀（大小写不敏感）"计数，残余 = 0** ⟹ **本条的结论（无 `Pass`/`CompilerPass` 结构）成立**，⚠ **但"非 `msgPass` 的 `Pass ` = 0"这一表述只在后一口径下为真** —— 登记时必须写明口径，否则会被下一轮复核判为"0 命中"式的错。＋ ⭐ **(c) 项目已有更强的**：`RealConversionCategorical.lean:137 compile_galoisConnection`、`:155 compile_galoisConnection_galois`（**真 `GaloisConnection` 结构**）、`:175 compileExtractEquiv : ConstraintSet ≃ Layer`（**含 `left_inv`/`right_inv`**）、`:182 compile_extract_adjunction_iso` ⟹ **Pass 只能单向，而项目有双向 + 等价** | ⚠⚠ **清单说"`Pass ` 94 命中、全在 `RealGNN.lean:57`"—— 实测计数 146、横跨 4 个文件**（`RealGNNEquivariance`/`RealGraphExpressivity`/`RealGNN`/`RealOverSmoothingSharp`）。⚠ **清单引的 `RealConversionCategorical.lean:20-21` 是 docstring 表格，不是定理**；真定理在 `:137/:155/:175/:182` |
| **X-3** | **`class Representation` / `structure Behavior` / 统一 Semantic Layer** | ⭐ **(a) grep**：`structure Representation` / `class Representation` / `structure Behavior` / `class Behavior` / `SemanticLayer` / `structure Semantic` 于 `lean/*.lean` **全为 0**；补充 `统一语义层`/`统一对象`/`不做统一`/`拒绝统一` **均 0**。＋ ⭐ **(c) 项目自证**：`RealReversibilityBoundary.lean:228 semantic_layer_not_injective` —— **证明语义层【非单射】**，即"语义层不可作唯一载体" | ⚠⚠ **清单称"`RealCompileExtractClosed.lean:56-59` 有意拒绝"—— 该处实为「二、语法闭环：两侧互为逆映射」小节，是【正面陈述】。该"自驳斥证据"不存在。**⚠ 附：`Representation` **是项目名本身**（LATTICE = Representation Lattice）⟹ 概念混淆 |
| **X-4** | **Master Theorem / `lattice_correctness` / 五层 `≡` 等价链** | ⭐ **(a) grep**：`Master Theorem`/`MasterTheorem`/`lattice_correctness`/`五层`/`等价链` 于 `lean/*.lean` **全为 0**。＋ ⭐⭐ **(c) 项目自证空转**：`RealEndToEnd.lean:100 e2e_vacuous_composition` —— ⚠⚠ **真正的自驳斥在此**，`:37-44` 逐字：「它给假设起的名字是 `_h`（**下划线 = 有意不用**）… 证明体**逐字**就是 `symbolToWeight_correct cs x`，与 `ts`、与 `Extract ts cs` **完全无关** ⟹ "L1→L2→L3 的语义链路"作为【组合】是假的」 | ⚠⚠ **清单引 `RealConversionInformation.lean:26-28` 说"证其空转"—— 该处是 docstring【正面】摘要**（"② 是本文件的核心正面结论：`compileToLayer` 是单射 ⟹ 一个比特都没丢"），**方向相反**。⚠ **另注口径**：`RealEndToEnd.lean:101 compileToLayer_not_injective`（**非单射**）与 `:138 compileToLayer_injective`（**是单射**）**同文件并存** —— 二者不冲突（前者在 `Layer` 商意义 / 缩放自由度，后者在 `List` 层），⚠ **但登记时必须写清，否则未来审计会当矛盾重开** |
| **X-5** | **`structure Behavior {input,output,eval}` 作全库统一对象** | ⭐ **(a) grep**：`structure Behavior` 于 `lean/*.lean` = **0**。＋ ⭐ **(c) 项目自证的结构事实**：本文档 **B-31**（`DIVERGENCES.md` B.3 节，逐字）：「**全库 93 个结构名中，仅 26 个**曾被真正构造…**其余 67 个从不被构造，只作参数/字段类型出现**」⟹ ⭐ **再加抽象只会让"无填充者"的结构名单更长**（B.4 已量化：**95 个声明 / 312 字段中，47 个是"真假设"字段**） | ⚠ 清单说"93 结构名仅 26 被构造"—— ⭐ **逐字吻合，无需订正** |
| **X-6** | **`LatticeRepresentation.lean`** | ⭐ **(a) grep**：`LatticeRepresentation` 于 `lean/*.lean` = **0**（大小写不敏感亦 0）。＋ ⭐ **(c) 语义已分头证明**：`ConvertLinear.lean:69 convert_preserves_semantics`、`ConvertVectorLinear.lean:55 convertVec_preserves_semantics`、`SymbolToWeightCorrectness.symbolToWeight_correct` ⟹ **不需要一个聚合模块** | ⚠ 清单说三条是"`convert_preserves_semantics`/`convertVec_preserves_semantics`/`comboN_preserves`"—— ⚠ **归类错误**：`ComboN.lean:56 comboN_preserves` 是 **L0 组合子引理**（`EvenSat`/`sumEven`），**与 L2/L3 转换语义无关**；**真正的第三条是 `symbolToWeight_correct`** |
| **X-7** | **目录重构**（`Core/` `Representation/` `Compiler/` `Verification/`） | ⭐ **(a) 现状实测**：`lean/` 下 **无任何源码子目录**，`.lean` 文件**全部平铺于仓库根**（符合"物理扁平"状态）。＋ ⭐ **(a) grep**：`物理扁平`/`逻辑分层`/`目录重构` 于**全仓（含 `.md`）**= **0** ⟹ **"逻辑分层 + 物理扁平"是【未文档化的现状默认】，不是成文决策** | ⚠⚠ **清单引 `MIGRATION.md` 作依据 —— 该文件讲的是 mathlib 4.14→4.33 的 toolchain 迁移，与目录重构【完全无关】。** ⚠ **本条如实登记为"默认隐含而非成文决策"**，**不得**虚构一个 ADR |
| **X-8** | **`reachable` 谓词式【全局】定理**（⚠ **订正 B409**：本条限**编译链 `compileToLayer` 的全局可达性**；⚠ **编辑通道不属本条**，见复核订正列） | ⭐ **(a) grep**：`Reachable` 于 `lean/*.lean` = **5**（全部在 `RealConversionRoundTrip.lean`：`:226 def CompileReachable`、`:236 theorem compileReachable_iff`；⚠ **行号订正（E4 复核）**：原引 `:160`/`:166` 已失效，该文件现为 **377** 行）；`可达`/`IsReachable`/`unreachable` = **0**。＋ ⭐⭐ **(c) 项目自证其无分辨力**：`RealConversionRoundTrip.lean:231` 逐字自述「`CompileReachable c` ⟺ `c` 是**任何**约束（即**恒真**）。⭐ **这是一条否定性发现**」；`:236 compileReachable_iff` **已证其恒真**。另：`compileToLayer` 是**函数**（`= List.map convertVec`），**不是关系** | ⚠⚠ **清单说"`reachable` = 0 命中"—— 实测 `Reachable` 有 5 处、`reachable`(cs) 有 1 处**（散文）。**"不存在 reachable 谓词式全局定理"的结论仍成立**（唯一的存在物已自证恒真），⚠ **但"0 命中"的表述是错的**。＋ ⚠⚠ **订正 B409（2026-09-27）：本条的字面判据【已被推翻】** —— `RealEditToSymbolConstructive.lean:343 theorem editConstraint_reachable_iff_length`（**在 roots**）是 **reachable 命名的、谓词式（结论为 `↔`）、且【非恒真】** 的定理：⟹ 方向用 `List.length_zipWith`，作者 `:338-342` 逐字自登记「⟸ 接近 `rfl`，**但 ⟹ 方向不是**」。⇒ ⭐ **本条【限全局可达性】仍成立**：(c) 判据（`CompileReachable` 恒真 ⟹ 无分辨力）**未被触动**。⚠ **故本条【不删除】，只加边界**（依 §方法论纪律 3 反面义务）。⚠ **另：(a) 计数「`Reachable`=5」经复测【仍准确】**，**但该计数【不足以支撑】结论** —— 它漏掉了一个**不同名字**的定理：`RealEditToSymbolConstructive.lean:343` **完全不含 `Reachable` 字样** ⟹ **按名字计数【看不见它】**。⭐ **可复用判据：判「不存在某类定理」不能只靠关键词计数；必须做【声明级扫描】。** |
| **X-9** | **`ExactEq` / `ApproxEq` / `ObsEq` 等价分级** | ⭐ **(a) grep**：`ExactEq` = **0**、`ApproxEq` = **0**。＋ ⭐ **(c) 近似已有承担者**：`RealApprox.lean:27 ApproxOn`（`:= ∀ x, |x| ≤ X → |f x - g x| ≤ ε`，同文件 `:22 def Approx`）＋ `RealVerifierReliable`（其 `:18` 自述是 `ApproxOn` 的**采样版**） | ⚠⚠ **清单说 `ObsEq` = 0 —— 实测 `ObsEq` = 2**（`RealContinuationEquivalence.lean:179 def ObsEq`、`:185 obsEq_iff_eval_eq`；⚠ **行号订正（E4 复核）**：原引 `:123`/`:127` 已失效，该文件现为 **195** 行）。⚠ **但它是【延续等价】（λ 演算语境），与转换层的等价分级无关** ⟹ **"无三级等价分级体系"的结论仍成立，"`ObsEq`=0"的表述错** |
| **X-10** | **把 FCA 收进 `FCA/` 子目录 / 认为 FCA 服务于 LATTICE** | ⭐ **(b) 逐字自述**：`RealFCA.lean:19-20` 逐字「⭐⭐ **⇒ 关系已经反过来：不是「FCA 服务于 LATTICE」，而是「LATTICE 是 FCA 的一个应用实例」。**」；`:16-17` 佐证「它不是「关于 LATTICE 的定理」，而是「关于 FCA 的定理」」。＋ ⭐ **(a) 独立实测的 import**：A 层 11 模块（`RealFCA` / `RealFCAClosureOperatorLattice` / `RealFCACompleteLattice` / `RealFCAConceptLatticeAlgebra` / `RealFCADuality` / `RealFCAImplicationBasis` / `RealFCAManyValued` / `RealFCARoughSet` / `RealFCATriadic` / `RealTemporalLayer` / `RealUpDown`）**只依赖 `Mathlib` 与 `RealFCA`，零 LATTICE 耦合**（R3 独立读 `import` 行复核，非抄 `FCA-LAYERING.md`）。⚠ 无 `FCA/` 子目录 | ⭐ **清单判据成立**。⚠ 补：`FCA-LAYERING.md` 已登记为"逻辑分层，不是物理搬迁"，且其 §六-4 明写「**不要动 B 层**」 |
| **X-11** | ⚠ **`Behavior_D` 采样语义 —— ⭐ 本项【不是"不做"，是"已存在且更强"】** | ⭐ **(a) grep**：`Behavior_D` 于 `lean/*.lean` = **0**（该命名确实不存在）。＋ ⭐⭐ **(c) 等价能力已存在且更强**：`RealVerifierReliable.lean:41-45 verifier_reliable_clean`（`DeltaDense S δ Ω` + `SampledVerified f g ε₀ S` + **双侧 Lipschitz** ⟹ **全域** `∀ x ∈ Ω, |f x − g x| ≤ ε₀ + (L + L')·δ`）、`:73 verifier_error_vanishes`、`RealNonlinearCompile.lean:211 nonlinear_soundness_local` | ⭐⭐ **清单自己已要求"应从【缺口】改判为【已有】"—— R3 复核【同意】，三项引文逐条验证属实**，是本类**最扎实**的一条。⚠ **故本项登记语义为"非缺口（已存在）"，与其余 12 条的"不做"性质不同** |
| **X-12** | **`well-founded` 序（按 ChatGPT 的形态）** | ⭐ **(a) grep**：`WellFounded` 于 `lean/*.lean` = **13**（`RealGlobalConfluence.lean` 9 / `RealTreeRecursion.lean` 3 / `RealOptimalTransport.lean` 1）；`well-founded`(cs) = **0**。⭐ **(c) 形态判读**：13 处**全为局部用途** —— 重写系统终止性（`RealGlobalConfluence.lean`：`def Terminating := WellFounded (…)`）与子树递归（`RealTreeRecursion.lean`：`wf_children`）；**无一处**把 `WellFounded` 用作**全局判据** ⟹ ⭐ **"ChatGPT 的全局 well-founded 形态未被采用"成立**。⚠ **两处真身在别处**：验证回路收敛用**奇偶有限情形**（`VerifyLoopConvergence.lean:73 even_loop_converges`）；ε-终止用 `RealGLUTraining.lean:166 gd_epsilon_termination`（⚠ **行号订正（E4 复核）**：原引 `:141` 为大段 docstring 内的自语行，**真定理在 `:166`**；经 `RealADMM.lean:349` / `RealConvergence.lean:84 contraction_converges`） | ⚠⚠ **清单说"12 命中"—— 实测 13**（差异可能为快照时点）。⚠⚠ **清单说"项目走度量收缩/ε-终止（`VerifyLoopConvergence`）"—— 归属错**：`VerifyLoopConvergence` 是**奇偶有限情形**论证，`contraction`/`度量`/`ε`/`收缩` 在该文件均为 **0 命中** |
| **X-13** | **CEGIS** | ⭐ **(a) grep**：`CEGIS`/`cegis`/`counterexample-guided`/`synthesis` 于 `lean/*.lean` **全为 0**（大小写不敏感亦 0）。＋ ⭐ **项目【从未自称】实现 CEGIS** ⟹ ⭐ **"从未声称"的能力不是缺口，也不是降级** —— 登记它的目的是**防止下一轮把它当缺口立项** | ⭐ **清单判据成立**。⚠ 旁证：`counterexample`(77) / `witness`(90) 是**反例/见证**机制，**不是 CEGIS 综合回路** |
| **X-14** | ⭐ **P3-6：合并"六列单表"（文件/定义/theorem/当前强度/缺口/建议）—— 判定【不建】** | ⭐ **(c) 键结构实测**：见 `SIX-COLUMN-TABLE-DECISION.md` §2 —— `STATS.md` 键=**文件**（476 行/476 去重）；`DIVERGENCES.md` 键=**偏离 ID**（47 ID / 72 文件 ⟹ 1.53 文件/条目）；`CORRECTIONS.md` 键=**事故 ID**（238 个 `^## B<n>.` / 180 文件）；⭐ **`ASSUMPTIONS.md` 键=文件+行**（2481 条） | ⚠⚠ **清单判据（"六表分工优于单表"）：R5 复核【同意】，但理由必须替换** —— ⚠ **清单只引审计报告 12 §五.5 的"很轻"评价，那不是判据**。⭐ **实测判据是【键不匹配】**：四张表**有四种主键**（文件 / 偏离 ID / 事故 ID / 文件+行），**"文件"不是最小公共超键** ⟹ 合并**不是集成，是降维**。⚠ **量化损失**：`CORRECTIONS` **238 个事故条目中 119 个（50.0%）根本不引用任何 `.lean` 文件名**，74.4% 引用 ≤1；以 `STATS` 的 476 模块为左表，**318 行（66.8%）在后两列上无来源**（**假阴性**，非真阴性）。⚠ **另有语义塌陷**：`DIVERGENCES` B-25/B-26/B-28 的**全部信息量就是【跨文件重复】本身**，拆成 3 行恰好抹掉它。⭐ **同型先例（本项目已判过一次）**：`DIVERGENCES.md:40-54`「分类维度（为什么不用"理论/实现"二分）」—— ⭐ **"把不同意义类型压进一个维度 ⟹ 该维度失效"**，本条是**该先例的第二次应用**。⚠ **且可见性上零净增**：手写表**不在 `verify.ps1` 的重生成链上**（`STATS.md`/`ASSUMPTIONS.md` 在），前四列**下次 `verify.ps1` 即陈旧而无物更新它**。⭐ **翻案条件**（见 `SIX-COLUMN-TABLE-DECISION.md` §5）：(a) 四表改键为文件；(b) 降级为**脚本生成的纯指针索引** `REGISTER-INDEX.md`（⭐ **本条 R5【不反对】**，但那是**另一个产物**）；(c) 采用复合键 |

| **X-15** | ⭐ **多模态四轴**（图像/音频/视频编码器、跨模态对齐、视觉 token、模态融合） | ⭐ **(a) grep（13 组关键词，实测 @B447）**：`multimodal` / `Multimodal` / `MultiModal` / `VLM` / `image_encoder` / `ImageEncoder` / `audio` / `Audio` / `vision_encoder` / `VisionEncoder` / `modality` / `Modality` 于 `lean/*.lean` **全为 0**（12/13）。⭐ **唯一非零项 `CLIP` = 35 处，但经逐处核实全部是 `clipGradient`/`clipNorm`/`clip_bias_bound` —— DP-SGD 的【梯度裁剪】，与 Contrastive Language-Image Pre-training 无关** ⟹ **真多模态内容 = 0**。＋ ⭐ **(c) 主张链自证**：主张链四节点（L0 数据 / L1 token / L2 符号模型 / L3 权重）**均无模态属性** —— `tokenize : List Char → List CharToken`、`VectorConstraint : a:List Int, b:Int`、`Layer = List Int`，**没有任何一处带模态标签**。 | ⭐ **本条经三次独立建议（M04 §四 R5 / M09 发现 4 / U03 §(b)），零执行** —— 登记它本身就是「防复活」判据的第三次应用。⚠ **判定的关键区分（U03）**：「必须覆盖」**不是二分**，是**三种形态** —— ①**隐含承诺**（如约束解码：`doc/02:90` 逐字称 L2⇄L3 编译方向是「★唯一难点」，不覆盖则编译方向只有训练期落点）②**字面承诺**（如 ZeRO/FSDP：`doc/02:78` 逐字称 L3 =「任意 LLM（**不限规模**/厂商）」）③**点名项**（如 SFT+PPO：`README.md:80` P3 点名）。⭐ **多模态属【无承诺】类** —— 主张链无模态属性，**不覆盖则主张字面仍成立** ⟹ **登记为 X 类（不做），而非 C 类（降级）**。⚠ **X-15 与 X-3 的关系**：X-3 否掉的是「统一语义层」，X-15 否掉的是「为多模态扩链」；二者**独立**，不可互推。

### ⭐ X 类的净结论（一句话）

> **14 条中：13 条登记为"不做"（防复活），1 条（X-11）改判为"已存在（且更强）"。**
> ⚠⭐ **且 13 条里有 7 条的【清单原文判据】经复核有误**（计数错 4 条 / 引文位置错 3 条 /
> 引文根本不存在 1 条 / 依据文件无关 1 条）⟹ ⭐ **本表登记的是"复核后判据"**。
> ⭐ **这本身就是一条可复用的判读规律**：**清单的"0 命中"与"逐字引文"两项都必须独立复核**
> （合 `PROCESS.md §4.1` 的"读数与它描述的对象不一致"家族）。
> ⚠ **补 X-14（R5/P3-6）**：清单对该条**只给审计报告的"很轻"评价而未给判据**，
> ⭐ **R5 复核对结论【同意】，但判据必须替换为实测的【键不匹配】**（见 X-14 行）——
> ⭐ **"结论对、判据缺"也是"判据必须可复用"纪律的一个实例**。
>
> ---
>
> ### ⭐⭐ E4 二次复核（第 3 轮观察者）—— **R3 的 4 个订正值【全部复现】，但另有 4 处锚点/口径缺陷**
>
> E4 对 R3 的订正做了**独立重算**（`scripts/_e4_recount.py`，全量 `lean/*.lean` 504 文件）：
> **`Pass `=146、`Reachable`=5、`WellFounded`=13、`ObsEq`=2 四个数字逐一复现**（`ExactEq`=0、
> `ApproxEq`=0、`well-founded`=0 三个对照亦复现）⟹ ⭐ **R3 的订正表已完整写入本表，无遗漏**。
>
> ⚠⚠ **但复核同时发现 R3 未查的 4 处缺陷，已就地订正**（R3 只复核了"清单原文"，未复核 R3 自己写下的锚点）：
>
> | # | 位置 | R3 写的 | 实测 | 性质 |
> |--:|:--|:--|:--|:--|
> | **E4-1** | X-8 判据 | `:160 def CompileReachable`、`:166 compileReachable_iff` | **`:226` / `:236`**（该文件现 377 行） | ⚠ **锚点失效**（行号漂移 66 行） |
> | **E4-2** | X-9 订正列 | `:123 def ObsEq`、`:127 obsEq_iff_eval_eq` | **`:179` / `:185`**（该文件现 195 行） | ⚠ **锚点失效**（漂移 56 行） |
> | **E4-3** | X-12 判据 | `RealGLUTraining.lean:141 gd_epsilon_termination` | **`:166`**（`:141` 是大段 docstring 内的自语行）；且 `RealADMM.lean:312` → **`:349`** | ⚠ **锚点指到 docstring，不是定理**（**B39 同族**："名字的存在性代替定理的存在性"） |
> | **E4-4** | X-2 判据 | 「**非 `msgPass` 的 `Pass ` = 0**」 | 按字面排除 `msgPass` 得 **59**（`sparseMsgPass`/`uniformMsgPass`/`iterMsgPass`）；按"`Msg` 前缀（cs）"口径得 **0** | ⚠ **口径未写明 ⟹ 下一轮会判为错** |
>
> ⭐⭐ **这本身是一条新的可复用判读规律**（**建议登记 STYLE**）：
> > **"订正了别人的数字" ≠ "自己的锚点是对的"。**
> > ⚠ **复核者的输出也是登记表的一部分，因此【也必须过锚点门禁】** ——
> > 否则 R3 修好了 7 个清单错，却留下 3 个**自己的**失效行号，
> > **而失效行号与"0 命中"同族：都让读者读到一份与对象不符的读数**（`PROCESS.md §4.1`）。
> > ⭐ **结构性根因**：本项目的 `.lean` 在**持续增长**（`RealConversionRoundTrip` 已 377 行 /
> > `RealContinuationEquivalence` 195 行），**任何绝对行号锚点都必然漂移** ⟹
> > ⭐ **这是 `P0-3`（DIVERGENCES 漂移门禁）应当覆盖的正是这一类**，而不只是"条数统计"。
> ⭐ **E4 的处置**：就地订正 4 处（**保留原值 + 标注"行号订正"**，遵循 `CORRECTIONS B243.4`
> "改数字等于销毁'当时是多少'这一事实"），并**把本条加进 `check-divergences.py` 的锚点检查范围**（见该脚本）。


---

## 数量统计

| 类别 | 条数 | 说明 |
|:--|--:|:--|
| **A 类（System boundary）** | **6** | A1–A6，体系自认不可内证 / 不可对象化 |
| **B 类（Axiomatic field）** | **12** | B-1–B-12，结构字段式假设 |
| **B 类（Explicit hypothesis）** | **12** | B-13–B-24，按模式归并（覆盖全库 **300 行**标注） |
| **B 类（新发现的结构事实）** | **5** | ⭐ B-25–B-29，**此前未集中登记** |
| **B 类（结构字段逐字段分类）** | **11** | ⭐ **B-30–B-40**，**补齐本文档§诚实边界 3/4 的待办**；产出 **A 类 47 字段完整清单** |
| **C 类（CORRECTIONS 索引）** | **11** | C-1–C-11 |
| **C 类（STYLE/WARNINGS/其他）** | **7** | C-12–C-18 |
| **C 类（上游结构性分歧）** | **4** | C-19–C-22 |
| **C 类（XOR/NOT 组合子，P1-2/P1-3）** | **4** | ⭐ **C-23–C-26**（定义域限制 / De Morgan vs 零化 / XOR≅NOT 同源 / 零集≠取值陷阱） |
| **C 类（R5：P1-4 语法侧桥 / P1-5 平凡性）** | **2** | ⭐ **C-27–C-28**（`concept ↦ constraint` 全域为假、只是 **C-19 的语法侧推论** / `repair` 恒等 ⟹ 三条定理**平凡真**，已显式标注） |
| **C 类（P0-4：`lean/_r9/` 未登记偏离源）** | **1** | ⭐ **C-29**：`_r9/` 的 19 个 `.lean` 为**过期副本**，4 个在顶层被 `B314`/`B318` 订正后未同步；`srcDir = "."` 使顶层同名文件遮蔽之 ⟹ **永不构建**（**显式永不构建条款**）|
| **C 类（执行轮：`extractLayer` 误判核查）** | **1** | ⭐ **C-30**：经复测为类 (iv) 合法影子副本（`rfl` 桥），**登记以阻止下一轮重新立项**，**无需治理** |
| **C 类（B410：`hreach` 边界缺陷）** | **1** | ⭐ **C-31**：B53 的修复有效但不完整；`hreach` 以同一见证在**原点开球**上失败，但整体仍可满足（两条须并述）|
| **X 类（明确不做 / 防复活）** | **13** | ⭐ **X-1–X-13**，**决策否定**（不是降级，也不是边界）；⚠ **其中 X-11 性质为"已存在（更强）"而非"不做"**；⚠ **7 条经 R3 独立复核后订正了清单原文判据** |
| **X 类（R5：P3-6 六列单表）** | **1** | ⭐ **X-14**：判定**不建**，判据 = 实测**键不匹配**（四表四种主键）；见 `SIX-COLUMN-TABLE-DECISION.md` |
| **X 类（多模态四轴）** | **1** | ⭐ **X-15**：判定**不做**，判据 = 13 组关键词 12 组为 0，唯一非零的 `CLIP` 经逐处核实全是 DP-SGD 的**梯度裁剪**；⚠ **本条经 M04/M09/U03 三次建议、零执行** |
| **合计** | **92** | ⭐ 原 **91** + **X-15 新增 1**；⚠ **已按上方各分项重算校验：A 6 + B 40 + C 31 + X 15 = 92** |

> ⚠ **X 类的计数口径**：13 条**全部计入**合计（含 X-11），因为它的**登记目的相同**
> —— **防止下一轮审计把它当缺口重新立项**。⚠ 但其**语义不同**（"已存在"而非"不做"），
> 已在 §X 类的表的"复核订正"列与 §X 类净结论中**显式标注**，
> ⟹ **凡引用本表者不得把 X-11 读作"项目拒绝做采样语义"。**

---

## ⭐ 本文档自身的方法论纪律

1. **每条给精确 `文件:行`。** ⚠ 本项目硬纪律：「**用名字/目录的存在性代替定理/实例的存在性**」
   **已 6 次失误**（`CORRECTIONS.md:520` 称"以名字判有无"为**第 6 次**）。
   ⇒ 本文档**所有**条目均由 `ReadAllLines` + `.Contains` 逐行实测，
   ⚠ **未使用 `Select-String`**（其正则对含 `?` 的 Lean 名字会**静默失配**）。
2. **"未登记即 bug"的默示义务。** 本文件**不**声称 LATTICE 的数学有错 ——
   `lake build` 全绿、0 `sorry`、0 `axiom` 均已复核。
   ⇒ 本文件登记的是**"与基准有意不同之处"**，正是这些不同**必须**在案。
3. **反面义务同样适用。** ⭐ 若某处**声称**了降级而**实际不是**（如 `RealRNGibbs` 的 `hintρ`
   已被删除、`RealExtractInvertibility` 的假设已升级为定理），
   **该条也必须在案**（见 **C-11**）—— 否则**登记表本身成为偏离源**。

---

## 诚实边界（本文档的）

1. ✅ **我提取的**：A1–A6、B-1–B-29、C-1–C-22 的**全部 `文件:行`** ——
   均经 `ReadAllLines` + `.Contains` 实测；B.1/B.2 的结构字段与假设谓词**逐行核对过定义体**。
2. ⚠ **我推测的**：**§B.3 的"重复建设"判断**（B-25/B-26/B-27）是**我看出的模式**，
   ⚠ **未经跨文件依赖实测**（无 `import` 图分析）⟹ **"3 处/4 个结构"的计数是文本层面的**，
   不排除有我没有的合并机制。
3. ✅ **已补做（B.4，原为本文档的待办）**：**§诚实边界 3** 原记「**B-11 的 3 个结构只登记位置、
   未逐字段判定**」—— **B.4 已逐字段判定**：`GeneralizationBound`（`sound`/`hdelta`）判为
   **A 类真假设**（A-38/A-39）；`CondGradModel` 判为**良性**（真假设在其**外部**的
   `CondUnbiased`（`RealQATRate.lean:291`）/`CondVarianceLe`（`:295`））；`IsGaussianVector` 判为
   **接口/谓词**（B-37/B-38）。
4. ✅ **已补做（B.4，原为本文档的待办）**：**§诚实边界 4** 原记「**92 个结构中只逐行核对了 12 个**，
   ⇒ B.1 不是完整清单，**其余 ~80 个可能仍藏假设字段**」—— **B.4 已全量执行**：
   **96 个文本命中 / 95 个真实声明 / 312 个字段全部逐个分类**，
   得出 **A 类（真假设）47 字段的完整清单**（13 个结构）。
   ⇒ ⚠ **本节**（诚实边界 4）**中的"未穷尽"现已不成立**；⚠ **但见新增的第 9–11 条**。
5. ⚠ **B.2 是归并而非枚举**：全库 **300 行** `显式假设/显式前提` 标注被归并为 **12 组**，
   ⇒ ⚠ **单条计数（每组的 `代表位置`）不是全量**；**逐条全量见 `ASSUMPTIONS.md`（2481 条）**。
6. ⚠ **`ASSUMPTIONS.md` 是自动生成的**（`scripts\gen-docs.ps1`，`:3`），
   基于**关键词**（`:4`：诚实/未证/未做/标注/降级/后续工作/留待/超出）——
   ⚠ **关键词命中 ≠ 偏离**，**未命中 ≠ 无偏离**（同 `HONESTY-COVERAGE.md:6-10` 的自我警告）。
   ⇒ 本文档**不**以 `ASSUMPTIONS.md` 为证据源。
7. **未做**：**未跑 Lean、未取锁、未 git、未修改任何既有文件**（纯静态阅读）。
   ⇒ ⚠ **B/C 类条目的"为什么可接受"来自源码 docstring 的**自述**，
   **我未独立验证**这些自述与证明体是否一致**（那需要内核级审计，见 `CORRECTIONS B39`）。
8. ⚠ **`_probe_mvp1_x.lean`**（与 `RealTemporalLayer.lean` 同内容的探针副本）**被排除**在扫描外，
   ⇒ **它不在 `roots` 中**，其存在本身可能是一条**未登记的偏离**（见 `README.md:37`：
   roots 是**显式白名单**）。**本条我未展开调查。**

### ⭐ B.4 自身的诚实边界（**哪些是核对过的、哪些是推断的**）

9. ✅ **逐字段核对过的**：**全部 95 个声明、312 个字段**的**字段名、类型、`文件:行`**
   均由 `ReadAllLines` 实测；**A 类 47 字段**与**良性 36 字段**的**每一个**都**读了定义体**，
   并对**有争议的**（`IEEERound`/`RoundOp`/`PositionEncoding`/`LvBitVec`/`IntervalAbstract`/
   `GeneralizationBound`/`Conversion`/`MAMLChainRule`/`FinSCM`/`BinSCM`）**读了构造点的证明体**。
10. ⚠ **用文本扫描代替依赖图的**：本文档判定"有无填充者"用的是
    **`def … : <结构> where` / `instance : <结构>` 的文本匹配**（`ReadAllLines` + `.Contains`），
    ⚠ **不是 Lean 层面解析**（未跑 Lean、无 `#check`、无 `import` 图）。
    ⇒ ⚠ **理论上可能漏掉"经 `@[to_additive]` 生成"或"经 `deriving`/`extends` 间接给出"的填充者**
    （本项目硬纪律已指出 `@[to_additive]` 生成名 **grep 声明行必然 0 命中**）。
    ⇒ ⚠ **"0 个填充者"= 文本层面的 0，不排除有我看不到的生成机制**。
11. ⚠ **我未判定的（如实列入，不猜）**：
    - ⚠ **`RealLv00Geometry.lean:133/136/139` 的 `GeoPoint`/`GeoLine`/`GeoPlane`**：
      是**空类型类**（`class X (α : Type) : Prop`，**无任何字段**）⟹ **无字段可分类**；
      ⚠ 但**它们作为 `Prop` 类型类的存在意义我未判定**（既不承载假设也无接口）。
    - ⚠ **`RealLv00Geometry.lean:146` `LvCongruence`（`seg_congruent`/`angle_congruent`）**：
      两字段是**关系载体**（`α → … → Prop`）⟹ 我判为 **I（接口）**；
      ⚠ **但该结构同样 0 个实例** ⟹ **若按 B-31 的判据，它是"无人使用的接口"**，
      是否应升级为 A 类**取决于"接口无实现者"是否等同"假设"** —— ⚠ **此判据我未确立**。
    - ⚠ **`RealLv00Geometry.lean:877` `AnalyticSurface.secondFF`**（`:881`
      `ℝ × ℝ → ℝ × ℝ × ℝ`，注释称"**真实的**第二基本形式系数场"）：
      ⚠ 字段类型是**函数（D 类形状）**，但注释的"**真实的**"暗示它与某个**未定义**的
      `Surface` 语义绑定 ⟹ **可能是"穿了数据外衣的假设"**，⚠ **我未判定**（同 B-39 的 `key` 形态）。
    - ⚠ **`RealLv00Solver.lean:974` `Theory.satisfiable : Prop`**：字段类型是 `Prop` 但**取值由构造方给**
      ⟹ 我按"`Prop` 型数据字段"归 **D**；⚠ **但它可被填入任意命题，实质接近 B-39 的 `key`** ——
      **边界情形，我未升级为 A**。
    - ⚠ **`RealLv00Geometry.lean:351` `AlgebraicNumber`（`minimalPoly`/`lower`/`upper`）**、
      **`:361` `TranscendentalNumber`（`name`/`coeff`）**：字段全是数据，
      ⚠ **但"极小多项式""超越数"的署名承诺（如 `minimalPoly` 真是极小的）无字段承载**
      ⟹ **与 B-39 同族（注释级假设）**，⚠ **我未逐条展开**。
12. ⚠ **B.4 的"良性"判定标准是**单项**的**：我判"良性"的依据是
    **存在至少一个填充点且该点由既有定理证成**。⚠ **这不排除**：
    (a) 某个"良性"结构的**其它字段**仍无填充（如 `RoundOp`：`reg_identityRoundOp:277` 是
    **恒等函数的退化见证**，**真实 IEEE 舍入仍是假设** —— 故 A-20…A-25 保留在 A 类）；
    (b) 填充点本身**依赖别的假设**（传递性未追）。⇒ ⚠ **"良性"≠"无条件成立"**。

---

*本文件为登记的产物，未修改 LATTICE 任何既有文件。*
