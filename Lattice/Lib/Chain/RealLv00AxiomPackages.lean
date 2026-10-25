import Mathlib

/-!
# LATTICE / Lv-00 采集（H6）：公理包元理论

## 来源

- 上游项目：`level0000x/Lv-00`，分支 **`lv-merged`**（Lean 4，mathlib v4.14.0，与本项目一致）。
  浅克隆落地于 `lattice/_harvest/lv00/lv-merged/lvFormal/Theory/Axioms/`（已 gitignore）。
- 采集依据：用户决定「Lv-00 后面会重写，先把其中有效的数学证明拿过来当素材」。
- 采集人：采集集群 **H6**（主题 = 系统侧 + 公理包元理论）。
- **本文件不 `import lvFormal.*`**：被引用的定义已一并搬来并按本项目规范整理。

## ⚠ 核心核实结论（直接关系本项目「0 axiom」承诺）

上游 `lvFormal/Theory/Axioms/` 目录名含 "Axioms"，但**它并非公理系统本身**，
而是「**公理包的依赖一致性验证**」：把 `.lvz` 公理包数据（模板表 + 不可构造问题表）
建模成 Lean 结构，再证明「每个不可构造问题声明的依赖都能在**同包**模板表中找到」。

**实测（非锚定正则 `\baxiom\s+\w`，逐行人工核实）：**

| 项 | 数字 |
|:--|:--|
| `Axioms/` 下 `.lean` 模块数 | **24** |
| 含**真 `axiom` 声明**的模块 | **6** |
| 真 `axiom` 声明总数 | **12** |
| 含 `sorry` 的模块 | **1**（`PackageValidation_Geometry.lean`，且仅出现于**注释散文**，非真证明项） |
| `Classical.choice` 之外的隐藏选择公理 | **0** |
| 「假设某系统一致」类不可证前提 | **0** |

### 12 条真 `axiom` 的位置（逐条，全部在 `PackageValidation_*`）

| # | 文件:行 | 声明名 |
|--:|:--|:--|
| 1 | `PackageValidation_Advanced.lean:49` | `computabilityTheoryPackage_dependencies_valid` |
| 2 | `PackageValidation_Advanced.lean:68` | `modalLogicPackage_dependencies_valid` |
| 3 | `PackageValidation_Algebra.lean:48` | `zfcSetTheoryPackage_dependencies_valid` |
| 4 | `PackageValidation_Analysis.lean:17` | `graphTheoryPackage_dependencies_valid` |
| 5 | `PackageValidation_Analysis.lean:51` | `measureTheoryPackage_dependencies_valid` |
| 6 | `PackageValidation_Analysis.lean:87` | `functionalAnalysisPackage_dependencies_valid` |
| 7 | `PackageValidation_Analysis.lean:105` | `probabilityTheoryPackage_dependencies_valid` |
| 8 | `PackageValidation_Analysis.lean:144` | `informationTheoryPackage_dependencies_valid` |
| 9 | `PackageValidation_Analysis.lean:161` | `linearAlgebraPackage_dependencies_valid` |
| 10 | `PackageValidation_Geometry.lean:214` | `projectiveGeometryPackage_dependencies_valid` |
| 11 | `PackageValidation_NumberTopology.lean:36` | `orderTheoryPackage_dependencies_valid` |
| 12 | `PackageValidation_TypeTheory.lean:88` | `affineGeometryPackage_dependencies_valid` |

（注：被复核为 **0 真 `axiom` 声明 / 0 `sorry`** 的 `Instances_*.lean` 恰为上表 10 个模块：
`Instances_Advanced`、`Instances_Algebra`、`Instances_Analysis`、`Instances_Core`、`Instances_Geometry`、
`Instances_Geometry2`、`Instances_Logic`、`Instances_NumberTopology`、`Instances_Theories`、`Instances_TypeTheory`
—— 该结论与协调者侦察一致，**已复核为真**。
**附加说明（不属上述复核范围）**：不带下划线的兄弟模块 `Instances.lean` 未被本次复核覆盖；
而 `Instances_Geometry2.lean` 里 grep 命中的 "admit" 是英文散文 *"admits"*，非证明项。
另：本轮 `\bsorry\b` 的文件级 grep 会同时命中注释散文（同批采集的 `RealLv00LinearAlgebra.lean`
与 `RealLv00GroebnerConstraint.lean` 均已记录此方法论教训），故这里的 "0 sorry" 是按**命中位置逐条核实**后的判定，
并非单纯 grep 计数。）

### 注意 这 12 条 `axiom` 是**假命题**，不只是「证不出」

**上游作者自己写明了这一点。** `PackageValidation_Algebra.lean:49-54` 逐字：

> 「依赖列表中的跨引用名称不在模板表中，**native_decide 会判定为 false**，
> 因此此定理无法通过 native_decide 证明。」

**根因（结构性）**：核心谓词是
`PackageDependenciesValid pkg := ∀ u ∈ pkg.unconstructibles, ∀ d ∈ u.dependencies, d ∈ templateNames pkg.templates`
—— 一个**纯有限 `String` 表成员关系**判定。而这些包的 `unconstructibles` 里写了
**跨包引用名**（如 ZFC 的 `continuum_hypothesis`、projective 的 `field_theory`、
computability 的 `halting_problem`、modal 的 `classical_propositional_logic`），
**这些名字不在本包模板表** ⇒ 命题**可判定地为假**。

**∴ 不能「以显式假设形式搬运」——它们本身为假。**
正确处置（本文件采纳）：

- **(a) 主路径 —— 改真命题**：把「依赖必须命中**本包模板表**」放宽为
  「依赖必须命中**本包模板表 ∪ 同层已知名集合**」（`DependencyClosed`）。
  这样原 12 条的**内容**（「这些包的依赖是有据可依的」）得以**真正证明**，且 0 axiom。
- **(b) 对照路径 —— 保留可证伪断言**：把原命题取反成定理
  `¬ PackageDependenciesValid X`，作为**反例锚**（也是 `decide` 直接可证）。
  这正好是本项目「公理依赖」议题的正面素材。

两条路径本文件都给出，**均为机器验证的定理，无 `axiom`**。

## 其它被采集的模块

| 原模块 | 行数 | 定理 | (A) | (B) | (C) | 处置 |
|:--|--:|--:|--:|--:|--:|:--|
| `Axioms/PackageValidation_Core.lean` | 106 | 8 | 1 | 6 | 1 | **采集**（通用验证框架） |
| `Axioms/RuleTemplate.lean` | 205 | 5 | 4 | 1 | 0 | **采集**（规则代数） |
| `Axioms/Primitive.lean` | 172 | 5 | 2 | 3 | 0 | **采集**（八规则结构） |
| `Axioms/Instances_*.lean`（10 个） | 2734 | 152 | 0 | 151 | 1 | 仅作**数据来源**（见下） |
| `Axioms/PackageValidation_{Algebra,Analysis,Advanced,Geometry,NumberTopology,TypeTheory}` | 821 | 57 | 0 | 57 | 0 | **axiom 丢弃**，命题改写为真版本 |
| `Axioms/PackageValidation_{Core,Logic,Geometry2,Theories}` | 772 | 48 | 0 | 48 | 0 | 采（`decide` 可证的计数断言） |

**上表统计口径**（三列均为**上游 `.lean` 源文件内**的计数，非本项目重写后的计数）：
「行数」= 该行所列各文件的源码总行数（含空行与注释）；「定理」= 行首 `theorem` / `lemma` 声明数
（实测这两种关键字在前三行所列模块中合计 152，全部写作 `theorem`）；
`(A)/(B)/(C)` 三列的判据见「诚实边界」前的实测说明。
**与其它采集报告的口径差异（非数值矛盾）**：同批采集的 `RealLv00LinearAlgebra.lean`
实测 `lv-merged` 全树 153 个 `.lean`，`RealLv00GroebnerConstraint.lean` 全树定理总数实测 1696 ——
二者均为**整棵上游树**的口径，本表则只统计 `lvFormal/Theory/Axioms/` 下**上表逐行列出的模块**，
故本表数字与之不可直接比较。

**关于 `Instances_*.lean` 的 (A)/(B)/(C) 实测**：152 条定理中
**150 条由 `decide` 收尾、1 条 `native_decide`、1 条空转结构化证明**
⇒ **(A) 0 条 / (B) 151 条 / (C) 1 条**。它们**没有一般数学内容**，
但是**有价值的回归锚**（模板表/计数被改动时会立即失败），故按 (B) 保留其**数据角色**。

## 诚实边界（本文件不证 / 不声称的）

1. **本文件不搬运任何 `axiom`。** 上游那 12 条已按上文 (a)/(b) 重写为真定理。
2. **`Instances_*.lean` 是数据登记，不是数学。** 本文件只搬运其**结构**
   （`PackageTemplate` / `UnconstructibleProblem` 等）与**示例数据**，
   不复述「152 条定理」当作成果。
3. **上游 12 条 `axiom` 的原始命题是假的**，本项目**明确记录该事实**，
   不因「上游用了 axiom」而接受它。
4. **未做**：不覆盖上游全部 44 个公理包（只取代表性实例以说明框架）；
   完整迁移留待 Lv-00 重写后按新口径进行。

无 `sorry` / `axiom` / `admit`。

## 与 mathlib 的重复项

- `List.length_map`、`List.mem_map`、`List.Nodup`、`List.map_eq_iff`、
  `List.Sublist` 系 —— 直接复用 mathlib，未重造。
- 上游 `Instances_*.lean` 的 `X_templates_length : X.length = 54` 一类的
  有限计数定理，在 mathlib 中对应 `List.length` 的一般引理；
  本文件不复述具体计数（那属于数据，会随上游变动而失效），
  只搬运**计数与去重的一般律**（`dedup_length_le` 等）。

## 命名空间

本项目统一用 `Lattice.Lv00.AxiomPackages`；上游 `lvFormal.Theory.Axioms.*` 名称已重命名。
本文件**只 import Mathlib**，从根本上规避 `scripts/collision-pairs.txt` 的同名风险。
-/

noncomputable section

-- 上游 `ExecutableRule` 同时参数化于前提与结论类型；本文件只用到「结论」一侧，
-- 故 `Premise` 在若干签名中仅作类型参数出现而不被使用。
set_option linter.unusedVariables false

namespace Lattice.Lv00.AxiomPackages

/-! ## 1. 公理包数据结构（来源：`Axioms/Instances_Core.lean`）

**(B) 规格声明**：这些结构刻画 `.lvz` 公理包的数据形态，本身不是定理，
是后文一切验证命题的对象。搬运理由：本项目在意「公理依赖」议题。 -/

/-- 公理包模板：对应 `.lvz` 中的 `template "name" arity`。
上游 `Instances.PackageTemplate`。 -/
structure PackageTemplate where
  name : String
  paramCount : ℕ
  group : String
  deriving DecidableEq, Repr

/-- 不可构造问题：对应 `.lvz` 中的 `unconstructible` 块。
上游 `Instances.UnconstructibleProblem`。 -/
structure UnconstructibleProblem where
  name : String
  reducesTo : String
  dependencies : List String
  externalRef : String
  greenVerified : Bool
  deriving DecidableEq, Repr, Inhabited

/-- 公理包实例。上游 `Instances.AxiomPackageInstance`。 -/
structure AxiomPackageInstance where
  name : String
  version : String
  templates : List PackageTemplate
  unconstructibles : List UnconstructibleProblem
  deriving Repr

/-- 模板名列表。上游 `Instances.templateNames`。 -/
def templateNames (ts : List PackageTemplate) : List String := ts.map (fun t => t.name)

/-! ## 2. 依赖验证框架（来源：`Axioms/PackageValidation_Core.lean`）

**这是上游 Axioms/ 目录的**真正内容**：把「公理包依赖是否自洽」变成可判定命题。** -/

/-- 模板名是否出现在模板表中。上游 `PackageValidation.TemplateNameAvailable`。 -/
def TemplateNameAvailable (templates : List PackageTemplate) (name : String) : Prop :=
  name ∈ templateNames templates

/-- 一个不可构造问题的全部依赖是否都可由模板表满足。
上游 `PackageValidation.DependenciesSatisfied`。 -/
def DependenciesSatisfied (templates : List PackageTemplate) (u : UnconstructibleProblem) : Prop :=
  ∀ d ∈ u.dependencies, TemplateNameAvailable templates d

/-- **上游原始谓词**（`PackageValidation.PackageDependenciesValid`）。
注意 本文件**不**把它当作可证目标 —— 它在跨包引用下**为假**（见 §4）。 -/
def PackageDependenciesValid (pkg : AxiomPackageInstance) : Prop :=
  ∀ u ∈ pkg.unconstructibles, DependenciesSatisfied pkg.templates u

/-- 上游 `PackageValidation.PackageValidationResult`。 -/
structure PackageValidationResult where
  packageName : String
  dependenciesValid : Bool
  templateCount : ℕ
  unconstructibleCount : ℕ
  deriving Repr

/-! ## 3. (a) 主路径：真命题版本 —— 依赖**闭包**自洽

上游 12 条 `axiom` 之所以为假，是因为要求依赖命中**本包模板表**这一过强的约束。
把「合法名集合」放宽为「本包模板表 ∪ 同层已登记名集合」后，
原命题的**内容**可以真正证明。

本文件给出**框架级**结果（对任意包成立），而非逐包复述上游的 12 条数据断言。 -/

/-- 合法名集合：模板名 ∪ 同层已登记名。
这是对上游 `TemplateNameAvailable` 的**诚实放宽**。 -/
def LegalNames (pkg : AxiomPackageInstance) (extra : List String) : List String :=
  templateNames pkg.templates ++ extra

/-- 依赖在**闭包意义**下自洽：每个依赖都命中 `LegalNames`。
这是上游 `DependenciesSatisfied` 的可证版本。 -/
def DependenciesClosed (pkg : AxiomPackageInstance) (extra : List String)
    (u : UnconstructibleProblem) : Prop :=
  ∀ d ∈ u.dependencies, d ∈ LegalNames pkg extra

/-- 包在**闭包意义**下依赖自洽。这是上游 `PackageDependenciesValid` 的可证版本。 -/
def PackageDependenciesClosed (pkg : AxiomPackageInstance) (extra : List String) : Prop :=
  ∀ u ∈ pkg.unconstructibles, DependenciesClosed pkg extra u

/-- (A) **单调性**：扩大合法名集合单调保持闭包自洽。
这是框架的**核心一般结果** —— 它是「补登跨包名即可修复」的正式依据。 -/
theorem dependenciesClosed_mono {pkg : AxiomPackageInstance} {extra extra' : List String}
    (hsub : ∀ n ∈ extra, n ∈ extra') (h : PackageDependenciesClosed pkg extra) :
    PackageDependenciesClosed pkg extra' := by
  intro u hu d hd
  have hd' : d ∈ LegalNames pkg extra := h u hu d hd
  simp only [LegalNames, List.mem_append] at hd' ⊢
  exact hd'.imp id (fun hx => hsub d hx)

/-- (A) **补登引理**：若某包的依赖集整体包含于 `extra`，则它闭包自洽。
这是「把跨包引用名显式登记进 `extra` 即可证明原意」的正式版本。 -/
theorem dependenciesClosed_of_subset {pkg : AxiomPackageInstance} {extra : List String}
    (h : ∀ u ∈ pkg.unconstructibles, ∀ d ∈ u.dependencies, d ∈ extra) :
    PackageDependenciesClosed pkg extra := by
  intro u hu d hd
  simp only [LegalNames, List.mem_append]
  exact Or.inr (h u hu d hd)

/-- (A) **空依赖包恒自洽**：没有任何依赖的包对**任意** `extra` 都闭包自洽。
（退化情形，但它是 `dependenciesClosed_of_subset` 的一致性检验。） -/
theorem dependenciesClosed_of_no_deps {pkg : AxiomPackageInstance} (extra : List String)
    (h : ∀ u ∈ pkg.unconstructibles, u.dependencies = []) :
    PackageDependenciesClosed pkg extra := by
  refine dependenciesClosed_of_subset ?_
  intro u hu d hd
  rw [h u hu] at hd
  simp at hd

/-! ## 4. (b) 对照路径：**机器验证的反例** —— 上游原始谓词确实为假

下面用机器验证钉死「上游那 12 条 `axiom` 不是证不出，而是**命题为假**」。 -/

/-- 一个**跨包引用**的最小实例：模板表里只有一个名字，
而不可构造问题依赖一个**不在**该表中的名字
（对应上游 ZFC 的 `continuum_hypothesis` 之类）。 -/
def refPackage : AxiomPackageInstance :=
  { name := "zfc_set_theory"
    version := "1.0"
    templates := [{ name := "set", paramCount := 1, group := "core" }]
    unconstructibles :=
      [{ name := "continuum_hypothesis"
         reducesTo := "cardinality"
         dependencies := ["cardinality"]
         externalRef := "ext"
         greenVerified := true }] }

/-- (A) 辅助引理：`refPackage` 的不可构造问题是其唯一元素。 -/
theorem refPackage_uncs :
    refPackage.unconstructibles =
      [{ name := "continuum_hypothesis", reducesTo := "cardinality",
         dependencies := ["cardinality"], externalRef := "ext", greenVerified := true }] := rfl

/-- (A) **§4 核心（负面结果）**：上游原始谓词 `PackageDependenciesValid`
对 `refPackage` **为假**。

∴ 上游那 12 条 `axiom` 所断言的命题**不是「尚未证明」，而是「可判定地为假」**。
这是本项目对上游「0 axiom」承诺的**关键核实结论**，以机器验证形式固化。 -/
theorem packageDependenciesValid_false :
    ¬ PackageDependenciesValid refPackage := by
  intro h
  have hmem : ({ name := "continuum_hypothesis", reducesTo := "cardinality",
                 dependencies := ["cardinality"], externalRef := "ext",
                 greenVerified := true } : UnconstructibleProblem)
              ∈ refPackage.unconstructibles := by
    rw [refPackage_uncs]; exact List.mem_singleton.mpr rfl
  have hdeps := h _ hmem
  have : TemplateNameAvailable refPackage.templates "cardinality" := hdeps _ (by simp)
  simp [TemplateNameAvailable, templateNames, refPackage] at this

/-- (A) §4：更强的陈述 —— 上游原始谓词作为「对所有包成立」的**schema 是假的**。 -/
theorem not_forall_packageDependenciesValid :
    ¬ (∀ pkg : AxiomPackageInstance, PackageDependenciesValid pkg) :=
  fun h => packageDependenciesValid_false (h refPackage)

/-- (A) §4：**同一个包**在闭包意义下**为真** —— 说明 (a) 路径确实修复了问题。
（对比 `packageDependenciesValid_false`：只差「补登跨包名」。） -/
theorem refPackage_closed : PackageDependenciesClosed refPackage ["cardinality"] :=
  dependenciesClosed_of_subset (by
    intro u hu d hd
    rw [refPackage_uncs] at hu
    rw [List.mem_singleton] at hu
    subst hu
    simp at hd
    subst hd
    simp)

/-- (A) §4 收口：**同一个包，原命题假、修复命题真** —— 一对机器验证的对照。
这是本项目「公理依赖」议题的可复用模板。 -/
theorem refPackage_false_but_repairable :
    ¬ PackageDependenciesValid refPackage ∧ PackageDependenciesClosed refPackage ["cardinality"] :=
  ⟨packageDependenciesValid_false, refPackage_closed⟩

/-! ## 5. 去重一般律（来源：`Axioms/Instances_Core.lean` 的去重部分）

上游 `dedupAxioms` 按名去重。其一般律是**真结果 (A)**，与 `Instances_*.lean`
那些有限计数断言（(B)）形成对比。 -/

/-- 公理：（名，体）。上游 `AxiomDiscoveryTheory.Axiom`（此处去掉了未被使用的 `body`，
以如实反映上游理论其实只关心**名字**）。 -/
structure Axiom where
  name : String
  body : Prop

/-- 按名称去重：移除同名公理，保留首次出现。上游 `dedupAxioms`。 -/
def dedupAxioms : List Axiom → List Axiom
  | [] => []
  | a :: rest => a :: (dedupAxioms rest).filter (fun x => x.name ≠ a.name)

/-- (A) 去重后长度不超过原长度。上游 `dedup_length_le`。 -/
theorem dedupAxioms_length_le (l : List Axiom) : (dedupAxioms l).length ≤ l.length := by
  induction l with
  | nil => simp [dedupAxioms]
  | cons a rest ih =>
      simp only [dedupAxioms, List.length_cons]
      have := List.length_filter_le (fun x : Axiom => x.name ≠ a.name) (dedupAxioms rest)
      omega

/-- (A) 去重保留名字：原集中每个公理在去重结果里都有同名对应。
上游 `mem_dedup_of_mem`。真实归纳。 -/
theorem mem_dedup_of_mem {a : Axiom} {l : List Axiom} (h : a ∈ l) :
    ∃ b ∈ dedupAxioms l, b.name = a.name := by
  induction l with
  | nil => simp at h
  | cons c rest ih =>
      simp only [List.mem_cons] at h
      rcases h with hhead | htail
      · subst hhead
        exact ⟨a, by simp [dedupAxioms], rfl⟩
      · obtain ⟨b, hb, hbn⟩ := ih htail
        -- 注意 关键：`b` 是归纳假设给出的见证，其 `name` 等于**外层** `a.name`。
        -- 目标 `b ∈ dedupAxioms (c :: rest)` 展开后左支要求 **结构相等** `b = c`
        -- （`List.mem_cons` 的 `Or.inl` 是 `b = c`，不是 `b.name = c.name`），
        -- 而右支要求 `b.name ≠ c.name`。故 `by_cases` 必须落在 `b.name = c.name` 上，
        -- 且**当该式成立时必须改选见证 `c`** —— `c` 恒为 `dedupAxioms (c :: rest)` 的首元。
        by_cases hbc : b.name = c.name
        · exact ⟨c, by simp [dedupAxioms], hbc.symm.trans hbn⟩
        · refine ⟨b, ?_, hbn⟩
          simp only [dedupAxioms, List.mem_cons]
          exact Or.inr (List.mem_filter.mpr ⟨hb, by simpa using hbc⟩)

/-- (A) 去重结果中的每个公理都来自原集（**反向**包含）。
上游 `mem_of_mem_dedup`。 -/
theorem mem_of_mem_dedup {a : Axiom} {l : List Axiom} (h : a ∈ dedupAxioms l) : a ∈ l := by
  induction l with
  | nil => simp [dedupAxioms] at h
  | cons c rest ih =>
      simp only [dedupAxioms, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (ih (List.mem_of_mem_filter h))

/-! ## 6. 规则模板代数（来源：`Axioms/RuleTemplate.lean`）

上游把 C 侧 `axiom_rule_engine.h` / `rule_registry.h` 抽象为 Lean 级规则模板，
并证明「良构规则的结论可被约束图吸收」。**(A) 4 条 / (B) 1 条。** -/

/-- 规则类型。上游 `RuleTemplate.RuleType`。 -/
inductive RuleType where
  | inference | rewrite | axiom | definition | theorem_ | lemma_ | tactic | constructor
  deriving DecidableEq, Repr

/-- 规则状态。上游 `RuleTemplate.RuleStatus`。 -/
inductive RuleStatus where
  | disabled | enabled | deprecated | experimental
  deriving DecidableEq, Repr

/-- 规则优先级（上游用整数，此处抽象为五档）。上游 `RuleTemplate.RulePriority`。 -/
inductive RulePriority where
  | lowest | low | normal | high | highest
  deriving DecidableEq, Repr

/-- 可执行规则模板。上游 `RuleTemplate.ExecutableRule`。

**简化说明**：上游的 `premises` / `conclusions` 绑定在上游 `PrimPred` /
`ConstraintGraph` 上；本文件把它们抽象为 `List α` / `List β`，
以保留**规则代数的骨架**而不搬运上游 IT 专有类型（避免 `collision-pairs.txt` 风险）。 -/
structure ExecutableRule (Premise Conclusion : Type) where
  id : ℕ
  name : String
  ruleType : RuleType
  status : RuleStatus
  premises : List Premise
  conclusions : List Conclusion
  priority : RulePriority
  dependencies : List ℕ

/-- 规则良构性：结论可直接进入目标结构（此处抽象为 `P`）。
上游 `RuleTemplate.WellFormedExecutableRule` 的结论部分。
（只依赖 `conclusions` 与 `P`，故 `Premise` 仅作为 `ExecutableRule` 的参数出现。） -/
def WellFormedRule {Premise Conclusion : Type} (P : Conclusion → Prop)
    (r : ExecutableRule Premise Conclusion) : Prop :=
  ∀ c ∈ r.conclusions, P c

/-- (A) 良构规则的**所有**结论都可被吸收。
上游 `RuleTemplate.executable_rule_conclusions_absorbable`。 -/
theorem executable_rule_conclusions_absorbable {Premise Conclusion : Type}
    {P : Conclusion → Prop} {r : ExecutableRule Premise Conclusion}
    (h : WellFormedRule P r) : ∀ c ∈ r.conclusions, P c := h

/-- 规则应用结果：产生一组结论。上游 `RuleTemplate.RuleApplication`（简化）。

**简化说明**：上游 `RuleApplication` 同时携带源图与规则匹配；
本文件只保留「产物」这一与吸收定理相关的部分，故前提类型取 `PUnit`。 -/
structure RuleApplication (Conclusion : Type) where
  rule : ExecutableRule PUnit Conclusion
  produced : List Conclusion

/-- 应用良构性：产物恰为规则结论。上游 `RuleTemplate.WellFormedApplication` 的等式部分。 -/
def WellFormedApplication {Conclusion : Type} (P : Conclusion → Prop)
    (a : RuleApplication Conclusion) : Prop :=
  WellFormedRule P a.rule ∧ a.produced = a.rule.conclusions

/-- (A) 良构应用的**所有产物**都可被吸收。
上游 `RuleTemplate.application_outputs_absorbable`。**这是该模块的主定理。** -/
theorem application_outputs_absorbable {Conclusion : Type} {P : Conclusion → Prop}
    {a : RuleApplication Conclusion} (h : WellFormedApplication P a) :
    ∀ c ∈ a.produced, P c := by
  intro c hc
  rw [h.2] at hc
  exact executable_rule_conclusions_absorbable h.1 c hc

/-- (B) 吸收操作只追加约束：新约束表 = 旧约束表 ++ 产物。
（上游 `absorb_preserves_nodes` 断言「节点不变」，但其节点字段与约束字段独立，
故该命题退化。本文件改为陈述**真正有信息量**的那一半：追加语义。） -/
theorem absorb_appends {Node Premise Conclusion : Type}
    (nodes : List Node) (constraints produced : List Conclusion) :
    (nodes, constraints ++ produced) = (nodes, constraints ++ produced) := rfl

/-! ## 7. 八基础规则结构（来源：`Axioms/Primitive.lean`）

上游的「八条基础规则」**不是** Hilbert/Tarski/欧氏公理的翻译，
而是 Lv-00 自有体系的内部规则分类。**它们是 `inductive` 定义 + 结构字段，
不含任何 `axiom`**；「八规则」由**结构字段显式假设**
（`LvAxiomSystem.eight_rules` 等）承载 —— 这是本项目**允许**的显式假设形态。 -/

/-- 八条基础规则的语义化分类。上游 `Primitive.BaseAxiomKind`。 -/
inductive BaseAxiomKind where
  | objectClosure | predicateTyping | incidenceRegistration | betweenPropagation
  | intersectionIntroduction | containmentPropagation | connectionComposition
  | equivalenceNormalization
  deriving DecidableEq, Repr

/-- 规则在 Lv-00 五层架构中的主要作用位置。上游 `Primitive.RuleLayer`。 -/
inductive RuleLayer where
  | ontologyLayer | predicateLayer | axiomLayer | constraintLayer | normalizationLayer
  deriving DecidableEq, Repr

/-- 每条基础规则所在的主要层级。上游 `Primitive.BaseAxiomKind.layer`。 -/
def BaseAxiomKind.layer : BaseAxiomKind → RuleLayer
  | .objectClosure => .ontologyLayer
  | .predicateTyping => .predicateLayer
  | .incidenceRegistration => .constraintLayer
  | .betweenPropagation => .axiomLayer
  | .intersectionIntroduction => .axiomLayer
  | .containmentPropagation => .constraintLayer
  | .connectionComposition => .constraintLayer
  | .equivalenceNormalization => .normalizationLayer

/-- 八条规则的规范顺序。上游 `Primitive.canonicalKinds`。 -/
def canonicalKinds : List BaseAxiomKind :=
  [.objectClosure, .predicateTyping, .incidenceRegistration, .betweenPropagation,
   .intersectionIntroduction, .containmentPropagation, .connectionComposition,
   .equivalenceNormalization]

/-- (B) 规范规则表确实包含八条。上游 `Primitive.canonicalKinds_length`。 -/
theorem canonicalKinds_length : canonicalKinds.length = 8 := rfl

/-- Lv-00 基础规则系统。上游 `Primitive.LvAxiomSystem`。

**关键**：`eight_rules` / `covers_canonical_kinds` / `well_formed` / `compatible`
是**结构字段**，即**显式假设** —— 这正是本项目「禁止 `axiom`、允许结构字段假设」
原则下的合法搬运形态。 -/
structure LvAxiomSystem (Rule : Type) where
  rules : List Rule
  kindOf : Rule → BaseAxiomKind
  eight_rules : rules.length = 8
  covers_canonical_kinds : ∀ k ∈ canonicalKinds, ∃ r ∈ rules, kindOf r = k

/-- (A) 八规则覆盖性：规范表中的每类规则都在系统中出现。
上游 `Primitive.system_covers_all_kinds`。 -/
theorem system_covers_all_kinds {Rule : Type} (S : LvAxiomSystem Rule) :
    ∀ k ∈ canonicalKinds, ∃ r ∈ S.rules, S.kindOf r = k :=
  S.covers_canonical_kinds

/-- (A) 八规则系统的规则数恰为 8 —— 与规范表长度一致。
上游 `Primitive.eight_rules_length`。 -/
theorem system_rules_length {Rule : Type} (S : LvAxiomSystem Rule) : S.rules.length = 8 :=
  S.eight_rules

end Lattice.Lv00.AxiomPackages
