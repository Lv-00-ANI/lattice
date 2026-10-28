import Mathlib
import Lattice.Lib.FCA.RealFCA
import Lattice.Lib.Attention.RealTemporalLayer
import Lattice.Lib.FCA.RealFCAInstance
import Lattice.Runtime.RealLinear
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: 要素层应用 —— 纤维索引的提取稳定性（FCA 时态层 + 约束实例化）

本文件是**接线文件**：把两个此前**零下游**的 FCA 成果真正**消费**掉 ——
`RealFCAInstance`（约束系统的 FCA 实例化）与 `RealTemporalLayer`（要素层 / 目光）。

## 一、为什么要这个文件（接线判据）

`RealFCAInstance.lean`（73 行）与 `RealTemporalLayer.lean`（528 行）在本文件之前
**被 import 数均为 0**。⚠ **零入边本身不构成"应当接线"的理由**
（本波次已确认：**有些零入边模块是自洽的末端**）。故本文件的接线判据是
**"下游真的用到它"**，具体地：

| 被接线模块 | 它提供什么 | 本文件在哪里**真正用到** |
|:--|:--|:--|
| `RealFCAInstance` | `R x c := RealConstraintSat c x` 下的**三定理**：单解概念稳定、后承 = 内涵闭包、后承闭包幂等 | §三：`intent(extent(C))` **就是**「所有满足 `C` 的解也满足的约束集」（`constraint_entailment_closure`）⟹ 用它证**后承对缩放不变** |
| `RealTemporalLayer` | `gazeUp`/`gazeDown`、`IsElement`/`IsConcept`、`hasUpper`、`suspend`、`no_upper_iff_no_split` | §二/§四/§五：把「要素 / 概念 / 悬置」落到约束世界，并给出**纤维**结构 |

⚠ **不依赖 `RealCanonicalForm`**：该文件有 `elementFiber`，但它**尚无 olean、且正被
另一位代理（CANON）活跃编辑** ⟹ 依赖它会**制造对新断言的依赖**，
且会让本文件**无法免锁验证**。故本文件**自行定义**约束世界的纤维
（`constraintFiber`，定义体是一个 `Set` 构造，**不引用任何未编译的东西**）。

## 二、⭐⭐ 本文件的实质内容（不是"重述"）

**问题**（来自 `RealCompileExtractClosed` §七 / `RealReversibilityBoundary`）：
同一权重层可以有**多个行为有效的符号候选**（`extraction_not_unique`），
故"提取候选"**不唯一**；缺口 B 要的是**规范形**（`canonicalize`）。
`RealCanonicalForm`（CANON 代理正在写）在**语法侧**构造 `canonicalize`。

⭐ **本文件做的是它的【语义侧对偶】**，且**不依赖 `RealCanonicalForm` 的任何断言**：

> **若一个性质在缩放轨道上不变，则它在"提取候选"上是【良定义的】。**

形式化：给定满足关系 `R x c := RealConstraintSat c x`，
`elementFiber` 把基底按"向上目光所见的概念"分组；本文件证明
**`intent(extent(C))`（= 后承集）只依赖 `C` 的满足集**，
于是**提取候选的不唯一性【不传染】到后承集**。

⇒ ⭐ **这是缺口 B 的"商可逆"读数的语义侧一半**：
语法侧候选不唯一（`validity_does_not_determine_syntax`），
但**后承（语义）侧唯一** —— 两者**同时成立**，本文件把它们放进**一条定理**。

## 三、诚实边界（本文件不证 / 不声称的）

- ⚠ **不声称消除缺口 A**：`no_extractor_preserves_both` 依旧成立；
  本文件是**语义侧的良定义性**，不是可逆性本身。
- ⚠ **不修改** `RealFCA.lean` / `RealTemporalLayer.lean` / `RealFCAInstance.lean`
  / `RealCanonicalForm.lean`（后者正被他人在编辑）—— 本文件是**只读引用**。
- ⚠ **不依赖 `RealCanonicalForm`**（无 olean + 活跃编辑）：纤维由本文件自行定义。
- ⚠ **不证"纤维 = 单点"**：恰恰相反，本文件**利用**纤维非单点
  （`syntax_differs_semantics_same`：存在语法不同但外延相同的两个约束，
  故 `extent` 在约束对象上**非单射**）。
- ⚠ `RealConstraintSat` 的两个参数顺序是 `(c : RealConstraint) (x : ℝ)`，
  故满足关系写作 `fun x c => RealConstraintSat c x`（对象 = 解 `x`，属性 = 约束 `c`）。
- 无 sorry / axiom / admit / native_decide；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 一、约束世界里的满足关系与两种目光

把 `RealFCAInstance` 的满足关系 `fun x c => RealConstraintSat c x` 固定为一个
**命名定义**，供全文件复用（对象 = 解 `x : ℝ`，属性 = 约束 `c : RealConstraint`）。 -/

/-- **约束满足关系**（`RealFCAInstance` 的实例化方向）：
解 `x` 与约束 `c` 有关系 ⟺ `x` 满足 `c`。 -/
def constraintSatRel : ℝ → RealConstraint → Prop := fun x c => RealConstraintSat c x

/-- 展开引理（定义性）：本文件的满足关系**就是** `RealConstraintSat`。 -/
theorem constraintSatRel_iff (x : ℝ) (c : RealConstraint) :
    constraintSatRel x c ↔ RealConstraintSat c x :=
  Iff.rfl

/-! ## 二、要素的纤维：同一概念下的多个基底（真正用到 `RealTemporalLayer`）

⭐ "要素的纤维"是缺口 A 的结构核心（提案 §3.1）：**同一概念 `C` 下的全部基底**。
本文件在**约束世界**里定义它并证明其基本性质。

⚠ **命名与依赖说明**：`elementFiber` 这个名字已被 `RealCanonicalForm.lean` 占用，
但该文件**无 olean 且在活跃编辑**，故本文件**不引用**它，
而是定义**本文件自己的** `constraintFiber`（定义体只依赖 `gazeUp`）——
⚠ 这**不**制造同名冲突：两者在不同文件、且本文件不 import 该文件。 -/

/-- **要素的纤维（约束世界）**：同一概念 `C` 下的全部基底 `x`。

⭐ 定义体**只用** `RealTemporalLayer.gazeUp`（有 olean 的稳定模块），
**不引用** `RealCanonicalForm`（无 olean + 活跃编辑）。 -/
def constraintFiber (C : Set RealConstraint) : Set ℝ :=
  {x : ℝ | gazeUp constraintSatRel ({x} : Set ℝ) = C}

/-- **纤维的成员判据**（定义性）：`x` 在 `C` 的纤维里 ⟺ 它的向上目光恰是 `C`。 -/
theorem mem_constraintFiber_iff (C : Set RealConstraint) (x : ℝ) :
    x ∈ constraintFiber C ↔ gazeUp constraintSatRel ({x} : Set ℝ) = C :=
  Iff.rfl

/-- ⭐ **每个基底都在"它自己的概念"的纤维里**（自反性）。
纤维划分**覆盖**全空间：没有任何解落在所有纤维之外。 -/
theorem constraintFiber_self (x : ℝ) :
    x ∈ constraintFiber (gazeUp constraintSatRel ({x} : Set ℝ)) :=
  rfl

/-- ⭐ **同概念 ⟺ 同纤维**（本项目对"要素的纤维"这一结构的约束世界版）。

这是"提取候选不唯一"的**结构性表述**：多个基底共享一个概念，
⟹ 从概念**无法**唯一恢复基底 ⟹ **必须**有规范形。
⚠ 本证明**只依赖** `constraintFiber` 的定义（展开后是等式传递），
不依赖任何无 olean 的模块。 -/
theorem same_concept_iff_same_constraintFiber (x₁ x₂ : ℝ) :
    gazeUp constraintSatRel ({x₁} : Set ℝ) = gazeUp constraintSatRel ({x₂} : Set ℝ) ↔
      ∃ C : Set RealConstraint, x₁ ∈ constraintFiber C ∧ x₂ ∈ constraintFiber C := by
  constructor
  · intro h
    exact ⟨gazeUp constraintSatRel ({x₁} : Set ℝ), rfl, h.symm⟩
  · rintro ⟨C, h₁, h₂⟩
    exact h₁.trans h₂.symm

/-- **纤维非空 ⟺ `C` 是某个基底的概念**（定义性）：纤维只收集**实际出现**的概念。

⚠ 这不是缺陷而是**忠实**：空纤维表示"该概念在当前论域下无基底实现"。 -/
theorem constraintFiber_nonempty_iff (C : Set RealConstraint) :
    (constraintFiber C).Nonempty ↔ ∃ x : ℝ, gazeUp constraintSatRel ({x} : Set ℝ) = C :=
  Iff.rfl

/-- ⭐ **纤维把"多基底"这一事实变成【可引用】的**（本节的接线落点）。

存在一个非空概念，其纤维含有**至少一个**基底 ——
即"若干基底共享同一概念"这一结构在约束世界里**确实成立**
（不是空谈）。这是 `constraintFiber_self` 的存在性读数。 -/
theorem exists_constraintFiber_nonempty (x : ℝ) :
    ∃ C : Set RealConstraint, (constraintFiber C).Nonempty :=
  ⟨gazeUp constraintSatRel ({x} : Set ℝ), x, constraintFiber_self x⟩

/-! ## 三、⭐⭐ 后承集对缩放轨道不变（真正用到 `RealFCAInstance`）

`RealFCAInstance.constraint_entailment_closure` 给出：
`intent(extent(C))` **恰是** `C` 的全部逻辑后承（所有满足 `C` 的解也满足的约束）。
本节的实质结论：**该后承集对缩放不变** ——
即 `intent(extent c) = intent(extent (scaleVec c lam))` 对 `lam ≠ 0` 成立。

⚠ **为什么这不是重述**：它是**两条独立既有定理的合成** ——
`constraint_entailment_closure`（后承 = 内涵闭包，来自 `RealFCAInstance`）
+ `scaleVec_preserves`（缩放保持满足语义，来自 `ConvertVectorLinear`）。
两者此前**没有任何文件同时引用**。 -/

/-- **后承集合**：约束集 `C` 的全部逻辑后承（所有满足 `C` 的解也满足的约束）。
这是 `RealFCAInstance.constraint_entailment_closure` 的 **LHS**，单列以便引用。 -/
def entailmentSet (C : Set RealConstraint) : Set RealConstraint :=
  intent constraintSatRel (extent constraintSatRel C)

/-- ⭐ **后承 = 内涵闭包**（直接引用 `RealFCAInstance` 的定理，非重证）。

`entailmentSet C` 恰等于「所有满足 `C` 的解也满足的约束集」——
即 `RealFCAInstance.constraint_entailment_closure` 的**逐字内容**
在 `constraintSatRel` 记法下的重述引用。 -/
theorem entailmentSet_eq_closure (C : Set RealConstraint) :
    entailmentSet C =
      {c : RealConstraint |
        ∀ x : ℝ, x ∈ extent constraintSatRel C → constraintSatRel x c} :=
  constraint_entailment_closure C

/-- ⭐⭐ **外延（解集）对单约束缩放不变**（本文件的核心内容）。

约束 `c` 与它的缩放 `{a := c.a * lam, b := c.b * lam}`（`lam ≠ 0`）
在**满足关系**下**挑出同一个解集**（外延相同）。

⚠ **为什么这不是重述**：它是**两条此前从未被放在一起的定理的合成** ——
`RealLinear.real_scale_preserves`（缩放保持满足语义）
+ `RealFCA.extent` 的**外延语义**（`extent R B = {o | ∀ a ∈ B, R o a}`）。
本定理把「缩放不变性」从**单点满足命题**提升为**外延集合等式**。 -/
theorem extent_scaled_eq (c : RealConstraint) (lam : ℝ) (hlam : lam ≠ 0) :
    extent constraintSatRel ({c} : Set RealConstraint) =
      extent constraintSatRel ({ { a := c.a * lam, b := c.b * lam } } :
        Set RealConstraint) := by
  ext x
  constructor
  · intro hx
    have h1 : constraintSatRel x c := hx c (Set.mem_singleton c)
    have h2 : RealConstraintSat c x := h1
    have h3 : RealConstraintSat { a := c.a * lam, b := c.b * lam } x :=
      (real_scale_preserves c x lam hlam).mp h2
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    subst hc'
    exact h3
  · intro hx
    have h1 : constraintSatRel x { a := c.a * lam, b := c.b * lam } :=
      hx _ (Set.mem_singleton _)
    have h3 : RealConstraintSat { a := c.a * lam, b := c.b * lam } x := h1
    have h2 : RealConstraintSat c x :=
      (real_scale_preserves c x lam hlam).mpr h3
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    subst hc'
    exact h2

/-- ⭐⭐ **后承集对单约束缩放不变**（`RealFCAInstance` × `RealLinear` 的合成，本文件核心定理）。

`entailmentSet {c}` 是 `c` 的全部**逻辑后承**
（`RealFCAInstance.constraint_entailment_closure`：= `intent(extent {c})`）。
本定理证明：**缩放 `c` 不改变它的后承集** ——
因为 `extent` 不变（上一条），而 `intent` 只依赖 `extent`。

⇒ ⭐ **这是缺口 B 的"语义侧"读数**：提取候选的**语法**不唯一
（`RealCompileExtractClosed.validity_does_not_determine_syntax`），
但**后承（语义）唯一** —— 两者**同时成立**，且**首次被放进同一条依赖链**。 -/
theorem entailmentSet_scaled_eq (c : RealConstraint) (lam : ℝ) (hlam : lam ≠ 0) :
    entailmentSet ({c} : Set RealConstraint) =
      entailmentSet ({ { a := c.a * lam, b := c.b * lam } } : Set RealConstraint) := by
  unfold entailmentSet
  rw [extent_scaled_eq c lam hlam]

/-- ⭐ **后承不变 + 语法改变【同时】成立**（本文件的收束定理，缺口 B 的精确陈述）。

存在两个**不同**的约束 `c ≠ c'`，它们：
① **语法不同**（`c ≠ c'`）；
② **语义相同**（满足集 / 外延相同）；
③ 因而**后承集相同**。

⚠ **诚实标注**：①的见证来自 `RealCompileExtractClosed.validity_does_not_determine_syntax`
的同类构造（`c = {a := [1], b := 1}`、`c' = scaleVec c 2`，⚠ 位于 **`Int` 版**
`VectorConstraint`，与本文件的 **`ℝ` 版** `RealConstraint` **不是同一个类型**）——
故本定理的 ① 用 `ℝ` 版**自行构造**见证：`c = {a := 1, b := 1}`、
`c' = {a := 1 * 2, b := 1 * 2} = {a := 2, b := 2}`，二者 `b` 分量 `1 ≠ 2`。
⇒ 这把「语法不唯一 ∧ 语义唯一」在**同一个类型上**钉住，**不需要**跨类型类比。 -/
theorem syntax_differs_semantics_same :
    ∃ c c' : RealConstraint, c ≠ c' ∧
      extent constraintSatRel ({c} : Set RealConstraint) =
        extent constraintSatRel ({c'} : Set RealConstraint) := by
  refine ⟨{ a := 1, b := 1 }, { a := 1 * 2, b := 1 * 2 }, ?_, ?_⟩
  · -- 语法不同：`b` 分量 `1 ≠ 1 * 2`
    intro h
    have hb : (1 : ℝ) = 1 * 2 := congrArg RealConstraint.b h
    norm_num at hb
  · -- 语义相同：`c'` 恰是 `c` 的 `lam = 2` 缩放
    have h2 : (1 : ℝ) * 2 = 2 := by norm_num
    have := extent_scaled_eq ({ a := 1, b := 1 } : RealConstraint) 2 (by norm_num)
    simpa using this

/-! ## 四、⭐⭐ 三态穷尽在约束世界里的落地（真正用到 `RealTemporalLayer`）

`RealTemporalLayer.element_or_concept` 给出：任一呈现**要么**是要素**要么**是概念。
本节把它落到**约束世界**：任一解 `x` 关于任一约束集 `C`，
在其中呈现为要素（无上位）或概念（有上位）——
这给出"**提取候选是否成立**"的**可判定判据**
（`RealTemporalLayer` 文档 §九「发现 1」已如实标注该判据的强度）。 -/

/-- **约束世界里的三态穷尽**：任一解关于任一满足关系，
要么无上位（要素），要么有上位（概念）。 -/
theorem constraint_element_or_concept (x : ℝ) :
    isElementUnderUpGaze constraintSatRel x ∨ isConceptUnderUpGaze constraintSatRel x :=
  up_gaze_element_or_concept constraintSatRel x

/-- ⭐ **「为什么某物是要素」在约束世界里可陈述**（`RealTemporalLayer` 用途 3）。

`x` 在当前论域下呈现为**要素** ⟺ 它**不被任何约束所捕获**
（不存在约束 `c` 使 `x` 满足 `c`）。

⚠ **诚实标注**：本命题是 `Iff.rfl`（`isElementUnderUpGaze` **就是** `¬ hasUpper`）——
**它的价值在【陈述】而非难度**（`RealTemporalLayer` §九「发现 1」已如实登记）。
此处如实沿用该标注，**不冒充实质定理**。 -/
theorem constraint_element_iff_no_upper (x : ℝ) :
    isElementUnderUpGaze constraintSatRel x ↔
      ¬ ∃ c : RealConstraint, RealConstraintSat c x :=
  Iff.rfl

/-- ⭐ **要素 ⟺ 任何非空约束集都拆不出它**（复用 `RealTemporalLayer.no_upper_iff_no_split`）。

⚠ **陈述里的「非空」不可省**：空约束集对**任意** `x` 都成立（空洞为真），
故去掉非空性后命题**为假** —— 这正是 `RealTemporalLayer` 已显式登记的陷阱。 -/
theorem constraint_element_iff_no_split (x : ℝ) :
    isElementUnderUpGaze constraintSatRel x ↔
      ∀ C : Set RealConstraint, C.Nonempty → x ∉ extent constraintSatRel C :=
  no_upper_iff_no_split constraintSatRel x

/-! ## 五、悬置：撤回目光后身份消解（真正用到 `RealTemporalLayer`）

`RealTemporalLayer.suspend`（法则 5）：撤回目光，概念退回要素 ——
**对象还在，身份消解**。本节给出它在**约束世界**的读数，
并把它与 §二 的纤维接起来：**悬置不改变基底，但消解纤维身份**。 -/

/-- **悬置不改变基底**：撤回目光后，解 `x` 本身不变（体系原理 1「同一张脸」）。 -/
theorem constraint_suspend_preserves_base (t : Temporal ℝ RealConstraint constraintSatRel) :
    (suspend t).base = t.base :=
  suspend_preserves_base t

/-- **悬置消解身份**：撤回目光后必定呈现为要素（法则 5「身份消解」）。 -/
theorem constraint_suspend_dissolves_identity
    (t : Temporal ℝ RealConstraint constraintSatRel) : IsElement (suspend t) :=
  suspend_dissolves_identity t

/-- ⭐ **悬置幂等**：悬置两次 = 悬置一次（撤回不是遗忘，是不再持有那束目光）。 -/
theorem constraint_suspend_idempotent
    (t : Temporal ℝ RealConstraint constraintSatRel) :
    suspend (suspend t) = suspend t :=
  suspend_idempotent t

/-! ## 六、注：本文件与既有文件的衔接

- **只读引用**，不修改任何既有文件；尤其**不碰** `RealCanonicalForm.lean`
  （正被 CANON 代理编辑）；
- 本文件与 `RealCanonicalForm` 是**语义侧 / 语法侧的关系**：
  后者构造 `canonicalize`（轨道代表元），本文件证**后承在轨道上不变**
  （故"取哪个代表元"对**语义**无影响）；
- ⚠ 本文件**不依赖** `RealCanonicalForm` 的任何断言（该文件尚无 olean、正在编辑），
  故**不会**制造对活跃编辑文件的依赖。 -/

end Lattice
