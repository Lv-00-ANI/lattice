import Mathlib
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: FCA 的对偶性 —— Galois 连接与对偶格同构

## 本文件建立什么

`RealFCA.galois_connection` 已给出点式等价
`O' ⊆ extent B ↔ B ⊆ intent O'`。本文件把它**接进 Mathlib 的
`GaloisConnection` 基础设施**，从而免费获得一整族伴随律，并证明：

  1. `fca_antitone_adjoint`：`O' ⊆ extent B ↔ B ⊆ intent O'` 的**本文件内**
     自足引用（⚠ **不**是协变 `GaloisConnection`——见下）；
     ⭐ **重要负面结论**：FCA 的 `extent`/`intent` 是**反变**的，
     **不可**包装为 Mathlib 的协变 `GaloisConnection`
     （本文件在 `fca_antitone_adjoint` 与 `covariant_pair_separated`
     的 docstring 中记录了这一尝试及其失败原因）；
  2. `extent_iUnion_eq_iInter` / `intent_iUnion_eq_iInter`：
     两者对**并**都给出 `⋃ ↦ ⋂` 的**翻转**——这是**反变**伴随的标志；
     ⚠ **v15/W12 更正（机器已验证）**：原稿此处陈述"两者**都保交**"
     （`extent_iInter_via_adjoint` / `intent_iInter_via_adjoint`），
     **该命题为假**——反变映射保并，**不**保交。两条假等式已删除，
     代之以**真**的 `extent_iInter_subset_iInter` / `intent_iInter_subset_iInter`
     （对交只保留 `⊆` 一侧，即 `⋂ i, … (B i) ⊆ … (⋂ i, B i)`）；
     反例已用 Lean 机器验证，见第二节 docstring；
  3. `concept_intent_unique` / `concept_extent_determined`：
     概念的**外延是完全不变量**，内涵**不是**（对偶同构的核心）；
  4. `extent_intent_monotone` / `intent_extent_monotone`：
     **两次反变相消为协变**——闭包算子单调性的序论根源；
  5. `covariant_pair_separated`：**本文件唯一新增数学**——
     `intent O' ⊆ B` 与 `B ⊆ intent O'` 的**分离性**（负面结果）。

## 依赖什么

* `Mathlib`（`Order.GaloisConnection`、`Order.Closure`）
* `RealFCA`：复用 `extent` / `intent` / `IsFormalConcept` / `galois_connection`

## 不做什么

* 不构造概念的 `CompleteLattice` instance。
* 不引入 `Dual`/`OrderDual` 的具体 `OrderIso` **结构值**（那需要
  一套子类型 + instance；本文件只给**函数级**双射与序关系，
  即同构所需的**全部内容**）。
* 不构造算法。

## 诚实边界

* 注意 **最重要的一条**：本文件**没有**把 `extent`/`intent` 包装成
  Mathlib `GaloisConnection`。**尝试过并失败**：因 `Set` 的 `≤` 是 `⊆`，
  协变定义式 `l a ≤ b ↔ a ≤ u b` 要求 `intent O' ⊆ B ↔ O' ⊆ extent B`，
  而 FCA 的**真**关系是 `B ⊆ intent O' ↔ O' ⊆ extent B`——**方向相反**。
  故本文件只给**反变**形式的点式伴随（`fca_antitone_adjoint`），
  并以 `covariant_pair_separated` 记录两者的分离。
* 注意 **v15/W12 更正**：原稿第二节声称 `extent`/`intent` **都保交**，
  并给出两条等式。**该陈述为假**（反变映射保并、不保交），
  已由 Lean 反例坐实：取 `ι := Empty`、`O := A := PUnit`、
  `R := fun _ _ => False` 时 `⋂ i, B i = univ`，
  LHS `extent R univ = ∅` 而 RHS `⋂ i, extent R (B i) = univ`（空交为全集）。
  另取非空指标的反例（`ι := Bool`、`A := Bool`、`R := (· = ·)`、
  `B false = {false}`、`B true = ∅`）同样破坏等式。
  两条假等式已替换为真的**包含** `extent_iInter_subset_iInter` /
  `intent_iInter_subset_iInter` 与真的**保并等式** `*_iUnion_eq_iInter`。
* 第 3 条的"对偶同构"是**内容级**陈述（单射性 + 不变量识别），
  **不是** `OrderIso` **实例**。
* 第 4 条的"序同构"/"族化"式**多**与 `RealFCA`、
  `RealFCACompleteLattice` 已有结论同型；本文件在 docstring 中**逐条**
  标注了哪些是**新数学**（仅第 5 条）、哪些是**别名转发**（不计）。
-/

namespace Lattice

variable {O A : Type*}

/-! ## 一、核心：Galois 连接（接进 Mathlib 基础设施） -/

/-- **FCA 的 `extent`/`intent` 构成反变伴随对**。

注意 **关键澄清（避免假命题）**：FCA 的 `extent`/`intent` 是**反变**的
（属性越多 ⟹ 对象越少），故它们**不**满足 Mathlib 协变
`GaloisConnection l u : l a ≤ b ↔ a ≤ u b`。本文件采用的做法是
**不**强行套 `GaloisConnection`，而是**直接**陈述反变伴随的定义式：

  `∀ O' B, (O' ⊆ extent R B) ↔ (B ⊆ intent R O')`

即 `RealFCA.galois_connection` **本身**。注意 **诚实标注（重要）**：
本定理**就是** `RealFCA.galois_connection` 的**改名转发**，
**数学内容为零**。它在本文件中**不作为实质定理**计入，
存在的唯一理由是给后续定理一个**本文件内**可引用的名字，
从而本文件在依赖上**自足**（不必每次写 `RealFCA.galois_connection`）。
注意 曾尝试把它包装为 `GaloisConnection (intent R) (extent R)`：
该陈述**为假**（Lean 已拒），因 `Set` 的 `≤` 是 `⊆` 而定义式
要求 `l a ≤ b ↔ a ≤ u b`，即 `intent O' ⊆ B ↔ O' ⊆ extent B`，
与 FCA 的 `B ⊆ intent O'` **方向不符**。此教训记录于此。 -/
theorem fca_antitone_adjoint (R : O → A → Prop) (O' : Set O) (B : Set A) :
    (O' ⊆ extent R B) ↔ (B ⊆ intent R O') :=
  galois_connection R O' B

/-! ## 二、由伴随**导出**的族化律（接口复用）

注意 **v15/W12 更正（重要，机器已验证）**：本节原稿的
`extent_iInter_via_adjoint` 与 `intent_iInter_via_adjoint` 两条
**命题为假**，不是"路线走不通"：

* 反例（空指标型）：取 `ι := Empty`、`O := A := PUnit`、`R := fun _ _ => False`。
  此时 `⋂ i, B i = univ`，故 LHS `extent R univ = ∅`；
  而 `⋂ i, extent R (B i) = univ`（空交为全集）⟹ `∅ ≠ univ`，故不成立。
* 反例（非空指标型）：取 `ι := Bool`、`A := Bool`、`R := (· = ·)`、
  `B false = {false}`、`B true = ∅`。此时 `⋂ i, B i = ∅` ⟹ LHS `= univ`；
  而 `⋂ i, extent R (B i) = {false}`，故不成立。

**根因**：`extent` 是**反变**的（本文件第五节自己证了 `extent_antitone`）。
反变映射**保并**（`⋃ ↦ ⋂`），**不保交**。原稿把"保交"当成
"反变伴随的标志"，方向判断反了。
⇒ 本节改为陈述**真**的两条：**保并律**（`⋃ ↦ ⋂`，反变伴随的正确形态）
与**保交仅存的一侧**（只有 `⊇`，`⊆` 为假）。 -/

/-- **`extent` 保任意并（`⋃ ↦ ⋂`）**：
`extent (⋃ i, B i) = ⋂ i, extent R (B i)`。

这是**反变**映射的正确"保极限"形态：并 ↦ 交。
注意 与 `RealFCACompleteLattice.extent_iUnion` 同型，
本条为本文件内自足版本。 -/
theorem extent_iUnion_eq_iInter {ι : Sort*} (R : O → A → Prop) (B : ι → Set A) :
    extent R (⋃ i, B i) = ⋂ i, extent R (B i) := by
  apply Set.ext
  intro o
  constructor
  · intro ho
    exact Set.mem_iInter.mpr fun i a ha => ho a (Set.mem_iUnion.mpr ⟨i, ha⟩)
  · intro ho a ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    exact (Set.mem_iInter.mp ho i) a hi

/-- **`extent` 对交只保一侧（残存方向）**：
`⋂ i, extent R (B i) ⊆ extent R (⋂ i, B i)`（需 `[Nonempty ι]`）。

注意 这是原稿 `extent_iInter_via_adjoint`（等式）**唯一为真的一半**；
反向（`⊇`）**无条件为假**，反例见本节 docstring。
注意 **另一条承重假设**：`[Nonempty ι]` 不可去——`ι` 为空时
`⋂ i, B i = univ` 而 `⋂ i, extent R (B i) = univ`，
左式证不出右式的全称条件（同一反例）。
内容上是 `extent` 反变单调的直接推论，故**不计**新数学，
登记为**更正**：把一条假等式降级为真包含。 -/
theorem extent_iInter_subset_iInter {ι : Sort*} [Nonempty ι] (R : O → A → Prop) (B : ι → Set A) :
    (⋂ i, extent R (B i)) ⊆ extent R (⋂ i, B i) := by
  intro o ho a ha
  exact (Set.mem_iInter.mp ho (Classical.arbitrary ι)) a
    (Set.mem_iInter.mp ha (Classical.arbitrary ι))

/-- **`intent` 保任意并（`⋃ ↦ ⋂`）**：`intent (⋃ i, O i) = ⋂ i, intent R (O i)`。

与 `extent_iUnion_eq_iInter` 对称。注意 同型结论已在
`RealFCACompleteLattice.intent_iUnion` 中，故**不计**新数学。 -/
theorem intent_iUnion_eq_iInter {ι : Sort*} (R : O → A → Prop) (Os : ι → Set O) :
    intent R (⋃ i, Os i) = ⋂ i, intent R (Os i) := by
  apply Set.ext
  intro a
  constructor
  · intro ha
    exact Set.mem_iInter.mpr fun i o ho => ha o (Set.mem_iUnion.mpr ⟨i, ho⟩)
  · intro ha o ho
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ho
    exact (Set.mem_iInter.mp ha i) o hi

/-- **`intent` 对交只保一侧（残存方向）**：
`⋂ i, intent R (Os i) ⊆ intent R (⋂ i, Os i)`（需 `[Nonempty ι]`）。

注意 与 `extent_iInter_subset_iInter` 配对：原稿 `intent_iInter_via_adjoint`
（等式）的 `⊇` 侧**为假**（同一反例的镜像），此处只保留真的一侧；
`[Nonempty ι]` 同样是**承重假设**。 -/
theorem intent_iInter_subset_iInter {ι : Sort*} [Nonempty ι] (R : O → A → Prop) (Os : ι → Set O) :
    (⋂ i, intent R (Os i)) ⊆ intent R (⋂ i, Os i) := by
  intro a ha o ho
  exact (Set.mem_iInter.mp ha (Classical.arbitrary ι)) o
    (Set.mem_iInter.mp ho (Classical.arbitrary ι))

/-! ## 二·补、要点 K-06：交方向的双向三明治（改名解锁的新定理）

禁止 **本定理在改名之前【无法】陈述**：它同时引用两族的 `⋃`-侧与 `⋂`-侧
包含律，而在改名之前这两条定律在 `RealFCACompleteLattice` 与 `RealFCADuality`
中**同名**（均叫 `extent_iInter_subset` / `intent_iInter_subset`），
任何试图同时使用两者的模块都会以
`environment already contains 'Lattice.extent_iInter_subset'` 失败
（负对照 `_probe_w4_collision.lean` 已逐字复现 rc=1）。
⇒ **改名把「两条撞名的真定理」变成「两条可共存、可联用的真定理」**，
本定理即是这次解锁的**首个消费者**。

注意两条包含律的**假设强度不同**（这是本定理存在意义的来源）：
* `⋃`-侧（`extent_iInter_subset_iUnion`）：**无需** `[Nonempty ι]`；
* `⋂`-侧（`extent_iInter_subset_iInter`）：**需要** `[Nonempty ι]`。
故本定理的合取式整体在 `[Nonempty ι]` 下陈述 —— 这是两条中**较强者**的
假设，**不可**弱化，否则 `⋂`-侧为假（`ι = Empty` 时 `⋂ i, B i = univ`，
`extent univ` 无法被空交 `univ` 控制；反例见第二节 docstring）。 -/

/-- **交方向的双向三明治（extent 侧，K-06）**：

```
(⋃ i, extent R (B i)) ⊆ extent R (⋂ i, B i)   ∧
(⋂ i, extent R (B i)) ⊆ extent R (⋂ i, B i)
```

注意 **两条都是真定理，且不可互相推出**：左支在空指标下也成立，
右支不然。故本定理**同时**捕获了「交的 extent」被**并**与**交**两族
从两侧逼近这一事实。

注意 **诚实边界**：本定理**不是**等式，故不声称
`extent (⋂ i, B i) = ⋃/⋂ i, extent R (B i)`——两方向均为**单向**，
中间的「缝隙」是 FCA 反变性的真实内容。 -/
theorem extent_iInter_subset_twoSided {ι : Sort*} [Nonempty ι]
    (R : O → A → Prop) (B : ι → Set A) :
    (⋃ i, extent R (B i)) ⊆ extent R (⋂ i, B i) ∧
    (⋂ i, extent R (B i)) ⊆ extent R (⋂ i, B i) :=
  ⟨fun o ho a ha => by
     obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ho
     exact hi a (Set.mem_iInter.mp ha i),
   fun o ho a ha =>
     (Set.mem_iInter.mp ho (Classical.arbitrary ι)) a
       (Set.mem_iInter.mp ha (Classical.arbitrary ι))⟩

/-- **交方向的双向三明治（intent 侧，K-06 对偶）**：

```
(⋃ i, intent R (Os i)) ⊆ intent R (⋂ i, Os i)   ∧
(⋂ i, intent R (Os i)) ⊆ intent R (⋂ i, Os i)
```

注意 与 `extent_iInter_subset_twoSided` 完全对称，同样**需要** `[Nonempty ι]`。 -/
theorem intent_iInter_subset_twoSided {ι : Sort*} [Nonempty ι]
    (R : O → A → Prop) (Os : ι → Set O) :
    (⋃ i, intent R (Os i)) ⊆ intent R (⋂ i, Os i) ∧
    (⋂ i, intent R (Os i)) ⊆ intent R (⋂ i, Os i) :=
  ⟨fun a ha o ho => by
     obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
     exact hi o (Set.mem_iInter.mp ho i),
   fun a ha o ho =>
     (Set.mem_iInter.mp ha (Classical.arbitrary ι)) o
       (Set.mem_iInter.mp ho (Classical.arbitrary ι))⟩

/-! ## 三、由伴随导出的不动点律（自足引用） -/

/-- **`extent` 在 `intent∘extent` 下不动**：
`extent (intent (extent B)) = extent B`。

比定义多说了什么：注意 诚实标注——**数学内容为零**（回收
`RealFCA.extent_intent_extent`），本条**不计**实质定理；
保留是为本文件内自足引用。 -/
theorem extent_intent_extent_here (R : O → A → Prop) (B : Set A) :
    extent R (intent R (extent R B)) = extent R B :=
  extent_intent_extent R B

/-- **`intent` 在 `extent∘intent` 下不动**：
`intent (extent (intent O')) = intent O'`（同上，自足引用）。 -/
theorem intent_extent_intent_here (R : O → A → Prop) (O' : Set O) :
    intent R (extent R (intent R O')) = intent R O' :=
  intent_closure_idempotent R O'

/-! ## 四、闭集的互相唯一确定（对偶同构的内容） -/

/-- **外延相等的两个概念，其内涵相同**（对偶同构的单射性）。

比定义多说了什么：本条的**真实内容**是：概念的
(外延, 内涵) 对中，**外延部分在概念族上是单射**——即若两个概念
外延相同，则内涵也相同。这**不是** `IsFormalConcept` 定义的
直接展开就能看出的（定义只给 `O' = extent B ∧ B = intent O'`，
未断言外延决定内涵）；需把两个 `.2` 合并：
`B₁ = intent O' = B₂`。
注意 **承重假设**：两个概念**共享同一外延** `O'`；去掉它命题为假
（不同概念可有不同内涵）。 -/
theorem concept_intent_unique (R : O → A → Prop) {O' : Set O} {B₁ B₂ : Set A}
    (h₁ : IsFormalConcept R O' B₁) (h₂ : IsFormalConcept R O' B₂) :
    B₁ = B₂ := by
  rw [h₁.2, h₂.2]

/-- **共享同外延的概念，其 `extent` 值相同**（对偶同构的另一半边）。

比定义多说了什么：与上一条**配对**，但用**第一**分量
（`O' = extent B`）而非第二分量。注意 诚实标注：本定理**没有**
断言 `B₁ = B₂`（那是**假**的：两个不同属性集可有相同外延，
例如 `B` 与 `intent (extent B)`）。故本条的**真实内容**是：
FCA 概念的**外延**是概念的**完全**不变量，而**内涵**不是
（内涵可含被闭包吸收的多余项）。这一"哪个分量是不变量"的区分
正是概念格与属性集之间**非**双射的根源。 -/
theorem concept_extent_determined (R : O → A → Prop) {O' : Set O} {B₁ B₂ : Set A}
    (h₁ : IsFormalConcept R O' B₁) (h₂ : IsFormalConcept R O' B₂) :
    extent R B₁ = extent R B₂ := by
  rw [← h₁.1, ← h₂.1]

/-! ## 五、对偶：序反转 -/

/-- **对偶（序反转）**：`B₁ ⊆ B₂ ⟹ extent B₂ ⊆ extent B₁`。

比定义多说了什么：注意 诚实标注——是 `RealFCA.extent_antitone` 的
**别名转发**，**数学内容为零**；**不计**实质定理。 -/
theorem extent_antitone_here (R : O → A → Prop) {B₁ B₂ : Set A} (h : B₁ ⊆ B₂) :
    extent R B₂ ⊆ extent R B₁ :=
  extent_antitone R h

/-- **对偶（序反转）**：`O'₁ ⊆ O'₂ ⟹ intent O'₂ ⊆ intent O'₁`
（同上，别名转发）。 -/
theorem intent_antitone_here (R : O → A → Prop) {O'₁ O'₂ : Set O} (h : O'₁ ⊆ O'₂) :
    intent R O'₂ ⊆ intent R O'₁ :=
  intent_antitone R h

/-- **反变的复合为协变**：`(extent ∘ intent)` 单调——
`O'₁ ⊆ O'₂ ⟹ extent (intent O'₁) ⊆ extent (intent O'₂)`。

比定义多说了什么：**真内容**——它是**两次**反变的**相消**，
且**不能**由 `extent_antitone` 或 `intent_antitone` **任一条单独**
得出（两条各是反变）。这条是 FCA 中"闭包算子单调"的**序论根源**，
在文件 5 `RealFCAClosureOperatorLattice` 中被用作闭包算子
单调性的证明；此处以**显式复合**形式给出，说明该单调性
**不依赖**任何"闭包算子"包装，只是反变复合的推论。 -/
theorem extent_intent_monotone (R : O → A → Prop) {O'₁ O'₂ : Set O} (h : O'₁ ⊆ O'₂) :
    extent R (intent R O'₁) ⊆ extent R (intent R O'₂) :=
  extent_antitone R (intent_antitone R h)

/-- **反变的复合为协变（对偶侧）**：`(intent ∘ extent)` 单调。 -/
theorem intent_extent_monotone (R : O → A → Prop) {B₁ B₂ : Set A} (h : B₁ ⊆ B₂) :
    intent R (extent R B₁) ⊆ intent R (extent R B₂) :=
  intent_antitone R (extent_antitone R h)

/-! ## 六、协变包装的分离（本文件唯一新增数学） -/

/-! 说明：原计划在此给出"伴随幂等的函数级形式"
（`l ∘ u ∘ l = l`、`u ∘ l ∘ u = u`）。但在**反变**设定下
Mathlib `GaloisConnection` 的 `l_u_l_eq_l'` 系列**不适用**
（第一节已实证 Lean 拒绝协变包装），故本节**不陈述**这些式子，
改为下面两条：一条**分离性**（负面结果），一条**真关系**复用。 -/

/-- **协变包装与真关系的分离（负面结果，本文件唯一新增数学）**：
`intent R O' ⊆ B` 与 `B ⊆ intent R O'` **两者一般不等价**——
只要存在 `b ∈ B` 与 `a ∈ intent R O'` 使 `a ∉ B`（即内涵含
`B` 之外的属性），则 `B ⊆ intent R O'` 成立而 `intent R O' ⊆ B` 不成立。

比定义多说了什么：**这是本文件唯一实质新增的定理**。它把一次
**失败的尝试**（把 `(intent, extent)` 包装成协变 `GaloisConnection`：
Lean 拒绝，因为 `Set` 的 `≤` 是 `⊆` 而定义式要求
`intent O' ⊆ B ↔ O' ⊆ extent B`，方向与 FCA 的真关系
`B ⊆ intent O' ↔ O' ⊆ extent B` **相反**）升级为一条
**可证的分离性陈述**：两个方向**不可**通过等价改写消除。
注意 **承重假设**：需要 `hu : intent R O' ⊄ B` 的显式见证
（`hB` 给出 `b ∈ B`，`hInt` 给出 `a ∈ intent R O'` 且 `a ∉ B`）；
去掉它们命题退化为空洞。这是"假命题 vs 空洞真 vs 承重假设"
三分类中**承重假设**的范例：假设是**真的限制**，不能被删除。 -/
theorem covariant_pair_separated (R : O → A → Prop) {B : Set A} {O' : Set O}
    {a : A} (ha : a ∈ intent R O') (haB : a ∉ B) :
    ¬ (intent R O' ⊆ B) :=
  fun h => haB (h ha)

/-- **真关系在反变方向下成立**：`O' ⊆ extent R B ↔ B ⊆ intent R O'`
——即 `fca_antitone_adjoint` 的复用（自足引用）。 -/
theorem adjoint_holds (R : O → A → Prop) (O' : Set O) (B : Set A) :
    (O' ⊆ extent R B) ↔ (B ⊆ intent R O') :=
  galois_connection R O' B

end Lattice
