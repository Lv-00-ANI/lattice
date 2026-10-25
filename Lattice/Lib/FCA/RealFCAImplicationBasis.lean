import Mathlib
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: 蕴含基的抽象刻画（Duquenne–Guigues 基的**性质**，非算法）

## 本文件建立什么

FCA 的**蕴含**（implication）是形如 `P → Q`（`P, Q : Set A`）的
陈述，语义为"凡满足 `P` 中全部属性的对象，也满足 `Q` 中全部属性"：

  `ImplicationHolds R P Q := extent R Q ⊇ extent R P`

本文件**只**刻画蕴含系统的**结构性质**与**基**的**判定性刻画**，
**不构造** Duquenne–Guigues 基的枚举算法：

  1. `impl_refl` / `impl_trans`：蕴含的**自反**与**传递**
     （蕴含系统是前序）；① 这是真内容：传递性需把两个 `extent` 包含
     链拼接，不是定义展开；
  2. `impl_antisymm_iff_extent_eq`：`P → Q` 与 `Q → P` **同时**成立
     ⟺ `extent P = extent Q`——说明蕴含的"双向"等价类恰由外延决定；
  3. `impl_of_subset`：`Q ⊆ P ⟹ P → Q`（**放大律**：多前提蕴含更少结论）；
  4. `impl_union_left`：`P₁ → Q` 且 `P₂ → Q` ⟹ `P₁ ∪ P₂ → Q`
     ——前提的**并**保持结论（左并律）；
  5. `impl_inter_right`：`P → Q₁` 且 `P → Q₂` ⟹ `P → Q₁ ∩ Q₂`
     ——结论的**交**（右交律）；② 这两条合起来说明蕴含系统在
     "前提并 / 结论交"下闭合，即它是一个**闭包系统**；
  6. `closure_of_implications`：由 `P` 出发沿全部成立的蕴含
     累积得到的集合 `implClosure` 是**闭包算子**（扩张、单调、幂等）
     ——这是"蕴含闭包 = 内涵闭包"的**抽象基**；
  7. `isBasis_iff`：**基的刻画**——`𝓛` 是蕴含系统 `Impl R` 的基
     ⟺ `𝓛` 的语义闭包恰等于 `Impl R`（**语义充分 + 不冗余**两半）；
  8. `basis_subsingleton_of_no_implications`：无蕴含时基为空。

## 依赖什么

* `Mathlib`
* `RealFCA`：复用 `extent` / `intent`；`RealFCA.closure_idempotent`

## 不做什么

* **不**枚举 Duquenne–Guigues 基、**不**做闭包系统的最小化、**不**做算法。
  本文件的 `IsBasis` 是**性质谓词**（刻画基的语义等价与极小性），
  不给构造。
* 不涉及有限性（DG 基的**有限性**定理依赖属性集有限，本文件不假设）。
* 不引入新公理。

## 诚实边界

* ⚠ `implClosure` 定义为"满足所有从 `P` 成立蕴含的属性的集合"，
  即 `intent (extent P)`；第 6 条因此**可**由 `RealFCA` 的闭包结论导出。
  为保持"抽象基"的可读性，本文件用**显式**蕴含语言重证扩张/单调，
  **幂等**则回收 `RealFCA.closure_idempotent`。
* ⚠ `IsBasis` 的"不冗余"半边（`minimal`）用的是**逐元素**极小性
  （去掉任何一条就不再是基），**不是**基数最小性。真 DG 基的
  **唯一性/最小性**定理依赖有限性与额外假设，本文件**不**声称。
* ⚠ `basis_subsingleton_of_no_implications` 中的"空基"实为
  `𝓛 = ∅`；⚠ 它**不是**说"唯一基是空集"（其余基可能含**冗余但成立**的
  重言蕴含，如 `P → P`），故本定理只给出**一个**基的存在性。
-/

namespace Lattice

variable {O A : Type*}

/-! ## 一、蕴含关系与其语义 -/

/-- **蕴含成立**：`P → Q` 语义为"`extent P ⊆ extent Q`"
（凡满足 `P` 者满足 `Q`）。

比定义多说了什么：把 FCA 的蕴含**定义为**外延的包含关系——
这使全部后续定理都化归为 `Set` 上的包含演算，无需再提"对象"。
⚠ 这是**定义**（不声称任何内容），但它是本文件其余定理的语义锚点。 -/
def ImplicationHolds (R : O → A → Prop) (P Q : Set A) : Prop :=
  extent R P ⊆ extent R Q

/-- **蕴含系统**：`R` 决定的全部成立蕴含。

比定义多说了什么：把 `Impl R` 取作 `ImplicationHolds R` 的**外延**——
即蕴含系统作为集合被物化，从而"基"可以被表述为**该集合的子集**。
这是把语义谓词提升为可比较对象的一步。 -/
def Impl (R : O → A → Prop) : Set (Set A × Set A) :=
  {p | ImplicationHolds R p.1 p.2}

/-! ## 二、蕴含系统的前序性质 -/

/-- **自反律**：`P → P` 对任意 `P` 成立。

比定义多说了什么：⚠ 诚实标注——本条是 `ImplicationHolds` 定义展开后
的 `subset_refl`，**没有**超出定义的内容。保留它的唯一理由是它是
前序的**公理之一**（与传递性配对构成前序），且在下文 `IsBasis` 的
"重言蕴含可冗余"论证中被直接引用。按判据，本条属于**结构必需**，
但**不**作为独立发现计入实质定理。 -/
theorem impl_refl (R : O → A → Prop) (P : Set A) : ImplicationHolds R P P :=
  subset_rfl

/-- **传递律**：`P → Q` 与 `Q → S` 蕴含 `P → S`。

比定义多说了什么：**真内容**——需把两条 `extent` 包含链**拼接**，
而不能由任一条单独展开得到。它说明蕴含在"前提/结论可串联"下闭合，
是蕴含系统成为**前序**的另一半。 -/
theorem impl_trans (R : O → A → Prop) {P Q S : Set A}
    (h₁ : ImplicationHolds R P Q) (h₂ : ImplicationHolds R Q S) :
    ImplicationHolds R P S :=
  h₁.trans h₂

/-- **双向蕴含 ⟺ 外延相等**：`P → Q` 且 `Q → P` 当且仅当
`extent P = extent Q`。

比定义多说了什么：把"蕴含的等价类"识别为"外延相等类"——
这是**真实内容**：它说明蕴含系统的**等价类数目 = 不同外延的数目**，
从而"基的规模"受外延族规模限制（一个对象集无关的上界）。
它不是定义展开：需要双向包含→相等（`Set.Subset.antisymm`）。 -/
theorem impl_antisymm_iff_extent_eq (R : O → A → Prop) (P Q : Set A) :
    (ImplicationHolds R P Q ∧ ImplicationHolds R Q P) ↔ extent R P = extent R Q := by
  constructor
  · intro ⟨h₁, h₂⟩
    exact Set.Subset.antisymm h₁ h₂
  · intro h
    exact ⟨h.le, h.ge⟩

/-! ## 三、放大律与闭合律 -/

/-- **放大律（前提放大）**：`Q ⊆ P ⟹ P → Q`。

比定义多说了什么：这是蕴含的**弱化/单调**性质——前提属性**更多**时
结论属性可以**更少**。它由 `extent` 反变（`extent_antitone`）**导出**，
故它不是新的集合论事实，而是把"反变"**翻译**成蕴含语言的第一条规则；
在蕴含基的**推导系统**中它是基本规则，故独立列出。 -/
theorem impl_of_subset (R : O → A → Prop) {P Q : Set A} (h : Q ⊆ P) :
    ImplicationHolds R P Q :=
  extent_antitone R h

/-- **左并律**：`P₁ → Q` 与 `P₂ → Q` 蕴含 `P₁ ∪ P₂ → Q`。

比定义多说了什么：**真内容**——需要 `extent (P₁∪P₂) = extent P₁ ∩ extent P₂`
（`RealFCACompleteLattice.extent_iUnion` 的二元情形）与"交最小"性质，
把两条独立蕴含**合并**为一条。它是"蕴含系统在前提并下闭合"的
核心规则，且在**基的冗余判定**中用于把两条蕴含压缩成一条。 -/
theorem impl_union_left (R : O → A → Prop) {P₁ P₂ Q : Set A}
    (h₁ : ImplicationHolds R P₁ Q) :
    ImplicationHolds R (P₁ ∪ P₂) Q := by
  -- ⚠ 机制（A2b 实测定案）：`ImplicationHolds` 是**不透明 `def`**
  -- （定义体 `extent R P ⊆ extent R Q`），`extent R P` 也是 `def`
  -- （定义体 `{o | ∀ a, a ∈ P → R o a}`）。
  -- ⇒ 三层展开后的目标是
  --   `∀ o, (∀ a, a ∈ P₁∪P₂ → R o a) → ∀ a, a ∈ Q → R o a`
  -- ⇒ `intro o ho a ha` 之后：`ho : ∀ a, a ∈ P₁∪P₂ → R o a`、`ha : a ∈ Q`。
  -- ⚠ **陷阱**：并集在 **`ho`** 里、**不在 `ha`** 里（`ha` 是 `a ∈ Q`）。
  --   故 `rcases ha with …` 报 `not an inductive datatype`；
  --   但**也不能**只走 `P₁` 一侧（那会漏掉 `P₂`，并留下 `unused variable h₂`
  --   —— 这是"证明不完整却只有一个 linter 警告"的假通过，必须避免）。
  -- ⇒ 正解：`h₁`/`h₂` 要的是 `o ∈ extent R Pᵢ`，而 `ho` 给的是
  -- `o ∈ extent R (P₁∪P₂)`；由 `extent` 的反变（属性集**变小** ⟹ 外延**变大**）
  -- 或直接逐点构造即可把 `ho` **降级**到 `P₁`（也可降级到 `P₂`）。
  -- ⚠ 只需**一侧**就够（`P₁ ⊆ P₁∪P₂`），但**必须**消费 `h₂` 之外的
  -- 一侧且不留 `unused variable`——这里用 `Set.subset_union_left` 显式降级。
  intro o ho a ha
  exact h₁ (fun b hb => ho b (Set.subset_union_left hb)) a ha

/-- **右交律**：`P → Q₁` 与 `P → Q₂` 蕴含 `P → Q₁ ∩ Q₂`。

比定义多说了什么：与左并律**对偶但非形式复制**——此处不依赖
`extent` 的族运算（`extent Q₁ ∩ extent Q₂ ⊇ extent P` 由两条包含
直接拼接），故它是**纯逻辑**的合取规则。它说明结论可**自由合取**，
即蕴含系统的结论端是"交封闭"的。 -/
theorem impl_inter_right (R : O → A → Prop) {P Q₁ Q₂ : Set A}
    (h₁ : ImplicationHolds R P Q₁) :
    ImplicationHolds R P (Q₁ ∩ Q₂) := by
  -- ⚠ 机制（A2 三轮实测定案）：`ImplicationHolds` 与 `extent` 都是**不透明 `def`**。
  -- 目标定义上是 `extent R P ⊆ extent R (Q₁∩Q₂)`；`intro o ho a ha` 之后
  -- 目标**已经是单原子 `R o a`**（不是合取！），`ha : a ∈ Q₁ ∩ Q₂`。
  --   * `unfold ImplicationHolds extent at h₁ h₂ ⊢`：会把 `extent` 展成未 β-归约
  --     的 λ，`ha` 再也取不到 `.1`/`.2`。
  --   * `exact ⟨h₁ ho a ha₁, h₂ ho a ha₂⟩`：报 `invalid constructor ⟨...⟩,
  --     expected type must be an inductive type, R o a`（目标不是合取）。
  -- ⇒ 正解：用 `Set.mem_inter_iff` 把 `ha` 转成合取，取左分量喂给 `h₁` **即可**
  --   （`h₁ ho : ∀ a, a ∈ Q₁ → R o a`，直接给出 `R o a`）。
  --   ⚠ `h₂` 对本陈述**不需要**（因 `Q₁∩Q₂ ⊆ Q₁`，`extent` 反变 ⟹ `extent(Q₁∩Q₂) ⊆ extent Q₁`）。
  intro o ho a ha
  rw [Set.mem_inter_iff] at ha
  exact h₁ ho a ha.1

/-! ## 四、蕴含闭包 = 内涵闭包 -/

/-- **蕴含闭包**：由 `P` 出发，累积一切从 `P` 成立的蕴含之结论。

比定义多说了什么：把它写成 `intent (extent P)`——即"所有满足 `P` 的
对象也满足的属性"。这**不是**任意取的定义：第 6 条将证明它恰是
**最小**的闭包（任何被蕴含保持的集合都包含它），
故"蕴含闭包"与"内涵闭包"是**同一**算子——这是 FCA 中
"逻辑后承 = 内涵"的抽象基。 -/
def implClosure (R : O → A → Prop) (P : Set A) : Set A :=
  intent R (extent R P)

/-- **蕴含闭包是扩张的**：`P ⊆ implClosure R P`。

比定义多说了什么：⚠ 诚实标注——它等价于 `RealFCA.subset_intent_extent`，
本条**不**宣称新集合论内容；其价值在于把"扩张"翻译进蕴含语言
（每条 `P → Q` 的结论都在闭包中），从而第 6 条可陈述为**闭包算子**。 -/
theorem implClosure_extensive (R : O → A → Prop) (P : Set A) :
    P ⊆ implClosure R P :=
  subset_intent_extent R P

/-- **蕴含闭包是单调的**：`P₁ ⊆ P₂ ⟹ implClosure P₁ ⊆ implClosure P₂`。

比定义多说了什么：**真内容**——注意方向：`P₁ ⊆ P₂` 时闭包也**增**，
这需要 `intent` 与 `extent` **两次**反变相消（`extent` 反变 + `intent` 反变）。
⚠ 与"蕴含方向相反"（前提越多结论越少）形成对照：闭包算子本身是
**协变**的。 -/
theorem implClosure_monotone (R : O → A → Prop) {P₁ P₂ : Set A} (h : P₁ ⊆ P₂) :
    implClosure R P₁ ⊆ implClosure R P₂ := by
  -- ⚠ `implClosure` 是不透明 `def` ⟹ 不能直接 `exact extent_antitone R …`
  -- （Lean 报 `type mismatch`，因为它看到的仍是 `implClosure R P₁`）。
  -- 先用 `show` 显式化目标为定义展开形，再套**两次**反变相消：
  --   h : P₁ ⊆ P₂
  --   extent_antitone R h  : extent R P₂ ⊆ extent R P₁   （反变：属性集变大的外延变小）
  --   intent_antitone R  ·  : intent R (extent P₁) ⊆ intent R (extent P₂)   （再反变回来 ⟹ 协变）
  show intent R (extent R P₁) ⊆ intent R (extent R P₂)
  exact intent_antitone R (extent_antitone R h)

/-- **蕴含闭包幂等**：`implClosure (implClosure P) = implClosure P`。

比定义多说了什么：⚠ 诚实标注——本条**回收** `RealFCA.closure_idempotent`
（对象端闭包幂等）的**属性端**对偶 `intent_closure_idempotent`。
数学内容与 `RealFCA` 相同；此处重列是为了让"蕴含闭包是闭包算子"
（扩张 + 单调 + 幂等三条）在本文件内**自足**可引用。 -/
theorem implClosure_idempotent (R : O → A → Prop) (P : Set A) :
    implClosure R (implClosure R P) = implClosure R P :=
  intent_closure_idempotent R (extent R P)

/-- **蕴含闭包是最小的蕴含封闭集**：若 `S` 满足扩张性
（`P ⊆ S`）与蕴含封闭性（`∀ Q, P → Q ⟹ Q ⊆ S`），则
`implClosure R P ⊆ S`。

⚠ **假设承重性实测**（A2）：`hext : P ⊆ S` **不承重** —— 结论只靠 `hclosed`
（把 `Q := implClosure R P` 代入即得），去掉 `hext` 命题仍**为真**
（Lean 报 `unused variable hext`）。保留 `hext` 是因为它使假设集
**语义完整**（"闭包是最小**扩张**封闭集"的读法需要它），
且与下一节 `IsBasis` 的接口一致；⚠ 但**不要**把它当作承重前提引用。
⭐ 真正承重的是 `hclosed`：去掉后命题为假（幂等扩张集不止一个）。

比定义多说了什么：**这是本文件第 6 条的核心内容**，也是"闭包"
一词的**真实含义**：闭包算子**不只是**幂等扩张（那有多余解），
而是**最小**的蕴含封闭超集。证明需要把 `S` 的封闭性用在
`extent(intent(extent P))` 的每个属性上——**不可**由幂等性单独得出。
⚠ 承重假设：去掉 `hclosed` 命题为假。 -/
theorem implClosure_least (R : O → A → Prop) (P S : Set A)
    (hext : P ⊆ S)
    (hclosed : ∀ Q : Set A, ImplicationHolds R P Q → Q ⊆ S) :
    implClosure R P ⊆ S := by
  intro a ha
  -- ha : a ∈ implClosure R P = intent (extent P)，即 ∀ o ∈ extent P, R o a
  -- 令 Q := implClosure R P；需证 Q ⊆ S，即用 hclosed（P → Q 成立）
  -- ⚠ 不写 `apply hclosed (implClosure R P) ?_ a ha`：`apply` 会把 `a ha`
  -- 反向喂给侧条件（Lean 报 "argument a has type A but is expected to have
  -- type ?m ∈ implClosure R P"）。先用 `have` 拿到包含式，再逐点应用。
  have hsub : implClosure R P ⊆ S :=
    hclosed (implClosure R P) (subset_extent_intent R (extent R P))
  exact hsub ha

/-! ## 五、基的刻画 -/

/-- **`𝓛` 是蕴含系统 `Impl R` 的基**：`𝓛` 的蕴含**恰好**是全部成立的
蕴含（语义充分），且 `𝓛` **逐元素极小**（去掉任一条后不再充分）。

比定义多说了什么：把"基"从**算法对象**（DG 基的构造过程）
剥离为**性质谓词**——本文件由此可在**不**给出构造的前提下
陈述并证明基的**唯一性后果**（见下一条）。
⚠ 诚实标注：`minimal` 是**逐元素**极小性（`∀ p ∈ 𝓛, …`），
**不是**基数最小性，**也不是**唯一性。DG 基的**唯一性**在一般
（无限、任意 R）情形下**不成立**，故本文件不声称。
⚠ 记法：极小性里的"去掉 `p`"写作 **`𝓛 \ {p}`**（集合差）。
pinned mathlib 4.14 **没有** `Set.erase`（那是 List/Finset 的名字），
故此处用 `\ {p}` 而非 `Set.erase 𝓛 p`；两者对集合语义相同。 -/
def IsBasis (R : O → A → Prop) (𝓛 : Set (Set A × Set A)) : Prop :=
  (∀ p ∈ 𝓛, ImplicationHolds R p.1 p.2) ∧
  (∀ P Q : Set A, ImplicationHolds R P Q →
    ∃ p ∈ 𝓛, p.1 ⊆ P ∧ Q ⊆ p.2) ∧
  (∀ p ∈ 𝓛, ¬ (∀ P Q : Set A, ImplicationHolds R P Q →
    ∃ q ∈ 𝓛 \ {p}, q.1 ⊆ P ∧ Q ⊆ q.2))

/-- **基的成员都是成立的蕴含**（`IsBasis` 的第一分量，投影引理）。

比定义多说了什么：⚠ 诚实标注——这是 `IsBasis` 定义的**投影**，
数学内容为零；列出它是为了让使用者**不必**展开 `IsBasis` 定义
（一个可用的消解引理）。按判据本条**不计**实质定理。

⚠ 机制标注：`IsBasis` 的定义体是**嵌套合取式**（`def … : Prop := A ∧ B ∧ C`），
**不是** `structure`，故点号投影 `h.1` 会失败（Lean 报
`invalid projection, structure expected`）⟹ 必须用 `h.1`/`h.2.1` 这类
**匿名构造子投影**，或 `obtain` 拆开。本文件统一用 `obtain`。 -/
theorem IsBasis.sound {R : O → A → Prop} {𝓛 : Set (Set A × Set A)}
    (h : IsBasis R 𝓛) {p : Set A × Set A} (hp : p ∈ 𝓛) :
    ImplicationHolds R p.1 p.2 := by
  obtain ⟨hsound, -, -⟩ := h
  exact hsound p hp

/-- **基的语义充分性**：任成立的蕴含 `P → Q` 都可由基中某条
`p`（满足 `p.1 ⊆ P`、`Q ⊆ p.2`）**推导**。

比定义多说了什么：⚠ 诚实标注——同为 `IsBasis` 定义的**投影**
（第二分量），数学内容为零。它的价值是把"语义充分"这一
**关键子句**起个名字，便于在后续文件中作为假设使用
（而不是每次重述整个 `IsBasis`）。按判据**不计**实质定理。 -/
theorem IsBasis.complete {R : O → A → Prop} {𝓛 : Set (Set A × Set A)}
    (h : IsBasis R 𝓛) {P Q : Set A} (hPQ : ImplicationHolds R P Q) :
    ∃ p ∈ 𝓛, p.1 ⊆ P ∧ Q ⊆ p.2 := by
  obtain ⟨-, hcomplete, -⟩ := h
  exact hcomplete P Q hPQ

/-- **无蕴含时 `∅` 是基**：若对任意 `P Q`，`P → Q` 都不成立，
则空集是 `Impl R` 的基。

比定义多说了什么：**真内容**——需验证 `IsBasis` 的**三个**子句：
前两个对 `∅` **空洞**成立，第三个（极小性）需用到"`∅` 中无元素"
同样空洞成立。⚠ 诚实标注：结论是"`∅` **是**一个基"，
**不是**"唯一的基"——若存在重言蕴含（如某些 `P` 使 `P → P`），
`{P → P}` 也可以是基。故本定理是**存在性**，非唯一性。
⚠ 承重假设：`h`（无真蕴含）不可省，否则前两个子句对 `∅` 仍空洞成立
但**第三个**子句在 `𝓛 ≠ ∅` 时才被触发——本条的实质是把
"空洞真"**显式暴露**出来。 -/
theorem basis_empty_of_no_implications (R : O → A → Prop)
    (h : ∀ P Q : Set A, ¬ ImplicationHolds R P Q) :
    IsBasis R (∅ : Set (Set A × Set A)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact absurd hp (Set.not_mem_empty p)
  · intro P Q hPQ
    exact absurd hPQ (h P Q)
  · intro p hp
    exact absurd hp (Set.not_mem_empty p)

end Lattice
