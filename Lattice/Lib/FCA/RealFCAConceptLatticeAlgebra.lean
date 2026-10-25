import Mathlib
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: 概念格的代数结构（⊓/⊔ 下的格律）

## 本文件建立什么

`RealFCA` 已有 `concept_meet` / `concept_join` 的定义，并证了它们**是概念**。
本文件补上**格律本身**——即这些运算确实给出一个格结构：

  1. `meet_comm` / `join_comm`：⊓、⊔ 交换；
  2. `meet_assoc`：⊓ 结合（对**任意**输入，不要求输入是概念）；
  3. `meet_absorb_join` / `join_absorb_meet`：吸收律（⊓、⊔ 构成格）；
  4. `meet_isGLB`：`C₁ ⊓ C₂` 是子概念序下的**最大**下界（三元合取）；
  5. `join_isLUB`：对**概念**输入，`C₁ ⊔ C₂` 是**概念上界**中的**最小**者；
  6. `le_meet_iff` / `le_join_left`：序与运算的接口律。

## ⭐⭐ 诚实更正（原稿的两条**假命题**）

⚠ 原稿把第 4、5 条陈述为 Lean 的 `IsGLB` / `IsLUB` 谓词，**两条都是假命题**
（同型，同一处结构性错误的两面）：

* **序不匹配**：`IsGLB`/`IsLUB` 内部只用**环境 `LE`**（对 `Set O × Set A`
  即 `Prod.instLE`，**逐分量**），而本文件的成员谓词 `IsSubconcept`
  **只看第一分量**。两个不同的序混用 ⟹ 断言无意义地强。
* **更根本**：`IsGLB s a` 并**不是**"`a` 是 `s` 的最大元"，而是
  "`a` 是 `s` 的**下界集的最大下界**"。`s` 的元素是"低于 `C₁` 与 `C₂`
  的**所有**对"，其中含第二分量任意极端者，故 `s` 的最大下界**严格小于**
  `concept_meet`（后者的第二分量被钉死为 `intent (C₁.1 ∩ C₂.1)`）。

**内核反例**（`O := PUnit`、`A := PUnit`、`R := fun _ _ => False`）：

* `meet_isGLB` 原版：取 `C₁ = C₂ = (∅, ∅)` ⟹
  `concept_meet = (∅, univ)`；而 `(∅, ∅) ∈ s`，`IsGLB` 要求
  `concept_meet ≤ (∅, ∅)`，即 `univ ⊆ ∅` —— **假**（`PUnit` 非空），故不成立
* `join_isLUB` 原版：取 `C₁ = C₂ = (∅, univ)`（二者都是概念）⟹
  `concept_join = (∅, univ)`；而 `(∅, ∅) ∈ s`，`IsLUB` 要求
  `(∅, ∅) ≤ concept_join`，即 `univ ⊆ ∅` —— **假**，故不成立

⇒ **修法**：两条都改为**显式的三元合取**（下界/上界性两分量 + 最大/最小性），
序一律统一为 `IsSubconcept`。这是格论上**真的**那两条命题。

## ⭐ 关于分配律与模律的**诚实结论**

经典 FCA 定理：**概念格一定是完备格，但一般不是分配格**。
因此本文件**不陈述**无条件的
`C₁ ⊓ (C₂ ⊔ C₃) = (C₁ ⊓ C₂) ⊔ (C₁ ⊓ C₃)` 型分配律——
在"任意 `R : O → A → Prop`"的设定下那句话**是假命题**（可代
`O = Fin 2`、`A = Fin 2`、`R = (· = ·)` 检验：三个概念
`(∅,univ)`、`({0},{0})`、`({1},{1})` 破坏分配性）。
同理，模律在概念格上**也不无条件成立**（概念格是代数格，
代数格一般非模）。

⇒ 按"**假命题 vs 空洞真 vs 承重假设**"三分类，本文件把分配/模律
**从定理清单中删除**，只保留无条件为真的格律（上述 1–6）。
这样每条定理都回答"比定义多说了什么"，而不是靠恒等重述充数。

## 依赖什么

* `Mathlib`
* `RealFCA`：复用 `extent` / `intent` / `IsFormalConcept` /
  `IsSubconcept` / `concept_meet` / `concept_join`

## 不做什么

* 不构造 `Lattice` / `CompleteLattice` 的 Lean instance（本文件只证
  instance 所需的**二元**定律；任意族的 `sSup` 需要分配性，故不做）。
* 不引入 `Finset`、有限性或额外公理。
* 不构造算法。

## 诚实边界

* `meet_assoc` 无条件成立，是因为 `concept_meet` 的第二分量**被定义为**
  第一分量的 `intent`；这是定义结构使然，但仍需把 `Set.inter_assoc`
  **穿过** `intent`，故不是 `rfl`。
* `join_isLUB` 需要概念假设（**输入与上界都要是概念**）；
  `meet_isGLB` **不需要**——这一不对称
  是真实的结构事实，不是省略。
* ⚠ `IsGLB` / `IsLUB` 这两个 mathlib 谓词在原稿的陈述下**是假命题**，
  故本文件**不使用**它们；改用的三元合取是它们的**正确弱化**，
  不含任何 `IsGLB`/`IsLUB` 的强度声明。
-/


namespace Lattice

variable {O A : Type*}

/-! ## 一、交换律 -/

/-- **⊓ 交换**：`C₁ ⊓ C₂ = C₂ ⊓ C₁`（对任意输入）。

比定义多说了什么：两个分量都要交换——第一分量是 `∩` 交换，
第二分量要求把 `Set.inter_comm` **代入** `intent` 的自变量。
故不是 `Iff.rfl` 级重述。 -/
theorem meet_comm (R : O → A → Prop) (C₁ C₂ : Set O × Set A) :
    concept_meet R C₁ C₂ = concept_meet R C₂ C₁ := by
  unfold concept_meet
  rw [Set.inter_comm]

/-- **⊔ 交换**：`C₁ ⊔ C₂ = C₂ ⊔ C₁`（对任意输入）。

比定义多说了什么：`concept_join` 的第二分量是
`intent (extent (C₁.2 ∩ C₂.2))`，交换 `∩` 后须把等式**穿过**
`extent`、`intent` 两层——不是定义展开。 -/
theorem join_comm (R : O → A → Prop) (C₁ C₂ : Set O × Set A) :
    concept_join R C₁ C₂ = concept_join R C₂ C₁ := by
  unfold concept_join
  rw [Set.inter_comm]

/-! ## 二、⊓ 结合律（无条件） -/

/-- **⊓ 结合**：`(C₁ ⊓ C₂) ⊓ C₃ = C₁ ⊓ (C₂ ⊓ C₃)`（对任意输入）。

比定义多说了什么：第一分量是 `Set.inter_assoc`；第二分量需要
`intent ((C₁.1∩C₂.1)∩C₃.1) = intent (C₁.1∩(C₂.1∩C₃.1))`，
即把 `inter_assoc` **穿过** `intent`。⚠ 注意此处"任意输入"是
**承重**的：因为第二分量由第一分量定义，输入无需是概念。 -/
theorem meet_assoc (R : O → A → Prop) (C₁ C₂ C₃ : Set O × Set A) :
    concept_meet R (concept_meet R C₁ C₂) C₃ = concept_meet R C₁ (concept_meet R C₂ C₃) := by
  unfold concept_meet
  rw [Set.inter_assoc]

/-! ## 三、吸收律（⊓、⊔ 构成格） -/

/-- **吸收律（⊓ 吸收 ⊔）**：`C₁ ⊓ (C₁ ⊔ C₂) = C₁`（`C₁` 为概念）。

比定义多说了什么：格的**定义性**定律之一，绝非重述：
`concept_join` 的第一分量 `extent (C₁.2 ∩ C₂.2)` 与随后的 `∩ C₁.1`
无句法关系，必须用概念的连接性质 `C₁.1 = extent C₁.2`
（`IsFormalConcept` 的**承重**作用）才闭合。
⚠ **假设不可省**：对非概念输入该等式为假。 -/
theorem meet_absorb_join (R : O → A → Prop) (C₁ C₂ : Set O × Set A)
    (h₁ : IsFormalConcept R C₁.1 C₁.2) :
    concept_meet R C₁ (concept_join R C₁ C₂) = C₁ := by
  -- 承重的概念性事实：o ∈ C₁.1 ⟹ ∀ a, a ∈ C₁.2 → R o a
  -- 先由 h₁.1 把 o ∈ C₁.1 送到 extent R C₁.2（即函数），再把 C₁.2 用 h₁.2 换掉。
  have key : ∀ o : O, o ∈ C₁.1 → ∀ a : A, a ∈ C₁.2 → R o a := by
    intro o ho a ha
    have ho' : o ∈ extent R C₁.2 := h₁.1 ▸ ho
    exact ho' a ha
  have hfirst : C₁.1 ∩ extent R (C₁.2 ∩ C₂.2) = C₁.1 := by
    refine Set.Subset.antisymm Set.inter_subset_left ?_
    intro o ho
    exact ⟨ho, fun a ha => key o ho a ha.1⟩
  unfold concept_meet concept_join
  refine Prod.ext ?_ ?_
  · exact hfirst
  · rw [hfirst]
    exact h₁.2.symm

/-- **吸收律（⊔ 吸收 ⊓）**：`C₁ ⊔ (C₁ ⊓ C₂) = C₁`（`C₁` 为概念）。

比定义多说了什么：与上一条对偶，但**非**形式复制：此处第一分量是
`extent (C₁.2 ∩ intent (C₁.1 ∩ C₂.1))`，须证它恰为 `C₁.1`
（用 `⊆ extent(intent ·)` 的扩张性与 `C₁.1 = extent C₁.2`）。
⚠ **假设 `h₁` 用在两处**，不可省。 -/
theorem join_absorb_meet (R : O → A → Prop) (C₁ C₂ : Set O × Set A)
    (h₁ : IsFormalConcept R C₁.1 C₁.2) :
    concept_join R C₁ (concept_meet R C₁ C₂) = C₁ := by
  -- 承重：C₁.2 ⊆ intent (C₁.1 ∩ C₂.1)，由 C₁.2 = intent C₁.1 与
  -- intent 的反单调性（C₁.1 ∩ C₂.1 ⊆ C₁.1 ⟹ intent C₁.1 ⊆ intent (C₁.1 ∩ C₂.1)）得到。
  have hsub : C₁.2 ⊆ intent R (C₁.1 ∩ C₂.1) := by
    rw [h₁.2]
    exact intent_antitone R Set.inter_subset_left
  have hinter : C₁.2 ∩ intent R (C₁.1 ∩ C₂.1) = C₁.2 := Set.inter_eq_left.mpr hsub
  unfold concept_join concept_meet
  refine Prod.ext ?_ ?_
  · rw [hinter, ← h₁.1]
  · rw [hinter, ← h₁.1, ← h₁.2]

/-! ## 四、⊓ 是最大下界、⊔ 是最小上界 -/

/-- **⊓ 是最大下界**：`C₁ ⊓ C₂` 是 `{C | C ≤ C₁ ∧ C ≤ C₂}` 中的**最大元**
（子概念序 `IsSubconcept` 下）。

比定义多说了什么：本条同时断言**下界性**与**最大性**：
`C.1 ⊆ C₁.1 ∩ C₂.1` 由两个假设拼出，而 `concept_meet` 的第一分量**正是**这个交。

## ⭐ 诚实更正（原稿的假命题：`IsGLB` 版）

原稿陈述为 `IsGLB {C | IsSubconcept R C C₁ ∧ IsSubconcept R C C₂} (concept_meet R C₁ C₂)`——
**这是假命题**，且**有两种独立的失败方式**（已由有限模型穷举 + 内核证伪）：

* **失败方式一（序不匹配）**：`IsGLB` 的 `lowerBounds`/`upperBounds` 用的是
  **环境 `LE`**（`Prod.instLE`，**逐分量**），而集合的成员谓词 `IsSubconcept`
  **只看第一分量**。两者不同序 ⟹ 断言无意义地强。
* **失败方式二（更根本）**：即便两侧都用 `Prod.instLE`，`IsGLB s a` 也**不是**
  "`a` 是 `s` 的最大元"，而是"`a` 是 `s` 的**下界集的最大下界**"——
  `s` 的元素是"同时低于 `C₁` 与 `C₂` 的**所有**对"，其中含第二分量任意大的对，
  故 `s` 的最大下界**严格小于** `concept_meet`（后者的第二分量被钉死为
  `intent (C₁.1 ∩ C₂.1)`）。

**内核反例**（`O := PUnit`、`A := PUnit`、`R := fun _ _ => False`、
`C₁ = C₂ = (∅, ∅)`）：`concept_meet = (∅, intent ∅) = (∅, univ)`；
而 `(∅, ∅) ∈ s`（`∅ ⊆ ∅`），`IsGLB` 要求 `concept_meet ≤ (∅, ∅)`，
即 `univ ⊆ ∅` —— **假**（`PUnit` 非空）⟹ `∅ ≠ univ`，故不成立

⇒ **修法**：改为**显式的三元合取**（下界性两分量 + 最大性），
序一律统一为 `IsSubconcept`（第一分量）。这才是格论上**真的**那条命题。 -/
theorem meet_isGLB (R : O → A → Prop) (C₁ C₂ : Set O × Set A) :
    IsSubconcept R (concept_meet R C₁ C₂) C₁ ∧
    IsSubconcept R (concept_meet R C₁ C₂) C₂ ∧
    ∀ C : Set O × Set A, IsSubconcept R C C₁ → IsSubconcept R C C₂ →
      IsSubconcept R C (concept_meet R C₁ C₂) := by
  -- 三个分量：下界性（左、右）与最大性。全部只是 `∩` 的泛性质。
  refine ⟨Set.inter_subset_left, Set.inter_subset_right, ?_⟩
  intro C h1 h2
  exact Set.subset_inter h1 h2

/-- **⊔ 是最小上界**：对**概念**输入，`C₁ ⊔ C₂` 是
`{C | C₁ ≤ C ∧ C₂ ≤ C}` 中**概念**的最小元。

比定义多说了什么：上界性要求 `C₁.1 ⊆ extent (C₁.2 ∩ C₂.2)`——
**这只有**在 `C₁` 是概念时才成立（用 `C₁.1 = extent C₁.2`）。
最小性部分**额外需要上界 `C` 本身是概念**（`hC`），
因为要把 `extent C.2` 与 `C.1` 互译才能把 `C₁.1 ⊆ C.1`、`C₂.1 ⊆ C.1`
升级为 `C₁.2 ⊇ C.2`、`C₂.2 ⊇ C.2`，从而 `C.2 ⊆ C₁.2 ∩ C₂.2`。

## ⭐ 诚实更正（原稿的假命题：`IsLUB` 版）

原稿陈述为 `IsLUB {C | IsSubconcept R C₁ C ∧ IsSubconcept R C₂ C} (concept_join R C₁ C₂)`——
**这是假命题**，与原稿 `meet_isGLB` 同型（同一处结构性错误的两面）：

* `IsLUB` 用的是**环境 `LE`**（`Prod.instLE`），而成员谓词 `IsSubconcept` 只看第一分量；
* 更根本地，`IsLUB s a` 要求 `a` 是 `s` 的**上界集的最小上界**，而 `s` 含
  第二分量任意小的对，其最小上界**严格小于** `concept_join`。

**内核反例**（`O := PUnit`、`A := PUnit`、`R := fun _ _ => False`、
`C₁ = C₂ = (∅, univ)`——二者都是概念）：此处 `R` 恒假，故 `extent univ = ∅`
（`extent R B` 要求 `∀ a ∈ B, R o a`，恒不成立）；于是
`concept_join = (extent (univ ∩ univ), intent (extent (univ ∩ univ))) = (∅, intent ∅) = (∅, univ)`；
而 `(∅, ∅) ∈ s`（`C₁.1 = ∅ ⊆ ∅`），`IsLUB` 要求 `(∅, ∅) ≤ concept_join`，
即 `univ ⊆ ∅` —— **假**，故不成立

⇒ **修法**：改为**显式的三元合取**（上界性两分量 + **对概念上界**的最小性），
序一律统一为 `IsSubconcept`。 -/
theorem join_isLUB (R : O → A → Prop) (C₁ C₂ : Set O × Set A)
    (h₁ : IsFormalConcept R C₁.1 C₁.2) (h₂ : IsFormalConcept R C₂.1 C₂.2) :
    IsSubconcept R C₁ (concept_join R C₁ C₂) ∧
    IsSubconcept R C₂ (concept_join R C₁ C₂) ∧
    ∀ C : Set O × Set A, IsFormalConcept R C.1 C.2 →
      IsSubconcept R C₁ C → IsSubconcept R C₂ C →
      IsSubconcept R (concept_join R C₁ C₂) C := by
  unfold IsSubconcept concept_join
  refine ⟨?_, ?_, ?_⟩
  · -- C₁.1 = extent C₁.2 ⊆ extent (C₁.2 ∩ C₂.2)（extent 反变）
    rw [h₁.1]
    exact fun o ho a ha => ho a ha.1
  · rw [h₂.1]
    exact fun o ho a ha => ho a ha.2
  · -- 最小性：C 是概念上界。C.1 = extent C.2，故"o ∈ C.1 ⟺ ∀ a ∈ C.2, R o a"。
    intro C hC h1 h2
    have key : ∀ a : A, a ∈ C.2 → a ∈ C₁.2 ∩ C₂.2 := by
      intro a ha
      exact ⟨(by rw [h₁.2]; intro o ho; exact (hC.1 ▸ h1 ho) a ha),
             (by rw [h₂.2]; intro o ho; exact (hC.1 ▸ h2 ho) a ha)⟩
    rw [hC.1]
    intro o ho a ha
    exact ho a (key a ha)

/-! ## 五、序-运算接口律 -/

/-- **⊓ 下方 ⟺ 双下方**：`C ≤ C₁ ⊓ C₂ ↔ C ≤ C₁ ∧ C ≤ C₂`。

比定义多说了什么：`IsSubconcept` 只看第一分量，而 `⊓` 的第一分量是
`∩`；故本式是 `Set.subset_inter_iff` 经 `IsSubconcept` 的**转写**，
但它把"下界"这一序概念与 `⊓` 这一**代数**概念钉在一起——
是 `meet_isGLB` 中最大性部分的**可复用**形式。 -/
theorem le_meet_iff (R : O → A → Prop) (C C₁ C₂ : Set O × Set A) :
    IsSubconcept R C (concept_meet R C₁ C₂) ↔
      IsSubconcept R C C₁ ∧ IsSubconcept R C C₂ := by
  unfold IsSubconcept concept_meet
  exact Set.subset_inter_iff

/-- **⊔ 的上界性（对概念输入）**：`C₁ ≤ C₁ ⊔ C₂`。

注意 **诚实更正（本文件原稿的假命题）**：原稿把本条陈述为**无条件**成立
（"确实不需要 `IsFormalConcept`"），那是**假命题**。
**反例**（`O = A = Fin 2`、`R = (· = ·)`、`C₁ = ({1},{0})`、`C₂ = ({1},{0})`）：
`concept_join` 第一分量 `= extent (C₁.2 ∩ C₂.2) = extent {0} = {0}`，
而 `C₁.1 = {1} ⊄ {0}` ⟹ `IsSubconcept` 失败。
根因：`C₁ ≤ C₁⊔C₂` 要求 `C₁.1 ⊆ extent C₁.2`，**这正是概念性条件**，
对任意输入不成立（`extent_antitone` 只给 `extent (C₁.2 ∩ C₂.2) ⊆ extent C₁.2`
这一**反向**的包含，帮不上忙）。
⇒ 故补上承重的概念假设 `h₁`；此时第一分量由 `h₁.1` 直接给出。 -/
theorem le_join_left (R : O → A → Prop) (C₁ C₂ : Set O × Set A)
    (h₁ : IsFormalConcept R C₁.1 C₁.2) :
    IsSubconcept R C₁ (concept_join R C₁ C₂) := by
  unfold IsSubconcept concept_join
  rw [h₁.1]
  exact fun o ho a ha => ho a ha.1

end Lattice
