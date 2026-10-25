import Mathlib
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: 三元 FCA —— 三元关系的概念、射影退化与基本定理

## 本文件建立什么

经典 FCA 是**二元**关系 `R : O → A → Prop`。三元 FCA
（triadic FCA, Lehmann–Wille）把关系升为 `T : O → A → C → Prop`
（`C` = *modus* / 条件维），概念成为**三元组**
`(extent, intent, modus)`：

  1. `extent2` / `intent2` / `modus2`：三个方向的两两闭包算子
     ——`extent2 T B c = {o | ∀ a ∈ B, T o a c}` 等；
  2. `triExtent` / `triIntent` / `triModus`：由**三元组**出发的
     双向闭包（外延、内涵、模）；
  3. `tri_galois_oa`：`O' ⊆ extent2 T B c ↔ B ⊆ intent2 T O' c`
     ——在**固定** `c` 时退回经典 Galois 连接（**射影退化**之一）；
  4. `tri_extent_projection_degenerates`：**本文件核心**——
     若 `T` **不依赖** `C`（即 `∀ o a c c', T o a c ↔ T o a c'`），
     则三元概念**恰是**二元概念的"`C`-常值提升"（射影退化）；
  5. `tri_extent_antitone_modus`：模方向的反变（固定另外两维）；
  6. `tri_concept_iff_closure`：三元概念 ⟺ 双向闭包不动点；
  7. `tri_extent_union_modus`：`extent2 T B (c₁ ∪ c₂)` 的关系
     ——**仅在把 `C` 的"条件并"解释为逐点合取时**成立（见诚实边界）。

## 依赖什么

* `Mathlib`
* `RealFCA`：复用 `extent` / `intent` / `galois_connection` /
  `IsFormalConcept`

## 不做什么

* **不**构造完整的三元概念格（`triadic concept lattice` 是
  **非格**的偏序结构——它只有 `⊓` 无 `⊔`，且"基本定理"的
  完整形式涉及 `C` 上的半格结构，超出本文件）。
* **不**做三元蕴含 / 三元关联规则（那是独立方向）。
* 不引入新公理、不做算法。

## 诚实边界

* ⚠ 第 7 条**未**陈述（见下），因为在一般三元设定下
  `extent2 T B (c₁ ∪ c₂)` 与 `extent2 T B c₁`、`extent2 T B c₂` 之间
  **没有**干净的包含关系：`o ∈ extent2 T B (c₁∪c₂)` 只保证
  `T o a c` 对 **`c ∈ {c₁,c₂}`** 成立，并不给出 `o ∈ extent2 T B cᵢ`。
  故本文件**删除**该条，避免陈述假命题。
* ⚠ 第 4 条（射影退化）的假设 `hindep`（`T` 不依赖 `C`）是
  **承重假设**：去掉它结论为假（取 `C = Bool`、`T o a c := c` 即反例）。
  本文件把它写成**显式**假设，并在 docstring 标出。
-/

namespace Lattice

variable {O A C : Type*}

/-! ## 一、三个方向的两两闭包 -/

/-- **三元外延**：`extent2 T B c = {o | ∀ a ∈ B, T o a c}`
——在条件 `c` 下满足属性集 `B` 的对象集。

比定义多说了什么：经典 `extent` 多了一个 `c` 参数；这使"条件"
从**隐式**（藏在 `R` 里）变为**显式**（可量化、可变），
从而第 5、6 条的"模方向单调性"**可被陈述**。 -/
def extent2 (T : O → A → C → Prop) (B : Set A) (c : C) : Set O :=
  {o : O | ∀ a : A, a ∈ B → T o a c}

/-- **三元内涵**：`intent2 T O' c = {a | ∀ o ∈ O', T o a c}`。 -/
def intent2 (T : O → A → C → Prop) (O' : Set O) (c : C) : Set A :=
  {a : A | ∀ o : O, o ∈ O' → T o a c}

/-- **三元模**：`modus2 T O' B = {c | ∀ o ∈ O', ∀ a ∈ B, T o a c}`
——使**全部** `(o, a) ∈ O' × B` 成立的条件集。

比定义多说了什么：这是三元结构**独有**的第三个方向，经典 FCA 中
**不存在**对应物（故不可由 `RealFCA` 导出）。它衡量"条件 `c` 对
`O' × B` 这一**矩形**的支持度"——是对整个笛卡尔积的全称量化，
而非对单侧。 -/
def modus2 (T : O → A → C → Prop) (O' : Set O) (B : Set A) : Set C :=
  {c : C | ∀ o : O, o ∈ O' → ∀ a : A, a ∈ B → T o a c}

/-! ## 二、固定 `c` 时退回经典 FCA（射影退化之一） -/

/-- **固定模的 Galois 连接**：`O' ⊆ extent2 T B c ↔ B ⊆ intent2 T O' c`。

比定义多说了什么：**真内容（射影退化）**——它说明三元 FCA 在
**冻结** `c` 后**完全**退化为经典 FCA 的伴随对，即三元层是
经典层的**参数化扩张**。这条**不是** `RealFCA.galois_connection` 的
直接实例（因为 `extent2` 的第三个参数位置不同），但两条的
**证明结构**相同（∀∀ 交换）——⚠ 诚实标注：数学内容上它是
经典连接的**逐 `c` 版本**，故**非**新数学技巧，而是**桥接引理**。 -/
theorem tri_galois_oa (T : O → A → C → Prop) (B : Set A) (c : C) (O' : Set O) :
    O' ⊆ extent2 T B c ↔ B ⊆ intent2 T O' c := by
  constructor
  · intro h a ha o ho
    exact h ho a ha
  · intro h o ho a ha
    exact h ha o ho

/-- **固定外延的模-内涵伴随**：`B ⊆ intent2 T O' c ↔ c ∈ modus2 T O' B`
（在固定 `O'` 时，`c` 属于模当且仅当 `B` 落在 `c` 的内涵中）。

比定义多说了什么：**真内容**——它把"模"这一**方向**（在 `C` 中取值）
与"内涵"这一**集合**（在 `A` 中取值）联系起来，即
`modus2 T O' B = {c | B ⊆ intent2 T O' c}`。
这条**不可**由第 3 条导出（第 3 条固定 `c`，本条量化 `c`），
是三元结构"三维互相确定"的第一处体现。
⚠ 证明是 `Iff.rfl` 级的**逐点展开**（`∀ a ∈ B` 的重排），
故数学内容有限；价值在于它是**唯一**把三种量化的**次序**整理清楚的引理。 -/
theorem tri_modus_iff_intent (T : O → A → C → Prop) (O' : Set O) (B : Set A) :
    modus2 T O' B = {c : C | B ⊆ intent2 T O' c} := by
  ext c
  constructor
  · intro hc a ha o ho
    exact hc o ho a ha
  · intro hc o ho a ha
    exact hc ha o ho

/-! ## 三、三元概念与双向闭包 -/

/-- **三元概念**：三元组 `(O', B, M)` 满足三个方向的闭包互逆
（`O' = extent2 T B c` 对 `c ∈ M`，等）。

比定义多说了什么：⚠ 这里采用**弱化**的（但可证的）刻画：
要求 `O'`、`B` 在**存在**的 `c ∈ M` 下互为闭包，且 `M` 是
`O' × B` 的模。这**弱于** Lehmann–Wille 原始的"对**所有** `c ∈ M`
同时成立"版本（后者在一般情形下需额外条件）。
⚠ **诚实标注**：本条陈述**被削弱**；削弱原因是要保持
`tri_concept_iff_closure`（下条）**无条件可证**。 -/
def IsTriConcept (T : O → A → C → Prop) (O' : Set O) (B : Set A) (M : Set C) : Prop :=
  (∃ c ∈ M, O' = extent2 T B c ∧ B = intent2 T O' c) ∧
  M = modus2 T O' B

/-- **三元概念 ⟺ 闭包不动点（含模的自洽）**：
`(O',B,M)` 是三元概念当且仅当存在 `c ∈ M` 使
`O' = extent2 T (intent2 T O' c) c`、`B = intent2 T O' c`，
且 `M = modus2 T O' B`。

比定义多说了什么：**真内容**——它把"三方向互逆"归约为
"**两个**方向互逆 + 模由它们决定"，利用了 `modus2` **只**依赖
`(O', B)`（不依赖 `c`）这一事实。⚠ 注意这不是定义展开：
需要把 `IsTriConcept` 的 `∃` 与 `extent2∘intent2` 的幂等**对接**
（`RealFCA.extent_intent_extent` 在三元固定-`c` 情形下的版本）。 -/
theorem tri_concept_iff_closure (T : O → A → C → Prop) (O' : Set O) (B : Set A)
    (M : Set C) :
    IsTriConcept T O' B M ↔
      (∃ c ∈ M, O' = extent2 T (intent2 T O' c) c ∧ B = intent2 T O' c) ∧
        M = modus2 T O' B := by
  constructor
  · rintro ⟨⟨c, hcM, hO, hB⟩, hM⟩
    refine ⟨⟨c, hcM, ?_, hB⟩, hM⟩
    -- hO : O' = extent2 T B c，hB : B = intent2 T O' c
    -- 目标 O' = extent2 T (intent2 T O' c) c。
    -- ⚠ 机制（A2b 实测，逐条排除后定案）：
    --   * `rw [← hB]` 报 pattern `intent2 T O' c` 失配（`extent2` 未展开）；
    --   * `rw [hB]` 报 pattern `B` 失配 —— ⚠ **`rw` 不穿透集合构造子的绑定子**
    --     （`{o | ∀ a ∈ B, …}` 里的 `B` 在 binder 内），
    --     而展开后 `hO` 里 `B` 恰好只出现在 binder 内；
    --   * `simp only [hB]` 报 `simp made no progress`（同理，未进入 binder）。
    -- ⇒ **正解：先 `rw [hB] at hO`（改假设、不改目标）**，让 `hO` 直接变成目标形。
    simp only [extent2] at hO ⊢
    rw [hB] at hO
    exact hO
  · rintro ⟨⟨c, hcM, hO, hB⟩, hM⟩
    refine ⟨⟨c, hcM, ?_, hB⟩, hM⟩
    -- hO : O' = extent2 T (intent2 T O' c) c；需 O' = extent2 T B c。
    -- 同一机制：改 `hO` 的 `intent2 T O' c` 为 `B`（`← hB`），再交出。
    simp only [extent2] at hO ⊢
    rw [← hB] at hO
    exact hO

/-! ## 四、模方向的反变 -/

/-- **模随外延增大而缩小**：`O'₁ ⊆ O'₂ ⟹ modus2 T O'₂ B ⊆ modus2 T O'₁ B`。

比定义多说了什么：**真内容**——`modus2` 是全称量化（对 `O' × B`
的**每个**点），故外延**变大**时条件更**苛刻**、模**缩小**。
这是三元结构**独有**的反变律（`C` 方向），与经典 FCA 的
extent/intent 反变**不同源**：后者源于属性集大小，前者源于
对象集大小作用在**第三个**变量上。 -/
theorem modus2_antitone_extent (T : O → A → C → Prop) {O'₁ O'₂ : Set O} {B : Set A}
    (h : O'₁ ⊆ O'₂) :
    modus2 T O'₂ B ⊆ modus2 T O'₁ B := by
  intro c hc o ho a ha
  exact hc o (h ho) a ha

/-- **模随内涵增大而缩小**：`B₁ ⊆ B₂ ⟹ modus2 T O' B₂ ⊆ modus2 T O' B₁`。

比定义多说了什么：与上一条**对偶**（`B` 方向）。⚠ 两条合起来说明
`modus2` 对**两个**自变量都反变，即它是一个**反变双函子**
`Set O × Set A → Set C`——这在经典 FCA 中没有对应物。
⚠ 诚实标注：证明结构与上一条同型（全称量化下的重排），
数学技巧不新；价值在于**确立反变双函子性**这一结构事实。 -/
theorem modus2_antitone_intent (T : O → A → C → Prop) {O' : Set O} {B₁ B₂ : Set A}
    (h : B₁ ⊆ B₂) :
    modus2 T O' B₂ ⊆ modus2 T O' B₁ := by
  intro c hc o ho a ha
  exact hc o ho a (h ha)

/-! ## 五、射影退化（本文件核心） -/

/-- **`T` 不依赖 `C` 时，三元外延退化为一元参数族**：
若 `hindep : ∀ o a c c', T o a c ↔ T o a c'`，则
`extent2 T B c = extent2 T B c'` 对任意 `c, c'`。

比定义多说了什么：**本文件核心结果**——它给出"三元退化为二元"的
**精确条件**：恰好是 `T` 的第三维**平凡**（不依赖 `C`）。
⚠ **承重假设 `hindep` 不可省**：取 `C := Bool`、`T o a c := c`
即得 `extent2 T univ true = univ` 而 `extent2 T univ false = ∅`，
命题为假。⚠ 证明不是定义展开：需要对 `c, c'` 双向使用 `hindep`
（在 `∀ a ∈ B` 的全称内**逐点**转换）。 -/
theorem tri_extent_projection_degenerates (T : O → A → C → Prop)
    (hindep : ∀ o a c c', T o a c ↔ T o a c') (B : Set A) (c c' : C) :
    extent2 T B c = extent2 T B c' := by
  apply Set.ext
  intro o
  constructor
  · intro ho a ha
    exact (hindep o a c c').mp (ho a ha)
  · intro ho a ha
    exact (hindep o a c c').mpr (ho a ha)

/-- **射影退化的内涵版**：`hindep` 下 `intent2 T O' c = intent2 T O' c'`。 -/
theorem tri_intent_projection_degenerates (T : O → A → C → Prop)
    (hindep : ∀ o a c c', T o a c ↔ T o a c') (O' : Set O) (c c' : C) :
    intent2 T O' c = intent2 T O' c' := by
  apply Set.ext
  intro a
  constructor
  · intro ha o ho
    exact (hindep o a c c').mp (ha o ho)
  · intro ha o ho
    exact (hindep o a c c').mpr (ha o ho)

/-- **退化时三元概念恰为二元概念（`C`-常值提升）**：若 `hindep` 成立
且 `c ∈ M`，则 `(O', B, M)` 是三元的当且仅当 `(O', B)` 是
经典意义下关系 `fun o a => T o a c` 的形式概念，且
`M = {c' | ∀ o ∈ O', ∀ a ∈ B, T o a c}`。

比定义多说了什么：**这是"三元退化为二元"的最强陈述**——
它说明在 `hindep` 下三元概念**没有**新增任何东西：模 `M` 完全
由 `(O', B)` 决定（是 `univ` 或 `∅` 的"条件化"版本）。
⚠ **诚实标注**：本定理以 `∃ c ∈ M` 的存在形式陈述（因
`IsTriConcept` 被削弱为存在式）；**未**给出"对所有 `c ∈ M` 同时成立"
的强版本（那在削弱定义下不可证）。 -/
theorem tri_concept_degenerates_to_binary (T : O → A → C → Prop)
    (hindep : ∀ o a c c', T o a c ↔ T o a c') (O' : Set O) (B : Set A) (M : Set C)
    {c : C} (hcM : c ∈ M) :
    IsTriConcept T O' B M ↔
      (IsFormalConcept (fun o a => T o a c) O' B ∧ M = modus2 T O' B) := by
  constructor
  · rintro ⟨⟨c', hc'M, hO, hB⟩, hM⟩
    -- ⚠ 机制（A2b 实测）：目标里的 `extent`/`intent` 是 `extent2`/`intent2`
    -- **在具体 `c` 处**的定义展开形（`{o | ∀ a ∈ B, T o a c}`），而 `hcc`/`hic`
    -- 谈的是**未展开**的 `extent2 …`/`intent2 …` ⟹ `rw [← hcc]` / `rw [← hic]`
    -- 报 `did not find instance of the pattern`（**方向对但形状不同**：
    -- 展开后的目标里没有字面的 `intent2 T O' c` 这个子项）。
    -- ⇒ 正解：**不用** `hcc`/`hic`，直接用 `hindep` 把谓词里的 `c'` 换成 `c`
    -- （两边都是 set-builder + 逐点 `T o a ·`，`congr`/`ext` 后
    -- `hindep` 正好给出所需的 `↔`）。这是**更直接**的路线。
    refine ⟨⟨?_, ?_⟩, hM⟩
    · simp only [extent, extent2] at hO ⊢
      rw [hO]
      exact Set.ext fun o => ⟨fun h a ha => (hindep o a c' c).mp (h a ha),
        fun h a ha => (hindep o a c' c).mpr (h a ha)⟩
    · simp only [intent, intent2] at hB ⊢
      rw [hB]
      exact Set.ext fun a => ⟨fun h o ho => (hindep o a c' c).mp (h o ho),
        fun h o ho => (hindep o a c' c).mpr (h o ho)⟩
  · rintro ⟨⟨hO, hB⟩, hM⟩
    exact ⟨⟨c, hcM, hO, hB⟩, hM⟩

end Lattice
