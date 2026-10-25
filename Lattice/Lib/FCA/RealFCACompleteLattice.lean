import Mathlib
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: FCA 的完备格推广（闭集格的 `sInf`/`sSup` 结构）

## 本文件建立什么

`RealFCA` 只处理**单个**属性集/对象集上的 `extent`/`intent`。本文件把
extent/intent 提升到**任意族的并/交**，从而得到：

  1. `extent_iUnion`：`extent (⋃ i, B i) = ⋂ i, extent (B i)`
     ——extent 把**并**映为**交**（反变映射的族化律，`⋃ ↦ ⋂`）；
  2. `intent_iUnion`：`intent (⋃ i, O i) = ⋂ i, intent (O i)`（对偶）；
  3. `extent_iInter_subset_iUnion` / `intent_iInter_subset_iUnion`：交方向的**单向**律
     `⋃ i, extent (B i) ⊆ extent (⋂ i, B i)`；
  4. `sSup`/`sInf` 版本（`extent_sSup` / `intent_sSup` 等式；
     `extent_sInf_subset` / `intent_sInf_subset` 单向，**需非空族**）；
  5. 闭包族封闭：闭集的任意交仍是闭集（`IsClosedExtent.iInter`），
     故闭集族构成**完备格**（`sInf` 由 `⋂` 给出，见证为 `extent (⋃ i, B i)`）。

## ⚠ 方向性（本文件的**核心**，v15 审核修正）

`extent`/`intent` 是**反变**的（`RealFCA.extent_antitone`）。
**反变映射保并（`⋃ ↦ ⋂`），不保交**：

```
extent (⋃ i, B i) = ⋂ i, extent (B i)        成立（含空指标）
extent (⋂ i, B i) = ⋂ i, extent (B i)        不成立
```

**内核验证的反例**（`O := PUnit`, `A := ι := Bool`, `B i := {i}`,
`R _ a := (a = false)`）：

* `⋂ i, B i = {false} ∩ {true} = ∅` ⟹ LHS `= extent ∅ = univ`；
* RHS `= extent {false} ∩ extent {true} = univ ∩ ∅ = ∅`；
* `univ ≠ ∅` ✗。

⚠ **该反例的指标族是**非空**的**（`ι = Bool`）：即使补上 `[Nonempty ι]`，
`extent (⋂ i, B i) = ⋂ i, extent (B i)` **仍然为假** —— 它是**方向性错误**，
**不是**"空指标边界"错误，**不可**靠加 `[Nonempty ι]` 修复。

**正确的解读**：`extent`/`intent` 互为反变伴随（`RealFCA.galois_connection`），
**作为从 `Set` 到 `Set` 的反变映射，它们的族化律是 `⋃ ↦ ⋂`**；
原稿把"保交"当作反变伴随的标志，**方向判反了**。

## 依赖什么

* `Mathlib`（`Set.iInter`、`Set.ext`、`Set.sInf_eq_sInter`）
* `RealFCA`：只复用 `extent` / `intent` 两个定义，**不重复定义**

## 不做什么

* 不构造 `CompleteLattice` 的 Lean **instance**（那需要 `SetLike`/`CompleteLattice`
  一整套基础设施，属于文件 5 `RealFCAClosureOperatorLattice` 的范围）；
  本文件只给出**族运算的等式**，即 instance 所需的全部内容性质。
* 不涉及有限性；`RealFCA` 的有限格结论此处**不需要**。
* 不引入任何新公理、不做算法。

## 诚实边界

* **交方向只有单向律**：`⋃ i, extent (B i) ⊆ extent (⋂ i, B i)`。
  **反方向为假**（见上文反例），故本文件**不声称**任何 `extent (⋂ …)` 的
  等式。`intent` 侧对称。
* `extent_sInf_subset`/`intent_sInf_subset` **需要 `𝓑.Nonempty`**，该假设
  **承重**：`𝓑 = ∅` 时 `sInf 𝓑 = univ`，而 `sInf (extent '' ∅) = sInf ∅ = univ`，
  却要 `⊆ extent univ = {o | ∀ a, R o a}` —— 对 `R := fun _ _ => False` 为假
  （内核已验证）。
* 等式版本 `extent (sInf 𝓑) = sInf (extent '' 𝓑)` **为假**
  （反例：`𝓑 = {{false}, {true}}`，**非空族**），已删除。
* `IsClosedExtent.iInter` / `.sInf` 只对**闭集族**陈述；对**任意**族的
  `sInf` 闭包并不给出（那需要先证 `extent∘intent` 保交，等价于右伴随的
  存在性，此处未证 —— 且如上述 `extent` **不**保交，该路线需另辟）。
* `IsClosedExtent.iInter` 的证明**不依赖**任何"保交"式，而使用真实的
  `extent_iUnion`（见该定理 docstring）。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

variable {O A : Type*}

/-! ## 一、extent / intent 的族化（反变：并 ↦ 交） -/

/-- **extent 把并映为交**：`extent (⋃ i, B i) = ⋂ i, extent (B i)`。

比定义多说了什么：定义只给出 `o ∈ extent B` 对**单个** B 的展开；
本定理给出**任意族**的精确等式，且右侧是 `⋂` 而非 `⋃`
—— 这正是 `extent` 反变（`RealFCA.extent_antitone`）的族化标志。

⚠ **这是本文件唯一成立的 `extent` 族等式**：对偶的 `extent (⋂ i, B i)`
**没有**等式版本（见文件头"方向性"及 `extent_iInter_subset_iUnion`）。
⚠ 本定理**含空指标情形**（两边同为 `univ`），故**不需要** `[Nonempty ι]`。 -/
theorem extent_iUnion {ι : Sort*} (R : O → A → Prop) (B : ι → Set A) :
    extent R (⋃ i, B i) = ⋂ i, extent R (B i) := by
  ext o
  simp only [extent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
  exact ⟨fun h i a hi => h a ⟨i, hi⟩, fun h a ⟨i, hi⟩ => h i a hi⟩

/-- **intent 把并映为交**（`extent_iUnion` 的对偶）：
`intent (⋃ i, O i) = ⋂ i, intent (O i)`。

比定义多说了什么：与 `extent_iUnion` 对称。它说明"属性被对象并共享"
退化为"被每个对象集共享"，这是概念格 join 被定义为**内涵交**
（而非内涵并）的原因。 -/
theorem intent_iUnion {ι : Sort*} (R : O → A → Prop) (Os : ι → Set O) :
    intent R (⋃ i, Os i) = ⋂ i, intent R (Os i) := by
  ext a
  simp only [intent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
  exact ⟨fun h i o ho => h o ⟨i, ho⟩, fun h o ⟨i, ho⟩ => h i o ho⟩

/-- **交方向的单向律（extent）**：`⋃ i, extent (B i) ⊆ extent (⋂ i, B i)`。

⚠ **只有这一侧成立**：由反变性，`⋂ i, B i ⊆ B i` 给出
`extent (B i) ⊆ extent (⋂ i, B i)`，取并得本式。
**反方向为假** —— 见文件头反例（`O := PUnit`, `A := ι := Bool`,
`B i := {i}`, `R _ a := (a = false)`：LHS `= ∅`，RHS `= univ`）。
故此处**不写等式**。
⚠ 本定理**不需要** `[Nonempty ι]`：`ι` 为空时两侧同为 `∅`。 -/
theorem extent_iInter_subset_iUnion {ι : Sort*} (R : O → A → Prop) (B : ι → Set A) :
    (⋃ i, extent R (B i)) ⊆ extent R (⋂ i, B i) := by
  intro o ho a ha
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ho
  exact hi a (Set.mem_iInter.mp ha i)

/-- **交方向的单向律（intent）**：`⋃ i, intent (O i) ⊆ intent (⋂ i, O i)`
（`extent_iInter_subset_iUnion` 的对偶）。 -/
theorem intent_iInter_subset_iUnion {ι : Sort*} (R : O → A → Prop) (Os : ι → Set O) :
    (⋃ i, intent R (Os i)) ⊆ intent R (⋂ i, Os i) := by
  intro a ha o ho
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  exact hi o (Set.mem_iInter.mp ho i)

/-! ## 二、`sInf` / `sSup` 版本

`sInf 𝓑 = ⋂₀ 𝓑`（`Set.sInf_eq_sInter`）、`sSup 𝓑 = ⋃₀ 𝓑`
（`Set.sSup_eq_sUnion`）。由第一节：**`sSup` 侧有等式，`sInf` 侧只有单向**。 -/

/-- **extent 保 `sSup`**：`extent (sSup 𝓑) = sInf (extent '' 𝓑)`。

比定义多说了什么：把 `extent_iUnion` 改写为 `sInf`/`sSup` 语言
（`sSup 𝓑 = ⋃₀ 𝓑`，而 `sInf (extent '' 𝓑)` 就是这些外延的交）。
价值在于给出**格论形式**（保 `sSup`），而非仅集合族形式，
从而可直接喂给 `Order.GaloisConnection` 的 `l_sSup`/`u_sInf` 接口。 -/
theorem extent_sSup (R : O → A → Prop) (𝓑 : Set (Set A)) :
    extent R (sSup 𝓑) = sInf (extent R '' 𝓑) := by
  ext o
  simp only [extent, Set.mem_setOf_eq, Set.sSup_eq_sUnion, Set.mem_sUnion,
    Set.sInf_eq_sInter, Set.mem_sInter, Set.mem_image]
  constructor
  · intro h t ⟨B, hB, hEq⟩
    rw [← hEq]
    exact fun a ha => h a ⟨B, hB, ha⟩
  · intro h a ⟨B, hB, ha⟩
    exact h _ ⟨B, hB, rfl⟩ a ha

/-- **intent 保 `sSup`**：`intent (sSup 𝓞) = sInf (intent '' 𝓞)`（对偶）。 -/
theorem intent_sSup (R : O → A → Prop) (𝓞 : Set (Set O)) :
    intent R (sSup 𝓞) = sInf (intent R '' 𝓞) := by
  ext a
  simp only [intent, Set.mem_setOf_eq, Set.sSup_eq_sUnion, Set.mem_sUnion,
    Set.sInf_eq_sInter, Set.mem_sInter, Set.mem_image]
  constructor
  · intro h t ⟨O', hO, hEq⟩
    rw [← hEq]
    exact fun o ho => h o ⟨O', hO, ho⟩
  · intro h o ⟨O', hO, ho⟩
    exact h _ ⟨O', hO, rfl⟩ o ho

/-- **`sInf` 方向的单向律（extent）**：`sInf (extent '' 𝓑) ⊆ extent (sInf 𝓑)`。

⚠ **`𝓑.Nonempty` 是承重假设**：`o ∈ sInf (extent '' 𝓑)` 只对
`𝓑` **中已有的** `B` 说话，非空才能取到一个 `B ∈ 𝓑` 并使用
`a ∈ ⋂₀ 𝓑 ⊆ B`。`𝓑 = ∅` 时命题**为假**（内核已验证：
`sInf ∅ = univ` 故 LHS `= univ`，而 RHS `= extent univ = {o | ∀ a, R o a}`，
取 `R := fun _ _ => False` 得 `∅`，`univ ⊄ ∅`）。

⚠ 等式版本 `extent (sInf 𝓑) = sInf (extent '' 𝓑)` **为假**
（反例：`𝓑 = {{false}, {true}}`，**非空族**，`R _ a := (a = false)`：
LHS `= extent ∅ = univ`，RHS `= univ ∩ ∅ = ∅`），本文件不采用。 -/
theorem extent_sInf_subset (R : O → A → Prop) (𝓑 : Set (Set A)) (h𝓑 : 𝓑.Nonempty) :
    sInf (extent R '' 𝓑) ⊆ extent R (sInf 𝓑) := by
  intro o ho a ha
  rw [Set.sInf_eq_sInter, Set.mem_sInter] at ho
  rw [Set.sInf_eq_sInter, Set.mem_sInter] at ha
  obtain ⟨B, hB⟩ := h𝓑
  exact ho (extent R B) ⟨B, hB, rfl⟩ a (ha B hB)

/-- **`sInf` 方向的单向律（intent）**：
`sInf (intent '' 𝓞) ⊆ intent (sInf 𝓞)`（对偶，同样需 `𝓞.Nonempty`）。 -/
theorem intent_sInf_subset (R : O → A → Prop) (𝓞 : Set (Set O)) (h𝓞 : 𝓞.Nonempty) :
    sInf (intent R '' 𝓞) ⊆ intent R (sInf 𝓞) := by
  intro a ha o ho
  rw [Set.sInf_eq_sInter, Set.mem_sInter] at ha
  rw [Set.sInf_eq_sInter, Set.mem_sInter] at ho
  obtain ⟨O', hO⟩ := h𝓞
  exact ha (intent R O') ⟨O', hO, rfl⟩ o (ho O' hO)

/-! ## 三、闭集族构成完备格（交封闭） -/

/-- 闭集谓词：`O'` 是 `extent` 的值域元素（等价于 `extent(intent O') = O'`，
由 `RealFCA.extent_intent_extent` 与扩张性立得）。

比定义多说了什么：把"闭"表述为**在 extent 值域中**，这是便于族封闭性
证明的形式；注意它是**谓词**而非新结构，故不引入额外类型。 -/
def IsClosedExtent (R : O → A → Prop) (O' : Set O) : Prop :=
  ∃ B : Set A, extent R B = O'

/-- **闭集族的任意交仍闭**：若每个 `i` 处 `Os i` 闭，则 `⋂ i, Os i` 闭。

比定义多说了什么：这不是 `IsClosedExtent` 的展开 —— 它依赖族级律
才能把 `⋂` 写成 `extent` 的取值。它确立了闭集族在任意交下封闭，
即闭集族是一个**完备格**的 `sInf` 半边（推论：闭集格存在，无需有限性）。

⚠ **证明走的是 `extent_iUnion`（真），而不是被证伪的"保交"式**：
取 `Os i = extent (B i)`，则
`⋂ i, Os i = ⋂ i, extent (B i) = extent (⋃ i, B i)`（`extent_iUnion`），
故它是 `extent` 的值域元素（见证 `⋃ i, B i`）。

⚠ **不需要 `[Nonempty ι]`**：`ι` 为空时 `⋂ i, Os i = univ = extent ∅`
（取 `B := ∅`）—— 本定理对**空族**也成立。
⚠ 原稿曾用 `extent_iInter`（**假命题**）证明本定理；**命题本身为真**，
故此处**保留定理、更换证明**（这是审核修正的要点之一）。 -/
theorem IsClosedExtent.iInter {ι : Sort*} (R : O → A → Prop) {Os : ι → Set O}
    (h : ∀ i, IsClosedExtent R (Os i)) : IsClosedExtent R (⋂ i, Os i) := by
  choose B hB using h
  refine ⟨⋃ i, B i, ?_⟩
  rw [extent_iUnion]
  exact Set.iInter_congr fun i => hB i

/-- **闭集族对 `sInf` 封闭**：`IsClosedExtent` 对 `sInf` 封闭。

比定义多说了什么：`sInf 𝓞 = ⋂₀ 𝓞`，故本定理是 `IsClosedExtent.iInter`
的 `sInf` 包装；单独列出是因为 `sInf` 形式才是"闭集族是完备格"的
标准陈述（`CompleteLattice` 的 `sInf` 字段直接由此满足）。 -/
theorem IsClosedExtent.sInf (R : O → A → Prop) {𝓞 : Set (Set O)}
    (h : ∀ O' ∈ 𝓞, IsClosedExtent R O') : IsClosedExtent R (sInf 𝓞) := by
  rw [Set.sInf_eq_sInter, Set.sInter_eq_iInter]
  exact IsClosedExtent.iInter R fun O' : 𝓞 => h O' O'.2

end Lattice
