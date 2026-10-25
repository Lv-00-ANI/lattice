import Mathlib
import Lattice.Lib.Compiler.RealRecursiveSemantics
/-!
# LATTICE: Kleene 最小不动点 —— 单调算子的有限格链稳定与 `⋃ₙ Fⁿ ∅`

`RealRecursiveSemantics.least_fixed_point_finite` 已经在「有限偏序 + 有底」上证明了
从 `⊥` 出发的迭代在 `≤ card α` 步稳定、稳定值是不动点且最小。本文件把那条结论
**重构成 Kleene 链定理的标准形态**并补上此前缺失的部件：

  1. **Kleene 链**：`kleeneChain f : ℕ → α`，`kleeneChain f 0 = ⊥`，
     `kleeneChain f (n+1) = f (kleeneChain f n)`（即 `Fⁿ⊥`）；
  2. **链的单调性**：单调算子 `f` 的 Kleene 链关于步数单调
     （`kleeneChain_monotone`），且相邻步递增（`kleeneChain_le_succ`）；
  3. **有限步稳定（用 `Nat.find`）**：存在步数使链出现重复；本文件用
     **`Nat.find`** 把「最小稳定步」定义出来（`kleeneStabIndex`），
     并证明其**存在性**（`kleeneStabIndex_spec`）、**上界 `≤ card α`**
     （`kleeneStabIndex_le_card`）与**极小性**（`kleeneStabIndex_minimal`）——
     即 `Nat.find` 的三个标准性质全部机器验证；
  4. **稳定值是不动点**：`kleeneLimit f = kleeneChain f (kleeneStabIndex f)` 满足
     `f (kleeneLimit f) = kleeneLimit f`（`kleeneLimit_fixed`）；
  5. **最小性**：`kleeneLimit f ≤ 任意不动点`（`kleeneLimit_le_of_fixed`）；
  6. **稳定后恒定**：`N ≤ n ⟹ kleeneChain f n = kleeneLimit f`
     （`kleeneChain_eq_limit_of_le`）；
  7. **应用 —— 「最小结 = ⋃ₙ Fⁿ ∅」**：在**幂集格**（`Set α`，`⊆` 序，`∅` 为底）上，
     单调算子 `F` 的最小不动点恰是 Kleene 链的并 `⋃ n, Fⁿ ∅`
     （`kleeneLimit_eq_iUnion`、`kleeneLimit_mem_iff`），并给出「最小结」的
     `⊆`-刻画（`kleeneLimit_subset_of_fixed`）；
     以及**有限幂集上的基数形式**（`kleeneLimit_card_le_of_fixed`）。

**诚实边界**（本文件不证 / 不声称的）：
- 本文件的有限步稳定**只在 `[Fintype α]`（有限格）上成立**，这正是 Kleene 定理的
  「有限步稳定」版本；**未做**：无限格（`CompleteLattice`）上 `lfp = ⨆ n, Fⁿ ⊥`
  的一般 Knaster–Tarski / Kleene 定理（那需要 `ωScottContinuous` 或
  `OrderHom.lfp` 的连续格理论）——这里**诚实标注为未做**，不给一般形式。
- **未做**：`⊔`-连续性与 `ωScottContinuous` 的桥接；本文件的稳定论证走
  **鸽笼原理（`Fintype.card_le_of_injective`）**而不是连续性，因此在有限格上
  比连续性假设**更弱、更强**（不需要连续性，但需要有限性）。
- **诚实标注**：`RealRecursiveSemantics.least_fixed_point_finite` 已经给出同一结论，
  本文件的**新增内容**是：`Nat.find` 形式的最小稳定步、稳定步的极小性与上界、
  稳定后的恒定形式、以及幂集格上的「最小结 = ⋃ₙ Fⁿ ∅」应用。
  两文件**互为交叉验证**（同一命题的两条独立证明路线）。
- 幂集格版本中 `Set α` 的「并」用 `Set.iUnion`；**未做**：把它推广为任意
  `CompleteLattice` 上的 `⨆ n, Fⁿ ⊥`（同第 2 条）。
- 无 sorry / axiom / admit。
-/

noncomputable section

open scoped Classical

namespace Lattice

variable {α : Type*}

/-! ## 一、Kleene 链 `Fⁿ⊥` -/

/-- **Kleene 链**：从底 `⊥` 出发的迭代 `Fⁿ⊥`。
`kleeneChain f 0 = ⊥`，`kleeneChain f (n+1) = f (kleeneChain f n)`。 -/
def kleeneChain [Bot α] (f : α → α) : ℕ → α
  | 0 => ⊥
  | n + 1 => f (kleeneChain f n)

variable [PartialOrder α] [OrderBot α]

@[simp] theorem kleeneChain_zero (f : α → α) : kleeneChain f 0 = ⊥ := rfl

@[simp] theorem kleeneChain_succ (f : α → α) (n : ℕ) :
    kleeneChain f (n + 1) = f (kleeneChain f n) := rfl

/-- 展开一步（点形式）：`F^{n+1}⊥ = F (Fⁿ⊥)`。 -/
theorem kleeneChain_succ' (f : α → α) (n : ℕ) :
    kleeneChain f (n + 1) = f (kleeneChain f n) := rfl

/-! ## 二、链的单调性与递增 -/

/-- **相邻步递增**：单调算子的 Kleene 链 `Fⁿ⊥ ≤ F^{n+1}⊥`。
归纳：`n = 0` 用 `bot_le`，后继步用 `hf` 保持。 -/
theorem kleeneChain_le_succ (f : α → α) (hf : Monotone f) :
    ∀ n : ℕ, kleeneChain f n ≤ kleeneChain f (n + 1) := by
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      change f (kleeneChain f n) ≤ f (kleeneChain f (n + 1))
      exact hf ih

/-- **Kleene 链关于步数单调**：`n ≤ m ⟹ Fⁿ⊥ ≤ Fᵐ⊥`。 -/
theorem kleeneChain_monotone (f : α → α) (hf : Monotone f) :
    Monotone (kleeneChain f) := by
  intro n m hnm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact ih.trans (kleeneChain_le_succ f hf (n + d))

/-- 链的每一层都不超过其任意后继：`Fⁿ⊥ ≤ Fᵐ⊥`（`n ≤ m`）的另一种写法。 -/
theorem kleeneChain_le_of_le (f : α → α) (hf : Monotone f) {n m : ℕ} (h : n ≤ m) :
    kleeneChain f n ≤ kleeneChain f m :=
  kleeneChain_monotone f hf h

/-! ## 三、有限步稳定：`Nat.find` 形式的最小稳定步 -/

variable [Fintype α]

/-- **稳定性的存在性（鸽笼原理）**：有限偏序上单调算子的 Kleene 链必在
某步出现重复 `Fⁿ⊥ = F^{n+1}⊥`。
反证：若前 `card α` 步都严格增，则 `Fin (card α + 1) → α` 的单射给出
`card α + 1 ≤ card α` 的矛盾。 -/
theorem kleeneChain_stabilizes (f : α → α) (hf : Monotone f) :
    ∃ N : ℕ, kleeneChain f N = kleeneChain f (N + 1) := by
  by_contra h
  push_neg at h
  have hle : ∀ n : ℕ, kleeneChain f n ≤ kleeneChain f (n + 1) := kleeneChain_le_succ f hf
  have hlt : ∀ n : ℕ, n ≤ Fintype.card α → kleeneChain f n < kleeneChain f (n + 1) :=
    fun n hn => lt_of_le_of_ne (hle n) (h n)
  have hmono : Monotone (kleeneChain f) := kleeneChain_monotone f hf
  -- 前段严格增 + 后段单调 ⟹ 该段严格增
  have hltj : ∀ i j : ℕ, i ≤ Fintype.card α → i < j →
      kleeneChain f i < kleeneChain f j := by
    intro i j hi hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : kleeneChain f i < kleeneChain f (i + 1) := hlt i hi
    have h2 : kleeneChain f (i + 1) ≤ kleeneChain f (i + d + 1) := hmono (by omega)
    exact lt_of_lt_of_le h1 h2
  -- 单射 Fin (card α + 1) → α（鸽笼）
  have hinj : Function.Injective
      (fun i : Fin (Fintype.card α + 1) => kleeneChain f (i : ℕ)) := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hltij | hgtij
    · exact (ne_of_lt (hltj (i : ℕ) (j : ℕ) (by have := i.isLt; omega) hltij)) hij
    · exact (ne_of_lt (hltj (j : ℕ) (i : ℕ) (by have := j.isLt; omega) hgtij)) hij.symm
  have hcard := Fintype.card_le_of_injective
    (fun i : Fin (Fintype.card α + 1) => kleeneChain f (i : ℕ)) hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- **最小稳定步**（`Nat.find`）：第一个使 `Fⁿ⊥ = F^{n+1}⊥` 的步数。
用 `Nat.find` 从 `kleeneChain_stabilizes` 的可判定性中取出。 -/
def kleeneStabIndex (f : α → α) (hf : Monotone f) : ℕ :=
  Nat.find (kleeneChain_stabilizes f hf)

/-- **`Nat.find` 的刻画（spec）**：`kleeneStabIndex f` 处链确实稳定。 -/
theorem kleeneStabIndex_spec (f : α → α) (hf : Monotone f) :
    kleeneChain f (kleeneStabIndex f hf) = kleeneChain f (kleeneStabIndex f hf + 1) :=
  Nat.find_spec (kleeneChain_stabilizes f hf)

/-- **`Nat.find` 的极小性**：任何使链稳定的步数都不小于 `kleeneStabIndex f`。 -/
theorem kleeneStabIndex_minimal (f : α → α) (hf : Monotone f) {n : ℕ}
    (hn : kleeneChain f n = kleeneChain f (n + 1)) :
    kleeneStabIndex f hf ≤ n :=
  Nat.find_min' (kleeneChain_stabilizes f hf) hn

/-- **最小稳定步的上界 `≤ card α`**：这是「有限步稳定」的定量形式
（步数不超过有限格的基数）。 -/
theorem kleeneStabIndex_le_card (f : α → α) (hf : Monotone f) :
    kleeneStabIndex f hf ≤ Fintype.card α := by
  -- 用存在性证明中同样的鸽笼论证，但直接对 `Nat.find` 的候选集取界
  by_contra h
  push_neg at h
  have hspec := kleeneStabIndex_spec f hf
  have hle : ∀ n : ℕ, kleeneChain f n ≤ kleeneChain f (n + 1) := kleeneChain_le_succ f hf
  have hmono : Monotone (kleeneChain f) := kleeneChain_monotone f hf
  -- 对 n < kleeneStabIndex f 都严格增（由极小性）
  have hlt : ∀ n : ℕ, n < kleeneStabIndex f hf →
      kleeneChain f n < kleeneChain f (n + 1) := by
    intro n hn
    refine lt_of_le_of_ne (hle n) (fun heq => ?_)
    have hmin := kleeneStabIndex_minimal f hf heq
    omega
  -- 于是前 card α + 1 步（均 < kleeneStabIndex）严格增 ⟹ 鸽笼
  have hltj : ∀ i j : ℕ, i < kleeneStabIndex f hf → i < j →
      kleeneChain f i < kleeneChain f j := by
    intro i j hi hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : kleeneChain f i < kleeneChain f (i + 1) := hlt i hi
    have h2 : kleeneChain f (i + 1) ≤ kleeneChain f (i + d + 1) := hmono (by omega)
    exact lt_of_lt_of_le h1 h2
  have hinj : Function.Injective
      (fun i : Fin (Fintype.card α + 1) => kleeneChain f (i : ℕ)) := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    have hi : (i : ℕ) < kleeneStabIndex f hf := by have := i.isLt; omega
    have hj : (j : ℕ) < kleeneStabIndex f hf := by have := j.isLt; omega
    rcases lt_or_gt_of_ne hne with hltij | hgtij
    · exact (ne_of_lt (hltj (i : ℕ) (j : ℕ) hi hltij)) hij
    · exact (ne_of_lt (hltj (j : ℕ) (i : ℕ) hj hgtij)) hij.symm
  have hcard := Fintype.card_le_of_injective
    (fun i : Fin (Fintype.card α + 1) => kleeneChain f (i : ℕ)) hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-! ## 四、稳定值：Kleene 极限（最小不动点） -/

/-- **Kleene 极限**：链在最小稳定步处的值，即 `F^{kleeneStabIndex}⊥`。
本文件将证明它恰是 `f` 的**最小不动点**。 -/
def kleeneLimit (f : α → α) (hf : Monotone f) : α :=
  kleeneChain f (kleeneStabIndex f hf)

/-- **稳定值是不动点**：`f (kleeneLimit f) = kleeneLimit f`。
由 `kleeneStabIndex_spec`（稳定）与 `kleeneChain_succ`（一步展开）直接得到。 -/
theorem kleeneLimit_fixed (f : α → α) (hf : Monotone f) :
    f (kleeneLimit f hf) = kleeneLimit f hf := by
  have hspec := kleeneStabIndex_spec f hf
  have h1 : kleeneChain f (kleeneStabIndex f hf + 1) = f (kleeneLimit f hf) := rfl
  rw [← h1]
  exact hspec.symm

/-- **最小性**：`kleeneLimit f` 不超过任意不动点 `y`（`f y = y`）。
归纳：`Fⁿ⊥ ≤ y` 对一切 `n`（`n = 0` 用 `bot_le`，后继用 `hf`），再取 `n = 稳定步`。 -/
theorem kleeneLimit_le_of_fixed (f : α → α) (hf : Monotone f) {y : α} (hy : f y = y) :
    kleeneLimit f hf ≤ y := by
  have hbound : ∀ n : ℕ, kleeneChain f n ≤ y := by
    intro n
    induction n with
    | zero => exact bot_le
    | succ n ih =>
        change f (kleeneChain f n) ≤ y
        rw [← hy]
        exact hf ih
  exact hbound (kleeneStabIndex f hf)

/-- **稳定后恒定**：若 `kleeneStabIndex f ≤ n`，则 `Fⁿ⊥ = kleeneLimit f`。
即链在最小稳定步之后不再变化。 -/
theorem kleeneChain_eq_limit_of_le (f : α → α) (hf : Monotone f) {n : ℕ}
    (hn : kleeneStabIndex f hf ≤ n) :
    kleeneChain f n = kleeneLimit f hf := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  have hfix := kleeneLimit_fixed f hf
  induction d with
  | zero => rfl
  | succ d ih =>
      have hstep : kleeneChain f (kleeneStabIndex f hf + (d + 1))
          = f (kleeneChain f (kleeneStabIndex f hf + d)) := rfl
      rw [hstep, ih, hfix]

/-- **Kleene 不动点定理（有限格版本，打包）**：有限偏序 + 有底 + 单调算子 ⟹
存在唯一的最小稳定步 `N ≤ card α`，链在 `N` 处稳定、稳定值是不动点且最小。
这是 Knaster–Tarski / Kleene 的**有限步稳定**形态，四条件一并给出。 -/
theorem kleene_fixed_point_finite (f : α → α) (hf : Monotone f) :
    kleeneStabIndex f hf ≤ Fintype.card α ∧
      kleeneChain f (kleeneStabIndex f hf) = kleeneChain f (kleeneStabIndex f hf + 1) ∧
      f (kleeneLimit f hf) = kleeneLimit f hf ∧
      (∀ y : α, f y = y → kleeneLimit f hf ≤ y) :=
  ⟨kleeneStabIndex_le_card f hf, kleeneStabIndex_spec f hf,
   kleeneLimit_fixed f hf, fun _ hy => kleeneLimit_le_of_fixed f hf hy⟩

/-- **最小不动点的唯一性**：任意使 `f y = y` 且被 `kleeneLimit f` 支配的 `y`
必与之相等（最小性是「≤」，配合 `kleeneLimit_le_of_fixed` 得双向）。 -/
theorem kleeneLimit_unique_minimal (f : α → α) (hf : Monotone f) {y : α} (hy : f y = y)
    (hle : y ≤ kleeneLimit f hf) :
    y = kleeneLimit f hf :=
  le_antisymm hle (kleeneLimit_le_of_fixed f hf hy)

/-! ## 五、应用：最小结 = `⋃ₙ Fⁿ ∅`（幂集格） -/

section Powerset

variable {β : Type*} [Fintype β]

/-- **`kleeneChain` 在 `Set β` 上的同义别名**：`powChain F` 的定义体只是把
参数原样转发给 `kleeneChain`（`Set β` 已由 `Set.instBot` 提供 `⊥ = ∅`）。
命名用意是让幂集语境下的链读作「幂集链」，而非声明 `F` 单调——`F` 的单调性
不是本定义的参数，单调性由下游定理以 `hF : Monotone F` 单独假设。
**说明**：本别名在文件内（含第五节、第六节的全部定理与清单）**无任何引用**，
保留仅为可读性；`F` 若记为 `F`，其语义与 `kleeneChain F` 完全一致。 -/
def powChain (F : Set β → Set β) : ℕ → Set β := kleeneChain F

/-- **幂集格上最小不动点 = Kleene 链的并 `⋃ₙ Fⁿ ∅`**（「最小结 = ⋃ₙ Fⁿ ∅」）：
单调 `F` 的最小不动点恰等于链的并。因为链在 `≤ card (Set β)` 步稳定，
并就是稳定项本身。
（本文件只声称**并 = 最小不动点**；`Set β` 的有限性由 `Fintype β` 保证，
故 `Fintype (Set β)` 由 `Set.fintype` 提供。） -/
theorem kleeneLimit_eq_iUnion (F : Set β → Set β) (hF : Monotone F) :
    (kleeneLimit F hF : Set β) = ⋃ n : ℕ, kleeneChain F n := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨kleeneStabIndex F hF, hx⟩
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    -- 链的每一层 ≤ 稳定值（稳定性 + 单调性）
    by_cases hle : n ≤ kleeneStabIndex F hF
    · exact kleeneChain_monotone F hF hle hn
    · have hge : kleeneStabIndex F hF ≤ n := by omega
      rw [kleeneChain_eq_limit_of_le F hF hge] at hn
      exact hn

/-- **并的成员刻画**：`x` 属于最小不动点 ⟺ `x` 属于某个 `Fⁿ ∅`。
先用 `kleeneLimit_eq_iUnion` 把最小不动点换写成链的并，再用 `Set.mem_iUnion`。 -/
theorem kleeneLimit_mem_iff (F : Set β → Set β) (hF : Monotone F) (x : β) :
    x ∈ (kleeneLimit F hF : Set β) ↔ ∃ n : ℕ, x ∈ kleeneChain F n := by
  rw [kleeneLimit_eq_iUnion F hF]
  exact Set.mem_iUnion

/-- **「最小结」的 `⊆`-刻画**：最小不动点包含于任意不动点（即任意「结」）。
这是幂集格上的最小性重述（「最小结」= 包含于所有结）。 -/
theorem kleeneLimit_subset_of_fixed (F : Set β → Set β) (hF : Monotone F)
    {Y : Set β} (hY : F Y = Y) :
    (kleeneLimit F hF : Set β) ⊆ Y :=
  fun _ hx => kleeneLimit_le_of_fixed F hF hY hx

/-- **不动点的基数上界**：任何不动点都至少与最小不动点一样大
（基数形式：`|最小结| ≤ |任意结|`，由 `⊆` 推出）。 -/
theorem kleeneLimit_card_le_of_fixed (F : Set β → Set β) (hF : Monotone F)
    {Y : Set β} (hY : F Y = Y) :
    (kleeneLimit F hF).ncard ≤ Y.ncard :=
  Set.ncard_le_ncard (kleeneLimit_subset_of_fixed F hF hY)

end Powerset

/-! ## 六、诚实缺口清单（本文件闭合了什么、没闭合什么）

闭合（均为机器验证的定理）：
  · Kleene 链的定义与单调性 —— `kleeneChain`、`kleeneChain_le_succ`、
    `kleeneChain_monotone`、`kleeneChain_le_of_le`；
  · **用 `Nat.find` 的最小稳定步**及其三性质 —— `kleeneStabIndex`、
    `kleeneStabIndex_spec`、`kleeneStabIndex_minimal`、`kleeneStabIndex_le_card`；
  · 稳定值是不动点且最小 —— `kleeneLimit`、`kleeneLimit_fixed`、
    `kleeneLimit_le_of_fixed`、`kleeneChain_eq_limit_of_le`、
    `kleene_fixed_point_finite`、`kleeneLimit_unique_minimal`；
  · **应用「最小结 = ⋃ₙ Fⁿ ∅」** —— `kleeneLimit_eq_iUnion`、
    `kleeneLimit_mem_iff`、`kleeneLimit_subset_of_fixed`、`kleeneLimit_card_le_of_fixed`。

未证 / 未做（诚实标注）：
  · **无限格（`CompleteLattice`）上的一般 Kleene 定理**
    `lfp F = ⨆ n, Fⁿ ⊥`：**未做**。需要 `ωScottContinuous` / 连续格理论
    （mathlib 的 `OrderHom.lfp`、`lfp_eq_sSup_iterate`），本文件不引入；
    有限步稳定的论证走**鸽笼原理**（`Fintype.card_le_of_injective`），
    因此不适用于无限格。
  · **`ωScottContinuous` 与单调性的桥接**：**未做**（同上）。
  · **幂集格版本的「无限 `β`」推广**：**未做**——本文件的幂集版本要求
    `[Fintype β]`（因为要 `Fintype (Set β)` 才能用鸽笼）。
  · **与 `RealRecursiveSemantics.least_fixed_point_finite` 的关系**：同一命题的
    两条独立路线（该文件用 `recFwd`，本文件用 `kleeneChain` + `Nat.find`），
    互为交叉验证；本文件**不声称**证明了该文件没有的东西，而是补上
    `Nat.find` 形式、极小性/上界与幂集应用。
-/

end Lattice
