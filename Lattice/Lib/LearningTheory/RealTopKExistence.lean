import Mathlib
import Lattice.Lib.Attention.RealDynamicRoute
/-!
# LATTICE: 一般 top-k 集的**存在性**、唯一性与最优性

`RealDynamicRoute` 把「存在一个 `k` 元集合 `S` 使 `IsTopK s S k`」当作**显式前提**
传给 `routeSelect`（其 docstring 明确写道：避免把组合存在性隐藏为未证前提）。
本文件补上这个缺口：**在有限指标集上一般 `k` 的 top-k 集确实存在**，并给出
唯一性、交换性质与求和最优性（交换论证）。

## 主要结果（全部无 sorry / axiom / admit）

1. `tk_exists_aux` / `exists_topK`（**核心存在性**）：`k ≤ card ι` ⟹
   存在 `S` 使 `IsTopK s S k`。证明是**贪心选择**：每步在剩余元素中取分数最大者，
   保持「S 内元素支配 S 外元素」的不变量——不需要显式排序（`Finset.sort`），
   只用 `Finset.exists_max_image` 与基数论证。
2. `topK_card_le`：top-k 集存在 ⟹ `k ≤ card ι`（必要性，说明 1 的假设是紧的）。
3. `topK_eq_univ_of_card_eq`：`k = card ι` 时 top-k 集就是全集。
4. `topK_unique_of_lt`（**唯一性**）：两个 top-k 集在「边界严格分离」
   （`∀ i ∈ S, j ∉ S, s j < s i`）下相等。
5. `topK_unique_of_gap`：分数间隔 `γ > 0`（`s j + γ ≤ s i`）是 4 的特例——
   即「间隔大于 0 时 top-k 唯一」。
6. `topK_unique_of_injective` / `exists_unique_topK_of_injective`：全部分数互异时
   top-k 集**唯一存在**。
7. `topK_swap_of_eq`（**交换性质**）：`i ∈ S`、`j ∉ S`、`s i = s j` 时，
   用 `j` 替换 `i` 仍是 top-k 集（平局下的选择自由度）。
8. `topK_sum_max`（**交换论证 / 求和最优性**）：若 `S` 是 top-k 型选择集，
   则任何与 `S` **同基数**的 `T` 满足 `∑_{T} s ≤ ∑_{S} s`——即 top-k 最大化保留分数和。
   证明用 `Finset.exists_max_image` 在 `T \ S` 上取最大元 `i0`，证明
   `∑_{T\S} s ≤ ∑_{S\T} s`（两边基数相等，逐项 `s i ≤ s i0 ≤ s j`）。
9. `topK_sum_eq`：任意两个 top-k 集的分数和相等（8 的双向应用）。
10. `topK_sum_mono_of_subset`：分数非负时保留集扩大不减少分数和（单调性）。

## 诚实边界（未做/降级，均显式标注）

- 本文件只处理**有限**指标集（`[Fintype ι]`）与实值分数；无限指标集上的 top-k
  存在性**未做**；
- `topK_sum_max` 的求和最优性要求 `T` 与 `S` **同基数**；本文件仅在 `T ⊆ S` 的**包含**
  情形下用 `topK_sum_mono_of_subset` 给出非负性版本（仅在 `s ≥ 0` 时），一般基数小于
  （`T.card < S.card`）的陈述仍然**未做**；
- 平局时的选择集**不唯一**是事实（`topK_swap_of_eq`），本文件不声称唯一性在无分离假设下成立；
- 「top-k 选择的计算复杂度 / 稳定排序实现」不涉及（纯组合）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 一、存在性：贪心选择（在剩余元素中反复取分数最大者） -/

/-- **贪心构造的不变量**：存在基数 `n` 的选择集 `S`，使得 `S` 内每个元素支配 `S` 外
每个元素（`IsTopK` 的支配部分）。证明：`n` 归纳；每步在补集上取分数最大者插入。 -/
theorem tk_exists_aux (s : ι → ℝ) :
    ∀ n : ℕ, n ≤ Fintype.card ι →
      ∃ S : Finset ι, S.card = n ∧ ∀ i ∈ S, ∀ j, j ∉ S → s j ≤ s i := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨∅, by simp, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨S, hScard, hSmax⟩ := ih (by omega)
    -- `S` 的基数严格小于全空间，故存在 `S` 之外的元素
    have hlt : S.card < Fintype.card ι := by omega
    have hex : ∃ j : ι, j ∉ S := by
      by_contra h
      push_neg at h
      have hsub : (Finset.univ : Finset ι) ⊆ S := fun j _ => h j
      have hle := Finset.card_le_card hsub
      simp only [Finset.card_univ] at hle
      omega
    -- 在补集上取分数最大者
    obtain ⟨j0, hj0mem, hj0max⟩ :=
      Finset.exists_max_image (Finset.univ.filter (fun j => j ∉ S)) s
        (by
          obtain ⟨j, hj⟩ := hex
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
    have hj0 : j0 ∉ S := (Finset.mem_filter.mp hj0mem).2
    refine ⟨insert j0 S, ?_, ?_⟩
    · rw [Finset.card_insert_of_not_mem hj0]
      omega
    · intro i hi j hj
      rcases Finset.mem_insert.mp hi with rfl | hiS
      · -- 新插入的最大元 `j0`：`j` 在补集中（或在 S 中但与 `j ∉ insert j0 S` 矛盾）
        by_cases hjS : j ∈ S
        · exact absurd hjS (fun hjs => hj (Finset.mem_insert.mpr (Or.inr hjs)))
        · exact hj0max j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjS⟩)
      · -- 原有元素：支配性由归纳假设给出（`S ⊆ insert j0 S`）
        have hjS : j ∉ S := fun hjs => hj (Finset.mem_insert.mpr (Or.inr hjs))
        exact hSmax i hiS j hjS

/-- **核心存在性定理**：`k ≤ card ι` 时 top-k 选择集存在。 -/
theorem exists_topK (s : ι → ℝ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    ∃ S : Finset ι, IsTopK s S k := by
  obtain ⟨S, hcard, hmax⟩ := tk_exists_aux s k hk
  exact ⟨S, hcard, hmax⟩

/-- 必要性：top-k 集存在 ⟹ `k ≤ card ι`（存在性假设 `hk` 是紧的）。 -/
theorem topK_card_le (s : ι → ℝ) {S : Finset ι} {k : ℕ} (hS : IsTopK s S k) :
    k ≤ Fintype.card ι := by
  have h := Finset.card_le_card (Finset.subset_univ S)
  simp only [Finset.card_univ, hS.1] at h
  exact h

/-- `k = card ι` 时 top-k 集必为全集（支配性无剩余元素可用）。 -/
theorem topK_eq_univ_of_card_eq (s : ι → ℝ) {S : Finset ι} {k : ℕ} (hS : IsTopK s S k)
    (hk : k = Fintype.card ι) : S = Finset.univ :=
  Finset.eq_univ_of_card S (by rw [hS.1, hk])

/-- 支配性质的便捷展开（`IsTopK` 的第二分量）。 -/
theorem topK_dominated (s : ι → ℝ) {S : Finset ι} {k : ℕ} (hS : IsTopK s S k) :
    ∀ i ∈ S, ∀ j, j ∉ S → s j ≤ s i := hS.2

/-! ## 二、唯一性：边界严格分离 -/

/-- **唯一性（严格分离版）**：两个 top-k 集在「边界严格分离」下相等。
若 `S ≠ T`，则同步取 `i ∈ S \ T`、`j ∈ T \ S`；由 `S` 的支配性与 `T` 的支配性
得到 `s i > s j` 与 `s i ≤ s j`，矛盾。 -/
theorem topK_unique_of_lt (s : ι → ℝ) {S T : Finset ι} {k : ℕ}
    (hS : IsTopK s S k) (hT : IsTopK s T k)
    (hsep : ∀ i ∈ S, ∀ j, j ∉ S → s j < s i) : S = T := by
  by_contra hne
  have hnotsub : ¬ S ⊆ T := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [hS.1, hT.1]))
  obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hnotsub
  have hnotsub' : ¬ T ⊆ S := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [hT.1, hS.1])).symm
  obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hnotsub'
  have h1 : s j < s i := hsep i hiS j hjS
  have h2 : s i ≤ s j := hT.2 j hjT i hiT
  linarith

/-- **唯一性（分数间隔版）**：存在间隔 `γ > 0` 使边界分离 `s j + γ ≤ s i` ⟹ top-k 唯一。
这是「分数间隔大于 0 时 top-k 稳定/唯一」的定量形式。 -/
theorem topK_unique_of_gap (s : ι → ℝ) {S T : Finset ι} {k : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (hS : IsTopK s S k) (hT : IsTopK s T k)
    (hgap : ∀ i ∈ S, ∀ j, j ∉ S → s j + γ ≤ s i) : S = T :=
  topK_unique_of_lt s hS hT fun i hiS j hjS => by
    have h := hgap i hiS j hjS
    linarith

/-- **唯一性（分数互异版）**：`s` 单射（无平局）⟹ 任意两个 top-k 集相等。 -/
theorem topK_unique_of_injective (s : ι → ℝ) (hinj : Function.Injective s) {S T : Finset ι}
    {k : ℕ} (hS : IsTopK s S k) (hT : IsTopK s T k) : S = T :=
  topK_unique_of_lt s hS hT fun i hiS j hjS => by
    have hle : s j ≤ s i := hS.2 i hiS j hjS
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact absurd (show j ∈ S from by simpa [hinj heq] using hiS) hjS

/-- **唯一存在性**：分数互异且 `k ≤ card ι` 时 top-k 集唯一存在。 -/
theorem exists_unique_topK_of_injective (s : ι → ℝ) (hinj : Function.Injective s) {k : ℕ}
    (hk : k ≤ Fintype.card ι) : ∃! S : Finset ι, IsTopK s S k := by
  obtain ⟨S, hS⟩ := exists_topK s hk
  exact ⟨S, hS, fun T hT => topK_unique_of_injective s hinj hT hS⟩

/-! ## 三、交换性质（平局下的选择自由度） -/

/-- **交换性质**：`S` 是 top-k 集，`i ∈ S`、`j ∉ S` 且 `s i = s j`，
则用 `j` 替换 `i` 后仍是 top-k 集（基数与支配性都保持）。
这也说明「top-k 集一般**不唯一**」，与 `topK_unique_of_injective` 的前提形成对照。 -/
theorem topK_swap_of_eq (s : ι → ℝ) {S : Finset ι} {k : ℕ} (hS : IsTopK s S k)
    {i j : ι} (hi : i ∈ S) (hj : j ∉ S) (heq : s i = s j) :
    IsTopK s (insert j (S.erase i)) k := by
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  have hje : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  refine ⟨?_, ?_⟩
  · rw [Finset.card_insert_of_not_mem hje, Finset.card_erase_add_one hi, hS.1]
  · intro a ha b hb
    have hb' : b ∉ S.erase i := fun h => hb (Finset.mem_insert.mpr (Or.inr h))
    rcases Finset.mem_insert.mp ha with haj | haS
    · -- `a = j`
      rw [haj]
      by_cases hbei : b = i
      · rw [hbei]
        linarith [heq]
      · have hbS : b ∉ S := fun hbs => hb' (Finset.mem_erase.mpr ⟨hbei, hbs⟩)
        have h := hS.2 i hi b hbS
        linarith [heq, h]
    · -- `a ∈ S.erase i`
      have haS' : a ∈ S := Finset.mem_of_mem_erase haS
      by_cases hbei : b = i
      · rw [hbei]
        have h := hS.2 a haS' j hj
        linarith [heq, h]
      · have hbS : b ∉ S := fun hbs => hb' (Finset.mem_erase.mpr ⟨hbei, hbs⟩)
        exact hS.2 a haS' b hbS

/-! ## 四、交换论证：top-k 最大化分数和 -/

/-- **交换论证（求和最大化）**：若 `S` 支配其补集（top-k 型选择集）且 `T` 与 `S` 同基数，
则 `∑_{T} s ≤ ∑_{S} s`。

证明：令 `U = T \ S`、`V = S \ T`。两边基数相等。
在 `U` 上取分数最大元 `i0`；对 `U` 逐项 `s i ≤ s i0`，对 `V` 逐项 `s i0 ≤ s j`
（因 `i0 ∉ S`、`j ∈ S`，用支配性）。两边各 `|U| = |V|` 项，逐项配对即得
`∑_{U} s ≤ ∑_{V} s`；再由 `∑_{T} = ∑_{T∩S} + ∑_{U}`、`∑_{S} = ∑_{T∩S} + ∑_{V}` 收尾。 -/
theorem topK_sum_max (s : ι → ℝ) {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → s j ≤ s i) :
    ∑ i in T, s i ≤ ∑ i in S, s i := by
  rcases Finset.eq_empty_or_nonempty (T \ S) with hU0 | hUne
  · -- `T \ S = ∅` ⟹ `T ⊆ S` ⟹ （同基数）`T = S`
    have hsub : T ⊆ S := by
      intro x hx
      by_contra hxS
      exact (Finset.eq_empty_iff_forall_not_mem.mp hU0) x (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
    have hTS : T = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [hTS]
  · -- `U = T \ S` 非空：取最大元 `i0`
    obtain ⟨i0, hi0mem, hi0max⟩ := Finset.exists_max_image (T \ S) s hUne
    have hi0S : i0 ∉ S := (Finset.mem_sdiff.mp hi0mem).2
    -- `|U| = |V|`
    have hcardUV : (T \ S).card = (S \ T).card := by
      have h1 := Finset.card_sdiff_add_card (s := T) (t := S)
      have h2 := Finset.card_sdiff_add_card (s := S) (t := T)
      rw [Finset.union_comm T S] at h1
      omega
    -- `∑_U s ≤ ∑_V s`
    have hUV : ∑ i in T \ S, s i ≤ ∑ j in S \ T, s j := by
      have hU : ∑ i in T \ S, s i ≤ ∑ _i in T \ S, s i0 :=
        Finset.sum_le_sum fun i hi => hi0max i hi
      have hV : ∑ _j in S \ T, s i0 ≤ ∑ j in S \ T, s j :=
        Finset.sum_le_sum fun j hj => htop j (Finset.mem_sdiff.mp hj).1 i0 hi0S
      have hcU : ∑ _i in T \ S, s i0 = (T \ S).card * s i0 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hcV : ∑ _j in S \ T, s i0 = (S \ T).card * s i0 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      calc
        ∑ i in T \ S, s i ≤ ∑ _i in T \ S, s i0 := hU
        _ = (T \ S).card * s i0 := hcU
        _ = (S \ T).card * s i0 := by rw [hcardUV]
        _ = ∑ _j in S \ T, s i0 := hcV.symm
        _ ≤ ∑ j in S \ T, s j := hV
    -- 分解 `∑_T` 与 `∑_S`
    have hTdec : ∑ i in T, s i = ∑ i in T ∩ S, s i + ∑ i in T \ S, s i := by
      have h := Finset.sum_sdiff (f := s) (s₁ := T ∩ S) (s₂ := T) Finset.inter_subset_left
      have hdiff : T \ (T ∩ S) = T \ S := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [hdiff] at h
      rw [← h]
      ring
    have hSdec : ∑ i in S, s i = ∑ i in S ∩ T, s i + ∑ i in S \ T, s i := by
      have h := Finset.sum_sdiff (f := s) (s₁ := S ∩ T) (s₂ := S) Finset.inter_subset_left
      have hdiff : S \ (S ∩ T) = S \ T := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [hdiff] at h
      rw [← h]
      ring
    calc
      ∑ i in T, s i = ∑ i in T ∩ S, s i + ∑ i in T \ S, s i := hTdec
      _ ≤ ∑ i in S ∩ T, s i + ∑ i in S \ T, s i := by
        rw [Finset.inter_comm T S]
        exact add_le_add_left hUV _
      _ = ∑ i in S, s i := hSdec.symm

/-- **分数和相等**：任意两个同 `k` 的 top-k 选择集保留的分数和相等
（`topK_sum_max` 的双向应用）——即「top-k 保留的总分数」是良定义的量。 -/
theorem topK_sum_eq (s : ι → ℝ) {S T : Finset ι} {k : ℕ}
    (hS : IsTopK s S k) (hT : IsTopK s T k) : ∑ i in T, s i = ∑ i in S, s i :=
  le_antisymm (topK_sum_max s (by rw [hS.1, hT.1]) hS.2)
    (topK_sum_max s (by rw [hT.1, hS.1]) hT.2)

/-- **单调性**：分数非负时保留集扩大（`T ⊆ S`）不减少分数和。 -/
theorem topK_sum_mono_of_subset (s : ι → ℝ) {S T : Finset ι} (hsub : T ⊆ S)
    (hs0 : ∀ i, 0 ≤ s i) : ∑ i in T, s i ≤ ∑ i in S, s i :=
  Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hs0 i

/-! ## 五、与块稀疏约束的交互（WP8 新增）

块稀疏注意力（`RealBlockSparse` / `RealBlockSparseExact`）先按**块掩码**筛出
可用块，再在块内做注意力；top-k 选择（`RealDynamicRoute` 的动态路由、KV 预算）
则先按分数排序再取前 `k`。两者的**组合顺序**（先筛块还是先取 top-k）会给出不同结果。
本节把「块约束」抽象为**候选集** `C`，刻画「候选内 top-k」的存在性、唯一性与
**块约束的价格**（相对全局 top-k 的损失）。

- **标注 —— 「块约束」的抽象层次**：本节把块约束建模为**候选元素集** `C`
  （可理解为「被块掩码允许入驻的块代表」），而不是「每个元素还被限制只能注意
  某些元素」的**成对**约束。后者会让「top-k 支配性」不再可用（最优集依赖成对
  结构），其存在性**未做**——见诚实边界。
- **标注 —— 复用**：`exists_topKIn` 的存在性证明复用本文件 `tk_exists_aux`
  的贪心不变量，只在每一步把「在补集上取最大」换成「在 `C` 的补集上取最大」；
  不重复引入排序设施。 -/

/-- **块约束可行集**（块稀疏与 top-k 的接口）：`C` 是**候选集**（被块掩码允许的
元素，如块代表），`IsTopKIn s C S k` 表示 `S` 是 `C` 内分数最大的 `k` 元子集。

三个分量：`S ⊆ C`（可行性）、`S.card = k`（预算）、
`∀ i ∈ S, ∀ j ∈ C, j ∉ S → s j ≤ s i`（**候选内**支配性）。

注意支配性的量词范围是 `j ∈ C` 而**不是** `j : ι`——这正是块约束削弱最优性的地方。 -/
def IsTopKIn (s : ι → ℝ) (C S : Finset ι) (k : ℕ) : Prop :=
  S ⊆ C ∧ S.card = k ∧ ∀ i ∈ S, ∀ j ∈ C, j ∉ S → s j ≤ s i

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
/-- 候选内支配性的展开（`IsTopKIn` 的第三分量）。 -/
theorem topKIn_dominated (s : ι → ℝ) {C S : Finset ι} {k : ℕ} (hS : IsTopKIn s C S k) :
    ∀ i ∈ S, ∀ j ∈ C, j ∉ S → s j ≤ s i := hS.2.2

omit [Fintype ι] [Nonempty ι] in
/-- **块约束下的存在性**：`k ≤ C.card` ⟹ 存在候选集 `C` 内的 top-k 集。

证明：对 `C.card` 做贪心归纳（同 `tk_exists_aux`，但每步在 `C \ S` 中取最大者），
保持「`S ⊆ C` 且 `S` 内每个元素支配 `C \ S` 中每个元素」的不变量。 -/
theorem exists_topKIn (s : ι → ℝ) (C : Finset ι) {k : ℕ} (hk : k ≤ C.card) :
    ∃ S : Finset ι, IsTopKIn s C S k := by
  classical
  have key : ∀ n : ℕ, n ≤ C.card → ∃ S : Finset ι,
      S ⊆ C ∧ S.card = n ∧ ∀ i ∈ S, ∀ j ∈ C, j ∉ S → s j ≤ s i := by
    intro n
    induction n with
    | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨S, hSC, hScard, hSmax⟩ := ih (by omega)
      have hlt : S.card < C.card := by omega
      have hex : ∃ j ∈ C, j ∉ S := by
        by_contra h
        push_neg at h
        have hsub : C ⊆ S := fun j hj => h j hj
        have := Finset.card_le_card hsub
        omega
      obtain ⟨j0, hj0C, hj0notinS⟩ := hex
      obtain ⟨j1, hj1mem, hj1max⟩ :=
        Finset.exists_max_image (C.filter (fun j => j ∉ S)) s
          ⟨j0, Finset.mem_filter.mpr ⟨hj0C, hj0notinS⟩⟩
      have hj1C : j1 ∈ C := (Finset.mem_filter.mp hj1mem).1
      have hj1S : j1 ∉ S := (Finset.mem_filter.mp hj1mem).2
      refine ⟨insert j1 S, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hj1C
        · exact hSC hx
      · rw [Finset.card_insert_of_not_mem hj1S]; omega
      · intro i hi j hj hjnotin
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · by_cases hjS : j ∈ S
          · exact absurd hjS (fun hjs => hjnotin (Finset.mem_insert.mpr (Or.inr hjs)))
          · exact hj1max j (Finset.mem_filter.mpr ⟨hj, hjS⟩)
        · have hjS : j ∉ S := fun hjs => hjnotin (Finset.mem_insert.mpr (Or.inr hjs))
          exact hSmax i hiS j hj hjS
  obtain ⟨S, h1, h2, h3⟩ := key k hk
  exact ⟨S, h1, h2, h3⟩

/-- **块约束削弱最优性（核心，价格 ≥ 0）**：候选内 top-k 的分数和**不超过**
全局 top-k 的分数和。

即「先按块筛候选再取 top-k」不会优于「直接全局取 top-k」——**块约束的价格**
恰是丢失候选集外元素所付出的分数。证明是 `topK_sum_max` 的实例化
（全局 top-k 支配**所有**元素，故也支配 `S`）。

诚实标注：这是**单侧**结论（价格 ≥ 0）；价格的**精确值**由
`topKIn_mass_deficit` 给出（候选集内未入选者的分数和），
但「价格 ≥ 某个正数」的**下界**需要候选集外的具体构造，**未做**。 -/
theorem topKIn_sum_le_topK (s : ι → ℝ) {C S T : Finset ι} {k : ℕ}
    (hS : IsTopKIn s C S k) (hT : IsTopK s T k) :
    ∑ i in S, s i ≤ ∑ i in T, s i := by
  -- `topK_sum_max s hcard htop` 给出 `∑_X ≤ ∑_Y`，其中 `Y` 是支配集、`X` 与 `Y` 同基数。
  -- 这里支配集取全局 top-k 的 `T`，被比较集取 `S`。
  exact topK_sum_max s (by rw [hT.1, hS.2.1]) hT.2

omit [Fintype ι] [Nonempty ι] in
/-- **块约束的价格（精确分解）**：候选集的质量分解为
`∑_C s = ∑_S s + ∑_{C \ S} s`——即候选集内「入选」与「落选」两部分之和。

这是价格的**精确记账**（与 `RealBlockSparseExact` 的
`maskCount_add_compl_eq_total` 同源的互补记账，在实数求和上的形式）。

**注意 R3 更正（悬空引用）**：`RealBlockSparseExact` **不在本文件的 import 闭包内**
（本文件只 `import Mathlib` + `RealDynamicRoute`），故上述对应关系是
**跨模块的文字类比**，**不构成本文件内的可引用依赖**——本文件**未** import
该模块，也**未**在该模块内使用任何引理。本定理的证明**完全自足**
（只用 `Finset.sum_sdiff` / `Finset.sum_filter`）。 -/
theorem topKIn_mass_deficit (s : ι → ℝ) {C S : Finset ι} {k : ℕ} (hS : IsTopKIn s C S k) :
    ∑ i in C, s i = ∑ i in S, s i + ∑ i in C \ S, s i := by
  have h := Finset.sum_sdiff (f := s) hS.1
  rw [Finset.sdiff_eq_filter] at h ⊢
  simp only [Finset.sum_filter] at h ⊢
  linarith

omit [Fintype ι] [Nonempty ι] in
/-- **块约束下的唯一性**：候选内 top-k 在「候选内严格分离」下唯一。

注意分离条件只须对**候选**成立（`j ∈ C`）——候选外的元素不参与比较，
故块约束**放宽**了唯一性的条件（全局版要求对所有 `j : ι` 分离）。 -/
theorem topKIn_unique_of_lt (s : ι → ℝ) {C S T : Finset ι} {k : ℕ}
    (hS : IsTopKIn s C S k) (hT : IsTopKIn s C T k)
    (hsep : ∀ i ∈ S, ∀ j ∈ C, j ∉ S → s j < s i) : S = T := by
  by_contra hne
  have hnotsub : ¬ S ⊆ T := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [hS.2.1, hT.2.1]))
  obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hnotsub
  have hnotsub' : ¬ T ⊆ S := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [hT.2.1, hS.2.1])).symm
  obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hnotsub'
  have hjC : j ∈ C := hT.1 hjT
  have h1 : s j < s i := hsep i hiS j hjC hjS
  have h2 : s i ≤ s j := hT.2.2 j hjT i (hS.1 hiS) hiT
  linarith

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
/-- **块约束无损的条件**：若候选集 `C` 已包含某个全局 top-k 集 `T`（`T ⊆ C`），
则 `T` 也是候选内 top-k——此时块约束**不损失任何最优性**。

这给出「块掩码选得足够好（覆盖了全局 top-k 的头）时，先筛块不影响结果」的精确判据，
与 `topKIn_sum_le_topK`（一般情形价格 ≥ 0）合起来刻画了块约束的代价结构。 -/
theorem topKIn_of_topK_subset (s : ι → ℝ) {C T : Finset ι} {k : ℕ}
    (hT : IsTopK s T k) (hsub : T ⊆ C) : IsTopKIn s C T k :=
  ⟨hsub, hT.1, fun i hi j _ hj => hT.2 i hi j hj⟩

omit [Fintype ι] [Nonempty ι] in
/-- **候选集内部的支配性求和（辅助，核心）**：若 `S' ⊆ C'` 且 `S'` 支配 `C'` 中
所有非 `S'` 元素，而 `S ⊆ C'` 且 `S.card = S'.card`，则 `∑_S s ≤ ∑_{S'} s`。

这是 `topK_sum_max` 在「比较范围限制在 `C'` 内」时的版本：把支配性从
「全体 `j : ι`」放宽到「`j ∈ C'`」，代价是要求 `S ⊆ C'`。

证明：沿用交换论证的框架。令 `U = S \ S'`、`V = S' \ S`。有 `U ⊆ C'`、`V ⊆ C'`，
两边基数相等；在 `U` 上取最大元 `i0`（`i0 ∈ C'`、`i0 ∉ S'`），
对 `U` 逐项 `s i ≤ s i0`，对 `V` 逐项 `s i0 ≤ s j`（`j ∈ C'`、`j ∉ S'`）。 -/
theorem sum_le_of_dominated_in (s : ι → ℝ) {C' S S' : Finset ι}
    (hinc : S ⊆ C') (hcard : S.card = S'.card)
    (htop : ∀ i ∈ S', ∀ j ∈ C', j ∉ S' → s j ≤ s i) :
    ∑ i in S, s i ≤ ∑ i in S', s i := by
  rcases Finset.eq_empty_or_nonempty (S \ S') with hU0 | hUne
  · have hsub : S ⊆ S' := by
      intro x hx
      by_contra hxS
      exact (Finset.eq_empty_iff_forall_not_mem.mp hU0) x (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
    have hSS' : S = S' := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [hSS']
  · obtain ⟨i0, hi0mem, hi0max⟩ := Finset.exists_max_image (S \ S') s hUne
    have hi0S : i0 ∉ S' := (Finset.mem_sdiff.mp hi0mem).2
    have hi0C : i0 ∈ C' := hinc (Finset.mem_sdiff.mp hi0mem).1
    have hcardUV : (S \ S').card = (S' \ S).card := by
      have h1 := Finset.card_sdiff_add_card (s := S) (t := S')
      have h2 := Finset.card_sdiff_add_card (s := S') (t := S)
      rw [Finset.union_comm S S'] at h1
      omega
    have hUV : ∑ i in S \ S', s i ≤ ∑ j in S' \ S, s j := by
      have hU : ∑ i in S \ S', s i ≤ ∑ _i in S \ S', s i0 :=
        Finset.sum_le_sum fun i hi => hi0max i hi
      have hV : ∑ _j in S' \ S, s i0 ≤ ∑ j in S' \ S, s j :=
        Finset.sum_le_sum fun j hj => htop j (Finset.mem_sdiff.mp hj).1 i0 hi0C hi0S
      have hcU : ∑ _i in S \ S', s i0 = (S \ S').card * s i0 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hcV : ∑ _j in S' \ S, s i0 = (S' \ S).card * s i0 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      calc
        ∑ i in S \ S', s i ≤ ∑ _i in S \ S', s i0 := hU
        _ = (S \ S').card * s i0 := hcU
        _ = (S' \ S).card * s i0 := by rw [hcardUV]
        _ = ∑ _j in S' \ S, s i0 := hcV.symm
        _ ≤ ∑ j in S' \ S, s j := hV
    have hSdec : ∑ i in S, s i = ∑ i in S ∩ S', s i + ∑ i in S \ S', s i := by
      have h := Finset.sum_sdiff (f := s) (s₁ := S ∩ S') (s₂ := S) Finset.inter_subset_left
      have hdiff : S \ (S ∩ S') = S \ S' := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
      rw [hdiff] at h
      rw [← h]; ring
    have hS'dec : ∑ i in S', s i = ∑ i in S' ∩ S, s i + ∑ i in S' \ S, s i := by
      have h := Finset.sum_sdiff (f := s) (s₁ := S' ∩ S) (s₂ := S') Finset.inter_subset_left
      have hdiff : S' \ (S' ∩ S) = S' \ S := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
      rw [hdiff] at h
      rw [← h]; ring
    calc
      ∑ i in S, s i = ∑ i in S ∩ S', s i + ∑ i in S \ S', s i := hSdec
      _ ≤ ∑ i in S' ∩ S, s i + ∑ i in S' \ S, s i := by
        rw [Finset.inter_comm S S']
        exact add_le_add_left hUV _
      _ = ∑ i in S', s i := hS'dec.symm

/-- **块约束的单调性（候选集越大越优，核心）**：`C ⊆ C'` 时，`C'` 内的候选 top-k
分数和**不低于** `C` 内的。即放宽块掩码（允许更多块）不会变差。

证明：`S'` 是 `C'` 内的 top-k，故 `S'` 支配 `C'` 中所有非 `S'` 元素；
而 `S ⊆ C ⊆ C'` 且两者同基数，故可直接用 `sum_le_of_dominated_in`（把支配范围
限制在 `C'` 内的交换论证）。 -/
theorem topKIn_sum_mono_candidate (s : ι → ℝ) {C C' S S' : Finset ι} {k : ℕ}
    (hC : C ⊆ C') (hS : IsTopKIn s C S k) (hS' : IsTopKIn s C' S' k) :
    ∑ i in S, s i ≤ ∑ i in S', s i :=
  sum_le_of_dominated_in (s := s) (S := S) (S' := S') (C' := C')
    (fun x hx => hC (hS.1 hx)) (by rw [hS.2.1, hS'.2.1]) hS'.2.2

end Lattice
