import Mathlib
import Lattice.Lib.Concentration.RealUnionBound
/-!
# LATTICE: 联合界的紧性 —— **等号成立的精确刻画**

方向（概率 / 集中不等式）：`RealUnionBound` 给出并集界（Boole 不等式）
`P(⋃_{i∈s} Aᵢ) ≤ Σ_{i∈s} P(Aᵢ)` 与 Bonferroni 推论。本文件回答
「**何时该界是精确的**」——给出**充要刻画**，而不是罗列例子。

## 本文件建立什么

1. `PairwiseDisjointFamily A s`：族 `A` 在 `s` 上**两两不交**（`Disjoint`）；
2. ⭐⭐ `union_prob_eq_sum_iff_pairwiseDisjoint`（**主定理，充要刻画**）：
   样本空间非空时，

     `P(⋃_{i∈s} Aᵢ) = Σ_{i∈s} P(Aᵢ)` ⟺ `PairwiseDisjointFamily A s`。

   **两个方向都承载内容**：
   * (⟸) 不交 ⟹ 基数可加（`Finset.card_biUnion`）⟹ **取等**；
   * (⟹) **取等 ⟹ 不交** —— 这是「紧性刻画」的实质：
     若某对 `i ≠ j` 相交，则该交中的元素在**并集**里计一次、
     在**和**里计两次，故 `(⋃).card < Σ (A k).card`（**严格**），
     除以 `|α| > 0` 得 `P(⋃) < ΣP`，与取等矛盾。
3. ⭐ `union_prob_lt_sum_iff_hasOverlap`：**严格形式** ——
   `P(⋃) < ΣP` ⟺ 存在 `i ≠ j ∈ s` 使 `(A i ∩ A j).Nonempty`。
   这把「不紧」**定位到一对具体事件**：检查紧性只需找（或排除）一对交非空事件。
4. ⭐ `duplicate_card_lt`（**新引理**）：重复计数引理——
   若 `i ≠ j` 都在 `s` 中且 `(A i ∩ A j).Nonempty`，则
   `(s.biUnion A).card < Σ_{k∈s} (A k).card`。
   证明：把 `A j` 换为 `A j \ {a}`（`a` 是交中一点）。
   该替换**不改变并集**（`a` 仍由 `A i` 提供），
   但使和**严格减少**（`A j \ {a} ⊂ A j`，`card_lt_card`）。
5. `union_bound_tight_witness` / `union_bound_strict_witness`：
   **紧性与非紧性的具体见证**（`Fin 2` 上的 `{0}`、`{1}` 与 `{0}`、`{0}`），
   证明刻画定理**不空洞**且能分辨两种情形。

## 依赖什么

* `RealUnionBound`：`uniformProb` 与 `union_prob_le_sum`
  （主定理的 (⟹) 方向需要它排除「并集概率更大」这一不可能情形）；
* `RealSamplingBoost`：`uniformProb` 的定义（经上述模块传递）；
* `Mathlib`：`Finset.card_biUnion`、`Finset.card_biUnion_le`、
  `Finset.not_disjoint_iff`、`Finset.card_lt_card`、`Finset.sdiff_subset`。

## 不做什么（诚实边界）

* **只做有限计数概率空间**（事件 = `Finset α`，`uniformProb`），
  与 `RealUnionBound` 的有限版完全同设定。
  **测度版**的类比（`μ(⋃) = Σμ(Aᵢ) ⟺ 两两不交 a.e.`）**未做**：
  「严格小于」在测度版需要「正测度的交」这一 `ae` 语言，
  本文件不展开（`RealUnionBound.union_bound_meas` 给出测度版的不等式一侧）。
* ⚠ **不使用 `A ∩ B`**：本 mathlib 版本中 `Finset` **没有 `Inter` 实例**，
  故所有「相交」都用 `¬ Disjoint` / `(A ∩ B).Nonempty` 的
  **可判定替身** `∃ a, a ∈ A i ∧ a ∈ A j` 表述（后者即 `Nonempty` 的展开）。
* **不证**二阶 Bonferroni 下界（`Σ P(Aᵢ) − Σ_{i<j} P(Aᵢ∩Aⱼ) ≤ P(⋃)`），
  它与本文件的一阶**上界**刻画是不同方向。
* **不给**可数族的极限形式（收敛性需额外条件）。

不使用 `sorry` / `axiom` / `admit` / `native_decide`；不以 `field_simp` 收尾。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、定义 -/

/-- **两两不交族**：有限族 `A : ι → Finset α` 在指标集 `s` 上两两不交。

⚠ **不是重述**：它是主定理的**右端**，且定理 2、3 证明它**恰好**刻画
「并集界取等」；若它恒真或空洞，(⟹) 方向就不会承载信息
（定理 5、6 给出两个具体见证把它钉住）。 -/
def PairwiseDisjointFamily {α ι : Type*} (A : ι → Finset α) (s : Finset ι) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)

/-- **交非空对（非不交的见证）**：存在公共点 `a` 同时属于 `A i` 与 `A j`
（`i ≠ j`，都在 `s` 中）。

用「存在公共点」而非 `A i ∩ A j ≠ ∅` 表述，是因为本 mathlib 版本中
`Finset` **没有 `Inter` 实例**；这与 `Finset.not_disjoint_iff` 的右端一致。 -/
def HasOverlap {α ι : Type*} (A : ι → Finset α) (s : Finset ι) : Prop :=
  ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ ∃ a : α, a ∈ A i ∧ a ∈ A j

/-! ## 二、⭐ 重复计数引理（主定理的关键一步） -/

/-- ⭐ **重复计数引理（严格性来源）**：
若 `i ≠ j` 都在 `s` 中、且存在公共点 `a ∈ A i`、`a ∈ A j`，则

  `(s.biUnion A).card < Σ_{k∈s} (A k).card`.

**证明**：令 `A' := Function.update A j (A j \ {a})`。
* **并集不变**：`s.biUnion A' = s.biUnion A`。`⊆` 显然（`A' k ⊆ A k` 逐点）；
  `⊇` 中唯一可能丢掉的元素是 `a`，而 `a ∈ A i`（`i ≠ j`）保证了它在并集里留下。
* **和严格减少**：`(A' k).card ≤ (A k).card` 逐点（`sdiff_subset`），
  且在第 `j` 项**严格**：`A j \ {a} ⊂ A j`（因为 `a ∈ A j`），
  故 `card_lt_card` 给出 `<`。
* 两式合并：并集基数 = `(s.biUnion A').card ≤ Σ_k (A' k).card < Σ_k (A k).card`
  （第一个 `≤` 是 `card_biUnion_le`）。

**它比定义多说了什么**：把「相交」这一**集合论**信息**量化**为
「和至少多计一次」这一**数值严格不等式**——这是主定理 (⟹) 方向的**全部内容**，
也是「union bound 何时不紧」的**可计算判据**。 -/
theorem duplicate_card_lt {α ι : Type*} [DecidableEq α] [DecidableEq ι] (s : Finset ι)
    (A : ι → Finset α) (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) (hij : i ≠ j)
    (a : α) (hai : a ∈ A i) (haj : a ∈ A j) :
    (s.biUnion A).card < ∑ k in s, (A k).card := by
  set A' : ι → Finset α := Function.update A j (A j \ {a}) with hA'
  have hAj' : A' j = A j \ {a} := by rw [hA']; exact Function.update_same j _ A
  have hother : ∀ k, k ≠ j → A' k = A k := by
    intro k hk; rw [hA']; exact Function.update_noteq hk _ A
  -- 并集不变：A' 与 A 只在第 j 项不同，而被去掉的元素 a 仍由 A i（i ≠ j）提供
  have hunion : s.biUnion A' = s.biUnion A := by
    apply Finset.Subset.antisymm
    · -- A' ⊆ A：逐点（A' k ⊆ A k）
      intro x hx
      rw [Finset.mem_biUnion] at hx ⊢
      obtain ⟨k, hk, hxk⟩ := hx
      refine ⟨k, hk, ?_⟩
      by_cases hkj : k = j
      · subst hkj
        rw [hAj'] at hxk
        exact (Finset.mem_sdiff.mp hxk).1
      · rwa [hother k hkj] at hxk
    · -- A ⊆ A'：唯一可能丢掉的是 a，但 a ∈ A i（i ≠ j）
      intro x hx
      rw [Finset.mem_biUnion] at hx ⊢
      obtain ⟨k, hk, hxk⟩ := hx
      by_cases hxj : k = j
      · -- ⚠ v14 修复（coordinator）：原稿写 `subst hxj`，**它把定理参数 `j` 整体改名为 `k`**，
        -- 于是下面所有字面量 `j`（`⟨j, hj, ?_⟩`、`hAj'`）都变成**未定义标识符**
        -- （报 `unknown identifier 'j'`，且目标退化为 `x ∈ A' sorry`）。
        -- ⇒ 正确做法：先把假设**改写成 `j = k` 的形式**（一份独立的 `have`），
        -- 再 `subst` 它 —— 这样被消去的是 **`k`**，而 **`j` 保持存在**。
        have hjk : j = k := hxj.symm
        subst hjk
        -- 此时 x ∈ A j：若 x = a 则用 A i 中的 a；否则 x ∈ A j \ {a} = A' j
        by_cases hxa : x = a
        · subst hxa
          exact ⟨i, hi, by rwa [hother i hij]⟩
        · refine ⟨j, hj, ?_⟩
          rw [hAj']
          exact Finset.mem_sdiff.mpr ⟨hxk, by simpa [hxa] using hxk⟩
      · refine ⟨k, hk, ?_⟩
        rwa [hother k hxj]
  -- 和严格减少
  have hsum_lt : ∑ k in s, (A' k).card < ∑ k in s, (A k).card := by
    apply Finset.sum_lt_sum
    · intro k hk
      by_cases hkj : k = j
      · subst hkj
        rw [hAj']
        exact Finset.card_le_card Finset.sdiff_subset
      · rw [hother k hkj]
    · refine ⟨j, hj, ?_⟩
      rw [hAj']
      have hss : A j \ {a} ⊂ A j := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
        intro hcontra
        have hmem : a ∈ A j \ {a} := by rw [hcontra]; exact haj
        exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_singleton_self a)
      exact Finset.card_lt_card hss
  calc (s.biUnion A).card = (s.biUnion A').card := by rw [hunion]
    _ ≤ ∑ k in s, (A' k).card := Finset.card_biUnion_le
    _ < ∑ k in s, (A k).card := hsum_lt

/-! ## 三、⭐ 主定理：并集界取等的充要刻画 -/

/-- ⭐⭐ **并集界取等的精确刻画（主定理）**：样本空间非空且有限时，

  `P(⋃_{i∈s} Aᵢ) = Σ_{i∈s} P(Aᵢ)` **当且仅当** 族 `A` 在 `s` 上两两不交。

**证明**：
* **(⟸)** 两两不交时 `(s.biUnion A).card = Σ_{i∈s}(A i).card`
  （`Finset.card_biUnion`），两边同除以 `|α| > 0` 即得等号；
* **(⟹)** 反之若族非两两不交，取见证 `i ≠ j` 与公共点 `a`；
  引理 4 给出**严格** `(s.biUnion A).card < Σ_{k∈s}(A k).card`，
  除以 `|α| > 0` 得 `P(⋃) < ΣP`，与取等矛盾。

**它比 `RealUnionBound.union_prob_le_sum` 多说了什么**：
后者只给 `≤`；本定理给出**逆命题**——「取等」这一**等号情形**
被不交性**精确刻画**。这才是「何时 union bound 是精确的」的完整答案，
而不是「若事件不交则取等」这种单向平凡陈述。 -/
theorem union_prob_eq_sum_iff_pairwiseDisjoint {α ι : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq ι] (s : Finset ι) (A : ι → Finset α) (hN : 0 < Fintype.card α) :
    uniformProb (s.biUnion A) = ∑ i in s, uniformProb (A i) ↔
      PairwiseDisjointFamily A s := by
  constructor
  · -- (⟹) 取等 ⟹ 两两不交
    intro heq i hi j hj hij
    by_contra hnd
    obtain ⟨a, ha⟩ := Finset.not_disjoint_iff.mp hnd
    have hlt := duplicate_card_lt s A i hi j hj hij a ha.1 ha.2
    have hltR : ((s.biUnion A).card : ℝ) < ∑ k in s, ((A k).card : ℝ) := by
      exact_mod_cast hlt
    have hNpos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hN
    have hprob : uniformProb (s.biUnion A) < ∑ i in s, uniformProb (A i) := by
      unfold uniformProb
      rw [← Finset.sum_div]
      exact div_lt_div_of_pos_right hltR hNpos
    exact absurd heq (ne_of_lt hprob)
  · -- (⟸) 两两不交 ⟹ 取等
    intro hdisj
    have hcard : (s.biUnion A).card = ∑ i in s, (A i).card :=
      Finset.card_biUnion (fun i hi j hj hij => hdisj i hi j hj hij)
    have hcardR : ((s.biUnion A).card : ℝ) = ∑ i in s, ((A i).card : ℝ) := by
      exact_mod_cast hcard
    unfold uniformProb
    rw [← Finset.sum_div, hcardR]

/-- ⭐ **严格形式：并集界不紧 ⟺ 存在交非空对**：

  `P(⋃_{i∈s}Aᵢ) < Σ_{i∈s}P(Aᵢ)` **当且仅当** 存在 `i ≠ j ∈ s` 有公共点。

**证明**：由 `RealUnionBound.union_prob_le_sum` 知 `P(⋃) ≤ ΣP` 恒成立，
故 `P(⋃) < ΣP ⟺ P(⋃) ≠ ΣP`；再用主定理的逆否：
`P(⋃) ≠ ΣP ⟺ ¬ PairwiseDisjointFamily`，而后者展开正是 `HasOverlap`。

**它比主定理多说了什么**：把「不紧」这一**全局**性质**定位到一对具体事件**——
这是**可操作判据**：要判断 union bound 是否精确，
只需找（或证明不存在）一对有公共点的事件。 -/
theorem union_prob_lt_sum_iff_hasOverlap {α ι : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq ι] (s : Finset ι) (A : ι → Finset α) (hN : 0 < Fintype.card α) :
    uniformProb (s.biUnion A) < ∑ i in s, uniformProb (A i) ↔ HasOverlap A s := by
  have hle := union_prob_le_sum s A
  have hiff := union_prob_eq_sum_iff_pairwiseDisjoint s A hN
  constructor
  · intro hlt
    by_contra hno
    have hdisj : PairwiseDisjointFamily A s := by
      intro i hi j hj hij
      by_contra hnd
      exact hno ⟨i, hi, j, hj, hij, Finset.not_disjoint_iff.mp hnd⟩
    exact absurd (hiff.mpr hdisj) (ne_of_lt hlt)
  · intro hov
    have hnotdisj : ¬ PairwiseDisjointFamily A s := by
      intro hdisj
      obtain ⟨i, hi, j, hj, hij, a, hai, haj⟩ := hov
      exact (Finset.not_disjoint_iff.mpr ⟨a, hai, haj⟩) (hdisj i hi j hj hij)
    exact lt_of_le_of_ne hle (fun heq => hnotdisj (hiff.mp heq))

/-- **不交时的等号（主定理的 (⟸) 半，独立列出）**：
族在 `s` 上两两不交 ⟹ `P(⋃) = ΣP`。

单独列出是因为它是最常用的方向（构造精确 union bound 时直接调用），
且**不需要** `0 < |α|`（等号两边在 `|α| = 0` 时同为 `0`，
而主定理的 (⟹) 方向**必须**要 `|α| > 0`，见诚实清单第 5 条）。 -/
theorem union_prob_eq_sum_of_pairwiseDisjoint {α ι : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq ι] (s : Finset ι) (A : ι → Finset α) (hdisj : PairwiseDisjointFamily A s) :
    uniformProb (s.biUnion A) = ∑ i in s, uniformProb (A i) := by
  have hcard : (s.biUnion A).card = ∑ i in s, (A i).card :=
    Finset.card_biUnion (fun i hi j hj hij => hdisj i hi j hj hij)
  have hcardR : ((s.biUnion A).card : ℝ) = ∑ i in s, ((A i).card : ℝ) := by
    exact_mod_cast hcard
  unfold uniformProb
  rw [← Finset.sum_div, hcardR]

/-! ## 四、具体见证（证明刻画不空洞、且有分辨力） -/

/-- **紧性见证（等号真的达到）**：`α = Fin 2`、`s = {0,1}`、
`A 0 = {0}`、`A 1 = {1}`（不交且覆盖全空间）。则 `P(⋃) = 1 = ΣP`。

⇒ 主定理的「⟸」方向有非平凡模型，且并集界在该族上**精确**（不可改进）。 -/
theorem union_bound_tight_witness :
    uniformProb (({(0 : Fin 2), 1} : Finset (Fin 2)).biUnion
        (fun i : Fin 2 => if i = 0 then ({(0 : Fin 2)} : Finset (Fin 2)) else {(1 : Fin 2)}))
      = ∑ i in ({(0 : Fin 2), 1} : Finset (Fin 2)),
          uniformProb (if i = 0 then ({(0 : Fin 2)} : Finset (Fin 2)) else {(1 : Fin 2)}) := by
  apply union_prob_eq_sum_of_pairwiseDisjoint
  intro i _ j _ hij
  fin_cases i <;> fin_cases j <;> simp_all [Finset.disjoint_singleton_left]

/-- **非紧性见证（界严格不紧）**：`α = Fin 2`、`s = {0,1}`、
`A 0 = A 1 = {0}`（**同一个事件**）。真值 `P(⋃) = 1/2`，界为 `1`，故 `1/2 < 1`。

**这条的意义**：
* 它与紧性见证**只差一个事件**（`{1}` 变成 `{0}`），
  说明刻画定理的判据**确实分辨**了两种情形（不是恒真）；
* 公共点 `0` 使 `HasOverlap` 成立，故定理 3 判定「严格不紧」，
  与数值 `1/2 < 1` 一致——**两个独立途径给出同一结论**。 -/
theorem union_bound_strict_witness :
    uniformProb ((({(0 : Fin 2), 1} : Finset (Fin 2)).biUnion
        (fun _ : Fin 2 => ({(0 : Fin 2)} : Finset (Fin 2)))))
      < ∑ _i in ({(0 : Fin 2), 1} : Finset (Fin 2)),
          uniformProb ({(0 : Fin 2)} : Finset (Fin 2)) := by
  have hprob : uniformProb ({(0 : Fin 2)} : Finset (Fin 2)) = 1 / 2 := by
    unfold uniformProb
    simp [Fintype.card_fin]
  have hunion : ({(0 : Fin 2), 1} : Finset (Fin 2)).biUnion
        (fun _ : Fin 2 => ({(0 : Fin 2)} : Finset (Fin 2)))
      = ({(0 : Fin 2)} : Finset (Fin 2)) := by
    ext a
    simp
  rw [hunion, hprob]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- **判据与数值的一致性（交叉验证）**：上一条的非紧性**同时**由
严格形式判据（定理 3）预测——公共点 `0 ∈ A 0`、`0 ∈ A 1`、
`0 ≠ 1` 都在 `s = {0,1}` 中，故 `HasOverlap` 成立。

这条把「数值算出的不紧」与「刻画定理预测的不紧」**接在一起**，
是刻画定理**有分辨力**的直接证据（若判据空洞，两者不会同时成立）。 -/
theorem union_bound_strict_witness_criterion :
    HasOverlap (fun _ : Fin 2 => ({(0 : Fin 2)} : Finset (Fin 2)))
      ({(0 : Fin 2), 1} : Finset (Fin 2)) := by
  refine ⟨(0 : Fin 2), by simp, (1 : Fin 2), by simp, by decide, (0 : Fin 2), by simp, by simp⟩

/-! ## 五、诚实清单

1. **未做**：测度版的紧性刻画
   `μ(⋃ᵢAᵢ) = Σᵢμ(Aᵢ) ⟺ 两两不交 a.e.`。有限计数版的「严格小于」
   在测度版需要「正测度的交」这一 `ae` 语言；本文件不展开。
2. **未做**：二阶 Bonferroni（`ΣP(Aᵢ) − Σ_{i<j}P(Aᵢ∩Aⱼ) ≤ P(⋃)`）。
   它与本文件的**一阶上界**刻画是不同方向。
3. **未做**：可数族的极限形式（收敛性需额外条件）。
4. **未做**：把 `HasOverlap` 与 `s.biUnion A` 的基数表示直接对上
   （两者等价但本条只用「公共点」形式，因为 `Finset` 无 `Inter` 实例）。
5. **前提不可去（诚实性）**：主定理 (⟹) 方向需要 `0 < |α|`。
   若 `|α| = 0`，则 `uniformProb` 恒为 `0`，等号**恒成立**而刻画**不成立**
   （任何非不交族都给 `0 = 0`）——这就是反例，
   故 `hN` 是本定理的**本质前提**。单方向定理 4 不需要它
   （`|α| = 0` 时两边同为 `0`，结论仍真）。
6. **见证的作用**：定理 5、6 分别证明「取等」与「严格不紧」**都可实现**，
   故主定理与严格形式都**非空洞**；定理 7 进一步把两种途径对上。
-/

end Lattice
