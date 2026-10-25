import Mathlib

/-!
# LATTICE: 非阿基米德范数 —— ultrametric 性质（模型无关）

把 p-adic 型范数的**纯结构性质**形式化，用结构类而不是具体 p-adic 数：

    class IsNonarchimedeanNorm (K) [NormedField K] where
      norm_add_le_max : ∀ x y, ‖x + y‖ ≤ max ‖x‖ ‖y‖

在该假设下证明（全部模型无关，任意 `NormedField K`）：

  1. `na_norm_sub_le_max`：`‖x − y‖ ≤ max ‖x‖ ‖y‖`；
  2. `na_norm_add_eq_max_of_ne`（**强三角/等边**）：`‖x‖ ≠ ‖y‖ ⟹ ‖x+y‖ = max ‖x‖ ‖y‖`；
  3. `na_norm_sub_eq_max_of_ne`：`‖x‖ ≠ ‖y‖ ⟹ ‖x−y‖ = max ‖x‖ ‖y‖`（等边三角形性质）；
  4. `na_norm_finset_sum_le` / `na_norm_finset_sum_lt` / `na_norm_finset_sum_le_sup'`：
   `‖∑‖ ≤ max`（任意有限和）；
  5. `na_isClosed_ball` / `na_ball_isClopen`：**开球既开又闭**（clopen）；
  6. `na_tail_sum_norm_lt`：`‖aₙ‖ → 0 ⟹ 尾和 `∑_{m≤i<m+k} aᵢ` 的范数 → 0`
   （非阿基米德级数收敛判据的 Cauchy 内核）；
  7. `na_converges_of_tendsto_zero`：在**显式完备性假设** `[CompleteSpace K]` 下，
   `‖aₙ‖ → 0` ⟹ 部分和收敛（Cauchy 判据 + 完备性）。

**诚实标注（降级/未做）**：
- 完备性在本文件作为**显式假设** `[CompleteSpace K]`；
  **但 mathlib 4.14 已提供真正的 p-adic 完备域**——
  `Mathlib/NumberTheory/Padics/PadicNumbers.lean`（注意目录名是 **`Padics`（复数）**）：
  - `def Padic (p : ℕ) [Fact p.Prime]`（`:429`，记法 `ℚ_[p]`）；
  - **`instance : IsUltrametricDist ℚ_[p]`（`:707`）** ——「强三角不等式」的 **mathlib 官方类型类**；
  - `instance : NontriviallyNormedField ℚ_[p]`（`:794`）；
  - **`instance : CompleteSpace ℚ_[p]`（`:921`）**。
  故「p-adic 完备性未做」应**降级为「未与 `ℚ_[p]` 接线」**，而**不是**「mathlib 没有 `ℚ_p`」：
  本文件的 ultrametric 结构理论（任意 `NormedField K` + `IsNonarchimedeanNorm`）与
  mathlib 的 `ℚ_[p]` 实例**可以对接**（`IsNonarchimedeanNorm` ↔ `IsUltrametricDist`），
  但**具体对接定理本文件未做**（`import Mathlib.NumberTheory.Padics.PadicNumbers`
  会显著拉长编译，留待单独一轮）。
- `IsNonarchimedeanNorm` 是自定义结构类（mathlib 另有 `NonarchimedeanRing`、`IsNonarchimedean`、
  **`IsUltrametricDist`**），本文件**不注册**全局实例、也不声称与它们等价，
  避免与 `ℚ_[p]` 等具体实例冲突——**降级**为纯结构理论；
- **未做**：`IsNonarchimedeanNorm K ↔ IsUltrametricDist K` 的等价定理（mathlib 的
  `IsUltrametricDist` 是**距离**层面的陈述，本类在**范数**层面，桥接需要
  `dist_eq_norm` 的逐项翻译——留待单独一轮）；
- `Padic p` 的具体实例**未接线**（原因见上：编译成本，且需与本文件的结构类做等价翻译）；
- 闭球是开集（`Metric.closedBall` 的 `IsOpen`）**未做**（需要「闭球中每点都是球心」的额外论证），
  标注未做；
- 具体函数空间（`C(K)`）与其它非阿基米德分析结论未做。

无 `sorry`/`axiom`/`admit`。
-/

noncomputable section

namespace Lattice

open scoped BigOperators Topology

variable {K : Type*} [NormedField K]

/-- **非阿基米德范数（结构类）**：`‖x + y‖ ≤ max ‖x‖ ‖y‖`（强三角不等式）。
模型无关：任何 `NormedField K` 都可（不）满足它；p-adic 域是其典型实例。 -/
class IsNonarchimedeanNorm (K : Type*) [NormedField K] : Prop where
  norm_add_le_max : ∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖

variable [IsNonarchimedeanNorm K]

/-- 强三角（减法形式）：`‖x − y‖ ≤ max ‖x‖ ‖y‖`。 -/
lemma na_norm_sub_le_max (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsNonarchimedeanNorm.norm_add_le_max x (-y)
  simpa [sub_eq_add_neg, norm_neg] using h

/-! ## 第一节：等边三角形 / 强三角等号情形 -/

/-- **强三角的等号情形（`‖x‖ < ‖y‖`）**：`‖x + y‖ = max ‖x‖ ‖y‖`。
核心论证：`‖y‖ = ‖(x+y) − x‖ ≤ max ‖x+y‖ ‖x‖`；若 `‖x+y‖ < ‖y‖` 则右边 `max < ‖y‖`，
矛盾，故 `‖y‖ ≤ ‖x+y‖`；结合强三角得等号。 -/
lemma na_norm_add_eq_max_of_lt {x y : K} (hlt : ‖x‖ < ‖y‖) :
    ‖x + y‖ = max ‖x‖ ‖y‖ := by
  have hbound : ‖y‖ ≤ max ‖x + y‖ ‖x‖ := by
    calc ‖y‖ = ‖(x + y) - x‖ := by rw [add_sub_cancel_left]
      _ ≤ max ‖x + y‖ ‖x‖ := na_norm_sub_le_max _ _
  have hxy : ‖y‖ ≤ ‖x + y‖ := by
    by_contra hc
    rw [not_le] at hc
    have hmax : max ‖x + y‖ ‖x‖ < ‖y‖ := max_lt hc hlt
    linarith
  have hle : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsNonarchimedeanNorm.norm_add_le_max x y
  rw [max_eq_right (le_of_lt hlt)] at hle ⊢
  exact le_antisymm hle hxy

/-- **强三角的等号情形**：`‖x‖ ≠ ‖y‖ ⟹ ‖x + y‖ = max ‖x‖ ‖y‖`。 -/
theorem na_norm_add_eq_max_of_ne {x y : K} (h : ‖x‖ ≠ ‖y‖) :
    ‖x + y‖ = max ‖x‖ ‖y‖ := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact na_norm_add_eq_max_of_lt hlt
  · rw [add_comm, max_comm]
    exact na_norm_add_eq_max_of_lt hgt

/-- **等边三角形性质**：`‖x‖ ≠ ‖y‖ ⟹ ‖x − y‖ = max ‖x‖ ‖y‖`。 -/
theorem na_norm_sub_eq_max_of_ne {x y : K} (h : ‖x‖ ≠ ‖y‖) :
    ‖x - y‖ = max ‖x‖ ‖y‖ := by
  have h' : ‖x‖ ≠ ‖-y‖ := by simpa [norm_neg] using h
  simpa [sub_eq_add_neg] using na_norm_add_eq_max_of_ne h'

/-! ## 第二节：有限和上界（`‖∑‖ ≤ max`） -/

/-- **有限和的强三角界（非严格）**：`0 ≤ C` 且 `∀ i ∈ s, ‖f i‖ ≤ C` ⟹ `‖∑_{i∈s} f i‖ ≤ C`。 -/
lemma na_norm_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i in s, f i‖ ≤ C := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty, norm_zero]
    exact hC
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    have h1 : ‖f a‖ ≤ C := h a (Finset.mem_insert_self a s)
    have h2 : ‖∑ i in s, f i‖ ≤ C :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact le_trans (IsNonarchimedeanNorm.norm_add_le_max _ _) (max_le h1 h2)

/-- **有限和的强三角界（严格）**：`0 < C` 且 `∀ i ∈ s, ‖f i‖ < C` ⟹ `‖∑_{i∈s} f i‖ < C`。 -/
lemma na_norm_finset_sum_lt {ι : Type*} (s : Finset ι) (f : ι → K) (C : ℝ) (hC : 0 < C)
    (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i in s, f i‖ < C := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty, norm_zero]
    exact hC
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    have h1 : ‖f a‖ < C := h a (Finset.mem_insert_self a s)
    have h2 : ‖∑ i in s, f i‖ < C :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact lt_of_le_of_lt (IsNonarchimedeanNorm.norm_add_le_max _ _) (max_lt h1 h2)

/-- **有限和的 max 形式**：非空 `s` 上 `‖∑_{i∈s} f i‖ ≤ s.sup' hs (‖f ·‖)`。 -/
lemma na_norm_finset_sum_le_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → K) :
    ‖∑ i in s, f i‖ ≤ s.sup' hs (fun i => ‖f i‖) := by
  obtain ⟨i, hi⟩ := hs
  exact na_norm_finset_sum_le s f _
    (le_trans (norm_nonneg (f i)) (Finset.le_sup' (fun i => ‖f i‖) hi))
    (fun j hj => Finset.le_sup' (fun i => ‖f i‖) hj)

/-! ## 第三节：球既开又闭（clopen） -/

/-- **开球是闭集**：在非阿基米德范数下，`Metric.ball x r` 的补集是开集。
证明：若 `y ∉ ball x r` 且 `y ≠ x`，取 `ε = ‖y − x‖ > 0`；对 `ball y ε` 中任意 `z`
有 `‖z − y‖ < ‖y − x‖`，由 `na_norm_add_eq_max_of_lt` 得
`‖z − x‖ = ‖(z−y) + (y−x)‖ = ‖y − x‖ ≥ r`，故 `z ∉ ball x r`。 -/
theorem na_isClosed_ball (x : K) (r : ℝ) : IsClosed (Metric.ball x r) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro y hy
  simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_eq_norm] at hy
  by_cases hyx : y = x
  · -- y = x 且 r ≤ 0：ball x r = ∅，半径 1 的球完全落在补集内
    subst hyx
    have hy0 : r ≤ 0 := by simpa using hy
    refine ⟨1, one_pos, ?_⟩
    intro z hz hzx
    simp only [Metric.mem_ball, dist_eq_norm] at hzx
    have h0 : (0 : ℝ) ≤ ‖z - y‖ := norm_nonneg _
    linarith
  · refine ⟨‖y - x‖, norm_pos_iff.mpr (sub_ne_zero.mpr hyx), ?_⟩
    intro z hz hzx
    simp only [Metric.mem_ball, dist_eq_norm] at hz hzx
    have hkey : z - x = (z - y) + (y - x) := by ring
    rw [hkey, na_norm_add_eq_max_of_lt hz, max_eq_right (le_of_lt hz)] at hzx
    linarith

/-- **开球既开又闭（clopen）**：`Metric.ball x r` 的 `IsClopen`。 -/
theorem na_ball_isClopen (x : K) (r : ℝ) : IsClopen (Metric.ball x r) :=
  ⟨na_isClosed_ball x r, Metric.isOpen_ball⟩

/-! ## 第四节：级数收敛判据（`‖aₙ‖ → 0 ⟹ Cauchy`） -/

/-- **尾和范数 → 0**：`‖aₙ‖ → 0` ⟹ 任意尾部有限和 `∑_{m≤i<m+k} aᵢ` 的范数 → 0。
这是非阿基米德级数「项 → 0 ⟹ 收敛」的 Cauchy 内核（尾和即部分和之差：
`∑_{i<m+k} aᵢ − ∑_{i<m} aᵢ = ∑_{m≤i<m+k} aᵢ`，见 `Finset.sum_Ico_eq_sub`）。 -/
theorem na_tail_sum_norm_lt (a : ℕ → K)
    (h : Filter.Tendsto (fun n => ‖a n‖) Filter.atTop (𝓝 0)) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ k : ℕ,
      ‖∑ i in Finset.Ico m (m + k), a i‖ < eps := by
  intro eps heps
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ‖a n‖ < eps := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) eps heps
    exact ⟨N, fun n hn => by
      have := hN n hn
      simpa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a n))] using this⟩
  refine ⟨N, fun m hm k => ?_⟩
  refine na_norm_finset_sum_lt _ _ eps heps ?_
  intro i hi
  exact hN i (le_trans hm (Finset.mem_Ico.mp hi).1)

omit [IsNonarchimedeanNorm K] in
/-- 部分和之差 = 尾和（`∑_{i<n} − ∑_{i<m} = ∑_{m≤i<n}`，`m ≤ n`）。 -/
lemma na_sum_range_sub_eq_Ico (a : ℕ → K) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.range n, a i) - (∑ i in Finset.range m, a i)
      = ∑ i in Finset.Ico m n, a i :=
  (Finset.sum_Ico_eq_sub a hmn).symm

/-- **非阿基米德级数收敛（显式完备性假设）**：`[CompleteSpace K]` 下，
`‖aₙ‖ → 0` ⟹ 部分和 `n ↦ ∑_{i<n} aᵢ` 收敛。

证明：由 `na_tail_sum_norm_lt` 与 `na_sum_range_sub_eq_Ico`（尾和 = 部分和之差）得部分和是
Cauchy 序列，再用 `cauchySeq_tendsto_of_complete` 得到极限。

诚实标注：**完备性作为显式假设** `[CompleteSpace K]`；
**mathlib 4.14 的 `ℚ_[p]` 满足它**（`PadicNumbers.lean:921`），但本文件不做接线。 -/
theorem na_converges_of_tendsto_zero [CompleteSpace K] (a : ℕ → K)
    (h : Filter.Tendsto (fun n => ‖a n‖) Filter.atTop (𝓝 0)) :
    ∃ L : K, Filter.Tendsto (fun n => ∑ i in Finset.range n, a i) Filter.atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro eps heps
  obtain ⟨N, hN⟩ := na_tail_sum_norm_lt a h eps heps
  refine ⟨N, fun m hm n hn => ?_⟩
  rcases le_total m n with hmn | hnm
  · simpa [dist_eq_norm, norm_sub_rev, ← na_sum_range_sub_eq_Ico a hmn,
      Nat.add_sub_cancel' hmn] using hN m hm (n - m)
  · simpa [dist_eq_norm, ← na_sum_range_sub_eq_Ico a hnm,
      Nat.add_sub_cancel' hnm] using hN n hn (m - n)

/-! ## 第六节：与 mathlib `IsUltrametricDist` 的接线（A1.5 的实际「接上」）

mathlib 4.14 **已提供**非阿基米德性的**官方类型类** `IsUltrametricDist`
（距离层面：`dist x z ≤ max (dist x y) (dist y z)`），
以及具体实例 **`instance : IsUltrametricDist ℚ_[p]`**
（`Mathlib/NumberTheory/Padics/PadicNumbers.lean:707`，目录名是 **`Padics`（复数）**）。

本文件的 `IsNonarchimedeanNorm` 是**范数层面**的自定义类
（`‖x + y‖ ≤ max ‖x‖ ‖y‖`）。本节把两者**接起来**：
由 `IsUltrametricDist K`（配合 `dist_eq_norm`）推出 `IsNonarchimedeanNorm K`，
从而本文件此前的**全部 ultrametric 结论**（强三角等号、有限和非阿基米德界、
开球既开又闭、级数收敛判据）**自动适用于任何 `IsUltrametricDist` 的赋范域**，
特别是 **`ℚ_[p]`**（无需本文件自行假设非阿基米德性）。

诚实标注（**降级为「单向接线」**）：
- 本节只证 **`IsUltrametricDist → IsNonarchimedeanNorm`**（下游最需要的方向：
  从 mathlib 的实例得到本文件理论的适用性）；
- **反向未做**：`IsNonarchimedeanNorm K → IsUltrametricDist K` 需要逐项翻译
  `dist x z = ‖x - z‖`，逻辑上同样直接，但本文件**未做**（留待后续）。
- 本节**不**注册全局 `instance`（避免与 `ℚ_[p]` 等既有实例的搜索冲突），
  以**具名定理**形式给出，调用方需显式 `haveI := na_of_isUltrametricDist K`。
- **未接线到 `ℚ_[p]`**：本文件**没有** `import Mathlib.NumberTheory.Padics.PadicNumbers`
  （避免拉长编译），故「`ℚ_[p]` 是本类实例」这一**具体实例化未做**；
  但 `IsUltrametricDist` 来自 `import Mathlib` 已覆盖的 `Ultra/Basic.lean`，
  故本定理**本身零额外依赖**。真实例化留待需要时单独一轮。 -/

/-- **由 `IsUltrametricDist` 得到 `IsNonarchimedeanNorm`**（范数层面的强三角不等式）。

证明：`dist x z ≤ max (dist x y) (dist y z)` 是 `IsUltrametricDist` 的定义；
取 `x = 0`、`y = -a`、`z = b - a`（即 `0 → -a → b - a`，距离分别是 `‖a‖` 与 `‖b‖`），
用 `dist_eq_norm` 把距离化为范数即得 `‖b‖ ≤ max ‖a‖ ‖b‖`；
对称地取路径 `0 → -b → a - b` 得 `‖a‖ ≤ max ‖a‖ ‖b‖`，两者合并给出
`‖a + b‖ ≤ max ‖a‖ ‖b‖`（再用 `a + b = (a+b) - 0` 与 `dist_eq_norm`）。

诚实标注：本定理**不需要** `K` 是域，`NormedRing`/`NormedAddCommGroup` 即可；
此处为与本文件的 `NormedField K` 语境一致而限定。 -/
theorem na_of_isUltrametricDist (K : Type*) [NormedField K] [IsUltrametricDist K] :
    IsNonarchimedeanNorm K where
  norm_add_le_max := fun x y => by
    -- 取路径 `-y → 0 → x`：`dist (-y) x ≤ max (dist (-y) 0) (dist 0 x)`
    have h1 : dist (-y) x ≤ max (dist (-y) (0 : K)) (dist (0 : K) x) :=
      IsUltrametricDist.dist_triangle_max (-y) 0 x
    -- 三个距离分别化简为范数：`‖x + y‖ ≤ max ‖y‖ ‖x‖`
    have h2 : dist (-y) x = ‖x + y‖ := by
      rw [dist_eq_norm, sub_eq_add_neg, ← neg_add_rev, norm_neg, add_comm]
    have h3 : dist (-y) (0 : K) = ‖y‖ := by
      rw [dist_eq_norm, sub_zero, norm_neg]
    have h4 : dist (0 : K) x = ‖x‖ := by
      rw [dist_eq_norm, zero_sub, norm_neg]
    rw [h2, h3, h4, max_comm] at h1
    exact h1

end Lattice
