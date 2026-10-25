import Mathlib
import Lattice.Lib.InfoTheory.RealKL
/-!
# LATTICE: 等号刻画统一库 —— 若干不等式的「取等 ⟹ 结构相等」公共引擎

本文件把全库反复用到的**等号情形**（"某不等式取等 ⟹ 结构常数/点相等"）收敛到唯一权威位置，
供 DPI 等号刻画（`RealDPIEquality`）、KL 零化（`RealKL.kl_zero_iff_support`）、
熵凹性等号（`RealEntropyConcavity.entropy_concavity_eq_iff`）、CE 零化
（`RealCrossEntropy.ce_eq_zero_iff_support`）等共用。

本文件建立：

  1. `one_sub_inv_lt_log_of_pos`：严格版 Gibbs 下界 `0 < x`、`x ≠ 1` ⟹ `1 − x⁻¹ < log x`
     （`Real.one_sub_inv_le_log_of_pos` 的严格化，由 `Real.log_lt_sub_one_of_pos` 在 `x⁻¹` 处取用）；
  2. `log_eq_one_sub_inv_iff`（**核心**）：`0 < x` ⟹ `log x = 1 − x⁻¹ ⟺ x = 1`；
  3. `mul_log_eq_sub_one_iff`（**核心**）：`0 < x` ⟹ `x·log x = x − 1 ⟺ x = 1`
     （信息论中 KL 逐项 Gibb 等号的规范化形式）；
  4. `sum_eq_zero_of_nonneg`：非负项有限和为零 ⟹ 每项为零
     （`Finset.sum_eq_zero_iff_of_nonneg` 的紧凑封装）；
  5. `sub_eq_mul_log_iff`（**核心**）：`0 < x`、`0 < y` ⟹ `x − y = x·log(x/y) ⟺ x = y`
     （逐项 KL 取等的等价形式，DPI/CE/KL 等号刻画的公共前置）；
  6. `sum_sq_shift`（工具恒等式）与 `cauchy_schwarz_eq_imp_proportional`（**核心**）：
     `(Σ aᵢbᵢ)² = (Σ aᵢ²)·(Σ bᵢ²)` 且 `Σ bᵢ² > 0` ⟹ 存在 c 使 `aᵢ = c·bᵢ`（有限实 CSR 等号 ⟹ 线性相关）。

**诚实边界**（本文件不证 / 不声称的）：

- `cauchy_schwarz_eq_imp_proportional` 只覆盖**有限实数列**且 `Σ bᵢ² > 0`；
  `Σ bᵢ² = 0`（即 `b = 0`）的退化情形下结论不成立（任意 `a` 都使等式成立），
  故作为显式假设排除，未声称退化版。
- 复内积空间 / 一般赋范空间 / 积分形式的 CSR 等号刻画未做（mathlib 4.14 无现成的
  等式情形 API，本文件只做有限和实版）。
- 本文件不依赖任何「未完成的等价文件」；log-sum 不等式自身的等号情形
  （`Σz·log A = 0 ⟹ A = 1`）在 `RealDPIEquality` 中承接本文件的 `log_eq_one_sub_inv_iff`。

模型无关：任意有限指标类型。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {ι : Type*}

/-! ## 1. 严格版 Gibbs 下界与 `log x = 1 − x⁻¹` 的等号刻画 -/

/-- **严格版 Gibbs 下界**：`0 < x`、`x ≠ 1` ⟹ `1 − x⁻¹ < log x`。

证明：在 `x⁻¹` 处用 `Real.log_lt_sub_one_of_pos` 得 `log(x⁻¹) < x⁻¹ − 1`，
再用 `Real.log_inv` 化为 `−log x < x⁻¹ − 1`。这是
`Real.one_sub_inv_le_log_of_pos`（非严格）的严格化，是全部等号刻画的引擎。 -/
lemma one_sub_inv_lt_log_of_pos {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    1 - x⁻¹ < Real.log x := by
  have hinv1 : x⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have h' := congrArg (fun t : ℝ => t⁻¹) h
    simpa using h'
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hx) hinv1
  rw [Real.log_inv] at h
  linarith

/-- **等号刻画一（`log` 的 Gibbs 形式）**：`0 < x` ⟹ `log x = 1 − x⁻¹ ⟺ x = 1`。

这是 `RealKL.kl_zero_iff_support`、DPI 等号刻画中「逐项 Gibb 取等 ⟹ 比值 = 1」
一步的权威封装。 -/
theorem log_eq_one_sub_inv_iff {x : ℝ} (hx : 0 < x) :
    Real.log x = 1 - x⁻¹ ↔ x = 1 := by
  constructor
  · intro h
    by_contra hx1
    have hlt := one_sub_inv_lt_log_of_pos hx hx1
    linarith
  · rintro rfl
    simp

/-- **等号刻画二（`x log x` 形式）**：`0 < x` ⟹ `x·log x = x − 1 ⟺ x = 1`。

证明：两边除以 `x > 0` 化为 `log x = 1 − x⁻¹`，再用 `log_eq_one_sub_inv_iff`。 -/
theorem mul_log_eq_sub_one_iff {x : ℝ} (hx : 0 < x) :
    x * Real.log x = x - 1 ↔ x = 1 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  constructor
  · intro h
    have h' : Real.log x = (x - 1) / x := by
      rw [eq_div_iff hx0, mul_comm]
      exact h
    have h'' : (x - 1) / x = 1 - x⁻¹ := by
      rw [sub_div, div_self hx0, one_div]
    have hfinal : Real.log x = 1 - x⁻¹ := by
      rw [h']
      exact h''
    exact (log_eq_one_sub_inv_iff hx).mp hfinal
  · rintro rfl
    simp

/-! ## 2. 非负项和为零 ⟹ 每项为零 -/

/-- **非负和为零**：`(∀ i, 0 ≤ f i)` 与 `Σ i, f i = 0` ⟹ `∀ i, f i = 0`。

`Finset.sum_eq_zero_iff_of_nonneg` 在 `Finset.univ` 上的紧凑封装，是逐项取等的标准桥梁。 -/
theorem sum_eq_zero_of_nonneg [Fintype ι] {f : ι → ℝ} (hnn : ∀ i, 0 ≤ f i)
    (h : ∑ i, f i = 0) : ∀ i, f i = 0 :=
  fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp h i (Finset.mem_univ i)

/-! ## 3. `x − y = x·log(x/y)` 的等号刻画 -/

/-- **等号刻画三（KL 逐项形式）**：`0 < x`、`0 < y` ⟹ `x − y = x·log(x/y) ⟺ x = y`。

证明：令 `t = x/y > 0`，两边除以 `y` 得 `t − 1 = t·log t`，用 `mul_log_eq_sub_one_iff` 得 `t = 1`，
再乘回 `y`。这是逐项 KL / 交叉熵取等的规范形式。 -/
theorem sub_eq_mul_log_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y = x * Real.log (x / y) ↔ x = y := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  set t : ℝ := x / y with ht
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos hx hy
  have hxt : x = t * y := by
    rw [ht, div_mul_cancel₀ x hy0]
  constructor
  · intro h
    have h' : t - 1 = t * Real.log t := by
      have h₁ : t * y - y = t * y * Real.log t := by
        rw [hxt] at h
        exact h
      have hdiv : (t * y - y) / y = (t * y * Real.log t) / y := by rw [h₁]
      have hL : (t * y - y) / y = t - 1 := by
        rw [show t * y - y = (t - 1) * y by ring, mul_div_cancel_right₀ _ hy0]
      have hR : (t * y * Real.log t) / y = t * Real.log t := by
        rw [show t * y * Real.log t = (t * Real.log t) * y by ring,
          mul_div_cancel_right₀ _ hy0]
      rw [hL, hR] at hdiv
      exact hdiv
    have ht1 : t = 1 := (mul_log_eq_sub_one_iff htpos).mp h'.symm
    calc x = t * y := hxt
      _ = 1 * y := by rw [ht1]
      _ = y := one_mul y
  · rintro rfl
    rw [ht, div_self hy0, Real.log_one, mul_zero, sub_self]

/-! ## 4. Cauchy–Schwarz 等号 ⟹ 线性相关（有限实版） -/

/-- **平移平方和恒等式**（有限实版，供 CSR 等号刻画）：
`Σ i, (aᵢB − bᵢC)² = B²·Σaᵢ² − 2BC·Σaᵢbᵢ + C²·Σbᵢ²`。

证明：逐项展开后用 `Finset.sum_add_distrib` / `Finset.sum_sub_distrib` 与
`Finset.sum_mul` / `Finset.mul_sum` 把常数从求和中提出。 -/
lemma sum_sq_shift [Fintype ι] (a b : ι → ℝ) (B C : ℝ) :
    ∑ i, (a i * B - b i * C) ^ 2
      = B ^ 2 * (∑ i, (a i) ^ 2) - 2 * B * C * (∑ i, a i * b i)
        + C ^ 2 * (∑ i, (b i) ^ 2) := by
  have hterm : ∀ i, (a i * B - b i * C) ^ 2
      = (a i) ^ 2 * B ^ 2 - (2 * B * C) * (a i * b i) + (b i) ^ 2 * C ^ 2 := by
    intro i
    ring
  calc ∑ i, (a i * B - b i * C) ^ 2
      = ∑ i, ((a i) ^ 2 * B ^ 2 - (2 * B * C) * (a i * b i) + (b i) ^ 2 * C ^ 2) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i, (a i) ^ 2 * B ^ 2) - (∑ i, (2 * B * C) * (a i * b i))
          + (∑ i, (b i) ^ 2 * C ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ((∑ i, (a i) ^ 2) * B ^ 2) - ((2 * B * C) * (∑ i, a i * b i))
          + ((∑ i, (b i) ^ 2) * C ^ 2) := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum]
    _ = B ^ 2 * (∑ i, (a i) ^ 2) - 2 * B * C * (∑ i, a i * b i)
          + C ^ 2 * (∑ i, (b i) ^ 2) := by
        ring

/-- **Cauchy–Schwarz 等号 ⟹ 线性相关（有限实版）**：
`(Σ aᵢbᵢ)² = (Σ aᵢ²)·(Σ bᵢ²)` 且 `Σ bᵢ² > 0` ⟹ `∃ c, ∀ i, aᵢ = c·bᵢ`。

证明：令 `B = Σbᵢ²`、`C = Σaᵢbᵢ`。由 `sum_sq_shift`，
`Σ (aᵢB − bᵢC)² = B²A − 2BC² + C²B = B·(BA − C²) = 0`（用 `C² = A·B`）。
逐项非负和为 0 ⟹ 每项 `aᵢB − bᵢC = 0`；`B > 0` 时除以 `B` 得 `aᵢ = (C/B)·bᵢ`。

**诚实标注**：`Σ bᵢ² = 0` 的退化情形结论不成立，故作为显式假设。 -/
theorem cauchy_schwarz_eq_imp_proportional [Fintype ι] (a b : ι → ℝ)
    (hb : 0 < ∑ i, (b i) ^ 2)
    (h : (∑ i, a i * b i) ^ 2 = (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2)) :
    ∃ c, ∀ i, a i = c * b i := by
  set B : ℝ := ∑ i, (b i) ^ 2 with hB
  set C : ℝ := ∑ i, a i * b i with hC
  set A : ℝ := ∑ i, (a i) ^ 2 with hA
  have hBpos : 0 < B := hB ▸ hb
  have hAB : C ^ 2 = A * B := by
    rw [hC, hA, hB] at h ⊢
    exact h
  have hzero : ∑ i, (a i * B - b i * C) ^ 2 = 0 := by
    rw [sum_sq_shift a b B C]
    nlinarith [hAB]
  have hall : ∀ i, (a i * B - b i * C) ^ 2 = 0 :=
    sum_eq_zero_of_nonneg (fun i => sq_nonneg _) hzero
  refine ⟨C / B, fun i => ?_⟩
  have hi : a i * B - b i * C = 0 := by
    have hnn : 0 ≤ a i * B - b i * C := by
      nlinarith [sq_nonneg (a i * B - b i * C), hall i]
    have hsq : (a i * B - b i * C) ^ 2 = 0 := hall i
    nlinarith [hsq, hnn]
  rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hBpos)]
  nlinarith [hi]

end Lattice
