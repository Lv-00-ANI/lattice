import Mathlib

/-!
# LATTICE: 复模与复向量 / 复矩阵范数

本文件建立复数范数（`Complex.normSq`）的初等工具，并给出复矩阵-向量范数界与复序列
Cauchy–Schwarz：

  1. `Complex.normSq_eq_abs_sq`：`normSq z = (Complex.abs z)^2`（回收 `Complex.sq_abs`）；
  2. `complexNormSq_nonneg`、`complexNormSq_zero_iff`（`normSq z = 0 ↔ z = 0`）、
     `complexNormSq_mul`（`normSq (z * w) = normSq z * normSq w`）；
  3. `normSq_add_le`：`normSq (z + w) ≤ 2 * (normSq z + normSq w)`
     （由实部虚部的 `(a+b)^2 ≤ 2(a²+b²)`）；
  4. `cvecNormSq`：复向量范数平方 `∑ i, normSq (v i)`；非负、零 iff、实标量齐次；
  5. **主定理 `cmat_vec_normSq_le`**（复矩阵-向量范数界）：
     `∑ i, normSq (∑ j, A i j * v j) ≤ (∑ i, ∑ j, normSq (A i j)) * (∑ j, normSq (v j))`；
  6. **`cseq_cauchy_schwarz`**（复序列 CS）：
     `normSq (∑ i, z i * star (w i)) ≤ cvecNormSq z * cvecNormSq w`
     （`star` 在 ℂ 上即复共轭 `conj`）。

证明路线（关键技巧，避免复杂的实部/虚部展开）：
对复数有限和先用**三角不等式** `‖∑ z_j‖ ≤ ∑ ‖z_j‖`，对 `∑ ‖z_j‖` 再用**实
Cauchy–Schwarz** `Finset.sum_mul_sq_le_sq_mul_sq`，最后用 `normSq_eq_norm_sq` 把
范数平方翻回 `normSq`。这给出**无松弛因子**的 sharp 复 CS。

诚实标注（无 sorry / axiom / admit）：
- 与 mathlib 已有名**不重名**：`Complex.*` 中已存在 `normSq_nonneg` / `normSq_mul` /
  `normSq_eq_zero`，本文件把它们以 `complexNormSq_*`（`Lattice` 命名空间）重新暴露，
  并新增 `Complex.normSq_eq_abs_sq`（mathlib 只有反向的 `Complex.sq_abs`）。
- 结论是**有限和**的范数界，不涉及复算子谱 / 奇异值理论，也不做紧算子近似。
- 复向量/矩阵为任意 `[Fintype]` 索引，不要求可计算。
-/

noncomputable section

namespace Lattice

/-! ## 一、复数范数基础 -/

/-- `Complex.normSq z = (Complex.abs z)^2`（mathlib 已有反向的 `Complex.sq_abs`）。 -/
theorem Complex.normSq_eq_abs_sq (z : ℂ) : Complex.normSq z = Complex.abs z ^ 2 :=
  (Complex.sq_abs z).symm

theorem complexNormSq_nonneg (z : ℂ) : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z

theorem complexNormSq_zero_iff (z : ℂ) : Complex.normSq z = 0 ↔ z = 0 := Complex.normSq_eq_zero

theorem complexNormSq_mul (z w : ℂ) :
    Complex.normSq (z * w) = Complex.normSq z * Complex.normSq w :=
  Complex.normSq_mul z w

/-- 平方和界：`normSq (z + w) ≤ 2 * (normSq z + normSq w)`。 -/
theorem normSq_add_le (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply,
    Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]

/-! ## 二、复向量范数平方 -/

/-- 复向量的范数平方：`∑ i, normSq (v i)`。 -/
def cvecNormSq {n : Type*} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

theorem cvecNormSq_nonneg {n : Type*} [Fintype n] (v : n → ℂ) : 0 ≤ cvecNormSq v :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem cvecNormSq_zero_iff {n : Type*} [Fintype n] (v : n → ℂ) :
    cvecNormSq v = 0 ↔ ∀ i, v i = 0 := by
  unfold cvecNormSq
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)]
  constructor
  · intro h i
    exact Complex.normSq_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _
    exact Complex.normSq_eq_zero.mpr (h i)

/-- 实标量齐次：`cvecNormSq (c • v) = c^2 * cvecNormSq v`（`c : ℝ`）。 -/
theorem cvecNormSq_smul {n : Type*} [Fintype n] (c : ℝ) (v : n → ℂ) :
    cvecNormSq (c • v) = c ^ 2 * cvecNormSq v := by
  unfold cvecNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (c • v) i = (c : ℂ) * v i := by
    rw [Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    rfl
  rw [hs, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-! ## 三、复矩阵-向量范数界（主定理） -/

/-- **复矩阵-向量范数界（sharp）**：
`∑ i, normSq (∑ j, A i j * v j) ≤ (∑ i, ∑ j, normSq (A i j)) * (∑ j, normSq (v j))`。

逐行证明：三角不等式 + 实 Cauchy–Schwarz。 -/
theorem cmat_vec_normSq_le {m n : Type*} [Fintype m] [Fintype n]
    (A : m → n → ℂ) (v : n → ℂ) :
    ∑ i, Complex.normSq (∑ j, A i j * v j) ≤
      (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (v j)) := by
  have hrow : ∀ i, Complex.normSq (∑ j, A i j * v j)
      ≤ (∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (v j)) := by
    intro i
    have htri : ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
      calc ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le Finset.univ _
        _ = ∑ j, ‖A i j‖ * ‖v j‖ := by simp [norm_mul]
    have hcs : (∑ j, ‖A i j‖ * ‖v j‖) ^ 2
        ≤ (∑ j, ‖A i j‖ ^ 2) * (∑ j, ‖v j‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖v j‖)
    have hsq : ‖∑ j, A i j * v j‖ ^ 2
        ≤ (∑ j, ‖A i j‖ ^ 2) * (∑ j, ‖v j‖ ^ 2) :=
      le_trans (pow_le_pow_left₀ (norm_nonneg _) htri 2) hcs
    simpa [Complex.normSq_eq_norm_sq] using hsq
  calc ∑ i, Complex.normSq (∑ j, A i j * v j)
      ≤ ∑ i, (∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (v j)) :=
        Finset.sum_le_sum (fun i _ => hrow i)
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (v j)) := by
        rw [Finset.sum_mul]

/-! ## 四、复序列 Cauchy–Schwarz -/

/-- **复序列 Cauchy–Schwarz**：
`normSq (∑ i, z i * star (w i)) ≤ cvecNormSq z * cvecNormSq w`。
（`star` 在 ℂ 上即复共轭。） -/
theorem cseq_cauchy_schwarz {n : Type*} [Fintype n] (z w : n → ℂ) :
    Complex.normSq (∑ i, z i * star (w i)) ≤ cvecNormSq z * cvecNormSq w := by
  have htri : ‖∑ i, z i * star (w i)‖ ≤ ∑ i, ‖z i‖ * ‖w i‖ := by
    calc ‖∑ i, z i * star (w i)‖ ≤ ∑ i, ‖z i * star (w i)‖ := norm_sum_le Finset.univ _
      _ = ∑ i, ‖z i‖ * ‖w i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, norm_star]
  have hcs : (∑ i, ‖z i‖ * ‖w i‖) ^ 2 ≤ (∑ i, ‖z i‖ ^ 2) * (∑ i, ‖w i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖z i‖) (fun i => ‖w i‖)
  have hsq : ‖∑ i, z i * star (w i)‖ ^ 2 ≤ (∑ i, ‖z i‖ ^ 2) * (∑ i, ‖w i‖ ^ 2) :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) htri 2) hcs
  simpa [Complex.normSq_eq_norm_sq, cvecNormSq] using hsq

end Lattice
