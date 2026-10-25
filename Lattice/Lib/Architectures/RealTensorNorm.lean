import Mathlib

/-!
# LATTICE: 张量 / 矩阵算子范数（初等，Frobenius 路线）

本文件对矩阵 `A : m → n → ℝ`（`[Fintype m] [Fintype n]`）建立初等的范数工具，
给出「矩阵算子范数 ≤ Frobenius 范数」的完整初等证明：

  1. `frobSq` / `frob`：Frobenius 范数平方（`∑ i, ∑ j, A i j ^ 2`）与范数（开方）；
  2. `frobSq_nonneg`、`frob_nonneg`、`frobSq_zero_iff`（`frobSq A = 0 ↔ A = 0`）；
  3. `frobSq_smul`、`frob_smul`：数乘齐次（`frob (c • A) = |c| * frob A`）；
  4. `frobSq_mono`：逐元素平方受控 ⟹ Frobenius 范数平方单调；
     `frobSq_le_card_mul_sq`：逐元素平方 ≤ M ⟹ `frobSq A ≤ card m * card n * M`（`M ≥ 0`）；
  5. `frobSq_inner_sq_le`：**Cauchy–Schwarz 矩阵内积版**
     `(∑ i, ∑ j, A i j * B i j)^2 ≤ frobSq A * frobSq B`（把 `m × n` 视为单一索引后一次 CS）；
  6. `frob_row_sq_le` / `frob_vec_sq_le`：逐行 CS 与向量版平方界
     `∑ i, (∑ j, A i j * x j)^2 ≤ frobSq A * ∑ j, x j^2`；
  7. **主定理 `frob_operator_norm_le`**：
     `Real.sqrt (∑ i, (∑ j, A i j * x j)^2) ≤ frob A * Real.sqrt (∑ j, x j^2)`，
     即欧氏 2-范数下矩阵算子范数不超过 Frobenius 范数。

诚实标注（无 sorry / axiom / admit）：
- 结论是**初等上界**（算子范数 ≤ Frobenius 范数），不是 sharp 常数；
  本文件不做奇异值/谱理论，也不证明 Frobenius 范数与谱范数的最优关系
  （sqrt(rank) 倍的 sharp 界）。
- `m`、`n` 为任意有限类型（`[Fintype]`），不要求可计算/`DecidableEq`。
- 全部定理只依赖 `Mathlib` 的 `Finset.sum_mul_sq_le_sq_mul_sq`（实 Cauchy–Schwarz）。
-/

noncomputable section

namespace Lattice

variable {m n : Type*} [Fintype m] [Fintype n]

/-! ## 一、Frobenius 范数 -/

/-- Frobenius 范数平方：`∑ i, ∑ j, A i j ^ 2`。 -/
def frobSq (A : m → n → ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- Frobenius 范数：`sqrt (frobSq A)`。 -/
def frob (A : m → n → ℝ) : ℝ := Real.sqrt (frobSq A)

theorem frobSq_nonneg (A : m → n → ℝ) : 0 ≤ frobSq A := by
  unfold frobSq
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem frob_nonneg (A : m → n → ℝ) : 0 ≤ frob A := Real.sqrt_nonneg _

/-- `frobSq A = 0` 当且仅当矩阵全零。 -/
theorem frobSq_zero_iff (A : m → n → ℝ) : frobSq A = 0 ↔ ∀ i j, A i j = 0 := by
  unfold frobSq
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  constructor
  · intro h i j
    have h1 : (∑ j : n, A i j ^ 2) = 0 := h i (Finset.mem_univ i)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at h1
    exact sq_eq_zero_iff.mp (h1 j (Finset.mem_univ j))
  · intro h i _
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
    intro j _
    exact sq_eq_zero_iff.mpr (h i j)

/-! ## 二、数乘齐次 -/

theorem frobSq_smul (c : ℝ) (A : m → n → ℝ) : frobSq (c • A) = c ^ 2 * frobSq A := by
  unfold frobSq
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem frob_smul (c : ℝ) (A : m → n → ℝ) : frob (c • A) = |c| * frob A := by
  unfold frob
  rw [frobSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-! ## 三、逐元素受控单调 -/

theorem frobSq_mono {A B : m → n → ℝ} (h : ∀ i j, A i j ^ 2 ≤ B i j ^ 2) :
    frobSq A ≤ frobSq B := by
  unfold frobSq
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h i j))

theorem frobSq_le_card_mul_sq {A : m → n → ℝ} {M : ℝ} (_hM : 0 ≤ M)
    (h : ∀ i j, A i j ^ 2 ≤ M) :
    frobSq A ≤ (Fintype.card m * Fintype.card n : ℝ) * M := by
  unfold frobSq
  calc ∑ i, ∑ j, A i j ^ 2 ≤ ∑ _i : m, ∑ _j : n, M :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h i j))
    _ = (Fintype.card m * Fintype.card n : ℝ) * M := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
        ring

/-! ## 四、Cauchy–Schwarz（矩阵内积版与逐行版） -/

/-- **矩阵内积的 Cauchy–Schwarz**：`(∑ i, ∑ j, A i j * B i j)^2 ≤ frobSq A * frobSq B`。
证明：把 `m × n` 视为单一有限索引（`Fintype.sum_prod_type`），对乘积型用一次实 CS。 -/
theorem frobSq_inner_sq_le (A B : m → n → ℝ) :
    (∑ i, ∑ j, A i j * B i j) ^ 2 ≤ frobSq A * frobSq B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n))
    (fun p : m × n => A p.1 p.2) (fun p : m × n => B p.1 p.2)
  rw [Fintype.sum_prod_type (fun p : m × n => A p.1 p.2 * B p.1 p.2),
      Fintype.sum_prod_type (fun p : m × n => A p.1 p.2 ^ 2),
      Fintype.sum_prod_type (fun p : m × n => B p.1 p.2 ^ 2)] at h
  simpa [frobSq] using h

omit [Fintype m] in
/-- 逐行 Cauchy–Schwarz：`(∑ j, A i j * x j)^2 ≤ (∑ j, A i j ^ 2) * (∑ j, x j ^ 2)`。 -/
theorem frob_row_sq_le (A : m → n → ℝ) (x : n → ℝ) (i : m) :
    (∑ j, A i j * x j) ^ 2 ≤ (∑ j, A i j ^ 2) * (∑ j, x j ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x j)

/-- 向量版平方界：`∑ i, (∑ j, A i j * x j)^2 ≤ frobSq A * ∑ j, x j^2`。 -/
theorem frob_vec_sq_le (A : m → n → ℝ) (x : n → ℝ) :
    ∑ i, (∑ j, A i j * x j) ^ 2 ≤ frobSq A * (∑ j, x j ^ 2) := by
  calc ∑ i, (∑ j, A i j * x j) ^ 2
      ≤ ∑ i, (∑ j, A i j ^ 2) * (∑ j, x j ^ 2) :=
        Finset.sum_le_sum (fun i _ => frob_row_sq_le A x i)
    _ = (∑ i, ∑ j, A i j ^ 2) * (∑ j, x j ^ 2) := by rw [Finset.sum_mul]
    _ = frobSq A * (∑ j, x j ^ 2) := rfl

/-! ## 五、主定理：算子范数 ≤ Frobenius 范数 -/

/-- **算子范数 ≤ Frobenius 范数**：
`sqrt (∑ i, (∑ j, A i j * x j)^2) ≤ frob A * sqrt (∑ j, x j^2)`。 -/
theorem frob_operator_norm_le (A : m → n → ℝ) (x : n → ℝ) :
    Real.sqrt (∑ i, (∑ j, A i j * x j) ^ 2) ≤ frob A * Real.sqrt (∑ j, x j ^ 2) := by
  calc Real.sqrt (∑ i, (∑ j, A i j * x j) ^ 2)
      ≤ Real.sqrt (frobSq A * (∑ j, x j ^ 2)) := Real.sqrt_le_sqrt (frob_vec_sq_le A x)
    _ = frob A * Real.sqrt (∑ j, x j ^ 2) := by
        rw [frob, Real.sqrt_mul (frobSq_nonneg A)]

end Lattice
