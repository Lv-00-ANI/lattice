import Mathlib
import Lattice.Lib.Architectures.RealTensorNorm
/-!
# LATTICE: 低秩近似（秩-1 外积结构与代数界）

本文件在 `RealTensorNorm` 的 Frobenius 范数基础上给出**低秩参数化**的代数结构：

  1. `outer u v`：秩-1 外积 `(i,j) ↦ u i * v j`；`vecNorm`：向量欧氏范数；
  2. `outer_rank_one`（**外积范数 = 两向量范数之积**）：`frob (outer u v) = vecNorm u * vecNorm v`
     （中间用 `frobSq_outer` 把双重平方和分解为两个向量平方和之积）；
  3. `row_sum_sq_le`：`(∑ k, a k)^2 ≤ r * ∑ k, a k^2`（对 `Fin r` 用 Cauchy–Schwarz + 全 1 向量）；
  4. **`low_rank_reparam`**：`frobSq (∑_{k<r} outer (u k) (v k)) ≤ r * ∑_k (vecNorm (u k) * vecNorm (v k))^2`
     （逐元素用 3，再求和换序）——低秩参数化的 Frobenius 范数界；
  5. `frob_add_le`：Frobenius 范数的三角不等式 `frob (A + B) ≤ frob A + frob B`
     （用矩阵内积 Cauchy–Schwarz + 平方展开）；
  6. **`low_rank_error_budget`**：`frob L ≤ B ⟹ frob (L + E) ≤ B + frob E`
     （先加三角不等式，再用预算假设）。

诚实标注（无 sorry / axiom / admit）：
- **Eckart–Young–Mirsky 最优性（SVD 最优低秩逼近）既未证也未做**：本文件只给
  **代数界与参数化结构**，不构造 SVD，不声称截断最优。
- `low_rank_reparam` 的界含因子 `r`（维度），不是 sharp 常数；sharp 版本需要
  最优 `u`、`v` 的选择（谱理论）。
- 索引类型为任意 `[Fintype]`，秩 `r` 为 `Fin r`。
- 复用了 `RealTensorNorm` 的 `frobSq` / `frob` / `frobSq_inner_sq_le`（只读，不修改）。
-/

noncomputable section

namespace Lattice

variable {m n : Type*} [Fintype m] [Fintype n]

/-! ## 一、秩-1 外积与向量范数 -/

/-- 秩-1 外积：`(outer u v) i j = u i * v j`。 -/
def outer (u : m → ℝ) (v : n → ℝ) : m → n → ℝ := fun i j => u i * v j

/-- 向量欧氏范数：`sqrt (∑ i, u i ^ 2)`。 -/
def vecNorm {m : Type*} [Fintype m] (u : m → ℝ) : ℝ := Real.sqrt (∑ i, u i ^ 2)

theorem vecNorm_nonneg {m : Type*} [Fintype m] (u : m → ℝ) : 0 ≤ vecNorm u :=
  Real.sqrt_nonneg _

theorem vecNorm_sq {m : Type*} [Fintype m] (u : m → ℝ) :
    vecNorm u ^ 2 = ∑ i, u i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (u i)))

/-- 外积的 Frobenius 范数平方 = 两个向量平方范数之积。 -/
theorem frobSq_outer (u : m → ℝ) (v : n → ℝ) :
    frobSq (outer u v) = (∑ i, u i ^ 2) * (∑ j, v j ^ 2) := by
  unfold frobSq outer
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **秩-1 外积的 Frobenius 范数 = 两向量范数之积**。 -/
theorem outer_rank_one (u : m → ℝ) (v : n → ℝ) :
    frob (outer u v) = vecNorm u * vecNorm v := by
  unfold frob vecNorm
  rw [frobSq_outer,
    Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (u i)))]

/-! ## 二、多项式低秩参数化的范数界 -/

/-- 有限和的三重换序：`∑ i ∑ j ∑ k g i j k = ∑ k ∑ i ∑ j g i j k`。 -/
theorem sum_swap_three {q : ℕ} (g : m → n → Fin q → ℝ) :
    (∑ i, ∑ j, ∑ k, g i j k) = ∑ k, ∑ i, ∑ j, g i j k := by
  calc ∑ i, ∑ j, ∑ k, g i j k
      = ∑ i, ∑ k, ∑ j, g i j k := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, g i j k := by rw [Finset.sum_comm]

/-- Cauchy–Schwarz（全 1 权重）：`(∑ k, a k)^2 ≤ r * ∑ k, a k^2`。 -/
theorem row_sum_sq_le {q : ℕ} (a : Fin q → ℝ) :
    (∑ k, a k) ^ 2 ≤ (q : ℝ) * ∑ k, a k ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q)) a (fun _ => (1 : ℝ))
  have hcard : (∑ _k : Fin q, (1 : ℝ) ^ 2) = (q : ℝ) := by simp
  simpa [hcard, one_mul, mul_comm] using h

/-- 低秩参数化：`(∑_{k<r} outer (u k) (v k)) i j = ∑ k, u k i * v k j`。 -/
def lowRankSum {r : ℕ} (u : Fin r → m → ℝ) (v : Fin r → n → ℝ) : m → n → ℝ :=
  fun i j => ∑ k, u k i * v k j

/-- **低秩参数化的 Frobenius 范数界**：
`frobSq (∑_{k<r} outer (u k) (v k)) ≤ r * ∑ k (vecNorm (u k) * vecNorm (v k))^2`。 -/
theorem low_rank_reparam {r : ℕ} (u : Fin r → m → ℝ) (v : Fin r → n → ℝ) :
    frobSq (lowRankSum u v) ≤ (r : ℝ) * ∑ k, (vecNorm (u k) * vecNorm (v k)) ^ 2 := by
  have hrow : ∀ i j, (∑ k, u k i * v k j) ^ 2 ≤ (r : ℝ) * ∑ k, (u k i * v k j) ^ 2 :=
    fun i j => row_sum_sq_le (fun k => u k i * v k j)
  calc frobSq (lowRankSum u v)
      = ∑ i, ∑ j, (∑ k, u k i * v k j) ^ 2 := rfl
    _ ≤ ∑ i, ∑ j, (r : ℝ) * ∑ k, (u k i * v k j) ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hrow i j))
    _ = (r : ℝ) * ∑ i, ∑ j, ∑ k, (u k i * v k j) ^ 2 := by
        simp only [Finset.mul_sum]
    _ = (r : ℝ) * ∑ k, frobSq (outer (u k) (v k)) := by
        congr 1
        exact sum_swap_three (fun i j k => (u k i * v k j) ^ 2)
    _ = (r : ℝ) * ∑ k, (vecNorm (u k) * vecNorm (v k)) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        calc frobSq (outer (u k) (v k))
            = (∑ i, u k i ^ 2) * (∑ j, v k j ^ 2) := frobSq_outer (u k) (v k)
          _ = (vecNorm (u k) * vecNorm (v k)) ^ 2 := by
              rw [mul_pow, vecNorm_sq, vecNorm_sq]

/-- 逐项矩阵和上界（矩阵因子分解形式）：`∑∑ (∑_k u i k * v k j)^2 ≤ r * ∑∑∑ ...`。 -/
theorem factorized_bound {r : ℕ} (u : m → Fin r → ℝ) (v : Fin r → n → ℝ) :
    (∑ i, ∑ j, (∑ k, u i k * v k j) ^ 2)
      ≤ (r : ℝ) * ∑ i, ∑ j, ∑ k, (u i k * v k j) ^ 2 := by
  calc ∑ i, ∑ j, (∑ k, u i k * v k j) ^ 2
      ≤ ∑ i, ∑ j, (r : ℝ) * ∑ k, (u i k * v k j) ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
          (fun j _ => row_sum_sq_le (fun k => u i k * v k j)))
    _ = (r : ℝ) * ∑ i, ∑ j, ∑ k, (u i k * v k j) ^ 2 := by
        simp only [Finset.mul_sum]

/-! ## 三、Frobenius 三角不等式与误差预算 -/

/-- **Frobenius 范数三角不等式**：`frob (A + B) ≤ frob A + frob B`。 -/
theorem frob_add_le (A B : m → n → ℝ) : frob (A + B) ≤ frob A + frob B := by
  have hA := frobSq_nonneg A
  have hB := frobSq_nonneg B
  have hAB : (∑ i, ∑ j, A i j * B i j) ≤ frob A * frob B := by
    have h1 : (∑ i, ∑ j, A i j * B i j) ^ 2 ≤ (frob A * frob B) ^ 2 := by
      have hsq := frobSq_inner_sq_le A B
      have hff : frobSq A * frobSq B = (frob A * frob B) ^ 2 := by
        show frobSq A * frobSq B
          = (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) ^ 2
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
      linarith
    have h2 : |∑ i, ∑ j, A i j * B i j| ≤ frob A * frob B := by
      have habs := sq_le_sq.mp h1
      rwa [abs_of_nonneg (mul_nonneg (frob_nonneg A) (frob_nonneg B))] at habs
    exact le_trans (le_abs_self _) h2
  have hexp : frobSq (A + B)
      = frobSq A + 2 * (∑ i, ∑ j, A i j * B i j) + frobSq B := by
    have h1 : ∀ i, (∑ j, (A i j + B i j) ^ 2)
        = (∑ j, A i j ^ 2) + 2 * (∑ j, A i j * B i j) + (∑ j, B i j ^ 2) := by
      intro i
      have hpt : ∀ j, (A i j + B i j) ^ 2
          = A i j ^ 2 + 2 * (A i j * B i j) + B i j ^ 2 := fun j => by ring
      simp only [hpt]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    unfold frobSq
    simp only [Pi.add_apply, h1]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsq : frobSq (A + B) ≤ (frob A + frob B) ^ 2 := by
    rw [hexp]
    have hfA : frobSq A = (frob A) ^ 2 := (Real.sq_sqrt hA).symm
    have hfB : frobSq B = (frob B) ^ 2 := (Real.sq_sqrt hB).symm
    rw [hfA, hfB]
    nlinarith [hAB, frob_nonneg A, frob_nonneg B]
  calc frob (A + B) = Real.sqrt (frobSq (A + B)) := rfl
    _ ≤ Real.sqrt ((frob A + frob B) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = frob A + frob B := Real.sqrt_sq (add_nonneg (frob_nonneg A) (frob_nonneg B))

/-- **低秩近似的误差-预算**：若低秩部分 `L` 的 Frobenius 范数不超过预算 `B`，
则整体 `L + E` 的 Frobenius 范数不超过 `B + frob E`。 -/
theorem low_rank_error_budget {L Epart : m → n → ℝ} {B : ℝ} (hL : frob L ≤ B) :
    frob (L + Epart) ≤ B + frob Epart :=
  le_trans (frob_add_le L Epart) (add_le_add_right hL (frob Epart))

end Lattice
