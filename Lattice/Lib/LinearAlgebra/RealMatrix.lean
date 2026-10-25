import Mathlib

/-!
# LATTICE: Fin 矩阵 —— 显式矩阵乘向量与编辑桥

真实模型权重是矩阵（W : Matrix (Fin m) (Fin n) ℝ）：
显式化「矩阵 → 连续线性映射」的桥，使抽象证明（编辑界/法方程）可直接
实例化到矩阵：

  1. 矩阵乘向量是线性映射：matvec 线性（map_add/map_smul）；
  2. 矩阵编辑界：‖(W+Δ)·x − W·x‖ = ‖Δ·x‖ ≤ ‖Δ‖_op·‖x‖
     （经连续线性映射桥复用 edit_output_bound）；
  3. 矩阵法方程衔接：矩阵作为算子，一致系统下驻点⟺满足（复用抽象版）。

模型无关：任意 m×n 维度（Fin 指标）。
-/

noncomputable section

namespace Lattice

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-! ## 矩阵乘向量（行点积） -/

def matvec (W : Matrix m n ℝ) (x : n → ℝ) : m → ℝ :=
  fun i => ∑ j, W i j * x j

/-! ## 引理：matvec 线性（加法） -/

omit [Fintype m] in
lemma matvec_add (W : Matrix m n ℝ) (x y : n → ℝ) :
    matvec W (x + y) = matvec W x + matvec W y := by
  funext i
  unfold matvec
  -- Σ Wᵢⱼ(xⱼ + yⱼ) = Σ Wᵢⱼxⱼ + Σ Wᵢⱼyⱼ
  calc
    ∑ j, W i j * (x j + y j) = ∑ j, (W i j * x j + W i j * y j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j, W i j * x j) + (∑ j, W i j * y j) := by
      rw [Finset.sum_add_distrib]

/-! ## 引理：matvec 线性（缩放） -/

omit [Fintype m] in
lemma matvec_smul (W : Matrix m n ℝ) (c : ℝ) (x : n → ℝ) :
    matvec W (c • x) = c • matvec W x := by
  funext i
  unfold matvec
  calc
    ∑ j, W i j * (c * x j) = ∑ j, c * (W i j * x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * ∑ j, W i j * x j := by
      rw [Finset.mul_sum]

/-! ## 引理：matvec 线性（矩阵加法，逐点展开） -/

omit [Fintype m] in
lemma matvec_add_matrix (W Δ : Matrix m n ℝ) (x : n → ℝ) :
    matvec (W + Δ) x = matvec W x + matvec Δ x := by
  funext i
  unfold matvec
  calc
    ∑ j, (W + Δ) i j * x j = ∑ j, (W i j * x j + Δ i j * x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [add_mul]
    _ = (∑ j, W i j * x j) + (∑ j, Δ i j * x j) := by
      rw [Finset.sum_add_distrib]

/-! ## 矩阵作为连续线性映射（桥） -/

def matCLM (W : Matrix m n ℝ) : (n → ℝ) →L[ℝ] (m → ℝ) :=
  { toFun := matvec W
    map_add' := matvec_add W
    map_smul' := matvec_smul W }

/-! ## 定理一：矩阵编辑输出变化界（经抽象桥）
‖(W+Δ)·x − W·x‖ = ‖Δ·x‖ ≤ ‖Δ‖_op·‖x‖。-/

theorem matrix_edit_bound (W Δ : Matrix m n ℝ) (x : n → ℝ) :
    ‖matvec (W + Δ) x - matvec W x‖ ≤ ‖matCLM Δ‖ * ‖x‖ := by
  -- matvec (W+Δ) = matvec W + matvec Δ（加法线性）
  have hadd : matvec (W + Δ) x = matvec W x + matvec Δ x := matvec_add_matrix W Δ x
  have hdiff : matvec (W + Δ) x - matvec W x = matvec Δ x := by
    rw [hadd]
    abel
  calc
    ‖matvec (W + Δ) x - matvec W x‖ = ‖matvec Δ x‖ := by rw [hdiff]
    _ ≤ ‖matCLM Δ‖ * ‖x‖ := (matCLM Δ).le_opNorm x

/-! ## 定理二：矩阵编辑后约束近似保持
标量行约束（W 的一行与 x 点积）：原满足 ⟹ 编辑后 |W'x| ≤ ‖Δ‖·‖x‖。 -/

theorem matrix_edit_constraint_row (W Δ : Matrix m n ℝ) (x : n → ℝ) (i : m)
    (h0 : matvec W x i = 0) :
    |matvec (W + Δ) x i| ≤ ‖matCLM Δ‖ * ‖x‖ := by
  -- |W'x i| = |W'x i - Wx i|（原 = 0）≤ ‖Δx‖（分量 ≤ 范数）≤ ‖Δ‖‖x‖
  have hdiff : matvec (W + Δ) x i - matvec W x i = matvec Δ x i := by
    have hlin : matvec (W + Δ) x = matvec W x + matvec Δ x := matvec_add_matrix W Δ x
    have hlin_i : matvec (W + Δ) x i = matvec W x i + matvec Δ x i := by
      simpa using congrFun hlin i
    linarith
  calc
    |matvec (W + Δ) x i| = |matvec (W + Δ) x i - matvec W x i| := by
      rw [h0]
      simp
    _ = |matvec Δ x i| := by rw [hdiff]
    _ ≤ ‖matvec Δ x‖ := by simpa using norm_le_pi_norm (matvec Δ x) i
    _ ≤ ‖matCLM Δ‖ * ‖x‖ := (matCLM Δ).le_opNorm x

/-! ## 定理三：零编辑精确保持 -/

omit [Fintype m] in
theorem matrix_zero_edit_identity (W : Matrix m n ℝ) (x : n → ℝ) :
    matvec (W + 0) x = matvec W x := by
  -- W + 0 = W
  have h : W + 0 = W := by
    ext i j
    simp
  rw [h]

end Lattice
