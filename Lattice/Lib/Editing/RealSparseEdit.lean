import Lattice.Lib.LinearAlgebra.RealSparsity
import Mathlib

/-!
# LATTICE: 稀疏编辑 —— 只改支撑集 S 上分量的编辑误差界

权重编辑线（ROME/MEMIT/LoRA 之后的稀疏编辑）：编辑**只在支撑集 S**
（|S| ≤ s 个坐标）上改变权重，其余分量严格不动。本文件把
RealSparsity 的剪枝误差框架**复用**为「稀疏编辑」框架：

    A' = sparseEdit A B S    （S 上取目标 B，S 外取原 A）
    ΔW = A' − A = sparseDelta A B S   （S 上 = B − A，S 外 = 0）

即稀疏编辑的误差就是「被改部分」的幅度集合，与剪枝误差矩阵
（pruneError）逐点相同（`sparseDelta_eq_pruneError`），因此
RealSparsity.prune_magnitude_bound 的整条证明路线可直接回收。

定理清单：
  1. `sparseEdit` / `sparseDelta`（def）：支撑集 S 上的稀疏编辑与其误差矩阵；
  2. `sparse_edit_frobenius_bound`（核心）：S.card ≤ s 且单坐标修改幅度
     |Bᵢⱼ − Aᵢⱼ| ≤ θ（θ ≥ 0）⟹ ‖ΔW‖_F ≤ √s·θ
     （精确复用 prune_magnitude_bound：`sparseDelta = pruneError (B − A) S`）；
  3. `sparse_edit_op_bound`：算子误差 ‖matCLME ΔW‖ ≤ √s·θ（opNorm ≤ Frobenius）；
  4. `sparse_edit_output_bound`：逐点输出误差 ‖ΔW·x‖ ≤ √s·θ·‖x‖
     （衔接 RealMatrixNorm.frobenius_bound）；
  5. `sparse_edit_constraint_drift`（核心）：稀疏编辑后约束输出的漂移
     ‖A'·x − A·x‖ ≤ √s·θ·‖x‖（把编辑误差代入约束/损失界，
     经 `matvecE_sub` 化归到 (4)）；
  6. `sparse_edit_zero_outside` / `sparse_delta_zero_outside`：支撑集外
     权重逐点不变、误差逐点为零。

诚实假设（全部显式）：支撑集大小 |S| ≤ s；单点修改幅度 |Bᵢⱼ − Aᵢⱼ| ≤ θ；
θ ≥ 0。模型无关：任意 m×n 维度（Fin 指标）。无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {m n : ℕ}

/-! ## 稀疏编辑与其误差矩阵 -/

/-- 稀疏编辑 A'：支撑集 S（行列坐标对）上取目标 B，S 外保持原 A 不变。 -/
def sparseEdit (A B : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if (i, j) ∈ S then B i j else A i j

/-- 稀疏编辑误差矩阵 ΔW = A' − A：S 上为 B − A，S 外为 0
（即「编辑误差 = 被改部分」）。 -/
def sparseDelta (A B : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if (i, j) ∈ S then B i j - A i j else 0

/-! ## 基本恒等式与支撑集性质 -/

/-- A' − A = ΔW（逐点）。 -/
lemma sparseEdit_sub_eq_delta (A B : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    sparseEdit A B S - A = sparseDelta A B S := by
  ext i j
  by_cases h : (i, j) ∈ S <;> simp [sparseEdit, sparseDelta, Matrix.sub_apply, h]

/-- 稀疏编辑误差 = 剪枝误差矩阵（B − A 在 S 上的限制）：
`sparseDelta A B S = pruneError (B − A) S`，从而 RealSparsity 的全部误差界可回收。 -/
lemma sparseDelta_eq_pruneError (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) :
    sparseDelta A B S = pruneError (B - A) S := by
  ext i j
  by_cases h : (i, j) ∈ S <;> simp [sparseDelta, pruneError, Matrix.sub_apply, h]

/-- 支撑集外权重逐点不变（稀疏编辑只影响 S）。 -/
lemma sparse_edit_zero_outside (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) :
    ∀ i j, (i, j) ∉ S → sparseEdit A B S i j = A i j := by
  intro i j hij
  simp [sparseEdit, hij]

/-- 支撑集外误差逐点为零。 -/
lemma sparse_delta_zero_outside (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) :
    ∀ i j, (i, j) ∉ S → sparseDelta A B S i j = 0 := by
  intro i j hij
  simp [sparseDelta, hij]

/-! ## 定理一（核心）：稀疏编辑的 Frobenius 误差界 ‖ΔW‖_F ≤ √s·θ -/

theorem sparse_edit_frobenius_bound (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) (s : ℕ) (θ : ℝ)
    (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |B p.1 p.2 - A p.1 p.2| ≤ θ) :
    frobeniusNorm (sparseDelta A B S) ≤ Real.sqrt (s : ℝ) * θ := by
  rw [sparseDelta_eq_pruneError]
  exact prune_magnitude_bound (B - A) S s θ hS hθ (fun p hp => by
    simpa [Matrix.sub_apply] using hA p hp)

/-- Frobenius 误差（直接形式）：‖A' − A‖_F ≤ √s·θ。 -/
theorem sparse_edit_delta_frobenius_bound (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) (s : ℕ) (θ : ℝ)
    (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |B p.1 p.2 - A p.1 p.2| ≤ θ) :
    frobeniusNorm (sparseEdit A B S - A) ≤ Real.sqrt (s : ℝ) * θ := by
  rw [sparseEdit_sub_eq_delta]
  exact sparse_edit_frobenius_bound A B S s θ hS hθ hA

/-! ## 定理二：算子误差界（opNorm ≤ Frobenius） -/

theorem sparse_edit_op_bound (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) (s : ℕ) (θ : ℝ)
    (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |B p.1 p.2 - A p.1 p.2| ≤ θ) :
    ‖matCLME (sparseDelta A B S)‖ ≤ Real.sqrt (s : ℝ) * θ :=
  le_trans (opNorm_le_frobenius (sparseDelta A B S))
    (sparse_edit_frobenius_bound A B S s θ hS hθ hA)

/-! ## 定理三：逐点输出误差界 ‖ΔW·x‖ ≤ √s·θ·‖x‖ -/

theorem sparse_edit_output_bound (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) (s : ℕ) (θ : ℝ)
    (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |B p.1 p.2 - A p.1 p.2| ≤ θ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖matvecE (sparseDelta A B S) x‖ ≤ Real.sqrt (s : ℝ) * θ * ‖x‖ := by
  calc
    ‖matvecE (sparseDelta A B S) x‖ ≤ frobeniusNorm (sparseDelta A B S) * ‖x‖ :=
      frobenius_bound (sparseDelta A B S) x
    _ ≤ (Real.sqrt (s : ℝ) * θ) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (sparse_edit_frobenius_bound A B S s θ hS hθ hA)
        (norm_nonneg x)

/-- 逐点输出误差界（算子版）。 -/
theorem sparse_edit_output_bound_clm (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) (s : ℕ) (θ : ℝ)
    (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |B p.1 p.2 - A p.1 p.2| ≤ θ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖matCLME (sparseDelta A B S) x‖ ≤ Real.sqrt (s : ℝ) * θ * ‖x‖ := by
  calc
    ‖matCLME (sparseDelta A B S) x‖ ≤ ‖matCLME (sparseDelta A B S)‖ * ‖x‖ :=
      (matCLME (sparseDelta A B S)).le_opNorm x
    _ ≤ (Real.sqrt (s : ℝ) * θ) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (sparse_edit_op_bound A B S s θ hS hθ hA) (norm_nonneg x)

/-! ## 定理四（核心）：稀疏编辑后约束输出的漂移 ≤ √s·θ·‖x‖ -/

theorem sparse_edit_constraint_drift (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) (s : ℕ) (θ : ℝ)
    (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |B p.1 p.2 - A p.1 p.2| ≤ θ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖matvecE (sparseEdit A B S) x - matvecE A x‖ ≤ Real.sqrt (s : ℝ) * θ * ‖x‖ := by
  rw [← matvecE_sub, sparseEdit_sub_eq_delta]
  exact sparse_edit_output_bound A B S s θ hS hθ hA x

/-- 约束漂移（线性约束泛化）：对任意连续线性约束泛函 ℓ（‖ℓ‖ ≤ 1），
稀疏编辑后 ℓ 的取值漂移 ≤ √s·θ·‖x‖（逐点输出界的 ℓ-对偶版本）。 -/
theorem sparse_edit_constraint_drift_functional (A B : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m × Fin n)) (s : ℕ) (θ : ℝ)
    (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |B p.1 p.2 - A p.1 p.2| ≤ θ)
    (x : EuclideanSpace ℝ (Fin n)) (ℓ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hℓ : ‖ℓ‖ ≤ 1) :
    ‖ℓ (matvecE (sparseEdit A B S) x - matvecE A x)‖ ≤ Real.sqrt (s : ℝ) * θ * ‖x‖ := by
  calc
    ‖ℓ (matvecE (sparseEdit A B S) x - matvecE A x)‖
        ≤ ‖ℓ‖ * ‖matvecE (sparseEdit A B S) x - matvecE A x‖ := ℓ.le_opNorm _
    _ ≤ 1 * (Real.sqrt (s : ℝ) * θ * ‖x‖) :=
      mul_le_mul hℓ (sparse_edit_constraint_drift A B S s θ hS hθ hA x)
        (norm_nonneg _) (by norm_num)
    _ = Real.sqrt (s : ℝ) * θ * ‖x‖ := by ring

end Lattice
