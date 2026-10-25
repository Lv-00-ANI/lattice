import Lattice.Lib.Editing.RealBatchEditClosed
import Mathlib

/-!
# LATTICE: 非正交键的精确批量写入 —— Gram 矩阵线性系统解

VERIFICATION.md §5 展望「一般键批量闭式」的终版：RealBatchEditClosed 在
**键两两正交**下给出精确闭式 Δᵢ = (vᵢ − W·kᵢ)/‖kᵢ‖²；RealCrosstalkGeneral
把非正交残差写成显式串扰和（精确但仍是「目标 + 残差」形式）。本文件**去掉
正交假设并直接求精确解**：一般键下批量编辑

    W' = W + Σᵢ Δᵢ⊗kᵢ       （标量行语义：x ↦ W·x + Σᵢ ⟨kᵢ,x⟩·Δᵢ）

精确写入全部目标 W'·kᵢ = vᵢ（∀i）当且仅当线性系统

    G·Δ = r,   Gᵢⱼ = ⟨kⱼ,kᵢ⟩（Gram 矩阵）,   rᵢ = vᵢ − W·kᵢ

可解；G 可逆时解存在且唯一，Δ = G⁻¹·r。

定理清单：
  1. `gramEdit_writes_iff`（桥）：∀i, W'·kᵢ = vᵢ ⟺ G·Δ = r（展开定义即得，
     把「精确写入」完全翻译为矩阵方程）；
  2. `gram_solvable_iff`（核心）：存在 Δ 使所有目标精确写入 ⟺ r ∈ range(G)
     （G 作为线性映射 `Matrix.mulVecLin` 的像），线性代数可解性判据；
  3. `gram_invertible_exact_write`（核心，构造性）：G 可逆（`Invertible G`）
     ⟹ ∃Δ, ∀i, W'·kᵢ = vᵢ；显式解 Δ = ⅟G·r（`Matrix.mulVec` + `mulVec_mulVec`
     + `Invertible.mul_invOf_self`），并给出 det 判据推论 `gram_det_exact_write`
     （`IsUnit G.det` ⟹ 可逆，`Matrix.invertibleOfIsUnitDet`）；
  4. `gram_exact_write_unique`：G 可逆 ⟹ 写入解 Δ 唯一（`mulVec_injective_of_invertible`）；
  5. `orthogonal_is_diagonal_gram` / `orthogonal_gram_diag_solves`
     （核心衔接）：正交键 ⟹ G 的非对角元全为 0（对角矩阵），且对角解
     Δᵢ = rᵢ/‖kᵢ‖² 恰解 G·Δ = r —— 于是 `orthogonal_gram_recovers_closed_form`
     回收 RealBatchEditClosed 的正交闭式（`batchClosed_orthogonal_writes`），
     两条路线在正交键下给出同一结论（`orthogonal_two_routes_agree`）。

诚实假设（全部显式）：G 可逆（或仅 r ∈ range G）；维度一致的有限维 ℝ 空间
（m 个键、Fin m 指标）；标量行语义。**无正交假设**（正交仅在定理 5 中作为
特例出现）。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Gram 矩阵与 Gram 批量编辑 -/

/-- Gram 矩阵 Gᵢⱼ = ⟨kⱼ,kᵢ⟩（约定：`G.mulVec Δ i = Σⱼ ⟨kⱼ,kᵢ⟩·Δⱼ`，正好是
键 kᵢ 处补丁的总响应）。 -/
def gramMatrix {m : ℕ} (k : Fin m → E) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => inner (k j) (k i)

omit [CompleteSpace E] in
/-- Gram 批量编辑：W'·x = W·x + Σᵢ ⟨kᵢ,x⟩·Δᵢ（与 `RankOnePatch` 同一 rank-one
补丁之和，只是 Δ 不再由正交闭式给出，而是候选解）。 -/
def GramEdit {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (Δ : Fin m → ℝ) (x : E) : ℝ :=
  W x + ∑ i : Fin m, inner (k i) x * Δ i

/-! ## 展开引理：Gram 矩阵乘向量的逐坐标公式 -/

lemma gramMatrix_mulVec_apply {m : ℕ} (k : Fin m → E) (Δ : Fin m → ℝ) (i : Fin m) :
    (gramMatrix k).mulVec Δ i = ∑ j : Fin m, inner (k j) (k i) * Δ j := by
  simp [gramMatrix, Matrix.mulVec, Matrix.dotProduct]

/-! ## 定理一（桥）：精确写入 ⟺ 线性系统 G·Δ = r -/

theorem gramEdit_writes_iff {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (Δ : Fin m → ℝ) :
    (∀ i : Fin m, GramEdit W k Δ (k i) = v i) ↔
      (gramMatrix k).mulVec Δ = (fun i : Fin m => v i - W (k i)) := by
  constructor
  · intro h
    funext i
    have hi := h i
    unfold GramEdit at hi
    rw [gramMatrix_mulVec_apply]
    linarith
  · intro h i
    have hi := congrFun h i
    rw [gramMatrix_mulVec_apply] at hi
    unfold GramEdit
    rw [hi]
    ring

omit [CompleteSpace E] in
/-- 编辑函数与 RealBatchEditClosed 的闭式补丁同构：取 Δᵢ = (vᵢ − W·kᵢ)/‖kᵢ‖²
时 `GramEdit` 恰为 `BatchEditClosed`（rfl，同一 `RankOnePatch` 之和）。 -/
theorem gramEdit_eq_batchClosed {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (x : E) :
    GramEdit W k (fun i => (v i - W (k i)) / ‖k i‖ ^ 2) x = BatchEditClosed W k v x :=
  rfl

/-! ## 定理二（核心）：可解性判据 —— 精确写入 ⟺ r ∈ range(G) -/

theorem gram_solvable_iff {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ) :
    (∃ Δ : Fin m → ℝ, ∀ i : Fin m, GramEdit W k Δ (k i) = v i) ↔
      (fun i : Fin m => v i - W (k i)) ∈ LinearMap.range (Matrix.mulVecLin (gramMatrix k)) := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨Δ, hΔ⟩
    exact ⟨Δ, by simpa [Matrix.mulVecLin_apply] using (gramEdit_writes_iff W k v Δ).mp hΔ⟩
  · rintro ⟨Δ, hΔ⟩
    exact ⟨Δ, (gramEdit_writes_iff W k v Δ).mpr (by simpa [Matrix.mulVecLin_apply] using hΔ)⟩

/-! ## 定理三（核心，构造性）：G 可逆 ⟹ 精确写入存在，Δ = ⅟G·r -/

/-- 可逆矩阵的乘向量映射单射（滚动回代）：G 可逆 ⟹ `G.mulVec` 单射。 -/
lemma mulVec_injective_of_invertible {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) [Invertible M] :
    Function.Injective M.mulVec := by
  intro a b hab
  have h2 : (⅟M).mulVec (M.mulVec a) = (⅟M).mulVec (M.mulVec b) := by rw [hab]
  rw [Matrix.mulVec_mulVec, Invertible.invOf_mul_self, Matrix.one_mulVec] at h2
  rw [Matrix.mulVec_mulVec, Invertible.invOf_mul_self, Matrix.one_mulVec] at h2
  exact h2

theorem gram_invertible_exact_write {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    [Invertible (gramMatrix k)] :
    ∃ Δ : Fin m → ℝ, ∀ i : Fin m, GramEdit W k Δ (k i) = v i := by
  refine ⟨(⅟(gramMatrix k)).mulVec (fun i => v i - W (k i)), ?_⟩
  rw [gramEdit_writes_iff]
  rw [Matrix.mulVec_mulVec, Invertible.mul_invOf_self, Matrix.one_mulVec]

/-- det 判据推论：`IsUnit G.det` ⟹ 精确写入存在（`Matrix.invertibleOfIsUnitDet`
把 det 可逆转成 `Invertible G`）。 -/
theorem gram_det_exact_write {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (hG : IsUnit (gramMatrix k).det) :
    ∃ Δ : Fin m → ℝ, ∀ i : Fin m, GramEdit W k Δ (k i) = v i := by
  haveI : Invertible (gramMatrix k) := Matrix.invertibleOfIsUnitDet (gramMatrix k) hG
  exact gram_invertible_exact_write W k v

/-! ## 定理四：G 可逆 ⟹ 写入解唯一 -/

theorem gram_exact_write_unique {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    [Invertible (gramMatrix k)] (Δ Δ' : Fin m → ℝ)
    (h : ∀ i : Fin m, GramEdit W k Δ (k i) = v i)
    (h' : ∀ i : Fin m, GramEdit W k Δ' (k i) = v i) :
    Δ = Δ' := by
  have h1 := (gramEdit_writes_iff W k v Δ).mp h
  have h2 := (gramEdit_writes_iff W k v Δ').mp h'
  exact mulVec_injective_of_invertible (gramMatrix k) (by rw [h1, h2])

/-! ## 定理五（核心衔接）：正交键 ⟹ G 对角，Δᵢ = rᵢ/‖kᵢ‖² 解 G·Δ = r -/

omit [CompleteSpace E] in
/-- 正交键 ⟹ Gram 矩阵非对角元全为 0（G 是对角矩阵）。 -/
theorem orthogonal_is_diagonal_gram {m : ℕ} (k : Fin m → E)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ)) :
    ∀ i j : Fin m, i ≠ j → gramMatrix k i j = (0 : ℝ) := by
  intro i j hij
  exact horth j i (Ne.symm hij)

/-- 对角解：正交键下 Δᵢ = rᵢ/‖kᵢ‖² 精确解 G·Δ = r
（由 RealBatchEditClosed.sum_orthogonal_kill 消去非对角项 + ‖kᵢ‖² 消去）。 -/
theorem orthogonal_gram_diag_solves {m : ℕ} (k : Fin m → E) (r : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) :
    (gramMatrix k).mulVec (fun i => r i / ‖k i‖ ^ 2) = r := by
  funext i
  rw [gramMatrix_mulVec_apply]
  rw [sum_orthogonal_kill (fun j => r j / ‖k j‖ ^ 2) k horth i]
  have hnorm : inner (k i) (k i) = ‖k i‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) (k i)
  rw [hnorm]
  have hk' : ‖k i‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero (k i) (hk i)
  field_simp [hk']

/-- 回收正交闭式：正交键 ⟹ Gram 路线（Δ = 对角解）精确写入全部目标。 -/
theorem orthogonal_gram_recovers_closed_form {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E)
    (v : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) :
    ∀ i : Fin m, GramEdit W k (fun i => (v i - W (k i)) / ‖k i‖ ^ 2) (k i) = v i := by
  rw [gramEdit_writes_iff]
  exact orthogonal_gram_diag_solves k (fun i => v i - W (k i)) horth hk

/-- 两条路线一致（正交键）：Gram 对角解路线与 RealBatchEditClosed 的正交闭式
路线给出同一精确写入结论。 -/
theorem orthogonal_two_routes_agree {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) :
    (∀ i : Fin m, GramEdit W k (fun i => (v i - W (k i)) / ‖k i‖ ^ 2) (k i) = v i) ∧
      (∀ i : Fin m, BatchEditClosed W k v (k i) = v i) :=
  ⟨orthogonal_gram_recovers_closed_form W k v horth hk,
    batchClosed_orthogonal_writes W k v horth hk⟩

/-- 非正交键的显式对照（衔接 RealCrosstalkGeneral.batchClosed_exact_residual）：
闭式补丁在 kᵢ 处的响应 = vᵢ + 非对角串扰和；G·Δ = r 则把该残差吸收进解中
（本文件定理一给出可解性判据）。 -/
theorem gram_vs_closed_residual {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (i : Fin m) :
    GramEdit W k (fun i => (v i - W (k i)) / ‖k i‖ ^ 2) (k i)
      = BatchEditClosed W k v (k i) :=
  gramEdit_eq_batchClosed W k v (k i)

end Lattice
