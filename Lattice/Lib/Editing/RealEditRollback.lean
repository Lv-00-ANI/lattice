import Lattice.Lib.Editing.RealBatchEditClosed
import Lattice.Lib.Editing.RealROME
import Lattice.Lib.Editing.RealEditCrosstalk
import Mathlib

/-!
# LATTICE: 编辑回滚 / 可逆性 —— rank-one 补丁的精确撤销

权重编辑线的可逆性维度：ROME/MEMIT 的 rank-one 编辑

    rankOneEdit F Δ k : x ↦ F·x + ⟨k,x⟩·Δ

是**加法**补丁。本文件证明它可精确撤销（回滚）：

  1. `rankOneEdit`（def）：与 RealROME.ROME / RealBatchEditClosed.RankOnePatch
     一致的 rank-one 补丁（标量行语义；Δ = 写入量，k = 键）；
  2. `rollback_edit`（核心）：`rankOneEdit (rankOneEdit F Δ k) (−Δ) k = F`
     —— 施加 Δ⊗k 后再施加 (−Δ)⊗k 精确恢复（加法逆元，逐点线性性）；
  3. `batch_rollback`（核心）：m 个批量编辑之和的逆 = 各编辑取负
     （`batchRankOneEdit (batchRankOneEdit F Δ k) (−Δ) k = F`，
     由 `Finset.sum_neg_distrib` 把增量和消成 0）；
  4. `rollback_after_write`（核心/衔接）：在**各键两两正交**（`horth`）与
     **各键非零**（`hk`）两条前提下一并给出：正交闭式写入事实
     （`BatchEditClosed W k v (k i) = v i`，调用 RealBatchEditClosed 的
     batchClosed_orthogonal_writes），再以负补丁回滚，精确恢复原权重 W
     （原写入事实保留）——写入侧的闭式本身以两两正交为承重前提，去掉它
     该写入并不成立；
  5. `edit_orbit_identity`（加分）：任意有限编辑序列的逆存在 ——
     `invEditSeq`（逐编辑取负、逆序）使 `editSeq (invEditSeq l) (editSeq l F) = F`，
     对列表结构归纳。

诚实假设：编辑是**线性加法** rank-one 补丁（`F x + ⟨k,x⟩·Δ`）；
`rollback_after_write` 的写入侧需要「各键两两正交」（`horth`）与
「各键非零」（`hk`，用于 ‖kᵢ‖² 的消去）；本文件其余定理不设键的前提。
域为 ℝ 欧氏内积。注意语义差异：顺序编辑（RealEditCrosstalk.ApplyEdits2）
为逐次复合，本文件的 `editSeq` 与其一致；而"覆盖语义"（同键最后写入胜出）
不是加法补丁，不在回滚范围内（见 RealEditCrosstalk.edit2_same_key_overwrites）。
无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## rank-one 编辑（加法补丁） -/

/-- 单键 rank-one 编辑（标量行语义）：`rankOneEdit F Δ k x = F x + ⟨k,x⟩·Δ`。
与 RealROME.ROME 的补丁项 `⟨k₀,x⟩·(v−W·k₀)/‖k₀‖²` 形式一致（取
Δ = (v−W·k₀)/‖k₀‖²），与 RealBatchEditClosed.RankOnePatch 同为加法补丁。 -/
def rankOneEdit (F : E → ℝ) (Δ : ℝ) (k : E) (x : E) : ℝ :=
  F x + inner k x * Δ

/-- m 键批量 rank-one 编辑：`F x + Σᵢ ⟨kᵢ,x⟩·Δᵢ`
（与 `RankOnePatch Δ k x` 恰为同一求和）。 -/
def batchRankOneEdit {m : ℕ} (F : E → ℝ) (Δ : Fin m → ℝ) (k : Fin m → E) (x : E) : ℝ :=
  F x + ∑ i : Fin m, inner (k i) x * Δ i

omit [CompleteSpace E] in
/-- 批量编辑与 RealBatchEditClosed.RankOnePatch 的桥（rfl）。 -/
lemma batchRankOneEdit_eq_rankOnePatch {m : ℕ} (F : E → ℝ) (Δ : Fin m → ℝ)
    (k : Fin m → E) (x : E) :
    batchRankOneEdit F Δ k x = F x + RankOnePatch Δ k x :=
  rfl

omit [CompleteSpace E] in
omit [CompleteSpace E] in
/-- 闭式批量编辑就是 `batchRankOneEdit`（取 Δᵢ = (vᵢ − W·kᵢ)/‖kᵢ‖²），rfl 桥。 -/
lemma batchClosed_eq_batchRankOneEdit {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E)
    (v : Fin m → ℝ) (x : E) :
    BatchEditClosed W k v x
      = batchRankOneEdit (fun y => W y) (fun i => (v i - W (k i)) / ‖k i‖ ^ 2) k x :=
  rfl

/-! ## 定理一（核心）：单编辑精确回滚 -/

theorem rollback_edit (F : E → ℝ) (Δ : ℝ) (k : E) :
    rankOneEdit (rankOneEdit F Δ k) (-Δ) k = F := by
  funext x
  unfold rankOneEdit
  ring

omit [CompleteSpace E] in
omit [CompleteSpace E] in
/-- 单编辑精确回滚（逐点形式）。 -/
theorem rollback_edit_apply (F : E → ℝ) (Δ : ℝ) (k : E) (x : E) :
    rankOneEdit (rankOneEdit F Δ k) (-Δ) k x = F x := by
  unfold rankOneEdit
  ring

/-! ## 定理二（核心）：批量编辑精确回滚 -/

theorem batch_rollback {m : ℕ} (F : E → ℝ) (Δ : Fin m → ℝ) (k : Fin m → E) :
    batchRankOneEdit (batchRankOneEdit F Δ k) (fun i => -Δ i) k = F := by
  funext x
  unfold batchRankOneEdit
  have hsum : (∑ i : Fin m, inner (k i) x * (-Δ i))
      = -(∑ i : Fin m, inner (k i) x * Δ i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

/-- 批量回滚（逐点形式）。 -/
theorem batch_rollback_apply {m : ℕ} (F : E → ℝ) (Δ : Fin m → ℝ) (k : Fin m → E) (x : E) :
    batchRankOneEdit (batchRankOneEdit F Δ k) (fun i => -Δ i) k x = F x := by
  have h := batch_rollback F Δ k
  exact congrFun h x

/-! ## 定理三（核心/衔接）：先写入事实，再回滚恢复原权重 -/

theorem rollback_after_write {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) :
    (∀ i : Fin m, BatchEditClosed W k v (k i) = v i) ∧
      (∀ x : E, batchRankOneEdit (fun y => BatchEditClosed W k v y)
        (fun i => -((v i - W (k i)) / ‖k i‖ ^ 2)) k x = W x) := by
  refine ⟨batchClosed_orthogonal_writes W k v horth hk, ?_⟩
  intro x
  unfold BatchEditClosed batchRankOneEdit RankOnePatch
  have hsum : (∑ i : Fin m, inner (k i) x * (-((v i - W (k i)) / ‖k i‖ ^ 2)))
      = -(∑ i : Fin m, inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

/-- 单键版：ROME 写入事实后可回滚恢复原权重 W（衔接 RealROME.ROME_writes_fact）。 -/
theorem rollback_after_rome (W : E →L[ℝ] ℝ) (k₀ : E) (v : ℝ) (hk : k₀ ≠ 0) :
    (ROME W k₀ v k₀ = v) ∧
      (∀ x : E,
        rankOneEdit (fun y => ROME W k₀ v y) (-((v - W k₀) / ‖k₀‖ ^ 2)) k₀ x = W x) := by
  refine ⟨ROME_writes_fact W k₀ v hk, ?_⟩
  intro x
  unfold ROME rankOneEdit
  ring

/-! ## 定理四（加分）：任意有限编辑序列的逆存在 -/

/-- 顺序编辑序列：把列表中的 (Δ,k) 依次作为 rank-one 补丁施加。 -/
def editSeq (l : List (ℝ × E)) (F : E → ℝ) : E → ℝ :=
  l.foldl (fun G p => rankOneEdit G p.1 p.2) F

/-- 逆编辑序列：逐编辑取负，并逆序（`invEditSeq [e₁,e₂] = [e₂⁻¹,e₁⁻¹]`）。 -/
def invEditSeq : List (ℝ × E) → List (ℝ × E)
  | [] => []
  | p :: l => invEditSeq l ++ [(-p.1, p.2)]

omit [CompleteSpace E] in
lemma editSeq_nil (F : E → ℝ) : editSeq [] F = F := rfl

omit [CompleteSpace E] in
lemma editSeq_singleton (p : ℝ × E) (F : E → ℝ) :
    editSeq [p] F = rankOneEdit F p.1 p.2 := rfl

omit [CompleteSpace E] in
lemma editSeq_append (l₁ l₂ : List (ℝ × E)) (F : E → ℝ) :
    editSeq (l₁ ++ l₂) F = editSeq l₂ (editSeq l₁ F) := by
  unfold editSeq
  rw [List.foldl_append]

/-- 核心（归纳）：`invEditSeq` 是 `editSeq` 的精确逆。 -/
theorem edit_orbit_identity (l : List (ℝ × E)) (F : E → ℝ) :
    editSeq (invEditSeq l) (editSeq l F) = F := by
  induction l generalizing F with
  | nil => rfl
  | cons p l ih =>
      change editSeq (invEditSeq l ++ [(-p.1, p.2)]) (editSeq (p :: l) F) = F
      rw [show editSeq (p :: l) F = editSeq l (rankOneEdit F p.1 p.2) from rfl]
      rw [editSeq_append]
      rw [ih (rankOneEdit F p.1 p.2)]
      rw [editSeq_singleton]
      exact rollback_edit F p.1 p.2

/-- 轨道陈述：编辑序列的作用是 F ↦ F + Σ⟨kᵢ,·⟩Δᵢ，其逆即负序列，
故每个有限编辑序列作用于函数空间给出一个可逆（双射）轨道。 -/
theorem edit_orbit_inverse_exists (l : List (ℝ × E)) :
    ∃ g : (E → ℝ) → (E → ℝ), ∀ F : E → ℝ, g (editSeq l F) = F :=
  ⟨editSeq (invEditSeq l), fun F => edit_orbit_identity l F⟩

end Lattice
