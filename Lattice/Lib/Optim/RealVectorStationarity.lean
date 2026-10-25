import Mathlib
import Lattice.Lift.RealLinear
/-!
# LATTICE: P0 向量版 —— 平方损失 fderiv 驻点 ⟺ 满足（法方程）

调研（research/embedding/README.md §4 P0）的向量版（ℝⁿ = ι → ℝ）：
一致标量系数系统（点积约束）dot a x = b，a ≠ 0，
平方损失 L(x) = (dot a x - b)²，

  驻点（fderiv = 0）⟺ 满足点（dot a x = b）。

证明：
  1. fderiv 计算：fderiv L x = 2(dot a x - b) • dotCLM a
     （dot a · 是连续线性映射，导数为自身；平方链式法则）；
  2. 线性映射为零 ⟹ 作用到 a 为零：2(dot a x-b)·(dot a a) = 0；
  3. 严格正定：dot a a > 0（a ≠ 0 ⟹ Σaᵢ² > 0）⟹ dot a x = b。

向量版法方程（Aᵀ(Ax-b)=0 ⟺ Ax=b，一致系统）的系数向量特例。
-/


noncomputable section

open Filter
open scoped Topology

namespace Lattice

/-! RealLinear 的内容同在 Lattice 命名空间，无需 open。-/

/-! ## 点积作为连续线性映射 -/

def dotCLM {ι : Type} [Fintype ι] (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  { toFun := fun x => RealDot a x
    map_add' := by
      intro x y
      simp [RealDot, Finset.sum_add_distrib, mul_add]
    map_smul' := by
      intro c x
      simp [RealDot, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    cont := by
      change Continuous (fun x : ι → ℝ => ∑ i, a i * x i)
      exact continuous_finset_sum Finset.univ
        (fun i hi => continuous_const.mul (continuous_apply i)) }

/-! ## 引理：点积的 fderiv = 自身（连续线性映射） -/

lemma hasFDerivAt_dot {ι : Type} [Fintype ι] (a x : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ => RealDot a y) (dotCLM a) x := by
  -- 连续线性映射的导数 = 自身
  simpa [dotCLM] using (dotCLM a).hasFDerivAt

/-! ## 引理：平方损失 fderiv 计算
fderiv (fun y => (dot a y - b)²) x = 2(dot a x - b) • dotCLM a。-/

lemma fderiv_vecLoss {ι : Type} [Fintype ι] (a : ι → ℝ) (b : ℝ) (x : ι → ℝ) :
    fderiv ℝ (fun y => (RealDot a y - b) ^ 2) x = (2 * (RealDot a x - b)) • dotCLM a := by
  -- 内层：dot a · - b，导数 = dotCLM a
  have hsub : HasFDerivAt (fun y : ι → ℝ => RealDot a y - b) (dotCLM a) x := by
    simpa using (hasFDerivAt_dot a x).sub_const b
  -- 外层平方：写成乘积 (dot a y - b)·(dot a y - b)，用乘法法则（mathlib 4.14 无 HasFDerivAt.pow）
  have hpow : HasFDerivAt (fun y : ι → ℝ => (RealDot a y - b) ^ 2)
      ((2 * (RealDot a x - b)) • dotCLM a) x := by
    have hmul := hsub.mul hsub
    have hfuneq : (fun y : ι → ℝ => (RealDot a y - b) ^ 2)
        = fun y : ι → ℝ => (RealDot a y - b) * (RealDot a y - b) := by
      funext y
      ring
    have hderiv : (RealDot a x - b) • dotCLM a + (RealDot a x - b) • dotCLM a
        = (2 * (RealDot a x - b)) • dotCLM a := by
      ext z
      simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hfuneq, ← hderiv]
    exact hmul
  exact hpow.fderiv

/-! ## 引理：点积严格正定
RealDot a a = 0 ⟺ a = 0（Σaᵢ² 逐项非负，和零 ⟺ 各项零）。-/

lemma dot_self_eq_zero_iff {ι : Type} [Fintype ι] (a : ι → ℝ) :
    RealDot a a = 0 ↔ a = 0 := by
  unfold RealDot
  -- Σ aᵢ·aᵢ = 0 ⟺ 每项 aᵢ·aᵢ = 0（非负和）⟺ a = 0（mul_self_eq_zero）
  exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (a i)).trans <| by
    simp [funext_iff, mul_self_eq_zero]

/-! ## 定理：P0 向量版 —— 平方损失驻点 ⟺ 满足（a ≠ 0） -/

theorem P0_vector_stationarity {ι : Type} [Fintype ι] (a : ι → ℝ) (b : ℝ) (x : ι → ℝ)
    (ha : a ≠ 0) :
    fderiv ℝ (fun y => (RealDot a y - b) ^ 2) x = 0 ↔ RealDot a x = b := by
  rw [fderiv_vecLoss a b x]
  constructor
  · intro h
    -- 线性映射 (2(dot a x-b)) • dotCLM a = 0，作用到 a
    have hva : (2 * (RealDot a x - b)) • dotCLM a = 0 := h
    have happly : (2 * (RealDot a x - b)) * RealDot a a = 0 := by
      have h0 : ((2 * (RealDot a x - b)) • dotCLM a) a = 0 := by
        simpa using congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L a) hva
      simpa [dotCLM, ContinuousLinearMap.smul_apply] using h0
    -- dot a a ≠ 0（a ≠ 0）
    have hdaa : RealDot a a ≠ 0 := by
      intro hz
      exact ha ((dot_self_eq_zero_iff a).mp hz)
    -- 2(dot a x-b)·(dot a a) = 0 → dot a x - b = 0
    have hz : RealDot a x - b = 0 := by
      have h2 : 2 * (RealDot a x - b) = 0 := (mul_eq_zero.mp happly).resolve_right hdaa
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    linarith
  · intro h
    -- 满足 → 损失局部平方 → fderiv = 2·0•dotCLM = 0
    have : (2 * (RealDot a x - b)) • dotCLM a = 0 := by
      rw [h]
      simp
    simpa using this

/-! ## 推论：驻点唯一（a ≠ 0 时点积方程唯一解不保证分量唯一，
但满足点处损失为全局最小——严格凸性）。 -/

theorem P0_vector_unique_loss_value {ι : Type} [Fintype ι] (a : ι → ℝ) (b : ℝ) (x : ι → ℝ)
    (ha : a ≠ 0) (h : fderiv ℝ (fun y => (RealDot a y - b) ^ 2) x = 0) :
    (RealDot a x - b) ^ 2 = 0 := by
  have hsat : RealDot a x = b := (P0_vector_stationarity a b x ha).mp h
  rw [hsat]
  ring

end Lattice
