import Mathlib

/-!
# LATTICE: P0 一般法方程 —— 内积空间上的平方损失驻点 ⟺ 满足

调研（research/embedding/README.md §4 P0）的一般形式：
E、F 为 ℝ 内积空间，A : E →L[ℝ] F 连续线性算子，b ∈ range A（一致系统），
平方损失 L(x) = ‖A·x - b‖²，

  驻点（fderiv = 0）⟺ 满足点（A·x = b）。

证明（法方程 Aᵀ(Ax-b)=0 ⟺ Ax=b 的抽象形式）：
  1. 方向导数：fderiv L x v = 2⟨Ax-b, A v⟩（norm² 沿直线求导 + fderiv_apply）；
  2. fderiv = 0 ⟹ ∀v, ⟨Ax-b, A v⟩ = 0 ⟹ Ax-b ∈ (range A)ᗮ（正交补）；
  3. 一致系统（b ∈ range A）⟹ Ax-b ∈ range A；
  4. range A ⊓ (range A)ᗮ = ⊥ ⟹ Ax-b = 0 ⟹ Ax = b。

这是「硬约束解嵌入软约束驻点」的完整抽象形式化。
-/

noncomputable section

open Filter
open scoped Topology

namespace Lattice

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ## 平方损失的范数形式 -/

def NormSqLoss (A : E →L[ℝ] F) (b : F) (x : E) : ℝ := ‖A x - b‖ ^ 2

/-! ## 引理一：范数平方沿直线的导数
d/dt [‖u + t·w‖²]₀ = 2⟨u, w⟩。-/

omit [CompleteSpace F] in
lemma norm_sq_line_deriv (u w : F) :
    deriv (fun t : ℝ => ‖u + t • w‖ ^ 2) 0 = 2 * inner u w := by
  -- 直线 u + t·w 的导数为 w，再用 HasDerivAt.norm_sq
  have hline : HasDerivAt (fun t : ℝ => u + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u
  have hquad : HasDerivAt (fun t : ℝ => ‖u + t • w‖ ^ 2) (2 * inner u w) 0 := by
    simpa using hline.norm_sq
  exact hquad.deriv

/-! ## 引理二：L 处处可导 -/

omit [CompleteSpace E] [CompleteSpace F] in
lemma loss_differentiable (A : E →L[ℝ] F) (b : F) : ∀ x : E, DifferentiableAt ℝ (NormSqLoss A b) x := by
  intro x
  -- A·x - b 可导（线性 + 常数），norm² 可导，复合可导
  have hlin : DifferentiableAt ℝ (fun y : E => A y - b) x := by
    simpa using (A.differentiableAt).sub (differentiableAt_const b)
  simpa [NormSqLoss] using (hlin.hasFDerivAt.norm_sq).differentiableAt

/-! ## 引理三：方向导数 = fderiv 作用（桥）
fderiv L x v = deriv (fun t => L (x + t·v)) 0。-/

omit [CompleteSpace E] in
lemma fderiv_apply_direction {f : E → ℝ} {x v : E}
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  -- 直线 t ↦ x + t·v 在 0 处导数为 v，复合 HasFDerivAt.comp_hasDerivAt
  have hg : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    have hx : x + (0 : ℝ) • v = x := by simp
    rw [hx]
    exact hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt 0 hg).deriv.symm

/-! ## 引理四：fderiv L x v = 2⟨Ax-b, A v⟩ -/

lemma fderiv_loss_apply (A : E →L[ℝ] F) (b : F) (x v : E) :
    fderiv ℝ (NormSqLoss A b) x v = 2 * inner (A x - b) (A v) := by
  -- 桥：方向导数
  have hg : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt (NormSqLoss A b) (fderiv ℝ (NormSqLoss A b) x) (x + (0 : ℝ) • v) := by
    have hx : x + (0 : ℝ) • v = x := by simp
    rw [hx]
    exact (loss_differentiable A b x).hasFDerivAt
  have hdir : fderiv ℝ (NormSqLoss A b) x v = deriv (fun t : ℝ => NormSqLoss A b (x + t • v)) 0 := by
    exact (hf'.comp_hasDerivAt 0 hg).deriv.symm
  rw [hdir]
  -- L(x + t·v) = ‖(Ax-b) + t·(Av)‖²
  have hL : ∀ t : ℝ, NormSqLoss A b (x + t • v) = ‖(A x - b) + t • (A v)‖ ^ 2 := by
    intro t
    have harg : A (x + t • v) - b = (A x - b) + t • A v := by
      calc
        A (x + t • v) - b = (A x + A (t • v)) - b := by rw [A.map_add]
        _ = (A x + t • A v) - b := by rw [A.map_smul]
        _ = (A x - b) + t • A v := by abel
    unfold NormSqLoss
    rw [harg]
  calc
    deriv (fun t : ℝ => NormSqLoss A b (x + t • v)) 0
        = deriv (fun t : ℝ => ‖(A x - b) + t • (A v)‖ ^ 2) 0 := by
          exact congrArg (fun g : ℝ → ℝ => deriv g 0) (funext hL)
    _ = 2 * inner (A x - b) (A v) := by
          -- 直线 (Ax-b) + t·(Av) 的导数 (Av)，norm² 复合
          have hline : HasDerivAt (fun t : ℝ => (A x - b) + t • (A v)) (A v) 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (A v)).const_add (A x - b)
          have hquad : HasDerivAt (fun t : ℝ => ‖(A x - b) + t • (A v)‖ ^ 2)
              (2 * inner (A x - b) (A v)) 0 := by
            simpa using hline.norm_sq
          exact hquad.deriv

/-! ## 引理五：fderiv 为零 ⟺ 对一切 v 方向导数为零 -/

omit [CompleteSpace E] in
lemma fderiv_eq_zero_iff_all (f : E → ℝ) (x : E) (_hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x = 0 ↔ ∀ v : E, fderiv ℝ f x v = 0 := by
  constructor
  · intro h v
    rw [h]
    simp
  · intro h
    -- 线性映射为零：ext v
    ext v
    simpa using h v

/-! ## 引理六：正交补条件（mem_orthogonal 的形式） -/

omit [CompleteSpace E] [CompleteSpace F] in
lemma mem_orthogonal_range {x : F} {A : E →L[ℝ] F}
    (h : ∀ v : E, (inner x (A v) : ℝ) = 0) : x ∈ (Submodule.orthogonal (LinearMap.range (A : E →ₗ[ℝ] F))) := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  rcases (LinearMap.mem_range.mp hy) with ⟨v, rfl⟩
  exact (real_inner_comm (A v) x).symm.trans (h v)

/-! ## 定理：P0 一般法方程 —— 平方损失驻点 ⟺ 满足（一致系统） -/

theorem P0_normal_equation (A : E →L[ℝ] F) (b : F) (x : E)
    (hb : b ∈ LinearMap.range (A : E →ₗ[ℝ] F)) :
    fderiv ℝ (NormSqLoss A b) x = 0 ↔ A x = b := by
  constructor
  · intro hfd
    -- fderiv = 0 ⟹ 所有方向导数为 0
    have hall : ∀ v : E, (2 * inner (A x - b) (A v) : ℝ) = 0 := by
      intro v
      have : fderiv ℝ (NormSqLoss A b) x v = 0 :=
        (fderiv_eq_zero_iff_all (NormSqLoss A b) x (loss_differentiable A b x)).mp hfd v
      rwa [fderiv_loss_apply A b x v] at this
    -- 2⟨Ax-b, Av⟩ = 0 ⟹ ⟨Ax-b, Av⟩ = 0
    have hinner : ∀ v : E, (inner (A x - b) (A v) : ℝ) = 0 := by
      intro v
      exact (mul_eq_zero.mp (hall v)).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    -- Ax-b ∈ (range A)ᗮ
    have horth : (A x - b) ∈ (Submodule.orthogonal (LinearMap.range (A : E →ₗ[ℝ] F))) := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      rcases (LinearMap.mem_range.mp hy) with ⟨v, rfl⟩
      exact (real_inner_comm (A v) (A x - b)).symm.trans (hinner v)
    -- Ax-b ∈ range A（一致系统：Ax ∈ range A，b ∈ range A）
    have hax : A x ∈ LinearMap.range (A : E →ₗ[ℝ] F) :=
      LinearMap.mem_range.mpr ⟨x, rfl⟩
    have hsub : (A x - b) ∈ LinearMap.range (A : E →ₗ[ℝ] F) :=
      Submodule.sub_mem (LinearMap.range (A : E →ₗ[ℝ] F)) hax hb
    -- 交为空：range ⊓ orthogonal = ⊥
    have hbot : (A x - b) = 0 := by
      have hmem : (A x - b) ∈
          (LinearMap.range (A : E →ₗ[ℝ] F)) ⊓
          (Submodule.orthogonal (LinearMap.range (A : E →ₗ[ℝ] F))) := by
        exact Submodule.mem_inf.mpr ⟨hsub, horth⟩
      -- 子空间与其正交补的交 = ⊥
      have hdisj : (LinearMap.range (A : E →ₗ[ℝ] F)) ⊓
          (Submodule.orthogonal (LinearMap.range (A : E →ₗ[ℝ] F))) = ⊥ := by
        exact Submodule.inf_orthogonal_eq_bot (LinearMap.range (A : E →ₗ[ℝ] F))
      have : (A x - b) ∈ (⊥ : Submodule ℝ F) := by simpa [hdisj] using hmem
      simpa using this
    -- A x = b
    exact sub_eq_zero.mp hbot
  · intro h
    -- A x = b ⟹ L 在 x 处 fderiv = 0（fderiv_loss_apply：⟨0, Av⟩ = 0）
    rw [fderiv_eq_zero_iff_all (NormSqLoss A b) x (loss_differentiable A b x)]
    intro v
    rw [fderiv_loss_apply A b x v, h]
    simp

end Lattice
