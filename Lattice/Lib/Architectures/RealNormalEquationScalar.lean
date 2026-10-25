import Mathlib

/-!
# LATTICE: P0 一般法方程（𝕜 版）—— 任意 RCLike 域内积空间上的驻点 ⟺ 满足

RealNormalEquation（ℝ 法方程）的**域参数化**：把 ℝ 推广到任意 RCLike 域 𝕜
（ℝ/ℂ/p-adic 闭包等）。平方损失 L(x) = ‖A·x - b‖² 在**实化结构**下：

  fderiv ℝ L x v = 2 · re⟨Ax - b, A v⟩      （方向导数，re 是 𝕜 的实部）

且（一致系统 b ∈ range A）：
  fderiv ℝ L x = 0  ⟺  A x = b              （驻点 ⟺ 满足）

证明要点：
  1. norm² 沿实直线导数 = 2·re⟨u,w⟩（norm_add_sq 的 𝕜 形式）；
  2. 方向导数桥 fderiv_apply（不需要内积）；
  3. re⟨r, Av⟩ = 0 且 re⟨r, A(I·v)⟩ = 0 ⟹ ⟨r, Av⟩ = 0（re/im 分解，
     用到 RCLike 的虚单位 I 与 conj_I）；
  4. range ⊓ orthogonal = ⊥（与 ℝ 版相同，mathlib 已泛化到 RCLike 𝕜）。

为什么是「实化」驻点而非 𝕜-驻点：‖·‖² 对 ℂ 不是全纯函数（含共轭），
𝕜-全纯导数不存在；训练/损失最小化本质上是实优化，实化 fderiv ℝ 正是
真实驻点概念。ℝ 域时本定理退化为 ℝ 版法方程。

模型无关：任意 RCLike 𝕜、任意 𝕜-内积空间（含 ℝ-实化假设，ℝ 时自动满足）。
-/

noncomputable section

open Filter
open scoped Topology ComplexConjugate

namespace Lattice

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-! mathlib 4.14 中 ⟪x, y⟫ 是作用域内记法（仅 ℝ/ℂ 有裸记法），
此处为任意 RCLike 𝕜 声明本地记法（与 mathlib 内部做法一致）。-/
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-! ## 平方损失的范数形式（𝕜-线性算子） -/

def NormSqLossScalar (A : E →L[𝕜] F) (b : F) (x : E) : ℝ := ‖A x - b‖ ^ 2

/-! ## 引理一：范数平方沿实直线的导数（𝕜 版）
d/dt [‖u + t·w‖²]₀ = 2·re⟨u, w⟩。-/

omit [CompleteSpace F] in
lemma norm_sq_line_deriv_scalar (u w : F) :
    deriv (fun t : ℝ => ‖u + t • w‖ ^ 2) 0 = 2 * RCLike.re ⟪u, w⟫ := by
  -- ‖u + t·w‖² = ‖u‖² + 2t·re⟨u,w⟩ + t²‖w‖²（norm_add_sq 的 𝕜 形式）
  have hnorm : ∀ t : ℝ, ‖u + t • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * t * RCLike.re ⟪u, w⟫ + t ^ 2 * ‖w‖ ^ 2 := by
    intro t
    calc
      ‖u + t • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * RCLike.re ⟪u, t • w⟫ + ‖t • w‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := 𝕜)]
      _ = ‖u‖ ^ 2 + 2 * RCLike.re ⟪u, (t : 𝕜) • w⟫ + ‖t • w‖ ^ 2 := by
        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
      _ = ‖u‖ ^ 2 + 2 * RCLike.re ((t : 𝕜) * ⟪u, w⟫) + ‖t • w‖ ^ 2 := by
        rw [inner_smul_right]
      _ = ‖u‖ ^ 2 + 2 * (t * RCLike.re ⟪u, w⟫) + ‖t • w‖ ^ 2 := by
        rw [RCLike.re_ofReal_mul]
      _ = ‖u‖ ^ 2 + 2 * (t * RCLike.re ⟪u, w⟫) + (t ^ 2 * ‖w‖ ^ 2) := by
        -- ‖t • w‖² = (|t|·‖w‖)² = t²·‖w‖²
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      _ = ‖u‖ ^ 2 + 2 * t * RCLike.re ⟪u, w⟫ + t ^ 2 * ‖w‖ ^ 2 := by ring
  -- 导数线性性：常数 0 + 2·re⟨u,w⟩ + 0（多项式求导）
  have hpoly : deriv (fun t : ℝ => ‖u‖ ^ 2 + 2 * t * RCLike.re ⟪u, w⟫ + t ^ 2 * ‖w‖ ^ 2) 0
      = 2 * RCLike.re ⟪u, w⟫ := by
    have hlin : HasDerivAt (fun t : ℝ => 2 * t * RCLike.re ⟪u, w⟫)
        (2 * RCLike.re ⟪u, w⟫) 0 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (hasDerivAt_id 0).const_mul (2 * RCLike.re ⟪u, w⟫)
    have hquad : HasDerivAt (fun t : ℝ => t ^ 2 * ‖w‖ ^ 2) 0 0 := by
      simpa using ((hasDerivAt_id 0).pow 2).mul_const (‖w‖ ^ 2)
    have hsum : HasDerivAt (fun t : ℝ => 2 * t * RCLike.re ⟪u, w⟫ + t ^ 2 * ‖w‖ ^ 2)
        (2 * RCLike.re ⟪u, w⟫) 0 := by
      simpa using hlin.add hquad
    have hfull : HasDerivAt (fun t : ℝ => ‖u‖ ^ 2 + 2 * t * RCLike.re ⟪u, w⟫ + t ^ 2 * ‖w‖ ^ 2)
        (2 * RCLike.re ⟪u, w⟫) 0 := by
      simpa [add_assoc] using hsum.const_add (‖u‖ ^ 2)
    exact hfull.deriv
  calc
    deriv (fun t : ℝ => ‖u + t • w‖ ^ 2) 0
        = deriv (fun t : ℝ => ‖u‖ ^ 2 + 2 * t * RCLike.re ⟪u, w⟫ + t ^ 2 * ‖w‖ ^ 2) 0 := by
          exact congrArg (fun g : ℝ → ℝ => deriv g 0) (funext hnorm)
    _ = 2 * RCLike.re ⟪u, w⟫ := hpoly

/-! ## 引理二：L 处处可导（实化）
A·-b 可导（ℝ 限制），norm² 是 C∞（无需内积），复合可导。-/

omit [CompleteSpace E] [CompleteSpace F] in
lemma loss_differentiable_scalar (A : E →L[𝕜] F) (b : F) :
    ∀ x : E, DifferentiableAt ℝ (NormSqLossScalar A b) x := by
  intro x
  -- A·x - b 可导（ℝ-限制线性 + 常数），norm² 可导，复合可导
  have hlin : DifferentiableAt ℝ (fun y : E => A y - b) x := by
    simpa using ((A.restrictScalars ℝ).differentiableAt).sub (differentiableAt_const b)
  simpa [NormSqLossScalar] using hlin.norm_sq 𝕜

/-! ## 引理三：方向导数 = fderiv 作用（桥） -/

omit [CompleteSpace E] in
lemma fderiv_apply_direction_scalar {f : E → ℝ} {x v : E}
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

/-! ## 引理四：fderiv L x v = 2·re⟨Ax-b, A v⟩ -/

omit [CompleteSpace E] [CompleteSpace F] in
lemma fderiv_loss_apply_scalar (A : E →L[𝕜] F) (b : F) (x v : E) :
    fderiv ℝ (NormSqLossScalar A b) x v = 2 * RCLike.re ⟪A x - b, A v⟫ := by
  -- 桥：方向导数
  have hg : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt (NormSqLossScalar A b) (fderiv ℝ (NormSqLossScalar A b) x) (x + (0 : ℝ) • v) := by
    have hx : x + (0 : ℝ) • v = x := by simp
    rw [hx]
    exact (loss_differentiable_scalar A b x).hasFDerivAt
  have hdir : fderiv ℝ (NormSqLossScalar A b) x v = deriv (fun t : ℝ => NormSqLossScalar A b (x + t • v)) 0 := by
    exact (hf'.comp_hasDerivAt 0 hg).deriv.symm
  rw [hdir]
  -- L(x + t·v) = ‖(Ax-b) + t·(Av)‖²
  have hL : ∀ t : ℝ, NormSqLossScalar A b (x + t • v) = ‖(A x - b) + t • (A v)‖ ^ 2 := by
    intro t
    have harg : A (x + t • v) - b = (A x - b) + t • A v := by
      calc
        A (x + t • v) - b = (A x + A (t • v)) - b := by rw [A.map_add]
        _ = (A x + t • A v) - b := by
          -- t • v 是 ℝ 作用，A 是 𝕜-线性：A (t • v) = t • A v
          have hsmul : A (t • v) = t • A v := by
            calc
              A (t • v) = A ((t : 𝕜) • v) := by rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
              _ = (t : 𝕜) • A v := A.map_smul (t : 𝕜) v
              _ = t • A v := by rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
          rw [hsmul]
        _ = (A x - b) + t • A v := by abel
    unfold NormSqLossScalar
    rw [harg]
  calc
    deriv (fun t : ℝ => NormSqLossScalar A b (x + t • v)) 0
        = deriv (fun t : ℝ => ‖(A x - b) + t • (A v)‖ ^ 2) 0 := by
          exact congrArg (fun g : ℝ → ℝ => deriv g 0) (funext hL)
    _ = 2 * RCLike.re ⟪A x - b, A v⟫ := norm_sq_line_deriv_scalar (A x - b) (A v)

/-! ## 引理五：fderiv 为零 ⟺ 对一切 v 方向导数为零 -/

omit [CompleteSpace E] in
lemma fderiv_eq_zero_iff_all_scalar (f : E → ℝ) (x : E) (_hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x = 0 ↔ ∀ v : E, fderiv ℝ f x v = 0 := by
  constructor
  · intro h v
    rw [h]
    simp
  · intro h
    -- 线性映射为零：ext v
    ext v
    simpa using h v

/-! ## 引理六：re/im 分解 —— re(-I·z) = im z -/

lemma re_neg_I_mul (z : 𝕜) : RCLike.re (-(RCLike.I : 𝕜) * z) = RCLike.im z := by
  calc
    RCLike.re (-(RCLike.I : 𝕜) * z) = RCLike.re (-((RCLike.I : 𝕜) * z)) := by rw [neg_mul]
    _ = -RCLike.re ((RCLike.I : 𝕜) * z) := by simp
    _ = -(RCLike.re (RCLike.I : 𝕜) * RCLike.re z - RCLike.im (RCLike.I : 𝕜) * RCLike.im z) := by
      rw [RCLike.mul_re]
    _ = RCLike.im (RCLike.I : 𝕜) * RCLike.im z := by simp [RCLike.I_re]
    _ = RCLike.im z := by
      rw [mul_comm]
      exact RCLike.I_im z

/-! ## 引理七：正交补条件（𝕜 版）
re⟨x, Av⟩ = 0（∀v）且 re⟨x, A(I·v)⟩ = 0（∀v）⟹ x ∈ (range A)ᗮ。
re 与 im 两个分量都为零 ⟹ ⟨x, Av⟩ = 0（RCLike.ext）。-/

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
lemma mem_orthogonal_range_scalar {x : F} {A : E →L[𝕜] F}
    (h : ∀ v : E, RCLike.re ⟪x, A v⟫ = 0) :
    x ∈ (Submodule.orthogonal (LinearMap.range (A : E →ₗ[𝕜] F))) := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  rcases (LinearMap.mem_range.mp hy) with ⟨v, rfl⟩
  -- ⟨x, A v⟩ = 0：re = 0 且 im = 0
  apply RCLike.ext
  · -- re ⟨x, A v⟩ = 0
    simpa using h v
  · -- im ⟨x, A v⟩ = 0：re ⟨x, A (I · v)⟩ = 0 给出虚部
    have hreI : RCLike.re ⟪x, A ((RCLike.I : 𝕜) • v)⟫ = 0 := h ((RCLike.I : 𝕜) • v)
    have him_of_reI : RCLike.im ⟪x, A v⟫ = -(RCLike.re ⟪x, A ((RCLike.I : 𝕜) • v)⟫) := by
      calc
        RCLike.im ⟪x, A v⟫ = RCLike.re (-(RCLike.I : 𝕜) * ⟪x, A v⟫) := (re_neg_I_mul ⟪x, A v⟫).symm
        _ = RCLike.re (-((RCLike.I : 𝕜) * ⟪x, A v⟫)) := by rw [neg_mul]
        _ = RCLike.re (-⟪x, (RCLike.I : 𝕜) • A v⟫) := by rw [← inner_smul_right]
        _ = -RCLike.re ⟪x, (RCLike.I : 𝕜) • A v⟫ := by simp
        _ = -RCLike.re ⟪x, A ((RCLike.I : 𝕜) • v)⟫ := by rw [← A.map_smul]
    simpa [him_of_reI] using hreI

/-! ## 定理：P0 一般法方程（𝕜 版）—— 实化驻点 ⟺ 满足（一致系统） -/

omit [CompleteSpace E] [CompleteSpace F] in
theorem P0_normal_equation_scalar (A : E →L[𝕜] F) (b : F) (x : E)
    (hb : b ∈ LinearMap.range (A : E →ₗ[𝕜] F)) :
    fderiv ℝ (NormSqLossScalar A b) x = 0 ↔ A x = b := by
  constructor
  · intro hfd
    -- fderiv = 0 ⟹ 所有方向导数（re 分量）为 0
    have hall : ∀ v : E, 2 * RCLike.re ⟪A x - b, A v⟫ = 0 := by
      intro v
      have hlin : fderiv ℝ (NormSqLossScalar A b) x v = 0 :=
        (fderiv_eq_zero_iff_all_scalar (NormSqLossScalar A b) x (loss_differentiable_scalar A b x)).mp hfd v
      rwa [fderiv_loss_apply_scalar A b x v] at hlin
    -- 2·re⟨r, Av⟩ = 0 ⟹ re⟨r, Av⟩ = 0
    have hre : ∀ v : E, RCLike.re ⟪A x - b, A v⟫ = 0 := by
      intro v
      exact (mul_eq_zero.mp (hall v)).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    -- Ax-b ∈ (range A)ᗮ
    have horth : (A x - b) ∈ (Submodule.orthogonal (LinearMap.range (A : E →ₗ[𝕜] F))) :=
      mem_orthogonal_range_scalar hre
    -- Ax-b ∈ range A（一致系统：Ax ∈ range A，b ∈ range A）
    have hax : A x ∈ LinearMap.range (A : E →ₗ[𝕜] F) :=
      LinearMap.mem_range.mpr ⟨x, rfl⟩
    have hsub : (A x - b) ∈ LinearMap.range (A : E →ₗ[𝕜] F) :=
      Submodule.sub_mem (LinearMap.range (A : E →ₗ[𝕜] F)) hax hb
    -- 交为空：range ⊓ orthogonal = ⊥
    have hbot : (A x - b) = 0 := by
      have hmem : (A x - b) ∈
          (LinearMap.range (A : E →ₗ[𝕜] F)) ⊓
          (Submodule.orthogonal (LinearMap.range (A : E →ₗ[𝕜] F))) := by
        exact Submodule.mem_inf.mpr ⟨hsub, horth⟩
      -- 子空间与其正交补的交 = ⊥（mathlib 泛化到 RCLike 𝕜）
      have hdisj : (LinearMap.range (A : E →ₗ[𝕜] F)) ⊓
          (Submodule.orthogonal (LinearMap.range (A : E →ₗ[𝕜] F))) = ⊥ := by
        exact Submodule.inf_orthogonal_eq_bot (LinearMap.range (A : E →ₗ[𝕜] F))
      have : (A x - b) ∈ (⊥ : Submodule 𝕜 F) := by simpa [hdisj] using hmem
      simpa using this
    -- A x = b
    exact sub_eq_zero.mp hbot
  · intro h
    -- A x = b ⟹ L 在 x 处 fderiv = 0（方向导数公式：⟨0, Av⟩ 的 re 为 0）
    rw [fderiv_eq_zero_iff_all_scalar (NormSqLossScalar A b) x (loss_differentiable_scalar A b x)]
    intro v
    rw [fderiv_loss_apply_scalar A b x v, h]
    simp

/-! ## 注：ℝ 退化
𝕜 = ℝ 时：I = 0（RCLike 的 I 字段在 ℝ 取 0），re = id，im = 0，
real_smul_eq_coe_smul 退化为恒等，IsScalarTower ℝ ℝ E 平凡成立；
本定理即 RealNormalEquation（ℝ 法方程）的精确复述——ℝ 版是其特例。-/

end Lattice
