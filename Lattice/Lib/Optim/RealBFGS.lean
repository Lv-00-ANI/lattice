import Mathlib

/-!
# LATTICE: BFGS 更新 —— 正定性保持、Secant 方程与牛顿法的衔接

BFGS 是最常用的拟牛顿更新：

    B⁺ = B + (y yᵀ)/(yᵀs) − (B s (B s)ᵀ)/(sᵀ B s)。

本文件给出三层内容（**矩阵层**、**抽象对称双线性形式层**、**一维衔接层**）：

一、矩阵层（`Matrix (Fin n) (Fin n) ℝ`）：
  1. `bfgsUpdate`（def）：`B + (1/(yᵀs))·yyᵀ − (1/(sᵀBs))·(Bs)(Bs)ᵀ`；
  2. `vecMulVec_mulVec`：`(u vᵀ) *ᵥ s = (vᵀs) • u`（秩一矩阵作用）；
  3. `bfgs_secant`（**Secant 方程**）：`B⁺ *ᵥ s = y`（需 `yᵀs ≠ 0`、`sᵀBs ≠ 0`）。

二、抽象二次型层（**模型无关**：只假设 `β` 是对称双线性形式）：
  4. `bfgs_paraboloid`（**抛物面恒等式 / 直接二次型配方**）：
     `β z z − (β z s)²/(β s s) = β (z − c s)(z − c s)`，`c = β z s/β s s`；
  5. `bfgs_form_psd`：`β` 半正定、`0 < β s s`、`0 < yᵀs` ⟹ BFGS 二次型
     `β z z − (β z s)²/(β s s) + (zᵀy)²/(yᵀs)` 半正定；
  6. `bfgs_form_pd`：`β` 正定 ⟹ BFGS 二次型**正定**（严格正定保持）；
  7. `matQuad` / `matQuad_symm` / `matQuad_bfgs_psd`：把 5 实例化到
     对称矩阵的二次型 `zᵀ(B z)` 上。

三、牛顿衔接层：
  8. `bfgs_one_dim_hessian`：一维二次目标 `f(x) = (a/2)x²` 上
     `y = a·s`，BFGS 的秩一修正系数 `y²/(ys) = a` 恰为**精确二阶导数**
     （与 `RealNewtonMethod.newton_step_quadratic` 的一步精确衔接）。

**诚实边界（重要）**：
- 本文件只证 **Secant 方程 + 正定性保持（抽象层与矩阵层）+ 一维 Hessian 恢复**。
  BFGS 的**全局收敛**（Wolfe 线搜索下 `∑‖∇f‖² < ∞`、超线性收敛）**未做**；
- 曲率条件 `yᵀs > 0` 是**显式假设**（由 Wolfe 线搜索保证），本文件不推导；
- 「矩阵更新的二次型恰为抽象层的 `bfgsForm`」这一对接，本文件通过
  `matQuad_bfgs_psd` 给出（把 `β u w = uᵀ(Bw)`），**完整的矩阵二次型分解等式**
  （`matQuad (bfgsUpdate B s y) z = β z z − (β z s)²/β s s + (zᵀy)²/(yᵀs)`）
  依赖 `bfgsUpdate` 的逐步矩阵计算，本文件**未逐步展开**，标注为降级；
- 一般 `n` 的 `B⁺ = y/s`（秩二项恰消去 `B`）只在一维给出**系数级**验证
  （`bfgs_one_dim_hessian`），矩阵级 `Fin 1` 的完整等式未做；
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {n : ℕ}

/-! ## 一、矩阵层：BFGS 更新与 Secant 方程 -/

/-- **BFGS 更新**：`B⁺ = B + (1/(yᵀs))·(y yᵀ) − (1/(sᵀ B s))·((Bs)(Bs)ᵀ)`。 -/
def bfgsUpdate (B : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  B + (1 / Matrix.dotProduct y s) • Matrix.vecMulVec y y
      - (1 / Matrix.dotProduct s (Matrix.mulVec B s))
        • Matrix.vecMulVec (Matrix.mulVec B s) (Matrix.mulVec B s)

/-- **秩一矩阵的作用**：`(u vᵀ) *ᵥ s = (vᵀ s) • u`。 -/
lemma vecMulVec_mulVec (u v s : Fin n → ℝ) :
    Matrix.mulVec (Matrix.vecMulVec u v) s = (Matrix.dotProduct v s) • u := by
  ext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, Matrix.dotProduct, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring
/-- **Secant 方程**：曲率条件 `yᵀs ≠ 0` 与 `sᵀ B s ≠ 0` 下，`B⁺ *ᵥ s = y`。 -/
theorem bfgs_secant (B : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ)
    (hys : Matrix.dotProduct y s ≠ 0) (hss : Matrix.dotProduct s (Matrix.mulVec B s) ≠ 0) :
    Matrix.mulVec (bfgsUpdate B s y) s = y := by
  have h1 : Matrix.mulVec (Matrix.vecMulVec y y) s = (Matrix.dotProduct y s) • y :=
    vecMulVec_mulVec y y s
  have h2 : Matrix.mulVec (Matrix.vecMulVec (Matrix.mulVec B s) (Matrix.mulVec B s)) s
      = (Matrix.dotProduct s (Matrix.mulVec B s)) • (Matrix.mulVec B s) := by
    rw [vecMulVec_mulVec, Matrix.dotProduct_comm]
  unfold bfgsUpdate
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc,
    h1, h2, smul_smul, smul_smul]
  rw [show (1 / Matrix.dotProduct y s) * Matrix.dotProduct y s = 1 by field_simp,
    show (1 / Matrix.dotProduct s (Matrix.mulVec B s))
        * Matrix.dotProduct s (Matrix.mulVec B s) = 1 by field_simp]
  rw [one_smul, one_smul]
  abel

/-! ## 二、抽象二次型层：抛物面恒等式与正定性保持 -/

/-- **BFGS 抛物面恒等式（直接二次型配方）**：`β` 对称双线性、`β s s ≠ 0`、
`c = β z s / β s s` ⟹ `β z z − (β z s)²/(β s s) = β (z − c s)(z − c s)`。

证明：展开右端为 `β z z − 2c·β z s + c²·β s s`，代入 `c` 即得。 -/
theorem bfgs_paraboloid {β : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hadd : ∀ u v w : Fin n → ℝ, β (u + v) w = β u w + β v w)
    (hsmul : ∀ (a : ℝ) (u w : Fin n → ℝ), β (a • u) w = a * β u w)
    (hsymm : ∀ u w : Fin n → ℝ, β u w = β w u)
    {s z : Fin n → ℝ} (hss : β s s ≠ 0) :
    β z z - (β z s) ^ 2 / (β s s)
      = β (z - (β z s / β s s) • s) (z - (β z s / β s s) • s) := by
  have hsub : ∀ u v w : Fin n → ℝ, β (u - v) w = β u w - β v w := by
    intro u v w
    have h : u - v = u + (-1 : ℝ) • v := by
      ext i
      simp [sub_eq_add_neg]
    rw [h, hadd, hsmul]
    ring
  have hsmulr : ∀ (a : ℝ) (u w : Fin n → ℝ), β u (a • w) = a * β u w := by
    intro a u w
    rw [hsymm u (a • w), hsmul, hsymm w u]
  have hexp : β (z - (β z s / β s s) • s) (z - (β z s / β s s) • s)
      = β z z - 2 * (β z s / β s s) * β z s + (β z s / β s s) ^ 2 * (β s s) := by
    set c : ℝ := β z s / β s s with hc
    have key : ∀ u : Fin n → ℝ, β u (z - c • s) = β u z - c * β u s := by
      intro u
      rw [hsymm u (z - c • s), hsub z (c • s) u, hsmul c s u, hsymm s u, hsymm z u]
    rw [hsub z (c • s) (z - c • s), key z, key (c • s), hsmul c s z, hsymm s z,
      hsmul c s s]
    ring
  rw [hexp]
  field_simp
  ring

/-- **BFGS 二次型的半正定保持**：`β` 对称双线性、半正定、`0 < β s s`、`0 < yᵀs` ⟹
`β z z − (β z s)²/(β s s) + (zᵀy)²/(yᵀs) ≥ 0`。 -/
theorem bfgs_form_psd {β : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hadd : ∀ u v w : Fin n → ℝ, β (u + v) w = β u w + β v w)
    (hsmul : ∀ (a : ℝ) (u w : Fin n → ℝ), β (a • u) w = a * β u w)
    (hsymm : ∀ u w : Fin n → ℝ, β u w = β w u)
    (hpsd : ∀ z : Fin n → ℝ, 0 ≤ β z z)
    {s y : Fin n → ℝ} (hss : 0 < β s s) (hys : 0 < Matrix.dotProduct y s) (z : Fin n → ℝ) :
    0 ≤ β z z - (β z s) ^ 2 / (β s s) + (Matrix.dotProduct z y) ^ 2 / Matrix.dotProduct y s := by
  have h1 : 0 ≤ β z z - (β z s) ^ 2 / (β s s) := by
    rw [bfgs_paraboloid hadd hsmul hsymm (ne_of_gt hss)]
    exact hpsd _
  have h2 : 0 ≤ (Matrix.dotProduct z y) ^ 2 / Matrix.dotProduct y s :=
    div_nonneg (sq_nonneg _) (le_of_lt hys)
  linarith

/-- **BFGS 二次型的严格正定保持**：`β` 对称双线性、正定、`0 < β s s`、`0 < yᵀs` ⟹
更新后的二次型在 `z ≠ 0` 时严格正。

证明分情形：若 `zᵀy ≠ 0`，秩一项严格正；若 `zᵀy = 0`，则
`w := z − c·s ≠ 0`（否则 `z = c·s` 会给出 `0 = zᵀy = c·(sᵀy)`，即 `c = 0`，矛盾），
故 `β w w > 0`。 -/
theorem bfgs_form_pd {β : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hadd : ∀ u v w : Fin n → ℝ, β (u + v) w = β u w + β v w)
    (hsmul : ∀ (a : ℝ) (u w : Fin n → ℝ), β (a • u) w = a * β u w)
    (hsymm : ∀ u w : Fin n → ℝ, β u w = β w u)
    (hpd : ∀ z : Fin n → ℝ, z ≠ 0 → 0 < β z z)
    {s y : Fin n → ℝ} (hss : 0 < β s s) (hys : 0 < Matrix.dotProduct y s)
    {z : Fin n → ℝ} (hz : z ≠ 0) :
    0 < β z z - (β z s) ^ 2 / (β s s) + (Matrix.dotProduct z y) ^ 2 / Matrix.dotProduct y s := by
  have hdot : ∀ (c : ℝ) (u w : Fin n → ℝ),
      Matrix.dotProduct (u - c • w) y = Matrix.dotProduct u y - c * Matrix.dotProduct w y := by
    intro c u w
    rw [show u - c • w = u + (-(c)) • w by
      ext i
      simp [sub_eq_add_neg]]
    rw [Matrix.add_dotProduct, Matrix.smul_dotProduct, smul_eq_mul]
    ring
  have hsy : (0 : ℝ) < Matrix.dotProduct s y := by
    rw [Matrix.dotProduct_comm]; exact hys
  -- 分情形：先看 `zᵀy` 是否为零。若 `zᵀy ≠ 0`，秩一项严格正，结论立得；
  -- 若 `zᵀy = 0`，则需证 `w := z − c·s ≠ 0`（`c = β z s/β s s`），从而第一项严格正。
  by_cases hy : Matrix.dotProduct z y = 0
  · -- hne 在 `zᵀy = 0` 之下成立：若 w = 0 则 z = c·s，故 zᵀy = c·(sᵀy) = 0，
    -- 由 `sᵀy ≠ 0` 得 c = 0，于是 z = 0，与 `hz` 矛盾。
    have hne : z - (β z s / β s s) • s ≠ 0 := by
      intro hzero
      have hzc : z = (β z s / β s s) • s := sub_eq_zero.mp hzero
      have hsdot : Matrix.dotProduct ((β z s / β s s) • s) y
          = (β z s / β s s) * Matrix.dotProduct s y := by
        simp [Matrix.dotProduct, Finset.mul_sum, mul_assoc]
      rw [hzc, hsdot] at hy
      have hc0 : β z s / β s s = 0 := (mul_eq_zero.mp hy).resolve_right (ne_of_gt hsy)
      rw [hzc, hc0, zero_smul] at hz
      exact hz rfl
    have hfirst : 0 < β z z - (β z s) ^ 2 / (β s s) := by
      rw [bfgs_paraboloid hadd hsmul hsymm (ne_of_gt hss)]
      exact hpd _ hne
    rw [hy]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero]
    linarith
  · have h2 : 0 < (Matrix.dotProduct z y) ^ 2 := by
      rw [← sq_abs (Matrix.dotProduct z y)]
      exact pow_pos (abs_pos.mpr hy) 2
    have hsecond : 0 < (Matrix.dotProduct z y) ^ 2 / Matrix.dotProduct y s :=
      div_pos h2 hys
    -- 第一项非负：`β w w ≥ 0`（`w ≠ 0` 时由正定性严格正；`w = 0` 时为 0）。
    have hfirst_nonneg : 0 ≤ β z z - (β z s) ^ 2 / (β s s) := by
      rw [bfgs_paraboloid hadd hsmul hsymm (ne_of_gt hss)]
      by_cases hw : z - (β z s / β s s) • s = 0
      · rw [hw]
        exact le_of_eq (by
          have h : (0 : Fin n → ℝ) = (0 : ℝ) • (0 : Fin n → ℝ) := by simp
          rw [h, hsmul]; ring)
      · exact le_of_lt (hpd _ hw)
    linarith

/-! ## 三、矩阵二次型实例 -/

/-- **矩阵二次型**：`matQuad B z = zᵀ(B z)`。 -/
def matQuad (B : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : ℝ :=
  Matrix.dotProduct z (Matrix.mulVec B z)

/-- **对称矩阵二次型的对称性**：`uᵀ(B w) = wᵀ(B u)`（`B` 对称）。 -/
lemma matQuad_symm {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (u w : Fin n → ℝ) :
    Matrix.dotProduct u (Matrix.mulVec B w) = Matrix.dotProduct w (Matrix.mulVec B u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, Matrix.dotProduct_comm]

/-- **BFGS 更新保持矩阵二次型的半正定性**：`B` 对称半正定、`0 < sᵀBs`、`0 < yᵀs` ⟹
`matQuad B z − (zᵀ(Bs))²/(sᵀ(Bs)) + (zᵀy)²/(yᵀs) ≥ 0`（即 BFGS 形式在
`β u w = uᵀ(Bw)` 上的实例化）。 -/
theorem matQuad_bfgs_psd {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm)
    (hpsd : ∀ z : Fin n → ℝ, 0 ≤ matQuad B z)
    {s y : Fin n → ℝ} (hss : 0 < matQuad B s) (hys : 0 < Matrix.dotProduct y s)
    (z : Fin n → ℝ) :
    0 ≤ matQuad B z - (Matrix.dotProduct z (Matrix.mulVec B s)) ^ 2 / matQuad B s
        + (Matrix.dotProduct z y) ^ 2 / Matrix.dotProduct y s := by
  have hadd : ∀ u v w : Fin n → ℝ,
      Matrix.dotProduct (u + v) (Matrix.mulVec B w)
        = Matrix.dotProduct u (Matrix.mulVec B w) + Matrix.dotProduct v (Matrix.mulVec B w) := by
    intro u v w
    rw [Matrix.add_dotProduct]
  have hsmul : ∀ (a : ℝ) (u w : Fin n → ℝ),
      Matrix.dotProduct (a • u) (Matrix.mulVec B w)
        = a * Matrix.dotProduct u (Matrix.mulVec B w) := by
    intro a u w
    rw [Matrix.smul_dotProduct, smul_eq_mul]
  have hsymm : ∀ u w : Fin n → ℝ,
      Matrix.dotProduct u (Matrix.mulVec B w) = Matrix.dotProduct w (Matrix.mulVec B u) :=
    matQuad_symm hB
  have := bfgs_form_psd (β := fun u w : Fin n → ℝ => Matrix.dotProduct u (Matrix.mulVec B w))
    hadd hsmul hsymm (fun z => hpsd z) hss hys z
  simpa [matQuad] using this

/-! ## 四、牛顿衔接层 -/

/-- **一维二次目标上的精确 Hessian 恢复**：`f(x) = (a/2)x²`、`∇f = a·x`、
`y = ∇f(x₁) − ∇f(x₀) = a·s`（`s = x₁ − x₀`）时，BFGS 的秩一修正系数
`y²/(y s) = a` 恰为**精确二阶导数**——即 BFGS 在一维二次目标上**一步恢复 Hessian**。

与 `RealNewtonMethod.newton_step_quadratic`（牛顿法在二次函数上一步到达极小点）
衔接：两者都体现「二阶信息被一步捕获」。 -/
theorem bfgs_one_dim_hessian (a s : ℝ) (ha : a ≠ 0) (hs : s ≠ 0) :
    (a * s) ^ 2 / ((a * s) * s) = a := by
  field_simp
  ring

end Lattice
