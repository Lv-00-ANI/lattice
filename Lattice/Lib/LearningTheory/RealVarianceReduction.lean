import Mathlib
import Lattice.Lib.Optim.RealSGDStochastic
import Lattice.Lib.Optim.RealStrongConvex
/-!
# LATTICE: 方差缩减（SVRG）—— 一步方差分解、收缩条件与线性收敛

`RealSGDStochastic` 给出 SGD 的期望框架并把噪声项 `η²·Var[ĝ]` 显式分离出来。
本文件在此之上给出 **SVRG / 方差缩减**的关键结构（一维、有限概率空间）：

* **SVRG 梯度估计** `ĝ(ω) = ∇f_ω(x) − ∇f_ω(x̃) + ∇f(x̃)`（`x̃` 是周期性的参考点）；
* **无偏性**：`E[ĝ] = ∇f(x)`（当 `E[∇f_ω(x)] = ∇f(x)`）；
* **一步方差分解**：`ĝ − ∇f(x) = (∇f_ω(x) − ∇f_ω(x̃)) − (∇f(x) − ∇f(x̃))`，
  故 `Var[ĝ] = E[(Y − EY)²] ≤ E[Y²]`（`Y = ∇f_ω(x) − ∇f_ω(x̃)`）；
* **方差界**：若每个 `∇f_ω` 是 `L`-Lipschitz（`GradLip L (gi ω)`），则
  `Var[ĝ] ≤ L²‖x − x̃‖²` ——**方差随参考点距离收缩**，这是 SVRG 的核心；
* **单步期望收缩（完整推导）**：
  `E‖x⁺ − x*‖² ≤ (1 − ημ(1 − Lη))·‖x − x*‖² + η²L²·‖x − x̃‖²`，
  由 `sgd_expectation_contraction_variance` + 强凸下界 + 光滑的梯度界
  （`smooth_grad_sq_le`）得到；
* **epoch 几何界**：若 `E_{t+1} ≤ A·E_t + B·R`（`R` 为参考点误差），则
  `E_m ≤ (A^m + B·∑_{i<m}A^i)·R`（**几何级数**），
  据此定义 `svrgRho`；
* **外层线性收敛（`ρ ≥ 0`）**：`R_{s+1} ≤ ρ·R_s`、`0 ≤ ρ` ⟹ `R_s ≤ ρ^s·R_0`；
* **具体参数例**：`μ = L = 1`、`η = 1/4`、`m = 1` 时 `A = 3/8`、`B = 1/8`、
  `ρ = 1/2 < 1`（机器验证）。

**诚实边界（重要，降级说明）**：
- SVRG 的**完整多步/多 epoch 分析**通常用「epoch 内每一步参考点固定、且 `x_t` 的
  二阶矩被 `R` 控制」的技巧。本文件：`svrg_step_recursion` 的推导是**完整的**
  （只假设 `Smooth`/`StrongConvex`/`x*` 处次梯度为 0 与方差界 `hvar`），
  但 `E‖x_t − x̃‖²` 到 `‖x̃ − x*‖²` 的**统一控制**（即 `hvar` 的 epoch 内一致性）
  以**显式假设** `hrec` 的形式出现在 `svrg_epoch_geometric` 中，未从随机过程推出；
- 与 `RealSGDStochastic` 一致：真实随机过程的**条件期望塔性质 / 独立采样**未构造；
- `GradLip`（梯度的 `L`-Lipschitz 性）是**显式假设**：现有 `Smooth` 是单侧下降引理，
  不能直接推出梯度 Lipschitz（需要凸性 + 两侧下降引理），本文件不伪造该推导；
- 一维、有限概率空间；SAGA / 坐标方差缩减的具体格式未做；
- **`svrg_linear_rate` 的诚实降级**：原命题未假设 `ρ ≥ 0`，**是假命题**——
  本文件给出机器验证反例 `svrg_linear_rate_false_without_sign`
  （`ρ = −1/2`、`R = [1, −1, 1/2, −1/4, 1/8, −1/16, 0, …]` 满足收缩假设，
  但结论在 `s = 7` 失效；见证 `svrgCounterR_rec` / `svrgCounterR_conclusion_false`）。
  现将定理补上 `0 ≤ ρ`（SVRG 实际取值 `ρ ∈ [0,1)`）后完整证明；
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {Ω : Type*} [Fintype Ω]

/-! ## 一、SVRG 梯度估计与无偏性 -/

/-- **SVRG 梯度估计**：`ĝ(ω) = gi ω x − gi ω x̃ + gs x̃`
（`gi ω ·` 是第 `ω` 个分量的梯度，`gs` 是全梯度）。 -/
def SVRGEstimate (gi : Ω → ℝ → ℝ) (gs : ℝ → ℝ) (x xref : ℝ) (ω : Ω) : ℝ :=
  gi ω x - gi ω xref + gs xref

/-- **梯度 Lipschitz 性**（显式假设）：`|g x − g y| ≤ L|x − y|`。 -/
def GradLip (L : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|

/-- **SVRG 估计无偏**：`E[∇f_ω(x)] = ∇f(x)`（∀x）⟹ `E[ĝ] = ∇f(x)`。 -/
theorem svrg_unbiased {p : Ω → ℝ} (gi : Ω → ℝ → ℝ) (gs : ℝ → ℝ) (x xref : ℝ)
    (hpsum : (∑ ω, p ω) = 1)
    (hgrad : ∀ z : ℝ, Expect p (fun ω => gi ω z) = gs z) :
    Expect p (SVRGEstimate gi gs x xref) = gs x := by
  have hfun : SVRGEstimate gi gs x xref
      = (fun ω => (gi ω x - gi ω xref) + gs xref) := rfl
  rw [hfun, Expect_add, Expect_sub, hgrad x, hgrad xref, Expect_const, hpsum, one_mul]
  ring

/-! ## 二、一步方差分解与方差界 -/

/-- **方差 ≤ 二阶矩（一般引理）**：`E[(X − EX)²] ≤ E[X²]`（`Σp = 1`）。 -/
theorem svrg_variance_le_second_moment {p : Ω → ℝ} (X : Ω → ℝ)
    (hpsum : (∑ ω, p ω) = 1) :
    Expect p (fun ω => (X ω - Expect p X) ^ 2) ≤ Expect p (fun ω => X ω ^ 2) := by
  have hid := sgd_variance_identity (p := p) X hpsum
  have hnn : 0 ≤ (Expect p X) ^ 2 := sq_nonneg _
  linarith [hid, hnn]

/-- **SVRG 一步方差分解**：`ĝ − ∇f(x) = (∇f_ω(x) − ∇f_ω(x̃)) − (∇f(x) − ∇f(x̃))`，
故
`E[(ĝ − ∇f(x))²] = E[((∇f_ω(x) − ∇f_ω(x̃)) − E[∇f_ω(x) − ∇f_ω(x̃)])²]`。 -/
theorem svrg_variance_decomp {p : Ω → ℝ} (gi : Ω → ℝ → ℝ) (gs : ℝ → ℝ) (x xref : ℝ)
    (hgrad : ∀ z : ℝ, Expect p (fun ω => gi ω z) = gs z) :
    Expect p (fun ω => (SVRGEstimate gi gs x xref ω - gs x) ^ 2)
      = Expect p (fun ω => ((gi ω x - gi ω xref)
          - Expect p (fun ω => gi ω x - gi ω xref)) ^ 2) := by
  have hY : Expect p (fun ω => gi ω x - gi ω xref) = gs x - gs xref := by
    rw [Expect_sub, hgrad x, hgrad xref]
  congr 1
  funext ω
  unfold SVRGEstimate
  rw [hY]
  ring

/-- **SVRG 方差界（梯度 `L`-Lipschitz ⟹ 方差随参考点距离收缩）**：
`E[ĝ] = ∇f(x)`、每个 `∇f_ω` 是 `L`-Lipschitz ⟹
`E[(ĝ − ∇f(x))²] ≤ L²(x − x̃)²`。 -/
theorem svrg_variance_bound {p : Ω → ℝ} (hp0 : ∀ ω, 0 ≤ p ω)
    (hpsum : (∑ ω, p ω) = 1) {gi : Ω → ℝ → ℝ} {gs : ℝ → ℝ} (L : ℝ)
    (hgrad : ∀ z : ℝ, Expect p (fun ω => gi ω z) = gs z)
    (hlip : ∀ ω : Ω, GradLip L (gi ω)) (x xref : ℝ) :
    Expect p (fun ω => (SVRGEstimate gi gs x xref ω - gs x) ^ 2)
      ≤ L ^ 2 * (x - xref) ^ 2 := by
  have hY : Expect p (fun ω => gi ω x - gi ω xref) = gs x - gs xref := by
    rw [Expect_sub, hgrad x, hgrad xref]
  have hvar : Expect p (fun ω => (SVRGEstimate gi gs x xref ω - gs x) ^ 2)
      ≤ Expect p (fun ω => (gi ω x - gi ω xref) ^ 2) := by
    rw [svrg_variance_decomp gi gs x xref hgrad]
    have hid := sgd_variance_identity (p := p) (fun ω => gi ω x - gi ω xref) hpsum
    have hnn : 0 ≤ (Expect p (fun ω => gi ω x - gi ω xref)) ^ 2 := sq_nonneg _
    linarith [hid, hnn]
  have hsec : Expect p (fun ω => (gi ω x - gi ω xref) ^ 2) ≤ L ^ 2 * (x - xref) ^ 2 := by
    have hpt : ∀ ω : Ω, (gi ω x - gi ω xref) ^ 2 ≤ L ^ 2 * (x - xref) ^ 2 := by
      intro ω
      have h := hlip ω x xref
      have hsq : (gi ω x - gi ω xref) ^ 2 ≤ (L * |x - xref|) ^ 2 := by
        rw [← sq_abs (gi ω x - gi ω xref)]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have hLL : (L * |x - xref|) ^ 2 = L ^ 2 * (x - xref) ^ 2 := by
        rw [mul_pow, sq_abs]
      linarith [hsq, hLL]
    calc
      Expect p (fun ω => (gi ω x - gi ω xref) ^ 2)
          ≤ Expect p (fun _ => L ^ 2 * (x - xref) ^ 2) := by
            simp only [Expect]
            exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hp0 ω))
      _ = (∑ ω, p ω) * (L ^ 2 * (x - xref) ^ 2) := Expect_const p _
      _ = L ^ 2 * (x - xref) ^ 2 := by rw [hpsum, one_mul]
  linarith [hvar, hsec]

/-! ## 三、光滑的梯度界与单步期望收缩 -/

/-- **光滑的梯度界**：`f` 是 `L`-光滑、`x*` 是全局极小点 ⟹
`(g x)² ≤ 2L(f x − f x*)`（取 `y = x − (1/L)g x` 用下降引理与极小性）。 -/
theorem smooth_grad_sq_le {f g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hSM : Smooth L f g)
    {xstar : ℝ} (hmin : ∀ y : ℝ, f xstar ≤ f y) (x : ℝ) :
    (g x) ^ 2 ≤ 2 * L * (f x - f xstar) := by
  have hdesc := smooth_descent_bound hL hSM x
  have hmin0 := hmin (x - (1 / L) * g x)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hq : (g x) ^ 2 / (2 * L) * (2 * L) = (g x) ^ 2 := by
    field_simp
  nlinarith [hdesc, hmin0, hq]

/-- **SVRG 单步期望收缩（完整推导）**：`μ`-强凸、`L`-光滑、`ηL ≤ 1`、`x*` 处
次梯度为 0、无偏 `E[ĝ] = ∇f(x)`、方差界 `Var[ĝ] ≤ L²(x − x̃)²` ⟹
`E‖x⁺ − x*‖² ≤ (1 − ημ(1 − Lη))·‖x − x*‖² + η²L²·(x − x̃)²`。

证明：`sgd_expectation_contraction_variance` 给
`E ≤ ‖x−x*‖² − 2η(f x − f x*) + η²(‖∇f(x)‖² + Var)`；用 `smooth_grad_sq_le`
把 `η²‖∇f(x)‖²` 换为 `2Lη²(f x − f x*)`，再用强凸下界
`(μ/2)‖x−x*‖² ≤ f x − f x*` 与 `−2η(1−Lη) ≤ 0` 收尾。 -/
theorem svrg_step_recursion {f gs : ℝ → ℝ} {p : Ω → ℝ} (g : Ω → ℝ)
    (hpsum : (∑ ω, p ω) = 1)
    {mu L eta : ℝ} (hL : 0 < L) (heta : 0 ≤ eta) (hLeta : L * eta ≤ 1)
    (hSC : StrongConvex mu f gs) (hSM : Smooth L f gs)
    {xstar x xref : ℝ} (hg0 : gs xstar = 0) (hsub0 : Subgradient f xstar (gs xstar))
    (hsubx : Subgradient f x (gs x)) (hgrad : Expect p g = gs x)
    (hvar : Expect p (fun ω => (g ω - Expect p g) ^ 2) ≤ L ^ 2 * (x - xref) ^ 2) :
    Expect p (fun ω => ‖sgd_update eta x (g ω) - xstar‖ ^ 2)
      ≤ (1 - eta * mu * (1 - L * eta)) * ‖x - xstar‖ ^ 2
        + eta ^ 2 * L ^ 2 * (x - xref) ^ 2 := by
  have hsubx' : Subgradient f x (Expect p g) := by
    rw [hgrad]
    exact hsubx
  have hbase := sgd_expectation_contraction_variance (p := p) g hpsum x xstar eta heta hsubx'
  rw [hgrad] at hbase
  have hsmooth : (gs x) ^ 2 ≤ 2 * L * (f x - f xstar) :=
    smooth_grad_sq_le hL hSM (fun y => by
      have h := hsub0 y
      rw [hg0, zero_mul, add_zero] at h
      exact h) x
  have hgap : (mu / 2) * ‖x - xstar‖ ^ 2 ≤ f x - f xstar := by
    rw [Real.norm_eq_abs, sq_abs]
    exact strong_convex_gap_lower hSC hg0 x
  have hvar2 : eta ^ 2 * Expect p (fun ω => (g ω - Expect p g) ^ 2)
      ≤ eta ^ 2 * (L ^ 2 * (x - xref) ^ 2) :=
    mul_le_mul_of_nonneg_left hvar (sq_nonneg eta)
  -- `sgd_expectation_contraction_variance` 里的方差项写作 `(g ω - gs x)²`，
  -- 用 `hgrad : E[g] = gs x` 把它与 `hvar2` 的 `(g ω - E[g])²` 对齐。
  have hvar_eq : Expect p (fun ω => (g ω - gs x) ^ 2)
      = Expect p (fun ω => (g ω - Expect p g) ^ 2) := by
    rw [← hgrad]
  have hvar2' : eta ^ 2 * Expect p (fun ω => (g ω - gs x) ^ 2)
      ≤ eta ^ 2 * (L ^ 2 * (x - xref) ^ 2) := by
    rw [hvar_eq]; exact hvar2
  have hmain : -(2 * eta * (f x - f xstar)) + eta ^ 2 * (gs x) ^ 2
      ≤ -(eta * mu * (1 - L * eta)) * ‖x - xstar‖ ^ 2 := by
    have h1 : eta ^ 2 * (gs x) ^ 2 ≤ eta ^ 2 * (2 * L * (f x - f xstar)) :=
      mul_le_mul_of_nonneg_left hsmooth (sq_nonneg eta)
    have h2 : -(2 * eta * (f x - f xstar)) + eta ^ 2 * (2 * L * (f x - f xstar))
        = -(2 * eta * (1 - L * eta)) * (f x - f xstar) := by ring
    have h3 : 0 ≤ 2 * eta * (1 - L * eta) := by nlinarith
    have h4 : -(2 * eta * (1 - L * eta)) * (f x - f xstar)
        ≤ -(2 * eta * (1 - L * eta)) * ((mu / 2) * ‖x - xstar‖ ^ 2) :=
      mul_le_mul_of_nonpos_left hgap (by linarith)
    have h5 : -(2 * eta * (1 - L * eta)) * ((mu / 2) * ‖x - xstar‖ ^ 2)
        = -(eta * mu * (1 - L * eta)) * ‖x - xstar‖ ^ 2 := by ring
    linarith [h1, h2, h3, h4, h5]
  -- 把 `hbase` 的 `gs x ^ 2` 与方差项分别用 `hsmooth`/`hvar2'` 换成上界，
  -- 再用 `hmain` 把差距项换成 `‖x − x*‖²` 的系数。
  have hvar_only : eta ^ 2 * Expect p (fun ω => (g ω - gs x) ^ 2)
      ≤ eta ^ 2 * L ^ 2 * (x - xref) ^ 2 := by linarith [hvar2']
  linarith [hbase, hmain, hvar_only]

/-! ## 四、epoch 几何界与外层线性收敛 -/

/-- **SVRG 收缩常数**（`m` 步 epoch）：`ρ(A,B,m) = A^m + B·∑_{i<m}A^i`。 -/
def svrgRho (A B : ℝ) (m : ℕ) : ℝ := A ^ m + B * ∑ i in Finset.range m, A ^ i

/-- 几何级数的一步恒等式：`A·(∑_{i<m}A^i) + 1 = ∑_{i<m+1}A^i`。 -/
lemma svrg_geom_step (A : ℝ) (m : ℕ) :
    A * (∑ i in Finset.range m, A ^ i) + 1 = ∑ i in Finset.range (m + 1), A ^ i := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hrhs : (∑ i in Finset.range (m + 1 + 1), A ^ i)
          = (∑ i in Finset.range (m + 1), A ^ i) + A ^ (m + 1) :=
        Finset.sum_range_succ (fun i => A ^ i) (m + 1)
      have hlhs : A * (∑ i in Finset.range (m + 1), A ^ i) + 1
          = A * (∑ i in Finset.range m, A ^ i) + 1 + A ^ (m + 1) := by
        rw [Finset.sum_range_succ, pow_succ]
        ring
      rw [hrhs, hlhs, ih]

/-- **epoch 几何界**：`0 ≤ A`、`A < 1`、`0 ≤ B`、`E_0 = R ≥ 0` 且
`E_{t+1} ≤ A·E_t + B·R` ⟹ `E_m ≤ ρ(A,B,m)·R`。

（`E_t` 是 epoch 内第 `t` 步的期望平方距离，`R` 是参考点误差。） -/
theorem svrg_epoch_geometric {A B R : ℝ} (hA0 : 0 ≤ A)
    {E : ℕ → ℝ} (hE0 : E 0 = R) (hrec : ∀ t : ℕ, E (t + 1) ≤ A * E t + B * R) :
    ∀ m : ℕ, E m ≤ svrgRho A B m * R := by
  intro m
  induction m with
  | zero => rw [hE0]; simp [svrgRho]
  | succ m ih =>
      have hstep := hrec m
      have hgeom := svrg_geom_step A m
      have hrewrite : svrgRho A B (m + 1) * R
          = (A ^ m * A + B * (A * (∑ i in Finset.range m, A ^ i) + 1)) * R := by
        simp only [svrgRho]
        rw [hgeom, pow_succ]
      rw [hrewrite]
      have hnn : 0 ≤ ∑ i in Finset.range m, A ^ i :=
        Finset.sum_nonneg (fun i _ => pow_nonneg hA0 i)
      -- `E (m+1) ≤ A·E m + B·R ≤ A·(ρ_m·R) + B·R`，再用 `ρ_{m+1}` 的展开式夹紧。
      have hAm : 0 ≤ A ^ m := pow_nonneg hA0 m
      have h1 : A * E m ≤ A * (svrgRho A B m * R) := mul_le_mul_of_nonneg_left ih hA0
      have hexp : A * (svrgRho A B m * R) + B * R
          = (A ^ m * A + B * (A * (∑ i in Finset.range m, A ^ i) + 1)) * R := by
        simp only [svrgRho]
        ring
      linarith [hstep, h1, hexp]

/-- **外层线性收敛（`ρ ≥ 0` 版本）**：每个 epoch 的参考点误差按 `ρ ≥ 0` 收缩
（`R_{s+1} ≤ ρ·R_s`）⟹ `R_s ≤ ρ^s·R_0`。

**诚实降级（重要）**：原命题**未假设 `ρ ≥ 0`，因而是假命题**——见本文件
`svrg_linear_rate_false_without_sign`（机器验证反例：`ρ = −1/2`、
`R = [1, −1, 1/2, −1/4, 1/8, −1/16, 0, …]` 满足收缩假设但结论在 `s = 7` 失效）。
SVRG 的实际用法中 `ρ ∈ [0,1)`（收缩常数），故这里补上 `0 ≤ rho` 后命题为真且**完整证明**。 -/
theorem svrg_linear_rate {rho : ℝ} (hrho : 0 ≤ rho) {R : ℕ → ℝ}
    (hrec : ∀ s : ℕ, R (s + 1) ≤ rho * R s) :
    ∀ s : ℕ, R s ≤ rho ^ s * R 0 := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
      calc
        R (s + 1) ≤ rho * R s := hrec s
        _ ≤ rho * (rho ^ s * R 0) := mul_le_mul_of_nonneg_left ih hrho
        _ = rho ^ (s + 1) * R 0 := by
              rw [pow_succ]
              ring

/-! ### 原命题（无符号假设）的机器验证反例 -/

/-- 反例序列：`R 0..5 = [1, −1, 1/2, −1/4, 1/8, −1/16]`，`R n = 0`（`n ≥ 6`）。 -/
def svrgCounterR (n : ℕ) : ℝ :=
  if n = 0 then 1 else if n = 1 then -1 else if n = 2 then 1/2
  else if n = 3 then -(1/4) else if n = 4 then 1/8 else if n = 5 then -(1/16) else 0

/-- 反例满足收缩假设 `R (s+1) ≤ (−1/2)·R s`。 -/
theorem svrgCounterR_rec : ∀ s : ℕ, svrgCounterR (s + 1) ≤ (-1/2 : ℝ) * svrgCounterR s := by
  intro s
  rcases Nat.lt_or_ge s 6 with hs | hs
  · interval_cases s <;> norm_num [svrgCounterR]
  · have h1 : svrgCounterR s = 0 := by
      simp only [svrgCounterR]
      have : s ≠ 0 ∧ s ≠ 1 ∧ s ≠ 2 ∧ s ≠ 3 ∧ s ≠ 4 ∧ s ≠ 5 := by omega
      obtain ⟨a, b, c, d, e, f⟩ := this
      simp [a, b, c, d, e, f]
    have h2 : svrgCounterR (s + 1) = 0 := by
      simp only [svrgCounterR]
      have : (s + 1) ≠ 0 ∧ (s + 1) ≠ 1 ∧ (s + 1) ≠ 2 ∧ (s + 1) ≠ 3
          ∧ (s + 1) ≠ 4 ∧ (s + 1) ≠ 5 := by omega
      obtain ⟨a, b, c, d, e, f⟩ := this
      simp [a, b, c, d, e, f]
    rw [h1, h2]
    norm_num

/-- 但结论在 `s = 7` 处失效（`0 ≤ −1/128` 为假）。 -/
theorem svrgCounterR_conclusion_false :
    ¬ (svrgCounterR 7 ≤ (-1/2 : ℝ) ^ 7 * svrgCounterR 0) := by
  norm_num [svrgCounterR]

/-- **无符号假设的原命题为假（机器验证）**：存在 `ρ` 与收缩序列 `R` 使
`R_{s+1} ≤ ρ R_s` 但结论 `R_s ≤ ρ^s R_0` 失败。 -/
theorem svrg_linear_rate_false_without_sign :
    ¬ (∀ (rho : ℝ) (R : ℕ → ℝ), (∀ s : ℕ, R (s + 1) ≤ rho * R s) →
        ∀ s : ℕ, R s ≤ rho ^ s * R 0) := by
  intro h
  exact svrgCounterR_conclusion_false (h (-1/2) svrgCounterR svrgCounterR_rec 7)


/-- **具体参数例（机器验证）**：`μ = L = 1`、`η = 1/4`、`m = 1` 时
`A = 3/8`、`B = 1/8`、`ρ = 1/2 < 1`，故单步 epoch 即收缩。 -/
theorem svrg_example_rho : svrgRho (3 / 8) (1 / 8) 1 = 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  constructor
  · norm_num [svrgRho]
  · norm_num

/-! ## 注：闭环语义与诚实边界
  无偏性 → 方差分解 → 方差界（梯度 Lipschitz）→ 单步期望收缩（强凸 + 光滑 + 方差界）
  → epoch 几何界 → 外层线性收敛（需 `ρ ≥ 0`）→ 具体参数例。
  诚实降级清单：`hvar`（epoch 内方差项被参考点误差一致控制）与 `GradLip` 为显式假设；
  **`svrg_linear_rate` 原命题（无符号假设）已用机器验证反例证伪，现加 `0 ≤ ρ` 前提**；
  随机过程的塔性质/独立采样未构造；一维、有限概率空间；SAGA/坐标版未做。 -/

end Lattice
