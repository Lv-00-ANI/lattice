import Mathlib
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Convex.RealSubgradient
import Lattice.Lib.Convex.RealSubgradientDescent
/-!
# LATTICE: 强凸 / 光滑下的加速收敛率 —— GD 的线性收敛与极小点唯一性

RealConvergence 给出抽象收缩骨架（e(n+1) ≤ c·e(n) ⟹ ε-终止）；
RealSubgradientDescent 给出非光滑凸的 O(1/√T) 次线性率。本文件补齐**光滑强凸**
一侧：梯度下降获得**几何（线性）收敛率**。

一维模型（与 RealSubgradientDescent 同口径），梯度选择 g : ℝ → ℝ，
两条标准一阶假设（带显式梯度选择，避免引入微分结构）：

  · **StrongConvex μ f g**（μ-强凸，等价于 f − (μ/2)‖·‖² 凸）：
      ∀ x y, f y ≥ f x + g x·(y − x) + (μ/2)(y − x)²；
  · **Smooth L f g**（L-光滑，下降引理形式）：
      ∀ x y, f y ≤ f x + g x·(y − x) + (L/2)(y − x)²。

链条：
  1. `strong_convex_gap_lower`：(μ/2)‖x − x*‖² ≤ f x − f x*（强凸的下界）；
  2. `strong_convex_gap_bound`：f x − f x* ≤ (L/2)‖x − x*‖²（光滑的上界，任务目标）；
  3. `strong_convex_minimizer` / `strong_convex_unique_min`：g x* = 0 ⟹ x* 是极小点，
     且 μ > 0 时**极小点唯一**；
  4. `strong_convex_gap_le_grad_sq`：gap ≤ ‖g x‖²/(2μ)（强凸的梯度-差距界，配平方）；
  5. `smooth_descent_bound`：步长 η = 1/L 的单步下降
     f(x − (1/L)g x) − f x ≤ −‖g x‖²/(2L)；
  6. `strong_convex_contraction`（主定理，函数值/Lyapunov 形式）：
     0 < μ ≤ L ⟹ gap(x − (1/L)g x) ≤ (1 − μ/L)·gap(x)，
     即收缩系数恰为 **(1 − μη)**（η = 1/L）；
  7. `gd_linear_rate`：e_n ≤ (1 − μ/L)ⁿ·e_0（接 RealConvergence.contraction_pow_bound 的
     同类归纳；常数因子 0 ≤ 1 − μ/L < 1）；
  8. `gd_converges`：连接 `contraction_converges` ⟹ ∀ ε > 0, ∃ n, gap_n < ε；
  9. `strong_convex_iterate_contraction`（可选、独立的梯度-迭代形式）：在
     **Baillon–Haddad 共强制性** `GradientCoCoercive` 假设下，步长 η = 2/(μ+L) 给出
     迭代收缩系数 **((L−μ)/(L+μ))²**（标准最优步长结果）；
 10. 二次模型实例 `quad_strong_convex` / `quad_smooth` / `quad_gd_contraction`：
     f(x) = (a/2)x²、∇f = a·x、x* = 0，对 μ ≤ a ≤ L 无条件成立。

## ⭐ 第八节：共强制性由【假设】升为【定理】

原诚实边界写着「光滑强凸函数的梯度确实满足 `GradientCoCoercive`，但该事实的完整推导
超出本文件范围，**未证明**」。第八节**补上了该推导**：

  · `cocoercive_lower_half`：`μ·d² ≤ G·d`（`d = x − x*`、`G = g x`）——
    由 `StrongConvex` 在 `(x*, x)` 与 `(x, x*)` 两个方向消去 `f x − f x*` 得到；
  · `cocoercive_upper_half`：`G·d ≤ L·d²` —— 由 `Smooth` 在两个方向同法消去；
  · ⭐ `strong_convex_implies_cocoercive`（**主定理**）：两式合并恰是
    `(G − μd)(G − Ld) ≤ 0`，展开并用 `μ + L > 0` 除，即得
    `G·d ≥ (μL/(μ+L))d² + (1/(μ+L))G²` —— **正是 `GradientCoCoercive` 的定义**；
  · `strong_convex_iterate_contraction_of_sc`：**去假设版**，直接从
    `StrongConvex` + `Smooth` + `g x* = 0` 给出最优系数 `((L−μ)/(L+μ))²`；
  · `quad_cocoercive`：二次实例（说明结论**非空洞**）。

⭐ **该推导是锐的**：二次 `f = (a/2)x²` 在 `a = μ` 或 `a = L` 处使
`(G − μd)(G − Ld) = 0`，故 `μ`、`L` 都是**最优常数**（数值验证取到等号）。

诚实边界：
  · `gd_linear_rate` / `gd_converges` 的收缩是**函数值（Lyapunov）**意义下的，
    系数 1 − μη = 1 − μ/L；迭代（参数空间）形式的最优系数 ((L−μ)/(L+μ))² 需要
    Baillon–Haddad 共强制性，本文件把它作为**显式假设** `GradientCoCoercive`
    （光滑强凸函数的梯度确实满足它，但该事实的完整推导超出本文件范围，未证明）；
     ⭐ **第八节已补上该推导**：`strong_convex_implies_cocoercive` 从
     `StrongConvex` + `Smooth` 直接推出 `GradientCoCoercive`（新推导额外需要
     `0 < μ + L` 供分母正性，已**显式写出**），并有去假设版
     `strong_convex_iterate_contraction_of_sc` 与二次实例 `quad_cocoercive`；
  · 一维 ℝ；`StrongConvex`/`Smooth` 以梯度选择 g 表述（不引入微分算子）；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、定义：强凸与光滑（带梯度选择） -/

/-- f 是 μ-强凸（用梯度选择 g 表述）：∀ x y, f y ≥ f x + g x·(y−x) + (μ/2)(y−x)²。 -/
def StrongConvex (μ : ℝ) (f g : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, f y ≥ f x + g x * (y - x) + (μ / 2) * (y - x) ^ 2

/-- f 是 L-光滑（下降引理形式）：∀ x y, f y ≤ f x + g x·(y−x) + (L/2)(y−x)²。 -/
def Smooth (L : ℝ) (f g : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, f y ≤ f x + g x * (y - x) + (L / 2) * (y - x) ^ 2

/-! ## 二、差距的下界（强凸）与上界（光滑） -/

/-- **强凸差距下界**：g x* = 0 ⟹ (μ/2)(x − x*)² ≤ f x − f x*。 -/
theorem strong_convex_gap_lower {f g : ℝ → ℝ} {μ : ℝ} (hSC : StrongConvex μ f g)
    {xstar : ℝ} (hg0 : g xstar = 0) (x : ℝ) :
    (μ / 2) * (x - xstar) ^ 2 ≤ f x - f xstar := by
  have h := hSC xstar x
  simp only [hg0, zero_mul, add_zero, zero_add] at h
  linarith

/-- **光滑差距上界（任务目标）**：g x* = 0 ⟹ f x − f x* ≤ (L/2)(x − x*)²。 -/
theorem strong_convex_gap_bound {f g : ℝ → ℝ} {L : ℝ} (hSM : Smooth L f g)
    {xstar : ℝ} (hg0 : g xstar = 0) (x : ℝ) :
    f x - f xstar ≤ (L / 2) * (x - xstar) ^ 2 := by
  have h := hSM xstar x
  simp only [hg0, zero_mul, add_zero, zero_add] at h
  linarith

/-- 强凸 + μ ≥ 0 ⟹ f x* ≤ f x（x* 是全局极小点）。 -/
theorem strong_convex_minimizer {f g : ℝ → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hSC : StrongConvex μ f g) {xstar : ℝ} (hg0 : g xstar = 0) (x : ℝ) :
    f xstar ≤ f x := by
  have h := strong_convex_gap_lower hSC hg0 x
  nlinarith [h, sq_nonneg (x - xstar), hμ]

/-- 强凸差距非负（Lyapunov 量非负）。 -/
theorem strong_convex_gap_nonneg {f g : ℝ → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hSC : StrongConvex μ f g) {xstar : ℝ} (hg0 : g xstar = 0) (x : ℝ) :
    0 ≤ f x - f xstar := by
  have h := strong_convex_gap_lower hSC hg0 x
  nlinarith [h, sq_nonneg (x - xstar), hμ]

/-- **极小点唯一**：μ > 0、g x* = 0 且 f x = f x* ⟹ x = x*。 -/
theorem strong_convex_unique_min {f g : ℝ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hSC : StrongConvex μ f g) {xstar : ℝ} (hg0 : g xstar = 0) {x : ℝ}
    (hx : f x = f xstar) : x = xstar := by
  have h := strong_convex_gap_lower hSC hg0 x
  have hs : (x - xstar) ^ 2 = 0 := by
    nlinarith [h, hx, hμ, sq_nonneg (x - xstar)]
  have hz : x - xstar = 0 := sq_eq_zero_iff.mp hs
  linarith

/-- **强凸的梯度-差距界**：gap ≤ ‖g x‖²/(2μ)（配平方论证）。 -/
theorem strong_convex_gap_le_grad_sq {f g : ℝ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hSC : StrongConvex μ f g) {xstar : ℝ} (_hg0 : g xstar = 0) (x : ℝ) :
    f x - f xstar ≤ (g x) ^ 2 / (2 * μ) := by
  have h := hSC x xstar
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hsquare : 0 ≤ (μ / 2) * (xstar - x) ^ 2 + g x * (xstar - x) + (g x) ^ 2 / (2 * μ) := by
    have hv : (μ / 2) * (xstar - x) ^ 2 + g x * (xstar - x) + (g x) ^ 2 / (2 * μ)
        = (μ / 2) * ((xstar - x) + g x / μ) ^ 2 := by
      field_simp [hμne]
      ring
    rw [hv]
    nlinarith [sq_nonneg ((xstar - x) + g x / μ), hμ]
  nlinarith [h, hsquare]

/-! ## 三、光滑的单步下降（步长 η = 1/L） -/

/-- 光滑下降引理：f(x − (1/L)g x) − f x ≤ −‖g x‖²/(2L)。 -/
theorem smooth_descent_bound {f g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hSM : Smooth L f g)
    (x : ℝ) :
    f (x - (1 / L) * g x) - f x ≤ - ((g x) ^ 2 / (2 * L)) := by
  have h := hSM x (x - (1 / L) * g x)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hquad : (L / 2) * ((x - (1 / L) * g x) - x) ^ 2 = (g x) ^ 2 / (2 * L) := by
    field_simp [hLne]
    ring
  have hlin : g x * ((x - (1 / L) * g x) - x) = - (g x) ^ 2 / L := by
    field_simp [hLne]
    ring
  rw [hquad, hlin] at h
  have hcomb : - (g x) ^ 2 / L + (g x) ^ 2 / (2 * L) = - ((g x) ^ 2 / (2 * L)) := by
    field_simp [hLne]
    ring
  linarith [h, hcomb]

/-! ## 四、主定理：函数值收缩系数 (1 − μη) -/

/-- **强凸 + 光滑 ⟹ 单步 Lyapunov 收缩**（步长 η = 1/L）：
gap(x − (1/L)g x) ≤ (1 − μ/L)·gap(x)（收缩系数 = 1 − μη，η = 1/L）。 -/
theorem strong_convex_contraction {f g : ℝ → ℝ} {μ L : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (_hμL : μ ≤ L) (hSC : StrongConvex μ f g) (hSM : Smooth L f g)
    {xstar : ℝ} (hg0 : g xstar = 0) (x : ℝ) :
    f (x - (1 / L) * g x) - f xstar ≤ (1 - μ / L) * (f x - f xstar) := by
  have hdesc := smooth_descent_bound hL hSM x
  have hgrad := strong_convex_gap_le_grad_sq hμ hSC hg0 x
  have h1 : μ * (f x - f xstar) ≤ (g x) ^ 2 / 2 := by
    have h2 : μ * ((g x) ^ 2 / (2 * μ)) = (g x) ^ 2 / 2 := by
      field_simp [ne_of_gt hμ]
      ring
    nlinarith [hgrad, h2]
  have hkey : (μ / L) * (f x - f xstar) ≤ (g x) ^ 2 / (2 * L) := by
    have hmul : (μ / L) * (f x - f xstar) = (μ * (f x - f xstar)) / L := by ring
    have h2L : (g x) ^ 2 / (2 * L) = ((g x) ^ 2 / 2) / L := by ring
    rw [hmul, h2L]
    exact div_le_div_of_nonneg_right h1 (le_of_lt hL)
  have hexp : (1 - μ / L) * (f x - f xstar)
      = (f x - f xstar) - (μ / L) * (f x - f xstar) := by ring
  rw [hexp]
  linarith [hdesc, hkey]

/-! ## 五、几何率与收敛 -/

/-- 第 n 步的函数值差距 gap_n = f(x_n) − f x*。 -/
def GDGap (f g : ℝ → ℝ) (η : ℝ) (xstar x0 : ℝ) (n : ℕ) : ℝ :=
  f (SubgradientIterate g η n x0) - f xstar

/-- **线性收敛率**：gap_n ≤ (1 − μ/L)ⁿ·gap_0。 -/
theorem gd_linear_rate {f g : ℝ → ℝ} {μ L : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (hμL : μ ≤ L) (hSC : StrongConvex μ f g) (hSM : Smooth L f g)
    {xstar : ℝ} (hg0 : g xstar = 0) (x0 : ℝ) :
    ∀ n : ℕ, GDGap f g (1 / L) xstar x0 n ≤
      (1 - μ / L) ^ n * GDGap f g (1 / L) xstar x0 0 := by
  have hc0 : 0 ≤ 1 - μ / L := by
    rw [sub_nonneg, div_le_iff₀ hL]
    simpa using hμL
  intro n
  induction n with
  | zero => simp [GDGap]
  | succ n ih =>
      have hstep := strong_convex_contraction hμ hL hμL hSC hSM hg0
        (SubgradientIterate g (1 / L) n x0)
      calc
        GDGap f g (1 / L) xstar x0 (n + 1)
            = f (SubgradientIterate g (1 / L) n x0
                - (1 / L) * g (SubgradientIterate g (1 / L) n x0)) - f xstar := rfl
        _ ≤ (1 - μ / L) * (f (SubgradientIterate g (1 / L) n x0) - f xstar) := hstep
        _ = (1 - μ / L) * GDGap f g (1 / L) xstar x0 n := rfl
        _ ≤ (1 - μ / L) * ((1 - μ / L) ^ n * GDGap f g (1 / L) xstar x0 0) :=
              mul_le_mul_of_nonneg_left ih hc0
        _ = (1 - μ / L) ^ (n + 1) * GDGap f g (1 / L) xstar x0 0 := by ring

/-- **强凸 ⟹ ε-终止**（连接 RealConvergence.contraction_converges）：
∀ ε > 0，∃ n，gap_n < ε。 -/
theorem gd_converges {f g : ℝ → ℝ} {μ L : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (hμL : μ ≤ L) (hSC : StrongConvex μ f g) (hSM : Smooth L f g)
    {xstar : ℝ} (hg0 : g xstar = 0) (x0 : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, GDGap f g (1 / L) xstar x0 n < ε := by
  have hc0 : 0 ≤ 1 - μ / L := by
    rw [sub_nonneg, div_le_iff₀ hL]
    simpa using hμL
  have hc1 : 1 - μ / L < 1 := by
    have hpos : 0 < μ / L := div_pos hμ hL
    linarith
  have hnonneg : ∀ n : ℕ, 0 ≤ GDGap f g (1 / L) xstar x0 n := by
    intro n
    exact strong_convex_gap_nonneg (le_of_lt hμ) hSC hg0 _
  have hstep : ∀ n : ℕ, GDGap f g (1 / L) xstar x0 (n + 1) ≤
      (1 - μ / L) * GDGap f g (1 / L) xstar x0 n := by
    intro n
    exact strong_convex_contraction hμ hL hμL hSC hSM hg0
      (SubgradientIterate g (1 / L) n x0)
  exact contraction_converges (1 - μ / L) hc0 hc1 hstep hnonneg

/-! ## 六、迭代形式的最优系数 ((L−μ)/(L+μ))²（Baillon–Haddad 共强制性，显式假设） -/

/-- 梯度共强制性（Baillon–Haddad）：⟨g x, x − x*⟩ ≥ (μL/(μ+L))‖x − x*‖² + (1/(μ+L))‖g x‖²。
光滑强凸函数满足此式；本文件以显式假设引入（不隐藏 gap）。 -/
def GradientCoCoercive (μ L : ℝ) (g : ℝ → ℝ) (xstar : ℝ) : Prop :=
  ∀ x : ℝ, (μ * L / (μ + L)) * (x - xstar) ^ 2 + (1 / (μ + L)) * (g x) ^ 2
    ≤ (g x) * (x - xstar)

/-- **共强制 ⟹ 迭代收缩系数 ((L−μ)/(L+μ))²**（步长 η = 2/(μ+L)）。 -/
theorem strong_convex_iterate_contraction {g : ℝ → ℝ} {μ L : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    {xstar : ℝ} (hcc : GradientCoCoercive μ L g xstar) (x : ℝ) :
    ‖x - (2 / (μ + L)) * g x - xstar‖ ^ 2 ≤
      ((L - μ) / (L + μ)) ^ 2 * ‖x - xstar‖ ^ 2 := by
  have hμLμ : μ + L ≠ 0 := by positivity
  have hkey := hcc x
  have hc4 : 0 ≤ 2 * (2 / (μ + L)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hkey hc4
  have hsq : ‖x - (2 / (μ + L)) * g x - xstar‖ ^ 2
      = (x - xstar) ^ 2 - 2 * (2 / (μ + L)) * (g x) * (x - xstar)
        + (2 / (μ + L)) ^ 2 * (g x) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    ring
  have hnorm2 : ‖x - xstar‖ ^ 2 = (x - xstar) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  have hmain : (x - xstar) ^ 2 - 2 * (2 / (μ + L)) * (g x) * (x - xstar)
      + (2 / (μ + L)) ^ 2 * (g x) ^ 2
      ≤ ((L - μ) / (L + μ)) ^ 2 * (x - xstar) ^ 2 := by
    have h1 : (x - xstar) ^ 2 - 2 * (2 / (μ + L)) * (g x) * (x - xstar)
        + (2 / (μ + L)) ^ 2 * (g x) ^ 2
        ≤ (x - xstar) ^ 2
          - 2 * (2 / (μ + L)) * ((μ * L / (μ + L)) * (x - xstar) ^ 2
              + (1 / (μ + L)) * (g x) ^ 2)
          + (2 / (μ + L)) ^ 2 * (g x) ^ 2 := by
      nlinarith [hmul]
    have h2 : (x - xstar) ^ 2
          - 2 * (2 / (μ + L)) * ((μ * L / (μ + L)) * (x - xstar) ^ 2
              + (1 / (μ + L)) * (g x) ^ 2)
          + (2 / (μ + L)) ^ 2 * (g x) ^ 2
        = ((L - μ) / (L + μ)) ^ 2 * (x - xstar) ^ 2 := by
      field_simp [hμLμ]
      ring
    linarith [h1, h2]
  rw [hsq, hnorm2]
  exact hmain

/-! ## 七、二次模型实例（对 μ ≤ a ≤ L 无条件成立） -/

/-- 二次 f(x) = (a/2)x²、g x = a·x 是 μ-强凸（μ ≤ a）。 -/
theorem quad_strong_convex {μ a : ℝ} (hμa : μ ≤ a) :
    StrongConvex μ (fun x : ℝ => (a / 2) * x ^ 2) (fun x : ℝ => a * x) := by
  intro x y
  have h : 0 ≤ (a - μ) * (y - x) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [h]

/-- 二次 f(x) = (a/2)x²、g x = a·x 是 L-光滑（a ≤ L）。 -/
theorem quad_smooth {L a : ℝ} (haL : a ≤ L) :
    Smooth L (fun x : ℝ => (a / 2) * x ^ 2) (fun x : ℝ => a * x) := by
  intro x y
  have h : 0 ≤ (L - a) * (y - x) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [h]

/-- 二次模型上的 Lyapunov 收缩实例（μ ≤ a ≤ L、步长 1/L）。 -/
theorem quad_gd_contraction {a μ L : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hμa : μ ≤ a)
    (haL : a ≤ L) (x : ℝ) :
    (a / 2) * (x - (1 / L) * (a * x)) ^ 2 ≤ (1 - μ / L) * ((a / 2) * x ^ 2) := by
  have h := strong_convex_contraction hμ hL (le_trans hμa haL) (quad_strong_convex hμa)
    (quad_smooth haL) (by ring : a * 0 = 0) x
  simpa using h

/-! ## 八、⭐ **从强凸 + 光滑【推出】共强制性**（本节新增；原为显式假设）

第六节把 Baillon–Haddad 共强制性写成**显式假设** `GradientCoCoercive`，
并在 docstring 中注明「光滑强凸函数的梯度确实满足它，但该事实的完整推导
超出本文件范围，未证明」。**本节补上该推导** —— 于是
`strong_convex_iterate_contraction` 可以直接从 `StrongConvex` + `Smooth` 调用，
**不再需要外部提供 `GradientCoCoercive`**。

### 推导（两条一枝的初等代数，无外部引理）

设 `d = x − x*`、`G = g x`、`D = f x − f x*`，且 `g x* = 0`。把两条定义
分别用在**两个方向**上（这是本证明的全部内容）：

| # | 前提 | 取用 | 得到 |
|--:|:--|:--|:--|
| ① | `StrongConvex μ f g` 在 `(x*, x)` | `g x* = 0` | `D ≥ (μ/2)·d²` |
| ② | `StrongConvex μ f g` 在 `(x, x*)` | 展开 | `D ≤ G·d − (μ/2)·d²` |
| ③ | `Smooth L f g` 在 `(x, x*)` | 展开 | `D ≥ G·d − (L/2)·d²` |
| ④ | `Smooth L f g` 在 `(x*, x)` | `g x* = 0` | `D ≤ (L/2)·d²` |

由 ①+② 消去 `D` 得 **`μ·d² ≤ G·d`**；
由 ③+④ 消去 `D` 得 **`G·d ≤ L·d²`**。

⭐ **关键一步**：两式合并恰是 `(G − μd)·(G − Ld) ≤ 0`（因为
`G·d ≥ μd²` ⟺ `(G − μd)d ≥ 0`，`G·d ≤ Ld²` ⟺ `(G − Ld)d ≤ 0`，
再同乘正因子 `d²` 即得）。展开该式：

    G² − (μ+L)·G·d + μ·L·d² ≤ 0
    ⟺ (μ+L)·G·d ≥ μ·L·d² + G²
    ⟺ G·d ≥ (μL/(μ+L))·d² + (1/(μ+L))·G²      （除以 `μ+L > 0`）

**这正是 `GradientCoCoercive μ L g x*` 的定义**。∎

⭐ **注意该推导是**锐的****：二次函数 `f = (a/2)x²`、`g = a·x`（`μ ≤ a ≤ L`）使
`(G − μd)(G − Ld) = 0` 在 `a = μ` 或 `a = L` 时成立，故 `μ`、`L` 都是**最优常数**
（数值验证：`min(G·d − BH右端) = 0` 在 `a ∈ [μ,L]` 上取到）。 -/

/-- **共强制的两个半边（一）**：强凸 + 光滑 + `g x* = 0` ⟹ `μ·d² ≤ G·d`。

证明：由 `StrongConvex` 在 `(x*, x)` 得 `D ≥ (μ/2)d²`；由 `StrongConvex` 在 `(x, x*)`
得 `D ≤ G·d − (μ/2)d²`；两式消去 `D`。 -/
lemma cocoercive_lower_half {f g : ℝ → ℝ} {μ : ℝ} (hSC : StrongConvex μ f g)
    {xstar : ℝ} (hg0 : g xstar = 0) (x : ℝ) :
    μ * (x - xstar) ^ 2 ≤ g x * (x - xstar) := by
  have h1 : (μ / 2) * (x - xstar) ^ 2 ≤ f x - f xstar := by
    have h := hSC xstar x
    simp only [hg0, zero_mul, add_zero, zero_add] at h
    linarith
  have h2 : f x - f xstar ≤ g x * (x - xstar) - (μ / 2) * (x - xstar) ^ 2 := by
    have h := hSC x xstar
    have hs : (xstar - x) ^ 2 = (x - xstar) ^ 2 := by ring
    rw [hs] at h
    linarith
  linarith

/-- **共强制的两个半边（二）**：强凸 + 光滑 + `g x* = 0` ⟹ `G·d ≤ L·d²`。

证明：由 `Smooth` 在 `(x, x*)` 得 `D ≥ G·d − (L/2)d²`；由 `Smooth` 在 `(x*, x)`
得 `D ≤ (L/2)d²`；两式消去 `D`。 -/
lemma cocoercive_upper_half {f g : ℝ → ℝ} {L : ℝ} (hSM : Smooth L f g)
    {xstar : ℝ} (hg0 : g xstar = 0) (x : ℝ) :
    g x * (x - xstar) ≤ L * (x - xstar) ^ 2 := by
  have h1 : g x * (x - xstar) - (L / 2) * (x - xstar) ^ 2 ≤ f x - f xstar := by
    have h := hSM x xstar
    have hs : (xstar - x) ^ 2 = (x - xstar) ^ 2 := by ring
    rw [hs] at h
    linarith
  have h2 : f x - f xstar ≤ (L / 2) * (x - xstar) ^ 2 := by
    have h := hSM xstar x
    simp only [hg0, zero_mul, add_zero, zero_add] at h
    linarith
  linarith

/-- ⭐ **从强凸 + 光滑【推出】Baillon–Haddad 共强制性**（本节主定理，原为假设）。

设 `0 < μ < μ+L`、`g x* = 0`，`f` 既 μ-强凸又 L-光滑，则

    G·d ≥ (μL/(μ+L))·d² + (1/(μ+L))·G²,   `d = x − x*`、`G = g x`,

即 `GradientCoCoercive μ L g x*` 成立。

**证明**：由 `cocoercive_lower_half` 得 `μ d² ≤ G d`，由 `cocoercive_upper_half` 得
`G d ≤ L d²`；二者合并即 `(G − μd)(G − Ld) ≤ 0`，展开并用 `μ + L > 0` 除即得。

**诚实边界（已按 Lean 的 `unused variable` 证据更正）**：⭐ Lean 报告
`unused variable hμ`（`RealStrongConvex:398`）—— 即 **`0 < μ` 在本证明中并不承重**，
**真正承重的只有 `0 < μ + L`**（用于 `div_le_iff₀` 的分母正性）。
⇒ 故本版**删除** `hμ : 0 < μ`，只保留 `hμL : 0 < μ + L`
（⚠ 这是**删除写松的假设**，不是削弱结论：结论不变，假设更少 ⟹ 更强）。
`L` 亦无需单独假设 `L > 0`。 -/
theorem strong_convex_implies_cocoercive {f g : ℝ → ℝ} {μ L : ℝ}
    (hμL : 0 < μ + L) (hSC : StrongConvex μ f g) (hSM : Smooth L f g)
    {xstar : ℝ} (hg0 : g xstar = 0) :
    GradientCoCoercive μ L g xstar := by
  intro x
  have hlow := cocoercive_lower_half hSC hg0 x
  have hupp := cocoercive_upper_half hSM hg0 x
  set d : ℝ := x - xstar with hd
  set G : ℝ := g x with hG
  -- 两个半边：`(G - μd)·d ≥ 0` 与 `(G - Ld)·d ≤ 0`
  have hA : 0 ≤ (G - μ * d) * d := by
    have : μ * d ^ 2 ≤ G * d := by simpa [hd, hG] using hlow
    nlinarith [this]
  have hB : (G - L * d) * d ≤ 0 := by
    have : G * d ≤ L * d ^ 2 := by simpa [hd, hG] using hupp
    nlinarith [this]
  -- 相乘：`(G - μd)(G - Ld)·d² ≤ 0`，再由 `d² ≥ 0` 得乘积 ≤ 0
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  have hprod : (G - μ * d) * (G - L * d) * d ^ 2 ≤ 0 := by
    have hrearr : (G - μ * d) * (G - L * d) * d ^ 2
        = ((G - μ * d) * d) * ((G - L * d) * d) := by ring
    rw [hrearr]
    exact mul_nonpos_of_nonneg_of_nonpos hA hB
  -- 由 `d² ≥ 0` 且 `乘积·d² ≤ 0` 推出 `乘积 ≤ 0`
  have hkey : (G - μ * d) * (G - L * d) ≤ 0 := by
    rcases eq_or_lt_of_le hd2 with h0 | hpos
    · -- d = 0 ⟹ x = x* ⟹ G = g x = g x* = 0 ⟹ 乘积 = 0
      have hdz : d = 0 := by nlinarith [sq_nonneg d]
      have hxd : x = xstar := by rw [hd] at hdz; linarith
      have hG0 : G = 0 := by rw [hG, hxd]; exact hg0
      subst hxd
      rw [hG0, hd]
      norm_num
    · by_contra hcon
      push_neg at hcon
      have : 0 < (G - μ * d) * (G - L * d) * d ^ 2 :=
        mul_pos hcon hpos
      linarith
  have hexp : (G - μ * d) * (G - L * d)
      = G ^ 2 - (μ + L) * (G * d) + μ * L * d ^ 2 := by ring
  rw [hexp] at hkey
  have hgoal : (μ * L * d ^ 2 + G ^ 2) / (μ + L) ≤ G * d := by
    rw [div_le_iff₀ hμL]
    linarith
  have hsplit : (μ * L / (μ + L)) * d ^ 2 + (1 / (μ + L)) * G ^ 2
      = (μ * L * d ^ 2 + G ^ 2) / (μ + L) := by
    field_simp
  rw [hsplit]
  simpa [hd, hG] using hgoal

/-- ⭐ **迭代收缩（去假设版）**：`strong_convex_iterate_contraction` 的
`GradientCoCoercive` 假设由 `strong_convex_implies_cocoercive` **推出** ⟹
只需 `StrongConvex` + `Smooth` + `g x* = 0` 即得最优系数 `((L−μ)/(L+μ))²`。

**注意（诚实边界，第 213 轮更正）**：本版额外显式写出 `μ ≤ L` 与 `0 < μ + L`
（后者供 `div_le_iff₀` 的分母正性）。

原文在此处写的是「`μ ≤ L`（原版 `_hμL`，被下划线标记为"未使用"，但**保留它是正确的**）」。
**那句话是错的，已删。** 原版的 `_hμL` **确实可删**：证明里 `h1` 只用共强制性，
`h2` 是纯代数恒等式（`field_simp` + `ring`），**没有任何一步需要 `μ ≤ L`**。
删掉后**命题本身仍为真**，只是当 `μ > L` 时系数 `((L−μ)/(L+μ))²` 不再 `≤ 1`，
**那时它不是收缩因子**。

**所以本版保留 `μ ≤ L` 的理由是「为了『收缩』这个解读」，不是「为了命题的真假」。**
两种理由必须分开写——把「为了解读」说成「为了真假」，正是原注的错误。 -/
theorem strong_convex_iterate_contraction_of_sc {f g : ℝ → ℝ} {μ L : ℝ} (hμ : 0 < μ)
    (hL : 0 < L) (hμL_le : μ ≤ L) (hSC : StrongConvex μ f g) (hSM : Smooth L f g)
    {xstar : ℝ} (hg0 : g xstar = 0) (x : ℝ) :
    ‖x - (2 / (μ + L)) * g x - xstar‖ ^ 2 ≤
      ((L - μ) / (L + μ)) ^ 2 * ‖x - xstar‖ ^ 2 := by
  have hμL : 0 < μ + L := by linarith
  exact strong_convex_iterate_contraction hμ hL
    (strong_convex_implies_cocoercive hμL hSC hSM hg0) x

/-- **二次模型上的共强制性实例**（无条件）：`f = (a/2)x²`、`g = a·x`、`x* = 0`、
`μ ≤ a ≤ L` ⟹ `GradientCoCoercive μ L g 0`。

这是 `strong_convex_implies_cocoercive` 的最简实例，同时说明该结论**非空洞**
（对 `μ < a < L` 严格不等）。 -/
theorem quad_cocoercive {μ L a : ℝ} (hμ : 0 < μ) (hμa : μ ≤ a) (haL : a ≤ L) :
    GradientCoCoercive μ L (fun x : ℝ => a * x) 0 := by
  have hμL : 0 < μ + L := by linarith
  exact strong_convex_implies_cocoercive hμL (quad_strong_convex hμa)
    (quad_smooth haL) (by ring : a * 0 = 0)

end Lattice
