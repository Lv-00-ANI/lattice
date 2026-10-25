import Mathlib
import Lattice.Lib.Optim.RealStrongConvex
import Lattice.Lib.Optim.RealNesterov
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: Polyak–Łojasiewicz 条件 —— 梯度下降的线性收敛

强凸（`RealStrongConvex.StrongConvex`）是线性收敛的经典充分条件。本文件给出**更弱**的
几何条件——**Polyak–Łojasiewicz（PL）不等式**——并证明它同样蕴含梯度下降的线性收敛：

    PL(μ) :  ∀ x, ‖∇f(x)‖² ≥ 2μ·(f(x) − f*)。

定理清单：
  1. `PLCondition`（def）：`∀ x, 2μ(f x − f x*) ≤ (g x)²`（一维、梯度选择 `g`）；
  2. `strong_convex_implies_PL`（**强凸 ⟹ PL**，真实证明）：`StrongConvex μ f g`、
     `g x* = 0`、`μ > 0` ⟹ `PLCondition μ f g x*`。由 `strong_convex_gap_le_grad_sq`
     得 `f x − f x* ≤ ‖g x‖²/(2μ)`，两边乘 `2μ`。**注意常数不退化**（同 μ）；
  3. `pl_gd_contraction`（**PL 单步收缩**）：`f` 是 `L`-光滑（下降引理形式）、
     `η·L ≤ 1` ⟹
     `f(x − η∇f x) − f* ≤ (1 − (2μη − μLη²))·(f x − f*)`；
  4. `pl_gd_contraction_step`：步长 `η = 1/L` 时收缩系数为 `1 − μ/L`；
  5. `pl_gd_linear_rate`：`gap_n ≤ (1 − μ/L)ⁿ·gap_0`（`PLGap` 定义）；
  6. `pl_gd_converges`：`∀ ε > 0, ∃ n, gap_n < ε`（接 `RealConvergence.contraction_converges`）。

**诚实边界（重要）**：
- 「PL 但不强凸」的**对比例子本文件未做**。一维中要机器验证一个光滑凸函数满足 PL 却
  违反任何强凸常数，需要分段 / 区间分析（`f''` 在某处小于任何候选常数而 PL 仍成立），
  工程量远大于本文件；已知的高维例子（如 Karimi–Nutini–Schmidt 型 `f(x,y)=x²+3sin²y`
  的变体）在 Lean 中未验证。因此本文件**只给出强凸 ⟹ PL 方向**，并把反向的严格性
  标注为**未做**，不伪造例子；
- PL 只要求「梯度不消失到零之外」的几何条件，**不要求凸性**；本文件的收敛定理同样
  不假设凸性，只在收敛（ε-终止）定理中额外用 `Subgradient f x* 0`（即 `x*` 是全局
  极小点）保证误差非负；
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、PL 条件的定义 -/

/-- **Polyak–Łojasiewicz 条件**（一维，梯度选择 `g`）：
`∀ x, 2μ·(f x − f x*) ≤ (g x)²`，即 `‖∇f(x)‖² ≥ 2μ·(f(x) − f*)`。 -/
def PLCondition (mu : ℝ) (f g : ℝ → ℝ) (xstar : ℝ) : Prop :=
  ∀ x : ℝ, 2 * mu * (f x - f xstar) ≤ (g x) ^ 2

/-! ## 二、强凸 ⟹ PL -/

/-- **强凸蕴含 PL（同常数 μ）**：`μ > 0`、`StrongConvex μ f g`、`g x* = 0` ⟹
`PLCondition μ f g x*`。
证明：`RealStrongConvex.strong_convex_gap_le_grad_sq` 给出
`f x − f x* ≤ ‖g x‖²/(2μ)`，两边乘正数 `2μ` 即得。 -/
theorem strong_convex_implies_PL {f g : ℝ → ℝ} {mu xstar : ℝ} (hmu : 0 < mu)
    (hSC : StrongConvex mu f g) (hg0 : g xstar = 0) :
    PLCondition mu f g xstar := by
  intro x
  have h := strong_convex_gap_le_grad_sq hmu hSC hg0 x
  have h2 : 2 * mu * (f x - f xstar) ≤ 2 * mu * ((g x) ^ 2 / (2 * mu)) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h3 : 2 * mu * ((g x) ^ 2 / (2 * mu)) = (g x) ^ 2 := by
    field_simp
  linarith [h2, h3]

/-! ## 三、PL 下的单步收缩 -/

/-- **PL 单步收缩（一般步长）**：`f` 是 `L`-光滑（下降引理形式 `Smooth L f g`）、
`η > 0`、`η·L ≤ 1`、`PLCondition μ f g x*`、`g x* = 0` ⟹
`f(x − η g x) − f x* ≤ (1 − (2μη − μLη²))·(f x − f x*)`。

证明：光滑下降引理 `f(x−ηgx) − f x ≤ −(η − Lη²/2)·(g x)²`；系数
`η − Lη²/2 ≥ 0`（由 `ηL ≤ 1`）；PL 给出 `(g x)² ≥ 2μ(f x − f x*)`，两者相乘后合并。 -/
theorem pl_gd_contraction {f g : ℝ → ℝ} {mu L eta x xstar : ℝ}
    (hmu : 0 < mu) (heta : 0 < eta) (hLeta : L * eta ≤ 1)
    (hSM : Smooth L f g) (hg0 : g xstar = 0) (hPL : PLCondition mu f g xstar) :
    f (x - eta * g x) - f xstar ≤
      (1 - (2 * mu * eta - mu * L * eta ^ 2)) * (f x - f xstar) := by
  have hcoef : 0 ≤ eta * (1 - L * eta / 2) := by nlinarith
  have hdec : f (x - eta * g x) - f x ≤ -(eta * (1 - L * eta / 2)) * (g x) ^ 2 :=
    nesterov_descent_lemma (L := L) (η := eta) hSM x
  have hPLx : 2 * mu * (f x - f xstar) ≤ (g x) ^ 2 := hPL x
  have hkey : -(eta * (1 - L * eta / 2)) * (g x) ^ 2
      ≤ -(eta * (1 - L * eta / 2)) * (2 * mu * (f x - f xstar)) := by
    have h := mul_le_mul_of_nonneg_left hPLx hcoef
    nlinarith [h]
  have heq : (eta * (1 - L * eta / 2)) * (2 * mu * (f x - f xstar))
      = (2 * mu * eta - mu * L * eta ^ 2) * (f x - f xstar) := by ring
  linarith [hdec, hkey, heq]

/-- **PL 单步收缩（最优步长 `η = 1/L`）**：收缩系数 `1 − μ/L`。 -/
theorem pl_gd_contraction_step {f g : ℝ → ℝ} {mu L x xstar : ℝ}
    (hmu : 0 < mu) (hL : 0 < L) (hSM : Smooth L f g) (hg0 : g xstar = 0)
    (hPL : PLCondition mu f g xstar) :
    f (x - (1 / L) * g x) - f xstar ≤ (1 - mu / L) * (f x - f xstar) := by
  have heta : 0 < (1 : ℝ) / L := by positivity
  have hLeta : L * (1 / L) ≤ 1 := by
    rw [mul_one_div, div_self (ne_of_gt hL)]
  have h := pl_gd_contraction (eta := 1 / L) (x := x) hmu heta hLeta hSM hg0 hPL
  have hc : (1 - (2 * mu * (1 / L) - mu * L * (1 / L) ^ 2)) = 1 - mu / L := by
    field_simp
    ring
  rwa [hc] at h

/-! ## 四、PL 下的线性率与 ε-终止 -/

/-- PL 迭代的第 n 步次优差距：`f(x_n) − f(x*)`，`x_{n+1} = x_n − (1/L)·g(x_n)`。 -/
def PLGap (f g : ℝ → ℝ) (L xstar x0 : ℝ) (n : ℕ) : ℝ :=
  f (SubgradientIterate g (1 / L) n x0) - f xstar

/-- **PL 线性收敛率**：`0 < μ ≤ L`、`Smooth L f g`、`g x* = 0`、
`PLCondition μ f g x*` ⟹ `gap_n ≤ (1 − μ/L)ⁿ·gap_0`。 -/
theorem pl_gd_linear_rate {f g : ℝ → ℝ} {mu L x0 xstar : ℝ} (hmu : 0 < mu)
    (hL : 0 < L) (hmuL : mu ≤ L) (hSM : Smooth L f g) (hg0 : g xstar = 0)
    (hPL : PLCondition mu f g xstar) :
    ∀ n : ℕ, PLGap f g L xstar x0 n ≤ (1 - mu / L) ^ n * PLGap f g L xstar x0 0 := by
  have hc0 : 0 ≤ 1 - mu / L := by
    rw [sub_nonneg, div_le_iff₀ hL]
    simpa using hmuL
  intro n
  induction n with
  | zero => simp [PLGap]
  | succ n ih =>
      have hstep := pl_gd_contraction_step (x := SubgradientIterate g (1 / L) n x0)
        hmu hL hSM hg0 hPL
      calc
        PLGap f g L xstar x0 (n + 1)
            = f (SubgradientIterate g (1 / L) n x0
                - (1 / L) * g (SubgradientIterate g (1 / L) n x0)) - f xstar := rfl
        _ ≤ (1 - mu / L)
              * (f (SubgradientIterate g (1 / L) n x0) - f xstar) := hstep
        _ = (1 - mu / L) * PLGap f g L xstar x0 n := rfl
        _ ≤ (1 - mu / L) * ((1 - mu / L) ^ n * PLGap f g L xstar x0 0) :=
              mul_le_mul_of_nonneg_left ih hc0
        _ = (1 - mu / L) ^ (n + 1) * PLGap f g L xstar x0 0 := by ring

/-- **PL ⟹ ε-终止**：额外假设 `g x* = 0` 是 `x*` 处的次梯度（用来保证差距非负，
即 `x*` 是全局极小点）。则 `∀ ε > 0, ∃ n, gap_n < ε`。 -/
theorem pl_gd_converges {f g : ℝ → ℝ} {mu L x0 xstar : ℝ} (hmu : 0 < mu) (hL : 0 < L)
    (hmuL : mu ≤ L) (hSM : Smooth L f g) (hg0 : g xstar = 0)
    (hPL : PLCondition mu f g xstar)
    (hsub0 : Subgradient f xstar (g xstar)) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, PLGap f g L xstar x0 n < ε := by
  have hc0 : 0 ≤ 1 - mu / L := by
    rw [sub_nonneg, div_le_iff₀ hL]
    simpa using hmuL
  have hc1 : 1 - mu / L < 1 := by
    have hpos : 0 < mu / L := div_pos hmu hL
    linarith
  have hnonneg : ∀ n : ℕ, 0 ≤ PLGap f g L xstar x0 n := by
    intro n
    have h := hsub0 (SubgradientIterate g (1 / L) n x0)
    simp only [hg0, zero_mul, add_zero] at h
    exact sub_nonneg.mpr h
  have hstep : ∀ n : ℕ, PLGap f g L xstar x0 (n + 1) ≤
      (1 - mu / L) * PLGap f g L xstar x0 n := by
    intro n
    exact pl_gd_contraction_step (x := SubgradientIterate g (1 / L) n x0)
      hmu hL hSM hg0 hPL
  exact contraction_converges (1 - mu / L) hc0 hc1 hstep hnonneg

/-! ## 注：闭环语义与诚实边界
  强凸 ⟹ PL（`strong_convex_implies_PL`，同常数）→ PL 单步收缩
  （`pl_gd_contraction` / `pl_gd_contraction_step`）→ 线性率
  （`pl_gd_linear_rate`）→ ε-终止（`pl_gd_converges`）。
  PL 的关键优势：**不要求凸性**，因此该率链条适用于非凸的光滑目标（只要
  PL 成立）；但本文件的收敛定理用 `Subgradient f x* 0` 保证差距非负。
  诚实降级：**「PL 但不强凸」的机器验证反例未做**（见文件头）。 -/

end Lattice
