import Mathlib
import Lattice.Lib.Optim.RealNewtonMethod
/-!
# LATTICE: 牛顿法的局部二次收敛（一维）

`RealNewtonMethod` 给出了牛顿步在**二次函数**上的有限步（一步）精确收敛，并把
一般 `f` 的局部二次收敛标注为后续工作。本文件补齐一维的局部二次收敛率：

    |x_{n+1} − x*| ≤ C·|x_n − x*|²，    C = L/(2μ)，

并进一步证明**双重指数**衰减（误差的「误差常数」每步平方）。

定理清单：
  1. `newton_error_quadratic_bound`（**主定理**）：`μ > 0`、`∀ z, μ ≤ f'' z`、
     `L ≥ 0`、以及**二阶 Taylor 余项假设**
     `∀ z, |f' z − f'' z·(z − x*)| ≤ (L/2)(z − x*)²` ⟹
     `|NewtonStep f' f'' x − x*| ≤ (L/(2μ))·|x − x*|²`；
  2. `newton_contraction_half`：在收缩区 `(L/(2μ))·|x − x*| ≤ 1/2` 内误差至少减半；
  3. `newton_doubly_exponential`：令 `c = L/(2μ)`、`r_n = c·|x_n − x*|`，
     则 `r_n ≤ r_0^(2^n)`（`r_0 ≤ 1/2` 时即双重指数衰减）；
  4. `newton_exact_on_quadratic`：二次函数的 Taylor 余项假设以 `L = 0` 精确成立；
  5. `newton_exact_step_on_quadratic`：一致的二次一步精确（衔接 `RealNewtonMethod`）。

**诚实边界（重要）**：
- 主定理的核心假设 `htaylor` 是**二阶 Taylor 余项的线性化误差界**
  `f'(z) = f''(z)(z − x*) + O((z − x*)²)`。它**作为显式假设引入**：从
  `f ∈ C²`（`HasDerivAt`/`HasDerivAtFilter`）与 MVT / 二阶 Taylor 定理推导该假设
  **本文件未做**，并在此明确标注为**未证/降级**。命题本身为真（它就是局部二次收敛的
  标准中间引理），只是余项估计未在 Lean 中形式化；
- `∀ z, μ ≤ f'' z`（Hessian 的一致下界）与 `f'' z > 0` 也是显式假设；未从
  `ContDiff`/凸性推导；
- **未做**：`f' x* = 0` 的角色只在二次例子与 `RealNewtonMethod` 中体现；一般情形下
  「`f' x* = 0` ⟹ `f'' x*(x−x*)` 是 `f'` 的线性化」这一步未单独形式化；
- 一维；高维牛顿法（矩阵求逆、`H^{-1}∇f`）未做；
- 全程无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 一、主定理：单步误差的二次界 -/

/-- **牛顿法单步误差的二次上界（一维）**：`μ > 0`、`∀ z, μ ≤ f'' z`、`L ≥ 0`、
二阶 Taylor 余项界 `∀ z, |f' z − f'' z·(z − x*)| ≤ (L/2)(z − x*)²` ⟹
`|NewtonStep f' f'' x − x*| ≤ (L/(2μ))·|x − x*|²`。

证明：`x⁺ − x* = (f'' x·(x − x*) − f' x)/f'' x`；分子由 `htaylor` 界住，分母
`f'' x ≥ μ > 0`，相除即得。 -/
theorem newton_error_quadratic_bound {f' f'' : ℝ → ℝ} {xstar mu L x : ℝ}
    (hmu : 0 < mu) (hmu' : ∀ z, mu ≤ f'' z) (hL : 0 ≤ L)
    (htaylor : ∀ z, |f' z - f'' z * (z - xstar)| ≤ (L / 2) * (z - xstar) ^ 2) :
    |NewtonStep f' f'' x - xstar| ≤ (L / (2 * mu)) * |x - xstar| ^ 2 := by
  have hxpos : 0 < f'' x := lt_of_lt_of_le hmu (hmu' x)
  have he : NewtonStep f' f'' x - xstar
      = (f'' x * (x - xstar) - f' x) / f'' x := by
    unfold NewtonStep
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hxpos]
  have hnum : |f'' x * (x - xstar) - f' x| ≤ (L / 2) * (x - xstar) ^ 2 := by
    rw [abs_sub_comm]
    exact htaylor x
  have hA : 0 ≤ (L / 2) * (x - xstar) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h1 : |f'' x * (x - xstar) - f' x| / f'' x
      ≤ ((L / 2) * (x - xstar) ^ 2) / f'' x := by
    rw [div_le_div_iff hxpos hxpos]
    exact mul_le_mul_of_nonneg_right hnum (le_of_lt hxpos)
  have h2 : ((L / 2) * (x - xstar) ^ 2) / f'' x
      ≤ ((L / 2) * (x - xstar) ^ 2) / mu := by
    rw [div_le_div_iff hxpos hmu]
    exact mul_le_mul_of_nonneg_left (hmu' x) hA
  have h3 : ((L / 2) * (x - xstar) ^ 2) / mu = (L / (2 * mu)) * (x - xstar) ^ 2 := by
    field_simp
  have habs : |x - xstar| ^ 2 = (x - xstar) ^ 2 := sq_abs _
  rw [habs]
  linarith [h1, h2, h3]

/-! ## 二、收缩区与双重指数 -/

/-- **收缩区**：在 `(L/(2μ))·|x − x*| ≤ 1/2` 时，牛顿步把误差至少减半：
`|x⁺ − x*| ≤ (1/2)|x − x*|`。 -/
theorem newton_contraction_half {f' f'' : ℝ → ℝ} {xstar mu L x : ℝ}
    (hmu : 0 < mu) (hmu' : ∀ z, mu ≤ f'' z) (hL : 0 ≤ L)
    (htaylor : ∀ z, |f' z - f'' z * (z - xstar)| ≤ (L / 2) * (z - xstar) ^ 2)
    (hsmall : (L / (2 * mu)) * |x - xstar| ≤ 1 / 2) :
    |NewtonStep f' f'' x - xstar| ≤ (1 / 2) * |x - xstar| := by
  have h := newton_error_quadratic_bound hmu hmu' hL htaylor (x := x)
  have : (L / (2 * mu)) * |x - xstar| ^ 2
      = ((L / (2 * mu)) * |x - xstar|) * |x - xstar| := by ring
  rw [this] at h
  nlinarith [h, abs_nonneg (x - xstar), hsmall]

/-- **双重指数衰减（二次收敛率）**：给误差序列满足每步二次界
`|x_{n+1} − x*| ≤ c|x_n − x*|²`（`c = L/(2μ)`），则 `r_n ≤ r_0^(2^n)`，
其中 `r_n = c·|x_n − x*|`。

证明：`r_{n+1} ≤ r_n²`，归纳并用 `pow_le_pow_left₀` 与 `(r_0^(2^n))² = r_0^(2^(n+1))`。 -/
theorem newton_doubly_exponential {xseq : ℕ → ℝ} {xstar mu L : ℝ}
    (hmu : 0 < mu) (hL : 0 ≤ L)
    (hstep : ∀ n : ℕ, |xseq (n + 1) - xstar| ≤ (L / (2 * mu)) * |xseq n - xstar| ^ 2) :
    ∀ n : ℕ, (L / (2 * mu)) * |xseq n - xstar|
      ≤ ((L / (2 * mu)) * |xseq 0 - xstar|) ^ (2 ^ n) := by
  set c : ℝ := L / (2 * mu) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact div_nonneg hL (by positivity)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hrec : c * |xseq (n + 1) - xstar| ≤ (c * |xseq n - xstar|) ^ 2 := by
        calc
          c * |xseq (n + 1) - xstar| ≤ c * (c * |xseq n - xstar| ^ 2) :=
            mul_le_mul_of_nonneg_left (hstep n) hc0
          _ = (c * |xseq n - xstar|) ^ 2 := by ring
      have hrn : 0 ≤ c * |xseq n - xstar| := mul_nonneg hc0 (abs_nonneg _)
      calc
        c * |xseq (n + 1) - xstar| ≤ (c * |xseq n - xstar|) ^ 2 := hrec
        _ ≤ (((c * |xseq 0 - xstar|) ^ (2 ^ n))) ^ 2 :=
              pow_le_pow_left₀ hrn ih 2
        _ = (c * |xseq 0 - xstar|) ^ (2 ^ (n + 1)) := by
              rw [← pow_mul]
              congr 1

/-! ## 三、与 `RealNewtonMethod` 的衔接 -/

/-- **二次函数上 Taylor 余项假设精确成立（`L = 0`）**：对 `f z = (a/2)z² − b z`
（`RealNewtonMethod.Quadratic`）、`x* = b/a`，有
`f' z − f'' z·(z − x*) = 0`，故 `htaylor` 以 `L = 0` 成立。 -/
theorem newton_exact_on_quadratic {a b : ℝ} (ha : 0 < a) :
    ∀ z : ℝ, |deriv (Quadratic a b) z
        - deriv (deriv (Quadratic a b)) z * (z - b / a)| ≤ (0 / 2) * (z - b / a) ^ 2 := by
  intro z
  rw [deriv_quadratic, deriv_deriv_quadratic]
  have h : a * z - b - a * (z - b / a) = 0 := by
    field_simp
    ring
  rw [h, abs_zero]
  norm_num

/-- **二次一步精确（衔接 `RealNewtonMethod.newton_step_quadratic`）**：
`a ≠ 0` 时 `NewtonStep` 在二次函数上一步到达驻点 `b/a`。 -/
theorem newton_exact_step_on_quadratic {a b x : ℝ} (ha : a ≠ 0) :
    NewtonStep (deriv (Quadratic a b)) (deriv (deriv (Quadratic a b))) x = b / a :=
  newton_step_quadratic a b x ha

/-! ## 注：闭环语义与诚实边界
  单步二次界（`newton_error_quadratic_bound`）→ 收缩区（`newton_contraction_half`）
  → 双重指数（`newton_doubly_exponential`）；二次情形 `L = 0` 时退化为
  `RealNewtonMethod` 的一步精确（`newton_exact_on_quadratic` /
  `newton_exact_step_on_quadratic`）。
  诚实降级清单：`htaylor`（二阶 Taylor 余项）与 `f'' ≥ μ` 为**显式假设**，
  从 `C²` + MVT/`HasFTaylorSeriesUpTo` 推导未做；一维；高维牛顿未做。 -/

end Lattice
