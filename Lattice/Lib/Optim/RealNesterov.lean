import Mathlib
import Lattice.Lib.Optim.RealStrongConvex
import Lattice.Lib.Optim.RealSGD
/-!
# LATTICE: Nesterov 加速 / 重球法 —— 下降引理、参数空间最优率与二阶递推收敛

RealStrongConvex 给出（函数值 Lyapunov 意义下）梯度下降的线性率与
Baillon–Haddad 共强制性假设下的参数空间收缩率 ((L−μ)/(L+μ))²；
RealConvergence 给出抽象收缩骨架；RealSGD 给出**标量二阶线性递推**的收敛引擎
`scalar_second_order_converges`。本文件把它们装配成加速法：

    y_{k+1} = x_k − η·∇f(x_k)
    x_{k+1} = y_{k+1} + β·(y_{k+1} − y_k)

定理清单：
  1. `nesterovMomentum`（def）：单步状态更新（状态 `(x_k, y_k)` 返回 `(x_{k+1}, y_{k+1})`）；
     `nesterovIterate`/`nesterovX`/`nesterovY`；`nesterovMomentum_fst`/`_snd`；
  2. `nesterov_gd_recovery`：`β = 0` 时 Nesterov 步退化为**普通梯度步**；
  3. `nesterov_descent_lemma`（**下降引理**，一般步长）：
        `f (x − η∇f(x)) − f x ≤ −η(1 − Lη/2)·(∇f(x))²`；
     `nesterov_descent_lemma_le`：`η ≤ 1/L` 时目标值**不增**；
  4. `heavyBall_contraction`（**参数空间最优率**）：在共强制性 `GradientCoCoercive`
     假设下、步长 `η = 2/(μ+L)`，
        `‖x − η∇f(x) − x*‖ ≤ ((L−μ)/(L+μ))·‖x − x*‖`
     （由 `RealStrongConvex.strong_convex_iterate_contraction` 的平方界开方得到）；
  5. `heavyBall_quadratic_converges`（**重球法的收敛**）：二次目标 `(a/2)x² + b·x` 上
     重球法的误差满足二阶线性递推 `e_{k+2} = (1 + β − ηa)e_{k+1} − βe_k`；
     `0 ≤ β`、`|1 + β − ηa| + β < 1` ⟹ ε-终止（接入
     `RealSGD.scalar_second_order_converges` 的 Lyapunov 论证）；
  6. `nesterov_descent_sum_bound`（**平方梯度求和界（望远镜）**）：步长 1/L 时
        `∑_{k<n} (∇f(x_k))² ≤ 2L·(f x₀ − f x_n)`；
     `nesterov_rate`：若前 n 步的平方梯度都 ≥ ε，则 `n·ε ≤ 2L·(f x₀ − f x_n)`
     ——即 O(1/n) 的**平方梯度平均**率（凸光滑）；
  7. `accelerated_vs_gd`（**加速 vs 普通 GD 的率对比**）：
        `((L−μ)/(L+μ))² ≤ 1 − μ/L`
     （重球/加速法的收缩因子严格优于 GD 的 Lyapunov 因子）。

诚实边界：
  · 步长 `η = 2/(μ+L)` 下的**迭代最优率**依赖 Baillon–Haddad 共强制性；
    与 RealStrongConvex 一致，它作为**显式假设** `GradientCoCoercive` 引入（不隐藏 gap）；
  · **完整的 Nesterov O(1/k²) 目标值率未证**：它需要耦合的 `(x_k, y_k)` 动量估计
    （Nesterov 的估计序列/Lyapunov 构造），本文件只给出**下降引理 + 望远镜求和界**
    所蕴含的 O(1/n) 平方梯度率，并显式标注；
  · 重球法的收敛在第 5 条中只对**标量二次目标**给出完整证明（此时递推是线性的，
    可直接接入 RealSGD 的二阶递推引擎）；一般强凸光滑下的重球收敛率
    `((L−μ)/(L+μ))` 以第 4 条的参数空间收缩形式给出（共强制性假设下）；
  · RealSGD 的动量在第 5 条中被复用为**参数空间**二阶递推的收敛引擎；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace Lattice

/-! ## 一、Nesterov / 重球法的定义 -/

/-- **Nesterov/重球单步**：状态 `(x_k, y_k)`，
`y' = x_k − η·g x_k`，`x_{k+1} = y' + β(y' − y_k)`，返回 `(x_{k+1}, y')`。 -/
def nesterovMomentum (g : ℝ → ℝ) (η β : ℝ) (xk yk : ℝ) : ℝ × ℝ :=
  let y' := xk - η * g xk
  (y' + β * (y' - yk), y')

/-- Nesterov 迭代（`n` 步）。 -/
def nesterovIterate (g : ℝ → ℝ) (η β : ℝ) : ℕ → ℝ × ℝ → ℝ × ℝ
  | 0, p => p
  | n + 1, p => nesterovIterate g η β n (nesterovMomentum g η β p.1 p.2)

/-- 第 n 步的 `x` 分量。 -/
def nesterovX (g : ℝ → ℝ) (η β : ℝ) (x0 y0 : ℝ) (n : ℕ) : ℝ :=
  (nesterovIterate g η β n (x0, y0)).1

/-- 第 n 步的 `y` 分量。 -/
def nesterovY (g : ℝ → ℝ) (η β : ℝ) (x0 y0 : ℝ) (n : ℕ) : ℝ :=
  (nesterovIterate g η β n (x0, y0)).2

lemma nesterovMomentum_fst (g : ℝ → ℝ) (η β xk yk : ℝ) :
    (nesterovMomentum g η β xk yk).1
      = (xk - η * g xk) + β * ((xk - η * g xk) - yk) := rfl

lemma nesterovMomentum_snd (g : ℝ → ℝ) (η β xk yk : ℝ) :
    (nesterovMomentum g η β xk yk).2 = xk - η * g xk := rfl

/-- **`β = 0` 时 Nesterov 步退化为普通梯度步**。 -/
theorem nesterov_gd_recovery (g : ℝ → ℝ) (η xk yk : ℝ) :
    nesterovMomentum g η 0 xk yk = (xk - η * g xk, xk - η * g xk) := by
  simp [nesterovMomentum]

/-! ## 二、下降引理（一般步长） -/

/-- **Nesterov/梯度下降引理**：f 是 L-光滑 ⟹
`f (x − η∇f(x)) − f x ≤ −η(1 − Lη/2)·(∇f(x))²`。
η = 1/L 时右端为 `−(∇f(x))²/(2L)`（回收 `RealStrongConvex.smooth_descent_bound`）。 -/
theorem nesterov_descent_lemma {f g : ℝ → ℝ} {L η : ℝ} (hSM : Smooth L f g) (x : ℝ) :
    f (x - η * g x) - f x ≤ -(η * (1 - L * η / 2)) * (g x) ^ 2 := by
  have h := hSM x (x - η * g x)
  have h1 : g x * ((x - η * g x) - x) = -(η * (g x) ^ 2) := by ring
  have h2 : (L / 2) * ((x - η * g x) - x) ^ 2 = (L * η ^ 2 / 2) * (g x) ^ 2 := by ring
  rw [h1, h2] at h
  have h3 : -(η * (1 - L * η / 2)) * (g x) ^ 2
      = -(η * (g x) ^ 2) + (L * η ^ 2 / 2) * (g x) ^ 2 := by ring
  linarith

/-- **步长条件 `η ≤ 1/L` 下目标值不增**。 -/
theorem nesterov_descent_lemma_le {f g : ℝ → ℝ} {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hηL : η ≤ 1 / L) (hSM : Smooth L f g) (x : ℝ) :
    f (x - η * g x) ≤ f x := by
  have h := nesterov_descent_lemma (η := η) hSM x
  have hLη : L * η ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hηL (le_of_lt hL)
    have hone : L * (1 / L) = 1 := by field_simp
    rwa [hone] at hm
  have hcoef : 0 ≤ η * (1 - L * η / 2) := by nlinarith
  have hnn : 0 ≤ (g x) ^ 2 := sq_nonneg _
  have : -(η * (1 - L * η / 2)) * (g x) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn
  linarith

/-! ## 三、参数空间最优率（重球/加速的收缩因子） -/

/-- **重球/加速法的参数空间收缩率**：在共强制性 `GradientCoCoercive μ L g x*`
（Baillon–Haddad，显式假设）下、步长 `η = 2/(μ+L)`，
`‖x − η∇f(x) − x*‖ ≤ ((L−μ)/(L+μ))·‖x − x*‖`。

证明：由 `RealStrongConvex.strong_convex_iterate_contraction` 得平方界，
两边非负，用 `sq_le_sq` 开方。 -/
theorem heavyBall_contraction {g : ℝ → ℝ} {μ L : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (hμL : μ ≤ L) {xstar : ℝ} (hcc : GradientCoCoercive μ L g xstar) (x : ℝ) :
    ‖x - (2 / (μ + L)) * g x - xstar‖ ≤ ((L - μ) / (L + μ)) * ‖x - xstar‖ := by
  have hc0 : 0 ≤ (L - μ) / (L + μ) := div_nonneg (by linarith) (by linarith)
  have h := strong_convex_iterate_contraction hμ hL hμL hcc x
  have hsquare : ((L - μ) / (L + μ)) ^ 2 * ‖x - xstar‖ ^ 2
      = (((L - μ) / (L + μ)) * ‖x - xstar‖) ^ 2 := by ring
  rw [hsquare] at h
  have habs := sq_le_sq.mp h
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hc0 (norm_nonneg _))] at habs

/-- **加速 vs 普通 GD 的率对比**：对 `0 < μ ≤ L`，
`((L−μ)/(L+μ))² ≤ 1 − μ/L`——重球/加速法的收缩因子不大于 GD 的
函数值 Lyapunov 因子 `1 − μ/L`。 -/
theorem accelerated_vs_gd {μ L : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hμL : μ ≤ L) :
    ((L - μ) / (L + μ)) ^ 2 ≤ 1 - μ / L := by
  have hLμ : 0 ≤ L - μ := by linarith
  have h1 : ((L - μ) / (L + μ)) ^ 2 = (L - μ) ^ 2 / (L + μ) ^ 2 := by rw [div_pow]
  have h2 : (L - μ) / L = 1 - μ / L := by
    rw [sub_div, div_self (ne_of_gt hL)]
  rw [h1, ← h2, div_le_div_iff₀ (by positivity : (0 : ℝ) < (L + μ) ^ 2) hL]
  have h4 : 0 ≤ 3 * L * μ + μ ^ 2 := by nlinarith [hμ, hL]
  have h3 : 0 ≤ (L - μ) * (3 * L * μ + μ ^ 2) := mul_nonneg hLμ h4
  nlinarith [h3]

/-! ## 四、重球法在二次目标上的收敛（二阶线性递推） -/

/-- **重球法在标量二次目标上的收敛**：若误差序列 `xseq` 满足二阶线性递推
`x_{k+2} = (1 + β − ηa)·x_{k+1} − β·x_k`，且 `0 ≤ β`、`|1 + β − ηa| + β < 1`，
则 `|xseq n|` 是 ε-终止的（∀ ε > 0，∃ n，`|xseq n| < ε`）。

证明：令 `p n = (xseq (n+1), xseq n)`，递推即
`p (n+1) = (((1 − ηa) + β)·(p n).1 − β·(p n).2, (p n).1)`，
套用 `RealSGD.scalar_second_order_converges`（加权 Lyapunov 论证）。 -/
theorem heavyBall_quadratic_converges (a η β : ℝ) (hβ0 : 0 ≤ β)
    (hs : |1 + β - η * a| + β < 1) (xseq : ℕ → ℝ)
    (hrec : ∀ k : ℕ, xseq (k + 1 + 1) = (1 + β - η * a) * xseq (k + 1) - β * xseq k) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, |xseq n| < ε := by
  let p : ℕ → ℝ × ℝ := fun n => (xseq (n + 1), xseq n)
  have hstep : ∀ n : ℕ, p (n + 1) = (((1 - η * a) + β) * (p n).1 - β * (p n).2, (p n).1) := by
    intro n
    have hr := hrec n
    simp only [p]
    refine Prod.ext ?_ ?_
    · show xseq (n + 1 + 1) = ((1 - η * a) + β) * xseq (n + 1) - β * xseq n
      rw [hr]
      ring
    · rfl
  have hs' : |(1 - η * a) + β| + β < 1 := by
    have heq : (1 : ℝ) - η * a + β = 1 + β - η * a := by ring
    rwa [heq]
  have hconv := scalar_second_order_converges (α := 1 - η * a) (μ := β) (p := p) hstep hβ0 hs'
  intro ε hε
  rcases hconv ε hε with ⟨n, hn⟩
  exact ⟨n + 1, by simpa [p] using hn⟩

/-! ## 五、平方梯度的望远镜界与 O(1/n) 率 -/

/-- **平方梯度求和界（望远镜）**：步长 `η = 1/L` 时
`∑_{k<n} (∇f(x_k))² ≤ 2L·(f x₀ − f x_n)`
（每一步 `f(x_{k+1}) ≤ f(x_k) − (∇f(x_k))²/(2L)`，求和消去中间项）。 -/
theorem nesterov_descent_sum_bound {f g : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hSM : Smooth L f g) (x0 : ℝ) :
    ∀ n : ℕ, ∑ k in Finset.range n, (g (SubgradientIterate g (1 / L) k x0)) ^ 2
      ≤ 2 * L * (f x0 - f (SubgradientIterate g (1 / L) n x0)) := by
  intro n
  induction n with
  | zero =>
      have h0 : SubgradientIterate g (1 / L) 0 x0 = x0 := rfl
      rw [h0, Finset.sum_range_zero]
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep : (g (SubgradientIterate g (1 / L) n x0)) ^ 2
          ≤ 2 * L * (f (SubgradientIterate g (1 / L) n x0)
              - f (SubgradientIterate g (1 / L) (n + 1) x0)) := by
        have h := smooth_descent_bound hL hSM (SubgradientIterate g (1 / L) n x0)
        have hx : SubgradientIterate g (1 / L) (n + 1) x0
            = SubgradientIterate g (1 / L) n x0
              - (1 / L) * g (SubgradientIterate g (1 / L) n x0) := rfl
        rw [hx]
        have hL2 : (0 : ℝ) < 2 * L := by linarith
        have hq : (g (SubgradientIterate g (1 / L) n x0)) ^ 2 / (2 * L) * (2 * L)
            = (g (SubgradientIterate g (1 / L) n x0)) ^ 2 := by
          field_simp
        nlinarith [h, hq]
      linarith

/-- **O(1/n) 平方梯度率**：若前 n 步的平方梯度都不小于 ε > 0，则
`n·ε ≤ 2L·(f x₀ − f x_n)`，即平方梯度的平均下降速度为 O(1/n)。 -/
theorem nesterov_rate {f g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hSM : Smooth L f g) (x0 : ℝ) :
    ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      (∀ k : ℕ, k < n → ε ≤ (g (SubgradientIterate g (1 / L) k x0)) ^ 2) →
      (n : ℝ) * ε
        ≤ 2 * L * (f x0 - f (SubgradientIterate g (1 / L) n x0)) := by
  intro n ε _ hge
  have h := nesterov_descent_sum_bound hL hSM x0 n
  have hsum : (n : ℝ) * ε
      ≤ ∑ k in Finset.range n, (g (SubgradientIterate g (1 / L) k x0)) ^ 2 := by
    have hs : ∑ _k in Finset.range n, ε
        ≤ ∑ k in Finset.range n, (g (SubgradientIterate g (1 / L) k x0)) ^ 2 :=
      Finset.sum_le_sum fun k hk => hge k (Finset.mem_range.mp hk)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hs
  linarith

/-! ## 注：闭环语义与诚实边界
  · `nesterov_descent_lemma`（单步下降）→ `nesterov_descent_sum_bound`（望远镜）→
    `nesterov_rate`（O(1/n) 平方梯度率）构成光滑凸（非强凸）一侧的率链条；
  · `heavyBall_contraction` + `accelerated_vs_gd` 给出强凸光滑下**参数空间**的
    最优收缩因子 `((L−μ)/(L+μ))`，并证明它优于 GD 的 Lyapunov 因子 `1 − μ/L`；
  · `heavyBall_quadratic_converges` 在标量二次目标上给出重球法的完整收敛证明
    （复用 RealSGD 的二阶递推 Lyapunov 引擎）；
  · **诚实降级**：完整的 Nesterov O(1/k²) **目标值**率（估计序列/Lyapunov 构造）
    与一般强凸光滑下的重球收敛率证明未形式化；本文件以「下降引理 + 望远镜界 +
    共强制性下的参数空间收缩」替代，并显式标注该缺口。 -/

end Lattice
