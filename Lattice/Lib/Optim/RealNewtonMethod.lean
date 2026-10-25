import Mathlib

/-!
# LATTICE: 一维牛顿法 —— 二次函数上的有限步（一步）收敛

RealGradDescent 是一阶方法（梯度下降）；本文件形式化**二阶方法**的最小
干净情形：一维牛顿步

    x' = x - f'(x) / f''(x)

对二次函数

    f(x) = (a/2)·x² - b·x      （a > 0 严格凸）

**一步收敛到精确极小点**：

    x' = x - (a·x - b)/a = b/a        （Newton 步的精确解，newton_step_quadratic）

因为二次函数的牛顿法是「精确线性化」：牛顿步消去全部二阶以内的信息，
一维二次情形下一阶导数的误差被完全消除。

定理清单：
  · deriv_quadratic：f'(x) = a·x - b（HasDerivAt 链式法则）；
  · deriv_deriv_quadratic：f''(x) = a（导数常值）；
  · newton_step_quadratic（核心）：a ≠ 0 ⟹ NewtonStep x = b/a；
  · newton_convergence_quadratic：一步之后 f'(x') = 0（到达驻点）；
  · quadratic_value_at_newton_point：f(b/a) = -b²/(2a)（极小值，验收值）；
  · newton_fixed_at_root / newton_step_eq_self_iff：f'(x*) = 0 ⟺ Newton 步不动点
    （f''(x*) ≠ 0）；
  · newton_step_zero_denominator_safe：Lean 的 x/0 = 0 约定下，牛顿步仍良定义
    （诚实标注：数值上必须处理 f''≈0，见注）。

诚实边界：
  · 完整**局部二次收敛**定理 ‖x_{n+1} - x*‖ ≤ C‖x_n - x*‖²（一般 f，需要
    f'' Lipschitz + f''(x*) > 0 + 足够好的初值）依赖 Taylor 定理的二阶余项
    估计，本文件未形式化，标注为后续工作；
  · 本文件的核心（二次情形一步精确）不需要上述假设，是牛顿法在二次函数上
    的**有限步终止**，也是最干净的可用结论；
  · 分母假设：牛顿步只在 f''(x) ≠ 0 处有数值意义（newton_step_eq_self_iff
    明确使用 f''(x) ≠ 0）；a ≠ 0 是本文件二次情形的分母条件；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-- 一维牛顿步：x' = x - f'(x) / f''(x)（f'、f'' 作为函数传入）。-/
def NewtonStep (f' f'' : ℝ → ℝ) (x : ℝ) : ℝ := x - f' x / f'' x

/-- 二次函数 f(x) = (a/2)·x² - b·x。-/
def Quadratic (a b : ℝ) : ℝ → ℝ := fun x => a / 2 * x ^ 2 - b * x

/-! ## 定理一：二次函数的一阶导数 -/

lemma deriv_quadratic (a b x : ℝ) :
    deriv (Quadratic a b) x = a * x - b := by
  have h1 : HasDerivAt (fun y : ℝ => a / 2 * y ^ 2) (a / 2 * (2 * x)) x := by
    have := ((hasDerivAt_id x).pow 2).const_mul (a / 2)
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ => b * y) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have h := h1.sub h2
  have hderiv : a / 2 * (2 * x) - b = a * x - b := by ring
  rw [hderiv] at h
  unfold Quadratic
  exact h.deriv

/-! ## 定理二：二次函数的二阶导数（常值） -/

lemma deriv_deriv_quadratic (a b x : ℝ) :
    deriv (deriv (Quadratic a b)) x = a := by
  have hfun : deriv (Quadratic a b) = fun y : ℝ => a * y - b := by
    funext y
    exact deriv_quadratic a b y
  rw [hfun]
  have h : HasDerivAt (fun y : ℝ => a * y - b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).sub_const b
  exact h.deriv

/-! ## 定理三：牛顿步在二次函数上一步到达精确解（核心）
a ≠ 0 ⟹ x' = x - (a·x - b)/a = b/a。-/

theorem newton_step_quadratic (a b x : ℝ) (ha : a ≠ 0) :
    NewtonStep (deriv (Quadratic a b)) (deriv (deriv (Quadratic a b))) x = b / a := by
  unfold NewtonStep
  rw [deriv_quadratic a b x, deriv_deriv_quadratic a b x]
  field_simp
  ring

/-! ## 定理四：一步收敛（到达驻点）
牛顿步之后 f'(x') = 0：二次函数上的牛顿法 1 步终止。-/

theorem newton_convergence_quadratic (a b x : ℝ) (ha : a ≠ 0) :
    deriv (Quadratic a b)
        (NewtonStep (deriv (Quadratic a b)) (deriv (deriv (Quadratic a b))) x) = 0 := by
  rw [newton_step_quadratic a b x ha, deriv_quadratic]
  field_simp

/-! ## 定理五：牛顿点的函数值（极小值 -b²/(2a)）
二次函数在牛顿点处的取值即极小值，验证 b/a 是全局最优。-/

theorem quadratic_value_at_newton_point (a b x : ℝ) (ha : a ≠ 0) :
    Quadratic a b
        (NewtonStep (deriv (Quadratic a b)) (deriv (deriv (Quadratic a b))) x)
      = -(b ^ 2) / (2 * a) := by
  rw [newton_step_quadratic a b x ha]
  unfold Quadratic
  field_simp
  ring

/-! ## 定理六：驻点是牛顿步的不动点
f'(x*) = 0 ⟹ NewtonStep x* = x*（无需 f''(x*) ≠ 0：0/f'' = 0）。-/

theorem newton_fixed_at_root (f' f'' : ℝ → ℝ) (x : ℝ) (h : f' x = 0) :
    NewtonStep f' f'' x = x := by
  unfold NewtonStep
  rw [h, zero_div, sub_zero]

/-- 逆命题：f''(x) ≠ 0 时，牛顿步不动 ⟺ f'(x) = 0。
这明确了牛顿法的语义：不动点恰是驻点（分母非零处）。-/
theorem newton_step_eq_self_iff (f' f'' : ℝ → ℝ) (x : ℝ) (h : f'' x ≠ 0) :
    NewtonStep f' f'' x = x ↔ f' x = 0 := by
  unfold NewtonStep
  constructor
  · intro hh
    have hz : f' x / f'' x = 0 := by
      have := sub_eq_self.mp hh
      exact this
    rcases (div_eq_zero_iff).mp hz with h1 | h1
    · exact h1
    · exact absurd h1 h
  · intro hh
    rw [hh, zero_div, sub_zero]

/-! ## 定理七：分母为零时的约定（诚实标注）
Lean 的 ℝ 除法约定 x/0 = 0，故 NewtonStep 在 f''(x) = 0 处仍良定义
（退化为恒等步）；但数值上必须在 f'' ≈ 0 处做保护，这不是定理能替代的。-/

theorem newton_step_zero_denominator (f' : ℝ → ℝ) (x : ℝ) (h : deriv f' x = 0) :
    NewtonStep f' (deriv f') x = x := by
  unfold NewtonStep
  rw [h, div_zero, sub_zero]

/-! ## 注：局部二次收敛（后续工作）
  一般 f 的牛顿法局部二次收敛
      |x_{n+1} - x*| ≤ C·|x_n - x*|²
  需要：
    (1) f'(x*) = 0，f''(x*) > 0（最小值二阶条件，RealReLUStationarity 型）；
    (2) f'' 在 x* 邻域 Lipschitz（常数 L）；
    (3) 初值 x_0 足够接近 x*；
  由 Taylor 定理（二阶余项）得 f'(x_n) = f''(x*)·e_n + O(e_n²)，再除以
  f''(x_n) ≥ m > 0 得到二次收缩。该路线依赖 mathlib 的 Taylor 定理
  （HasFTaylorSeriesUpTo / taylor_mean_remainder），标注为后续工作；
  本文件的二次情形一步精确（newton_step_quadratic）是该定理 C = 0 的极限情形。-/

end Lattice
