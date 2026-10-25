import Mathlib
import Lattice.Lib.Chain.RealPMix
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: ADMM（交替方向乘子法）—— 更新算子性质、残差界与可解实例的收敛

RealPMix 给出等式约束的增广拉格朗日 `L_aug(x,μ) = L_CE x + (a x − b)² + μ(a x − b)`
及其驻点 ⟺ 满足的刻画。本文件把增广拉格朗日推广到**分裂形式**

    min  f(x) + h(z)   s.t.  a·x + b·z = c

并形式化 ADMM 的三步更新：

    x⁺ = argmin_x L_ρ(x, z, y)
    z⁺ = argmin_z L_ρ(x⁺, z, y)
    y⁺ = y + ρ·(a·x⁺ + b·z⁺ − c)

其中增广拉格朗日

    L_ρ(x, z, y) = f(x) + h(z) + y·(a·x + b·z − c) + (ρ/2)·(a·x + b·z − c)²

定理清单（一般情形：更新算子的性质 + 残差界）：
  1. `augmentedLagrangian`（def，分裂形式的增广拉格朗日）；
     `augmentedLagrangian_matches_pmix`（**衔接 RealPMix**）：h ≡ 0、b = 0、ρ = 2 时
     它恰是 `RealPMix.AugLagrangian`；
  2. `admmDualUpdate`（def）：`y⁺ = y + ρ(a x + b z − c)`；
  3. `admm_dual_ascent`（**对偶上升恒等式**）：
        `L_ρ(x, z, y⁺) = L_ρ(x, z, y) + ρ·(a x + b z − c)²`，
     ρ ≥ 0 时右端不降——对偶更新的上升性质；另有严格版本（r ≠ 0 时严格上升）；
  4. `admm_x_minimizer` / `admm_z_minimizer`（**x/z 更新是最小化增广拉格朗日**）；
     `admm_x_stationarity` / `admm_z_stationarity`（**一阶最优性条件**）：
     x 更新是 `L_ρ(·, z, y)` 的最小点（h ≡ 0、f 可导）⟹
        `f'(x) + a·y + ρ·a·(a x + b z − c) = 0`；
  5. `admm_residual_eq_dual_change`：对偶变化 = ρ·原始残差；
     `admm_residual_bound`（**原始残差界**）：由 x-最优性得
        `a x + b z − c = −(f'(x) + a y)/(ρ a)`（ρ,a ≠ 0），
     即残差 = 一阶最优性违背量 / ρ；
     `admm_residual_le_of_grad_bound`：`|f'(x) + a y| ≤ M ⟹ |r| ≤ M/(ρ a)`；
     `admm_residual_single_step`（单步变化界）：
        `|r(x',z') − r(x,z)| ≤ |a|·|x'−x| + |b|·|z'−z|`；
  6. `admmUpdate`（def，单步状态更新）及其投影恒等式；
  7. **可解实例的完整收敛**（等式约束二次问题 `min (α/2)x² s.t. x = c`）：
     `admmScalarXStep` / `admmScalarYStep` / `admmScalarYIterate` / `admmScalarYError`；
     `admmScalarXStep_is_minimizer`（精确最小点）；
     `admmScalarYStep_eq`、`admm_contraction`（**对偶误差收缩**，系数 α/(α+ρ)）；
     `admm_converges`（ε-终止，连接 `RealConvergence.contraction_converges`）；
     `admm_scalar_primal_feasibility` / `admm_scalar_primal_converges`
     （原始可行性 `|x_k − c| = 误差/(α+ρ) → 0`）。

诚实边界（**降级说明**）：
  · ADMM 的**完整全局收敛**（原始残差与对偶残差的单调性、O(1/k) 遍历率）需要凸分析中
    的次梯度/单调算子理论（如 Moreau 分解、变分不等式框架），本仓库未形式化。
    本文件因此诚实地只做「**更新算子的精确性质 + 残差界**」，并对**一个可精确求解的
    实例**（等式约束二次问题）给出完整的收缩率与 ε-终止证明；
  · 一般情形下原始残差**并不单调**（这是 ADMM 的已知事实），故本文件不声称残差单调性，
    只给出精确恒等式与单步变化界；
  · argmin 以**关系式**（`IsADMMXStep` 的 `∀x'` 形式）与**选择函数**（`admmScalarXStep`
    等）两种方式给出，避免在 Lean 中使用选择公理式的 `argmin`；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Lattice

/-! ## 一、分裂形式的增广拉格朗日 -/

/-- **分裂形式的增广拉格朗日**（等式约束 `a·x + b·z = c`）：
`f x + h z + y·(a x + b z − c) + (ρ/2)·(a x + b z − c)²`。 -/
def augmentedLagrangian (f h : ℝ → ℝ) (a b c ρ : ℝ) (x z y : ℝ) : ℝ :=
  f x + h z + y * (a * x + b * z - c) + (ρ / 2) * (a * x + b * z - c) ^ 2

/-- 原始残差 `r = a·x + b·z − c`。 -/
def admmResidual (a b c x z : ℝ) : ℝ := a * x + b * z - c

/-- **对偶（乘子）更新**：`y⁺ = y + ρ·r`。 -/
def admmDualUpdate (a b c ρ x z y : ℝ) : ℝ := y + ρ * admmResidual a b c x z

/-- **x-更新**（关系式）：x 使 `L_ρ(·, z, y)` 取到全局最小。 -/
def IsADMMXStep (f h : ℝ → ℝ) (a b c ρ x z y : ℝ) : Prop :=
  ∀ x' : ℝ, augmentedLagrangian f h a b c ρ x z y
    ≤ augmentedLagrangian f h a b c ρ x' z y

/-- **z-更新**（关系式）：z 使 `L_ρ(x, ·, y)` 取到全局最小。 -/
def IsADMMZStep (f h : ℝ → ℝ) (a b c ρ x z y : ℝ) : Prop :=
  ∀ z' : ℝ, augmentedLagrangian f h a b c ρ x z y
    ≤ augmentedLagrangian f h a b c ρ x z' y

/-- ADMM 状态 `(x, z, y)`。 -/
abbrev ADMMState := ℝ × ℝ × ℝ

/-- **ADMM 单步**：给定 x-选择函数 `sx : z → y → x` 与 z-选择函数 `sz : x → y → z`，
    `x⁺ = sx z y`，`z⁺ = sz x⁺ y`，`y⁺ = y + ρ(a x⁺ + b z⁺ − c)`。 -/
def admmUpdate (sx sz : ℝ → ℝ → ℝ) (a b c ρ : ℝ) (st : ADMMState) : ADMMState :=
  let x := sx st.2.1 st.2.2
  let z := sz x st.2.2
  (x, z, admmDualUpdate a b c ρ x z st.2.2)

/-! ## 二、与 RealPMix 的衔接 -/

/-- **衔接 RealPMix**：h ≡ 0、b = 0、ρ = 2 时，分裂形式的增广拉格朗日恰是
`RealPMix.AugLagrangian`（`L_CE x + (a x − b)² + μ(a x − b)`），变量对应
`z ↦ 0`、`c ↦ b`、`y ↦ μ`。 -/
theorem augmentedLagrangian_matches_pmix (L_CE : ℝ → ℝ) (a b x μ : ℝ) :
    augmentedLagrangian L_CE (fun _ : ℝ => 0) a 0 b 2 x 0 μ = AugLagrangian L_CE a b x μ := by
  unfold augmentedLagrangian AugLagrangian
  ring

/-! ## 三、对偶上升（乘子更新的上升性质） -/

/-- **对偶上升恒等式**：`L_ρ(x, z, y⁺) = L_ρ(x, z, y) + ρ·r²`，其中 `r = a x + b z − c`。

证明：把 `y⁺ = y + ρ r` 代入并展开 `y⁺ r + (ρ/2) r² = y r + ρ r² + (ρ/2) r²`。 -/
theorem admm_dual_ascent (f h : ℝ → ℝ) (a b c ρ x z y : ℝ) :
    augmentedLagrangian f h a b c ρ x z (admmDualUpdate a b c ρ x z y)
      = augmentedLagrangian f h a b c ρ x z y + ρ * admmResidual a b c x z ^ 2 := by
  unfold augmentedLagrangian admmDualUpdate admmResidual
  ring

/-- 对偶上升（不降）：ρ ≥ 0 时 `L_ρ(x, z, y⁺) ≥ L_ρ(x, z, y)`。 -/
theorem admm_dual_ascent_mono (f h : ℝ → ℝ) (a b c ρ x z y : ℝ) (hρ : 0 ≤ ρ) :
    augmentedLagrangian f h a b c ρ x z y
      ≤ augmentedLagrangian f h a b c ρ x z (admmDualUpdate a b c ρ x z y) := by
  rw [admm_dual_ascent]
  have : 0 ≤ ρ * admmResidual a b c x z ^ 2 := mul_nonneg hρ (sq_nonneg _)
  linarith

/-- 对偶上升（严格）：ρ > 0 且残差非零时严格上升。 -/
theorem admm_dual_ascent_strict (f h : ℝ → ℝ) (a b c ρ x z y : ℝ) (hρ : 0 < ρ)
    (hr : admmResidual a b c x z ≠ 0) :
    augmentedLagrangian f h a b c ρ x z y
      < augmentedLagrangian f h a b c ρ x z (admmDualUpdate a b c ρ x z y) := by
  rw [admm_dual_ascent]
  have hpos : 0 < admmResidual a b c x z ^ 2 := by positivity
  have : 0 < ρ * admmResidual a b c x z ^ 2 := mul_pos hρ hpos
  linarith

/-- 对偶变量的变化恰为 `ρ·r`（原始残差的 ρ 倍）。 -/
theorem admm_residual_eq_dual_change (a b c ρ x z y : ℝ) :
    admmDualUpdate a b c ρ x z y - y = ρ * admmResidual a b c x z := by
  unfold admmDualUpdate
  ring

/-! ## 四、x/z 更新是最小化增广拉格朗日（及其一阶条件） -/

/-- **x-更新是最小化增广拉格朗日**（展开掉与 x 无关的 `h z`）。 -/
theorem admm_x_minimizer (f h : ℝ → ℝ) (a b c ρ x z y : ℝ)
    (hmin : IsADMMXStep f h a b c ρ x z y) (x' : ℝ) :
    f x + y * (a * x + b * z - c) + (ρ / 2) * (a * x + b * z - c) ^ 2
      ≤ f x' + y * (a * x' + b * z - c) + (ρ / 2) * (a * x' + b * z - c) ^ 2 := by
  have h := hmin x'
  unfold augmentedLagrangian at h
  linarith

/-- **z-更新是最小化增广拉格朗日**。 -/
theorem admm_z_minimizer (f h : ℝ → ℝ) (a b c ρ x z y : ℝ)
    (hmin : IsADMMZStep f h a b c ρ x z y) (z' : ℝ) :
    h z + y * (a * x + b * z - c) + (ρ / 2) * (a * x + b * z - c) ^ 2
      ≤ h z' + y * (a * x + b * z' - c) + (ρ / 2) * (a * x + b * z' - c) ^ 2 := by
  have h := hmin z'
  unfold augmentedLagrangian at h
  linarith

/-- 增广拉格朗日（h ≡ 0）沿 x 方向的导数：
`f'(x) + a·y + ρ·a·(a x + b z − c)`。 -/
lemma hasDerivAt_augmentedLagrangian_x {f : ℝ → ℝ} {f' a b c ρ z y x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t : ℝ => augmentedLagrangian f (fun _ : ℝ => 0) a b c ρ t z y)
      (f' + a * y + ρ * a * (a * x + b * z - c)) x := by
  -- 线性部分 `a·t + b·z − c` 的导数
  have hR : HasDerivAt (fun t : ℝ => a * t + b * z - c) a x := by
    have h1 : HasDerivAt (fun t : ℝ => a * t) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have h2 : HasDerivAt (fun _ : ℝ => b * z - c) 0 x := hasDerivAt_const x _
    have h3 := h1.add h2
    simpa only [sub_eq_add_neg, add_assoc, add_zero] using h3
  have hlin : HasDerivAt (fun t : ℝ => y * (a * t + b * z - c)) (y * a) x := hR.const_mul y
  have hquad : HasDerivAt (fun t : ℝ => (ρ / 2) * (a * t + b * z - c) ^ 2)
      ((ρ / 2) * (2 * (a * x + b * z - c) * a)) x := by
    have h := (hR.pow 2).const_mul (ρ / 2)
    simpa using h
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
  have h := ((hf.add hzero).add hlin).add hquad
  have hderiv : f' + 0 + y * a + (ρ / 2) * (2 * (a * x + b * z - c) * a)
      = f' + a * y + ρ * a * (a * x + b * z - c) := by ring
  rw [hderiv] at h
  simpa [augmentedLagrangian, add_assoc] using h

/-- **x-更新的一阶最优性条件**：h ≡ 0、f 在 x 处可导、x 是 `L_ρ(·, z, y)` 的全局最小点
⟹ `f'(x) + a·y + ρ·a·(a x + b z − c) = 0`。 -/
theorem admm_x_stationarity {f : ℝ → ℝ} {a b c ρ x z y : ℝ}
    (hd : DifferentiableAt ℝ f x)
    (hmin : IsADMMXStep f (fun _ : ℝ => 0) a b c ρ x z y) :
    deriv f x + a * y + ρ * a * (a * x + b * z - c) = 0 := by
  have hloc : IsLocalMin
      (fun t : ℝ => augmentedLagrangian f (fun _ : ℝ => 0) a b c ρ t z y) x := by
    refine IsMinOn.isLocalMin ?_ Filter.univ_mem
    intro t _
    exact hmin t
  have h0 : deriv (fun t : ℝ => augmentedLagrangian f (fun _ : ℝ => 0) a b c ρ t z y) x = 0 :=
    hloc.deriv_eq_zero
  have hder := hasDerivAt_augmentedLagrangian_x (f := f) (a := a) (b := b) (c := c) (ρ := ρ)
    (z := z) (y := y) (x := x) hd.hasDerivAt
  rw [hder.deriv] at h0
  exact h0

/-! ## 五、原始残差界 -/

/-- **原始残差 = 一阶最优性违背量 / (ρ a)**：由 x-更新的一阶条件直接得到。 -/
theorem admm_residual_bound {f : ℝ → ℝ} {a b c ρ x z y : ℝ} (ha : a ≠ 0) (hρ : ρ ≠ 0)
    (hd : DifferentiableAt ℝ f x)
    (hmin : IsADMMXStep f (fun _ : ℝ => 0) a b c ρ x z y) :
    admmResidual a b c x z = -(deriv f x + a * y) / (ρ * a) := by
  have hs := admm_x_stationarity hd hmin
  unfold admmResidual
  rw [eq_div_iff (mul_ne_zero hρ ha)]
  nlinarith [hs]

/-- **残差的定量界**：a > 0、ρ > 0 且一阶最优性违背量有界 `M` 时，`|r| ≤ M/(ρ a)`。 -/
theorem admm_residual_le_of_grad_bound {f : ℝ → ℝ} {a b c ρ x z y M : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hd : DifferentiableAt ℝ f x)
    (hmin : IsADMMXStep f (fun _ : ℝ => 0) a b c ρ x z y)
    (hM : |deriv f x + a * y| ≤ M) :
    |admmResidual a b c x z| ≤ M / (ρ * a) := by
  have hid := admm_residual_bound (ne_of_gt ha) (ne_of_gt hρ) hd hmin
  rw [hid, abs_div, abs_neg, abs_of_pos (mul_pos hρ ha)]
  exact div_le_div_of_nonneg_right hM (by positivity)

/-- **原始残差的单步变化界**：
`|r(x',z') − r(x,z)| ≤ |a|·|x'−x| + |b|·|z'−z|`（三角不等式）。 -/
theorem admm_residual_single_step (a b c x z x' z' : ℝ) :
    |admmResidual a b c x' z' - admmResidual a b c x z|
      ≤ |a| * |x' - x| + |b| * |z' - z| := by
  have he : admmResidual a b c x' z' - admmResidual a b c x z
      = a * (x' - x) + b * (z' - z) := by
    unfold admmResidual
    ring
  rw [he]
  calc |a * (x' - x) + b * (z' - z)|
      ≤ |a * (x' - x)| + |b * (z' - z)| := abs_add _ _
    _ = |a| * |x' - x| + |b| * |z' - z| := by rw [abs_mul, abs_mul]

/-! ## 六、单步更新算子的投影恒等式 -/

theorem admmUpdate_fst (sx sz : ℝ → ℝ → ℝ) (a b c ρ : ℝ) (st : ADMMState) :
    (admmUpdate sx sz a b c ρ st).1 = sx st.2.1 st.2.2 := rfl

theorem admmUpdate_snd_fst (sx sz : ℝ → ℝ → ℝ) (a b c ρ : ℝ) (st : ADMMState) :
    (admmUpdate sx sz a b c ρ st).2.1 = sz (sx st.2.1 st.2.2) st.2.2 := rfl

theorem admmUpdate_snd_snd (sx sz : ℝ → ℝ → ℝ) (a b c ρ : ℝ) (st : ADMMState) :
    (admmUpdate sx sz a b c ρ st).2.2
      = admmDualUpdate a b c ρ (sx st.2.1 st.2.2) (sz (sx st.2.1 st.2.2) st.2.2) st.2.2 :=
  rfl

/-- **单步更新确实执行了 x-更新与 z-更新**：若 `sx z y` 与 `sz x y` 分别是 x/z-更新，
则 `admmUpdate` 产出的状态满足 `IsADMMXStep` 与 `IsADMMZStep`（对「选择函数给出的值
恰是极小点」这一假设的直接翻译）。 -/
theorem admmUpdate_is_step (sx sz : ℝ → ℝ → ℝ) (f h : ℝ → ℝ) (a b c ρ : ℝ) (st : ADMMState)
    (hx : IsADMMXStep f h a b c ρ (sx st.2.1 st.2.2) st.2.1 st.2.2)
    (hz : IsADMMZStep f h a b c ρ (sx st.2.1 st.2.2) (sz (sx st.2.1 st.2.2) st.2.2) st.2.2) :
    (admmUpdate sx sz a b c ρ st).1 = sx st.2.1 st.2.2 ∧
      (admmUpdate sx sz a b c ρ st).2.1 = sz (sx st.2.1 st.2.2) st.2.2 ∧
      IsADMMXStep f h a b c ρ (admmUpdate sx sz a b c ρ st).1 st.2.1 st.2.2 ∧
      IsADMMZStep f h a b c ρ (admmUpdate sx sz a b c ρ st).1
        (admmUpdate sx sz a b c ρ st).2.1 st.2.2 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simpa only [admmUpdate_fst] using hx
  · simpa only [admmUpdate_fst, admmUpdate_snd_fst] using hz

/-! ## 七、可解实例：等式约束二次问题 `min (α/2)x²  s.t.  x = c`

这是 `a = 1, b = 0` 的特例，增广拉格朗日

    L_ρ(x, y) = (α/2)x² + y(x − c) + (ρ/2)(x − c)²

的 x-极小点有显式解 `x⁺ = (ρ c − y)/(α + ρ)`，对偶更新 `y⁺ = y + ρ(x⁺ − c)`，
误差 `y − y*`（`y* = −α c`）按 **α/(α+ρ)** 收缩。 -/

/-- x-更新（精确解）：`x⁺ = (ρ c − y)/(α + ρ)`。 -/
def admmScalarXStep (α ρ c y : ℝ) : ℝ := (ρ * c - y) / (α + ρ)

/-- 对偶更新：`y⁺ = y + ρ(x⁺ − c)`。 -/
def admmScalarYStep (α ρ c y : ℝ) : ℝ := y + ρ * (admmScalarXStep α ρ c y - c)

/-- 对偶迭代。 -/
def admmScalarYIterate (α ρ c : ℝ) : ℕ → ℝ → ℝ
  | 0, y => y
  | n + 1, y => admmScalarYStep α ρ c (admmScalarYIterate α ρ c n y)

/-- 第 n 步的对偶误差 `‖y_n − y*‖`，`y* = −α c`。 -/
def admmScalarYError (α ρ c y0 : ℝ) (n : ℕ) : ℝ :=
  ‖admmScalarYIterate α ρ c n y0 + α * c‖

/-- **x-更新是精确最小点**：`α + ρ > 0` 时 `x⁺ = (ρc − y)/(α+ρ)` 最小化
`x ↦ (α/2)x² + y(x−c) + (ρ/2)(x−c)²`（后者与 `x⁺` 之差恰为 `((α+ρ)/2)(x−x⁺)²`）。 -/
theorem admmScalarXStep_is_minimizer (α ρ c y x : ℝ) (h : 0 < α + ρ) :
    (α / 2) * admmScalarXStep α ρ c y ^ 2
        + y * (admmScalarXStep α ρ c y - c)
        + (ρ / 2) * (admmScalarXStep α ρ c y - c) ^ 2
      ≤ (α / 2) * x ^ 2 + y * (x - c) + (ρ / 2) * (x - c) ^ 2 := by
  have hne : α + ρ ≠ 0 := ne_of_gt h
  have hident : (α / 2) * x ^ 2 + y * (x - c) + (ρ / 2) * (x - c) ^ 2
      - ((α / 2) * admmScalarXStep α ρ c y ^ 2
        + y * (admmScalarXStep α ρ c y - c)
        + (ρ / 2) * (admmScalarXStep α ρ c y - c) ^ 2)
      = ((α + ρ) / 2) * (x - admmScalarXStep α ρ c y) ^ 2 := by
    unfold admmScalarXStep
    field_simp
    ring
  have hnn : 0 ≤ ((α + ρ) / 2) * (x - admmScalarXStep α ρ c y) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- **对偶更新的显式形式**：`y⁺ = (α y − ρ α c)/(α + ρ)`。 -/
theorem admmScalarYStep_eq (α ρ c y : ℝ) (h : α + ρ ≠ 0) :
    admmScalarYStep α ρ c y = (α * y - ρ * α * c) / (α + ρ) := by
  unfold admmScalarYStep admmScalarXStep
  field_simp
  ring

/-- **对偶误差的精确递推**：`y_{n+1} + α c = (α/(α+ρ))·(y_n + α c)`。 -/
theorem admmScalarYError_recurrence (α ρ c y0 : ℝ) (h : α + ρ ≠ 0) (n : ℕ) :
    admmScalarYIterate α ρ c (n + 1) y0 + α * c
      = (α / (α + ρ)) * (admmScalarYIterate α ρ c n y0 + α * c) := by
  show admmScalarYStep α ρ c (admmScalarYIterate α ρ c n y0) + α * c
      = (α / (α + ρ)) * (admmScalarYIterate α ρ c n y0 + α * c)
  rw [admmScalarYStep_eq α ρ c (admmScalarYIterate α ρ c n y0) h]
  field_simp
  ring

/-- **对偶误差的收缩**：`0 < α`、`0 < ρ`、`α + ρ > 0` 时
`‖y⁺ + α c‖ ≤ (α/(α+ρ))·‖y + α c‖`。 -/
theorem admm_contraction (α ρ c y : ℝ) (hα : 0 < α) (hρ : 0 < ρ) :
    ‖admmScalarYStep α ρ c y + α * c‖ ≤ (α / (α + ρ)) * ‖y + α * c‖ := by
  have hsum : α + ρ ≠ 0 := by positivity
  have key : admmScalarYStep α ρ c y + α * c = (α / (α + ρ)) * (y + α * c) := by
    rw [admmScalarYStep_eq α ρ c y hsum]
    field_simp
    ring
  rw [key, norm_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ α / (α + ρ))]

/-- **对偶误差 ε-终止**：`0 < α`、`0 < ρ` ⟹ 对任意 ε > 0 存在 n 使
`‖y_n + α c‖ < ε`（连接 `RealConvergence.contraction_converges`）。 -/
theorem admm_converges (α ρ c y0 : ℝ) (hα : 0 < α) (hρ : 0 < ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, admmScalarYError α ρ c y0 n < ε := by
  set k : ℝ := α / (α + ρ) with hk
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hk1 : k < 1 := by
    rw [hk, div_lt_one (by positivity : (0 : ℝ) < α + ρ)]
    linarith
  have hstep : ∀ n : ℕ, admmScalarYError α ρ c y0 (n + 1) ≤ k * admmScalarYError α ρ c y0 n := by
    intro n
    have hc := admm_contraction α ρ c (admmScalarYIterate α ρ c n y0) hα hρ
    rw [← hk] at hc
    simpa [admmScalarYError] using hc
  exact contraction_converges (e := fun n => admmScalarYError α ρ c y0 n) k
    hk0 hk1 hstep (fun n => by simp only [admmScalarYError]; positivity)

/-- **原始可行性由对偶误差控制**：`x⁺ − c = −(y + α c)/(α + ρ)`，故
`‖x⁺ − c‖ = ‖y + α c‖/(α + ρ)`。 -/
theorem admm_scalar_primal_feasibility (α ρ c y : ℝ) (hα : 0 < α) (hρ : 0 < ρ) :
    ‖admmScalarXStep α ρ c y - c‖ = ‖y + α * c‖ / (α + ρ) := by
  have hid : admmScalarXStep α ρ c y - c = -(y + α * c) / (α + ρ) := by
    unfold admmScalarXStep
    field_simp
    ring
  rw [hid, norm_div, norm_neg, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ α + ρ)]

/-- **原始可行性 ε-终止**：`0 < α`、`0 < ρ` ⟹ 对任意 ε > 0 存在 n 使
`‖x_n − c‖ < ε`（原始残差 → 0）。 -/
theorem admm_scalar_primal_converges (α ρ c y0 : ℝ) (hα : 0 < α) (hρ : 0 < ρ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, ‖admmScalarXStep α ρ c (admmScalarYIterate α ρ c n y0) - c‖ < ε := by
  intro ε hε
  have hpos : 0 < α + ρ := by linarith
  obtain ⟨n, hn⟩ := admm_converges α ρ c y0 hα hρ (ε * (α + ρ))
    (by positivity : 0 < ε * (α + ρ))
  refine ⟨n, ?_⟩
  rw [admm_scalar_primal_feasibility α ρ c (admmScalarYIterate α ρ c n y0) hα hρ]
  rw [div_lt_iff₀ hpos]
  simpa [admmScalarYError] using hn

/-! ## 注：闭环语义与诚实边界
  · 结构链：增广拉格朗日（含 RealPMix 的衔接）→ 三步更新 → 对偶上升恒等式 →
    x/z 最优性条件 → 残差界；
  · 与 RealPMix 的关系：那里的 `∂/∂μ = 0 ⟹ a x = b` 是「对偶更新强制约束满足」的
    静态版本；本文件的 `admm_dual_ascent` 是同一现象的动态版本
    （对偶变量按残差上升，增广拉格朗日恰增加 ρ r²）；
  · 与 RealConvergence 的关系：可解实例（第七节）的对偶误差满足线性收缩递推，
    直接接入 `contraction_converges` 得 ε-终止，并给出原始可行性收敛；
  · **诚实降级**：一般情形的完整 ADMM 收敛（原始/对偶残差单调性、O(1/k) 遍历率、
    凸性下的全局收敛）需要 Moreau 分解与单调算子理论，本仓库未形式化，
    故此处只证「更新算子的精确性质 + 残差界」，并以一个可精确求解的实例
    补足「收敛率 + ε-终止」的完整证明。 -/

end Lattice
