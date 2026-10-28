import Mathlib
import Lattice.Lib.Convex.RealSubgradient
import Lattice.Lib.Convex.RealSubgradientDescent
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: 随机梯度下降的期望收敛 —— 无偏估计 + 有限概率空间上的 O(1/√T)

RealSubgradientDescent 给出**确定性**次梯度下降的差距界：
    x_{t+1} = x_t − η·g_t，g_t ∈ ∂f(x_t)
    ⟹ 2η·Σ_{t<T}(f x_t − f x*) ≤ ‖x_0 − x*‖² + η²·Σ_{t<T}‖g_t‖²
    ⟹ ∃ t < T, f x_t − f x* ≤ (‖x_0 − x*‖² + η²TG²)/(2ηT) = O(GD/√T)。

本文件把它**随机化**：真实 SGD 每步拿到的是梯度的**无偏随机估计** ĝ（小批量采样），
在有限概率空间 (Ω, p)（`p ω ≥ 0`、`Σ p ω = 1`）上定义期望
    E[X] = Σ_ω p(ω)·X(ω)（`Expect`）。

核心链条：
  1. `sgd_update`：单步 x' = x − η·ĝ；
  2. `Expect_norm_sq_sgd_update`（代数核心）：期望意义下的平方距离展开
     E‖x − η·ĝ − x*‖² = (x−x*)² − 2η(x−x*)·E[ĝ] + η²·E[ĝ²]；
  3. `sgd_expectation_contraction`（单步期望收缩，主引理）：
     无偏 E[ĝ] = ∇f(x)（以 `Subgradient f x (Expect p g)` 表述）+
     二阶矩界 E[ĝ²] ≤ G² ⟹
     E‖x − η·ĝ − x*‖² ≤ ‖x − x*‖² − 2η(f x − f x*) + η²G²；
  4. `sgd_variance_identity` / `sgd_variance_nonneg`：方差恒等式
     Var[ĝ] = E[ĝ²] − (E[ĝ])² ≥ 0；
  5. `sgd_expectation_contraction_variance`：把 3 中的 η²E[ĝ²] 换写成
     η²((E[ĝ])² + Var[ĝ]) —— **方差项的显式作用**：噪声以 η²·Var 的代价抬高界；
  6. `sgd_expected_gap_sum_seq`（望远镜求和）：逐步期望收缩 ⟹
     2η·Σ_{t<T} E[f(x_t) − f x*] ≤ E‖x_0 − x*‖² + η²TG²；
  7. `sgd_expected_avg_gap` / `sgd_expected_min_gap`：平均与「存在一步」的期望差距界；
  8. `sgd_rate_bound`：最优步长 η = D/(G√T)（D² = E‖x_0 − x*‖²）⟹
     ∃ t < T, E[f(x_t) − f x*] ≤ D·G/√T = **O(1/√T)**；
  9. 对照：`sgd_deterministic_recovery`（估计退化 = 确定性次梯度步）。

诚实边界（重要）：
  · **概率空间的粒度**：这里把每步的估计视为**同一个有限概率空间** (Ω, p) 上的
    随机变量，并把「第 t 步的期望收缩」`hstep` 作为**假设**（逐步期望收缩条件）交给
    望远镜求和引理。单步定理 `sgd_expectation_contraction` 证明的是：在**任一固定状态
    x**（确定性）处、对无偏估计取期望，该逐步条件成立。把逐步条件从「无条件的
    随机过程」推出（滤子的条件期望、独立采样、塔性质）需要构造乘积概率空间，
    本文件**未**做这一构造——这是标注的后续工作，不是被掩盖的 gap；
  · 期望线性性只需要 Σp = 1；`p ≥ 0` 用于期望的单调性（`Expect_nonneg`）；
  · 一维 ℝ（与 RealSubgradientDescent 的确定性对照同口径）；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {Ω : Type*} [Fintype Ω]

/-! ## 一、有限概率空间上的期望 -/

/-- 有限概率空间上的期望：E[X] = Σ_ω p(ω)·X(ω)。 -/
def Expect (p : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, p ω * X ω

/-- 期望对常数函数：E[c] = (Σ p)·c。 -/
lemma Expect_const (p : Ω → ℝ) (c : ℝ) :
    Expect p (fun _ : Ω => c) = (∑ ω, p ω) * c := by
  simp only [Expect]
  rw [Finset.sum_mul]

/-- 期望对常系数乘法：E[c·X] = c·E[X]。 -/
lemma Expect_const_mul (p : Ω → ℝ) (c : ℝ) (X : Ω → ℝ) :
    Expect p (fun ω => c * X ω) = c * Expect p X := by
  simp only [Expect]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- 期望可加。 -/
lemma Expect_add (p : Ω → ℝ) (X Y : Ω → ℝ) :
    Expect p (fun ω => X ω + Y ω) = Expect p X + Expect p Y := by
  simp only [Expect]
  rw [show (∑ ω, p ω * (X ω + Y ω)) = ∑ ω, (p ω * X ω + p ω * Y ω) from
    Finset.sum_congr rfl (fun ω _ => by ring)]
  rw [Finset.sum_add_distrib]

/-- 期望可减。 -/
lemma Expect_sub (p : Ω → ℝ) (X Y : Ω → ℝ) :
    Expect p (fun ω => X ω - Y ω) = Expect p X - Expect p Y := by
  simp only [Expect]
  rw [show (∑ ω, p ω * (X ω - Y ω)) = ∑ ω, (p ω * X ω - p ω * Y ω) from
    Finset.sum_congr rfl (fun ω _ => by ring)]
  rw [Finset.sum_sub_distrib]

/-- 期望的单调性（用 p ≥ 0）。 -/
lemma Expect_nonneg {p : Ω → ℝ} (hp0 : ∀ ω, 0 ≤ p ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ Expect p X := by
  simp only [Expect]
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hp0 ω) (hX ω))

/-! ## 二、SGD 单步与期望平方距离的展开 -/

/-- SGD 单步：x' = x − η·ghat。 -/
def sgd_update (η x ghat : ℝ) : ℝ := x - η * ghat

/-- 确定性次梯度步是 SGD 步的特例（对照 RealSubgradientDescent）。 -/
theorem sgd_deterministic_recovery (η x grad : ℝ) :
    sgd_update η x grad = subgradient_descent_step η x grad := rfl

/-- 期望平方距离的展开（核心代数恒等式）：
E‖x − η·ĝ − x*‖² = (Σp)(x−x*)² − 2η(x−x*)·E[ĝ] + η²·E[ĝ²]。 -/
lemma Expect_norm_sq_sgd_update (p : Ω → ℝ) (x xstar η : ℝ) (g : Ω → ℝ) :
    Expect p (fun ω => ‖sgd_update η x (g ω) - xstar‖ ^ 2)
      = (∑ ω, p ω) * (x - xstar) ^ 2
        - 2 * η * (x - xstar) * Expect p g
        + η ^ 2 * Expect p (fun ω => g ω ^ 2) := by
  unfold sgd_update
  have hfun : (fun ω : Ω => ‖x - η * g ω - xstar‖ ^ 2)
      = (fun ω : Ω => ((x - xstar) ^ 2 - 2 * η * (x - xstar) * g ω) + η ^ 2 * (g ω) ^ 2) := by
    funext ω
    rw [Real.norm_eq_abs, sq_abs]
    ring
  rw [hfun]
  rw [Expect_add, Expect_sub, Expect_const, Expect_const_mul, Expect_const_mul]

/-- 期望平方距离非负。 -/
lemma ExpDist_nonneg (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (x : Ω → ℝ) (xstar : ℝ) :
    0 ≤ Expect p (fun ω => ‖x ω - xstar‖ ^ 2) :=
  Expect_nonneg hp0 (fun ω => sq_nonneg (‖x ω - xstar‖))

/-! ## 三、主引理：单步期望收缩 -/

/-- **SGD 单步期望收缩**。设 ĝ 是 ∇f(x) 的无偏估计（以 `Subgradient f x (Expect p g)`
刻画：E[ĝ] 是 f 在 x 处的梯度/次梯度），且二阶矩 E[‖ĝ‖²] ≤ G²。则
E‖x' − x*‖² ≤ ‖x − x*‖² − 2η(f x − f x*) + η²G²。 -/
theorem sgd_expectation_contraction {f : ℝ → ℝ} {p : Ω → ℝ} (g : Ω → ℝ)
    (hpsum : (∑ ω, p ω) = 1)
    (x xstar η G : ℝ) (hη : 0 ≤ η)
    (hsub : Subgradient f x (Expect p g))
    (hG : Expect p (fun ω => g ω ^ 2) ≤ G ^ 2) :
    Expect p (fun ω => ‖sgd_update η x (g ω) - xstar‖ ^ 2) ≤
      ‖x - xstar‖ ^ 2 - 2 * η * (f x - f xstar) + η ^ 2 * G ^ 2 := by
  have hexp := Expect_norm_sq_sgd_update (p := p) x xstar η g
  have hdec := subgradient_step_decrease hsub xstar
  have hnorm : ‖x - xstar‖ ^ 2 = (x - xstar) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  have hcross : 2 * η * (f x - f xstar) ≤ 2 * η * (x - xstar) * Expect p g := by
    nlinarith [hdec, hη]
  have hG' : η ^ 2 * Expect p (fun ω => g ω ^ 2) ≤ η ^ 2 * G ^ 2 :=
    mul_le_mul_of_nonneg_left hG (sq_nonneg η)
  rw [hexp, hpsum, one_mul, hnorm]
  nlinarith [hcross, hG']

/-! ## 四、方差项的显式作用 -/

/-- **方差恒等式**：Var[ĝ] = E[ĝ²] − (E[ĝ])²。 -/
theorem sgd_variance_identity (p : Ω → ℝ) (g : Ω → ℝ) (hpsum : (∑ ω, p ω) = 1) :
    Expect p (fun ω => (g ω - Expect p g) ^ 2)
      = Expect p (fun ω => g ω ^ 2) - (Expect p g) ^ 2 := by
  have hfun : (fun ω : Ω => (g ω - Expect p g) ^ 2)
      = (fun ω : Ω => (g ω ^ 2 - 2 * (Expect p g) * g ω) + (Expect p g) ^ 2) := by
    funext ω
    ring
  rw [hfun]
  rw [Expect_add, Expect_sub, Expect_const_mul, Expect_const, hpsum, one_mul]
  ring

/-- 方差非负：E[(ĝ − E[ĝ])²] ≥ 0（用 p ≥ 0）。 -/
theorem sgd_variance_nonneg (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (g : Ω → ℝ) :
    0 ≤ Expect p (fun ω => (g ω - Expect p g) ^ 2) :=
  Expect_nonneg hp0 (fun ω => sq_nonneg (g ω - Expect p g))

/-- **方差形式的期望收缩**：η²E[ĝ²] = η²((E[ĝ])² + Var[ĝ]），
即噪声方差以 η²·Var 的代价抬高单步界。 -/
theorem sgd_expectation_contraction_variance {f : ℝ → ℝ} {p : Ω → ℝ} (g : Ω → ℝ)
    (hpsum : (∑ ω, p ω) = 1)
    (x xstar η : ℝ) (hη : 0 ≤ η)
    (hsub : Subgradient f x (Expect p g)) :
    Expect p (fun ω => ‖sgd_update η x (g ω) - xstar‖ ^ 2) ≤
      ‖x - xstar‖ ^ 2 - 2 * η * (f x - f xstar)
        + η ^ 2 * ((Expect p g) ^ 2 + Expect p (fun ω => (g ω - Expect p g) ^ 2)) := by
  have hexp := Expect_norm_sq_sgd_update (p := p) x xstar η g
  have hvar := sgd_variance_identity (p := p) g hpsum
  have hdec := subgradient_step_decrease hsub xstar
  have hnorm : ‖x - xstar‖ ^ 2 = (x - xstar) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  have hcross : 2 * η * (f x - f xstar) ≤ 2 * η * (x - xstar) * Expect p g := by
    nlinarith [hdec, hη]
  rw [hexp, hpsum, one_mul, hnorm]
  nlinarith [hcross, hvar]

/-! ## 五、期望距离与期望差距 -/

/-- 期望平方距离：E‖x − x*‖²。 -/
def ExpDist (p : Ω → ℝ) (x : Ω → ℝ) (xstar : ℝ) : ℝ :=
  Expect p (fun ω => ‖x ω - xstar‖ ^ 2)

/-- 期望次优差距：E[f(x) − f(x*)]。 -/
def ExpGap (p : Ω → ℝ) (f : ℝ → ℝ) (x : Ω → ℝ) (xstar : ℝ) : ℝ :=
  Expect p (fun ω => f (x ω) - f xstar)

/-! ## 六、望远镜求和：逐步期望收缩 ⟹ 累积期望差距界 -/

/-- **期望收缩的望远镜求和**：若每一步的期望平方距离按
E_{t+1} ≤ E_t − 2η·Gap_t + η²G² 收缩，则
2η·Σ_{t<T} Gap_t ≤ E_0 + η²TG²。 -/
theorem sgd_expected_gap_sum_seq (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (f : ℝ → ℝ)
    (x : ℕ → Ω → ℝ) (xstar η G : ℝ) (T : ℕ) (_hη : 0 ≤ η)
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * G ^ 2) :
    2 * η * (∑ t in Finset.range T, ExpGap p f (x t) xstar) ≤
      ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2 := by
  have hstep_le : ∀ t : ℕ, 2 * η * ExpGap p f (x t) xstar ≤
      ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar + η ^ 2 * G ^ 2 := by
    intro t
    have h := hstep t
    nlinarith [h]
  have hsum : (∑ t in Finset.range T, 2 * η * ExpGap p f (x t) xstar) ≤
      ∑ t in Finset.range T,
        (ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar + η ^ 2 * G ^ 2) :=
    Finset.sum_le_sum (fun t _ => hstep_le t)
  have hsplit :
      (∑ t in Finset.range T,
          (ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar + η ^ 2 * G ^ 2))
        = (∑ t in Finset.range T,
            (ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar))
          + η ^ 2 * (∑ t in Finset.range T, G ^ 2) := by
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum]
  have hconst : (∑ t in Finset.range T, G ^ 2) = (T : ℝ) * G ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htel : (∑ t in Finset.range T,
        (ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar))
      = ExpDist p (x 0) xstar - ExpDist p (x T) xstar :=
    sum_range_sub_telescoping T
  have hET : 0 ≤ ExpDist p (x T) xstar :=
    ExpDist_nonneg p hp0 (x T) xstar
  have htel_le : (∑ t in Finset.range T,
        (ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar))
      ≤ ExpDist p (x 0) xstar := by
    rw [htel]
    linarith
  calc
    2 * η * (∑ t in Finset.range T, ExpGap p f (x t) xstar)
        = ∑ t in Finset.range T, 2 * η * ExpGap p f (x t) xstar := by
          rw [Finset.mul_sum]
    _ ≤ ∑ t in Finset.range T,
          (ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar + η ^ 2 * G ^ 2) := hsum
    _ = (∑ t in Finset.range T, (ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar))
          + η ^ 2 * (∑ t in Finset.range T, G ^ 2) := hsplit
    _ = (∑ t in Finset.range T, (ExpDist p (x t) xstar - ExpDist p (x (t + 1)) xstar))
          + η ^ 2 * ((T : ℝ) * G ^ 2) := by rw [hconst]
    _ ≤ ExpDist p (x 0) xstar + η ^ 2 * ((T : ℝ) * G ^ 2) := by
          exact add_le_add_right htel_le _
    _ = ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2 := by ring

/-! ## 七、平均 / 存在一步的期望差距界 -/

/-- 平均期望差距界：Σ_{t<T} E[f(x_t) − f x*] ≤ (E_0 + η²TG²)/(2η)。 -/
theorem sgd_expected_avg_gap (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (f : ℝ → ℝ)
    (x : ℕ → Ω → ℝ) (xstar G η : ℝ) (T : ℕ) (hη : 0 < η)
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * G ^ 2) :
    (∑ t in Finset.range T, ExpGap p f (x t) xstar) ≤
      (ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η) := by
  have h := sgd_expected_gap_sum_seq p hp0 f x xstar η G T (le_of_lt hη) hstep
  rw [le_div_iff₀ (by positivity : 0 < 2 * η)]
  nlinarith [h]

/-- **存在一步的期望差距界**：∃ t < T，
E[f(x_t) − f x*] ≤ (E_0 + η²TG²)/(2ηT)（min ≤ 平均）。 -/
theorem sgd_expected_min_gap (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (f : ℝ → ℝ)
    (x : ℕ → Ω → ℝ) (xstar G η : ℝ) (T : ℕ) (hη : 0 < η) (hT : 0 < T)
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * G ^ 2) :
    ∃ t : ℕ, t < T ∧
      ExpGap p f (x t) xstar ≤
        (ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ)) := by
  have havg := sgd_expected_avg_gap p hp0 f x xstar G η T hη hstep
  let B : ℝ := (ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η)
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hB : B = (T : ℝ) *
      ((ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ))) := by
    dsimp [B]
    field_simp [mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hη), hTne]
    ring
  have hcalc : (∑ t in Finset.range T, ExpGap p f (x t) xstar) ≤
      (T : ℝ) * ((ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ))) := by
    calc
      (∑ t in Finset.range T, ExpGap p f (x t) xstar) ≤ B := havg
      _ = (T : ℝ) * ((ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2)
            / (2 * η * (T : ℝ))) := hB
  rcases exists_le_sum_mul (a := fun t : ℕ => ExpGap p f (x t) xstar) hT hcalc with
    ⟨t, ht, hgap⟩
  exact ⟨t, ht, hgap⟩

/-! ## 八、最优步长 ⟹ O(1/√T) -/

/-- **一般半径形式的 O(1/T) 率**（s > 0、s² = T、η = D/(G·s)）：
∃ t < T, E[f(x_t) − f x*] ≤ D·G/s。 -/
theorem sgd_rate_bound_aux (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (f : ℝ → ℝ)
    (x : ℕ → Ω → ℝ) (xstar G D s η : ℝ) (T : ℕ)
    (hG : 0 < G) (hT : 0 < T) (hD : 0 < D) (hs : 0 < s)
    (hssq : s ^ 2 = (T : ℝ))
    (hD2 : ExpDist p (x 0) xstar = D ^ 2)
    (hη : η = D / (G * s))
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * G ^ 2) :
    ∃ t : ℕ, t < T ∧ ExpGap p f (x t) xstar ≤ D * G / s := by
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hDne : D ≠ 0 := ne_of_gt hD
  have hGne : G ≠ 0 := ne_of_gt hG
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hηpos : 0 < η := by
    rw [hη]
    exact div_pos hD (mul_pos hG hs)
  rcases sgd_expected_min_gap p hp0 f x xstar G η T hηpos hT hstep with ⟨t, ht, hgap⟩
  have hbnd : (ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ))
      = D * G / s := by
    have hs4 : s ^ 4 = (T : ℝ) ^ 2 := by
      calc
        s ^ 4 = (s ^ 2) ^ 2 := by ring
        _ = (T : ℝ) ^ 2 := by rw [hssq]
    rw [hD2, hη]
    have hden_ne : 2 * η * (T : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hηpos)) hTne
    have hmul_ne : G * s ≠ 0 := mul_ne_zero hGne hs_ne
    field_simp [hDne, hGne, hs_ne, hden_ne, hmul_ne]
    ring_nf
    rw [hssq, hs4]
    ring
  refine ⟨t, ht, ?_⟩
  calc
    ExpGap p f (x t) xstar
        ≤ (ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ)) := hgap
    _ = D * G / s := hbnd

/-- **SGD 的 O(GD/√T) 期望率**：`D ^ 2 = E‖x_0 − x*‖^2`、`η = D/(G·√T)` ⟹
`∃ t < T, E[f(x_t) − f x*] ≤ D·G/√T`。

## 假设清单（第 7 轮补齐）

⚠ **原来这里只列了 `D > 0`、`G > 0`、`T > 0`，漏掉了真正承重的 `hstep`。**
（`PROOF-DEBT` 的 `register` 条目正是这么判的：「doc 的假设清单不覆盖陈述」。）

| 前提 | 作用 | 可省否 |
|:--|:--|:--|
| `hD : 0 < D` | `D ^ 2 = E‖x_0 − x*‖^2` 是**距离的平方**，`D` 是半径 | 不可省（`D = 0` 时 `η = 0`） |
| `hG : 0 < G` | 二阶矩界 | 不可省（同上） |
| `hT : 0 < T` | 求平均需要非空序列 | 不可省 |
| **`hstep`** | **逐步期望收缩：`E_{t+1} ≤ E_t − 2η·Gap_t + η²G²`** | **这是本定理的实质前提** |

## 为什么 `hstep` 是**假设**而不是可补的缺口

这是本条最要紧的一点，**不是偷懒**：

1. **接口里有的是** `Subgradient f (x t) (Expect p (g t))`，即 `E[g_t]` 是 `f` 在 `x t` 处的次梯度；
2. **但 `x : ℕ → Ω → ℝ` 是随机过程**，所以 `x t` 逐 `ω` 变化，
   而 `Subgradient` 是在**一个点**上说的——两者**类型上就对不齐**
   （`PROOF-DEBT` 里那条 `B_missing` 写的 `Subgradient f (x t) (…)` 本身就是病式：
   `x t : Ω → ℝ` 而 `Subgradient` 要 `ℝ`）；
3. 唯一能把它对齐的方式是**逐路径**要求 `Subgradient f (x t ω) (g t ω)`，
   而那等于说**每个采样都是真次梯度**——**噪声就没了**，不是 SGD。

**标准证明靠的是条件期望**：`E[g_t | x_t] = ∇f(x_t)`，
于是交叉项 `E[⟨g_t, x_t − x*⟩] = E[⟨∇f(x_t), x_t − x*⟩]` 再由凸性控制。
⚠ **这需要一个带 σ-代数与滤流的概率空间**，而本形式化只有 `Expect p Y = ∑ ω, p ω · Y ω`
——**没有条件期望，就没有这一步**。

⭐ **所以 `hstep` 是这个接口下诚实的假设。** 能推出的是**确定性 `x` 的单步**：
见 `sgd_expectation_contraction`（`x : ℝ` 固定，`E[g]` 是次梯度，`E[g²] ≤ G²`）。

⭐ **第 13 轮补充**：上面那句「能推出的只有单步」已经**不再完整**。
新增的 `sgd_averaged_step`（§九）证明：对**确定性的平均迭代**
`X : ℕ → ℝ`、`X (t+1) = X t − η·E[g t]`，`hstep` 是**可导出的**——
关键是平方的 Jensen `Expect_sq_le`：`(E[Y])² ≤ E[Y²]`。

**边界因此更精确了，而不是更松**：

| 迭代类型 | `hstep` 能否导出 | 原因 |
|:--|:--|:--|
| 确定性 `X : ℕ → ℝ`，平均梯度更新 | **能**（`sgd_averaged_step`） | `Subgradient f (X t) (E[g t])` 与 `X t : ℝ` 类型对齐 |
| **随机** `x : ℕ → Ω → ℝ` | **不能**（本条仍需假设） | 逐 `ω` 的次梯度条件会消灭噪声；真证明需要条件期望 | -/
theorem sgd_rate_bound (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (f : ℝ → ℝ)
    (x : ℕ → Ω → ℝ) (xstar G D η : ℝ) (T : ℕ)
    (hG : 0 < G) (hT : 0 < T) (hD : 0 < D)
    (hD2 : ExpDist p (x 0) xstar = D ^ 2)
    (hη : η = D / (G * Real.sqrt (T : ℝ)))
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * G ^ 2) :
    ∃ t : ℕ, t < T ∧ ExpGap p f (x t) xstar ≤ D * G / Real.sqrt (T : ℝ) := by
  have hT0 : 0 ≤ (T : ℝ) := by exact_mod_cast le_of_lt hT
  have hs_pos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hs_sq : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) := Real.sq_sqrt hT0
  exact sgd_rate_bound_aux p hp0 f x xstar G D (Real.sqrt (T : ℝ)) η T hG hT hD
    hs_pos hs_sq hD2 hη hstep

/-! ## 注：闭环语义
  确定性次梯度下降（RealSubgradientDescent）→ 随机化估计（Expect）→
  单步期望收缩（sgd_expectation_contraction）→ 望远镜求和（sgd_expected_gap_sum_seq）
  → 平均/存在步差距（sgd_expected_avg_gap / sgd_expected_min_gap）→
  O(GD/√T) 率（sgd_rate_bound）。
  方差恒等式（sgd_variance_identity）显式分离出噪声项：η²·Var 是随机的代价。
  诚实标注：逐步期望收缩 hstep 作为假设给出（见文件头「诚实边界」）。 -/

/-! ## 九、⭐ Jensen（平方）：`(E[Y])² ≤ E[Y²]`，以及用它**导出的**一步界

### 为什么需要它

第 7 轮判定 `sgd_rate_bound` 的 `hstep`（逐步期望收缩）**不能**从接口推出，
并写清了理由：`Subgradient f (x t) (Expect p (g t))` 与**随机过程** `x : ℕ → Ω → ℝ` 类型上对不齐，
而标准证明需要**条件期望**，本形式化没有。

**那个结论是对的，但它有一个可做的特例**：若迭代是**确定的** `X : ℕ → ℝ`、
更新用**平均梯度** `X (t+1) = X t - η·E[g t]`，则 `E` 只在**一步之内**出现，
`Subgradient f (X t) (E[g t])` 与 `X t : ℝ` **类型对齐**。此时缺的只有一步：

> `‖E[Y]‖² ≤ E[‖Y‖²]`

即平方的 Jensen。有了它，`sgd_expectation_contraction`（确定性 `x` 的单步收缩）
就能推到**确定性的平均迭代**上，`hstep` 因此**可导**。

### 证明思路

加权 Cauchy–Schwarz：`(∑ pᵢyᵢ)² ≤ (∑ pᵢ)(∑ pᵢyᵢ²)`，再用 `∑ p = 1`。
写成 `√pᵢ` 的形式即可调用 mathlib 的 Cauchy–Schwarz。 -/

/-- ⭐⭐ **平方的 Jensen**：对概率权重，`(E[Y]) ^ 2 ≤ E[Y ^ 2]`。

`hp0`（非负）与 `hpsum`（和为 1）都承重：去掉 `hpsum` 结论变成 `(∑p)` 倍的关系；
去掉 `hp0` 则 `√p` 不成立。

证明是**加权 Cauchy–Schwarz**：`(∑ pᵢyᵢ)² ≤ (∑ pᵢ)(∑ pᵢyᵢ²)`，再用 `∑ p = 1`。
写成 `√pᵢ` 的形式即可调用 mathlib 的 Cauchy–Schwarz。 -/
theorem Expect_sq_le {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (hpsum : (∑ ω, p ω) = 1) (Y : Ω → ℝ) :
    (Expect p Y) ^ 2 ≤ Expect p (fun ω => (Y ω) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω)
    (fun ω => Real.sqrt (p ω)) (fun ω => Real.sqrt (p ω) * Y ω)
  have h1 : (∑ ω, Real.sqrt (p ω) * (Real.sqrt (p ω) * Y ω)) = Expect p Y := by
    unfold Expect
    refine Finset.sum_congr rfl ?_
    intro ω _
    rw [← mul_assoc, Real.mul_self_sqrt (hp0 ω)]
  have h2 : (∑ ω, Real.sqrt (p ω) ^ 2) = ∑ ω, p ω := by
    refine Finset.sum_congr rfl ?_
    intro ω _
    exact Real.sq_sqrt (hp0 ω)
  have h3 : (∑ ω, (Real.sqrt (p ω) * Y ω) ^ 2) = Expect p (fun ω => Y ω ^ 2) := by
    unfold Expect
    refine Finset.sum_congr rfl ?_
    intro ω _
    rw [mul_pow, Real.sq_sqrt (hp0 ω)]
  rw [h1, h2, h3, hpsum, one_mul] at hcs
  exact hcs
theorem sgd_averaged_step {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (hpsum : (∑ ω, p ω) = 1) (f : ℝ → ℝ) (X : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (xstar G η : ℝ) (hη : 0 ≤ η)
    (hupd : ∀ t, X (t + 1) = X t - η * Expect p (g t))
    (hsub : ∀ t, Subgradient f (X t) (Expect p (g t)))
    (hbnd : ∀ t, Expect p (fun ω => (g t ω) ^ 2) ≤ G ^ 2) :
    ∀ t, ‖X (t + 1) - xstar‖ ^ 2 ≤
      ‖X t - xstar‖ ^ 2 - 2 * η * (f (X t) - f xstar) + η ^ 2 * G ^ 2 := by
  intro t
  have hc := sgd_expectation_contraction (p := p) (g := g t) hpsum (X t) xstar η G hη
    (hsub t) (hbnd t)
  -- stated AFTER unfolding `sgd_update`, so the lambda shape matches `Expect_sub` syntactically
  have hlin : Expect p (fun ω => X t - η * g t ω) = X t - η * Expect p (g t) := by
    rw [Expect_sub, Expect_const, Expect_const_mul, hpsum, one_mul]
  have hmean : Expect p (fun ω => sgd_update η (X t) (g t ω) - xstar) = X (t + 1) - xstar := by
    unfold sgd_update
    rw [Expect_sub, Expect_const, hlin, hpsum, one_mul, hupd t]
  -- Jensen on `Y ω = sgd_update η (X t) (g t ω) - xstar`
  have hj := Expect_sq_le p hp0 hpsum (fun ω => sgd_update η (X t) (g t ω) - xstar)
  rw [hmean] at hj
  calc ‖X (t + 1) - xstar‖ ^ 2
      = (X (t + 1) - xstar) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ Expect p (fun ω => (sgd_update η (X t) (g t ω) - xstar) ^ 2) := hj
    _ = Expect p (fun ω => ‖sgd_update η (X t) (g t ω) - xstar‖ ^ 2) := by
        unfold Expect
        refine Finset.sum_congr rfl ?_
        intro ω _
        simp only [Real.norm_eq_abs, sq_abs]
    _ ≤ ‖X t - xstar‖ ^ 2 - 2 * η * (f (X t) - f xstar) + η ^ 2 * G ^ 2 := hc

/-! ## 十、⭐⭐ **最终形态**：一条**不带 `hstep`** 的率定理

§九 把 `hstep` 导出到了**确定性平均迭代**上。本节的率定理因此**前提里没有 `hstep`**——
它是被推出来的。

**做法**：把 `X : ℕ → ℝ` 嵌入为**常数随机变量** `x t := fun _ => X t`。
于是

- `ExpDist p (fun _ => c) xstar = (∑ p) · ‖c − x*‖²`；
- `ExpGap p f (fun _ => c) xstar = (∑ p) · (f c − f x*)`。

在 `∑ p = 1` 下两者退化成普通量，`sgd_averaged_step` 给出 `hstep`，再交给既有的
`sgd_rate_bound`。**所以这条定理的假设清单里只有更新规则、次梯度条件与二阶矩界。** -/

/-- **常数随机变量的期望平方距离**：`E‖c − x*‖² = (∑ p) · ‖c − x*‖²`。 -/
theorem ExpDist_const (p : Ω → ℝ) (c xstar : ℝ) :
    ExpDist p (fun _ : Ω => c) xstar = (∑ ω, p ω) * ‖c - xstar‖ ^ 2 := by
  unfold ExpDist
  rw [Expect_const]

/-- **常数随机变量的期望差距**：`E[f c − f x*] = (∑ p) · (f c − f x*)`。 -/
theorem ExpGap_const (p : Ω → ℝ) (f : ℝ → ℝ) (c xstar : ℝ) :
    ExpGap p f (fun _ : Ω => c) xstar = (∑ ω, p ω) * (f c - f xstar) := by
  unfold ExpGap
  rw [Expect_const]

/-- ⭐⭐ **率定理（平均迭代版）：前提里没有 `hstep`。**

`η = D/(G√T)`、`‖X 0 − x*‖² = D²`、平均梯度更新、`E[g_t]` 是次梯度、`E[g_t²] ≤ G²`
⟹ `∃ t < T, f (X t) − f x* ≤ D·G/√T`。

**与 `sgd_rate_bound` 的唯一区别**：那条把 `hstep` 当假设（因为它讲的是**随机**迭代，
那里的 `hstep` 在本接口下不可导出，见 §八 的边界说明）；本条把它**推出来**，
代价是把迭代限定为**确定性**的 `X : ℕ → ℝ`。 -/
theorem sgd_rate_bound_averaged (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (hpsum : (∑ ω, p ω) = 1) (f : ℝ → ℝ) (X : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (xstar G D η : ℝ) (T : ℕ)
    (hG : 0 < G) (hT : 0 < T) (hD : 0 < D)
    (hD2 : ‖X 0 - xstar‖ ^ 2 = D ^ 2)
    (hη : η = D / (G * Real.sqrt (T : ℝ)))
    (hupd : ∀ t, X (t + 1) = X t - η * Expect p (g t))
    (hsub : ∀ t, Subgradient f (X t) (Expect p (g t)))
    (hbnd : ∀ t, Expect p (fun ω => (g t ω) ^ 2) ≤ G ^ 2) :
    ∃ t : ℕ, t < T ∧ f (X t) - f xstar ≤ D * G / Real.sqrt (T : ℝ) := by
  -- the constant extension of `X`
  set x : ℕ → Ω → ℝ := fun t _ => X t with hx
  -- η > 0 from η = D / (G * √T)
  have hsq : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hηpos : 0 ≤ η := by
    rw [hη]
    exact le_of_lt (div_pos hD (mul_pos hG hsq))
  have hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * G ^ 2 := by
    intro t
    have h := sgd_averaged_step p hp0 hpsum f X g xstar G η hηpos
      hupd hsub hbnd t
    -- rewrite the `ExpDist` / `ExpGap` of constant random variables
    simp only [hx, ExpDist_const, ExpGap_const, hpsum, one_mul]
    exact h
  have hD2' : ExpDist p (x 0) xstar = D ^ 2 := by
    simp only [hx, ExpDist_const, hpsum, one_mul]
    exact hD2
  obtain ⟨t, ht, hgap⟩ :=
    sgd_rate_bound p hp0 f x xstar G D η T hG hT hD hD2' hη hstep
  refine ⟨t, ht, ?_⟩
  simp only [hx, ExpGap_const, hpsum, one_mul] at hgap
  exact hgap

end Lattice
