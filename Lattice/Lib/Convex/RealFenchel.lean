import Mathlib
import Lattice.Lib.InfoTheory.RealFDivergence
import Lattice.Lib.InfoTheory.RealDataProcessing
/-!
# LATTICE: 凸共轭（Fenchel 对偶）—— f-散度的变分表示与 TV 的变分表示

信息论线的对偶一环（衔接 RealFDivergence 的 f-散度/χ²/TV、RealKL 的 KL、
RealDataProcessing 的 `tv_eq_sum_abs`）：

凸共轭（Fenchel 共轭）f*(y) = sup_x (⟨x,y⟩ − f(x))。本文件在**有限支撑**上实现：
函数 f 的支撑点集取为有限指标集 `x : Fin n → ℝ`，于是 sup 变成有限 `Finset.sup'`。

本文件建立：

  1. `fenchelConjugate`（定义）：f*(y) = max_i (x_i·y − f(x_i))（有限支撑）；
     `le_fenchelConjugate` / `fenchelConjugate_le`：sup 的两条基本性质；
  2. `fenchel_inequality`（Fenchel 不等式）：x_i·y ≤ f(x_i) + f*(y)；
  3. `fenchelBiconjugate` / `fenchel_biconjugate_le`：f** ≤ f（**恒真**，
     因为在任意指标 j 处 f*(y) ≥ x_j·y − f(x_j) 逐点给出 y·x_j − f*(y) ≤ f(x_j)，
     再取 sup）；
  4. `fenchel_dual_lower_bound`（**核心**）：f-散度的 Fenchel 对偶下界
     Σ_a p_a·g_a − Σ_a q_a·f*(g_a) ≤ D_f(q‖p) = Σ_a q_a·f(p_a/q_a)，
     其中有限支撑 x 包含所有 p_a/q_a（逐项用 Fenchel 不等式，乘 q_a > 0 后求和）；
  5. `kl_dual_lower_bound`：f = t·log t 的推论，用 `kl_as_fdiv` 把右边换成 KL(p‖q)；
  6. `fenchelConjugate_mul_log_le_exp`：f = t·log t 时 f*(y) ≤ e^{y−1}
     （标量不等式 t·y − t·log t ≤ e^{y−1}，t ≥ 0；对数换元 u = t/e^{y−1} 后用
     `Real.one_sub_inv_le_log_of_pos`）；
  7. `kl_dual_representation`（**核心强结果**）：KL 的对偶表示被 g_a = log(p_a/q_a)+1
     **取到**：KL(p‖q) = Σ_a p_a·g_a − Σ_a q_a·f*(g_a)（f = t·log t）
     —— 结合 4 与 6：由 x ⊇ {p_a/q_a} 得 f*(g_a) ≥ p_a/q_a，由 6 得 f*(g_a) ≤ e^{g_a−1} = p_a/q_a，
     故 f*(g_a) = p_a/q_a，再纯代数化简；
  8. `tv_dual_upper` / `tv_dual_attained`：全变差的变分表示两半
     TV(p,q) = sup_{|g|≤1} Σ_a (p_a − q_a)·g_a
     —— 上界（任意 |g| ≤ 1 给出 ≤ TV）与取到（g = sign(q−p) 给出 = TV）。

**诚实边界**（本文件不证 / 不声称的）：

- 全部是**有限支撑**版本：f* 的 sup 只在一个有限点集 `x : Fin n → ℝ` 上取，
  而不是整个 ℝ。因此 `fenchel_dual_lower_bound` 需要显式假设「x 包含所有 p_a/q_a」
  （`hin`）；这不是无谓的技术条件，而是有限支撑 f* 的真实语义。
- `fenchel_biconjugate_le`（f** ≤ f）是 Fenchel–Moreau 的**弱方向**，恒成立。
  **凸闭情形 f** = f 的等号方向未证**：它需要 f 凸闭时的支撑超平面/次梯度存在性
  （mathlib 的凸分析设施），标注为后续。本文件不声称等号。
- `kl_dual_representation` 的取到是对 **f = t·log t** 这一个具体 f 完成的；
  一般 f 的强对偶（sup 取到）需要 f 凸且 f* 的次梯度在 p/q 处取到，未做。
- `tv_dual_upper` / `tv_dual_attained` 用 `tv_eq_sum_abs`（需要 p 严格正）把
  f-散度记号下的 TV 写成 L¹ 距离 Σ|q_a − p_a|；因此 TV 的变分表示在 p > 0 下陈述。
  若用半和约定 TV = (1/2)Σ|p−q|，两侧同因子，不等式不变。
- 未做：f-散度的联合凸性对偶、Fenchel–Moreau 的等号方向、无限维（函数空间）版本、
  KL 的对偶表示与 Donsker–Varadhan 变分式（无限 sup over 有界函数）的联系。

模型无关：任意有限 k、任意有限支撑 n、任意 f : ℝ → ℝ
（除 KL/TV 的具体实例外不需要 f 的任何性质）。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 定义：有限支撑凸共轭 -/

/-- 有限支撑凸共轭：f*(y) = sup_i (x_i·y − f(x_i))（在有限点集 x 上取 sup）。 -/
noncomputable def fenchelConjugate {n : ℕ} [Nonempty (Fin n)] (f : ℝ → ℝ) (x : Fin n → ℝ)
    (y : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => x i * y - f (x i))

/-- sup 的上界性质：每个 i 的 x_i·y − f(x_i) 都不超过 f*(y)。 -/
lemma le_fenchelConjugate {n : ℕ} [Nonempty (Fin n)] (f : ℝ → ℝ) (x : Fin n → ℝ) (y : ℝ)
    (i : Fin n) : x i * y - f (x i) ≤ fenchelConjugate f x y :=
  Finset.le_sup' (fun i => x i * y - f (x i)) (Finset.mem_univ i)

/-- sup 的最小上界性质：若所有 x_i·y − f(x_i) ≤ C，则 f*(y) ≤ C。 -/
lemma fenchelConjugate_le {n : ℕ} [Nonempty (Fin n)] (f : ℝ → ℝ) (x : Fin n → ℝ) (y C : ℝ)
    (h : ∀ i, x i * y - f (x i) ≤ C) : fenchelConjugate f x y ≤ C :=
  Finset.sup'_le Finset.univ_nonempty _ (fun i _ => h i)

/-! ## 定理一：Fenchel 不等式 -/

theorem fenchel_inequality {n : ℕ} [Nonempty (Fin n)] (f : ℝ → ℝ) (x : Fin n → ℝ)
    (y : ℝ) (i : Fin n) : x i * y ≤ f (x i) + fenchelConjugate f x y := by
  have h := le_fenchelConjugate f x y i
  linarith

/-! ## 定义与定理二：二次共轭 f** ≤ f（恒真） -/

/-- 二次共轭：f**(x_j) = sup_{y ∈ ys} (y·x_j − f*(y))（斜率也取有限支撑 ys）。 -/
noncomputable def fenchelBiconjugate {m n : ℕ} [Nonempty (Fin n)] [Nonempty (Fin m)]
    (f : ℝ → ℝ) (x : Fin n → ℝ) (ys : Fin m → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ys i * x j - fenchelConjugate f x (ys i))

/-- f** ≤ f（Fenchel–Moreau 的弱方向，**恒成立**）：
对每个斜率 y 与每个支撑点 x_j，y·x_j − f*(y) ≤ f(x_j)；对 y 取 sup 即得。 -/
theorem fenchel_biconjugate_le {m n : ℕ} [Nonempty (Fin n)] [Nonempty (Fin m)]
    (f : ℝ → ℝ) (x : Fin n → ℝ) (ys : Fin m → ℝ) (j : Fin n) :
    fenchelBiconjugate f x ys j ≤ f (x j) := by
  apply Finset.sup'_le
  intro i _
  have h := le_fenchelConjugate f x (ys i) j
  rw [mul_comm (ys i) (x j)]
  linarith

/-! ## 定理三（核心）：f-散度的 Fenchel 对偶下界 -/

/-- f-散度的 Fenchel 对偶下界：
若有限支撑 x 包含所有 p_a/q_a（`hin`）、q 严格正，则对任意 g
  Σ_a p_a·g_a − Σ_a q_a·f*(g_a) ≤ D_f(q‖p) = Σ_a q_a·f(p_a/q_a)。
证明：逐项 Fenchel 不等式 (p_a/q_a)·g_a ≤ f(p_a/q_a) + f*(g_a)，
乘 q_a > 0 得 p_a·g_a ≤ q_a·f(p_a/q_a) + q_a·f*(g_a)，求和。 -/
theorem fenchel_dual_lower_bound {k n : ℕ} [Nonempty (Fin n)] (f : ℝ → ℝ)
    (p q : Fin k → ℝ) (x : Fin n → ℝ) (hin : ∀ a, ∃ i, x i = p a / q a)
    (hq : ∀ a, 0 < q a) (g : Fin k → ℝ) :
    (∑ a, p a * g a) - ∑ a, q a * fenchelConjugate f x (g a)
      ≤ fDivergence f q p := by
  have hterm : ∀ a, p a * g a - q a * fenchelConjugate f x (g a)
      ≤ q a * f (p a / q a) := by
    intro a
    obtain ⟨i, hi⟩ := hin a
    have h := le_fenchelConjugate f x (g a) i
    rw [hi] at h
    have h2 : (p a / q a) * g a ≤ f (p a / q a) + fenchelConjugate f x (g a) := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt (hq a))
    have h3 : q a * ((p a / q a) * g a) = p a * g a := by
      rw [← mul_assoc, mul_div_self (p a) (q a) (ne_of_gt (hq a))]
    have h4 : q a * (f (p a / q a) + fenchelConjugate f x (g a))
        = q a * f (p a / q a) + q a * fenchelConjugate f x (g a) := by ring
    rw [h3, h4] at hmul
    linarith
  calc (∑ a, p a * g a) - ∑ a, q a * fenchelConjugate f x (g a)
      = ∑ a, (p a * g a - q a * fenchelConjugate f x (g a)) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ a, q a * f (p a / q a) := Finset.sum_le_sum (fun a _ => hterm a)
    _ = fDivergence f q p := rfl

/-- KL 的对偶下界（f = t·log t 的推论）：由 `kl_as_fdiv` 把 D_f(q‖p) 换成 KL(p‖q)。 -/
theorem kl_dual_lower_bound {k n : ℕ} [Nonempty (Fin n)] (p q : Fin k → ℝ) (x : Fin n → ℝ)
    (hin : ∀ a, ∃ i, x i = p a / q a) (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (g : Fin k → ℝ) :
    (∑ a, p a * g a)
        - ∑ a, q a * fenchelConjugate (fun t => t * Real.log t) x (g a) ≤ kl p q := by
  have h := fenchel_dual_lower_bound (fun t => t * Real.log t) p q x hin hq g
  rwa [kl_as_fdiv p q hp hq] at h

/-! ## 定理四：t·log t 的共轭的显式上界

标量不等式：t ≥ 0 ⟹ t·y − t·log t ≤ e^{y−1}。
t = 0 时左边 = 0 ≤ e^{y−1}；t > 0 时令 u = t/e^{y−1} > 0，
t·y − t·log t = u·e^{y−1}·(1 − log u) ≤ u·e^{y−1}·u⁻¹ = e^{y−1}（`one_sub_inv_le_log_of_pos`）。 -/

lemma mul_log_sub_le_exp (t y : ℝ) (ht : 0 ≤ t) :
    t * y - t * Real.log t ≤ Real.exp (y - 1) := by
  by_cases ht0 : t = 0
  · rw [ht0]
    have hz : (0 : ℝ) * y - 0 * Real.log 0 = 0 := by ring
    rw [hz]
    exact le_of_lt (Real.exp_pos _)
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    set E : ℝ := Real.exp (y - 1) with hE
    have hEpos : 0 < E := Real.exp_pos _
    set u : ℝ := t / E with hu
    have hupos : 0 < u := div_pos htpos hEpos
    have ht_eq : t = u * E := by
      rw [hu]; field_simp
    have hlogt : Real.log t = Real.log u + (y - 1) := by
      rw [ht_eq, Real.log_mul (ne_of_gt hupos) (ne_of_gt hEpos), hE, Real.log_exp]
    have hkey : t * y - t * Real.log t = u * E * (1 - Real.log u) := by
      rw [hlogt, ht_eq]; ring
    have hbound : 1 - Real.log u ≤ u⁻¹ := by
      have := Real.one_sub_inv_le_log_of_pos hupos
      linarith
    have hstep : u * E * (1 - Real.log u) ≤ u * E * u⁻¹ :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg (le_of_lt hupos) (le_of_lt hEpos))
    have hcancel : u * E * u⁻¹ = E := by
      field_simp
    rw [hkey]
    linarith [hstep, hcancel]

/-- f = t·log t 的共轭上界：f*(y) ≤ e^{y−1}（逐点标量不等式 + sup 的最小上界性质）。 -/
lemma fenchelConjugate_mul_log_le_exp {n : ℕ} [Nonempty (Fin n)] (x : Fin n → ℝ) (y : ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    fenchelConjugate (fun t => t * Real.log t) x y ≤ Real.exp (y - 1) := by
  apply fenchelConjugate_le
  intro i
  exact mul_log_sub_le_exp (x i) y (hx i)

/-! ## 定理五（核心强结果）：KL 的对偶表示被特定 g 取到 -/

/-- KL 的对偶表示（取到版）：取 g_a = log(p_a/q_a) + 1，则对偶配对精确等于 KL(p‖q)。
    （f = t·log t，有限支撑 x ⊇ {p_a/q_a}。） -/
theorem kl_dual_representation {k n : ℕ} [Nonempty (Fin n)] (p q : Fin k → ℝ)
    (x : Fin n → ℝ) (hin : ∀ a, ∃ i, x i = p a / q a) (hx : ∀ i, 0 ≤ x i)
    (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a) :
    kl p q
      = (∑ a, p a * (Real.log (p a / q a) + 1))
        - ∑ a, q a
            * fenchelConjugate (fun t => t * Real.log t) x (Real.log (p a / q a) + 1) := by
  have hval : ∀ a, fenchelConjugate (fun t => t * Real.log t) x (Real.log (p a / q a) + 1)
      = p a / q a := by
    intro a
    apply le_antisymm
    · have h := fenchelConjugate_mul_log_le_exp x (Real.log (p a / q a) + 1) hx
      rwa [show Real.log (p a / q a) + 1 - 1 = Real.log (p a / q a) by ring,
        Real.exp_log (div_pos (hp a) (hq a))] at h
    · obtain ⟨i, hi⟩ := hin a
      have h := le_fenchelConjugate (fun t => t * Real.log t) x
        (Real.log (p a / q a) + 1) i
      rw [hi] at h
      have hkey : (p a / q a) * (Real.log (p a / q a) + 1)
          - (p a / q a) * Real.log (p a / q a) = p a / q a := by ring
      linarith
  have hsum_q : (∑ a, q a * (p a / q a)) = ∑ a, p a := by
    apply Finset.sum_congr rfl
    intro a _
    field_simp [ne_of_gt (hq a)]
  calc kl p q = ∑ a, p a * Real.log (p a / q a) := kl_as_sum_log_ratio p q hp hq
    _ = ∑ a, p a * (Real.log (p a / q a) + 1) - ∑ a, p a := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ∑ a, p a * (Real.log (p a / q a) + 1) - ∑ a, q a * (p a / q a) := by
          rw [hsum_q]
    _ = (∑ a, p a * (Real.log (p a / q a) + 1))
        - ∑ a, q a
            * fenchelConjugate (fun t => t * Real.log t) x (Real.log (p a / q a) + 1) := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          rw [hval a]

/-! ## 定理六：全变差的变分表示（上界 + 取到） -/

/-- TV 变分表示的上界半边：任意 |g| ≤ 1 给出 Σ_a (p_a − q_a)·g_a ≤ TV(p,q)。 -/
theorem tv_dual_upper {k : ℕ} (p q g : Fin k → ℝ) (hp : ∀ a, 0 < p a)
    (hg : ∀ a, |g a| ≤ 1) :
    ∑ a, (p a - q a) * g a ≤ tv p q := by
  rw [tv_eq_sum_abs p q hp]
  calc ∑ a, (p a - q a) * g a ≤ ∑ a, |p a - q a| := by
        apply Finset.sum_le_sum
        intro a _
        calc (p a - q a) * g a ≤ |(p a - q a) * g a| := le_abs_self _
          _ = |p a - q a| * |g a| := abs_mul _ _
          _ ≤ |p a - q a| * 1 := mul_le_mul_of_nonneg_left (hg a) (abs_nonneg _)
          _ = |p a - q a| := mul_one _
    _ = ∑ a, |q a - p a| := by
        apply Finset.sum_congr rfl
        intro a _
        rw [abs_sub_comm]

/-- TV 变分表示的取到半边：g = sign(q − p)（即 q ≥ p 时取 −1、否则取 1，满足 |g| ≤ 1）
给出 Σ_a (p_a − q_a)·g_a = TV(p,q)。 -/
theorem tv_dual_attained {k : ℕ} (p q : Fin k → ℝ) (hp : ∀ a, 0 < p a) :
    ∑ a, (p a - q a) * (if q a ≥ p a then -1 else 1) = tv p q := by
  rw [tv_eq_sum_abs p q hp]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : q a ≥ p a
  · have h1 : |q a - p a| = q a - p a := abs_of_nonneg (by linarith)
    rw [if_pos h, h1]
    ring
  · have h1 : |q a - p a| = p a - q a := by
      rw [abs_of_neg (by linarith)]
      ring
    rw [if_neg h, h1]
    ring

end Lattice
