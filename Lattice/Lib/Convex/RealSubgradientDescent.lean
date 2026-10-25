import Mathlib
import Lattice.Lib.Convex.RealSubgradient
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Optim.RealGradDescent
/-!
# LATTICE: 次梯度下降的收敛 —— 非光滑凸优化的基本算法（§5 约束行「次梯度算法收敛」）

衔接 RealSubgradient 的次梯度定义（一维 f : ℝ → ℝ）：
    g ∈ ∂f(x) ⟺ ∀ y, f y ≥ f x + g·(y − x)

次梯度下降更新
    x_{t+1} = x_t − η·g_t      （g_t ∈ ∂f(x_t)，η > 0 步长）
是 RealGradDescent.GDUpdate（可导梯度下降）的非光滑推广：把「梯度」换成
「次梯度」，光滑分析的偏序论证换成次梯度不等式（subgradient_step_decrease）。

核心链条（**不需要显式凸性**——次梯度定义本身即凸不等式，代入 y = x* 重排）：
  1. subgradient_step_decrease：f x − f y ≤ g·(x − y)；
  2. subgradient_descent_norm_decrease（核心）：‖x_{t+1} − y‖² ≤ ‖x_t − y‖²
     − 2η·(f x_t − f y) + η²·‖g_t‖²（‖(x−y) − ηg‖² = ‖x−y‖² − 2η⟨g, x−y⟩
     + η²‖g‖² 展开 + 引理 1；一维 ℝ 中内积即乘法，‖·‖² 用 sq 展开）；
  3. subgradient_descent_gap_sum（核心）：对 y = x* 求和 + 望远镜消去
     ‖x_t − x*‖² 项 ⟹ 2η·Σ_{t<T}(f x_t − f x*) ≤ ‖x_0 − x*‖² + η²·Σ_{t<T}‖g_t‖²；
  4. subgradient_descent_avg_gap：‖g_t‖ ≤ G ⟹
     Σ_{t<T}(f x_t − f x*) ≤ (‖x_0 − x*‖² + η²·T·G²)/(2η)；
  5. subgradient_descent_min_gap：min ≤ 平均 ⟹ ∃ t < T，
     f(x_t) − f(x*) ≤ (‖x_0 − x*‖² + η²·T·G²)/(2η·T)；
  6. subgradient_descent_rate_bound：最优步长 η = D/(G√T)（D = ‖x_0 − x*‖）⟹
     单步差距 ≤ D·G/√T，即 O(GD/√T)。

与 RealGradDescent / RealConvergence 的关系：
  · GDUpdate（平方损失伴随梯度）是次梯度下降的光滑特例（平滑梯度即次梯度）；
  · 次梯度下降**不收缩**（无几何收敛）——得到的是差距的 O(1/√T) 和式界，
    因此不接 contraction_converges（那是收缩骨架）；这是非光滑优化的本质代价
    （几何收敛需强凸性/光滑性，非光滑凸只有次线性率）。

诚实边界：
  · 一维 ℝ（Subgradient 定义于 ℝ → ℝ，复用 RealSubgradient，未推广到内积空间；
    任务标注的 ⟨g, x−y⟩ 在一维即 g·(x−y)）；
  · 差距 f x_t − f x* 无需非负（min ≤ 平均的论证不要求 x* 是全局最小）；
  · 步长假设仅 η > 0；次梯度选择 g 假设处处良定（∀ x, Subgradient f x (g x)）；
  · rate 定理要求 D > 0、G > 0、T > 0（避免 η = 0 或除零退化）；
  · 无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 定义：次梯度下降更新、迭代与次优差距 -/

/-- 次梯度下降单步：x' = x − η·g（g ∈ ∂f(x)，η > 0 步长）。 -/
def subgradient_descent_step (η : ℝ) (x g : ℝ) : ℝ :=
  x - η * g

/-- 次梯度下降迭代：x_{t+1} = x_t − η·g(x_t)，g 是次梯度选择映射。 -/
def SubgradientIterate (g : ℝ → ℝ) (η : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => subgradient_descent_step η (SubgradientIterate g η n x) (g (SubgradientIterate g η n x))

/-- 第 t 步的次优差距：f(x_t) − f(x*)。 -/
def SubgradientGap (f g : ℝ → ℝ) (η : ℝ) (x0 xstar : ℝ) (t : ℕ) : ℝ :=
  f (SubgradientIterate g η t x0) - f xstar

/-! ## 引理：望远镜求和 Σ_{t<T}(a_t − a_{t+1}) = a_0 − a_T -/

lemma sum_range_sub_telescoping {a : ℕ → ℝ} (T : ℕ) :
    (∑ t in Finset.range T, (a t - a (t + 1))) = a 0 - a T := by
  induction T with
  | zero => simp
  | succ T ih =>
      calc
        (∑ t in Finset.range (T + 1), (a t - a (t + 1)))
            = (∑ t in Finset.range T, (a t - a (t + 1))) + (a T - a (T + 1)) := by
              rw [Finset.sum_range_succ]
        _ = (a 0 - a T) + (a T - a (T + 1)) := by rw [ih]
        _ = a 0 - a (T + 1) := by ring

/-! ## 引理 2：次梯度不等式 ⟹ f x − f y ≤ g·(x − y)
次梯度定义 f y ≥ f x + g·(y − x) 代入 y，重排（无需凸性）。 -/

theorem subgradient_step_decrease {f : ℝ → ℝ} {x g : ℝ} (hg : Subgradient f x g) (y : ℝ) :
    f x - f y ≤ g * (x - y) := by
  have h := hg y
  nlinarith

/-! ## 引理 3：单步范数收缩（核心）
‖x − η·g − y‖² ≤ ‖x − y‖² − 2η·(f x − f y) + η²·‖g‖²。
‖(x−y) − ηg‖² = ‖x−y‖² − 2η⟨g, x−y⟩ + η²‖g‖²（norm_add_sq 的 sq 展开），
代入引理 2（⟨g, x−y⟩ ≥ f x − f y）与 η ≥ 0。-/

theorem subgradient_descent_norm_decrease {f : ℝ → ℝ} {x g : ℝ} (hg : Subgradient f x g)
    (y : ℝ) (η : ℝ) (hη : 0 ≤ η) :
    ‖subgradient_descent_step η x g - y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 - 2 * η * (f x - f y) + η ^ 2 * ‖g‖ ^ 2 := by
  unfold subgradient_descent_step
  simp only [Real.norm_eq_abs, sq_abs]
  have hdec := subgradient_step_decrease hg y
  nlinarith [hdec, hη]

/-! ## 引理 3b：沿迭代序列的单步收缩（序列版）
x(n+1) = x_n − η·g(x_n)，g(x_n) ∈ ∂f(x_n) ⟹ 每步的范数收缩。 -/

lemma subgradient_descent_norm_decrease_seq {x : ℕ → ℝ} (f g : ℝ → ℝ) (η : ℝ) (xstar : ℝ)
    (hsub : ∀ n : ℕ, Subgradient f (x n) (g (x n)))
    (hstep : ∀ n : ℕ, x (n + 1) = subgradient_descent_step η (x n) (g (x n)))
    (hη : 0 ≤ η) :
    ∀ n : ℕ,
      ‖x (n + 1) - xstar‖ ^ 2 ≤
        ‖x n - xstar‖ ^ 2 - 2 * η * (f (x n) - f xstar) + η ^ 2 * ‖g (x n)‖ ^ 2 := by
  intro n
  rw [hstep n]
  exact subgradient_descent_norm_decrease (hsub n) xstar η hη

/-! ## 引理 4：差距求和（核心，望远镜消去）
2η·Σ_{t<T}(f x_t − f x*) ≤ ‖x_0 − x*‖² + η²·Σ_{t<T}‖g_t‖²。 -/

theorem subgradient_descent_gap_sum_seq {x : ℕ → ℝ} (f g : ℝ → ℝ) (η : ℝ) (xstar : ℝ) (T : ℕ)
    (hsub : ∀ n : ℕ, Subgradient f (x n) (g (x n)))
    (hstep : ∀ n : ℕ, x (n + 1) = subgradient_descent_step η (x n) (g (x n)))
    (hη : 0 ≤ η) :
    2 * η * (∑ t in Finset.range T, (f (x t) - f xstar)) ≤
      ‖x 0 - xstar‖ ^ 2 + η ^ 2 * (∑ t in Finset.range T, ‖g (x t)‖ ^ 2) := by
  have hdec := subgradient_descent_norm_decrease_seq f g η xstar hsub hstep hη
  have hstep_le : ∀ t : ℕ,
      2 * η * (f (x t) - f xstar) ≤
        ‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 + η ^ 2 * ‖g (x t)‖ ^ 2 := by
    intro t
    have hd := hdec t
    nlinarith [hd]
  have hsum : (∑ t in Finset.range T, 2 * η * (f (x t) - f xstar)) ≤
      ∑ t in Finset.range T,
        (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 + η ^ 2 * ‖g (x t)‖ ^ 2) := by
    exact Finset.sum_le_sum (fun t ht => hstep_le t)
  have hsum_split :
      (∑ t in Finset.range T,
        (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 + η ^ 2 * ‖g (x t)‖ ^ 2))
        = (∑ t in Finset.range T, (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2))
          + η ^ 2 * (∑ t in Finset.range T, ‖g (x t)‖ ^ 2) := by
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
  have htelescope : (∑ t in Finset.range T, (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2))
      = ‖x 0 - xstar‖ ^ 2 - ‖x T - xstar‖ ^ 2 := by
    exact sum_range_sub_telescoping T
  have htele_le : (∑ t in Finset.range T, (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2))
      ≤ ‖x 0 - xstar‖ ^ 2 := by
    rw [htelescope]
    nlinarith [sq_nonneg (‖x T - xstar‖)]
  calc
    2 * η * (∑ t in Finset.range T, (f (x t) - f xstar))
        = ∑ t in Finset.range T, 2 * η * (f (x t) - f xstar) := by rw [Finset.mul_sum]
    _ ≤ ∑ t in Finset.range T,
          (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 + η ^ 2 * ‖g (x t)‖ ^ 2) := hsum
    _ = (∑ t in Finset.range T, (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2))
          + η ^ 2 * (∑ t in Finset.range T, ‖g (x t)‖ ^ 2) := hsum_split
    _ ≤ ‖x 0 - xstar‖ ^ 2 + η ^ 2 * (∑ t in Finset.range T, ‖g (x t)‖ ^ 2) := by
          exact add_le_add_right htele_le _

/-! ## 引理 4b：具体迭代实例（g 是处处定义的次梯度选择）
hsub : ∀ x, Subgradient f x (g x) 给出轨迹上每步的次梯度。 -/

theorem subgradient_descent_gap_sum (f g : ℝ → ℝ) (η : ℝ) (x0 xstar : ℝ) (T : ℕ)
    (hsub : ∀ x : ℝ, Subgradient f x (g x)) (hη : 0 ≤ η) :
    2 * η * (∑ t in Finset.range T, SubgradientGap f g η x0 xstar t) ≤
      ‖x0 - xstar‖ ^ 2 + η ^ 2 * (∑ t in Finset.range T, ‖g (SubgradientIterate g η t x0)‖ ^ 2) := by
  simpa [SubgradientGap] using
    (subgradient_descent_gap_sum_seq f g η xstar T
      (fun n => hsub (SubgradientIterate g η n x0))
      (fun n => by rfl)
      hη)

/-! ## 定理 5：次梯度有界 ⟹ 平均次优差距（一般形式）
‖g(x)‖ ≤ G（∀x），η > 0 ⟹ Σ_{t<T}(f x_t − f x*) ≤ (‖x_0 − x*‖² + η²·T·G²)/(2η)。 -/

theorem subgradient_descent_avg_gap (f g : ℝ → ℝ) (η : ℝ) (x0 xstar G : ℝ) (T : ℕ)
    (hsub : ∀ x : ℝ, Subgradient f x (g x)) (hη : 0 < η) (hG : 0 ≤ G)
    (hGbound : ∀ x : ℝ, ‖g x‖ ≤ G) :
    (∑ t in Finset.range T, SubgradientGap f g η x0 xstar t) ≤
      (‖x0 - xstar‖ ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η) := by
  have hgrad_sq : ∀ t : ℕ, ‖g (SubgradientIterate g η t x0)‖ ^ 2 ≤ G ^ 2 := by
    intro t
    exact sq_le_sq' (by nlinarith [hG, norm_nonneg (g (SubgradientIterate g η t x0))])
      (hGbound (SubgradientIterate g η t x0))
  have hgrad_sum : (∑ t in Finset.range T, ‖g (SubgradientIterate g η t x0)‖ ^ 2) ≤
      (T : ℝ) * G ^ 2 := by
    calc
      (∑ t in Finset.range T, ‖g (SubgradientIterate g η t x0)‖ ^ 2)
          ≤ ∑ t in Finset.range T, G ^ 2 := by
            exact Finset.sum_le_sum (fun t ht => hgrad_sq t)
      _ = (T : ℝ) * G ^ 2 := by
            rw [Finset.sum_const, Finset.card_range]
            rw [nsmul_eq_mul]
  have hmain := subgradient_descent_gap_sum f g η x0 xstar T hsub (le_of_lt hη)
  have hmain2 : 2 * η * (∑ t in Finset.range T, SubgradientGap f g η x0 xstar t) ≤
      ‖x0 - xstar‖ ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2 := by
    nlinarith [hmain, hgrad_sum]
  rw [le_div_iff₀ (by positivity : 0 < 2 * η)]
  nlinarith [hmain2]

/-! ## 引理：min ≤ 平均（存在性形式）
Σ_{t<T} a_t ≤ T·B，T > 0 ⟹ ∃ t < T，a_t ≤ B。 -/

lemma exists_le_sum_mul {a : ℕ → ℝ} {T : ℕ} {B : ℝ} (hT : 0 < T)
    (h : (∑ t in Finset.range T, a t) ≤ (T : ℝ) * B) :
    ∃ t : ℕ, t < T ∧ a t ≤ B := by
  by_contra hnot
  push_neg at hnot
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hsum_lt : (∑ t in Finset.range T, B) < ∑ t in Finset.range T, a t := by
    have hw : ∃ t ∈ Finset.range T, B < a t := by
      refine ⟨0, ?_, ?_⟩
      · simp [hT]
      · exact hnot 0 (by simp [hT])
    exact Finset.sum_lt_sum (fun t ht => le_of_lt (hnot t (Finset.mem_range.mp ht))) hw
  have hsum_B : (∑ t in Finset.range T, B) = (T : ℝ) * B := by
    rw [Finset.sum_const, Finset.card_range]
    rw [nsmul_eq_mul]
  nlinarith [h, hsum_lt, hsum_B]

/-! ## 定理 5b：min ≤ 平均 ⟹ 存在一步的差距界
∃ t < T，f(x_t) − f(x*) ≤ (‖x_0 − x*‖² + η²·T·G²)/(2η·T)。 -/

theorem subgradient_descent_min_gap (f g : ℝ → ℝ) (η : ℝ) (x0 xstar G : ℝ) (T : ℕ)
    (hsub : ∀ x : ℝ, Subgradient f x (g x)) (hη : 0 < η) (hG : 0 ≤ G)
    (hGbound : ∀ x : ℝ, ‖g x‖ ≤ G) (hT : 0 < T) :
    ∃ t : ℕ, t < T ∧
      SubgradientGap f g η x0 xstar t ≤
        (‖x0 - xstar‖ ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ)) := by
  have havg := subgradient_descent_avg_gap f g η x0 xstar G T hsub hη hG hGbound
  let B : ℝ := (‖x0 - xstar‖ ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η)
  have hmain : (∑ t in Finset.range T, SubgradientGap f g η x0 xstar t) ≤ B := by
    dsimp [B]
    exact havg
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hB : B = (T : ℝ) * ((‖x0 - xstar‖ ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ))) := by
    dsimp [B]
    field_simp [mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hη), hTne]
    ring
  have hcalc : (∑ t in Finset.range T, SubgradientGap f g η x0 xstar t) ≤
      (T : ℝ) * ((‖x0 - xstar‖ ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ))) := by
    calc
      (∑ t in Finset.range T, SubgradientGap f g η x0 xstar t) ≤ B := hmain
      _ = (T : ℝ) * ((‖x0 - xstar‖ ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ))) := hB
  rcases (exists_le_sum_mul (a := SubgradientGap f g η x0 xstar) hT hcalc) with ⟨t, ht, hgap⟩
  exact ⟨t, ht, hgap⟩

/-! ## 定理 6（最优步长，O(GD/√T)）：η = D/(G√T)，D = ‖x_0 − x*‖
∃ t < T，f(x_t) − f(x*) ≤ D·G/√T。D > 0、G > 0、T > 0 防退化。 -/

theorem subgradient_descent_rate_bound (f g : ℝ → ℝ) (x0 xstar G : ℝ) (T : ℕ)
    (hsub : ∀ x : ℝ, Subgradient f x (g x))
    (hG : 0 < G) (hT : 0 < T) (hD : 0 < ‖x0 - xstar‖)
    (hGbound : ∀ x : ℝ, ‖g x‖ ≤ G) :
    ∃ t : ℕ, t < T ∧
      SubgradientGap f g (‖x0 - xstar‖ / (G * Real.sqrt (T : ℝ))) x0 xstar t ≤
        ‖x0 - xstar‖ * G / Real.sqrt (T : ℝ) := by
  let D : ℝ := ‖x0 - xstar‖
  let s : ℝ := Real.sqrt (T : ℝ)
  let η : ℝ := D / (G * s)
  have hDne : D ≠ 0 := by dsimp [D]; exact ne_of_gt hD
  have hGne : G ≠ 0 := ne_of_gt hG
  have hT0 : 0 ≤ (T : ℝ) := by exact_mod_cast le_of_lt hT
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 = (T : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt hT0
  have hη0 : 0 < η := by
    dsimp [η]
    exact div_pos hD (mul_pos hG hs_pos)
  rcases (subgradient_descent_min_gap f g η x0 xstar G T hsub hη0 (le_of_lt hG) hGbound hT)
    with ⟨t, ht, hgap⟩
  have hbnd : (D ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ)) = D * G / s := by
    dsimp [η]
    rw [← hs_sq]
    field_simp [hDne, hGne, hs_ne]
    ring
  refine ⟨t, ht, ?_⟩
  calc
    SubgradientGap f g η x0 xstar t ≤
        (D ^ 2 + η ^ 2 * (T : ℝ) * G ^ 2) / (2 * η * (T : ℝ)) := by
          simpa [D] using hgap
    _ = D * G / s := hbnd
    _ = ‖x0 - xstar‖ * G / Real.sqrt (T : ℝ) := by dsimp [D, s]

/-! ## relu 实例：x > 0 处 ∂relu(x) = {1}（RealSubgradient.relu_subgradient_positive）
验证引理 2/3 对 f = relu、g = 1 成立（代入 Subgradient relu x 1）。 -/

theorem relu_subgradient_step_decrease (x y : ℝ) (hx : 0 < x) :
    relu x - relu y ≤ x - y := by
  have hg : Subgradient relu x 1 := (relu_subgradient_positive x 1 hx).mpr rfl
  simpa using subgradient_step_decrease hg y

theorem relu_subgradient_descent_norm_decrease (x xstar : ℝ) (η : ℝ) (hx : 0 < x) (hη : 0 ≤ η) :
    ‖x - η * 1 - xstar‖ ^ 2 ≤ ‖x - xstar‖ ^ 2 - 2 * η * (relu x - relu xstar) + η ^ 2 * ‖(1 : ℝ)‖ ^ 2 := by
  have hg : Subgradient relu x 1 := (relu_subgradient_positive x 1 hx).mpr rfl
  simpa [subgradient_descent_step] using subgradient_descent_norm_decrease hg xstar η hη

/-! ## relu 实例（迭代版）：轨迹保持 x_t > 0 时，差距求和界成立（g ≡ 1） -/

theorem relu_subgradient_descent_gap_sum (η : ℝ) (x0 xstar : ℝ) (T : ℕ)
    (hη : 0 ≤ η) (hpos : ∀ n : ℕ, 0 < SubgradientIterate (fun _ => 1) η n x0) :
    2 * η * (∑ t in Finset.range T, (relu (SubgradientIterate (fun _ => 1) η t x0) - relu xstar)) ≤
      ‖x0 - xstar‖ ^ 2 + η ^ 2 * (∑ t in Finset.range T, ‖(1 : ℝ)‖ ^ 2) := by
  simpa using
    (subgradient_descent_gap_sum_seq relu (fun _ => 1) η xstar T
      (fun n => (relu_subgradient_positive (SubgradientIterate (fun _ => 1) η n x0) 1 (hpos n)).mpr rfl)
      (fun n => by rfl)
      hη)

/-! ## 注：闭环语义
  次梯度定义（RealSubgradient）→ 次梯度不等式（引理 2）→ 单步范数收缩（引理 3）
  → 求和 + 望远镜（引理 4）→ 平均/单步次优差距（定理 5/5b）→ 最优步长 O(GD/√T)
  （定理 6）。次梯度下降不收缩，故不接 contraction_converges（RealConvergence）；
  这是非光滑优化的本质：O(1/√T) 取代几何收敛。 -/

end Lattice
