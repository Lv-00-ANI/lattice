import Mathlib
import Lattice.Lib.Optim.RealSGDStochastic
import Lattice.Lib.Convex.RealConvexProjection
/-!
# LATTICE: 投影随机梯度下降的完整 O(1/√T)（无界方差 + 平均迭代）

`RealSGDStochastic` 已在有限概率空间上给出 SGD 的期望收敛框架与 O(GD/√T) 率，
但（a）步子是**无投影**的；（b）逐步期望收缩 `hstep` 作为假设；（c）只给「存在一步」，
未给**平均迭代**（`x̄_T`）的函数值界。本文件补齐：

* **投影步** `Π_C(x − η ĝ)` 与**投影单步期望收缩**（用 `RealConvexProjection` 的
  投影非扩张性；`x* ∈ C` 是关键）；
* **无界方差的机器验证说明**：二阶矩界 `E‖g‖² ≤ G²` **不蕴含**逐样本有界
  `∀ω, ‖g ω‖ ≤ G`（给出具体反例，说明该假设比「一致有界梯度」更弱）；
* **平均迭代的差距界**（Jensen）：`ConvexOn` 下
  `f(x̄_T) ≤ (1/T)∑ f(x_t)`，故
  `E[f(x̄_T)] − f* ≤ E₀/(2ηT) + ηG²/2`，其中 `x̄_T` 是迭代的算术平均；
* 最优步长 `η = D/(G√T)` 下的 `∃t<T, E[f(x_t)−f*] ≤ D·G/√T`（投影版）。

定理清单：
  1. `projSgdUpdate`（def）、`projOn_point_le`（投影非扩张到固定点）；
  2. `proj_sgd_expectation_contraction`（**投影单步期望收缩**）；
  3. `unbounded_variance_weaker_than_uniform`（**无界方差的反例**，机器验证）；
  4. `Expect_finset_sum`（期望与有限和交换）；
  5. `sgd_average_jensen`（**Jensen**，调用 mathlib `ConvexOn.map_sum_le`）；
  6. `sgd_avg_gap_bound`（平均期望差距）、`sgd_average_iterate_gap`（**平均迭代的函数值界**）；
  7. `sgd_projected_rate_bound`（**投影版 O(GD/√T)**，含最优步长）。

**诚实边界**：
- 与 `RealSGDStochastic` 相同的标注：真实 SGD 的**条件期望塔性质 / 独立采样**未构造，
  「逐步期望收缩」仍是本节的前提（对投影步，本文件证明它在**任一固定状态 x** 处、
  对无偏估计取期望后成立，见定理 2）；
- `Π_C` 用 `RealConvexProjection.projOn`（需要 `C` 非空、`IsComplete`、`Convex`）；
  在 `ℝ` 上 `IsComplete C` 由闭性给出，本文件把 `IsComplete` 作为假设传入；
- 平均迭代的 Jensen 用 mathlib 的 `ConvexOn.map_sum_le`（完整证明，无缺口）；
- 「无界方差」定理只是**假设强弱**的机器验证说明（二阶矩界更弱），不是收敛率；
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Lattice

variable {Ω : Type*} [Fintype Ω]

/-! ## 一、投影 SGD 步 -/

/-- **投影 SGD 步**：`x⁺ = Π_C(x − η ĝ)`（`Π_C` 是 `RealConvexProjection.projOn`）。 -/
def projSgdUpdate (C : Set ℝ) (hne : C.Nonempty) (hcomp : IsComplete C) (hconv : Convex ℝ C)
    (eta x ghat : ℝ) : ℝ :=
  projOn C hne hcomp hconv (sgd_update eta x ghat)

/-- **投影非扩张（到固定点）**：`x* ∈ C` ⟹ `‖Π_C(u) − x*‖ ≤ ‖u − x*‖`。
由 `RealConvexProjection.proj_nonexpansive_of_variational`（`x*` 自身的变分不等式平凡）。 -/
theorem projOn_point_le (C : Set ℝ) (hne : C.Nonempty) (hcomp : IsComplete C)
    (hconv : Convex ℝ C) {xstar u : ℝ} (hxC : xstar ∈ C) :
    ‖projOn C hne hcomp hconv u - xstar‖ ≤ ‖u - xstar‖ :=
  proj_nonexpansive_of_variational (projOn_mem C hne hcomp hconv u) hxC
    (projOn_variational C hne hcomp hconv u)
    (fun z _ => by simp)
/-- **投影 SGD 单步期望收缩**：`E[ĝ]` 是 `f` 在 `x` 处的（次）梯度、`E[ĝ²] ≤ G²`、
`x* ∈ C` ⟹
`E‖Π_C(x − ηĝ) − x*‖² ≤ ‖x − x*‖² − 2η(f x − f x*) + η²G²`。 -/
theorem proj_sgd_expectation_contraction {f : ℝ → ℝ} {p : Ω → ℝ} (g : Ω → ℝ)
    (hp0 : ∀ ω, 0 ≤ p ω) (hpsum : (∑ ω, p ω) = 1)
    (C : Set ℝ) (hne : C.Nonempty) (hcomp : IsComplete C) (hconv : Convex ℝ C)
    {xstar : ℝ} (hxC : xstar ∈ C)
    (x eta G : ℝ) (heta : 0 ≤ eta)
    (hsub : Subgradient f x (Expect p g))
    (hG : Expect p (fun ω => g ω ^ 2) ≤ G ^ 2) :
    Expect p (fun ω => ‖projSgdUpdate C hne hcomp hconv eta x (g ω) - xstar‖ ^ 2) ≤
      ‖x - xstar‖ ^ 2 - 2 * eta * (f x - f xstar) + eta ^ 2 * G ^ 2 := by
  have hbase := sgd_expectation_contraction (p := p) g hpsum x xstar eta G heta hsub hG
  have hsq : ∀ ω, ‖projSgdUpdate C hne hcomp hconv eta x (g ω) - xstar‖ ^ 2
      ≤ ‖sgd_update eta x (g ω) - xstar‖ ^ 2 := by
    intro ω
    have h1 : ‖projOn C hne hcomp hconv (sgd_update eta x (g ω)) - xstar‖
        ≤ ‖sgd_update eta x (g ω) - xstar‖ :=
      projOn_point_le C hne hcomp hconv hxC (u := sgd_update eta x (g ω))
    have h2 : (0 : ℝ) ≤ ‖projOn C hne hcomp hconv (sgd_update eta x (g ω)) - xstar‖ :=
      norm_nonneg _
    have h3 : (0 : ℝ) ≤ ‖sgd_update eta x (g ω) - xstar‖ := norm_nonneg _
    have h4 : projSgdUpdate C hne hcomp hconv eta x (g ω)
        = projOn C hne hcomp hconv (sgd_update eta x (g ω)) := rfl
    rw [h4]
    nlinarith [h1, h2, h3]
  have hmono : Expect p (fun ω => ‖projSgdUpdate C hne hcomp hconv eta x (g ω) - xstar‖ ^ 2)
      ≤ Expect p (fun ω => ‖sgd_update eta x (g ω) - xstar‖ ^ 2) := by
    simp only [Expect]
    exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hsq ω) (hp0 ω))
  linarith [hmono, hbase]

/-! ## 二、无界方差：二阶矩界严格弱于逐样本有界 -/

/-- **二阶矩界不蕴含逐样本有界（机器验证反例）**：在两点均匀概率空间 `Fin 2` 上取
`G = 1`、`g 0 = √2`、`g 1 = 0`，则 `E[g²] = 1 ≤ G²` 但 `|g 0| = √2 > G`。
这说明 `E‖g‖² ≤ G²`（无界方差假设）**比**「`∀ω, ‖g ω‖ ≤ G`」**更弱**。 -/
theorem unbounded_variance_weaker_than_uniform :
    ∃ (G : ℝ) (g : Fin 2 → ℝ),
      Expect (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun ω => g ω ^ 2) ≤ G ^ 2 ∧ ∃ ω, G < |g ω| := by
  have hsqrt : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨1, fun ω : Fin 2 => if ω = 0 then Real.sqrt 2 else 0, ?_, ⟨0, ?_⟩⟩
  · simp only [Expect, Fin.sum_univ_two]
    simp only [show ((0 : Fin 2) = 0) = True from by simp, if_true]
    rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  · simp only [show ((0 : Fin 2) = 0) = True from by simp, if_true]
    rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
    exact hsqrt

/-! ## 三、平均迭代（Jensen） -/

/-- **期望与有限和交换**：`E[∑_i F_i] = ∑_i E[F_i]`。 -/
lemma Expect_finset_sum {ι : Type*} (p : Ω → ℝ) (F : ι → Ω → ℝ) (t : Finset ι) :
    Expect p (fun ω => ∑ i in t, F i ω) = ∑ i in t, Expect p (F i) := by
  classical
  induction t using Finset.induction with
  | empty => simp [Expect]
  | @insert a s ha ih =>
      have hfun : (fun ω => ∑ j in insert a s, F j ω)
          = (fun ω => F a ω + ∑ j in s, F j ω) := by
        funext ω
        rw [Finset.sum_insert ha]
      rw [hfun, Expect_add, ih, Finset.sum_insert ha]

/-- **Jensen 不等式（等权）**：`f` 凸、`T > 0` ⟹
`f((∑_{t<T} x_t)/T) ≤ (∑_{t<T} f(x_t))/T`。
由 mathlib `ConvexOn.map_sum_le` 取权重 `1/T`。 -/
theorem sgd_average_jensen {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {T : ℕ} (hT : 0 < T)
    (x : ℕ → ℝ) :
    f ((∑ t in Finset.range T, x t) / (T : ℝ))
      ≤ (∑ t in Finset.range T, f (x t)) / (T : ℝ) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hw : (∑ _t in Finset.range T, (1 / (T : ℝ))) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have h := ConvexOn.map_sum_le (t := Finset.range T) (w := fun _ : ℕ => 1 / (T : ℝ))
    (p := x) (s := Set.univ) hf (fun i _ => by positivity) hw (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at h
  have hl : (∑ t in Finset.range T, (1 / (T : ℝ)) * x t)
      = (∑ t in Finset.range T, x t) / (T : ℝ) := by
    rw [← Finset.mul_sum]
    ring_nf
  have hr : (∑ t in Finset.range T, (1 / (T : ℝ)) * f (x t))
      = (∑ t in Finset.range T, f (x t)) / (T : ℝ) := by
    rw [← Finset.mul_sum]
    ring_nf
  rwa [hl, hr] at h

/-- **平均期望差距界**：由 `RealSGDStochastic.sgd_expected_avg_gap` 除以 `T`：
`(1/T)∑_{t<T} E[f(x_t)−f*] ≤ E₀/(2ηT) + ηG²/2`。 -/
theorem sgd_avg_gap_bound {p : Ω → ℝ} (hp0 : ∀ ω, 0 ≤ p ω) (f : ℝ → ℝ)
    (x : ℕ → Ω → ℝ) (xstar G eta : ℝ) (T : ℕ) (hT : 0 < T) (heta : 0 < eta)
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * eta * ExpGap p f (x t) xstar + eta ^ 2 * G ^ 2) :
    (∑ t in Finset.range T, ExpGap p f (x t) xstar) / (T : ℝ)
      ≤ ExpDist p (x 0) xstar / (2 * eta * (T : ℝ)) + eta * G ^ 2 / 2 := by
  have havg := sgd_expected_avg_gap p hp0 f x xstar G eta T heta hstep
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  rw [div_le_iff₀ hTpos]
  have heq : (ExpDist p (x 0) xstar / (2 * eta * (T : ℝ)) + eta * G ^ 2 / 2) * (T : ℝ)
      = (ExpDist p (x 0) xstar + eta ^ 2 * (T : ℝ) * G ^ 2) / (2 * eta) := by
    field_simp
    ring
  rw [heq]
  linarith [havg]

/-- **平均迭代的函数值界（Jensen）**：`f` 凸、`∑p = 1`、`p ≥ 0`、逐步期望收缩 ⟹
`E[f(x̄_T) − f*] ≤ E₀/(2ηT) + ηG²/2`，其中 `x̄_T = (1/T)∑_{t<T} x_t`。

证明：逐点 Jensen 给 `f(x̄_T) ≤ (1/T)∑ f(x_t)`，取期望后化为
`(1/T)∑ ExpGap`，再用 `sgd_avg_gap_bound`。 -/
theorem sgd_average_iterate_gap {p : Ω → ℝ} (hp0 : ∀ ω, 0 ≤ p ω)
    (hpsum : (∑ ω, p ω) = 1) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (x : ℕ → Ω → ℝ) (xstar G eta : ℝ) (T : ℕ) (hT : 0 < T) (heta : 0 < eta)
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * eta * ExpGap p f (x t) xstar + eta ^ 2 * G ^ 2) :
    ExpGap p f (fun ω => (∑ t in Finset.range T, x t ω) / (T : ℝ)) xstar
      ≤ ExpDist p (x 0) xstar / (2 * eta * (T : ℝ)) + eta * G ^ 2 / 2 := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hjensen : ∀ ω, f ((∑ t in Finset.range T, x t ω) / (T : ℝ))
      ≤ (∑ t in Finset.range T, f (x t ω)) / (T : ℝ) :=
    fun ω => sgd_average_jensen hf hT (fun t => x t ω)
  have hmono : Expect p (fun ω => f ((∑ t in Finset.range T, x t ω) / (T : ℝ)) - f xstar)
      ≤ Expect p (fun ω => (∑ t in Finset.range T, f (x t ω)) / (T : ℝ) - f xstar) := by
    simp only [Expect]
    exact Finset.sum_le_sum (fun ω _ =>
      mul_le_mul_of_nonneg_left (by linarith [hjensen ω]) (hp0 ω))
  have hbridge : Expect p (fun ω => (∑ t in Finset.range T, f (x t ω)) / (T : ℝ) - f xstar)
      = (∑ t in Finset.range T, ExpGap p f (x t) xstar) / (T : ℝ) := by
    have h1 : (fun ω : Ω => (∑ t in Finset.range T, f (x t ω)) / (T : ℝ) - f xstar)
        = (fun ω : Ω => (1 / (T : ℝ)) * (∑ t in Finset.range T, f (x t ω)) - f xstar) := by
      funext ω
      rw [div_eq_mul_inv, one_div, mul_comm]
    rw [h1, Expect_sub, Expect_const_mul, Expect_finset_sum, Expect_const, hpsum, one_mul]
    have hexp : ∀ t : ℕ, Expect p (fun ω => f (x t ω)) = ExpGap p f (x t) xstar + f xstar := by
      intro t
      unfold ExpGap
      rw [Expect_sub, Expect_const, hpsum, one_mul]
      ring
    rw [Finset.sum_congr rfl (fun t _ => hexp t)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  calc
    ExpGap p f (fun ω => (∑ t in Finset.range T, x t ω) / (T : ℝ)) xstar
        = Expect p (fun ω => f ((∑ t in Finset.range T, x t ω) / (T : ℝ)) - f xstar) := rfl
    _ ≤ Expect p (fun ω => (∑ t in Finset.range T, f (x t ω)) / (T : ℝ) - f xstar) := hmono
    _ = (∑ t in Finset.range T, ExpGap p f (x t) xstar) / (T : ℝ) := hbridge
    _ ≤ ExpDist p (x 0) xstar / (2 * eta * (T : ℝ)) + eta * G ^ 2 / 2 :=
          sgd_avg_gap_bound hp0 f x xstar G eta T hT heta hstep

/-! ## 四、投影版的 O(GD/√T) -/

/-- **投影 SGD 的 O(GD/√T)**：与 `RealSGDStochastic.sgd_rate_bound` 相同的率，
只是单步假设由**投影**单步收缩（定理 2）提供：
`D² = E‖x_0 − x*‖²`、`η = D/(G√T)` ⟹ `∃ t < T, E[f(x_t) − f*] ≤ D·G/√T`。 -/
theorem sgd_projected_rate_bound {p : Ω → ℝ} (hp0 : ∀ ω, 0 ≤ p ω) (f : ℝ → ℝ)
    (x : ℕ → Ω → ℝ) (xstar G D eta : ℝ) (T : ℕ)
    (hG : 0 < G) (hT : 0 < T) (hD : 0 < D)
    (hD2 : ExpDist p (x 0) xstar = D ^ 2)
    (heta : eta = D / (G * Real.sqrt (T : ℝ)))
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * eta * ExpGap p f (x t) xstar + eta ^ 2 * G ^ 2) :
    ∃ t : ℕ, t < T ∧ ExpGap p f (x t) xstar ≤ D * G / Real.sqrt (T : ℝ) :=
  sgd_rate_bound p hp0 f x xstar G D eta T hG hT hD hD2 heta hstep

/-! ## 注：闭环语义与诚实边界
  投影非扩张 → 投影单步期望收缩 → 平均期望差距（除以 T）→**平均迭代的 Jensen 界**
  `E[f(x̄_T)−f*] ≤ E₀/(2ηT) + ηG²/2`；最优步长 `η = D/(G√T)` 给出 `∃t<T, ... ≤ DG/√T`。
  `unbounded_variance_weaker_than_uniform` 机器验证了「二阶矩界 ⟹ 逐样本有界」**不成立**
  （假设更弱，结论仍成立）。
  诚实降级清单：条件期望塔性质/独立采样未构造（与 RealSGDStochastic 一致）；
  `IsComplete C` 作为假设；`x*` 的可行性与无偏性 `Subgradient f x (Expect p g)` 为假设。 -/

end Lattice
