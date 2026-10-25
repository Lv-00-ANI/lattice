import Mathlib
import Lattice.Lib.InfoTheory.RealKL
/-!
# LATTICE: f-散度族 —— 一般 f-散度的非负性（Jensen）与实例

信息论线的推广：把 KL（RealKL）推广为 **f-散度族**

    D_f(p‖q) = Σ_a p_a·f(q_a / p_a)

一般非负性由 **Jensen 不等式**（`ConvexOn.map_sum_le`）给出：f 凸、f(1) = 0、
p 严格正概率向量、q 非负概率向量 ⟹ Σ_a p_a·f(q_a/p_a) ≥ f(Σ_a p_a·(q_a/p_a)) = f(1) = 0。

本文件建立：

  1. `fdiv_nonneg_of_convex`（核心）：上述 Jensen 路线的一般非负性；
  2. `mul_div_self`（工具引理）：b·(a/b) = a（b ≠ 0）；
  3. `chiSq` / `chiSq_nonneg`：χ² 散度（f(t) = (t−1)²）非负（逐项非负直接证）；
  4. `tv` / `tv_nonneg`：全变差（f(t) = |t−1|）非负（逐项非负直接证）；
  5. `kl_as_fdiv`：**KL 是 f-散度实例**——KL(p‖q) = D_f(q‖p)（f(t) = t·log t），
     纯代数桥（`kl_as_sum_log_ratio` + 分母消去），无需凸性；
  6. `kl_fdiv_nonneg`：由 KL 非负（`kl_nonneg`）得 D_{t log t} 实例的非负性。

**诚实边界**：
- `fdiv_nonneg_of_convex` 的凸性假设写在 `Set.Ici 0` 上（f-散度的自然定义域 t ≥ 0）；
  实例（χ²、TV、t·log t）各自用直接路线或引用既有结果，避免依赖未验证的凸性引理名。
- 未做：f-散度的联合凸性、对偶表示（Fenchel）、f-散度的单调变换不变性。

模型无关：任意有限 k、任意凸 f。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-! ## 定义：f-散度 -/

/-- f-散度：D_f(p‖q) = Σ_a p_a·f(q_a / p_a)。 -/
noncomputable def fDivergence (f : ℝ → ℝ) (p q : Fin k → ℝ) : ℝ :=
  ∑ a, p a * f (q a / p a)

/-! ## 工具引理：b·(a/b) = a -/

lemma mul_div_self (a b : ℝ) (hb : b ≠ 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel₀ _ hb]

/-! ## 定理一（核心）：凸 f、f(1)=0 ⟹ f-散度非负（Jensen）
路线：`ConvexOn.map_sum_le` 以权重 w_a = p_a、质点 x_a = q_a/p_a 得
f(Σ p_a·(q_a/p_a)) ≤ Σ p_a·f(q_a/p_a)；左端 = f(Σ q_a) = f(1) = 0。 -/

theorem fdiv_nonneg_of_convex {f : ℝ → ℝ} (hconv : ConvexOn ℝ (Set.Ici 0) f) (hf1 : f 1 = 0)
    (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a) (hq0 : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) :
    0 ≤ fDivergence f p q := by
  have hxmem : ∀ a ∈ (Finset.univ : Finset (Fin k)), q a / p a ∈ Set.Ici (0 : ℝ) := by
    intro a _
    exact div_nonneg (hq0 a) (le_of_lt (hp0 a))
  have hjen : f (∑ a, p a • (q a / p a)) ≤ ∑ a, p a • f (q a / p a) :=
    hconv.map_sum_le (t := Finset.univ) (w := fun a => p a) (p := fun a => q a / p a)
      (fun a _ => le_of_lt (hp0 a)) hpsum hxmem
  have hleft : ∑ a, p a • (q a / p a) = 1 := by
    have h1 : ∀ a : Fin k, p a • (q a / p a) = q a := by
      intro a
      rw [smul_eq_mul]
      exact mul_div_self (q a) (p a) (ne_of_gt (hp0 a))
    rw [Finset.sum_congr rfl (fun a _ => h1 a)]
    exact hqsum
  have hright : ∑ a, p a • f (q a / p a) = fDivergence f p q := by
    unfold fDivergence
    apply Finset.sum_congr rfl
    intro a _
    rw [smul_eq_mul]
  calc
    0 = f 1 := hf1.symm
    _ = f (∑ a, p a • (q a / p a)) := by rw [hleft]
    _ ≤ ∑ a, p a • f (q a / p a) := hjen
    _ = fDivergence f p q := hright

/-! ## 实例一：χ² 散度（f(t) = (t−1)²） -/

/-- χ² 散度：D(p‖q) = Σ_a p_a·(q_a/p_a − 1)²。 -/
noncomputable def chiSq (p q : Fin k → ℝ) : ℝ := fDivergence (fun t => (t - 1) ^ 2) p q

/-- χ² 散度非负：逐项 p_a ≥ 0 与平方 ≥ 0 直接得（也由 `fdiv_nonneg_of_convex` 得，
此处给出不依赖凸性引理名的直接证明）。 -/
theorem chiSq_nonneg (p q : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a) : 0 ≤ chiSq p q := by
  unfold chiSq fDivergence
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp0 a) (sq_nonneg _))

/-! ## 实例二：全变差（f(t) = |t−1|） -/

/-- 全变差型散度：D(p‖q) = Σ_a p_a·|q_a/p_a − 1|。 -/
noncomputable def tv (p q : Fin k → ℝ) : ℝ := fDivergence (fun t => |t - 1|) p q

/-- 全变差非负：逐项非负直接得。 -/
theorem tv_nonneg (p q : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a) : 0 ≤ tv p q := by
  unfold tv fDivergence
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp0 a) (abs_nonneg _))

/-! ## 实例三：KL 是 f-散度（f(t) = t·log t）
KL(p‖q) = Σ_a p_a·log(p_a/q_a) = Σ_a q_a·((p_a/q_a)·log(p_a/q_a)) = D_f(q‖p)。 -/

theorem kl_as_fdiv (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a) (hq0 : ∀ a, 0 < q a) :
    fDivergence (fun t => t * Real.log t) q p = kl p q := by
  rw [kl_as_sum_log_ratio p q hp0 hq0]
  unfold fDivergence
  apply Finset.sum_congr rfl
  intro a _
  calc
    q a * ((p a / q a) * Real.log (p a / q a))
        = (q a * (p a / q a)) * Real.log (p a / q a) := by rw [mul_assoc]
    _ = p a * Real.log (p a / q a) := by
          rw [mul_div_self (p a) (q a) (ne_of_gt (hq0 a))]

/-- KL 实例的 f-散度非负（由 `kl_nonneg` 直接转写）。 -/
theorem kl_fdiv_nonneg (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) :
    0 ≤ fDivergence (fun t => t * Real.log t) q p := by
  rw [kl_as_fdiv p q hp0 hq0]
  exact kl_nonneg p q hp0 hpsum hq0 hqsum

end Lattice
