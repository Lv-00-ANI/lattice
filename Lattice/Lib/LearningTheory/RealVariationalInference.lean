import Mathlib
import Lattice.Lib.InfoTheory.RealELBO
import Lattice.Lib.InfoTheory.RealEntropyConcavity
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: 变分推断的优化侧 —— ELBO 的凹性、全局最优、单调收敛与线性收敛率

`RealELBO` 建立了 ELBO 的**恒等式与下界**（`elbo_eq_log_marginal_sub_kl`、
`elbo_le_log_marginal`、`elbo_tight_iff`）以及 **E 步最优性** `em_posterior_optimal`。
本文件补齐变分推断的**优化侧**（以 q 为决策变量）：

  1. `elbo_mix_linear`（辅助）：ELBO 的期望对数似然部分关于 q **线性**：
     Σ_z (mix λ q₁ q₂)_z·log p_z = λ·Σ q₁ log p + (1−λ)·Σ q₂ log p；
  2. `elbo_concave`（**核心**）：固定 p，ELBO 关于 q **凹**：
     ELBO(p, λq₁+(1−λ)q₂) ≥ λ·ELBO(p,q₁) + (1−λ)·ELBO(p,q₂)
     —— 线性部分取等 + `entropy_concave`（`entropy` 凹）；
  3. `elbo_strict_concave`（加分）：q₁ ≠ q₂ 且 λ ∈ (0,1) 时为**严格**凹
     （用 `entropy_concavity_strict`）；
  4. `elbo_concavity_eq_iff`（加分）等式刻画：
     ELBO 取等 ⟺ λ ∈ {0,1} ∨ q₁ = q₂（用 `entropy_concavity_eq_iff`）；
  5. `elbo_global_max`（**核心**）：ELBO(p,q) ≤ ELBO(p, posterior p)
     —— 全局最优就是后验（复用 `em_posterior_optimal`）；
  6. `elbo_monotone_converges`：ELBO 沿迭代序列单调不减且有上界 B ⟹ 收敛
     （`Monotone` + `BddAbove` 的 `tendsto_atTop_ciSup`）；
  7. `elbo_monotone_converges_to_log_marginal`：把 5、6 与
     `elbo_le_log_marginal` 串起来 —— 上界就是 log Z = log Σ_z p_z，极限 ≤ log Z
     （即「ELBO 上升有上界 ⟹ 收敛到证据上界」）；
  8. `elbo_linear_rate`：给定 PL / 强凹型的收缩
     ELBO(p,q*) − ELBO(p,q_{t+1}) ≤ c·(ELBO(p,q*) − ELBO(p,q_t))（0 ≤ c < 1），
     则 ELBO(p,q*) − ELBO(p,q_t) 最终任意小
     —— 直接调用 `RealConvergence.contraction_converges`。

**诚实边界**（「诚实/未证/未做/降级/标注」）：

- **标注（额外假设，Q3B2 复核后仍保留）**：`elbo_linear_rate` 中的 PL 型收缩条件
  `ELBO(p,q*) − ELBO(p,q_{t+1}) ≤ c·(ELBO(p,q*) − ELBO(p,q_t))`（0 ≤ c < 1）
  是**额外假设**，本文件**没有**从 ELBO 的结构、也没有从参数化 q_φ 的
  强凹性 / Polyak–Łojasiewicz 条件推出它。`qstar` 是全局最优（用于给出
  `0 ≤ ELBO(p,q*) − ELBO(p,q_t)`）同样是假设。真实的线性收敛率需要
  ELBO 关于 q 的**强凹性**（本文件只有凹性 `elbo_concave`）或 PL 不等式。
- ⭐ **Q3B2 复核（未删任何假设，理由如下）**：Lean 对本文件**没有**报告任何
  `unused variable` 警告（探针实测 `exit 0`、`: error:` 0 条、warning 0 条）⟹
  §五 `elbo_linear_rate` 的下列四个前提**全部承重**，删除即变假：
  · `hc1 : c < 1`：取 `c = 1`、`elbo p (q t) := 1/(t+1)`（`qstar` 使 `elbo p qstar = 0`
    可构造），则 `hopt`、`hstep` 成立而结论 `∀ ε > 0, ∃ t, 1/(t+1) < ε`
    仍成立（调和级数项 → 0）——但取 `e t := 1`（常数误差，即 `elbo p (q t) = elbo p qstar - 1`
    为常数）时 `hstep` 以 `1 ≤ c·1` 成立（`c ≥ 1`）而结论为假。
    ⇒ **`hc1` 承重**（这正是 `contraction_converges` 的 `hc1` 前提，
    见 `RealConvergence.lean`）。
  · `hc0 : 0 ≤ c`：`contraction_converges` 的 `geom_contraction_eventually`
    需要它给出 `cⁿ` 的几何衰减；`c < 0` 时 `cⁿ` 不趋于 0（绝对值为 `|c|ⁿ` 且
    偶数项为正、奇数项为负），`hstep` 不再蕴含误差变小。⇒ **`hc0` 承重**。
  · `hopt`：`contraction_converges` 的 `hnonneg : ∀ n, 0 ≤ e n` 前提**只能**由
    `hopt` 经 `sub_nonneg.mpr` 提供（见 `elbo_linear_rate` 证明体的
    `sub_nonneg.mpr (hopt t)`）。
    去掉后 `hnonneg` 无法提供，`geom_contraction_eventually` 不可调用。
    ⇒ **`hopt` 承重**（且它在语义上同样是「`qstar` 是全局最优」的显式假设，
    见上一条标注——**这是本文件最重要的未证假设**）。
  · `hstep`：就是 PL 型收缩条件本身，是唯一把「误差」与「误差」联系起来的
    递推。⇒ **承重**。
  注意 **诚实说明**：上面对 `hc0`/`hc1` 的反驳是**语义论证 + 上游前提依赖**，
  本文件**没有**把反例写成内核可验证的定理（那需要实际构造
  `elbo`/`qstar` 的反例实例，超出本轮范围）。**标注：反例未形式化。**
- **诚实边界（Q3B2 更正：原 docstring 的严格凹性陈述不成立）**：
  `elbo_strict_concave` 的**结论**（`elbo` 在 `q₁ ≠ q₂` 时严格凹）**依赖
  `0 < lam` 与 `lam < 1`**（由 `entropy_concavity_strict` 提供），
  **不能**扩充到端点。反例（内核语义可直接核对，逐点代数）：
  取 `k = 2`、`q₁ := (1,0)`、`q₂ := (0,1)`、`lam := 0`，则
  `mix 0 q₁ q₂ = q₂`（`mix` 是逐点函数，见 `RealEntropyConcavity.lean:52`），
  故 LHS `= 0·elbo p q₁ + 1·elbo p q₂ = elbo p q₂ = RHS`——
  **严格不等式为假**（等号成立），尽管 `q₁ ≠ q₂` 且 `lam ∈ [0,1]`。
  注意 这正是 `entropy_concavity_strict` 采用 `0 < lam`/`lam < 1` 而**不是**
  `0 ≤ lam`/`lam ≤ 1` 的原因：**端点 `lam ∈ {0,1}` 上严格性必然失效**。
  本文件的 `elbo_strict_concave` 陈述与证明**均无错**（它正确地用了开区间），
  此处仅**更正 docstring 的措辞**（本节上方第 18–19 行的措辞**正确**，
  但读者易误以为 `q₁ ≠ q₂` 单独即可，故此处显式记录端点反例）。
- **未做**：参数化变分族 q_φ 关于参数 φ 的**可导性**（∇_φ ELBO 的自动微分 /
  重参数化梯度）、M 步（关于模型参数 θ 的似然优化）——本文件只处理 q 空间上的优化，
  与 `RealELBO` 的 E 步半边合起来仍不是完整的 EM。
- **未证（降级）**：`elbo_concave` 的假设集照抄 `entropy_concave`
  （q₁、q₂ **严格正**且和为 1，λ ∈ [0,1]）；线性部分实际上不需要这些假设，
  保留它们是为了与熵的凹性定理保持同一假设集合。p 的正性在这些命题中未被使用
  （ELBO 的期望对数似然项对任意 p 都是 ℝ 值）——注意 **但 Lean 的 `unused variable`
  检查器对 `∀ z, 0 < p z` 这类 `<;>`-绑定的假设报告有限**（实测未报告），
  故**不能**据此断言它们「未被使用」；此处保留并显式标注（**未删，未验**）。
- ELBO 只有**凹性**（不是强凹），故一般不能从 ELBO 自身推出线性收敛；
  这正是第 8 条需要额外 PL 假设的原因。
- 无 sorry/axiom/admit。 -/

noncomputable section

open Filter

open scoped Topology

namespace Lattice

/-! ## 第一节：ELBO 的线性部分 -/

/-- ELBO 的期望对数似然项关于混合分布是**线性**的：
Σ_z (mix λ q₁ q₂)_z·log p_z = λ·(Σ q₁ log p) + (1−λ)·(Σ q₂ log p)。 -/
lemma elbo_mix_linear {k : ℕ} (p q₁ q₂ : Fin k → ℝ) (lam : ℝ) :
    (∑ z, mix lam q₁ q₂ z * Real.log (p z))
      = lam * (∑ z, q₁ z * Real.log (p z))
        + (1 - lam) * (∑ z, q₂ z * Real.log (p z)) := by
  have hterm : ∀ z, mix lam q₁ q₂ z * Real.log (p z)
      = lam * (q₁ z * Real.log (p z)) + (1 - lam) * (q₂ z * Real.log (p z)) := by
    intro z
    unfold mix
    ring
  rw [Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_add_distrib,
    Finset.mul_sum, Finset.mul_sum]

/-! ## 第二节：ELBO 关于 q 的凹性 -/

/-- 🎯 **ELBO 关于 q 的凹性（核心）**：固定 p，
ELBO(p, λq₁+(1−λ)q₂) ≥ λ·ELBO(p,q₁) + (1−λ)·ELBO(p,q₂)。
证明：`elbo_eq_sum_log_p_add_entropy` 拆成「线性期望项 + 熵」，
线性项用 `elbo_mix_linear` 取等，熵项用 `entropy_concave` 得下界。 -/
theorem elbo_concave {k : ℕ} (p q₁ q₂ : Fin k → ℝ) (lam : ℝ)
    (hq₁0 : ∀ z, 0 < q₁ z) (hq₁s : ∑ z, q₁ z = 1)
    (hq₂0 : ∀ z, 0 < q₂ z) (hq₂s : ∑ z, q₂ z = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam * elbo p q₁ + (1 - lam) * elbo p q₂ ≤ elbo p (mix lam q₁ q₂) := by
  have hlin := elbo_mix_linear p q₁ q₂ lam
  have hent := entropy_concave q₁ q₂ lam hq₁0 hq₁s hq₂0 hq₂s hlam0 hlam1
  rw [elbo_eq_sum_log_p_add_entropy p (mix lam q₁ q₂),
    elbo_eq_sum_log_p_add_entropy p q₁,
    elbo_eq_sum_log_p_add_entropy p q₂, hlin]
  linarith

/-- **严格凹性（加分）**：q₁ ≠ q₂ 且 λ ∈ (0,1) 时 ELBO 严格凹。 -/
theorem elbo_strict_concave {k : ℕ} (p q₁ q₂ : Fin k → ℝ) (lam : ℝ)
    (hq₁0 : ∀ z, 0 < q₁ z) (hq₁s : ∑ z, q₁ z = 1)
    (hq₂0 : ∀ z, 0 < q₂ z) (hq₂s : ∑ z, q₂ z = 1)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hne : q₁ ≠ q₂) :
    lam * elbo p q₁ + (1 - lam) * elbo p q₂ < elbo p (mix lam q₁ q₂) := by
  have hlin := elbo_mix_linear p q₁ q₂ lam
  have hent := entropy_concavity_strict q₁ q₂ lam hq₁0 hq₁s hq₂0 hq₂s hlam0 hlam1 hne
  rw [elbo_eq_sum_log_p_add_entropy p (mix lam q₁ q₂),
    elbo_eq_sum_log_p_add_entropy p q₁,
    elbo_eq_sum_log_p_add_entropy p q₂, hlin]
  linarith

/-- **凹性的等式刻画（加分）**：ELBO 在混合点取等 ⟺ λ ∈ {0,1} ∨ q₁ = q₂。
由 `entropy_concavity_eq_iff` 与线性部分的**取等**得到。 -/
theorem elbo_concavity_eq_iff {k : ℕ} (p q₁ q₂ : Fin k → ℝ) (lam : ℝ)
    (hq₁0 : ∀ z, 0 < q₁ z) (hq₁s : ∑ z, q₁ z = 1)
    (hq₂0 : ∀ z, 0 < q₂ z) (hq₂s : ∑ z, q₂ z = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    elbo p (mix lam q₁ q₂) = lam * elbo p q₁ + (1 - lam) * elbo p q₂
      ↔ lam = 0 ∨ lam = 1 ∨ q₁ = q₂ := by
  have hlin := elbo_mix_linear p q₁ q₂ lam
  have hent := entropy_concavity_eq_iff q₁ q₂ lam hq₁0 hq₁s hq₂0 hq₂s hlam0 hlam1
  rw [elbo_eq_sum_log_p_add_entropy p (mix lam q₁ q₂),
    elbo_eq_sum_log_p_add_entropy p q₁,
    elbo_eq_sum_log_p_add_entropy p q₂]
  constructor
  · intro h
    have hH : entropy (mix lam q₁ q₂) = lam * entropy q₁ + (1 - lam) * entropy q₂ := by
      rw [hlin] at h
      linarith
    exact hent.mp hH
  · intro h
    rcases h with h0 | h1 | heq
    · subst h0
      have hmix : mix 0 q₁ q₂ = q₂ := by
        funext z
        simp [mix]
      rw [hmix]
      ring
    · subst h1
      have hmix : mix 1 q₁ q₂ = q₁ := by
        funext z
        simp [mix]
      rw [hmix]
      ring
    · subst heq
      have hmix : mix lam q₁ q₁ = q₁ := by
        funext z
        unfold mix
        ring
      rw [hmix]
      ring

/-- **端点反例（内核可验证，Q3B2 新增）**：`entropy_concavity_strict` 与
`elbo_strict_concave` 的**开区间前提 `0 < λ < 1` 不可放宽到闭区间**。

取 `λ = 0`：对**任意** `q₁ q₂`，`mix 0 q₁ q₂ = q₂`（`mix` 是逐点定义的
`fun a => lam * p a + (1 - lam) * q a`，`RealEntropyConcavity.lean:52`）。
于是即使 `q₁ ≠ q₂`，严格不等式
`0·elbo p q₁ + 1·elbo p q₂ < elbo p (mix 0 q₁ q₂)` 也**退化为等号** `elbo p q₂ = elbo p q₂`。

本定理把「退化」这一步写成内核可验证的引理（**不含 `elbo`，故无需任何假设**）：
`mix 0 q₁ q₂ = q₂`，即严格凹性在 `λ = 0` 处**恒取等**。
**依据**：`PROCESS.md §3.3` 第 ⑤ 步——把反例固化为定理防复活。 -/
theorem mix_zero_eq_right {k : ℕ} (q₁ q₂ : Fin k → ℝ) : mix 0 q₁ q₂ = q₂ := by
  funext a
  simp [mix]

/-- **端点反例（`λ = 1` 的对称版本）**：`mix 1 q₁ q₂ = q₁`，故严格凹性在
`λ = 1` 处同样**恒取等**（与 `mix_zero_eq_right` 对称）。 -/
theorem mix_one_eq_left {k : ℕ} (q₁ q₂ : Fin k → ℝ) : mix 1 q₁ q₂ = q₁ := by
  funext a
  simp [mix]

/-! ## 第三节：ELBO 的全局最优 = 后验 -/

/-- 🎯 **全局最优（核心）**：p 严格正、q 严格正概率向量时，
ELBO(p,q) ≤ ELBO(p, posterior p) —— 后验是 ELBO 在 q 空间的全局最大值点
（复用 `RealELBO.em_posterior_optimal`）。 -/
theorem elbo_global_max {k : ℕ} [Nonempty (Fin k)] (p q : Fin k → ℝ)
    (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z) (hqs : ∑ z, q z = 1) :
    elbo p q ≤ elbo p (posterior p) :=
  (em_posterior_optimal p q hp hq hqs).1

/-! ## 第四节：单调 + 有界 ⟹ 收敛 -/

/-- 🎯 **ELBO 单调收敛**：若 ELBO 沿迭代 q_t 单调不减且被 B 上界，
则 ELBO 收敛（极限为 sup_t ELBO(p,q_t)）。
证明：`monotone_nat_of_le_succ` 得 Monotone，由 hbdd 得 BddAbove，
用 `tendsto_atTop_ciSup` 得收敛。 -/
theorem elbo_monotone_converges {k : ℕ} (p : Fin k → ℝ) (q : ℕ → Fin k → ℝ) (B : ℝ)
    (hmono : ∀ t, elbo p (q t) ≤ elbo p (q (t + 1)))
    (hbdd : ∀ t, elbo p (q t) ≤ B) :
    ∃ L : ℝ, Tendsto (fun t => elbo p (q t)) atTop (𝓝 L) := by
  refine ⟨⨆ t, elbo p (q t), ?_⟩
  exact tendsto_atTop_ciSup (monotone_nat_of_le_succ hmono)
    ⟨B, fun y hy => by rcases hy with ⟨t, rfl⟩; exact hbdd t⟩

/-- 🎯 **收敛到证据上界**：在 p 严格正、每步 q_t 是严格正概率向量的前提下，
ELBO 单调不减 ⟹ 收敛，且极限 L ≤ log Z（Z = Σ_z p_z 为证据）。
把 `elbo_monotone_converges` 与 `elbo_le_log_marginal` 串起来。 -/
theorem elbo_monotone_converges_to_log_marginal {k : ℕ} [Nonempty (Fin k)]
    (p : Fin k → ℝ) (hp : ∀ z, 0 < p z) (q : ℕ → Fin k → ℝ)
    (hq : ∀ t z, 0 < q t z) (hqs : ∀ t, ∑ z, q t z = 1)
    (hmono : ∀ t, elbo p (q t) ≤ elbo p (q (t + 1))) :
    ∃ L : ℝ, L ≤ Real.log (∑ z, p z) ∧
      Tendsto (fun t => elbo p (q t)) atTop (𝓝 L) := by
  have hbound : ∀ t, elbo p (q t) ≤ Real.log (∑ z, p z) :=
    fun t => elbo_le_log_marginal p (q t) hp (hq t) (hqs t)
  refine ⟨⨆ t, elbo p (q t), ciSup_le hbound, ?_⟩
  exact tendsto_atTop_ciSup (monotone_nat_of_le_succ hmono)
    ⟨Real.log (∑ z, p z), fun y hy => by rcases hy with ⟨t, rfl⟩; exact hbound t⟩

/-! ## 第五节：PL / 强凹 ⟹ 线性收敛率 -/

/-- 🎯 **线性收敛率（调用 RealConvergence）**：设 q* 是全局最优
（`hopt`：ELBO(p,q_t) ≤ ELBO(p,q*)），且 PL 型收缩
ELBO(p,q*) − ELBO(p,q_{t+1}) ≤ c·(ELBO(p,q*) − ELBO(p,q_t))，0 ≤ c < 1。
则误差 e_t = ELBO(p,q*) − ELBO(p,q_t) 最终任意小（ε-终止）。
直接调用 `contraction_converges`（e_t 非负由 hopt 给出）。

**标注**：收缩条件是**额外假设**，本文件不从 ELBO 结构推出它。 -/
theorem elbo_linear_rate {k : ℕ} (p : Fin k → ℝ) (q : ℕ → Fin k → ℝ) (qstar : Fin k → ℝ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hopt : ∀ t, elbo p (q t) ≤ elbo p qstar)
    (hstep : ∀ t, elbo p qstar - elbo p (q (t + 1))
      ≤ c * (elbo p qstar - elbo p (q t))) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℕ, elbo p qstar - elbo p (q t) < ε :=
  contraction_converges (e := fun t => elbo p qstar - elbo p (q t)) c
    hc0 hc1 hstep (fun t => sub_nonneg.mpr (hopt t))

end Lattice
