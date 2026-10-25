import Mathlib

/-!
# LATTICE: 推测解码的正确性 —— 接受/拒绝与目标分布等价（有限分布代数）

推测解码（speculative decoding，Leviathan et al. / Chen et al.）用一个廉价的**草稿
分布** `q` 生成候选 token，再用**目标分布** `p` 做接受/拒绝检验，从而在不改变输出
分布的前提下减少一次前向调用：

  · 草稿采样 `i ~ q`，以 `acceptProb p q i = min 1 (p i / q i)` 接受；
  · 拒绝时从残差分布 `(p i − min(p i, q i)) / R`（`R = Σ_j (p j − min(p j, q j))`）
    重采样。

本文件在**有限字母表**上给出该机制的代数正确性（全部无 sorry / axiom / admit）：

  1. `acceptProb` / `residualMass` / `residualDist` / `speculativeDist`：机制定义；
  2. `accept_mass_eq_min`（核心代数引理）：`q i · acceptProb p q i = min (p i) (q i)`
     ——「按 q 采、按 min(1,p/q) 接受」的**接受质量**恰为 `min(p,q)`；
  3. `accept_reject_unbiased`：求和得 `Σ_i q i · acceptProb p q i = Σ_i min (p i) (q i)`
     ——接受-拒绝的**无偏性**（期望接受质量 = 逐点最小质量之和）；
  4. `residualMass_eq`：`R = Σp − Σ min(p,q)`（残差 = 总质量 − 接受质量）；
  5. `speculative_eq_target`（**核心**）：`R ≠ 0` ⟹ `speculativeDist p q = p`
     ——推测采样的输出分布**逐点等于目标分布**（分布等式，纯 `Finset`/`field` 代数）；
  6. `no_quality_loss`：分布相等 ⟹ **任意**统计量 `g` 的期望不变
     `Σ_i spec_i · g_i = Σ_i p_i · g_i`（质量无损的精确表述）；
  7. `speculative_nonneg` / `speculative_sum_one` / `spec_pmf`：输出分布是概率分布；
  8. `acceptance_rate_le_one`：接受率 ≤ 1（`Σ min ≤ Σp = 1`）；
  9. `speculative_tokens_ge_one` / `speculative_cost_per_token_le`：**加速结构**——
     每次调用产出 `1 + γ` 个 token（`γ ≥ 0` 为期望额外接受数），于是分摊到每 token 的
     成本 `c/(1+γ) ≤ c`（`c ≥ 0`）——计数/代价不等式，非墙钟时间定理。

**诚实假设与降级**（均显式标注）：
  · 有限字母表 `ι`（`Fintype` + `Nonempty`）；连续分布不在本文件范围；
  · `p`、`q` 非负：仅在 `accept_mass_eq_min` / `acceptance_rate_le_one` 中显式假设
    （乘除的单调性需要）；`speculative_eq_target` **不需要**非负性（纯代数等式）；
  · `Σ_i p i = 1`（`p` 是概率分布）只在概率性结论（`speculative_sum_one`、
    `acceptance_rate_le_one`）中假设；
  · `R ≠ 0`（`hR`）：残差质量非零。`R = 0` 时 `p = min(p,q) ≤ q`（`p` 处处不超 `q`），
    无需重采样；此时 `speculativeDist` 的除零项在 Lean 中为 0（`x / 0 = 0`），本文件
    不声称该退化情形的等价性（避免除零语义带来的伪结论）——这是**定义域限制**而非证明困难；
  · `residualDist` 在 `R = 0` 时被 Lean 定义为 `0 / 0 = 0`，故 `speculativeDist` 仍
    是良定义的函数；
  · **未涉及**：草稿/目标联合耦合的实现（`q` 与 `p` 的 coupling 存在性）、
    任意（非有限）测度空间、最优接受概率的**必然性**（本文件只证「按 min(1,p/q) 接受
    得到的输出恰为 p」，不证它是唯一/最优选择）、墙钟加速比（只给代价不等式）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## 机制定义 -/

/-- 接受概率：草稿采到 `i` 时以 `min 1 (p i / q i)` 接受（`q i = 0` 时 Lean 约定
`p i / 0 = 0`，接受概率为 0）。 -/
def acceptProb (p q : ι → ℝ) : ι → ℝ :=
  fun i => min 1 (p i / q i)

/-- 残差质量 `R = Σ_i (p i − min (p i) (q i))`：拒绝后重采样分布的归一化常数。 -/
def residualMass (p q : ι → ℝ) : ℝ :=
  ∑ i, (p i - min (p i) (q i))

/-- 残差分布（拒绝后重采样）：`(p i − min (p i, q i)) / R`。 -/
def residualDist (p q : ι → ℝ) : ι → ℝ :=
  fun i => (p i - min (p i) (q i)) / residualMass p q

omit [Fintype ι] [Nonempty ι] in
/-- 推测采样的输出分布：`min(p,q) i + R · residualDist i`
（接受质量 ⊕ 拒绝概率 × 重采样分布）。 -/
def speculativeDist (p q : ι → ℝ) : ι → ℝ :=
  fun i => min (p i) (q i) + residualMass p q * residualDist p q i

/-! ## 定理一（核心代数引理）：接受质量 = 逐点最小质量
`q i · acceptProb p q i = min (p i) (q i)`（`p, q ≥ 0`）。 -/

lemma accept_mass_eq_min {p q : ι → ℝ} (i : ι) (hp : 0 ≤ p i) (hq : 0 ≤ q i) :
    q i * acceptProb p q i = min (p i) (q i) := by
  rcases eq_or_lt_of_le hq with hq0 | hqpos
  · unfold acceptProb
    rw [← hq0, div_zero, zero_mul, min_eq_right hp]
  · unfold acceptProb
    rcases le_total (p i) (q i) with h | h
    · rw [min_eq_left h, min_eq_right ((div_le_one hqpos).mpr h)]
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm (q i), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hqpos), mul_one]
    · rw [min_eq_right h, min_eq_left ((one_le_div hqpos).mpr h)]
      ring

omit [Nonempty ι] in
omit [Fintype ι] [Nonempty ι] in
/-- 接受概率不超过 1。 -/
lemma acceptProb_le_one (p q : ι → ℝ) (i : ι) : acceptProb p q i ≤ 1 :=
  min_le_left _ _

/-! ## 定理二：接受-拒绝无偏性（期望接受质量 = 逐点最小质量之和） -/

theorem accept_reject_unbiased {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    ∑ i, q i * acceptProb p q i = ∑ i, min (p i) (q i) :=
  Finset.sum_congr rfl fun i _ => accept_mass_eq_min i (hp i) (hq i)

/-! ## 引理：残差质量 = 总质量 − 接受质量 -/

lemma residualMass_eq (p q : ι → ℝ) :
    residualMass p q = (∑ i, p i) - ∑ i, min (p i) (q i) := by
  unfold residualMass
  rw [Finset.sum_sub_distrib]

omit [Nonempty ι] in
omit [Nonempty ι] in
/-- 残差质量非负。 -/
lemma residualMass_nonneg (p q : ι → ℝ) : 0 ≤ residualMass p q := by
  unfold residualMass
  exact Finset.sum_nonneg fun i _ => sub_nonneg.mpr (min_le_left _ _)

/-! ## 定理三（核心）：推测采样与目标分布等价
`R ≠ 0` ⟹ `∀ i, speculativeDist p q i = p i`（分布等式）。 -/

theorem speculative_eq_target {p q : ι → ℝ} (hR : residualMass p q ≠ 0) :
    ∀ i, speculativeDist p q i = p i := by
  intro i
  have hcancel : residualMass p q * residualDist p q i = p i - min (p i) (q i) := by
    unfold residualDist
    rw [div_eq_mul_inv, ← mul_assoc, mul_comm (residualMass p q), mul_assoc,
      mul_inv_cancel₀ hR, mul_one]
  unfold speculativeDist
  rw [hcancel]
  ring

/-! ## 定理四：质量无损（分布相等 ⟹ 任意统计量的期望不变） -/

theorem no_quality_loss {p q : ι → ℝ} (hR : residualMass p q ≠ 0) (g : ι → ℝ) :
    ∑ i, speculativeDist p q i * g i = ∑ i, p i * g i :=
  Finset.sum_congr rfl fun i _ => by rw [speculative_eq_target hR i]

/-! ## 定理五：输出分布是概率分布 -/

theorem speculative_nonneg {p q : ι → ℝ} (hR : residualMass p q ≠ 0)
    (hp : ∀ i, 0 ≤ p i) (i : ι) : 0 ≤ speculativeDist p q i := by
  rw [speculative_eq_target hR i]
  exact hp i

theorem speculative_sum_one {p q : ι → ℝ} (hR : residualMass p q ≠ 0)
    (hpsum : ∑ i, p i = 1) : ∑ i, speculativeDist p q i = 1 := by
  calc
    ∑ i, speculativeDist p q i = ∑ i, p i :=
      Finset.sum_congr rfl fun i _ => speculative_eq_target hR i
    _ = 1 := hpsum

/-- 推测采样的输出分布与目标分布同为概率分布（`p` 是分布时）。 -/
theorem spec_pmf {p q : ι → ℝ} (hR : residualMass p q ≠ 0) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) :
    (∀ i, 0 ≤ speculativeDist p q i) ∧ (∑ i, speculativeDist p q i = 1) :=
  ⟨fun i => speculative_nonneg hR hp i, speculative_sum_one hR hpsum⟩

/-! ## 定理六：接受率 ≤ 1 -/

theorem acceptance_rate_le_one {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) : ∑ i, q i * acceptProb p q i ≤ 1 := by
  rw [accept_reject_unbiased hp hq]
  calc
    ∑ i, min (p i) (q i) ≤ ∑ i, p i := Finset.sum_le_sum fun i _ => min_le_left _ _
    _ = 1 := hpsum

/-! ## 定理七（加速结构）：每次调用 ≥ 1 个 token，分摊代价不增
`γ ≥ 0` 为期望额外接受数，则每次调用产出 `1 + γ` 个 token；固定每次调用代价 `c ≥ 0`
时分摊到每 token 的代价 `c/(1+γ) ≤ c`。这是**组合/代价计数**陈述。 -/

theorem speculative_tokens_ge_one (γ : ℝ) (hγ : 0 ≤ γ) : 1 ≤ 1 + γ := by linarith

theorem speculative_cost_per_token_le (c γ : ℝ) (hc : 0 ≤ c) (hγ : 0 ≤ γ) :
    c / (1 + γ) ≤ c := by
  have hpos : (0 : ℝ) < 1 + γ := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- `γ > 0` 时严格更快（严格不等式）。 -/
theorem speculative_cost_per_token_lt (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) :
    c / (1 + γ) < c := by
  have hpos : (0 : ℝ) < 1 + γ := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

end Lattice
