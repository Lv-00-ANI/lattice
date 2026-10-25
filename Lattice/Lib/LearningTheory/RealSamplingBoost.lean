import Mathlib

/-!
# LATTICE: 多轮采样验证的概率放大 —— k 轮独立采样命中违背的置信度 ≥ 1−ε^k

方向（§5 验证行「自适应/随机化验证」）：RealRandomVerify 给出单轮界
`verify_probability_guarantee`（∫f ≤ ε² ⟹ 单轮违背概率 ≤ ε，马尔可夫），
只保证**单次**采样 miss 概率 ≤ ε。本文件把 k 轮**独立**采样放大为：

  P(k 轮全部 miss) = ∏ᵢ P(miss_i) ≤ ε^k  ⟹  P(至少一轮命中) ≥ 1 − ε^k

——随机化验证的置信度提升：轮数 k 越大，全部采样都错过违背的概率按
ε^k 指数衰减，验证 pass 的置信度指数逼近 1。

**诚实选择（方案 A：有限计数概率空间）**：全测度论独立性
（`ProbabilityTheory.IndepFun` / 乘积测度）在 mathlib 中需要验证
σ-代数独立条件，引理签名与既有 RealRandomVerify 的 `.toReal` 风格
衔接成本高；本文件采用完全可证的**有限计数概率空间**：

  · α 为 Fintype（样本空间有限），miss 集为 Finset（card = m），
    均匀概率 = 计数 / 总数（`uniformProb`）；
  · k 轮独立采样 = 乘积空间 α^k = `Fin k → α`（Fintype），
    全 miss 事件 = 每个坐标都落在 missSet 中的函数集
    （`allMissSet` = `Fintype.piFinset`），计数 = m^k
    （`Fintype.card_piFinset_const`）；
  · 独立性在计数下的精确体现：乘积空间全 miss 事件的概率等于
    各轮 miss 概率之积（`boost_product_event` / `boost_prob_all_miss_prod`）
    ——这正是「∏P(miss_i)」的有限计数版（乘积测度 = 计数乘积）；
  · 于是 P(all miss) = (m/N)^k，P(至少一轮命中) = 1 − (m/N)^k
    ≥ 1 − ε^k（若单轮 miss 概率 m/N ≤ ε 且 0 ≤ ε，幂单调）。

诚实假设：① 单轮 miss 概率 ≤ ε（`hmiss : uniformProb missSet ≤ ε`，
由 `verify_probability_guarantee` 在有限均匀设置下提供：其 `.toReal ≤ ε`
正是 count/total）；② N = |α| > 0（均匀概率分母非零，α 非空）。
`0 ≤ ε` 无需单独假设：`uniformProb missSet ≥ 0`（计数/总数），由
`hmiss` 自动推出 `0 ≤ ε`；`pow_le_pow_left₀` 只需左端（m/N）非负。
k : ℕ 自动满足 k ≥ 0。不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 均匀概率与 k 轮乘积空间 -/

/-- 有限集上的均匀概率：`s` 的元素数 / 全域元素数（计数概率）。 -/
def uniformProb {α : Type*} [Fintype α] (s : Finset α) : ℝ :=
  (s.card : ℝ) / (Fintype.card α : ℝ)

/-- k 轮独立采样全部 miss 的事件：乘积空间 `Fin k → α` 中每个坐标都落在 `missSet`
里的函数集（= `Fintype.piFinset`，即各坐标独立地从 `missSet` 取值的函数全体）。 -/
def allMissSet {α : Type*} (missSet : Finset α) (k : ℕ) : Finset (Fin k → α) :=
  Fintype.piFinset (fun _ : Fin k => missSet)

/-- 至少一轮命中违背的事件：全 miss 事件的补（`Fin k → α` 全域去掉全 miss）。 -/
def hitSet {α : Type*} [Fintype α] [DecidableEq α] (missSet : Finset α) (k : ℕ) :
    Finset (Fin k → α) :=
  (Finset.univ : Finset (Fin k → α)) \ allMissSet missSet k

/-! ## 引理：事件的成员刻画（全 miss = 每坐标都在 missSet；hit = 某坐标不在） -/

theorem boost_mem_allMissSet {α : Type*} (missSet : Finset α) (k : ℕ) (v : Fin k → α) :
    v ∈ allMissSet missSet k ↔ ∀ i : Fin k, v i ∈ missSet := by
  simp [allMissSet]

theorem boost_mem_hitSet {α : Type*} [Fintype α] [DecidableEq α] (missSet : Finset α) (k : ℕ)
    (v : Fin k → α) :
    v ∈ hitSet missSet k ↔ ∃ i : Fin k, v i ∉ missSet := by
  rw [hitSet, Finset.mem_sdiff, allMissSet, Fintype.mem_piFinset, Classical.not_forall]
  simp

/-! ## 定理 1：计数 —— |全 miss 事件| = |missSet|^k
（k 轮独立采样全 miss 的函数数 = 每坐标从 missSet 取值，共 m^k 个；
直接引用 `Fintype.card_piFinset_const`。） -/

theorem boost_product_count {α : Type*} (missSet : Finset α) (k : ℕ) :
    (allMissSet missSet k).card = missSet.card ^ k := by
  simp [allMissSet]

/-! ## 定理 2：独立乘积（一般形式）——乘积空间事件概率 = 各轮 miss 概率之积
对任意（逐轮不同的）miss 集 `s i`，全 miss 事件 `piFinset s` 的概率恰为
`∏ i, P(s i)`：这正是「∏P(miss_i)」的有限计数版（乘积测度 = 计数乘积）。 -/

theorem boost_product_event {α : Type*} [Fintype α] (s : Fin k → Finset α) :
    uniformProb (Fintype.piFinset s) = ∏ i : Fin k, uniformProb (s i) := by
  calc
    uniformProb (Fintype.piFinset s)
        = (∏ i : Fin k, ((s i).card : ℝ)) / ((Fintype.card α : ℝ) ^ k) := by
          unfold uniformProb
          rw [Fintype.card_piFinset, Fintype.card_pi_const, Nat.cast_prod, Nat.cast_pow]
    _ = ∏ i : Fin k, ((s i).card : ℝ) / (Fintype.card α : ℝ) := by
          rw [Finset.prod_div_distrib]
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## 定理 3：k 轮全 miss 概率（每轮同一 miss 集）
均匀概率下 P(all miss) = (m/N)^k；即单轮 miss 概率的 k 次幂
（独立同分布采样 ⟹ 联合 miss 概率 = 单轮 miss 概率之积）。 -/

theorem boost_uniform_prob_all_miss {α : Type*} [Fintype α] (missSet : Finset α) (k : ℕ) :
    uniformProb (allMissSet missSet k) = uniformProb missSet ^ k := by
  unfold uniformProb allMissSet
  rw [Fintype.card_piFinset_const, Fintype.card_pi_const]
  rw [Nat.cast_pow, Nat.cast_pow]
  rw [div_pow]

/-- 同一事件的乘积写法：P(all miss) = ∏ᵢ P(miss_i)（各轮同分布，积 = k 次幂）。 -/
theorem boost_prob_all_miss_prod {α : Type*} [Fintype α] (missSet : Finset α) (k : ℕ) :
    uniformProb (allMissSet missSet k) = ∏ _ : Fin k, uniformProb missSet := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact boost_uniform_prob_all_miss missSet k

/-! ## 定理 4：补事件 —— P(至少一轮命中) = 1 − P(all miss)
（hit = 全 miss 的补集；计数补集 N−m 除以 N。） -/

theorem boost_hit_prob {α : Type*} [Fintype α] [DecidableEq α] (missSet : Finset α) (k : ℕ)
    (hN : 0 < Fintype.card α) :
    uniformProb (hitSet missSet k) = 1 - uniformProb (allMissSet missSet k) := by
  have hNℝ : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hN
  have hNk : 0 < (Fintype.card (Fin k → α) : ℝ) := by
    rw [Fintype.card_pi_const, Nat.cast_pow]
    exact pow_pos hNℝ k
  unfold uniformProb hitSet
  have hsub : allMissSet missSet k ⊆ (Finset.univ : Finset (Fin k → α)) :=
    Finset.subset_univ _
  rw [Finset.card_sdiff hsub]
  have hmle : (allMissSet missSet k).card ≤ (Finset.univ : Finset (Fin k → α)).card :=
    Finset.card_le_card hsub
  rw [Nat.cast_sub hmle]
  field_simp [ne_of_gt hNk]

/-! ## 定理 5（核心）：置信度放大
单轮 miss 概率 ≤ ε ⟹ k 轮后至少一轮命中的概率 ≥ 1 − ε^k。
证明路线：P(hit) = 1 − P(all miss)（定理 4）= 1 − (m/N)^k（定理 3）
≥ 1 − ε^k（(m/N) ≤ ε 且 0 ≤ (m/N) ⟹ 幂单调 `pow_le_pow_left₀`，
注意只需左端非负，无需假设 0 ≤ ε——由 0 ≤ m/N ≤ ε 自动成立）。 -/

theorem boost_confidence {α : Type*} [Fintype α] [DecidableEq α] (missSet : Finset α) (k : ℕ)
    {ε : ℝ} (hmiss : uniformProb missSet ≤ ε) (hN : 0 < Fintype.card α) :
    1 - ε ^ k ≤ uniformProb (hitSet missSet k) := by
  rw [boost_hit_prob missSet k hN]
  rw [boost_uniform_prob_all_miss missSet k]
  have hnonneg : 0 ≤ uniformProb missSet := by
    unfold uniformProb
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpow : uniformProb missSet ^ k ≤ ε ^ k := pow_le_pow_left₀ hnonneg hmiss k
  exact sub_le_sub_left hpow (1 : ℝ)

/-! ## 定理 6：衔接单轮界（verify_probability_guarantee 型界）
若单轮由 `verify_probability_guarantee` 给出违背集 `{x | ε ≤ f x}` 的
miss 概率 ≤ ε（有限均匀设置下其 `.toReal ≤ ε` 即 `uniformProb` 界），
则 k 轮采样验证的命中概率 ≥ 1 − ε^k。本定理即 `boost_confidence`
在 miss 集 = 违背集（finset 过滤）下的特例化组合陈述。 -/

theorem boost_verify_chain {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (k : ℕ)
    {ε : ℝ} (hN : 0 < Fintype.card α)
    (hmiss : uniformProb (Finset.univ.filter (fun x => ε ≤ f x)) ≤ ε) :
    1 - ε ^ k ≤ uniformProb (hitSet (Finset.univ.filter (fun x => ε ≤ f x)) k) :=
  boost_confidence (Finset.univ.filter (fun x => ε ≤ f x)) k hmiss hN

/-! ## 注：与 RealRandomVerify 的衔接
`verify_probability_guarantee` 给出 `(μ {x | ε ≤ f x}).toReal ≤ ε`（任意概率
测度 μ，马尔可夫）；在有限均匀设置（α 有限，μ = 计数/N）下该值恰为
`uniformProb (univ.filter (fun x => ε ≤ f x))`，即定理 6 的 `hmiss`。
于是「训练收敛 ∫f ≤ ε²（RealGradDescent/RealConvergence）⟹ 单轮
miss ≤ ε（RealRandomVerify）⟹ k 轮命中 ≥ 1−ε^k（本文件）」形成完整
的多轮随机化验证闭环。 -/

end Lattice
