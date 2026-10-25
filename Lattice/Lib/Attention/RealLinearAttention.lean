import Mathlib
import Lattice.Lib.Attention.RealAttention
/-!
# LATTICE: 线性注意力（核化）—— 归一化概率分布、凸组合界与结合律重排

标准注意力显式计算 `n × n` 的分数矩阵（`softmax` 行归一化），是 `O(n²)`；**线性
注意力**用特征映射 `φ` 把打分写成核内积

  `featScore φ q k = ∑_i φ(q_i)·φ(k_i)`     （φ ≥ 0 时核非负）

于是行权重 `w_j = φ(q)·φ(k_j) / ∑_l φ(q)·φ(k_l)`，输出 `Σ_j w_j • V_j`。

本文件给出（全部无 sorry / axiom / admit）：

  1. `featScore` / `linAttnDenom` / `linAttnWeights` / `linearAttentionOutput`：
     核化注意力的定义（`φ` 抽象为任意 `ℝ → ℝ`，实践中取 `elu+1`、`relu` 等非负映射）；
  2. `featScore_nonneg`、`linAttnDenom_nonneg`：核非负（唯一假设 `∀x, 0 ≤ φ x`）；
  3. `linAttnDenom_pos`：**分母为正**（某一行核分数为正 ⟹ 分母正）；
  4. `linear_attn_weights_nonneg`、`linear_attn_weights_sum_one`、`linear_attn_weights_pmf`：
     归一化后权重是**概率分布**（行随机）；
  5. `linear_attn_output_bound`：**凸组合界** `‖输出‖ ≤ max‖V_j‖`
     （直接复用 `RealAttention.convComb_norm_bound`——线性注意力与标准注意力共享
     同一个「输出被 value 最大范数界住」的稳定性结论）；
  6. `linear_attn_is_softmax`（核心关系）：`w = softmax (fun j => log (featScore j))`
     ——**归一化后的**线性注意力恰好是「以核分数的对数为 logits」的 softmax 注意力。
     这是「线性注意力 = 标准注意力」的**精确**关系式（有限分布上的代数等式）；
  7. `softmax_vs_linear`（核心关系）：φ = exp 且特征维 `d = 1` 时，
     `featScore exp q (K j) = exp(q_0 + K_{j,0})`，于是线性注意力权重**逐点等于**
     `softmax (fun j => q_0 + K_{j,0})`——标准 softmax 注意力是线性注意力的特例；
  8. `linear_attn_associativity`（核心）：**结合律重排**——分子
     `Σ_j (φ(q)·φ(k_j)) • V_j = Σ_i φ(q_i) • (Σ_j φ(k_j)_i • V_j)`，
     即「先算 `Σ_j φ(k_j) ⊗ V_j`（`d × d` 状态，与 query 无关），再对每个 query 做
     一次 `d` 维内积」——这是线性注意力 `O(n)` 预计算的核心代数依据（纯 Finset 重排）；
  9. `linear_attn_state_form`：把 8 写成「状态复用」形式
     `linearAttentionNum = Σ_i φ(q_i) • linAttnState_i`（同一状态对所有 query 复用）；
  10. `linearAttentionOutput_eq_inv_smul_num`：输出 = `(分母)⁻¹ • 分子`（归一化恒等式）；
  11. `linear_attn_complexity` 组：`linearAttentionOps n d = n·d ≤ n·n = denseAttentionOps n`
      （`d ≤ n` 时）与严格版本——**组合计数陈述**（标量乘法次数），`O(n)` vs `O(n²)`。

**诚实假设与降级**（均显式标注）：
  · `hφ : ∀ x, 0 ≤ φ x`：特征映射非负（`elu+1`、`relu`、`exp` 都满足；这是核非负的
    充要条件，去掉它 `featScore` 可能为负、权重非负性不成立）；
  · 权重行随机需要**分母为正**（`∃ j, 0 < featScore φ q (K j)`，即至少一个位置核
    分数为正）；分母为 0 时权重恒 0（Lean 中 `x / 0 = 0`），行随机不成立（数学事实，
    非证明困难）；
  · 关系 6 要求**所有**核分数为正（取对数）；
  · 关系 7 只在 `d = 1` 时是**精确等式**：`φ = exp` 时 `featScore` 是「逐维指数之
    和」，而标准 softmax 的 logits 是「内积」；一般 `d` 时二者不同（`Σ_i e^{a_i}` 与
    `e^{Σ_i a_i}`），本文件不声称一般 `d` 的等价，只给 `d = 1` 的精确版本；
  · 复杂度陈述是**标量乘法计数**（组合计数），不是运行时/常数因子定理：核化形式
    每次调用仍要 `O(n·d)` 做状态更新，省下的是 `n × n` 分数矩阵的物化。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 核分数与线性注意力定义 -/

/-- 特征映射 `φ` 下的核分数：`φ(q)·φ(k) = Σ_i φ(q_i)·φ(k_i)`。
这是线性注意力的「打分」，把 query/key 的交互写成逐维特征内积（可分核）。 -/
def featScore {d : ℕ} (φ : ℝ → ℝ) (q k : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, φ (q i) * φ (k i)

/-- 线性注意力的分母：`Σ_j featScore φ q (K j)`（与标准 softmax 的分母同构）。 -/
def linAttnDenom {d : ℕ} (φ : ℝ → ℝ) (q : Fin d → ℝ) (K : ι → Fin d → ℝ) : ℝ :=
  ∑ j : ι, featScore φ q (K j)

/-- 线性注意力权重：`w_j = featScore φ q (K j) / Σ_l featScore φ q (K l)`。
归一化后是 query 行的概率分布（见 `linear_attn_weights_pmf`）。 -/
def linAttnWeights {d : ℕ} (φ : ℝ → ℝ) (q : Fin d → ℝ) (K : ι → Fin d → ℝ) : ι → ℝ :=
  fun j => featScore φ q (K j) / linAttnDenom φ q K

/-- 线性注意力输出（归一化版）：`Σ_j w_j • V_j`。 -/
def linearAttentionOutput {d : ℕ} (φ : ℝ → ℝ) (q : Fin d → ℝ) (K : ι → Fin d → ℝ)
    (V : ι → F) : F :=
  ∑ j : ι, linAttnWeights φ q K j • V j

/-- 线性注意力分子（**未归一化**）：`Σ_j featScore φ q (K j) • V_j`。
结合律重排（`linear_attn_associativity`）作用在这个量上。 -/
def linearAttentionNum {d : ℕ} (φ : ℝ → ℝ) (q : Fin d → ℝ) (K : ι → Fin d → ℝ)
    (V : ι → F) : F :=
  ∑ j : ι, featScore φ q (K j) • V j

/-- 线性注意力的**状态**：`Σ_j φ(k_j)_i • V_j`（第 `i` 个特征维的聚合）。
与 query 无关，可对所有 query 复用——`O(n·d)` 预计算的载体。 -/
def linAttnState {d : ℕ} (φ : ℝ → ℝ) (K : ι → Fin d → ℝ) (V : ι → F) (i : Fin d) : F :=
  ∑ j : ι, φ (K j i) • V j

/-! ## 引理：核分数非负、分母非负/为正 -/

/-- `featScore` 非负（`φ ≥ 0`）。 -/
lemma featScore_nonneg {d : ℕ} (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (q k : Fin d → ℝ) :
    0 ≤ featScore φ q k := by
  unfold featScore
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hφ _) (hφ _)

omit [Nonempty ι] in
/-- 分母非负（`φ ≥ 0`）。 -/
lemma linAttnDenom_nonneg {d : ℕ} (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (q : Fin d → ℝ) (K : ι → Fin d → ℝ) : 0 ≤ linAttnDenom φ q K := by
  unfold linAttnDenom
  exact Finset.sum_nonneg fun j _ => featScore_nonneg φ hφ q (K j)

omit [Nonempty ι] in
/-- 分母为正：只要存在某个位置核分数为正（`φ ≥ 0` 下即该位置有非零特征）。 -/
lemma linAttnDenom_pos {d : ℕ} (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (q : Fin d → ℝ) (K : ι → Fin d → ℝ) (hne : ∃ j, 0 < featScore φ q (K j)) :
    0 < linAttnDenom φ q K := by
  obtain ⟨j, hj⟩ := hne
  unfold linAttnDenom
  exact Finset.sum_pos'
    (fun l _ => featScore_nonneg φ hφ q (K l))
    ⟨j, Finset.mem_univ j, hj⟩

/-! ## 定理一：线性注意力权重非负 -/

omit [Nonempty ι] in
theorem linear_attn_weights_nonneg {d : ℕ} (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (q : Fin d → ℝ) (K : ι → Fin d → ℝ) (j : ι) : 0 ≤ linAttnWeights φ q K j := by
  unfold linAttnWeights
  exact div_nonneg (featScore_nonneg φ hφ q (K j)) (linAttnDenom_nonneg φ hφ q K)

/-! ## 定理二：线性注意力权重行随机（归一化后是概率分布） -/

omit [Nonempty ι] in
theorem linear_attn_weights_sum_one {d : ℕ} (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (q : Fin d → ℝ) (K : ι → Fin d → ℝ) (hne : ∃ j, 0 < featScore φ q (K j)) :
    ∑ j, linAttnWeights φ q K j = 1 := by
  have hD : linAttnDenom φ q K ≠ 0 := ne_of_gt (linAttnDenom_pos φ hφ q K hne)
  unfold linAttnWeights
  rw [← Finset.sum_div]
  exact div_self hD

/-- 归一化后线性注意力权重构成概率分布（非负 + 和为 1）。 -/
theorem linear_attn_weights_pmf {d : ℕ} (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (q : Fin d → ℝ) (K : ι → Fin d → ℝ) (hne : ∃ j, 0 < featScore φ q (K j)) :
    (∀ j, 0 ≤ linAttnWeights φ q K j) ∧ (∑ j, linAttnWeights φ q K j = 1) :=
  ⟨fun j => linear_attn_weights_nonneg φ hφ q K j,
   linear_attn_weights_sum_one φ hφ q K hne⟩

/-! ## 定理三（核心）：线性注意力的输出界（凸组合界）
行随机 + 复用 `RealAttention.convComb_norm_bound`：输出被 `max‖V_j‖` 界住——
与标准 softmax 注意力共享同一稳定性结论。 -/

theorem linear_attn_output_bound {d : ℕ} (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (q : Fin d → ℝ) (K : ι → Fin d → ℝ) (hne : ∃ j, 0 < featScore φ q (K j))
    (V : ι → F) (M : ℝ) (hV : ∀ j, ‖V j‖ ≤ M) :
    ‖linearAttentionOutput φ q K V‖ ≤ M :=
  convComb_norm_bound (linAttnWeights φ q K) V M
    (linear_attn_weights_nonneg φ hφ q K)
    (linear_attn_weights_sum_one φ hφ q K hne) hV

/-! ## 定理四（核心关系）：归一化线性注意力 = 核分数对数的 softmax
`w = softmax (fun j => log (featScore j))`——精确的有限分布等式。 -/

omit [Nonempty ι] in
theorem linear_attn_is_softmax {d : ℕ} (φ : ℝ → ℝ) (q : Fin d → ℝ) (K : ι → Fin d → ℝ)
    (hpos : ∀ j, 0 < featScore φ q (K j)) :
    linAttnWeights φ q K = softmax (fun j => Real.log (featScore φ q (K j))) := by
  funext j
  unfold linAttnWeights linAttnDenom softmax
  rw [Real.exp_log (hpos j)]
  congr 1
  exact Finset.sum_congr rfl fun l _ => (Real.exp_log (hpos l)).symm

/-! ## 定理五（核心关系）：φ = exp、d = 1 时线性注意力 = 标准 softmax
`featScore exp q (K j) = exp(q_0 + K_{j,0})` ⟹ 权重逐点等于 `softmax (q_0 + K_{·,0})`。 -/

omit [Nonempty ι] in
theorem softmax_vs_linear (q : Fin 1 → ℝ) (K : ι → Fin 1 → ℝ) :
    linAttnWeights Real.exp q K = softmax (fun j => q 0 + K j 0) := by
  have hterm : ∀ (k : Fin 1 → ℝ),
      (∑ i : Fin 1, Real.exp (q i) * Real.exp (k i)) = Real.exp (q 0 + k 0) := by
    intro k
    rw [Fin.sum_univ_one, ← Real.exp_add]
  funext j
  unfold linAttnWeights linAttnDenom featScore softmax
  rw [hterm (K j)]
  congr 1
  exact Finset.sum_congr rfl fun l _ => hterm (K l)

/-! ## 定理六（核心）：线性注意力的结合律重排（`O(n)·d` 状态的代数依据）
`Σ_j (Σ_i φ(q_i)φ(k_{j,i})) • V_j = Σ_i φ(q_i) • (Σ_j φ(k_{j,i}) • V_j)`。
右式即「先算状态 `Σ_j φ(k_j) ⊗ V_j`（与 query 无关），再对每个 query 做 `d` 维
内积」——线性注意力线性化的纯粹 Finset 重排（求和交换 + `smul` 结合）。 -/

omit [Nonempty ι] in
theorem linear_attn_associativity {d : ℕ} (φ : ℝ → ℝ) (q : Fin d → ℝ)
    (K : ι → Fin d → ℝ) (V : ι → F) :
    linearAttentionNum φ q K V = ∑ i : Fin d, φ (q i) • linAttnState φ K V i := by
  unfold linearAttentionNum linAttnState featScore
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _

omit [Nonempty ι] in
/-- 状态复用形式（定理六的改写）：输出分子 = `Σ_i φ(q_i) • state_i`。 -/
theorem linear_attn_state_form {d : ℕ} (φ : ℝ → ℝ) (q : Fin d → ℝ)
    (K : ι → Fin d → ℝ) (V : ι → F) :
    linearAttentionNum φ q K V = ∑ i : Fin d, φ (q i) • linAttnState φ K V i :=
  linear_attn_associativity φ q K V

/-! ## 定理七：归一化恒等式（输出 = 分母⁻¹ • 分子） -/

omit [Nonempty ι] in
theorem linearAttentionOutput_eq_inv_smul_num {d : ℕ} (φ : ℝ → ℝ) (q : Fin d → ℝ)
    (K : ι → Fin d → ℝ) (V : ι → F) :
    linearAttentionOutput φ q K V = (linAttnDenom φ q K)⁻¹ • linearAttentionNum φ q K V := by
  unfold linearAttentionOutput linearAttentionNum linAttnWeights
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [div_eq_inv_mul, mul_smul]

/-! ## 定理八：复杂度（组合计数）—— `n·d ≤ n·n`
`denseAttentionOps n = n²`：显式分数矩阵的标量乘法次数；
`linearAttentionOps n d = n·d`：核化形式（每个 token 一次 `d` 维特征内积）。
特征维不超过序列长度时核化形式不多于显式形式。 -/

/-- 显式注意力分数矩阵的规模（`n²` 次标量乘法）。 -/
def denseAttentionOps (n : ℕ) : ℕ := n * n

/-- 线性注意力核化形式的规模（`n·d` 次标量乘法）。 -/
def linearAttentionOps (n d : ℕ) : ℕ := n * d

/-- `d ≤ n` 时核化形式的计数量不超过显式形式。 -/
theorem linear_attn_complexity {n d : ℕ} (h : d ≤ n) :
    linearAttentionOps n d ≤ denseAttentionOps n := by
  unfold linearAttentionOps denseAttentionOps
  exact Nat.mul_le_mul_left n h

/-- 严格版本：`d < n` 且 `n > 0` 时严格更少（真正的 `O(n)` vs `O(n²)` 节省）。 -/
theorem linear_attn_complexity_strict {n d : ℕ} (hn : 0 < n) (h : d < n) :
    linearAttentionOps n d < denseAttentionOps n := by
  unfold linearAttentionOps denseAttentionOps
  exact Nat.mul_lt_mul_of_pos_left h hn

end Lattice
