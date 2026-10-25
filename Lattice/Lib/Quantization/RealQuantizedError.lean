import Mathlib
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Architectures.RealOperatorNorm
/-!
# LATTICE: 量化部署误差传播 —— 权重量化误差的 n 层线性链端到端累积

把 RealApprox 的「标量线性层权重扰动误差界」（`layer_out_error_bound`：
权重扰动 ε₁、输入界 X ⟹ 输出误差 ≤ ε₁X+ε₂）推广为**算子级**的
n 层线性链端到端误差界，并接入 RealChain 的 n 层链骨架（`ChainFwd`）：

  1. `quant_layer_pointwise`：单层量化误差界 ‖Wq−W‖_op ≤ δ ⟹ 逐点界
     ‖Wq y − W y‖ ≤ δ·‖y‖（`layer_out_error_bound` 的算子版：ε₁=δ、X=‖y‖）；
  2. `quantized_two_layer_error`：两层精确展开（中间插值点 Wq₂(W₁x)）：
     ‖Wq₂(Wq₁x) − W₂(W₁x)‖ ≤ ‖Wq₂‖·δ₁·‖x‖ + δ₂·‖W₁‖·‖x‖；
     `quantized_two_layer_error_add`：再以 ‖Wq₂‖ ≤ ‖W₂‖+δ₂ 收紧为
     (‖W₂‖+δ₂)·δ₁·‖x‖ + δ₂·‖W₁‖·‖x‖（`add_norm_bound` 的实例化）；
  3. `quantized_chain_error`：n 层归纳端到端误差（递归界 `quantErrBound`），
     `quantized_chain_error_closed`：闭式求和
     ‖Fq x − F x‖ ≤ Σ_{i<n} (∏_{j∈Ioo i n} ‖Wq_j‖)·δ_i·(∏_{k<i} ‖W_k‖)·‖x‖
     —— 第 i 层量化误差 δ_i 经其后各层（‖Wq_j‖）放大、其前各层（‖W_k‖）
     放缩输入；归纳结构参照 `chainN_error_bound` 的 induction n 模式；
  4. `quantized_chain_error_lipschitz`（更通用版）：非线性 Lipschitz 层
     F_i（常数 Ls i，原层与量化层同为 Ls i-Lipschitz）、量化算子近似界
     ‖Fq_i(y) − F_i(y)‖ ≤ ε_i（输入无关）⟹ 端到端
     ≤ Σ_{i<n} (∏_{j∈Ioo i n} Ls_j)·ε_i。

实用场景：权重量化（INT8/FP16 等）的前向传播误差保证——每层量化误差
界 δ_i 已知（rounding 界），上式给出量化模型输出与浮点模型输出的范数
界，供验证器容差判定（RealApprox/RealVerifierReliable 的容差线）。

诚实假设（全部显式标注）：量化误差界 δ_i ≥ 0 与层 Lipschitz 常数
Ls i ≥ 0（δ_i ≥ 0 由 ‖Wq−W‖ ≥ 0 与假设 ‖Wq−W‖ ≤ δ 自动推出）；其余为
范数公理（算子范数非负、`le_opNorm`、三角不等式）。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 量化前向链（线性层，层 0..n-1 依次作用） -/

/-- 量化前向链：`quantFwd W n x` = W_{n-1}∘⋯∘W₀ 作用于 x（与
`RealChain.ChainFwd` 一致，层为连续线性映射的版本）。 -/
def quantFwd (W : ℕ → E →L[ℝ] E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => W n (quantFwd W n x)

/-- 与 RealChain 的 n 层链骨架一致：`quantFwd W n x = ChainFwd (fun i => W i) n x`。 -/
lemma quantFwd_eq_ChainFwd (W : ℕ → E →L[ℝ] E) :
    ∀ n x, quantFwd W n x = ChainFwd (fun i => (W i).toFun) n x := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      simp [quantFwd, ChainFwd, ih]

/-! ## 单层量化误差：算子界 → 逐点界 -/

/-- 量化误差界非负：‖Wq−W‖ ≤ δ 且范数非负 ⟹ 0 ≤ δ。 -/
lemma quant_delta_nonneg (W Wq : E →L[ℝ] E) (δ : ℝ) (hq : ‖Wq - W‖ ≤ δ) : 0 ≤ δ :=
  le_trans (norm_nonneg (Wq - W)) hq

/-- 单层量化逐点界：‖Wq y − W y‖ ≤ δ·‖y‖（`layer_out_error_bound` 的
算子版：权重扰动 δ、输入范数界 ‖y‖）。 -/
lemma quant_layer_pointwise (W Wq : E →L[ℝ] E) (δ : ℝ) (hq : ‖Wq - W‖ ≤ δ) (y : E) :
    ‖Wq y - W y‖ ≤ δ * ‖y‖ := by
  calc
    ‖Wq y - W y‖ ≤ ‖Wq - W‖ * ‖y‖ := by
      simpa using (Wq - W).le_opNorm y
    _ ≤ δ * ‖y‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg y)

/-! ## 线性链输出范数界 -/

/-- 线性链输出范数界：‖quantFwd W n x‖ ≤ (∏_{k<n} ‖W k‖)·‖x‖
（每层 ‖W_k‖ 放大输入，∏ 连乘）。 -/
lemma quantFwd_norm_bound (W : ℕ → E →L[ℝ] E) :
    ∀ n x, ‖quantFwd W n x‖ ≤ (∏ k in Finset.range n, ‖W k‖) * ‖x‖ := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [quantFwd]
  | succ n ih =>
      intro x
      calc
        ‖quantFwd W (n + 1) x‖ = ‖W n (quantFwd W n x)‖ := by simp [quantFwd]
        _ ≤ ‖W n‖ * ‖quantFwd W n x‖ := by
          exact (W n).le_opNorm (quantFwd W n x)
        _ ≤ ‖W n‖ * ((∏ k in Finset.range n, ‖W k‖) * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left (ih x) (norm_nonneg (W n))
        _ = (∏ k in Finset.range (n + 1), ‖W k‖) * ‖x‖ := by
          rw [Finset.prod_range_succ]
          ring

/-! ## 递归误差界（归纳友好的定义） -/

/-- 递归误差界：B(0)=0，B(n+1)=‖Wq n‖·B(n) + δ n·(∏_{k<n}‖W k‖)·‖x‖。
归纳时直接匹配此递归，闭式求和形式见 `quantErrBound_closed`。 -/
def quantErrBound (W Wq : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (x : E) : ℕ → ℝ
  | 0 => 0
  | n + 1 => ‖Wq n‖ * quantErrBound W Wq δ x n + δ n * (∏ k in Finset.range n, ‖W k‖) * ‖x‖

/-! ## 定理：n 层端到端量化误差（归纳，递归界） -/

/-- 定理二（n 层端到端，递归界）：每层量化误差 ‖Wq i − W i‖ ≤ δ i
⟹ ‖quantFwd Wq n x − quantFwd W n x‖ ≤ quantErrBound W Wq δ x n。
第 n 层误差 = 前 n 层误差经 Wq n 放大（‖Wq n‖·B(n)）+ 第 n 层量化误差
在本层输入点的贡献（δ n·‖quantFwd W n x‖ ≤ δ n·(∏_{k<n}‖W k‖)·‖x‖）。 -/
theorem quantized_chain_error (W Wq : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (n : ℕ)
    (hq : ∀ i, i < n → ‖Wq i - W i‖ ≤ δ i) :
    ∀ x, ‖quantFwd Wq n x - quantFwd W n x‖ ≤ quantErrBound W Wq δ x n := by
  induction n with
  | zero =>
      intro x
      simp [quantFwd, quantErrBound]
  | succ n ih =>
      -- 归纳假设：限制到前 n 层（hq 对 i < n 成立）
      have hih : ∀ x, ‖quantFwd Wq n x - quantFwd W n x‖ ≤ quantErrBound W Wq δ x n :=
        ih (fun i hi => hq i (by omega))
      intro x
      -- 第 n 层量化逐点界 + 输出范数界
      have hδn : 0 ≤ δ n := quant_delta_nonneg (W n) (Wq n) (δ n) (hq n (by omega))
      have hpoint : ‖Wq n (quantFwd W n x) - W n (quantFwd W n x)‖ ≤ δ n * ‖quantFwd W n x‖ :=
        quant_layer_pointwise (W n) (Wq n) (δ n) (hq n (by omega)) (quantFwd W n x)
      have hnorm : ‖quantFwd W n x‖ ≤ (∏ k in Finset.range n, ‖W k‖) * ‖x‖ :=
        quantFwd_norm_bound W n x
      calc
        ‖quantFwd Wq (n + 1) x - quantFwd W (n + 1) x‖
            = ‖Wq n (quantFwd Wq n x) - W n (quantFwd W n x)‖ := by
              simp [quantFwd]
        _ = ‖(Wq n (quantFwd Wq n x) - Wq n (quantFwd W n x))
              + (Wq n (quantFwd W n x) - W n (quantFwd W n x))‖ := by
              congr 1
              abel
        _ ≤ ‖Wq n (quantFwd Wq n x) - Wq n (quantFwd W n x)‖
            + ‖Wq n (quantFwd W n x) - W n (quantFwd W n x)‖ := by
              exact norm_add_le _ _
        _ ≤ ‖Wq n‖ * ‖quantFwd Wq n x - quantFwd W n x‖ + δ n * ‖quantFwd W n x‖ := by
              exact add_le_add
                (linear_map_lipschitz (Wq n) (quantFwd Wq n x) (quantFwd W n x)) hpoint
        _ ≤ ‖Wq n‖ * quantErrBound W Wq δ x n
            + δ n * ((∏ k in Finset.range n, ‖W k‖) * ‖x‖) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hih x) (norm_nonneg (Wq n)))
                (mul_le_mul_of_nonneg_left hnorm hδn)
        _ = quantErrBound W Wq δ x (n + 1) := by
              simp [quantErrBound]
              ring

/-! ## Finset 工具：Ioo 的 succ 分解（闭式求和的归纳步） -/

/-- `Ioo i (n+1) = insert n (Ioo i n)`（i < n）：在 ℕ 上逐点验证。 -/
lemma Ioo_succ_insert {i n : ℕ} (hin : i < n) : Finset.Ioo i (n + 1) = insert n (Finset.Ioo i n) := by
  ext j
  rw [Finset.mem_Ioo, Finset.mem_insert, Finset.mem_Ioo]
  by_cases hjn : j = n
  · subst j
    simp [hin]
  · constructor
    · intro hj
      exact Or.inr ⟨hj.1, by omega⟩
    · intro hj
      rcases hj with rfl | hji
      · exact ⟨hin, by omega⟩
      · exact ⟨hji.1, by omega⟩

/-- `Ioo n (n+1) = ∅`：n 与 n+1 之间无自然数。 -/
lemma Ioo_self_succ (n : ℕ) : Finset.Ioo n (n + 1) = (∅ : Finset ℕ) := by
  ext j
  constructor
  · intro hj
    simp [Finset.mem_Ioo] at hj
    omega
  · intro hj
    simp at hj

/-! ## 闭式求和界 -/

/-- 递归界等于闭式求和（纯 Finset/ring 等式，归纳）：
quantErrBound W Wq δ x n = Σ_{i<n} (∏_{j∈Ioo i n} ‖Wq j‖)·δ i·(∏_{k<i}‖W k‖)·‖x‖。 -/
lemma quantErrBound_closed (W Wq : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) :
    ∀ n x, quantErrBound W Wq δ x n
      = ∑ i in Finset.range n, (∏ j in Finset.Ioo i n, ‖Wq j‖) * δ i * (∏ k in Finset.range i, ‖W k‖) * ‖x‖ := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [quantErrBound]
  | succ n ih =>
      intro x
      change ‖Wq n‖ * quantErrBound W Wq δ x n + δ n * (∏ k in Finset.range n, ‖W k‖) * ‖x‖
          = ∑ i in Finset.range (n + 1), (∏ j in Finset.Ioo i (n + 1), ‖Wq j‖) * δ i * (∏ k in Finset.range i, ‖W k‖) * ‖x‖
      rw [ih]
      rw [Finset.sum_range_succ]
      rw [Finset.mul_sum]
      -- 逐项：‖Wq n‖ 乘入求和并吸收到 ∏_{j∈Ioo i (n+1)}
      have hterm : ∀ i, i < n →
          ‖Wq n‖ * ((∏ j in Finset.Ioo i n, ‖Wq j‖) * δ i * (∏ k in Finset.range i, ‖W k‖) * ‖x‖)
            = (∏ j in Finset.Ioo i (n + 1), ‖Wq j‖) * δ i * (∏ k in Finset.range i, ‖W k‖) * ‖x‖ := by
        intro i hin
        have hset : Finset.Ioo i (n + 1) = insert n (Finset.Ioo i n) := Ioo_succ_insert hin
        rw [hset, Finset.prod_insert]
        · ring
        · simp [Finset.mem_Ioo]
      have hsum : (∑ i in Finset.range n,
            ‖Wq n‖ * ((∏ j in Finset.Ioo i n, ‖Wq j‖) * δ i * (∏ k in Finset.range i, ‖W k‖) * ‖x‖))
          = ∑ i in Finset.range n,
            ((∏ j in Finset.Ioo i (n + 1), ‖Wq j‖) * δ i * (∏ k in Finset.range i, ‖W k‖) * ‖x‖) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i (Finset.mem_range.mp hi)
      -- 末项：i = n 时 ∏_{j∈Ioo n (n+1)} = 1
      have hlast : δ n * (∏ k in Finset.range n, ‖W k‖) * ‖x‖
          = (∏ j in Finset.Ioo n (n + 1), ‖Wq j‖) * δ n * (∏ k in Finset.range n, ‖W k‖) * ‖x‖ := by
        have hset : Finset.Ioo n (n + 1) = (∅ : Finset ℕ) := Ioo_self_succ n
        simp [hset]
      rw [hsum, hlast]

/-- 定理二（n 层端到端，闭式求和）：每层量化误差 ‖Wq i − W i‖ ≤ δ i
⟹ ‖quantFwd Wq n x − quantFwd W n x‖
≤ Σ_{i<n} (∏_{j∈Ioo i n} ‖Wq j‖)·δ i·(∏_{k<i} ‖W k‖)·‖x‖。
第 i 层量化误差 δ_i 经其后各层（‖Wq_j‖）放大、其前各层（‖W_k‖）放缩输入。 -/
theorem quantized_chain_error_closed (W Wq : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (n : ℕ)
    (hq : ∀ i, i < n → ‖Wq i - W i‖ ≤ δ i) :
    ∀ x, ‖quantFwd Wq n x - quantFwd W n x‖
      ≤ ∑ i in Finset.range n, (∏ j in Finset.Ioo i n, ‖Wq j‖) * δ i * (∏ k in Finset.range i, ‖W k‖) * ‖x‖ := by
  intro x
  exact le_trans (quantized_chain_error W Wq δ n hq x)
    (le_of_eq (quantErrBound_closed W Wq δ n x))

/-! ## 定理一：两层精确展开 -/

/-- 定理一（两层精确展开）：‖Wq₂(Wq₁x) − W₂(W₁x)‖
≤ ‖Wq₂‖·δ₁·‖x‖ + δ₂·‖W₁‖·‖x‖。
中间插值：Wq₂(Wq₁x) − W₂(W₁x) = [Wq₂(Wq₁x) − Wq₂(W₁x)] + [Wq₂(W₁x) − W₂(W₁x)]；
第一项 ≤ ‖Wq₂‖·δ₁‖x‖（Wq₂ Lipschitz + 层一量化误差），第二项 ≤ δ₂·‖W₁ x‖
≤ δ₂·‖W₁‖·‖x‖（层二量化误差在点 W₁x 处 + W₁ 的算子范数界）。 -/
theorem quantized_two_layer_error (W₁ W₂ Wq₁ Wq₂ : E →L[ℝ] E) (δ₁ δ₂ : ℝ)
    (hq₁ : ‖Wq₁ - W₁‖ ≤ δ₁) (hq₂ : ‖Wq₂ - W₂‖ ≤ δ₂) (x : E) :
    ‖Wq₂ (Wq₁ x) - W₂ (W₁ x)‖ ≤ ‖Wq₂‖ * δ₁ * ‖x‖ + δ₂ * ‖W₁‖ * ‖x‖ := by
  calc
    ‖Wq₂ (Wq₁ x) - W₂ (W₁ x)‖
        = ‖(Wq₂ (Wq₁ x) - Wq₂ (W₁ x)) + (Wq₂ (W₁ x) - W₂ (W₁ x))‖ := by
          congr 1
          abel
    _ ≤ ‖Wq₂ (Wq₁ x) - Wq₂ (W₁ x)‖ + ‖Wq₂ (W₁ x) - W₂ (W₁ x)‖ := by
          exact norm_add_le _ _
    _ ≤ ‖Wq₂‖ * ‖Wq₁ x - W₁ x‖ + δ₂ * ‖W₁ x‖ := by
          exact add_le_add (linear_map_lipschitz (Wq₂) (Wq₁ x) (W₁ x))
            (quant_layer_pointwise W₂ Wq₂ δ₂ hq₂ (W₁ x))
    _ ≤ ‖Wq₂‖ * (δ₁ * ‖x‖) + δ₂ * (‖W₁‖ * ‖x‖) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (quant_layer_pointwise W₁ Wq₁ δ₁ hq₁ x) (norm_nonneg (Wq₂)))
            (mul_le_mul_of_nonneg_left ((W₁).le_opNorm x) (quant_delta_nonneg W₂ Wq₂ δ₂ hq₂))
    _ = ‖Wq₂‖ * δ₁ * ‖x‖ + δ₂ * ‖W₁‖ * ‖x‖ := by ring

/-- 定理一'（两层，用 ‖Wq₂‖ ≤ ‖W₂‖+δ₂ 收紧）：
‖Wq₂(Wq₁x) − W₂(W₁x)‖ ≤ (‖W₂‖+δ₂)·δ₁·‖x‖ + δ₂·‖W₁‖·‖x‖
（‖Wq₂‖ ≤ ‖W₂‖+δ₂ 来自 ‖Wq₂‖ = ‖(Wq₂−W₂)+W₂‖ ≤ ‖Wq₂−W₂‖+‖W₂‖，即
`add_norm_bound` 的实例化 + 三角不等式）。 -/
theorem quantized_two_layer_error_add (W₁ W₂ Wq₁ Wq₂ : E →L[ℝ] E) (δ₁ δ₂ : ℝ)
    (hq₁ : ‖Wq₁ - W₁‖ ≤ δ₁) (hq₂ : ‖Wq₂ - W₂‖ ≤ δ₂) (x : E) :
    ‖Wq₂ (Wq₁ x) - W₂ (W₁ x)‖ ≤ (‖W₂‖ + δ₂) * δ₁ * ‖x‖ + δ₂ * ‖W₁‖ * ‖x‖ := by
  have h1 := quantized_two_layer_error W₁ W₂ Wq₁ Wq₂ δ₁ δ₂ hq₁ hq₂ x
  have hnorm : ‖Wq₂‖ ≤ ‖W₂‖ + δ₂ := by
    calc
      ‖Wq₂‖ = ‖(Wq₂ - W₂) + W₂‖ := by
        congr 1
        abel
      _ ≤ ‖Wq₂ - W₂‖ + ‖W₂‖ := norm_add_le _ _
      _ ≤ δ₂ + ‖W₂‖ := add_le_add_right hq₂ ‖W₂‖
      _ = ‖W₂‖ + δ₂ := by ring
  have hnonneg : 0 ≤ δ₁ * ‖x‖ := mul_nonneg (quant_delta_nonneg W₁ Wq₁ δ₁ hq₁) (norm_nonneg x)
  have hmul : ‖Wq₂‖ * (δ₁ * ‖x‖) ≤ (‖W₂‖ + δ₂) * (δ₁ * ‖x‖) :=
    mul_le_mul_of_nonneg_right hnorm hnonneg
  have hmul' : ‖Wq₂‖ * δ₁ * ‖x‖ ≤ (‖W₂‖ + δ₂) * δ₁ * ‖x‖ := by
    calc
      ‖Wq₂‖ * δ₁ * ‖x‖ = ‖Wq₂‖ * (δ₁ * ‖x‖) := by rw [← mul_assoc]
      _ ≤ (‖W₂‖ + δ₂) * (δ₁ * ‖x‖) := hmul
      _ = (‖W₂‖ + δ₂) * δ₁ * ‖x‖ := by rw [mul_assoc]
  calc
    ‖Wq₂ (Wq₁ x) - W₂ (W₁ x)‖ ≤ ‖Wq₂‖ * δ₁ * ‖x‖ + δ₂ * ‖W₁‖ * ‖x‖ := h1
    _ ≤ (‖W₂‖ + δ₂) * δ₁ * ‖x‖ + δ₂ * ‖W₁‖ * ‖x‖ := by
          exact add_le_add_right hmul' (δ₂ * ‖W₁‖ * ‖x‖)

/-! ## 定理四（更通用）：非线性 Lipschitz 层 -/

/-- 闭式求和递归（Lipschitz 版，纯 Finset 等式）：
Σ_{i<n+1} (∏_{j∈Ioo i (n+1)} Ls j)·ε i = Ls n·(Σ_{i<n} (∏_{j∈Ioo i n} Ls j)·ε i) + ε n。 -/
lemma lipschitzSum_succ (Ls ε : ℕ → ℝ) (n : ℕ) :
    (∑ i in Finset.range (n + 1), (∏ j in Finset.Ioo i (n + 1), Ls j) * ε i)
      = Ls n * (∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i) + ε n := by
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hterm : ∀ i, i < n →
      (∏ j in Finset.Ioo i (n + 1), Ls j) * ε i = Ls n * ((∏ j in Finset.Ioo i n, Ls j) * ε i) := by
    intro i hin
    have hset : Finset.Ioo i (n + 1) = insert n (Finset.Ioo i n) := Ioo_succ_insert hin
    rw [hset, Finset.prod_insert]
    · ring
    · simp [Finset.mem_Ioo]
  have hsum : (∑ i in Finset.range n, (∏ j in Finset.Ioo i (n + 1), Ls j) * ε i)
      = ∑ i in Finset.range n, Ls n * ((∏ j in Finset.Ioo i n, Ls j) * ε i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i (Finset.mem_range.mp hi)
  have hlast : (∏ j in Finset.Ioo n (n + 1), Ls j) * ε n = ε n := by
    have hset : Finset.Ioo n (n + 1) = (∅ : Finset ℕ) := Ioo_self_succ n
    simp [hset]
  rw [hsum, hlast]

omit [NormedSpace ℝ E] in
/-- 定理四（非线性 Lipschitz 层，n 层端到端）：原层 F_i 与量化层 Fq_i
均为 Ls i-Lipschitz（hL/hLq），量化算子近似界 ‖Fq_i(y) − F_i(y)‖ ≤ ε_i
（输入无关，hε）⟹ 端到端
‖ChainFwd Fq n x − ChainFwd F n x‖ ≤ Σ_{i<n} (∏_{j∈Ioo i n} Ls j)·ε i。
比线性版更通用：不需要 W 的结构，Lipschitz 常数即放大因子。 -/
theorem quantized_chain_error_lipschitz (F Fq : ℕ → E → E) (Ls ε : ℕ → ℝ) (n : ℕ)
    (hL : ∀ i, i < n → ∀ x y, ‖F i x - F i y‖ ≤ Ls i * ‖x - y‖)
    (hLq : ∀ i, i < n → ∀ x y, ‖Fq i x - Fq i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i)
    (hε : ∀ i, i < n → ∀ y, ‖Fq i y - F i y‖ ≤ ε i) :
    ∀ x, ‖ChainFwd Fq n x - ChainFwd F n x‖
      ≤ ∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i := by
  induction n with
  | zero =>
      intro x
      simp [ChainFwd]
  | succ n ih =>
      -- 归纳假设：内层 n 层链（限制 i < n）
      have hih : ∀ x, ‖ChainFwd Fq n x - ChainFwd F n x‖
          ≤ ∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i :=
        ih (fun i hi => hL i (by omega)) (fun i hi => hLq i (by omega))
          (fun i hi => hL0 i (by omega)) (fun i hi => hε i (by omega))
      intro x
      -- 第 n 层量化层 Lipschitz（放大前 n 层误差）
      have hstep : ‖Fq n (ChainFwd Fq n x) - Fq n (ChainFwd F n x)‖
          ≤ Ls n * ‖ChainFwd Fq n x - ChainFwd F n x‖ :=
        hLq n (by omega) (ChainFwd Fq n x) (ChainFwd F n x)
      calc
        ‖ChainFwd Fq (n + 1) x - ChainFwd F (n + 1) x‖
            = ‖Fq n (ChainFwd Fq n x) - F n (ChainFwd F n x)‖ := by
              simp [ChainFwd]
        _ = ‖(Fq n (ChainFwd Fq n x) - Fq n (ChainFwd F n x))
              + (Fq n (ChainFwd F n x) - F n (ChainFwd F n x))‖ := by
              congr 1
              abel
        _ ≤ ‖Fq n (ChainFwd Fq n x) - Fq n (ChainFwd F n x)‖
            + ‖Fq n (ChainFwd F n x) - F n (ChainFwd F n x)‖ := by
              exact norm_add_le _ _
        _ ≤ Ls n * ‖ChainFwd Fq n x - ChainFwd F n x‖ + ε n := by
              exact add_le_add hstep (hε n (by omega) (ChainFwd F n x))
        _ ≤ Ls n * (∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i) + ε n := by
              exact add_le_add (mul_le_mul_of_nonneg_left (hih x) (hL0 n (by omega))) (le_rfl)
        _ = ∑ i in Finset.range (n + 1), (∏ j in Finset.Ioo i (n + 1), Ls j) * ε i := by
              exact (lipschitzSum_succ Ls ε n).symm

/-! ## 定理三：均匀量化特例（所有层 δ_i = δ、‖Wq_i‖ ≤ L、‖W_i‖ ≤ L） -/

/-- 递归误差界非负：各层误差界 δ i ≥ 0（i < n）⟹ B(n) ≥ 0
（每项 = 非负范数 × 非负误差 × 非负输入界之积）。 -/
lemma quantErrBound_nonneg (W Wq : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (x : E) :
    ∀ n, (∀ i, i < n → 0 ≤ δ i) → 0 ≤ quantErrBound W Wq δ x n := by
  intro n
  induction n with
  | zero =>
      intro h
      simp [quantErrBound]
  | succ n ih =>
      intro h
      have hδn : 0 ≤ δ n := h n (by omega)
      have hB : 0 ≤ quantErrBound W Wq δ x n := ih (fun i hi => h i (by omega))
      have hP : 0 ≤ ∏ k in Finset.range n, ‖W k‖ :=
        Finset.prod_nonneg (fun k hk => norm_nonneg (W k))
      change 0 ≤ ‖Wq n‖ * quantErrBound W Wq δ x n + δ n * (∏ k in Finset.range n, ‖W k‖) * ‖x‖
      nlinarith [mul_nonneg (norm_nonneg (Wq n)) hB,
        mul_nonneg (mul_nonneg hδn hP) (norm_nonneg x)]

/-- 均匀量化（递归界）：所有层误差界 δ i = d（≥ 0）、‖Wq i‖ ≤ L、
‖W i‖ ≤ L（L ≥ 1）⟹ 递归误差界 B(n) ≤ n·d·Lⁿ·‖x‖（归纳）。
L ≥ 1 保证 L^n ≤ L^(n+1)（误差随层数扩张）；L < 1 时量化误差经
收缩层衰减，界不成立（需另一形式，此处诚实标注）。 -/
lemma quantErrBound_uniform (W Wq : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (L d : ℝ)
    (hδ0 : ∀ i, 0 ≤ δ i) (hδ : ∀ i, δ i = d)
    (hWq : ∀ i, ‖Wq i‖ ≤ L) (hW : ∀ i, ‖W i‖ ≤ L) (hL1 : 1 ≤ L) :
    ∀ n x, quantErrBound W Wq δ x n ≤ (n : ℝ) * d * L ^ n * ‖x‖ := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [quantErrBound]
  | succ n ih =>
      intro x
      have hL0 : 0 ≤ L := le_trans zero_le_one hL1
      have hd0 : 0 ≤ d := by
        rw [← hδ 0]
        exact hδ0 0
      -- 归纳步事实
      have hB0 : 0 ≤ quantErrBound W Wq δ x n :=
        quantErrBound_nonneg W Wq δ x n (fun i hi => hδ0 i)
      have hP : (∏ k in Finset.range n, ‖W k‖) ≤ L ^ n := by
        calc
          (∏ k in Finset.range n, ‖W k‖) ≤ ∏ k in Finset.range n, L := by
            exact Finset.prod_le_prod (fun k hk => norm_nonneg (W k)) (fun k hk => hW k)
          _ = L ^ n := by
            rw [Finset.prod_const, Finset.card_range]
      have hlast : δ n * (∏ k in Finset.range n, ‖W k‖) * ‖x‖ ≤ d * L ^ n * ‖x‖ := by
        have hδn : δ n ≤ d := le_of_eq (hδ n)
        have hδn0 : 0 ≤ δ n := hδ0 n
        have hmul : δ n * (∏ k in Finset.range n, ‖W k‖) ≤ d * L ^ n := by
          calc
            δ n * (∏ k in Finset.range n, ‖W k‖) ≤ δ n * L ^ n :=
              mul_le_mul_of_nonneg_left hP hδn0
            _ ≤ d * L ^ n := mul_le_mul_of_nonneg_right hδn (pow_nonneg hL0 n)
        exact mul_le_mul_of_nonneg_right hmul (norm_nonneg x)
      have hfirst : ‖Wq n‖ * quantErrBound W Wq δ x n
          ≤ L * ((n : ℝ) * d * L ^ n * ‖x‖) :=
        mul_le_mul (hWq n) (ih x) hB0 hL0
      have hLpow : L ^ n ≤ L ^ (n + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (pow_nonneg hL0 n) hL1
      calc
        quantErrBound W Wq δ x (n + 1)
            = ‖Wq n‖ * quantErrBound W Wq δ x n + δ n * (∏ k in Finset.range n, ‖W k‖) * ‖x‖ := by
              simp [quantErrBound]
        _ ≤ L * ((n : ℝ) * d * L ^ n * ‖x‖) + d * L ^ n * ‖x‖ := by
              exact add_le_add hfirst hlast
        _ = (n : ℝ) * d * L ^ (n + 1) * ‖x‖ + d * L ^ n * ‖x‖ := by
              have hpow : L * L ^ n = L ^ (n + 1) := by rw [← pow_succ']
              calc
                L * ((n : ℝ) * d * L ^ n * ‖x‖) + d * L ^ n * ‖x‖
                    = (n : ℝ) * d * (L * L ^ n) * ‖x‖ + d * L ^ n * ‖x‖ := by ring
                _ = (n : ℝ) * d * L ^ (n + 1) * ‖x‖ + d * L ^ n * ‖x‖ := by rw [hpow]
        _ ≤ (n : ℝ) * d * L ^ (n + 1) * ‖x‖ + d * L ^ (n + 1) * ‖x‖ := by
              have hm : d * L ^ n * ‖x‖ ≤ d * L ^ (n + 1) * ‖x‖ := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hLpow hd0) (norm_nonneg x)
              exact add_le_add_left hm ((n : ℝ) * d * L ^ (n + 1) * ‖x‖)
        _ = (↑(n + 1) : ℝ) * d * L ^ (n + 1) * ‖x‖ := by
              have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
                simp [Nat.cast_add]
              rw [hc]
              ring

/-- 定理三（均匀量化特例）：所有层量化误差界 δ i = d（d ≥ 0）、
‖Wq i‖ ≤ L、‖W i‖ ≤ L（L ≥ 1）⟹ 端到端误差
‖quantFwd Wq n x − quantFwd W n x‖ ≤ n·d·Lⁿ·‖x‖。
（L ≥ 1 时每层至多放大 L 倍，n 层端到端 ≤ n·d·Lⁿ；L < 1 时误差被
收缩层衰减，需以 Σᵢ d·Lⁱ 形式给出——诚实标注，未在此展开。） -/
theorem quantized_uniform_error (W Wq : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (n : ℕ) (L d : ℝ)
    (hq : ∀ i, i < n → ‖Wq i - W i‖ ≤ δ i)
    (hδ : ∀ i, δ i = d) (hd0 : 0 ≤ d)
    (hWq : ∀ i, ‖Wq i‖ ≤ L) (hW : ∀ i, ‖W i‖ ≤ L)
    (hL1 : 1 ≤ L) :
    ∀ x, ‖quantFwd Wq n x - quantFwd W n x‖ ≤ (n : ℝ) * d * L ^ n * ‖x‖ := by
  intro x
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => by
    rw [hδ i]
    exact hd0
  exact le_trans (quantized_chain_error W Wq δ n hq x)
    (quantErrBound_uniform W Wq δ L d hδ0 hδ hWq hW hL1 n x)

/-! ## 注：实例化闭环
  线性层量化误差界（‖Wq−W‖ ≤ δ，由 rounding 界给出）代入定理二 ⟹
  n 层线性链端到端误差；Lipschitz 层（hL/hLq，如激活+权重复合层）代入
  定理四 ⟹ 更通用的 n 层端到端误差。两层版（定理一）是 n 层版的
  显式特例（δ₁ 经 ‖Wq₂‖ 放大、δ₂ 经 ‖W₁‖ 放缩输入）。均匀量化
  （每层 δ_i = d、范数 ≤ L）代入定理三 ⟹ 实用上界 n·d·Lⁿ·‖x‖。
  与 RealApprox 的 layer_out_error_bound（标量版）衔接：本文件是其在
  算子/链结构上的推广；与 RealChain 的 chainN_error_bound 衔接：本文件
  处理「量化前后两套链之差」，chainN_error_bound 处理「同一链在两点
  之差」。-/

end Lattice
