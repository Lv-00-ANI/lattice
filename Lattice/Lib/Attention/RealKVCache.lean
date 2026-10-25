import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Attention.RealCausalAttention
/-!
# LATTICE: KV 缓存推理等价性 —— 增量解码与全量解码的输出一致

自回归（incremental）推理用 **KV 缓存**避免重算：位置 `i` 的注意力只 attend
到 `j ≤ i`（因果掩码），因此缓存前 `i` 个（含 `i`）key/value，新 token 只计算
新的一行输出（`RealCausalAttention` 的 `causalDenom` / `causalSoftmax`）。
本文件形式化这一优化**不改变输出**（KV 缓存 = 全量因果注意力的逐行重写）：

  1. `prefixScores s i`：前缀截断分数（把 `i` 之后的未来槽位置零，模拟"缓存
     尚未写入的未来槽位"）；
  2. `cache_independent_of_future`（核心引理）：若两个分数向量在 `j ≤ i` 上
     一致，则 `causalSoftmax s i = causalSoftmax s' i`——因果掩码使权重
     `w_j` 对 `j > i` 的分数**无依赖**（分子带掩码、分母是掩码内前缀和，
     未来分数被 `if` 分支整段丢弃）；
  3. `cache_append_eq_full`（核心）：`causalSoftmax (prefixScores s i) i
     = causalSoftmax s i`——用缓存前缀重算第 `i` 行与全量计算逐点相同；
     行级推论 `cache_row_output_eq_full`：`cacheRowOutput = causalRowOutput`；
  4. `cache_output_eq_full`：整条序列的缓存输出与全量输出相等（逐行 + `funext`）；
  5. `cache_append_preserves_earlier_rows`：追加新 token（缓存扩展到 `i`）不改变
     已缓存位置 `k ≤ i` 的输出行——增量推理的"已生成 token 不变"性质；
  6. `cache_weights_supported_on_prefix` / `cache_row_output_supported_on_prefix`：
     非零权重只落在前缀 `j ≤ i` 上，故缓存行输出只需前缀 value；
  7. `cache_memory_bound`（加分）：非零权重支持集大小 ≤ `i.val + 1`
     = 已处理 token 数（`cacheLength`）——缓存大小 = 已处理 token 数。

诚实假设（均显式标注）：
  · 因果掩码 `j ≤ i`（只看过去与当前）——本文件所有结论都依赖它；
  · 权重定义用 `RealCausalAttention` 的 `causalDenom` / `causalSoftmax`
    （`if` 分支形式，避免 −∞）；
  · "缓存"抽象为**前缀截断分数向量** `prefixScores`（未来槽位的值无关紧要，
    这正是引理 2 所断言的内容）：本文件证明缓存行输出等于全量行输出，
    即缓存策略的正确性，而非实现层面的内存布局；
  · value 表 `V : Fin n → F` 为参数（缓存同时缓存 key 派生的分数与 value，
    本文件把 key→分数 与 value 都视作已缓存的历史数据）。
全部证明无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 缓存长度 = 已处理 token 数 -/

/-- 处理到位置 `i`（含）时，已缓存的 token 数 = `i.val + 1`。 -/
def cacheLength {n : ℕ} (i : Fin n) : ℕ := i.val + 1

/-- 缓存长度的定义式展开（已处理 token 数）。 -/
theorem cache_size_eq_processed {n : ℕ} (i : Fin n) : cacheLength i = i.val + 1 := rfl

/-! ## 前缀截断分数（未来槽位视作 0） -/

/-- 前缀截断分数：把位置 `i` 之后的未来分数置零——模拟缓存中尚未写入的
未来槽位（未来取值任意，不影响计算结果，见 `cache_independent_of_future`）。 -/
def prefixScores {n : ℕ} (s : Fin n → ℝ) (i : Fin n) : Fin n → ℝ :=
  fun j => if j ≤ i then s j else 0

/-- 前缀截断保持前缀上的取值：`j ≤ i ⟹ prefixScores s i j = s j`。 -/
@[simp] lemma prefixScores_of_le {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) (h : j ≤ i) :
    prefixScores s i j = s j := by
  unfold prefixScores
  rw [if_pos h]

/-- 前缀截断丢弃后缀：`¬ j ≤ i ⟹ prefixScores s i j = 0`。 -/
@[simp] lemma prefixScores_of_not_le {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) (h : ¬ j ≤ i) :
    prefixScores s i j = 0 := by
  unfold prefixScores
  rw [if_neg h]

/-! ## 全量因果行输出 与 缓存（增量）行输出 -/

/-- 全量因果注意力的第 `i` 行输出：`Σ_j w_j • V_j`，`w = causalSoftmax s i`。 -/
def causalRowOutput {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F) (i : Fin n) : F :=
  convComb (causalSoftmax s i) V

/-- 增量（KV 缓存）行输出：只用前缀截断分数（缓存前 `i` 个 key/value）重算
第 `i` 行，与全量计算的差由 `cache_row_output_eq_full` 断言为零。 -/
def cacheRowOutput {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F) (i : Fin n) : F :=
  convComb (causalSoftmax (prefixScores s i) i) V

/-- 全量因果注意力的整条序列输出（逐行）。 -/
def causalFullOutput {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F) : Fin n → F :=
  fun i => causalRowOutput s V i

/-- 增量（KV 缓存）推理的整条序列输出（逐行用缓存前缀计算）。 -/
def causalCacheOutput {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F) : Fin n → F :=
  fun i => cacheRowOutput s V i

/-! ## 定理一（核心引理）：因果权重与未来分数无关

若 `s` 与 `s'` 在 `j ≤ i` 上一致，则 `causalSoftmax s i = causalSoftmax s' i`。
证明：分母 `Σ_{k ≤ i} exp(s_k)` 的每个 `if` 分支只在 `k ≤ i` 处取非零值，
分子同理；故两侧逐项（逐 `Fin n`）相等——未来位置的分数在 `if_neg` 分支中
被完全丢弃（因果掩码性质）。 -/

theorem cache_independent_of_future {n : ℕ} (s s' : Fin n → ℝ) (i : Fin n)
    (h : ∀ j, j ≤ i → s j = s' j) :
    causalSoftmax s i = causalSoftmax s' i := by
  funext j
  unfold causalSoftmax causalDenom
  have hden : (∑ k, (if k ≤ i then Real.exp (s k) else 0))
      = ∑ k, (if k ≤ i then Real.exp (s' k) else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k ≤ i
    · rw [if_pos hki, if_pos hki, h k hki]
    · rw [if_neg hki, if_neg hki]
  rw [hden]
  by_cases hji : j ≤ i
  · rw [if_pos hji, if_pos hji, h j hji]
  · rw [if_neg hji, if_neg hji]

/-! ## 定理二（核心）：缓存前缀重算 = 全量计算

`causalSoftmax (prefixScores s i) i = causalSoftmax s i`——前缀截断分数与
原分数在 `j ≤ i` 上一致（`prefixScores_of_le`），由定理一即得。这是
"缓存前 `i` 项再算第 `i` 项与全量一致"的权重级陈述。 -/

theorem cache_append_eq_full {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    causalSoftmax (prefixScores s i) i = causalSoftmax s i := by
  symm
  apply cache_independent_of_future
  intro j hj
  rw [prefixScores_of_le s i j hj]

/-! ## 定理三：缓存行输出 = 全量行输出（逐行等价） -/

theorem cache_row_output_eq_full {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F) (i : Fin n) :
    cacheRowOutput s V i = causalRowOutput s V i := by
  unfold cacheRowOutput causalRowOutput
  rw [cache_append_eq_full]

/-! ## 定理四：整条序列的缓存输出 = 全量输出 -/

theorem cache_output_eq_full {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F) :
    causalCacheOutput s V = causalFullOutput s V := by
  funext i
  exact cache_row_output_eq_full s V i

/-! ## 定理五：追加 token 不改变已缓存行

缓存从 `k` 扩展到 `i`（`k ≤ i`）后，位置 `k` 的输出行不变：
`causalSoftmax (prefixScores s i) k = causalSoftmax (prefixScores s k) k`。
证明：两份截断分数在 `j ≤ k` 上都是 `s j`（因为 `j ≤ k ≤ i`），
再用定理一。这是自回归生成"已生成 token 不再变化"的结构性保证。 -/

theorem cache_append_preserves_earlier_rows {n : ℕ} (s : Fin n → ℝ) (k i : Fin n)
    (hk : k ≤ i) :
    causalSoftmax (prefixScores s i) k = causalSoftmax (prefixScores s k) k := by
  apply cache_independent_of_future
  intro j hj
  rw [prefixScores_of_le s i j (le_trans hj hk), prefixScores_of_le s k j hj]

/-- 定理五'（输出级）：追加 token 不改变已缓存位置 `k` 的输出行。 -/
theorem cache_append_preserves_earlier_outputs {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F)
    (k i : Fin n) (hk : k ≤ i) :
    convComb (causalSoftmax (prefixScores s i) k) V
      = convComb (causalSoftmax (prefixScores s k) k) V := by
  rw [cache_append_preserves_earlier_rows s k i hk]

/-! ## 定理六：未来位置权重为零（缓存支持集只在前缀上） -/

theorem cache_weights_supported_on_prefix {n : ℕ} (s : Fin n → ℝ) (i j : Fin n)
    (h : ¬ j ≤ i) : causalSoftmax (prefixScores s i) i j = 0 :=
  causalSoftmax_eq_zero_of_gt (prefixScores s i) i j h

/-- 定理六'：缓存行输出只需前缀 `j ≤ i` 上的 value
（`Σ_{j ∈ univ} = Σ_{j ∈ Iic i}`，因后缀权重为 0）。 -/
theorem cache_row_output_supported_on_prefix {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F)
    (i : Fin n) :
    cacheRowOutput s V i
      = ∑ j in Finset.Iic i, causalSoftmax (prefixScores s i) i j • V j := by
  unfold cacheRowOutput convComb
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hxnot
  have hxi : ¬ x ≤ i := fun h => hxnot (Finset.mem_Iic.mpr h)
  rw [cache_weights_supported_on_prefix s i x hxi, zero_smul]

/-! ## 定理七（加分）：缓存大小 = 已处理 token 数

非零注意力权重只落在前缀 `j ≤ i` 上（定理六），故缓存行输出实际使用的
位置数 ≤ `(Finset.Iic i).card = i.val + 1 = cacheLength i`——缓存规模由
已处理 token 数界住（`Fin.card_Iic`）。 -/

theorem cache_memory_bound {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    (Finset.univ.filter (fun j : Fin n => causalSoftmax (prefixScores s i) i j ≠ 0)).card
      ≤ cacheLength i := by
  have hsub : Finset.univ.filter (fun j : Fin n => causalSoftmax (prefixScores s i) i j ≠ 0)
      ⊆ Finset.Iic i := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_Iic]
    by_contra hji
    exact hj.2 (cache_weights_supported_on_prefix s i j hji)
  calc
    (Finset.univ.filter (fun j : Fin n => causalSoftmax (prefixScores s i) i j ≠ 0)).card
        ≤ (Finset.Iic i).card := Finset.card_le_card hsub
    _ = i.val + 1 := Fin.card_Iic i
    _ = cacheLength i := rfl

/-! ## 定理八：缓存行输出仍被最大 value 界住（凸组合界，复用既有结论）

缓存不改变输出（定理三）⟹ 输出界照旧：`‖cacheRowOutput s V i‖ ≤ M`
（`RealCausalAttention.causal_attention_output_bound`）。 -/

theorem cache_output_bound {n : ℕ} (s : Fin n → ℝ) (V : Fin n → F) (i : Fin n) (M : ℝ)
    (hV : ∀ j, ‖V j‖ ≤ M) : ‖cacheRowOutput s V i‖ ≤ M := by
  unfold cacheRowOutput
  exact causal_attention_output_bound (prefixScores s i) i V M hV

end Lattice
