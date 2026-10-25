import Mathlib
import Lattice.Lib.Attention.RealAttention
/-!
# LATTICE: 分组查询注意力（GQA）—— KV 参数共享特例与 MHA/MQA 关系

transformer 调研（research/real-world/transformer-semantics.md 的 MHA 变体）：
GQA（Grouped Query Attention）是标准多头注意力（MHA）的**参数共享特例**：
H 个查询头共享 K 个 KV 头（分组函数 g : Fin H → Fin K，查询头 i 使用第
g i 个 KV 头的键/值投影）；K = H 时退化为标准 MHA（每头独立 KV，
g = id），K = 1 时退化为 MQA（Multi-Query Attention，全体查询头共享
唯一 KV 头）。

核心结构观察（与 RealAttention 相同的行随机凸组合性质，模型无关）：
  1. groupedAttnWeights：查询头 i 在位置 j 的注意力权重 =
     softmax_j(⟨Q_i x_q, K_{g i} x_j⟩ / √d)——键投影按组共享（g i），
     查询投影按头独立（i）；
  2. grouped_attention_output：头 i 输出 = Σ_j w_{i,j} · V_{g i} x_j
     （value 投影也按组共享）——行随机凸组合；
  3. grouped_output_bound（核心）：‖头 i 输出‖ ≤ max_j ‖V_{g i} x_j‖
     ——权重非负 + 和 1（softmax 行随机，softmax_nonneg / softmax_sum_one）
     ⟹ 凸组合界（复用 convComb_norm_bound）。GQA 与 MHA/MQA 共享同一
     输出界结构：行随机性质完全保持；
  4. gqa_is_mha_special（核心/加分）：g = id（K = H，每头独立 KV）时
     GQA 输出 = 标准 MHA 输出——代入 g i = i 后定义逐点相同（陈述式
     化简定理）；
  5. mqa_is_gqa_extreme（加分）：K = 1（唯一 KV 头）时任意分组函数
     恒为 0（mqa_grouping_constant），全体查询头共享同一 KV——输出界
     同引理 3（MQA 是 GQA 的极端）；
  6. gqa_logit_scale_bound：√d 缩放界 |⟨Q_i x_q, K_{g i} x_j⟩/√d|
     ≤ ‖Q_i x_q‖·‖K_{g i} x_j‖/√d（Cauchy-Schwarz，sqrt_d_scale_bound）。

诚实假设（模型无关，与 RealAttention / RealTopK 相同）：
  · E 是实内积空间（查询/键向量所在空间），F 是实赋范空间（value 所在）；
  · ι 是非空有限指标集（位置/token），H / K 为查询头数 / KV 头数；
  · 分组函数 g : Fin H → Fin K 任意（K ≤ H 仅为语境，本文件不需要该假设）；
  · value 向量 V (g i) j 抽象为参数（= 第 g i 个 KV 头的值投影作用于
    token j，与 RealAttention 的 V : ι → F 抽象一致）；
  · √d 缩放出现在 logits 中，但权重行随机 / 输出界与 d 无关（对任意 d
    成立）；仅 gqa_logit_scale_bound 需要 hd : 0 < d。
全部证明无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

variable {H K : ℕ} {ι F E : Type*}
  [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## GQA logits（查询头 i 对第 g i 个 KV 头在位置 j 的分数）
⟨Q_i x_q, K_{g i} x_j⟩ / √d：查询投影按头独立（Q i），键投影按组共享
（Kv (g i)）。 -/

def gqaLogits (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) : ι → ℝ :=
  fun j => inner (Q i xq) (Kv (g i) (x j)) / Real.sqrt d

/-! ## 定理一：√d 缩放界（Cauchy-Schwarz）
|⟨Q_i x_q, K_{g i} x_j⟩/√d| ≤ ‖Q_i x_q‖·‖K_{g i} x_j‖/√d（d > 0）——
复用 sqrt_d_scale_bound（RealAttention）。-/

omit [Fintype ι] [Nonempty ι] in
theorem gqa_logit_scale_bound (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) (j : ι) (hd : 0 < d) :
    |gqaLogits Q Kv g d xq x i j| ≤ ‖Q i xq‖ * ‖Kv (g i) (x j)‖ / Real.sqrt d := by
  unfold gqaLogits
  exact sqrt_d_scale_bound (Q i xq) (Kv (g i) (x j)) d hd

/-! ## 分组注意力权重（softmax 行，组内共享 KV 键投影） -/

def groupedAttnWeights (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) : ι → ℝ :=
  softmax (gqaLogits Q Kv g d xq x i)

/-! ## 定理二：权重行随机保持（softmax 性质直接给）
每个查询头的权重行都是概率分布：非负（softmax_nonneg）+ 和 1
（softmax_sum_one）。行随机性质与分组共享无关——GQA 权重与标准 MHA
权重同属行随机凸组合。 -/

theorem gqa_weights_nonneg (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) (j : ι) :
    0 ≤ groupedAttnWeights Q Kv g d xq x i j := by
  unfold groupedAttnWeights
  exact softmax_nonneg (gqaLogits Q Kv g d xq x i) j

theorem gqa_weights_sum_one (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) :
    ∑ j : ι, groupedAttnWeights Q Kv g d xq x i j = 1 := by
  unfold groupedAttnWeights
  exact softmax_sum_one (gqaLogits Q Kv g d xq x i)

theorem gqa_preserves_pmf (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) :
    ProbDist (groupedAttnWeights Q Kv g d xq x i) := by
  exact ⟨gqa_weights_nonneg Q Kv g d xq x i, gqa_weights_sum_one Q Kv g d xq x i⟩

/-! ## 分组注意力输出（行随机凸组合，value 按组共享）
头 i 输出 = Σ_j w_{i,j} · V_{g i} x_j，其中 V (g i) j 是第 g i 个 KV 头
的值投影在位置 j 的输出（V 抽象为参数）。 -/

def grouped_attention_output (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (V : Fin K → ι → F) (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E)
    (i : Fin H) : F :=
  ∑ j : ι, groupedAttnWeights Q Kv g d xq x i j • V (g i) j

/-! ## 定理三：GQA 输出界（核心：凸组合界）
‖头 i 输出‖ ≤ M，其中 M 界住全部 ‖V (g i) j‖（M = max_j ‖V_{g i} x_j‖
的 M-形式）——复用 convComb_norm_bound（RealAttention）：权重非负 + 和 1
（定理二）⟹ 行随机凸组合的范数 ≤ 最大 value 范数。GQA 与 MHA/MQA
共享同一输出界结构，行随机性质保持不变。-/

theorem grouped_output_bound (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (V : Fin K → ι → F) (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E)
    (i : Fin H) (M : ℝ) (hV : ∀ j : ι, ‖V (g i) j‖ ≤ M) :
    ‖grouped_attention_output Q Kv V g d xq x i‖ ≤ M := by
  unfold grouped_attention_output
  exact convComb_norm_bound (groupedAttnWeights Q Kv g d xq x i) (fun j => V (g i) j) M
    (fun j => gqa_weights_nonneg Q Kv g d xq x i j) (gqa_weights_sum_one Q Kv g d xq x i) hV

/-! ## 推论：全体查询头的输出统一被界住
M 界住全部 KV 头在全部位置的 value 范数（∀k, ∀j, ‖V k j‖ ≤ M）⟹
每个查询头（任意 i）的输出 ≤ M——GQA 的全局输出界。 -/

theorem gqa_all_heads_output_bound (Q : Fin H → E →L[ℝ] E) (Kv : Fin K → E →L[ℝ] E)
    (V : Fin K → ι → F) (g : Fin H → Fin K) (d : ℝ) (xq : E) (x : ι → E)
    (M : ℝ) (hV : ∀ k : Fin K, ∀ j : ι, ‖V k j‖ ≤ M) :
    ∀ i : Fin H, ‖grouped_attention_output Q Kv V g d xq x i‖ ≤ M := by
  intro i
  exact grouped_output_bound Q Kv V g d xq x i M (fun j => hV (g i) j)

/-! ## 标准 MHA 输出（每查询头独立 KV：K = H，对照用）
头 i 输出 = Σ_j softmax_j(⟨Q_i x_q, K_i x_j⟩/√d) · V_i x_j——查询、键、
值投影全部按头独立（Kv i / V i）。 -/

def mhaHeadOutput (Q : Fin H → E →L[ℝ] E) (Kv : Fin H → E →L[ℝ] E)
    (V : Fin H → ι → F) (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) : F :=
  ∑ j : ι, softmax (fun j => inner (Q i xq) (Kv i (x j)) / Real.sqrt d) j • V i j

/-! ## 定理四：GQA = MHA 特例（g = id，K = H）（核心/加分）
代入 g i = i 后 GQA 定义与标准 MHA 定义逐点相同（陈述式化简定理）：
  · 权重级：groupedAttnWeights（g = id）= softmax(⟨Q_i x_q, K_i x_j⟩/√d)
    = MHA 权重（gqa_weights_eq_mha_weights）；
  · 输出级：grouped_attention_output（g = id）= mhaHeadOutput
    （gqa_is_mha_special）。-/

omit [Nonempty ι] in
theorem gqa_weights_eq_mha_weights (Q : Fin H → E →L[ℝ] E) (Kv : Fin H → E →L[ℝ] E)
    (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) (j : ι) :
    groupedAttnWeights Q Kv (fun k : Fin H => k) d xq x i j =
      softmax (fun k : ι => inner (Q i xq) (Kv i (x k)) / Real.sqrt d) j := by
  unfold groupedAttnWeights gqaLogits
  simp

omit [Nonempty ι] in
theorem gqa_is_mha_special (Q : Fin H → E →L[ℝ] E) (Kv : Fin H → E →L[ℝ] E)
    (V : Fin H → ι → F) (d : ℝ) (xq : E) (x : ι → E) (i : Fin H) :
    grouped_attention_output Q Kv V (fun k : Fin H => k) d xq x i =
      mhaHeadOutput Q Kv V d xq x i := by
  unfold grouped_attention_output mhaHeadOutput groupedAttnWeights gqaLogits
  simp

/-! ## 定理五：K = 1（MQA 极端，加分）
Fin 1 只有元素 0，故任意分组函数 g : Fin H → Fin 1 恒为 0（mqa_grouping_
constant）——全体查询头共享唯一 KV 头（MQA）；输出界同定理三
（mqa_is_gqa_extreme：对任意 g 直接实例化 grouped_output_bound）。-/

lemma mqa_grouping_constant (g : Fin H → Fin 1) (i : Fin H) : g i = 0 := by
  ext
  have hlt : (g i).val < 1 := (g i).isLt
  omega

theorem mqa_is_gqa_extreme (Q : Fin H → E →L[ℝ] E) (Kv : Fin 1 → E →L[ℝ] E)
    (V : Fin 1 → ι → F) (g : Fin H → Fin 1) (d : ℝ) (xq : E) (x : ι → E)
    (i : Fin H) (M : ℝ) (hV : ∀ j : ι, ‖V 0 j‖ ≤ M) :
    ‖grouped_attention_output Q Kv V g d xq x i‖ ≤ M := by
  have hconst : g i = 0 := mqa_grouping_constant g i
  have hV' : ∀ j : ι, ‖V (g i) j‖ ≤ M := by
    intro j
    rw [hconst]
    exact hV j
  exact grouped_output_bound Q Kv V g d xq x i M hV'

end Lattice
