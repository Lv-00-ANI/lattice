import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Architectures.RealBlockLipschitz
import Lattice.Lib.Architectures.RealBlockConstants
/-!
# LATTICE: encoder–decoder 交叉注意力 —— 行随机权重、凸组合输出界与块 Lipschitz 组装

transformer 调研（research/real-world/transformer-semantics.md 的 encoder–decoder
架构）核心组件：**交叉注意力**（cross-attention）。与自注意力不同，交叉注意力的
查询来自 decoder 表示 `x_q`，键/值来自 encoder 表示 `x_kv`（长度为 `ιkv` 的序列）：

  1. `crossLogits`：查询 `x_q` 与键 `x_kv j` 的分数
     `⟨Q x_q, K (x_kv j)⟩ / √d`（Q、K 为查询/键投影，d 为头维）；
  2. `crossAttnWeights` = `softmax(crossLogits)`，`crossAttnOutput`
     = `Σ_j w_j • V (x_kv j)`（V 为 encoder 侧值投影，值向量抽象为参数）；
  3. 权重行随机：`crossAttn_weights_nonneg` / `crossAttn_weights_sum_one` /
     `crossAttn_weights_pmf`（复用 `RealAttention.softmax_nonneg` /
     `softmax_sum_one`）——交叉注意力权重同样是概率分布；
  4. `cross_attention_output_bound`（核心）：输出是 encoder 值的**凸组合**，
     `‖Σ_j w_j • V_j‖ ≤ max_j ‖V_j‖`（复用
     `RealAttention.convComb_norm_bound`）——对任意键长度 `ιkv` 稳健
     （`cross_attention_is_row_stochastic_operator` 把「任意非空有限键指标」
     的重述与输出界打包在同一命题里，显式展示对 `ιkv` 的无关性）；
  5. `cross_logit_scale_bound`：√d 缩放界（复用 `sqrt_d_scale_bound`）；
  6. `cross_attention_lipschitz_in_query`（加分）：权重随查询变化时交叉注意力
     对查询输入的 Lipschitz 界 `M · Lw`——权重 L1 差 × encoder 值范数界
     （`RealBlockConstants.weight_l1_diff_bound` / `score_lin_lipschitz` 给出
     数字常数版的 `cross_attention_lipschitz_numeric_in_query`）；
  7. `encoder_decoder_block_bound`（核心/组装）：encoder 块（双向自注意力）
     与 decoder 块（自注意力 + 交叉注意力 + FFN）组合的块 Lipschitz 界。
     组装方式（与 `RealBlockConstants.transformer_block_numeric` /
     `RealMixedAttention.mixed_block_lipschitz` 同一骨架）：
     decoder 块 = `F ∘ (id + A_self + A_cross + G)`，其中交叉注意力项
     **并入加法组合**（`RealBlockLipschitz.lipschitz_add`：
     `A_self + A_cross` 的 Lipschitz 常数 = `La_s + La_c`），再经
     `block_lipschitz_bound` 与 encoder 块复合（`lipschitz_comp` 模式）。

诚实假设（模型无关，均显式标注）：
  · `E` 是实内积空间（查询/键所在），`F` 是实赋范空间（encoder 值所在）；
  · `ιkv` 非空有限（键/值位置数），`ιq` 任意（查询 batch/位置，无有限性要求）；
  · 交叉注意力的值向量 `V : ιkv → F` 抽象为参数（= encoder 侧值投影在键位置
    的输出），因此输出界 / 对查询的 Lipschitz 界都**不依赖值是否随查询变化**
    （这与自注意力的 `attention_lipschitz_weighted` 不同：那里值也随输入变化，
    故界里出现因子 `(1 + B·Lw)`；交叉注意力只需 `M · Lw`，因为值是 encoder
    常量——这是交叉注意力比自注意力"更稳"的结构性原因）；
  · 数字常数版需要数据域假设 `‖z‖ ≤ B`（分数上界）与值界 `∀j, ‖V j‖ ≤ M`；
  · 块组装需要各组件 Lipschitz 常数非负（`hLf / hLa / hLg`）以推出组合常数
    非负——这是范数界的自然前提，显式标注。
全部证明无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

variable {ιq ιkv : Type*} [Fintype ιkv] [Nonempty ιkv]
  {F E : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 交叉注意力分数（查询来自 decoder，键来自 encoder） -/

/-- 交叉注意力分数：`⟨Q x_q, K (x_kv j)⟩ / √d`（查询向量 `x_q` 来自 decoder，
键向量 `x_kv j` 来自 encoder）。 -/
def crossLogits (Q K : E →L[ℝ] E) (d : ℝ) (xq : E) (xkv : ιkv → E) : ιkv → ℝ :=
  fun j => inner (Q xq) (K (xkv j)) / Real.sqrt d

/-! ## 交叉注意力权重（softmax 行） -/

/-- 交叉注意力权重：`w_j = softmax_j(⟨Q x_q, K (x_kv j)⟩ / √d)`——行随机。 -/
def crossAttnWeights (Q K : E →L[ℝ] E) (d : ℝ) (xq : E) (xkv : ιkv → E) : ιkv → ℝ :=
  softmax (crossLogits Q K d xq xkv)

/-! ## 交叉注意力输出（encoder 值的凸组合） -/

/-- 交叉注意力输出：`Σ_j w_j • V (x_kv j)`（V 为 encoder 侧值投影，抽象为
`V : ιkv → F` 参数）。 -/
def crossAttnOutput (Q K : E →L[ℝ] E) (V : ιkv → F) (d : ℝ) (xq : E)
    (xkv : ιkv → E) : F :=
  convComb (crossAttnWeights Q K d xq xkv) V

/-! ## 定理一：√d 缩放界（Cauchy-Schwarz）

`|⟨Q x_q, K (x_kv j)⟩ / √d| ≤ ‖Q x_q‖·‖K (x_kv j)‖ / √d`（`d > 0`）——
复用 `RealAttention.sqrt_d_scale_bound`。 -/

omit [Fintype ιkv] [Nonempty ιkv] in
theorem cross_logit_scale_bound (Q K : E →L[ℝ] E) (d : ℝ) (xq : E) (xkv : ιkv → E)
    (j : ιkv) (hd : 0 < d) :
    |crossLogits Q K d xq xkv j| ≤ ‖Q xq‖ * ‖K (xkv j)‖ / Real.sqrt d := by
  unfold crossLogits
  exact sqrt_d_scale_bound (Q xq) (K (xkv j)) d hd

/-! ## 定理二：交叉注意力权重非负（softmax 行随机之一） -/

theorem crossAttn_weights_nonneg (Q K : E →L[ℝ] E) (d : ℝ) (xq : E) (xkv : ιkv → E)
    (j : ιkv) : 0 ≤ crossAttnWeights Q K d xq xkv j := by
  unfold crossAttnWeights
  exact softmax_nonneg (crossLogits Q K d xq xkv) j

/-! ## 定理三：交叉注意力权重和为 1（softmax 行随机之二） -/

theorem crossAttn_weights_sum_one (Q K : E →L[ℝ] E) (d : ℝ) (xq : E) (xkv : ιkv → E) :
    ∑ j, crossAttnWeights Q K d xq xkv j = 1 := by
  unfold crossAttnWeights
  exact softmax_sum_one (crossLogits Q K d xq xkv)

/-! ## 定理四：交叉注意力权重行随机（概率分布）

`ProbDist (crossAttnWeights ...)`——非负 + 和 1，与自注意力（`RealAttention`）
同一 softmax 结构，故行随机性完全保持。 -/

theorem crossAttn_weights_pmf (Q K : E →L[ℝ] E) (d : ℝ) (xq : E) (xkv : ιkv → E) :
    ProbDist (crossAttnWeights Q K d xq xkv) :=
  ⟨crossAttn_weights_nonneg Q K d xq xkv, crossAttn_weights_sum_one Q K d xq xkv⟩

/-! ## 定理五（核心）：交叉注意力输出界（凸组合界）

`M` 界住全部 encoder 值范数 ⟹ `‖crossAttnOutput‖ ≤ M`——输出是 encoder 值的
凸组合（行随机权重），复用 `RealAttention.convComb_norm_bound`。这是交叉注意力
的残差稳定性：无论键/值序列多长，输出范数被最大 encoder 值界住。 -/

theorem cross_attention_output_bound (Q K : E →L[ℝ] E) (V : ιkv → F) (d : ℝ) (xq : E)
    (xkv : ιkv → E) (M : ℝ) (hV : ∀ j, ‖V j‖ ≤ M) :
    ‖crossAttnOutput Q K V d xq xkv‖ ≤ M := by
  unfold crossAttnOutput
  exact convComb_norm_bound (crossAttnWeights Q K d xq xkv) V M
    (crossAttn_weights_nonneg Q K d xq xkv) (crossAttn_weights_sum_one Q K d xq xkv) hV

/-! ## 定理六：对任意键长度稳健的行随机算子 + 输出界（键指标类型再量化）

把键指标类型在命题内重新量化：对**任意**非空有限键指标集 `ικv`（任意键长度），
交叉注意力权重仍是概率分布，且输出仍被最大 encoder 值界住。这把「输出是
encoder 值的凸组合，且与键长度无关」这一结构性质作为单一命题陈述。 -/

theorem cross_attention_is_row_stochastic_operator
    {ικv : Type*} [Fintype ικv] [Nonempty ικv]
    (Q K : E →L[ℝ] E) (V : ικv → F) (d : ℝ) (xq : E) (xkv : ικv → E) (M : ℝ)
    (hV : ∀ j, ‖V j‖ ≤ M) :
    (∀ j, 0 ≤ crossAttnWeights Q K d xq xkv j) ∧
      (∑ j, crossAttnWeights Q K d xq xkv j = 1) ∧
      ‖crossAttnOutput Q K V d xq xkv‖ ≤ M := by
  refine ⟨crossAttn_weights_nonneg Q K d xq xkv, crossAttn_weights_sum_one Q K d xq xkv, ?_⟩
  exact cross_attention_output_bound Q K V d xq xkv M hV

/-! ## 交叉注意力 batch（查询 batch/位置，任意指标类型） -/

/-- 交叉注意力 batch 输出：对每个查询位置 `i : ιq` 计算一行交叉注意力
（键/值共享同一 encoder 序列）。 -/
def batchCrossAttnOutput (Q K : E →L[ℝ] E) (V : ιkv → F) (d : ℝ) (xq : ιq → E)
    (xkv : ιkv → E) : ιq → F :=
  fun i => crossAttnOutput Q K V d (xq i) xkv

/-- 推论：batch 中每一行输出都被最大 encoder 值界住（逐点实例化定理五）。 -/
theorem cross_attention_batch_output_bound (Q K : E →L[ℝ] E) (V : ιkv → F) (d : ℝ)
    (xq : ιq → E) (xkv : ιkv → E) (M : ℝ) (hV : ∀ j, ‖V j‖ ≤ M) :
    ∀ i, ‖batchCrossAttnOutput Q K V d xq xkv i‖ ≤ M := by
  intro i
  exact cross_attention_output_bound Q K V d (xq i) xkv M hV

/-! ## 定理七（加分）：对查询输入的 Lipschitz 界

交叉注意力的权重随查询 `x` 变化（softmax∘线性分数），但值向量是 encoder 常量
`V : ιkv → F`。若权重满足 L1-Lipschitz 假设 `Σ_j |w x j − w y j| ≤ Lw·‖x−y‖`
（`RealBlockConstants.attention_lipschitz_weighted` 的同一 Lw 假设），则
`‖A(x) − A(y)‖ ≤ M · Lw · ‖x − y‖`。

与自注意力的差别：自注意力的值 `Vᵢ x` 也随输入变化，`attention_lipschitz_weighted`
的界里因此有额外的 `(1 + B·Lw)` 因子（权重固定项的贡献）；交叉注意力值固定，
故只需 `M · Lw`——交叉注意力对查询扰动的敏感度严格更小。 -/

omit [InnerProductSpace ℝ E] in
theorem cross_attention_lipschitz_in_query (w : E → ιkv → ℝ) (V : ιkv → F) (M Lw B : ℝ)
    (_hw0 : ∀ x j, 0 ≤ w x j)
    (_hsum : ∀ x, ∑ j, w x j = 1)
    -- B365 (P0-2): was `hwlip : ∀ x y, …` UNCONDITIONALLY.  Proving such a lemma
    -- requires a global bound on the inputs -- exactly the unsatisfiable
    -- `hB : ∀ z, ‖z‖ ≤ B` (B357) that made every consumer vacuous.  The bound is
    -- now a PER-CALL parameter, so a caller needs it only at the two points its
    -- conclusion mentions.  Verified by probe before editing (B364).
    (hwlip : ∀ x y, ‖x‖ ≤ B → ‖y‖ ≤ B →
      (∑ j, |w x j - w y j|) ≤ Lw * ‖x - y‖)
    (hM : ∀ j, ‖V j‖ ≤ M) :
    ∀ x y : E, ‖x‖ ≤ B → ‖y‖ ≤ B →
      ‖(∑ j, w x j • V j) - (∑ j, w y j • V j)‖ ≤ M * Lw * ‖x - y‖ := by
  have hM0 : 0 ≤ M := by
    obtain ⟨j₀⟩ := (inferInstance : Nonempty ιkv)
    linarith [hM j₀, norm_nonneg (V j₀)]
  intro x y hx hy
  -- 差分解：A x − A y = Σ_j (w x j − w y j) • V j
  have hdiff : (∑ j, w x j • V j) - (∑ j, w y j • V j)
      = ∑ j, (w x j - w y j) • V j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [sub_smul]
  calc
    ‖(∑ j, w x j • V j) - (∑ j, w y j • V j)‖
        = ‖∑ j, (w x j - w y j) • V j‖ := by rw [hdiff]
    _ ≤ ∑ j, ‖(w x j - w y j) • V j‖ := norm_sum_le _ _
    _ = ∑ j, |w x j - w y j| * ‖V j‖ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j, |w x j - w y j| * M := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hM j) (abs_nonneg _)
    _ = (∑ j, |w x j - w y j|) * M := by rw [Finset.sum_mul]
    _ ≤ (Lw * ‖x - y‖) * M := mul_le_mul_of_nonneg_right (hwlip x y hx hy) hM0
    _ = M * Lw * ‖x - y‖ := by ring

/-! ## 定理八（数字常数版）：softmax 交叉注意力的查询 Lipschitz

`w x = softmax(S x)`（`S : E →L[ℝ] (Fin k → ℝ)` 是线性分数映射），
数据域 `‖z‖ ≤ B`：L1-Lipschitz 常数 `Lw = k·(k+1)·e^{4·‖S‖·B}·‖S‖`
（`RealBlockConstants.weight_l1_diff_bound`：softmax 权重 L1 差界 +
`score_lin_lipschitz`：线性分数 ∞-范数 Lipschitz），代入定理七得
`‖A(x) − A(y)‖ ≤ M · Lw · ‖x − y‖`。

诚实假设：需要 `[NeZero k]`（键非空）与数据域界 `‖z‖ ≤ B`（分数有界，
softmax 坐标 Lipschitz 的前提）。 -/

theorem cross_attention_lipschitz_numeric_in_query {k : ℕ} [NeZero k]
    (S : E →L[ℝ] (Fin k → ℝ)) (V : Fin k → F) (M B : ℝ)
    (hM : ∀ j : Fin k, ‖V j‖ ≤ M) :
    -- B365 (P0-2): was `(hB : ∀ z : E, ‖z‖ ≤ B)`, UNSATISFIABLE on any nontrivial
    -- space (B357 kernel-proved), hence every statement carrying it was vacuous.
    -- The bound is needed only at the two points the conclusion names.
    ∀ x y : E, ‖x‖ ≤ B → ‖y‖ ≤ B →
      ‖(∑ j : Fin k, softmax (S x) j • V j) - (∑ j : Fin k, softmax (S y) j • V j)‖
        ≤ M * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖) * ‖x - y‖ := by
  intro x y hBx hBy
  have hB0 : 0 ≤ B := le_trans (norm_nonneg x) hBx
  let M' : ℝ := ‖S‖ * B
  have hM' : 0 ≤ M' := by
    dsimp [M']
    exact mul_nonneg (norm_nonneg S) hB0
  -- 分数坐标界：|(S z) j| ≤ ‖S‖·B，界作为**该点**的前提（B365）
  have hscore : ∀ (z : E), ‖z‖ ≤ B → ∀ j : Fin k, |(S z) j| ≤ M' := by
    intro z hz j
    dsimp [M']
    calc
      |(S z) j| = ‖(S z) j‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖S z‖ := norm_le_pi_norm (S z) j
      _ ≤ ‖S‖ * ‖z‖ := S.le_opNorm z
      _ ≤ ‖S‖ * B := mul_le_mul_of_nonneg_left hz (norm_nonneg S)
  -- softmax 权重 L1-Lipschitz，界作为**该对**的前提（B365）
  have hwlip : ∀ (u v : E), ‖u‖ ≤ B → ‖v‖ ≤ B →
      (∑ j : Fin k, |softmax (S u) j - softmax (S v) j|)
        ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) * ‖u - v‖ := by
    intro u v hu hv
    have h1 := weight_l1_diff_bound (k := k) M' hM' (S u) (S v)
      (fun j => abs_le.mp (hscore u hu j)) (fun j => abs_le.mp (hscore v hv j))
    have h2 := score_lin_lipschitz S u v
    have hcoef : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') := by positivity
    calc
      (∑ j : Fin k, |softmax (S u) j - softmax (S v) j|)
          ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (S u - S v) := h1
      _ ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * (‖S‖ * ‖u - v‖) :=
            mul_le_mul_of_nonneg_left h2 hcoef
      _ = ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) * ‖u - v‖ := by ring
  have hmain := cross_attention_lipschitz_in_query (w := fun z j => softmax (S z) j) V M
    ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) B
    (fun z j => softmax_nonneg (S z) j) (fun z => softmax_sum_one (S z)) hwlip hM x y hBx hBy
  simpa [M'] using hmain

/-! ## encoder–decoder 块组装

decoder 块（自注意力 + 交叉注意力 + FFN + RMSNorm/FFN 包装 `F`）作用于
encoder 块输出：

  `encoderDecoderOutput enc F A_self A_cross G x`
    = `F (enc x + (A_self (enc x) + A_cross (enc x)) + G (enc x))`

交叉注意力项 `A_cross` **并入加法组合**（与 `A_self` 相加），故组装骨架与
`RealMixedAttention.mixed_block_lipschitz` 完全一致：只看各组件的 Lipschitz
常数，不看注意力权重的来源（双向 / 因果 / 交叉）。 -/

/-- encoder–decoder 块输出：encoder 块 `enc` 的输出作为 decoder 块的输入，
decoder 块 = `F ∘ (id + A_self + A_cross + G)`。 -/
def encoderDecoderOutput (enc Fd Aself Across G : E → E) (x : E) : E :=
  Fd (enc x + (Aself (enc x) + Across (enc x)) + G (enc x))

/-- 定理九（核心/组装）：encoder–decoder 块的 Lipschitz 界。
encoder 块 `Le`-Lipschitz、decoder 包装 `Fd` 为 `Lf`、自注意力 `La_s`、
交叉注意力 `La_c`、FFN `Lg`-Lipschitz（常数非负）⟹ 整个 encoder–decoder 块是
`Lf·(1 + La_s + La_c + Lg)·Le`-Lipschitz。

证明路线：`A_self + A_cross` 是 `(La_s + La_c)`-Lipschitz
（`RealBlockLipschitz.lipschitz_add`，交叉项并入加法组合）⟹ decoder 内层
`id + (A_self + A_cross) + G` 经 `block_lipschitz_bound` 得
`Lf·(1 + (La_s+La_c) + Lg)` ⟹ 再与 encoder 块复合（`lipschitz_comp` 的
常数相乘模式，因组合常数非负）。 -/
theorem encoder_decoder_block_bound (enc Fd Aself Across G : E → E)
    (Le Lf La_s La_c Lg : ℝ)
    (henc : ∀ x y, ‖enc x - enc y‖ ≤ Le * ‖x - y‖)
    (hF : ∀ x y, ‖Fd x - Fd y‖ ≤ Lf * ‖x - y‖)
    (hAs : ∀ x y, ‖Aself x - Aself y‖ ≤ La_s * ‖x - y‖)
    (hAc : ∀ x y, ‖Across x - Across y‖ ≤ La_c * ‖x - y‖)
    (hG : ∀ x y, ‖G x - G y‖ ≤ Lg * ‖x - y‖)
    (hLf : 0 ≤ Lf) (hLa : 0 ≤ La_s + La_c) (hLg : 0 ≤ Lg) :
    ∀ x y, ‖encoderDecoderOutput enc Fd Aself Across G x
        - encoderDecoderOutput enc Fd Aself Across G y‖
      ≤ (Lf * (1 + La_s + La_c + Lg) * Le) * ‖x - y‖ := by
  -- 自注意力 + 交叉注意力：La_s + La_c
  have hA : ∀ x y, ‖(Aself x + Across x) - (Aself y + Across y)‖
      ≤ (La_s + La_c) * ‖x - y‖ :=
    lipschitz_add Aself Across La_s La_c hAs hAc
  have hblock := block_lipschitz_bound Fd (fun z => Aself z + Across z) G Lf
    (La_s + La_c) Lg hF hA hG hLf
  have hC0 : 0 ≤ Lf * (1 + (La_s + La_c) + Lg) :=
    mul_nonneg hLf (by linarith)
  intro x y
  calc
    ‖encoderDecoderOutput enc Fd Aself Across G x
        - encoderDecoderOutput enc Fd Aself Across G y‖
        = ‖Fd (enc x + (Aself (enc x) + Across (enc x)) + G (enc x))
            - Fd (enc y + (Aself (enc y) + Across (enc y)) + G (enc y))‖ := rfl
    _ ≤ (Lf * (1 + (La_s + La_c) + Lg)) * ‖enc x - enc y‖ := hblock (enc x) (enc y)
    _ ≤ (Lf * (1 + (La_s + La_c) + Lg)) * (Le * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (henc x y) hC0
    _ = (Lf * (1 + La_s + La_c + Lg) * Le) * ‖x - y‖ := by ring

/-- 推论：encoder 块 + 任一 `Ld`-Lipschitz decoder 块（抽象，不展开内部结构）
的复合界 `Ld·Le`（`lipschitz_comp` 的常数相乘；需要 `0 ≤ Ld` 使组合常数
非负——Lipschitz 常数的自然前提）。 -/
theorem encoder_decoder_comp_bound (enc dec : E → E) (Le Ld : ℝ)
    (henc : ∀ x y, ‖enc x - enc y‖ ≤ Le * ‖x - y‖)
    (hdec : ∀ x y, ‖dec x - dec y‖ ≤ Ld * ‖x - y‖) (hLd : 0 ≤ Ld) :
    ∀ x y, ‖dec (enc x) - dec (enc y)‖ ≤ (Ld * Le) * ‖x - y‖ :=
  lipschitz_comp dec enc Ld Le hdec henc hLd

end Lattice
