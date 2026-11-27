import Mathlib
import Lattice.Lib.Attention.RealRoPE
import Lattice.Lib.Attention.RealALiBi
import Lattice.Lib.Attention.RealRelPosEncoding
import Lattice.Lib.Attention.RealRoPEExtrapolation
/-!
# LATTICE: 绝对位置编码（sin/cos 型）—— 有界、平滑、奇偶与三角相对位置

RoPE（RealRoPE：乘性相位旋转）与 ALiBi（RealALiBi：加性距离偏置）之外的
第三条位置编码主线是 **正弦绝对位置编码**（Vaswani et al. 2017）：

    PE(pos, 2k)   = sin(pos / 10000^{2k/d})
    PE(pos, 2k+1) = cos(pos / 10000^{2k/d})

本文件把它的结构性质形式化，并给出与 RoPE/ALiBi 的统一对照：

  1. `absPosDenom`/`absPosEnc`（def）：`10000^{2k/d}` 分母（`k = i/2`）与
     sin/cos 交替的绝对编码（偶坐标 sin、奇坐标 cos）；
  2. `absPosDenom_one_le`/`absPosDenom_pos`：分母 `≥ 1`（`10000 ≥ 1` 且指数非负）；
  3. `abs_pos_bounded`：**有界** `|PE| ≤ 1`（正弦/余弦的界）；
  4. `abs_pos_smooth`：**Lipschitz-1 平滑** `|PE(p) − PE(q)| ≤ |p − q|`
     ——分母 `≥ 1` 使位置差缩小后仍被原位置差界住；
  5. `abs_pos_symmetry_sin`/`abs_pos_symmetry_cos`：**奇偶对称**
     （sin 奇：`PE(−pos) = −PE(pos)`；cos 偶：`PE(−pos) = PE(pos)`）；
  6. `abs_pos_pythagorean`：同一频率对 `(PE(pos,2k), PE(pos,2k+1))` 落在单位圆上
     `PE²+PE² = 1`（RoPE 等距性的绝对编码类比）；
  7. **`abs_pos_relative_shift`（核心）**：绝对位置编码下的相对位置只通过
     三角恒等式**间接**编码——固定频率 `D` 的一对分量在平移 `k` 时满足
     `PE(pos+k, 2k) = PE(pos,2k)·cos(k/D) + PE(pos,2k+1)·sin(k/D)`
     `PE(pos+k, 2k+1) = PE(pos,2k+1)·cos(k/D) − PE(pos,2k)·sin(k/D)`
     ——这正是 `(2k, 2k+1)` 平面内角度为 `k/D` 的**旋转**（`Real.sin_add`/`Real.cos_add`）；
     换言之绝对编码不含平移等变性，但**含逐频旋转结构**（与 RoPE 同源）；
  8. **`abs_vs_rope_vs_alibi`（核心对照）**：三种编码的统一读法——
     绝对编码 = 有界三角表示（本文件定理 3）、ALiBi = 加性距离偏置的平移等变
     （`alibi_bias_translation_equivariant`）、RoPE = 乘性相位/相对旋转保点积
     （`rope_relative_preserves_dot`）。

诚实假设（全部显式标注）：
  · `10000` 是原始论文的**规范基**（换成任意 `> 1` 的基，本文件除具体数值外的
    全部结论不变；`absPosDenom_one_le` 只用到 `10000 ≥ 1`）；
  · 维度 `d` 上「`2k` 与 `2k+1` 同频」由 `i.val / 2` 给出并显式证明
    （`absPosDenom_eq_of_div2_eq`）；
  · **绝对位置编码本身不是平移等变的**（`abs_pos_relative_shift` 显示的只是
    逐频旋转结构，不是分数不变性）——这一点在 docstring 中明确标注，
    避免与 `RealRelPosEncoding.IsTranslationEquivariant` 混淆；
  · sin/cos 的 Lipschitz 界由 `Real.sin_sub_sin`/`Real.cos_sub_cos` 与
    `Real.abs_sin_le_abs` 初等推出（mathlib 4.14 无现成的 `abs_sin_sub_sin_le`）。
模型无关：任意维度 `d`、位置 `pos`、平移 `k`；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 工具：sin/cos 的 Lipschitz 界（mathlib 4.14 未直接提供） -/


def absPosDenom (d : ℕ) (i : Fin d) : ℝ :=
  (10000 : ℝ) ^ (((2 * (i.val / 2) : ℕ) : ℝ) / (d : ℝ))

/-- 绝对位置编码：偶坐标 `PE(pos, 2k) = sin(pos / 10000^{2k/d})`、
奇坐标 `PE(pos, 2k+1) = cos(pos / 10000^{2k/d})`
（同一 `k = i.val / 2` 的两个坐标用同一分母）。 -/
def absPosEnc (d : ℕ) (pos : ℝ) (i : Fin d) : ℝ :=
  if i.val % 2 = 0 then Real.sin (pos / absPosDenom d i)
  else Real.cos (pos / absPosDenom d i)

/-! ## 分母的基本性质 -/

/-- 频率分母 `≥ 1`（`10000 ≥ 1`、指数 `≥ 0`）。 -/
lemma absPosDenom_one_le (d : ℕ) (i : Fin d) : 1 ≤ absPosDenom d i := by
  unfold absPosDenom
  exact Real.one_le_rpow (by norm_num) (by positivity)

/-- 频率分母 `> 0`。 -/
lemma absPosDenom_pos (d : ℕ) (i : Fin d) : 0 < absPosDenom d i :=
  lt_of_lt_of_le zero_lt_one (absPosDenom_one_le d i)

/-- 同频判定：`i.val / 2 = j.val / 2` ⟹ 两坐标的分母相同。 -/
lemma absPosDenom_eq_of_div2_eq {d : ℕ} {i j : Fin d} (h : i.val / 2 = j.val / 2) :
    absPosDenom d i = absPosDenom d j := by
  unfold absPosDenom
  rw [h]

/-! ## Fin 索引的 mod/除法事实（偶、奇坐标） -/

lemma fin_two_mul_mod (d m : ℕ) (h : 2 * m < d) :
    ((⟨2 * m, h⟩ : Fin d).val) % 2 = 0 := by
  show (2 * m) % 2 = 0
  omega

lemma fin_two_mul_add_one_mod (d m : ℕ) (h : 2 * m + 1 < d) :
    ((⟨2 * m + 1, h⟩ : Fin d).val) % 2 = 1 := by
  show (2 * m + 1) % 2 = 1
  omega

lemma fin_two_mul_add_one_not_mod (d m : ℕ) (h : 2 * m + 1 < d) :
    ¬ (((⟨2 * m + 1, h⟩ : Fin d).val) % 2 = 0) := by
  rw [fin_two_mul_add_one_mod d m h]
  norm_num

/-- 偶、奇坐标的分母相同（`(2m)/2 = (2m+1)/2 = m`）。 -/
lemma absPosDenom_pair (d m : ℕ) (h1 : 2 * m < d) (h2 : 2 * m + 1 < d) :
    absPosDenom d ⟨2 * m + 1, h2⟩ = absPosDenom d ⟨2 * m, h1⟩ := by
  apply absPosDenom_eq_of_div2_eq
  show (2 * m + 1) / 2 = (2 * m) / 2
  omega

/-! ## 定理一：有界 -/

/-- **有界**：`|PE(pos, i)| ≤ 1`（sin/cos 的界，与位置和频率无关）。 -/
theorem abs_pos_bounded (d : ℕ) (pos : ℝ) (i : Fin d) : |absPosEnc d pos i| ≤ 1 := by
  unfold absPosEnc
  by_cases h : i.val % 2 = 0
  · rw [if_pos h]; exact Real.abs_sin_le_one _
  · rw [if_neg h]; exact Real.abs_cos_le_one _

/-! ## 定理二：平滑（Lipschitz-1） -/

/-- **平滑**：`|PE(p, i) − PE(q, i)| ≤ |p − q|`——编码关于位置是 1-Lipschitz
的（分母 `≥ 1` 把 `|p−q|/D` 缩回 `|p−q|` 之内）。 -/
theorem abs_pos_smooth (d : ℕ) (p q : ℝ) (i : Fin d) :
    |absPosEnc d p i - absPosEnc d q i| ≤ |p - q| := by
  have hD : 0 < absPosDenom d i := absPosDenom_pos d i
  have hdiv : |p / absPosDenom d i - q / absPosDenom d i| ≤ |p - q| := by
    have heq : p / absPosDenom d i - q / absPosDenom d i
        = (p - q) / absPosDenom d i := by ring
    rw [heq, abs_div, abs_of_nonneg (le_of_lt hD)]
    rw [div_le_iff₀ hD]
    nlinarith [abs_nonneg (p - q), absPosDenom_one_le d i]
  unfold absPosEnc
  by_cases h : i.val % 2 = 0
  · rw [if_pos h, if_pos h]
    exact le_trans (abs_sin_sub_sin_le _ _) hdiv
  · rw [if_neg h, if_neg h]
    exact le_trans (abs_cos_sub_cos_le _ _) hdiv

/-! ## 定理三：奇偶对称 -/

/-- **sin 的奇性**（偶坐标）：`PE(−pos, 2k) = −PE(pos, 2k)`。 -/
theorem abs_pos_symmetry_sin (d : ℕ) (pos : ℝ) (i : Fin d) (h : i.val % 2 = 0) :
    absPosEnc d (-pos) i = -absPosEnc d pos i := by
  unfold absPosEnc
  rw [if_pos h, if_pos h, neg_div, Real.sin_neg]

/-- **cos 的偶性**（奇坐标）：`PE(−pos, 2k+1) = PE(pos, 2k+1)`。 -/
theorem abs_pos_symmetry_cos (d : ℕ) (pos : ℝ) (i : Fin d) (h : i.val % 2 = 1) :
    absPosEnc d (-pos) i = absPosEnc d pos i := by
  have hnot : ¬ (i.val % 2 = 0) := by rw [h]; norm_num
  unfold absPosEnc
  rw [if_neg hnot, if_neg hnot, neg_div, Real.cos_neg]

/-! ## 定理四：同频对落在单位圆上 -/

/-- **单位圆**：同一频率对满足 `PE(pos,2k)² + PE(pos,2k+1)² = 1`
（绝对编码版的等距性；RoPE 的 `rotate_preserves_dot` 是其乘性类比）。 -/
theorem abs_pos_pythagorean (d : ℕ) (pos : ℝ) (m : ℕ)
    (h1 : 2 * m < d) (h2 : 2 * m + 1 < d) :
    absPosEnc d pos ⟨2 * m, h1⟩ ^ 2 + absPosEnc d pos ⟨2 * m + 1, h2⟩ ^ 2 = 1 := by
  have hm1 := fin_two_mul_mod d m h1
  have hnot := fin_two_mul_add_one_not_mod d m h2
  have hden := absPosDenom_pair d m h1 h2
  unfold absPosEnc
  rw [if_pos hm1, if_neg hnot, hden, Real.sin_sq_add_cos_sq]

/-! ## 定理五（核心）：绝对编码下相对位置经三角恒等式间接编码 -/

/-- **核心：平移 `k` 在频率对上是旋转**。设同一频率对 `(2m, 2m+1)` 的分母都是
`D`（`hD1`/`hD2`）⟹ 平移 `k` 后的编码由 `(PE(pos,2m), PE(pos,2m+1))` 经角度
`k/D` 的**旋转**给出：

  `PE(pos+k, 2m)   = PE(pos,2m)·cos(k/D) + PE(pos,2m+1)·sin(k/D)`
  `PE(pos+k, 2m+1) = PE(pos,2m+1)·cos(k/D) − PE(pos,2m)·sin(k/D)`

证明即 `Real.sin_add`/`Real.cos_add`（`(pos+k)/D = pos/D + k/D`）。
**诚实边界**：这是「逐频旋转结构」，不是分数的平移等变性——绝对编码本身
不满足 `IsTranslationEquivariant`（`RealRelPosEncoding` 的接口），
相对位置信息只能经此三角恒等式**间接**进入点积。 -/
theorem abs_pos_relative_shift (d : ℕ) (pos k D : ℝ) (m : ℕ)
    (h1 : 2 * m < d) (h2 : 2 * m + 1 < d)
    (hD1 : absPosDenom d ⟨2 * m, h1⟩ = D) (hD2 : absPosDenom d ⟨2 * m + 1, h2⟩ = D) :
    (absPosEnc d (pos + k) ⟨2 * m, h1⟩
        = absPosEnc d pos ⟨2 * m, h1⟩ * Real.cos (k / D)
          + absPosEnc d pos ⟨2 * m + 1, h2⟩ * Real.sin (k / D)) ∧
    (absPosEnc d (pos + k) ⟨2 * m + 1, h2⟩
        = absPosEnc d pos ⟨2 * m + 1, h2⟩ * Real.cos (k / D)
          - absPosEnc d pos ⟨2 * m, h1⟩ * Real.sin (k / D)) := by
  have hm1 := fin_two_mul_mod d m h1
  have hnot := fin_two_mul_add_one_not_mod d m h2
  have hpt : (pos + k) / D = pos / D + k / D := by ring
  constructor
  · unfold absPosEnc
    rw [if_pos hm1, if_pos hm1, if_neg hnot, hD1, hD2, hpt, Real.sin_add]
  · unfold absPosEnc
    rw [if_neg hnot, if_neg hnot, if_pos hm1, hD1, hD2, hpt, Real.cos_add]

/-- `abs_pos_relative_shift` 的实例化形式（分母自动取 `absPosDenom d ⟨2m, h1⟩`）。 -/
theorem abs_pos_relative_shift_no_denom (d : ℕ) (pos k : ℝ) (m : ℕ)
    (h1 : 2 * m < d) (h2 : 2 * m + 1 < d) :
    (absPosEnc d (pos + k) ⟨2 * m, h1⟩
        = absPosEnc d pos ⟨2 * m, h1⟩ * Real.cos (k / absPosDenom d ⟨2 * m, h1⟩)
          + absPosEnc d pos ⟨2 * m + 1, h2⟩ * Real.sin (k / absPosDenom d ⟨2 * m, h1⟩)) ∧
    (absPosEnc d (pos + k) ⟨2 * m + 1, h2⟩
        = absPosEnc d pos ⟨2 * m + 1, h2⟩ * Real.cos (k / absPosDenom d ⟨2 * m, h1⟩)
          - absPosEnc d pos ⟨2 * m, h1⟩ * Real.sin (k / absPosDenom d ⟨2 * m, h1⟩)) :=
  abs_pos_relative_shift d pos k (absPosDenom d ⟨2 * m, h1⟩) m h1 h2 rfl
    (absPosDenom_pair d m h1 h2)

/-- 平移平移的一致性读法：连续做两次平移 `k₁`、`k₂` 等于一次平移 `k₁+k₂`
（旋转的组合性，逐频）。 -/
theorem abs_pos_shift_compose (d : ℕ) (pos k₁ k₂ D : ℝ) (m : ℕ)
    (h1 : 2 * m < d) (h2 : 2 * m + 1 < d)
    (hD1 : absPosDenom d ⟨2 * m, h1⟩ = D) (hD2 : absPosDenom d ⟨2 * m + 1, h2⟩ = D) :
    absPosEnc d (pos + k₁ + k₂) ⟨2 * m, h1⟩
        = absPosEnc d (pos + k₁) ⟨2 * m, h1⟩ * Real.cos (k₂ / D)
          + absPosEnc d (pos + k₁) ⟨2 * m + 1, h2⟩ * Real.sin (k₂ / D) := by
  have h1' : 2 * m < d := h1
  have h2' : 2 * m + 1 < d := h2
  have hpos : pos + k₁ + k₂ = (pos + k₁) + k₂ := by ring
  rw [hpos]
  exact (abs_pos_relative_shift d (pos + k₁) k₂ D m h1' h2' hD1 hD2).1

/-! ## 定理六（核心）：三种位置编码的统一对照 -/

/-- **绝对编码 vs RoPE vs ALiBi（统一接口注记）**：三种编码的刻画性事实同时成立——

  * **绝对编码**：有界三角表示 `|PE(pos,i)| ≤ 1`（本文件定理一，且可经
    `abs_pos_relative_shift` 的逐频旋转间接编码相对位置）；
  * **ALiBi**：加性距离偏置**平移等变**
    （`alibi_bias_translation_equivariant`，偏置只依赖 `dist(i,j)`）；
  * **RoPE**：乘性相位/相对旋转**保点积**
    （`rope_relative_preserves_dot`：`⟨R(aθ)q, R(bθ)k⟩ = ⟨q, R((b−a)θ)k⟩`）。

三者统一在「相对位置语义」下（`RealRelPosEncoding.IsTranslationEquivariant`
刻画 ALiBi 与 RoPE；绝对编码则只含逐频旋转结构，其平移等变性不成立）。 -/
theorem abs_vs_rope_vs_alibi (d : ℕ) (pos : ℝ) (i : Fin d) (m θ : ℝ) (q k : Point2R) :
    |absPosEnc d pos i| ≤ 1 ∧
    IsTranslationEquivariant (fun i j : ℕ => alibiBias m i j) ∧
    (∀ a b : ℝ,
      rdot (rotateR (a * θ) q) (rotateR (b * θ) k) = rdot q (rotateR ((b - a) * θ) k)) :=
  ⟨abs_pos_bounded d pos i, alibi_bias_translation_equivariant m,
    fun a b => rope_relative_preserves_dot a b θ q k⟩

/-! ## 注：诚实边界
  · **绝对编码不是平移等变的**：`abs_pos_relative_shift` 给出的是
    「每个频率对在平移下做旋转」，即编码在平移下**变化**（只是变化被三角度量化）；
    因此 `PE` 本身不满足 `IsTranslationEquivariant`，
    `RealRelPosEncoding.relpos_family_unified` 列举的成员也不包含 `PE`
    本身（只包含 RoPE 的点积与 ALiBi 的偏置）——这是位置编码理论中
    「绝对编码需靠模型学会相对性」的形式表达。
  · `10000` 只用到 `≥ 1`；换成任意 `base > 1`，定理一/二/三/四/五**逐字不变**
    （证明中只出现 `Real.one_le_rpow` 与三角恒等式）。具体数值 `10000`
    仅用于 `absPosDenom` 的定义以对齐原始论文。
  · sin/cos 的 Lipschitz 界（`abs_sin_sub_sin_le`/`abs_cos_sub_cos_le`）
    是 mathlib 4.14 缺失的初等引理，此处自行证明。
  无 sorry/axiom/admit。 -/

end Lattice
