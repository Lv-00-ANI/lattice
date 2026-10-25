import Mathlib
import Lattice.Lib.Attention.RealHighDimRoPE
import Lattice.Lib.Attention.RealRoPE
import Lattice.Lib.Attention.RealALiBi
import Lattice.Lib.Attention.RealRelPosEncoding
/-!
# LATTICE: RoPE 外推（长上下文）—— 频率、角度漂移、NTK 缩放与位置插值

RealRoPE/RealHighDimRoPE 只陈述「训练长度内」的相对位置保点积。
长上下文的关键问题是**外推**：位置 `pos` 超出训练长度时，RoPE 的旋转角
`θ_i = pos · base^{−2i/d}` 继续线性增长，分数是否还可控？

  1. `ropeFreq`/`ropeExtrapolate`（def）：频率 `base^{−2i/d}` 与位置角
     `pos · base^{−2i/d}`（训练长度无关的纯参数化）；
  2. `ropeFreq_pos`/`ropeExtrapolate_zero`/`rope_angle_add`：频率正定、
     位置零角、**角对位置可加**（外推的代数基础）；
  3. `ropeScore`/`driftConst`/`rdot_rotate_diff_le`：分数只依赖相对角度差
     `(b−a)θ`，且对角度差是 `driftConst q k`-Lipschitz
     （`|⟨q, R(φ)k⟩ − ⟨q, R(ψ)k⟩| ≤ C·|φ−ψ|`，由 sin/cos 的 Lipschitz 界推出）；
  4. **`extrapolation_score_drift`（核心）**：外推位置的分数漂移被**旋转角差**
     控制：`|score(a,b) − score(a',b')| ≤ C·|((b'−a') − (b−a))·θ|`
     ——外推分数与训练分布分数的偏差只取决于相对角度的改变量；
  5. **`ntk_scaling_bound`（NTK-aware 缩放）**：`base' = base · s^{d/(d−2)}` 给出
     显式频率关系 `freq_i(base') = freq_i(base) · s^{−2i/(d−2)}`；
     并附**频谱结构保持**（`ropeFreq_antitone`：`base > 1` 时频率关于维度严格
     递减）与 `ntk_scaling_shrinks_freq`（`s > 1`、`i > 0` 时 NTK 缩放使频率变小
     ——波长变长，正是外推友好的方向）。诚实标注：NTK 缩放**不是**「频谱不变」，
     而是「频谱按显式因子逐维缩放的均匀拉伸」；
  6. **`linear_interpolation_bound`（位置插值）**：`pos ↦ pos·r`
     （`r = n_train/n_test ≤ 1`）⟹ 与原始分数的偏差
     `≤ C·|(b−a)θ|·|r−1|`——插值把外推问题化为「相对角度的压缩」；
  7. **`extrapolation_degrades`（构造性反例）**：无缩放时外推**不保分数**：
     `∃ θ a t q k, ⟨R((a+t)θ)q, R(aθ)k⟩ ≠ ⟨R(aθ)q, R(aθ)k⟩`
     （显式见证 `θ=1, a=0, t=π/2, q=(1,0), k=(0,1)`：分数 1 vs 0）；
     `extrapolation_angle_unbounded`：角度 `t·θ` 随 `t` 无界——这正是
     无缩放外推破坏分数稳定的根本原因；
  8. `block_extrapolation_drift`（加分）：把漂移界逐块提升到 RealHighDimRoPE 的
     `blockDot`/`blockRotate`（每块频率 `θ i` 不同，误差按块求和）。

诚实假设（全部显式标注）：`base > 0`、`s > 0` 用于 `Real.rpow` 的代数律；
`2 < d` 用于 NTK 指数分母非零；`driftConst` 是 2D 内积的显式常数
（`|q.x||k.x|+|q.y||k.y|+|q.y||k.x|+|q.x||k.y|`，即 `ℓ¹` 意义上的张量积界的常数）；
`extrapolation_degrades` 的见证是**具体数值**（`π/2` 处的 sin/cos 取值），
不是 `∀` 陈述——它证明「无缩放时存在分数漂移」，而非「对所有位置都漂移」。
模型无关：任意维度、频率、位置；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、频率与位置角 -/

/-- RoPE 的第 `i` 维频率 `base^{−2i/d}`（`i : Fin d`）。 -/
def ropeFreq (base : ℝ) (d : ℕ) (i : Fin d) : ℝ :=
  base ^ (-(2 * (i.val : ℝ)) / (d : ℝ))

/-- RoPE 的第 `i` 维位置角 `pos · base^{−2i/d}`（训练长度无关的纯参数化）。 -/
def ropeExtrapolate (base : ℝ) (d : ℕ) (i : Fin d) (pos : ℝ) : ℝ :=
  pos * ropeFreq base d i

/-- 频率正定（`base > 0`）。 -/
lemma ropeFreq_pos {base : ℝ} (hb : 0 < base) (d : ℕ) (i : Fin d) :
    0 < ropeFreq base d i :=
  Real.rpow_pos_of_pos hb _

/-- 零维频率为 `1`（`i = 0` 时指数为 `0`）。 -/
lemma ropeFreq_zero {base : ℝ} (d : ℕ) (h : 0 < d) :
    ropeFreq base d ⟨0, h⟩ = 1 := by
  unfold ropeFreq
  simp

/-- 位置零 ⟹ 角为零。 -/
lemma ropeExtrapolate_zero (base : ℝ) (d : ℕ) (i : Fin d) :
    ropeExtrapolate base d i 0 = 0 := by
  unfold ropeExtrapolate
  ring

/-- **角关于位置可加**：`angle(p+q) = angle(p) + angle(q)`
（外推的代数基础：位置可加 ⟺ 角度可加，频率是比例常数）。 -/
lemma rope_angle_add (base : ℝ) (d : ℕ) (i : Fin d) (p q : ℝ) :
    ropeExtrapolate base d i (p + q)
      = ropeExtrapolate base d i p + ropeExtrapolate base d i q := by
  unfold ropeExtrapolate
  ring

/-- 同频角差只依赖位置差：`angle(b) − angle(a) = (b−a)·freq`。 -/
lemma rope_angle_sub (base : ℝ) (d : ℕ) (i : Fin d) (a b : ℝ) :
    ropeExtrapolate base d i b - ropeExtrapolate base d i a
      = (b - a) * ropeFreq base d i := by
  unfold ropeExtrapolate
  ring

/-! ## 二、分数对角度差的 Lipschitz 界 -/

/-- RoPE 分数（查询在 `a`、键在 `b`，基频 `θ`）：`⟨R(aθ)q, R(bθ)k⟩`。 -/
def ropeScore (θ a b : ℝ) (q k : Point2R) : ℝ :=
  rdot (rotateR (a * θ) q) (rotateR (b * θ) k)

/-- 2D 内积-旋转的 Lipschitz 常数（`ℓ¹` 张量积形式）。 -/
def driftConst (q k : Point2R) : ℝ :=
  |q.x| * |k.x| + |q.y| * |k.y| + |q.y| * |k.x| + |q.x| * |k.y|

lemma driftConst_nonneg (q k : Point2R) : 0 ≤ driftConst q k := by
  unfold driftConst
  positivity

/-- `|cos φ − cos ψ| ≤ |φ − ψ|`（初等：`cos_sub_cos` 分解 + `|sin| ≤ 1`、`|sin t| ≤ |t|`）。 -/
lemma abs_cos_sub_cos_le (φ ψ : ℝ) : |Real.cos φ - Real.cos ψ| ≤ |φ - ψ| := by
  have h1 : |Real.sin ((φ + ψ) / 2)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : |Real.sin ((φ - ψ) / 2)| ≤ |φ - ψ| / 2 := by
    have h := Real.abs_sin_le_abs (x := (φ - ψ) / 2)
    rw [abs_div] at h
    rw [show |(2 : ℝ)| = 2 by norm_num] at h
    linarith [h]
  have hkey : Real.cos φ - Real.cos ψ
      = 2 * Real.sin ((φ + ψ) / 2) * (-Real.sin ((φ - ψ) / 2)) := by
    rw [Real.cos_sub_cos]
    ring
  rw [hkey]
  have htri : |2 * Real.sin ((φ + ψ) / 2) * (-Real.sin ((φ - ψ) / 2))|
      = 2 * |Real.sin ((φ + ψ) / 2)| * |Real.sin ((φ - ψ) / 2)| := by
    rw [abs_mul, abs_mul, abs_neg, show |(2 : ℝ)| = 2 by norm_num]
  rw [htri]
  calc
    2 * |Real.sin ((φ + ψ) / 2)| * |Real.sin ((φ - ψ) / 2)|
        ≤ 2 * 1 * (|φ - ψ| / 2) := by
          nlinarith [h1, h2, abs_nonneg (Real.sin ((φ + ψ) / 2)),
            abs_nonneg (Real.sin ((φ - ψ) / 2))]
    _ = |φ - ψ| := by ring

/-- `|sin φ − sin ψ| ≤ |φ − ψ|`（同法，用 `sin_sub_sin`）。 -/
lemma abs_sin_sub_sin_le (φ ψ : ℝ) : |Real.sin φ - Real.sin ψ| ≤ |φ - ψ| := by
  have h1 : |Real.cos ((φ + ψ) / 2)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |Real.sin ((φ - ψ) / 2)| ≤ |φ - ψ| / 2 := by
    have h := Real.abs_sin_le_abs (x := (φ - ψ) / 2)
    rw [abs_div] at h
    rw [show |(2 : ℝ)| = 2 by norm_num] at h
    linarith [h]
  have hkey : Real.sin φ - Real.sin ψ
      = 2 * Real.sin ((φ - ψ) / 2) * Real.cos ((φ + ψ) / 2) :=
    Real.sin_sub_sin φ ψ
  rw [hkey]
  have htri : |2 * Real.sin ((φ - ψ) / 2) * Real.cos ((φ + ψ) / 2)|
      = 2 * |Real.sin ((φ - ψ) / 2)| * |Real.cos ((φ + ψ) / 2)| := by
    rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
  rw [htri]
  calc
    2 * |Real.sin ((φ - ψ) / 2)| * |Real.cos ((φ + ψ) / 2)|
        ≤ 2 * (|φ - ψ| / 2) * 1 := by
          nlinarith [h1, h2, abs_nonneg (Real.sin ((φ - ψ) / 2)),
            abs_nonneg (Real.cos ((φ + ψ) / 2))]
    _ = |φ - ψ| := by ring

/-- **旋转角差的分数界**：`|⟨q, R(φ)k⟩ − ⟨q, R(ψ)k⟩| ≤ C·|φ − ψ|`
（展开内积 + `|cos φ − cos ψ| ≤ |φ−ψ|`、`|sin φ − sin ψ| ≤ |φ−ψ|`）。 -/
lemma rdot_rotate_diff_le (φ ψ : ℝ) (q k : Point2R) :
    |rdot q (rotateR φ k) - rdot q (rotateR ψ k)| ≤ driftConst q k * |φ - ψ| := by
  have hcos : |Real.cos φ - Real.cos ψ| ≤ |φ - ψ| := abs_cos_sub_cos_le φ ψ
  have hsin : |Real.sin φ - Real.sin ψ| ≤ |φ - ψ| := abs_sin_sub_sin_le φ ψ
  have hd : 0 ≤ |φ - ψ| := abs_nonneg _
  have hexp : rdot q (rotateR φ k) - rdot q (rotateR ψ k)
      = (q.x * k.x + q.y * k.y) * (Real.cos φ - Real.cos ψ)
        + (q.y * k.x - q.x * k.y) * (Real.sin φ - Real.sin ψ) := by
    unfold rdot rotateR
    ring
  have hA : |q.x * k.x + q.y * k.y| ≤ |q.x| * |k.x| + |q.y| * |k.y| := by
    calc
      |q.x * k.x + q.y * k.y| ≤ |q.x * k.x| + |q.y * k.y| := abs_add _ _
      _ = |q.x| * |k.x| + |q.y| * |k.y| := by rw [abs_mul, abs_mul]
  have hB : |q.y * k.x - q.x * k.y| ≤ |q.y| * |k.x| + |q.x| * |k.y| := by
    calc
      |q.y * k.x - q.x * k.y| = |q.y * k.x + -(q.x * k.y)| := by ring_nf
      _ ≤ |q.y * k.x| + |-(q.x * k.y)| := abs_add _ _
      _ = |q.y| * |k.x| + |q.x| * |k.y| := by rw [abs_neg, abs_mul, abs_mul]
  rw [hexp]
  calc
    |(q.x * k.x + q.y * k.y) * (Real.cos φ - Real.cos ψ)
        + (q.y * k.x - q.x * k.y) * (Real.sin φ - Real.sin ψ)|
        ≤ |(q.x * k.x + q.y * k.y) * (Real.cos φ - Real.cos ψ)|
          + |(q.y * k.x - q.x * k.y) * (Real.sin φ - Real.sin ψ)| := abs_add _ _
    _ = |q.x * k.x + q.y * k.y| * |Real.cos φ - Real.cos ψ|
          + |q.y * k.x - q.x * k.y| * |Real.sin φ - Real.sin ψ| := by
          rw [abs_mul, abs_mul]
    _ ≤ (|q.x| * |k.x| + |q.y| * |k.y|) * |φ - ψ|
          + (|q.y| * |k.x| + |q.x| * |k.y|) * |φ - ψ| :=
          add_le_add
            (mul_le_mul hA hcos (abs_nonneg _) (by positivity))
            (mul_le_mul hB hsin (abs_nonneg _) (by positivity))
    _ = driftConst q k * |φ - ψ| := by
          unfold driftConst
          ring

/-! ## 三、定理一（核心）：外推分数漂移由相对角差控制 -/

/-- **外推分数漂移界**：RoPE 分数只依赖相对角度差（`rope_relative_preserves_dot`），
故两个位置对 `(a,b)` 与 `(a',b')` 的分数差被**相对角差**控制：
`|score(a,b) − score(a',b')| ≤ C·|((b'−a') − (b−a))·θ|`。
外推（`b` 很大）本身不坏；坏的是相对角度差变得很大——这解释了为何长上下文
需要 NTK 缩放或位置插值（把相对角差压回训练范围）。 -/
theorem extrapolation_score_drift (θ a b a' b' : ℝ) (q k : Point2R) :
    |ropeScore θ a b q k - ropeScore θ a' b' q k|
      ≤ driftConst q k * |((b' - a') - (b - a)) * θ| := by
  have h1 : ropeScore θ a b q k = rdot q (rotateR ((b - a) * θ) k) :=
    rope_relative_preserves_dot a b θ q k
  have h2 : ropeScore θ a' b' q k = rdot q (rotateR ((b' - a') * θ) k) :=
    rope_relative_preserves_dot a' b' θ q k
  rw [h1, h2]
  refine le_trans (rdot_rotate_diff_le ((b - a) * θ) ((b' - a') * θ) q k) ?_
  apply mul_le_mul_of_nonneg_left _ (driftConst_nonneg q k)
  rw [show (b - a) * θ - (b' - a') * θ = -(((b' - a') - (b - a)) * θ) from by ring, abs_neg]

/-- 训练长度外的**绝对角度漂移**：位置从 `a` 外推到 `a+t`，相对角改变 `t·θ`；
漂移界的核心因子就是它。 -/
lemma extrapolation_angle_shift (θ a t : ℝ) :
    ((a + t) - a) * θ - (a - a) * θ = t * θ := by
  ring

/-! ## 四、定理二：NTK-aware 缩放 -/

/-- NTK-aware 缩放基：`base' = base · s^{d/(d−2)}`（`d > 2`）。 -/
def ntkScaledBase (base s : ℝ) (d : ℕ) : ℝ :=
  base * s ^ ((d : ℝ) / ((d : ℝ) - 2))

/-- **NTK 频率关系（核心）**：`freq_i(base·s^{d/(d−2)}) = freq_i(base) · s^{−2i/(d−2)}`
——NTK 缩放对每个维度乘一个**显式**因子，指数只依赖维度 `i`。
诚实标注：这不是「频谱不变」；频率被逐维缩放（`ntk_scaling_shrinks_freq`
给出 `s > 1`、`i > 0` 时的缩小方向）。 -/
theorem ntk_scaling_bound (base s : ℝ) (d : ℕ) (i : Fin d)
    (hb : 0 < base) (hs : 0 < s) (hd : 2 < d) :
    ropeFreq (ntkScaledBase base s d) d i
      = ropeFreq base d i * s ^ (-(2 * (i.val : ℝ)) / ((d : ℝ) - 2)) := by
  have hd2 : 0 < (d : ℝ) - 2 := by
    have : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hspos : 0 < s ^ ((d : ℝ) / ((d : ℝ) - 2)) := Real.rpow_pos_of_pos hs _
  have hexp : ((d : ℝ) / ((d : ℝ) - 2)) * (-(2 * (i.val : ℝ)) / (d : ℝ))
      = -(2 * (i.val : ℝ)) / ((d : ℝ) - 2) := by
    have hdne : (d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      exact ne_of_gt this
    field_simp
    ring
  unfold ropeFreq ntkScaledBase
  rw [Real.mul_rpow (le_of_lt hb) (le_of_lt hspos)]
  rw [← Real.rpow_mul (le_of_lt hs)]
  rw [hexp]

/-- **频谱结构保持（严格递减）**：`base > 1` 时频率关于维度 `i` 严格递减
（`i < j ⟹ freq_j < freq_i`）——NTK 缩放改变频率的值，但保持这一单调结构。 -/
theorem ropeFreq_antitone (base : ℝ) (d : ℕ) (hb : 1 < base) (hd : 0 < d) :
    ∀ i j : Fin d, i.val < j.val → ropeFreq base d j < ropeFreq base d i := by
  intro i j hij
  have hb0 : 0 < base := lt_trans zero_lt_one hb
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
  have hpos : 0 < (2 * ((j.val : ℝ) - (i.val : ℝ))) / (d : ℝ) :=
    div_pos (by linarith) hd0
  have hone : 1 < base ^ ((2 * ((j.val : ℝ) - (i.val : ℝ))) / (d : ℝ)) :=
    Real.one_lt_rpow hb hpos
  have hkey : ropeFreq base d i
      = ropeFreq base d j * base ^ ((2 * ((j.val : ℝ) - (i.val : ℝ))) / (d : ℝ)) := by
    unfold ropeFreq
    rw [← Real.rpow_add hb0]
    congr 1
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
    field_simp
    ring
  rw [hkey]
  have hfj : 0 < ropeFreq base d j := Real.rpow_pos_of_pos hb0 _
  nlinarith

/-- **NTK 缩放使频率变小**（`s > 1`、`i > 0`、`base > 1`、`d > 2`）：
波长变长，是外推友好的方向（把远处位置的相对角压小）。 -/
theorem ntk_scaling_shrinks_freq (base s : ℝ) (d : ℕ) (i : Fin d)
    (hb : 1 < base) (hs : 1 < s) (hd : 2 < d) (hi : 0 < i.val) :
    ropeFreq (ntkScaledBase base s d) d i < ropeFreq base d i := by
  have hb0 : 0 < base := lt_trans zero_lt_one hb
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  rw [ntk_scaling_bound base s d i hb0 hs0 hd]
  have hd2 : 0 < (d : ℝ) - 2 := by
    have : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hi' : (0 : ℝ) < (i.val : ℝ) := by exact_mod_cast hi
  have hneg : -(2 * (i.val : ℝ)) / ((d : ℝ) - 2) < 0 := by
    rw [neg_div]
    have hpos2 : 0 < (2 * (i.val : ℝ)) / ((d : ℝ) - 2) :=
      div_pos (by linarith) hd2
    linarith
  have hlt1 : s ^ (-(2 * (i.val : ℝ)) / ((d : ℝ) - 2)) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_neg
      (x := s) (y := 1) (z := -(2 * (i.val : ℝ)) / ((d : ℝ) - 2)) (by norm_num) hs hneg
    rwa [Real.one_rpow] at h
  have hfp : 0 < ropeFreq base d i := Real.rpow_pos_of_pos hb0 _
  calc
    ropeFreq base d i * s ^ (-(2 * (i.val : ℝ)) / ((d : ℝ) - 2))
        < ropeFreq base d i * 1 := mul_lt_mul_of_pos_left hlt1 hfp
    _ = ropeFreq base d i := by ring

/-! ## 五、定理三：位置插值 -/

/-- **位置插值界**：`pos ↦ pos·r`（`r` 为训练/测试长度比）⟹ 分数偏差
`|score(ar,br) − score(a,b)| ≤ C·|(b−a)·θ|·|r−1|`。
插值把「外推」化为「相对角度的线性压缩」（`|r−1|` 因子）。 -/
theorem linear_interpolation_bound (θ a b r : ℝ) (q k : Point2R) :
    |ropeScore θ (a * r) (b * r) q k - ropeScore θ a b q k|
      ≤ driftConst q k * |(b - a) * θ| * |r - 1| := by
  refine le_trans (extrapolation_score_drift θ (a * r) (b * r) a b q k) ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (driftConst_nonneg q k)
  have harg : ((b - a) - (b * r - a * r)) * θ = ((b - a) * θ) * (1 - r) := by ring
  rw [harg, abs_mul, abs_sub_comm (1 : ℝ) r]

/-! ## 六、定理四：无缩放时外推破坏分数（构造性） -/

/-- **角度无界**：`θ > 0` 时位置差 `t` 的外推角 `t·θ` 无界（`∀ B, ∃ t, B < t·θ`）
——无缩放时相对角度持续增长，这是分数不能保持的根本原因。 -/
theorem extrapolation_angle_unbounded (θ : ℝ) (hθ : 0 < θ) (B : ℝ) :
    ∃ t : ℝ, B < t * θ := by
  refine ⟨(B + 1) / θ, ?_⟩
  rw [div_mul_cancel₀ (B + 1) (ne_of_gt hθ)]
  linarith

/-- **无缩放外推破坏分数（构造性反例）**：存在具体参数使外推后的分数改变
（`θ=1, a=0, t=π/2, q=(1,0), k=(0,1)`：外推分数 `1` ≠ 训练分数 `0`）。
这证明「无缩放时外推不保分数」；配合 `extrapolation_angle_unbounded`
说明漂移随位置无界增长（`extrapolation_score_drift` 的界 `C·|Δ角·θ|` 随之放大）。 -/
theorem extrapolation_degrades :
    ∃ θ a t : ℝ, ∃ q k : Point2R,
      rdot (rotateR ((a + t) * θ) q) (rotateR (a * θ) k)
        ≠ rdot (rotateR (a * θ) q) (rotateR (a * θ) k) := by
  refine ⟨1, 0, Real.pi / 2, ⟨1, 0⟩, ⟨0, 1⟩, ?_⟩
  simp only [rdot, rotateR, Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.cos_zero, Real.sin_zero]
  norm_num

/-! ## 七、定理五（加分）：分块 RoPE 的外推漂移 -/

/-- **分块外推漂移**（衔接 RealHighDimRoPE）：每块频率 `θ i` 不同，
外推 `(a,b) → (a',b')` 的分数漂移按块求和：
`|blockDot(R(aθ)q, R(bθ)k) − blockDot(R(a'θ)q, R(b'θ)k)|
 ≤ Σ_i C_i·|((b'−a') − (b−a))·θ i|`，其中 `C_i = driftConst (q i) (k i)`。 -/
theorem block_extrapolation_drift {d : ℕ} (θ : Fin d → ℝ) (a b a' b' : ℝ)
    (q k : Fin d → Point2R) :
    |blockDot (blockRotate (fun i => a * θ i) q) (blockRotate (fun i => b * θ i) k)
        - blockDot (blockRotate (fun i => a' * θ i) q) (blockRotate (fun i => b' * θ i) k)|
      ≤ ∑ i, driftConst (q i) (k i) * |((b' - a') - (b - a)) * θ i| := by
  have h1 : blockDot (blockRotate (fun i => a * θ i) q) (blockRotate (fun i => b * θ i) k)
      = blockDot q (blockRotate (fun i => (b - a) * θ i) k) :=
    block_rope_relative_preserves_dot a b θ q k
  have h2 : blockDot (blockRotate (fun i => a' * θ i) q) (blockRotate (fun i => b' * θ i) k)
      = blockDot q (blockRotate (fun i => (b' - a') * θ i) k) :=
    block_rope_relative_preserves_dot a' b' θ q k
  rw [h1, h2]
  unfold blockDot
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (rdot (q i) (blockRotate (fun i => (b - a) * θ i) k i)
        - rdot (q i) (blockRotate (fun i => (b' - a') * θ i) k i))|
        ≤ ∑ i, |rdot (q i) (blockRotate (fun i => (b - a) * θ i) k i)
            - rdot (q i) (blockRotate (fun i => (b' - a') * θ i) k i)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, driftConst (q i) (k i) * |((b' - a') - (b - a)) * θ i| := by
          apply Finset.sum_le_sum
          intro i _
          refine le_trans (rdot_rotate_diff_le ((b - a) * θ i) ((b' - a') * θ i) (q i) (k i)) ?_
          apply mul_le_mul_of_nonneg_left _ (driftConst_nonneg (q i) (k i))
          rw [show (b - a) * θ i - (b' - a') * θ i
                = -(((b' - a') - (b - a)) * θ i) from by ring, abs_neg]

/-! ## 注：实例化闭环与诚实边界
  · **漂移链**：`ropeFreq`（频率）→ `ropeExtrapolate`（角）→
    `rope_relative_preserves_dot`（相对角）→ `rdot_rotate_diff_le`（分数对角的
    Lipschitz）→ `extrapolation_score_drift`（外推漂移界）。整条链只依赖
    sin/cos 的 Lipschitz 界与 2D 内积展开，无模型假设。
  · **NTK 缩放**：`ntk_scaling_bound` 是**精确恒等式**；
    `ropeFreq_antitone` 与 `ntk_scaling_shrinks_freq` 一起刻画「频谱结构保持
    + 逐维缩放」——**不声称** NTK 缩放保持频谱不变（那是错误的读法）。
  · **位置插值**：`linear_interpolation_bound` 给出 `|r−1|` 的线性因子；
    与 `extrapolation_score_drift` 组合即「插值 = 把相对角差乘 `r`」。
  · **无缩放退化**：`extrapolation_degrades` 是具体见证（`π/2` 处 sin/cos 取值），
    配合 `extrapolation_angle_unbounded` 说明漂移界随位置线性放大。
  · **诚实边界**：`driftConst` 依赖 `q,k` 的 `ℓ¹` 结构，界对 `q,k` 不是一致的；
    `ntk_scaling_bound` 需要 `0 < base`、`0 < s`、`2 < d`
    （`Real.rpow` 代数律的前提）。
  无 sorry/axiom/admit。 -/

end Lattice
