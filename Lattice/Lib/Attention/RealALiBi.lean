import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Attention.RealSoftmaxLipschitz
import Lattice.Lib.Attention.RealHardAttention
import Lattice.Lib.Optim.RealValueIteration
/-!
# LATTICE: ALiBi 位置编码 —— 有界线性偏置（相对位置单调 + 标准注意力有界扰动）

ALiBi（Attention with Linear Biases）是位置编码的另一条主线，与 RoPE
（RealRoPE：旋转乘法编码，`rope_relative_preserves_dot`）互补：

  * RoPE 把位置信息**乘**进查询/键（旋转正交变换，保点积）；
  * ALiBi 把位置信息**加**进注意力分数：位置 i 的查询对位置 j 的键的分数为
        score(i, j) − m · |i − j|
    其中 m > 0 是斜率超参，|i − j| 是位置距离（这里是 ℕ 上的度量距离 `dist`，
    由 `Nat.dist_eq` 它就是实数 |(i:ℝ) − (j:ℝ)|，等价于数学距离而非截断减法）。

本文件的形式化目标（模型无关：任意位置数 n、任意斜率 m、任意键分数）：

  1. `alibi_bias_monotone`：偏置项相对位置单调 —— 距离越远偏置越小（严格）；
  2. `alibi_bias_lipschitz`：偏置作为键位置的函数是 m-Lipschitz
     （关于 ℕ 上的离散度量 `dist`，即 |j−k| 的整数距离；不是关于实数坐标的
     C¹-Lipschitz —— 该结论只约束相距整数步的键位置之间的差商，
     见 `alibiBias` 的定义处与 `alibi_bias_lipschitz` 本身的陈述。
     三角不等式的度量形式 `abs_dist_sub_le`）；
  3. `alibi_is_bounded_perturbation` / `alibi_score_is_bounded_perturbation`：
     ALiBi 分数 = 标准分数 + 有界扰动，|−m·|i−j|| ≤ m·(n−1)（Fin n 上位置距离有界）；
  4. `alibi_softmax_close_to_standard`（核心衔接定理）：把 ALiBi 归约为
     「标准注意力 + 可量化扰动」—— ALiBi 的 softmax 权重与标准 softmax 权重的差
     由 `softmax_lipschitz_coord`（RealSoftmaxLipschitz，常数 (n+1)·e^{4M}）控制：
         |softmax(ALiBi 分数) − softmax(标准分数)| ≤ (n+1)·e^{4(M+m(n−1))}·m·(n−1)
     这里 M 是标准分数的数据范围假设（诚实假设），m·(n−1) 是扰动幅度；
  5. `alibi_attention_output_bound`：ALiBi 注意力输出仍是 value 的凸组合
     （衔接 RealAttention 的 `attention_output_bound`）；
  6. `alibi_nearer_position_dominates`：相同键分数下，较近位置获得 ≥ 的 softmax
     权重（`softmax_monotone` 保序 + 偏置单调）。

位置距离实现说明：使用 ℕ 上的度量距离 `dist`（mathlib 的 `Dist ℕ` 实例，
`MetricSpace ℕ`），其全套度量引理（`dist_comm`、`dist_triangle`、
`abs_dist_sub_le`、`dist_nonneg`）直接可用；`alibi_dist_cast` 给出它到
`Nat.dist`（截断减法定义，i − j + (j − i)）的实数一致桥。

模型无关：不依赖任何具体模型的维度/层数/训练过程，只依赖位置距离的度量性质
与 softmax 的 Lipschitz 常数（后者来自 RealSoftmaxLipschitz，M 为分数数据范围）。
-/

noncomputable section

namespace Lattice

/-! ## 定义：ALiBi 偏置与 ALiBi 分数 -/

/-- ALiBi 偏置项：−m · dist(i,j)（m 为斜率，dist 为 ℕ 上的度量距离 = |i−j|）。 -/
def alibiBias (m : ℝ) (i j : ℕ) : ℝ := -m * dist i j

/-- ALiBi 分数：标准分数 s(i,j) 减去 m 倍位置距离（查询位置 i 对键位置 j）。 -/
def alibiScores {n : ℕ} (s : Fin n → Fin n → ℝ) (m : ℝ) (i : Fin n) : Fin n → ℝ :=
  fun jj => s i jj - m * dist i.val jj.val

/-! ## 引理：Nat.dist（截断减法定义）到度量距离的桥
(Nat.dist i j : ℝ) = dist i j（两者是同一个数学距离；dist 的定义即
|(i:ℝ) − (j:ℝ)|，见 Nat.dist_eq）。-/

lemma alibi_dist_cast (i j : ℕ) : (Nat.dist i j : ℝ) = dist i j := by
  rw [Nat.dist_eq]
  by_cases h : i ≤ j
  · -- i ≤ j：Nat.dist i j = j − i；|(i:ℝ) − (j:ℝ)| = (j:ℝ) − (i:ℝ)
    rw [Nat.dist_eq_sub_of_le h]
    rw [Nat.cast_sub h]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · -- ¬ i ≤ j：j < i；Nat.dist i j = i − j；|(i:ℝ) − (j:ℝ)| = (i:ℝ) − (j:ℝ)
    have hj : j ≤ i := le_of_not_ge h
    rw [Nat.dist_eq_sub_of_le_right hj]
    rw [Nat.cast_sub hj]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hj))]

/-! ## 定理一：偏置项相对位置单调（m > 0）
对固定查询位置 i，键位置距离越大偏置越小：|i−j| < |i−k| ⟹ −m·|i−j| > −m·|i−k|。-/

theorem alibi_bias_monotone (m : ℝ) (hm : 0 < m) {i j k : ℕ} (h : dist i j < dist i k) :
    alibiBias m i j > alibiBias m i k := by
  unfold alibiBias
  have hmul : m * dist i j < m * dist i k := mul_lt_mul_of_pos_left h hm
  have hneg : -(m * dist i k) < -(m * dist i j) := neg_lt_neg hmul
  simpa [neg_mul] using hneg

/-! ## 定理二：偏置作为键位置的函数 m-Lipschitz（m ≥ 0）
|alibiBias m i j − alibiBias m i k| ≤ m·|j−k|（度量三角不等式 ⟹ 反向三角
`abs_dist_sub_le`）。-/

theorem alibi_bias_lipschitz (m : ℝ) (hm : 0 ≤ m) (i j k : ℕ) :
    |alibiBias m i j - alibiBias m i k| ≤ m * dist j k := by
  unfold alibiBias
  have hrev : |dist i j - dist i k| ≤ dist j k := by
    simpa [dist_comm] using (abs_dist_sub_le (x := j) (y := k) (z := i))
  have hcalc : |(-m) * dist i j - (-m) * dist i k| = m * |dist i j - dist i k| := by
    rw [← mul_sub]
    simp [abs_mul, abs_neg, abs_of_nonneg, hm]
  calc
    |(-m) * dist i j - (-m) * dist i k| = m * |dist i j - dist i k| := hcalc
    _ ≤ m * dist j k := by
      exact mul_le_mul_of_nonneg_left hrev hm

/-! ## 引理：Fin n 上位置距离有界
dist i.val j.val ≤ n − 1（i、j 的 val 都 < n，距离 ≤ 最大值 ≤ n−1）。-/

lemma alibi_fin_dist_le {n : ℕ} (i j : Fin n) : dist i.val j.val ≤ (n - 1 : ℕ) := by
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  rw [Nat.dist_eq]
  have ha : (i.val : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : i.val ≤ n - 1)
  have hb : (j.val : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : j.val ≤ n - 1)
  have ha0 : (0 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast Nat.zero_le i.val
  have hb0 : (0 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast Nat.zero_le j.val
  apply abs_le.mpr
  constructor
  · linarith
  · linarith

/-! ## 定理三：偏置有界（扰动幅度 m·(n−1)）
∀ j : Fin n，|−m·|i−j|| ≤ m·(n−1)（Fin n 的位置距离 ≤ n−1）。-/

theorem alibi_is_bounded_perturbation (m : ℝ) (hm : 0 ≤ m) {n : ℕ} (i : Fin n) :
    ∀ j : Fin n, |alibiBias m i.val j.val| ≤ m * (n - 1 : ℕ) := by
  intro j
  unfold alibiBias
  calc
    |(-m) * dist i.val j.val| = m * dist i.val j.val := by
      simp [abs_mul, abs_neg, abs_of_nonneg, dist_nonneg, hm]
    _ ≤ m * (n - 1 : ℕ) := by
      exact mul_le_mul_of_nonneg_left (alibi_fin_dist_le i j) hm

/-! ## 推论：ALiBi 分数 = 标准分数 + 有界扰动
|alibiScores s m i j − s i j| ≤ m·(n−1)（扰动即偏置项本身）。-/

theorem alibi_score_is_bounded_perturbation (m : ℝ) (hm : 0 ≤ m) {n : ℕ}
    (s : Fin n → Fin n → ℝ) (i j : Fin n) :
    |alibiScores s m i j - s i j| ≤ m * (n - 1 : ℕ) := by
  calc
    |alibiScores s m i j - s i j| = |alibiBias m i.val j.val| := by
      unfold alibiScores alibiBias
      congr 1
      ring
    _ ≤ m * (n - 1 : ℕ) := alibi_is_bounded_perturbation m hm i j

/-! ## 引理：ALiBi 分数有界（衔接 softmax Lipschitz 的输入界）
标准分数 |s(i,j)| ≤ M 且 m ≥ 0 ⟹ ALiBi 分数落在
[−(M + m·(n−1)), M + m·(n−1)]（扰动界 m·(n−1) 叠加到数据范围 M 上）。-/

lemma alibi_score_bounds {n : ℕ} (m M : ℝ) (hm : 0 ≤ m)
    (s : Fin n → Fin n → ℝ) (i : Fin n) (hs : ∀ jj : Fin n, |s i jj| ≤ M) :
    ∀ jj : Fin n,
      -(M + m * (n - 1 : ℕ)) ≤ alibiScores s m i jj ∧ alibiScores s m i jj ≤ M + m * (n - 1 : ℕ) := by
  intro jj
  constructor
  · -- 下界：s ≥ −M 且 m·dist ≤ m·(n−1) ⟹ s − m·dist ≥ −M − m·(n−1)
    have hlo : -M ≤ s i jj := (abs_le.mp (hs jj)).1
    have hd : m * dist i.val jj.val ≤ m * (n - 1 : ℕ) :=
      mul_le_mul_of_nonneg_left (alibi_fin_dist_le i jj) hm
    unfold alibiScores
    linarith
  · -- 上界：s ≤ M 且 m·dist ≥ 0、m·(n−1) ≥ 0 ⟹ s − m·dist ≤ M ≤ M + m·(n−1)
    have hhi : s i jj ≤ M := (abs_le.mp (hs jj)).2
    have hmul : 0 ≤ m * dist i.val jj.val := mul_nonneg hm dist_nonneg
    have hmul2 : 0 ≤ m * (n - 1 : ℕ) := mul_nonneg hm (Nat.cast_nonneg (n - 1))
    unfold alibiScores
    linarith

/-! ## 定理四（核心衔接定理）：ALiBi softmax 权重是标准 softmax 权重的有界扰动
把 ALiBi 归约为「标准注意力 + 可量化扰动」：对固定查询位置 i 与键位置 j，

  |softmax(ALiBi 分数)ⱼ − softmax(标准分数)ⱼ| ≤ (n+1)·e^{4(M+m(n−1))}·m·(n−1)

其中 M 是标准分数的数据范围假设（|s(i,j)| ≤ M），m·(n−1) 是扰动幅度。
证明：ALiBi 分数 = 标准分数 + 扰动（alibi_score_is_bounded_perturbation），
两者都在 [−M', M']（M' = M + m·(n−1)，alibi_score_bounds），
故 softmax_lipschitz_coord（RealSoftmaxLipschitz）给出
坐标 Lipschitz 界 (n+1)·e^{4M'}·LinfNorm(分数差)，而
LinfNorm(ALiBi 分数 − 标准分数) ≤ m·(n−1)（逐坐标扰动界 ⟹ sSup 界）。-/

theorem alibi_softmax_close_to_standard {n : ℕ} [NeZero n] (m M : ℝ) (hm : 0 ≤ m) (hM : 0 ≤ M)
    (s : Fin n → Fin n → ℝ) (i j : Fin n) (hs : ∀ jj : Fin n, |s i jj| ≤ M) :
    |softmax (alibiScores s m i) j - softmax (s i) j|
      ≤ (n + 1) * Real.exp (4 * (M + m * (n - 1 : ℕ))) * (m * (n - 1 : ℕ)) := by
  haveI : Nonempty (Fin n) := ⟨j⟩
  let Mp : ℝ := M + m * (n - 1 : ℕ)
  have hMp : 0 ≤ Mp := by
    dsimp [Mp]
    exact add_nonneg hM (mul_nonneg hm (Nat.cast_nonneg (n - 1)))
  have hx : ∀ jj : Fin n, -Mp ≤ alibiScores s m i jj ∧ alibiScores s m i jj ≤ Mp := by
    intro jj
    have hb := alibi_score_bounds m M hm s i hs jj
    dsimp [Mp] at hb ⊢
    exact hb
  have hy : ∀ jj : Fin n, -Mp ≤ s i jj ∧ s i jj ≤ Mp := by
    intro jj
    have hMle : M ≤ Mp := by
      dsimp [Mp]
      have hmul : 0 ≤ m * (n - 1 : ℕ) := mul_nonneg hm (Nat.cast_nonneg (n - 1))
      linarith
    exact abs_le.mp (le_trans (hs jj) hMle)
  have hlips := softmax_lipschitz_coord Mp (alibiScores s m i) (s i) hMp hx hy j
  have hlinf : LinfNorm (alibiScores s m i - s i) ≤ m * (n - 1 : ℕ) := by
    unfold LinfNorm
    apply csSup_le
    · exact ⟨|(alibiScores s m i - s i) j|, ⟨j, rfl⟩⟩
    · intro b hb
      rcases hb with ⟨jj, rfl⟩
      calc
        |(alibiScores s m i - s i) jj| = |(s i jj - m * dist i.val jj.val) - s i jj| := by
          simp [alibiScores]
        _ = |(-m) * dist i.val jj.val| := by
          congr 1
          ring
        _ = m * dist i.val jj.val := by
          simp [abs_mul, abs_neg, abs_of_nonneg, dist_nonneg, hm]
        _ ≤ m * (n - 1 : ℕ) := by
          exact mul_le_mul_of_nonneg_left (alibi_fin_dist_le i jj) hm
  calc
    |softmax (alibiScores s m i) j - softmax (s i) j|
        ≤ (n + 1) * Real.exp (4 * Mp) * LinfNorm (alibiScores s m i - s i) := hlips
    _ ≤ (n + 1) * Real.exp (4 * Mp) * (m * (n - 1 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hlinf
            (mul_nonneg (by positivity) (le_of_lt (Real.exp_pos (4 * Mp))))

/-! ## 定理五：ALiBi 注意力输出有界（凸组合界）
ALiBi 权重仍是概率分布（softmax 行随机），故注意力输出被最大 value 界住
（与标准注意力共用 RealAttention 的 `attention_output_bound`；模型无关）。-/

theorem alibi_attention_output_bound {n : ℕ} [NeZero n] (m : ℝ)
    (s : Fin n → Fin n → ℝ) (i : Fin n) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Fin n → F) (M : ℝ) (hV : ∀ j : Fin n, ‖V j‖ ≤ M) :
    ‖convComb (softmax (alibiScores s m i)) V‖ ≤ M := by
  exact attention_output_bound (alibiScores s m i) V M hV

/-! ## 定理六：相同键分数下，较近位置胜出（softmax 保序 + 偏置单调）
s(i,j) = s(i,k) 且 |i−j| < |i−k|（j 比 k 更近）⟹ softmax 在 j 的权重 ≥ 在 k 的权重。
（`softmax_monotone`：RealHardAttention 的单坐标保序。）-/

theorem alibi_nearer_position_dominates (m : ℝ) (hm : 0 < m) {n : ℕ} (s : Fin n → Fin n → ℝ)
    (i j k : Fin n) (hs : s i j = s i k) (hclose : dist i.val j.val < dist i.val k.val) :
    softmax (alibiScores s m i) k ≤ softmax (alibiScores s m i) j := by
  haveI : Nonempty (Fin n) := ⟨j⟩
  have hbias := alibi_bias_monotone m hm hclose
  unfold alibiBias at hbias
  have hbias' : -(m * dist i.val k.val) < -(m * dist i.val j.val) := by
    simpa [neg_mul] using hbias
  have hscore : alibiScores s m i k ≤ alibiScores s m i j := by
    unfold alibiScores
    rw [hs]
    linarith [hbias']
  exact softmax_monotone (alibiScores s m i) j k hscore

end Lattice
