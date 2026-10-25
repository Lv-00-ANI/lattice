import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealFDivergence
/-!
# LATTICE: 数据处理不等式 —— KL 与全变差经信道不增

信息论线的又一块基石（衔接 RealKL 的 KL、RealFDivergence 的 tv）：
有限状态**马尔可夫核**（信道）K : Fin k → Fin l → ℝ 满足 K ≥ 0 且每行和为 1
（`markov_row_sum`），把输入分布 p 推到输出分布

    (pK)_b = Σ_a p_a·K_ab        （`channelPush`）

**数据处理不等式（DPI）**：任何信道的处理都不会增加分布之间的可辨识度：

    KL(pK ‖ qK) ≤ KL(p ‖ q)      （`dp_inequality`）

证明路线是**逐输出符号的 log-sum 不等式**：对每个 b，令 z_a = p_a·K_ab、z'_a = q_a·K_ab，
由 `logsum_le`（一般形式的 log-sum，Z ≥ 0、Z' > 0）

    (Σ_a z_a)·log((Σ_a z_a)/(Σ_a z'_a)) ≤ Σ_a z_a·log(z_a/z'_a)

即 (pK)_b·log((pK)_b/(qK)_b) ≤ Σ_a p_a·K_ab·log(p_a/q_a)；对 b 求和后用
Σ_b K_ab = 1 收缩，得 KL(pK‖qK) ≤ Σ_a p_a·log(p_a/q_a) = KL(p‖q)。

本文件建立：

  1. `channelPush`：信道的推前分布 (pK)_b = Σ_a p_a·K_ab；
  2. `logsum_le`（核心工具）：一般 log-sum 不等式（z 严格正、z' 严格正）
     (Σz)·log((Σz)/(Σz')) ≤ Σ z·log(z/z')；
  3. `dp_inequality`（核心定理）：KL(pK‖qK) ≤ KL(p‖q)
     （K 严格正、p、q 严格正概率向量）；
  4. `dp_eq_of_eq`：p = q ⟹ KL(pK‖qK) = KL(p‖q)（平凡方向）；
  5. `tv_data_processing`：全变差版 DPI，TV(pK, qK) ≤ TV(p, q)
     （用三角不等式 `Finset.abs_sum_le_sum_abs`，与 KL 版不同路线）；
  6. `tv_eq_sum_abs`：0 < p a 时 tv p q = Σ_a |q_a − p_a|（把 f-散度记号写成 L¹ 距离）。

**诚实边界**（本文件不证 / 不声称的）：

- `dp_inequality` 要求信道**严格正**（K_ab > 0）与 p、q 严格正。一般非负信道下
  p_a·K_ab 可能为 0，而本文件的 `logsum_le` 需要 z_a > 0；含零的边界情形
  （0·log 0 = 0 的连续延拓）标注为后续，未在此声称。
- **等号刻画 `dp_eq_iff`（KL(pK‖qK) = KL(p‖q) ⟺ p = q）本文件未证明**，标注为后续。
  数学上它是真的：等号要求每个 b 的 log-sum 取等，即 (p_a·K_ab)/(q_a·K_ab) = p_a/q_a
  对所有 a 相同，从而 p_a/q_a 与 b 无关、由 Σp = Σq = 1 得比值 1，故 p = q。
  但形式化需要 log-sum 等号情形的精细分析（Aᵢ = 1 的强制），超出本文件范围。
  本文件只给出平凡方向 `dp_eq_of_eq`。
- `tv_data_processing` 的 TV 用 RealFDivergence.tv（= Σ|q_a − p_a|，未除 2），
  因此不等式是 TV(pK,qK) ≤ TV(p,q)；若用半和约定，两侧同因子，不等式不变。
  它同样要求 K 严格正（为使 pK 分量严格正、从而可写成 L¹ 距离 Σ|qK_b − pK_b|；
  三角不等式本身只需 K ≥ 0）。一般非负信道的退化情形标注为后续。
  相反，TV 版**不需要** q 的正性或归一（对任意 q 成立），故其陈述比 KL 版更弱假设。

模型无关：任意有限 k、l。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k l : ℕ}

/-! ## 定义：马尔可夫核的推前分布 -/

/-- 信道的推前分布：(pK)_b = Σ_a p_a·K_ab。 -/
noncomputable def channelPush (K : Fin k → Fin l → ℝ) (p : Fin k → ℝ) : Fin l → ℝ :=
  fun b => ∑ a, p a * K a b

/-- 每行和为 1（行随机）的记号性引理（信道公理）。 -/
lemma markov_row_sum (K : Fin k → Fin l → ℝ) (hKrow : ∀ a, ∑ b, K a b = 1) (a : Fin k) :
    ∑ b, K a b = 1 := hKrow a

/-! ## 工具引理：一般 log-sum 不等式

z, z' 严格正 ⟹ (Σz)·log((Σz)/(Σz')) ≤ Σ z·log(z/z')。
证明：令 m = Σz、r = Σz'、Aᵢ = zᵢ·r/(z'ᵢ·m)，差值 = Σ zᵢ·log Aᵢ
≥ Σ zᵢ·(1 − Aᵢ⁻¹) = m − (m/r)·Σz'ᵢ = 0（`Real.one_sub_inv_le_log_of_pos`）。 -/

lemma logsum_le {ι : Type*} [Fintype ι] [Nonempty ι] (z z' : ι → ℝ)
    (hz : ∀ i, 0 < z i) (hz' : ∀ i, 0 < z' i) :
    (∑ i, z i) * Real.log ((∑ i, z i) / (∑ i, z' i))
      ≤ ∑ i, z i * Real.log (z i / z' i) := by
  have hmpos : 0 < ∑ i, z i :=
    Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
  have hrpos : 0 < ∑ i, z' i :=
    Finset.sum_pos (fun i _ => hz' i) Finset.univ_nonempty
  set m : ℝ := ∑ i, z i with hm
  set r : ℝ := ∑ i, z' i with hr
  set A : ι → ℝ := fun i => z i * r / (z' i * m) with hA
  have hApos : ∀ i, 0 < A i :=
    fun i => div_pos (mul_pos (hz i) hrpos) (mul_pos (hz' i) hmpos)
  have hlogA : ∀ i, Real.log (A i)
      = (Real.log (z i) - Real.log (z' i)) + (Real.log r - Real.log m) := by
    intro i
    have h1 : A i = (z i / z' i) * (r / m) := by
      rw [hA]
      exact (div_mul_div_comm (z i) (z' i) r m).symm
    rw [h1, Real.log_mul (ne_of_gt (div_pos (hz i) (hz' i))) (ne_of_gt (div_pos hrpos hmpos)),
      Real.log_div (ne_of_gt (hz i)) (ne_of_gt (hz' i)),
      Real.log_div (ne_of_gt hrpos) (ne_of_gt hmpos)]
  have hsplit : ∑ i, z i * Real.log (A i)
      = (∑ i, z i * Real.log (z i / z' i)) + m * (Real.log r - Real.log m) := by
    have hterm : ∀ i, z i * Real.log (A i)
        = z i * Real.log (z i / z' i) + z i * (Real.log r - Real.log m) := by
      intro i
      rw [hlogA i, Real.log_div (ne_of_gt (hz i)) (ne_of_gt (hz' i))]
      ring
    calc ∑ i, z i * Real.log (A i)
        = ∑ i, (z i * Real.log (z i / z' i) + z i * (Real.log r - Real.log m)) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, z i * Real.log (z i / z' i)) + ∑ i, z i * (Real.log r - Real.log m) :=
          Finset.sum_add_distrib
      _ = (∑ i, z i * Real.log (z i / z' i)) + (∑ i, z i) * (Real.log r - Real.log m) := by
          rw [Finset.sum_mul]
      _ = (∑ i, z i * Real.log (z i / z' i)) + m * (Real.log r - Real.log m) := by
          rw [← hm]
  have hdecomp : (∑ i, z i * Real.log (z i / z' i)) - m * Real.log (m / r)
      = ∑ i, z i * Real.log (A i) := by
    rw [hsplit, Real.log_div (ne_of_gt hmpos) (ne_of_gt hrpos)]
    ring
  have hb : ∀ i, z i * (1 - (A i)⁻¹) ≤ z i * Real.log (A i) := by
    intro i
    exact mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (hApos i)) (le_of_lt (hz i))
  have hzero : ∑ i, z i * (1 - (A i)⁻¹) = 0 := by
    have hAinv : ∀ i, (A i)⁻¹ = z' i * m / (z i * r) := by
      intro i
      rw [hA, inv_div]
    have hterm : ∀ i, z i * (1 - (A i)⁻¹) = z i - (m / r) * z' i := by
      intro i
      rw [hAinv i]
      field_simp [ne_of_gt (hz i), ne_of_gt hrpos]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
    have h1 : (∑ i, z i) = m := hm.symm
    have h2 : (∑ i, (m / r) * z' i) = m := by
      rw [← Finset.mul_sum]
      rw [show (∑ i, z' i) = r from hr.symm, div_mul_cancel₀ m (ne_of_gt hrpos)]
    rw [h1, h2, sub_self]
  have hlow : 0 ≤ ∑ i, z i * Real.log (A i) := by
    calc 0 = ∑ i, z i * (1 - (A i)⁻¹) := hzero.symm
      _ ≤ ∑ i, z i * Real.log (A i) := Finset.sum_le_sum (fun i _ => hb i)
  have hD : 0 ≤ (∑ i, z i * Real.log (z i / z' i)) - m * Real.log (m / r) := by
    rw [hdecomp]
    exact hlow
  linarith

/-! ## 定理一（核心）：KL 的数据处理不等式

KL(pK‖qK) ≤ KL(p‖q)。逐输出 b 用 `logsum_le`（z_a = p_a·K_ab），
再用 Σ_b K_ab = 1 收缩内层求和。 -/

theorem dp_inequality (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1)
    (hK : ∀ a b, 0 < K a b) (hKrow : ∀ a, ∑ b, K a b = 1) :
    kl (channelPush K p) (channelPush K q) ≤ kl p q := by
  have hexp : ∃ a, p a ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : ∑ a, p a = 0 := Finset.sum_eq_zero (fun a _ => h a)
    rw [hps] at hz
    norm_num at hz
  have hexq : ∃ a, q a ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : ∑ a, q a = 0 := Finset.sum_eq_zero (fun a _ => h a)
    rw [hqs] at hz
    norm_num at hz
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hps
  haveI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hpK : ∀ b, 0 < channelPush K p b := by
    obtain ⟨a0, ha0⟩ := hexp
    intro b
    have h : 0 < ∑ a, p a * K a b :=
      Finset.sum_pos (fun a _ => mul_pos (hp a) (hK a b)) ⟨a0, Finset.mem_univ a0⟩
    simpa [channelPush] using h
  have hqK : ∀ b, 0 < channelPush K q b := by
    obtain ⟨a0, ha0⟩ := hexq
    intro b
    have h : 0 < ∑ a, q a * K a b :=
      Finset.sum_pos (fun a _ => mul_pos (hq a) (hK a b)) ⟨a0, Finset.mem_univ a0⟩
    simpa [channelPush] using h
  rw [kl_as_sum_log_ratio (channelPush K p) (channelPush K q) hpK hqK,
    kl_as_sum_log_ratio p q hp hq]
  calc ∑ b, channelPush K p b * Real.log (channelPush K p b / channelPush K q b)
      = ∑ b, (∑ a, p a * K a b)
          * Real.log ((∑ a, p a * K a b) / (∑ a, q a * K a b)) := by
        simp only [channelPush]
    _ ≤ ∑ b, ∑ a, (p a * K a b) * Real.log ((p a * K a b) / (q a * K a b)) := by
        apply Finset.sum_le_sum
        intro b _
        exact logsum_le (fun a => p a * K a b) (fun a => q a * K a b)
          (fun a => mul_pos (hp a) (hK a b)) (fun a => mul_pos (hq a) (hK a b))
    _ = ∑ a, p a * Real.log (p a / q a) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        have hdiv : ∀ b, (p a * K a b) / (q a * K a b) = p a / q a := fun b =>
          mul_div_mul_right (p a) (q a) (ne_of_gt (hK a b))
        rw [Finset.sum_congr rfl (fun b _ => by rw [hdiv b])]
        rw [← Finset.sum_mul, ← Finset.mul_sum, hKrow a, mul_one]

/-! ## 推论：p = q ⟹ 处理前后 KL 相等（等号刻画的平凡方向） -/

theorem dp_eq_of_eq (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ) (hpq : p = q) :
    kl (channelPush K p) (channelPush K q) = kl p q := by
  rw [hpq]
  unfold kl entropy
  ring

/-! ## 引理：0 < p a 时 tv p q = Σ_a |q_a − p_a|

RealFDivergence.tv p q = Σ_a p_a·|q_a/p_a − 1|；p_a > 0 时 p_a·|x| = |p_a·x|，
且 p_a·(q_a/p_a − 1) = q_a − p_a。 -/

lemma tv_eq_sum_abs (p q : Fin k → ℝ) (hp : ∀ a, 0 < p a) :
    tv p q = ∑ a, |q a - p a| := by
  unfold tv fDivergence
  apply Finset.sum_congr rfl
  intro a _
  have h2 : p a * (q a / p a - 1) = q a - p a := by
    field_simp [ne_of_gt (hp a)]
  calc p a * |q a / p a - 1| = |p a * (q a / p a - 1)| := by
        rw [abs_mul, abs_of_pos (hp a)]
    _ = |q a - p a| := by rw [h2]

/-! ## 定理二：全变差的数据处理不等式

TV(pK, qK) ≤ TV(p, q)。路线：|Σ_a (q_a − p_a)·K_ab| ≤ Σ_a |q_a − p_a|·K_ab
（三角不等式），对 b 求和后用 Σ_b K_ab = 1 收缩。K 只需非负。 -/

theorem tv_data_processing (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hK : ∀ a b, 0 < K a b) (hKrow : ∀ a, ∑ b, K a b = 1) :
    tv (channelPush K p) (channelPush K q) ≤ tv p q := by
  have hexp : ∃ a, p a ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : ∑ a, p a = 0 := Finset.sum_eq_zero (fun a _ => h a)
    rw [hps] at hz
    norm_num at hz
  obtain ⟨a0, ha0⟩ := hexp
  have hpK : ∀ b, 0 < channelPush K p b := by
    intro b
    have h : 0 < ∑ a, p a * K a b :=
      Finset.sum_pos (fun a _ => mul_pos (hp a) (hK a b)) ⟨a0, Finset.mem_univ a0⟩
    simpa [channelPush] using h
  rw [tv_eq_sum_abs (channelPush K p) (channelPush K q) hpK, tv_eq_sum_abs p q hp]
  calc ∑ b, |channelPush K q b - channelPush K p b|
      = ∑ b, |∑ a, (q a - p a) * K a b| := by
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        simp only [channelPush]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ b, ∑ a, |q a - p a| * K a b := by
        apply Finset.sum_le_sum
        intro b _
        calc |∑ a, (q a - p a) * K a b| ≤ ∑ a, |(q a - p a) * K a b| := by
              simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun a => (q a - p a) * K a b))
          _ ≤ ∑ a, |q a - p a| * K a b := by
              apply Finset.sum_le_sum
              intro a _
              rw [abs_mul, abs_of_nonneg (le_of_lt (hK a b))]
    _ = ∑ a, |q a - p a| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum, hKrow a, mul_one]

end Lattice
