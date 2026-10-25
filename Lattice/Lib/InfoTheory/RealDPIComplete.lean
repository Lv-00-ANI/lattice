import Mathlib
import Lattice.Lib.InfoTheory.RealDataProcessing
import Lattice.Lib.InfoTheory.RealEntropyConcavity
/-!
# LATTICE: 数据处理不等式的完备化 —— 信道复合、零列、比值刻画与严格下降

衔接 RealDataProcessing（KL 版 DPI `dp_inequality`、log-sum 工具 `logsum_le`）。
本文件把 DPI 的结构补完整：

  1. `channelComp`：信道复合 (KL)_{ac} = Σ_b K_{ab}·L_{bc}；
     `channelComp_row_sum` / `channelComp_pos`：复合仍行随机、仍严格正；
     `channelPush_comp`（**函子性**）：(p·K)·L = p·(K∘L)；
  2. `channelPush_pos` / `channelPush_sum`：推前分布严格正、和为 1（从 RealDataProcessing
     的证明内联提取为可复用引理）；
  3. `dp_chain`（**核心**）：DPI 的链式复合
     KL(p(K∘L) ‖ q(K∘L)) ≤ KL(pK ‖ qK) ≤ KL(p ‖ q)
     —— 两次信道处理的 KL 下降可加（下降量非负）；
  4. `channelPush_zero_col`：零列 K_{·b} ≡ 0 ⟹ (pK)_b = 0；
     `dp_zero_column_term`：该列在 KL 求和中的项为 0（边界情形的显式处理）；
  5. `ratioConstant`（定义）+ `dp_eq_of_ratio_constant`（**核心后向方向**）：
     若 p_a/q_a 在每个信道的纤维上为常数，则 KL(pK‖qK) = KL(p‖q)
     —— DPI 的**等号刻画后向方向**（等号确实可达）；
  6. `ratioFactorized`（等价表述）+ `ratioConstant_iff_ratioFactorized`：
     「纤维上常值」⟺「存在 c : Fin l → ℝ 使 K_{ab} > 0 时 p_a/q_a = c_b」；
  7. `dpGap` / `dp_gap_nonneg`：把 DPI 写成下降量（gap）非负；
  8. `dp_strict_of_collapse`（**核心严格下降实例**）：单输出信道（l = 1，K ≡ 1）
     把两个不同分布探塌为同一点分布，KL 严格下降为 0：
     KL(pK‖qK) = 0 < KL(p‖q)（p ≠ q）。

**诚实边界**（本文件不证 / 不声称的）：

- **等号刻画的完整 iff（正向：KL(pK‖qK) = KL(p‖q) ⟹ ratioConstant）本文件未证**。
  这条需要 `logsum_le`（RealDataProcessing）的**等号情形分析**：逐输出 b 的
  log-sum 差 `gap_b = Σ_a z_ab·(log A_ab − (1 − A_ab⁻¹))`（A_ab = z_ab·r_b/(z'_ab·m_b)）
  每项非负且 = 0 ⟺ A_ab = 1，故 gap = 0 ⟺ 所有 A_ab = 1（或 z_ab = 0）。
  形式化需要把 `logsum_le` 证明内部的恒等式
  `Σ_a z_ab·(1 − A_ab⁻¹) = 0` 提取出来，并补 `log x = 1 − x⁻¹ ⟹ x = 1` 的等号情形。
  本文件给出**后向方向**（`dp_eq_of_ratio_constant`，完整可证）与**严格下降实例**
  （`dp_strict_of_collapse`），正向刻画标注为后续。这是诚实的降级：本文件不声称 iff。
- `dp_eq_of_ratio_constant` 需要 k ≠ 0（从 Σp = 1 得到）、l ≠ 0（从行随机得到）、
  非空输出纤维的见证点；这些都在证明内部从概率向量/行随机公理导出。
- `dp_strict_of_collapse` 的 K ≡ 1 是严格正信道（满足 `dp_inequality` 的假设），
  但它不是数值稳定的常见信道；它作为「DPI 严格性可达」的清晰实例。
- `dp_zero_column_term` 只处理「整列为零」的退化列（其 KL 项为 0），
  不含零的连续延拓（0·log 0 = 0）在本文件的严格正信道假设下不出现。
- 未做：非严格正信道的完整 DPI（需要 logsum_le 的含零版本）、KL 的
  Rényi 推广、等号刻画的「最大值原理」表述。

模型无关：任意有限 k、l、m。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k l m : ℕ}

/-! ## 定义：信道复合 -/

/-- 信道复合：(K∘L)_{ac} = Σ_b K_{ab}·L_{bc}。 -/
noncomputable def channelComp (K : Fin k → Fin l → ℝ) (L : Fin l → Fin m → ℝ) :
    Fin k → Fin m → ℝ :=
  fun a c => ∑ b, K a b * L b c

/-- 复合信道的行和仍为 1。 -/
lemma channelComp_row_sum (K : Fin k → Fin l → ℝ) (L : Fin l → Fin m → ℝ)
    (hKr : ∀ a, ∑ b, K a b = 1) (hLr : ∀ b, ∑ c, L b c = 1) :
    ∀ a, ∑ c, channelComp K L a c = 1 := by
  intro a
  simp only [channelComp]
  rw [Finset.sum_comm]
  have h : ∀ b, ∑ c, K a b * L b c = K a b := by
    intro b
    rw [← Finset.mul_sum, hLr b, mul_one]
  rw [Finset.sum_congr rfl (fun b _ => h b), hKr a]

/-- 复合信道仍严格正。 -/
lemma channelComp_pos [Nonempty (Fin l)] (K : Fin k → Fin l → ℝ) (L : Fin l → Fin m → ℝ)
    (hK : ∀ a b, 0 < K a b) (hL : ∀ b c, 0 < L b c) :
    ∀ a c, 0 < channelComp K L a c := by
  intro a c
  simp only [channelComp]
  exact Finset.sum_pos (fun b _ => mul_pos (hK a b) (hL b c)) Finset.univ_nonempty

/-- 信道推前的函子性：(p·K)·L = p·(K∘L)。 -/
lemma channelPush_comp (K : Fin k → Fin l → ℝ) (L : Fin l → Fin m → ℝ) (p : Fin k → ℝ) :
    channelPush (channelComp K L) p = channelPush L (channelPush K p) := by
  funext c
  have hL : ∑ a, p a * (∑ b, K a b * L b c)
      = ∑ b, ∑ a, p a * (K a b * L b c) := by
    rw [Finset.sum_congr rfl (fun a _ => by rw [Finset.mul_sum]), Finset.sum_comm]
  have hR : ∑ b, (∑ a, p a * K a b) * L b c
      = ∑ b, ∑ a, (p a * K a b) * L b c :=
    Finset.sum_congr rfl (fun b _ => by rw [Finset.sum_mul])
  simp only [channelPush, channelComp]
  rw [hL, hR]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-! ## 引理：推前分布的正性与归一 -/

lemma channelPush_pos [Nonempty (Fin k)] (K : Fin k → Fin l → ℝ) (p : Fin k → ℝ)
    (hp : ∀ a, 0 < p a) (hK : ∀ a b, 0 < K a b) (b : Fin l) : 0 < channelPush K p b := by
  simp only [channelPush]
  exact Finset.sum_pos (fun a _ => mul_pos (hp a) (hK a b)) Finset.univ_nonempty

lemma channelPush_sum (K : Fin k → Fin l → ℝ) (p : Fin k → ℝ)
    (hKr : ∀ a, ∑ b, K a b = 1) (hps : ∑ a, p a = 1) :
    ∑ b, channelPush K p b = 1 := by
  simp only [channelPush]
  rw [Finset.sum_comm]
  have h : ∀ a, ∑ b, p a * K a b = p a := by
    intro a
    rw [← Finset.mul_sum, hKr a, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => h a), hps]

/-! ## 定理一（核心）：DPI 的链式复合 -/

theorem dp_chain (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ) (L : Fin l → Fin m → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1)
    (hK : ∀ a b, 0 < K a b) (hKr : ∀ a, ∑ b, K a b = 1)
    (hL : ∀ b c, 0 < L b c) (hLr : ∀ b, ∑ c, L b c = 1) :
    kl (channelPush (channelComp K L) p) (channelPush (channelComp K L) q) ≤ kl p q := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hps
  haveI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  rw [channelPush_comp K L p, channelPush_comp K L q]
  have hpK : ∀ b, 0 < channelPush K p b := fun b => channelPush_pos K p hp hK b
  have hpKs : ∑ b, channelPush K p b = 1 := channelPush_sum K p hKr hps
  have hqK : ∀ b, 0 < channelPush K q b := fun b => channelPush_pos K q hq hK b
  have hqKs : ∑ b, channelPush K q b = 1 := channelPush_sum K q hKr hqs
  calc kl (channelPush L (channelPush K p)) (channelPush L (channelPush K q))
      ≤ kl (channelPush K p) (channelPush K q) :=
        dp_inequality (channelPush K p) (channelPush K q) L hpK hpKs hqK hqKs hL hLr
    _ ≤ kl p q := dp_inequality p q K hp hps hq hqs hK hKr

/-! ## 定理二：零列的边界处理 -/

/-- 若第 b 列整列为零，则推前分布的第 b 分量为零。 -/
lemma channelPush_zero_col (K : Fin k → Fin l → ℝ) (p : Fin k → ℝ) (b : Fin l)
    (h : ∀ a, K a b = 0) : channelPush K p b = 0 := by
  simp only [channelPush]
  exact Finset.sum_eq_zero (fun a _ => by rw [h a, mul_zero])

/-- 零列的 KL 项为零：推前分布两侧在该分量都为零。 -/
lemma dp_zero_column_term (K : Fin k → Fin l → ℝ) (p q : Fin k → ℝ) (b : Fin l)
    (h : ∀ a, K a b = 0) :
    channelPush K p b = 0 ∧ channelPush K q b = 0 ∧
      channelPush K p b * Real.log (channelPush K p b / channelPush K q b) = 0 := by
  have hp := channelPush_zero_col K p b h
  have hq := channelPush_zero_col K q b h
  refine ⟨hp, hq, ?_⟩
  rw [hp, zero_div, Real.log_zero, mul_zero]

/-! ## 等号刻画：纤维上常值 ⟹ KL 不变 -/

/-- 比值在信道的每个纤维上常值：
   对任意 b 与任意两个 K_{·b} > 0 的输入 a、a'，有 p_a/q_a = p_{a'}/q_{a'}。 -/
def ratioConstant (K : Fin k → Fin l → ℝ) (p q : Fin k → ℝ) : Prop :=
  ∀ b a a', 0 < K a b → 0 < K a' b → p a / q a = p a' / q a'

/-- 等价表述：存在 c : Fin l → ℝ，使 K_{ab} > 0 时 p_a/q_a = c_b（「因子化」）。 -/
def ratioFactorized (K : Fin k → Fin l → ℝ) (p q : Fin k → ℝ) : Prop :=
  ∃ c : Fin l → ℝ, ∀ a b, 0 < K a b → p a / q a = c b

/-- 两种表述等价（K 严格正、Fin k 非空时；否则空纤维赋予任意常数）。 -/
lemma ratioConstant_iff_ratioFactorized [Nonempty (Fin k)] (K : Fin k → Fin l → ℝ)
    (p q : Fin k → ℝ) (hK : ∀ a b, 0 < K a b) :
    ratioConstant K p q ↔ ratioFactorized K p q := by
  constructor
  · intro hrc
    refine ⟨fun b => p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k)), ?_⟩
    intro a b _
    exact hrc b a (Classical.arbitrary (Fin k)) (hK a b) (hK _ b)
  · rintro ⟨c, hc⟩ b a a' ha ha'
    rw [hc a b ha, hc a' b ha']

/-- **DPI 等号刻画的（后向）方向**：比值在纤维上常值 ⟹ KL 不变。
证明：由常值性 (pK)_b = c_b·(qK)_b（c_b = p_{a₀}/q_{a₀}），故
(pK)_b/(qK)_b = c_b 与 b 无关地等于一个固定常数 c；
KL(pK‖qK) = Σ_b (pK)_b·log c = log c·Σ_b (pK)_b = log c，
KL(p‖q) = Σ_a p_a·log(p_a/q_a) = log c·Σ_a p_a = log c。两者相等。 -/
theorem dp_eq_of_ratio_constant (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1)
    (hK : ∀ a b, 0 < K a b) (hKr : ∀ a, ∑ b, K a b = 1)
    (hrc : ratioConstant K p q) :
    kl (channelPush K p) (channelPush K q) = kl p q := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hps
  haveI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hl : l ≠ 0 := by
    rintro rfl
    have h := hKr (Classical.arbitrary (Fin k))
    simp at h
  obtain ⟨b0⟩ : Nonempty (Fin l) := ⟨⟨0, Nat.pos_of_ne_zero hl⟩⟩
  -- 公共比值
  have hc : ∀ a, p a / q a = p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k)) :=
    fun a => hrc b0 a (Classical.arbitrary (Fin k)) (hK a b0) (hK _ b0)
  -- (pK)_b = c·(qK)_b
  have hratio : ∀ b, channelPush K p b
      = (p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k))) * channelPush K q b := by
    intro b
    simp only [channelPush]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    have h1 : p a
        = (p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k))) * q a :=
      calc p a = (p a / q a) * q a := (div_mul_cancel₀ (p a) (ne_of_gt (hq a))).symm
        _ = (p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k))) * q a := by
              rw [hc a]
    rw [h1]
    ring
  have hqK : ∀ b, 0 < channelPush K q b := fun b => channelPush_pos K q hq hK b
  have hpK : ∀ b, 0 < channelPush K p b := fun b => channelPush_pos K p hp hK b
  have hpKs : ∑ b, channelPush K p b = 1 := channelPush_sum K p hKr hps
  rw [kl_as_sum_log_ratio (channelPush K p) (channelPush K q) hpK hqK, kl_as_sum_log_ratio p q hp hq]
  have hL : ∑ b, channelPush K p b * Real.log (channelPush K p b / channelPush K q b)
      = Real.log (p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k))) := by
    have hterm : ∀ b, channelPush K p b * Real.log (channelPush K p b / channelPush K q b)
        = channelPush K p b
          * Real.log (p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k))) := by
      intro b
      have hdiv : channelPush K p b / channelPush K q b
          = p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k)) := by
        rw [hratio b, mul_div_cancel_right₀ _ (ne_of_gt (hqK b))]
      rw [hdiv]
    rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.sum_mul, hpKs, one_mul]
  have hR : ∑ a, p a * Real.log (p a / q a)
      = Real.log (p (Classical.arbitrary (Fin k)) / q (Classical.arbitrary (Fin k))) := by
    rw [Finset.sum_congr rfl (fun a _ => by rw [hc a]), ← Finset.sum_mul, hps, one_mul]
  rw [hL, hR]

/-! ## 下降量与严格下降实例 -/

/-- DPI 的下降量（gap）：KL(p‖q) − KL(pK‖qK) ≥ 0。 -/
noncomputable def dpGap (K : Fin k → Fin l → ℝ) (p q : Fin k → ℝ) : ℝ :=
  kl p q - kl (channelPush K p) (channelPush K q)

theorem dp_gap_nonneg (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1)
    (hK : ∀ a b, 0 < K a b) (hKr : ∀ a, ∑ b, K a b = 1) :
    0 ≤ dpGap K p q := by
  have h := dp_inequality p q K hp hps hq hqs hK hKr
  unfold dpGap
  linarith

/-- **DPI 的严格下降实例**：单输出信道（l = 1，K ≡ 1）把任意分布探塌为同一点分布，
    故 KL(pK‖qK) = 0；只要 p ≠ q，就有 KL(p‖q) > 0，于是 KL 严格下降。

这是「DPI 一般不是等号」的清晰证据，也是等号刻画正向方向的一个反例锚点。 -/
theorem dp_strict_of_collapse {k : ℕ} (p q : Fin k → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1) (hpq : p ≠ q) :
    kl (channelPush (fun (_ : Fin k) (_ : Fin 1) => (1 : ℝ)) p)
        (channelPush (fun (_ : Fin k) (_ : Fin 1) => (1 : ℝ)) q) < kl p q := by
  have hcolp : channelPush (fun (_ : Fin k) (_ : Fin 1) => (1 : ℝ)) p = fun _ => (1 : ℝ) := by
    funext b
    simp only [channelPush, mul_one]
    exact hps
  have hcolq : channelPush (fun (_ : Fin k) (_ : Fin 1) => (1 : ℝ)) q = fun _ => (1 : ℝ) := by
    funext b
    simp only [channelPush, mul_one]
    exact hqs
  rw [hcolp, hcolq,
    kl_eq_zero_of_eq (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) rfl]
  have hpos := kl_pos_of_ne p q hp hps hq hqs hpq
  linarith

end Lattice
