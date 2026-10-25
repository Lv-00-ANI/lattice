import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealDataProcessing
import Lattice.Lib.InfoTheory.RealDPIComplete
import Lattice.Lib.Chain.RealEqualityCharacterization
/-!
# LATTICE: 数据处理不等式（DPI）等号刻画的**正向** —— KL 不变 ⟹ 纤维上比值常值

衔接 `RealDataProcessing`（KL 版 DPI `dp_inequality`、log-sum 工具 `logsum_le`）与
`RealDPIComplete`（后向方向 `dp_eq_of_ratio_constant`、严格下降实例 `dp_strict_of_collapse`）。

`CORRECTIONS.md` 的 B7b / C 节记录：`RealDPIComplete` 只证了等号刻画的**后向**方向
（比值常值 ⟹ KL 不变），**正向**（`KL(pK‖qK) = KL(p‖q) ⟹ 纤维上比值常值`）标注为「未证」。
本文件补上这一缺口，从而把 `RealDPIComplete.ratioConstant` 的刻画补成完整 iff。

**证明路线**（每条输出通道 b 单独分析）：

1. 记 `z_ab = p_a·K_ab`、`z'_ab = q_a·K_ab`、`m_b = Σ_a z_ab = (pK)_b`、`r_b = Σ_a z'_ab = (qK)_b`。
2. `logsum_le`（`RealDataProcessing`）给出逐通道 gap
   `gap_b := Σ_a z_ab·log(z_ab/z'_ab) − m_b·log(m_b/r_b) ≥ 0`；
   且 `Σ_a z_ab·log(z_ab/z'_ab) = Σ_a p_a·K_ab·log(p_a/q_a)`（因 `z_ab/z'_ab = p_a/q_a`），
   对 b 求和用行随机 `Σ_b K_ab = 1` 收缩得 `Σ_b gap_b = KL(p‖q) − KL(pK‖qK) = 0`。
3. 非负和为零 ⟹ 每个 `gap_b = 0`。
4. `logsum_eq_imp_ratio_one`（本文件工具引理，承接 `RealEqualityCharacterization.log_eq_one_sub_inv_iff`）
   把 `gap_b = 0` 化为「每条通道的比值 `z_ab/z'_ab = p_a/q_a` 在该通道内常值」的乘积形式
   `(p_a·K_ab)·r_b = (q_a·K_ab)·m_b`；由 `K_ab > 0` 消去 `K_ab` 得 `p_a·r_b = q_a·m_b`。
5. 对 b 求和并用 `Σ_b r_b = Σ_b m_b = 1` 得 `p_a = q_a`（**比「纤维常值」更强**）。

本文件建立：

  1. `logsum_eq_imp_ratio_one`（**核心工具**）：`logsum_le` 的等号情形 ——
     取等 ⟹ `z_i·(Σz') = z'_i·(Σz)`（即 `A_i = z_i·(Σz')/(z'_i·(Σz)) = 1`）；
  2. `dp_eq_imp_eq`（**核心定理**）：严格正信道下 `KL(pK‖qK) = KL(p‖q) ⟹ p = q`；
  3. `dp_eq_imp_ratio_constant`（**核心定理**）：同假设下 `ratioConstant K p q`
     （`RealDPIComplete.ratioConstant` 的正向方向）；
  4. `dp_eq_iff_ratio_constant`（**完整 iff**）：`KL(pK‖qK) = KL(p‖q) ⟺ ratioConstant K p q`，
     由本文件正向 + `RealDPIComplete.dp_eq_of_ratio_constant` 后向合成。

**诚实边界**（本文件不证 / 不声称的）：

- 全部结果要求**信道严格正**（`∀ a b, 0 < K a b`）与 p、q 严格正概率向量，
  因为工具 `logsum_le` 需要 `z > 0`；非严格正信道（含零列 / 0·log 0 连续延拓）的
  完整 DPI 等号刻画未做，沿用 `RealDataProcessing` / `RealDPIComplete` 的诚实边界。
- 「纤维上比值常值」在本文件被**强化**为 `p = q`（由 `Σp = Σq = 1` 逼出常数 = 1），
  故 `ratioConstant` 的正向由 `dp_eq_imp_eq` 平凡推出；未给出「常数为 1」之外的中间刻画。
- 未做：Rényi / f-散度的等号刻画、非有限状态的一般测度版 DPI 等号。

模型无关：任意有限 k、l。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k l : ℕ}

/-! ## 工具引理：log-sum 不等式取等 ⟹ 每个 `Aᵢ = 1` -/

/-- **log-sum 函数的等号情形（核心工具）**。

设 `z, z' : ι → ℝ` 严格正，且 log-sum 不等式取等：
`(Σz)·log((Σz)/(Σz')) = Σ z·log(z/z')`。则对每个 i 有 `z_i·(Σz') = z'_i·(Σz)`，
即 `A_i := z_i·(Σz')/(z'_i·(Σz)) = 1`。

证明：令 `m = Σz`、`r = Σz'`、`A_i = z_i·r/(z'_i·m) > 0`。由 `RealDataProcessing.logsum_le`
证明内部的恒等式
  `Σ z_i·log A_i = (Σ z_i·log(z_i/z'_i)) − m·log(m/r)`，
取等给出 `Σ z_i·log A_i = 0`。另一方面
  `(A_i = 1) ⟺ log A_i = 1 − A_i⁻¹`（`RealEqualityCharacterization.log_eq_one_sub_inv_iff`），
且每项 `z_i·(1 − A_i⁻¹) ≤ z_i·log A_i`、`Σ z_i·(1 − A_i⁻¹) = 0`，
故差 `Σ (z_i·log A_i − z_i·(1 − A_i⁻¹)) = 0` 而非负逐项，每项为零；
`z_i > 0` 时 `log A_i = 1 − A_i⁻¹`，于是 `A_i = 1`。 -/
lemma logsum_eq_imp_ratio_one {ι : Type*} [Fintype ι] [Nonempty ι] (z z' : ι → ℝ)
    (hz : ∀ i, 0 < z i) (hz' : ∀ i, 0 < z' i)
    (heq : (∑ i, z i) * Real.log ((∑ i, z i) / (∑ i, z' i))
      = ∑ i, z i * Real.log (z i / z' i)) :
    ∀ i, z i * (∑ i, z' i) = z' i * (∑ i, z i) := by
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
    rw [h1, Real.log_mul (ne_of_gt (div_pos (hz i) (hz' i)))
        (ne_of_gt (div_pos hrpos hmpos)),
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
  have heq' : m * Real.log (m / r) = ∑ i, z i * Real.log (z i / z' i) := by
    rw [hm, hr]
    exact heq
  have heq'' : m * (Real.log m - Real.log r) = ∑ i, z i * Real.log (z i / z' i) := by
    have h := heq'
    rw [Real.log_div (ne_of_gt hmpos) (ne_of_gt hrpos)] at h
    exact h
  have hsumA : ∑ i, z i * Real.log (A i) = 0 := by
    rw [hsplit, ← heq'']
    ring
  have hb : ∀ i, z i * (1 - (A i)⁻¹) ≤ z i * Real.log (A i) :=
    fun i => mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (hApos i))
      (le_of_lt (hz i))
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
  have hnn : ∀ i, 0 ≤ z i * Real.log (A i) - z i * (1 - (A i)⁻¹) := by
    intro i
    linarith [hb i]
  have hsumdiff : ∑ i, (z i * Real.log (A i) - z i * (1 - (A i)⁻¹)) = 0 := by
    rw [Finset.sum_sub_distrib, hsumA, hzero, sub_zero]
  have hterm0 : ∀ i, z i * Real.log (A i) - z i * (1 - (A i)⁻¹) = 0 :=
    sum_eq_zero_of_nonneg hnn hsumdiff
  intro i
  have hzlog : z i * Real.log (A i) = z i * (1 - (A i)⁻¹) := by
    linarith [hterm0 i]
  have hlogeq : Real.log (A i) = 1 - (A i)⁻¹ :=
    mul_left_cancel₀ (ne_of_gt (hz i)) hzlog
  have hA1 : A i = 1 := (log_eq_one_sub_inv_iff (hApos i)).mp hlogeq
  have hden : z' i * m ≠ 0 := ne_of_gt (mul_pos (hz' i) hmpos)
  have hprod : z i * r = z' i * m := by
    have := hA1
    rw [hA, div_eq_one_iff_eq hden] at this
    exact this
  exact hprod

/-! ## 核心定理：DPI 取等 ⟺ 纤维上比值常值 -/

/-- **DPI 等号刻画的（正向）方向**，强化形式：严格正信道、严格正概率向量下
`KL(pK‖qK) = KL(p‖q) ⟹ p = q`。

证明路线见文件头说明：逐通道 log-sum 取等（`logsum_eq_imp_ratio_one`）给出
`p_a·r_b = q_a·m_b`，对 b 求和并用 `Σ_b r_b = Σ_b m_b = 1` 收缩得 `p_a = q_a`。 -/
theorem dp_eq_imp_eq (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1)
    (hK : ∀ a b, 0 < K a b) (hKr : ∀ a, ∑ b, K a b = 1)
    (heq : kl (channelPush K p) (channelPush K q) = kl p q) :
    p = q := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hps
  haveI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  -- 逐通道 gap ≥ 0
  have hgap_b : ∀ b, 0 ≤ (∑ a, (p a * K a b) * Real.log ((p a * K a b) / (q a * K a b)))
      - (∑ a, p a * K a b) * Real.log ((∑ a, p a * K a b) / (∑ a, q a * K a b)) := by
    intro b
    have h := logsum_le (fun a => p a * K a b) (fun a => q a * K a b)
      (fun a => mul_pos (hp a) (hK a b)) (fun a => mul_pos (hq a) (hK a b))
    linarith
  -- 总 gap 为零
  have hsum_gap : ∑ b, ((∑ a, (p a * K a b) * Real.log ((p a * K a b) / (q a * K a b)))
      - (∑ a, p a * K a b) * Real.log ((∑ a, p a * K a b) / (∑ a, q a * K a b))) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hR : ∑ b, ∑ a, (p a * K a b) * Real.log ((p a * K a b) / (q a * K a b)) = kl p q := by
      rw [kl_as_sum_log_ratio p q hp hq, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      have hdiv : ∀ b, (p a * K a b) / (q a * K a b) = p a / q a := fun b =>
        mul_div_mul_right (p a) (q a) (ne_of_gt (hK a b))
      rw [Finset.sum_congr rfl (fun b _ => by rw [hdiv b])]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hKr a, mul_one]
    have hL : ∑ b, (∑ a, p a * K a b) * Real.log ((∑ a, p a * K a b) / (∑ a, q a * K a b))
        = kl (channelPush K p) (channelPush K q) := by
      rw [kl_as_sum_log_ratio (channelPush K p) (channelPush K q)
        (fun b => channelPush_pos K p hp hK b)
        (fun b => channelPush_pos K q hq hK b)]
      simp only [channelPush]
    rw [hR, hL, heq, sub_self]
  have hgap0 : ∀ b, (∑ a, (p a * K a b) * Real.log ((p a * K a b) / (q a * K a b)))
      - (∑ a, p a * K a b) * Real.log ((∑ a, p a * K a b) / (∑ a, q a * K a b)) = 0 :=
    sum_eq_zero_of_nonneg hgap_b hsum_gap
  -- 逐通道消去 K_ab：p_a·r_b = q_a·m_b
  have hprod : ∀ b a, p a * (∑ a', q a' * K a' b) = q a * (∑ a', p a' * K a' b) := by
    intro b a
    have heq_b : (∑ a', p a' * K a' b)
          * Real.log ((∑ a', p a' * K a' b) / (∑ a', q a' * K a' b))
        = ∑ a', (p a' * K a' b) * Real.log ((p a' * K a' b) / (q a' * K a' b)) := by
      linarith [hgap0 b]
    have hA := logsum_eq_imp_ratio_one (fun a' => p a' * K a' b) (fun a' => q a' * K a' b)
      (fun a' => mul_pos (hp a') (hK a' b)) (fun a' => mul_pos (hq a') (hK a' b)) heq_b a
    have hcab : (K a b) ≠ 0 := ne_of_gt (hK a b)
    have hcancel : (p a * (∑ a', q a' * K a' b)) * K a b
        = (q a * (∑ a', p a' * K a' b)) * K a b := by
      nlinarith [hA]
    exact mul_right_cancel₀ hcab hcancel
  -- 对 b 求和收缩（Σ_b r_b = Σ_b m_b = 1）
  funext a
  have hsum_b : ∑ b, p a * (∑ a', q a' * K a' b) = ∑ b, q a * (∑ a', p a' * K a' b) :=
    Finset.sum_congr rfl (fun b _ => hprod b a)
  have hsum_r : ∑ b, (∑ a', q a' * K a' b) = 1 := by
    rw [Finset.sum_comm]
    have h : ∀ a', ∑ b, q a' * K a' b = q a' := fun a' => by
      rw [← Finset.mul_sum, hKr a', mul_one]
    rw [Finset.sum_congr rfl (fun a' _ => h a'), hqs]
  have hsum_m : ∑ b, (∑ a', p a' * K a' b) = 1 := by
    rw [Finset.sum_comm]
    have h : ∀ a', ∑ b, p a' * K a' b = p a' := fun a' => by
      rw [← Finset.mul_sum, hKr a', mul_one]
    rw [Finset.sum_congr rfl (fun a' _ => h a'), hps]
  have h2 : p a * (∑ b, (∑ a', q a' * K a' b)) = q a * (∑ b, (∑ a', p a' * K a' b)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact hsum_b
  rw [hsum_r, hsum_m, mul_one, mul_one] at h2
  exact h2

/-- **DPI 等号刻画的（正向）方向**：严格正信道下 KL 不变 ⟹
`RealDPIComplete.ratioConstant K p q`（比值 `p_a/q_a` 在每个信道的纤维上常值）。

由强化定理 `dp_eq_imp_eq`（得 `p = q`）平凡推出。 -/
theorem dp_eq_imp_ratio_constant (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1)
    (hK : ∀ a b, 0 < K a b) (hKr : ∀ a, ∑ b, K a b = 1)
    (heq : kl (channelPush K p) (channelPush K q) = kl p q) :
    ratioConstant K p q := by
  have hpq : p = q := dp_eq_imp_eq p q K hp hps hq hqs hK hKr heq
  intro b a a' _ _
  rw [hpq]
  rw [div_self (ne_of_gt (hq a)), div_self (ne_of_gt (hq a'))]

/-- **DPI 等号刻画的完整 iff**（正向 + 后向）：严格正信道、严格正概率向量下
`KL(pK‖qK) = KL(p‖q) ⟺ ratioConstant K p q`。

正向是 `dp_eq_imp_ratio_constant`，后向是 `RealDPIComplete.dp_eq_of_ratio_constant`。 -/
theorem dp_eq_iff_ratio_constant (p q : Fin k → ℝ) (K : Fin k → Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1)
    (hK : ∀ a b, 0 < K a b) (hKr : ∀ a, ∑ b, K a b = 1) :
    kl (channelPush K p) (channelPush K q) = kl p q ↔ ratioConstant K p q :=
  ⟨dp_eq_imp_ratio_constant p q K hp hps hq hqs hK hKr,
   dp_eq_of_ratio_constant p q K hp hps hq hqs hK hKr⟩

end Lattice
