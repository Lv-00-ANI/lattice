import Mathlib
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: 学习率调度下的收敛率 —— 多项式衰减、有限和界与 √t 调度

RealConvergence 给出**常数收缩**系数下的几何收敛（e(n+1) ≤ c·e(n)，c < 1）。
真实训练使用**衰减学习率** η_t = η₀/(t+1)^p，收缩系数趋近 1。本文件给出
这套衰减调度下可证、可用的定量结构：

  · poly_decay_summable：p > 1 ⟹ Σ 1/(t+1)^p < ∞（引用 mathlib
    Real.summable_one_div_nat_rpow + 指标平移）；
  · linear_lr_not_summable：η_t = η₀/(t+1)（p = 1 调和调度）不可求和
    （Σ η_t = ∞）—— 衰减「太慢」；
  · small_error_of_summable_weighted（核心序列推论）：若 e ≥ 0、η ≥ 0、
    Σ η_t·e_t 收敛而 Σ η_t 发散，则 ∀ ε > 0，∃ n，e_n < ε
    （反证 + 比较判别法：若 e_n ≥ ε 恒成立则 η_t·e_t ≥ ε·η_t 迫使 Σ η_t 收敛）；
  · harmonic_lr_small_error：η_t = η₀/(t+1) 时的特化；
  · lr_decay_antitone / decay_product_bound：单步收缩 e(n+1) ≤ (1-η_n)e_n
    （0 ≤ η_n ≤ 1）⟹ e 单调不增，且 e_N ≤ e_0·∏_{t<N}(1-η_t)（有限乘积上界）；
  · lr_decay_finite_phase：若前 N 步 η_t ≥ c > 0，则 e_N ≤ (1-c)^N·e_0
    （「几何阶段」有限时间保证）；
  · constant_lr_converges：η_t ≡ η₀ ∈ (0,1) 时回收 RealConvergence 的
    ε-终止（连接既有抽象收敛骨架）；
  · product_exp_bound：∏(1-η_t) ≤ exp(-Σ η_t)（用 1-x ≤ e^{-x}）；
  · sqrt_inv_le_two_sub / sum_sqrt_range / sqrt_decay：Σ_{t<N} 1/√(t+1) ≤ 2√N
    （Rodrigues 的 1/√t 步长累计界，逐项差分 + 裂项相消）；
  · sqrt_decay_rate：e_N ≤ e_0·exp(-Σ_{t<N} η_t)（显式指数率）；
  · sqrt_decay_explicit：Σ_{t<N} 1/√(t+1) ≥ √N ⟹
    e_N ≤ e_0·exp(-η₀·√N) —— 1/√t 调度的显式 O(e^{-√N}) 率。

诚实边界：
  · 「衰减学习率下 e_n → 0」在仅有 e(n+1) ≤ (1-η_n)e_n、η_n → 0 时**不成立**
    （序列可收敛到正极限）；因此本文件不声称该伪定理。真正的衰减调度收敛
    依赖损失函数的下降引理（descent lemma，需要 Lipschitz 梯度/凸性）给出
    Σ η_t·e_t < ∞ 或 Σ η_t·‖∇‖² < ∞ 这类**额外求和结构**——本文件的
    small_error_of_summable_weighted 正是把这一结构转化为收敛结论的桥梁，
    完整的下降引理推导标注为后续工作；
  · sqrt_decay_explicit 的证明只需 η_t ≤ 1 与 e_0 ≥ 0；率是 exp(-η₀√N)，
    比一般文献的 O(1/√N) 更强，因为这里直接从乘积界得到（无须平均化）；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Filter
open scoped Topology

namespace Lattice

/-! ## 一、级数侧：p > 1 可和，p = 1 不可和 -/

/-- p > 1 ⟹ Σ_{t≥0} 1/(t+1)^p 收敛（引用 mathlib 的 nat rpow 判别法 + 平移）。-/
theorem poly_decay_summable (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ p) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    (Real.summable_one_div_nat_rpow).mpr hp
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ p) 1).mpr hbase
  simpa [Nat.cast_add, Nat.cast_one] using hshift

/-- 调和级数 Σ 1/(t+1) 发散（p = 1 处的临界判别）。-/
theorem linear_lr_one_not_summable :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro hs
  have hbase : ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    intro h
    have hp := (Real.summable_one_div_nat_rpow (p := 1)).mp (by simpa using h)
    exact lt_irrefl (1 : ℝ) hp
  apply hbase
  have hs' : Summable (fun n : ℕ => (fun m : ℕ => 1 / (m : ℝ)) (n + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hs
  exact (summable_nat_add_iff 1).mp hs'

/-- η₀ > 0 ⟹ η_t = η₀/(t+1) 不可求和（Σ η_t = ∞）。-/
theorem linear_lr_not_summable (η₀ : ℝ) (hη : 0 < η₀) :
    ¬ Summable (fun n : ℕ => η₀ / ((n : ℝ) + 1)) := by
  intro hs
  have h2 : Summable (fun n : ℕ => η₀⁻¹ * (η₀ / ((n : ℝ) + 1))) :=
    Summable.mul_left η₀⁻¹ hs
  have hfun : (fun n : ℕ => η₀⁻¹ * (η₀ / ((n : ℝ) + 1)))
      = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    funext n
    have hc : η₀⁻¹ * η₀ = 1 := inv_mul_cancel₀ (ne_of_gt hη)
    calc
      η₀⁻¹ * (η₀ / ((n : ℝ) + 1)) = (η₀⁻¹ * η₀) / ((n : ℝ) + 1) := by ring
      _ = 1 / ((n : ℝ) + 1) := by rw [hc]
  rw [hfun] at h2
  exact linear_lr_one_not_summable h2

/-! ## 二、核心：加权和收敛 ⟹ 存在任意小误差（序列推论）

若 e ≥ 0、η ≥ 0、Σ η_t·e_t < ∞ 而 Σ η_t = ∞，则 e_t 不能有正的下界，
即 ∀ ε > 0，∃ n，e_n < ε。这是「加权平均收敛」的精确形式，也是把
下降引理（Σ η_t·‖∇‖² < ∞）转成「∃ 小梯度点」的标准桥梁。-/

theorem small_error_of_summable_weighted {e η : ℕ → ℝ}
    (he : ∀ n, 0 ≤ e n) (hη : ∀ n, 0 ≤ η n)
    (hsum : Summable (fun n => η n * e n)) (hηns : ¬ Summable η) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, e n < ε := by
  intro ε hε
  by_contra h
  push_neg at h
  -- h : ∀ n, ε ≤ e n
  have hle : ∀ n, η n * ε ≤ η n * e n :=
    fun n => mul_le_mul_of_nonneg_left (h n) (hη n)
  have hnonneg : ∀ n, 0 ≤ η n * ε := fun n => mul_nonneg (hη n) (le_of_lt hε)
  have hsum' : Summable (fun n => η n * ε) :=
    Summable.of_nonneg_of_le hnonneg hle hsum
  apply hηns
  have h2 : Summable (fun n => ε⁻¹ * (η n * ε)) := Summable.mul_left ε⁻¹ hsum'
  have hfun : (fun n => ε⁻¹ * (η n * ε)) = η := by
    funext n
    have hc : ε⁻¹ * ε = 1 := inv_mul_cancel₀ (ne_of_gt hε)
    calc
      ε⁻¹ * (η n * ε) = (ε⁻¹ * ε) * η n := by ring
      _ = η n := by rw [hc, one_mul]
  rwa [hfun] at h2

/-- 特化：η_t = η₀/(t+1)（调和衰减），Σ η_t·e_t 收敛 ⟹ 存在任意小误差。-/
theorem harmonic_lr_small_error {e : ℕ → ℝ} (η₀ : ℝ) (hη0 : 0 < η₀)
    (he : ∀ n, 0 ≤ e n)
    (hsum : Summable (fun n : ℕ => (η₀ / ((n : ℝ) + 1)) * e n)) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, e n < ε :=
  small_error_of_summable_weighted he
    (fun n => div_nonneg (le_of_lt hη0) (by positivity))
    hsum (linear_lr_not_summable η₀ hη0)

/-! ## 三、单步衰减调度的一般结构 -/

/-- 衰减调度下误差单调不增：0 ≤ η_n ≤ 1，e ≥ 0，e(n+1) ≤ (1-η_n)e_n。-/
theorem lr_decay_antitone {e η : ℕ → ℝ}
    (he : ∀ n, 0 ≤ e n) (hη0 : ∀ n, 0 ≤ η n) (_hη1 : ∀ n, η n ≤ 1)
    (hdec : ∀ n, e (n + 1) ≤ (1 - η n) * e n) :
    Antitone e := by
  apply antitone_nat_of_succ_le
  intro n
  calc
    e (n + 1) ≤ (1 - η n) * e n := hdec n
    _ ≤ 1 * e n := mul_le_mul_of_nonneg_right (by linarith [hη0 n]) (he n)
    _ = e n := one_mul _

/-- 有限乘积上界：e_N ≤ e_0·∏_{t<N}(1-η_t)。-/
theorem decay_product_bound {e η : ℕ → ℝ}
    (he : ∀ n, 0 ≤ e n) (_hη0 : ∀ n, 0 ≤ η n) (hη1 : ∀ n, η n ≤ 1)
    (hdec : ∀ n, e (n + 1) ≤ (1 - η n) * e n) :
    ∀ N : ℕ, e N ≤ e 0 * ∏ t in Finset.range N, (1 - η t) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hfac : 0 ≤ 1 - η N := by linarith [hη1 N]
      calc
        e (N + 1) ≤ (1 - η N) * e N := hdec N
        _ ≤ (1 - η N) * (e 0 * ∏ t in Finset.range N, (1 - η t)) :=
              mul_le_mul_of_nonneg_left ih hfac
        _ = e 0 * ∏ t in Finset.range (N + 1), (1 - η t) := by
              rw [Finset.prod_range_succ]
              ring

/-- 几何阶段保证：前 N 步若 η_t ≥ c（0 ≤ c ≤ 1），则 e_N ≤ (1-c)^N·e_0。
连接 RealConvergence.contraction_pow_bound。-/
theorem lr_decay_finite_phase {e η : ℕ → ℝ} (c : ℝ)
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (he : ∀ n, 0 ≤ e n) (hηc : ∀ n, c ≤ η n) (_hη1 : ∀ n, η n ≤ 1)
    (hdec : ∀ n, e (n + 1) ≤ (1 - η n) * e n) :
    ∀ N : ℕ, e N ≤ (1 - c) ^ N * e 0 := by
  apply contraction_pow_bound (1 - c) (by linarith)
  intro n
  calc
    e (n + 1) ≤ (1 - η n) * e n := hdec n
    _ ≤ (1 - c) * e n := mul_le_mul_of_nonneg_right (by linarith [hηc n]) (he n)

/-- p = 0（常数学习率 η_t ≡ η₀ ∈ (0,1)）时回收几何收敛：ε-终止。-/
theorem constant_lr_converges {e : ℕ → ℝ} (η₀ : ℝ) (h0 : 0 < η₀) (h1 : η₀ < 1)
    (he : ∀ n, 0 ≤ e n) (hdec : ∀ n, e (n + 1) ≤ (1 - η₀) * e n) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, e n < ε :=
  contraction_converges (1 - η₀) (by linarith) (by linarith) hdec he

/-! ## 四、乘积的指数上界 -/

/-- ∏_{t<N}(1-η_t) ≤ exp(-Σ_{t<N} η_t)（逐项 1-x ≤ e^{-x}）。-/
theorem product_exp_bound (η : ℕ → ℝ) (hη1 : ∀ n, η n ≤ 1) (N : ℕ) :
    (∏ t in Finset.range N, (1 - η t))
      ≤ Real.exp (-(∑ t in Finset.range N, η t)) := by
  have hprod : (∏ t in Finset.range N, (1 - η t))
      ≤ ∏ t in Finset.range N, Real.exp (-(η t)) :=
    Finset.prod_le_prod (fun t _ => by linarith [hη1 t])
      (fun t _ => Real.one_sub_le_exp_neg (η t))
  calc
    (∏ t in Finset.range N, (1 - η t))
        ≤ ∏ t in Finset.range N, Real.exp (-(η t)) := hprod
    _ = Real.exp (∑ t in Finset.range N, -(η t)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(∑ t in Finset.range N, η t)) := by rw [Finset.sum_neg_distrib]

/-! ## 五、√t 调度（Rodrigues）：有限和界 Σ 1/√(t+1) ≤ 2√N -/

/-- 逐项界：1/√(t+1) ≤ 2(√(t+1) - √t)。
（(√(t+1))²-(√t)² = 1 ⟹ √(t+1)-√t = 1/(√(t+1)+√t)，再用 √t ≤ √(t+1)。）-/
theorem sqrt_inv_le_two_sub (n : ℕ) :
    1 / Real.sqrt ((n : ℝ) + 1)
      ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  set a := Real.sqrt ((n : ℝ) + 1) with ha
  set b := Real.sqrt (n : ℝ) with hb
  have ha0 : 0 < a := Real.sqrt_pos_of_pos (by positivity)
  have hba : b ≤ a := by
    rw [ha, hb]
    exact Real.sqrt_le_sqrt (by linarith)
  have hden : 0 < a + b := by
    have : 0 ≤ b := Real.sqrt_nonneg _
    linarith
  have hmul : (a - b) * (a + b) = 1 := by
    have hexp : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
    rw [hexp, ha, hb, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  have hsub : a - b = 1 / (a + b) := (eq_div_iff (ne_of_gt hden)).mpr hmul
  have hstep : 1 / a ≤ 2 / (a + b) := by
    rw [div_le_div_iff₀ ha0 hden]
    linarith
  calc
    1 / Real.sqrt ((n : ℝ) + 1) = 1 / a := by rw [ha]
    _ ≤ 2 / (a + b) := hstep
    _ = 2 * (a - b) := by rw [hsub]; ring
    _ = 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by rw [ha, hb]

/-- 裂项相消：Σ_{t<N}(√(t+1) - √t) = √N。-/
theorem sum_sqrt_range (N : ℕ) :
    (∑ t in Finset.range N, (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ)))
      = Real.sqrt (N : ℝ) := by
  have h := Finset.sum_range_sub (f := fun t : ℕ => Real.sqrt (t : ℝ)) N
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- √t 调度的累计步长界（sqrt_decay）：Σ_{t<N} η₀/√(t+1) ≤ 2·η₀·√N。-/
theorem sqrt_decay (η₀ : ℝ) (hη₀ : 0 ≤ η₀) (N : ℕ) :
    (∑ t in Finset.range N, η₀ / Real.sqrt ((t : ℝ) + 1))
      ≤ 2 * η₀ * Real.sqrt (N : ℝ) := by
  have hterm : ∀ t ∈ Finset.range N,
      η₀ / Real.sqrt ((t : ℝ) + 1)
        ≤ η₀ * (2 * (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ))) := by
    intro t _
    calc
      η₀ / Real.sqrt ((t : ℝ) + 1)
          = η₀ * (1 / Real.sqrt ((t : ℝ) + 1)) := (mul_one_div η₀ _).symm
      _ ≤ η₀ * (2 * (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ))) :=
            mul_le_mul_of_nonneg_left (sqrt_inv_le_two_sub t) hη₀
  calc
    (∑ t in Finset.range N, η₀ / Real.sqrt ((t : ℝ) + 1))
        ≤ ∑ t in Finset.range N,
            η₀ * (2 * (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ))) :=
          Finset.sum_le_sum hterm
    _ = η₀ * (2 * ∑ t in Finset.range N,
            (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = η₀ * (2 * Real.sqrt (N : ℝ)) := by rw [sum_sqrt_range]
    _ = 2 * η₀ * Real.sqrt (N : ℝ) := by ring

/-! ## 六、√t 调度的显式指数率 -/

/-- 显式率（以累计步长表示）：e_N ≤ e₀·exp(-Σ_{t<N} η_t)。-/
theorem sqrt_decay_rate {e : ℕ → ℝ} (η₀ : ℝ) (he : ∀ n, 0 ≤ e n) (hη0 : 0 ≤ η₀)
    (hη1 : ∀ n : ℕ, η₀ / Real.sqrt ((n : ℝ) + 1) ≤ 1)
    (hdec : ∀ n : ℕ, e (n + 1) ≤ (1 - η₀ / Real.sqrt ((n : ℝ) + 1)) * e n) :
    ∀ N : ℕ, e N
      ≤ e 0 * Real.exp (-(∑ t in Finset.range N, η₀ / Real.sqrt ((t : ℝ) + 1))) := by
  intro N
  have hprod := decay_product_bound he
    (fun n => div_nonneg hη0 (Real.sqrt_nonneg _)) hη1 hdec N
  have hexp := product_exp_bound (fun t : ℕ => η₀ / Real.sqrt ((t : ℝ) + 1))
    hη1 N
  exact le_trans hprod (mul_le_mul_of_nonneg_left hexp (he 0))

/-- 下界：Σ_{t<N} 1/√(t+1) ≥ √N（N 项，每项 ≥ 1/√N）。-/
theorem sum_sqrt_inv_ge (N : ℕ) :
    Real.sqrt (N : ℝ)
      ≤ ∑ t in Finset.range N, 1 / Real.sqrt ((t : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hden : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos_of_pos hNpos
    have hterm : ∀ t ∈ Finset.range N,
        1 / Real.sqrt (N : ℝ) ≤ 1 / Real.sqrt ((t : ℝ) + 1) := by
      intro t ht
      have htN : t + 1 ≤ N := by
        have := Finset.mem_range.mp ht
        omega
      have hle : Real.sqrt ((t : ℝ) + 1) ≤ Real.sqrt (N : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast htN)
      exact one_div_le_one_div_of_le (Real.sqrt_pos_of_pos (by positivity)) hle
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hdiv : (N : ℝ) * (1 / Real.sqrt (N : ℝ)) = Real.sqrt (N : ℝ) := by
      rw [mul_one_div, div_eq_iff (ne_of_gt hden)]
      rw [← sq, Real.sq_sqrt (le_of_lt hNpos)]
    linarith [hdiv ▸ hsum]

/-- √t 调度的显式率（sqrt_decay 主结果）：
e_N ≤ e₀·exp(-η₀·√N)，即误差以 e^{-η₀√N} 速度衰减。-/
theorem sqrt_decay_explicit {e : ℕ → ℝ} (η₀ : ℝ) (he : ∀ n, 0 ≤ e n) (hη0 : 0 ≤ η₀)
    (hη1 : ∀ n : ℕ, η₀ / Real.sqrt ((n : ℝ) + 1) ≤ 1)
    (hdec : ∀ n : ℕ, e (n + 1) ≤ (1 - η₀ / Real.sqrt ((n : ℝ) + 1)) * e n) :
    ∀ N : ℕ, e N ≤ e 0 * Real.exp (-(η₀ * Real.sqrt (N : ℝ))) := by
  intro N
  have hrate := sqrt_decay_rate η₀ he hη0 hη1 hdec N
  have hge := sum_sqrt_inv_ge N
  have hsum_le : η₀ * Real.sqrt (N : ℝ)
      ≤ ∑ t in Finset.range N, η₀ / Real.sqrt ((t : ℝ) + 1) := by
    calc
      η₀ * Real.sqrt (N : ℝ)
          ≤ η₀ * ∑ t in Finset.range N, 1 / Real.sqrt ((t : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hge hη0
      _ = ∑ t in Finset.range N, η₀ / Real.sqrt ((t : ℝ) + 1) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring
  calc
    e N ≤ e 0 * Real.exp (-(∑ t in Finset.range N, η₀ / Real.sqrt ((t : ℝ) + 1))) := hrate
    _ ≤ e 0 * Real.exp (-(η₀ * Real.sqrt (N : ℝ))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (he 0)

/-! ## 注：调度收敛的诚实边界
  · 仅有 e(n+1) ≤ (1-η_n)e_n 且 η_n → 0 时，e_n 收敛但极限可以 > 0；
    本文件因此不声称「衰减调度 ⟹ e_n → 0」；
  · 真正的结论走两条已形式化的路径：
      (a) small_error_of_summable_weighted：把下降引理给出的
          Σ η_t·e_t < ∞（或 Σ η_t‖∇‖² < ∞）转成「∃ 任意小误差点」；
      (b) sqrt_decay_explicit：在 η_t = η₀/√(t+1) 下直接给出
          e_N ≤ e_0·exp(-η₀√N) 的显式率（确定性收缩框架内）；
  · poly_decay_summable 覆盖 p > 1 的可和调度；p ≤ 1 的不可和性
    本文只形式化了 p = 1（linear_lr_not_summable），一般 p ≤ 1 需要
    rpow 单调性，标注为后续。-/

end Lattice
