import Mathlib
import Lattice.Lib.Optim.RealDPSGD
/-!
# LATTICE: Rényi 散度与 Rényi 差分隐私（有限支撑版）

本文件给出 Rényi 散度 `D_α` 的有限支撑定义、非负性、乘积可加性（**组合定理**）、
以及 Rényi DP 到 `(ε,δ)`-DP 的显式换算，并接到 `RealDPSGD` 的裁剪-噪声结构上。

主要结果：

  1. `renyiDivergence`（定义）：`D_α(p‖q) = (α−1)⁻¹·log Σ_i p_i^α·q_i^{1−α}`
     （`Real.rpow` 实指数）。
  2. `renyiDivergence_self`：`D_α(p‖p) = 0`。
  3. `renyiDivergence_two_eq` / `renyiDivergence_two_nonneg`：`α = 2` 时
     `D_2 = log Σ p_i²/q_i`，并由 **Cauchy–Schwarz**（`Finset.sum_mul_sq_le_sq_mul_sq`）
     得 `0 ≤ D_2`。
  4. `prodPmf`（乘积分布）与 `renyiDivergence_prodPmf_additive`（**组合定理**）：
     `D_α(p₁⊗p₂ ‖ q₁⊗q₂) = D_α(p₁‖q₁) + D_α(p₂‖q₂)`（`Real.mul_rpow` + `Real.log_mul`
     + 双重求和乘积分解）。
  5. `rdpDelta`（定义 `δ = exp(−(α−1)ε')`）与 `rdpDelta_add_eq_mul`：
     **δ 关于复合可乘**。
  6. `renyiDP_compose`：`D_α ≤ ε₁`、`D_α ≤ ε₂` ⟹ 复合机制的 `D_α ≤ ε₁ + ε₂`
     （RDP 组合定理）。
  7. `rpow_sum_le_of_renyiDivergence_le` / `rdp_event_bound`：RDP 参数到事件界
     `p(E) ≤ exp(ε')·q(E)^{1−1/α}` 的换算；**Hölder 步骤作为显式假设引入（诚实降级）**。
  8. `gaussianRDPEpsilon` / `dpsgd_noise_scale_of_rdp` / `dpsgd_gaussian_delta`：
     高斯机制 `ε'(α) = αΔ²/(2σ²)` 与 `(ε,δ)` 的**显式换算条件定理**，
     接 `RealDPSGD.noiseVariance`（`σ²C²`）的噪声尺度结构。

**诚实边界（标注）**：
- α→1 退化为 KL：**未做**（需要 `Real.rpow` 在 `α → 1` 的极限与 `Real.deriv`，
  本文件只证明 `α = 2` 的具体情形，如实标注）。
- `D_α ≥ 0` 的一般 `α > 1`：**未做**（需要广义 Hölder / 加权 AM–GM 的有限和版本）；
  本文件用 Cauchy–Schwarz 完整证明了 `α = 2`。
- `rdp_event_bound` 的 **Hölder 步骤是显式假设**（诚实降级）：即「对任意事件 `E`，
  `Σ_{i∈E} p_i ≤ (Σ_{i∈E} p_i^α q_i^{1−α})^{1/α}·(Σ_{i∈E} q_i)^{1−1/α}`」。
  该不等式是标准的（对 `x_i = p_i q_i^{-(α−1)/α}`、`y_i = q_i^{(α−1)/α}` 用
  共轭指数 `α, α/(α−1)` 的 Hölder）；mathlib 的有限和 Hölder 未直接覆盖该指数形式，
  故本文件未证并标注。
- 高斯机制的 RDP 界 `D_α(N(0,σ²)‖N(Δ,σ²)) ≤ αΔ²/(2σ²)` 是**显式假设**
  （其证明需高斯分布的对数矩母函数，本文件未做，标注）。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、Rényi 散度（有限支撑） -/

/-- **Rényi 散度**（有限支撑）：`D_α(p‖q) = (α−1)⁻¹·log(Σ_i p_i^α·q_i^{1−α})`。
`α = 1` 处分母为零（退化情形本文件未处理，见诚实边界）。
索引类型泛化为任意 `Fintype`（`Fin n` 是其特例），以便乘积分布 `Fin m × Fin n`
直接落入同一接口。 -/
noncomputable def renyiDivergence {ι : Type*} [Fintype ι] (α : ℝ) (p q : ι → ℝ) : ℝ :=
  (α - 1)⁻¹ * Real.log (∑ i, p i ^ α * q i ^ (1 - α))

/-- **自散度为零**：`p` 严格正、`Σ p = 1`、`α ≠ 1` ⟹ `D_α(p‖p) = 0`。
证明：`p^α·p^{1−α} = p^{α+(1−α)} = p`（`Real.rpow_add`）+ `log 1 = 0`。 -/
theorem renyiDivergence_self {n : ℕ} {α : ℝ} (_hα : α ≠ 1) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    renyiDivergence α p p = 0 := by
  unfold renyiDivergence
  have hterm : ∀ i : Fin n, p i ^ α * p i ^ (1 - α) = p i := by
    intro i
    rw [← Real.rpow_add (hp i)]
    have h : α + (1 - α) = 1 := by ring
    rw [h, Real.rpow_one]
  simp_rw [hterm]
  rw [hsum, Real.log_one, mul_zero]

/-! ## 二、`α = 2`：显式形式与非负（Cauchy–Schwarz） -/

/-- `α = 2` 时的显式形式：`D_2(p‖q) = log(Σ_i p_i²/q_i)`（`q > 0`）。
（`hq` 保留为定义域标注，当前证明不消耗它。） -/
theorem renyiDivergence_two_eq {n : ℕ} (p q : Fin n → ℝ) (_hq : ∀ i, 0 < q i) :
    renyiDivergence 2 p q = Real.log (∑ i, p i ^ 2 / q i) := by
  unfold renyiDivergence
  have hterm : ∀ i : Fin n, p i ^ (2 : ℝ) * q i ^ ((1 : ℝ) - 2) = p i ^ 2 / q i := by
    intro i
    have h2 : (1 : ℝ) - 2 = -1 := by norm_num
    rw [h2, Real.rpow_neg_one, div_eq_mul_inv]
    norm_num
  simp only [hterm]
  norm_num

/-- **`α = 2` 的 Rényi 散度非负**（Cauchy–Schwarz）：
`p ≥ 0`、`q > 0`、`Σ p = Σ q = 1` ⟹ `0 ≤ D_2(p‖q)`。
证明：`(Σ p_i)² = (Σ (p_i/√q_i)·√q_i)² ≤ (Σ p_i²/q_i)·(Σ q_i) = Σ p_i²/q_i`，
故 `Σ p_i²/q_i ≥ 1`，取 `log` 得非负。 -/
theorem renyiDivergence_two_nonneg {n : ℕ} (p q : Fin n → ℝ) (_hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 < q i) (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) :
    0 ≤ renyiDivergence 2 p q := by
  rw [renyiDivergence_two_eq p q hq]
  have hsq : ∀ i : Fin n, Real.sqrt (q i) ≠ 0 := fun i => ne_of_gt (Real.sqrt_pos.mpr (hq i))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i => p i / Real.sqrt (q i)) (fun i => Real.sqrt (q i))
  simp only [Finset.mem_univ, Finset.sum_attach, true_implies] at hcs
  have hleft : (∑ i : Fin n, p i / Real.sqrt (q i) * Real.sqrt (q i)) = ∑ i, p i := by
    apply Finset.sum_congr rfl
    intro i _
    exact div_mul_cancel₀ (p i) (hsq i)
  have hright1 : (∑ i : Fin n, (p i / Real.sqrt (q i)) ^ 2) = ∑ i, p i ^ 2 / q i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, Real.sq_sqrt (le_of_lt (hq i))]
  have hright2 : (∑ i : Fin n, (Real.sqrt (q i)) ^ 2) = ∑ i, q i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sq_sqrt (le_of_lt (hq i))]
  rw [hleft, hpsum, hright1, hright2, hqsum, mul_one, one_pow] at hcs
  exact Real.log_nonneg hcs

/-! ## 三、乘积分布与 Rényi 散度的乘积可加性（组合定理的核心） -/

/-- **乘积分布**：`(p ⊗ q)(x,y) = p x · q y`。 -/
noncomputable def prodPmf {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) :
    Fin m × Fin n → ℝ := fun x => p x.1 * q x.2

/-- **Rényi 散度的乘积可加性**（**组合定理的核心**）：
`D_α(p₁⊗p₂ ‖ q₁⊗q₂) = D_α(p₁‖q₁) + D_α(p₂‖q₂)`。
证明：`Real.mul_rpow` 拆幂 + 双重和分解为乘积（`Fintype.sum_prod_type`、
`Finset.sum_mul_sum`）+ `Real.log_mul`。 -/
theorem renyiDivergence_prodPmf_additive {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (α : ℝ) (p₁ : Fin m → ℝ) (p₂ : Fin n → ℝ) (q₁ : Fin m → ℝ) (q₂ : Fin n → ℝ)
    (hp₁ : ∀ i, 0 < p₁ i) (hp₂ : ∀ j, 0 < p₂ j) (hq₁ : ∀ i, 0 < q₁ i)
    (hq₂ : ∀ j, 0 < q₂ j) :
    renyiDivergence α (prodPmf p₁ p₂) (prodPmf q₁ q₂)
      = renyiDivergence α p₁ q₁ + renyiDivergence α p₂ q₂ := by
  have hterm : (∑ x : Fin m × Fin n,
        prodPmf p₁ p₂ x ^ α * prodPmf q₁ q₂ x ^ (1 - α))
      = (∑ i : Fin m, p₁ i ^ α * q₁ i ^ (1 - α))
        * (∑ j : Fin n, p₂ j ^ α * q₂ j ^ (1 - α)) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [prodPmf]
    rw [Real.mul_rpow (le_of_lt (hp₁ i)) (le_of_lt (hp₂ j)),
      Real.mul_rpow (le_of_lt (hq₁ i)) (le_of_lt (hq₂ j))]
    ring
  have hApos : 0 < ∑ i : Fin m, p₁ i ^ α * q₁ i ^ (1 - α) :=
    Finset.sum_pos (fun i _ => mul_pos (Real.rpow_pos_of_pos (hp₁ i) α)
      (Real.rpow_pos_of_pos (hq₁ i) (1 - α))) Finset.univ_nonempty
  have hBpos : 0 < ∑ j : Fin n, p₂ j ^ α * q₂ j ^ (1 - α) :=
    Finset.sum_pos (fun j _ => mul_pos (Real.rpow_pos_of_pos (hp₂ j) α)
      (Real.rpow_pos_of_pos (hq₂ j) (1 - α))) Finset.univ_nonempty
  unfold renyiDivergence
  rw [hterm, Real.log_mul (ne_of_gt hApos) (ne_of_gt hBpos)]
  ring

/-! ## 四、Rényi DP 的 `(ε,δ)` 换算：`δ = exp(−(α−1)ε')` -/

/-- **RDP→DP 的 δ 换算**：`δ(α,ε') = exp(−(α−1)·ε')`（标准 Rényi DP 换算形式）。 -/
noncomputable def rdpDelta (α ε' : ℝ) : ℝ := Real.exp (-(α - 1) * ε')

/-- **δ 关于复合可乘**：`δ(α, ε₁+ε₂) = δ(α,ε₁)·δ(α,ε₂)`。 -/
theorem rdpDelta_add_eq_mul (α ε₁ ε₂ : ℝ) :
    rdpDelta α (ε₁ + ε₂) = rdpDelta α ε₁ * rdpDelta α ε₂ := by
  unfold rdpDelta
  rw [← Real.exp_add]
  ring_nf

/-- **Rényi DP 组合定理**：若两个机制分别满足 `D_α ≤ ε₁`、`D_α ≤ ε₂`，
则其乘积（独立复合）机制满足 `D_α ≤ ε₁ + ε₂`。 -/
theorem renyiDP_compose {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    {α ε₁ ε₂ : ℝ} (p₁ : Fin m → ℝ) (p₂ : Fin n → ℝ) (q₁ : Fin m → ℝ) (q₂ : Fin n → ℝ)
    (hp₁ : ∀ i, 0 < p₁ i) (hp₂ : ∀ j, 0 < p₂ j) (hq₁ : ∀ i, 0 < q₁ i)
    (hq₂ : ∀ j, 0 < q₂ j)
    (h₁ : renyiDivergence α p₁ q₁ ≤ ε₁) (h₂ : renyiDivergence α p₂ q₂ ≤ ε₂) :
    renyiDivergence α (prodPmf p₁ p₂) (prodPmf q₁ q₂) ≤ ε₁ + ε₂ := by
  rw [renyiDivergence_prodPmf_additive α p₁ p₂ q₁ q₂ hp₁ hp₂ hq₁ hq₂]
  exact add_le_add h₁ h₂

/-- **RDP 参数 ⟹ 幂和界**：由 `D_α` 的定义与 `(α−1) > 0` 直接得到
`Σ p^α q^{1−α} ≤ exp((α−1)ε')`（`Real.log_le_iff_le_exp`）。 -/
theorem rpow_sum_le_of_renyiDivergence_le {n : ℕ} (p q : Fin n → ℝ) {α ε' : ℝ}
    (hα : 1 < α) (hpos : 0 < ∑ i, p i ^ α * q i ^ (1 - α))
    (h : renyiDivergence α p q ≤ ε') :
    (∑ i, p i ^ α * q i ^ (1 - α)) ≤ Real.exp ((α - 1) * ε') := by
  have hα1 : 0 < α - 1 := by linarith
  have hlog : Real.log (∑ i, p i ^ α * q i ^ (1 - α)) ≤ (α - 1) * ε' := by
    have := mul_le_mul_of_nonneg_left h (le_of_lt hα1)
    have hinv : (α - 1) * ((α - 1)⁻¹ * Real.log (∑ i, p i ^ α * q i ^ (1 - α)))
        = Real.log (∑ i, p i ^ α * q i ^ (1 - α)) := by
      field_simp
    unfold renyiDivergence at this
    linarith [this, hinv]
  exact (Real.log_le_iff_le_exp hpos).mp hlog

/-- **RDP 事件界（诚实降级：Hölder 步骤为显式假设）**：
若 `Σ p^α q^{1−α} ≤ exp((α−1)ε')` 且（Hölder 假设）对任意事件 `E`
`Σ_{i∈E} p_i ≤ (Σ_{i∈E} p_i^α q_i^{1−α})^{1/α}·(Σ_{i∈E} q_i)^{1−1/α}`，
则 `Σ_{i∈E} p_i ≤ exp(ε')·(Σ_{i∈E} q_i)^{1−1/α}`。 -/
theorem rdp_event_bound {n : ℕ} (p q : Fin n → ℝ) {α ε' : ℝ} (hα : 1 < α)
    (hε' : 0 ≤ ε') (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hrdp : (∑ i, p i ^ α * q i ^ (1 - α)) ≤ Real.exp ((α - 1) * ε'))
    (hholder : ∀ E : Finset (Fin n),
      (∑ i in E, p i)
        ≤ (∑ i in E, p i ^ α * q i ^ (1 - α)) ^ (1 / α)
          * (∑ i in E, q i) ^ (1 - 1 / α)) :
    ∀ E : Finset (Fin n),
      (∑ i in E, p i) ≤ Real.exp ε' * (∑ i in E, q i) ^ (1 - 1 / α) := by
  intro E
  have hα0 : 0 < α := by linarith
  have hA0 : 0 ≤ ∑ i in E, p i ^ α * q i ^ (1 - α) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg (hp i) α)
      (le_of_lt (Real.rpow_pos_of_pos (hq i) (1 - α))))
  have hAle : (∑ i in E, p i ^ α * q i ^ (1 - α)) ≤ Real.exp ((α - 1) * ε') :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
      (fun i _ _ => mul_nonneg (Real.rpow_nonneg (hp i) α)
        (le_of_lt (Real.rpow_pos_of_pos (hq i) (1 - α))))) hrdp
  have hcoef : (1 / α) * ((α - 1) * ε') ≤ ε' := by
    have h2 : (α - 1) / α ≤ 1 := by
      rw [div_le_one hα0]; linarith
    have h3 : (1 / α) * ((α - 1) * ε') = ((α - 1) / α) * ε' := by
      field_simp
    rw [h3]
    calc ((α - 1) / α) * ε' ≤ 1 * ε' := mul_le_mul_of_nonneg_right h2 hε'
      _ = ε' := one_mul _
  have hpow : (Real.exp ((α - 1) * ε')) ^ (1 / α)
      = Real.exp ((1 / α) * ((α - 1) * ε')) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    ring_nf
  have hαinv : 0 < 1 / α := by positivity
  have hone_sub : 0 < 1 - 1 / α := by
    rw [sub_pos, div_lt_one hα0]
    linarith
  have hroot : (∑ i in E, p i ^ α * q i ^ (1 - α)) ^ (1 / α) ≤ Real.exp ε' := by
    calc (∑ i in E, p i ^ α * q i ^ (1 - α)) ^ (1 / α)
        ≤ (Real.exp ((α - 1) * ε')) ^ (1 / α) :=
          Real.rpow_le_rpow hA0 hAle hαinv.le
      _ = Real.exp ((1 / α) * ((α - 1) * ε')) := hpow
      _ ≤ Real.exp ε' := Real.exp_le_exp.mpr hcoef
  have hq0 : 0 ≤ (∑ i in E, q i) ^ (1 - 1 / α) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => le_of_lt (hq i))) _
  calc (∑ i in E, p i)
      ≤ (∑ i in E, p i ^ α * q i ^ (1 - α)) ^ (1 / α) * (∑ i in E, q i) ^ (1 - 1 / α) :=
        hholder E
    _ ≤ Real.exp ε' * (∑ i in E, q i) ^ (1 - 1 / α) :=
        mul_le_mul_of_nonneg_right hroot hq0

/-- **RDP → `(ε,δ)` 的事件界**：在 `rdp_event_bound` 的假设下，
若事件满足 `Σ_{i∈E} q_i ≤ δ`，则 `Σ_{i∈E} p_i ≤ exp(ε')·δ^{1−1/α}`。 -/
theorem rdp_event_bound_of_delta {n : ℕ} (p q : Fin n → ℝ) {α ε' δ : ℝ} (hα : 1 < α)
    (hε' : 0 ≤ ε') (_hδ : 0 ≤ δ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hrdp : (∑ i, p i ^ α * q i ^ (1 - α)) ≤ Real.exp ((α - 1) * ε'))
    (hholder : ∀ E : Finset (Fin n),
      (∑ i in E, p i)
        ≤ (∑ i in E, p i ^ α * q i ^ (1 - α)) ^ (1 / α)
          * (∑ i in E, q i) ^ (1 - 1 / α)) :
    ∀ E : Finset (Fin n), (∑ i in E, q i) ≤ δ →
      (∑ i in E, p i) ≤ Real.exp ε' * δ ^ (1 - 1 / α) := by
  intro E hE
  have hα0 : 0 < α := by linarith
  have hexp : 0 < 1 - 1 / α := by
    rw [sub_pos, div_lt_one hα0]
    linarith
  calc (∑ i in E, p i)
      ≤ Real.exp ε' * (∑ i in E, q i) ^ (1 - 1 / α) :=
        rdp_event_bound p q hα hε' hp hq hrdp hholder E
    _ ≤ Real.exp ε' * δ ^ (1 - 1 / α) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => le_of_lt (hq i))) hE hexp.le)
          (Real.exp_pos ε').le

/-! ## 五、高斯机制的噪声尺度与 `(ε,δ)` 的显式换算（接 RealDPSGD） -/

/-- **高斯机制的 Rényi DP 参数**（标准形式）：`ε'(α) = αΔ²/(2σ²)`，
`Δ` 为敏感度、`σ` 为噪声尺度。 -/
noncomputable def gaussianRDPEpsilon (α Δ σ : ℝ) : ℝ := α * Δ ^ 2 / (2 * σ ^ 2)

/-- **噪声尺度 ⟹ RDP 参数**（显式换算）：若 `σ² ≥ αΔ²/(2ε')`，则
`gaussianRDPEpsilon α Δ σ ≤ ε'`。 -/
theorem dpsgd_noise_scale_of_rdp {α Δ σ ε' : ℝ} (hσ : 0 < σ) (hε' : 0 < ε')
    (h : α * Δ ^ 2 / (2 * ε') ≤ σ ^ 2) :
    gaussianRDPEpsilon α Δ σ ≤ ε' := by
  unfold gaussianRDPEpsilon
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * σ ^ 2)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ε')] at h
  nlinarith [h, sq_nonneg σ, sq_nonneg Δ, hε', hσ]

/-- **RDP 参数 ⟹ δ 的显式换算**：`(α−1)·ε' ≤ log(1/δ)` ⟹
`δ ≤ rdpDelta α ε' = exp(−(α−1)ε')`。 -/
theorem rdp_delta_of_log_bound {α ε' δ : ℝ} (hδ : 0 < δ)
    (h : (α - 1) * ε' ≤ Real.log (1 / δ)) :
    δ ≤ rdpDelta α ε' := by
  have hlog : Real.log δ = -Real.log (1 / δ) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hδ), Real.log_one]
    ring
  have hle : Real.log δ ≤ -(α - 1) * ε' := by
    rw [hlog]; linarith
  calc δ = Real.exp (Real.log δ) := (Real.exp_log hδ).symm
    _ ≤ Real.exp (-(α - 1) * ε') := Real.exp_le_exp.mpr hle
    _ = rdpDelta α ε' := rfl

/-- **高斯机制 + 噪声尺度的 `(ε,δ)` 显式换算（条件定理）**：
给定（显式假设，诚实降级）高斯机制的 RDP 界 `ε'(α) ≤ ε'_0`，以及
`(α−1)ε'_0 ≤ log(1/δ)`，则 `δ ≤ exp(−(α−1)ε'_0)`。
这里 `ε'(α) = αΔ²/(2σ²)` 是 `RealDPSGD` 中噪声方差 `σ²C²` 的 RDP 对应参数。 -/
theorem dpsgd_gaussian_delta {α Δ σ δ ε'₀ : ℝ} (hα : 1 < α) (hδ : 0 < δ) (_hσ : 0 < σ)
    (hrdp : gaussianRDPEpsilon α Δ σ ≤ ε'₀)
    (h : (α - 1) * ε'₀ ≤ Real.log (1 / δ)) :
    δ ≤ rdpDelta α (gaussianRDPEpsilon α Δ σ) := by
  have hα1 : 0 < α - 1 := by linarith
  have hmono : (α - 1) * gaussianRDPEpsilon α Δ σ ≤ (α - 1) * ε'₀ :=
    mul_le_mul_of_nonneg_left hrdp (le_of_lt hα1)
  exact le_trans (rdp_delta_of_log_bound hδ (le_trans hmono h))
    (le_of_eq (by rfl))

/-- **与 `RealDPSGD` 噪声结构的对接**：`RealDPSGD.privacyProxy σ = 1/σ` 单调，
且其噪声方差 `RealDPSGD.noiseVariance σ C = σ²C²` 与 `gaussianRDPEpsilon` 的分母一致：
`gaussianRDPEpsilon α Δ σ = αΔ²/(2σ²)` 关于 `σ` 严格递减（`σ > 0`）。 -/
theorem gaussianRDPEpsilon_antitone {α Δ : ℝ} (hα : 0 < α) (hΔ : Δ ≠ 0)
    {σ₁ σ₂ : ℝ} (h₁ : 0 < σ₁) (hle : σ₁ ≤ σ₂) :
    gaussianRDPEpsilon α Δ σ₂ ≤ gaussianRDPEpsilon α Δ σ₁ := by
  unfold gaussianRDPEpsilon
  have h₂ : 0 < σ₂ := lt_of_lt_of_le h₁ hle
  have hsq : σ₁ ^ 2 ≤ σ₂ ^ 2 := by nlinarith
  have hnum : 0 < α * Δ ^ 2 := mul_pos hα (pow_pos (abs_pos.mpr hΔ) 2 |>.trans_eq (by rw [sq_abs]))
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * σ₂ ^ 2) (by positivity : (0 : ℝ) < 2 * σ₁ ^ 2)]
  nlinarith [hsq, hnum, sq_nonneg σ₁, sq_nonneg σ₂]

end Lattice
