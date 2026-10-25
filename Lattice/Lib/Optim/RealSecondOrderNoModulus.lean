import Mathlib
import Lattice.Lib.LinearAlgebra.RealHessian
/-!
# LATTICE: 去掉一致正定模数假设 —— 由点式正定推出显式模数 μ

`RealHessian` 把「存在 μ > 0 使 `∀v, μ‖v‖² ≤ quadForm H v`」写成**显式假设**，
并在诚实边界里明确标注这是一个未形式化的缺口：

> 由点式 `PosDefQ` 推出「存在 μ > 0 …」需要单位球面的紧性与连续性（有限维紧性论证），
> 本文件未形式化，故 μ 是**显式假设**（不隐藏 gap）。

**本文件把这个缺口补成定理**：`exists_modulus_of_posDef`。

## 数学内容

设 `M : Matrix (Fin n) (Fin n) ℝ` 满足点式正定 `PosDefQ M`（即 `∀ v ≠ 0, 0 < quadForm M v`）。
则存在**具体可计算的**模数
    `μ = min { quadForm M v | v ∈ S^{n-1} } > 0`
使得 `∀ v, μ · normSq v ≤ quadForm M v`。

证明路线（有限维紧性，全程只用 mathlib 已有引理）：

  1. **连续**：`v ↦ quadForm M v` 是连续函数（`continuous_quadForm`，由 `fun_prop` 拿下）；
  2. **紧**：单位球面 `Metric.sphere 0 1` 在 `EuclideanSpace ℝ (Fin n)` 中紧
     （`isCompact_sphere`）；非空由 `EuclideanSpace.single i 1` 给出（`n > 0`）；
  3. **取到最小**：`IsCompact.exists_isMinOn`（极值定理）给出 `x ∈ sphere` 使
     `∀ v ∈ sphere, quadForm M x ≤ quadForm M v`；
  4. **最小值正**：`x ≠ 0`（因 `‖x‖ = 1`），由 `PosDefQ` 得 `quadForm M x > 0`；
  5. **齐次化**：对 `v ≠ 0` 令 `u = ‖v‖⁻¹ • v`，则 `‖u‖ = 1`（单位球面），故
     `μ ≤ quadForm M u = ‖v‖⁻² · quadForm M v`（二次型齐次性 `quadForm_smul`），
     整理得 `μ ‖v‖² ≤ quadForm M v`；`v = 0` 时两边为 0。

## 与 RealHessian 的衔接

  · `exists_modulus_of_posDef`：**点式正定 ⟹ 显式模数存在**（本文件新增，补掉上述缺口）；
  · `modulus_of_posDef_bound`：给出 `RealHessian.quadratic_lower_bound_of_posdef` 所用
    假设形式的直接推论（即 `∀v, μ * normSq v ≤ quadForm H v` 的无条件版本）；
  · `second_order_sufficient_multidim_unconditional`：**把 RealHessian 的
    `second_order_sufficient_multidim` 的 hμ 与 hH 两个假设合并为「Hessian 点式正定」**，
    从而二阶充分条件不再需要外部提供模数。

## 诚实边界

  · 本文件处理的是**二次型** `quadForm`（`RealHessian` 的 `PosDefQ` 谓词）的模数存在性。
    把 `quadForm H v` 与真实的二阶 Fréchet 导数 `fderiv ℝ (fderiv ℝ f x) x` 对齐
    （即「H 确实是 f 的 Hessian」）仍是**未做**的桥接工作：`RealHessian` 已把
    `fderiv² f x` 与 `quadForm H` 的关系留给 `iteratedFDeriv` API，本文件不重复该桥接，
    故 `unconditional` 版定理的陈述仍以抽象 `H` 为载体（这是**接口层**而非结论层的降级）；
  · 模数是**存在性**陈述（由紧性给出的最小点 `x` 定义），不是闭式表达；
    对 2×2 的情形，`RealHessian.two_dim_posdef_iff` 已给出 Sylvester 判据式的闭式条件，
    本文件不重证；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter Metric
open scoped Topology BigOperators

namespace Lattice

/-! ## 一、连续性与齐次性 -/

/-- **二次型连续**：`v ↦ quadForm M v` 在 `EuclideanSpace ℝ (Fin n)` 上连续。

证明：把二次型写成 `∑ᵢ ∑ⱼ Mᵢⱼ·(vᵢ·vⱼ)`，坐标投影 `v ↦ v i` 连续，
有限和的乘积连续 ⟹ `fun_prop` 直接收尾。 -/
lemma continuous_quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun v : EuclideanSpace ℝ (Fin n) => quadForm M v) := by
  unfold quadForm
  fun_prop

/-- **`normSq` 就是范数平方**：`normSq v = ‖v‖²`。

证明：`‖v‖² = re ⟪v, v⟫`（`InnerProductSpace.norm_sq_eq_inner`），
在 `EuclideanSpace ℝ (Fin n)` 上内积按坐标展开为 `∑ᵢ vᵢ·vᵢ`（`PiLp.inner_apply`），
与 `∑ᵢ vᵢ²` 逐项一致。 -/
lemma normSq_eq_norm_sq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    normSq v = ‖v‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_inner (𝕜 := ℝ)]
  simp only [normSq, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_apply,
    Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `normSq` 非负。 -/
lemma normSq_nonneg_euclid {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ normSq v := by
  rw [normSq_eq_norm_sq]
  exact sq_nonneg _

/-- `v ≠ 0 ⟹ normSq v > 0`。 -/
lemma normSq_pos_euclid {n : ℕ} {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) : 0 < normSq v := by
  rw [normSq_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hv) 2

/-! ## 二、主定理：点式正定 ⟹ 显式模数 -/

/-- **单位球面非空**（`n > 0`）：取坐标基向量 `EuclideanSpace.single i 1`，其范数为 1。 -/
lemma sphere_one_nonempty {n : ℕ} (hn : 0 < n) :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact ⟨EuclideanSpace.single (Classical.arbitrary (Fin n)) 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    simp⟩

/-- **主定理（补 RealHessian 的缺口）**：设 `M` 点式正定（`PosDefQ M`），`n > 0`，
则**存在显式模数** `μ > 0` 使
    `∀ v : EuclideanSpace ℝ (Fin n), μ · normSq v ≤ quadForm M v`。

模数取为单位球面上的最小值 `μ = quadForm M x`（`x` 由极值定理给出）。

证明（有限维紧性）：
  1. `Metric.sphere 0 1` 紧（`isCompact_sphere`）且非空（`sphere_one_nonempty`）；
  2. `quadForm M` 连续（`continuous_quadForm`），由 `IsCompact.exists_isMinOn` 得极小点 `x`；
  3. `x ∈ sphere` ⟹ `‖x‖ = 1` ⟹ `normSq x = 1` ⟹ `x ≠ 0` ⟹ `quadForm M x > 0`（点式正定）；
  4. 对 `v ≠ 0`：`u := ‖v‖⁻¹ • v` 满足 `normSq u = 1`（在球面上），故
     `μ ≤ quadForm M u = ‖v‖⁻² · quadForm M v`，两边乘 `‖v‖² > 0` 即得结论；
  5. `v = 0`：`normSq 0 = 0 ≤ quadForm M 0 = 0`。 -/
theorem exists_modulus_of_posDef {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hpd : PosDefQ M) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ v : EuclideanSpace ℝ (Fin n), μ * normSq v ≤ quadForm M v := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  -- 极值定理：单位球面上的最小点
  have hK : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := isCompact_sphere 0 1
  have hcont : ContinuousOn (fun v : EuclideanSpace ℝ (Fin n) => quadForm M v)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := (continuous_quadForm M).continuousOn
  obtain ⟨x, hx, hxmin⟩ := hK.exists_isMinOn (sphere_one_nonempty hn) hcont
  -- x 在球面上 ⟹ normSq x = 1 ⟹ x ≠ 0
  have hxnorm : ‖x‖ = 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
    exact hx
  have hx1 : normSq x = 1 := by rw [normSq_eq_norm_sq, hxnorm, one_pow]
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, normSq] at hx1
    simp at hx1
  refine ⟨quadForm M x, hpd x hxne, ?_⟩
  intro v
  by_cases hv : v = 0
  · -- v = 0：两边为 0
    rw [hv]
    simp [normSq, quadForm]
  · -- v ≠ 0：归一化到球面
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hne' : ‖v‖ ≠ 0 := ne_of_gt hvpos
    -- u := ‖v‖⁻¹ • v 在球面上
    have hu_sphere : (‖v‖⁻¹ • v) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hvpos), inv_mul_cancel₀ hne']
    have hmin_u := hxmin hu_sphere
    -- 齐次性走 normSq 路线：比较 μ ≤ q(u) 与 q(v) 的尺度关系
    -- 记 q := quadForm M，先证 q(u) 与 q(v) 的关系
    have hsmul : quadForm M (‖v‖⁻¹ • v) = ‖v‖⁻¹ * ‖v‖⁻¹ * quadForm M v := by
      unfold quadForm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    -- μ ≤ ‖v‖⁻² · q(v)，乘 ‖v‖² 得 μ·‖v‖² ≤ q(v)
    have hμle : quadForm M x ≤ ‖v‖⁻¹ * ‖v‖⁻¹ * quadForm M v := by
      rw [← hsmul]
      exact hmin_u
    have hsq : ‖v‖ * ‖v‖ * (‖v‖⁻¹ * ‖v‖⁻¹) = 1 := by
      field_simp
    -- 把右式的系数合并成 (‖v‖⁻¹ * ‖v‖⁻¹ * q(v)) * (‖v‖*‖v‖) = q(v)
    have hstep : (‖v‖⁻¹ * ‖v‖⁻¹) * (‖v‖ * ‖v‖) = 1 := by
      rw [mul_comm (‖v‖⁻¹ * ‖v‖⁻¹) (‖v‖ * ‖v‖)]
      exact hsq
    have hmain : quadForm M x * (‖v‖ * ‖v‖) ≤ quadForm M v := by
      have hnp : (0 : ℝ) ≤ ‖v‖ * ‖v‖ := by positivity
      have h1 : quadForm M x * (‖v‖ * ‖v‖)
          ≤ (‖v‖⁻¹ * ‖v‖⁻¹ * quadForm M v) * (‖v‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right hμle hnp
      have h2 : ‖v‖⁻¹ * ‖v‖⁻¹ * quadForm M v * (‖v‖ * ‖v‖) = quadForm M v := by
        have hc : ‖v‖⁻¹ * ‖v‖⁻¹ * (‖v‖ * ‖v‖) = 1 := hstep
        calc ‖v‖⁻¹ * ‖v‖⁻¹ * quadForm M v * (‖v‖ * ‖v‖)
            = (‖v‖⁻¹ * ‖v‖⁻¹ * (‖v‖ * ‖v‖)) * quadForm M v := by ring
          _ = 1 * quadForm M v := by rw [hc]
          _ = quadForm M v := by ring
      linarith [h1, h2]
    rw [normSq_eq_norm_sq, sq]
    linarith [hmain]

/-! ## 三、回收 RealHessian 的假设形式 -/

/-- **模数界（RealHessian 假设形式的无条件版）**：点式正定 `H` 直接给出
`RealHessian.quadratic_lower_bound_of_posdef` 所需的假设
`∀v, μ * normSq v ≤ quadForm H v`（不再需要外部提供 μ）。 -/
theorem modulus_of_posDef_bound {n : ℕ} (hn : 0 < n) {H : Matrix (Fin n) (Fin n) ℝ}
    (hpd : PosDefQ H) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ v : EuclideanSpace ℝ (Fin n), μ * normSq v ≤ quadForm H v :=
  exists_modulus_of_posDef hn H hpd

/-- **二阶充分条件（去模数版）**：把 `RealHessian.second_order_sufficient_multidim` 的
**两个假设**（模数 `hμ : 0 < μ` 与一致正定 `hH`）合并为一条**点式正定** `PosDefQ H`，
余下只需 Taylor 型二次下界。

结论与 RealHessian 版完全一致：`∀ y ≠ x, F x < F y`（全局严格极小）。
证明：由 `exists_modulus_of_posDef` 取得显式 μ > 0 与模数界，再调用
`RealHessian.second_order_sufficient_multidim`。 -/
theorem second_order_sufficient_multidim_unconditional {n : ℕ} (hn : 0 < n)
    {F : (Fin n → ℝ) → ℝ} {H : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hpd : PosDefQ H)
    (hTaylor : ∀ v : Fin n → ℝ, F x + (1 / 2) * quadForm H v ≤ F (x + v)) :
    ∀ y : Fin n → ℝ, y ≠ x → F x < F y := by
  obtain ⟨μ, hμpos, hH⟩ := exists_modulus_of_posDef hn H hpd
  exact second_order_sufficient_multidim hμpos hH hTaylor

/-! ## 四、与 RealHessian 的对照（含二维闭式特例）

`RealHessian` 已给出 2×2 的 Sylvester 判据 `two_dim_posdef_iff`：
`PosDefQ (sym2 a b d) ↔ 0 < a ∧ 0 < a·d − b²`。
把它与本文件的主定理组合，可得到二维的**显式模数存在性**——这是闭式判据与
紧性论证两条路线的一致性检查。 -/

/-- **二维：Sylvester 判据 ⟹ 显式模数存在**。
由 `RealHessian.two_dim_posdef_iff` 把 `0 < a ∧ 0 < a·d − b²` 转成 `PosDefQ`，
再用主定理取得模数（`n = 2 > 0`）。 -/
theorem modulus_two_dim_of_sylvester {a b d : ℝ} (ha : 0 < a) (hdet : 0 < a * d - b * b) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ v : EuclideanSpace ℝ (Fin 2), μ * normSq v ≤ quadForm (sym2 a b d) v :=
  exists_modulus_of_posDef (by norm_num) (sym2 a b d)
    ((two_dim_posdef_iff a b d).mpr ⟨ha, hdet⟩)

end Lattice
