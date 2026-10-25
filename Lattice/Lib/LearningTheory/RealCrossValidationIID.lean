import Mathlib
import Lattice.Lib.LearningTheory.RealCrossValidation
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: i.i.d. 版交叉验证 —— 边缘均匀性、无偏性与偏差-方差分解

方向（§5 验证行「交叉验证」）：`RealCrossValidation` 在**有限总体**上用
「划分 + 等大小折」代替 i.i.d. 抽样，并明确标注「i.i.d. 抽样未被形式化」。
本文件补齐这一缺口：把验证样本建模为**均匀乘积空间** `w : Fin m → α`
（`α` 有限，均匀计数测度 `uniformExpectation X = (∑ x, X x)/|α|`），
这正是 m 重独立同分布（i.i.d.）乘积空间：独立性体现为单坐标边缘分布
仍是均匀分布（`uniformExpectation_marginal`），从而经验风险对总体风险
**无偏**。

## 主结果

1. `empRisk` / `popRisk`：经验风险 `(1/m)Σ i, Z (w i)` 与总体风险 `EZ`。
2. **主引理（边缘分布是均匀的）** `uniformExpectation_marginal`：
   对任意坐标 `i : Fin m`（`m > 0`），
   `E_w[ Z (w i) ] = E_z[ Z z ]`。
   这正是「i.i.d. 乘积空间」的精确有限计数内容：任何一个坐标的边缘分布
   与单次抽样分布一致。证明：递推因子化
   `|α|·Σ_w Z (w i) = |α|^m · Σ_z Z z`（对 m 归纳，用首坐标分解
   `(Fin (n+1) → α) ≃ α × (Fin n → α)` 与 `Fintype.sum_equiv`），再约去 `|α|`。
3. **主结果（无偏性）** `cv_iid_unbiased`：
   `E_w[ empRisk Z w ] = popRisk Z`（`m > 0`）。
4. **主结果（偏差-方差分解）** `cv_bias_variance_decomposition`：
   `E[(X − R)²] = variance X + (EX − R)²`（`Ω` 非空）。
5. **主结果（k 折方差随 k 减小，定量）** `cv_kfold_variance_le`：
   在显式**不相关假设** `huncorr`（折间偏差乘积期望为 0）下，
   `variance ((1/k)Σ_j Y_j) ≤ (1/k)·σ2`；
   并由 `cv_variance_decreasing` 得 `σ2/k2 ≤ σ2/k1`（`k1 ≤ k2`）。
6. `cv_kfold_unbiased`：`E[(1/k)Σ_j Y_j] = R`（由各折无偏）。
7. `cv_kfold_variance_bound_bias`：结合 4 与 5，
   `E[(cv_k − R)²] ≤ σ2/k + Bias_k²`，`Bias_k = E[cv_k] − R`。

## 诚实边界

- **去掉 `huncorr` 后 `cv_kfold_variance_le` 的结论会失败（B11 结论，机器验证）**：
  `no_uncorr_counterexample` 给出具体反例（两折完全相同、各折方差为 1 时，
  平均值的方差仍是 1 > 1/2）。该反例采用存在量词，只断言**存在**一个方差上界
  `σ2` 使结论失败，并不断言无 `huncorr` 时 `cv_kfold_variance_le` 恒假；
  反例的构造满足 `hmean`（各折期望均为 `R`，取 `R = 0`），故足以说明
  「方差 ≤ σ2/k」这一收益**依赖折间不相关**。故 B11 的结论是
  **「保留该假设并给出其必要性的机器验证反例」**，而不是「去掉」。
- `uniformExpectation_marginal` **形式化了 i.i.d. 有限乘积空间**：
  样本空间是 `Fin m → α` 上的均匀计数测度，其单坐标边缘是均匀的。
  与 `RealCrossValidation` 的「有限总体划分」模型互补；交叉验证文件中的
  相应表述不再重复展开（见上文「主结果」第 2 条与文末「闭环语义」注）。
- **折间独立性/不相关性是显式假设**（`huncorr`），不是推导出来的：
  本文件按任务要求把它作为 `cv_kfold_variance_le` 的显式前提并标注
  「显式假设」；这避免了伪造独立性。
- `cv_kfold_variance_le` 的 `hvar`（各折方差 ≤ σ2）同样是显式假设。
- `uniformExpectation_const` / `uniformExpectation_centered` /
  `cv_bias_variance_decomposition` 需要 `[Nonempty Ω]`（常数期望 `E[c] = c`
  需要样本数非零）；`uniformExpectation_marginal` **不需要**非空假设
  （空 `α` 时两边都是 0，已单独处理）。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice.Lib.LearningTheory.RealCrossValidationIID

/-! ## 一、定义：经验风险与总体风险 -/

/-- 经验风险：`(1/m)·Σ_{i<m} Z (w i)`（`w : Fin m → α` 是大小为 m 的样本）。 -/
def empRisk {α : Type*} {m : ℕ} (Z : α → ℝ) (w : Fin m → α) : ℝ :=
  (1 / (m : ℝ)) * ∑ i : Fin m, Z (w i)

/-- 总体风险：`E[Z]`（沿用 `RealHoeffding` 的均匀计数期望）。 -/
def popRisk {α : Type*} [Fintype α] (Z : α → ℝ) : ℝ :=
  uniformExpectation Z

/-- 方差：`E[(X − EX)²]`。 -/
def variance {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  uniformExpectation (fun w => (X w - uniformExpectation X) ^ 2)

/-! ## 二、均匀期望的线性代数小引理（辅助） -/

/-- 常数倍线性：`E[c·X] = c·EX`。 -/
theorem uniformExpectation_const_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (X : Ω → ℝ) :
    uniformExpectation (fun w => c * X w) = c * uniformExpectation X := by
  unfold uniformExpectation
  rw [← Finset.mul_sum, mul_div_assoc]

/-- 有限和线性：`E[Σ_i F_i] = Σ_i E[F_i]`。 -/
theorem uniformExpectation_sum {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι]
    (F : ι → Ω → ℝ) :
    uniformExpectation (fun w => ∑ i, F i w) = ∑ i, uniformExpectation (F i) := by
  unfold uniformExpectation
  rw [Finset.sum_comm, Finset.sum_div]

/-- 加法线性：`E[X + Y] = EX + EY`。 -/
theorem uniformExpectation_add {Ω : Type*} [Fintype Ω] (X Y : Ω → ℝ) :
    uniformExpectation (fun w => X w + Y w) = uniformExpectation X + uniformExpectation Y := by
  unfold uniformExpectation
  rw [Finset.sum_add_distrib, add_div]

/-- 常数的期望：`E[c] = c`（需 `Ω` 非空，样本数非零）。 -/
theorem uniformExpectation_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformExpectation (fun _ : Ω => c) = c := by
  unfold uniformExpectation
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Fintype.card Ω : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := Ω))
  rw [div_eq_iff hN]
  ring

/-- 中心化变量的期望为零：`E[X − EX] = 0`（需 `Ω` 非空）。 -/
theorem uniformExpectation_centered {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    uniformExpectation (fun w => X w - uniformExpectation X) = 0 := by
  unfold uniformExpectation
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Fintype.card Ω : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := Ω))
  rw [div_eq_iff hN]
  rw [mul_comm (Fintype.card Ω : ℝ) ((∑ w : Ω, X w) / (Fintype.card Ω : ℝ)),
    div_mul_cancel₀ (∑ w : Ω, X w) hN]
  ring

/-! ## 三、i.i.d. 乘积空间：单坐标边缘分布是均匀的 -/

/-- 首坐标分解等价：`(Fin (n+1) → α) ≃ α × (Fin n → α)`，
`w ↦ (w 0, fun j ↦ w j.succ)`。用于对乘积空间的求和作归纳。 -/
def splitFinSucc (n : ℕ) (α : Type*) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun w := (w 0, fun j => w j.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv w := by
    funext k
    induction k using Fin.cases with
    | zero => simp
    | succ j => simp
  right_inv p := by
    obtain ⟨a, f⟩ := p
    refine Prod.ext ?_ ?_
    · simp
    · funext j
      simp

/-- **因子化（辅助）**：`|α|·Σ_{w} Z (w i) = |α|^m · Σ_x Z x`。
对 `m` 归纳：`m = 0` 时 `Fin 0` 为空；`m+1` 时用 `splitFinSucc` 拆出首坐标，
首坐标为 `0` 的情形内层和是常数 `Σ_x Z x`，为 `j.succ` 的情形用归纳假设。
两边同乘 `|α|` 是为了避免除以 `|α|`（`α` 可能为空）。 -/
theorem sum_marginal_mul_card {α : Type*} [Fintype α] (m : ℕ) (Z : α → ℝ) :
    ∀ i : Fin m,
      (Fintype.card α : ℝ) * (∑ w : Fin m → α, Z (w i))
        = (Fintype.card α : ℝ) ^ m * (∑ x : α, Z x) := by
  induction m with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i
    induction i using Fin.cases with
    | zero =>
      have h1 : (∑ w : Fin (n + 1) → α, Z (w 0))
          = ∑ p : α × (Fin n → α), Z p.1 :=
        Fintype.sum_equiv (splitFinSucc n α) (fun w => Z (w 0)) (fun p => Z p.1)
          (fun w => by simp [splitFinSucc])
      rw [h1, Fintype.sum_prod_type]
      have hinner : ∀ a : α, (∑ _q : Fin n → α, Z a)
          = (Fintype.card α : ℝ) ^ n * Z a := by
        intro a
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi_const,
          Nat.cast_pow]
      have hfact : (∑ a : α, ∑ _q : Fin n → α, Z a)
          = (Fintype.card α : ℝ) ^ n * (∑ a : α, Z a) := by
        rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.mul_sum]
      rw [hfact, pow_succ]
      ring
    | succ j =>
      have h1 : (∑ w : Fin (n + 1) → α, Z (w j.succ))
          = ∑ p : α × (Fin n → α), Z (p.2 j) :=
        Fintype.sum_equiv (splitFinSucc n α) (fun w => Z (w j.succ)) (fun p => Z (p.2 j))
          (fun w => by simp [splitFinSucc])
      rw [h1, Fintype.sum_prod_type]
      have h2 : (∑ _a : α, ∑ q : Fin n → α, Z (q j))
          = (Fintype.card α : ℝ) * (∑ q : Fin n → α, Z (q j)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [h2, ih j, pow_succ]
      ring

/-- **主引理：i.i.d. 乘积空间的单坐标边缘分布是均匀的**。
对任意 `i : Fin m`（`m > 0`），`E_w[ Z (w i) ] = E_z[ Z z ]`。
证明：由 `sum_marginal_mul_card` 的因子化，分 `|α| = 0`（两边都是 0）
与 `|α| > 0`（约去 `|α| = |α|^m / |α|^(m-1)` 侧的公因子）两种情形。 -/
theorem uniformExpectation_marginal {α : Type*} [Fintype α] {m : ℕ} (hm : 0 < m)
    (Z : α → ℝ) (i : Fin m) :
    uniformExpectation (fun w : Fin m → α => Z (w i)) = uniformExpectation Z := by
  rcases eq_or_ne (Fintype.card α) 0 with h0 | h0
  · haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp h0
    haveI : IsEmpty (Fin m → α) := ⟨fun w => isEmptyElim (w ⟨0, hm⟩)⟩
    have hcard0 : Fintype.card (Fin m → α) = 0 := Fintype.card_eq_zero_iff.mpr inferInstance
    simp [uniformExpectation, h0, hcard0]
  · have hA : ((Fintype.card α : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0
    have hcard : (Fintype.card (Fin m → α) : ℝ) = (Fintype.card α : ℝ) ^ m := by
      rw [Fintype.card_pi_const, Nat.cast_pow]
    have haux := sum_marginal_mul_card m Z i
    unfold uniformExpectation
    rw [hcard, div_eq_div_iff (pow_ne_zero m hA) hA]
    calc (∑ w : Fin m → α, Z (w i)) * (Fintype.card α : ℝ)
        = (Fintype.card α : ℝ) * (∑ w : Fin m → α, Z (w i)) := by ring
      _ = (Fintype.card α : ℝ) ^ m * (∑ x : α, Z x) := haux
      _ = (∑ x : α, Z x) * (Fintype.card α : ℝ) ^ m := by ring

/-! ## 四、主结果：i.i.d. 经验风险对总体风险无偏 -/

/-- **主结果：i.i.d. 版 CV 无偏性**。经验风险 `empRisk Z w` 的期望等于总体风险
`popRisk Z`（`m > 0`）：由 `uniformExpectation_marginal` 逐坐标
`E_w[Z (w i)] = E_z[Z z]` + 和的线性性得到。 -/
theorem cv_iid_unbiased {α : Type*} [Fintype α] {m : ℕ} (hm : 0 < m) (Z : α → ℝ) :
    uniformExpectation (fun w : Fin m → α => empRisk Z w) = popRisk Z := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  change uniformExpectation (fun w : Fin m → α => (1 / (m : ℝ)) * ∑ i : Fin m, Z (w i))
    = popRisk Z
  rw [uniformExpectation_const_mul, uniformExpectation_sum]
  have h2 : (∑ i : Fin m, uniformExpectation (fun w : Fin m → α => Z (w i)))
      = ∑ _i : Fin m, popRisk Z :=
    Finset.sum_congr rfl (fun i _ => uniformExpectation_marginal hm Z i)
  rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold popRisk
  rw [one_div, inv_mul_cancel_left₀ hmR]

/-! ## 五、主结果：偏差-方差分解 -/

/-- **主结果：偏差-方差分解**。`E[(X − R)²] = variance X + (EX − R)²`。
展开 `(X − R) = (X − EX) + (EX − R)`，交叉项由
`E[X − EX] = 0` 消失（`uniformExpectation_centered`），常数项由
`uniformExpectation_const` 提出。需 `Ω` 非空。 -/
theorem cv_bias_variance_decomposition {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ)
    (R : ℝ) :
    uniformExpectation (fun w => (X w - R) ^ 2) = variance X + (uniformExpectation X - R) ^ 2 := by
  have hXc : uniformExpectation (fun w : Ω => X w - uniformExpectation X) = 0 :=
    uniformExpectation_centered X
  have hcv : uniformExpectation (fun _ : Ω => (uniformExpectation X - R) ^ 2)
      = (uniformExpectation X - R) ^ 2 := uniformExpectation_const _
  have hkey : (fun w : Ω => (X w - R) ^ 2)
      = fun w => (X w - uniformExpectation X) ^ 2
          + (2 * (X w - uniformExpectation X) * (uniformExpectation X - R)
              + (uniformExpectation X - R) ^ 2) := by
    funext w
    ring
  calc uniformExpectation (fun w : Ω => (X w - R) ^ 2)
      = uniformExpectation (fun w => (X w - uniformExpectation X) ^ 2
          + (2 * (X w - uniformExpectation X) * (uniformExpectation X - R)
              + (uniformExpectation X - R) ^ 2)) := by rw [hkey]
    _ = uniformExpectation (fun w => (X w - uniformExpectation X) ^ 2)
          + uniformExpectation (fun w => 2 * (X w - uniformExpectation X)
              * (uniformExpectation X - R) + (uniformExpectation X - R) ^ 2) :=
          uniformExpectation_add _ _
    _ = uniformExpectation (fun w => (X w - uniformExpectation X) ^ 2)
          + (uniformExpectation (fun w => 2 * (X w - uniformExpectation X)
                * (uniformExpectation X - R))
              + uniformExpectation (fun _ : Ω => (uniformExpectation X - R) ^ 2)) := by
          rw [uniformExpectation_add]
    _ = uniformExpectation (fun w => (X w - uniformExpectation X) ^ 2)
          + (2 * (uniformExpectation X - R)
                * uniformExpectation (fun w => X w - uniformExpectation X)
              + (uniformExpectation X - R) ^ 2) := by
          rw [show (fun w : Ω => 2 * (X w - uniformExpectation X)
                * (uniformExpectation X - R))
              = fun w => (2 * (uniformExpectation X - R))
                  * (X w - uniformExpectation X) by
                funext w; ring]
          rw [uniformExpectation_const_mul, hcv]
    _ = uniformExpectation (fun w => (X w - uniformExpectation X) ^ 2)
          + (2 * (uniformExpectation X - R) * 0 + (uniformExpectation X - R) ^ 2) := by rw [hXc]
    _ = variance X + (uniformExpectation X - R) ^ 2 := by
          unfold variance
          rw [mul_zero, zero_add]

/-! ### 六-0、**B11：`huncorr` 不能去掉**（机器验证反例）

ROADMAP 的 B11 要求「CV 去 `huncorr`」。**代入检验的结论是该假设不可去**。

取 `Ω = Fin 2`（均匀计数测度）、`k = 2`，两折**完全相同** `Y 0 = Y 1 = X`
（最极端的正相关），则：
* 各折期望相同、方差都等于 `variance X`；
* 折间协方差 `E[(Y 0 − R)(Y 1 − R)] = variance X ≠ 0`，即 `huncorr` **失效**；
* 而平均值 `(Y 0 + Y 1)/2 = X` 的方差仍是 `variance X`，
  **大于** `σ2/2 = variance X / 2`（当 `variance X > 0`）。

所以 `cv_kfold_variance_le` 的结论在无 `huncorr` 时**为假**：
「随 `k` 减小」这一收益完全依赖折间不相关。
下面 `no_uncorr_counterexample` 给出可在内核验证的具体反例。 -/

/-- **B11 反例（机器验证）：去掉 `huncorr` 后命题为假**。
在 `Ω = Fin 2` 上取 `X w = if w = 0 then −1 else 1`，则 `E[X] = 0`、`variance X = 1`
（`uniformExpectation` 为 `Fin 2` 上的平均）。令 `k = 2`、两折都是 `X`，则

    variance ((1/2)·Σ_j Y j) = 1 > 1/2 = (1/k)·σ2,

其中 `σ2 = 1` 是各折方差。故 `huncorr` **不可去**（诚实标注）。 -/
theorem no_uncorr_counterexample :
    ∃ (Y : Fin 2 → Fin 2 → ℝ) (σ2 : ℝ),
      (∀ j, variance (Y j) ≤ σ2) ∧
      ¬ (variance (fun w => (1 / (2 : ℝ)) * ∑ j : Fin 2, Y j w) ≤ (1 / (2 : ℝ)) * σ2) := by
  -- 取 `X w = if w = 0 then -1 else 1`，两折同为 `X`，`σ2 = 1`。
  refine ⟨fun _ w => if w = 0 then -1 else 1, 1, ?_, ?_⟩
  · -- 各折方差恰为 1（`E[X] = 0`，`E[X²] = 1`）
    intro j
    have hE : uniformExpectation (fun w : Fin 2 => (if w = 0 then (-1 : ℝ) else 1)) = 0 := by
      unfold uniformExpectation
      rw [Fin.sum_univ_two]
      norm_num
    unfold variance
    rw [hE]
    unfold uniformExpectation
    rw [Fin.sum_univ_two]
    norm_num
  · -- 平均值恰为 `X`（两折相同），方差为 1 > 1/2
    intro hcon
    have hsum : (fun w : Fin 2 => (1 / (2 : ℝ))
        * ∑ j : Fin 2, (if w = 0 then (-1 : ℝ) else 1))
        = fun w : Fin 2 => if w = 0 then (-1 : ℝ) else 1 := by
      funext w
      rw [Fin.sum_univ_two]
      ring
    rw [hsum] at hcon
    have hE : uniformExpectation (fun w : Fin 2 => (if w = 0 then (-1 : ℝ) else 1)) = 0 := by
      unfold uniformExpectation
      rw [Fin.sum_univ_two]
      norm_num
    have hvar1 : variance (fun w : Fin 2 => (if w = 0 then (-1 : ℝ) else 1)) = 1 := by
      unfold variance
      rw [hE]
      unfold uniformExpectation
      rw [Fin.sum_univ_two]
      norm_num
    rw [hvar1] at hcon
    norm_num at hcon

/-- **k 折无偏性**：各折 `Y j` 的期望都是 `R` ⟹ 均值 `(1/k)Σ_j Y_j` 的期望也是 `R`。 -/
theorem cv_kfold_unbiased {Ω : Type*} [Fintype Ω] {k : ℕ} (Y : Fin k → Ω → ℝ) (R : ℝ)
    (hk : 0 < k) (hmean : ∀ j, uniformExpectation (Y j) = R) :
    uniformExpectation (fun w => (1 / (k : ℝ)) * ∑ j : Fin k, Y j w) = R := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  rw [uniformExpectation_const_mul, uniformExpectation_sum]
  have hsum : (∑ j : Fin k, uniformExpectation (Y j)) = ∑ _j : Fin k, R :=
    Finset.sum_congr rfl (fun j _ => hmean j)
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [one_div, inv_mul_cancel_left₀ hkR]

/-- **对角线 + 非对角线求和界（辅助）**：若对角项 `E[A_j²] ≤ σ2`、非对角项
`E[A_j A_l] = 0`（`j ≠ l`），则 `E[(Σ_j A_j)²] ≤ k·σ2`。
证明：`(Σ A_j)² = Σ_j Σ_l A_j A_l`，逐次用和的线性性，
内层由 `Finset.sum_eq_single` 只剩对角项。 -/
theorem uniformExpectation_sq_sum_le {Ω : Type*} [Fintype Ω] {k : ℕ} (A : Fin k → Ω → ℝ)
    (σ2 : ℝ)
    (hdiag : ∀ j, uniformExpectation (fun w => (A j w) ^ 2) ≤ σ2)
    (hoff : ∀ j l, j ≠ l → uniformExpectation (fun w => A j w * A l w) = 0) :
    uniformExpectation (fun w => (∑ j : Fin k, A j w) ^ 2) ≤ (k : ℝ) * σ2 := by
  have hsq : (fun w : Ω => (∑ j : Fin k, A j w) ^ 2)
      = fun w => ∑ j : Fin k, ∑ l : Fin k, A j w * A l w := by
    funext w
    rw [sq, Fintype.sum_mul_sum]
  rw [hsq]
  have hstep : ∀ j : Fin k, uniformExpectation (fun w => ∑ l : Fin k, A j w * A l w)
      = uniformExpectation (fun w => (A j w) ^ 2) := by
    intro j
    rw [uniformExpectation_sum]
    have hsingle : (∑ l : Fin k, uniformExpectation (fun w => A j w * A l w))
        = uniformExpectation (fun w => A j w * A j w) :=
      Finset.sum_eq_single j (fun l _ hl => hoff j l hl.symm)
        (fun h => absurd (Finset.mem_univ j) h)
    rw [hsingle]
    congr 1
    funext w
    ring
  rw [uniformExpectation_sum, Finset.sum_congr rfl (fun j _ => hstep j)]
  calc (∑ j : Fin k, uniformExpectation (fun w => (A j w) ^ 2))
      ≤ ∑ _j : Fin k, σ2 := Finset.sum_le_sum (fun j _ => hdiag j)
    _ = (k : ℝ) * σ2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **主结果：k 折平均的方差 ≤ σ2/k（显式假设）**。设各折期望都是 `R`、
各折方差 `≤ σ2`，且**折间不相关**（`huncorr`：`E[(Y_j−R)(Y_l−R)] = 0`，`j ≠ l`），则

    variance ((1/k)·Σ_j Y_j) ≤ (1/k)·σ2。

**诚实标注（显式假设）**：折间不相关 `huncorr` 与各折方差界 `hvar`
都是**显式前提**，不是从 i.i.d. 推出的——本文件只把
`uniformExpectation_marginal`（单坐标边缘均匀性）形式化，
真正跨折的独立性是额外假设。 -/
theorem cv_kfold_variance_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] {k : ℕ}
    (Y : Fin k → Ω → ℝ) (R σ2 : ℝ) (hk : 0 < k)
    (hmean : ∀ j, uniformExpectation (Y j) = R)
    (hvar : ∀ j, variance (Y j) ≤ σ2)
    (huncorr : ∀ j l, j ≠ l → uniformExpectation (fun w => (Y j w - R) * (Y l w - R)) = 0) :
    variance (fun w => (1 / (k : ℝ)) * ∑ j : Fin k, Y j w) ≤ (1 / (k : ℝ)) * σ2 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hmean_avg : uniformExpectation (fun w => (1 / (k : ℝ)) * ∑ j : Fin k, Y j w) = R :=
    cv_kfold_unbiased Y R hk hmean
  have hvar_eq : ∀ j, variance (Y j) = uniformExpectation (fun w => (Y j w - R) ^ 2) := by
    intro j
    unfold variance
    rw [hmean j]
  have hdecomp : ∀ w, (1 / (k : ℝ)) * (∑ j : Fin k, Y j w) - R
      = (1 / (k : ℝ)) * ∑ j : Fin k, (Y j w - R) := by
    intro w
    have hsumR : (∑ _j : Fin k, (R : ℝ)) = (k : ℝ) * R := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_sub_distrib, hsumR, mul_sub, one_div, inv_mul_cancel_left₀ hkR]
  calc variance (fun w => (1 / (k : ℝ)) * ∑ j : Fin k, Y j w)
      = uniformExpectation (fun w => ((1 / (k : ℝ)) * ∑ j : Fin k, Y j w - R) ^ 2) := by
          unfold variance
          rw [hmean_avg]
    _ = uniformExpectation (fun w => ((1 / (k : ℝ)) * ∑ j : Fin k, (Y j w - R)) ^ 2) := by
          apply congrArg uniformExpectation
          funext w
          rw [hdecomp w]
    _ = (1 / (k : ℝ)) ^ 2
          * uniformExpectation (fun w => (∑ j : Fin k, (Y j w - R)) ^ 2) := by
          rw [show (fun w : Ω => ((1 / (k : ℝ)) * ∑ j : Fin k, (Y j w - R)) ^ 2)
              = fun w => (1 / (k : ℝ)) ^ 2 * (∑ j : Fin k, (Y j w - R)) ^ 2 by
                funext w; ring]
          rw [uniformExpectation_const_mul]
    _ ≤ (1 / (k : ℝ)) ^ 2 * ((k : ℝ) * σ2) := by
          apply mul_le_mul_of_nonneg_left
          · exact uniformExpectation_sq_sum_le (fun j w => Y j w - R) σ2
              (fun j => by rw [← hvar_eq j]; exact hvar j)
              (fun j l h => huncorr j l h)
          · exact sq_nonneg _
    _ = (1 / (k : ℝ)) * σ2 := by
          rw [one_div]
          calc ((k : ℝ)⁻¹) ^ 2 * ((k : ℝ) * σ2)
              = ((k : ℝ)⁻¹) * (((k : ℝ)⁻¹) * ((k : ℝ) * σ2)) := by ring
            _ = ((k : ℝ)⁻¹) * σ2 := by rw [inv_mul_cancel_left₀ hkR]

/-- **k 增大 ⟹ 方差上界减小**：`1 ≤ k1 ≤ k2`、`0 ≤ σ2` ⟹
`σ2/k2 ≤ σ2/k1`（即 `(1/k2)·σ2 ≤ (1/k1)·σ2`）。 -/
theorem cv_variance_decreasing (k1 k2 : ℕ) (σ2 : ℝ) (hk1 : 1 ≤ k1) (h12 : k1 ≤ k2)
    (hσ : 0 ≤ σ2) :
    σ2 / (k2 : ℝ) ≤ σ2 / (k1 : ℝ) := by
  have hk1R : (0 : ℝ) < (k1 : ℝ) := by exact_mod_cast hk1
  have h12R : (k1 : ℝ) ≤ (k2 : ℝ) := by exact_mod_cast h12
  have h : 1 / (k2 : ℝ) ≤ 1 / (k1 : ℝ) := one_div_le_one_div_of_le hk1R h12R
  calc σ2 / (k2 : ℝ) = σ2 * (1 / (k2 : ℝ)) := by ring
    _ ≤ σ2 * (1 / (k1 : ℝ)) := mul_le_mul_of_nonneg_left h hσ
    _ = σ2 / (k1 : ℝ) := by ring

/-- **主结果：偏差-方差合成界**。结合偏差-方差分解（`cv_bias_variance_decomposition`）
与 k 折方差界（`cv_kfold_variance_le`）：

    E[(cv_k − R)²] ≤ σ2/k + Bias_k²,   Bias_k = E[cv_k] − R。

**诚实标注（显式假设）**：同 `cv_kfold_variance_le`：
`hvar`（各折方差 ≤ σ2）与 `huncorr`（折间不相关）是显式前提。 -/
theorem cv_kfold_variance_bound_bias {Ω : Type*} [Fintype Ω] [Nonempty Ω] {k : ℕ}
    (Y : Fin k → Ω → ℝ) (R σ2 : ℝ) (hk : 0 < k)
    (hmean : ∀ j, uniformExpectation (Y j) = R)
    (hvar : ∀ j, variance (Y j) ≤ σ2)
    (huncorr : ∀ j l, j ≠ l → uniformExpectation (fun w => (Y j w - R) * (Y l w - R)) = 0) :
    uniformExpectation (fun w => ((1 / (k : ℝ)) * ∑ j : Fin k, Y j w - R) ^ 2)
      ≤ (1 / (k : ℝ)) * σ2
        + (uniformExpectation (fun w => (1 / (k : ℝ)) * ∑ j : Fin k, Y j w) - R) ^ 2 := by
  have h1 : variance (fun w => (1 / (k : ℝ)) * ∑ j : Fin k, Y j w) ≤ (1 / (k : ℝ)) * σ2 :=
    cv_kfold_variance_le Y R σ2 hk hmean hvar huncorr
  have h2 : uniformExpectation (fun w => ((1 / (k : ℝ)) * ∑ j : Fin k, Y j w - R) ^ 2)
      = variance (fun w => (1 / (k : ℝ)) * ∑ j : Fin k, Y j w)
        + (uniformExpectation (fun w => (1 / (k : ℝ)) * ∑ j : Fin k, Y j w) - R) ^ 2 :=
    cv_bias_variance_decomposition _ R
  rw [h2]
  linarith

/-! ## 注：闭环语义

  `empRisk` / `popRisk`（经验/总体风险）→
  `uniformExpectation_marginal`（**i.i.d. 乘积空间单坐标边缘均匀性**，
  补齐 `RealCrossValidation` 标注的「i.i.d. 抽样未被形式化」）→
  `cv_iid_unbiased`（经验风险对总体风险无偏）→
  `variance` / `cv_bias_variance_decomposition`（偏差-方差分解）→
  `cv_kfold_unbiased`（k 折无偏）→
  `cv_kfold_variance_le`（方差 ≤ σ2/k，**显式不相关假设 `huncorr`**）→
  `cv_variance_decreasing`（k 越大上界越小）→
  `cv_kfold_variance_bound_bias`（偏差-方差合成界）。

  与 `RealCrossValidation` 的关系：那边是「有限总体划分 + 等大小折」的
  组合恒等式（CV 风险 = 全样本风险）；本文件补上**概率/期望**层面的 i.i.d. 内容
  ——边缘均匀性（独立性）与无偏性、方差随 k 的定量下降。
  诚实地讲：真正跨折的独立性在本文件中是**显式假设** `huncorr`，
  只有单坐标边缘分布是从乘积空间结构证明的。 -/

end Lattice.Lib.LearningTheory.RealCrossValidationIID
