import Mathlib
import Lattice.Lib.Convex.RealConvexToolkit
import Lattice.Lib.InfoTheory.RealDataProcessing
/-!
# LATTICE: log-sum 不等式的**等号情形** —— 补上 DPI 等号刻画的正向缺口

`RealDPIComplete.lean` 第 31–48 行把 DPI 的完整等号刻画 `dp_eq_iff` 明确标注为
**未证**，并指出缺口正是 `RealDataProcessing.logsum_le` 的**等号情形分析**，具体需要：

> 逐输出 b 的 log-sum 差 `gap_b = Σ_a z_ab·(log A_ab − (1 − A_ab⁻¹))`
> （`A_ab = z_ab·r_b/(z'_ab·m_b)`）每项非负且 `= 0 ⟺ A_ab = 1`，
> 故 `gap = 0 ⟺ 所有 A_ab = 1`（或 `z_ab = 0`）。
> 形式化需要把 `logsum_le` 证明内部的恒等式
> `Σ_a z_ab·(1 − A_ab⁻¹) = 0` 提取出来，并补 `log x = 1 − x⁻¹ ⟹ x = 1` 的等号情形。

**历史沿革 / 已否证（对「缺口至今空缺」的更正）**：上述 `RealDPIComplete.lean` 的登记是
该文件写作时的状态；同库 `RealDPIEquality.lean` 后来已声明补上同一缺口，并给出完整 iff
`RealDPIEquality.dp_eq_iff_ratio_constant`（`KL(pK‖qK) = KL(p‖q) ⟺ ratioConstant K p q`，
由该文件正向 + `RealDPIComplete.dp_eq_of_ratio_constant` 后向合成）。因此
「DPI 等号刻画的正向缺口未证」这一表述**已否证**，不宜再作为当前结论引用。

**本文件补上的是该缺口中的标量 / log-sum 层判据**（标量核心 + log-sum 等号判据 + 归一化推论）：
把 `RealDataProcessing.logsum_le` 的等号情形独立成可实例化的定理，供下游逐输出符号实例化
组装信道层的 `dp_eq_iff`。

## 数学内容

记 `z z' : ι → ℝ`，`m = Σz`，`r = Σz'`，`R = m/r`，`rho i = z i / z' i`，`u i = rho i / R`。

1. **标量核心**（`0 < u`）：
   - `mul_log_sub_add_nonneg`：`0 ≤ u·log u − u + 1`（由 `Real.one_sub_inv_le_log_of_pos` 乘 `u > 0`）；
   - `one_sub_inv_lt_log_of_pos_logsum`：`u ≠ 1 ⟹ 1 − u⁻¹ < log u`
     （在 `u⁻¹` 处用 `Real.log_lt_sub_one_of_pos`）；
   - `mul_log_sub_add_pos`：`u ≠ 1 ⟹ 0 < u·log u − u + 1`；
   - `mul_log_sub_add_eq_zero_iff` / `log_eq_one_sub_inv_iff_logsum`：
     `u·log u − u + 1 = 0 ⟺ u = 1` 与 `log u = 1 − u⁻¹ ⟺ u = 1`。
2. **等号判据（主定理）** `logsum_eq_iff_ratio_const`：
   `(Σz)·log((Σz)/(Σz')) = Σ z·log(z/z') ⟺ ∀ i, z i·(Σz') = z' i·(Σz)`，
   即**等号 ⟺ 比值 `z i / z' i` 恒等于 `(Σz)/(Σz')`**。
   正向（等号 ⟹ 比值常值）是本任务最高价值的一半，完整给出；
   反向（比值常值 ⟹ 等号）平凡，也完整给出。
3. **归一化推论** `logsum_eq_iff_eq_of_sum_eq`：在 `Σz = Σz'` 下等号 ⟺ `z = z'`。
4. **比值常值的等价叙述** `logsum_eq_iff_exists_ratio_const`：
   等号 ⟺ `∃ c > 0, ∀ i, z i / z' i = c`。

## 证明骨架（与 `RealDataProcessing.logsum_le` 同构，但提取等号）

`A i := z i·r/(z' i·m) = u i`。`logsum_le` 的证明内部已给出两条关键恒等式：

- `hdecomp`：`(Σ z·log(z/z')) − m·log(m/r) = Σ z·log(A i)`；
- `hzero`：`Σ z i·(1 − A i⁻¹) = 0`。

又每项 `z i·(1 − A i⁻¹) ≤ z i·log(A i)`（`log A ≥ 1 − A⁻¹` 乘 `z i > 0`）。
于是「等号」即 `Σ z·log(A i) = 0`，从而
`Σ (z i·log(A i) − z i·(1 − A i⁻¹)) = 0`，各项非负 ⟹ 逐项为 0
⟹ `log(A i) = 1 − A i⁻¹` ⟹ `A i = 1` ⟹ 交叉相乘得 `z i·r = z' i·m`。

## 诚实边界（`诚实` / `标注` / `未做`）

- **`未做`**：本文件仍假设 `z z'` **逐点严格正**。`RealDataProcessing.logsum_le` 的
  **含零版本**（`z i = 0` 或 `z' i = 0`，`0·log 0 = 0` 的边界延拓）未做；
  因此 DPI 等号刻画在**非严格正信道**下的完整版本仍未完成，是后续工作。
  本文件的等号分析中 `z i > 0` 用于「非负项之和为 0 ⟹ 逐项为 0」的除法消去，
  若允许 `z i = 0`，则该项强制条件消失（可退化），刻画需更精细的支撑集叙述。
- **`诚实`**：与 `RealEqualityCharacterization.log_eq_one_sub_inv_iff` 有**同义**的标量引理；
  为避免跨文件重名，此处一律使用 `_logsum` 后缀或 `mul_log_sub_add_*` 前缀命名，
  **不重定义**任何只读文件中的名字。
- **`降级` / `标注` / 历史沿革**：本文件**不**给出 `dp_eq_iff` 本身（那需要信道层的组装，且需
  把本文件的定理逐输出符号实例化）；本文件只交付其中被标注为缺口的
  **log-sum 等号判据**。这是有意的分工：下游可直接对本定理实例化。
  需注意：该缺口的**信道层**完整 iff 已由 `RealDPIEquality.dp_eq_iff_ratio_constant` 交付
  （见开头的「历史沿革 / 已否证」），故本文件不是「缺口当前唯一未补的部分」，
  而是同一缺口在标量 / log-sum 层的、可独立实例化的判据。
- **`未证`**：`RealDataProcessing.logsum_le` 的一般非严格正信道下的等号刻画未证。

模型无关：任意有限非空指标类型 `ι`。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 1. 标量核心：`u·log u − u + 1 ≥ 0` 及其等号情形 -/

/-- **标量核心（非严格）**：`0 < u` ⟹ `0 ≤ u·log u − u + 1`。

证明：`Real.one_sub_inv_le_log_of_pos hu : 1 − u⁻¹ ≤ log u` 乘 `u > 0` 得
`u − 1 ≤ u·log u`，整理即得。这是 `u·log u` 在 `u = 1` 处切线的全局下界。 -/
lemma mul_log_sub_add_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ u * Real.log u - u + 1 := by
  have h := Real.one_sub_inv_le_log_of_pos hu
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hu)
  have heq : u * (1 - u⁻¹) = u - 1 := by field_simp
  rw [heq] at hmul
  linarith

/-- **严格版 Gibbs 下界**：`0 < u`、`u ≠ 1` ⟹ `1 − u⁻¹ < Real.log u`。

证明：在 `u⁻¹` 处用 `Real.log_lt_sub_one_of_pos` 得 `log(u⁻¹) < u⁻¹ − 1`，
再用 `Real.log_inv` 化为 `−log u < u⁻¹ − 1`。

命名带 `_logsum` 后缀以避开 `RealEqualityCharacterization.one_sub_inv_lt_log_of_pos`
（同义、只读），遵守「不重定义已有声明」的约束。 -/
lemma one_sub_inv_lt_log_of_pos_logsum {u : ℝ} (hu : 0 < u) (hu1 : u ≠ 1) :
    1 - u⁻¹ < Real.log u := by
  have hinv1 : u⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have h' := congrArg (fun t : ℝ => t⁻¹) h
    simpa using h'
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hu) hinv1
  rw [Real.log_inv] at h
  linarith

/-- **标量核心（严格）**：`0 < u`、`u ≠ 1` ⟹ `0 < u·log u − u + 1`。

证明：`one_sub_inv_lt_log_of_pos_logsum` 乘 `u > 0` 得 `u − 1 < u·log u`。 -/
lemma mul_log_sub_add_pos {u : ℝ} (hu : 0 < u) (hu1 : u ≠ 1) :
    0 < u * Real.log u - u + 1 := by
  have h := one_sub_inv_lt_log_of_pos_logsum hu hu1
  have hmul := mul_lt_mul_of_pos_left h hu
  have heq : u * (1 - u⁻¹) = u - 1 := by field_simp
  rw [heq] at hmul
  linarith

/-- **标量等号刻画（`u·log u` 形式）**：`0 < u` ⟹ `u·log u − u + 1 = 0 ⟺ u = 1`。

正向用 `mul_log_sub_add_pos` 反证；反向显然。这是主定理中「逐项取等 ⟹ `A i = 1`」
一步的引擎。 -/
lemma mul_log_sub_add_eq_zero_iff {u : ℝ} (hu : 0 < u) :
    u * Real.log u - u + 1 = 0 ↔ u = 1 := by
  constructor
  · intro h
    by_contra hu1
    have hpos := mul_log_sub_add_pos hu hu1
    linarith
  · rintro rfl
    simp

/-- **标量等号刻画（`log` 的 Gibbs 形式）**：`0 < u` ⟹ `log u = 1 − u⁻¹ ⟺ u = 1`。

命名带 `_logsum` 后缀以避开只读的 `RealEqualityCharacterization.log_eq_one_sub_inv_iff`
（同义），遵守「不重定义已有声明」的约束。 -/
lemma log_eq_one_sub_inv_iff_logsum {u : ℝ} (hu : 0 < u) :
    Real.log u = 1 - u⁻¹ ↔ u = 1 := by
  constructor
  · intro h
    by_contra hu1
    have hlt := one_sub_inv_lt_log_of_pos_logsum hu hu1
    linarith
  · rintro rfl
    simp

/-! ## 2. 主定理：log-sum 不等式的等号 ⟺ 比值常值 -/

/-- **log-sum 不等式的等号判据（主定理）**。

`z z'` 逐点严格正时：

`(Σ z)·log((Σ z)/(Σ z')) = Σ z·log(z/z')  ⟺  ∀ i, z i·(Σ z') = z' i·(Σ z)`。

右端即「比值 `z i / z' i` 对所有 `i` 恒等于 `(Σ z)/(Σ z')`」（等价形式见
`logsum_eq_iff_exists_ratio_const`）。

正向（等号 ⟹ 比值常值）是 `RealDPIComplete.lean` 31–48 行标注为缺口、本文件
**补上**的那一半：把 `RealDataProcessing.logsum_le` 证明内部的分解恒等式
`(Σ z·log(z/z')) − m·log(m/r) = Σ z·log(A i)`（`A i = z i·r/(z' i·m)`）
与 `Σ z i·(1 − A i⁻¹) = 0` 提取出来，配合每项 `z i·(1 − A i⁻¹) ≤ z i·log(A i)`，
由「非负项之和为 0 ⟹ 逐项为 0」得 `log(A i) = 1 − A i⁻¹`，
再用标量等号刻画 `mul_log_sub_add_eq_zero_iff` 得 `A i = 1`。

反向（比值常值 ⟹ 等号）由 `Finset.sum_mul` 收尾。 -/
theorem logsum_eq_iff_ratio_const {ι : Type*} [Fintype ι] [Nonempty ι] (z z' : ι → ℝ)
    (hz : ∀ i, 0 < z i) (hz' : ∀ i, 0 < z' i) :
    ((∑ i, z i) * Real.log ((∑ i, z i) / (∑ i, z' i)) = ∑ i, z i * Real.log (z i / z' i))
      ↔ ∀ i, z i * (∑ j, z' j) = z' i * (∑ j, z j) := by
  constructor
  · -- 正向：等号 ⟹ 比值常值
    intro heq
    have hmpos : 0 < ∑ i, z i :=
      Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
    have hrpos : 0 < ∑ i, z' i :=
      Finset.sum_pos (fun i _ => hz' i) Finset.univ_nonempty
    set m : ℝ := ∑ i, z i with hm
    set r : ℝ := ∑ i, z' i with hr
    set A : ι → ℝ := fun i => z i * r / (z' i * m) with hA
    have hApos : ∀ i, 0 < A i :=
      fun i => div_pos (mul_pos (hz i) hrpos) (mul_pos (hz' i) hmpos)
    -- `set m := ∑ i, z i` 已经把**假设** `heq` 里的求和整体重写为 `m`/`r`
    -- （`set` 默认 `discharger := rfl` 会重写所有出现），故 `heq'` 就是 `heq` 本身，
    -- 不能再 `rw [h1, h2]`（模式 `∑ i, z i` 已不存在）。
    have heq' : m * Real.log (m / r) = ∑ i, z i * Real.log (z i / z' i) := heq
    -- 以下 hlogA / hsplit / hdecomp / hzero 与 `RealDataProcessing.logsum_le` 内部同构
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
    have hdecomp : (∑ i, z i * Real.log (z i / z' i)) - m * Real.log (m / r)
        = ∑ i, z i * Real.log (A i) := by
      rw [hsplit, Real.log_div (ne_of_gt hmpos) (ne_of_gt hrpos)]
      ring
    have hb : ∀ i, z i * (1 - (A i)⁻¹) ≤ z i * Real.log (A i) :=
      fun i => mul_le_mul_of_nonneg_left
        (Real.one_sub_inv_le_log_of_pos (hApos i)) (le_of_lt (hz i))
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
      -- `set` 已把 `∑ i, z i` 整体重写为 `m`，故此处首项就是 `m`，无需再 `rw`。
      have h2 : (∑ i, (m / r) * z' i) = m := by
        rw [← Finset.mul_sum]
        rw [show (∑ i, z' i) = r from hr.symm, div_mul_cancel₀ m (ne_of_gt hrpos)]
      rw [h2, sub_self]
    -- 等号 ⟹ Σ z·log(A i) = 0
    have hgap0 : ∑ i, z i * Real.log (A i) = 0 := by
      rw [← hdecomp, ← heq', sub_self]
    have hnonneg : ∀ i, 0 ≤ z i * Real.log (A i) - z i * (1 - (A i)⁻¹) := by
      intro i
      have hi := hb i
      linarith
    have hsumzero : ∑ i, (z i * Real.log (A i) - z i * (1 - (A i)⁻¹)) = 0 := by
      rw [Finset.sum_sub_distrib, hgap0, hzero, sub_zero]
    have hterm0 : ∀ i, z i * Real.log (A i) - z i * (1 - (A i)⁻¹) = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsumzero i
        (Finset.mem_univ i)
    intro i
    have hlogAi : Real.log (A i) = 1 - (A i)⁻¹ := by
      have hi := hterm0 i
      have hzi : z i ≠ 0 := ne_of_gt (hz i)
      have hfac : z i * (Real.log (A i) - (1 - (A i)⁻¹)) = 0 := by linarith
      have hdiff : Real.log (A i) - (1 - (A i)⁻¹) = 0 :=
        (mul_eq_zero.mp hfac).resolve_left hzi
      linarith
    have hAi : A i = 1 := (log_eq_one_sub_inv_iff_logsum (hApos i)).mp hlogAi
    have hd : z' i * m ≠ 0 := ne_of_gt (mul_pos (hz' i) hmpos)
    -- `rw [hA] at hmul` 会留下 `(fun i => ...) i` 的 beta-redex，`rw` 与
    -- `div_mul_cancel₀` 的模式对不上；先用 `simp only` 展开并 beta-归约。
    have hmul : z i * r = z' i * m := by
      have h1 : A i = 1 := hAi
      rw [hA] at h1
      simp only at h1
      -- `h1 : z i * r / (z' i * m) = 1`，两边乘 `z' i * m` 并用 `hd` 约分。
      have := congrArg (fun t : ℝ => t * (z' i * m)) h1
      simp only at this
      rw [div_mul_cancel₀ _ hd, one_mul] at this
      exact this
    -- 目标里 `m`/`r` 就是 `∑ i, z i` / `∑ i, z' i`（`set` 已整体替换），
    -- 故不能也不需要再 `rw [← hm, ← hr]`。
    exact hmul
  · -- 反向：比值常值 ⟹ 等号
    intro h
    have hmpos : 0 < ∑ i, z i :=
      Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
    have hrpos : 0 < ∑ i, z' i :=
      Finset.sum_pos (fun i _ => hz' i) Finset.univ_nonempty
    set m : ℝ := ∑ i, z i with hm
    set r : ℝ := ∑ i, z' i with hr
    have hrho : ∀ i, z i / z' i = m / r := by
      intro i
      rw [div_eq_div_iff (ne_of_gt (hz' i)) (ne_of_gt hrpos)]
      -- `set` 已把假设 `h` 中的 `∑ j, z' j` / `∑ j, z j` 重写为 `r` / `m`，
      -- 即 `h i : z i * r = z' i * m`；目标 `z i * r = m * z' i` 仅差乘法交换。
      have hi := h i
      rw [mul_comm (z' i) m] at hi
      exact hi
    have hsum : ∑ i, z i * Real.log (z i / z' i) = m * Real.log (m / r) := by
      simp only [hrho]
      -- `∑ i, z i` 已被 `set` 重写为 `m`，故 `Finset.sum_mul` 后直接就是 `m * log(m/r)`。
      rw [Finset.sum_mul]
    exact hsum.symm

/-! ## 3. 归一化推论与比值常值的等价叙述 -/

/-- **归一化等号判据**：当 `Σ z = Σ z'` 时，log-sum 的等号 ⟺ `z = z'`。

由主定理 `logsum_eq_iff_ratio_const` 与 `hs` 直接化去求和：交叉相乘关系
`z i·(Σ z') = z' i·(Σ z)` 在 `Σ z = Σ z' =: S > 0` 下化为 `z i·S = z' i·S`，
再由 `S > 0` 消去。这是 DPI 等号刻画「等号 ⟹ p = q」所用的最终形式
（输入分布 `p q` 常常分别归一）。 -/
theorem logsum_eq_iff_eq_of_sum_eq {ι : Type*} [Fintype ι] [Nonempty ι] (z z' : ι → ℝ)
    (hz : ∀ i, 0 < z i) (hz' : ∀ i, 0 < z' i) (hs : ∑ i, z i = ∑ i, z' i) :
    ((∑ i, z i) * Real.log ((∑ i, z i) / (∑ i, z' i)) = ∑ i, z i * Real.log (z i / z' i))
      ↔ ∀ i, z i = z' i := by
  rw [logsum_eq_iff_ratio_const z z' hz hz']
  have hmpos : 0 < ∑ j, z j := Finset.sum_pos (fun j _ => hz j) Finset.univ_nonempty
  constructor
  · intro h i
    have hi := h i
    rw [← hs] at hi
    exact mul_right_cancel₀ (ne_of_gt hmpos) hi
  · intro h i
    rw [h i, ← hs]

/-- **比值常值的等价叙述**：log-sum 的等号 ⟺ 存在 `c > 0` 使
`∀ i, z i / z' i = c`（且此时必有 `c = (Σ z)/(Σ z')`）。

由主定理除以 `Σ z' > 0` 得到；反向用 `z i = c·z' i` 逐项求和得
`Σ z = c·Σ z'`，再验证交叉相乘关系。 -/
theorem logsum_eq_iff_exists_ratio_const {ι : Type*} [Fintype ι] [Nonempty ι] (z z' : ι → ℝ)
    (hz : ∀ i, 0 < z i) (hz' : ∀ i, 0 < z' i) :
    ((∑ i, z i) * Real.log ((∑ i, z i) / (∑ i, z' i)) = ∑ i, z i * Real.log (z i / z' i))
      ↔ ∃ c : ℝ, 0 < c ∧ ∀ i, z i / z' i = c := by
  have hmpos : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
  have hrpos : 0 < ∑ i, z' i := Finset.sum_pos (fun i _ => hz' i) Finset.univ_nonempty
  rw [logsum_eq_iff_ratio_const z z' hz hz']
  constructor
  · intro h
    refine ⟨(∑ i, z i) / (∑ i, z' i), div_pos hmpos hrpos, fun i => ?_⟩
    rw [div_eq_div_iff (ne_of_gt (hz' i)) (ne_of_gt hrpos)]
    have hi := h i
    linarith
  · rintro ⟨c, _hc, hci⟩ i
    have h1 : ∀ j, z j = c * z' j :=
      fun j => (div_eq_iff (ne_of_gt (hz' j))).mp (hci j)
    have hsum : ∑ j, z j = c * ∑ j, z' j := by
      rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.mul_sum]
    rw [h1 i, hsum]
    ring

end Lattice