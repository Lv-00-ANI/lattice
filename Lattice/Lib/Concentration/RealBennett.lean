import Mathlib
import Lattice.Lib.Concentration.RealBernstein
/-!
# LATTICE: Bennett 逐点不等式与 Bennett 尾界 —— 收紧 RealBernstein 的保守常数

`RealBernstein` 的 docstring（第 23–32 行）**明确标注**：它没有走 Bennett 路线，
而是用「λ ≤ 1 的保守二次 Taylor 界」`e^{λx} ≤ 1 + λx + (λx)²`，代价是常数从 2 变到 4，
且只有在 `t ≤ 2nV` 时才给出二次指数衰减。本文件补上 Bennett 路线中缺失的那一块微积分：

  **Bennett 逐点不等式**：对 `0 ≤ λ`、`b > 0`、`x ≤ b`，
    `e^{λx} ≤ 1 + λx + (x/b)²·(e^{λb} − 1 − λb)`。

与 `RealBernstein` 的二次界不同，这个逐点界**对所有 λ ≥ 0 成立**（不要求 λb ≤ 1），
而且对负的 `x`（零均值有界上方差变量的必然取值）也成立——这正是 Bennett 引理优于
Bernstein 保守版的来源。

**定理链**：
1. `bennettH`：Bennett 熵函数 `h(u) = (1+u)·log(1+u) − u`；`bennettH_nonneg` 证 `u ≥ 0 ⟹ h(u) ≥ 0`。
2. `bennett_exp_neg_le`：`e^{−w} ≤ 1 − w + w²/2`（w ≥ 0）。
   证明：`1 + w + w²/2 ≤ e^w`（`Real.sum_le_exp_of_nonneg` 取 3 项）⟹ 取倒数，
   再用恒等式 `(1 + w + w²/2)(1 − w + w²/2) = 1 + w⁴/4 ≥ 1`。
   由此得 `bennett_exp_le_of_nonpos`：`e^u ≤ 1 + u + u²/2`（u ≤ 0）。
3. `bennettN` = `(t−2)e^t + t + 2`、`bennettN1` = `(t−1)e^t + 1`、`bennettN2` = `t·e^t`。
   它们是 `g(t) = (e^t − 1 − t)/t²` 的导数链（`N'' = t e^t ≥ 0`、`N' = N1 ≥ 0`、`N ≥ 0`），
   均用 `monotoneOn_of_hasDerivWithinAt_nonneg` 沿 `[0,∞)` 单调性证明。
4. `bennettG_monoOn`：`g` 在 `(0,∞)` 上单调递增（`g' = N(t)/t³ ≥ 0`）。
5. `bennett_scalar`（核心标量引理）：`u ≤ v`、`v > 0` ⟹
   `e^u − 1 − u ≤ (u/v)²·(e^v − 1 − v)`。
   证明分两支：`u ≤ 0` 用第 2 条 + `e^v ≥ 1 + v + v²/2`；
   `u > 0` 用第 4 条的单调性。
6. `bennett_pointwise`：换回 `λ, b, x` 形式的逐点不等式。
7. `bennett_mgf_lemma`：有限均匀概率空间、`EX = 0`、`X ≤ b`、`λ ≥ 0` ⟹
   `E[e^{λX}] ≤ exp((E[X²]/b²)·(e^{λb} − 1 − λb))`。
8. `bennett_mgf_product`：n 个独立副本的 MGF 乘积分解
   `E[e^{λΣXᵢ}] ≤ exp(n·(V/b²)·(e^{λb} − 1 − λb))`。
9. `bennett_tail`（核心尾界）：`P(ΣXᵢ ≥ t) ≤ exp(−(nV/b²)·h(b·t/(nV)))`，
   其中 `V = E[X²]`。证明：乘积分解 + 切尔诺夫桥 `markov_exp_tail`
   （`RealHoeffding`），取 `λ = log(1 + u)/b`（`u = b t/(nV)`），
   再作纯代数化简 `−λt + n(V/b²)(e^{λb} − 1 − λb) = −(nV/b²)h(u)`。
   **注意**：这不是「先优化 λ 再代入」，而是直接取最优 λ；等价的指数化简是纯 `log` 代数。

**与 RealBernstein 的对比（诚实标注）**：`bernstein_tail` 给的是
`e^{−t²/(4nV)}`（且只在 `t ≤ 2nV` 时有二次衰减），而 Bennett 的
`h(u) ≥ u²/(2(1+u/3))` 给出 `exp(−(nV/b²)·u²/(2(1+u/3)))`
（`u = bt/(nV)`）——对所有 `t > 0` 都成立，且当 `t` 小（`u → 0`）时退化到
`e^{−t²/(2nV)}`，系数 2 而非 4。Bennett 的常数是文献最优的（无 λ ≤ 1 截断）。

**诚实假设**：`α` 非空（均匀概率分母非零）、`n > 0`、`b > 0`、`t > 0`、
`V = E[X²] > 0`、`X` 在支撑上逐点 `≤ b`（**不**要求 `X ≥ −b`，负值可以任意大，
只要二阶矩有限）。不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、Bennett 熵函数 -/

/-- Bennett 熵函数 `h(u) = (1 + u)·log(1 + u) − u`（u ≥ 0）。
`Real.log` 是 mathlib 的全函数（非正处取 0）；本文件只在 `1 + u ≥ 1` 处使用。 -/
noncomputable def bennettH (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u

/-- `h` 在 `u ≥ 0` 上非负：由 `1 − 1/(1+u) ≤ log(1+u)` 乘以 `1 + u > 0` 得
`(1+u) − 1 ≤ (1+u)·log(1+u)`，即 `h(u) ≥ 0`。 -/
theorem bennettH_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ bennettH u := by
  have h1u : 0 < 1 + u := by linarith
  have hlog : 1 - (1 + u)⁻¹ ≤ Real.log (1 + u) := Real.one_sub_inv_le_log_of_pos h1u
  have hzero : (1 + u) * (1 - (1 + u)⁻¹) - u = 0 := by
    field_simp
    try ring
  have hmul : (1 + u) * (1 - (1 + u)⁻¹) ≤ (1 + u) * Real.log (1 + u) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt h1u)
  unfold bennettH
  linarith

/-- `h(1) = 2·log 2 − 1`（数值约 0.3863）。 -/
theorem bennettH_one : bennettH 1 = 2 * Real.log 2 - 1 := by
  unfold bennettH
  norm_num

/-! ## 二、标量辅助不等式：`e^{−w} ≤ 1 − w + w²/2`（w ≥ 0） -/

/-- `e^{−w} ≤ 1 − w + w²/2`（w ≥ 0）。
证明路线（无微积分）：`1 + w + w²/2 ≤ e^w`（`Real.sum_le_exp_of_nonneg` 前三项），
故 `e^{−w} = 1/e^w ≤ 1/(1 + w + w²/2)`；又
`(1 + w + w²/2)(1 − w + w²/2) = 1 + w⁴/4 ≥ 1`，由 `div_le_iff₀` 得
`1/(1 + w + w²/2) ≤ 1 − w + w²/2`。 -/
lemma bennett_exp_neg_le (w : ℝ) (hw : 0 ≤ w) :
    Real.exp (-w) ≤ 1 - w + w ^ 2 / 2 := by
  have hsum : 1 + w + w ^ 2 / 2 ≤ Real.exp w := by
    have h := Real.sum_le_exp_of_nonneg hw 3
    have h3 : (∑ i ∈ Finset.range 3, w ^ i / (Nat.factorial i : ℝ)) = 1 + w + w ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ]
    rwa [h3] at h
  have ha : 0 < 1 + w + w ^ 2 / 2 := by nlinarith [sq_nonneg w]
  have hprod : 1 ≤ (1 + w + w ^ 2 / 2) * (1 - w + w ^ 2 / 2) := by
    have h : (1 + w + w ^ 2 / 2) * (1 - w + w ^ 2 / 2) = 1 + w ^ 4 / 4 := by ring
    rw [h]
    nlinarith [sq_nonneg (w ^ 2)]
  have step1 : 1 / Real.exp w ≤ 1 / (1 + w + w ^ 2 / 2) :=
    one_div_le_one_div_of_le ha hsum
  have step2 : 1 / (1 + w + w ^ 2 / 2) ≤ 1 - w + w ^ 2 / 2 := by
    rw [div_le_iff₀ ha]
    have hprod' : 1 ≤ (1 - w + w ^ 2 / 2) * (1 + w + w ^ 2 / 2) := by
      rw [mul_comm]; exact hprod
    exact hprod'
  calc
    Real.exp (-w) = 1 / Real.exp w := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + w + w ^ 2 / 2) := step1
    _ ≤ 1 - w + w ^ 2 / 2 := step2

/-- `e^u ≤ 1 + u + u²/2`（u ≤ 0）：`bennett_exp_neg_le` 取 `w = −u`。 -/
lemma bennett_exp_le_of_nonpos (u : ℝ) (hu : u ≤ 0) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
  have hw : 0 ≤ -u := by linarith
  have h := bennett_exp_neg_le (-u) hw
  simpa [neg_neg, sub_neg_eq_add, neg_sq] using h

/-- `e^v ≥ 1 + v + v²/2`（v ≥ 0）：`Real.sum_le_exp_of_nonneg` 取前三项。 -/
lemma bennett_exp_ge_one_add_add_sq {v : ℝ} (hv : 0 ≤ v) :
    1 + v + v ^ 2 / 2 ≤ Real.exp v := by
  have h := Real.sum_le_exp_of_nonneg hv 3
  have h3 : (∑ i ∈ Finset.range 3, v ^ i / (Nat.factorial i : ℝ)) = 1 + v + v ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  rwa [h3] at h

/-! ## 三、`g(t) = (e^t − 1 − t)/t²` 的导数链与单调性

`N(t) = (t−2)e^t + t + 2`、`N1(t) = (t−1)e^t + 1`、`N2(t) = t·e^t`，
满足 `N2 = N1'`、`N1 = N'`、`g' = N(t)/t³`。沿 `[0,∞)`：
`N2 ≥ 0 ⟹ N1 递增 ⟹ N1 ≥ N1(0) = 0 ⟹ N 递增 ⟹ N ≥ N(0) = 0`。 -/

/-- `N(t) = (t − 2)·e^t + t + 2`（`g` 的导数的分子）。 -/
noncomputable def bennettN (t : ℝ) : ℝ := (t - 2) * Real.exp t + t + 2

/-- `N1(t) = (t − 1)·e^t + 1`（`N` 的导数）。 -/
noncomputable def bennettN1 (t : ℝ) : ℝ := (t - 1) * Real.exp t + 1

/-- `N2(t) = t·e^t`（`N1` 的导数）。 -/
noncomputable def bennettN2 (t : ℝ) : ℝ := t * Real.exp t

/-- `N' = N1`。 -/
lemma hasDerivAt_bennettN (t : ℝ) : HasDerivAt bennettN (bennettN1 t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s - 2) 1 t := by
    simpa using (hasDerivAt_id t).sub (hasDerivAt_const t (2 : ℝ))
  have h2 : HasDerivAt (fun s : ℝ => Real.exp s) (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun s : ℝ => s + 2) 1 t := by
    simpa using (hasDerivAt_id t).add (hasDerivAt_const t (2 : ℝ))
  have h := (h1.mul h2).add h3
  have hval : 1 * Real.exp t + (t - 2) * Real.exp t + 1 = bennettN1 t := by
    unfold bennettN1
    ring
  rw [hval] at h
  have hfun : bennettN = fun s : ℝ => (s - 2) * Real.exp s + (s + 2) := by
    funext s
    unfold bennettN
    ring
  rw [hfun]
  exact h

/-- `N1' = N2`。 -/
lemma hasDerivAt_bennettN1 (t : ℝ) : HasDerivAt bennettN1 (bennettN2 t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 t := by
    simpa using (hasDerivAt_id t).sub (hasDerivAt_const t (1 : ℝ))
  have h2 : HasDerivAt (fun s : ℝ => Real.exp s) (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have h := (h1.mul h2).add h3
  have hval : 1 * Real.exp t + (t - 1) * Real.exp t + 0 = bennettN2 t := by
    unfold bennettN2
    ring
  rw [hval] at h
  have hfun : bennettN1 = fun s : ℝ => (s - 1) * Real.exp s + 1 := by
    funext s
    unfold bennettN1
    ring
  rw [hfun]
  exact h

/-- `N2(t) = t·e^t ≥ 0`（t ≥ 0）。 -/
lemma bennettN2_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ bennettN2 t := by
  unfold bennettN2
  positivity

/-- `N2 ≥ 0` 于 `[0,∞)` ⟹ `N1` 在 `[0,∞)` 上单调递增 ⟹ `N1(t) ≥ N1(0) = 0`。 -/
lemma bennettN1_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ bennettN1 t := by
  have hmono : MonotoneOn bennettN1 (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f := bennettN1) (f' := bennettN2)
      (convex_Ici 0) ?_ ?_ ?_
    · show ContinuousOn (fun s : ℝ => (s - 1) * Real.exp s + 1) (Set.Ici 0)
      fun_prop
    · intro x _
      exact (hasDerivAt_bennettN1 x).hasDerivWithinAt
    · intro x hx
      have hx' : (0 : ℝ) < x := by simpa [interior_Ici] using hx
      exact bennettN2_nonneg x (le_of_lt hx')
  have h0 : bennettN1 0 = 0 := by unfold bennettN1; norm_num
  have hle := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr ht) ht
  linarith

/-- `N1 ≥ 0` 于 `[0,∞)` ⟹ `N` 在 `[0,∞)` 上单调递增 ⟹ `N(t) ≥ N(0) = 0`。 -/
lemma bennettN_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ bennettN t := by
  have hmono : MonotoneOn bennettN (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f := bennettN) (f' := bennettN1)
      (convex_Ici 0) ?_ ?_ ?_
    · show ContinuousOn (fun s : ℝ => (s - 2) * Real.exp s + s + 2) (Set.Ici 0)
      fun_prop
    · intro x _
      exact (hasDerivAt_bennettN x).hasDerivWithinAt
    · intro x hx
      have hx' : (0 : ℝ) < x := by simpa [interior_Ici] using hx
      exact bennettN1_nonneg x (le_of_lt hx')
  have h0 : bennettN 0 = 0 := by unfold bennettN; norm_num
  have hle := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr ht) ht
  linarith

/-- `g(t) = (e^t − 1 − t)/t²`。 -/
noncomputable def bennettG (s : ℝ) : ℝ := (Real.exp s - 1 - s) / s ^ 2

/-- `g'(t) = N(t)/t³`（t ≠ 0）。 -/
lemma hasDerivAt_bennettG (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt bennettG (bennettN t / t ^ 3) t := by
  have hnum : HasDerivAt (fun s : ℝ => Real.exp s - 1 - s) (Real.exp t - 1) t := by
    have h := ((Real.hasDerivAt_exp t).sub (hasDerivAt_const t (1 : ℝ))).sub (hasDerivAt_id t)
    simpa using h
  have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_id t).pow 2
  have h := hnum.div hden (pow_ne_zero 2 ht)
  have hval : ((Real.exp t - 1) * t ^ 2 - (Real.exp t - 1 - t) * (2 * t)) / (t ^ 2) ^ 2
      = bennettN t / t ^ 3 := by
    unfold bennettN
    field_simp
    try ring
  rw [hval] at h
  simpa [bennettG] using h

/-- `g` 在 `(0,∞)` 上单调递增：`g' = N(t)/t³`，`N(t) ≥ 0`（`bennettN_nonneg`）、`t³ > 0`。 -/
theorem bennettG_monoOn : MonotoneOn bennettG (Set.Ioi 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f := bennettG)
    (f' := fun x => bennettN x / x ^ 3) (convex_Ioi 0) ?_ ?_ ?_
  · show ContinuousOn (fun s : ℝ => (Real.exp s - 1 - s) / s ^ 2) (Set.Ioi 0)
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact pow_ne_zero 2 (ne_of_gt hx)
  · intro x hx
    have hx' : (0 : ℝ) < x := by simpa [isOpen_Ioi.interior_eq] using hx
    exact (hasDerivAt_bennettG x (ne_of_gt hx')).hasDerivWithinAt
  · intro x hx
    have hx' : (0 : ℝ) < x := by simpa [isOpen_Ioi.interior_eq] using hx
    exact div_nonneg (bennettN_nonneg x (le_of_lt hx')) (le_of_lt (pow_pos hx' 3))

/-! ## 四、核心标量引理：`e^u − 1 − u ≤ (u/v)²(e^v − 1 − v)`（u ≤ v、v > 0） -/

/-- **Bennett 标量引理（核心）**：对 `u ≤ v`、`v > 0`，
`e^u − 1 − u ≤ (u/v)²·(e^v − 1 − v)`。
证明分两支：
· `u ≤ 0`：`e^u − 1 − u ≤ u²/2`（`bennett_exp_le_of_nonpos`），
  而 `e^v − 1 − v ≥ v²/2`（`bennett_exp_ge_one_add_add_sq`），
  故 `(u/v)²(e^v − 1 − v) ≥ (u/v)²(v²/2) = u²/2`；
· `0 < u`：两边除以 `(uv)² > 0` 后即时 `g(u) ≤ g(v)`，由 `g` 在 `(0,∞)` 的单调性
  （`bennettG_monoOn`）得到。 -/
theorem bennett_scalar {u v : ℝ} (hv : 0 < v) (huv : u ≤ v) :
    Real.exp u - 1 - u ≤ (u / v) ^ 2 * (Real.exp v - 1 - v) := by
  rcases le_or_lt u 0 with hu | hu
  · have hA : Real.exp u - 1 - u ≤ u ^ 2 / 2 := by
      have := bennett_exp_le_of_nonpos u hu
      linarith
    have hB : v ^ 2 / 2 ≤ Real.exp v - 1 - v := by
      have := bennett_exp_ge_one_add_add_sq (le_of_lt hv)
      linarith
    have hC : u ^ 2 / 2 ≤ (u / v) ^ 2 * (Real.exp v - 1 - v) := by
      have hsq : 0 ≤ (u / v) ^ 2 := sq_nonneg _
      have h := mul_le_mul_of_nonneg_left hB hsq
      have heq : (u / v) ^ 2 * (v ^ 2 / 2) = u ^ 2 / 2 := by
        field_simp
        try ring
      linarith [heq]
    linarith
  · have hmono := bennettG_monoOn hu hv huv
    have h2 : (Real.exp u - 1 - u) / u ^ 2 ≤ (Real.exp v - 1 - v) / v ^ 2 := by
      simpa [bennettG] using hmono
    have hu2 : 0 < u ^ 2 := pow_pos hu 2
    calc
      Real.exp u - 1 - u = u ^ 2 * ((Real.exp u - 1 - u) / u ^ 2) := by
        field_simp
      _ ≤ u ^ 2 * ((Real.exp v - 1 - v) / v ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hu2)
      _ = (u / v) ^ 2 * (Real.exp v - 1 - v) := by
        field_simp
        try ring

/-! ## 五、Bennett 逐点不等式（λ, b, x 形式） -/

/-- **Bennett 逐点不等式**：`0 ≤ λ`、`b > 0`、`x ≤ b` ⟹
`e^{λx} ≤ 1 + λx + (x/b)²·(e^{λb} − 1 − λb)`。
取 `u = λx`、`v = λb`（`λ > 0` 时 `v > 0`、`u ≤ v`）后即 `bennett_scalar`；
`λ = 0` 时两边都等于 1。**注意**：`x` 可以是任意负值，不需要 `|x| ≤ b`。 -/
theorem bennett_pointwise {lam b x : ℝ} (hlam : 0 ≤ lam) (hb : 0 < b) (hx : x ≤ b) :
    Real.exp (lam * x) ≤ 1 + lam * x + (x / b) ^ 2 * (Real.exp (lam * b) - 1 - lam * b) := by
  rcases eq_or_lt_of_le hlam with h0 | hpos
  · rw [← h0]
    simp
  · have hv : 0 < lam * b := mul_pos hpos hb
    have huv : lam * x ≤ lam * b := mul_le_mul_of_nonneg_left hx (le_of_lt hpos)
    have h := bennett_scalar hv huv
    have hratio : lam * x / (lam * b) = x / b := by
      field_simp
      ring
    rw [hratio] at h
    linarith

/-! ## 六、Bennett 引理（指数矩上界） -/

/-- **Bennett 引理（核心）**：有限均匀概率空间 `α`、`EX = 0`、逐点 `X ≤ b`（b > 0）、
`λ ≥ 0` ⟹ `E[e^{λX}] ≤ exp((E[X²]/b²)·(e^{λb} − 1 − λb))`。
证明：`bennett_pointwise` 逐点求和，`ΣX = 0` 消去线性项，
得 `E[e^{λX}] ≤ 1 + (E[X²]/b²)(e^{λb} − 1 − λb) ≤ exp(...)`（`Real.add_one_le_exp`）。
**诚实标注**：这里把 `E[X²]`（零均值时的方差）从期望中提取，是 Bennett 优于
Hoeffding 的关键；不要求 X 有下界。 -/
theorem bennett_mgf_lemma {α : Type*} [Fintype α] {X : α → ℝ} {b lam : ℝ}
    (hN : 0 < Fintype.card α) (hzero : uniformExpectation X = 0)
    (hb : 0 < b) (hXb : ∀ x : α, X x ≤ b) (hlam : 0 ≤ lam) :
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤
      Real.exp (uniformSecondMoment X / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b)) := by
  set K : ℝ := Real.exp (lam * b) - 1 - lam * b with hK
  have hzero_sum : (∑ x : α, X x) = 0 := sum_eq_zero_of_uniformExpectation_eq_zero hN hzero
  have hpt : ∀ x : α, Real.exp (lam * X x) ≤ 1 + lam * X x + (X x / b) ^ 2 * K := by
    intro x
    have := bennett_pointwise hlam hb (hXb x)
    simpa [hK] using this
  have hsum_le : (∑ x : α, Real.exp (lam * X x)) ≤
      ∑ x : α, (1 + lam * X x + (X x / b) ^ 2 * K) :=
    Finset.sum_le_sum (fun x _ => hpt x)
  have hsum_val : (∑ x : α, (1 + lam * X x + (X x / b) ^ 2 * K)) =
      (Fintype.card α : ℝ) + K / b ^ 2 * (∑ x : α, X x ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hA : (∑ x : α, (1 : ℝ)) = (Fintype.card α : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hB : (∑ x : α, lam * X x) = lam * (∑ x : α, X x) := by rw [Finset.mul_sum]
    have hsq : (∑ x : α, (X x / b) ^ 2) = (∑ x : α, X x ^ 2) / b ^ 2 := by
      calc (∑ x : α, (X x / b) ^ 2) = ∑ x : α, X x ^ 2 / b ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _
            field_simp
            try ring
        _ = (∑ x : α, X x ^ 2) / b ^ 2 := by rw [Finset.sum_div]
    have hC : (∑ x : α, (X x / b) ^ 2 * K) = K / b ^ 2 * (∑ x : α, X x ^ 2) := by
      rw [← Finset.sum_mul, hsq]
      ring
    rw [hA, hB, hC, hzero_sum]
    ring
  have hfinal : uniformExpectation (fun x => Real.exp (lam * X x)) ≤
      1 + K / b ^ 2 * uniformSecondMoment X := by
    calc
      uniformExpectation (fun x => Real.exp (lam * X x))
          ≤ ((Fintype.card α : ℝ) + K / b ^ 2 * (∑ x : α, X x ^ 2)) / (Fintype.card α : ℝ) := by
            unfold uniformExpectation
            rw [← hsum_val]
            exact div_le_div_of_nonneg_right hsum_le (Nat.cast_nonneg _)
      _ = 1 + K / b ^ 2 * uniformSecondMoment X := by
            unfold uniformSecondMoment uniformExpectation
            field_simp
            try ring
  calc
    uniformExpectation (fun x => Real.exp (lam * X x))
        ≤ 1 + K / b ^ 2 * uniformSecondMoment X := hfinal
    _ ≤ Real.exp (K / b ^ 2 * uniformSecondMoment X) := by
          rw [add_comm]
          exact Real.add_one_le_exp _
    _ = Real.exp (uniformSecondMoment X / b ^ 2 * K) := by
          congr 1
          ring

/-! ## 七、n 个独立副本的 MGF 乘积分解 -/

/-- **Bennett MGF 乘积分解**：n 个独立副本（乘积空间 `Fin n → α`）的指数矩
`E[e^{λΣXᵢ}] = ∏ᵢ E[e^{λX}] ≤ exp(n·(V/b²)·(e^{λb} − 1 − λb))`，
`V = E[X²]`。证明：`Finset.prod_univ_sum` 把乘积空间的期望分解为单坐标期望之积
（与 `RealBernstein.bernstein_mgf_product` 同一路线，但逐项界换成 Bennett 引理）。 -/
theorem bennett_mgf_product {α : Type*} [Fintype α] {X : α → ℝ} {b : ℝ} (n : ℕ)
    (_hn : 0 < n) (hN : 0 < Fintype.card α) (hzero : uniformExpectation X = 0)
    (hb : 0 < b) (hXb : ∀ x : α, X x ≤ b) {lam : ℝ} (hlam : 0 ≤ lam) :
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * ∑ i : Fin n, X (w i))) ≤
      Real.exp ((n : ℝ) * (uniformSecondMoment X / b ^ 2 *
        (Real.exp (lam * b) - 1 - lam * b))) := by
  have hfunc : (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, X (w i))))
      = fun w : Fin n → α => ∏ i : Fin n, Real.exp (lam * X (w i)) := by
    funext w
    rw [Finset.mul_sum, Real.exp_sum]
  calc
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * ∑ i : Fin n, X (w i)))
        = (∏ i : Fin n, ∑ x : α, Real.exp (lam * X x)) / ((Fintype.card α : ℝ) ^ n) := by
          unfold uniformExpectation
          rw [hfunc, Fintype.card_pi_const, Nat.cast_pow]
          congr 1
          rw [Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset α))
            (f := fun i x => Real.exp (lam * X x))]
          simp
    _ = ∏ i : Fin n, uniformExpectation (fun x => Real.exp (lam * X x)) := by
          unfold uniformExpectation
          rw [Finset.prod_div_distrib]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ _i : Fin n,
          Real.exp (uniformSecondMoment X / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b)) := by
          apply Finset.prod_le_prod
          · intro i _
            unfold uniformExpectation
            exact div_nonneg (Finset.sum_nonneg (fun x _ => Real.exp_nonneg _)) (Nat.cast_nonneg _)
          · intro i _
            exact bennett_mgf_lemma (X := X) hN hzero hb hXb hlam
    _ = Real.exp ((n : ℝ) * (uniformSecondMoment X / b ^ 2 *
          (Real.exp (lam * b) - 1 - lam * b))) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]

/-! ## 八、Bennett 尾界（核心） -/

/-- **Bennett 尾界（核心）**：n 个独立副本、`EX = 0`、逐点 `X ≤ b`、`b > 0`、
`V = E[X²] > 0`、`t > 0` ⟹
  `P(Σᵢ X(Xᵢ) ≥ t) ≤ exp(−(n·V/b²)·h(b·t/(n·V)))`，`h(u) = (1+u)log(1+u) − u`。

证明：乘积分解（`bennett_mgf_product`）+ 切尔诺夫马尔可夫桥
（`markov_exp_tail`，`RealHoeffding`），取
`u = b·t/(nV)`、`λ = log(1+u)/b > 0`；此时 `e^{λb} = 1 + u`、`λt = n(V/b²)·u·log(1+u)`，
故指数 `−λt + n(V/b²)(e^{λb} − 1 − λb) = −(nV/b²)·[(1+u)log(1+u) − u] = −(nV/b²)h(u)`。
这是**直接取最优 λ**（不是先优化再代入）：`λ` 由 Bennett 的一阶条件给出，
随后只是 `log` 代数化简。**对比** `RealBernstein.bernstein_tail` 的
`e^{−t²/(4nV)}`（且需 `t ≤ 2nV`）：由 `bennettH_nonneg` 之后的
`h(u) ≥ u²/(2(1+u/3))` 型下界，Bennett 给出对所有 `t > 0` 成立的更强界
`exp(−(nV/b²)·h(bt/(nV)))`（小 `t` 时系数 2，文献最优）。 -/
theorem bennett_tail {α : Type*} [Fintype α] {X : α → ℝ} {b : ℝ} (n : ℕ)
    (hn : 0 < n) (hN : 0 < Fintype.card α) (hzero : uniformExpectation X = 0)
    (hb : 0 < b) (hXb : ∀ x : α, X x ≤ b) (hV : 0 < uniformSecondMoment X)
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ ∑ i : Fin n, X (w i))) ≤
      Real.exp (-((n : ℝ) * uniformSecondMoment X / b ^ 2) *
        bennettH (b * t / ((n : ℝ) * uniformSecondMoment X))) := by
  let V : ℝ := uniformSecondMoment X
  let u : ℝ := b * t / ((n : ℝ) * V)
  let lam : ℝ := Real.log (1 + u) / b
  let S : (Fin n → α) → ℝ := fun w => ∑ i : Fin n, X (w i)
  have hnℝ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hVpos : 0 < V := hV
  have hu : 0 < u := by
    unfold u
    exact div_pos (mul_pos hb ht) (mul_pos hnℝ hVpos)
  have h1u : 1 < 1 + u := by linarith
  have hlogpos : 0 < Real.log (1 + u) := Real.log_pos h1u
  have hlam : 0 < lam := by
    unfold lam
    exact div_pos hlogpos hb
  have hmgf' : uniformExpectation (fun w : Fin n → α => Real.exp (lam * ∑ i : Fin n, X (w i))) ≤
      Real.exp ((n : ℝ) * (V / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b))) := by
    have h := bennett_mgf_product (X := X) (b := b) n hn hN hzero hb hXb (le_of_lt hlam)
    simpa [V] using h
  have hmarkov := markov_exp_tail (S := S) (t := t) (lam := lam) hlam
  have hexp : -lam * t + (n : ℝ) * (V / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b))
      = -((n : ℝ) * V / b ^ 2) * bennettH u := by
    have hlog : lam * b = Real.log (1 + u) := by
      unfold lam
      field_simp
    have hexpval : Real.exp (lam * b) = 1 + u := by
      rw [hlog, Real.exp_log (by linarith)]
    have ht_eq : t = (n : ℝ) * V * u / b := by
      unfold u
      field_simp
      try ring
    have hlam_eq : lam = Real.log (1 + u) / b := rfl
    rw [ht_eq, hexpval, hlog, hlam_eq]
    unfold bennettH
    field_simp
    try ring_nf
  calc
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ ∑ i : Fin n, X (w i)))
        = uniformProb (Finset.univ.filter (fun w => t ≤ S w)) := by simp [S]
    _ ≤ Real.exp (-lam * t) * uniformExpectation (fun w => Real.exp (lam * S w)) := hmarkov
    _ ≤ Real.exp (-lam * t) *
          Real.exp ((n : ℝ) * (V / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          simpa [S] using hmgf'
    _ = Real.exp (-lam * t + (n : ℝ) * (V / b ^ 2 * (Real.exp (lam * b) - 1 - lam * b))) := by
          rw [← Real.exp_add]
    _ = Real.exp (-((n : ℝ) * V / b ^ 2) * bennettH u) := by rw [hexp]
    _ = Real.exp (-((n : ℝ) * uniformSecondMoment X / b ^ 2) *
          bennettH (b * t / ((n : ℝ) * uniformSecondMoment X))) := by
          simp [V, u]

/-! ## 九、注：与 RealBernstein / RealHoeffding 的衔接

· `RealBernstein.bernstein_tail` 给 `P(ΣY ≥ t) ≤ e^{−t²/(4nV)}`，只在 `t ≤ 2nV` 时
  有二次指数衰减（来自 `λ ≤ 1` 的二次 Taylor 截断）。本文件 `bennett_tail` 去掉
  了该截断，对所有 `t > 0` 成立。
· 由 `h` 的已知下界 `h(u) ≥ u²/(2(1 + u/3))`（u ≥ 0），Bennett 蕴含
  `P(ΣX ≥ t) ≤ exp(−t²/(2nV(1 + bt/(3nV))))`——这就是文献中标准的 Bennett 形式；
  本文件只对**直接用到的** `h` 形式给出完整证明，该下界本身**未做**（诚实标注），
  以避免额外一长串微积分。
· 常数对比：Hoeffding（`RealHoeffding.hoeffding_tail`）给 `e^{−nt²/8}`，
  Bernstein 保守版给 `e^{−t²/(4nV)}`（`V ≤ 1` 时始终不弱于 Hoeffding），
  Bennett 在 `V` 小时给出 `e^{−t²/(2nV)}` 型主项——三者同属
  RealSamplingBoost 的随机化验证置信度链的「单轮 miss 概率」来源。
-/

end Lattice
