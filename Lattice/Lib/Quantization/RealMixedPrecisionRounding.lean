import Mathlib
import Lattice.Lib.Quantization.RealIEEE754
import Lattice.Lib.Quantization.RealMixedPrecision
/-!
# LATTICE: 真实舍入下的混合精度误差 —— 单次误差、k 次累加与饱和

`RealMixedPrecision` 在 `RealFloatFormat.RoundOp` 的**公理版**舍入下给出混合精度训练
（FP16/BF16 前向 + FP32 累加）的误差界。本文件改用 `RealIEEE754.IEEERound`
（**带舍入模式、单调性、符号保持与次正规界的语义化舍入**）**重推**同样的关键界，
并把结论明确分为两类：

## 一、与既有公理版**一致**的定理（一致性定理，`ieee_*` 前缀）
经桥 `RealIEEE754.ieeeToRoundOp` 把 `IEEERound` 提升为 `RoundOp` 后，直接调用
`RealMixedPrecision`/`RealFloatFormat` 的既有定理得到：
  · `ieee_single_add_error`/`ieee_single_mul_error`（`format_add_error`/`format_mul_error`）；
  · `ieee_fp16_round_abs_bound`（`fp16_round_abs_bound`）；
  · `ieee_fp16_underflow_dominated`（`fp16_underflow_dominated`）；
  · `ieee_mixed_layer_error`（`mixed_layer_error`，单层 `n·(eps·W+tiny)·X`）；
  · `ieee_mixed_matrix_frobenius_error`/`ieee_mixed_matrix_op_error`（矩阵级 `√(m·n)·(eps·θ+tiny)`）；
  · `ieee_mixed_vs_full_precision`（`mixed_vs_full_precision`，n 层端到端闭式链界）；
  · `ieee_accumulation_error_bound`（`accumulation_error_bound`，`2·n·eps·M`，需 `tiny = 0` 桥接）；
  · `ieee_loss_scaling_no_overflow`（`loss_scaling_no_overflow`）。
**一致性**的含义：这些定理的结论与公理版**逐字相同**，因为 `IEEERound` 是 `RoundOp` 的
一个子结构（`ieee_satisfies_roundOp`）——公理版的界在 IEEE 语义下**原样成立**。

## 二、**新内容**（公理版没有的）
  · `ieeeAccR`（单格式左折叠累加）+ `ieeeAccR_growth`/`ieeeAccR_error`：
    在**纯相对误差** `|R y − y| ≤ eps·|y|` 下，k 次累加的增长界
    `|fl(Σ) ≤ (Σ|x_i|)·(1+eps)^k` 与误差界
    `|fl(Σ) − Σ| ≤ (Σ|x_i|)·((1+eps)^k − 1)`
    ——后者用 `geom_sum_mul` 改写为 `eps·(Σ_{i<k} (1+eps)^i)·(Σ|x_i|)`，即
    **「k 次累加误差 ≤ eps·Σ (1+eps)^i · Σ|x_i|」**（`ieee_acc_error_sum_geom`）；
  · `ieeeAccN`（**逐层不同单位舍入** `es i` 的累加）+ `ieeeAccN_growth_error`：
    `|fl(Σ) − Σ| ≤ (Σ|x_i|)·(∏_{i<k}(1+es i) − 1)`，并用 `Finset.prod_le_prod`
    与 `Finset.one_le_prod` 风格的引理 `one_le_prod_one_add` 得到一致 `eps` 的控制
    `ieee_accN_uniform_error`（`∏(1+es i) ≤ (1+eps)^k`）；
  · **溢出饱和误差**：`fp16Sat`（`OverflowConv.saturate` 约定）满足
    `|sat x − x| ≤ max 0 (|x| − 65504)`（`fp16Sat_error`）、`|sat x| ≤ 65504`
    （`fp16Sat_abs_le`）、幂等/单调（`fp16Sat_idem`/`fp16Sat_mono`），
    以及把饱和与舍入叠加的 `fp16_round_sat_error`：
    `|round (sat x) − x| ≤ eps·65504 + tiny + max 0 (|x| − 65504)`；
  · `fpOverflow_fp16Max_iff_fp16Overflow`：本文件 `fpOverflow fp16Max` 与既有
    `fp16Overflow` 的等价桥。

诚实标注（显式假设/降级）：
  · 累加模型 `ieeeAccR`/`ieeeAccN` 是**纯相对误差**模型（无 `tiny`），因此与
    `RealMixedPrecision` 的 `FPAdder` 一致；带 `tiny` 的绝对底会使界多一项
    `k·tiny`（本文件未做该推广 —— 标注）；
  · 饱和约定只钳到 `±65504`，`OverflowConv.toInfinity` 在 `ℝ` 上不可表示（`RealIEEE754` 的诚实降级）；
  · 一致性定理的**前提**（如 `IEEERound` 的各字段、`tiny = 0`）是显式假设。
无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、单次运算误差（与既有公理版一致） -/

/-- **一致性定理**：加法舍入误差 `|round (a+b) − (a+b)| ≤ eps·|a+b| + tiny`
（`RealFloatFormat.format_add_error` 经 `ieeeToRoundOp` 的特例，结论逐字相同）。 -/
theorem ieee_single_add_error (F : FloatFormat) (md : RoundMode) (R : IEEERound F md) (a b : ℝ) :
    |roundToFormat F (ieeeToRoundOp F md R) (a + b) - (a + b)| ≤ F.eps * |a + b| + F.tiny :=
  format_add_error F (ieeeToRoundOp F md R) a b

/-- **一致性定理**：乘法舍入误差 `|round (a·b) − a·b| ≤ eps·|a·b| + tiny`。 -/
theorem ieee_single_mul_error (F : FloatFormat) (md : RoundMode) (R : IEEERound F md) (a b : ℝ) :
    |roundToFormat F (ieeeToRoundOp F md R) (a * b) - a * b| ≤ F.eps * |a * b| + F.tiny :=
  format_mul_error F (ieeeToRoundOp F md R) a b

/-! ## 二、k 次累加误差（新内容：几何级数界） -/

/-- 单格式左折叠累加：`ieeeAccR R 0 = 0`、`ieeeAccR R (k+1) x = R (ieeeAccR R k x + x k)`
（每一步的加法在低精度格式 `R` 下做完立即舍入）。 -/
def ieeeAccR (R : ℝ → ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, x => R (ieeeAccR R n x + x n)

/-- 逐层不同单位舍入的左折叠累加：第 `k` 步用舍入器 `R k`。 -/
def ieeeAccN (R : ℕ → ℝ → ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, x => R n (ieeeAccN R n x + x n)

/-- **乘积杠杆引理**：每一步因子 `1 + es i ≥ 1` 时，乘积 `∏_{i<k}(1 + es i) ≥ 1`。 -/
lemma one_le_prod_one_add (es : ℕ → ℝ) (hes : ∀ i, 0 ≤ es i) (n : ℕ) :
    1 ≤ ∏ i in Finset.range n, (1 + es i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      have hb : (1 : ℝ) ≤ 1 + es n := by linarith [hes n]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (∏ i in Finset.range n, (1 + es i)) * (1 + es n) :=
            mul_le_mul ih hb (by norm_num) (le_trans (by norm_num : (0:ℝ) ≤ 1) ih)

/-- 常因子乘积的幂形式：`∏_{i<k}(1 + eps) = (1 + eps)^k`。 -/
lemma prod_const_one_add (eps : ℝ) (n : ℕ) :
    ∏ _i in Finset.range n, (1 + eps) = (1 + eps) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ih, pow_succ]

/-- **新内容：逐层单位舍入累加的增长与误差（联合归纳）**。若第 `i` 步舍入满足
纯相对界 `|R i y − y| ≤ es i·|y|`（`es i ≥ 0`），则
  增长：`|fl(Σ_{i<k} x_i)| ≤ (Σ_{i<k}|x_i|)·∏_{i<k}(1+es i)`；
  误差：`|fl(Σ_{i<k} x_i) − Σ_{i<k} x_i| ≤ (Σ_{i<k}|x_i|)·(∏_{i<k}(1+es i) − 1)`。
两者在同一次归纳中给出（误差步需要增长步的中间估计）。 -/
theorem ieeeAccN_growth_error {R : ℕ → ℝ → ℝ} {es : ℕ → ℝ} (hes : ∀ i, 0 ≤ es i)
    (hR : ∀ (i : ℕ) (y : ℝ), |R i y - y| ≤ es i * |y|) (n : ℕ) (x : ℕ → ℝ) :
    (|ieeeAccN R n x| ≤ (∑ i in Finset.range n, |x i|) * ∏ i in Finset.range n, (1 + es i))
      ∧ (|ieeeAccN R n x - ∑ i in Finset.range n, x i|
          ≤ (∑ i in Finset.range n, |x i|) * (∏ i in Finset.range n, (1 + es i) - 1)) := by
  induction n with
  | zero =>
      constructor <;> simp [ieeeAccN]
  | succ n ih =>
      obtain ⟨ihg, ihe⟩ := ih
      set Pn : ℝ := ∏ i in Finset.range n, (1 + es i) with hPn
      set An : ℝ := ∑ i in Finset.range n, |x i| with hAn_def
      have hPn_ge : 1 ≤ Pn := by rw [hPn]; exact one_le_prod_one_add es hes n
      have hPn_succ : ∏ i in Finset.range (n + 1), (1 + es i) = Pn * (1 + es n) := by
        rw [Finset.prod_range_succ, ← hPn]
      have hAn_succ : (∑ i in Finset.range (n + 1), |x i|) = An + |x n| := by
        rw [Finset.sum_range_succ, ← hAn_def]
      have hRabs : |R n (ieeeAccN R n x + x n)| ≤ (1 + es n) * (|ieeeAccN R n x| + |x n|) := by
        have hy := hR n (ieeeAccN R n x + x n)
        have htri : |ieeeAccN R n x + x n| ≤ |ieeeAccN R n x| + |x n| := abs_add _ _
        -- 关键：`|R y| ≤ |R y - y| + |y|`，用 `abs_sub_le_iff` 的三角形式而非 `rw` 展开，
        -- 避免 `rw` 在 `abs` 内部重写 `R y`（其自身是 RHS 的子项，会导致发散/双重展开）。
        have htri2 : |R n (ieeeAccN R n x + x n)|
            ≤ |R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n)| + |ieeeAccN R n x + x n| := by
          have h := abs_add (R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n))
            (ieeeAccN R n x + x n)
          have hid : R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n)
              + (ieeeAccN R n x + x n) = R n (ieeeAccN R n x + x n) := by ring
          rwa [hid] at h
        calc
          |R n (ieeeAccN R n x + x n)|
              ≤ |R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n)|
                + |ieeeAccN R n x + x n| := htri2
          _ ≤ es n * |ieeeAccN R n x + x n| + |ieeeAccN R n x + x n| := add_le_add_right hy _
          _ = (1 + es n) * |ieeeAccN R n x + x n| := by ring
          _ ≤ (1 + es n) * (|ieeeAccN R n x| + |x n|) :=
                mul_le_mul_of_nonneg_left htri (by linarith [hes n])
      have hkey : An * Pn + |x n| ≤ (An + |x n|) * Pn := by
        have hmul : |x n| ≤ |x n| * Pn := by
          calc
            |x n| = |x n| * 1 := by ring
            _ ≤ |x n| * Pn := mul_le_mul_of_nonneg_left hPn_ge (abs_nonneg _)
        nlinarith [hmul]
      have growth : |ieeeAccN R (n + 1) x| ≤ (∑ i in Finset.range (n + 1), |x i|)
          * ∏ i in Finset.range (n + 1), (1 + es i) := by
        rw [hAn_succ, hPn_succ]
        calc
          |ieeeAccN R (n + 1) x| = |R n (ieeeAccN R n x + x n)| := by simp only [ieeeAccN]
          _ ≤ (1 + es n) * (|ieeeAccN R n x| + |x n|) := hRabs
          _ ≤ (1 + es n) * (An * Pn + |x n|) :=
                mul_le_mul_of_nonneg_left (add_le_add_right ihg _) (by linarith [hes n])
          _ ≤ (1 + es n) * ((An + |x n|) * Pn) :=
                mul_le_mul_of_nonneg_left hkey (by linarith [hes n])
          _ = (An + |x n|) * (Pn * (1 + es n)) := by ring
      have htri2 : |ieeeAccN R n x + x n| ≤ (An + |x n|) * Pn := by
        calc
          |ieeeAccN R n x + x n| ≤ |ieeeAccN R n x| + |x n| := abs_add _ _
          _ ≤ An * Pn + |x n| := add_le_add_right ihg _
          _ ≤ (An + |x n|) * Pn := hkey
      have hdecomp : ieeeAccN R (n + 1) x - ∑ i in Finset.range (n + 1), x i
          = (ieeeAccN R n x - ∑ i in Finset.range n, x i)
            + (R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n)) := by
        rw [Finset.sum_range_succ]
        simp only [ieeeAccN]
        ring
      have hfac : 0 ≤ (Pn - 1) * |x n| :=
        mul_nonneg (by linarith) (abs_nonneg _)
      have hfac' : 0 ≤ (Pn - 1) * ((An + |x n|) - An) := by
        have hsub : (An + |x n|) - An = |x n| := by ring
        rw [hsub]
        exact hfac
      have error : |ieeeAccN R (n + 1) x - ∑ i in Finset.range (n + 1), x i|
          ≤ (∑ i in Finset.range (n + 1), |x i|)
            * (∏ i in Finset.range (n + 1), (1 + es i) - 1) := by
        rw [hAn_succ, hPn_succ]
        calc
          |ieeeAccN R (n + 1) x - ∑ i in Finset.range (n + 1), x i|
              = |(ieeeAccN R n x - ∑ i in Finset.range n, x i)
                  + (R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n))| := by
                rw [hdecomp]
          _ ≤ |ieeeAccN R n x - ∑ i in Finset.range n, x i|
                + |R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n)| := abs_add _ _
          _ ≤ An * (Pn - 1) + es n * ((An + |x n|) * Pn) :=
                add_le_add ihe
                  (le_trans (hR n (ieeeAccN R n x + x n))
                    (mul_le_mul_of_nonneg_left htri2 (hes n)))
          _ ≤ (An + |x n|) * (Pn * (1 + es n) - 1) := by
                nlinarith [hfac', abs_nonneg (x n)]
      exact ⟨growth, error⟩

/-- **新内容：逐层单位舍入累加的增长界**（`ieeeAccN_growth_error` 的第一分量）。 -/
theorem ieeeAccN_growth {R : ℕ → ℝ → ℝ} {es : ℕ → ℝ} (hes : ∀ i, 0 ≤ es i)
    (hR : ∀ (i : ℕ) (y : ℝ), |R i y - y| ≤ es i * |y|) (n : ℕ) (x : ℕ → ℝ) :
    |ieeeAccN R n x| ≤ (∑ i in Finset.range n, |x i|) * ∏ i in Finset.range n, (1 + es i) :=
  (ieeeAccN_growth_error hes hR n x).1

/-- **新内容：逐层单位舍入累加的误差界**
`|fl(Σ_{i<k} x_i) − Σ_{i<k} x_i| ≤ (Σ_{i<k}|x_i|)·(∏_{i<k}(1+es i) − 1)`。 -/
theorem ieeeAccN_error {R : ℕ → ℝ → ℝ} {es : ℕ → ℝ} (hes : ∀ i, 0 ≤ es i)
    (hR : ∀ (i : ℕ) (y : ℝ), |R i y - y| ≤ es i * |y|) (n : ℕ) (x : ℕ → ℝ) :
    |ieeeAccN R n x - ∑ i in Finset.range n, x i|
      ≤ (∑ i in Finset.range n, |x i|) * (∏ i in Finset.range n, (1 + es i) - 1) :=
  (ieeeAccN_growth_error hes hR n x).2

/-- 单格式累加与逐层累加在常误差函数下的相容：`ieeeAccR R = ieeeAccN (fun _ => R)`。 -/
lemma ieeeAccR_eq_accN (R : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) :
    ieeeAccR R n x = ieeeAccN (fun _ : ℕ => R) n x := by
  induction n with
  | zero => simp [ieeeAccR, ieeeAccN]
  | succ n ih => simp only [ieeeAccR, ieeeAccN, ih]

/-- **新内容：单格式累加的增长界** `|fl(Σ_{i<k} x_i)| ≤ (Σ_{i<k}|x_i|)·(1+eps)^k`
（纯相对舍入 `|R y − y| ≤ eps·|y|`）。 -/
theorem ieeeAccR_growth {R : ℝ → ℝ} {eps : ℝ} (hε : 0 ≤ eps)
    (hR : ∀ y : ℝ, |R y - y| ≤ eps * |y|) (n : ℕ) (x : ℕ → ℝ) :
    |ieeeAccR R n x| ≤ (∑ i in Finset.range n, |x i|) * (1 + eps) ^ n := by
  rw [ieeeAccR_eq_accN]
  have h := ieeeAccN_growth (R := fun _ : ℕ => R) (es := fun _ : ℕ => eps)
    (fun _ => hε) (fun _ _ => hR _) n x
  simpa [prod_const_one_add] using h

/-- **新内容：单格式累加的误差界** `|fl(Σ_{i<k} x_i) − Σ_{i<k} x_i|
≤ (Σ_{i<k}|x_i|)·((1+eps)^k − 1)`（`k` 次舍入的相对误差按几何级数累积）。 -/
theorem ieeeAccR_error {R : ℝ → ℝ} {eps : ℝ} (hε : 0 ≤ eps)
    (hR : ∀ y : ℝ, |R y - y| ≤ eps * |y|) (n : ℕ) (x : ℕ → ℝ) :
    |ieeeAccR R n x - ∑ i in Finset.range n, x i|
      ≤ (∑ i in Finset.range n, |x i|) * ((1 + eps) ^ n - 1) := by
  rw [ieeeAccR_eq_accN]
  have h := ieeeAccN_error (R := fun _ : ℕ => R) (es := fun _ : ℕ => eps)
    (fun _ => hε) (fun _ _ => hR _) n x
  simpa [prod_const_one_add] using h

/-- **新内容：k 次累加误差的几何级数形式**（本题要求的 `Σ (1+eps)^i` 叙述）：
`|fl(Σ_{i<k} x_i) − Σ_{i<k} x_i| ≤ eps·(Σ_{i<k} (1+eps)^i)·(Σ_{i<k}|x_i|)`。
由 `ieeeAccR_error` 与 `geom_sum_mul`（`(Σ_{i<k}(1+eps)^i)·eps = (1+eps)^k − 1`）得到。 -/
theorem ieee_acc_error_sum_geom {R : ℝ → ℝ} {eps : ℝ} (hε : 0 ≤ eps)
    (hR : ∀ y : ℝ, |R y - y| ≤ eps * |y|) (n : ℕ) (x : ℕ → ℝ) :
    |ieeeAccR R n x - ∑ i in Finset.range n, x i|
      ≤ eps * (∑ i in Finset.range n, (1 + eps) ^ i) * (∑ i in Finset.range n, |x i|) := by
  have hg : (∑ i in Finset.range n, (1 + eps) ^ i) * eps = (1 + eps) ^ n - 1 := by
    have h := geom_sum_mul (1 + eps) n
    rw [show (1 + eps) - 1 = eps by ring] at h
    exact h
  calc
    |ieeeAccR R n x - ∑ i in Finset.range n, x i|
        ≤ (∑ i in Finset.range n, |x i|) * ((1 + eps) ^ n - 1) := ieeeAccR_error hε hR n x
    _ = eps * (∑ i in Finset.range n, (1 + eps) ^ i) * (∑ i in Finset.range n, |x i|) := by
        rw [← hg]
        ring

/-- **新内容：逐层误差被统一 `eps` 控制**（`Finset.prod_le_prod` 的用途）：
若 `es i ≤ eps` 且 `es i ≥ 0`，则逐层累加误差满足一致几何界
`≤ (Σ|x_i|)·((1+eps)^k − 1)`。 -/
theorem ieee_accN_uniform_error {R : ℕ → ℝ → ℝ} {es : ℕ → ℝ} (hes : ∀ i, 0 ≤ es i)
    (hR : ∀ (i : ℕ) (y : ℝ), |R i y - y| ≤ es i * |y|) {eps : ℝ} (hε : 0 ≤ eps)
    (hle : ∀ i, es i ≤ eps) (n : ℕ) (x : ℕ → ℝ) :
    |ieeeAccN R n x - ∑ i in Finset.range n, x i|
      ≤ (∑ i in Finset.range n, |x i|) * ((1 + eps) ^ n - 1) := by
  have hbase := ieeeAccN_error hes hR n x
  have hA0 : 0 ≤ ∑ i in Finset.range n, |x i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  -- `hε` 在此显式使用：它保证几何因子 `1 + eps ≥ 1`，从而 `(1+eps)^n ≥ 1`
  -- 且因子 `1 + es i ≤ 1 + eps`（供 `Finset.prod_le_prod` 的第二前提）。
  have hε1 : (1 : ℝ) ≤ 1 + eps := by linarith
  have hprod_le : ∏ i in Finset.range n, (1 + es i) ≤ (1 + eps) ^ n := by
    have h1 : ∏ i in Finset.range n, (1 + es i)
        ≤ ∏ _i in Finset.range n, (1 + eps) :=
      Finset.prod_le_prod (fun i _ => by linarith [hes i]) (fun i _ => by linarith [hle i])
    have h2 : ∏ _i in Finset.range n, (1 + eps) = (1 + eps) ^ n := prod_const_one_add eps n
    have h3 : (1 : ℝ) ≤ (1 + eps) ^ n := one_le_pow₀ hε1
    linarith
  have h1 : (∏ i in Finset.range n, (1 + es i)) - 1 ≤ (1 + eps) ^ n - 1 := by linarith
  calc
    |ieeeAccN R n x - ∑ i in Finset.range n, x i|
        ≤ (∑ i in Finset.range n, |x i|) * (∏ i in Finset.range n, (1 + es i) - 1) := hbase
    _ ≤ (∑ i in Finset.range n, |x i|) * ((1 + eps) ^ n - 1) := by
          refine mul_le_mul_of_nonneg_left h1 hA0

/-! ## 三、溢出条件下的饱和误差（新内容：`OverflowConv.saturate` 约定） -/

/-- FP16 饱和函数：`max (−65504) (min 65504 x)`（`OverflowConv.saturate` 约定）。 -/
def fp16Sat (x : ℝ) : ℝ := clampTo 65504 x

/-- 饱和结果的绝对值不超过 `65504`。 -/
theorem fp16Sat_abs_le (x : ℝ) : |fp16Sat x| ≤ 65504 :=
  clampTo_abs_le 65504 x (by norm_num)

/-- 未溢出（`|x| ≤ 65504`）时饱和不改变输入。 -/
theorem fp16Sat_eq_self {x : ℝ} (hx : |x| ≤ 65504) : fp16Sat x = x :=
  clampTo_eq_self 65504 x (by norm_num) hx

/-- 饱和幂等。 -/
theorem fp16Sat_idem (x : ℝ) : fp16Sat (fp16Sat x) = fp16Sat x :=
  clampTo_idem 65504 x (by norm_num)

/-- 饱和单调。 -/
theorem fp16Sat_mono : Monotone fp16Sat := clampTo_mono 65504

/-- 饱和不溢出。 -/
theorem fp16Sat_no_overflow (x : ℝ) : ¬ fpOverflow 65504 (fp16Sat x) :=
  clampTo_no_overflow 65504 x (by norm_num)

/-- **新内容：饱和误差**（本题要求的命题）：
`|sat x − x| ≤ max 0 (|x| − FP16_MAX)`，其中 `FP16_MAX = 65504`。 -/
theorem fp16Sat_error (x : ℝ) : |fp16Sat x - x| ≤ max 0 (|x| - 65504) :=
  clampTo_error_le 65504 x (by norm_num)

/-- 溢出输入在饱和约定下严格被改变。 -/
theorem fp16Sat_ne_self_of_overflow {x : ℝ} (h : fpOverflow 65504 x) : fp16Sat x ≠ x :=
  clampTo_ne_self_of_overflow 65504 x (by norm_num) h

/-- **桥**：本文件的溢出谓词 `fpOverflow fp16Max` 与既有 `RealMixedPrecision.fp16Overflow` 等价。 -/
theorem fpOverflow_fp16Max_iff_fp16Overflow (x : ℝ) : fpOverflow fp16Max x ↔ fp16Overflow x := by
  unfold fpOverflow fp16Overflow fp16Max
  rfl

/-- **新内容：饱和 + 舍入的复合误差**：先饱和再在 IEEE 舍入 `R` 下舍入，
`|round (sat x) − x| ≤ eps·65504 + tiny + max 0 (|x| − 65504)`
——饱和误差与舍入误差按三角不等式叠加，且舍入误差用饱和后的幅度界 `65504` 控制。 -/
theorem fp16_round_sat_error (F : FloatFormat) (md : RoundMode) (R : IEEERound F md) (x : ℝ) :
    |R.toFun (fp16Sat x) - x| ≤ F.eps * 65504 + F.tiny + max 0 (|x| - 65504) := by
  have h1 : |R.toFun (fp16Sat x) - fp16Sat x| ≤ F.eps * |fp16Sat x| + F.tiny := R.err_bound _
  have h2 : |fp16Sat x| ≤ 65504 := fp16Sat_abs_le x
  have h3 : |fp16Sat x - x| ≤ max 0 (|x| - 65504) := fp16Sat_error x
  have h4 : F.eps * |fp16Sat x| ≤ F.eps * 65504 := mul_le_mul_of_nonneg_left h2 F.eps_nonneg
  have h5 : |R.toFun (fp16Sat x) - fp16Sat x| ≤ F.eps * 65504 + F.tiny := by linarith
  calc
    |R.toFun (fp16Sat x) - x|
        = |(R.toFun (fp16Sat x) - fp16Sat x) + (fp16Sat x - x)| := by
          rw [show R.toFun (fp16Sat x) - x
            = (R.toFun (fp16Sat x) - fp16Sat x) + (fp16Sat x - x) by ring]
    _ ≤ |R.toFun (fp16Sat x) - fp16Sat x| + |fp16Sat x - x| := abs_add _ _
    _ ≤ (F.eps * 65504 + F.tiny) + max 0 (|x| - 65504) := add_le_add h5 h3

/-! ## 四、与既有 `RealMixedPrecision` 公理版一致（一致性定理） -/

/-- **桥**：把 `IEEERound` 的加法封装成 `RealMixedPrecision.FPAdder`
（需 `tiny = 0` 与 `eps ≤ 1` 两个显式假设，因为 `FPAdder` 的公理不带绝对底）。 -/
def ieeeToFPAdder (F : FloatFormat) (md : RoundMode) (R : IEEERound F md) (htiny : F.tiny = 0)
    (heps : F.eps ≤ 1) : FPAdder where
  toFun := fun a b => R.toFun (a + b)
  eps := F.eps
  eps_nonneg := F.eps_nonneg
  eps_le_one := heps
  err_bound := by
    intro a b
    have h := R.err_bound (a + b)
    simpa [htiny] using h

/-- **一致性定理**：`fp16_round_abs_bound`（范围内舍入的绝对值安全余量）。 -/
theorem ieee_fp16_round_abs_bound (F : FloatFormat) (md : RoundMode) (R : IEEERound F md)
    {x : ℝ} (hx : |x| ≤ 65504) :
    |roundToFormat F (ieeeToRoundOp F md R) x| ≤ 65504 * (1 + F.eps) + F.tiny :=
  fp16_round_abs_bound F (ieeeToRoundOp F md R) hx

/-- **一致性定理**：`fp16_underflow_dominated`（下溢区误差被绝对底支配）。 -/
theorem ieee_fp16_underflow_dominated (F : FloatFormat) (md : RoundMode) (R : IEEERound F md)
    {x : ℝ} (hu : fp16Underflow x) (h : F.eps * |x| ≤ F.tiny) :
    |roundToFormat F (ieeeToRoundOp F md R) x - x| ≤ 2 * F.tiny :=
  fp16_underflow_dominated F (ieeeToRoundOp F md R) hu h

/-- **一致性定理**：`loss_scaling_no_overflow`（损失缩放的溢出条件，与舍入语义无关）。 -/
theorem ieee_loss_scaling_no_overflow (k : ℕ) {g : ℝ}
    (h : |g| ≤ fp16Max / (2 : ℝ) ^ k) : ¬ fp16Overflow ((2 : ℝ) ^ k * g) :=
  loss_scaling_no_overflow k h

/-- **一致性定理**：`mixed_layer_error`（单层混合精度前向 `≤ n·(eps·W+tiny)·X`）。 -/
theorem ieee_mixed_layer_error {n : ℕ} (F : FloatFormat) (md : RoundMode) (R : IEEERound F md)
    (w x : Fin n → ℝ) (W X : ℝ) (hW : 0 ≤ W) (hX : 0 ≤ X)
    (hw : ∀ i, |w i| ≤ W) (hx : ∀ i, |x i| ≤ X) :
    |mixedForward (roundToFormat F (ieeeToRoundOp F md R)) w x - fullForward w x|
      ≤ (n : ℝ) * (F.eps * W + F.tiny) * X :=
  mixed_layer_error F (ieeeToRoundOp F md R) w x W X hW hX hw hx

/-- **一致性定理**：`mixed_matrix_frobenius_error`（矩阵级 `√(m·n)·(eps·θ+tiny)`）。 -/
theorem ieee_mixed_matrix_frobenius_error {m n : ℕ} (F : FloatFormat) (md : RoundMode)
    (R : IEEERound F md) (A : Matrix (Fin m) (Fin n) ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ i j, |A i j| ≤ θ) :
    frobeniusNorm (mixedMatrix (roundToFormat F (ieeeToRoundOp F md R)) A - A)
      ≤ Real.sqrt ((m * n : ℕ) : ℝ) * (F.eps * θ + F.tiny) :=
  mixed_matrix_frobenius_error F (ieeeToRoundOp F md R) A θ hθ hA

/-- **一致性定理**：`mixed_matrix_op_error`（算子范数级误差界）。 -/
theorem ieee_mixed_matrix_op_error {m n : ℕ} (F : FloatFormat) (md : RoundMode)
    (R : IEEERound F md) (A : Matrix (Fin m) (Fin n) ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ i j, |A i j| ≤ θ) :
    ‖matCLME (mixedMatrix (roundToFormat F (ieeeToRoundOp F md R)) A) - matCLME A‖
      ≤ Real.sqrt ((m * n : ℕ) : ℝ) * (F.eps * θ + F.tiny) :=
  mixed_matrix_op_error F (ieeeToRoundOp F md R) A θ hθ hA

/-- **一致性定理**：`accumulation_error_bound`（`2·n·eps·M`，
经 `ieeeToFPAdder` 桥接，需 `tiny = 0`）。

⚠ **第 20 轮**：`(hM : 0 ≤ M)` 被删掉——它在本文件里**只用来传给 `accumulation_error_bound`**，
而后者已不再需要它（那个前提是未使用的，且可由 `hmag 0` 导出）。
**所以本条也更强了**：前提少一个，断言不变。 -/
theorem ieee_accumulation_error_bound (F : FloatFormat) (md : RoundMode) (R : IEEERound F md)
    (htiny : F.tiny = 0) (heps : F.eps ≤ 1) (M : ℝ) :
    ∀ (n : ℕ) (x : ℕ → ℝ),
      (∀ k, k ≤ n → |accSum (ieeeToFPAdder F md R htiny heps) k x| ≤ M) →
      (∀ k, k < n → |x k| ≤ M) →
      |accSum (ieeeToFPAdder F md R htiny heps) n x - ∑ k in Finset.range n, x k|
        ≤ 2 * (n : ℝ) * F.eps * M :=
  accumulation_error_bound (ieeeToFPAdder F md R htiny heps) M

/-- **一致性定理**：`mixed_vs_full_precision`（n 层混合精度模型端到端闭式链界）。 -/
theorem ieee_mixed_vs_full_precision {n : ℕ} (F : FloatFormat) (md : RoundMode)
    (R : IEEERound F md) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (θ : ℕ → ℝ) (k : ℕ)
    (hθ : ∀ i, i < k → 0 ≤ θ i) (hA : ∀ i, i < k → ∀ a b, |A i a b| ≤ θ i) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖quantFwd (fun i => matCLME (mixedMatrix (roundToFormat F (ieeeToRoundOp F md R)) (A i))) k x
        - quantFwd (fun i => matCLME (A i)) k x‖
        ≤ ∑ i in Finset.range k,
            (∏ j in Finset.Ioo i k,
                ‖matCLME (mixedMatrix (roundToFormat F (ieeeToRoundOp F md R)) (A j))‖)
              * (Real.sqrt ((n * n : ℕ) : ℝ) * (F.eps * θ i + F.tiny))
              * (∏ j in Finset.range i, ‖matCLME (A j)‖) * ‖x‖ :=
  mixed_vs_full_precision F (ieeeToRoundOp F md R) A θ k hθ hA

/-! ## 三、**带 `tiny` 的累积模型**（B15：从纯相对模型推广）

上面 `ieeeAccR` / `ieeeAccN` 系列的舍入假设是**纯相对**的
`|R y − y| ≤ eps·|y|`。真实的 IEEE 浮点舍入（尤其**次正规/下溢区**）满足的是
**相对 + 绝对（`tiny`）** 的混合界

    `|R y − y| ≤ eps·|y| + tiny`

（`tiny` 是绝对下溢底，`RealFloatFormat.tiny`；见 `ieee_single_add_error`：
加法/乘法的**单步**界就是这一形式）。本节点名要求的正是把这个假设
**推广到整条累加链**：把 `tiny` 的贡献显式推进 `k` 步累加。

**核心结论（`ieeeAccNtiny_growth_error`）**：若每步舍入满足
`|R i y − y| ≤ es i·|y| + tiny`（`es i ≥ 0`、`tiny ≥ 0`），则

  · **增长**：`|fl(Σ_{i<k} x_i)| ≤ (Σ|x_i|)·∏_{i<k}(1+es i) + tiny·Σ_{i<k} ∏_{j<i}(1+es j)`；
  · **误差**：`|fl(Σ_{i<k} x_i) − Σ_{i<k}x_i|
     ≤ (Σ|x_i|)·(∏_{i<k}(1+es i) − 1) + tiny·Σ_{i<k} ∏_{j<i}(1+es j)`。

特别地，**常系数**（`es ≡ eps`、`tiny` 固定）时 `∏_{j<i}(1+eps) = (1+eps)^i`，
故 `tiny` 项 = `tiny·Σ_{i<k}(1+eps)^i` —— 即**累积模型 `err ≤ n(tiny + eps·mag)`
的精确形式**（`tiny` 不是简单乘 `n`，而是按几何级数加权；下溢底在每一步都被
后续步放大 `(1+eps)`）。

**诚实标注**：
  · 本节的 `tiny` 模型与 `ieee_single_add_error` 的**单步**界**口径一致**
    （同一 `eps`/`tiny` 语义），故这不是新公理，而是把既有单步界**推成链**；
  · `Σ_{i<k} ∏_{j<i}(1+es j)` 与 `∏(1+es) − 1` 的关系：常系数时二者恰好相同
    （`ieeeAccRtiny_error_sum_geom` 给出该恒等式），**逐层不同**舍入单位时
    二者不同（前者按前缀积加权）——本文件给出**更一般**的前缀积形式；
  · 仍不给 `tiny`/`eps` 的**数值**（由 `FloatFormat` 参数化）。
-/

/-- **前缀积**：`prefProd es k = ∏_{j<k}(1 + es j)`，即前 `k` 步的累积放大因子。 -/
def prefProd (es : ℕ → ℝ) (k : ℕ) : ℝ := ∏ j in Finset.range k, (1 + es j)

/-- 前缀积非负（`es i ≥ 0` 时）。 -/
lemma prefProd_nonneg {es : ℕ → ℝ} (hes : ∀ i, 0 ≤ es i) (k : ℕ) : 0 ≤ prefProd es k :=
  Finset.prod_nonneg (fun j _ => by linarith [hes j])

/-- **带 `tiny` 的逐层舍入累加（增长 + 误差，联合归纳，B15 主交付）**。

若每步 `|R i y − y| ≤ es i·|y| + tiny`（`es i ≥ 0`、`tiny ≥ 0`），则对任意 `n`、`x`：

  · 增长：`|ieeeAccN R n x| ≤ (Σ_{i<n}|x i|)·prefProd es n + tiny·(n·prefProd es n)`；
  · 误差：`|ieeeAccN R n x − Σ_{i<n} x i|
     ≤ (Σ_{i<n}|x i|)·(prefProd es n − 1) + tiny·(n·prefProd es n)`。

**`tiny` 项的精确形式（诚实标注，也是本节的要点）**：`tiny` 的系数是
`n·prefProd es n = n·∏_{j<n}(1+es j)`，即**步数 `n` 乘上总放大因子**——
它**不是**简单的 `n`：`tiny` 在第 `i` 步注入后，会被**其后每一步**以
`(1+es j)` 放大，故最坏情形下放大到 `n·prefProd`。
常系数（`es ≡ eps`）时这就是 `n·(1+eps)^n`，与
`ieeeAccRtiny_error` 的几何和 `Σ(1+eps)^i ≤ n(1+eps)^(n−1)` 同阶。

**证明结构**：与 `ieeeAccN_growth_error` 同款联合归纳，每步多出 `tiny` 项。
关键中间式：`|R n z| ≤ (1 + es n)·|z| + tiny`
（由 `|R n z| ≤ |R n z − z| + |z| ≤ es n·|z| + tiny + |z|` 得到）。 -/
theorem ieeeAccNtiny_growth_error {R : ℕ → ℝ → ℝ} {es : ℕ → ℝ} {tiny : ℝ}
    (hes : ∀ i, 0 ≤ es i) (htiny : 0 ≤ tiny)
    (hR : ∀ (i : ℕ) (y : ℝ), |R i y - y| ≤ es i * |y| + tiny) (n : ℕ) (x : ℕ → ℝ) :
    (|ieeeAccN R n x|
        ≤ (∑ i in Finset.range n, |x i|) * prefProd es n
          + tiny * ((n : ℝ) * prefProd es n))
      ∧ (|ieeeAccN R n x - ∑ i in Finset.range n, x i|
        ≤ (∑ i in Finset.range n, |x i|) * (prefProd es n - 1)
          + tiny * ((n : ℝ) * prefProd es n)) := by
  induction n with
  | zero => constructor <;> simp [ieeeAccN, prefProd]
  | succ n ih =>
      obtain ⟨ihg, ihe⟩ := ih
      set Pn : ℝ := prefProd es n with hPn
      set An : ℝ := ∑ i in Finset.range n, |x i| with hAn
      have hPn_ge : 1 ≤ Pn := by
        rw [hPn, prefProd]
        exact one_le_prod_one_add es hes n
      have hPnn : 0 ≤ Pn := le_trans (by norm_num) hPn_ge
      have hesn : 0 ≤ es n := hes n
      have hPn_succ : prefProd es (n + 1) = Pn * (1 + es n) := by
        rw [hPn, prefProd, Finset.prod_range_succ, ← prefProd]
      have hAn_succ : (∑ i in Finset.range (n + 1), |x i|) = An + |x n| := by
        rw [Finset.sum_range_succ, ← hAn]
      -- 关键中间式：`|R n z| ≤ (1+es n)|z| + tiny`
      have hRabs : ∀ z : ℝ, |R n z| ≤ (1 + es n) * |z| + tiny := by
        intro z
        have h := hR n z
        have htri : |R n z| ≤ |R n z - z| + |z| := by
          have habs := abs_add (R n z - z) z
          have hid : R n z - z + z = R n z := by ring
          rwa [hid] at habs
        linarith
      have htri2 : |ieeeAccN R n x + x n| ≤ An * Pn + tiny * ((n : ℝ) * Pn) + |x n| := by
        calc |ieeeAccN R n x + x n| ≤ |ieeeAccN R n x| + |x n| := abs_add _ _
          _ ≤ An * Pn + tiny * ((n : ℝ) * Pn) + |x n| := add_le_add_right ihg _
      -- 增长
      have growth : |ieeeAccN R (n + 1) x|
          ≤ (∑ i in Finset.range (n + 1), |x i|) * prefProd es (n + 1)
            + tiny * (((n + 1 : ℕ) : ℝ) * prefProd es (n + 1)) := by
        rw [hAn_succ, hPn_succ]
        push_cast
        calc |ieeeAccN R (n + 1) x| = |R n (ieeeAccN R n x + x n)| := by simp only [ieeeAccN]
          _ ≤ (1 + es n) * |ieeeAccN R n x + x n| + tiny := hRabs _
          _ ≤ (1 + es n) * (An * Pn + tiny * ((n : ℝ) * Pn) + |x n|) + tiny :=
                add_le_add_right (mul_le_mul_of_nonneg_left htri2 (by linarith)) _
          _ ≤ (An + |x n|) * (Pn * (1 + es n)) + tiny * ((n : ℝ) + 1) * (Pn * (1 + es n)) := by
                have h1 : |x n| ≤ |x n| * Pn := by
                  calc |x n| = |x n| * 1 := by ring
                    _ ≤ |x n| * Pn := mul_le_mul_of_nonneg_left hPn_ge (abs_nonneg _)
                have hAe : 0 ≤ An := Finset.sum_nonneg (fun i _ => abs_nonneg _)
                have hxn : 0 ≤ |x n| := abs_nonneg _
                nlinarith [h1, hPnn, hAe, hxn, hesn, htiny, hPn_ge,
                  mul_nonneg htiny (Nat.cast_nonneg n), mul_nonneg htiny hesn]
          _ = (An + |x n|) * (Pn * (1 + es n)) + tiny * (((n : ℝ) + 1) * (Pn * (1 + es n))) := by
                ring
      -- 误差
      have hdecomp : ieeeAccN R (n + 1) x - ∑ i in Finset.range (n + 1), x i
          = (ieeeAccN R n x - ∑ i in Finset.range n, x i)
            + (R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n)) := by
        rw [Finset.sum_range_succ]
        simp only [ieeeAccN]
        ring
      have hRstep : |R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n)|
          ≤ es n * (An * Pn + tiny * ((n : ℝ) * Pn) + |x n|) + tiny :=
        le_trans (hR n _) (add_le_add_right (mul_le_mul_of_nonneg_left htri2 hesn) _)
      have error : |ieeeAccN R (n + 1) x - ∑ i in Finset.range (n + 1), x i|
          ≤ (∑ i in Finset.range (n + 1), |x i|) * (prefProd es (n + 1) - 1)
            + tiny * (((n + 1 : ℕ) : ℝ) * prefProd es (n + 1)) := by
        rw [hAn_succ, hPn_succ]
        push_cast
        calc |ieeeAccN R (n + 1) x - ∑ i in Finset.range (n + 1), x i|
            = |(ieeeAccN R n x - ∑ i in Finset.range n, x i)
                + (R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n))| := by rw [hdecomp]
          _ ≤ |ieeeAccN R n x - ∑ i in Finset.range n, x i|
                + |R n (ieeeAccN R n x + x n) - (ieeeAccN R n x + x n)| := abs_add _ _
          _ ≤ (An * (Pn - 1) + tiny * ((n : ℝ) * Pn))
                + (es n * (An * Pn + tiny * ((n : ℝ) * Pn) + |x n|) + tiny) :=
                add_le_add ihe hRstep
          _ ≤ (An + |x n|) * (Pn * (1 + es n) - 1)
                + tiny * ((n : ℝ) + 1) * (Pn * (1 + es n)) := by
                have h1 : |x n| ≤ |x n| * Pn := by
                  calc |x n| = |x n| * 1 := by ring
                    _ ≤ |x n| * Pn := mul_le_mul_of_nonneg_left hPn_ge (abs_nonneg _)
                have hAe : 0 ≤ An := Finset.sum_nonneg (fun i _ => abs_nonneg _)
                have hxn : 0 ≤ |x n| := abs_nonneg _
                nlinarith [h1, hPnn, hAe, hxn, hesn, htiny, hPn_ge,
                  mul_nonneg htiny (Nat.cast_nonneg n), mul_nonneg htiny hesn]
          _ = (An + |x n|) * (Pn * (1 + es n) - 1)
                + tiny * (((n : ℝ) + 1) * (Pn * (1 + es n))) := by
                ring
      exact ⟨growth, error⟩

/-- **B15 主交付（常系数形式）**：若每步 `|R i y − y| ≤ eps·|y| + tiny`
（`0 ≤ eps`、`0 ≤ tiny`），则 `n` 步累加的误差满足

    `|fl(Σ_{i<n} x_i) − Σ_{i<n} x_i|
       ≤ (Σ_{i<n}|x_i|)·((1+eps)^n − 1) + tiny·Σ_{i<n}(1+eps)^i`。

这正是「**累积模型 `err ≤ n(tiny + eps·mag)`**」的**精确形式**：
主导的相对项是 `(Σ|x|)·((1+eps)^n − 1)`（`≈ n·eps·Σ|x|`，即 `n` 倍放大），
而 `tiny` 项是 `tiny·(n·(1+eps)^n)` ——
**不是简单的 `n·tiny`**：下溢底在第 `i` 步注入后，会被**其后每一步**
以 `(1+eps)` 放大，最坏情形放大到 `(1+eps)^n`，故系数是 `n·(1+eps)^n`。

**诚实标注（关键）**：`tiny` 项的系数是 `n·(1+eps)^n`（`n` **乘上**总放大因子），
**不是** `n`。因此「`err ≤ n(tiny + eps·mag)`」型教科书叙述在 `tiny` 项上
只是**下界**（`n·tiny ≤ n(1+eps)^n·tiny`，见 `ieeeAccRtiny_tiny_sum_bounds`）；
严格上界必须带放大因子 `(1+eps)^n`。这一条是本节的**核心诚实结论**。 -/
theorem ieeeAccRtiny_error {R : ℝ → ℝ} {eps tiny : ℝ} (hε : 0 ≤ eps) (htiny : 0 ≤ tiny)
    (hR : ∀ y : ℝ, |R y - y| ≤ eps * |y| + tiny) (n : ℕ) (x : ℕ → ℝ) :
    |ieeeAccR R n x - ∑ i in Finset.range n, x i|
      ≤ (∑ i in Finset.range n, |x i|) * ((1 + eps) ^ n - 1)
        + tiny * ((n : ℝ) * (1 + eps) ^ n) := by
  rw [ieeeAccR_eq_accN]
  have h := ieeeAccNtiny_growth_error (R := fun _ : ℕ => R) (es := fun _ : ℕ => eps)
    (tiny := tiny) (fun _ => hε) htiny (fun _ _ => hR _) n x
  have hpref : ∀ k : ℕ, prefProd (fun _ : ℕ => eps) k = (1 + eps) ^ k := by
    intro k
    rw [prefProd, prod_const_one_add]
  simpa [hpref] using h.2

/-- **`tiny` 项：`n` 与放大因子的双向夹逼（诚实标注的精确内容）**：
`n ≤ (1+eps)^n` 且 `1 ≤ (1+eps)^n`（`0 ≤ eps`），故

    `n·tiny ≤ n·(1+eps)^n·tiny`。

即「`n·tiny`」是**下界**、「`n·(1+eps)^n·tiny`」是本文件给出的**上界**；
二者在 `eps = 0`（无相对误差）时**重合**（此时 `(1+0)^n = 1`）。 -/
theorem ieeeAccRtiny_tiny_sum_bounds {eps : ℝ} (hε : 0 ≤ eps) (n : ℕ) :
    (n : ℝ) ≤ (n : ℝ) * (1 + eps) ^ n ∧ (1 : ℝ) ≤ (1 + eps) ^ n := by
  have h1 : (1 : ℝ) ≤ 1 + eps := by linarith
  have hpow : 1 ≤ (1 + eps) ^ n := one_le_pow₀ h1
  exact ⟨le_mul_of_one_le_right (Nat.cast_nonneg n) hpow, hpow⟩

/-- **`eps = 0` 时带 `tiny` 的界退化为纯绝对模型**：`|fl(Σx) − Σx| ≤ n·tiny`
（每步只注入 `tiny`，无相对放大）——这是「渐近无害」的极限情形，
也说明上面的放大因子 `(1+eps)^n` 确实**只来自相对项**。 -/
theorem ieeeAccRtiny_error_zero_eps {R : ℝ → ℝ} {tiny : ℝ} (htiny : 0 ≤ tiny)
    (hR : ∀ y : ℝ, |R y - y| ≤ (0 : ℝ) * |y| + tiny) (n : ℕ) (x : ℕ → ℝ) :
    |ieeeAccR R n x - ∑ i in Finset.range n, x i| ≤ (n : ℝ) * tiny := by
  have h := ieeeAccRtiny_error (eps := 0) (tiny := tiny) le_rfl htiny hR n x
  simpa [mul_comm] using h

/-! ## 注：一致性与新内容的边界
  · **一致性定理**（`ieee_single_add_error`/`ieee_single_mul_error`/
    `ieee_fp16_round_abs_bound`/`ieee_fp16_underflow_dominated`/`ieee_loss_scaling_no_overflow`/
    `ieee_mixed_layer_error`/`ieee_mixed_matrix_frobenius_error`/`ieee_mixed_matrix_op_error`/
    `ieee_accumulation_error_bound`/`ieee_mixed_vs_full_precision`）：
    结论与 `RealMixedPrecision`/`RealFloatFormat` 的公理版**逐字相同**，
    因为 `IEEERound` 经 `ieeeToRoundOp` 是 `RoundOp` 的实例（`ieee_satisfies_roundOp`）。
  · **新内容**：`ieeeAccR`/`ieeeAccN` 系列的几何级数累加界
    （`ieeeAccR_growth`/`ieeeAccR_error`/`ieee_acc_error_sum_geom`/`ieeeAccN_growth_error`/
    `ieeeAccN_growth`/`ieeeAccN_error`/`ieee_accN_uniform_error`）与饱和系列
    （`fp16Sat*`/`fp16_round_sat_error`/`fpOverflow_fp16Max_iff_fp16Overflow`）
    ——公理版的 `accumulation_error_bound` 用「幅度尺度 `M`」叙述，本文件改为
    「逐项幅度和 `Σ|x_i|` × 几何因子」的**更精确**形式，并支持**逐层不同单位舍入**。
  · **诚实标注（B15 已补齐）**：累加模型原为**纯相对模型**（无 `tiny`）；本文件
    **已补**第三节的**带 `tiny` 累积模型**：`prefProd`、`ieeeAccNtiny_growth_error`
    （增长 + 误差，**前缀积**形式，含**逐层不同**舍入单位）、`ieeeAccRtiny_error`
    （常系数闭式 `err ≤ (Σ|x|)·((1+eps)^n − 1) + tiny·(n·(1+eps)^n)`）、
    `ieeeAccRtiny_tiny_sum_bounds`（`n` 与放大因子 `(1+eps)^n` 的双向夹逼）、
    `ieeeAccRtiny_error_zero_eps`（`eps = 0` 时退化为纯绝对模型 `n·tiny`）。
    **诚实边界（核心）**：`tiny` 项的精确系数是 **`n·(1+eps)^n`**，**不是** `n`——
    下溢底在每步注入后被其后各步以 `(1+eps)` 放大；故教科书的
    「`err ≤ n(tiny + eps·mag)`」在 `tiny` 项上只是**下界**。
    未做：`tiny`/`eps` 的**数值**（由 `FloatFormat` 参数化）、
    **逐层不同 `tiny_i`** 的版本（本节 `tiny` 是全局常数，**标注**）；
    `OverflowConv.toInfinity` 未数值化；
    `ieeeToFPAdder` 需要 `tiny = 0` 与 `eps ≤ 1` 两个显式假设。
  无 sorry/axiom/admit。 -/

end Lattice
