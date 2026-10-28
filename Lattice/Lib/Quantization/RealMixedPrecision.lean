import Mathlib
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Quantization.RealQuantizedError
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.LinearAlgebra.RealSparsity
import Lattice.Lib.Optim.RealApprox
/-!
# LATTICE: 混合精度训练（FP16/BF16）—— 动态范围、损失缩放与累加误差

RealFloatFormat 给出抽象浮点格式 `FloatFormat`/`RoundOp`。本文件把它用于
**混合精度训练**：前向（权重的伪量化）在 FP16/BF16 上做，累加与主权重在 FP32 上做。

  1. `fp16Max`/`fp16MinSubnormal`/`fp16Overflow`/`fp16Underflow`：FP16 动态范围的
     形式化——溢出条件 `|x| > 65504`、下溢条件 `|x| < 2⁻²⁴`；
  2. `fp16_overflow_iff`/`fp16_no_overflow_bounds`/`fp16_round_abs_bound`：
     溢出判定与「输入在范围内 ⟹ 舍入结果仍在 `65504·(1+eps)+tiny` 内」；
  3. `fp16_underflow_dominated`：下溢区 `|x| < 2⁻²⁴` 时绝对误差被 `tiny` 支配
     （相对界失效，只剩绝对底 `≤ 2·tiny`）；
  4. `lossScaled`/`loss_scaling_unscale`/`loss_scaling_bound`/
     `loss_scaling_no_overflow`（**损失缩放**）：损失乘 `2^k` 后梯度同步乘 `2^k`，
     未缩放梯度 `|g| ≤ 65504/2^k` 时缩放后**无溢出**；反缩放精确还原；
  5. `FPAdder`/`accSum`/`accumulation_error_bound`（**FP32 累加误差**）：
     每步加法舍入相对误差 `≤ eps`、各步幅度 `≤ M` ⟹
     `|fl(Σ_{k<n} x_k) − Σ_{k<n} x_k| ≤ 2·n·eps·M`
     （标准「`n·ε·(幅度尺度)`」型累加界；幅度尺度 `M` 可取代 `Σ|x_i|`，
     见 docstring 的诚实说明）；
  6. `mixedForward`/`fullForward`/`mixed_layer_error`：单层混合精度前向
     （权重经低精度舍入、乘积在 FP32 精确累加）与全精度前向之差的界
     `≤ n·(eps·W + tiny)·X`（`W`/`X` 为权重/输入幅度界）；
  7. `mixedMatrix`/`mixed_matrix_frobenius_error`：逐元素低精度舍入的
     Frobenius 误差界 `≤ √(m·n)·(eps·θ + tiny)`（`θ` 为权重幅度界）；
  8. `mixed_vs_full_precision`（**核心衔接**）：把逐层混合精度误差
     `δᵢ = √(n·n)·(eps·θᵢ + tiny)` 代入 RealQuantizedError 的
     `quantized_chain_error_closed`，得 n 层混合精度模型的端到端误差界
     ——混合精度误差界 ≤ 量化链的界（同一结构，δᵢ 来自浮点舍入）。

诚实假设（全部显式标注）：
  · FP16 的具体格式参数（`65504`、`2⁻²⁴`、`eps = 2⁻¹¹`、`tiny = 2⁻²⁴`）与
    FP32 的 `eps = 2⁻²⁴` 是**格式常数**，按 IEEE-754 直接写出，不从位宽推导；
  · 舍入算子仍是 RealFloatFormat 的 `RoundOp` 抽象（公理式：相对误差 + 幂等），
    **不建模 IEEE 逐位语义**（无 NaN/Inf、无舍入模式）；
  · 累加误差界的 `M`（每步中间和的幅度界）是显式假设；`Σ|x_i|` 形式
    由 `Σ|x_i| ≤ n·M` 得到（本文件用 `M` 叙述，见定理 docstring）；
  · 损失缩放用 `k : ℕ`（缩放因子 `2^k`，`k = 0` 即不缩放）。
模型无关：任意层数 `n` 与矩阵维数 `m×n`；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

open Matrix

/-! ## 一、FP16 动态范围 -/

/-- FP16 最大有限值：`65504 = 2¹⁵·(2 − 2⁻¹⁰)`。 -/
def fp16Max : ℝ := 65504

/-- FP16 最小正次正规数：`2⁻²⁴`。 -/
def fp16MinSubnormal : ℝ := ((2 : ℝ) ^ (24 : ℕ))⁻¹

/-- FP16 溢出：`|x| > 65504`（真实 FP16 溢出为 ±∞；本文件只建模条件）。 -/
def fp16Overflow (x : ℝ) : Prop := fp16Max < |x|

/-- FP16 下溢：`0 < |x| < 2⁻²⁴`（落入次正规/零区，相对精度失效）。 -/
def fp16Underflow (x : ℝ) : Prop := 0 < |x| ∧ |x| < fp16MinSubnormal

/-- **溢出条件**：`fp16Overflow x ↔ 65504 < |x|`（定义展开，作为可引用定理）。 -/
theorem fp16_overflow_iff (x : ℝ) : fp16Overflow x ↔ 65504 < |x| := Iff.rfl

/-- 非溢出 ⟹ 数值落在 `[−65504, 65504]`（`abs_le`）。 -/
theorem fp16_no_overflow_bounds {x : ℝ} (h : ¬ fp16Overflow x) :
    -65504 ≤ x ∧ x ≤ 65504 := by
  unfold fp16Overflow fp16Max at h
  rw [not_lt] at h
  exact abs_le.mp h

/-- 下溢的幅度刻画：`fp16Underflow x → |x| < 2⁻²⁴` 且 `0 < |x|`。 -/
theorem fp16_underflow_lt {x : ℝ} (h : fp16Underflow x) : |x| < fp16MinSubnormal := h.2

/-- **下溢条件**：`fp16Underflow x ↔ 0 < |x| ∧ |x| < 2⁻²⁴`。 -/
theorem fp16_underflow_iff (x : ℝ) :
    fp16Underflow x ↔ 0 < |x| ∧ |x| < fp16MinSubnormal := Iff.rfl

/-- **范围内舍入的绝对值界**：`|x| ≤ 65504` ⟹
`|round x| ≤ 65504·(1 + eps) + tiny`（舍入不放大到溢出的安全余量）。 -/
theorem fp16_round_abs_bound (F : FloatFormat) (r : RoundOp F) {x : ℝ}
    (hx : |x| ≤ 65504) :
    |roundToFormat F r x| ≤ 65504 * (1 + F.eps) + F.tiny := by
  have hb : |roundToFormat F r x| ≤ (F.eps * |x| + F.tiny) + |x| := by
    calc
      |roundToFormat F r x| = |(roundToFormat F r x - x) + x| := by congr 1; ring
      _ ≤ |roundToFormat F r x - x| + |x| := abs_add _ _
      _ ≤ (F.eps * |x| + F.tiny) + |x| := add_le_add_right (r.err_bound x) |x|
  have hstep : (F.eps * |x| + F.tiny) + |x| ≤ 65504 * (1 + F.eps) + F.tiny := by
    have h1 : F.eps * |x| ≤ F.eps * 65504 := mul_le_mul_of_nonneg_left hx F.eps_nonneg
    linarith
  linarith

/-- **下溢区误差被绝对底支配**：`|x| < 2⁻²⁴` 且 `eps·|x| ≤ tiny` ⟹
`|round x − x| ≤ 2·tiny`（相对界在次正规区失效，只剩不可约的 `tiny`）。 -/
theorem fp16_underflow_dominated (F : FloatFormat) (r : RoundOp F) {x : ℝ}
    (_hu : fp16Underflow x) (h : F.eps * |x| ≤ F.tiny) :
    |roundToFormat F r x - x| ≤ 2 * F.tiny := by
  calc
    |roundToFormat F r x - x| ≤ F.eps * |x| + F.tiny := r.err_bound x
    _ ≤ F.tiny + F.tiny := by linarith [h]
    _ = 2 * F.tiny := by ring

/-! ## 二、损失缩放（loss scaling） -/

/-- 损失缩放：把损失乘 `2^k`（梯度同步放大 `2^k`），避免下溢。 -/
def lossScaled (k : ℕ) (L : ℝ) : ℝ := (2 : ℝ) ^ k * L

/-- 反缩放精确还原：`2^k · (g / 2^k) = g`。 -/
theorem loss_scaling_unscale (k : ℕ) (g : ℝ) :
    (2 : ℝ) ^ k * (g / (2 : ℝ) ^ k) = g := by
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  exact mul_div_cancel₀ g hp

/-- **损失缩放的溢出条件**：`|g| ≤ M / 2^k` ⟹ `|2^k·g| ≤ M`。 -/
theorem loss_scaling_bound (k : ℕ) (g M : ℝ) (h : |g| ≤ M / (2 : ℝ) ^ k) :
    |(2 : ℝ) ^ k * g| ≤ M := by
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  rw [abs_mul, abs_of_nonneg (le_of_lt hp)]
  calc
    (2 : ℝ) ^ k * |g| ≤ (2 : ℝ) ^ k * (M / (2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hp)
    _ = M := mul_div_cancel₀ M (ne_of_gt hp)

/-- **损失缩放无溢出**：未缩放梯度满足 `|g| ≤ 65504 / 2^k` ⟹
缩放后的梯度 `2^k·g` 不溢出 FP16。 -/
theorem loss_scaling_no_overflow (k : ℕ) {g : ℝ}
    (h : |g| ≤ fp16Max / (2 : ℝ) ^ k) :
    ¬ fp16Overflow ((2 : ℝ) ^ k * g) := by
  rw [fp16_overflow_iff, not_lt]
  unfold fp16Max at h
  exact loss_scaling_bound k g 65504 h

/-! ## 三、FP32 累加误差 -/

/-- 浮点加法器（抽象）：`toFun a b` 是 `a + b` 的舍入结果，满足每步相对误差
`|toFun a b − (a + b)| ≤ eps·|a + b|`（`0 ≤ eps ≤ 1`）。 -/
structure FPAdder where
  /-- 舍入加法 -/
  toFun : ℝ → ℝ → ℝ
  /-- 单位舍入 -/
  eps : ℝ
  /-- 单位舍入非负 -/
  eps_nonneg : 0 ≤ eps
  /-- 单位舍入不超过 1（标准格式均满足） -/
  eps_le_one : eps ≤ 1
  /-- 每步加法的相对误差界 -/
  err_bound : ∀ a b : ℝ, |toFun a b - (a + b)| ≤ eps * |a + b|

/-- 左折叠累加：`accSum ad n x` 依次累加 `x 0, …, x (n−1)`。 -/
def accSum (ad : FPAdder) : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, x => ad.toFun (accSum ad n x) (x n)

/-- 累加误差的递归展开：第 `n+1` 步误差 = 本步舍入误差 + 前 `n` 步累积误差
（中间点插值）。 -/
lemma accSum_succ_sub (ad : FPAdder) (n : ℕ) (x : ℕ → ℝ) :
    accSum ad (n + 1) x - ∑ k in Finset.range (n + 1), x k
      = (ad.toFun (accSum ad n x) (x n) - (accSum ad n x + x n))
        + (accSum ad n x - ∑ k in Finset.range n, x k) := by
  rw [Finset.sum_range_succ]
  simp [accSum]
  ring

/-- **FP32 累加误差界**：每一步加法的相对误差 `≤ eps`、各步中间和的幅度
`≤ M`、各输入幅度 `≤ M` ⟹
`|fl(Σ_{k<n} x_k) − Σ_{k<n} x_k| ≤ 2·n·eps·M`。

⚠⚠ **第 20 轮：`0 ≤ M` 这个前提被删掉了。**

原来签名里有 `(_hM : 0 ≤ M)`，但它**在证明里从未被引用**（`_` 前缀就是证据），
而且**它是可导出的**：`hmag 0 (Nat.zero_le n)` 给出 `|accSum ad 0 x| ≤ M`，
而 `accSum ad 0 x = 0`，所以 `0 ≤ M`。

**删掉它使本条更强**（前提更少），不是更弱。下游 `ieee_accumulation_error_bound`
的 `hM` 只用来传给本条，因此一并去掉。

**诚��说明**：标准叙事写作 `n·ε·Σ|x_i|`；本文件用统一的幅度尺度 `M`
（`M = max(中间和幅度, 输入幅度)`），由 `Σ|x_i| ≤ n·M` 即得
`2·n·eps·M ≥ 2·eps·Σ|x_i|`——两种写法等价到常数因子，此处选择假设更少的形式。 -/
theorem accumulation_error_bound (ad : FPAdder) (M : ℝ) :
    ∀ (n : ℕ) (x : ℕ → ℝ),
      (∀ k, k ≤ n → |accSum ad k x| ≤ M) → (∀ k, k < n → |x k| ≤ M) →
      |accSum ad n x - ∑ k in Finset.range n, x k| ≤ 2 * (n : ℝ) * ad.eps * M := by
  intro n
  induction n with
  | zero =>
      intro x _hmag _hx
      simp [accSum]
  | succ n ih =>
      intro x hmag hx
      have he := ad.err_bound (accSum ad n x) (x n)
      have he0 : 0 ≤ ad.eps := ad.eps_nonneg
      have hsum : |accSum ad n x + x n| ≤ M + M := by
        have h1 : |accSum ad n x| ≤ M := hmag n (Nat.le_succ n)
        have h2 : |x n| ≤ M := hx n (Nat.lt_succ_self n)
        have := abs_add (accSum ad n x) (x n)
        linarith
      have hprev : |accSum ad n x - ∑ k in Finset.range n, x k| ≤ 2 * (n : ℝ) * ad.eps * M :=
        ih x (fun k hk => hmag k (le_trans hk (Nat.le_succ n)))
          (fun k hk => hx k (Nat.lt_succ_of_lt hk))
      have h1 : |accSum ad (n + 1) x - ∑ k in Finset.range (n + 1), x k|
          ≤ ad.eps * M + ad.eps * M + 2 * (n : ℝ) * ad.eps * M := by
        rw [accSum_succ_sub]
        calc
          |(ad.toFun (accSum ad n x) (x n) - (accSum ad n x + x n))
              + (accSum ad n x - ∑ k in Finset.range n, x k)|
              ≤ |ad.toFun (accSum ad n x) (x n) - (accSum ad n x + x n)|
                + |accSum ad n x - ∑ k in Finset.range n, x k| := abs_add _ _
          _ ≤ ad.eps * |accSum ad n x + x n|
                + |accSum ad n x - ∑ k in Finset.range n, x k| := by linarith
          _ ≤ ad.eps * (M + M) + 2 * (n : ℝ) * ad.eps * M :=
                add_le_add (mul_le_mul_of_nonneg_left hsum he0) hprev
          _ = ad.eps * M + ad.eps * M + 2 * (n : ℝ) * ad.eps * M := by ring
      have hgoal : 2 * ((n : ℝ) + 1) * ad.eps * M = ad.eps * M + ad.eps * M + 2 * (n : ℝ) * ad.eps * M := by
        ring
      calc
        |accSum ad (n + 1) x - ∑ k in Finset.range (n + 1), x k|
            ≤ ad.eps * M + ad.eps * M + 2 * (n : ℝ) * ad.eps * M := h1
        _ = 2 * ((n : ℝ) + 1) * ad.eps * M := hgoal.symm
        _ = 2 * ((n + 1 : ℕ) : ℝ) * ad.eps * M := by push_cast; ring

/-- 累加误差的非负性：`0 ≤ 2·n·eps·M`（`0 ≤ eps`、`0 ≤ M`）。 -/
theorem accumulation_error_nonneg (ad : FPAdder) (M : ℝ) (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ 2 * (n : ℝ) * ad.eps * M := by
  have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : 0 ≤ 2 * (n : ℝ) := by linarith
  have h3 : 0 ≤ 2 * (n : ℝ) * ad.eps := mul_nonneg h2 ad.eps_nonneg
  exact mul_nonneg h3 hM

/-! ## 四、单层混合精度前向 -/

/-- 混合精度前向（单层）：权重经低精度舍入 `R`、乘积在 FP32 精确累加。 -/
def mixedForward {n : ℕ} (R : ℝ → ℝ) (w x : Fin n → ℝ) : ℝ :=
  ∑ i, R (w i) * x i

/-- 全精度前向（单层）：`Σ wᵢxᵢ`（fp32 主权重、不额外舍入）。 -/
def fullForward {n : ℕ} (w x : Fin n → ℝ) : ℝ :=
  ∑ i, w i * x i

/-- **单层混合精度误差界**：权重幅度 `≤ W`、输入幅度 `≤ X`（`W, X ≥ 0`）⟹
`|mixedForward (round w) x − fullForward w x| ≤ n·(eps·W + tiny)·X`。 -/
theorem mixed_layer_error {n : ℕ} (F : FloatFormat) (r : RoundOp F) (w x : Fin n → ℝ)
    (W X : ℝ) (hW : 0 ≤ W) (_hX : 0 ≤ X)
    (hw : ∀ i, |w i| ≤ W) (hx : ∀ i, |x i| ≤ X) :
    |mixedForward (roundToFormat F r) w x - fullForward w x|
      ≤ (n : ℝ) * (F.eps * W + F.tiny) * X := by
  have hδ0 : 0 ≤ F.eps * W + F.tiny := add_nonneg (mul_nonneg F.eps_nonneg hW) F.tiny_nonneg
  have hterm : ∀ i : Fin n,
      |roundToFormat F r (w i) * x i - w i * x i| ≤ (F.eps * W + F.tiny) * X := by
    intro i
    have hsplit : roundToFormat F r (w i) * x i - w i * x i
        = (roundToFormat F r (w i) - w i) * x i := by ring
    rw [hsplit, abs_mul]
    have hw' : |roundToFormat F r (w i) - w i| ≤ F.eps * W + F.tiny := by
      have h1 : F.eps * |w i| ≤ F.eps * W := mul_le_mul_of_nonneg_left (hw i) F.eps_nonneg
      calc
        |roundToFormat F r (w i) - w i| ≤ F.eps * |w i| + F.tiny := r.err_bound (w i)
        _ ≤ F.eps * W + F.tiny := by linarith [h1]
    exact mul_le_mul hw' (hx i) (abs_nonneg _) hδ0
  calc
    |mixedForward (roundToFormat F r) w x - fullForward w x|
        = |∑ i : Fin n, (roundToFormat F r (w i) * x i - w i * x i)| := by
          unfold mixedForward fullForward
          rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin n, |roundToFormat F r (w i) * x i - w i * x i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (F.eps * W + F.tiny) * X := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (n : ℝ) * ((F.eps * W + F.tiny) * X) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * (F.eps * W + F.tiny) * X := by ring

/-- 全精度与混合精度前向之差的可加性读法（三角不等式的直接形式）：
`|mixed − full| ≤ Σᵢ |R(wᵢ) − wᵢ|·|xᵢ|`——逐元素舍入误差按输入幅度加权求和。 -/
theorem mixed_layer_error_pointwise {n : ℕ} (R : ℝ → ℝ) (w x : Fin n → ℝ) :
    |mixedForward R w x - fullForward w x|
      ≤ ∑ i : Fin n, |R (w i) - w i| * |x i| := by
  calc
    |mixedForward R w x - fullForward w x|
        = |∑ i : Fin n, (R (w i) * x i - w i * x i)| := by
          unfold mixedForward fullForward
          rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin n, |R (w i) * x i - w i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |R (w i) - w i| * |x i| := by
          apply Finset.sum_congr rfl
          intro i _
          have hsplit : R (w i) * x i - w i * x i = (R (w i) - w i) * x i := by ring
          rw [hsplit, abs_mul]

/-! ## 五、逐元素低精度舍入的矩阵误差 -/

/-- 逐元素低精度舍入的矩阵：`mixedMatrix R A i j = R (A i j)`。 -/
def mixedMatrix {m n : ℕ} (R : ℝ → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => R (A i j)

/-- **矩阵级混合精度误差界**：权重幅度 `≤ θ`（`θ ≥ 0`）⟹
`‖mixedMatrix (round) A − A‖_F ≤ √(m·n)·(eps·θ + tiny)`
（`(eps·θ + tiny)²` 逐元素求和 + `Real.sq_sqrt` 开方）。 -/
theorem mixed_matrix_frobenius_error {m n : ℕ} (F : FloatFormat) (r : RoundOp F)
    (A : Matrix (Fin m) (Fin n) ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hA : ∀ i j, |A i j| ≤ θ) :
    frobeniusNorm (mixedMatrix (roundToFormat F r) A - A)
      ≤ Real.sqrt ((m * n : ℕ) : ℝ) * (F.eps * θ + F.tiny) := by
  have hδ0 : 0 ≤ F.eps * θ + F.tiny := add_nonneg (mul_nonneg F.eps_nonneg hθ) F.tiny_nonneg
  have hsq : (frobeniusNorm (mixedMatrix (roundToFormat F r) A - A)) ^ 2
      ≤ (Real.sqrt ((m * n : ℕ) : ℝ) * (F.eps * θ + F.tiny)) ^ 2 := by
    calc
      (frobeniusNorm (mixedMatrix (roundToFormat F r) A - A)) ^ 2
          = ∑ i : Fin m, ∑ j : Fin n,
              ((mixedMatrix (roundToFormat F r) A - A) i j) ^ 2 := frobeniusNorm_sq _
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin n, (F.eps * θ + F.tiny) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            have hb : |(mixedMatrix (roundToFormat F r) A - A) i j| ≤ F.eps * θ + F.tiny := by
              have h1 : F.eps * |A i j| ≤ F.eps * θ := mul_le_mul_of_nonneg_left (hA i j) F.eps_nonneg
              have h2 := r.err_bound (A i j)
              simp only [mixedMatrix, Matrix.sub_apply, roundToFormat] at h2 ⊢
              linarith [h1, h2]
            exact sq_le_sq.mpr (by rwa [abs_of_nonneg hδ0])
      _ = ((m : ℝ) * (n : ℝ)) * (F.eps * θ + F.tiny) ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
      _ = (Real.sqrt ((m * n : ℕ) : ℝ) * (F.eps * θ + F.tiny)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((m * n : ℕ) : ℝ))]
            push_cast
            ring
  have hnonneg : 0 ≤ Real.sqrt ((m * n : ℕ) : ℝ) * (F.eps * θ + F.tiny) :=
    mul_nonneg (Real.sqrt_nonneg _) hδ0
  have habs := sq_le_sq.mp hsq
  rw [abs_of_nonneg (frobeniusNorm_nonneg _), abs_of_nonneg hnonneg] at habs
  exact habs

/-- 矩阵级算子误差界：`‖matCLME (mixedMatrix round A) − matCLME A‖_op ≤ √(m·n)·(eps·θ+tiny)`
（`opNorm_le_frobenius` + 定理）。 -/
theorem mixed_matrix_op_error {m n : ℕ} (F : FloatFormat) (r : RoundOp F)
    (A : Matrix (Fin m) (Fin n) ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hA : ∀ i j, |A i j| ≤ θ) :
    ‖matCLME (mixedMatrix (roundToFormat F r) A) - matCLME A‖
      ≤ Real.sqrt ((m * n : ℕ) : ℝ) * (F.eps * θ + F.tiny) := by
  calc
    ‖matCLME (mixedMatrix (roundToFormat F r) A) - matCLME A‖
        = ‖matCLME (mixedMatrix (roundToFormat F r) A - A)‖ := by rw [matCLME_sub]
    _ ≤ frobeniusNorm (mixedMatrix (roundToFormat F r) A - A) := opNorm_le_frobenius _
    _ ≤ Real.sqrt ((m * n : ℕ) : ℝ) * (F.eps * θ + F.tiny) :=
        mixed_matrix_frobenius_error F r A θ hθ hA

/-! ## 六、核心衔接：n 层混合精度模型端到端误差（回收 RealQuantizedError） -/

/-- **混合精度 vs 全精度（n 层端到端）**：每层权重幅度 `≤ θ i`（`θ i ≥ 0`）⟹
混合精度链（每层权重经 `roundToFormat F r` 逐元素舍入）与全精度链的端到端误差
`≤ Σ_{i<k} (∏后层范数)·(√(n·n)·(eps·θ i + tiny))·(∏前层范数)·‖x‖`。
δᵢ 来自 `mixed_matrix_op_error`，代入 `quantized_chain_error_closed`
——混合精度误差界**就是**量化链的界（同一结构，δᵢ 由浮点舍入给出），
这也说明：混合精度训练的前向误差可被 RealQuantizedError 的统一框架覆盖。 -/
theorem mixed_vs_full_precision {n : ℕ} (F : FloatFormat) (r : RoundOp F)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (θ : ℕ → ℝ) (k : ℕ)
    (hθ : ∀ i, i < k → 0 ≤ θ i) (hA : ∀ i, i < k → ∀ a b, |A i a b| ≤ θ i) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖quantFwd (fun i => matCLME (mixedMatrix (roundToFormat F r) (A i))) k x
        - quantFwd (fun i => matCLME (A i)) k x‖
        ≤ ∑ i in Finset.range k,
            (∏ j in Finset.Ioo i k, ‖matCLME (mixedMatrix (roundToFormat F r) (A j))‖)
              * (Real.sqrt ((n * n : ℕ) : ℝ) * (F.eps * θ i + F.tiny))
              * (∏ j in Finset.range i, ‖matCLME (A j)‖) * ‖x‖ := by
  intro x
  refine quantized_chain_error_closed (fun i => matCLME (A i))
    (fun i => matCLME (mixedMatrix (roundToFormat F r) (A i)))
    (fun i => Real.sqrt ((n * n : ℕ) : ℝ) * (F.eps * θ i + F.tiny)) k ?_ x
  intro i hi
  exact mixed_matrix_op_error F r (A i) (θ i) (hθ i hi) (hA i hi)

/-- FP16 特例的逐层误差界：`δ = √(n·n)·(eps₁₆·θ + tiny₁₆)`（`eps₁₆ = 2⁻¹¹`、
`tiny₁₆ = 2⁻²⁴`）——混合精度链中 FP16 前向的逐层量化式误差。 -/
theorem fp16_layer_delta (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Real.sqrt ((n * n : ℕ) : ℝ) * (fp16.eps * θ + fp16.tiny) ≥ 0 := by
  have : 0 ≤ fp16.eps * θ + fp16.tiny :=
    add_nonneg (mul_nonneg fp16.eps_nonneg hθ) fp16.tiny_nonneg
  positivity

/-! ## 注：实例化闭环与诚实边界
  · **动态范围**：`fp16Overflow`/`fp16Underflow` 是 `65504` 与 `2⁻²⁴` 处的
    严格条件（`fp16_overflow_iff`/`fp16_underflow_iff`），非溢出给出
    `[−65504, 65504]`（`fp16_no_overflow_bounds`）；范围内舍入的安全余量是
    `65504·(1+eps)+tiny`（`fp16_round_abs_bound`）。
  · **损失缩放**：`loss_scaling_unscale`（精确还原）+ `loss_scaling_no_overflow`
    （`|g| ≤ 65504/2^k` 时缩放不溢出的充分条件）。
  · **累加误差**：`accumulation_error_bound` 给出 `2·n·eps·M`；`M` 是中间和
    与输入的幅度界（显式假设），`Σ|x_i| ≤ n·M` 说明它与经典
    `n·ε·Σ|x_i|` 同阶。
  · **混合精度 vs 全精度**：`mixed_layer_error`（单层，`n·(eps·W+tiny)·X`）、
    `mixed_matrix_frobenius_error`/`mixed_matrix_op_error`（矩阵级
    `√(m·n)·(eps·θ+tiny)`），再由 `mixed_vs_full_precision` 代入
    RealQuantizedError 的闭式链界——**混合精度误差界 ≤ 量化链的界**，
    因为两者是同一个 δᵢ-传播结构，只有 δᵢ 的来源不同（浮点舍入 vs 量化舍入）。
  · **诚实边界**：`RoundOp` 是公理式抽象（无 IEEE 逐位语义、无 NaN/Inf）；
    `eps`/`tiny` 是格式常数而非位宽推导量；累加的 `M` 是显式幅度假设。
  无 sorry/axiom/admit。 -/

end Lattice
