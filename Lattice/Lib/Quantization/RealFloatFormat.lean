import Mathlib
import Lattice.Lib.Optim.RealApprox
/-!
# LATTICE: 浮点格式建模 —— 抽象舍入算子与其误差公理

RealApprox 的 `Approx` 处理「函数在 ε 内近似等价」，但没有**浮点格式本身**的
模型。本文件给出最小的浮点格式抽象，供混合精度/量化误差界复用：

  1. `FloatFormat`（structure）：格式参数 —— 指数位 `expBits`、尾数位 `mantBits`、
     单位舍入 `eps`（unit roundoff）、绝对误差底 `tiny`（最小次正规数），
     并带上 `0 ≤ eps`、`0 ≤ tiny` 的字段（格式良定性）；
  2. 典型实例：`fp16`（5 指数字 / 10 尾数，`eps = 2⁻¹¹`、`tiny = 2⁻²⁴`）、
     `bf16`（8 / 7，`eps = 2⁻⁸`、`tiny = 2⁻¹³³`）、`fp32`（8 / 23）；
  3. `RoundOp`（structure）：**抽象舍入算子** —— 只要求两条公理式性质
     · `err_bound`：`|round x − x| ≤ eps·|x| + tiny`（相对误差 + 绝对底）
     · `idem`：`round (round x) = round x`（幂等：舍入到格式内的点不再改变）
     **诚实降级（显式标注）**：本文件**不建模 IEEE 逐位语义**
     （不舍入模式、不建模 subnormal/NaN/Inf 的位模式、不建模指数偏置），
     只把「舍入算子应满足的两条公理」作为 `RoundOp` 的字段；
     这不是 Lean `axiom`，而是**显式假设的数据**，使用者必须自己给出实例；
  4. `roundToFormat`（def）：`RoundOp` 的底层函数；
  5. `format_round_idempotent`：`round (round x) = round x`（直接来自 `idem`）；
  6. `format_error_bound`：`|round x − x| ≤ eps·|x| + tiny`（来自 `err_bound`）；
  7. `format_add_error`/`format_mul_error`：加法/乘法舍入误差的同类界；
  8. `format_error_bound_of_le`：`|x| ≤ M` ⟹ `|round x − x| ≤ eps·M + tiny`；
  9. `round_preserves_zero`：`tiny = 0` ⟹ `round 0 = 0`；
  10. `round_close`：`|x − y| ≤ η` ⟹ `|round x − y| ≤ eps·|x| + tiny + η`（传递性）；
  11. `op_error_propagation`（**核心**）：`κ`-Lipschitz 算子 `f` 在舍入输入下的
      「条件数 × eps」误差界 `|f (round x) − f x| ≤ κ·(eps·|x| + tiny)`
      ——抽象版的「误差传播 ≤ 条件数 · 单位舍入」；
  12. `op_error_chain`：两算子复合 `g ∘ f` 的误差界 `≤ λ·κ·(eps·|x| + tiny)`
      （运算链上误差按各环节 Lipschitz 常数相乘累积）。

诚实假设（全部显式标注）：`eps`、`tiny` 是格式数据而非从位宽推出的量
（真实格式里 `eps = 2^{−(mantBits+1)}`、`tiny` 由最小指数决定；本文件不推导它们）；
舍入算子的两条公理是**假设**而非定理；`op_error_propagation` 的 `κ ≥ 0`
与 Lipschitz 性是显式假设。与 `RealMatrixStability` 的关系：本文件的
`op_error_propagation` 是「条件数 × 单位舍入」这一稳定性叙事的抽象标量版
（`RealMatrixStability` 未在本仓库中出现，故不 import）。
模型无关：任意实数函数；无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 浮点格式参数 -/

/-- 浮点格式：指数位/尾数位（结构元数据）+ 单位舍入 `eps` + 绝对误差底 `tiny`。
`eps`、`tiny` 是**给定数据**（不是从位宽推算的），并带非负性字段。 -/
structure FloatFormat where
  /-- 指数位数 -/
  expBits : ℕ
  /-- 尾数位数 -/
  mantBits : ℕ
  /-- 单位舍入（unit roundoff） -/
  eps : ℝ
  /-- 绝对误差底（最小次正规数尺度） -/
  tiny : ℝ
  /-- 单位舍入非负 -/
  eps_nonneg : 0 ≤ eps
  /-- 绝对误差底非负 -/
  tiny_nonneg : 0 ≤ tiny

/-- IEEE binary16（FP16）：5 位指数、10 位尾数，`eps = 2⁻¹¹`、`tiny = 2⁻²⁴`。 -/
def fp16 : FloatFormat where
  expBits := 5
  mantBits := 10
  eps := ((2 : ℝ) ^ (11 : ℕ))⁻¹
  tiny := ((2 : ℝ) ^ (24 : ℕ))⁻¹
  eps_nonneg := by positivity
  tiny_nonneg := by positivity

/-- bfloat16（BF16）：8 位指数、7 位尾数，`eps = 2⁻⁸`、`tiny = 2⁻¹³³`。 -/
def bf16 : FloatFormat where
  expBits := 8
  mantBits := 7
  eps := ((2 : ℝ) ^ (8 : ℕ))⁻¹
  tiny := ((2 : ℝ) ^ (133 : ℕ))⁻¹
  eps_nonneg := by positivity
  tiny_nonneg := by positivity

/-- IEEE binary32（FP32）：8 位指数、23 位尾数，`eps = 2⁻²⁴`、`tiny = 2⁻¹⁴⁹`。 -/
def fp32 : FloatFormat where
  expBits := 8
  mantBits := 23
  eps := ((2 : ℝ) ^ (24 : ℕ))⁻¹
  tiny := ((2 : ℝ) ^ (149 : ℕ))⁻¹
  eps_nonneg := by positivity
  tiny_nonneg := by positivity

/-! ## 抽象舍入算子（公理式刻画） -/

/-- 抽象舍入算子：一个函数 `toFun` 加两条**假设**：
相对误差界 `|round x − x| ≤ eps·|x| + tiny` 与幂等性 `round (round x) = round x`。
**不建模 IEEE 逐位语义**（无舍入模式、无 NaN/Inf、无指数偏置）——
这是显式的抽象降级，两条性质作为结构字段由使用者提供。 -/
structure RoundOp (F : FloatFormat) where
  /-- 舍入函数 -/
  toFun : ℝ → ℝ
  /-- 相对误差界：`|round x − x| ≤ eps·|x| + tiny` -/
  err_bound : ∀ x : ℝ, |toFun x - x| ≤ F.eps * |x| + F.tiny
  /-- 幂等性：`round (round x) = round x` -/
  idem : ∀ x : ℝ, toFun (toFun x) = toFun x

/-- 舍入算子的函数形式（把 `RoundOp` 的底层函数取出）。 -/
def roundToFormat (F : FloatFormat) (r : RoundOp F) : ℝ → ℝ := r.toFun

/-! ## 基本性质 -/

/-- **幂等性**：`round (round x) = round x`。 -/
theorem format_round_idempotent (F : FloatFormat) (r : RoundOp F) (x : ℝ) :
    roundToFormat F r (roundToFormat F r x) = roundToFormat F r x :=
  r.idem x

/-- **基本舍入误差界**：`|round x − x| ≤ eps·|x| + tiny`。 -/
theorem format_error_bound (F : FloatFormat) (r : RoundOp F) (x : ℝ) :
    |roundToFormat F r x - x| ≤ F.eps * |x| + F.tiny :=
  r.err_bound x

/-- 加法舍入误差：`|round (a + b) − (a + b)| ≤ eps·|a + b| + tiny`。 -/
theorem format_add_error (F : FloatFormat) (r : RoundOp F) (a b : ℝ) :
    |roundToFormat F r (a + b) - (a + b)| ≤ F.eps * |a + b| + F.tiny :=
  r.err_bound (a + b)

/-- 乘法舍入误差：`|round (a · b) − a · b| ≤ eps·|a · b| + tiny`。 -/
theorem format_mul_error (F : FloatFormat) (r : RoundOp F) (a b : ℝ) :
    |roundToFormat F r (a * b) - a * b| ≤ F.eps * |a * b| + F.tiny :=
  r.err_bound (a * b)

/-- 有界输入的舍入误差界：`|x| ≤ M`（`M ≥ 0`）⟹ `|round x − x| ≤ eps·M + tiny`
（把相对项 `eps·|x|` 用输入界 `M` 换掉，供逐元素一致估计使用）。 -/
theorem format_error_bound_of_le (F : FloatFormat) (r : RoundOp F) {x M : ℝ}
    (hx : |x| ≤ M) :
    |roundToFormat F r x - x| ≤ F.eps * M + F.tiny := by
  refine le_trans (r.err_bound x) ?_
  exact add_le_add_right (mul_le_mul_of_nonneg_left hx F.eps_nonneg) F.tiny

/-- 零的舍入：`tiny = 0` 时 `round 0 = 0`
（误差界在 `x = 0` 处给出 `|round 0| ≤ 0`）。 -/
theorem round_preserves_zero (F : FloatFormat) (r : RoundOp F) (h : F.tiny = 0) :
    roundToFormat F r 0 = 0 := by
  have hb := r.err_bound 0
  rw [h] at hb
  simp at hb
  simpa [roundToFormat] using hb

/-- 传递性：`|x − y| ≤ η` ⟹ `|round x − y| ≤ eps·|x| + tiny + η`。 -/
theorem round_close (F : FloatFormat) (r : RoundOp F) {x y η : ℝ}
    (h : |x - y| ≤ η) :
    |roundToFormat F r x - y| ≤ F.eps * |x| + F.tiny + η := by
  have hsplit : roundToFormat F r x - y = (roundToFormat F r x - x) + (x - y) := by ring
  calc
    |roundToFormat F r x - y| = |(roundToFormat F r x - x) + (x - y)| := by rw [hsplit]
    _ ≤ |roundToFormat F r x - x| + |x - y| := abs_add _ _
    _ ≤ (F.eps * |x| + F.tiny) + η := add_le_add (r.err_bound x) h

/-! ## 定理（核心）：运算链误差传播 ≤ 条件数 · eps -/

/-- **运算误差传播（条件数 × eps）**：`f` 为 `κ`-Lipschitz（`κ ≥ 0` 为条件数），
输入经舍入 ⟹ `|f (round x) − f x| ≤ κ·(eps·|x| + tiny)`。
这就是数值稳定性叙事的抽象形式：**误差放大 = 条件数 × 单位舍入**。 -/
theorem op_error_propagation (F : FloatFormat) (r : RoundOp F) (f : ℝ → ℝ)
    (κ x : ℝ) (hκ : 0 ≤ κ) (hf : ∀ x y : ℝ, |f x - f y| ≤ κ * |x - y|) :
    |f (roundToFormat F r x) - f x| ≤ κ * (F.eps * |x| + F.tiny) := by
  calc
    |f (roundToFormat F r x) - f x| ≤ κ * |roundToFormat F r x - x| := hf _ _
    _ ≤ κ * (F.eps * |x| + F.tiny) :=
      mul_le_mul_of_nonneg_left (r.err_bound x) hκ

/-- **两段运算链的误差传播**：`f` 为 `κ`-Lipschitz、`g` 为 `λ`-Lipschitz
（`κ, λ ≥ 0`），舍入发生在 `f` 的输入 ⟹
`|g (f (round x)) − g (f x)| ≤ λ·κ·(eps·|x| + tiny)`
（误差沿链按各环节 Lipschitz 常数相乘累积 = 链的条件数）。 -/
theorem op_error_chain (F : FloatFormat) (r : RoundOp F) (f g : ℝ → ℝ)
    (κ lam x : ℝ) (hκ : 0 ≤ κ) (hlam : 0 ≤ lam)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ κ * |x - y|)
    (hg : ∀ x y : ℝ, |g x - g y| ≤ lam * |x - y|) :
    |g (f (roundToFormat F r x)) - g (f x)| ≤ lam * κ * (F.eps * |x| + F.tiny) := by
  have h2 : |f (roundToFormat F r x) - f x| ≤ κ * (F.eps * |x| + F.tiny) :=
    op_error_propagation F r f κ x hκ hf
  calc
    |g (f (roundToFormat F r x)) - g (f x)| ≤ lam * |f (roundToFormat F r x) - f x| := hg _ _
    _ ≤ lam * (κ * (F.eps * |x| + F.tiny)) := mul_le_mul_of_nonneg_left h2 hlam
    _ = lam * κ * (F.eps * |x| + F.tiny) := by ring

/-- 运算链的逐层形式：`n` 层 `κ`-Lipschitz 算子复合的舍入误差 ≤ `κⁿ·(eps·|x| + tiny)`
（`Function.iterate` 形式的链，`κ ≥ 0`）。 -/
theorem op_error_chain_iterate (F : FloatFormat) (r : RoundOp F) (f : ℝ → ℝ)
    (κ x : ℝ) (hκ : 0 ≤ κ)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ κ * |x - y|) :
    ∀ n : ℕ, |(f^[n]) (roundToFormat F r x) - (f^[n]) x| ≤ κ ^ n * (F.eps * |x| + F.tiny) := by
  have hbase : 0 ≤ F.eps * |x| + F.tiny :=
    add_nonneg (mul_nonneg F.eps_nonneg (abs_nonneg x)) F.tiny_nonneg
  intro n
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply, pow_zero, one_mul]
      exact r.err_bound x
  | succ n ih =>
      calc
        |(f^[n + 1]) (roundToFormat F r x) - (f^[n + 1]) x|
            = |f ((f^[n]) (roundToFormat F r x)) - f ((f^[n]) x)| := by
              rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        _ ≤ κ * |(f^[n]) (roundToFormat F r x) - (f^[n]) x| := hf _ _
        _ ≤ κ * (κ ^ n * (F.eps * |x| + F.tiny)) := mul_le_mul_of_nonneg_left ih hκ
        _ = κ ^ (n + 1) * (F.eps * |x| + F.tiny) := by ring

/-! ## 注：诚实边界与实例化
  · 本文件建模的是**舍入算子的公理**（`RoundOp.err_bound` + `RoundOp.idem`），
    不是 IEEE-754 的逐位语义：不建模舍入模式（就近/向上/向下）、
    不建模 NaN/Inf、不建模指数偏置与 subnormal 的位表示；
  · `eps`/`tiny` 是**格式数据**：真实格式满足 `eps = 2^{−(mantBits+1)}`、
    `tiny` 由最小指数决定，本文件不推导这一关系（`fp16`/`bf16`/`fp32`
    的取值按标准直接写出）；
  · `op_error_propagation`/`op_error_chain`/`op_error_chain_iterate` 把
    「误差传播 ≤ 条件数 × 单位舍入」形式化：`κ` 是 Lispchitz/条件数，
    `eps` 是单位舍入，`tiny` 是不可约的绝对底——与 RealApprox 的
    `layer_out_error_bound`（ε₁X+ε₂）同构，此处以舍入算子为中心组织。
  无 sorry/axiom/admit。 -/

end Lattice
