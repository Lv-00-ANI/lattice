import Mathlib
import Lattice.Lib.Quantization.RealIEEE754.Basic

/-!
# `IEEERound` 非空吗？——以及为什么「非空」这件事本身几乎什么都没说

## 为什么这个问题必须问

`Lib/Quantization/RealIEEE754/Basic.lean` 把 IEEE-754 的舍入建模成一个**七字段结构**
`IEEERound F m`：舍入函数、相对误差界、幂等、单调、双侧符号保持、次正规界。
文件自己诚实标注「这些性质是结构字段（显式数据）」。

**但没有任何地方证明过这个结构有居民。** 一个不可满足的结构会让它下游的一切
（`ieee_error_bound_of_le`、`FloatStackRefinement.roundLayer_rel`）**关于虚无地成立**——`∀ R : IEEERound F m, …`
在空类型上是真命题，且不含信息。

## 本文件给的两个答案，一个正一个负

1. **✅ 非空**：在**退化格式**（`eps = tiny = 0`）上，恒等函数满足全部七个字段。
2. **❌ 但这不是关于真实格式的证据**：`eps = tiny = 0` 时**唯一的** `IEEERound` 就是恒等
   （`ieee_round_eq_id_of_eps_zero`）。所以第 1 条只说明**字段彼此不矛盾**，
   **不说明 `fp16`/`fp32` 上存在这样的舍入**。

## 第三条：为什么不能用一个固定网格凑出 `eps > 0` 的居民

`grid_rounding_fails_relative_bound`：`x ↦ δ·⌊x/δ⌋` **不**满足相对误差界。
**这不是技术困难，是数学事实**——固定步长的误差是**绝对**的（`< δ`），
而浮点的误差是**相对**的（随量级缩放）。取 `x = δ/2` 即反例。

**所以构造 `fp16` 上的居民需要「尾数随量级缩放」的模型**（`s · 2^⌊log₂|x|⌋ · mantissa`），
那是一件独立的工作，**本文件不做，也不假装做了**。 -/

namespace Lattice.Lib.Quantization

open Lattice.Lib.Quantization

/-! ## 一、退化格式：`eps = tiny = 0` -/

/-- **退化格式**：`eps = tiny = 0`。

`FloatFormat` 只要求两者**非负**（不是正），所以这是合法格式——
它对应的不是任何真实 IEEE 格式，而是一个**精确算术**的理想化。 -/
def exactFormat : FloatFormat where
  expBits := 0
  mantBits := 0
  eps := 0
  tiny := 0
  eps_nonneg := le_refl 0
  tiny_nonneg := le_refl 0

/-- **恒等函数是退化格式上的一个合法 `IEEERound`**：七个字段逐条成立。 -/
def identityRound (m : RoundMode) : IEEERound exactFormat m where
  toFun := id
  err_bound := by intro x; simp [exactFormat]
  idem := by intro x; rfl
  monotone := monotone_id
  sign_preserve_pos := by intro x h; simpa using h
  sign_preserve_neg := by intro x h; simpa using h
  subnormal_bound := by intro x h; simpa using h

/-- ⭐ **`IEEERound` 不是空结构**：退化格式上它有居民。

**这条能排除的情形**：字段互相矛盾（那样整条 IEEE 链都是空的）。
**这条不能排除的情形**：真实格式上没有居民——见 `ieee_round_eq_id_of_eps_zero` 与
`grid_rounding_fails_relative_bound`。 -/
theorem ieee_round_nonempty (m : RoundMode) : Nonempty (IEEERound exactFormat m) :=
  ⟨identityRound m⟩

/-- ⭐⭐ **`eps = tiny = 0` 时唯一的舍入是恒等。**

**这是上一条的诚实面**：非空性在退化格式上是**平凡**的，因为误差界退化为 `|round x − x| ≤ 0`。
所以「`IEEERound` 非空」**不构成关于 `fp16`/`fp32` 的证据**——那需要另一条构造。 -/
theorem ieee_round_eq_id_of_eps_zero {F : FloatFormat} (heps : F.eps = 0) (htiny : F.tiny = 0)
    (m : RoundMode) (R : IEEERound F m) : R.toFun = id := by
  funext x
  have hb := R.err_bound x
  rw [heps, htiny] at hb
  have hb0 : |R.toFun x - x| ≤ 0 := by simpa using hb
  have hzero : R.toFun x - x = 0 := abs_eq_zero.mp (le_antisymm hb0 (abs_nonneg _))
  exact sub_eq_zero.mp hzero

/-! ## 二、为什么固定网格不行 -/

/-- ⭐⭐ **固定网格舍入无法满足相对误差界。**

对任意步长 `δ ∈ (0,1)`，`x ↦ δ·⌊x/δ⌋` **不**满足 `|f x − x| ≤ δ·|x|`（`tiny = 0` 的相对界）。

**反例是 `x = δ/2`**：绝对误差 `δ/2`，相对界只给 `δ·δ/2 = δ²/2`，而 `δ < 1` 时后者更小。

**所以相对误差界是「尾数随量级缩放」的性质，不是「舍入到某个网格」的性质**——
这条把「构造 `fp16` 上的 `IEEERound` 需要什么」说清楚了，而不是只留下一个未做的缺口。 -/
theorem grid_rounding_fails_relative_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ¬ (∀ x : ℝ, |δ * (⌊x / δ⌋ : ℝ) - x| ≤ δ * |x|) := by
  intro h
  have hx : ⌊(δ / 2) / δ⌋ = 0 := by
    have hq : (δ / 2) / δ = 1 / 2 := by field_simp; ring
    rw [hq]
    exact Int.floor_eq_zero_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb := h (δ / 2)
  rw [hx] at hb
  simp only [Int.cast_zero, mul_zero, zero_sub, abs_neg,
             abs_of_pos (by linarith : (0 : ℝ) < δ / 2)] at hb
  nlinarith [hb, hδ, hδ1]

end Lattice.Lib.Quantization
