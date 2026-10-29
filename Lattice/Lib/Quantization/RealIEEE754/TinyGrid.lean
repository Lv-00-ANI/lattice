import Mathlib
import Lattice.Lib.Quantization.RealIEEE754.Basic
import Lattice.Lib.Quantization.RealIEEE754.Nonvacuous

/-!
# `IEEERound` 在 `tiny > 0` 时的居民：`tiny`-网格舍入

## 上一轮留下的缺口，这一轮关掉

第 34 轮（`Nonvacuous.lean`）证了 `IEEERound` 在**退化格式**（`eps = tiny = 0`）上可居，
并诚实指出**那不是关于真实格式的证据**——`fp16` 的 `tiny > 0`，而当时没有构造。

**本轮给出构造**：`x ↦ tiny · ⌊x/tiny⌋`。它对**任意** `tiny > 0` 的格式满足全部七个字段。

## ⚠ 一条必须写下的更正

第 34 轮的 `grid_rounding_fails_relative_bound` 陈述是

    ¬ (∀ x : ℝ, |δ * ⌊x/δ⌋ - x| ≤ δ * |x|)        -- 即 tiny = 0

**这条定理本身是对的**，但它当时的**解读**被写成了「固定网格不能建模浮点」。**那个解读太强了。**

关键在右端：`err_bound` 是 `eps·|x| + tiny`，**不是** `eps·|x|`。取步长为 `tiny` 的网格，
误差是 `≤ tiny`（绝对），而右端**恰好**也有 `+ tiny` 那一项——**绝对误差被右端的 `tiny` 吸收**，
于是界对**所有** `x` 成立，**不需要 `|x|` 的下界**。

**所以：`tiny = 0` 时固定网格失败，`tiny > 0` 时成功。** 这不是矛盾，是那条反例的范围被说清了。 -/

namespace Lattice.Lib.Quantization

open Lattice.Lib.Quantization

/-! ## 一、两条关于 `⌊·⌋` 的算术 -/

/-- `|⌊y⌋ − y| < 1`。 -/
theorem abs_floor_sub_lt_one (y : ℝ) : abs ((⌊y⌋ : ℝ) - y) < 1 := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  rw [abs_lt]
  constructor <;> linarith

/-- **`|y| ≤ 1` 时 `|⌊y⌋| ≤ 1`**。 -/
theorem abs_floor_le_one {y : ℝ} (h : |y| ≤ 1) : abs ((⌊y⌋ : ℝ)) ≤ 1 := by
  have h1 : -1 ≤ y := (abs_le.mp h).1
  have h2 : y ≤ 1 := (abs_le.mp h).2
  have hle := Int.floor_le y
  -- the lower bound is an INTEGER step: `-1 ≤ y` gives `-1 ≤ ⌊y⌋` via `Int.le_floor`
  have hz : (-1 : ℤ) ≤ ⌊y⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  rw [abs_le]
  constructor
  · exact_mod_cast hz
  · linarith

/-! ## 二、`tiny`-网格舍入与它的七个字段 -/

/-- **`tiny`-网格舍入**：`x ↦ tiny · ⌊x/tiny⌋`。

**为什么步长是 `tiny` 而不是 `eps`**：见文件头——`err_bound` 的右端有 `+ tiny` 这一项，
绝对误差 `tiny` 被它吸收。 -/
noncomputable def tinyGrid (F : FloatFormat) (x : ℝ) : ℝ := F.tiny * (⌊x / F.tiny⌋ : ℝ)

/-- **幂等**：网格是闭的，再舍入一次不动。 -/
theorem tinyGrid_idem {F : FloatFormat} (ht : 0 < F.tiny) (x : ℝ) :
    tinyGrid F (tinyGrid F x) = tinyGrid F x := by
  unfold tinyGrid
  have hne : F.tiny ≠ 0 := ne_of_gt ht
  have hdiv : F.tiny * (⌊x / F.tiny⌋ : ℝ) / F.tiny = (⌊x / F.tiny⌋ : ℝ) := by
    field_simp
  rw [hdiv, Int.floor_intCast]

/-- **单调**。 -/
theorem tinyGrid_mono {F : FloatFormat} (ht : 0 < F.tiny) : Monotone (tinyGrid F) := by
  intro a b hab
  unfold tinyGrid
  have h1 : a / F.tiny ≤ b / F.tiny := by gcongr
  have h2 : ⌊a / F.tiny⌋ ≤ ⌊b / F.tiny⌋ := Int.floor_le_floor h1
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (le_of_lt ht)

/-- **符号保持（非负）**。 -/
theorem tinyGrid_sign_pos {F : FloatFormat} (ht : 0 < F.tiny) {x : ℝ} (h : 0 ≤ x) :
    0 ≤ tinyGrid F x := by
  unfold tinyGrid
  have h1 : 0 ≤ x / F.tiny := div_nonneg h (le_of_lt ht)
  have h2 : (0 : ℤ) ≤ ⌊x / F.tiny⌋ := Int.le_floor.mpr (by push_cast; exact h1)
  exact mul_nonneg (le_of_lt ht) (by exact_mod_cast h2)

/-- **符号保持（非正）**。 -/
theorem tinyGrid_sign_neg {F : FloatFormat} (ht : 0 < F.tiny) {x : ℝ} (h : x ≤ 0) :
    tinyGrid F x ≤ 0 := by
  unfold tinyGrid
  have h1 : x / F.tiny ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (le_of_lt ht)
  have h2 : ⌊x / F.tiny⌋ ≤ 0 := Int.floor_nonpos h1
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (by exact_mod_cast h2)

/-- ⭐ **相对误差界**：`|tiny·⌊x/tiny⌋ − x| ≤ eps·|x| + tiny`，**对所有 `x`**。 -/
theorem tinyGrid_err {F : FloatFormat} (ht : 0 < F.tiny) (x : ℝ) :
    abs (tinyGrid F x - x) ≤ F.eps * |x| + F.tiny := by
  unfold tinyGrid
  have hkey : F.tiny * (⌊x / F.tiny⌋ : ℝ) - x
      = F.tiny * ((⌊x / F.tiny⌋ : ℝ) - x / F.tiny) := by
    field_simp
    ring
  rw [hkey, abs_mul, abs_of_pos ht]
  have h1 : abs ((⌊x / F.tiny⌋ : ℝ) - x / F.tiny) < 1 := abs_floor_sub_lt_one _
  have h2 : F.tiny * abs ((⌊x / F.tiny⌋ : ℝ) - x / F.tiny) ≤ F.tiny := by
    calc F.tiny * abs ((⌊x / F.tiny⌋ : ℝ) - x / F.tiny) ≤ F.tiny * 1 :=
          mul_le_mul_of_nonneg_left (le_of_lt h1) (le_of_lt ht)
      _ = F.tiny := mul_one _
  have h3 : 0 ≤ F.eps * |x| := mul_nonneg F.eps_nonneg (abs_nonneg _)
  linarith

/-- **次正规界**：`|x| ≤ tiny ⟹ |tiny·⌊x/tiny⌋| ≤ tiny`。 -/
theorem tinyGrid_subnormal {F : FloatFormat} (ht : 0 < F.tiny) {x : ℝ} (h : |x| ≤ F.tiny) :
    abs (tinyGrid F x) ≤ F.tiny := by
  unfold tinyGrid
  have hy : |x / F.tiny| ≤ 1 := by
    rw [abs_div, abs_of_pos ht, div_le_one ht]
    exact h
  have hfloor : abs ((⌊x / F.tiny⌋ : ℝ)) ≤ 1 := abs_floor_le_one hy
  rw [abs_mul, abs_of_pos ht]
  calc F.tiny * abs ((⌊x / F.tiny⌋ : ℝ)) ≤ F.tiny * 1 :=
        mul_le_mul_of_nonneg_left hfloor (le_of_lt ht)
    _ = F.tiny := mul_one _

/-! ## 三、结论：`tiny > 0` 的格式都有居民 -/

/-- ⭐⭐ **任意 `tiny > 0` 的格式上 `IEEERound` 非空**：`tiny`-网格舍入满足全部七个字段。 -/
noncomputable def tinyGridRound (F : FloatFormat) (ht : 0 < F.tiny) (m : RoundMode) :
    IEEERound F m where
  toFun := tinyGrid F
  err_bound := tinyGrid_err ht
  idem := tinyGrid_idem ht
  monotone := tinyGrid_mono ht
  sign_preserve_pos := fun _ hx => tinyGrid_sign_pos ht hx
  sign_preserve_neg := fun _ hx => tinyGrid_sign_neg ht hx
  subnormal_bound := fun _ hx => tinyGrid_subnormal ht hx

/-- ⭐⭐ **`tiny > 0` 的格式上 `IEEERound` 非空**。 -/
theorem ieee_round_nonempty_of_tiny_pos (F : FloatFormat) (ht : 0 < F.tiny) (m : RoundMode) :
    Nonempty (IEEERound F m) :=
  ⟨tinyGridRound F ht m⟩

/-- **`fp16` 可居**（`tiny = 2⁻²⁴ > 0`）。 -/
theorem fp16_round_nonempty (m : RoundMode) : Nonempty (IEEERound fp16 m) := by
  have ht : 0 < fp16.tiny := by unfold fp16; positivity
  exact ieee_round_nonempty_of_tiny_pos fp16 ht m

/-- **`bf16` 可居**。 -/
theorem bf16_round_nonempty (m : RoundMode) : Nonempty (IEEERound bf16 m) := by
  have ht : 0 < bf16.tiny := by unfold bf16; positivity
  exact ieee_round_nonempty_of_tiny_pos bf16 ht m

/-- **`fp32` 可居**。 -/
theorem fp32_round_nonempty (m : RoundMode) : Nonempty (IEEERound fp32 m) := by
  have ht : 0 < fp32.tiny := by unfold fp32; positivity
  exact ieee_round_nonempty_of_tiny_pos fp32 ht m

end Lattice.Lib.Quantization
