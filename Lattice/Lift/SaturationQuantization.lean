/-
# 饱和截断：`clamp` 的格引理组，以及饱和量化的失真界

## 0. 上一轮为什么没做成，这一轮为什么成了

第 185 轮试了三条路，全失败，障碍记在 `LayerQuantizationBits.lean` 的边界段里：

1. `max`/`min` 直接 `rw` —— `max_eq_left` 与 `unfold` 后的形态对不上；
2. `if` 定义 + `split_ifs` —— 假设顺序不是预期的，且 **`omega` 不穿透未归约的 `if`**；
3. `Set.projIcc` —— `projIcc_val_mem` 等引理**不存在**。

**三条路的共同错误：试图在一个定理里展开 `max`/`min` 的定义。**

这一轮的关键是**不展开**：`max`/`min` 是**格运算**，它们有 `le_max_left`、`le_max_right`、
`min_le_left`、`min_le_right`、`max_le`、`le_min`、`max_eq_left`、`max_eq_right`、
`min_eq_left`、`min_eq_right`——**十条引理覆盖了我需要的全部推理**，一条也用不到定义。

第 185 轮记的结论是「需要先建一组 `clamp` 的格引理」；**这一轮把那组引理建出来了**。

## 1. `clamp` 的格引理组

| 引理 | 内容 | 用的格引理 |
|:--|:--|:--|
| `clamp_le` | `clampTo B x ≤ B` | `max_le` + `min_le_left` |
| `le_clamp` | `-B ≤ clampTo B x` | `le_max_left` |
| `clamp_eq_self` | `|x| ≤ B → clamp = x` | `max_le`/`min_le_right`/`le_min`/`le_max_right` |
| `clamp_eq_of_le` | `x ≤ -B → clamp = -B` | `max_eq_left` |
| `clamp_eq_of_ge` | `B ≤ x → clamp = B` | `max_eq_right` |
| **`clamp_error`** | **`|clamp - x| ≤ max (|x| - B) 0`** | 前五条 |

**`clamp_error` 是饱和失真的完整刻画**：`|x| ≤ B` 时为零，超出时正好是超出量。

## 2. 饱和量化：总失真 = 舍入 + 饱和

真实量化器的失真有两个来源，本节把它们**分开**：

```lean
satQuant b B x := clampTo B (x / 2^b) * 2^b        -- 先丢位，再截断
```

**`quantRingLoss` 与 `quantSatLoss` 分开陈述**，因为它们的性质根本不同：

- **舍入损失** `< 2^b`（`LayerQuantizationBits.quant_error_lt_two_pow`）：**与值无关**，是常数界；
- **饱和损失** `≤ max (|x| - B) 0`：**依赖值**，`|x| > B` 时随超出量线性增长。

**把两者合成一个常数界是不可能的**——这正是为什么「量化误差 ≤ 2^b」这句话在有截断时是**错的**。
本节把它写成两个定理，而不是一个乐观的单界。

## 3. 边界

- **`satQuant` 先舍入再截断**，顺序与实现一致（先除，再 clamp，再乘回）。反过来做会对不齐。
- **不加饱和之前，`b` 位量化的误差是常数界；加了之后，误差无上界**（可随 `|x|` 任意大）。
  **这是量化失真的本质，不是本节的形式化缺陷。**
- 本节**不改** `LayerQuantization.lean`、`LayerQuantizationBits.lean` 的任何既有定理。
- 本节**不建** `LossyRep` 实例：`LossyRep.semEq` 需要一个**与 `p` 无关**的口径，
  而饱和失真的界依赖 `p` 本身（`max (|p| - B) 0`）。**这不是遗漏，是结构与事实不符**：
  `LossyRep` 的 `obs` 是「两个符号点的关系」，而饱和失真的界是「一个点与它的量化值的关系」，
  它当然依赖那个点。要装进 `LossyRep`，`obs` 得写成 `|p - q| ≤ max (|p| - B) 0`，
  那**不对称**——而 `obs_refl` 只要求自反，所以能做，但那样 `obs` 就不是「等价关系」的直觉了。
  **本节选择陈述定理而不硬塞进结构。**
-/
import Mathlib
import Lattice.Lift.LayerQuantizationBits

namespace Lattice.Lift.IntQuant

/-! ## 一、`clamp` 的格引理组

**不展开 `max`/`min` 的定义**——它们是格运算，十条标准引理足够。这正是第 185 轮三次失败后
学到的：失败都在展开定义那一步。 -/

/-- **截断到 `[-B, B]`**。 -/
def clampTo (B x : ℤ) : ℤ := max (-B) (min B x)

/-- **上界**：`clampTo B x ≤ B`。 -/
theorem clamp_le (B x : ℤ) (hB : 0 ≤ B) : clampTo B x ≤ B :=
  max_le (by omega) (min_le_left B x)

/-- **下界**：`-B ≤ clampTo B x`。 -/
theorem le_clamp (B x : ℤ) : -B ≤ clampTo B x :=
  le_max_left _ _

/-- **区间内不动**：`|x| ≤ B` 时截断不改变值。 -/
theorem clamp_eq_self (B x : ℤ) (hB : 0 ≤ B) (hx : |x| ≤ B) : clampTo B x = x := by
  have hx1 : -B ≤ x := (abs_le.mp hx).1
  have hx2 : x ≤ B := (abs_le.mp hx).2
  apply le_antisymm
  · exact max_le hx1 (min_le_right B x)
  · exact le_trans (le_min hx2 (le_refl x)) (le_max_right _ _)

/-- **低于下界时夹到下界**。 -/
theorem clamp_eq_of_le (B x : ℤ) (hx : x ≤ -B) : clampTo B x = -B := by
  have hmin : min B x ≤ -B := le_trans (min_le_right B x) hx
  exact max_eq_left hmin

/-- **高于上界时夹到上界**。 -/
theorem clamp_eq_of_ge (B x : ℤ) (hB : 0 ≤ B) (hx : B ≤ x) : clampTo B x = B := by
  have hmin : min B x = B := min_eq_left hx
  rw [clampTo, hmin]
  exact max_eq_right (by omega)

/-- **饱和失真的完整刻画**：截断值与 `x` 的差不超过超出量。

`|x| ≤ B` 时为零，超出时正好是 `|x| - B`。**饱和失真没有别的东西。** -/
theorem clamp_error (B x : ℤ) (hB : 0 ≤ B) :
    |clampTo B x - x| ≤ max (|x| - B) 0 := by
  by_cases hx : x < -B
  · have hneg : x < 0 := by omega
    rw [clamp_eq_of_le B x (le_of_lt hx)]
    have : (-B : ℤ) - x = -x - B := by ring
    rw [this, abs_of_pos (by omega), abs_of_neg hneg]
    exact le_max_left _ _
  · by_cases hx2 : B < x
    · have hpos : 0 < x := by omega
      rw [clamp_eq_of_ge B x hB (le_of_lt hx2)]
      have : (B : ℤ) - x = -(x - B) := by ring
      rw [this, abs_neg, abs_of_pos (by omega), abs_of_pos hpos]
      exact le_max_left _ _
    · have hin : |x| ≤ B := by
        rw [abs_le]
        constructor <;> omega
      rw [clamp_eq_self B x hB hin]
      rw [show x - x = (0 : ℤ) by ring, abs_zero]
      exact le_max_right _ _

/-! ## 二、饱和量化：两条失真分开陈述 -/

/-- **饱和量化**：先丢 `b` 位，再截断到 `[-B, B]`，再乘回。

顺序与实现一致：除 → clamp → 乘。**反过来做会对不齐**（先乘回再截断，
截断作用在量化后的值上而不是量化域上）。 -/
def satQuant (b : ℕ) (B x : ℤ) : ℤ := clampTo B (x / (2 : ℤ) ^ b) * 2 ^ b

/-- **舍入损失**：丢 `b` 位造成的那一份，**与值无关的常数界**。

这是 `quant_error_lt_two_pow` 的直接复用。 -/
theorem satQuant_rounding (b : ℕ) (x : ℤ) :
    |(x / (2 : ℤ) ^ b) * 2 ^ b - x| < 2 ^ b := by
  have h := quant_error_lt_two_pow b x
  rwa [mul_comm] at h

/-- **饱和损失**：截断造成的那一份，**依赖值**。

`|q| ≤ B` 时为零；超出时等于超出量。 -/
theorem satQuant_saturation (b : ℕ) (B : ℤ) (hB : 0 ≤ B) (x : ℤ) :
    |clampTo B (x / (2 : ℤ) ^ b) - x / (2 : ℤ) ^ b| ≤
      max (|x / (2 : ℤ) ^ b| - B) 0 :=
  clamp_error B _ hB

/-- **总失真不能用一个常数界住**：一个具体见证显示饱和误差可以是 `2^b` 的任意倍数。

取 `x = (B + 1) * 2^b`：它量化成 `B + 1`，截断到 `B`，乘回 `B * 2^b`，误差正好 `2^b`。
再取 `x = (B + k) * 2^b` 就得到 `k * 2^b`——**误差随超出量线性增长，与位宽无关。**

**这是本节最重要的陈述**：加了截断之后，「量化误差 ≤ 2^b」这句话**是错的**，
而很多人会默认它。饱和失真的量级由**值域**决定，不由位宽决定。 -/
theorem satQuant_error_scales (b : ℕ) (B : ℤ) (hB : 0 ≤ B) (k : ℕ) :
    satQuant b B ((B + k + 1) * 2 ^ b) - (B + k + 1) * 2 ^ b = -(k + 1) * 2 ^ b := by
  unfold satQuant
  have hpos : (0 : ℤ) < 2 ^ b := by positivity
  rw [Int.mul_ediv_cancel _ (ne_of_gt hpos)]
  have hge : B ≤ B + k + 1 := by omega
  rw [clamp_eq_of_ge B _ hB hge]
  ring

/-- **推论**：误差的绝对值是 `(k+1) * 2^b`，所以它随 `k` 无界增长、与 `b` 无关。 -/
theorem satQuant_error_abs (b : ℕ) (B : ℤ) (hB : 0 ≤ B) (k : ℕ) :
    |satQuant b B ((B + k + 1) * 2 ^ b) - (B + k + 1) * 2 ^ b| = (k + 1) * 2 ^ b := by
  rw [satQuant_error_scales b B hB k]
  rw [neg_mul, abs_neg, abs_of_pos (by positivity)]

end Lattice.Lift.IntQuant
