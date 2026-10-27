/-
# 位宽参数化的整层量化：`b` 位，误差严格小于 `2^b`

## 0. 为什么需要这一节

`Lift/LayerQuantization.lean` 把量化从标量提升到了整层，但**丢位数硬编码为 1**（除 2）——

```lean
quant L := (fun i j => L.1 i j / 2, fun j => L.2 j / 2)     -- 只有 1 位
```

**那只对应 1 bit 量化**。真实部署是 4 bit 或 8 bit（`2^b`）。所以第 183 轮的实例是**示意**，
不是可用参数——这一节把它变成可参数的。

## 1. 核心引理

```lean
theorem quant_error_lt_two_pow (b : ℕ) (x : ℤ) :
    |2^b * (x / 2^b) - x| < 2^b
```

**证明思路**：差值正好是余数。

`x - 2^b * (x / 2^b) = x % 2^b`（这正是 `Int.emod_def` 的内容：
`a % b = a - b * (a / b)`，取负号即可），而余数落在 `[0, 2^b)`
（`Int.emod_nonneg` + `Int.emod_lt_of_pos`）。

**注意是严格小于**，不是 `≤`：`b` 位余数的上界是开区间。`b = 0` 时 `2^0 = 1`，
所以误差 `< 1`，即**误差为 0**——不丢位就不失真，这是正确的边界行为。

## 2. 为什么 `b = 1` 与第 183 轮的版本不同

第 183 轮用的是 `RoundingBackend.roundtrip_error_le_one`：`|2 * (x/2) - x| ≤ 1`（**`≤ 1`**）。

本节给出的是 **`< 2`**，在 `b = 1` 时即 `< 2`。两者都对，但本节的界更松一档
（因为余数在 `[0,2)` 里可以是 `1`，而 `≤ 1` 恰好卡住）。**第 183 轮的界更好，但它不可推广**：
`b = 8` 时余数可以到 `255`，`≤ 1` 显然不成立。

**所以本节取代它的推广位置，而不是取代它本身**：`layerQuantization` 仍然是 1 位情形里更紧的陈述。

## 3. 交付

| 声明 | 内容 |
|:--|:--|
| `quant_error_lt_two_pow` | **核心**：`b` 位量化的误差严格小于 `2^b` |
| `quantB` / `dequantB` | `b` 位的量化 / 反量化 |
| `obsWithin` | 逐分量误差 `< 2^b` |
| `obsWithin_refl` | 该口径自反 |
| `dequantB_quantB_error` | 整层的逐分量误差 |
| **`layerQuantizationB`** | **`LossyRep`，位宽 `b` 为参数** |
| `layerQuantizationB_one_bits` | `b = 1` 时与实际实现一致 |

## 4. 边界

- **仍然不做饱和截断**。真实量化器截到 `[-2^(b-1), 2^(b-1))`（有符号），那时误差界不成立，
  而**那是量化失真的主要来源**。本节只证「丢低位」。

  **第 185 轮试过做它，没做成，障碍记录在这里**（不是「没时间」，是具体卡点）：
  需要先定义 `clampTo B x := max (-B) (min B x)` 并证
  `|clampTo B x - x| ≤ max (|x| - B) 0`。三条路都试了：
  1. **`max`/`min` 直接 `rw`**：`Int` 上 `⊔`/`⊓` 是记法，`max_eq_left` 的目标形态与
     `unfold` 后的表达式对不上（报 `did not find instance of the pattern x ⊔ -B`）；
  2. **改成 `if` 定义 + `split_ifs`**：分支数对，但 `split_ifs` 产生的假设顺序与预期不同
     （得到 `h1 : B ≤ x`、`h2 : -B ≤ B`），后续 `omega` 在含 `if` 项的目标上给出
     「possible counterexample」——`omega` 不穿透未归约的 `if`；
  3. **`Set.projIcc`**：定义可行（`hB : 0 ≤ B` 给 `-B ≤ B`），但 `Set.projIcc_val_mem`
     在本 mathlib 不存在（与 `Int.div_mul_add_emod` 一样，名字是猜的），而剩下的
     `omega` 步骤在 `|·|` 与 `max` 组合上仍失败。

  **结论**：这条路需要的是**先建一组 `clamp` 的格引理**（`clamp_le`、`le_clamp_iff`、
  `clamp_eq_self` 之类），而不是在一个定理里硬解 case。**那是独立的一块**，
  按目标的「该分文件的分文件」，它应该有自己的一节。**本轮不硬凑一个弱化版本冒充它。**
- **`obsWithin` 仍只界住单分量**，不界住层的作用（`affineAct` 输出误差）。
- **`b` 很大时 `2^b` 溢出**不在形式化范围内：`ℤ` 是无界的，而真实实现是定宽整数。
  **这是模型与实现之间一处已知的差距，不是遗漏。**
- 本节**不改** `LayerQuantization.lean`、`RoundingBackend.lean` 的任何既有定理。
-/
import Mathlib
import Lattice.Lift.LossyRepresentation
import Lattice.Lift.LayerQuantization

namespace Lattice.Lift.IntQuant

open Lattice.Lift.LossyRepresentation

variable {m n : ℕ}

/-- **`b` 位量化的误差严格小于 `2^b`。**

差值正好是余数（`Int.emod_def`），余数落在 `[0, 2^b)`。 -/
theorem quant_error_lt_two_pow (b : ℕ) (x : ℤ) :
    |2 ^ b * (x / (2 : ℤ) ^ b) - x| < (2 : ℤ) ^ b := by
  have hpos : (0 : ℤ) < 2 ^ b := by positivity
  have hkey : 2 ^ b * (x / (2 : ℤ) ^ b) - x = -(x % (2 : ℤ) ^ b) := by
    have := Int.emod_def x ((2 : ℤ) ^ b)
    rw [this]; ring
  rw [hkey, abs_neg, abs_of_nonneg (Int.emod_nonneg _ (ne_of_gt hpos))]
  exact Int.emod_lt_of_pos _ hpos

/-- **丢 `b` 位的整层量化。** -/
def quantB (b : ℕ) : IntLayer m n → IntLayer m n :=
  fun L => (fun i j => L.1 i j / (2 : ℤ) ^ b, fun j => L.2 j / (2 : ℤ) ^ b)

/-- **反量化**：乘回 `2^b`。 -/
def dequantB (b : ℕ) : IntLayer m n → IntLayer m n :=
  fun L => (fun i j => 2 ^ b * L.1 i j, fun j => 2 ^ b * L.2 j)

/-- **观察口径**：每个分量误差 `< 2^b`。

用严格小于而不是 `≤`，因为 `b` 位余数的上界是开区间——这与 `b = 0`（不丢位则不失真）
的边界行为一致。 -/
def obsWithin (b : ℕ) (p q : IntLayer m n) : Prop :=
  (∀ i j, |p.1 i j - q.1 i j| < (2 : ℤ) ^ b) ∧
    (∀ j, |p.2 j - q.2 j| < (2 : ℤ) ^ b)

/-- 该口径自反。 -/
theorem obsWithin_refl (b : ℕ) (p : IntLayer m n) : obsWithin b p p := by
  refine ⟨?_, ?_⟩
  · intro i j; simpa using (abs_zero : |(0:ℤ)| = 0).le.trans_lt (by positivity : (0:ℤ) < 2 ^ b)
  · intro j; simpa using (abs_zero : |(0:ℤ)| = 0).le.trans_lt (by positivity : (0:ℤ) < 2 ^ b)

/-- **整层的逐分量误差**：每个分量都由一维引理给出。 -/
theorem dequantB_quantB_error (b : ℕ) (L : IntLayer m n) :
    obsWithin b (dequantB b (quantB b L)) L := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact quant_error_lt_two_pow b (L.1 i j)
  · intro j
    exact quant_error_lt_two_pow b (L.2 j)

/-- **`b` 位整层量化是一个 `LossyRep`**：位宽是参数，不是硬编码。

`semEq` 就是 `dequantB_quantB_error`——三次复用同一维引理。 -/
noncomputable def layerQuantizationB (b : ℕ) : LossyRep (IntLayer m n) (IntLayer m n) where
  inputP := Fin n → ℤ
  inputW := Fin n → ℤ
  encode := id
  decode := id
  compile := quantB b
  extract := dequantB b
  obs := obsWithin b
  obs_refl := obsWithin_refl b
  semEq := dequantB_quantB_error b

/-- **`b = 1` 时与第 183 轮的实现一致**：`quantB 1` 与 `quant` 逐分量相同。

这是「推广而非替换」的机器检查形式。 -/
theorem layerQuantizationB_one_bits (L : IntLayer m n) :
    (quantB (m := m) (n := n) 1 L) = quant L := by
  unfold quantB quant
  simp

end Lattice.Lift.IntQuant
