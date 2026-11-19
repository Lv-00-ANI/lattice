import Mathlib
import Lattice.Lib.Compiler.ExecutableBoundary
import Lattice.Lib.Compiler.IRWeightsBridge

/-!
# **可执行边界推到权重：`ℚ` 上的整条链能跑**（阶段 S，`STATE-FINAL` §3.1 续）

## 上一轮做到哪一步

**第 978 轮的 `ExecutableBoundary` 让**网格求值**在 `ℚ` 上可执行，并证明与 `ℝ` 一致：**

```
gridEvalRat_coe : ((gridEvalRat g n x : ℚ) : ℝ) = gridEval (fun k => (g k).toReal) n (x : ℝ)
```

**⇒ 但那只是**求**。整条链还需要**编译**（符号 → 权重）也可执行。**

## 本轮补上的那一跳：`ℚ` 上的权重载体

**`IRWeights` 是 `ℕ → ℝ`。它的 `ℚ` 对应是 `ℕ → ℚ`：**

```lean
abbrev IRWeightsRat : Type := ℕ → ℚ
```

**编码器 `encodeGrid` 是**交织**（偶数位斜率、奇数位截距），逐位可计算；**
**⇒ 它的 `ℚ` 版本与 `ℝ` 版本逐位一致，而这一点**不需要新的算术**——只需按奇偶分两支。**

## 于是「整条链路能跑」有了确切含义

| 步 | `ℝ` 模型 | `ℚ` 模型（可执行） | 一致性 |
|:--|:--|:--|:--|
| 符号 → 段 | `ℕ → Segment` | `ℕ → SegmentRat` | `SegmentRat.evalRat_coe` |
| **符号 → 权重** | **`encodeGrid`** | **`encodeGridRat`** | **`encodeGridRat_coe`** |
| 权重 → 符号 | `decodeGrid` | `decodeGridRat` | `decodeGridRat_encodeGridRat` |
| 求值 | `gridEval` | `gridEvalRat` | `gridEvalRat_coe` |

**=> 四步全部有 `ℚ` 对应，且四步全部与 `ℝ` 模型一致。**

## 数值见证：不是「存在」，而是**算出来的**

**`endToEndRat_witness` 让整条链**跑一遍**：符号网格 → 编码成 `ℚ` 权重 → 解码 → 求值，
结果由 `norm_num` **直接算出**。**

**⇒ 这是 §3.1 从「能求值」到「整条链路能跑」的差别。**
**⇒ 它仍然不要求放弃任何 `ℝ` 定理：本文件一行都没有改既有定义。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`IRWeightsRat`** | **⭐⭐ `ℚ` 上的权重载体** |
| **`encodeGridRat`** | **⭐⭐ 可执行的交织编码** |
| **`decodeGridRat`** | **⭐⭐ 可执行的解码** |
| **`decodeGridRat_encodeGridRat`** | **⭐⭐ 往返恒等（`ℚ` 版）** |
| **`encodeGridRat_coe`** | **⭐⭐⭐ 编码在 `ℚ` 与 `ℝ` 上逐位一致** |
| **`endToEndRat_witness`** | **⭐⭐⭐ 整条链的数值见证，由 `norm_num` 算出** | -/

namespace Lattice.Lib.Compiler

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.IRWeightsBridge

/-- **⭐⭐ `ℚ` 上的权重载体：`ℕ → ℚ`。**

**=> 与 `IRWeights = ℕ → ℝ` 逐位对应，故一致性定理是逐位陈述。** -/
abbrev IRWeightsRat : Type := ℕ → ℚ

/-- **⭐⭐ 可执行的交织编码：偶数位取斜率、奇数位取截距。**

**=> 与 `encodeGrid` 定义逐字相同，只是装配在 `ℚ` 上，故**可计算**。** -/
def encodeGridRat (g : ℕ → SegmentRat) : IRWeightsRat :=
  fun i => if i % 2 = 0 then (g (i / 2)).m else (g (i / 2)).c

/-- **⭐⭐ 可执行的解码：相邻两位组成一段。** -/
def decodeGridRat (w : IRWeightsRat) : ℕ → SegmentRat :=
  fun k => ⟨w (2 * k), w (2 * k + 1)⟩

/-- **⭐⭐ `ℚ` 上的往返恒等。**

**=> 与第 965 轮 `decodeGrid_encodeGrid` 同构，但这次是**算得出来**的。** -/
theorem decodeGridRat_encodeGridRat (g : ℕ → SegmentRat) :
    decodeGridRat (encodeGridRat g) = g := by
  funext k
  show (⟨encodeGridRat g (2 * k), encodeGridRat g (2 * k + 1)⟩ : SegmentRat)
      = g k
  have hev : encodeGridRat g (2 * k) = (g k).m := by
    unfold encodeGridRat
    rw [if_pos (by omega : (2 * k) % 2 = 0), show (2 * k) / 2 = k from by omega]
  have hod : encodeGridRat g (2 * k + 1) = (g k).c := by
    unfold encodeGridRat
    rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0),
      show (2 * k + 1) / 2 = k from by omega]
  rw [hev, hod]

/-- **⭐⭐⭐ 编码在 `ℚ` 与 `ℝ` 上**逐位一致**。**

**=> 按奇偶分两支即可：两支都只是强制转换，没有算术。** -/
theorem encodeGridRat_coe (g : ℕ → SegmentRat) (i : ℕ) :
    ((encodeGridRat g i : ℚ) : ℝ) = encodeGrid (fun k => (g k).toReal) i := by
  unfold encodeGridRat encodeGrid
  by_cases h : i % 2 = 0
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- **⭐⭐⭐ 整条链路的数值见证：符号网格 → `ℚ` 权重 → 解码 → 求值。**

**=> `g` 恒取斜率为 `1`、截距为 `0` 的段；`n = 4`；在 `x = 3/8` 处求值。**

**=> `segmentIndexRat 4 (3/8) = (⌊3/2⌋).toNat = 1`，故取第 1 段，得 `1 · 3/8 + 0 = 3/8`。**

**⇒ 全部由 `norm_num` 算出——这是**可执行**的证据，不是「存在某个提取器」。** -/
theorem endToEndRat_witness :
    gridEvalRat (decodeGridRat (encodeGridRat (fun _ => (⟨1, 0⟩ : SegmentRat)))) 4 (3 / 8 : ℚ)
      = 3 / 8 := by
  norm_num [gridEvalRat, decodeGridRat, encodeGridRat, segmentIndexRat, SegmentRat.evalRat,
    Rat.floor]

end Lattice.Lib.Compiler
