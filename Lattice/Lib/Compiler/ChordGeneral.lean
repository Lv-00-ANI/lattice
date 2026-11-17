import Mathlib
import Lattice.Lib.Compiler.WeightSequence
import Lattice.Lib.Compiler.PiecewiseWeights

/-!
# **一般弦**：把 `chordSegment` 从 `x²` 泛化到任意函数（阶段 F，P8 边界 3）

## 为什么需要泛化

**`WeightSequence.chordSegment a b = ⟨a + b, -(a·b)⟩` 是**过 `(a,a²)` 与 `(b,b²)` 的割线**。
它对 `f = ·²` 正确，但**把它写死进了定义**：`a + b` 就是 `(b²-a²)/(b-a)` 这个特例。**

**=> 于是证明「分段线性族能精确表示**仿射**函数」时必须另起一套，
而那条陈述正是**表达力**的核心（P8 §10 边界 3）。**

**本文件把割线定义为**从函数值出发**的一般构造：**

```lean
def chordSlope (f : ℝ → ℝ) (a b : ℝ) : ℝ := (f b - f a) / (b - a)
def chordOf (f : ℝ → ℝ) (a b : ℝ) : Segment :=
  ⟨chordSlope f a b, f a - chordSlope f a b * a⟩
```

**=> 于是 `chordSegment` 成为 `chordOf (·²)` 的**特例**（定理 `chordOf_sq`），
旧结果不被丢弃，而是被**包含**。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`chordOf_eval_left`** | **⭐⭐ 弦在 `a` 处取 `f a`** |
| **`chordOf_eval_right`** | **⭐⭐ 弦在 `b` 处取 `f b`** |
| **`chordOf_sq`** | **⭐⭐⭐ `chordOf (·²) a b = chordSegment a b`（泛化包含旧特例）** |
| **`chordOf_affine`** | **⭐⭐⭐ 仿射函数的弦**就是该函数本身** |
| **`affine_exactly_representable`** | **⭐⭐⭐ 表达力：仿射权重误差恰为 `0`** |

## 这一组定理对 P8 的意义

**第 944 轮的下界说：线性族对 `x²` 有 `1/8` 地板。**
**=> 本条列的说法是：**对仿射函数，弦是精确的。**

**=> 两者合起来给出「为什么地板存在」的**结构性解释**：
**分段线性族**严格包含**仿射族**，所以它能做的事多于仿射族；
而 `x²` 不在仿射族里（第 944 轮的 `1/8`），所以仿射族必然失败。**

**=> 这就是边界 3 的可做部分：不是「完整表达定理」（仍需堆叠构造），
而是**包含关系 + 精确表示**这一层的表达力。** -/

namespace Lattice.Lib.Compiler.ChordGeneral

open Set
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights

/-- **⭐⭐ 两点斜率 `(f b - f a) / (b - a)`。** -/
noncomputable def chordSlope (f : ℝ → ℝ) (a b : ℝ) : ℝ := (f b - f a) / (b - a)

/-- **⭐⭐⭐ 过 `(a, f a)` 与 `(b, f b)` 的**一般弦**。**

**=> 斜率由两点决定，截距使该直线过 `(a, f a)`。**
**=> 于是 `chordOf (·²)` 应当退化为 `chordSegment`（见 `chordOf_sq`）。** -/
noncomputable def chordOf (f : ℝ → ℝ) (a b : ℝ) : Segment :=
  ⟨chordSlope f a b, f a - chordSlope f a b * a⟩

/-- **⭐⭐ 弦在左端点取 `f a`。**

**=> `m·a + (f a - m·a) = f a`，纯代数，无需 `a ≠ b`。** -/
theorem chordOf_eval_left (f : ℝ → ℝ) (a b : ℝ) : (chordOf f a b).eval a = f a := by
  unfold chordOf Segment.eval
  ring

/-- **⭐⭐ 弦在右端点取 `f b`。**

**=> 需要 `a ≠ b`（否则斜率无定义）。** -/
theorem chordOf_eval_right (f : ℝ → ℝ) (a b : ℝ) (h : a ≠ b) :
    (chordOf f a b).eval b = f b := by
  unfold chordOf Segment.eval chordSlope
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

/-- **⭐⭐⭐ 泛化包含旧特例：`chordOf (·²) a b = chordSegment a b`。**

**=> 对 `f x = x²`：斜率 `(b²-a²)/(b-a) = a + b`，截距 `a² - (a+b)·a = -a·b`。**

**=> 这就是 `chordSegment` 的 `⟨a+b, -(a*b)⟩`。
=> 于是第 948–959 轮关于 `chordSegment` 的全部结果**都不作废**，
而是本定义的特例。** -/
theorem chordOf_sq (a b : ℝ) (h : a ≠ b) :
    chordOf (fun x : ℝ => x ^ 2) a b = chordSegment a b := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [chordOf, chordSlope, chordSegment]
  congr 1
  · -- slopes: (b²-a²)/(b-a) = a+b
    field_simp
    ring
  · -- intercepts: a² - (a+b)·a = -a·b
    field_simp
    ring

/-- **⭐⭐⭐ 仿射函数的弦**就是该函数本身**。**

**=> 设 `f x = c·x + d`，则过任意两点的斜率都是 `c`，截距都是 `d`。**
**=> **无需 `a ≠ b`**：斜率公式 `(c·b + d - (c·a + d))/(b - a)` 在 `b = a` 时退化，
但结论（弦 `= ⟨c, d⟩`）在 `b ≠ a` 时成立。**

**=> 这是「分段线性族**包含**仿射族」的结构性根据。** -/
theorem chordOf_affine (c d a b : ℝ) (h : a ≠ b) :
    chordOf (fun x : ℝ => c * x + d) a b = ⟨c, d⟩ := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [chordOf, chordSlope]
  congr 1
  · -- slope = c
    field_simp
    ring
  · -- intercept = d
    field_simp
    ring

/-- **⭐⭐⭐ 表达力：仿射函数的弦在**任意点**都复现该函数（误差恰为 `0`）。**

**=> 陈述：`c·b + d - (c·a + d) = c·(b - a)`，故弦就是 `⟨c, d⟩`，
于是 `(chordOf f a b).eval x = c·x + d` 对所有 `x` 成立。**

**=> 与第 944 轮的 `1/8` 地板对照：
**对仿射 `f` 误差为 `0`，对 `x²` 误差 `≥ 1/8`。**
**=> 两者的差别在于 `x²` 不在仿射族内——
这正是「线性族为何有地板」的**结构性解释**，而不是一个偶然的常数。** -/
theorem affine_exactly_representable (c d a b x : ℝ) (h : a ≠ b) :
    |(c * x + d) - (chordOf (fun t : ℝ => c * t + d) a b).eval x| = 0 := by
  rw [chordOf_affine c d a b h]
  unfold Segment.eval
  simp only
  ring_nf
  exact abs_zero

/-- **⭐⭐ 推论：仿射弦的误差不超过任何 `ε ≥ 0`。**

**=> 与 `quarter_inv_sq_tends_to_zero` 的形状对齐，
说明「仿射族能满足任意精度」是**平凡**的（误差为零），
而「`x²` 能被分段线性族任意精度逼近」才需要 `1/(4n²)` 的估计。** -/
theorem affine_within_any_eps (c d a b x ε : ℝ) (h : a ≠ b) (hε : 0 ≤ ε) :
    |(c * x + d) - (chordOf (fun t : ℝ => c * t + d) a b).eval x| ≤ ε := by
  rw [affine_exactly_representable c d a b x h]
  exact hε

/-! ## 把一般弦接回分段族

**=> 上面几节证明了「弦」的一般理论；本节让它**承担作用**：
用 `chordOf` 定义**任意函数**的分段线性插值族，并证明两条：**

1. **对 `x²`，它**就是**第 955 轮的 `piecewiseWeights`（旧族是新族的特例）；**
2. **对仿射函数，它**精确**（误差为零）。** -/

/-- **⭐⭐⭐ 任意函数的分段线性插值族。**

**=> `piecewiseInterp f n x` 取 `x` 所在片上的**一般弦**（过该片两端点）。
`n` 段时它是 `f` 的分段线性插值。** -/
noncomputable def piecewiseInterp (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (chordOf f ((segmentIndex n x : ℝ) / n) (((segmentIndex n x : ℝ) + 1) / n)).eval x

/-- **⭐ 相邻网格点不相等（`0 < n` 时）。** -/
theorem grid_ne (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ((k : ℝ) / n) ≠ (((k : ℝ) + 1) / n) := by
  intro h
  have hdiff : ((k : ℝ) + 1) / n - (k : ℝ) / n = 0 := by linarith [h]
  have hone : ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n := by
    field_simp
  rw [hone] at hdiff
  have hpos : (0 : ℝ) < 1 / n := by positivity
  linarith

/-- **⭐⭐⭐ 旧族是新族的特例：`piecewiseInterp (·²) = piecewiseWeights`。**

**=> 于是第 948–959 轮关于 `chordSegment` / `piecewiseWeights` 的全部结果
**都不作废**——它们是本泛化的特例。**

**=> 这正是「泛化的泛化」应有的形状：新定义**包含**旧定义，
且包含关系本身是一条定理。** -/
theorem piecewiseInterp_sq (n : ℕ) (hn : 0 < n) (x : ℝ) :
    piecewiseInterp (fun t : ℝ => t ^ 2) n x
      = Lattice.Lib.Compiler.PiecewiseWeights.piecewiseWeights n x := by
  unfold piecewiseInterp Lattice.Lib.Compiler.PiecewiseWeights.piecewiseWeights
  rw [chordOf_sq _ _ (grid_ne n hn (segmentIndex n x))]

/-- **⭐⭐⭐ 表达力：对**任意**仿射函数，分段线性插值**处处精确**。**

**=> 陈述：`piecewiseInterp (fun t => c·t + d) n x = c·x + d`，误差为零。**

**=> 与第 944 轮的 `1/8` 地板对照，这就是「线性族为何有地板」的**结构性理由**：
**分段线性族**包含**仿射族（误差 `0`），所以它能表示仿射族表示不了的东西；
而 `x²` 不在仿射族内，故仿射族必然失败。**

**=> P8 §10 边界 3 的可做部分到此闭合：**
**不是「完整表达定理」（仍需堆叠构造），而是**包含关系 + 精确表示**。** -/
theorem piecewiseInterp_affine_exact (c d : ℝ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    piecewiseInterp (fun t : ℝ => c * t + d) n x = c * x + d := by
  unfold piecewiseInterp
  rw [chordOf_affine c d _ _ (grid_ne n hn (segmentIndex n x))]
  unfold Segment.eval
  ring

end Lattice.Lib.Compiler.ChordGeneral
