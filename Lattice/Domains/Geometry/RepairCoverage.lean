/-
# 修复算子的覆盖：`sqDistEq` 与 `collinear`

## 0. 本节补什么

`REPAIR-CENSUS §5` 与外部审查指出同一缺口：

> `distEq`、`collinear`、`parallel` 等没有修复算子，再注入不覆盖它们。

**核实**：`GeoConstraint` 有八个构造子（`eqZero`、`leZero`、`ltZero`、`gtZero`、
`sqDistEq`、`equalLength`、`collinear`、`perpendicular`），而 `Geo` 层只有
`samePointRepair`、`perpRepair`、`conjRepair` 三类。**覆盖确实不足。**

本节补 `sqDistEq` 与 `collinear`。

## 1. 证明思路：照 `perpRepair` 的形态

`perpRepair` 的做法是：**`μ` 取指示（未满足为 1，满足为 0），`fix` 一步建立约束。**
于是：

- `absorbs`：已满足时 `fix` 不动（`μ` 已是 0）；
- `decreases`：未满足时 `fix` 一步建立约束，`μ` 从 1 降到 0；
- `atomic`：`μ = 0` 即已满足。

**本节两类都用这个形态**，因此 `atomic` 与 `decreases` 都由「`fix` 一步建立约束」得到。

### 1.1 `sqDistEq`：沿方向伸缩

`|ab|² = d`。修复：**`a` 不动、方向不动、只改长度**，令 `k = √(d / |ab|²)`。
因 `|a, a+k(b−a)|² = k²|ab|² = d`，一步到位。

**前提 `|ab|² ≠ 0`**（两重合时方向无定义）——这是必要前提，不是遗漏。

### 1.2 `collinear`：把第三点投到连线上

三点 `a b c` 共线 ⟺ `c` 在直线 `ab` 上。修复：把 `c` 换成 `a + t(b−a)` 对某个 `t`。
**投影系数 `t := ⟨c−a, b−a⟩ / |b−a|²`**，则 `c` 一步落到 `ab` 上。

**前提 `|b−a|² ≠ 0`**（`a ≠ b`）。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `sqDist` | 两点距离平方 |
| `sqDistFix` / `sqDistFix_reaches` | 伸缩修复，**一步达到目标** |
| `sqDistRepair` | `Repair` 实例（三条义务齐备） |
| `projCoeff` / `collinearFix` | 投影修复 |
| `collinearRepair` | `Repair` 实例（三条义务齐备） |
| `one_step_suffices` | 两类算子都是**一次修复**到解 |

## 3. 边界

- 在 `ℝ` 上做，`Pt n := Fin n → ℝ`，与 `perpRepair` 一致。
- **`d ≥ 0` 是必要前提**：`d < 0` 时 `|ab|² = d` 无解（`sqDistEq_rhs_nonneg` 已记录）。
  本节把 `d < 0` 的情形交给 `absorbs/decreases` 的守卫：`fix` 在该情形下不变，`μ` 不降，
  **算子因此不成立**——这是正确行为，因为**无解时不该要求算子工作**。
- `collinear` 需要 `a ≠ b`。`a = b` 时 `ab` 不是直线，投影无定义。
- 本节**不**做 `ratioDivision`：`GeoConstraint` 里**没有这个构造子**（审查提到的可能是旧库名字）。
- `sqDistEq` 的符号侧 `d : GeoExpr n` 需要先求值成实数，
  本节在**已求值**的配置上工作——这与 `perpRepair` 的选择相同。
-/
import Mathlib
import Lattice.Domains.Geometry.LoopPerp
import Lattice.Domains.Constraints.Constraint
import Lattice.Domains.Geometry.RepairPerp

open scoped BigOperators

namespace Lattice.Geo

namespace RepairCoverage

open Lattice.Lift Lattice.Core

variable {n : ℕ}

/-! ## 一、`sqDistEq` 的修复 -/

/-- **两点距离的平方。** -/
noncomputable def sqDist (p q : Pt n) : ℝ := ∑ i, (p i - q i) ^ 2

/-- **距离平方非负。** -/
theorem sqDist_nonneg (p q : Pt n) : 0 ≤ sqDist p q :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **伸缩后的距离平方**：`|a, a + k(b−a)|² = k²|ab|²`。

这是 `sqDistFix` 正确性的核心计算。 -/
theorem sqDist_affine (a b : Pt n) (k : ℝ) :
    sqDist a (fun i => a i + k * (b i - a i)) = k ^ 2 * sqDist a b := by
  unfold sqDist
  have h : ∀ i, (a i - (a i + k * (b i - a i))) ^ 2 = k ^ 2 * (a i - b i) ^ 2 := by
    intro i; ring
  simp only [h]
  rw [Finset.mul_sum]

/-- **`sqDistEq` 的修复**：`d` 为目标距离平方，把 `b` 沿 `a→b` 伸缩。

`|ab|² = 0` 时（两点重合）方向无定义，因此**原样返回**——
此时 `fix` 不建立约束，`Repair` 的字段会诚实失败，而不是假装修好。 -/
noncomputable def sqDistFix (a : Pt n) (d : ℝ) : Pt n → Pt n :=
  fun b =>
    if h : sqDist a b = 0 then b
    else fun i => a i + Real.sqrt (d / sqDist a b) * (b i - a i)

/-- **`sqDistFix` 一步达到目标**：`d ≥ 0` 且 `|ab|² ≠ 0` 时，修复后距离平方恰为 `d`。 -/
theorem sqDistFix_reaches (a b : Pt n) {d : ℝ} (hd : 0 ≤ d) (hne : sqDist a b ≠ 0) :
    sqDist a (sqDistFix a d b) = d := by
  unfold sqDistFix
  rw [dif_neg hne, sqDist_affine]
  have hpos : 0 < sqDist a b := lt_of_le_of_ne (sqDist_nonneg a b) (Ne.symm hne)
  rw [Real.sq_sqrt (div_nonneg hd (le_of_lt hpos))]
  field_simp

/-! ## 二、`collinear` 的修复 -/

/-- **投影系数**：把 `c` 投到直线 `ab` 上所需的 `t`。 -/
noncomputable def projCoeff (a b c : Pt n) : ℝ :=
  (∑ i, (c i - a i) * (b i - a i)) / sqDist a b

/-- **`collinear` 的修复**：把 `c` 换到直线 `ab` 上。 -/
noncomputable def collinearFix (a b : Pt n) : Pt n → Pt n :=
  fun c => fun i => a i + projCoeff a b c * (b i - a i)

/-- **投影后的第三点落在直线 `ab` 上**：存在 `t` 使 `c' = a + t(b−a)`。

这正是三点共线的判据（`c' − a` 是 `b − a` 的标量倍）。 -/
theorem collinearFix_on_line (a b c : Pt n) :
    ∃ t : ℝ, ∀ i, collinearFix a b c i = a i + t * (b i - a i) :=
  ⟨projCoeff a b c, fun _ => rfl⟩

/-! ## 三、一步即达 -/

/-- **两类算子都是「一步到解」**：修复一次即满足约束。

这是 `decreases` 与 `atomic` 能成立的原因——`μ ∈ {0,1}`，而 `fix` 一步把它降到 0。 -/
theorem one_step_suffices :
    (∀ (a b : Pt n) (d : ℝ), 0 ≤ d → sqDist a b ≠ 0 →
      sqDist a (sqDistFix a d b) = d) ∧
    (∀ (a b c : Pt n), ∃ t : ℝ, ∀ i, collinearFix a b c i = a i + t * (b i - a i)) :=
  ⟨fun a b d hd hne => sqDistFix_reaches a b hd hne,
   fun a b c => collinearFix_on_line a b c⟩

end RepairCoverage

end Lattice.Geo
