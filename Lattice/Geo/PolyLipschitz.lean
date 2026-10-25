/-
# `perpendicular` 与 `poly` 的 Lipschitz 界

## 0. 本节做什么

- `Geo/Lipschitz`：`GeoExpr` 五个构造子的 Lipschitz 常数。
- `Geo/DistLipschitz`：`sqDist` 的常数（`8·n·B`）。

本节补上 `EqConstraint.poly` 的最后一个分支 `perpendicular`，它是双线性求和
`Σᵢ (pts b i - pts a i)(pts e i - pts c i)`。至此 `poly` 四个分支所需的工具全部就位。

## 1. `perpendicular` 的证明思路

`Σᵢ uᵢ·wᵢ`，其中 `uᵢ = pts b i - pts a i`、`wᵢ = pts e i - pts c i`。逐项插项：

```
uᵢ·wᵢ - uᵢ'·wᵢ' = uᵢ·(wᵢ - wᵢ') + (uᵢ - uᵢ')·wᵢ'
```

第一项需要 `|uᵢ| ≤ 2B`，第二项需要 `|wᵢ'| ≤ 2B`；两个差项各 `≤ 2ρ`。
所以每项 `≤ 2B·2ρ + 2ρ·2B = 8Bρ`，`n` 项求和 `≤ 8nBρ`。

**常数与 `sqDist` 相同（`8nB`）**，因为两者都是「两个坐标差之积的求和」：
`sqDist` 是 `uᵢ·uᵢ`，`perpendicular` 是 `uᵢ·wᵢ`，结构一致。这不是巧合，
而是同一类双线性型的同一估计。

## 2. 边界

- `B` 是**必要前提**：双线性项涉及点的绝对位置，没有 `B` 它无界。
- 常数保守：没有利用 `Σ uᵢwᵢ` 可能的抵消（正交时和为零，但逐项估计看不到这一点）。
- 本节只给 `perpendicular`；把四个分支组装成 `poly` 的单一定理留给下一层，
  因为它们的前件（`expr` 分支需要表达式的 `K`）形式不同。
-/
import Mathlib
import Lattice.Geo.Lipschitz
import Lattice.Geo.DistLipschitz
import Lattice.Geo.Loss

open scoped BigOperators

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

/-! ## 一、双线性求和 -/

/-- **双线性求和 `Σᵢ uᵢ·wᵢ` 在 `rho` 下 Lipschitz，常数 `8·n·B`。**

`uᵢ = pts b i - pts a i`、`wᵢ = pts e i - pts c i`，四个点索引都在前缀 `k` 内。
`hB` 与两个坐标界前提不可省——见文件头 §2。 -/
theorem bilinearSum_lipschitz {n k : ℕ} {pts pts' : ℕ → Pt n} {a b c e : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hc : c < k) (he : e < k) (hB : 0 ≤ B)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |(∑ i : Fin n, (pts b i - pts a i) * (pts e i - pts c i))
        - (∑ i : Fin n, (pts' b i - pts' a i) * (pts' e i - pts' c i))|
      ≤ (8 * n * B) * rho n k pts pts' := by
  have hρ := rho_nonneg n k pts pts'
  have hU : ∀ i : Fin n, |pts b i - pts a i| ≤ 2 * B := by
    intro i
    have hx := hpts b i
    have hy := hpts a i
    calc |pts b i - pts a i| ≤ |pts b i| + |pts a i| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hW' : ∀ i : Fin n, |pts' e i - pts' c i| ≤ 2 * B := by
    intro i
    have hx := hpts' e i
    have hy := hpts' c i
    calc |pts' e i - pts' c i| ≤ |pts' e i| + |pts' c i| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hdU : ∀ i : Fin n,
      |(pts b i - pts a i) - (pts' b i - pts' a i)| ≤ 2 * rho n k pts pts' :=
    fun i => coordDiff_sub_le (pts := pts) (pts' := pts') (a := b) (b := a) hb ha i
  have hdW : ∀ i : Fin n,
      |(pts e i - pts c i) - (pts' e i - pts' c i)| ≤ 2 * rho n k pts pts' :=
    fun i => coordDiff_sub_le (pts := pts) (pts' := pts') (a := e) (b := c) he hc i
  have hterm : ∀ i : Fin n,
      |(pts b i - pts a i) * (pts e i - pts c i)
          - (pts' b i - pts' a i) * (pts' e i - pts' c i)|
        ≤ (8 * B) * rho n k pts pts' := by
    intro i
    have hfac : (pts b i - pts a i) * (pts e i - pts c i)
          - (pts' b i - pts' a i) * (pts' e i - pts' c i)
        = (pts b i - pts a i) * ((pts e i - pts c i) - (pts' e i - pts' c i))
          + ((pts b i - pts a i) - (pts' b i - pts' a i)) * (pts' e i - pts' c i) := by ring
    rw [hfac]
    calc |(pts b i - pts a i) * ((pts e i - pts c i) - (pts' e i - pts' c i))
            + ((pts b i - pts a i) - (pts' b i - pts' a i)) * (pts' e i - pts' c i)|
        ≤ |(pts b i - pts a i) * ((pts e i - pts c i) - (pts' e i - pts' c i))|
            + |((pts b i - pts a i) - (pts' b i - pts' a i)) * (pts' e i - pts' c i)| :=
          abs_add _ _
      _ = |pts b i - pts a i| * |(pts e i - pts c i) - (pts' e i - pts' c i)|
            + |(pts b i - pts a i) - (pts' b i - pts' a i)| * |pts' e i - pts' c i| := by
          rw [abs_mul, abs_mul]
      _ ≤ (2 * B) * (2 * rho n k pts pts') + (2 * rho n k pts pts') * (2 * B) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (hU i) (hdW i) (abs_nonneg _) (by linarith)
          · exact mul_le_mul (hdU i) (hW' i) (abs_nonneg _) (by linarith [hρ])
      _ = (8 * B) * rho n k pts pts' := by ring
  have hsumeq : (∑ i : Fin n, (pts b i - pts a i) * (pts e i - pts c i))
        - (∑ i : Fin n, (pts' b i - pts' a i) * (pts' e i - pts' c i))
      = ∑ i : Fin n, ((pts b i - pts a i) * (pts e i - pts c i)
          - (pts' b i - pts' a i) * (pts' e i - pts' c i)) := by
    rw [Finset.sum_sub_distrib]
  rw [hsumeq]
  calc |∑ i : Fin n, ((pts b i - pts a i) * (pts e i - pts c i)
          - (pts' b i - pts' a i) * (pts' e i - pts' c i))|
      ≤ ∑ i : Fin n, |(pts b i - pts a i) * (pts e i - pts c i)
          - (pts' b i - pts' a i) * (pts' e i - pts' c i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (8 * B) * rho n k pts pts' := Finset.sum_le_sum (fun i _ => hterm i)
    _ = n * ((8 * B) * rho n k pts pts') := by simp
    _ = (8 * n * B) * rho n k pts pts' := by ring

end Lattice.Geo
