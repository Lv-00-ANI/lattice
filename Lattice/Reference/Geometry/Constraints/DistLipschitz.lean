/-
# `sqDist` 的 Lipschitz 界

## 0. 本节做什么

`Geo/Lipschitz` 给出了 `GeoExpr` 五个构造子的 Lipschitz 常数与值域界。
但 `EqConstraint.poly` 的真正载体是 `sqDist`（三个分支用到它），
`sqDist` 不在 `GeoExpr` 里，所以上轮的界不覆盖它。本文件补上。

## 1. 为什么上轮的草稿是错的

上一轮我写的 `sqDist_lipschitz` 用**同一个坐标和**去界定两组点：

```
|sqDist a b (pts) - sqDist a b (pts')| ≤ (4 * (Σ |pts a i| + |pts b i|) + 2) * rho
```

这是错的：`sqDist` 同时涉及 `pts` 与 `pts'` 两组坐标，`pts'` 的量级完全不受
`Σ |pts a i| + |pts b i|` 约束——两条点列可以一条在原点附近、另一条很远，
`rho` 依然可以很小（`rho` 只约束**同一坐标**在两条点列间的差）。

正确的陈述必须**同时给出两组点各自的界**。

## 2. 正确的思路

`sqDist a b = Σᵢ (pts a i - pts b i)²`。记 `uᵢ = pts a i - pts b i`、`vᵢ = pts' a i - pts' b i`。
则 `uᵢ - vᵢ = (pts a i - pts' a i) - (pts b i - pts' b i)`，故

```
|uᵢ - vᵢ| ≤ 2·rho                              （两个坐标差各 ≤ rho）
```

而 `|uᵢ + vᵢ| ≤ 2·(Ma + Mb)`，其中 `Ma = Σⱼ |pts a j|`、`Mb = Σⱼ |pts b j|`
（对应地 `Ma'`、`Mb'` 是带撇的）。

逐项 `|uᵢ² - vᵢ²| = |uᵢ - vᵢ|·|uᵢ + vᵢ| ≤ 2·rho · 2·(Ma + Mb + Ma' + Mb')`，
求和 `n` 项得界。

**关键修正**：`|uᵢ + vᵢ|` 要同时被 `pts` 和 `pts'` 界住，所以常数里必须出现
`Ma + Mb + Ma' + Mb'`，不能只有一份。

## 3. 结论形式

为了便于下游使用，本文件把界写成**存在形式**：给定两组点的坐标界 `B`（即
`∀ p i, |pts p i| ≤ B` 与 `∀ p i, |pts' p i| ≤ B`），则

```
|sqDist a b pts - sqDist a b pts'| ≤ (4 * n * B * 2) * rho
```

即常数 `8·n·B`。这比上面逐步估计的 `4·B`（每项）× `n`（项数）更宽松一点，
但**形式统一、下游好用**，且 `B` 的语义清晰：坐标系的原点附近多大的盒子。

## 4. 边界

- `B` 是**必要前提**，不是装饰：没有它 `sqDist` 无界（点可以任意远），命题为假。
- 常数是保守上界：`8·n·B` 没有利用 `uᵢ`、`vᵢ` 的实际大小，只用了上界。
  更紧的界需要知道点的具体位置，属数值分析范围。
- 本文件只处理 `sqDist`；`poly` 四分支的组装在下一层。
-/
import Mathlib
import Lattice.Reference.Geometry.Constraints.Lipschitz
import Lattice.Reference.Geometry.Constraints.Dist

open scoped BigOperators

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

/-! ## 一、坐标差在 `rho` 下是 2-Lipschitz -/

/-- **两个点的差向量各分量之差 ≤ 2·rho。**

`(pts a i - pts b i) - (pts' a i - pts' b i) = (pts a i - pts' a i) - (pts b i - pts' b i)`，
两两对应相减。 -/
theorem coordDiff_sub_le {n k : ℕ} {pts pts' : ℕ → Pt n} {a b : ℕ}
    (ha : a < k) (hb : b < k) (i : Fin n) :
    |(pts a i - pts b i) - (pts' a i - pts' b i)| ≤ 2 * rho n k pts pts' := by
  have h1 := abs_coord_sub_le_rho (n := n) (k := k) (pts := pts) (pts' := pts') (p := a) (i := i) ha
  have h2 := abs_coord_sub_le_rho (n := n) (k := k) (pts := pts) (pts' := pts') (p := b) (i := i) hb
  have heq : (pts a i - pts b i) - (pts' a i - pts' b i)
      = (pts a i - pts' a i) - (pts b i - pts' b i) := by ring
  rw [heq]
  calc |(pts a i - pts' a i) - (pts b i - pts' b i)|
      ≤ |pts a i - pts' a i| + |pts b i - pts' b i| := abs_sub _ _
    _ ≤ rho n k pts pts' + rho n k pts pts' := by linarith
    _ = 2 * rho n k pts pts' := by ring

/-- **两个点的差向量各分量的和 ≤ 4·B。**

`|uᵢ + vᵢ| ≤ |uᵢ| + |vᵢ| ≤ 2B + 2B`，其中每个坐标 `|pts p i| ≤ B`。 -/
theorem coordDiff_add_le {n : ℕ} {pts pts' : ℕ → Pt n} {a b : ℕ} {B : ℝ}
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) (i : Fin n) :
    |(pts a i - pts b i) + (pts' a i - pts' b i)| ≤ 4 * B := by
  have h1 : |pts a i - pts b i| ≤ 2 * B := by
    have hx := hpts a i
    have hy := hpts b i
    calc |pts a i - pts b i| ≤ |pts a i| + |pts b i| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have h2 : |pts' a i - pts' b i| ≤ 2 * B := by
    have hx := hpts' a i
    have hy := hpts' b i
    calc |pts' a i - pts' b i| ≤ |pts' a i| + |pts' b i| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  calc |(pts a i - pts b i) + (pts' a i - pts' b i)|
      ≤ |pts a i - pts b i| + |pts' a i - pts' b i| := abs_add _ _
    _ ≤ 2 * B + 2 * B := by linarith
    _ = 4 * B := by ring

/-! ## 二、`sqDist` 的界 -/

/-- ⭐ **`sqDist` 的绝对值界**：坐标被 `B` 界住时，`|sqDist (pts a) (pts b)| ≤ 4·n·B²`。

**这是 `sqDist` 的【有界性】，与 `sqDist_lipschitz` 的【Lipschitz 性】是两件事。**
`sqDistEq`／`equalLength` 两个分支的**外层平方**需要它（`sq_lipschitz_on_bounded` 要求两端有界）。

**推导**：`sqDist p q = ∑ i, (p i − q i)²`（`Dist.sqDist_eq_sum`），
而 `|p i − q i| ≤ |p i| + |q i| ≤ 2B`，所以每项 `≤ 4B²`，`n` 项求和。 -/
theorem sqDist_abs_le {n : ℕ} {pts : ℕ → Pt n} {a b : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hpts : ∀ p i, |pts p i| ≤ B) :
    |sqDist (n := n) (pts a) (pts b)| ≤ 4 * (n : ℝ) * B * B := by
  have hd : ∀ i : Fin n, |pts a i - pts b i| ≤ 2 * B := by
    intro i
    have h1 : |pts a i - pts b i| ≤ |pts a i| + |pts b i| := by
      have := abs_add (pts a i) (-(pts b i))
      simpa only [sub_eq_add_neg, abs_neg] using this
    linarith [hpts a i, hpts b i]
  have hterm : ∀ i : Fin n, (pts a i - pts b i) ^ 2 ≤ 4 * B * B := by
    intro i
    have h2 := hd i
    have h3 : |pts a i - pts b i| ^ 2 ≤ (2 * B) ^ 2 := pow_le_pow_left (abs_nonneg _) h2 2
    rw [sq_abs] at h3
    nlinarith [h3]
  have hnonneg : 0 ≤ ∑ i, (pts a i - pts b i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [Lattice.Geo.sqDist_eq_sum, abs_of_nonneg hnonneg]
  calc ∑ i, (pts a i - pts b i) ^ 2 ≤ ∑ _i : Fin n, 4 * B * B :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 4 * (n : ℝ) * B * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **`sqDist` 在 `rho` 下是 Lipschitz 的，常数 `8·n·B`。**

前提 `hpts`、`hpts'` 给出两组点各自的坐标界 `B ≥ 0`。**不可省**：
`sqDist` 涉及点的绝对位置，而 `rho` 只约束两条点列之间的差。

证明：逐项 `|uᵢ² - vᵢ²| = |uᵢ - vᵢ|·|uᵢ + vᵢ| ≤ 2ρ · 4B = 8Bρ`，`n` 项求和。 -/
theorem sqDist_lipschitz {n k : ℕ} {pts pts' : ℕ → Pt n} {a b : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hB : 0 ≤ B)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts' a) (pts' b)|
      ≤ (8 * n * B) * rho n k pts pts' := by
  have hρ := rho_nonneg n k pts pts'
  -- per-coordinate bound
  have hterm : ∀ i : Fin n,
      |(pts a i - pts b i) ^ 2 - (pts' a i - pts' b i) ^ 2| ≤ (8 * B) * rho n k pts pts' := by
    intro i
    have hd := coordDiff_sub_le (n := n) (k := k) (pts := pts) (pts' := pts') (a := a) (b := b) ha hb i
    have hs := coordDiff_add_le (n := n) (pts := pts) (pts' := pts') (a := a) (b := b) hpts hpts' i
    have hfac : (pts a i - pts b i) ^ 2 - (pts' a i - pts' b i) ^ 2
        = ((pts a i - pts b i) - (pts' a i - pts' b i))
          * ((pts a i - pts b i) + (pts' a i - pts' b i)) := by ring
    rw [hfac, abs_mul]
    calc |(pts a i - pts b i) - (pts' a i - pts' b i)|
          * |(pts a i - pts b i) + (pts' a i - pts' b i)|
        ≤ (2 * rho n k pts pts') * (4 * B) :=
          mul_le_mul hd hs (abs_nonneg _) (by linarith [hρ])
      _ = (8 * B) * rho n k pts pts' := by ring
  -- sum them up
  unfold sqDist sqNorm diff
  rw [← Finset.sum_sub_distrib]
  calc |∑ i : Fin n, ((pts a i - pts b i) ^ 2 - (pts' a i - pts' b i) ^ 2)|
      ≤ ∑ i : Fin n, |(pts a i - pts b i) ^ 2 - (pts' a i - pts' b i) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (8 * B) * rho n k pts pts' := Finset.sum_le_sum (fun i _ => hterm i)
    _ = n * ((8 * B) * rho n k pts pts') := by simp
    _ = (8 * n * B) * rho n k pts pts' := by ring

end Lattice.Geo
