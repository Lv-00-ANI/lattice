/-
# 验证机制的第一个实例：网格是 δ-稠密的

## 0. 本节补什么

`Lift/RealVerifierReliable.lean` 定义了

```
DeltaDense (S : Set ℝ) (δ : ℝ) (Ω : Set ℝ) : Prop :=
  ∀ x ∈ Ω, ∃ s ∈ Ω, s ∈ S ∧ |x - s| ≤ δ
```

并给了**条件式**的可靠性定理（`hd : DeltaDense S δ Ω` ⟹ 结论）。
`Geo/GeoSampledBound.lean` 的 `geo_sampled_bound` 同样以稠密性为前提。

**但全库没有一处证明过任何具体集合是 `DeltaDense`。**

⇒ **验证机制虽然形式完整，但从未被实例化。** 这与第 102 轮发现的
「数据合成的覆盖率没有推广到多种子」是同一类缺口：**定理存在，但前提从未被满足过。**

## 1. 证明思路

最自然的稠密集合是**等距网格**：

```
grid h := { k * h | k : ℤ }
```

**要证**：`grid h` 在 `ℝ` 上 `h`-稠密（`h > 0`）。

证明：任给 `x`，取 `k := ⌊x / h⌋`，则 `0 ≤ x - k*h < h`，故 `|x - k*h| < h ≤ h`。∎

### 1.1 为什么这条重要

它把 `DeltaDense` 从一个**假设**变成**可以构造的事实**。
于是 `geo_sampled_bound` 与 `verifier_reliable_clean` **第一次可以被真正使用**。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `grid` | 步长 `h` 的整数网格 |
| `grid_mem_iff` | 成员判定 |
| **`grid_delta_dense`** | **`h > 0` 时 `grid h` 在 `ℝ` 上 `h`-稠密** |
| `grid_dense_le` | 容差可放宽 |
| **`exists_delta_dense_set`** | **存在 `DeltaDense` 的非空见证** |

## 3. 边界

- **在 `ℝ`（一维）上做**，与 `DeltaDense` 的定义域一致。
- **`h > 0` 是必要前提**：`h = 0` 时网格退化为 `{0}`，不稠密。
- 本节**不**把网格接到 `geo_sampled_bound` 的 `Lipschitz` 前提上——
  那需要具体约束的 Lipschitz 常数，属另一件事。**本节只补稠密性这一环。**
- 本节**不**处理多维。`DeltaDense` 只定义在一维，多维需要新的定义。
-/
import Mathlib
import Lattice.Lift.RealVerifierReliable

namespace Lattice.Lift

namespace GridDensity

/-! ## 一、网格 -/

/-- **步长 `h` 的整数网格**。 -/
def grid (h : ℝ) : Set ℝ := {x | ∃ k : ℤ, x = k * h}

/-- **成员判定**：`x` 在网格上，当且仅当它是 `h` 的整数倍。 -/
theorem grid_mem_iff (h x : ℝ) : x ∈ grid h ↔ ∃ k : ℤ, x = k * h :=
  Iff.rfl

/-- **每个整数倍都在网格上**。 -/
theorem grid_mem_mul (h : ℝ) (k : ℤ) : (k : ℝ) * h ∈ grid h :=
  ⟨k, rfl⟩

/-! ## 二、网格是稠密的 -/

/-- **网格 `h` 在 `ℝ` 上 `h`-稠密**（`h > 0`）。

证明：任取 `x`，令 `k := ⌊x / h⌋`，则 `k * h ≤ x < (k+1) * h`，
所以 `0 ≤ x - k * h < h`，于是 `|x - k * h| ≤ h`。

**这是 `DeltaDense` 的第一个具体见证**——此前全库只有定义与条件式定理。 -/
theorem grid_delta_dense (h : ℝ) (hh : 0 < h) :
    DeltaDense (grid h) h Set.univ := by
  intro x _
  refine ⟨(⌊x / h⌋ : ℤ) * h, ?_, grid_mem_mul h ⌊x / h⌋, ?_⟩
  · trivial
  · -- |x - floor(x/h)*h| <= h
    have hpos : 0 < h := hh
    set k : ℤ := ⌊x / h⌋ with hk
    have h1 : (k : ℝ) ≤ x / h := Int.floor_le _
    have h2 : x / h < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have hk1 : (k : ℝ) * h ≤ x := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
    have hk2 : x < ((k : ℝ) + 1) * h := by
      have := mul_lt_mul_of_pos_right h2 hpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
    have : x - (k : ℝ) * h < h := by
      have : ((k : ℝ) + 1) * h = (k : ℝ) * h + h := by ring
      linarith
    have hnn : 0 ≤ x - (k : ℝ) * h := by linarith
    rw [abs_of_nonneg hnn]
    linarith

/-- **容差可放宽**：`h`-稠密推出 `h'`-稠密（`h ≤ h'`）。 -/
theorem grid_dense_le (h h' : ℝ) (hh : 0 < h) (hle : h ≤ h') :
    DeltaDense (grid h) h' Set.univ := by
  intro x hx
  obtain ⟨s, hs, hmem, hd⟩ := grid_delta_dense h hh x hx
  exact ⟨s, hs, hmem, le_trans hd hle⟩

/-! ## 三、存在性 -/

/-- **存在 `DeltaDense` 的非空见证**：单位网格在 `ℝ` 上 `1`-稠密。

⇒ **`DeltaDense` 不再是一个从未被满足的前提。** -/
theorem exists_delta_dense_set :
    ∃ (S : Set ℝ) (δ : ℝ), 0 < δ ∧ DeltaDense S δ Set.univ :=
  ⟨grid 1, 1, by norm_num, grid_delta_dense 1 (by norm_num)⟩

/-- **具体形式**：整数网格 `ℤ` 在 `ℝ` 上 `1`-稠密。

（`grid 1` 就是整数集合。） -/
theorem int_grid_delta_dense : DeltaDense (grid 1) 1 Set.univ :=
  grid_delta_dense 1 (by norm_num)

end GridDensity

end Lattice.Lift
