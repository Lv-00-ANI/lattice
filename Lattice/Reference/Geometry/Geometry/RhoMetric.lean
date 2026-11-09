/-
# `rho` 的度量性质

## 0. 本节做什么

`VerificationSoundness` 需要 `PseudoMetricSpace`。`rho n k` 已经做这件事
（两条点列在前 `k` 个点上的最大坐标偏差），本节证明它满足三条度量公理。

## 1. 证明策略：只展开 `if` 一次

`rho` 写成 `if h : Nonempty then sup' ... else 0`，因为 `Finset.sup'` 要求非空见证。
直接对 `rho` 展开会陷入 `if` 分支与 `Nonempty` 见证的嵌套；前两次尝试都是这样失败的。
第三次尝试一度留下了未完成的占位，已整体删除——本项目不允许证明里存在未闭合的步骤，
因此改走「先证泛性质」的路线。

正确做法：**先证一条泛性质**，之后三条公理都不再碰 `if`：

```
rho_le_iff :  0 ≤ L  →  (rho n k a b ≤ L  ↔  ∀ pi ∈ ptIndex n k, |a pi.1 pi.2 - b pi.1 pi.2| ≤ L)
```

由它立刻得到：

| 公理 | 推导 |
|:--|:--|
| `rho x x = 0` | 每项 `= 0 ≤ 0`，且 `rho ≥ 0` |
| `rho x y = rho y x` | 两侧都等价于「每项 ≤ L」，而每项由 `abs_sub_comm` 相等 |
| `rho x z ≤ rho x y + rho y z` | 每项 `\|a-c\| ≤ \|a-b\| + \|b-c\| ≤ rho ab + rho bc` |

## 2. 空索引集

`ptIndex n k` 为空时（`k = 0` 或 `n = 0`）`rho ≡ 0`。
此时 `rho_le_iff` 的右侧是**空洞真**，所以等价式只在 `L ≥ 0` 时成立。
因此 `rho_le_iff` 带前提 `0 ≤ L`——这不是弱化，而是空集情形的正确形式。
-/
import Mathlib
import Lattice.Reference.Geometry.Constraints.Lipschitz

namespace Lattice.Geo

/-! ## 一、`rho` 的泛性质 -/

/-- **`rho` 刻画为最小上界（非负情形）。**

`rho n k a b ≤ L` 当且仅当每个分量 `≤ L`，前提 `0 ≤ L`（空索引集时需要）。 -/
theorem rho_le_iff {n k : ℕ} (a b : ℕ → Pt n) {L : ℝ} (hL : 0 ≤ L) :
    rho n k a b ≤ L ↔ ∀ pi ∈ ptIndex n k, |a pi.1 pi.2 - b pi.1 pi.2| ≤ L := by
  constructor
  · intro h pi hpi
    have hne : (ptIndex n k).Nonempty := ⟨pi, hpi⟩
    have hrho : rho n k a b
        = (ptIndex n k).sup' (f := fun pi => |a pi.1 pi.2 - b pi.1 pi.2|) hne := by
      unfold rho
      rw [dif_pos hne]
    have key : |a pi.1 pi.2 - b pi.1 pi.2|
        ≤ (ptIndex n k).sup' (f := fun pi => |a pi.1 pi.2 - b pi.1 pi.2|) hne :=
      Finset.le_sup' (f := fun pi => |a pi.1 pi.2 - b pi.1 pi.2|) hpi
    rw [hrho] at h
    exact le_trans key h
  · intro h
    unfold rho
    by_cases hne : (ptIndex n k).Nonempty
    · rw [dif_pos hne]
      exact Finset.sup'_le hne _ h
    · rw [dif_neg hne]
      exact hL

/-- 前缀内每个偏差不超过 `rho`（`rho_le_iff` 的单点形式）。 -/
theorem abs_coord_sub_le_rho_singlePoint {n k : ℕ} {a b : ℕ → Pt n} {p : ℕ} {i : Fin n}
    (hp : p < k) :
    |a p i - b p i| ≤ rho n k a b := by
  have hmem : (p, i) ∈ ptIndex n k :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hp, Finset.mem_univ _⟩
  exact (rho_le_iff a b (rho_nonneg n k a b)).mp
    (le_rfl : rho n k a b ≤ rho n k a b) (p, i) hmem

/-! ## 二、三条度量公理 -/

/-- **自反性**：同一序列偏差为零。 -/
theorem rho_self {n k : ℕ} (a : ℕ → Pt n) : rho n k a a = 0 := by
  refine le_antisymm ?_ (rho_nonneg n k a a)
  refine (rho_le_iff a a (le_refl (0 : ℝ))).mpr ?_
  intro pi _
  simp

/-- **对称性**：`rho a b = rho b a`。

两个方向都用单点界 `abs_coord_sub_le_rho_singlePoint`，配合 `abs_sub_comm`。 -/
theorem rho_comm {n k : ℕ} (a b : ℕ → Pt n) : rho n k a b = rho n k b a := by
  have h2 := rho_nonneg n k b a
  have h1 := rho_nonneg n k a b
  refine le_antisymm ?_ ?_
  · refine (rho_le_iff a b h2).mpr ?_
    intro pi hpi
    have hp : pi.1 < k := (Finset.mem_product.mp hpi).1 |> Finset.mem_range.mp
    calc |a pi.1 pi.2 - b pi.1 pi.2| = |b pi.1 pi.2 - a pi.1 pi.2| := abs_sub_comm _ _
      _ ≤ rho n k b a := abs_coord_sub_le_rho_singlePoint (a := b) (b := a) (i := pi.2) hp
  · refine (rho_le_iff b a h1).mpr ?_
    intro pi hpi
    have hp : pi.1 < k := (Finset.mem_product.mp hpi).1 |> Finset.mem_range.mp
    calc |b pi.1 pi.2 - a pi.1 pi.2| = |a pi.1 pi.2 - b pi.1 pi.2| := abs_sub_comm _ _
      _ ≤ rho n k a b := abs_coord_sub_le_rho_singlePoint (a := a) (b := b) (i := pi.2) hp

/-- **三角不等式**：`rho a c ≤ rho a b + rho b c`。 -/
theorem rho_triangle {n k : ℕ} (a b c : ℕ → Pt n) :
    rho n k a c ≤ rho n k a b + rho n k b c := by
  have hab := rho_nonneg n k a b
  have hbc := rho_nonneg n k b c
  refine (rho_le_iff a c (by linarith)).mpr ?_
  intro pi hpi
  have e1 : |a pi.1 pi.2 - b pi.1 pi.2| ≤ rho n k a b :=
    (rho_le_iff a b hab).mp (le_rfl : rho n k a b ≤ rho n k a b) pi hpi
  have e2 : |b pi.1 pi.2 - c pi.1 pi.2| ≤ rho n k b c :=
    (rho_le_iff b c hbc).mp (le_rfl : rho n k b c ≤ rho n k b c) pi hpi
  have e3 : |a pi.1 pi.2 - c pi.1 pi.2|
      ≤ |a pi.1 pi.2 - b pi.1 pi.2| + |b pi.1 pi.2 - c pi.1 pi.2| := abs_sub_le _ _ _
  linarith

end Lattice.Geo
