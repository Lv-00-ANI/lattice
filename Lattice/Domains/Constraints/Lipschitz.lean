/-
# 几何表达式的 Lipschitz 界

## 0. 本节补上什么

`Lattice.Lift.VerificationSoundness` 的结论是

```
在 δ-稠密采样集上验证通过  ⟹  全域残差 ≤ ε₀ + L·δ
```

其中 `L` 是残差的 Lipschitz 常数。`Geo/ApproxEmbedding` 把几何约束接进了这条链，
但当时明确写着：**没有给出 `L`**。本文件补这一环。

## 1. 度量：点集在有限前缀上的偏差

`pts : ℕ → Pt n` 是点序列。两点列的距离取**前 `k` 个点的最大坐标偏差**：

```
rho n k pts pts' = max { |pts p i - pts' p i| : p < k, i < n }
```

取**有限最大值**而非上确界：索引集是 `Finset.range k × univ`，
`Finset.sup'` 直接给出，无需论证上确界存在。

`k = 0` 或 `n = 0` 时索引集为空，而 `Finset.sup'` 要求非空见证；`rho` 用 `if`
把空集情形显式定为 `0`。这不是回避：它把「没有点就没有偏差」写进定义。

## 2. 表达式：同时携带 Lipschitz 常数与值域界

`GeoExpr` 有五个构造子。**乘法不是 1-Lipschitz 的**：

```
|f·g - f'·g'| ≤ |f|·|g - g'| + |f - f'|·|g'|
```

第一项需要 `|f|` 的界，第二项需要 `|g'|` 的界。所以归纳必须同时给出
**常数 `K`** 与**值域界 `B`**；只带 `K` 的归纳在 `mul` 分支无法闭合。
这是结构性的，不是风格选择——本文件因此把两个谓词分开定义，
而不是合成一个结构体，因为多数构造子只需要其中一个。

| 构造子 | `K` | `B` |
|:--|:--|:--|
| `coord p axis` | `1` | 外部给定 |
| `const c` | `0` | `|c|` |
| `add e₁ e₂` | `K₁ + K₂` | `B₁ + B₂` |
| `sub e₁ e₂` | `K₁ + K₂` | `B₁ + B₂` |
| `mul e₁ e₂` | `K₁·B₂ + K₂·B₁` | `B₁·B₂` |

## 3. 边界

- 常数是**上界**，不是最优。`add` 用 `K₁+K₂` 而非 `max`；乘法用保守交叉项。
  更紧的界需要分析表达式的实际次数结构，属后续工作。
- `rho` 只约束**前 `k` 个点**。表达式引用第 `p ≥ k` 个坐标时 `rho` 对它无约束，
  故 `coord` 分支带前提 `p < k`。这个前提不可省：省掉后命题为假。
- `coord` 的值域界由**外部给定**，不从 `rho` 推出：`rho` 约束两条点列之间的距离，
  不约束绝对位置。
-/
import Mathlib
import Lattice.Domains.Constraints.Expr

open scoped BigOperators

namespace Lattice.Geo

/-! ## 一、点集的有限前缀偏差 -/

/-- 索引集：`range k × univ`（点号 × 坐标）。 -/
def ptIndex (n k : ℕ) : Finset (ℕ × Fin n) :=
  Finset.range k ×ˢ (Finset.univ : Finset (Fin n))

/-- **点列在前缀上的偏差。**

`k = 0` 或 `n = 0` 时索引集为空，取值 `0`。 -/
noncomputable def rho (n k : ℕ) (pts pts' : ℕ → Pt n) : ℝ :=
  if h : (ptIndex n k).Nonempty
  then (ptIndex n k).sup' (f := fun pi => |pts pi.1 pi.2 - pts' pi.1 pi.2|) h
  else 0

theorem rho_nonneg (n k : ℕ) (pts pts' : ℕ → Pt n) : 0 ≤ rho n k pts pts' := by
  unfold rho
  split
  · next h =>
    obtain ⟨x, _hx, hfx⟩ := Finset.exists_mem_eq_sup' h
      (fun pi : ℕ × Fin n => |pts pi.1 pi.2 - pts' pi.1 pi.2|)
    rw [hfx]
    exact abs_nonneg _
  · exact le_rfl

/-- 前缀内的单个坐标差不超过 `rho`。 -/
theorem abs_coord_sub_le_rho {n k : ℕ} {pts pts' : ℕ → Pt n} {p : ℕ} {i : Fin n}
    (hp : p < k) :
    |pts p i - pts' p i| ≤ rho n k pts pts' := by
  have hmem : (p, i) ∈ ptIndex n k :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hp, Finset.mem_univ _⟩
  have hne : (ptIndex n k).Nonempty := ⟨(p, i), hmem⟩
  unfold rho
  rw [dif_pos hne]
  exact Finset.le_sup' (f := fun pi => |pts pi.1 pi.2 - pts' pi.1 pi.2|) hmem

/-! ## 二、两个谓词 -/

/-- **`LipschitzK e K`**：`e` 在偏差 `rho` 下以 `K` 为 Lipschitz 常数。 -/
def LipschitzK (n k : ℕ) (e : GeoExpr n) (K : ℝ) : Prop :=
  ∀ pts pts' : ℕ → Pt n,
    |GeoExpr.evalPts e pts - GeoExpr.evalPts e pts'| ≤ K * rho n k pts pts'

/-- **`BoundedV e B`**：`e` 的取值被 `B` 界住。 -/
def BoundedV (n : ℕ) (e : GeoExpr n) (B : ℝ) : Prop :=
  ∀ pts : ℕ → Pt n, |GeoExpr.evalPts e pts| ≤ B

/-! ## 三、构造子逐条 -/

/-- **`coord p axis`** 是 `1`-Lipschitz（在前缀内）。 -/
theorem lipschitz_coord (n k : ℕ) (p : ℕ) (axis : Fin n) (hp : p < k) :
    LipschitzK n k (.coord p axis) 1 := by
  intro pts pts'
  have h := abs_coord_sub_le_rho (n := n) (k := k) (pts := pts) (pts' := pts') (p := p)
    (i := axis) hp
  simpa [LipschitzK, GeoExpr.evalPts] using h

/-- **`const c`** 是 `0`-Lipschitz。 -/
theorem lipschitz_const (n k : ℕ) (c : ℝ) : LipschitzK n k (.const c) 0 := by
  intro pts pts'
  simp [LipschitzK, GeoExpr.evalPts]

/-- **`const c`** 的值域界是 `|c|`。 -/
theorem boundedV_const (n : ℕ) (c : ℝ) : BoundedV n (.const c) |c| := by
  intro pts
  simp [BoundedV, GeoExpr.evalPts]

/-- **`add`**：常数 `K₁ + K₂`。 -/
theorem lipschitz_add {n k : ℕ} {e₁ e₂ : GeoExpr n} {K₁ K₂ : ℝ}
    (h₁ : LipschitzK n k e₁ K₁) (h₂ : LipschitzK n k e₂ K₂) :
    LipschitzK n k (.add e₁ e₂) (K₁ + K₂) := by
  intro pts pts'
  have h1 := h₁ pts pts'
  have h2 := h₂ pts pts'
  have heq : GeoExpr.evalPts (.add e₁ e₂) pts - GeoExpr.evalPts (.add e₁ e₂) pts'
      = (GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts')
        + (GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts') := by
    simp [GeoExpr.evalPts]; ring
  rw [heq]
  calc |(GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts')
          + (GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts')|
      ≤ |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts'|
          + |GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts'| := abs_add _ _
    _ ≤ K₁ * rho n k pts pts' + K₂ * rho n k pts pts' := by linarith
    _ = (K₁ + K₂) * rho n k pts pts' := by ring

/-- **`add`** 的值域界：`B₁ + B₂`。 -/
theorem boundedV_add {n : ℕ} {e₁ e₂ : GeoExpr n} {B₁ B₂ : ℝ}
    (h₁ : BoundedV n e₁ B₁) (h₂ : BoundedV n e₂ B₂) :
    BoundedV n (.add e₁ e₂) (B₁ + B₂) := by
  intro pts
  have h1 := h₁ pts
  have h2 := h₂ pts
  have heq : |GeoExpr.evalPts (.add e₁ e₂) pts|
      = |GeoExpr.evalPts e₁ pts + GeoExpr.evalPts e₂ pts| := by rfl
  rw [heq]
  calc |GeoExpr.evalPts e₁ pts + GeoExpr.evalPts e₂ pts|
      ≤ |GeoExpr.evalPts e₁ pts| + |GeoExpr.evalPts e₂ pts| := abs_add _ _
    _ ≤ B₁ + B₂ := by linarith

/-- **`sub`**：常数 `K₁ + K₂`。 -/
theorem lipschitz_sub {n k : ℕ} {e₁ e₂ : GeoExpr n} {K₁ K₂ : ℝ}
    (h₁ : LipschitzK n k e₁ K₁) (h₂ : LipschitzK n k e₂ K₂) :
    LipschitzK n k (.sub e₁ e₂) (K₁ + K₂) := by
  intro pts pts'
  have h1 := h₁ pts pts'
  have h2 := h₂ pts pts'
  have heq : GeoExpr.evalPts (.sub e₁ e₂) pts - GeoExpr.evalPts (.sub e₁ e₂) pts'
      = (GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts')
        - (GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts') := by
    simp [GeoExpr.evalPts]; ring
  rw [heq]
  calc |(GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts')
          - (GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts')|
      ≤ |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts'|
          + |GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts'| := abs_sub _ _
    _ ≤ K₁ * rho n k pts pts' + K₂ * rho n k pts pts' := by linarith
    _ = (K₁ + K₂) * rho n k pts pts' := by ring

/-- **`sub`** 的值域界：`B₁ + B₂`。 -/
theorem boundedV_sub {n : ℕ} {e₁ e₂ : GeoExpr n} {B₁ B₂ : ℝ}
    (h₁ : BoundedV n e₁ B₁) (h₂ : BoundedV n e₂ B₂) :
    BoundedV n (.sub e₁ e₂) (B₁ + B₂) := by
  intro pts
  have h1 := h₁ pts
  have h2 := h₂ pts
  have heq : |GeoExpr.evalPts (.sub e₁ e₂) pts|
      = |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₂ pts| := by rfl
  rw [heq]
  calc |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₂ pts|
      ≤ |GeoExpr.evalPts e₁ pts| + |GeoExpr.evalPts e₂ pts| := abs_sub _ _
    _ ≤ B₁ + B₂ := by linarith

/-- **`mul`**：常数 `K₁·B₂ + K₂·B₁`。

关键插项：`f·g - f'·g' = f·(g - g') + (f - f')·g'`。
第一项用 `|f| ≤ B₁`，第二项用 `|g'| ≤ B₂`。
**这就是归纳必须携带值域界的原因**。 -/
theorem lipschitz_mul {n k : ℕ} {e₁ e₂ : GeoExpr n} {K₁ K₂ B₁ B₂ : ℝ}
    (hl₁ : LipschitzK n k e₁ K₁) (hl₂ : LipschitzK n k e₂ K₂)
    (hb₁ : BoundedV n e₁ B₁) (hb₂ : BoundedV n e₂ B₂)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hK₁ : 0 ≤ K₁) :
    LipschitzK n k (.mul e₁ e₂) (K₁ * B₂ + K₂ * B₁) := by
  intro pts pts'
  have hρ := rho_nonneg n k pts pts'
  have h1 := hl₁ pts pts'
  have h2 := hl₂ pts pts'
  have hv1 := hb₁ pts
  have hv2 := hb₂ pts'
  have heq : GeoExpr.evalPts (.mul e₁ e₂) pts - GeoExpr.evalPts (.mul e₁ e₂) pts'
      = GeoExpr.evalPts e₁ pts * (GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts')
        + (GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts') * GeoExpr.evalPts e₂ pts' := by
    simp [GeoExpr.evalPts]; ring
  rw [heq]
  have htri : |GeoExpr.evalPts e₁ pts * (GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts')
        + (GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts') * GeoExpr.evalPts e₂ pts'|
      ≤ |GeoExpr.evalPts e₁ pts| * |GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts'|
        + |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts'| * |GeoExpr.evalPts e₂ pts'| := by
    calc |GeoExpr.evalPts e₁ pts * (GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts')
            + (GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts') * GeoExpr.evalPts e₂ pts'|
        ≤ |GeoExpr.evalPts e₁ pts * (GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts')|
            + |(GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts') * GeoExpr.evalPts e₂ pts'| :=
          abs_add _ _
      _ = |GeoExpr.evalPts e₁ pts| * |GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts'|
            + |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts'| * |GeoExpr.evalPts e₂ pts'| := by
          rw [abs_mul, abs_mul]
  refine htri.trans ?_
  -- Term 1: |f| <= B1 times the (non-negative) gap |g - g'| <= K2 * rho.
  have hgap : 0 ≤ |GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts'| := abs_nonneg _
  have hterm1 : |GeoExpr.evalPts e₁ pts| * |GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts'|
      ≤ B₁ * (K₂ * rho n k pts pts') :=
    mul_le_mul hv1 h2 hgap hB₁
  -- Term 2: |f - f'| <= K1 * rho times the (non-negative) bound |g'| <= B2.
  have hgap2 : 0 ≤ |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts'| := abs_nonneg _
  have hterm2 : |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts'| * |GeoExpr.evalPts e₂ pts'|
      ≤ (K₁ * rho n k pts pts') * B₂ :=
    mul_le_mul h1 hv2 (abs_nonneg _) (mul_nonneg hK₁ hρ)
  calc |GeoExpr.evalPts e₁ pts| * |GeoExpr.evalPts e₂ pts - GeoExpr.evalPts e₂ pts'|
          + |GeoExpr.evalPts e₁ pts - GeoExpr.evalPts e₁ pts'| * |GeoExpr.evalPts e₂ pts'|
      ≤ B₁ * (K₂ * rho n k pts pts') + (K₁ * rho n k pts pts') * B₂ := add_le_add hterm1 hterm2
    _ = (K₁ * B₂ + K₂ * B₁) * rho n k pts pts' := by ring

/-- **`mul`** 的值域界：`B₁ · B₂`。 -/
theorem boundedV_mul {n : ℕ} {e₁ e₂ : GeoExpr n} {B₁ B₂ : ℝ}
    (h₁ : BoundedV n e₁ B₁) (h₂ : BoundedV n e₂ B₂) :
    BoundedV n (.mul e₁ e₂) (B₁ * B₂) := by
  intro pts
  have h1 := h₁ pts
  have h2 := h₂ pts
  have heq : |GeoExpr.evalPts (.mul e₁ e₂) pts|
      = |GeoExpr.evalPts e₁ pts * GeoExpr.evalPts e₂ pts| := by rfl
  rw [heq, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)

end Lattice.Geo
