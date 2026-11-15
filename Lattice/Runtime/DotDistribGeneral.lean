import Mathlib
import Lattice.Runtime.ZipAssoc

/-!
# 一般分配律：已装配的部分，以及**未**装配的部分（阶段 C，P6）

## 四轮的进展，诚实记账

| 轮 | 成分 | 状态 |
|:--|:--|:--|
| **928** | `combine_sat_pointwise`：逐点分配律 | **已证** |
| **929** | `foldl_add_eq_sum`、`sum_map_add` | **已证** |
| **930** | `zipWith_zip_assoc`：三方 `zip` 对齐 | **已证** |
| **931** | **装配 `dot_zipWith_add`（一般分配律）** | ****未完成**** |

**=> 本文件交付装配所需的**最后一块**（`dot_as_sum`，把 `dot` 统一写成 `sum`），
并把**为什么最终一步仍差**写清楚。**

## 最终一步差在哪里

**目标形态是：**

```
(map (fun u => u.1 * u.2) (zipWith (fun u v => (u.1 + v.1, u.2)) (a.zip x) (b.zip x))).sum
  =  (map (fun u => u.1 * u.2) (a.zip x)).sum + (map (fun u => u.1 * u.2) (b.zip x)).sum
```

**左端是对**三元组**列表求和，右端是对**二元组**列表求和。**

**=> 要连接它们，必须先证**一条投影引理**：**

```lean
(map (fun u => u.1 * u.2) (zipWith (fun u v => (u.1+v.1, u.2)) l₁ l₂)).sum
  = (map (fun u => u.1.1 * u.2) ...).sum + ...
```

**而 `zipWith` 在其结果上不保留分量结构（它丢失了 `v.1` 之外的 `v` 信息），
所以这条投影引理**不能**从 `sum_map_add` 直接得到 —— 必须先**重新展开 `zipWith`**，
把三元组的 `.1` 与 `.2.1` 显式恢复。**

**=> 这一步我在本轮内没能让 Lean 通过；把它留成**明确的下一步**，
而不是把 `dot_zipWith_add` 写成未证或假证。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| **`dot_as_sum`** | **⭐⭐ 把 `dot` 统一写成 `sum` 形式（装配的前置，已证）** |

**=> 这条本身有独立价值：它把 `dot` 从 `foldl` 形态搬到 `sum` 形态，
使任何后续关于 `dot` 的代数推理都只需处理 `sum`。** -/

namespace Lattice.Runtime.DotDistribGeneral

open Lattice

/-- **⭐⭐ `dot` 统一写成 `sum` 形式。**

**=> `dot l x = ((l.zip x).map (fun u => u.1 * u.2)).sum`。**

**=> 这使 `dot` 的代数推理只需处理 `List.sum`，而 `sum` 有现成的分配/归并引理
（`sum_map_add` 等）。**

**=> 它是装配 `dot_zipWith_add` 的**第一步**，已完成。** -/
theorem dot_as_sum (l x : List Int) :
    dot l x = (((l.zip x).map (fun u : Int × Int => u.1 * u.2))).sum := by
  unfold dot
  exact Lattice.Runtime.FoldlSum.foldl_add_eq_sum (fun u : Int × Int => u.1 * u.2) _

/-- **⭐ `dot` 的 `sum` 形式与零的关系：`dot l x = 0` 当且仅当对应的 `sum` 为零。** -/
theorem dot_eq_zero_iff (l x : List Int) :
    dot l x = 0 ↔ (((l.zip x).map (fun u : Int × Int => u.1 * u.2))).sum = 0 := by
  rw [dot_as_sum]

end Lattice.Runtime.DotDistribGeneral
