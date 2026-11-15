import Mathlib
import Lattice.Runtime.DotDistrib

/-!
# `foldl` 的求和形式：`dot` 分配律所需的可复用引理（阶段 C，P6）

## 第 928 轮留下的

**第 928 轮证明了**逐点**分配律（`combine_sat_pointwise`），并写明：**

> **完整长度的分配律**不是**无条件的；它需要把长度假设穿过一次 `foldl` 归纳。
> 我把一般 `foldl` 引理留作未声称。**

**本轮就是那一步的**准备**：把 `foldl` 的求和形式证出来。**

## 一处已被门禁拦下的重复

**本文初稿在这里重新定义了 `dot_eq_sum`。
**=> 但它**早已存在**（`Lib/Editing/RealConversionRobustness.lean:123`，语义完全相同），
被第 924 轮的分类器以 `dot_eq_sum in 2 files` 拦下。**

**=> 处置：删掉本文的副本，不加重定义。**
**本文真正新增的只有 `foldl_add_eq_sum`（`dot_eq_sum` 的**可复用版**）与 `sum_map_add`。**

## 交付什么

| 引理 | 内容 |
|:--|:--|
| **`foldl_add_eq_sum_aux`** | **⭐⭐ 带任意累加器的形式（归纳所必需）** |
| **`foldl_add_eq_sum`** | **⭐⭐ 累加器为零的形式：`foldl (· + f u) 0 l = (l.map f).sum`** |
| **`sum_map_add`** | **⭐⭐ `sum` 的分配：逐项相加的 `sum` = 两个 `sum` 之和** |

**=> 这两条合起来，`dot` 的一般分配律只剩把 `zip` 的两侧对齐这一步（下一轮）。** -/

namespace Lattice.Runtime.FoldlSum

/-- **⭐⭐ `foldl` 的求和形式（带任意累加器）。**

**=> `l.foldl (fun a u => a + f u) acc = acc + (l.map f).sum`。**

**=> 必须推广到任意 `acc`：归纳步里 `foldl` 的累加器是 `acc + f x`，不是 `0`。**
**=> 这正是第 928 轮「逐点」形式所缺的那层。** -/
theorem foldl_add_eq_sum_aux {α : Type} (f : α → ℤ) :
    ∀ (l : List α) (acc : ℤ), l.foldl (fun a u => a + f u) acc = acc + (l.map f).sum
  | [], acc => by simp
  | x :: xs, acc => by
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [foldl_add_eq_sum_aux f xs (acc + f x)]
      ring

/-- **⭐⭐ `foldl` 的求和形式（累加器为零）。**

**=> 这是 `dot_eq_sum`（既有，`RealConversionRobustness.lean:123`）的**通用骨架**：
任何「带累加的 `foldl`」都能化成「先 `map` 再 `sum`」。** -/
theorem foldl_add_eq_sum {α : Type} (f : α → ℤ) (l : List α) :
    l.foldl (fun acc u => acc + f u) 0 = (l.map f).sum := by
  rw [foldl_add_eq_sum_aux f l 0, zero_add]

/-- **⭐⭐ `sum` 的分配：逐项相加后求和，等于分别求和再相加。**

**=> `(l.map (fun u => f u + g u)).sum = (l.map f).sum + (l.map g).sum`。**

**=> 证明对 `l` 归纳；归纳步是 `Int` 的交换律与结合律（`ring` 收）。** -/
theorem sum_map_add {α : Type} (f g : α → ℤ) :
    ∀ l : List α, (l.map (fun u => f u + g u)).sum = (l.map f).sum + (l.map g).sum
  | [] => by simp
  | x :: xs => by
      simp only [List.map_cons, List.sum_cons]
      rw [sum_map_add f g xs]
      ring

end Lattice.Runtime.FoldlSum
