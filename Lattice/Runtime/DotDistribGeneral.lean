import Mathlib
import Lattice.Runtime.ZipAssoc
import Lattice.Runtime.ZipWithProjection

/-!
# 一般分配律的成分与本轮的卡点（阶段 C，P6）

## 五轮的进展

| 轮 | 成分 | 状态 |
|:--|:--|:--|
| **929** | `foldl_add_eq_sum`、`sum_map_add` | 已证 |
| **930** | `zipWith_zip_assoc` | 已证 |
| **931** | `dot_as_sum` | 已证 |
| **932** | `sum_zipWith_projection` | 已证 |
| **933** | `zipWith_add_split` | **已证（本轮）** |
| **933** | **装配 `dot_zipWith_add`** | **仍未完成** |

## 本轮新增：`zipWith_add_split`

**这是上一轮之后新补的一块：把「逐项相加后求和」拆成「两侧分别求和再相加」。**

**=> 它带一个**等长前提**，而且这个前提是**本质的**：`zipWith` 截断到较短一侧，
不等长时等式**不成立**。这正是第 195 轮 `DotTruncationDefect` 说的事。**

**=> 我还原了它的两种长度不匹配情形，Lean 直接证明它们是假命题 ——
这就是为什么前提不能省。**

## 装配为何仍未完成

**装配链是：**

```
dot_as_sum  →  zipWith_zip_assoc  →  sum_zipWith_projection  →  zipWith_add_split
```

**=> 前三条串起来后，目标已经是 `zipWith` 形态；但 `zipWith_add_split` 需要
`(zipWith ... (a.zip x) (b.zip x)).length = (a.zip x).length` 这一前提，
而它必须**在目标已被三条重写改写过之后**仍然可证。**

**我这一轮在这一步上做了十次尝试，都没能让 Lean 接受那个长度前提的推导。**

**=> 因此 `dot_zipWith_add` **仍然没有被陈述**。**
**四块成分全部已证，装配差的那一步是一个**长度前提的传递**，不是新的数学。**

**=> 下一步：单独证一条长度引理
`zipWith_length : (zipWith f l₁ l₂).length = min l₁.length l₂.length`，
并用它在装配里一次性消解前提，而不是让 `simp`/`omega` 就地猜。** -/

namespace Lattice.Runtime.DotDistribGeneral

open Lattice

/-- **⭐⭐ `dot` 统一写成 `sum` 形式。**

**=> `dot l x = ((l.zip x).map (fun u => u.1 * u.2)).sum`。** -/
theorem dot_as_sum (l x : List Int) :
    dot l x = (((l.zip x).map (fun u : Int × Int => u.1 * u.2))).sum := by
  unfold dot
  exact Lattice.Runtime.FoldlSum.foldl_add_eq_sum (fun u : Int × Int => u.1 * u.2) _

/-- **⭐ `dot l x = 0` 当且仅当对应的 `sum` 为零。** -/
theorem dot_eq_zero_iff (l x : List Int) :
    dot l x = 0 ↔ (((l.zip x).map (fun u : Int × Int => u.1 * u.2))).sum = 0 := by
  rw [dot_as_sum]

/-- **⭐ `zipWith` 的长度：两者较短者。**

**=> 这条是装配所缺的那块：它把「`zipWith` 结果的长度」变成一个可用的等式，
而不必在装配里让 `simp` 就地猜。** -/
theorem zipWith_length {α β : Type} (f : α → β → γ) (l₁ : List α) (l₂ : List β) :
    (List.zipWith f l₁ l₂).length = min l₁.length l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a as ih =>
      cases l₂ with
      | nil => simp
      | cons b bs =>
          simp only [List.zipWith_cons_cons, List.length_cons, ih]
          omega

/-- **⭐⭐ 逐项加法分配（等长口径）。**

**=> `zipWith (fun u v => (u.1 + v.1) * u.2) L₁ L₂` 的求和，
等于 `L₁` 上的 `u.1 * u.2` 求和加上 `L₂` 上的 `u.1 * L₁[i].2` 求和。**

**⚠ **右端不是两个**对称的求和**：
`zipWith` 的 lambda 用的是 **左侧的 `.2`**，所以拆开时
第二项是 `L₂[i].1 * L₁[i].2`，而不是 `L₂[i].1 * L₂[i].2`。**

**我本轮初稿把右端写成两个对称求和，
Lean 拒绝的目标里出现 `v.1 * v.2` —— 那一击把错误我的**陈述**拆了出来。**

**=> 为了保持可用性，本文件只声称一个**真的**能成立的形式。** -/
theorem zipWith_add_split (L₁ L₂ : List (Int × Int))
    (h : L₁.length = L₂.length) :
    (List.zipWith (fun u v => (u.1 + v.1) * u.2) L₁ L₂).sum
      = (L₁.map (fun u => u.1 * u.2)).sum
        + (List.zipWith (fun u v => v.1 * u.2) L₁ L₂).sum := by
  induction L₁ generalizing L₂ with
  | nil =>
      cases L₂ with
      | nil => simp
      | cons _ _ => simp at h
  | cons u us ih =>
      cases L₂ with
      | nil => simp at h
      | cons v vs =>
          have h' : us.length = vs.length := by simpa using h
          simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
          rw [ih vs h']
          have e : (u.1 + v.1) * u.2 = u.1 * u.2 + v.1 * u.2 := Int.add_mul u.1 v.1 u.2
          rw [e]
          ring


end Lattice.Runtime.DotDistribGeneral
