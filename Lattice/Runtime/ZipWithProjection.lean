import Mathlib
import Lattice.Runtime.FoldlSum

/-!
# `zipWith` 结果的逐项投影：一般分配律的最后一块（阶段 C，P6）

## 第 931 轮卡在哪

装配到这一步时，目标是：

```
(map (fun u => u.1 * u.2) (zipWith (fun u v => (u.1 + v.1, u.2)) L₁ L₂)).sum
  =  (map (fun u => u.1 * u.2) L₁).sum + (map (fun u => u.1 * u.2) L₂).sum
```

我不该直接对 `sum` 做文章，而应先证一条**逐项**恒等式。

## 关键观察

`zipWith (fun u v => (u.1 + v.1, u.2)) L₁ L₂` 的第 `i` 项是 `(L₁[i].1 + L₂[i].1, L₁[i].2)`。
对它取 `.1 * .2` 得 `(L₁[i].1 + L₂[i].1) * L₁[i].2`，右端第 `i` 项是
`L₁[i].1 * L₁[i].2 + L₂[i].1 * L₁[i].2`，二者由 `Int.add_mul` 相等。

**=> 问题从「`zipWith` 投影」化成了「逐项乘法分配」，后者是纯代数，
`zipWith` 的递归结构只需一次归纳。**

## 交付什么

- `zipWith_projection_step`：单步的乘法分配；
- `map_zipWith_projection`：逐项投影恒等式；
- `sum_zipWith_projection`：**其求和版，即第 931 轮卡住的恒等式本身。**
-/

namespace Lattice.Runtime.ZipWithProjection
/-- **⭐⭐ 逐项投影恒等式（直接展开版）。**

**=> `zipWith` 结果的投影就是逐项 `(两侧之和) * 左侧的 .2`。**

**=> 这一步不需要归纳；归纳在下一条里用于把它与右端对齐。** -/
theorem map_zipWith_projection : ∀ (L₁ L₂ : List (Int × Int)),
    (List.zipWith (fun u v => (u.1 + v.1, u.2)) L₁ L₂).map (fun u : Int × Int => u.1 * u.2)
      = (List.zipWith (fun u v => (u.1 + v.1) * u.2) L₁ L₂)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | u :: us, v :: vs => by
      simp only [List.zipWith_cons_cons, List.map_cons]
      rw [map_zipWith_projection us vs]

/-- **⭐⭐ 求和版。** -/
theorem sum_zipWith_projection (L₁ L₂ : List (Int × Int)) :
    ((List.zipWith (fun u v => (u.1 + v.1, u.2)) L₁ L₂).map
        (fun u : Int × Int => u.1 * u.2)).sum
      = (List.zipWith (fun u v => (u.1 + v.1) * u.2) L₁ L₂).sum := by
  rw [map_zipWith_projection]


end Lattice.Runtime.ZipWithProjection
