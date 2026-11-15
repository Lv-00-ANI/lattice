import Mathlib
import Lattice.Runtime.FoldlSum

/-!
# `zip` 与 `zipWith` 的交换律：一般分配律的前置（阶段 C，P6）

## 第 929 轮留下的

**`foldl` 骨架（`foldl_add_eq_sum`、`sum_map_add`）已就位。**

**=> 一般分配律 `dot (zipWith (+) a b) x = dot a x + dot b x` 还差一级：
把「先逐分量加、再配对」与「先配对、再逐分量加」联系起来。**

**本文件证的就是那个交换律，它是**纯 `List` 引理**，与 `dot` 无关。**

## 交付什么

**`zipWith_zip_assoc`：三者等长时，
`(zipWith (+) a b).zip x = zipWith (fun u v => (u.1+v.1, u.2)) (a.zip x) (b.zip x)`。**

**=> 这条引理恰好说明 `zip` 的截断行为**在对齐后不发生**，
因此它也是第 195 轮 `DotTruncationDefect` 那条警告的正面补充。** -/

namespace Lattice.Runtime.ZipAssoc

/-- **⭐⭐ 三方 `zip` 的交换律（等长时）。**

**=> 先加再配对，等于先配对再加。**
**=> 证明按 `zipWith` 的结构递归，长度为假设保证没有一侧先耗尽。** -/
theorem zipWith_zip_assoc : ∀ (a b x : List Int),
    a.length = b.length → a.length = x.length →
      (List.zipWith (· + ·) a b).zip x
        = List.zipWith (fun u v => (u.1 + v.1, u.2)) (a.zip x) (b.zip x)
  | [], [], [] => fun _ _ => rfl
  | _ :: _, [], [] => fun h1 _ => by simp at h1
  | [], _ :: _, [] => fun h1 _ => by simp at h1
  | [], [], _ :: _ => fun _ h2 => by simp at h2
  | [], _ :: _, _ :: _ => fun h1 _ => by simp at h1
  | _ :: _, [], _ :: _ => fun h1 _ => by simp at h1
  | _ :: _, _ :: _, [] => fun _ h2 => by simp at h2
  | a₀ :: as, b₀ :: bs, x₀ :: xs => fun h1 h2 => by
      simp only [List.zipWith_cons_cons, List.zip_cons_cons]
      have h1' : as.length = bs.length := by simpa using h1
      have h2' : as.length = xs.length := by simpa using h2
      rw [zipWith_zip_assoc as bs xs h1' h2']

end Lattice.Runtime.ZipAssoc
