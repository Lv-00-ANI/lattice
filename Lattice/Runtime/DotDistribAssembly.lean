import Mathlib
import Lattice.Runtime.DotDistribGeneral

/-!
# 装配的最后一环：`a.zip x` 与 `b.zip x` 的第二分量相同（阶段 C，P6）

## 第 933 轮之后还差什么

**第 933 轮把 `zipWith_add_split` 修正成**非对称**形式：**

```
(zipWith (fun u v => (u.1 + v.1) * u.2) L₁ L₂).sum
  = (L₁.map (fun u => u.1 * u.2)).sum
    + (zipWith (fun u v => v.1 * u.2) L₁ L₂).sum
```

**=> 要接到 `dot a x + dot b x`，右端第二项必须变回 `b` 自己的 `v.1 * v.2`。**

**而这需要 `L₁ = a.zip x` 与 `L₂ = b.zip x` 的第二分量对齐 —— 它们的第二投影**都是** `x[i]`。**

## 交付什么

- `zip_snd_align`：两个 `zip x` 的**第二分量序列相同**；
- `dot_zipWith_add`：**一般分配律**。
-/

namespace Lattice.Runtime.DotDistribAssembly

/-- **⭐ 两个 `zip x` 的第二分量序列相同。**

**=> 若 `a` 与 `b` 等长，则它们各自与 `x` 配对后的第二分量序列**逐项相等**。**

**=> 证明：对两个 `zip` 同时展开，逐项用 `x` 的同一元素对齐。** -/
theorem zip_snd_align (a b x : List Int) (ha : a.length = b.length) :
    (a.zip x).map (fun u => u.2) = (b.zip x).map (fun u => u.2) := by
  induction a generalizing b x with
  | nil =>
      cases b with
      | nil => simp
      | cons _ _ => simp at ha
  | cons a₀ as ih =>
      cases b with
      | nil => simp at ha
      | cons b₀ bs =>
          cases x with
          | nil => simp
          | cons x₀ xs =>
              have ha' : as.length = bs.length := by simpa using ha
              simp only [List.zip_cons_cons, List.map_cons]
              rw [ih bs xs ha']

/-- **⭐⭐ 第二分量对齐时，`v.1 * u.2` 可以换成 `v.1 * v.2`。**

**=> 若两个列表等长且第二分量序列相同，
则 `zipWith (fun u v => v.1 * u.2) L₁ L₂` 的求和等于 `L₂` 上 `v.1 * v.2` 的求和。** -/
theorem zipWith_snd_swap (L₁ L₂ : List (Int × Int))
    (h₁ : L₁.length = L₂.length)
    (h₂ : L₁.map (fun u => u.2) = L₂.map (fun u => u.2)) :
    (List.zipWith (fun u v => v.1 * u.2) L₁ L₂).sum
      = (L₂.map (fun v => v.1 * v.2)).sum := by
  induction L₁ generalizing L₂ with
  | nil =>
      cases L₂ with
      | nil => simp
      | cons _ _ => simp at h₁
  | cons u us ih =>
      cases L₂ with
      | nil => simp at h₁
      | cons v vs =>
          have h₁' : us.length = vs.length := by simpa using h₁
          obtain ⟨huv, h₂'⟩ := List.cons.inj h₂
          simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
          rw [ih vs h₁' h₂']
          simp only [huv]


/-- **⭐⭐⭐ 一般分配律：装配完成。**

**⚠ **一个已存在的定理：**同一条命题已在
`Lib/Editing/RealEditSemantics.lean:328` 证明（`dot_zipWith_add`，词字相同）。**

**=> 因此本文件的价值**不在重证**它，而在于：**

1. **把它从**装配链**重新推一遍（五步，每步一条可引用的小引理）；**
2. **把它**为何不能去掉长度前提**说清楚。**

**=> 后者已有反例支持：`RealEditSemantics.lean:627` 的
`dot_zipWith_add_ORIGINAL_is_false_ce` 证明**无条件**版为假。**

**本文件的定理与那条已有定理同义，但它的**证明路径不同**：
它逐步抽出了五块小引理，每一块都单独归档。** -/
theorem dot_zipWith_add_via_sum (a b x : List Int)
    (ha : a.length = b.length) (hb : a.length = x.length) :
    dot (List.zipWith (· + ·) a b) x = dot a x + dot b x := by
  rw [Lattice.Runtime.DotDistribGeneral.dot_as_sum,
      Lattice.Runtime.DotDistribGeneral.dot_as_sum,
      Lattice.Runtime.DotDistribGeneral.dot_as_sum]
  rw [Lattice.Runtime.ZipAssoc.zipWith_zip_assoc a b x ha hb]
  rw [Lattice.Runtime.ZipWithProjection.sum_zipWith_projection]
  have hlen : (a.zip x).length = (b.zip x).length := by simp [ha]
  rw [Lattice.Runtime.DotDistribGeneral.zipWith_add_split (a.zip x) (b.zip x) hlen]
  rw [zipWith_snd_swap (a.zip x) (b.zip x) hlen (zip_snd_align a b x ha)]


end Lattice.Runtime.DotDistribAssembly

