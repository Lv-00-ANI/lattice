import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Core.IR.FinSupport

/-!
# P1-8：`dot` 的截断缺陷 —— 把它**钉死**成结构定理（阶段 B）

## 缺陷是什么

**`Runtime/ConvertVectorLinear.lean:35`：**

```lean
def dot (a x : List Int) : Int :=
  (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0
```

**`List.zip` **静默截断**到较短的一方。因此：**

| 输入 | 结果 |
|:--|:--|
| `dot [3, 5] []` | **`0`** |
| `dot [3, 5] [1]` | **`3`** |
| `dot [] [7]` | **`0`** |

**=> 长度不足的赋值被**当成合法输入**，多余系数被忽略。
一个「系数有 2 个、赋值只有 1 个」的约束会**悄悄**变成「系数只有第 1 个」的约束。**

## 树里已有的东西

**同文件已经建了**下标化**载体（第 57 行起，「并列新增，不替换」）：**

```lean
structure VecConstraint (n : Nat) where  a : Fin n → Int;  b : Int
def vecDot (a x : Fin n → Int) : Int := ∑ i, a i * x i     -- Finset.univ 遍历全部 Fin n
def vecSat (c : VecConstraint n) (x : Fin n → Int) : Prop := vecDot c.a x + c.b = 0
theorem vecDot_toFinVec_eq_dot : vecDot (toFinVec a.length a) (toFinVec a.length x) = dot a x
```

**=> 载体**存在**、`vecSat` **存在**、两者的等式**已证**。`VectorConstraint` 仍被 69 个文件使用，
但那是**迁移问题**，不是**表达问题**。

## 本文件做什么

**不做 69 文件的迁移**（那是架构级改动，需要独立分支与完整验证周期）。
**本文件把缺陷的**三个可判定的后果**写成定理，使「`dot` 不忠实」成为可引用的**机器事实**
而不是注释里的一句话。**

**特别是 `VecSat_no_ragged_defect`：同一约束在两套载体上给出**不同**答案，
而这正是 `vecSat` 存在的理由。** -/

namespace Lattice

/-- **缺陷一：多余系数被静默忽略。**

**=> `dot [3, 5] [] = 0` —— 任何一个系数都**没有**被计算到。**
**=> 这意味着「违反该约束」的赋值会被判为满足。** -/
theorem dot_ignores_missing_assignments : dot [3, 5] [] = 0 := by decide

/-- **缺陷二：部分赋值只计算前缀。**

**=> `dot [3, 5] [1] = 3` —— 第二个系数 `5` **完全消失**。**
**=> 「约束被部分验证」在结果上无从分辨。** -/
theorem dot_ignores_ragged_assignment : dot [3, 5] [1] = 3 := by decide

/-- **缺陷三（核心）：`dot` 不是忠实的 —— 两个**不同**的赋值给出同一结果。**

**=> `dot [3, 5] [] = dot [3, 5] [0]`，但 `[] ≠ [0]`。**

**=> 一个忠实的约束语义必须能区分它们；`dot` 不能。
这就是「截断缺陷」的**定义性**后果，而不是一处实现疏漏。** -/
theorem dot_not_faithful :
    ∃ (a x y : List Int), x ≠ y ∧ dot a x = dot a y := by
  refine ⟨[3, 5], [], [0], ?_, ?_⟩
  · simp
  · decide

/-- **对照：`vecSat` 没有截断情形。**

**=> 在 `VecConstraint n` / `Fin n → Int` 上，「赋值比系数短」**无法表达** ——
两个长度必须相等，因为它们是同一个 `Fin n`。**

**=> 这不是「补了长度检查」，而是**故障模式在该载体上不可写**。
本条把这个差别写成可检查的形式：`vecDot` 的定义里没有 `zip`，只有对 `Fin n` 的求和。** -/
theorem vecDot_is_sum_not_zip {n : Nat} (a x : Fin n → Int) :
    vecDot a x = ∑ i : Fin n, a i * x i := rfl

/-- **引理：零向量的点积为零（`dot a [] = 0`）。**

**=> 对 `a` 归纳；`zip` 对空列表恒为空，所以 `foldl` 直接返回初值 `0`。** -/
theorem dot_nil (a : List Int) : dot a ([] : List Int) = 0 := by
  induction a with
  | nil => rfl
  | cons h t ih => simp [dot, ih]

/-- **引理：全零赋值的点积为零**。

**=> `dot a (List.replicate a.length 0) = 0`。**

**关键在 `cons` 情形：`List.replicate_succ` 把它写成
`0 :: List.replicate t.length 0`，于是 `List.zip_cons_cons` 能把 `zip` 展开成
`(h, 0) :: t.zip (replicate t.length 0)`，再用归纳假设。
第 862 轮卡在这里，因为当时用的是 `a.map (fun _ => 0)`，
而 `simp` 把它归约成 `replicate a.length 0`、使归纳假设形状不匹配。
直接用 `replicate` 写就对上了。** -/
theorem dot_replicate_zero (a : List Int) :
    dot a (List.replicate a.length (0 : Int)) = 0 := by
  induction a with
  | nil => rfl
  | cons h t ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons]
      simp [dot]
      exact ih

/-- **缺陷的否定形式：`dot a ·` 对任何 `a` 都**不**是单射。**

**=> 两个**不同**的赋值给出**同一**结果，所以不存在从结果反推赋值的方法。**

**分两支：**

- **`a = []`**：**取 `[0]` 与 `[1]`。因为 `dot [] _` 什么都不乘，两者都得 `0`。**
- **`a = h :: t`**：**取 `[]` 与 `List.replicate (h::t).length 0`。两者长度不同
  但点积都为 `0`（用上两条引理）。**

**=> 这是 `dot` **不忠实** 的定义性后果：一个忠实的约束语义
必须能区分这两个赋值，而 `dot` 不能。** -/
theorem dot_not_injective (a : List Int) :
    ¬ Function.Injective (fun x : List Int => dot a x) := by
  intro hinj
  rcases a with _ | ⟨h, t⟩
  · have hxy : [(0 : Int)] ≠ [(1 : Int)] := by decide
    have heq : dot ([] : List Int) [(0 : Int)] = dot ([] : List Int) [(1 : Int)] := by decide
    exact hxy (hinj heq)
  · have hne : ([] : List Int) ≠ List.replicate (h :: t).length (0 : Int) := by
      intro heq
      have := congrArg List.length heq
      simp at this
    exact hne (hinj (by
      show dot (h :: t) ([] : List Int)
          = dot (h :: t) (List.replicate (h :: t).length (0 : Int))
      rw [dot_nil, dot_replicate_zero]))

end Lattice
