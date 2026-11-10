import Mathlib
import Lattice.Core.CIC.ProgressComplete
import Lattice.Core.CIC.PiShape

/-!
# 组装进展：`PiShapeR` 携带头部信息，使递归良基（阶段 5）

## 本轮先发现的问题

**第 806 轮的 `PiShape.app (f a)` **不携带**函数部分的形状。于是想对「`PiShape f` 且 `Closed Γ f`」
做结构递归时，`app g x` 分支拿到的是「`f = app g x`」，**却不知道 `g` 的形状** ——
递归无处落脚。**

**本轮把它修正为 `PiShapeR`：`app` 构造子**携带头部的形状**：**

```lean
| app {f a : Term} : PiShapeR f -> PiShapeR (.app f a)
```

**=> 于是 `PiShapeR (.app f a)` 可以**反推** `PiShapeR f`（`piShapeR_head`），
递归因此良基。**

## 这解释了第 806 轮为什么只能「展示四条路径」而没有组装

**路径是有的，但**数据结构不足以支撑递归**。这不是证明技巧问题，
是归纳定义的形状问题 —— 也正是第 801 轮 `HeadForm → HeadShape` 那一次的同一个教训：
**归纳族必须对它要递归的方向**封闭**。** -/

namespace Lattice.Core.CIC

/-- **携带头部形状的 `pi` 类型形状。**

**=> 与第 806 轮的 `PiShape` 相比，`app` 构造子多一个前提 `PiShapeR f`。
这使「`app` 的头部形状」可被反推，递归因而良基。** -/
inductive PiShapeR : Term → Prop
  /-- **抽象。** -/
  | lam (A b : Term) : PiShapeR (.lam A b)
  /-- **变量。** -/
  | var (n : ℕ) : PiShapeR (.var n)
  /-- **局部定义。** -/
  | letE (A t b : Term) : PiShapeR (.letE A t b)
  /-- **应用：头部形状是已知的。**

  **=> 这一条就是与 `PiShape.app` 的全部差别，也是递归能进行的唯一原因。** -/
  | app {f a : Term} : PiShapeR f → PiShapeR (.app f a)

/-- **`PiShapeR (.app f a)` 反推 `PiShapeR f`。**

**=> 由 `app` 构造子携带的前提直接得到。第 806 轮的 `PiShape` **做不到**这一点，
因为它的 `app` 构造子没有前提。** -/
theorem piShapeR_head {f a : Term} (h : PiShapeR (.app f a)) : PiShapeR f := by
  cases h with
  | app hf => exact hf

end Lattice.Core.CIC
