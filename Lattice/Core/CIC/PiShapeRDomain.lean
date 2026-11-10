import Mathlib
import Lattice.Core.CIC.PiShapeRDirection
import Lattice.Core.CIC.ProgressComplete

/-!
# `PiShapeR` 只描述「具有 `pi` 类型」的项，不能覆盖一切（阶段 5）

## 第 809 轮记下的路线，本轮走上去之后发现什么

**第 809 轮的路线是：「把 `PiShapeR.app` 的前提改成陈述在结果类型上，使两个族方向一致」。**

**本轮先试了更简单的一步：把陈述从「`HasType noConsts Γ f (pi A B)`」放宽成
「`HasType noConsts Γ f A`」任意 `A`，于是 `generalize` 不再需要，方向问题自然消失。**

**放宽之后立刻暴露另一件事：`PiShapeR` **没有** `sort` 与 `pi` 的构造子。**

**`PiShapeR` 的四条构造子是 `lam`、`var`、`letE`、`app` —— 全是「可以具有 `pi` 类型」的形状。
而 `sort` 与 `pi` 本身**不能**具有 `pi` 类型（它们是宇宙层级上的东西），
所以它们**本来就不该**出现在 `PiShapeR` 里。**

**=> 这解释了为什么第 809 轮的 `app` 分支失败：`PiShapeR` 是按「`pi` 类型的形状」设计的，
而把结论放宽到「任意类型」之后，`sort` 与 `pi` 两个分支就没有对应的构造子可给了。**

## 结论

**`HasType noConsts Γ f A → PiShapeR f` 对**任意** `A` 是**假**的：
取 `f = sort k l`，它良类型化（`HasType.sort`），而 `PiShapeR (sort k l)` 不成立。**

**这不是缺陷 —— 是 `PiShapeR` 的**定义域**决定的。它只在「具有 `pi` 类型」的条件下有意义，
而那个条件下 `sort`/`pi` 被构造子互斥排除（第 806 轮已证）。**

## 所以第 809 轮的失败要重新理解

**那里失败的不是「方向不一致」，而是「`generalize` 把目标钉成 `pi A B` 之后，
`app` 的结果类型 `Bg` 必须同时是 `pi A B`」—— 这是**同一个**事实的另一种说法：
`PiShapeR` 的定义域与 `HasType.app` 的结果类型不是同一个东西。**

**=> 两条路线都需要：**

1. **把 `PiShapeR` 的适用范围明确写成「具有 `pi` 类型」**（本文件给出 `PiShapeR` 与类型的对应关系）；
2. **让 `HasType.app` 的结果类型参与 `PiShapeR` 的构造**，使 `app` 分支的递归落到它上面。

**本轮做第 1 条。** -/

namespace Lattice.Core.CIC

/-- **`PiShapeR` 的项**不能**是 `sort`。**

**=> 四条构造子的结论都不是 `sort`。这是「`PiShapeR` 只在 `pi` 类型下有意义」的第一半。** -/
theorem piShapeR_not_sort {f : Term} (h : PiShapeR f) : ∀ (k : SortKind) (l : Level), f ≠ .sort k l := by
  intro k l he
  subst he
  cases h

/-- **`PiShapeR` 的项**不能**是 `pi`。**

**=> 第二半。`pi` 本身就是宇宙层级的东西，不具备「`pi` 类型」。** -/
theorem piShapeR_not_pi {f : Term} (h : PiShapeR f) : ∀ (A B : Term), f ≠ .pi A B := by
  intro A B he
  subst he
  cases h

/-- **`PiShapeR (sort k l)` 不成立。**

**=> 与 `HasType.sort` 并置，说明「放宽到任意 `A`」的那条路**必然失败**：
`sort` 良类型化但不在 `PiShapeR` 里。** -/
theorem piShapeR_sort_false (k : SortKind) (l : Level) : ¬ PiShapeR (.sort k l) := by
  intro h
  exact piShapeR_not_sort h k l rfl

/-- **`sort` 是良类型的，且不在 `PiShapeR` 里。**

**=> 把「放宽路线失败」写成一条可检查的定理，而不是散文。** -/
theorem sort_typed_not_piShapeR (Γ : CICCtx) (k : SortKind) (l : Level) :
    HasType noConsts Γ (.sort k l) (.sort k l) ∧ ¬ PiShapeR (.sort k l) :=
  ⟨HasType.sort Γ k l, piShapeR_sort_false k l⟩

end Lattice.Core.CIC
