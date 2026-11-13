/-
# The `Compose` plugin's proofs -- MOVED from `Lattice/Compose/ComposeObligation.lean`

**The composed-obligation counterexample and the `h_of_pre_true` positive case.**

**The DECLARATIONS do not change -- same names, same statements, same proofs, same namespace --
so no downstream file needs editing for the move itself.**
The old path is now a facade that imports this file and contains no proof.
-/

import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
/-!
# L1-2：`compose` 的 `h` 义务——**不可导出**，而且是构造性证明的

## 那个 `h` 是什么

`Compose/Combinators.lean:78`：

    def compose (f : Primitive I M) (g : Primitive M O)
        (h : ∀ x y, f.post x y → g.pre y) : Primitive I O

**`h` 不是类型产物，是语义义务**：`f` 产出的中间值必须满足 `g` 的前置。

评估的 L1-2 要「每个组合提供 `h`」。**那问的是它能否被导出。本文件回答：不能，而且能证明不能。**

## 为什么这条值得一个文件

文件 `Combinators.lean` 的 docstring 已经**用散文**说过「`h` 仍是参数……兼容性义务不能凭空消掉」。
**散文不是证明**：它没有说「存在一个 `f`/`g` 使 `h` 不存在」。

本文件给一个**具体的 `Primitive`**（`blocked`：前置为 `False`，永不运行），
并证明 **`compose (identity α) (blocked α)` 没有任何合法的 `h`**。

## 但也有一类**确实不需要额外义务**的情形

若第二个 primitive 的前置是**恒真**的（`∀ y, g.pre y`），则 `h` 可**直接构造**。
`identity` 就是这一类（`pre := fun _ => True`）。**所以「每个组合都要 `h`」这句话是错的**——
准确的说法是「`h` 在 `g.pre` 非恒真时需要，且那时可能不存在」。 -/

namespace Lattice.Compose

/-! ## 一、一个前置为 `False` 的 primitive -/

/-- **`blocked`**：前置恒假、永不运行——**这是反例用的测试夹具，不是那 11 个 primitive 之一**。

**它是合法的**：`sound` 要求「前置成立 ⟹ 运行成功且后置成立」，而前置永假，所以**空真**。 -/
private def blocked (α : Type) : Primitive α α where
  pre := fun _ => False
  post := fun _ _ => True
  run := fun _ => none
  sound := fun _ hx => absurd hx (by simp)
  strength := .exact
  coverage := some ∅
  frame := fun _ _ => True

/-- **`blocked.pre` 恒假**。 -/
private theorem blocked_pre (α : Type) (y : α) : (blocked α).pre y = False := rfl

/-- **`identity.pre` 恒真**。 -/
theorem identity_pre (α : Type) (y : α) : (identity α).pre y = True := rfl

/-- `identity` 的后置就是相等。 -/
theorem identity_post (α : Type) (x y : α) : (identity α).post x y = (y = x) := rfl

/-! ## 二、⭐ `h` 不可导出：构造性反例 -/

/-- ⭐⭐ **`compose` 的 `h` 不可导出。**

取 `f := identity α`、`g := blocked α`。于是 `h` 的类型是

    ∀ x y : α, y = x → False

**任取 `x`（`α` 非空）与 `y := x`**，前件成立而后件不可能——所以**没有任何 `h`**。

**这条结论的意义**：`compose` 的 `h` **不是**「调用方忘了给的东西」，而是**类型里没有的信息**。
把它变成自动的只能改变 `compose` 的语义（例如要求 `g.pre` 恒真），**那不是清理，是换定理**。 -/
theorem compose_h_not_derivable (α : Type) [Nonempty α] :
    ¬ (∀ x y : α, (identity α).post x y → (blocked α).pre y) := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty α›
  have hpost : (identity α).post a a := rfl
  have := h a a hpost
  simpa using this

/-- **同一个反例也说明「不加 `h` 的 `compose` 会说不实话」**：`blocked` 的前置为假，
所以 `compose (identity α) (blocked α)` 的 `post` 对它自己产出的值**不可能成立**（它根本不产出值）。
**这正是 `h` 要挡住的**。 -/
private theorem blocked_run_none (α : Type) (x : α) : (blocked α).run x = none := rfl

/-! ## 三、⭐ 可导出的类：`g.pre` 恒真时 `h` 自动存在 -/

/-- ⭐⭐ **`g.pre` 恒真 ⟹ `compose` 的 `h` 自动存在**。

**所以「每个组合都要 `h`」是错的**：需要它的是 `g.pre` 非恒真的那一类。 -/
theorem compose_h_of_pre_true {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (hg : ∀ y, g.pre y) : ∀ x y, f.post x y → g.pre y :=
  fun _ y _ => hg y


/-! ## 四、把 `h` 变成**具名义务**：让调用方不可能忘记

`h` 是参数，所以调用方不能忘。但**读者**看不出某个 `compose` 用了什么义务。
`Composed` 把「组合 + 它的 `h`」绑成一个值，于是义务跟着值走。 -/

/-- **带义务的组合**：`h` 与两个 primitive 一起被打包，义务不再是一个游离的参数。 -/
structure Composed (I M O : Type) where
  /-- 第一段 -/
  f : Primitive I M
  /-- 第二段 -/
  g : Primitive M O
  /-- **兼容性义务**：见 `compose_h_not_derivable`——它不可能被消掉 -/
  h : ∀ x y, f.post x y → g.pre y

/-- **`Composed` 就是 `compose` 带上它的 `h`。** -/
def Composed.toPrimitive {I M O : Type} (c : Composed I M O) : Primitive I O :=
  compose c.f c.g c.h

/-- **打包不改变语义**：`toPrimitive` 的 `run` 就是 `compose` 的 `run`。 -/
theorem Composed.toPrimitive_run {I M O : Type} (c : Composed I M O) (x : I) :
    (c.toPrimitive).run x = (c.f.run x).bind c.g.run := rfl

end Lattice.Compose
