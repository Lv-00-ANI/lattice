import Mathlib
import Lattice.Core.CIC.TypeUniqueness
import Lattice.Core.CIC.HasTypeW

/-!
# `TypeUniq` 的两条前置：`pi` 单射性与 `Conv` 在 `pi` 上的合同性（阶段 5）

## 第 814 轮点名了什么

**第 814 轮把 `TypeUniq`（类型唯一性）写成 `Prop`，并指出它需要两个前提：**

1. **`pi` 的单射性**（`pi A B = pi A' B'` 蕴含 `A = A'` 且 `B = B'`）；
2. **`Conv` 在 `pi` 上的合同性**（`Conv A A'` 与 `Conv B B'` 蕴含 `Conv (pi A B) (pi A' B')`）。

**本轮把两条都证出来。**

## 怎么证的

**`pi` 单射性是 `Term` 构造子的直接性质：`injection` 一句。**
**`Conv` 的合同性走 `Reduces`：先对 `Reduces E A A'` 归纳（用 `Step.piDom` 推进），
再对 `Conv` 归纳（`reduces`/`symm`/`trans` 三条构造子分别处理）。**

**=> 值得注意：两步都**不需要** `Conv` 的任何额外性质，因为 `Conv` 是**自由生成**的等价关系
（第 812 轮的设计选择在这里兑现：若当时选「存在公共归约」，这一步反而会卡住）。** -/

namespace Lattice.Core.CIC

/-- **`pi` 的单射性：`pi A B = pi A' B'` 蕴含 `A = A'` 且 `B = B'`。**

**=> 由 `Term` 构造子的 `injection` 直接得到。** -/
theorem pi_inj {A B A' B' : Term} (h : (Term.pi A B : Term) = Term.pi A' B') :
    A = A' ∧ B = B' := by
  injection h with h1 h2
  exact ⟨h1, h2⟩

/-- **`Reduces` 在 `pi` 的定义域上是合同的。**

**=> 对 `Reduces E A A'` 归纳：零步用 `refl`，步进用 `Step.piDom` 推进一步再接归纳假设。** -/
theorem reduces_pi_dom (E : DefEnv) {A A' B : Term} (h : Reduces E A A') :
    Reduces E (.pi A B) (.pi A' B) := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step a b c hab hbc ih => exact Reduces.step (Step.piDom a b B hab) ih

/-- **`Reduces` 在 `pi` 的余域上也是合同的。**

**=> 与上一条对称，用 `Step.piCod`。** -/
theorem reduces_pi_cod (E : DefEnv) {A B B' : Term} (h : Reduces E B B') :
    Reduces E (.pi A B) (.pi A B') := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step a b c hab hbc ih => exact Reduces.step (Step.piCod A a b hab) ih

/-- **`Conv` 在 `pi` 的定义域上合同。**

**=> 对 `Conv` 归纳：`reduces` 用 `reduces_pi_dom`，`symm`/`trans` 由归纳假设与 `conv_symm`/`conv_trans` 给出。
这条与 `pi_inj` 合起来就是第 814 轮点名的两条前提之一。** -/
theorem conv_pi_dom (E : DefEnv) {A A' B : Term} (h : Conv E A A') :
    Conv E (.pi A B) (.pi A' B) := by
  induction h with
  | reduces hr => exact Conv.reduces (reduces_pi_dom E hr)
  | symm _ ih => exact conv_symm ih
  | trans _ _ ih1 ih2 => exact conv_trans ih1 ih2

/-- **`Conv` 在 `pi` 的余域上合同。** -/
theorem conv_pi_cod (E : DefEnv) {A B B' : Term} (h : Conv E B B') :
    Conv E (.pi A B) (.pi A B') := by
  induction h with
  | reduces hr => exact Conv.reduces (reduces_pi_cod E hr)
  | symm _ ih => exact conv_symm ih
  | trans _ _ ih1 ih2 => exact conv_trans ih1 ih2

/-- **`Conv` 在 `pi` 上整体合同：两部分都可转换则乘积可转换。**

**=> 先对定义域用 `conv_pi_dom`，再对余域用 `conv_pi_cod`，中间以 `conv_trans` 相接。
这是第 814 轮点名的第二条前提。** -/
theorem conv_pi_congr (E : DefEnv) {A A' B B' : Term}
    (hA : Conv E A A') (hB : Conv E B B') :
    Conv E (.pi A B) (.pi A' B') := by
  refine conv_trans (conv_pi_dom E hA) ?_
  exact conv_pi_cod E hB

end Lattice.Core.CIC
