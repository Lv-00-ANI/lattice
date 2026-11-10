import Mathlib
import Lattice.Core.CIC.NormalFormWF
import Lattice.Core.CIC.TermSize

/-!
# 为什么 `size` 与 `maxConst` **不能**合成一个字典序（阶段 5，强规范化组装）

## 组装的自然想法

**第 785 轮给了 `size`（对 `beta` **增长**），第 787 轮给了 `maxConst`（对 `delta` **严格下降**）。
最自然的组装是字典序 `(maxConst, size)`：**

- **`delta`**：`maxConst` 严格下降 → 字典序下降 ✅
- **子项情形**（`appL`/`appR`/…）：`size` 严格下降且 `maxConst` 不变 → 字典序下降 ✅
- **`beta`/`zeta`**：`maxConst` **不变**，而 `size` **增长** → **字典序上升 ❌**

**=> 字典序在这三个构造子上是**反的**。本轮给出具体的 `decide` 见证。**

## 见证（全部来自第 785 轮的那个项）

**取 `A0 = sort prop zero`、`a = lam A0 A0`、`b = app (app (app (var 0) (var 0)) (var 0)) (var 0)`，
这些项**不含任何 `const`**，所以 `maxConst` 两边都是 `0`：**

| 项 | `maxConst` | `size` |
|:--|--:|--:|
| `app (lam A0 b) a` | **0** | **13** |
| `subst 0 a b` | **0** | **15** |

**=> `beta` 保持第一分量、抬高第二分量。任何以 `maxConst` 为主的字典序都会被它打破。**

## 这意味着什么

**`normal_form` 的证明**不能**是一次「找一个良基序」的动作。真正需要的是**

1. **对子项情形用 `size` 做结构归纳（这部分 `size` 完全够用，第 785 轮的七条定理就是它）；**
2. **对 `delta` 用 `maxConst`（第 787 轮已备）；**
3. **对 `beta`/`zeta` 用**替换本身的结构性质** —— 即「替换后的项是某个原项的子结构并」，或者
   直接走**可归约性（reducibility / Tait）**论证，而不是任何语法序。**

**=> 第 3 条是这条路的真难点，也是本轮**没有**假装解决的部分。把它写成三条候选路线，
比写一个 `sorry` 更有价值。**

## 三条候选路线

| 路线 | 内容 | 现状 |
|:--|:--|:--|
| **A. 可归约性（Tait）** | 定义 `Reducible t`（「`t` 的每个归约都终止」），对类型归纳 | **需要类型层，而 `Typing.lean` 尚未与本归约系统对接** |
| **B. 序列化度量** | 找一个对 `subst` 不增长的非语法度量（如「未归约 redex 的多重集」） | **未尝试；需要先定义 redex 位置** |
| **C. 限制 `b`** | 只对 `b` 中 `var 0` 至多出现一次的项证终止 | **可做，但结论比想要弱** |

**本文件只把「字典序不行」证成定理，不动上面三条。** -/

namespace Lattice.Core.CIC

/-- **`A0`：一个最小的项，不含任何 `const`。** -/
def A0 : Term := Term.sort SortKind.prop Level.zero

/-- **`aa = lam A0 A0`：大小 3 的闭合项。** -/
def aa : Term := Term.lam A0 A0

/-- **`bb`：`var 0` 出现三次的项，大小 7。** -/
def bb : Term := Term.app (Term.app (Term.app (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 0)

/-- **`beta` 之前：`maxConst` 为 0。** -/
theorem maxConst_beta_before : maxConst (Term.app (Term.lam A0 bb) aa) = 0 := by decide

/-- **`beta` 之后：`maxConst` 仍为 0。**

**=> `beta` 对 `maxConst` **不严格下降**，这是字典序失败的第一半。** -/
theorem maxConst_beta_after : maxConst (subst 0 aa bb) = 0 := by decide

/-- **`beta` 之后 `size` 更大。**

**=> 字典序失败的第二半：第一分量不变，第二分量上升，所以序上升。** -/
theorem size_beta_before_after : size (Term.app (Term.lam A0 bb) aa) < size (subst 0 aa bb) := by
  decide

/-- **`beta` 对两个分量都不提供下降。**

**结论写成两个分量的并置，而不是 `Prod.Lex`：更直接，也不依赖序的定义细节。
`maxConst` 不变、`size` 上升 —— 因此任何「先比 `maxConst`、再比 `size`」的字典序在 `beta` 上上升。** -/
theorem beta_no_lex_descent :
    maxConst (subst 0 aa bb) = maxConst (Term.app (Term.lam A0 bb) aa)
      ∧ size (Term.app (Term.lam A0 bb) aa) < size (subst 0 aa bb) := by
  refine ⟨?_, ?_⟩
  · rw [maxConst_beta_after, maxConst_beta_before]
  · exact size_beta_before_after

end Lattice.Core.CIC
