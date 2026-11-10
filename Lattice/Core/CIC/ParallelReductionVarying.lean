import Mathlib
import Lattice.Core.CIC.TakahashiDev

/-!
# `ParRedV`：允许类型标注变化的平行归约（阶段 5，解开第 825 轮的缺口）

## 第 825 轮把缺口定位成什么

**`shift` 的定义是：**

```lean
| c, d, .lam A b    => .lam (shift c d A) (shift (c + 1) d b)
| c, d, .letE A t b => .letE (shift c d A) (shift c d t) (shift (c + 1) d b)
```

**=> `shift` **同时**作用于类型标注与体，而且体用 `c+1`、标注用 `c`。**

**而第 819 轮的 `ParRedS`/`ParRedU` 的 `lam` 构造子**固定**标注（`lam A b → lam A b'`），
于是「`shift` 之后的项」与「`ParRedU` 之后的项」在**标注位置上不一致** ——
`shift c d (lam A b)` 的标注是 `shift c d A`，而 `ParRedU.lam` 要求标注不变。**

**`=>` 六次尝试的失败不是一般化顺序问题，而是**两个定义对标注的处理不一致**。
本轮把它统一：让 `ParRedV.lam` 也允许标注变化。**

## 为什么这个决定是对的

**第 819 轮当时选择「固定标注」，理由是让 `ParRedS` 与 `Step` 对齐（`Step` 不碰标注）。**

**但 `shift` 是**替换基础设施**的一部分，它**必须**作用到标注上 —— 否则进入绑定层时标注会捕获变量。
两个要求无法同时满足「`ParRed` 固定标注」与「`ParRed` 对 `shift` 合同」。**

**=> 正确的关系必须允许标注变化，然后由**与 `Step` 的对应**单独处理（`Step` 的子集情形）。
这就是 `ParRedV`（V = var/annotation-varying）。**

## 本文件给出

**`ParRedV` 的定义（`lam`/`letE`/`beta` 都允许标注变化），以及它的自反性。
`shift` 合同与它与 `ParRedU` 的关系是下一轮。** -/

namespace Lattice.Core.CIC

/-- **允许类型标注变化的平行归约。**

**=> 与 `ParRedU` 的差别：`lam`、`letE`、`beta` 三条构造子**额外**携带 `ParRedV E A A'`，
即类型标注也能平行归约。这是 `shift` 合同性的必要条件。** -/
inductive ParRedV (E : DefEnv) : Term → Term → Prop
  /-- **零处归约。** -/
  | zero (t : Term) : ParRedV E t t
  /-- **常量按 `delta` 展开。** -/
  | delta (c : ℕ) (body : Term) : E c = some body → ParRedV E (.const c) body
  /-- **应用：两边同时归约。** -/
  | app {f f' a a' : Term} : ParRedV E f f' → ParRedV E a a' → ParRedV E (.app f a) (.app f' a')
  /-- **β：标注、体、参数三者都归约，并执行替换。**

  **=> 标注 `A` 也变，因为 `shift` 会改变它。** -/
  | beta {A A' b b' a a' : Term} :
      ParRedV E A A' → ParRedV E b b' → ParRedV E a a' →
      ParRedV E (.app (.lam A b) a) (subst 0 a' b')
  /-- **抽象：标注与体都归约。**

  **=> 这一条是第 825 轮缺口的直接修正。** -/
  | lam {A A' b b' : Term} :
      ParRedV E A A' → ParRedV E b b' → ParRedV E (.lam A b) (.lam A' b')
  /-- **乘积：两部分都归约。** -/
  | pi {A A' B B' : Term} :
      ParRedV E A A' → ParRedV E B B' → ParRedV E (.pi A B) (.pi A' B')
  /-- **局部定义：只归约值。** -/
  | letL {A t t' b : Term} : ParRedV E t t' → ParRedV E (.letE A t b) (.letE A t' b)
  /-- **局部定义：只归约体。** -/
  | letR {A t b b' : Term} : ParRedV E b b' → ParRedV E (.letE A t b) (.letE A t b')
  /-- **局部定义：标注、值、体都归约，并执行替换。** -/
  | letE {A A' t t' b b' : Term} :
      ParRedV E A A' → ParRedV E t t' → ParRedV E b b' →
      ParRedV E (.letE A t b) (subst 0 t' b')

/-- **`ParRedV` 对每个项自反。** -/
theorem parRedV_refl (E : DefEnv) (t : Term) : ParRedV E t t :=
  ParRedV.zero t

/-- **`ParRedV` 的 `lam` 允许标注变化。**

**=> 与 `ParRedU.lam`（固定标注）并置，就是本轮全部改动的意义：
标注位置现在**可以**动，`shift` 因此能穿过去。** -/
theorem parRedV_lam_varying {E : DefEnv} {A A' b b' : Term}
    (hA : ParRedV E A A') (hb : ParRedV E b b') :
    ParRedV E (.lam A b) (.lam A' b') :=
  ParRedV.lam hA hb

end Lattice.Core.CIC
