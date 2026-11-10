import Mathlib
import Lattice.Core.CIC.ParRedUEquivalence

/-!
# Takahashi 的完整展开 `dev`：菱形性质**不需要**分情形（阶段 5，Tait–Martin–Löf 第 2 步）

## 文献指出的方法

**标准的菱形性质证明要对 `ParRed` 的两条派生做**四次分情形**。Takahashi 的「完整展开」
把这个证明压成**两步**（[UNSW CS3161 讲义](https://cgi.cse.unsw.edu.au/~cs3161/26T3/Lectures/w03b/Lecture%20notes.pdf)、
[Lean 4 的 Metatheory 框架](https://arxiv.org/html/2512.09280v1)、
[Agda 形式化](https://iwilare.com/bsc-thesis.pdf)）：**

1. **定义 `dev t`：把 `t` 里的**所有** redex 一次展开；**
2. **证明**三角形性质**：`ParRedU E t u → ParRedU E u (dev t)`。**

**=> 有了三角形性质，菱形性质的见证就是**同一个项** `dev t`，而且**完全不用分情形**：**

```lean
diamond h1 h2 = ⟨dev t, triangle h1, triangle h2⟩
```

**这是「找到正确的构造」胜过「做更多分情形」的典型。**

## 本文件的范围

**`dev` 的定义需要对 `app` 的函数部分做判断（是不是 `lam`），因此先给 `isLam`。**
**`dev` 本身与三角形性质是本轮**未完成**的部分 —— 它需要 `subst` 与 `ParRedU` 的交换引理，
那是 `SubstitutionShift` 一族所处理的领域。本文件给出定义骨架与它的第一条性质。** -/

namespace Lattice.Core.CIC

/-- **判断一个项是不是抽象。**

**=> `dev` 需要按函数部分的形状分派：`app (lam ..) ..` 要展开成替换，
其余 `app` 只展开两侧。** -/
def isLam : Term → Bool
  | .lam _ _ => true
  | .sort _ _ => false
  | .var _ => false
  | .const _ => false
  | .app _ _ => false
  | .pi _ _ => false
  | .letE _ _ _ => false

/-- **`lam` 被判定为抽象。** -/
@[simp] theorem isLam_lam (A b : Term) : isLam (.lam A b) = true := rfl

/-- **`var` 不是抽象。** -/
@[simp] theorem isLam_var (n : ℕ) : isLam (.var n) = false := rfl

/-- **`app` 不是抽象（它的头部可能是，但它自身不是）。** -/
@[simp] theorem isLam_app (f a : Term) : isLam (.app f a) = false := rfl

/-- **`sort` 不是抽象。** -/
@[simp] theorem isLam_sort (k : SortKind) (l : Level) : isLam (.sort k l) = false := rfl

/-- **`const` 不是抽象。** -/
@[simp] theorem isLam_const (c : ℕ) : isLam (.const c) = false := rfl

/-- **`pi` 不是抽象。** -/
@[simp] theorem isLam_pi (A B : Term) : isLam (.pi A B) = false := rfl

/-- **`letE` 不是抽象。** -/
@[simp] theorem isLam_letE (A t b : Term) : isLam (.letE A t b) = false := rfl

/-- **完整展开 `dev`：对每个构造子定义。**

**`app (lam A b) a` 展开为 `subst 0 (dev a) (dev b)`（β-redex 被消去）；
其余 `app` 展开两侧；`lam`/`pi` 只展开体/两部分；`letE` 按 `zeta` 消去。**

**=> `dev` 是**确定的**——它不依赖任何选择，这正是三角形性质能成立的原因。
本轮**未**证三角形性质，它需要 `subst` 与 `ParRedU` 的交换引理。** -/
def dev (E : DefEnv) : Term → Term
  | .sort k l => .sort k l
  | .var n => .var n
  | .const c => match E c with
    | some body => body
    | none => .const c
  | .app (.lam _ b) a => subst 0 (dev E a) (dev E b)
  | .app f a => .app (dev E f) (dev E a)
  | .lam A b => .lam A (dev E b)
  | .pi A B => .pi (dev E A) (dev E B)
  | .letE A t b => subst 0 (dev E t) (dev E b)

/-- **`dev` 对 `var` 是恒等的。** -/
@[simp] theorem dev_var (E : DefEnv) (n : ℕ) : dev E (.var n) = .var n := rfl

/-- **`dev` 对 `sort` 是恒等的。** -/
@[simp] theorem dev_sort (E : DefEnv) (k : SortKind) (l : Level) : dev E (.sort k l) = .sort k l := rfl

/-- **`dev` 对 `lam` 只展开体。** -/
@[simp] theorem dev_lam (E : DefEnv) (A b : Term) : dev E (.lam A b) = .lam A (dev E b) := rfl

/-- **`dev` 对 `pi` 展开两部分。** -/
@[simp] theorem dev_pi (E : DefEnv) (A B : Term) : dev E (.pi A B) = .pi (dev E A) (dev E B) := rfl

end Lattice.Core.CIC
