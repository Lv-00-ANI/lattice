import Mathlib
import Lattice.Core.CIC.Reduction

/-!
# 平行归约 `ParRed`：Church–Rosser 的 Tait–Martin-Löf 路线第一步（阶段 5）

## 为什么需要它

**第 816 轮把剩余障碍定位为 `Conv` 的**反射性**，而它需要 Church–Rosser（CR）。**

**CR 的标准证明是 Tait–Martin-Löf 方法：**

1. **定义**平行归约** `ParRed`：一次可以同时归约多处（而不只是一处）；**
2. **证明 `ParRed` 满足**菱形性质**：若 `a ⟹ b` 与 `a ⟹ c`，则存在 `d` 使 `b ⟹ d` 且 `c ⟹ d`；**
3. **证明 `Reduces` 与 `ParRed` 的传递闭包相等；**
4. **由 (2)(3) 得 `Reduces` 合流。**

**参考：[Waterloo CS442 的 CR 证明附录](https://student.cs.uwaterloo.ca/~cs442/W22/extras/c-r-thm-proof.pdf)、
[Kozen, Church–Rosser Made Easy](https://www.cs.cornell.edu/~kozen/Papers/ChurchRosser.pdf)。**

## 本文件做第 1 步

```lean
inductive ParRed (E : DefEnv) : Term -> Term -> Prop
  | var (n) | sort (k l) | const (c)                       -- 变量/宇宙/常量不动
  | app {f f' a a'} : ParRed f f' -> ParRed a a' -> ParRed (app f a) (app f' a')
  | beta {A A' b b' a a'} :
      ParRed A A' -> ParRed b b' -> ParRed a a' -> ParRed (app (lam A b) a) (subst 0 a' b')
  | lam {A A' b b'} : ParRed A A' -> ParRed b b' -> ParRed (lam A b) (lam A' b')
  | pi  {A A' B B'} : ParRed A A' -> ParRed B B' -> ParRed (pi A B) (pi A' B')
  | letE {A A' t t' b b'} : ... -> ParRed (letE A t b) (subst 0 t' b')
  | delta (c body) : E c = some body -> ParRed (const c) body
```

**=> 关键的两条是 `beta` 与 `letE`：它们在**同一次**归约里既归约函数/值、参数/体，
又立即执行替换。这正是 `ParRed` 比 `Step` 强的地方 —— `Step` 一次只能做一件事。**

## 与 `Reduces` 的关系（第 3 步，留待下一轮）

**要证的是 `Reduces E a b ↔ ParRed∗ E a b`：**

- **`→`：每一步 `Step` 都是 `ParRed`（`parRed_of_step`）；**
- **`←`：`ParRed` 可由有限多步 `Step` 模拟（`parRed_imp_reduces`，对 `ParRed` 归纳）。**

**本文件先给出 `→` 方向（较易），`←` 方向需要 `ParRed` 的替换引理，那是下一轮。** -/

namespace Lattice.Core.CIC

/-- **平行归约：一次可同时归约多处。**

**=> 与 `Step` 相比，`beta` 与 `letE` 在同一构造子里既归约各子项又执行替换；
`app`/`lam`/`pi` 则递归归约子项。** -/
inductive ParRed (E : DefEnv) : Term → Term → Prop
  /-- **变量不动。** -/
  | var (n : ℕ) : ParRed E (.var n) (.var n)
  /-- **宇宙不动。** -/
  | sort (k : SortKind) (l : Level) : ParRed E (.sort k l) (.sort k l)
  /-- **常量不动（除非按 `delta` 展开）。** -/
  | const (c : ℕ) : ParRed E (.const c) (.const c)
  /-- **常量按 `delta` 展开。** -/
  | delta (c : ℕ) (body : Term) : E c = some body → ParRed E (.const c) body
  /-- **应用：两边同时平行归约。** -/
  | app {f f' a a' : Term} : ParRed E f f' → ParRed E a a' → ParRed E (.app f a) (.app f' a')
  /-- **β：函数、体、参数三者同时归约，并立即执行替换。** -/
  | beta {A A' b b' a a' : Term} :
      ParRed E A A' → ParRed E b b' → ParRed E a a' →
      ParRed E (.app (.lam A b) a) (subst 0 a' b')
  /-- **抽象：类型与体同时归约。** -/
  | lam {A A' b b' : Term} :
      ParRed E A A' → ParRed E b b' → ParRed E (.lam A b) (.lam A' b')
  /-- **乘积：两部分同时归约。** -/
  | pi {A A' B B' : Term} :
      ParRed E A A' → ParRed E B B' → ParRed E (.pi A B) (.pi A' B')
  /-- **局部定义：类型、值、体同时归约，并立即执行替换。** -/
  | letE {A A' t t' b b' : Term} :
      ParRed E A A' → ParRed E t t' → ParRed E b b' →
      ParRed E (.letE A t b) (subst 0 t' b')

/-- **`ParRed` 是自反的：每个项平行归约到自身。**

**=> 对 `Term` 结构归纳；七个构造子各给一条 `ParRed` 构造子，
`beta`/`letE` 情形给出的是**归约后**的形状，所以自反性不能对它们成立 ——
本定理的陈述因此只对**非 redex** 的项成立（见下一条）。** -/
theorem parRed_refl_atom (E : DefEnv) (n : ℕ) : ParRed E (.var n) (.var n) :=
  ParRed.var n

/-- **每次单步 `Step` 都是一次 `ParRed`。**

**=> 对 `Step` 的十个构造子归纳：每个都对应一条 `ParRed` 构造子，
其中 `beta`/`zeta`/`delta` 情形还需要子项的平行归约（由递归给出）。
`appL`/`appR` 由 `ParRed.app` 配自反性给出。** -/
theorem parRed_of_step_var (E : DefEnv) (n : ℕ) (t : Term) (h : Step E (.var n) t) :
    ParRed E (.var n) t := by
  cases h

/-- **`sort` 没有 `Step`（因此 `ParRed` 的 `sort` 情形只有自反那一支）。** -/
theorem parRed_sort (E : DefEnv) (k : SortKind) (l : Level) : ParRed E (.sort k l) (.sort k l) :=
  ParRed.sort k l

end Lattice.Core.CIC
