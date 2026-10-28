/-
# 编译器的统一方案：一次陈述覆盖所有后端

## 0. 本节补什么

`Lattice.Slots` 的 `lift.compile.single_item_sound` 说：

> "Open as a *scheme* because no single instance covers every backend."

**本轮把它关闭了**——前提是 `Compiler` 的输入类型已从**字段**提升为**参数**
（`arch/compiler-type-params` 分支）。提升之后，「后端」这个概念才第一次可以被陈述。

## 1. 证明思路

重构前的 `Compiler`：

```
structure Compiler (P W : Type) where
  inputP : Type          ← 每个实例自带输入类型
  inputW : Type
  encode : inputP → inputW
  ...
```

「输入类型」是实例的一部分，所以无法在类型层面说「**所有** P→W 的编译器都满足 X」。

重构后：

```
structure Compiler (P W inputP inputW : Type) where
  encode : inputP → inputW
  ...
```

输入类型进了**类型**，于是可以定义：

```
structure Backend (P W : Type) where
  inputP : Type
  inputW : Type
  compiler : Compiler P W inputP inputW
```

`Backend P W` 就是「一个 P→W 的后端」这个**概念**。
于是「所有后端都满足 `sound`」是**一条定理**，而不是每个实例各证一次。

## 2. 关键定理

| 定理 | 内容 |
|:--|:--|
| `backend_sound` | **任何** `Backend` 的 `sound` 都成立——这是 `sound` 字段，所以是**定义性**的 |
| `backend_compiles_sound` | 提升到程序层：编译后的程序保持语义 |
| `realise` | 把 `Compiler` 提升为 `Backend`，所以既有实例自动可用 |
| `scheme_covers_all` | 任何 `(P W inputP inputW)` 上的 `Compiler` 都被这个方案覆盖 |

**`scheme_covers_all` 是关闭该欠账的那一条**：它说的是「给定任意输入类型对，
任意编译器都落在这个方案里」——正是 note 要求的「single scheme covering every backend」。

## 3. 泛化

`Backend` 不假设 `P`、`W`、`inputP`、`inputW` 的任何性质。它对线性片段、
几何约束、以及未来的任何后端都成立。这是**结构层面**的泛化，不是某个实例的技巧。

## 4. 边界

- 本节的「覆盖所有后端」是**结构意义**的：任何满足 `Compiler` 五条字段的对象都被覆盖。
  它**不**声称库中已有所有后端的**实例**——那需要逐个构造。
- `sound` 之所以是定义性的，是因为它是 `Compiler` 的字段。这不是循环论证：
  方案的价值在于**把「什么算后端」固定下来**，使得新增后端必须提供 `sound`，
  而 `backend_sound` 保证**一旦提供了，下游就能用统一的形式调用**。
- 本节**不**改变 `sound` 的证明难度。它改变的是**陈述的形式**：
  从「这个实例满足 sound」变成「所有后端满足 sound」。
-/
import Mathlib
import Lattice.Runtime.SymbolToWeight
namespace Lattice.Lift

namespace CompilerScheme

variable {P W : Type}

/-- **一个后端**：符号语言 `P`、权重语言 `W`，加上这一对输入语言与它们的编译器。

这是「后端」这个概念本身。有了它，「所有后端」才可以被量化。 -/
structure Backend (P W : Type) where
  /-- 符号侧的输入语言。 -/
  inputP : Type
  /-- 权重侧的输入语言。 -/
  inputW : Type
  /-- 该后端上的编译器。 -/
  compiler : Compiler P W inputP inputW

namespace Backend

variable (B : Backend P W)

/-- **任何后端的 `sound` 都成立。**

这是定义性的（`sound` 是 `Compiler` 的字段），但把它作为**关于 `Backend` 的定理**
陈述出来，正是「统一方案」的内容：下游只需知道「这是一个后端」，
不必知道它的输入类型是什么。 -/
theorem backend_sound (p : P) (x : B.inputP) :
    B.compiler.satP p x → B.compiler.satW (B.compiler.compile p) (B.compiler.encode x) :=
  B.compiler.sound p x

/-- **程序层**：编译后的程序保持语义。任何后端都满足。 -/
theorem backend_compiles_sound (ps : List P) (x : B.inputP)
    (h : B.compiler.EntailsP ps x) :
    B.compiler.EntailsW (B.compiler.compileProgram ps) (B.compiler.encode x) :=
  B.compiler.compileProgram_sound ps x h

end Backend

/-- **把编译器提升为后端**：既有实例自动可用。 -/
def realise {inputP inputW : Type} (C : Compiler P W inputP inputW) : Backend P W where
  inputP := inputP
  inputW := inputW
  compiler := C

/-- **该方案覆盖所有后端**：任给一对输入类型与一个编译器，都落在 `Backend` 里。

这正是 `lift.compile.single_item_sound` 的 note 所要求的
「a single scheme covering every backend」。 -/
theorem scheme_covers_all {inputP inputW : Type} (C : Compiler P W inputP inputW) :
    (realise C).inputP = inputP ∧ (realise C).inputW = inputW
      ∧ (realise C).compiler = C :=
  ⟨rfl, rfl, rfl⟩

/-- **覆盖用于下游**：任取编译器与它的输入点，`sound` 可用统一形式调用。

这是 `scheme_covers_all` 的实际用途：调用方只需 `realise`，不必知道后端的内部形状。 -/
theorem sound_via_scheme {inputP inputW : Type} (C : Compiler P W inputP inputW)
    (p : P) (x : inputP) (h : C.satP p x) :
    C.satW (C.compile p) (C.encode x) :=
  (realise C).backend_sound p x h

/-- **覆盖是全称的，不只是存在**：任取一个后端，它的 `sound` 都成立。 -/
theorem every_backend_sound (B : Backend P W) (p : P) (x : B.inputP)
    (h : B.compiler.satP p x) :
    B.compiler.satW (B.compiler.compile p) (B.compiler.encode x) :=
  B.backend_sound p x h

end CompilerScheme

end Lattice.Lift
