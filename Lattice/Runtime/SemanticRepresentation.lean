import Mathlib
import Lattice.Runtime.ConstraintRepresentation

/-!
# `Lattice.Runtime.SemanticRepresentation` — **给 `Representation` 加一条语义律，而不动它**

## 为什么是"加一层"而不是"改结构"

`Lattice.Lift.Representation P W`（`Runtime/Extraction.lean` L66）有三个字段与一条律：

```lean
compile : P → W
extract : W → P
roundtrip : ∀ p, extract (compile p) = p
```

**它没有语义。** 所以一个 `Representation` **可以完全不带语义被构造出来**——
`ofEquiv` 就是：任何双射都是表示，**而双射关于「满足哪些点」什么都没说**。

**直接给 `Representation` 加字段会让全库 9 个实例同时失效**（第 59 轮实测的 9 个）。
所以本文件**不碰** `Representation`，而是定义**强化**：

## `SemanticRepresentation`

```lean
structure SemanticRepresentation (P W X : Type) extends Representation P W where
  denoteP : P → X → Prop          -- 符号侧：p 在点 x 上成立
  denoteW : W → X → Prop          -- 权重侧：w 在点 x 上成立
  compile_preserves : ∀ p x, denoteP p x ↔ denoteW (compile p) x
```

**`compile_preserves` 就是 `symbolToWeight_correct` 的形状**——「符号程序满足 ⟺ 网络输出为零」。
**把它提成字段，等于把整条链路的核心义务变成一个结构的第三条律。**

## 本文件给什么

1. `SemanticRepresentation` 结构本身；
2. ⭐ `constraintSemantic : SemanticRepresentation ConstraintSet Layer (List Int)`
   —— **`compile_preserves` 字段就是 `symbolToWeight_correct`**；
3. `SemanticRepresentation.ofRepresentation` —— **构造器**：给定任意 `Representation` 加两侧语义，
   只要 `compile` 保语义，就得到一个 `SemanticRepresentation`。**因此 9 个实例不必改写，
   谁有语义谁就能升级**；
4. `semantic_roundtrip_compiles_agree` —— **泛型组合**：往返之后编译结果与原来语义相同。

## ⚠ 本文件**不**做的

- **不声称 9 个实例都已升级。** 只有 `ConstraintSet → Layer` 这一个真正升级了；
  其余 8 个**有没有语义**是各自的事（`ℚ → ℤ × ℕ` 有，`α → α × Bool` 对泛型 `α` 没有）。
- **不涉及 `no_extractor_both_layers` 的否定结论。** 那条说「左逆不能同时忠实于语义商」，
  **与本文件的 `compile_preserves` 不冲突**：前者约束 `extract`，后者约束 `compile`。
  两者可以同时成立——**这正是「编译保语义」与「提取不能恢复语义」并存的意思**。
-/

namespace Lattice.Lift

open Lattice.Lift.SymbolToWeightCorrectness

/-- ⭐⭐ **带语义的表示**。

`Representation` 只说「编译与提取互逆」。**它不说什么叫"满足"。** 本结构补上那一层：

- `denoteP p x`：符号侧的 `p` 在点 `x` 上成立；
- `denoteW w x`：权重侧的 `w` 在点 `x` 上成立；
- `compile_preserves`：**编译不改变「在哪些点上成立」**。

**第三条是整条链路的核心义务。** 把它放进结构，意味着**一个 `SemanticRepresentation` 不能只凭
"我有一对互逆映射"被构造出来**——它必须同时交出「编译保语义」的证明。 -/
structure SemanticRepresentation (P W : Type) (X : Type) extends Representation P W where
  /-- 符号侧的语义：`p` 在点 `x` 上成立。 -/
  denoteP : P → X → Prop
  /-- 权重侧的语义：`w` 在点 `x` 上成立。 -/
  denoteW : W → X → Prop
  /-- ⭐ **编译保语义**：这就是 `symbolToWeight_correct` 的形状。 -/
  compile_preserves : ∀ p x, denoteP p x ↔ denoteW (compile p) x

namespace SemanticRepresentation

/-- **构造器**：任意 `Representation` 加上两侧语义，只要 `compile` 保语义，就升级成
`SemanticRepresentation`。

**这让升级是"按需"的**：9 个既有实例不必改写，**有语义的那几个各自加一条实例即可**，
没有语义的（例如泛型 `α → α × Bool`）保持原样，**而"没有语义"这件事是可见的**，
因为它们不出现在本结构的实例里。 -/
def ofRepresentation {P W X : Type} (R : Representation P W)
    (denoteP : P → X → Prop) (denoteW : W → X → Prop)
    (h : ∀ p x, denoteP p x ↔ denoteW (R.compile p) x) :
    SemanticRepresentation P W X where
  toRepresentation := R
  denoteP := denoteP
  denoteW := denoteW
  compile_preserves := h

/-- ⭐ **泛型组合**：往返之后，编译出来的权重**语义不变**。

**这条同时用到 `roundtrip` 与 `compile_preserves`**：它把 `p` 编译、提取、再编译，
断言第二次编译的结果与第一次在**所有点**上等价。

**它是 `roundtrip_preserves_semantics` 的泛化版本**——那条是 `ConstraintSet` 上的特例，
这条对**任何** `SemanticRepresentation` 成立。 -/
theorem semantic_roundtrip_compiles_agree {P W X : Type} (R : SemanticRepresentation P W X)
    (p : P) (x : X) :
    R.denoteW (R.compile (R.extract (R.compile p))) x ↔ R.denoteW (R.compile p) x := by
  rw [R.roundtrip]

/-- **语义可以沿往返搬运**：`extract (compile p)` 与 `p` 在**所有点**上语义相同。

**这是 `compile_preserves` 与 `roundtrip` 的直接合成**，也是「提取回来还能用」的精确含义。 -/
theorem semantic_of_extract {P W X : Type} (R : SemanticRepresentation P W X)
    (p : P) (x : X) :
    R.denoteP (R.extract (R.compile p)) x ↔ R.denoteP p x := by
  rw [R.roundtrip]

end SemanticRepresentation

/-! ## 实例：`ConstraintSet → Layer` 的语义化

⚠ **放在 `Lattice.Lift` 里面**，不是另起一个顶层命名空间：`check_namespace_balance` 要求
**文件末行闭合的是首命名空间**，而本文件的首个顶层命名空间是 `Lattice.Lift`。
把实例留在外面会让文件的最后一行闭合 `Lattice.Runtime.ConstraintRepresentation`——
**平衡检查（正确地）把它报成 NEW finding。** -/

/-- ⭐⭐ **L2⇄L3 的语义化表示**。

`compile_preserves` 字段**就是 `symbolToWeight_correct`**——不是"由它推出"，是**它就是**。
于是第 59 轮那个 `Representation ConstraintSet Layer` 实例在这里升级：
**往返律与语义律现在住在同一个对象里。**

⚠ 这也是本文件存在的理由：在它之前，L2⇄L3 的语义是**一个定理**，
往返是**另一个文件里的泛型结构**，两者只能靠一篇文档说"它们是同一个 `compile`"。
**现在它们是同一个值的两个字段。** -/
def constraintSemantic : SemanticRepresentation ConstraintSet Layer (List Int) where
  toRepresentation :=
    Lattice.Runtime.ConstraintRepresentation.constraintRepresentation
  denoteP := AllSatisfied
  denoteW := AllZeroOutputs
  compile_preserves := symbolToWeight_correct

end Lattice.Lift
