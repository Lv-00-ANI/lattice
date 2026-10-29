import Mathlib
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.Extraction

/-!
# `Lattice.Runtime.ConstraintRepresentation` — **L2⇄L3 拿到了它的 `Representation` 实例**

## 这个文件补的是哪一环

四环端到端（`数据 ⇄ token ⇄ 符号模型 ⇄ 权重`）的端点在库里各自存在：

| 环 | 端点 | 在哪 |
|:--|:--|:--|
| L1⇄L2 | `tokenize` / `decode` | `Runtime/L1L2.lean` |
| **L2⇄L3** | **`compileToLayer` + `symbolToWeight_correct`** | **`Runtime/SymbolToWeightCorrectness.lean`** |
| L3⇄L4 | `Representation.compile` / `.extract` + `roundtrip` | `Runtime/Extraction.lean` |

**但 L2⇄L3 与 L3⇄L4 说的是不同的函数。**

- `Lattice.Lift.Representation P W`（`Extraction.lean` L66）把 `compile : P → W`、`extract : W → P`、
  **往返律**三者捆在一起；
- 而 `compileToLayer : ConstraintSet → Layer` **没有 `Representation` 实例** —— 第 59 轮实测：
  全库 9 个实例，**没有一个的 `P` 是 `ConstraintSet`**。

⇒ **`extract_compile` 那条往返律，对 `compileToLayer` 一个字都没说。**
**「符号⇄权重」这一跳在 `Extraction` 里是一个泛型结构，在 `SymbolToWeightCorrectness` 里是一个具体函数，
两者之间没有桥。**

## 这一跳能补，因为 `convertVec` 是双射

```lean
structure VectorConstraint where  a : List Int;  b : Int
structure LinearLayer     where  w : List Int;  b : Int
def convertVec (c : VectorConstraint) : LinearLayer := { w := c.a, b := c.b }
```

**两个结构的字段逐一对应**，所以 `convertVec` 有显然的逆 `⟨l.w, l.b⟩`。

## 本文件给什么

1. `extractLayer : Layer → ConstraintSet` —— `convertVec` 的逐层逆；
2. `extractLayer_compileToLayer` —— **往返律**（`Representation.roundtrip` 要的正是它）；
3. ⭐ `constraintRepresentation : Lattice.Lift.Representation ConstraintSet Layer` —— **实例本身**；
4. ⭐ `constraintRepresentation_semantics` —— **语义律挂到同一个 `compile` 上**。

**第 3、4 条合起来才是「L2⇄L3 的完整端点」**：一个 `compile`，同时有**往返**与**语义**。

## ⚠ 这个文件**不**证明的

- **不做 L1⇄L2**：`encode`/`decode` 在本实例里取 `id`；`Representation` 结构对它们**没有律**
  （只有 `compile`/`extract` 有 `roundtrip` 字段）。**token 层的往返在 `L1L2.lean`，不在本文件。**
- **不声称四环已串成一条合取**。第 58 轮的教训是**不同空间不能塞进一个合取**；本文件做的是
  **让 L2⇄L3 与 L3⇄L4 共用同一个 `compile`**——这是能做的、而且此前没做的那一步。
- **不涉及 `Float`/IEEE**：载体是 `List Int`，与 C 侧的可执行模型无关。
-/

namespace Lattice.Runtime.ConstraintRepresentation

open Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Lift (Representation)

/-! ## 逐层逆 -/

/-- **`convertVec` 的逆**：把神经元的 `(w, b)` 读回约束的 `(a, b)`。

`convertVec` 与它互为逆，因为两个结构的字段**逐一对应**——这不是巧合，是这两处选型的后果，
而本文件是第一次把它写成映射。 -/
def extractLayer (l : LinearLayer) : VectorConstraint :=
  { a := l.w, b := l.b }

/-- **`extractLayer` 逐点还原 `convertVec`。** -/
theorem extractLayer_convertVec (c : VectorConstraint) : extractLayer (convertVec c) = c := by
  cases c with
  | mk a b => rfl

/-- **`convertVec` 是单射**——由上面的左逆立得。 -/
theorem convertVec_injective : Function.Injective convertVec :=
  Function.LeftInverse.injective extractLayer_convertVec

/-- ⭐ **列表层的往返律**：`extractLayer` 是 `compileToLayer` 的左逆。

**这就是 `Representation.roundtrip` 要的那条义务**，此前对 `compileToLayer` 从未陈述过。 -/
theorem extractLayer_compileToLayer (cs : ConstraintSet) :
    (compileToLayer cs).map extractLayer = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [compileToLayer, List.map_cons, extractLayer_convertVec] at ih ⊢
    exact congrArg (List.cons c) ih

/-! ## 实例 -/

/-- ⭐⭐ **`ConstraintSet` 与 `Layer` 之间的表示**——**L2⇄L3 的 `Representation` 实例。**

在此之前，`compileToLayer` 只管语义（`symbolToWeight_correct`），
`Representation` 只管往返（`extract_compile`），**两者说的是两个不同的 `compile`**。
本实例让它们说同一个。

`encode`/`decode` 取 `id`：**本实例不承担 token 层的往返义务**（那在 `L1L2.lean`），
而 `Representation` 结构对 `encode`/`decode` 本来就没有律。 -/
def constraintRepresentation : Representation ConstraintSet Layer where
  inputP := List Int
  inputW := List Int
  encode := id
  decode := id
  compile := compileToLayer
  extract := fun ls => ls.map extractLayer
  roundtrip := fun cs => extractLayer_compileToLayer cs

/-! ## 往返与语义的**组合**——这才是本文件的内容

⚠ **两条被删掉的定理**（第 59 轮的别名普查抓到它们）：

    theorem constraintRepresentation_roundtrip (cs) : ...= cs := constraintRepresentation.roundtrip cs
    theorem constraintRepresentation_semantics (cs) (x) : ... := symbolToWeight_correct cs x

**两条都是把已有事实原样复述**（`forward` 别名）。实例的 `roundtrip` 字段**本身就是**那条律，
再给它起一个名字只是制造第二个名字。**真正缺的是把两者组合起来的那一步**，下面就是。 -/

/-- ⭐⭐ **往返保持语义**：把 `cs` 编译成权重层再提取回来，`AllSatisfied` 不变。

**这条用的是本实例的 `compile` 与 `extract` 两者**，而不是其中任何一个：
左边经过 `compile`（所以它是 `AllZeroOutputs` 的形状），再经过 `extract`（所以是 `cs`），
中间由 `roundtrip` 与 `symbolToWeight_correct` 各出一半。

**它是「L2⇄L3 与 L3⇄L4 共用同一个 `compile`」的可检验后果**：
若 `extract` 不是 `compile` 的左逆，这条就证不出来。 -/
theorem roundtrip_preserves_semantics (cs : ConstraintSet) (x : List Int) :
    AllSatisfied (constraintRepresentation.extract (constraintRepresentation.compile cs)) x ↔
      AllZeroOutputs (constraintRepresentation.compile cs) x := by
  rw [constraintRepresentation.roundtrip]
  exact symbolToWeight_correct cs x

/-- **推论**：提取回来的约束集合与原集合**语义完全相同**（同一个 `x` 上满足性一致）。

这是上一条的直接读法：`extract (compile cs)` 与 `cs` 满足同一批点。 -/
theorem extract_compile_semantically_equal (cs : ConstraintSet) (x : List Int) :
    AllSatisfied (constraintRepresentation.extract (constraintRepresentation.compile cs)) x ↔
      AllSatisfied cs x := by
  rw [constraintRepresentation.roundtrip]

end Lattice.Runtime.ConstraintRepresentation
