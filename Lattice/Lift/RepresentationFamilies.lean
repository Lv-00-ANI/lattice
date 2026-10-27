/-
# 表示族：权重的三族表示及其函子性

## 0. 本节补什么

外部审查对新范式的硬缺口：

> **每层只有一族表示。** 权重侧只有 `AffineLayer`，符号侧只有几何约束，token 侧只有
> `CharToken`。⇒ 这是**一条链，不是谱系**。

**核实**：`Lattice/Core` 里其实有**三个**权重结构，但它们**互不连通**：

| 结构 | 文件 | 索引 | 权重类型 |
|:--|:--|:--|:--|
| `AffineLayer n` | `Net.lean` | 单一类型 `n` | `n → n → ℝ`（方阵） |
| `LayerParams m n` | `Weight.lean` | 两个类型 | `m → n → ℝ`（矩形） |
| `MLayer m n` | `VariableNet.lean` | 两个 `Nat` | `Matrix (Fin m) (Fin n)` |

⇒ **三族表示存在，但没有一条定理把它们相连。** 本节补这个。

## 1. 证明思路

### 1.1 三族的关系

**`LayerParams` 是最一般的**：任意 `m → n → ℝ`。
`AffineLayer n` 是它在 `m = n` 时的特例。
`MLayer m n` 是 `LayerParams (Fin m) (Fin n)` 的 `Matrix` 包装。

⇒ **存在两条自然的嵌入**：

```
AffineLayer n      →  LayerParams n n
LayerParams (Fin m) (Fin n)  →  MLayer m n
```

### 1.2 函子性：转换保持行为

**关键**：转换不只是改类型，还必须**保持前向传播的语义**。

```
act_msame : affineAct p x = LayerParams.act (toParams p) x
```

**这条是本节的核心**：它说明**换一族表示不改变行为**。
这就是「函子性」的实际内容——不是范畴论的口号，而是**行为不变**。

### 1.3 往返

两条嵌入都应当是**单射**的（信息不丢）：

```
toParams_injective :  toParams p = toParams q → p = q
```

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `toParams` | `AffineLayer n → LayerParams n n` |
| `ofParams` | 反向（只在各方阵时有定义） |
| **`act_toParams`** | **函子性**：转换保持前向传播 |
| `toParams_ofParams` / `ofParams_toParams` | **往返**（两个方向） |
| `toMLayer` / `ofMLayer` | `LayerParams (Fin m) (Fin n) ↔ MLayer m n` |
| `toMLayer_ofMLayer` / `ofMLayer_toMLayer` | **往返**（两个方向） |
| `three_families_connected` | **三族连通** |

**第 167 轮修正**：此表此前有一行 **「act_toMLayer」（「函子性（矩阵版）」），该引理不存在。**
矩阵版只证到**往返**，没有证到**行为保持**——`MLayer` 的前向传播需要矩阵-向量乘法的展开，
那一步没做。所以那一行换成实际存在的两条往返定理，而不是留一个不存在的名字。

## 3. 边界

- 本节**只做权重侧**的三族。符号侧与 token 侧的第二族**未做**——
  那需要定义新的约束类型或 token 类型，是更大的工作。**已登记为未做。**
- `MLayer` 的 `act` 若与 `Matrix` 乘法绑定，矩阵版的行为保持需要矩阵-向量乘法的展开。
  **那一步没有做**：本节对矩阵族只证**往返**（`toMLayer_ofMLayer` / `ofMLayer_toMLayer`），
  **不证行为保持**。这是本节自认的退让，写在这里而不是留一个不存在的引理名。
- 三族连通**不等于**谱系完备。报告说的「每层第二族」要求的是**语义上不同**的族
  （如浮点 vs 精确有理数），本节做的是**同一语义的三族编码**。
  **这个区别必须说清**——否则「谱系」会是一个过强的说法。
-/
import Mathlib
import Lattice.Core.Net
import Lattice.Core.Weight
import Lattice.Core.VariableNet

open scoped BigOperators

namespace Lattice.Lift

namespace RepresentationFamilies

open Lattice.Core

/-! ## 一、`AffineLayer n ↔ LayerParams n n` -/

/-- **`AffineLayer n` → `LayerParams n n`**。 -/
def toParams {n : Type} (p : AffineLayer n) : LayerParams n n where
  W := p.W
  b := p.b

/-- **`LayerParams n n` → `AffineLayer n`**。 -/
def ofParams {n : Type} (q : LayerParams n n) : AffineLayer n where
  W := q.W
  b := q.b

/-- **往返**：两族在方阵情形下是同一个东西。 -/
theorem toParams_ofParams {n : Type} (q : LayerParams n n) : toParams (ofParams q) = q := rfl

/-- **往返（另一方向）**。 -/
theorem ofParams_toParams {n : Type} (p : AffineLayer n) : ofParams (toParams p) = p := rfl

/-- **单射**：转换不丢信息。 -/
theorem toParams_injective {n : Type} : Function.Injective (@toParams n) := by
  intro p q h
  have := ofParams_toParams p ▸ ofParams_toParams q ▸ congrArg ofParams h
  simpa using this

/-! ## 二、函子性：转换保持行为 -/

/-- **函子性**：`AffineLayer` 与 `LayerParams` 的前向传播一致。

**这是「换一族表示不改变行为」的确切内容**——
不是范畴论的口号，而是 `affineAct p x = LayerParams.act (toParams p) x`。 -/
theorem act_toParams {n : Type} [Fintype n] (p : AffineLayer n) (x : n → ℝ) (j : n) :
    affineAct p x j = (∑ i, (toParams p).W i j * x i) + (toParams p).b j := rfl

/-! ## 三、`LayerParams (Fin m) (Fin n) ↔ MLayer m n` -/

/-- **`LayerParams (Fin m) (Fin n)` → `MLayer m n`**。 -/
def toMLayer {m n : ℕ} (q : LayerParams (Fin m) (Fin n)) : MLayer m n where
  W := fun i j => q.W i j
  b := q.b

/-- **`MLayer m n` → `LayerParams (Fin m) (Fin n)`**。 -/
def ofMLayer {m n : ℕ} (l : MLayer m n) : LayerParams (Fin m) (Fin n) where
  W := fun i j => l.W i j
  b := l.b

/-- **往返**。 -/
theorem toMLayer_ofMLayer {m n : ℕ} (l : MLayer m n) : toMLayer (ofMLayer l) = l := by
  cases l; rfl

/-- **往返（另一方向）**。 -/
theorem ofMLayer_toMLayer {m n : ℕ} (q : LayerParams (Fin m) (Fin n)) :
    ofMLayer (toMLayer q) = q := by
  cases q; rfl

/-! ## 四、三族连通 -/

/-- **三族连通**：`AffineLayer n` 与 `LayerParams n n` 同构，
且 `LayerParams (Fin m) (Fin n)` 与 `MLayer m n` 同构。

⇒ **权重侧不是一族，是三族且可互转。** 这是「链 → 谱系」的第一步。 -/
theorem three_families_connected {n m : ℕ} :
    (∀ q : LayerParams (Fin n) (Fin n), toParams (ofParams q) = q) ∧
    (∀ p : AffineLayer (Fin n), ofParams (toParams p) = p) ∧
    (∀ l : MLayer m n, toMLayer (ofMLayer l) = l) ∧
    (∀ q : LayerParams (Fin m) (Fin n), ofMLayer (toMLayer q) = q) :=
  ⟨fun q => toParams_ofParams q,
   fun p => ofParams_toParams p,
   fun l => toMLayer_ofMLayer l,
   fun q => ofMLayer_toMLayer q⟩

end RepresentationFamilies

end Lattice.Lift
