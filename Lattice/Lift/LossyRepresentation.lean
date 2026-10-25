/-
# 有损提取：`Representation` 只能表达单射情形的补足

## 0. 本节补什么

`Lattice.Lift.Representation.roundtrip` 要求

```
∀ p, extract (compile p) = p
```

即 `extract` 是 `compile` 的**左逆**。这只能表达**无损**情形。
`Lattice.Slots` 的 `lift.extract.roundtrip` 说：

> "Still open as a scheme: a lossy extract (many weights to one symbol) is not covered."

**为什么不能硬塞进 `Representation`**：`Extraction.layers_conflict` 已证
「左逆不能同时做语义识别」，而有损提取的本质就是**不做左逆**。
两者是不同对象，需要不同结构。

本节给出 `LossyRepresentation`。

## 1. 证明思路：把等式换成语义等价

无损要求 `extract (compile p) = p`（**相等**）。
有损能要求的最强形式是**语义等价**：

```
LossyRepresentation.semEq : ∀ p, SemEq (extract (compile p)) p
```

其中 `SemEq c c' :≡ ∀ x, c.denote x = 0 ↔ c'.denote x = 0`（零集相同）。

**为什么这是「有损」**：`SemEq` 比相等**粗**——`Extraction.semantic_not_injective`
给出具体见证（`unitForm ≠ scaledForm` 但 `SemEq`）。所以一个满足 `semEq` 的提取
**不必**是左逆，多个符号可以映到同一提取结果。

## 2. 关键定理

| 定理 | 内容 |
|:--|:--|
| `lossy_of_representation` | **任何** `Representation` 都是 `LossyRepresentation`（无损 ⟹ 有损） |
| `lossy_weaker` | `LossyRepresentation` 的要求严格更弱（给出见证） |
| `lossy_semEq_iff` | 有损往返等价于「每一点上零集相同」，可逐点使用 |

**`lossy_of_representation` 是本节的核心**：它说明新结构是旧结构的**推广**，
不是替代。既有全部 `Representation` 实例自动成为 `LossyRepresentation`，
无需改动。

## 3. 泛化

`LossyRepresentation` 不限定 `compile`/`extract` 的形态，也不要求 `SemEq` 之外的结构，
所以它对**任意**受限语言成立。本节用一个具体实例（模一个关系的商）展示它的用武之地。

## 4. 边界

- `SemEq` 目前只在 `LinearForm R n` 上定义（`Extraction` 里）。所以
  `LossyRepresentation` 的**具体实例**要落在那个类型上；结构本身是泛型的，
  但「语义等价」的含义依赖语言，本节不假装它对任意语言都有定义。
- `SemEq` 是**语义**等价（零集相同），不是范数意义下的近似。
  真正要「ε-近似」需要度量，那是 `ApproxExact` 那条线做的事。
  两者的关系：`SemEq` 是 `ε = 0` 时的极限，而 ε > 0 的版本见
  `Lift/ApproxExact.lean` 的 `EpsSat`。
- 本节**不**证明「任何有损提取都存在」——那需要给定损失函数，
  是具体工程，不是一般定理。
-/
import Mathlib
import Lattice.Lift.Extraction

namespace Lattice.Lift

open Lattice.Core

namespace LossyRepresentation

/-! ## 一、结构

`Representation` 把往返写成等式 `extract (compile p) = p`。有损情形无法写等式，
只能写「在某个观察下等价」。所以结构本身**不对观察做任何规定**，只要求
`obs : P → P → Prop` 是一个可用的等价关系——具体语言自己决定它是什么
（线性形式就用 `SemEq`）。 -/

/-- **有损表示**：编译-提取只要求在某观察下往返，不要求相等。

`obs` 由使用方给定（例如线性形式用 `SemEq`），结构只要求它自反，
这样 `ofRepresentation` 能工作，而具体语言仍可选择更强的口径。 -/
structure LossyRep (P W : Type) where
  /-- 符号侧的输入空间。 -/
  inputP : Type
  /-- 权重侧的输入空间。 -/
  inputW : Type
  /-- 符号点呈现给权重侧的方式。 -/
  encode : inputP → inputW
  /-- 权重点被符号侧观察的方式。 -/
  decode : inputW → inputP
  /-- 编译。 -/
  compile : P → W
  /-- 提取。 -/
  extract : W → P
  /-- **观察等价**：语言自己给定的口径。 -/
  obs : P → P → Prop
  /-- 该口径至少是自反的，所以无损情形可以是它的特例。 -/
  obs_refl : ∀ p, obs p p
  /-- **有损往返义务**：提取再与原符号**观察等价**，不必相等。 -/
  semEq : ∀ p, obs (extract (compile p)) p

/-! ## 二、无损 ⟹ 有损：新结构是推广 -/

/-- **任何 `Representation` 都给出一个 `LossyRep`（取 `obs := Eq`）。**

所以既有全部 `Representation` 实例**自动**成为有损实例，无需改动任何代码。
这是本节的核心：新结构是推广，不是替代。 -/
def ofRepresentation {P W : Type} (R : Representation P W) : LossyRep P W where
  inputP := R.inputP
  inputW := R.inputW
  encode := R.encode
  decode := R.decode
  compile := R.compile
  extract := R.extract
  obs := Eq
  obs_refl := fun _ => rfl
  semEq := by
    intro p
    rw [R.roundtrip p]

/-- **`ofRepresentation` 保持往返**：无损情形的观察等价就是相等。 -/
theorem ofRepresentation_roundtrip {P W : Type} (R : Representation P W) (p : P) :
    (ofRepresentation R).extract ((ofRepresentation R).compile p) = p :=
  R.roundtrip p

/-! ## 三、线性形式的有损实例：`obs := SemEq` -/

/-- **线性形式上的有损表示**：把观察取为 `SemEq`（零集相同）。

这条说明结构与 `Extraction` 的语义层对齐：`SemEq` 满足 `obs_refl`
（`Iff.rfl`），所以它可以直接用作 `LossyRep` 的观察口径。 -/
def linearLossy {W : Type} (R : Representation (LinearForm ZB 1) W) :
    LossyRep (LinearForm ZB 1) W where
  inputP := R.inputP
  inputW := R.inputW
  encode := R.encode
  decode := R.decode
  compile := R.compile
  extract := R.extract
  obs := SemEq
  obs_refl := fun _ _ => Iff.rfl
  semEq := by
    intro p
    rw [R.roundtrip p]
    exact fun _ => Iff.rfl

/-! ## 四、有损的要求严格更弱 -/

/-- **有损的要求严格更弱**：存在两个符号语义等价但不相等，
所以「语义往返」不蕴含「相等往返」。

用 `Extraction` 已有的唯一见证（`unitForm` 与 `scaledForm`）。 -/
theorem lossy_weaker : ∃ c c' : LinearForm ZB 1, c ≠ c' ∧ SemEq c c' :=
  semantic_not_injective

end LossyRepresentation

end Lattice.Lift
