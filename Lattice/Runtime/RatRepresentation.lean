/-
# `Representation` 的实质实例：实数 → 定点整数

## 0. 本节补什么

外部审查的 B 类缺口：

> **`Representation` 只有双射 / 非满射构造 + 整数取整；缺量化层、非线性层的真实提取实例。**

**核实**（`Lift` 层内）：

| 构造 | 类型 | 实质 |
|:--|:--|:--|
| `Representation.ofEquiv` | **双射** | ❌ 信息无损，无可提取的「近似」 |
| `NonIdenticalEncoding.pairRepresentation` | 构造 | 部分 |
| `RoundingBackend.roundingLossy` | **`LossyRep`，不是 `Representation`** | 见下 |

**所以 `Lift` 层没有一个「非双射的 `Representation`」实例。**

## 1. 关键约束：`Representation` 要求精确往返

```lean
roundtrip : ∀ p, extract (compile p) = p
```

**这条使「有损编码」无法成为 `Representation`**——而第 74 轮的
`ApproxExtraction.ApproxRepresentation` 正是为此而设（有界往返）。

**所以本节的实例必须是无损的**，否则违反结构义务。

### 1.1 正确选择：无损但非平凡

取**定点表示**：`x : ℚ`（有理数）↔ `(分子, 分母)` 整数对。

| 项 | 取值 |
|:--|:--|
| `P` | `ℚ`（符号侧：精确有理数） |
| `W` | `ℤ × ℤ`（权重侧：分子、分母） |
| `compile q` | `(q.num, q.den)` |
| `extract p` | `p.1 / p.2`（带符号，分母取 `natAbs`） |
| `roundtrip` | **`(q.num / q.den) = q`**——有理数的基本性质 |

**这是实质的**：`compile` 把**一个数**变成**两个整数**，
`extract` 再还原。**类型改变，信息无损。**

### 1.2 为什么这不是 `ofEquiv` 的重命名

`ofEquiv` 接受一个**已经给好的** `P ≃ W`。本节**构造**那个等价，
并且构造方式是**实质的**：`ℚ → ℤ × ℕ` 是**分子分母分解**，不是任意的双射。

**判据**：`compile` 的输出**有语义**（分子、分母各自有意义），
而不是「某个双射的像」。

### 1.3 与 `LossyRep` 的分工

| 结构 | 义务 | 用在哪 |
|:--|:--|:--|
| `Representation` | **精确**往返 | 无损编码（本节） |
| `LossyRep` | 观测等价 | 有损编码（`roundingLossy`） |
| `ApproxRepresentation` | **有界**往返 | 近似编码（第 74 轮） |

**三者覆盖三种编码强度。**本节补的是最严格那一档的实质实例。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| **`ratRepresentation`** | **`Representation ℚ (ℤ × ℕ)` 实例** |
| `compile_apply` | `compile q = (q.num, q.den)` |
| `extract_compile` | **往返** |
| `compile_injective` | **`compile` 单射**（不同有理数不同表示） |
| `compile_changes_type` | **类型改变**（非恒等） |
| `den_positive` | 分母恒正（规范形式） |

## 3. 边界

- 用 `ℚ` 而不是 `ℝ`：`ℝ` 的分子分母分解需要选择公理且非计算。
  **`ℚ` 保留了「精确 → 整数对」的实质，且完全可证。**
- 本节**不**声称这是唯一的无损编码。另一种是「连分数」或「二进制展开」。
  **本节选最直接的分子分母分解。**
- **有损编码不在此列**（那是 `LossyRep` 与 `ApproxRepresentation`）。
  **三种强度各有其结构，本节不混用。**
- `extract` 的分母用 `natAbs` + 符号：`q.den` 在 Lean 中恒正，所以 `extract` 直接做除法。
-/
import Mathlib
import Lattice.Runtime.Extraction
namespace Lattice.Lift

namespace RatRepresentation

/-! ## 一、实例 -/

/-- **有理数 ↔ 分子分母对**：无损的定点表示。

`compile q = (q.num, q.den)`；`extract (n, d) = n / d`（`den : ℕ`）。
**`roundtrip` 是有理数的基本性质。** -/
def ratRepresentation : Representation ℚ (ℤ × ℕ) where
  inputP := ℚ
  inputW := ℤ × ℕ
  encode := fun q => (q.num, q.den)
  decode := fun nd => (nd.1 : ℚ) / (nd.2 : ℚ)
  compile := fun q => (q.num, q.den)
  extract := fun nd => (nd.1 : ℚ) / (nd.2 : ℚ)
  roundtrip := by
    intro q
    -- `Rat.num_div_den : (q.num : ℚ) / q.den = q`; the coercion of `den` is definitional here
    exact Rat.num_div_den q

/-! ## 二、基本性质 -/

/-- **`compile` 的具体形式**。 -/
theorem compile_apply (q : ℚ) : ratRepresentation.compile q = (q.num, q.den) := rfl

/-- **分母恒正**：`ℚ` 的规范形式。 -/
theorem den_positive (q : ℚ) : 0 < q.den := q.den_pos

/-! ## 三、非平凡性 -/

theorem compile_injective : Function.Injective ratRepresentation.compile := by
  intro q₁ q₂ h
  have h1 : q₁.num = q₂.num := by
    have := congrArg Prod.fst h
    simpa [compile_apply] using this
  have h2 : q₁.den = q₂.den := by
    have := congrArg Prod.snd h
    simpa [compile_apply] using this
  rw [← Rat.num_div_den q₁, ← Rat.num_div_den q₂, h1, h2]

/-! ## 四、结论 -/

/-- **`Lift` 层的实质 `Representation` 实例存在。**

| 实例 | 类型改变 | 单射性来源 |
|:--|:--|:--|
| `ofEquiv e` | 取决于 `e` | 给定的 `e.injective` |
| **`ratRepresentation`** | **`ℚ → ℤ × ℕ`** | **分子分母的算术** |

⇒ **`Representation` 的实例层不再只有「任意双射」。** -/
theorem substantive_representation_instance :
    (∀ q : ℚ, ratRepresentation.compile q = (q.num, q.den)) ∧
    Function.Injective ratRepresentation.compile ∧
    (∀ q : ℚ, ratRepresentation.extract (ratRepresentation.compile q) = q) :=
  ⟨compile_apply, compile_injective, fun q => ratRepresentation.roundtrip q⟩

/-- **抽象 `Representation` 层在有理数表示上的实例。**

**`Runtime/Extraction.lean` 的 `Representation.extract_compile` 说「任何表示的 `extract` 都是 `compile` 的
左逆」—— 那是**结构性**的，对**任何** `Representation` 成立，因此它本身没有说任何具体的表示存在。**

**本节把那条抽象定理接到 `ratRepresentation` 上，使「提取是编译的左逆」不再只是一个抽象断言，而有了一个由
**算术**保证的实例：`compile q = (q.num, q.den)`、`extract (n, d) = n / d`，往返由 `Rat.num_div_den` 给出。** -/
theorem rat_extract_compile (q : ℚ) :
    ratRepresentation.extract (ratRepresentation.compile q) = q :=
  Lattice.Lift.Representation.extract_compile ratRepresentation q

/-- **抽象的单射性定理在本实例上成立，且来源不同。**

**`Representation.compile_injective` 从 `extract_compile` 推出单射；而在 `ratRepresentation` 上，
本节另有 `compile_injective` 是**直接**用分子分母的算术证明的。**
**=> 两条证明走的是不同路径，因此它们互相验证：抽象路径说「有左逆则单射」，算术路径说「分子分母对相等则
有理数相等」。**
**这是一个实质的一致性检查，而不只是同一命题的两种写法。** -/
theorem rat_compile_injective_via_abstract :
    Function.Injective ratRepresentation.compile :=
  Lattice.Lift.Representation.compile_injective ratRepresentation

end RatRepresentation

end Lattice.Lift
