/-
# 一个具体的有损后端：整数取整压缩

## 0. 本节补什么

`Lattice.Slots` 的 `lift.extract.roundtrip` 的最后一句是：

> "What is STILL owed: a concrete lossy backend with `compile` genuinely non-injective,
> which needs a decision about what the loss measures."

本节给出那个后端，并做出那个决定。

## 1. 决定：损失度量取「提取误差」

有损有多种含义。本节选定**最可操作的一种**：

```
compile : ℤ → ℤ      x ↦ x / 2      （整数除法，向下取整）
extract : ℤ → ℤ      k ↦ 2 * k      （取代表元）
```

**损失**：`loss x = |extract (compile x) - x|`，本节证明 `loss x ≤ 1`。

| 性质 | 值 |
|:--|:--|
| `compile` 非单射（真实有损） | `2 / 2 = 1 = 3 / 2` |
| 往返误差有界 | `≤ 1` |
| 无界误差 | **不存在**（界是常数，与 `x` 无关） |

## 2. 为什么这是「有损后端」而不是玩具

三条都要，缺一不可：

1. **`compile` 真的丢信息**：`2` 与 `3` 映到同一个值。这是与
   `NonIdentical.pairRepresentation`（单射非满射）的**关键区别**——
   那里的 `compile` 是单射的，所以它其实无损。
2. **往返不能用等式**：`extract (compile 3) = 2 ≠ 3`。
3. **误差有界**：这是有损系统的**最低可用性要求**，而它需要证明。

## 3. 与既有结构的关系

`LossyRep` 的 `obs` 要求一个**自反关系**。本节的 `obs` 取

```
obs x y := |x - y| ≤ 1
```

它自反（`|x - x| = 0 ≤ 1`），并且**严格比 `Eq` 粗**（`2` 与 `3` 相关但不相等）。
于是这个后端是一个真正的 `LossyRep`，并且**不**来自任何 `Representation`。

## 4. 边界

- 本节只在 `ℤ` 上给出实例。推广到 `ℝ` 需要取整函数，那是不同的构造，
  且「损失」的含义会变（`ℝ` 上可以做到任意小）。**这是刻意的选择**：
  离散域上「取整」是真实的有损压缩，连续域上它只是近似。
- 损失用**绝对误差**，不是相对误差。对有界域，绝对误差是标准选择；
  对无界域（如 `ℤ`）它也在本节用得上，因为界与 `x` 无关。
- 本节**不**声称所有有损后端都形如取整。它给的是**一个**具体实例，
  从而证明「有损后端可以存在且可证」，而不是「所有有损后端如何构造」。
- 本节**不**把 `loss` 加进 `LossyRep` 结构——`obs` 已经能表达有界相关，
  再加一个数值字段会让结构变重而没有新信息。若将来需要数值，那是一次结构调整。
-/
import Mathlib
import Lattice.Runtime.LossyRepresentation

namespace Lattice.Lift

namespace RoundingBackend

/-! ## 一、编译与提取 -/

/-- **有损编译**：整数除以 2（向下取整）。

这不是单射：`2 / 2 = 1 = 3 / 2`。所以信息真的丢了。 -/
def compileZ (x : ℤ) : ℤ := x / 2

/-- **提取**：选代表元 `2 * k`。 -/
def extractZ (k : ℤ) : ℤ := 2 * k

/-- **`compile` 不是单射。** 这是「有损」的直接证据。 -/
theorem compileZ_not_injective : ¬ Function.Injective compileZ := by
  intro hinj
  have h : compileZ 2 = compileZ 3 := by decide
  have h23 : (2 : ℤ) = 3 := hinj h
  norm_num at h23

/-- **往返误差的上界是 1。** 这是有损系统的可用性保证。 -/
theorem roundtrip_error_le_one (x : ℤ) : |extractZ (compileZ x) - x| ≤ 1 := by
  unfold extractZ compileZ
  have h1 : 2 * (x / 2) ≤ x := by omega
  have h2 : x < 2 * (x / 2) + 2 := by omega
  rw [abs_le]
  constructor <;> omega

/-- **误差确实会达到 1**（对奇数），所以这个界是紧的。 -/
theorem roundtrip_error_eq_one (x : ℤ) (hodd : x % 2 ≠ 0) :
    extractZ (compileZ x) - x = -1 := by
  unfold extractZ compileZ
  have h2 : x < 2 * (x / 2) + 2 := by omega
  have h1 : 2 * (x / 2) ≤ x := by omega
  omega

/-! ## 二、观察关系 -/

/-- **有界相关**：两个整数相差不超过 1。

它自反，并且严格比等式粗（`2` 与 `3` 相差 1 但不相等）。 -/
def obsLeOne (x y : ℤ) : Prop := |x - y| ≤ 1

/-- `obsLeOne` 自反。 -/
theorem obsLeOne_refl (x : ℤ) : obsLeOne x x := by
  unfold obsLeOne
  simp

/-- `obsLeOne` 严格比等式粗。 -/
theorem obsLeOne_weaker : ∃ x y : ℤ, x ≠ y ∧ obsLeOne x y := by
  refine ⟨2, 3, by norm_num, ?_⟩
  unfold obsLeOne
  norm_num

/-! ## 三、这是一个 `LossyRep` -/

/-- **取整压缩是一个真正的有损表示。**

`compile` 非单射（有损），`obs` 取有界相关（比等式粗），
而 `semEq` 由 `roundtrip_error_le_one` 供给。

**它不来自任何 `Representation`**：`compile` 非单射，所以不存在左逆。 -/
def roundingLossy : LossyRepresentation.LossyRep ℤ ℤ where
  inputP := ℤ
  inputW := ℤ
  encode := id
  decode := id
  compile := compileZ
  extract := extractZ
  obs := obsLeOne
  obs_refl := obsLeOne_refl
  semEq := fun x => roundtrip_error_le_one x

end RoundingBackend

end Lattice.Lift
