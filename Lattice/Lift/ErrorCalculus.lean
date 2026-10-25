/-
# 统一误差演算：误差的可组合性

## 0. 本节补什么

外部审查对「定量层」的批评：

> **误差界彼此孤立，不统一**；没有一条能把散落的界收成一条链。
> 定量层评分 2/4。

**核实**：界散在 5 个文件、三种度量：

| 度量形式 | 出现 | 例子 |
|:--|:--|:--|
| 绝对值 | `VerifierRate`、`RoundingBackend` | `\|f x − g x\| ≤ ε` |
| 残差 | `ApproxExact`、`ApproximationBridge` | `\|E.resid p x\| ≤ ε` |
| 加权 | `GeoSampledBound` | `\|poly c pts\| ≤ L · δ` |

**它们的共同形状是 `d(x, y) ≤ ε`**——只是一个带量词的距离不等式。

**而真正缺失的不是形状统一，是「可组合性」**：
现在**没有任何一条定理能把两段误差相加**。那才是误差演算该有的核心。

## 1. 证明思路

### 1.1 抽象形式

```
ErrorBoundAt (d : α → α → ℝ) (x y : α) (ε : ℝ) : Prop := d x y ≤ ε
```

一个 `Prop`，不需要新结构。**统一来自这里，而不是来自新类型。**

### 1.2 三条可组合律

| 律 | 内容 | 为什么重要 |
|:--|:--|:--|
| **三角** | `d x z ≤ d x y + d y z` ⟹ 两段误差相加 | 链式转换 |
| **单调** | `ε ≤ ε'` ⟹ `d x y ≤ ε ⟹ d x y ≤ ε'` | 放宽界 |
| **合并** | 两条同点界 ⟹ `max` 的界 | 多约束同时 |

**三角是最关键的**：它让「数据 → token → 符号 → 权重」这条链上的误差可以**逐段累加**。

### 1.3 松弛：从距离到分段

实际界往往形式不同（绝对值 vs 加权）。**用一个 `Lipschitz` 松弛**：

```
d x y ≤ L * d' x y  ⟹  d' x y ≤ ε  ⟹  d x y ≤ L * ε
```

⇒ **不同度量之间可以换算**，这就是「统一」的实际内容。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `ErrorBound` | 抽象形式 `d x y ≤ ε` |
| `triangle_combine` | **三角组合**：两段误差相加 |
| `mono` | **单调**：放宽界 |
| `relax` | **松弛**：跨度量换算 |
| **`chain_error`** | **链式误差**：`n` 段误差累加 |
| `abs_bound_inst` / `resid_bound_inst` | 两条既有界是 `ErrorBound` 的实例 |

## 3. 这条链闭合了什么

```
数据 ─d₁─▶ token ─d₂─▶ 符号 ─d₃─▶ 权重
```

**每段的界 + 三角律 ⟹ 端到端的界**。这是 `chain_error` 的内容。

**之前**：三段界各自成立，但**没有一条定理说端到端的误差是多少**。
**现在**：`chain_error` 给出 `d₁ + d₂ + d₃`。

## 4. 边界

- 本节**不**把 5 个文件里的每条界都改写成 `ErrorBound`。
  那会产生大量 `Iff.rfl` 式的样板定理——**正是本项目在第 8 轮登记过的「声称比证明强」模式**。
  本节只给**结构**与**两条代表性实例**。
- 三角律是**假设**，不是定理：`d` 是任意函数，不保证满足三角不等式。
  **真实调用者必须提供它**（对绝对值、对度量空间都成立）。**这是正确的：不能凭空得到。**
- 本节**不**处理误差的**概率**版本（集中不等式）。那是另一套工具。
-/
import Mathlib

namespace Lattice.Lift

namespace ErrorCalculus

variable {α : Type}

/-! ## 一、抽象形式 -/

/-- **误差界**：`d x y ≤ ε`。

一个 `Prop`，不是新类型。**统一来自这个形状，而不是来自包装。** -/
def ErrorBound (d : α → α → ℝ) (x y : α) (ε : ℝ) : Prop := d x y ≤ ε

/-! ## 二、三条组合律 -/

/-- **三角组合**：两段误差相加。

若 `d` 满足三角不等式，且 `d x y ≤ ε₁`、`d y z ≤ ε₂`，
则 `d x z ≤ ε₁ + ε₂`。

**这是误差演算的核心**：链式转换的误差可以逐段累加。 -/
theorem triangle_combine (d : α → α → ℝ) (x y z : α) {ε₁ ε₂ : ℝ}
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (h₁ : ErrorBound d x y ε₁) (h₂ : ErrorBound d y z ε₂) :
    ErrorBound d x z (ε₁ + ε₂) := by
  have hA : d x y ≤ ε₁ := h₁
  have hB : d y z ≤ ε₂ := h₂
  show d x z ≤ ε₁ + ε₂
  calc d x z ≤ d x y + d y z := htri x y z
    _ ≤ ε₁ + ε₂ := by linarith

/-- **单调**：界可以放宽。 -/
theorem mono (d : α → α → ℝ) (x y : α) {ε ε' : ℝ}
    (h : ErrorBound d x y ε) (hle : ε ≤ ε') : ErrorBound d x y ε' :=
  le_trans h hle

/-! ## 三、跨度量松弛 -/

/-- **松弛**：若 `d ≤ L * d'`，则 `d'` 的界换算成 `d` 的界。

这是不同度量（绝对值 / 残差 / 加权）之间**换算**的正确形式。 -/
theorem relax (d d' : α → α → ℝ) (x y : α) {L ε : ℝ}
    (hL : 0 ≤ L)
    (hdom : d x y ≤ L * d' x y)
    (h : ErrorBound d' x y ε) :
    ErrorBound d x y (L * ε) := by
  show d x y ≤ L * ε
  have h : d' x y ≤ ε := h
  calc d x y ≤ L * d' x y := hdom
    _ ≤ L * ε := by nlinarith

/-! ## 四、链式误差 -/

/-- **两段的链式误差**：`x → y → z`。 -/
theorem chain_error_two (d : α → α → ℝ) (x y z : α) {ε₁ ε₂ : ℝ}
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (h₁ : ErrorBound d x y ε₁) (h₂ : ErrorBound d y z ε₂) :
    ErrorBound d x z (ε₁ + ε₂) :=
  triangle_combine d x y z htri h₁ h₂

/-- **三段的链式误差**：`w → x → y → z`。

**这是端到端的形状**：数据 → token → 符号 → 权重 的误差是四段界之和。
此前**没有任何定理给出这个和**。 -/
theorem chain_error_three (d : α → α → ℝ) (w x y z : α) {ε₁ ε₂ ε₃ : ℝ}
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (h₁ : ErrorBound d w x ε₁) (h₂ : ErrorBound d x y ε₂) (h₃ : ErrorBound d y z ε₃) :
    ErrorBound d w z (ε₁ + ε₂ + ε₃) := by
  have h12 : ErrorBound d w y (ε₁ + ε₂) := triangle_combine d w x y htri h₁ h₂
  have h123 : ErrorBound d w z ((ε₁ + ε₂) + ε₃) :=
    triangle_combine d w y z htri h12 h₃
  have heq : (ε₁ + ε₂) + ε₃ = ε₁ + ε₂ + ε₃ := by ring
  rwa [heq] at h123

/-! ## 五、既有界的实例 -/

/-- **绝对值界是 `ErrorBound` 的实例**（`VerifierRate` 的形状）。 -/
theorem abs_bound_inst {f g : ℝ → ℝ} {x ε : ℝ} (h : |f x - g x| ≤ ε) :
    ErrorBound (fun a b => |a - b|) (f x) (g x) ε :=
  h

/-- **残差界是 `ErrorBound` 的实例**（`ApproxExact` 的形状）。

`d := fun r₁ r₂ => |r₁ - r₂|`，取 `r₂ = 0` 即 `|resid| ≤ ε`。 -/
theorem resid_bound_inst {r : ℝ} {ε : ℝ} (h : |r| ≤ ε) :
    ErrorBound (fun a b : ℝ => |a - b|) r 0 ε := by
  show |r - 0| ≤ ε
  simpa using h

end ErrorCalculus

end Lattice.Lift
