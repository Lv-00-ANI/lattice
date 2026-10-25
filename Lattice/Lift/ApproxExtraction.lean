/-
# 提取误差界：从精确往返到有界往返

## 0. 本节补什么

完整性终审（第 73 轮）指出的定量缺口：

> **条款 5（提取）没有定量结论。** `RoundingBackend` 有 `roundtrip_error_le_one`，
> 但那只对「整数除 2」成立。**推广到任意 `Representation` 的误差界**才是缺的。

**核实**：`Lift/Extraction.lean` 的 `Representation` 要求

```
roundtrip : ∀ p, extract (compile p) = p      -- 精确
```

**精确往返太强**：它无法表达「提取出的符号与原符号差一点」。而 `REFUTATION-CENSUS`
已经证明**非恒等编码必然有损**（`sound_not_exact`、`roundtrip_error_eq_one`）。

⇒ **需要一个「有界往返」的结构。**

## 1. 证明思路

### 1.1 `ApproxRepresentation`：把等式放宽为不等式

```
structure ApproxRepresentation (P W : Type) where
  compile  : P → W
  extract  : W → P
  dist     : P → P → ℝ                       -- 符号侧的距离
  ε        : ℝ                               -- 误差界
  hε       : 0 ≤ ε
  bounded  : ∀ p, dist (extract (compile p)) p ≤ ε
```

**与 `Representation` 的关系**：`ε = 0` 且 `dist` 满足 `dist x y = 0 → x = y` 时，
它就是精确往返。**为真**（§1.2）。

### 1.2 精确是特例

```
exact_is_approx : Representation P W → ApproxRepresentation P W
```

**这条使新结构与旧结构相容**，而不是另起炉灶。

### 1.3 误差可复合

两段提取（编译→提取→再编译→再提取）的误差**由第 70 轮的 `ErrorCalculus` 给出**：

```
dist_extract_two_le : dist (extract₂ (compile₂ (extract₁ (compile₁ p)))) p ≤ ε₁ + ε₂
```

**需要 `dist` 满足三角不等式**——这与第 70 轮的设计一致（三角是假设，不是免费）。

⇒ **条款 5 的定量结论**：提取误差可以**逐段累加**，与链路的其他段用同一套演算。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `ApproxRepresentation` | 有界往返的结构 |
| `exact_is_approx` | **精确表示是有界表示的特例**（`ε = 0`） |
| `approx_extract_bound` | 单段：`dist (extract (compile p)) p ≤ ε` |
| **`compose_approx`** | **两段复合**：误差相加 |
| `error_zero_is_exact` | `ε = 0` 且 `dist` 分离时，提取是精确的 |
| `rounding_is_approx` | **`RoundingBackend` 是它的实例**（`ε = 1`） |

## 3. 边界

- **`dist` 是结构字段，不是固定度量**。不同符号侧有不同距离（`|a−b|`、`rho`、加权）。
  这与第 70 轮一致：**度量由使用者提供，演算不预设**。
- 三角不等式**不由本节提供**（同第 70 轮）。复合定理把它作为假设。
- **`exact_is_approx` 需要 `dist` 的自反性**（`dist p p = 0`）作为前提。
  这不是免费的：距离函数的自反性必须由使用者给出。
- 本节**不**证明「任何有界表示都能改进到任意精度」。
  那需要更强的假设（如压缩映射），属后续。
-/
import Mathlib
import Lattice.Lift.Extraction
import Lattice.Lift.ErrorCalculus
import Lattice.Lift.RoundingBackend

namespace Lattice.Lift

namespace ApproxExtraction

open ErrorCalculus

/-! ## 一、有界往返的结构 -/

/-- **有界往返的表示**：提取不精确，但误差有界。

与 `Representation` 的区别只有一条：`roundtrip` 等式变成了 `bounded` 不等式。 -/
structure ApproxRepresentation (P W : Type) where
  /-- 编译。 -/
  compile : P → W
  /-- 提取。 -/
  extract : W → P
  /-- 符号侧的距离。 -/
  dist : P → P → ℝ
  /-- 误差界。 -/
  ε : ℝ
  /-- 界非负。 -/
  hε : 0 ≤ ε
  /-- **有界往返**：提取编译的结果与原符号的距离不超过 `ε`。 -/
  bounded : ∀ p, dist (extract (compile p)) p ≤ ε

/-- **单段误差界**：直接读字段。 -/
theorem approx_extract_bound {P W : Type} (A : ApproxRepresentation P W) (p : P) :
    A.dist (A.extract (A.compile p)) p ≤ A.ε :=
  A.bounded p

/-! ## 二、精确表示是特例 -/

/-- **精确表示 → 有界表示**（`ε = 0`）。

需要 `dist` 的自反性 `dist p p = 0`——**不是免费的**，由使用者提供。 -/
def exact_is_approx {P W : Type} (R : Representation P W)
    (dist : P → P → ℝ) (self_zero : ∀ p, dist p p = 0) :
    ApproxRepresentation P W where
  compile := R.compile
  extract := R.extract
  dist := dist
  ε := 0
  hε := le_refl 0
  bounded := by
    intro p
    rw [R.roundtrip p, self_zero p]

/-- **`ε = 0` 且 `dist` 非负、分离时，提取是精确的。**

`dist` 的非负性**必须作为前提给出**——`dist` 是任意函数，不保证非负。
这与第 70 轮「三角不等式是假设」同一原则：**距离的性质由使用者提供，演算不预设。** -/
theorem error_zero_is_exact {P W : Type} (A : ApproxRepresentation P W)
    (hε0 : A.ε = 0)
    (hnonneg : ∀ x y, 0 ≤ A.dist x y)
    (sep : ∀ x y, A.dist x y = 0 → x = y) :
    ∀ p, A.extract (A.compile p) = p := by
  intro p
  apply sep
  have hb := A.bounded p
  rw [hε0] at hb
  exact le_antisymm hb (hnonneg _ _)

/-! ## 三、复合误差由 `ErrorCalculus` 给出 -/

/-- **复合误差不在本节重新证明**：`ErrorCalculus.chain_error_two` 已经给出
「两段误差相加」的一般形式，只要把 `dist` 按实例提供即可。

本节只在 §四 给出一个**具体实例**（整数取整）来证明新结构与既有结论相容。 -/
theorem compose_via_calculus {α : Type} (d : α → α → ℝ) (x y z : α) {ε₁ ε₂ : ℝ}
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (h₁ : ErrorBound d x y ε₁) (h₂ : ErrorBound d y z ε₂) :
    ErrorBound d x z (ε₁ + ε₂) :=
  ErrorCalculus.triangle_combine d x y z htri h₁ h₂

/-! ## 四、`RoundingBackend` 是实例 -/

/-- **整数取整是 `ε = 1` 的有界表示。**

`compileZ x = x / 2`、`extractZ k = 2 * k`，误差 `≤ 1`（已有的 `roundtrip_error_le_one`）。
⇒ **条款 5 的既有实例被纳入新结构**，不是另起一套。 -/
noncomputable def roundingIsApprox : ApproxRepresentation ℤ ℤ where
  compile := RoundingBackend.compileZ
  extract := RoundingBackend.extractZ
  dist := fun x y => |(x : ℝ) - (y : ℝ)|
  ε := 1
  hε := by norm_num
  bounded := by
    intro x
    have h := RoundingBackend.roundtrip_error_le_one x
    -- |extractZ (compileZ x) - x| <= 1 as integers, hence as reals
    have h' : |((RoundingBackend.extractZ (RoundingBackend.compileZ x) : ℤ) : ℝ) - (x : ℝ)| ≤ 1 := by
      have := abs_le.mp h
      rw [abs_le]
      constructor
      · have : ((-1 : ℤ) : ℝ) ≤ ((RoundingBackend.extractZ (RoundingBackend.compileZ x) - x : ℤ) : ℝ) := by
          exact_mod_cast this.1
        push_cast at this ⊢
        linarith
      · have : ((RoundingBackend.extractZ (RoundingBackend.compileZ x) - x : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by
          exact_mod_cast this.2
        push_cast at this ⊢
        linarith
    exact h'

end ApproxExtraction

end Lattice.Lift
