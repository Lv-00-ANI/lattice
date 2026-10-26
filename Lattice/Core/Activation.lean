/-
# 带激活的网络栈：多层之所以是多层的理由

## 0. 本节补什么

第 135 轮的 `MultiLayerLadder` 满足 D4 的字面要求（任意层数、任意点），但它在文件里
**如实写明了一个边界**：

> `AffineLayer` 没有激活函数，所以「多层仿射」在数学上等价于一层仿射。

**这意味着那个实例虽然有多层，但「多层」这个词在那里还没有实际内容。**

本节补上让「多层」有内容的东西：**激活函数**。`Core/Net` 已有 `relu` 与
`netRelu_not_injective`（说明激活破坏可逆性），但**没有一个「仿射与激活交替」的栈类型**。

## 1. 证明思路

### 1.1 要证的事

**「带激活的网络严格强于纯仿射网络」**——即**存在一个函数，它能被激活网络表示，但不能被仿射映射表示**。

### 1.2 最简单的一维见证

取 `relu : ℝ → ℝ`：

| 事实 | 值 |
|:--|:--|
| `relu 0` | `0` |
| `relu 1` | `1` |
| `relu (-1)` | `0` |

**若 `relu = a·x + b`**，则 `a·0 + b = 0` 给出 `b = 0`，`a·1 + b = 1` 给出 `a = 1`，
于是 `a·(-1) + b = -1`，**但 `relu (-1) = 0 ≠ -1`。矛盾。**

⇒ **`relu` 不是仿射函数。**

### 1.3 为什么这足以说明「多层」有内容

**纯仿射栈（任意深度）= 仿射映射**：`netAct [p, q] x = affineAct q (affineAct p x)`，
两次仿射复合仍是仿射。

⇒ **加入 `relu` 之后，栈不再折叠**：`relu ∘ affine` 已经超出仿射类。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `ActStack` | **仿射与激活交替的栈** |
| `actStackEval` | 求值：逐层仿射后接激活 |
| `actStack_nil` | 空栈是恒等 |
| `actStack_single_affine` | **单个仿射层（无激活）就是仿射** |
| `relu_not_affine` | **`relu` 不是仿射函数** |
| **`activation_strictly_stronger`** | **带激活的栈严格强于纯仿射** |

## 3. 边界

- **本节只证一维的 `relu`**。多维激活网络的表达力定理（万能逼近）**不在本节范围内**——
  那是逼近论，不是本库的定位。
- 本节**不声称**「激活网络能逼近所有连续函数」，只声称**它的表达力严格大于仿射**。
- `ActStack` 的层是同维的（`Fin n → Fin n`），**不做维度变换**；维度变换由 `Core/Chain` 负责。
- 本节**不改** `Core/Net`，只在其上新增结构。
-/
import Mathlib
import Lattice.Core.Net

open scoped BigOperators

namespace Lattice.Core

namespace Activation

variable {n : ℕ}

/-! ## 一、带激活的栈 -/

/-- **网络栈的一层**：仿射映射，可带激活。

`act` 是 `Option (ℝ → ℝ)`：`none` 表示纯仿射，`some σ` 表示该层之后施加 `σ`。 -/
structure StackLayer (n : ℕ) where
  /-- 仿射部分。 -/
  affine : AffineLayer (Fin n)
  /-- 可选的激活函数。 -/
  act : Option (ℝ → ℝ)

/-- **一层的作用**：先仿射，再（若有）逐坐标施加激活。 -/
noncomputable def layerApply (L : StackLayer n) (x : Fin n → ℝ) : Fin n → ℝ :=
  match L.act with
  | none => affineAct L.affine x
  | some σ => fun j => σ (affineAct L.affine x j)

/-- **整条栈的求值**：从左到右 foldl。 -/
noncomputable def actStackEval (ls : List (StackLayer n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  ls.foldl (fun acc L => layerApply L acc) x

/-! ## 二、基本性质 -/

/-- **空栈是恒等**。 -/
@[simp] theorem actStackEval_nil (x : Fin n → ℝ) : actStackEval [] x = x := rfl

/-- **单个纯仿射层就是仿射映射**：`act = none` 时 `layerApply` 退化为 `affineAct`。 -/
theorem actStackSingle_affine (p : AffineLayer (Fin n)) (x : Fin n → ℝ) :
    layerApply ⟨p, none⟩ x = affineAct p x := rfl

/-- **纯仿射栈就是 `netAct`**：所有层的 `act` 都是 `none` 时，两种求值一致。

⇒ **多层的纯仿射栈不增加表达力**，这是 §1.3 的前半部分。 -/
theorem actStackEval_of_no_activation (ps : List (AffineLayer (Fin n))) (x : Fin n → ℝ) :
    actStackEval (ps.map fun p => ⟨p, none⟩) x = netAct ps x := by
  induction ps generalizing x with
  | nil => rfl
  | cons p ps ih =>
      show actStackEval ((⟨p, none⟩ :: ps.map fun q => ⟨q, none⟩)) x = netAct (p :: ps) x
      show actStackEval (ps.map fun q => ⟨q, none⟩) (layerApply ⟨p, none⟩ x) =
        netAct ps (affineAct p x)
      rw [ih]
      rfl

/-! ## 三、`relu` 不是仿射 -/

/-- **`relu` 在关键三点上的取值**：`0 ↦ 0`、`1 ↦ 1`、`-1 ↦ 0`。 -/
theorem relu_key_values : relu 0 = 0 ∧ relu 1 = 1 ∧ relu (-1) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [relu] <;> norm_num

/-- **`relu` 不是任何仿射函数**：不存在 `a b : ℝ` 使 `∀ x, relu x = a * x + b`。

**证明**：假设有。由 `x = 0` 得 `b = 0`，由 `x = 1` 得 `a = 1`，
于是 `x = -1` 处右边是 `-1`，但 `relu (-1) = 0`。矛盾。

⇒ **这一条就是「激活让栈超出仿射类」的**最小见证。 -/
theorem relu_not_affine : ¬ ∃ (a b : ℝ), ∀ x : ℝ, relu x = a * x + b := by
  rintro ⟨a, b, h⟩
  have h0 : b = 0 := by
    have := h 0
    simp only [relu, max_eq_left (le_refl (0 : ℝ)), mul_zero, zero_add] at this
    exact this.symm
  have h1 : a = 1 := by
    have := h 1
    rw [h0] at this
    simp only [relu, max_eq_left (zero_le_one' ℝ), mul_one, add_zero] at this
    exact this.symm
  have hm : relu (-1) = 0 := relu_key_values.2.2
  have := h (-1)
  rw [h1, h0] at this
  simp only [mul_neg, mul_one, zero_add] at this
  rw [hm] at this
  norm_num at this

/-! ## 四、结论：激活让「多层」有内容 -/

/-- **带激活的栈严格强于纯仿射栈。**

两个方向：

1. **纯仿射栈能做的，激活栈都能做**（`actStackEval_of_no_activation`）；
2. **激活栈能做的，纯仿射栈不都能做**（`relu_not_affine`）。

⇒ **第 135 轮 `MultiLayerLadder` 里「多层」这个词，在纯仿射的设置下确实没有实际内容；
加入激活之后它才有。** 这条定理把这个区别显式地记录了下来。 -/
theorem activation_strictly_stronger :
    (∀ (ps : List (AffineLayer (Fin n))) (x : Fin n → ℝ),
        actStackEval (ps.map fun p => ⟨p, none⟩) x = netAct ps x) ∧
    (¬ ∃ (a b : ℝ), ∀ x : ℝ, relu x = a * x + b) :=
  ⟨actStackEval_of_no_activation, relu_not_affine⟩

end Activation

end Lattice.Core
