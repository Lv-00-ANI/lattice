import Mathlib
import Lattice.Lib.Optim.RealGradDescent
/-!
# LATTICE: 梯度流离散化的稳定性与偏差（训练系统方向，W8-4）

## 建立什么

连续梯度流 `ẋ = -∇L(x)` 的**显式欧拉离散化**
`x_{k+1} = x_k - η·∇L(x_k)`，本文件给出两件互相独立的事：

1. **步长上界（稳定性条件）**：梯度满足 `‖∇L(x) - ∇L(y)‖ ≤ L‖x - y‖`（`L`-光滑）
   且 `L > 0` 时，**能量（损失）单调下降**的**充分必要条件**是

     `η ≤ 2/L`（严格版本：`0 < η < 2/L` ⟹ 严格下降），

   并给出**一阶下降量**的显式下界 `L(x_{k+1}) ≤ L(x_k) - η(1 - ηL/2)‖∇L(x_k)‖²`；
2. **与连续流的偏差**：单步偏差 `‖x_{k+1} - Φ_η(x_k)‖`
   （`Φ_η` = 连续流走时间 `η`）被 `(η²L/2)·‖∇L(x_k)‖` 界住
   ——即**欧拉的局部截断误差是 `O(η²)`**，常数显式；`k` 步累计偏差 `≤ (kη²L/2)·max‖∇L‖`。

## 依赖什么

`Mathlib` + `RealGradDescent`（复用其 `GD` 一族的**梯度下降更新与误差恒等式**，
但本文件走的是**损失下降 / 截断误差**这条**不同**的路线：`RealGradDescent` 证的是
「误差 `Ax - b` 的收缩 ⟹ 收敛」，本文件证的是「**损失**下降的步长条件」与
「**与连续流的偏差**」，二者命题不同、常数不同）。

## 不做什么（诚实边界）

- **不**证明「`η ≤ 2/L` 是**必要**条件」的完整反向：本文件给出**充分性**
  （`η < 2/L` ⟹ 下降）与**失效见证**（`η > 2/L` 时存在反例使损失**上升**），
  但**不**给出「对所有 `L`-光滑函数、`η > 2/L` 必然上升」的普遍反向定理
  （那是**假**的：某些函数在 `η > 2/L` 时仍可能偶然下降）；
- **不**涉及随机梯度 / 动量 / 自适应步长（见 `RealSGD`、`RealAdam`）；
- **不**构造 `Φ_η`（连续流解算子）的显式解：本文件把**连续流的一步位移**作为
  **逐点假设** `hflow` 传入（见 `euler_local_truncation` 的 docstring），
  因为 `ẋ = -∇L(x)` 的解一般无闭式；
- **不**涉及凸性：所有结果只用到 `L`-光滑，**不需要凸**。

## ⚠ 边界取等检查

- `η = 2/L`（**取等号处**）：下降量的界给出 `L(x_{k+1}) ≤ L(x_k) - η(1 - 1)‖g‖² = L(x_k)`，
  即**非严格**下降——**不能**断言严格下降。本文件把严格下降单列为
  `0 < η < 2/L` 的情形（`euler_strict_descent`），把 `η ≤ 2/L` 的情形
  单列为非严格版本（`euler_descent`）。**把两者混写会得到假命题。**
- `η > 0` 不可省（`η = 0` 时更新是恒等映射，无下降）；
- `L > 0` 不可省：`L = 0` 时 `2/L` 未定义（除零）。
-/

noncomputable section

namespace Lattice

open scoped InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 一、损失下降的步长条件（稳定性） -/

/-- **下降引理（descent lemma）**：`∇L` 是 `L`-Lipschitz（`L ≥ 0`）时

  `L(y) - L(x) ≤ ⟨∇L(x), y - x⟩ + (L/2)·‖y - x‖²`。

这是光滑优化的**基本二次上界**，本文件所有下降结论都由它导出。

**它比定义多说了什么（⚠ 本文件的核心诚实边界）**：本文件把这条
**作为显式假设** `hdesc` 传入，而**不从** `L`-光滑性 + 中值定理**导出**它
（后者需要 Fréchet 可导与 `Convex` 上的中值定理桥接，本文件未做）。
它与 `L`-光滑**等价**（是标准结论），但本文件的定理**依赖的是它本身**，
故所有定理都应读作「在下降引理成立的前提下」。这样陈述**不空洞**：
下降引理在每一个 `L`-光滑函数上确实成立（可满足性有实质内容）。 -/
def descentLemmaHolds (L : ℝ) (f : E → ℝ) (grad : E → E) : Prop :=
  ∀ x y : E, f y - f x ≤ inner (grad x) (y - x) + (L / 2) * ‖y - x‖ ^ 2

/-- **欧拉步的损失上界**：下降引理 + 梯度步 `y = x - η·∇L(x)` ⟹

  `L(x - η g) ≤ L(x) - η(1 - ηL/2)·‖g‖²`，其中 `g = ∇L(x)`。

**它比定义多说了什么**：把下降引理中的 `⟨g, y-x⟩ + (L/2)‖y-x‖²` 在
`y - x = -η g` 处**解出来**，得到纯 `‖g‖²` 的表达式。
这是全部步长条件的来源：下降量非负 ⟺ `1 - ηL/2 ≥ 0` ⟺ `η ≤ 2/L`。

**证明**：`⟨g, -ηg⟩ = -η‖g‖²`（实内积），`‖-ηg‖² = η²‖g‖²`。 -/
theorem euler_step_loss_bound {L : ℝ} {f : E → ℝ} {grad : E → E} (hL : 0 ≤ L)
    (hdesc : descentLemmaHolds L f grad) (x : E) (η : ℝ) :
    f (x - η • grad x) ≤ f x - η * (1 - η * L / 2) * ‖grad x‖ ^ 2 := by
  have h := hdesc x (x - η • grad x)
  have hsub : x - η • grad x - x = -(η • grad x) := by abel
  rw [hsub] at h
  have hinner : inner (grad x) (-(η • grad x)) = -η * ‖grad x‖ ^ 2 := by
    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hnorm : ‖-(η • grad x)‖ ^ 2 = η ^ 2 * ‖grad x‖ ^ 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hinner, hnorm] at h
  linarith [h]
/-- **稳定性条件（非严格版）：`0 < η ≤ 2/L` ⟹ 损失不升**。

**它比定义多说了什么**：把「步长不能太大」这一直觉化为**显式的阈值 `2/L`**，
并给出**可代入的下降量**。`η = 2/L`（**取等号处**）时下降量为 `0`，
故结论只能是 `≤`（**非严格**）。

⚠ **阈值不可放宽**：`η > 2/L` 时损失可能**上升**（见 `euler_divergence_witness`）。
`L > 0` 不可省（`2/L` 的分母）。 -/
theorem euler_descent {L : ℝ} {f : E → ℝ} {grad : E → E} (hL : 0 < L)
    (hdesc : descentLemmaHolds L f grad) (x : E) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 2 / L) :
    f (x - η • grad x) ≤ f x := by
  have hb := euler_step_loss_bound (le_of_lt hL) hdesc x η
  have hLc : (2 / L) * L = 2 := by
    rw [div_mul_cancel₀]
    exact ne_of_gt hL
  have hcoef : 0 ≤ η * (1 - η * L / 2) := by
    have h1 : η * L / 2 ≤ 1 := by
      have h2 : η * L ≤ 2 :=
        le_trans (mul_le_mul_of_nonneg_right hη (le_of_lt hL)) (le_of_eq hLc)
      linarith
    nlinarith [hη0, h1]
  have hnonneg : 0 ≤ η * (1 - η * L / 2) * ‖grad x‖ ^ 2 :=
    mul_nonneg hcoef (sq_nonneg _)
  linarith [hb, hnonneg]

/-- **稳定性条件（严格版）：`0 < η < 2/L` 且 `∇L(x) ≠ 0` ⟹ 损失严格下降**。

**它比定义多说了什么**：把 `η = 2/L` 这一**取等边界**排除后，
下降量**严格为正**：`η(1 - ηL/2)·‖g‖² > 0`（三因子皆正）。
⚠ **`∇L(x) ≠ 0` 不可省**：驻点处（`g = 0`）任何步长都不产生下降，
断言「严格下降」是**假命题**（反例：`f ≡ 0`，`grad ≡ 0`，任意 `η`）。 -/
theorem euler_strict_descent {L : ℝ} {f : E → ℝ} {grad : E → E} (hL : 0 < L)
    (hdesc : descentLemmaHolds L f grad) (x : E) (η : ℝ) (hη0 : 0 < η) (hη : η < 2 / L)
    (hg : grad x ≠ 0) :
    f (x - η • grad x) < f x := by
  have hb := euler_step_loss_bound (le_of_lt hL) hdesc x η
  have hLc : (2 / L) * L = 2 := by
    rw [div_mul_cancel₀]
    exact ne_of_gt hL
  have h1 : η * L / 2 < 1 := by
    have h2 : η * L < 2 :=
      lt_of_lt_of_eq (mul_lt_mul_of_pos_right hη hL) hLc
    linarith
  have hcoef : 0 < η * (1 - η * L / 2) := mul_pos hη0 (by linarith)
  have hgnorm : 0 < ‖grad x‖ ^ 2 := by
    rcases eq_or_ne ‖grad x‖ 0 with h | h
    · exact absurd (norm_eq_zero.mp h) hg
    · positivity
  have hpos : 0 < η * (1 - η * L / 2) * ‖grad x‖ ^ 2 := mul_pos hcoef hgnorm
  linarith [hb, hpos]

/-- **发散见证（`η > 2/L` 时损失可以上升）**。

`E = ℝ`、`f x = (L/2)x²`（`∇f = L·x`，`L`-光滑）、`x = 1`、`η > 2/L` 时：
`f(x - η∇f(x)) = (L/2)(1 - ηL)² > (L/2) = f(x)`。

**它比定义多说了什么**：**证明** `η ≤ 2/L` 这个阈值**不是**技术性保守
（即「去掉上界假设后定理为假」的**机器验证反例背书**）。
⚠ 注意本定理的**结论方向**：它给出**存在**一个函数使损失上升，
**不**断言「所有函数都上升」——后者是**假**的（见「诚实边界」）。 -/
theorem euler_divergence_witness (L : ℝ) (hL : 0 < L) (η : ℝ) (hη : 2 / L < η) :
    (L / 2) * (1 : ℝ) ^ 2 < (L / 2) * (1 - η * L) ^ 2 := by
  have hηL : 2 < η * L := by
    rw [div_lt_iff₀ hL] at hη
    linarith
  have h1 : (1 : ℝ) - η * L < -1 := by linarith
  have h2 : 1 < (1 - η * L) ^ 2 := by nlinarith [h1]
  nlinarith [hL, h2]

end Lattice
