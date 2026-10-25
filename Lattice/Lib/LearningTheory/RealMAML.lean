import Lattice.Lib.Convex.RealSubgradientDescent
import Lattice.Lib.Optim.RealStrongConvex
import Mathlib

/-!
# LATTICE: MAML 元学习的元梯度结构与一阶近似（FOMAML）偏差界

模型无关元学习（MAML）对每个任务做一步**任务内更新**，再在更新后的参数上求元梯度：

    θ' = innerUpdate θ α g = θ − α·∇L_task(θ)              （任务内）
    θ  ← outerUpdate θ β h = θ − β·∇_θ L_meta(θ')          （元更新）

**元梯度的链式法则**（Hessian 项）：

    ∇_θ L(θ') = (I − α·∇²L_task(θ))·∇_{θ'}L(θ')

一维形式即 `mamlGrad α H h = (1 − α·H)·h`，其中 `H = ∇²L_task(θ)`。
本文件把它作为**显式结构** `MAMLChainRule` 给出（不声称从微积分推出）。

## 主结果

1. **FOMAML 偏差界**（`first_order_maml`）：忽略二阶项得到 `fomamlGrad h = h`，则

       |∇MAML − ∇FOMAML| = α·|H|·|h| ≤ α·Λ·|h|      （|H| ≤ Λ）

   即一阶近似的偏差与步长 α、曲率上界 Λ 成正比。
2. **MAML vs 联合训练**（`maml_vs_joint`）：若元目标就是任务损失（h = ∇L_task(θ)），
   则 `|∇MAML − ∇联合| ≤ α·Λ·|∇L_task(θ)|`。
3. **元更新放大**（`maml_meta_step_bound`）：元更新一步对偏差放大 β 倍。
4. **元损失单步变化**（`maml_inner_step_bound`）：`|L(innerUpdate θ α g) − L θ| ≤ ΛL·α·|g|`。
5. **退化/回收**：`H = 0`（`fomaml_grad_eq_maml_zero_hessian`）或 `α = 0`
   （`firstOrderMAML_exact`）时 FOMAML 与 MAML 的元梯度精确相同。

## 诚实边界

- **完整的 MAML 收敛定理不做**。本文件只给元梯度的链式法则结构 + 一阶/二阶偏差的
  代数界；它不涉及任务分布的采样、元目标的光滑性/凸性，也不做 MAML 迭代的收敛分析。
- `H`（Hessian 项）与曲率界 Λ 是**显式假设**：一维模型中 `H` 直接作为实数出现，
  不从 `L_task` 的二阶导推出（那需要 `ContDiff` 与二阶 Fréchet 导数的形式化）。
- 一维参数与标量任务损失（与项目其它 Real* 文件同口径）。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、定义：任务内/元更新与元梯度 -/

/-- 任务内更新：`θ' = θ − α·g`（g = ∇L_task(θ)）。 -/
def innerUpdate (θ α g : ℝ) : ℝ := θ - α * g

/-- 元更新：`θ ← θ − β·h`（h = ∇_θ L_meta(θ')）。 -/
def outerUpdate (θ β h : ℝ) : ℝ := θ - β * h

/-- MAML 元梯度（链式法则，一维）：`(1 − α·H)·h`，`H = ∇²L_task(θ)`。 -/
def mamlGrad (α H h : ℝ) : ℝ := (1 - α * H) * h

/-- FOMAML 元梯度：忽略二阶项，`∇FOMAML = h`。 -/
def fomamlGrad (h : ℝ) : ℝ := h

/-- 元更新一步（MAML，含 Hessian 项）。 -/
def mamlMetaStep (θ β α H h : ℝ) : ℝ := outerUpdate θ β (mamlGrad α H h)

/-- 元更新一步（FOMAML，一阶近似）。 -/
def fomamlMetaStep (θ β h : ℝ) : ℝ := outerUpdate θ β (fomamlGrad h)

/-- **MAML 链式法则的显式结构**：`grad = (1 − α·H)·metaGrad`，
    其中 `alpha` 是任务内步长、`hessian` 是 `∇²L_task(θ)`、`metaGrad` 是 `∇_{θ'}L(θ')`。 -/
structure MAMLChainRule where
  alpha : ℝ
  hessian : ℝ
  metaGrad : ℝ
  grad : ℝ
  chain : grad = (1 - alpha * hessian) * metaGrad

/-! ## 二、链式法则与退化 -/

/-- **链式法则（纯代数重排）**：`mamlGrad α H h = h − α·(H·h)`。 -/
theorem maml_gradient_chain_rule (α H h : ℝ) :
    mamlGrad α H h = h - α * (H * h) := by
  unfold mamlGrad
  ring

/-- 由 `mamlGrad` 构造的链式法则结构。 -/
def mamlChainRuleOf (α H h : ℝ) : MAMLChainRule where
  alpha := α
  hessian := H
  metaGrad := h
  grad := mamlGrad α H h
  chain := rfl

/-- 任务内更新 = 一次次梯度下降步。 -/
lemma innerUpdate_eq_subgradient_step (θ α g : ℝ) :
    innerUpdate θ α g = subgradient_descent_step α θ g := rfl

/-- **Hessian 为零 ⟹ MAML = FOMAML**（精确回收）。 -/
theorem fomaml_grad_eq_maml_zero_hessian (α h : ℝ) :
    mamlGrad α 0 h = fomamlGrad h := by
  simp [mamlGrad, fomamlGrad]

/-- **步长为零 ⟹ MAML = FOMAML**（精确回收）。 -/
theorem firstOrderMAML_exact (H h : ℝ) :
    mamlGrad 0 H h = fomamlGrad h := by
  simp [mamlGrad, fomamlGrad]

/-! ## 三、FOMAML 偏差界（主结果） -/

/-- **一阶 MAML 偏差界**：`0 ≤ α`、`|H| ≤ Λ` ⟹
    `|∇MAML − ∇FOMAML| ≤ α·Λ·|h|`。 -/
theorem first_order_maml (α Λ H h : ℝ) (hα : 0 ≤ α) (hH : |H| ≤ Λ) :
    |mamlGrad α H h - fomamlGrad h| ≤ α * Λ * |h| := by
  have hval : (1 - α * H) * h - h = -(α * H * h) := by ring
  rw [mamlGrad, fomamlGrad, hval, abs_neg, abs_mul, abs_mul, abs_of_nonneg hα]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH hα) (abs_nonneg h)

/-- **MAML vs 联合训练**：元目标 = 任务损失（h = g）时
    `|∇MAML − ∇联合| ≤ α·Λ·|g|`。 -/
theorem maml_vs_joint (α Λ H g : ℝ) (hα : 0 ≤ α) (hH : |H| ≤ Λ) :
    |mamlGrad α H g - g| ≤ α * Λ * |g| := by
  have h := first_order_maml α Λ H g hα hH
  simpa [fomamlGrad] using h

/-- **元更新一步的偏差放大**：`|MAML 步 − FOMAML 步| ≤ β·(α·Λ·|h|)`。 -/
theorem maml_meta_step_bound (θ β α Λ H h : ℝ) (hβ : 0 ≤ β) (hα : 0 ≤ α)
    (hH : |H| ≤ Λ) :
    |mamlMetaStep θ β α H h - fomamlMetaStep θ β h| ≤ β * (α * Λ * |h|) := by
  have hval : mamlMetaStep θ β α H h - fomamlMetaStep θ β h
      = -(β * (mamlGrad α H h - fomamlGrad h)) := by
    unfold mamlMetaStep fomamlMetaStep outerUpdate
    ring
  rw [hval, abs_neg, abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left (first_order_maml α Λ H h hα hH) hβ

/-- **元损失单步变化**：`L` 以 ΛL 为 Lipschitz 常数 ⟹
    `|L(innerUpdate θ α g) − L θ| ≤ ΛL·α·|g|`。 -/
theorem maml_inner_step_bound (L : ℝ → ℝ) (ΛL α θ g : ℝ) (hα : 0 ≤ α)
    (hLip : ∀ a b : ℝ, |L a - L b| ≤ ΛL * |a - b|) :
    |L (innerUpdate θ α g) - L θ| ≤ ΛL * (α * |g|) := by
  have h := hLip (innerUpdate θ α g) θ
  have hd : |innerUpdate θ α g - θ| = α * |g| := by
    unfold innerUpdate
    have h1 : θ - α * g - θ = -(α * g) := by ring
    rw [h1, abs_neg, abs_mul, abs_of_nonneg hα]
  rwa [hd] at h

/-! ## 注：闭环语义
  任务内更新（innerUpdate）→ 元梯度链式法则（mamlGrad / MAMLChainRule /
  maml_gradient_chain_rule）→ 退化回收（fomaml_grad_eq_maml_zero_hessian /
  firstOrderMAML_exact）→ FOMAML 偏差界（first_order_maml）→
  MAML vs 联合训练（maml_vs_joint）→ 元更新放大（maml_meta_step_bound）→
  元损失单步界（maml_inner_step_bound）。
  诚实降级：完整 MAML 收敛定理不做；Hessian 项 H 与曲率界 Λ 为显式假设。 -/

end Lattice
