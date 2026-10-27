/-
# 约束损失的下降：把「训练降低约束损失」变成定理（M2-1 的闭环）

## 0. 上一轮之后缺的那一环

第 199 轮交付了 `netLoss : params → 约束表 → 配置 → ℝ`，它**真的依赖参数**。但——

> **没有任何东西在最小化它。**

「约束损失」若不能被训练降低，就只是一个函数。本节把**下降**证出来。

## 1. 为什么先做线性约束这一例

`netLoss` 的一般形状是 `∑ penaltyLoss c (netAct params ·)`，
其中 `params` 是 `List (AffineLayer (Fin n))`。要给**一般**情形证下降，需要
`netLoss` 在参数空间上的可微性 + Lipschitz 梯度——而参数空间是**层的列表**，
库里没有它的赋范向量空间结构。**那是独立的一块（M2-2 反向传播）。**

本节做的是**能完整证出来的最小闭环**：一条 `eqZero` 线性约束。
这时残差是参数（层的偏置 `β`）的**仿射函数**，损失是它的**平方**，
于是下降是**纯代数**，而且**更新真的作用在参数上**（改 `β`，不是改残差）。

**这不是回避一般情形，是把能闭环的那一例闭环到底。** 一般情形需要什么写在 §4。

## 2. 具体形状

固定 `n = 1` 的层：

```lean
shiftLayer β : AffineLayer (Fin 1)   -- W := 0, b := fun _ => β
```

于是 `netAct [shiftLayer β] x = fun _ => β`（零点偏置、单层），
而约束 `eqZero (.add (.coord 0 0) (.const c))` 在输出配置上的残差是 **`β + c`**。

`netLoss [shiftLayer β] [该约束] pts = (β + c)²`。

**梯度步**：`d/dβ (β+c)² = 2(β+c)`，所以

```lean
step η β := β - η * (2 * (β + c))
```

于是 `loss (step η β) = (1 - 2η)² * loss β`。

## 3. 交付

| 声明 | 内容 |
|:--|:--|
| `shiftLayer` | `W = 0`、`b = β` 的单层 |
| `shiftLayer_netAct` | 它把任何点送到常值 `β` |
| `linearConstraint` | `eqZero (coord + c)` |
| **`netLoss_shiftLayer`** | **`netLoss = (β + c)²`**（损失是参数的显式二次函数） |
| `step` | 梯度步 `β ↦ β - 2η(β+c)` |
| **`netLoss_step`** | **`loss (step η β) = (1−2η)² · loss β`** |
| **`netLoss_step_le`** | **`0 < η < 1` 时损失不增**（`(1−2η)² ≤ 1`） |
| **`netLoss_step_pow`** | **`k` 步后 `loss = (1−2η)^{2k} · loss₀`** |
| **`netLoss_step_tendsto`** | **`|1−2η| < 1` 时损失趋于零** |
| **`constraint_eventually_holds`** | **闭环：损失趋于零 ⟹ 约束最终成立** |

## 4. 一般情形需要什么（明说，不含糊）

要把本节推广到 `List (AffineLayer (Fin n))` 与 12 个构造子，需要：

1. **参数空间上的向量空间结构与可微性**：`List (AffineLayer (Fin n))` 的坐标表示，
   以及 `netLoss` 对它的 `HasFDerivAt`；
2. **`penaltyLoss` 的光滑性**：`(max e 0)²` 在 `e = 0` 处不 `C¹`，
   所以 `leZero`/`ltZero` 需要次梯度或光滑化（hinge 的平方）；
3. **下降引理**（`L`-smooth ⟹ `f(x − η∇f) ≤ f(x) − η(1 − Lη/2)‖∇f‖²`），
   那需要中值定理/泰勒展开在 `Fin n → ℝ` 上。

**这三样都不是「补一条引理」。** 本节因此只做能闭环的那一例，并把这三条写在上面。

## 5. 边界

- **`n = 1`**：单坐标。`n` 维的推广是逐坐标独立求和，但本节不做。
- **单条约束**：`netLoss_append`（第 199 轮）说明多条约束的损失是各自之和，
  但各条的下降步不同（不同坐标/不同 `η`），**合起来需要联合更新**，本节不做。
- **`η` 是假设**（`0 < η < 1`），不是导出的。**学习率没有理论能定**——本节只说
  「在这个区间内损失不增」，不说「这个区间是最优的」。
- **本节不声称收敛速率最优**：`(1−2η)²` 是**精确**的每步因子（不是界），
  而最优步长 `η = 1/2` 给零损失一步到位——那是二次函数的性质，推广不到一般损失。
- 本节**不改** `Geo/NetLoss.lean`、`Geo/PenaltyLoss.lean`。
-/
import Mathlib
import Lattice.Core.Net
import Lattice.Geo.Constraint
import Lattice.Geo.PenaltyLoss
import Lattice.Geo.NetLoss

namespace Lattice.Geo.ConstraintDescent

open Lattice.Core Lattice.Geo Lattice.Geo.PenaltyLoss Lattice.Geo.NetLoss

/-! ## 一、把参数的影响压到一个偏置上 -/

/-- **只改偏置的层**：`W = 0`、`b = β`。

单层、零权重 ⟹ 它把**任何**输入送到常值 `β`。这让「改参数」对输出的影响是**恒等位移**，
因此损失对参数的依赖是显式的、可算的。 -/
noncomputable def shiftLayer (β : ℝ) : AffineLayer (Fin 1) where
  W := fun _ _ => 0
  b := fun _ => β

/-- **`shiftLayer` 把一切送到 `β`。** -/
theorem shiftLayer_netAct (β : ℝ) (x : Pt 1) :
    netAct [shiftLayer β] x = fun _ => β := by
  funext j
  show affineAct (shiftLayer β) x j = β
  unfold affineAct shiftLayer
  simp

/-- **一条线性约束**：`z + c = 0`，其中 `z` 是第 0 个点的第 0 个坐标。 -/
noncomputable def linearConstraint (c : ℝ) : GeoConstraint 1 :=
  .eqZero (.add (.coord 0 0) (.const c))

/-- **损失是参数的显式二次函数**：`netLoss [shiftLayer β] [线性约束] pts = (β + c)²`。

**这是本节的关键式子**：它把「跑网络再判约束」这一步算穿成 `β` 的二次式，
于是后面所有下降论证都是纯代数。 -/
theorem netLoss_shiftLayer (β c : ℝ) (pts : ℕ → Pt 1) :
    netLoss [shiftLayer β] [linearConstraint c] pts = (β + c) ^ 2 := by
  -- `penaltyLoss (.eqZero e) X` is definitionally `(e.evalPts X)^2`, so `unfold` is not needed:
  -- the `match` reduces by the equation lemma. Doing `unfold` here would leave the match unreduced.
  have hpay : penaltyLoss (.eqZero (.add (.coord 0 0) (.const c)))
      (fun k => netAct [shiftLayer β] (pts k))
      = (GeoExpr.evalPts (.add (.coord 0 0) (.const c))
          (fun k => netAct [shiftLayer β] (pts k))) ^ 2 := rfl
  have hres : GeoExpr.evalPts (.add (.coord 0 0) (.const c))
      (fun k => netAct [shiftLayer β] (pts k)) = β + c := by
    simp only [GeoExpr.evalPts]
    rw [shiftLayer_netAct]
  unfold netLoss linearConstraint
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hpay, hres]

/-! ## 二、梯度步与每次的收缩 -/

/-- **梯度步**：`β ↦ β − η · 2(β + c)`。

`2(β+c)` 正是 `d/dβ (β+c)²`，所以这是对 `netLoss` 的**精确**梯度下降。 -/
noncomputable def step (η c β : ℝ) : ℝ := β - η * (2 * (β + c))

/-- **每步损失乘上 `(1 − 2η)²`**：这是**等式**，不是界。

二次损失的梯度下降是精确可解的，所以这里不必用下降引理。 -/
theorem netLoss_step (η c β : ℝ) (pts : ℕ → Pt 1) :
    netLoss [shiftLayer (step η c β)] [linearConstraint c] pts
      = (1 - 2 * η) ^ 2 * netLoss [shiftLayer β] [linearConstraint c] pts := by
  rw [netLoss_shiftLayer, netLoss_shiftLayer]
  unfold step
  ring

/-- **`0 < η < 1` 时损失不增**：`(1−2η)² ≤ 1`。

⚠ **`η` 是假设不是导出的**：学习率没有理论能定，本节只给出「在这个区间内不增」。 -/
theorem netLoss_step_le (η c β : ℝ) (h0 : 0 < η) (h1 : η < 1) (pts : ℕ → Pt 1) :
    netLoss [shiftLayer (step η c β)] [linearConstraint c] pts
      ≤ netLoss [shiftLayer β] [linearConstraint c] pts := by
  rw [netLoss_step]
  have hnn : 0 ≤ netLoss [shiftLayer β] [linearConstraint c] pts :=
    netLoss_nonneg _ _ _
  have hfac : (1 - 2 * η) ^ 2 ≤ 1 := by nlinarith
  calc (1 - 2 * η) ^ 2 * netLoss [shiftLayer β] [linearConstraint c] pts
      ≤ 1 * netLoss [shiftLayer β] [linearConstraint c] pts := by
        exact mul_le_mul_of_nonneg_right hfac hnn
    _ = netLoss [shiftLayer β] [linearConstraint c] pts := one_mul _

/-! ## 三、多步与极限 -/

/-- `k` 步之后的偏置。 -/
noncomputable def stepN (η c : ℝ) : ℕ → ℝ → ℝ
  | 0, β => β
  | k + 1, β => step η c (stepN η c k β)

/-- **`k` 步后损失是 `(1−2η)^{2k}` 倍**。 -/
theorem netLoss_stepN (η c β : ℝ) (pts : ℕ → Pt 1) :
    ∀ k : ℕ,
      netLoss [shiftLayer (stepN η c k β)] [linearConstraint c] pts
        = ((1 - 2 * η) ^ 2) ^ k * netLoss [shiftLayer β] [linearConstraint c] pts := by
  intro k
  induction k with
  | zero => simp [stepN]
  | succ k ih =>
      rw [stepN, netLoss_step, ih, pow_succ]
      ring

/-- **`|1−2η| < 1` 时损失趋于零**。

⚠ 这正是 `Lib.Optim.RealConvergence.contraction_converges` 的形状
（几何收缩序列趋于零），但那里的对象是抽象的 `e : ℕ → ℝ`，
这里是 `netLoss` 本身——**本节把那条一般结论接到了具体损失上**。 -/
theorem netLoss_stepN_tendsto (η c β : ℝ) (h : |1 - 2 * η| < 1) (pts : ℕ → Pt 1) :
    Filter.Tendsto (fun k => netLoss [shiftLayer (stepN η c k β)] [linearConstraint c] pts)
      Filter.atTop (nhds 0) := by
  have hsq : |(1 - 2 * η) ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg (1 - 2 * η)]
  have hpos : 0 ≤ |(1 - 2 * η) ^ 2| := abs_nonneg _
  have := tendsto_pow_atTop_nhds_zero_of_lt_one hpos hsq
  have hmul := this.mul_const (netLoss [shiftLayer β] [linearConstraint c] pts)
  simpa [netLoss_stepN, mul_comm] using hmul

/-- **损失趋于零**（`|1−2η| < 1` 时）。

⚠ **这不是「某个有限步之后约束成立」。** 损失趋于零意味着残差**趋于**零，
而 `Holds` 要求残差**等于**零——一般 `η` 下只在极限处成立。
**初稿把这条命名成 `constraint_eventually_holds`，那是错的**：趋于零不等于到达。
真正的「到达」在 `η = 1/2` 时一步完成，见下。 -/
theorem netLoss_tendsto_zero (η c β : ℝ) (h : |1 - 2 * η| < 1) (pts : ℕ → Pt 1) :
    Filter.Tendsto (fun k => netLoss [shiftLayer (stepN η c k β)] [linearConstraint c] pts)
      Filter.atTop (nhds 0) :=
  netLoss_stepN_tendsto η c β h pts

/-! ## 四、`η = 1/2` 时**一步**到达：这才是闭环

二次损失的最优步长是 `1/2`（Newton 步），此时 `step` 是 `β ↦ −c`，
于是残差 `β + c` 一次就变成 `0`。**这不是收敛，是精确消解。** -/

/-- **`η = 1/2` 的步就是 Newton 步**：`β ↦ −c`。 -/
theorem step_half (c β : ℝ) : step (1 / 2) c β = -c := by
  unfold step
  ring

/-- **一步之后损失为零**。 -/
theorem netLoss_step_half (c β : ℝ) (pts : ℕ → Pt 1) :
    netLoss [shiftLayer (step (1 / 2) c β)] [linearConstraint c] pts = 0 := by
  rw [netLoss_shiftLayer, step_half]
  ring

/-- **闭环：`η = 1/2` 时，一步更新之后约束成立。**

用 `penaltyLoss_eq_zero_eqZero`（第 198 轮：`eqZero` 的惩罚是**精确**的）把「零损失」
翻成「残差为零」，再用 `Holds` 的定义翻成「约束成立」。

**这是整条链的终点**：符号约束 → 损失 → 参数更新 → **约束成立**，且只需一步。 -/
theorem constraint_satisfied_after_one_step (c β : ℝ) (pts : ℕ → Pt 1) :
    GeoConstraint.Holds (linearConstraint c) (fun k => netAct [shiftLayer (step (1 / 2) c β)] (pts k)) := by
  have hlen : penaltyLoss (linearConstraint c)
      (fun k => netAct [shiftLayer (step (1 / 2) c β)] (pts k)) = 0 := by
    -- the single-constraint net loss IS that penalty
    have hsingle := netLoss_step_half c β pts
    unfold netLoss at hsingle
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsingle
    exact hsingle
  -- `eqZero`'s penalty is exact, so zero penalty gives the residual equation,
  -- which is `Holds` by definition
  have hiff := penaltyLoss_eq_zero_eqZero (n := 1) (.add (.coord 0 0) (.const c))
    (fun k => netAct [shiftLayer (step (1 / 2) c β)] (pts k))
  unfold linearConstraint
  exact hiff.mp hlen

end Lattice.Geo.ConstraintDescent
