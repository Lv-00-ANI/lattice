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
import Lattice.Domains.Constraints.Constraint
import Lattice.Domains.Constraints.PenaltyLoss
import Lattice.Domains.Constraints.NetLoss

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

/-! ## 五、推广到 `n` 维与 `n` 条约束

第四节的闭环是 `1` 维、`1` 条。本节把它推到 **`n` 维、每个坐标一条约束**，
而收缩因子**完全相同**——因为各坐标的下降是互相独立的，只是求和。

**为什么用 `List.ofFn` 而不是 `List.finRange.map`**：本 mathlib **没有 `List.sum_finRange`**
（又一次名字猜错——与 `Int.div_mul_add_emod`、`max_eq_zero_iff`、`List.getD_append_left` 同一类）。
而 `List.sum_ofFn : (List.ofFn f).sum = ∑ i, f i` **存在**，所以用它构造约束表，
求和桥就直通了。**换一个构造方式，省一条不存在的引理。** -/

/-- **`n` 维的位移层**：`W = 0`、`b = β`（逐坐标）。

它把**任何**输入送到常值向量 `β`，于是约束在输出配置上的残差是 `β` 的**线性函数**。 -/
noncomputable def shiftLayerVec {n : ℕ} (β : Fin n → ℝ) : AffineLayer (Fin n) where
  W := fun _ _ => 0
  b := β

/-- **`shiftLayerVec` 把一切送到 `β`。** -/
theorem shiftLayerVec_netAct {n : ℕ} (β : Fin n → ℝ) (x : Pt n) :
    netAct [shiftLayerVec β] x = β := by
  funext j
  show affineAct (shiftLayerVec β) x j = β j
  unfold affineAct shiftLayerVec
  simp

/-- **第 `axis` 个坐标上的线性约束**：`x_axis + c = 0`。 -/
noncomputable def coordConstraint {n : ℕ} (axis : Fin n) (c : ℝ) : GeoConstraint n :=
  .eqZero (.add (.coord 0 axis) (.const c))

/-- **每个坐标一条约束**，由 `c : Fin n → ℝ` 给出。

用 `List.ofFn` 构造，以便直接用 `List.sum_ofFn` 把列表和接到 `∑ j : Fin n`。 -/
noncomputable def coordConstraints {n : ℕ} (c : Fin n → ℝ) : List (GeoConstraint n) :=
  List.ofFn (fun j => coordConstraint j (c j))

/-- **`n` 维的损失是逐坐标二次式之和**：`∑ j, (β j + c j)²`。

这是第四节 `netLoss_shiftLayer` 的 `n` 维版本。 -/
theorem netLoss_shiftLayerVec {n : ℕ} (β c : Fin n → ℝ) (pts : ℕ → Pt n) :
    netLoss [shiftLayerVec β] (coordConstraints c) pts = ∑ j : Fin n, (β j + c j) ^ 2 := by
  have hX : ∀ k : ℕ, netAct [shiftLayerVec β] (pts k) = β := fun k => shiftLayerVec_netAct β (pts k)
  -- the penalty of coordinate `j`'s constraint is `(β j + c j)^2`
  have hterm : ∀ j : Fin n,
      penaltyLoss (coordConstraint j (c j)) (fun k => netAct [shiftLayerVec β] (pts k))
        = (β j + c j) ^ 2 := by
    intro j
    have hpay : penaltyLoss (.eqZero (.add (.coord 0 j) (.const (c j))))
        (fun k => netAct [shiftLayerVec β] (pts k))
        = (GeoExpr.evalPts (.add (.coord 0 j) (.const (c j)))
            (fun k => netAct [shiftLayerVec β] (pts k))) ^ 2 := rfl
    have hres : GeoExpr.evalPts (.add (.coord 0 j) (.const (c j)))
        (fun k => netAct [shiftLayerVec β] (pts k)) = β j + c j := by
      simp only [GeoExpr.evalPts]
      rw [hX]
    unfold coordConstraint
    rw [hpay, hres]
  -- rewrite the mapped list as `List.ofFn`, then use `List.sum_ofFn`
  have hmap : (coordConstraints c).map
      (fun k => penaltyLoss k (fun k => netAct [shiftLayerVec β] (pts k)))
      = List.ofFn (fun j => (β j + c j) ^ 2) := by
    unfold coordConstraints
    rw [List.map_ofFn]
    congr 1
    funext j
    exact hterm j
  unfold netLoss
  rw [hmap, List.sum_ofFn]

/-- **`n` 维的梯度步**：逐坐标 `β j ↦ β j − η · 2(β j + c j)`。 -/
noncomputable def stepVec {n : ℕ} (η : ℝ) (c β : Fin n → ℝ) : Fin n → ℝ :=
  fun j => β j - η * (2 * (β j + c j))

/-- **`n` 维收缩：损失乘上 `(1−2η)²`**——与一维**完全相同的因子**。

因为各坐标独立求和，公共因子可以提出来。**这就是「推广」的实质：不是新的数学，是同一条代数在 `∑` 下面。** -/
theorem netLoss_stepVec {n : ℕ} (η : ℝ) (c β : Fin n → ℝ) (pts : ℕ → Pt n) :
    netLoss [shiftLayerVec (stepVec η c β)] (coordConstraints c) pts
      = (1 - 2 * η) ^ 2 * netLoss [shiftLayerVec β] (coordConstraints c) pts := by
  rw [netLoss_shiftLayerVec, netLoss_shiftLayerVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold stepVec
  ring

/-- **`n` 维：`0 < η < 1` 时损失不增。** -/
theorem netLoss_stepVec_le {n : ℕ} (η : ℝ) (c β : Fin n → ℝ) (h0 : 0 < η) (h1 : η < 1)
    (pts : ℕ → Pt n) :
    netLoss [shiftLayerVec (stepVec η c β)] (coordConstraints c) pts
      ≤ netLoss [shiftLayerVec β] (coordConstraints c) pts := by
  rw [netLoss_stepVec]
  have hnn : 0 ≤ netLoss [shiftLayerVec β] (coordConstraints c) pts := netLoss_nonneg _ _ _
  have hfac : (1 - 2 * η) ^ 2 ≤ 1 := by nlinarith
  calc (1 - 2 * η) ^ 2 * netLoss [shiftLayerVec β] (coordConstraints c) pts
      ≤ 1 * netLoss [shiftLayerVec β] (coordConstraints c) pts :=
        mul_le_mul_of_nonneg_right hfac hnn
    _ = netLoss [shiftLayerVec β] (coordConstraints c) pts := one_mul _

/-- **`n` 维、`n` 条约束：`η = 1/2` 时一步之后全部成立。**

```lean
stepVec (1/2) c β j = β j - (β j + c j) = -c j
```

于是每个坐标的残差 `β j + c j` 变成零，**每条约束都成立**。

**这是第四节 `constraint_satisfied_after_one_step` 的 `n` 维推广**：
不是「每条约束各自跑一遍」，而是**一次联合更新同时解掉全部 `n` 条**。 -/
theorem all_coord_constraints_after_one_step {n : ℕ} (c β : Fin n → ℝ) (pts : ℕ → Pt n) :
    ∀ j : Fin n,
      GeoConstraint.Holds (coordConstraint j (c j))
        (fun k => netAct [shiftLayerVec (stepVec (1 / 2) c β)] (pts k)) := by
  intro j
  have hX : ∀ k : ℕ,
      netAct [shiftLayerVec (stepVec (1 / 2) c β)] (pts k) = stepVec (1 / 2) c β :=
    fun k => shiftLayerVec_netAct _ _
  have hres : GeoExpr.evalPts (.add (.coord 0 j) (.const (c j)))
      (fun k => netAct [shiftLayerVec (stepVec (1 / 2) c β)] (pts k))
      = (stepVec (1 / 2) c β) j + c j := by
    simp only [GeoExpr.evalPts]
    rw [hX]
  unfold coordConstraint
  show GeoExpr.evalPts (.add (.coord 0 j) (.const (c j)))
      (fun k => netAct [shiftLayerVec (stepVec (1 / 2) c β)] (pts k)) = 0
  rw [hres]
  unfold stepVec
  ring

/-! ## 六、损失的两条事实（capstone 已搬到 `Compose`）

### ⚠ 第 228 轮：capstone **搬走了**，不是删了

本节原来有 `forward_chain_capstone` 与 `forward_chain_at_solution`。
`DIRECTORY-DESIGN.md` §2.6 要求「`Primitives` 之间零 import」，而 §10 把
`NetLoss`/`PenaltyLoss`/`ConstraintDescent` 都映射到 `Primitives/Train` ——
**capstone 恰恰跨了这三者**，所以它不能留在 `Primitives/Train` 的任何一个文件里。

**第 228 轮的裁决：搬到 `Compose` 并重写陈述。**
新位置：**`Lattice/Compose/ForwardChain.lean`**，`forward_chain_capstone`（四环仍然齐全）
与 `forward_chain_at_solution`。

**陈述变了，这是有意的**：`Compose` 版本把这一步做成一个 **`Primitive`**（`trainStep`），
于是 `post` 是**结构字段**，可以被 `compose`/`parallel`/`Matrix` 消费；
而在本节它只是一条孤立定理，**谁也用不上**。第 220 轮那条的价值在于「四环写进一条陈述」，
第 228 轮在保留这一点的同时让它**可组合**。

### 本节留下什么

两条**损失层的事实**——它们是 `Geo` 层的，不是组合层的：

| 定理 | 内容 |
|:--|:--|
| `netLoss_pos_of_ne` | 残差非零 ⟹ 损失为正 |
| `netLoss_zero_iff_holds` | 损失为零 ⟺ 约束成立 |

`Compose/ForwardChain` 的 `trainStep.sound` 与 capstone 都用这两条。**留在这里而不是搬走**，
因为它们不涉及 `Primitive`，而 `Compose` 之上的任何东西都需要它们。 -/


/-- **残差非零时损失为正**：`β + c ≠ 0 ⟹ 0 < netLoss`。

这是 `netLoss_shiftLayer` 的 `(β + c)²` 形状的直接推论。 -/
theorem netLoss_pos_of_ne (c β : ℝ) (hne : β + c ≠ 0) (pts : ℕ → Pt 1) :
    0 < netLoss [shiftLayer β] [linearConstraint c] pts := by
  rw [netLoss_shiftLayer]
  exact sq_pos_of_ne_zero hne

/-- **损失为零 ⟺ 约束成立**（单条 `eqZero` 线性约束）。

两个方向分别来自 `penaltyLoss` 的**精确性**（第 198 轮：`eqZero` 的零集恰是解集）
与 `netLoss` 的 `sound` 方向（第 199 轮）。 -/
theorem netLoss_zero_iff_holds (c β : ℝ) (pts : ℕ → Pt 1) :
    netLoss [shiftLayer β] [linearConstraint c] pts = 0 ↔
      GeoConstraint.Holds (linearConstraint c)
        (fun k => netAct [shiftLayer β] (pts k)) := by
  rw [netLoss_shiftLayer]
  constructor
  · intro h
    -- `(β + c)^2 = 0` means the residual is zero, which IS `Holds` for `eqZero`
    have hz : β + c = 0 := by
      have := sq_eq_zero_iff.mp h
      exact this
    unfold linearConstraint
    show GeoExpr.evalPts (.add (.coord 0 0) (.const c))
      (fun k => netAct [shiftLayer β] (pts k)) = 0
    simp only [GeoExpr.evalPts]
    rw [shiftLayer_netAct]
    simpa using hz
  · intro h
    unfold linearConstraint at h
    have hres : GeoExpr.evalPts (.add (.coord 0 0) (.const c))
        (fun k => netAct [shiftLayer β] (pts k)) = 0 := h
    simp only [GeoExpr.evalPts] at hres
    rw [shiftLayer_netAct] at hres
    rw [hres]
    ring


end Lattice.Geo.ConstraintDescent

