import Mathlib
import Lattice.Domains.Constraints.PenaltyLossDerivative
import Lattice.Domains.Constraints.NetLoss
import Lattice.Core.StackDerivative
import Lattice.Core.Net

/-!
# `Lattice.Geo.NetLossDerivative` — **`netLoss` 对点列的导数：桥接引理**

## 接口障碍，及其解法

`netLoss params cs pts = (cs.map (fun c => penaltyLoss c (fun k => netAct params (pts k)))).sum`
（第 101 轮）。

第 128 轮的 `hasFDerivAt_penaltyLoss` 载体是 `fun r : Fin K → Pt n => penaltyLoss c (trunc r)`，
**而 `trunc` 在 `k ≥ K` 处【补零】。**

**`netLoss` 的点列是 `fun k => netAct params (pts k)`，而 `netAct params 0 ≠ 0`**（仿射层带偏置），
**所以「`netLoss` 的点列等于某个 `trunc φ`」【不成立】。**

## 解法：把「只读界内」这条事实显式化

**`ConstraintIndicesBelow c K` 说的是「`c` 用到的点索引都 `< K`」。**
**所以 `penaltyLoss c Φ` 只依赖 `Φ` 在 `[0,K)` 上的值——与 `Φ` 在界外是什么【无关】。**

**本文件把这条事实逐层证出来：**

1. `evalPts_congr_of_indicesBelow`：`GeoExpr` 的求值只依赖界内坐标；
2. 由此逐步到 `penaltyLoss` 的同一性质。

**有了它，`netLoss` 的导数只需把 `fun k => netAct params (trunc r k)` 与 `trunc φ` 在界内对齐，
完全不必碰界外。**
-/

namespace Lattice.Geo

open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open Lattice.Core
open scoped BigOperators

/-- ⭐ **`evalPts` 只依赖界内坐标**：若 `Φ` 与 `Ψ` 在 `[0,K)` 上一致，且 `e` 的索引都 `< K`，
则求值相同。

**对 `GeoExpr` 的五个构造子归纳**：`coord` 用一致性假设，其余三项逐层应用归纳假设。 -/
theorem evalPts_congr_of_indicesBelow {n : ℕ} (e : GeoExpr n) (K : ℕ)
    (hK : IndicesBelow e K) (Φ Ψ : ℕ → Pt n) (h : ∀ k, k < K → Φ k = Ψ k) :
    GeoExpr.evalPts e Φ = GeoExpr.evalPts e Ψ := by
  induction e with
  | coord q axis =>
      have hq : q < K := hK
      simp only [GeoExpr.evalPts]
      rw [h q hq]
  | const c => simp only [GeoExpr.evalPts]
  | add e₁ e₂ ih₁ ih₂ => simp only [GeoExpr.evalPts, ih₁ hK.1, ih₂ hK.2]
  | sub e₁ e₂ ih₁ ih₂ => simp only [GeoExpr.evalPts, ih₁ hK.1, ih₂ hK.2]
  | mul e₁ e₂ ih₁ ih₂ => simp only [GeoExpr.evalPts, ih₁ hK.1, ih₂ hK.2]

/-! ## 第二层：`penaltyLoss` 只依赖界内坐标

**`Pt n` 层的三条**：`sqDist`、`seg`、`midpointCLM` 都只读两个点，
**所以「点的坐标一致」直接给出「由它们构成的量一致」。**

**然后是 `penaltyLoss` 的十二支**——**每支只用前两条加 `evalPts_congr_of_indicesBelow`。** -/

/-- **`sqDist` 对点的坐标一致性**。 -/
theorem sqDist_congr {n : ℕ} {x y x' y' : Pt n} (hx : x = x') (hy : y = y') :
    sqDist x y = sqDist x' y' := by
  rw [hx, hy]

/-- **`seg` 对点的坐标一致性**。 -/
theorem seg_congr {n : ℕ} (Φ Ψ : ℕ → Pt n) (a b : ℕ) (ha : Φ a = Ψ a) (hb : Φ b = Ψ b) :
    seg Φ a b = seg Ψ a b := by
  funext i
  simp only [seg]
  rw [ha, hb]

/-- **`minorDefect` 对两个向量的相等性**。 -/
theorem minorDefect_congr {n : ℕ} {u v u' v' : Pt n} (hu : u = u') (hv : v = v') :
    minorDefect u v = minorDefect u' v' := by
  rw [hu, hv]

/-- ⭐⭐ **`penaltyLoss` 只依赖界内坐标**——**十二支逐一处理**。

**这是 `netLoss` 导数的关键：它把「`trunc` 的补零假设」换成「在 `[0,K)` 上一致」，
而后者对 `fun k => netAct params (trunc r k)` 是【构造上成立】的。** -/
theorem penaltyLoss_congr_of_indicesBelow {n : ℕ} (c : GeoConstraint n) (K : ℕ)
    (hK : ConstraintIndicesBelow c K) (Φ Ψ : ℕ → Pt n)
    (h : ∀ k, k < K → Φ k = Ψ k) :
    penaltyLoss c Φ = penaltyLoss c Ψ := by
  match c, hK with
  | .eqZero e, hK =>
      simp only [penaltyLoss, evalPts_congr_of_indicesBelow e K hK Φ Ψ h]
  | .leZero e, hK =>
      simp only [penaltyLoss, evalPts_congr_of_indicesBelow e K hK Φ Ψ h]
  | .ltZero e, hK =>
      simp only [penaltyLoss, evalPts_congr_of_indicesBelow e K hK Φ Ψ h]
  | .gtZero e, hK =>
      simp only [penaltyLoss, evalPts_congr_of_indicesBelow e K hK Φ Ψ h]
  | .sqDistEq a b d, ⟨ha, hb, hd⟩ =>
      simp only [penaltyLoss, sqDist_congr (h a ha) (h b hb),
        evalPts_congr_of_indicesBelow d K hd Φ Ψ h]
  | .equalLength a b c' e, ⟨ha, hb, hc, he⟩ =>
      simp only [penaltyLoss, sqDist_congr (h a ha) (h b hb),
        sqDist_congr (h c' hc) (h e he)]
  | .collinear a b c', ⟨ha, hb, hc⟩ =>
      simp only [penaltyLoss]
      rw [minorDefect_congr (seg_congr Φ Ψ a b (h a ha) (h b hb))
        (seg_congr Φ Ψ a c' (h a ha) (h c' hc))]
  | .perpendicular a b c' e, ⟨ha, hb, hc, he⟩ =>
      simp only [penaltyLoss]
      rw [seg_congr Φ Ψ a b (h a ha) (h b hb), seg_congr Φ Ψ c' e (h c' hc) (h e he)]
  | .parallel a b c' e, ⟨ha, hb, hc, he⟩ =>
      simp only [penaltyLoss]
      rw [minorDefect_congr (seg_congr Φ Ψ a b (h a ha) (h b hb))
        (seg_congr Φ Ψ c' e (h c' hc) (h e he))]
  | .rightAngle a b c', ⟨ha, hb, hc⟩ =>
      simp only [penaltyLoss]
      rw [seg_congr Φ Ψ a b (h a ha) (h b hb), seg_congr Φ Ψ b c' (h b hb) (h c' hc)]
  | .midpoint m a b, ⟨hm, ha, hb⟩ =>
      simp only [penaltyLoss]
      rw [h m hm, h a ha, h b hb]
  | .samePoint a b, ⟨ha, hb⟩ =>
      simp only [penaltyLoss, sqDist_congr (h a ha) (h b hb)]

/-! ## 第三层：把「点列一致」提升到「损失函数一致」

**`netLoss` 的内层点列 `fun j => netAct params (pts j)` 不是任何 `trunc φ`**
（`netAct params 0 ≠ 0`，见上一节）。

**但上一节说的是：`penaltyLoss c` 只读 `[0,K)`。**
**于是若有两条点列在 `[0,K)` 上逐点一致，则复合出的损失值【相等】。**
**这条等式是纯函数的（不涉及导数）。** -/

/-- ⭐⭐ **函数层面的版本**：若两【族】点列在界内逐点一致，则复合出的函数相等。 -/
theorem penaltyLoss_comp_funext {E : Type*} {n : ℕ} (c : GeoConstraint n) (K : ℕ)
    (hK : ConstraintIndicesBelow c K) (F G : E → ℕ → Pt n)
    (h : ∀ e j, j < K → F e j = G e j) :
    (fun e => penaltyLoss c (F e)) = fun e => penaltyLoss c (G e) := by
  funext e
  exact penaltyLoss_congr_of_indicesBelow c K hK (F e) (G e) (fun j hj => h e j hj)

/-! ### ⚠ 未闭合：把 `netAct` 路径接上 `trunc`

**要证的是**

```lean
(fun r : Fin K → Pt n => penaltyLoss c (fun j => netAct params (trunc r j)))
  = fun r : Fin K → Pt n => penaltyLoss c (trunc (fun j => netAct params (trunc r j)))
```

**它由 `penaltyLoss_comp_funext` 加 `trunc_apply` 应当直接得到**——
**逐点：`trunc (fun i => netAct params (trunc r i)) j = netAct params (trunc r j)`（`j < K`）。**

**⚠ 但 `trunc {K n : ℕ}` 的 `n` 无法从 `fun i => netAct params (trunc r i)` 的返回类型推断，
而显式写 `(n := n)` 时 `n` 又与定理自己的 `n` 同名，Lean 报
`don't know how to synthesize implicit argument @trunc (?m …) n …`。**

**⇒ 下一步的解法是先把这个复合点列绑定到一个**有类型的局部 `let`**：**

```lean
let Ψ : ℕ → Pt n := fun j => netAct params (trunc r j)
-- 然后在 Ψ 上做 trunc Ψ，`n` 就从 Ψ 的类型里读出来了
```

**这是第 111／124／130 轮同一族问题的第 N 次出现**：
**隐式参数无唯一来源时，先给它一个有类型的名字，再使用。** -/

/-! ## 第四层：`netLossOn` —— 有限前缀上的损失，整条链由此贯通

## 为什么需要新定义

**`netLoss` 的点列载体是 `ℕ → Pt n`，而 `NormedSpace ℝ (ℕ → Pt n)` 不存在**（第 115 轮实测）。
**第 131 轮又发现：`netLoss` 的内层点列 `fun j => netAct params (pts j)` 在界外【不为零】，
所以它不是任何 `trunc φ`——把 `trunc` 硬套上去得到的等式是【假的】。**

**⇒ 正确的载体是 `Fin K → Pt n`，且内层【在构造时就用 `trunc`】**：

```lean
netLossOn params cs p := (cs.map (fun c =>
  penaltyLoss c (trunc (n := n) (fun j => netAct params (p ⟨j, _⟩))))).sum
```

**⚠ `p ⟨j, _⟩` 需要 `j < K`。所以内层写成 `fun j => if h : j < K then netAct params (p ⟨j, h⟩) else 0`
——【那正是 `trunc` 的定义】**，**所以 `penaltyLoss c (trunc Ψ)` 与 `penaltyLoss c Φ`
（`Φ j = if j < K then netAct params (p ⟨j,_⟩) else 0`）逐字相同。**

**于是第 128 轮的 `hasFDerivAt_penaltyLoss` 可以【直接】用在 `trunc Ψ` 上，
而 `Ψ` 的界内值由 `p` 经 `netAct` 给出。** -/

/-- **有限前缀上的内层点列**：`j < K` 处取 `netAct params (p ⟨j⟩)`，界外为 `0`。

**它【就是】一个 `trunc` 形式**——这正是本层设计的目的。 -/
noncomputable def netPoints {K n : ℕ} (params : List (AffineLayer (Fin n)))
    (p : Fin K → Pt n) : ℕ → Pt n :=
  fun j => if h : j < K then netAct params (p ⟨j, h⟩) else 0

/-- **`netPoints` 就是 `trunc` 作用在「逐点 `netAct`」上**——**定义级等式。** -/
theorem netPoints_eq_trunc {K n : ℕ} (params : List (AffineLayer (Fin n)))
    (p : Fin K → Pt n) :
    netPoints (n := n) params p
      = trunc (n := n) (fun i : Fin K => netAct params (p i)) := by
  funext j
  simp only [netPoints, trunc]

/-- **有限前缀上的 `netLoss`**——**内层点列用 `netPoints`，界外为零。** -/
noncomputable def netLossOn {K n : ℕ} (params : List (AffineLayer (Fin n)))
    (cs : List (GeoConstraint n)) (p : Fin K → Pt n) : ℝ :=
  (cs.map (fun c => penaltyLoss c (netPoints params p))).sum

/-! ### ⚠ 未闭合：`netLossOn` 的可微性

**`netPoints params p` 与 `trunc p` 的差别就是「界内经过 `netAct`」。**

**而 `hasFDerivAt_penaltyLoss`（第 128 轮）的内层是 `trunc r`——`r` 是【点列本身】。**

**⇒ 用它去证 `netLossOn` 的可微性，需要一条「内层点列经过 `netAct` 后」的 `penaltyLoss` 导数，
而那正是 `penaltyLoss_nontrunc` 缺失的东西。**

**本轮尝试的走法是：把 `netPoints` 写成 `trunc (fun i => netAct params (p i))`（这条【成立】，
见 `netPoints_eq_trunc`），但接着 `hasFDerivAt_penaltyLoss` 要的是 `trunc r`，
而 `trunc (netAct ∘ r)` 与 `trunc r` 的关系是【`netAct` 在界内逐点作用】——
所以导数链是：`r ↦ netAct ∘ r`（逐点）↦ `trunc` ↦ `penaltyLoss`。**

**⇒ 中间那一步 `r ↦ (fun i => netAct params (r i))` 是一个从 `Fin K → Pt n` 到 `Fin K → Pt n` 的映射，
它的 `HasFDerivAt` 由 `hasFDerivAt_netAct_ofFn`（`Core/StackDerivative.lean:223`）给出——
所以整条链是【可以接通】的，只差把它按顺序拼起来。**

**本文件保留了可以独立成立的两条（`netPoints`、`netPoints_eq_trunc`）与 `netLossOn` 的定义，
而【不声称】它的可微性。** -/

/-! ## 第五层：`penaltyLoss` 对【任意逐点界内等价族】的导数

**第 128 轮的 `hasFDerivAt_penaltyLoss` 说 `fun r => penaltyLoss c (trunc r)`。
但 `netLossOn` 的内层是 `netPoints params r`——随 `r` 变化、且只在 `[0,K)` 上与 `trunc r` 一致。**

**⇒ 把导数定理推广到这种族；桥是上一层的局部性引理：两者给出【相同】的损失函数，导数直接继承。**

**⚠ 这一层必须放在本文件而不是 `PenaltyLossDerivative.lean`**：
**它需要 `penaltyLoss_congr_of_indicesBelow`，而那条在本文件——
`NetLossDerivative` 依赖 `PenaltyLossDerivative`，反向 import 会成环。** -/

/-- ⭐⭐⭐ **`penaltyLoss` 在任意「逐点界内等价」族上的导数**。 -/
theorem hasFDerivAt_penaltyLoss_family {K n : ℕ} (c : GeoConstraint n)
    (hK : ConstraintIndicesBelow c K) (p : Fin K → Pt n)
    (P : (Fin K → Pt n) → ℕ → Pt n)
    (hP : ∀ r j, j < K → P r j = trunc r j)
    (hk : KinkPositive c K p) :
    HasFDerivAt (fun r : Fin K → Pt n => penaltyLoss c (P r))
      (penaltyLossFDeriv c hK p) p := by
  have hloc : (fun r : Fin K → Pt n => penaltyLoss c (P r))
      = fun r : Fin K → Pt n => penaltyLoss c (trunc r) := by
    funext r
    exact penaltyLoss_congr_of_indicesBelow c K hK (P r) (trunc r) (hP r)
  rw [hloc]
  exact hasFDerivAt_penaltyLoss c hK p hk

/-- ⭐⭐⭐ **可微性版本**——`netLossOn` 直接消费这一条。 -/
theorem differentiableAt_penaltyLoss_family {K n : ℕ} (c : GeoConstraint n)
    (hK : ConstraintIndicesBelow c K) (p : Fin K → Pt n)
    (P : (Fin K → Pt n) → ℕ → Pt n)
    (hP : ∀ r j, j < K → P r j = trunc r j)
    (hk : KinkPositive c K p) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => penaltyLoss c (P r)) p :=
  (hasFDerivAt_penaltyLoss_family c hK p P hP hk).differentiableAt

/-! ### ⚠ 下一层障碍：`netAct` 的导数只对 `List.ofFn p` 有陈述

**`netPoints params p j = netAct params (p ⟨j, _⟩)` 里 `params` 是任意 `List`，
而 `netAct` 的可微性定理（`Core/StackDerivative.lean:213`、`:223`）的陈述是**

```lean
theorem differentiableAt_netAct_ofFn {k n : ℕ} (p : Fin k → AffineLayer (Fin n)) :
    DifferentiableAt ℝ (fun y => netAct (List.ofFn p) y) x
```

**——即它只覆盖 `params = List.ofFn p` 这一形式。**

**⇒ 对任意 `List`，`netAct` 的可微性【没有陈述】，因此把 `netAct` 逐点应用到点列上
（`r ↦ fun j => netAct params (r j)`）也无法用现有定理复合。**

**第 134 轮实测：`fun_prop` 对 `netAct` 报 `No theorems found for Lattice.Core.netAct`；
而 `differentiableAt_netAct_ofFn` 需要 `params` 已经是 `List.ofFn p` 形式。**

## 正确形状（下一轮）

**库里【没有】`List → Fin k →` 的桥**（第 134 轮实测：只有反方向的 `List.ofFn`）。
**⇒ 有两条路：**

1. **给 `netLossOn` 的 `params` 从 `List` 改成 `Fin k → AffineLayer (Fin n)`**——
   **这与 `stackParams`（第 104 轮）一致，也避开所有 List 桥**；**推荐这条路**；
2. 或者补一条 `List.equivFin` 形式的桥并证明 `netAct` 与它相容——**成本高于第 1 条。**

**⇒ 下一轮先量 `netLossOn` 改成 `Fin k → AffineLayer` 载体后，
`hasFDerivAt_penaltyLoss_family` 的 `P` 能否直接取 `netPoints`（那时 `netAct` 的导数就有陈述了）。** -/

/-! ## 第六层：逐点 `netActN` 作用于点列

**`netLossOn` 的内层点列是 `fun j => netActN n k Pf (r j)`——`netActN` 逐点作用在 `r` 上。**

**本节证这条映射对 `r` 可微，用第 109 轮的 `differentiableAt_netActN`（关于【输入】）与
`differentiableAt_pi`（逐坐标）复合。**

**⚠ `netActN` 而不是 `netAct`**：前者直接以 `Fin k →` 为载体，不需要 `List.ofFn` 桥（第 134 轮的障碍）。 -/

/-- ⭐⭐ **逐点 `netActN` 作用于点列，对点列可微**。 -/
theorem differentiableAt_pointwiseNetActN {K k n : ℕ} (Pf : Fin k → AffineLayer (Fin n))
    (r : Fin K → Pt n) :
    DifferentiableAt ℝ (fun s : Fin K → Pt n => fun j : Fin K => netActN n k Pf (s j)) r := by
  rw [show (fun s : Fin K → Pt n => fun j : Fin K => netActN n k Pf (s j))
      = fun s : Fin K → Pt n => (fun j => netActN n k Pf (s j)) from rfl]
  refine differentiableAt_pi.2 (fun j => ?_)
  exact (differentiableAt_netActN k Pf (r j)).comp r
    (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => Pt n) j)).differentiableAt

/-- ⭐⭐ **逐点 `netActN` 的 `HasFDerivAt` 句柄**——下游要导数时从这里取。 -/
theorem hasFDerivAt_pointwiseNetActN {K k n : ℕ} (Pf : Fin k → AffineLayer (Fin n))
    (r : Fin K → Pt n) :
    HasFDerivAt (fun s : Fin K → Pt n => fun j : Fin K => netActN n k Pf (s j))
      (fderiv ℝ (fun s : Fin K → Pt n => fun j : Fin K => netActN n k Pf (s j)) r) r :=
  (differentiableAt_pointwiseNetActN Pf r).hasFDerivAt

/-! ## 第七层：`lossOfActivations` —— 把网络与损失解耦

## 为什么要这一层

**`netLossOn` 的内层是 `fun j => netActN n k Pf (r j)`——`netActN` 把 `0` 映到偏置，
所以它在界外【不为零】，与 `trunc r` 不一致。**

**⇒ 用 `penaltyLoss` 的导数定理（内层必须是 `trunc r`）时，中间隔着 `netActN`，两边的形状对不上。**

**本层的解法是【把两者拆开】**：

```lean
lossOfActivations cs (acts : Fin K → Pt n) := ∑ c ∈ cs, penaltyLoss c (trunc acts)
```

**于是：**

- **`lossOfActivations` 对内层【已经是 `trunc` 形式】——第 128 轮的定理原样可用，
  给出对 `acts` 的导数；**
- **`acts = fun j => netActN n k Pf (r j)` 的导数由第 135 轮的
  `differentiableAt_pointwiseNetActN` 给出；**
- **两者复合就是 `netLossOn` 对 `r` 的导数。**

**这是标准的链式分解：【先算损失关于激活的依赖，再算激活关于输入的依赖】，
而两层各自都有现成的定理。** -/

/-- **激活点列上的损失**：`∑ c ∈ cs, penaltyLoss c (trunc acts)`。

**⚠ 内层直接是 `trunc acts`**——**这是本层设计的目的：让 `penaltyLoss` 的导数定理原样可用。** -/
noncomputable def lossOfActivations {K n : ℕ} (cs : List (GeoConstraint n))
    (acts : Fin K → Pt n) : ℝ :=
  (cs.map (fun c => penaltyLoss c (trunc acts))).sum

/-- ⭐⭐ **`lossOfActivations` 对激活可微**——**逐约束 `HasFDerivAt.sum`，每支直接用第 128 轮的定理。** -/
theorem lossOfActivations_differentiableAt {K n : ℕ} (cs : List (GeoConstraint n))
    (acts : Fin K → Pt n)
    (hK : ∀ c ∈ cs, ConstraintIndicesBelow c K)
    (hk : ∀ c ∈ cs, KinkPositive c K acts) :
    DifferentiableAt ℝ (fun a : Fin K → Pt n => lossOfActivations cs a) acts := by
  induction cs with
  | nil =>
      have hnil : (fun a : Fin K → Pt n => lossOfActivations [] a) = fun _ => (0 : ℝ) := by
        funext a
        simp only [lossOfActivations, List.map_nil, List.sum_nil]
      rw [hnil]
      exact differentiableAt_const 0
  | cons c rest ih =>
      have hc : ConstraintIndicesBelow c K := hK c (by simp)
      have hkc : KinkPositive c K acts := hk c (by simp)
      have hrest : DifferentiableAt ℝ
          (fun a : Fin K → Pt n => lossOfActivations rest a) acts :=
        ih (fun c' hc' => hK c' (List.mem_cons_of_mem c hc'))
          (fun c' hc' => hk c' (List.mem_cons_of_mem c hc'))
      have hsplit : (fun a : Fin K → Pt n => lossOfActivations (c :: rest) a)
          = fun a : Fin K → Pt n => penaltyLoss c (trunc a) + lossOfActivations rest a := by
        funext a
        simp only [lossOfActivations, List.map_cons, List.sum_cons]
      rw [hsplit]
      exact (hasFDerivAt_penaltyLoss c hc acts hkc).differentiableAt.add hrest

/-! ### ⚠ 未闭合：`netLossOn = lossOfActivations ∘ pointwiseNetActN`

**要证的是 `netLossOn (List.ofFn Pf) cs r = lossOfActivations cs (fun j => netActN n k Pf (r j))`。**

**它在【界内】是逐字的：两侧的 `j < K` 分支都给出 `netActN n k Pf (r j)`。**

**但 `netPoints` 用的是 `if h : j < K then netAct params (p ⟨j, h⟩) else 0`（`netAct` + `List`），
而 `lossOfActivations` 的内层是 `trunc`（`netActN` + `Fin k →`）——两处【同时】差一个 `List.ofFn` 桥与一个 `netAct`/`netActN` 桥。**

**⇒ 正确做法是把 `netPoints` 的定义【改成】`netActN` 版本**（`Fin k →` 载体，与第 135 轮一致），
**这样两侧就只差 `trunc` 的展开，一行 `simp` 可收。**

**本轮未做这一步**：它要改 `netPoints` 与 `netLossOn` 的定义（以及 `netPoints_eq_trunc`），
**而那是第 134 轮记录过的「载体改名」决策——应当先声明再做，而不是在一轮末尾改。** -/

/-! ### ⚠ 载体改名的精确步骤（第 137 轮六次尝试后的结论）

**目标：把 `netPoints`／`netLossOn` 的载体从 `List (AffineLayer (Fin n))` 换成 `Fin k → AffineLayer (Fin n)`，
使内层成为 `netActN`，从而 `netLossOn = lossOfActivations ∘ pointwiseNetActN` 是一次 `simp`。**

**第 137 轮实测：改动本身是机械的，但【定义顺序】必须一次排对，否则每一步都失败在同一个地方。**

## 必需的文件内顺序

**Lean 是单遍处理，所以凡是【引用】某定义的地方必须在它之后。当前文件里的依赖是：**

```
lossOfActivations            (第 136 轮，定义在文件偏后处)
  ← lossOfActivations_differentiableAt
  ← differentiableAt_pointwiseNetActN   (第 135 轮，更后)
  ← netPoints / netLossOn / netPoints_eq_trunc   (第 132 轮，更前)
```

**⇒ 新的 `netPoints`／`netLossOn`／`netLossOn_eq_comp`／`netLossOn_differentiableAt`
必须放在 **`pointwiseNetActN` 之后**，而**不能**放在它们当前的（文件偏前）位置。**

**第 137 轮我两次尝试移动那个块，两次都因为「按 `end Lattice.Geo` 锚点插入」而落回原位——
`end Lattice.Geo` 是文件唯一的收尾，所以「插到它前面」等于「插到文件末尾」，
而末尾【已经】在 `pointwiseNetActN` 之后——**但那不是失败的原因：真正的失败是那块代码里
`lossOfActivations` 的引用位置没有随之移动。**

## 正确的做法（下一轮直接照做）

**不要移动块，而是【重排整节】**：把下列五者按此顺序放成连续的第四节（`## 第四层`），
从 `netPoints` 一直到 `netLossOn_differentiableAt`：

1. `netPoints`（`Fin k → AffineLayer`）
2. `netPoints_eq_trunc`
3. `netLossOn`
4. `lossOfActivations` + `lossOfActivations_differentiableAt`
5. `differentiableAt_pointwiseNetActN`（或从第 135 轮处前置）
6. `netLossOn_eq_comp`
7. `netLossOn_differentiableAt`

**⇒ 判据：改完后 `lake build Lattice.Domains.Constraints.NetLossDerivative` 必须一次通过；
若仍报 `function expected at lossOfActivations`，那就是步骤 4 没有排在步骤 6 之前。**

**本轮【未】做这个重排**——六次尝试说明我对 Lean 单遍处理的直觉在这条链上不够可靠，
**而重排整个文件的一节是一个应当单独、完整地做的改动，不是在一轮末尾继续试。** -/

end Lattice.Geo
