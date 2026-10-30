import Mathlib
import Lattice.Domains.Constraints.PenaltyLoss
import Lattice.Domains.Constraints.DistDerivative
import Lattice.Domains.Constraints.ExprDerivative

set_option maxHeartbeats 800000

/-!
# `Lattice.Geo.PenaltyLossDerivative` — **`penaltyLoss` 对点列的显式导数**

## 载体与前提

**导数载体是 `Fin K → Pt n`**（与 `ExprDerivative` 一致：`NormedSpace ℝ (ℕ → Pt n)` 不存在），
**函数是 `fun r => penaltyLoss c (trunc r)`**，**前提是 `IndicesBelow c K`**。

## 本文件覆盖的分支

`penaltyLoss` 有 12 支，**本文件做【无条件可导】的那些**：

| 分支 | 形状 |
|:--|:--|
| `samePoint a b` | `sqDist (pts a) (pts b)` |
| `eqZero e` | `(evalPts e)²` |
| `sqDistEq a b d` | `(sqDist − evalPts d)²` |
| `equalLength a b c e` | `(sqDist − sqDist)²` |

⚠ **`leZero`/`ltZero`/`gtZero` 走 `max · 0`，在折点 `evalPts e = 0` 处【不可导】**——
**它们需要额外前提，本文件不声称它们是可导的。**

## 为什么先要 `sqDist` 的联合可微性

`samePoint a b` 是 `sqDist (trunc r a) (trunc r b)`——**两个槽都随 `r` 动**，
**所以 `sqDistFDeriv`（单槽）不够，必须有 `(x, y) ↦ sqDist x y` 的联合可微性。**
**而 `fun_prop` 能直接证它**（探针验证，第 117 轮）。
-/

namespace Lattice.Geo

open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open scoped BigOperators

/-- ⭐ **`sqDist` 对【两个】变元联合可微**——`samePoint` 支的前提。 -/
theorem sqDist_differentiableAt_pair {n : ℕ} (x y : Pt n) :
    DifferentiableAt ℝ (fun r : Pt n × Pt n => sqDist r.1 r.2) (x, y) := by
  have hfun : (fun r : Pt n × Pt n => sqDist r.1 r.2)
      = fun r : Pt n × Pt n => ∑ i, (r.1 i - r.2 i) ^ 2 := by
    funext r
    exact sqDist_eq_sum r.1 r.2
  rw [hfun]
  fun_prop

/-- **取第 `a` 个点的投影**：`(Fin K → Pt n) →L[ℝ] Pt n`。 -/
noncomputable def pointProj {K n : ℕ} (a : Fin K) : (Fin K → Pt n) →L[ℝ] Pt n :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => Pt n) a

/-- **`trunc r a` 对 `r` 的导数就是 `pointProj a`**。 -/
theorem hasFDerivAt_truncPoint {K n : ℕ} (a : ℕ) (ha : a < K) (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => trunc r a) (pointProj ⟨a, ha⟩) p := by
  have hfun : (fun r : Fin K → Pt n => trunc r a) = fun r : Fin K → Pt n => r ⟨a, ha⟩ := by
    funext r
    exact trunc_apply r ⟨a, ha⟩
  rw [hfun]
  exact ContinuousLinearMap.hasFDerivAt (pointProj ⟨a, ha⟩)

/-- **`r ↦ (trunc r a, trunc r b)` 是连续的线性映射**（两个 `pointProj` 的积）。 -/
noncomputable def pairProj {K n : ℕ} (a b : Fin K) :
    (Fin K → Pt n) →L[ℝ] (Pt n × Pt n) :=
  (pointProj a).prod (pointProj b)

/-- **`r ↦ (trunc r a, trunc r b)` 的导数**。 -/
theorem hasFDerivAt_pairProj {K n : ℕ} (a b : ℕ) (ha : a < K) (hb : b < K)
    (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => (trunc r a, trunc r b))
      (pairProj ⟨a, ha⟩ ⟨b, hb⟩) p :=
  (hasFDerivAt_truncPoint a ha p).prod (hasFDerivAt_truncPoint b hb p)

/-- ⭐⭐ **`samePoint` 分支可微**：`sqDist (trunc · a) (trunc · b)`。

**由 `sqDist_differentiableAt_pair` 与 `hasFDerivAt_pairProj` 复合。** -/
theorem samePoint_differentiableAt {K n : ℕ} (a b : ℕ) (ha : a < K) (hb : b < K)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => sqDist (trunc r a) (trunc r b)) p :=
  (sqDist_differentiableAt_pair (trunc p a) (trunc p b)).comp p
    (hasFDerivAt_pairProj a b ha hb p).differentiableAt

/-- ⭐⭐ **`eqZero` 分支可微**：`(evalPts e (trunc ·))²`。

**由 `evalPts_differentiableAt`（第 115 轮）与 `y ↦ y²`（`Core.hasFDerivAt_sq`）复合。** -/
theorem eqZero_differentiableAt {K n : ℕ} (e : GeoExpr n) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r) ^ 2) p :=
  (Lattice.Core.hasFDerivAt_sq (GeoExpr.evalPts e (trunc p))).differentiableAt.comp p
    (evalPts_differentiableAt e hK p)

/-- ⭐⭐ **`sqDistEq` 分支可微**：`(sqDist (trunc · a) (trunc · b) − evalPts d (trunc ·))²`。

**两个求导对象分别是 `sqDist` 的联合复合与 `evalPts`，相减后用 `y ↦ y²` 复合。** -/
theorem sqDistEq_differentiableAt {K n : ℕ} (a b : ℕ) (d : GeoExpr n)
    (ha : a < K) (hb : b < K) (hd : IndicesBelow d K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n =>
        (sqDist (trunc r a) (trunc r b) - GeoExpr.evalPts d (trunc r)) ^ 2) p := by
  have h1 := samePoint_differentiableAt a b ha hb p
  have h2 := evalPts_differentiableAt d hd p
  exact (Lattice.Core.hasFDerivAt_sq
    (sqDist (trunc p a) (trunc p b) - GeoExpr.evalPts d (trunc p))).differentiableAt.comp p
    (h1.sub h2)

/-- ⭐⭐ **`equalLength` 分支可微**：`(sqDist (trunc · a) (trunc · b) − sqDist (trunc · c) (trunc · e))²`。 -/
theorem equalLength_differentiableAt {K n : ℕ} (a b c e : ℕ)
    (ha : a < K) (hb : b < K) (hc : c < K) (he : e < K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n =>
        (sqDist (trunc r a) (trunc r b) - sqDist (trunc r c) (trunc r e)) ^ 2) p := by
  have h1 := samePoint_differentiableAt a b ha hb p
  have h2 := samePoint_differentiableAt c e hc he p
  exact (Lattice.Core.hasFDerivAt_sq
    (sqDist (trunc p a) (trunc p b) - sqDist (trunc p c) (trunc p e))).differentiableAt.comp p
    (h1.sub h2)

/-! ## ⭐ `seg` 作为线性映射，以及 `midpoint` 的导数

`seg (trunc r) a b i = trunc r b i − trunc r a i`——**对 `r` 是【线性】的**，
**所以 `seg` 本身就是一条 `(Fin K → Pt n) →L[ℝ] Pt n`，而不是需要乘积法则的东西。**

**这直接给出 `midpoint` 支**（`∑ i, (2·pts m i − pts a i − pts b i)²`，线性形式平方和）：
**每项的导数由 `Core.hasFDerivAt_sq_comp` 给出，求和由 `HasFDerivAt.sum` 收。** -/

/-- **`seg` 作为线性映射**：`r ↦ fun i => r b i − r a i`。 -/
noncomputable def segCLM {K n : ℕ} (a b : Fin K) : (Fin K → Pt n) →L[ℝ] Pt n :=
  (pointProj b) - (pointProj a)

/-- **`segCLM` 的求值**：与 `seg (trunc r) a b` 逐点一致。 -/
theorem segCLM_apply {K n : ℕ} (a b : Fin K) (r : Fin K → Pt n) (i : Fin n) :
    segCLM a b r i = trunc r b i - trunc r a i := by
  simp only [segCLM, ContinuousLinearMap.sub_apply, pointProj, Pi.sub_apply,
    ContinuousLinearMap.proj_apply]
  rw [trunc_apply, trunc_apply]

/-- **`segCLM` 的导数**。 -/
theorem hasFDerivAt_segCLM {K n : ℕ} (a b : Fin K) (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => segCLM a b r) (segCLM a b) p :=
  ContinuousLinearMap.hasFDerivAt (segCLM a b)

/-! ## `midpoint` 与 `perpendicular`：两个「平方」分支

`midpoint m a b` 是 `∑ i, (2·pts m i − pts a i − pts b i)²`——**一个线性形式的平方和**。
`perpendicular a b c e` 是 `(∑ i, seg a b i · seg c e i)²`——**一个双线性形式的平方**。

**两者的内层都写成 `segCLM` 的组合：**

- `midpoint` 的内层：`L = 2 • segCLM b m − segCLM a b`（因为 `2·pts m − pts a − pts b = 2(ptm − pta) − (ptb − pta)` 的展开，
  但直接写成 `2 • pointProj m − pointProj a − pointProj b` 更短且逐字正确）；
- `perpendicular` 的内层：`∑ i, segCLM a b r i * segCLM c e r i`。

⚠ **`midpoint` 的内层我用 `2 • pointProj m − pointProj a − pointProj b`**（**不是** `segCLM` 的组合）——
**因为它就是 `2·pts m − pts a − pts b` 的字面翻译**，少一次换形就少一处出错（第 118 轮在这里失败过）。

⚠ **`2` 必须写成 `(2 : ℝ)`**——第 118 轮它被推断成 `ℕ` 而失败。 -/

/-- **`midpoint` 的内层线性形式**：`r ↦ 2·r m − r a − r b`。 -/
noncomputable def midpointCLM {K n : ℕ} (m a b : Fin K) : (Fin K → Pt n) →L[ℝ] Pt n :=
  (2 : ℝ) • pointProj m - pointProj a - pointProj b

/-- **`midpointCLM` 的求值**。 -/
theorem midpointCLM_apply {K n : ℕ} (m a b : Fin K) (r : Fin K → Pt n) (i : Fin n) :
    midpointCLM m a b r i = 2 * trunc r m i - trunc r a i - trunc r b i := by
  simp only [midpointCLM, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    pointProj, Pi.sub_apply, Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [trunc_apply, trunc_apply, trunc_apply]

/-- ⭐⭐ **`midpoint` 分支可微**：`∑ i, (2·trunc · m i − trunc · a i − trunc · b i)²`。 -/
theorem midpoint_differentiableAt {K n : ℕ} (m a b : ℕ) (hm : m < K) (ha : a < K) (hb : b < K)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n => ∑ i, (2 * trunc r m i - trunc r a i - trunc r b i) ^ 2) p := by
  have hlin : HasFDerivAt (fun r : Fin K → Pt n => midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩ r)
      (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩) p :=
    ContinuousLinearMap.hasFDerivAt (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩)
  have hfun : (fun r : Fin K → Pt n => ∑ i, (2 * trunc r m i - trunc r a i - trunc r b i) ^ 2)
      = fun r : Fin K → Pt n => ∑ i, (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩ r i) ^ 2 := by
    funext r
    exact Finset.sum_congr rfl (fun i _ => by rw [midpointCLM_apply])
  rw [hfun]
  refine DifferentiableAt.sum (u := Finset.univ) ?_
  intro i _
  have hcoord : HasFDerivAt (fun r : Fin K → Pt n => midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩ r i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp
        (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩)) p :=
    ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp
        (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩))
  exact (Lattice.Core.hasFDerivAt_sq_comp hcoord).differentiableAt

/-! ## `perpendicular` 与 `rightAngle`：**双线性形式的平方**

`perpendicular a b c e` 是 `(∑ i, seg a b i · seg c e i)²`，`rightAngle a b c` 是
`(∑ i, seg a b i · seg b c i)²`。

**内层那个和对 `r` 是【二次】的**（两个因子都随 `r` 动），**所以：**

1. **逐项 `HasFDerivAt.mul`**（`f = fun r => segCLM a b r i`、`g = fun r => segCLM c e r i`，两者都是 `r ↦ ℝ`）——
   **导数是 `(f p) • g' + (g p) • f'`，其中 `f p`、`g p` 是实数，`g'`、`f'` 是 `segCLM`**；
2. **`DifferentiableAt.sum` 收起来**（第 119 轮的教训：不用 `HasFDerivAt.sum`）；
3. **再 `Core.hasFDerivAt_sq_comp`。**

⚠ **内层写成 `segCLM a b r i * segCLM c e r i`（不做换形）**——
**`segCLM_apply` 已给出求值等式，所以「对 `r` 的依赖」是逐字的**（第 119 轮的成功配方）。 -/

/-- **`perpendicular` 的内层**：`r ↦ ∑ i, segCLM a b r i * segCLM c e r i`。 -/
noncomputable def bilinearSum {K n : ℕ} (a b c e : Fin K) (r : Fin K → Pt n) : ℝ :=
  ∑ i, segCLM a b r i * segCLM c e r i

/-- **内层对 `r` 可微**——逐项乘积法则后求和。 -/
theorem bilinearSum_differentiableAt {K n : ℕ} (a b c e : Fin K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => bilinearSum a b c e r) p := by
  refine DifferentiableAt.sum (u := Finset.univ) ?_
  intro i _
  have hf : HasFDerivAt (fun r : Fin K → Pt n => segCLM a b r i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp (segCLM a b)) p :=
    ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp (segCLM a b))
  have hg : HasFDerivAt (fun r : Fin K → Pt n => segCLM c e r i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp (segCLM c e)) p :=
    ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp (segCLM c e))
  exact (hf.mul hg).differentiableAt

/-- ⭐⭐ **`perpendicular` 分支可微**：`(∑ i, seg a b i · seg c e i)²`。 -/
theorem perpendicular_differentiableAt {K n : ℕ} (a b c e : ℕ)
    (ha : a < K) (hb : b < K) (hc : c < K) (he : e < K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n => (∑ i, seg (trunc r) a b i * seg (trunc r) c e i) ^ 2) p := by
  have hfun : (fun r : Fin K → Pt n => (∑ i, seg (trunc r) a b i * seg (trunc r) c e i) ^ 2)
      = fun r : Fin K → Pt n => bilinearSum ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨e, he⟩ r ^ 2 := by
    funext r
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [bilinearSum, seg, segCLM_apply]
  rw [hfun]
  have hb_ := bilinearSum_differentiableAt ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨e, he⟩ p
  -- `y ↦ y²` composed with the bilinear sum
  exact (differentiableAt_id.pow 2).comp p hb_

/-- ⭐⭐ **`rightAngle` 分支可微**：`(∑ i, seg a b i · seg b c i)²`。

**与 `perpendicular` 同形**，只是第二条 `seg` 是 `b → c` 而不是 `c → e`。 -/
theorem rightAngle_differentiableAt {K n : ℕ} (a b c : ℕ)
    (ha : a < K) (hb : b < K) (hc : c < K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n => (∑ i, seg (trunc r) a b i * seg (trunc r) b c i) ^ 2) p := by
  have hfun : (fun r : Fin K → Pt n => (∑ i, seg (trunc r) a b i * seg (trunc r) b c i) ^ 2)
      = fun r : Fin K → Pt n => bilinearSum ⟨a, ha⟩ ⟨b, hb⟩ ⟨b, hb⟩ ⟨c, hc⟩ r ^ 2 := by
    funext r
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [bilinearSum, seg, segCLM_apply]
  rw [hfun]
  have hb_ := bilinearSum_differentiableAt ⟨a, ha⟩ ⟨b, hb⟩ ⟨b, hb⟩ ⟨c, hc⟩ p
  exact (differentiableAt_id.pow 2).comp p hb_

/-! ## `collinear` 与 `parallel`：**子式缺陷**

`minorDefect u v = ∑ i ∑ j (u i * v j − u j * v i)²`，**每一项是一个【二次】多项式的平方**。

**两次求和，每一项用 `Core.hasFDerivAt_sq_comp`**——
**内层 `u i * v j − u j * v i` 对 `r` 是二次的**（`u`、`v` 都随 `r` 动），**所以用乘积法则两次再相减。** -/

/-- **子式项**：`u i * v j − u j * v i`，其中 `u`、`v` 是由 `segCLM` 给出的线性映射。 -/
noncomputable def minorTerm {K n : ℕ} (u v : (Fin K → Pt n) →L[ℝ] Pt n)
    (i j : Fin n) (r : Fin K → Pt n) : ℝ :=
  u r i * v r j - u r j * v r i

/-- **子式项对 `r` 可微**——两次乘积法则再相减。 -/
theorem minorTerm_differentiableAt {K n : ℕ} (u v : (Fin K → Pt n) →L[ℝ] Pt n)
    (i j : Fin n) (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => minorTerm u v i j r) p :=
  ((ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u)).mul
    (ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp v))).differentiableAt.sub
    ((ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp u)).mul
    (ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v))).differentiableAt

/-- ⭐⭐ **`minorDefect` 复合 `trunc` 后可微**。 -/
theorem minorDefect_differentiableAt {K n : ℕ} (u v : (Fin K → Pt n) →L[ℝ] Pt n)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n => minorDefect (u r) (v r)) p := by
  have hfun : (fun r : Fin K → Pt n => minorDefect (u r) (v r))
      = fun r : Fin K → Pt n => ∑ i : Fin n, ∑ j : Fin n, minorTerm u v i j r ^ 2 := by
    funext r
    simp only [minorDefect, minorTerm]
  rw [hfun]
  refine DifferentiableAt.sum (u := Finset.univ) ?_
  intro i _
  refine DifferentiableAt.sum (u := Finset.univ) ?_
  intro j _
  exact ((minorTerm_differentiableAt u v i j p).pow 2)

/-- ⭐⭐ **`collinear` 分支可微**：`minorDefect (seg · a b) (seg · a c)`。 -/
theorem collinear_differentiableAt {K n : ℕ} (a b c : ℕ)
    (ha : a < K) (hb : b < K) (hc : c < K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n => minorDefect (seg (trunc r) a b) (seg (trunc r) a c)) p := by
  have hfun : (fun r : Fin K → Pt n => minorDefect (seg (trunc r) a b) (seg (trunc r) a c))
      = fun r : Fin K → Pt n => minorDefect (segCLM ⟨a, ha⟩ ⟨b, hb⟩ r) (segCLM ⟨a, ha⟩ ⟨c, hc⟩ r) := by
    funext r
    congr 1 <;> funext i <;> simp only [seg, segCLM_apply]
  rw [hfun]
  exact minorDefect_differentiableAt _ _ p

/-- ⭐⭐ **`parallel` 分支可微**：`minorDefect (seg · a b) (seg · c e)`。 -/
theorem parallel_differentiableAt {K n : ℕ} (a b c e : ℕ)
    (ha : a < K) (hb : b < K) (hc : c < K) (he : e < K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n => minorDefect (seg (trunc r) a b) (seg (trunc r) c e)) p := by
  have hfun : (fun r : Fin K → Pt n => minorDefect (seg (trunc r) a b) (seg (trunc r) c e))
      = fun r : Fin K → Pt n =>
          minorDefect (segCLM ⟨a, ha⟩ ⟨b, hb⟩ r) (segCLM ⟨c, hc⟩ ⟨e, he⟩ r) := by
    funext r
    congr 1 <;> funext i <;> simp only [seg, segCLM_apply]
  rw [hfun]
  exact minorDefect_differentiableAt _ _ p

/-! ## ⭐⭐⭐ 装配：`penaltyLossFDeriv` 与 `hasFDerivAt_penaltyLoss`

**九支的内层配料全部就位**（`evalPtsFDeriv`、`sqDistFDeriv`、`segCLM`、`bilinearSum`、`minorTerm`、`midpointCLM`），
**本节把它们装配成一条 `match` 定义的 `(Fin K → Pt n) →L[ℝ] ℝ`。**

## 设计决定：`max` 三支怎么办

`leZero`/`ltZero`/`gtZero` 走 `max · 0`，**在折点 `evalPts e = 0` 处不可导。**

**⇒ 定义里用 `(2 * max (evalPts e (trunc p)) 0) • evalPtsFDeriv e`**——
**折点处这个系数恰好是 `0`，所以定义处处$是$一条连续线性泛函**；
**而定理带前提 `evalPts e (trunc p) ≠ 0`，在那里它才是真导数。**

**这样「定义全、定理诚实」**：定义不需要分部，定理明确说出适用范围。

## `ConstraintIndicesBelow`

`IndicesBelow`（`ExprDerivative` 里）只处理 `GeoExpr`。**约束级的前提对 12 个构造子逐支给出**：
每个 `ℕ` 索引 `< K`，每个 `GeoExpr` 的 `IndicesBelow` 成立。 -/

/-- **约束级索引前提**：所有点索引 `< K`，且所有表达式只读界内点。 -/
def ConstraintIndicesBelow {n : ℕ} (c : GeoConstraint n) (K : ℕ) : Prop :=
  match c with
  | .eqZero e => IndicesBelow e K
  | .leZero e => IndicesBelow e K
  | .ltZero e => IndicesBelow e K
  | .gtZero e => IndicesBelow e K
  | .sqDistEq a b d => a < K ∧ b < K ∧ IndicesBelow d K
  | .equalLength a b c e => a < K ∧ b < K ∧ c < K ∧ e < K
  | .collinear a b c => a < K ∧ b < K ∧ c < K
  | .perpendicular a b c e => a < K ∧ b < K ∧ c < K ∧ e < K
  | .parallel a b c e => a < K ∧ b < K ∧ c < K ∧ e < K
  | .rightAngle a b c => a < K ∧ b < K ∧ c < K
  | .midpoint m a b => m < K ∧ a < K ∧ b < K
  | .samePoint a b => a < K ∧ b < K

/-- ⭐ **`max (evalPts e) 0` 在非折点处可微**。

**非折点前提 `evalPts e (trunc p) > 0` 让 `max · 0` 在 `p` 的一个邻域内就是恒等**，
**所以它的平方在那里等于 `evalPts e ²`，用 `DifferentiableAt.congr_of_eventuallyEq` 接过去。**

**⚠ 这里取 `0 < evalPts e` 而不是 `≠ 0`**——`leZero`/`ltZero` 的 `max · 0` 只在【正】侧才等于恒等；
**在负侧它恒为 0，那里也可微（导数 0），但那需要分情况，本轮不做。** -/
theorem maxZero_pos_differentiableAt {K n : ℕ} (e : GeoExpr n) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) (hpos : 0 < GeoExpr.evalPts e (trunc p)) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => (max (GeoExpr.evalPts e (trunc r)) 0) ^ 2) p := by
  have hev : DifferentiableAt ℝ (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r)) p :=
    evalPts_differentiableAt e hK p
  have hcont : ContinuousAt (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r)) p :=
    hev.continuousAt
  have hev_pos : ∀ᶠ r in nhds p, 0 < GeoExpr.evalPts e (trunc r) :=
    hcont.eventually (isOpen_Ioi.mem_nhds hpos)
  have hsq : DifferentiableAt ℝ (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r) ^ 2) p :=
    (differentiableAt_id.pow 2).comp p hev
  refine hsq.congr_of_eventuallyEq ?_
  filter_upwards [hev_pos] with r hr
  simp only [max_eq_left (le_of_lt hr)]

/-! ## ⭐⭐⭐ 总定理：`penaltyLoss` 在非折点处可微

**十二支里九支无条件是导数，三支（`max` 族）需要「不在折点」的前提。
本节给出统一的定理，把这两类放在同一个陈述里。**

**前提的形状**：
1. `ConstraintIndicesBelow c K`——所有点索引界内；
2. **对 `leZero`／`ltZero`／`gtZero` 的表达式，`0 < evalPts e (trunc p)`**——
   用一个谓词 `NoKink c p` 统一表述。

**⚠ 这是本轮能做到的最强形式**：**`max · 0` 在负侧虽然也可微（导数 0），
但那条要么额外分情况、要么把 `max` 换成 `if`，两条都会让陈述比「真实」更弱。
所以 `NoKink` 只排除正侧折点，其余情形由九支覆盖。** -/

/-- **三支 `max` 的前提**：`leZero`／`ltZero` 要求内层取正值，
`gtZero` 要求内层也取正值（因为它的内层是 `-evalPts`，所以那里 `max` 恒为 `0`）。 -/
def KinkPositive {n : ℕ} (c : GeoConstraint n) (K : ℕ) (p : Fin K → Pt n) : Prop :=
  match c with
  | .leZero e => 0 < GeoExpr.evalPts e (trunc p)
  | .ltZero e => 0 < GeoExpr.evalPts e (trunc p)
  | .gtZero e => 0 < GeoExpr.evalPts e (trunc p)
  | _ => True

/-- ⭐⭐⭐ **`penaltyLoss` 的九支在 `trunc p` 处都可微**。

**这是一条 `match` 定义的定理**，**每一支由前面各节的分支定理直接给出**——
**所以它同时是「九支都成立」的证明，也是它们的目录。** -/
theorem penaltyLoss_differentiableAt {K n : ℕ} (c : GeoConstraint n)
    (hK : ConstraintIndicesBelow c K) (p : Fin K → Pt n)
    (hk : KinkPositive c K p) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => penaltyLoss c (trunc r)) p := by
  match c, hK with
  | .eqZero e, hK =>
      exact eqZero_differentiableAt e hK p
  | .leZero e, hK =>
      have h : 0 < GeoExpr.evalPts e (trunc p) := hk
      have hfun : (fun r : Fin K → Pt n => penaltyLoss (.leZero e) (trunc r))
          = fun r : Fin K → Pt n => (max (GeoExpr.evalPts e (trunc r)) 0) ^ 2 := by
        funext r
        simp only [penaltyLoss]
      rw [hfun]
      exact maxZero_pos_differentiableAt e hK p h
  | .ltZero e, hK =>
      have h : 0 < GeoExpr.evalPts e (trunc p) := hk
      have hfun : (fun r : Fin K → Pt n => penaltyLoss (.ltZero e) (trunc r))
          = fun r : Fin K → Pt n => (max (GeoExpr.evalPts e (trunc r)) 0) ^ 2 := by
        funext r
        simp only [penaltyLoss]
      rw [hfun]
      exact maxZero_pos_differentiableAt e hK p h
  | .gtZero e, hK =>
      have h : 0 < GeoExpr.evalPts e (trunc p) := hk
      have hfun : (fun r : Fin K → Pt n => penaltyLoss (.gtZero e) (trunc r))
          = fun r : Fin K → Pt n => (max (-(GeoExpr.evalPts e (trunc r))) 0) ^ 2 := by
        funext r
        simp only [penaltyLoss]
      rw [hfun]
      -- with `x > 0`, `max (-x) 0` is constantly `0` near `p`, so its square is too
      have hev : DifferentiableAt ℝ (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r)) p :=
        evalPts_differentiableAt e hK p
      have hev_neg : ∀ᶠ r in nhds p, 0 < GeoExpr.evalPts e (trunc r) :=
        hev.continuousAt.eventually (isOpen_Ioi.mem_nhds h)
      have hconst : (fun r : Fin K → Pt n => (max (-(GeoExpr.evalPts e (trunc r))) 0) ^ 2)
          =ᶠ[nhds p] fun _ => (0 : ℝ) := by
        filter_upwards [hev_neg] with r hr
        simp only [max_eq_right (by linarith : -GeoExpr.evalPts e (trunc r) ≤ 0)]
        ring
      exact (differentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hconst
  | .sqDistEq a b d, ⟨ha, hb, hd⟩ =>
      exact sqDistEq_differentiableAt a b d ha hb hd p
  | .equalLength a b c e, ⟨ha, hb, hc, he⟩ =>
      exact equalLength_differentiableAt a b c e ha hb hc he p
  | .collinear a b c, ⟨ha, hb, hc⟩ =>
      exact collinear_differentiableAt a b c ha hb hc p
  | .perpendicular a b c e, ⟨ha, hb, hc, he⟩ =>
      exact perpendicular_differentiableAt a b c e ha hb hc he p
  | .parallel a b c e, ⟨ha, hb, hc, he⟩ =>
      exact parallel_differentiableAt a b c e ha hb hc he p
  | .rightAngle a b c, ⟨ha, hb, hc⟩ =>
      exact rightAngle_differentiableAt a b c ha hb hc p
  | .midpoint m a b, ⟨hm, ha, hb⟩ =>
      exact midpoint_differentiableAt m a b hm ha hb p
  | .samePoint a b, ⟨ha, hb⟩ =>
      exact samePoint_differentiableAt a b ha hb p

/-! ## ⭐⭐⭐ 显式导函数 `penaltyLossFDeriv`

**十二支一条 `match` 定义的 `(Fin K → Pt n) →L[ℝ] ℝ`**，**每支复用前面各节的配料。**

| 分支 | 导数 |
|:--|:--|
| `eqZero e` | `(2 * evalPts e) • evalPtsFDeriv e` |
| `leZero e`／`ltZero e` | `(2 * max (evalPts e) 0) • evalPtsFDeriv e` |
| `gtZero e` | `(2 * max (-(evalPts e)) 0) • (-(evalPtsFDeriv e))` |
| `sqDistEq a b d` | `(2 * (sqDist − evalPts d)) • (sqDistFDerivX − evalPtsFDeriv d)` |
| `equalLength a b c e` | `(2 * (sqDist − sqDist)) • (sqDistFDerivX − sqDistFDerivX)` |
| `collinear a b c` | `minorDefectFDeriv (seg · a b) (seg · a c)` |
| `perpendicular a b c e` | `(2 * bilinearSum) • bilinearSumFDeriv` |
| `parallel a b c e` | `minorDefectFDeriv (seg · a b) (seg · c e)` |
| `rightAngle a b c` | `(2 * bilinearSum') • bilinearSumFDeriv'` |
| `midpoint m a b` | `∑ i, (2 * (midpointCLM r i)) • (proj i ∘ midpointCLM)` |
| `samePoint a b` | `sqDistFDerivX` |

**⚠ 三条辅助导数先定义**：`sqDistFDerivX`（`sqDist` 复合 `pointProj` 的链式）、
`bilinearSumFDeriv`、`minorDefectFDeriv`。**它们的形状由 `Derivative.fderiv` 决定，
所以定义写在它们之后。** -/

/-- **`sqDist (trunc · a) (trunc · b)` 的导数**（联合可微性 + 两个 `pointProj` 的乘积）。

**由 `sqDist` 在 `(x, y)` 上的联合导数经 `pairProj` 复合**——
**这里直接把它写成两条单槽导数的组合，因为 `sqDist` 对两个槽的偏导都是 `(2(x−y)) • proj`。** -/
noncomputable def sqDistPairFDeriv {K n : ℕ} (a b : Fin K) (p : Fin K → Pt n) :
    (Fin K → Pt n) →L[ℝ] ℝ :=
  (sqDistFDeriv (p a) (p b)).comp (pointProj a) + (sqDistFDeriv (p b) (p a)).comp (pointProj b)

/-- **`bilinearSum` 的导数**：`∑ i, (v p i) • (proj i ∘ u) + (u p i) • (proj i ∘ v)`。 -/
noncomputable def bilinearSumFDeriv {K n : ℕ} (u v : (Fin K → Pt n) →L[ℝ] Pt n)
    (p : Fin K → Pt n) : (Fin K → Pt n) →L[ℝ] ℝ :=
  ∑ i, ((u p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v)
    + (v p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u))

/-- **`midpointCLM` 平方和的导数**：`∑ i, (2 * (L p i)) • (proj i ∘ L)`。 -/
noncomputable def midpointSumFDeriv {K n : ℕ} (L : (Fin K → Pt n) →L[ℝ] Pt n)
    (p : Fin K → Pt n) : (Fin K → Pt n) →L[ℝ] ℝ :=
  ∑ i, (2 * (L p i)) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp L)

/-- **子式缺陷的导数**：对 `minorDefect u v = ∑ i ∑ j (u i v j − u j v i)²` 逐项求导。

**每一项 `(u i v j − u j v i)²` 的导数是
`2(u i v j − u j v i) • (v j • (proj i ∘ u) + u i • (proj j ∘ v) − v i • (proj j ∘ u) − u j • (proj i ∘ v))`。** -/
noncomputable def minorDefectFDeriv {K n : ℕ} (u v : (Fin K → Pt n) →L[ℝ] Pt n)
    (p : Fin K → Pt n) : (Fin K → Pt n) →L[ℝ] ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (2 * (u p i * v p j - u p j * v p i)) •
      (((u p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp v)
        + (v p j) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u))
        - ((u p j) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v)
        + (v p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp u)))

/-- ⭐⭐⭐ **`penaltyLoss` 的显式导数**——十二支一条 `match` 定义的连续线性泛函。

**三支 `max` 用 `(2 * max x 0) • (·)′`**：**折点处系数是 `0`，所以定义处处是一条 CLM**
（但只有 `KinkPositive` 成立处它才是真导数——见 `penaltyLoss_differentiableAt`）。 -/
noncomputable def penaltyLossFDeriv {K n : ℕ} (c : GeoConstraint n)
    (hK : ConstraintIndicesBelow c K) (p : Fin K → Pt n) : (Fin K → Pt n) →L[ℝ] ℝ :=
  match c, hK with
  | .eqZero e, hK =>
      (2 * GeoExpr.evalPts e (trunc p)) • evalPtsFDeriv e K hK p
  | .leZero e, hK =>
      (2 * max (GeoExpr.evalPts e (trunc p)) 0) • evalPtsFDeriv e K hK p
  | .ltZero e, hK =>
      (2 * max (GeoExpr.evalPts e (trunc p)) 0) • evalPtsFDeriv e K hK p
  | .gtZero e, hK =>
      (2 * max (-(GeoExpr.evalPts e (trunc p))) 0) • (-(evalPtsFDeriv e K hK p))
  | .sqDistEq a b d, hK =>
      (2 * (sqDist (trunc p a) (trunc p b) - GeoExpr.evalPts d (trunc p))) •
        (sqDistPairFDeriv ⟨a, hK.1⟩ ⟨b, hK.2.1⟩ p - evalPtsFDeriv d K hK.2.2 p)
  | .equalLength a b c e, hK =>
      (2 * (sqDist (trunc p a) (trunc p b) - sqDist (trunc p c) (trunc p e))) •
        (sqDistPairFDeriv ⟨a, hK.1⟩ ⟨b, hK.2.1⟩ p - sqDistPairFDeriv ⟨c, hK.2.2.1⟩ ⟨e, hK.2.2.2⟩ p)
  | .collinear a b c, hK =>
      minorDefectFDeriv (segCLM ⟨a, hK.1⟩ ⟨b, hK.2.1⟩) (segCLM ⟨a, hK.1⟩ ⟨c, hK.2.2⟩) p
  | .perpendicular a b c e, hK =>
      (2 * bilinearSum ⟨a, hK.1⟩ ⟨b, hK.2.1⟩ ⟨c, hK.2.2.1⟩ ⟨e, hK.2.2.2⟩ p) •
        (bilinearSumFDeriv (segCLM ⟨a, hK.1⟩ ⟨b, hK.2.1⟩) (segCLM ⟨c, hK.2.2.1⟩ ⟨e, hK.2.2.2⟩) p)
  | .parallel a b c e, hK =>
      minorDefectFDeriv (segCLM ⟨a, hK.1⟩ ⟨b, hK.2.1⟩) (segCLM ⟨c, hK.2.2.1⟩ ⟨e, hK.2.2.2⟩) p
  | .rightAngle a b c, hK =>
      (2 * bilinearSum ⟨a, hK.1⟩ ⟨b, hK.2.1⟩ ⟨b, hK.2.1⟩ ⟨c, hK.2.2⟩ p) •
        (bilinearSumFDeriv (segCLM ⟨a, hK.1⟩ ⟨b, hK.2.1⟩) (segCLM ⟨b, hK.2.1⟩ ⟨c, hK.2.2⟩) p)
  | .midpoint m a b, hK =>
      midpointSumFDeriv (midpointCLM ⟨m, hK.1⟩ ⟨a, hK.2.1⟩ ⟨b, hK.2.2⟩) p
  | .samePoint a b, hK =>
      sqDistPairFDeriv ⟨a, hK.1⟩ ⟨b, hK.2⟩ p

/-- ⭐⭐⭐ **`penaltyLossFDeriv` 的求值**：它在方向 `d` 上的值。

**这是「梯度可计算」的准确形式**——**下游可以把 `d` 取成坐标方向 `e_k` 而得到梯度的每个分量，
不需要知道 `fderiv` 是什么。** -/
theorem penaltyLossFDeriv_apply {K n : ℕ} (c : GeoConstraint n)
    (hK : ConstraintIndicesBelow c K) (p d : Fin K → Pt n) :
    penaltyLossFDeriv c hK p d
      = match c, hK with
        | .eqZero e, hK =>
            (2 * GeoExpr.evalPts e (trunc p)) * (evalPtsFDeriv e K hK p d)
        | .leZero e, hK =>
            (2 * max (GeoExpr.evalPts e (trunc p)) 0) * (evalPtsFDeriv e K hK p d)
        | .ltZero e, hK =>
            (2 * max (GeoExpr.evalPts e (trunc p)) 0) * (evalPtsFDeriv e K hK p d)
        | .gtZero e, hK =>
            (2 * max (-(GeoExpr.evalPts e (trunc p))) 0) * (-(evalPtsFDeriv e K hK p d))
        | .sqDistEq a b e, hK =>
            (2 * (sqDist (trunc p a) (trunc p b) - GeoExpr.evalPts e (trunc p))) *
              (sqDistPairFDeriv ⟨a, hK.1⟩ ⟨b, hK.2.1⟩ p d - evalPtsFDeriv e K hK.2.2 p d)
        | .equalLength a b c' e, hK =>
            (2 * (sqDist (trunc p a) (trunc p b) - sqDist (trunc p c') (trunc p e))) *
              (sqDistPairFDeriv ⟨a, hK.1⟩ ⟨b, hK.2.1⟩ p d
                - sqDistPairFDeriv ⟨c', hK.2.2.1⟩ ⟨e, hK.2.2.2⟩ p d)
        | .collinear a b c', hK =>
            minorDefectFDeriv (segCLM ⟨a, hK.1⟩ ⟨b, hK.2.1⟩) (segCLM ⟨a, hK.1⟩ ⟨c', hK.2.2⟩) p d
        | .perpendicular a b c' e, hK =>
            (2 * bilinearSum ⟨a, hK.1⟩ ⟨b, hK.2.1⟩ ⟨c', hK.2.2.1⟩ ⟨e, hK.2.2.2⟩ p) *
              (bilinearSumFDeriv (segCLM ⟨a, hK.1⟩ ⟨b, hK.2.1⟩)
                (segCLM ⟨c', hK.2.2.1⟩ ⟨e, hK.2.2.2⟩) p d)
        | .parallel a b c' e, hK =>
            minorDefectFDeriv (segCLM ⟨a, hK.1⟩ ⟨b, hK.2.1⟩) (segCLM ⟨c', hK.2.2.1⟩ ⟨e, hK.2.2.2⟩) p d
        | .rightAngle a b c', hK =>
            (2 * bilinearSum ⟨a, hK.1⟩ ⟨b, hK.2.1⟩ ⟨b, hK.2.1⟩ ⟨c', hK.2.2⟩ p) *
              (bilinearSumFDeriv (segCLM ⟨a, hK.1⟩ ⟨b, hK.2.1⟩) (segCLM ⟨b, hK.2.1⟩ ⟨c', hK.2.2⟩) p d)
        | .midpoint m a b, hK =>
            midpointSumFDeriv (midpointCLM ⟨m, hK.1⟩ ⟨a, hK.2.1⟩ ⟨b, hK.2.2⟩) p d
        | .samePoint a b, hK =>
            sqDistPairFDeriv ⟨a, hK.1⟩ ⟨b, hK.2⟩ p d := by
  match c, hK with
  | .eqZero e, hK => simp only [penaltyLossFDeriv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  | .leZero e, hK => simp only [penaltyLossFDeriv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  | .ltZero e, hK => simp only [penaltyLossFDeriv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  | .gtZero e, hK =>
      simp only [penaltyLossFDeriv, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.neg_apply, smul_eq_mul]
  | .sqDistEq a b e, hK =>
      simp only [penaltyLossFDeriv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        smul_eq_mul]
  | .equalLength a b c' e, hK =>
      simp only [penaltyLossFDeriv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        smul_eq_mul]
  | .collinear a b c', hK => simp only [penaltyLossFDeriv]
  | .perpendicular a b c' e, hK =>
      simp only [penaltyLossFDeriv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  | .parallel a b c' e, hK => simp only [penaltyLossFDeriv]
  | .rightAngle a b c', hK =>
      simp only [penaltyLossFDeriv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  | .midpoint m a b, hK => simp only [penaltyLossFDeriv]
  | .samePoint a b, hK => simp only [penaltyLossFDeriv]

/-! ## ⭐⭐⭐ `HasFDerivAt` 版本的三支 `max` 与总装配

**第 121 轮给的三支 `max` 只有 `DifferentiableAt`**，**而装配需要 `HasFDerivAt` 且导数【恰好】是
`penaltyLossFDeriv` 的形状。**

**`HasFDerivAt.congr_of_eventuallyEq` 的方向（探针确认）：`h.congr_of_eventuallyEq (g =ᶠ f)`**——
**即 `h` 是已知可微的那个 `f`，`g` 是目标。** -/

/-- ⭐⭐ **`leZero`／`ltZero` 的 `HasFDerivAt`**：非折点处导数是 `(2x) • evalPtsFDeriv`。 -/
theorem hasFDerivAt_maxZero_pos {K n : ℕ} (e : GeoExpr n) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) (hpos : 0 < GeoExpr.evalPts e (trunc p)) :
    HasFDerivAt (fun r : Fin K → Pt n => (max (GeoExpr.evalPts e (trunc r)) 0) ^ 2)
      ((2 * GeoExpr.evalPts e (trunc p)) • evalPtsFDeriv e K hK p) p := by
  have hd := hasFDerivAt_evalPts e hK p
  have hsq := Lattice.Core.hasFDerivAt_sq_comp hd
  have hev_pos : ∀ᶠ r in nhds p, 0 < GeoExpr.evalPts e (trunc r) :=
    hd.differentiableAt.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
  refine hsq.congr_of_eventuallyEq ?_
  filter_upwards [hev_pos] with r hr
  simp only [max_eq_left (le_of_lt hr)]

/-- ⭐⭐ **`gtZero` 的 `HasFDerivAt`**：非折点处（`evalPts e > 0`）导数是 `0`。

**邻域内 `max (-x) 0 = 0`，所以平方恒为 `0`；而声明的导数 `(2 · max (-x) 0) • …` 的系数也正是 `0`，
两者一致。** -/
theorem hasFDerivAt_negMaxZero_pos {K n : ℕ} (e : GeoExpr n) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) (hpos : 0 < GeoExpr.evalPts e (trunc p)) :
    HasFDerivAt (fun r : Fin K → Pt n => (max (-(GeoExpr.evalPts e (trunc r))) 0) ^ 2)
      ((2 * max (-(GeoExpr.evalPts e (trunc p))) 0) • (-(evalPtsFDeriv e K hK p))) p := by
  have hd := hasFDerivAt_evalPts e hK p
  have hev_pos : ∀ᶠ r in nhds p, 0 < GeoExpr.evalPts e (trunc r) :=
    hd.differentiableAt.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
  have hconst : (fun r : Fin K → Pt n => (max (-(GeoExpr.evalPts e (trunc r))) 0) ^ 2)
      =ᶠ[nhds p] fun _ => (0 : ℝ) := by
    filter_upwards [hev_pos] with r hr
    have hz : max (-(GeoExpr.evalPts e (trunc r))) 0 = 0 := max_eq_right (by linarith)
    rw [hz]
    ring
  have hcoef : max (-(GeoExpr.evalPts e (trunc p))) 0 = 0 := max_eq_right (by linarith)
  have hzero : ((2 * max (-(GeoExpr.evalPts e (trunc p))) 0) •
      (-(evalPtsFDeriv e K hK p))) = (0 : (Fin K → Pt n) →L[ℝ] ℝ) := by
    rw [hcoef]
    simp only [mul_zero, zero_smul]
  rw [hzero]
  exact (hasFDerivAt_const (x := p) (c := (0 : ℝ))).congr_of_eventuallyEq hconst

/-! ## ⭐⭐ 四条 `HasFDerivAt` 前件（装配所需）

**第 112–120 轮的分支定理大多只给 `DifferentiableAt`**，**而装配需要 `HasFDerivAt`，
并且导数必须【逐字】是前面定义的闭式。**

**关键技巧**：`HasFDerivAt.sum` 的导数是 `∑ i, f' i`，**所以闭式的定义就写成同一个 `∑` 形式**——
**求和的导数与定义逐字对上，装配时不需要 `convert`。** -/

/-- **`midpointSum` 的导数**：`∑ i, (2 · L p i) • (proj i ∘ L)`。 -/
theorem hasFDerivAt_midpointSum {K n : ℕ} (L : (Fin K → Pt n) →L[ℝ] Pt n) (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => ∑ i, (L r i) ^ 2) (midpointSumFDeriv L p) p := by
  have hterm : ∀ i : Fin n, HasFDerivAt (fun r : Fin K → Pt n => (L r i) ^ 2)
      ((2 * (L p i)) •
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp L)) p := by
    intro i
    exact Lattice.Core.hasFDerivAt_sq_comp
      (ContinuousLinearMap.hasFDerivAt
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp L))
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ => hterm i)
  simpa only [midpointSumFDeriv] using h

/-- **`bilinearSum` 的导数**：逐项乘积法则后求和。 -/
theorem hasFDerivAt_bilinearSum {K n : ℕ} (u v : (Fin K → Pt n) →L[ℝ] Pt n)
    (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => ∑ i, u r i * v r i) (bilinearSumFDeriv u v p) p := by
  have hterm : ∀ i : Fin n, HasFDerivAt (fun r : Fin K → Pt n => u r i * v r i)
      ((u p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v)
        + (v p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u)) p := by
    intro i
    have hu : HasFDerivAt (fun r : Fin K → Pt n => u r i)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u) p :=
      ContinuousLinearMap.hasFDerivAt
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u)
    have hv : HasFDerivAt (fun r : Fin K → Pt n => v r i)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v) p :=
      ContinuousLinearMap.hasFDerivAt
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v)
    exact hu.mul hv
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ => hterm i)
  simpa only [bilinearSumFDeriv] using h

/-- **`minorDefect` 的导数**：两层求和，每项一次平方链式（内层四个乘积相加减）。 -/
theorem hasFDerivAt_minorDefect {K n : ℕ} (u v : (Fin K → Pt n) →L[ℝ] Pt n)
    (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => ∑ i : Fin n, ∑ j : Fin n,
        (u r i * v r j - u r j * v r i) ^ 2) (minorDefectFDeriv u v p) p := by
  have hinner : ∀ i : Fin n, HasFDerivAt
      (fun r : Fin K → Pt n => ∑ j : Fin n, (u r i * v r j - u r j * v r i) ^ 2)
      (∑ j : Fin n,
        (2 * (u p i * v p j - u p j * v p i)) •
          (((u p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp v)
            + (v p j) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u))
            - ((u p j) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v)
            + (v p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp u)))) p := by
    intro i
    have hterm : ∀ j : Fin n, HasFDerivAt
        (fun r : Fin K → Pt n => (u r i * v r j - u r j * v r i) ^ 2)
        ((2 * (u p i * v p j - u p j * v p i)) •
          (((u p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp v)
            + (v p j) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u))
            - ((u p j) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v)
            + (v p i) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp u)))) p := by
      intro j
      have hpui : HasFDerivAt (fun r : Fin K → Pt n => u r i)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u) p :=
        ContinuousLinearMap.hasFDerivAt
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp u)
      have hpvj : HasFDerivAt (fun r : Fin K → Pt n => v r j)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp v) p :=
        ContinuousLinearMap.hasFDerivAt
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp v)
      have hpuj : HasFDerivAt (fun r : Fin K → Pt n => u r j)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp u) p :=
        ContinuousLinearMap.hasFDerivAt
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp u)
      have hpvi : HasFDerivAt (fun r : Fin K → Pt n => v r i)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v) p :=
        ContinuousLinearMap.hasFDerivAt
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp v)
      exact Lattice.Core.hasFDerivAt_sq_comp ((hpui.mul hpvj).sub (hpuj.mul hpvi))
    exact HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun j _ => hterm j)
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ => hinner i)
  simpa only [minorDefectFDeriv] using h

/-- **`minorDefect` 复合两个线性映射的导数**——装配里用的形式。 -/
theorem hasFDerivAt_minorDefect_seg {K n : ℕ} (u v : (Fin K → Pt n) →L[ℝ] Pt n)
    (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n =>
        minorDefect (u r) (v r)) (minorDefectFDeriv u v p) p := by
  have hfun : (fun r : Fin K → Pt n => minorDefect (u r) (v r))
      = fun r : Fin K → Pt n => ∑ i : Fin n, ∑ j : Fin n, (u r i * v r j - u r j * v r i) ^ 2 := by
    funext r
    simp only [minorDefect]
  rw [hfun]
  exact hasFDerivAt_minorDefect u v p

/-- **`sqDist (trunc · a) (trunc · b)` 可微**——由 `sqDist` 在 `(x, y)` 上的联合可微性经线性配对映射复合。

**⚠ 这里只给【可微性】**：把 `fderiv` 的显式形式与 `sqDistPairFDeriv` 对齐需要拆开联合 `fderiv`，
**那是一条独立的引理（`fderiv_sqDist_left` 已给出单槽版本，联合版本尚未做）。** -/
theorem differentiableAt_sqDist_pair {K n : ℕ} (a b : Fin K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => sqDist (trunc r a) (trunc r b)) p := by
  have hjoint : DifferentiableAt ℝ (fun r : Pt n × Pt n => sqDist r.1 r.2)
      (trunc p a.val, trunc p b.val) := by
    have hfun : (fun r : Pt n × Pt n => sqDist r.1 r.2)
        = fun r : Pt n × Pt n => ∑ i, (r.1 i - r.2 i) ^ 2 := by
      funext r
      exact sqDist_eq_sum r.1 r.2
    rw [hfun]
    fun_prop
  have hpair : DifferentiableAt ℝ (fun r : Fin K → Pt n => (trunc r a, trunc r b)) p :=
    ((hasFDerivAt_truncPoint a.val a.isLt p).prod
      (hasFDerivAt_truncPoint b.val b.isLt p)).differentiableAt
  exact hjoint.comp p hpair

/-! ## ⭐⭐ `sqDist` 的联合导数，显式形式

**`sqDist x y = ∑ i, (x i − y i)²`，所以联合导数是**

```lean
sqDistJointFDeriv x y = ∑ i, (2(x i − y i)) • (proj i ∘ fst − proj i ∘ snd)
```

**这条 CLM 直接作用在 `(d₁, d₂)` 上得到 `∑ i, 2(x i − y i)(d₁ i − d₂ i)`——
与单槽版本 `sqDistFDeriv` 在「一个槽固定」时逐字一致。**

## 为什么需要它

**第 124 轮只证了 `differentiableAt_sqDist_pair`（`DifferentiableAt`）**，
**而装配需要「导数就是 `sqDistPairFDeriv`」。**
**有了联合 `HasFDerivAt`，`sqDist (trunc · a) (trunc · b)` 的导数就是它与 `pairProj` 的复合，
而 `sqDistPairFDeriv` 正是那条复合的展开式**——**所以最后一步是一次 `Finset.sum_congr` 加 `ring`。** -/

/-- **`sqDist` 在 `(x, y)` 上的联合导数**，显式 CLM。 -/
noncomputable def sqDistJointFDeriv {n : ℕ} (x y : Pt n) : (Pt n × Pt n) →L[ℝ] ℝ :=
  ∑ i, (2 * (x i - y i)) •
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
      (ContinuousLinearMap.fst ℝ (Pt n) (Pt n))
      - ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
        (ContinuousLinearMap.snd ℝ (Pt n) (Pt n)))

/-- **`sqDist` 的联合 `HasFDerivAt`**。 -/
theorem hasFDerivAt_sqDist_joint {n : ℕ} (x y : Pt n) :
    HasFDerivAt (fun r : Pt n × Pt n => sqDist r.1 r.2) (sqDistJointFDeriv x y) (x, y) := by
  have hfun : (fun r : Pt n × Pt n => sqDist r.1 r.2)
      = fun r : Pt n × Pt n => ∑ i, (r.1 i - r.2 i) ^ 2 := by
    funext r
    exact sqDist_eq_sum r.1 r.2
  rw [hfun]
  have hterm : ∀ i : Fin n,
      HasFDerivAt (fun r : Pt n × Pt n => (r.1 i - r.2 i) ^ 2)
        ((2 * (x i - y i)) •
          (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
            (ContinuousLinearMap.fst ℝ (Pt n) (Pt n))
            - ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
              (ContinuousLinearMap.snd ℝ (Pt n) (Pt n)))) (x, y) := by
    intro i
    have hfst : HasFDerivAt (fun r : Pt n × Pt n => r.1 i)
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
          (ContinuousLinearMap.fst ℝ (Pt n) (Pt n))) (x, y) :=
      ContinuousLinearMap.hasFDerivAt
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
          (ContinuousLinearMap.fst ℝ (Pt n) (Pt n)))
    have hsnd : HasFDerivAt (fun r : Pt n × Pt n => r.2 i)
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
          (ContinuousLinearMap.snd ℝ (Pt n) (Pt n))) (x, y) :=
      ContinuousLinearMap.hasFDerivAt
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
          (ContinuousLinearMap.snd ℝ (Pt n) (Pt n)))
    exact Lattice.Core.hasFDerivAt_sq_comp (hfst.sub hsnd)
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ => hterm i)
  simpa only [sqDistJointFDeriv] using h

/-! ## ⭐⭐ `sqDistPairFDeriv` 的求值与 `HasFDerivAt`

**第 125 轮卡在「联合导数与 `pairProj` 复合后与 `sqDistPairFDeriv` 的对齐」上**，
**原因是 `(fst ℝ _ _) (d1, d2)` 在 `simp only` 下不归约。**

**本节的绕法是**：**先把两条 CLM 各自的【求值】等式陈述出来**（它们只涉及 `proj`／`comp`／`smul`／`sum`，
这些的求值引理都存在），**再在【标量层面】做 `Finset.sum_congr` + `ring`**——
**于是 `fst`／`snd` 那一层完全不出现在证明里。** -/

/-- **`sqDistJointFDeriv` 的求值**：`∑ i, 2(x i − y i)(d₁ i − d₂ i)`。 -/
theorem sqDistJointFDeriv_apply {n : ℕ} (x y d1 d2 : Pt n) :
    sqDistJointFDeriv x y (d1, d2) = ∑ i, 2 * (x i - y i) * (d1 i - d2 i) := by
  simp only [sqDistJointFDeriv, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.fst, ContinuousLinearMap.snd,
    ContinuousLinearMap.coe_mk', LinearMap.fst_apply, LinearMap.snd_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- **`sqDistPairFDeriv` 的求值**：
`∑ i, 2(p a i − p b i) * d a i + ∑ i, 2(p b i − p a i) * d b i`。 -/
theorem sqDistPairFDeriv_apply {K n : ℕ} (a b : Fin K) (p d : Fin K → Pt n) :
    sqDistPairFDeriv a b p d
      = ∑ i, 2 * (p a i - p b i) * d a i + ∑ i, 2 * (p b i - p a i) * d b i := by
  simp only [sqDistPairFDeriv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    sqDistFDeriv_apply, pointProj, ContinuousLinearMap.proj_apply]

/-! ### ⚠ 未闭合：`hasFDerivAt_sqDist_pair_explicit`

**要证的是 `sqDist (trunc · a) (trunc · b)` 的导数【就是】`sqDistPairFDeriv`**，
**而这需要把「联合导数与 `pairProj` 复合后的求值」与 `sqDistPairFDeriv_apply` 的展开式对齐。**

**两条求值引理（`sqDistJointFDeriv_apply`、`sqDistPairFDeriv_apply`）都已证明**，
**所以两边都已经是具体的 `∑` 表达式**；**但把它们接起来需要穿过一串重写**：
`fst`／`snd` → `LinearMap.fst_apply`／`snd_apply` → `proj_apply` → `trunc` 的 `dif_pos`
→ `sqDistPairFDeriv_apply` → `Finset.sum_add_distrib`。

**第 126 轮已经把这串重写定位到最后一环（`trunc d a` 与 `d a` 的形式差）**，
**但没能一次走完，所以这里如实记录而未提交一个部分正确的定理。**

**⇒ 下一步的思路**：**不在 `pairProj` 复合这一层做，而是把 `sqDistPairFDeriv` 的定义【改写成
`sqDistJointFDeriv (p a) (p b) ∘ pairProj`】**——
**于是 `hasFDerivAt_sqDist_pair_explicit` 变成 `congr_fderiv` + `rfl`，
而对齐的那条等式被隔离成一条独立的、只关于 CLM 的引理。** -/

end Lattice.Geo
