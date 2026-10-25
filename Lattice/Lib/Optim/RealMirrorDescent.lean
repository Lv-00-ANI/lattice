import Mathlib
import Lattice.Lib.Optim.RealStrongConvex
/-!
# LATTICE: 镜像下降与遗憾界（Bregman 散度、强凸距离生成函数、O(√T) 遗憾）

本文件在一维 `ℝ` 上形式化镜像下降：

* **Bregman 散度** `B_h(x, y) = h y − h x − h'(x)·(y − x)`；凸性 ⟹ `≥ 0`，
  `h` 的 `μ`-强凸性 ⟹ `B_h(x,y) ≥ (μ/2)(y − x)²`；
* **三项恒等式**（纯代数）：`B_h(a,c) = B_h(a,b) + B_h(b,c) + (h'b − h'a)(c − b)`；
* **镜像步（极小刻画，无 `argmin`）**：
  `IsMirrorStep h h' g η x z ⟺ ∀ y, η g z + B_h(x,z) ≤ η g y + B_h(x,y)`，
  即 `z` 极小化 `y ↦ η g y + B_h(x,y)`；
* **镜像步存在性（二次势，完整证明）**：对二次势 `h(y) = y²/2`，
  `z = x − η g` 是镜像步（`mirror_step_exists_quadratic`）；
  **诚实降级**：一般 `μ`-强凸 `h` 上 `x − ηg/μ` **不是**镜像步——
  机器验证反例 `mirror_step_general_false`（`h(y)=y²/2+y⁴/4` 是 `1`-强凸，
  见证 `cubic_strongly_convex`；取 `ηg=1, x=0, y=−3/4` 镜像步不等式失效）。
* **单步界**：`η g(x − x*) ≤ (η²/(2μ)) g² + B_h(x, x*)`；
* **遗憾界的望远镜（条件形式）**：若每步满足标准望远镜不等式
  `η g_t(x_t − x*) ≤ B_h(x*, x_t) − B_h(x*, x_{t+1}) + (η²/(2μ)) g_t²`，则
  `∑_t g_t(x_t − x*) ≤ B_h(x*, x_0)/η + (η/(2μ)) ∑_t g_t²`（记 `B := B_h(x*,x_0)`）；
* **二次势（`h = y²/2`）的完整遗憾界**：此时 `B_h(x,y) = (y−x)²/2`，望远镜不等式
  **精确成立**（可证），于是得到 **OGD 的完整遗憾界**
  `∑_t g_t(x_t − x*) ≤ (x_0 − x*)²/(2η) + (η/2) ∑_t g_t²`。

**诚实边界（重要，降级说明）**：
- 一般 Bregman 势下的**望远镜不等式**（即「镜像步 ⟹ 标准单步遗憾不等式」的
  三项恒等式推导）本文件**未证**，它以显式假设 `hstep` 出现在
  `md_regret_bound` 中；本文件只**证明**了它的**二次势特例**
  （`euclidean_three_point`），后者恰好对应 OGD，所以 OGD 的遗憾界是**完整**的；
- 一般势的**单步界**（`md_single_step_bound`）是**完整**可证的，只是它的参考
  Bregman 是 `B_h(x_t, x*)` 而非 `B_h(x*, x_t)`，故不能直接望远镜；本文件把
  这一结构性差异如实标注；
- 约束集（单纯形/凸集）上的投影镜像下降 **未做**（本文件在 `ℝ` 上无约束）；
- 有限维 `Fin n` 分布单纯形版 **未做**；
- **O(√T)** 的代入最优步长：二次势下 `η = (x_0−x*)·(∑g²)^{-1/2}` 型的最优步长
  与 `√T` 显式率本文件给出**算术陈述**（`ogd_regret_sqrt`）但只用 `Real.sqrt` 的
  基本性质；若 `sqrt` 算术过重则标注为后续工作；
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、Bregman 散度 -/

/-- **Bregman 散度**（以距离生成函数的次梯度选择 `h'` 给出）：
`B_h(x, y) = h y − h x − h'(x)·(y − x)`。 -/
def Bregman (h h' : ℝ → ℝ) (x y : ℝ) : ℝ := h y - h x - h' x * (y - x)

/-- **非负性**：`h` 在 `x` 处的次梯度为 `h' x`（即 `∀ y, h y ≥ h x + h'x(y−x)`）⟹
`0 ≤ B_h(x,y)`。 -/
lemma bregman_nonneg {h h' : ℝ → ℝ} (hsub : ∀ x y : ℝ, h y ≥ h x + h' x * (y - x))
    (x y : ℝ) : 0 ≤ Bregman h h' x y := by
  unfold Bregman
  linarith [hsub x y]

/-- **强凸下界**：`h` 是 `μ`-强凸 ⟹ `(μ/2)(y − x)² ≤ B_h(x,y)`。 -/
lemma bregman_strong_lower {h h' : ℝ → ℝ} {mu : ℝ} (hSC : StrongConvex mu h h')
    (x y : ℝ) : (mu / 2) * (y - x) ^ 2 ≤ Bregman h h' x y := by
  unfold Bregman
  linarith [hSC x y]

/-- **Bregman 三项恒等式（纯代数）**：
`B_h(a,c) = B_h(a,b) + B_h(b,c) + (h'b − h'a)(c − b)`。 -/
lemma bregman_three_point (h h' : ℝ → ℝ) (a b c : ℝ) :
    Bregman h h' a c = Bregman h h' a b + Bregman h h' b c + (h' b - h' a) * (c - b) := by
  unfold Bregman
  ring

/-! ## 二、镜像步：极小刻画与存在性 -/

/-- **镜像步（极小刻画）**：`z` 极小化 `y ↦ η·g·y + B_h(x, y)`。
这是 `argmin` 的无选择形式化（与 `RealProximal.IsProx` 同风格）。 -/
def IsMirrorStep (h h' : ℝ → ℝ) (gt eta xt z : ℝ) : Prop :=
  ∀ y : ℝ, eta * gt * z + Bregman h h' xt z ≤ eta * gt * y + Bregman h h' xt y

/-- **镜像步存在性（二次势，完整证明）**：对**二次势** `h(y) = y²/2`、`h'(y) = y`
（属 `1`-强凸），`z = x − η·g` 是 `x` 处的镜像步。

**诚实降级（重要）**：一般 `μ`-强凸 `h` 上 `z = x − ηg/μ` **不是**镜像步——
本文件底部给出机器验证反例 `mirror_step_general_false`；
一般势的正确做法是解 `h'(z) = h'(x) − ηg`（镜像映射的隐式方程），
本文件**未做**。因此这里只证二次势特例（对应 OGD，是该文件遗憾界链条实际用到的情形）。 -/
theorem mirror_step_exists_quadratic {gt eta xt : ℝ} :
    IsMirrorStep (fun y : ℝ => y ^ 2 / 2) (fun y : ℝ => y) gt eta xt (xt - eta * gt) := by
  intro y
  simp only [Bregman]
  nlinarith [sq_nonneg (xt - eta * gt - y)]

/-- **一般 `μ`-强凸势下「镜像步存在性」为假（机器验证反例）**：
取 `h(y) = y²/2 + y⁴/4`、`h'(y) = y + y³`（`1`-强凸，见 `cubic_strongly_convex`），
`μ = 1`、`η·g = 1`、`x = 0`，则 `z = x − ηg/μ = −1` **不是**镜像步：
在 `y = −3/4` 处镜像步不等式失效。

这说明原命题「`μ`-强凸 ⟹ `x − ηg/μ` 是镜像步」**不成立**，
本文件把它如实标注为**未证/已证伪**，并以二次势特例
`mirror_step_exists_quadratic` 替代。 -/
theorem mirror_step_general_false :
    ¬ IsMirrorStep (fun y : ℝ => y ^ 2 / 2 + y ^ 4 / 4) (fun y : ℝ => y + y ^ 3) 1 1 0 (-1) := by
  intro h
  have h1 := h (-3 / 4)
  unfold Bregman at h1
  norm_num at h1

/-- `h(y) = y²/2 + y⁴/4` 配 `h'(y) = y + y³` 是 `1`-强凸（反例的合法性见证）。 -/
theorem cubic_strongly_convex :
    StrongConvex 1 (fun y : ℝ => y ^ 2 / 2 + y ^ 4 / 4) (fun y : ℝ => y + y ^ 3) := by
  intro x y
  have hkey : (y ^ 4 - x ^ 4) / 4 - x ^ 3 * (y - x)
      = (y - x) ^ 2 * (2 * x ^ 2 + (2 * x + (y - x)) ^ 2) / 4 := by
    ring
  have hnn : 0 ≤ (y - x) ^ 2 * (2 * x ^ 2 + (2 * x + (y - x)) ^ 2) / 4 := by positivity
  nlinarith [hkey, hnn]

/-! ## 三、单步界 -/

/-- **镜像下降单步界**：`μ > 0`、`h` 强凸、`z` 是 `x` 处的镜像步 ⟹
`η·g·(x − x*) ≤ (η²/(2μ))·g² + B_h(x, x*)`。

证明：极小性取 `y = x*` 与强凸下界（`B_h(x,z) ≥ (μ/2)(z−x)²`）相加，再用
`2ab ≤ a² + b²` 配平方。 -/
theorem md_single_step_bound {h h' : ℝ → ℝ} {mu gt eta xt xstar z : ℝ} (hmu : 0 < mu)
    (hSC : StrongConvex mu h h') (hstep : IsMirrorStep h h' gt eta xt z) :
    eta * gt * (xt - xstar) ≤ (eta ^ 2 / (2 * mu)) * gt ^ 2 + Bregman h h' xt xstar := by
  have hmin : eta * gt * z + Bregman h h' xt z ≤ eta * gt * xstar + Bregman h h' xt xstar :=
    hstep xstar
  have hsc : (mu / 2) * (z - xt) ^ 2 ≤ Bregman h h' xt z := bregman_strong_lower hSC xt z
  have hprod : eta * gt * (xt - z) ≤ (eta ^ 2 / (2 * mu)) * gt ^ 2 + (mu / 2) * (z - xt) ^ 2 := by
    have hsq : 0 ≤ (eta * gt - mu * (xt - z)) ^ 2 := sq_nonneg _
    have hexp : (eta * gt - mu * (xt - z)) ^ 2
        = (eta * gt) ^ 2 - 2 * mu * (eta * gt * (xt - z)) + mu ^ 2 * (xt - z) ^ 2 := by ring
    rw [hexp] at hsq
    have hgoal : 2 * mu * (eta * gt * (xt - z)) ≤ (eta * gt) ^ 2 + mu ^ 2 * (z - xt) ^ 2 := by
      rw [show (z - xt) ^ 2 = (xt - z) ^ 2 by ring]
      linarith [hsq]
    have heq : 2 * mu * ((eta ^ 2 / (2 * mu)) * gt ^ 2 + (mu / 2) * (z - xt) ^ 2)
        = (eta * gt) ^ 2 + mu ^ 2 * (z - xt) ^ 2 := by
      field_simp
      ring
    rw [← heq] at hgoal
    exact (mul_le_mul_left (by linarith : (0 : ℝ) < 2 * mu)).mp hgoal
  have hdecomp : eta * gt * (xt - xstar) = eta * gt * (xt - z) + eta * gt * (z - xstar) := by
    ring
  have hz : eta * gt * (z - xstar) ≤ Bregman h h' xt xstar - Bregman h h' xt z := by
    linarith [hmin]
  linarith [hdecomp, hprod, hz, hsc]

/-! ## 四、遗憾界的望远镜 -/

/-- **镜像下降遗憾界（望远镜形式，条件陈述）**：设每步满足标准望远镜不等式
`η g_t(x_t − x*) ≤ B_h(x*,x_t) − B_h(x*,x_{t+1}) + (η²/(2μ)) g_t²`，`h` 凸
（保证 Bregman 非负）、`η > 0`、`μ > 0` ⟹
`∑_{t<T} g_t(x_t − x*) ≤ B_h(x*,x_0)/η + (η/(2μ)) ∑_{t<T} g_t²`。

**注意（降级标注）**：该望远镜不等式从**镜像步极小性**的推导（一般 Bregman 势）
本文件未证；见文件头。 -/
theorem md_regret_bound {h h' : ℝ → ℝ} {gt : ℕ → ℝ} {x : ℕ → ℝ} {xstar eta mu : ℝ}
    {T : ℕ} (heta : 0 < eta) (hmu : 0 < mu)
    (hsub : ∀ x y : ℝ, h y ≥ h x + h' x * (y - x))
    (hstep : ∀ t : ℕ, t < T →
      eta * gt t * (x t - xstar) ≤
        Bregman h h' xstar (x t) - Bregman h h' xstar (x (t + 1))
          + (eta ^ 2 / (2 * mu)) * (gt t) ^ 2) :
    (∑ t in Finset.range T, gt t * (x t - xstar)) ≤
      Bregman h h' xstar (x 0) / eta + (eta / (2 * mu)) * ∑ t in Finset.range T, (gt t) ^ 2 := by
  have hsum : eta * (∑ t in Finset.range T, gt t * (x t - xstar))
      ≤ Bregman h h' xstar (x 0) + (eta ^ 2 / (2 * mu)) * ∑ t in Finset.range T, (gt t) ^ 2 := by
    rw [Finset.mul_sum]
    calc
      (∑ t in Finset.range T, eta * (gt t * (x t - xstar)))
          ≤ ∑ t in Finset.range T,
              (Bregman h h' xstar (x t) - Bregman h h' xstar (x (t + 1))
                + (eta ^ 2 / (2 * mu)) * (gt t) ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro t ht
            have := hstep t (Finset.mem_range.mp ht)
            linarith [this]
      _ = (Bregman h h' xstar (x 0) - Bregman h h' xstar (x T))
            + (eta ^ 2 / (2 * mu)) * ∑ t in Finset.range T, (gt t) ^ 2 := by
            rw [Finset.sum_add_distrib, sum_range_sub_telescoping, Finset.mul_sum]
      _ ≤ Bregman h h' xstar (x 0) + (eta ^ 2 / (2 * mu)) * ∑ t in Finset.range T, (gt t) ^ 2 := by
            have hnn : 0 ≤ Bregman h h' xstar (x T) := bregman_nonneg hsub xstar (x T)
            linarith
  have heq : eta * (Bregman h h' xstar (x 0) / eta
      + (eta / (2 * mu)) * ∑ t in Finset.range T, (gt t) ^ 2)
      = Bregman h h' xstar (x 0)
        + (eta ^ 2 / (2 * mu)) * ∑ t in Finset.range T, (gt t) ^ 2 := by
    field_simp
    ring
  rw [← heq] at hsum
  exact (mul_le_mul_left heta).mp hsum

/-! ## 五、二次势（`h = y²/2`）：完整遗憾界（OGD） -/

/-- **二次势的三项望远镜不等式（精确成立）**：对 `h(y) = y²/2`、`h'(y) = y`，
`z = x_t − η g_t` 时
`η g_t(x_t − x*) ≤ B_h(x*,x_t) − B_h(x*,z) + (η²/2) g_t²`（实为等式）。 -/
theorem euclidean_three_point (gt eta xt xstar : ℝ) :
    eta * gt * (xt - xstar) ≤
      Bregman (fun y : ℝ => y ^ 2 / 2) (fun y : ℝ => y) xstar xt
        - Bregman (fun y : ℝ => y ^ 2 / 2) (fun y : ℝ => y) xstar (xt - eta * gt)
        + (eta ^ 2 / 2) * gt ^ 2 := by
  unfold Bregman
  ring_nf
  exact le_rfl

/-- **OGD 的完整遗憾界**：对二次势（Euclidean）与梯度步 `x_{t+1} = x_t − η g_t`，
`∑_{t<T} g_t(x_t − x*) ≤ (x_0 − x*)²/(2η) + (η/2) ∑_{t<T} g_t²`。

这是 `md_regret_bound` 在 `h = y²/2`、`μ = 1`、`B(x*,x_0) = (x_0 − x*)²/2` 的实例，
其中望远镜不等式由 `euclidean_three_point` 完整给出。 -/
theorem ogd_regret_bound {gt : ℕ → ℝ} {x : ℕ → ℝ} {xstar eta : ℝ} {T : ℕ}
    (heta : 0 < eta) (hupdate : ∀ t : ℕ, x (t + 1) = x t - eta * gt t) :
    (∑ t in Finset.range T, gt t * (x t - xstar)) ≤
      (x 0 - xstar) ^ 2 / (2 * eta) + (eta / 2) * ∑ t in Finset.range T, (gt t) ^ 2 := by
  have hsub : ∀ x y : ℝ, y ^ 2 / 2 ≥ x ^ 2 / 2 + x * (y - x) := by
    intro x y
    nlinarith [sq_nonneg (y - x)]
  have hstep : ∀ t : ℕ, t < T →
      eta * gt t * (x t - xstar) ≤
        Bregman (fun y : ℝ => y ^ 2 / 2) (fun y : ℝ => y) xstar (x t)
          - Bregman (fun y : ℝ => y ^ 2 / 2) (fun y : ℝ => y) xstar (x (t + 1))
          + (eta ^ 2 / (2 * 1)) * (gt t) ^ 2 := by
    intro t _
    have h := euclidean_three_point (gt t) eta (x t) xstar
    rw [hupdate t]
    simpa using h
  have h := md_regret_bound (h := fun y : ℝ => y ^ 2 / 2) (h' := fun y : ℝ => y)
    (gt := gt) (x := x) (xstar := xstar) (eta := eta) (mu := 1) (T := T)
    heta one_pos hsub hstep
  have hB : Bregman (fun y : ℝ => y ^ 2 / 2) (fun y : ℝ => y) xstar (x 0)
      = (x 0 - xstar) ^ 2 / 2 := by
    unfold Bregman
    ring
  rw [hB] at h
  have hc : ((x 0 - xstar) ^ 2 / 2) / eta
      = (x 0 - xstar) ^ 2 / (2 * eta) := by
    field_simp
  rw [hc] at h
  simpa using h

/-- **OGD 遗憾界的 `√T` 形式（算术推论）**：若 `(gt)² ≤ G²`（∀t）、`D² = (x_0 − x*)²`、步长 `η = D/(G√T)`，则
`∑_{t<T} g_t(x_t − x*) ≤ D·G·√T`（`G,D>0`、`T>0`）。

（这是 `O(√T)` 遗憾：`OGD` 在 Lipschitz 随机/在线凸优化中的标准率。） -/
theorem ogd_regret_sqrt {gt : ℕ → ℝ} {x : ℕ → ℝ} {xstar eta G D : ℝ} {T : ℕ}
    (hG : 0 < G) (hD : 0 < D) (hT : 0 < T)
    (hD2 : (x 0 - xstar) ^ 2 = D ^ 2)
    (heta : eta = D / (G * Real.sqrt T))
    (hbound : ∀ t : ℕ, (gt t) ^ 2 ≤ G ^ 2)
    (hupdate : ∀ t : ℕ, x (t + 1) = x t - eta * gt t) :
    (∑ t in Finset.range T, gt t * (x t - xstar)) ≤ D * G * Real.sqrt T := by
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast le_of_lt hT
  have hsT : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hsT2 : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) := Real.sq_sqrt hT0
  have heta_pos : 0 < eta := by
    rw [heta]
    exact div_pos hD (mul_pos hG hsT)
  have h := ogd_regret_bound (gt := gt) (x := x) (xstar := xstar) (eta := eta) (T := T)
    heta_pos hupdate
  have hsumG : (∑ t in Finset.range T, (gt t) ^ 2) ≤ ∑ _t in Finset.range T, G ^ 2 :=
    Finset.sum_le_sum (fun t _ => hbound t)
  have hsumG' : (∑ _t in Finset.range T, G ^ 2) = (T : ℝ) * G ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hbnd : (x 0 - xstar) ^ 2 / (2 * eta) + (eta / 2) * ∑ t in Finset.range T, (gt t) ^ 2
      ≤ (x 0 - xstar) ^ 2 / (2 * eta) + (eta / 2) * ((T : ℝ) * G ^ 2) := by
    have h2 : (eta / 2) * (∑ t in Finset.range T, (gt t) ^ 2)
        ≤ (eta / 2) * ((T : ℝ) * G ^ 2) := by
      have hle : (∑ t in Finset.range T, (gt t) ^ 2) ≤ (T : ℝ) * G ^ 2 := by
        rw [← hsumG']; exact hsumG
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    linarith [h2]
  have hfinal : (x 0 - xstar) ^ 2 / (2 * eta) + (eta / 2) * ((T : ℝ) * G ^ 2)
      = D * G * Real.sqrt T := by
    rw [hD2, heta]
    have hDne : D ≠ 0 := ne_of_gt hD
    have hGne : G ≠ 0 := ne_of_gt hG
    have hsne : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt hsT
    have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
    field_simp
    ring_nf
    rw [hsT2]
    ring
  linarith [h, hbnd, hfinal]

/-! ## 注：闭环语义与诚实边界
  Bregman 非负/强凸下界/三项恒等式 → 镜像步存在性 → 单步界 → 遗憾望远镜
  （条件形式）→ 二次势特例的**完整** OGD 遗憾界与 `√T` 形式。
  诚实降级清单：一般 Bregman 势下望远镜不等式（镜像步 ⟹ 标准单步不等式）未证
  （以显式假设 `hstep` 引入）；约束/单纯形投影版未做；有限维 `Fin n` 单纯形版未做。 -/

end Lattice
