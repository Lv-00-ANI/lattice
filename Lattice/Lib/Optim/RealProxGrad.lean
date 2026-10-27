import Mathlib
import Lattice.Lib.Optim.RealProximal
import Lattice.Lib.Optim.RealStrongConvex
import Lattice.Lib.Convex.RealKKTSecondOrder
/-!
# LATTICE: 临近梯度法（proximal gradient）—— 下降引理、收缩与 ε-终止

RealProximal 给出近端算子的变分刻画与非扩张性；RealStrongConvex 给出光滑/强凸下的
梯度下降率；RealKKTSecondOrder 给出一维 KKT 分支刻画。本文件把三者装配成**临近梯度法**

    x⁺ = prox_{η h}(x − η ∇f(x))

（f 光滑可微、h 凸可能非光滑；∇f 以梯度选择 g 表示，与 RealStrongConvex 同口径）。

定理清单：
  1. `proxGradStep`（def）：`proxGradStep prox g η x = prox (x − η·g x)`；
  2. `IsProxGradStep`（def，关系式）：p 是 x 处的临近梯度步 ⟺ `IsProx h η (x−η g x) p`；
  3. `proxGrad_descent_lemma`（**下降引理**）：f 是 L-光滑、p 是 x 处的临近梯度步 ⟹
        (f+h)(p) − (f+h)(x) ≤ (L/2 − 1/(2η))·(p−x)²；
     η = 1/L 时右端为负，即**目标值单调下降**；
  4. `proxGrad_zero_h`（h ≡ 0 时 prox 是恒等（梯度步））与
     `proxGrad_descent_zero_h`：f(p) ≤ f(x) − η(1 − Lη/2)·(g x)²；
  5. `proxGrad_contraction`（**收缩**）：h 凸、Baillon–Haddad 共强制性 `GradientCoCoercive`
     成立、步长 η = 2/(μ+L)、x* 是 prox 的不动点 ⟹
        ‖p − x*‖ ≤ ((L−μ)/(L+μ))·‖x − x*‖
     （prox 非扩张 + `RealStrongConvex.strong_convex_iterate_contraction`）；
  6. `proxGrad_converges`（**ε-终止**）：迭代误差按 ((L−μ)/(L+μ)) 收缩，连接
     `RealConvergence.contraction_converges`；
  7. `proxGrad_fixed_iff_subgradient`（**不动点 ⟺ 次梯度最优性**）：
     不动点 ⟺ −g x ∈ ∂h(x)（回收 `RealSubgradient.Subgradient`）；
  8. `proxGrad_fixed_iff_stationary`：h ≡ 0 时不动点 ⟺ g x = 0；
  9. `proxGrad_fixed_iff_kkt`（**衔接 RealKKTSecondOrder**）：约束不活跃
     (c·x < d, c ≠ 0) 时，h ≡ 0 的临近梯度不动点 ⟺ 一维 KKT 系统（乘子 λ = 0）。

诚实边界：
  · prox 一般没有显式表达；`proxGradStep` 以**prox 选择函数 prox** 为参数，假设
    `hprox` 说明它确实是 prox（`IsProx`）。这与 RealProximal 的诚实边界一致
    （一般 f 的 prox 存在性在一维（凸 + 连续 + 强制）已由
    `RealProxExistence.prox_exists_unique` 给出，高维未做）；
  · `proxGrad_contraction` 的收缩系数 ((L−μ)/(L+μ)) 依赖 Baillon–Haddad 共强制性；
    与 RealStrongConvex 一样，把它作为**显式假设** `GradientCoCoercive` 引入，
    不隐藏在证明里；
  · 第 9 条的「不动点 ⟺ KKT」只在**约束不活跃**分支给出：一般约束下的 KKT 需要
    「指示函数的 prox = 投影」这一事实，本仓库未形式化（RealConvexProjection 只给了
    一般凸集的投影，未给其与 prox 的等同）；
  · `proxGrad_descent_lemma` 以区间/整体的 L-光滑（`Smooth`）表述，不含微分算子假设，
    与 RealStrongConvex 完全一致；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Lattice

/-! ## 一、临近梯度法的定义 -/

/-- **临近梯度步**：给定 prox 选择函数 `prox` 与光滑部分的梯度选择 `g`，
`proxGradStep prox g η x = prox (x − η·g x)`。 -/
def proxGradStep (prox g : ℝ → ℝ) (η x : ℝ) : ℝ := prox (x - η * g x)

/-- **临近梯度步的关系式刻画**：p 是 x 处的临近梯度步 ⟺
p 是 h 在 `x − η·g x` 处的近端点。 -/
def IsProxGradStep (g h : ℝ → ℝ) (η x p : ℝ) : Prop := IsProx h η (x - η * g x) p

/-- 临近梯度迭代（以 prox 选择函数给出）。 -/
def proxGradIterate (prox g : ℝ → ℝ) (η : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => proxGradStep prox g η (proxGradIterate prox g η n x)

/-- 第 n 步到目标点 `xstar` 的误差。 -/
def proxGradError (prox g : ℝ → ℝ) (η xstar x0 : ℝ) (n : ℕ) : ℝ :=
  ‖proxGradIterate prox g η n x0 - xstar‖

/-- **临近梯度不动点**：`prox_{η h}(x − η·g x) = x`，即 x 是 h 在 `x − η·g x` 处的
近端点（`IsProx h η (x − η·g x) x`；g 为光滑部分的梯度选择）。 -/
def IsProxGradFixed (g h : ℝ → ℝ) (η x : ℝ) : Prop := IsProx h η (x - η * g x) x

/-! ## 二、下降引理

从 prox 在 `y = x` 处的极小性得到 h 的下界，与光滑的下降引理相加。 -/

/-- **临近梯度下降引理**：f 是 L-光滑、p 是 x 处的临近梯度步 ⟹
`(f+h)(p) − (f+h)(x) ≤ (L/2 − 1/(2η))·(p−x)²`。

证明：prox 的极小性（取 y = x）给出
  `h p ≤ h x − (1/(2η))(p−x)² − (g x)(p−x)`，
光滑的下降引理给出 `f p ≤ f x + (g x)(p−x) + (L/2)(p−x)²`，两式相加。 -/
theorem proxGrad_descent_lemma {f h g : ℝ → ℝ} {L η : ℝ} (hη : 0 < η)
    (hSM : Smooth L f g) {x p : ℝ} (hprox : IsProx h η (x - η * g x) p) :
    (f p + h p) - (f x + h x) ≤ (L / 2 - 1 / (2 * η)) * (p - x) ^ 2 := by
  have hηne : η ≠ 0 := ne_of_gt hη
  have hx := hprox x
  simp only [real_norm_sq] at hx
  have e1 : (p - (x - η * g x)) ^ 2 = (p - x + η * g x) ^ 2 := by ring
  have e2 : (x - (x - η * g x)) ^ 2 = (η * g x) ^ 2 := by ring
  rw [e1, e2] at hx
  -- h p ≤ h x − (1/(2η))(p−x)² − (g x)(p−x)
  have hA : h p ≤ h x - (1 / (2 * η)) * (p - x) ^ 2 - (g x) * (p - x) := by
    have he : (1 / (2 * η)) * (η * g x) ^ 2 - (1 / (2 * η)) * (p - x + η * g x) ^ 2
        = -((1 / (2 * η)) * (p - x) ^ 2) - (g x) * (p - x) := by
      field_simp [hηne]
      ring
    linarith
  have hB := hSM x p
  have hmid : f p + h p ≤
      f x + h x + ((L / 2) * (p - x) ^ 2 - (1 / (2 * η)) * (p - x) ^ 2) := by
    linarith
  have hfin : (L / 2) * (p - x) ^ 2 - (1 / (2 * η)) * (p - x) ^ 2
      = (L / 2 - 1 / (2 * η)) * (p - x) ^ 2 := by ring
  linarith

/-- 步长条件 `η ≤ 1/L` 时目标值（单步）不增。 -/
theorem proxGrad_descent_lemma_step {f h g : ℝ → ℝ} {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hηL : η ≤ 1 / L) (hSM : Smooth L f g) {x p : ℝ} (hprox : IsProx h η (x - η * g x) p) :
    f p + h p ≤ f x + h x := by
  have h := proxGrad_descent_lemma hη hSM hprox
  have hcoef : L / 2 - 1 / (2 * η) ≤ 0 := by
    have hLη : L * η ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hηL (le_of_lt hL)
      have hone : L * (1 / L) = 1 := by field_simp
      rwa [hone] at h
    have hpos : 0 < 2 * η := by linarith
    rw [sub_nonpos, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hpos]
    nlinarith [hLη]
  have hnn : 0 ≤ (p - x) ^ 2 := sq_nonneg _
  have : (L / 2 - 1 / (2 * η)) * (p - x) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcoef hnn
  linarith

/-! ## 三、h ≡ 0 的特例：prox 退化为梯度步 -/

/-- **h ≡ 0 时 prox 是恒等映射**：`IsProx 0 η x' p ⟹ p = x'`（严格凸二次的极小点唯一）。 -/
theorem proxGrad_zero_h {g : ℝ → ℝ} {η x p : ℝ} (hη : 0 < η)
    (hprox : IsProx (fun _ : ℝ => 0) η (x - η * g x) p) :
    p = x - η * g x := by
  refine prox_unique (convexOn_const (0 : ℝ) convex_univ) hη hprox ?_
  refine prox_self_of_minimizer (f := fun _ : ℝ => 0) (η := η)
    (p := x - η * g x) hη ?_
  intro y
  simp

/-- **h ≡ 0 的下降引理（标准梯度步）**：
`f p ≤ f x − η(1 − Lη/2)·(g x)²`。η = 1/L 时即 `f p ≤ f x − (g x)²/(2L)`。 -/
theorem proxGrad_descent_zero_h {f g : ℝ → ℝ} {L η : ℝ} (hη : 0 < η) (hSM : Smooth L f g)
    {x p : ℝ} (hprox : IsProx (fun _ : ℝ => 0) η (x - η * g x) p) :
    f p - f x ≤ -(η * (1 - L * η / 2)) * (g x) ^ 2 := by
  have hp : p = x - η * g x := proxGrad_zero_h hη hprox
  rw [hp]
  -- 直接由光滑的下降引理（不经过 prox 下降引理，后者在 h ≡ 0 时只是更弱的界）
  have h := hSM x (x - η * g x)
  have h1 : g x * ((x - η * g x) - x) = -(η * (g x) ^ 2) := by ring
  have h2 : (L / 2) * ((x - η * g x) - x) ^ 2 = (L * η ^ 2 / 2) * (g x) ^ 2 := by ring
  rw [h1, h2] at h
  have h3 : -(η * (1 - L * η / 2)) * (g x) ^ 2
      = -(η * (g x) ^ 2) + (L * η ^ 2 / 2) * (g x) ^ 2 := by ring
  linarith

/-! ## 四、收缩：prox 非扩张 + 强凸/光滑（Baillon–Haddad）

`prox_{ηh}` 是 1-Lipschitz 的（RealProximal.prox_nonexpansive）；
强凸 + 光滑下梯度步把到极小点的距离按 ((L−μ)/(L+μ)) 收缩
（RealStrongConvex.strong_convex_iterate_contraction，其前提是显式的共强制性假设）。
两者复合即得临近梯度法的收缩。 -/

/-- **临近梯度收缩**：h 凸、共强制性 `GradientCoCoercive μ L g x*` 成立、步长
`η = 2/(μ+L)`、`x*` 是 prox 的不动点 ⟹
`‖p − x*‖ ≤ ((L−μ)/(L+μ))·‖x − x*‖`。

证明：prox 非扩张给出 `‖p − x*‖ ≤ ‖(x − η g x) − x*‖`；把 η 代入并用
`strong_convex_iterate_contraction` 得平方界，两边开方（非负）。 -/
theorem proxGrad_contraction {g h : ℝ → ℝ} {μ L η : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (hμL : μ ≤ L) (hη : η = 2 / (μ + L)) {xstar : ℝ}
    (hcc : GradientCoCoercive μ L g xstar) (hconv : ConvexOn ℝ Set.univ h)
    {x p : ℝ} (hprox : IsProx h η (x - η * g x) p) (hstar : IsProx h η xstar xstar) :
    ‖p - xstar‖ ≤ ((L - μ) / (L + μ)) * ‖x - xstar‖ := by
  have hsum : 0 < μ + L := by linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  have hne := prox_nonexpansive hconv hηpos hprox hstar
  rw [hη] at hne
  have hcc' := strong_convex_iterate_contraction hμ hL hcc x
  have hsquare : ((L - μ) / (L + μ)) ^ 2 * ‖x - xstar‖ ^ 2
      = (((L - μ) / (L + μ)) * ‖x - xstar‖) ^ 2 := by ring
  rw [hsquare] at hcc'
  have hneg : -‖(x - (2 / (μ + L)) * g x) - xstar‖ ≤ ‖p - xstar‖ :=
    le_trans (neg_nonpos.mpr (norm_nonneg _)) (norm_nonneg _)
  have hsq : ‖p - xstar‖ ^ 2 ≤ (((L - μ) / (L + μ)) * ‖x - xstar‖) ^ 2 :=
    le_trans (sq_le_sq' hneg hne) hcc'
  have hc0 : 0 ≤ (L - μ) / (L + μ) := div_nonneg (by linarith) (by linarith)
  have habs := sq_le_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hc0 (norm_nonneg _))] at habs
  exact habs

/-- **临近梯度法 ε-终止**：在 `proxGrad_contraction` 的前提下，
误差 `‖x_n − x*‖` 按 ((L−μ)/(L+μ)) 收缩，故对任意 ε > 0 存在 n 使误差 < ε。 -/
theorem proxGrad_converges {g h prox : ℝ → ℝ} {μ L η xstar : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (hμL : μ ≤ L) (hη : η = 2 / (μ + L)) (hcc : GradientCoCoercive μ L g xstar)
    (hconv : ConvexOn ℝ Set.univ h)
    (hprox : ∀ x : ℝ, IsProx h η (x - η * g x) (prox (x - η * g x)))
    (hstar : IsProx h η xstar xstar) (x0 : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, proxGradError prox g η xstar x0 n < ε := by
  have hsum : 0 < μ + L := by linarith
  have hsum' : 0 < L + μ := by linarith
  set c : ℝ := (L - μ) / (L + μ) with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg (by linarith) (by linarith)
  have hc1 : c < 1 := by rw [hc, div_lt_one hsum']; linarith
  have hstep : ∀ n : ℕ,
      proxGradError prox g η xstar x0 (n + 1) ≤ c * proxGradError prox g η xstar x0 n := by
    intro n
    have hiter : proxGradIterate prox g η (n + 1) x0
        = proxGradStep prox g η (proxGradIterate prox g η n x0) := by
      simp only [proxGradIterate]
    have hc' := proxGrad_contraction hμ hL hμL hη hcc hconv
      (hprox (proxGradIterate prox g η n x0)) hstar
    rw [← hc] at hc'
    simpa [proxGradError, proxGradStep, hiter] using hc'
  exact contraction_converges (e := fun n => proxGradError prox g η xstar x0 n) c
    hc0 hc1 hstep (fun n => by simp only [proxGradError]; positivity)

/-! ## 五、不动点刻画（衔接次梯度与 KKT） -/

/-- **临近梯度不动点 ⟺ 次梯度最优性条件**：h 凸、η > 0 时
不动点 ⟺ `−(g x) ∈ ∂h(x)`。

证明：（⟸）由 `Subgradient` 直接验证 `IsProx` 的二次比较（两边差恰好相等）；
（⟹）用 `RealProximal.prox_vi_of_isProx` 把 `IsProx` 转成变分不等式，
再在 x 处取值即得次梯度不等式。 -/
theorem proxGrad_fixed_iff_subgradient {g h : ℝ → ℝ} {η x : ℝ} (hη : 0 < η)
    (hconv : ConvexOn ℝ Set.univ h) :
    IsProxGradFixed g h η x ↔ Subgradient h x (-(g x)) := by
  constructor
  · intro hfix
    intro y
    have hVI := prox_vi_of_isProx hconv hη hfix
    have hy := hVI y
    have he : (1 / η) * (((x - η * g x) - x) * (y - x)) = (-(g x)) * (y - x) := by
      have h1 : (x - η * g x) - x = -(η * g x) := by ring
      rw [h1]
      field_simp [ne_of_gt hη]
      ring
    rw [he] at hy
    linarith
  · intro hsub
    intro y
    have hsuby : h x - (g x) * (y - x) ≤ h y := by
      have h := hsub y
      have he : (-(g x)) * (y - x) = -((g x) * (y - x)) := by ring
      rw [he] at h
      linarith
    have e1 : (x - (x - η * g x)) ^ 2 = (η * g x) ^ 2 := by ring
    have e2 : (y - (x - η * g x)) ^ 2 = (y - x + η * g x) ^ 2 := by ring
    rw [real_norm_sq, real_norm_sq, e1, e2]
    have key : (1 / (2 * η)) * (η * g x) ^ 2
        ≤ (1 / (2 * η)) * (y - x + η * g x) ^ 2 - (g x) * (y - x) := by
      have hid : (1 / (2 * η)) * (η * g x) ^ 2
          = (1 / (2 * η)) * (y - x + η * g x) ^ 2 - (g x) * (y - x)
            - (1 / (2 * η)) * (y - x) ^ 2 := by
        field_simp [ne_of_gt hη]
        ring
      have hnn : 0 ≤ (1 / (2 * η)) * (y - x) ^ 2 := by positivity
      rw [hid]
      linarith
    linarith

/-- **h ≡ 0 时的不动点 ⟺ 驻点**：不动点 ⟺ `g x = 0`。 -/
theorem proxGrad_fixed_iff_stationary {g : ℝ → ℝ} {η x : ℝ} (hη : 0 < η) :
    IsProxGradFixed g (fun _ : ℝ => 0) η x ↔ g x = 0 := by
  have hconv : ConvexOn ℝ Set.univ (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 convex_univ
  rw [proxGrad_fixed_iff_subgradient hη hconv]
  constructor
  · intro hsub
    have h1 := hsub (x + 1)
    have h2 := hsub (x - 1)
    simp only [] at h1 h2
    linarith
  · intro h0
    intro y
    rw [h0]
    simp

/-- **临近梯度不动点 ⟺ 一维 KKT（约束不活跃分支）**：设约束为 `c·x ≤ d`（`c ≠ 0`），
h ≡ 0（无约束部分），且 x 处约束**不活跃**（`c·x < d`）。则 x 是临近梯度不动点
⟺ x 满足一维 KKT 系统 `KKTOneDim f c d x 0`（乘子 λ = 0、`deriv f x = 0`）。

证明：不动点 ⟺ `deriv f x = 0`（`proxGrad_fixed_iff_stationary`）；
再由 `RealKKTSecondOrder.kkt_one_dim_complete` 在不活跃分支上 KKT ⟺ `deriv f x = 0`。 -/
theorem proxGrad_fixed_iff_kkt {f : ℝ → ℝ} {η c d x : ℝ} (hη : 0 < η) (hc : c ≠ 0)
    (hact : c * x < d) :
    IsProxGradFixed (deriv f) (fun _ : ℝ => 0) η x ↔ KKTOneDim f c d x 0 := by
  rw [proxGrad_fixed_iff_stationary hη]
  rw [kkt_one_dim_complete f c d x 0 hc]
  constructor
  · intro h0
    exact Or.inl ⟨hact, rfl, h0⟩
  · intro h
    rcases h with ⟨-, -, h0⟩ | ⟨heq, -⟩
    · exact h0
    · exact absurd heq (ne_of_lt hact)

/-! ## 注：闭环语义
  · 下降引理（本文件 3/4）→ 收缩（5）→ ε-终止（6）：临近梯度法的完整收敛链；
  · 不动点 ⟺ 次梯度最优性（7）→ h ≡ 0 退化为驻点（8）→ 约束不活跃时 ⟺ KKT（9）：
    非光滑优化的最优性刻画链；
  · 与 RealProximal 的关系：那里只证 prox 的**算子性质**（非扩张、唯一性、线性范例），
    本文件把 prox 装进**算法**并给出收敛率与最优性；
  · 与 RealKKTSecondOrder 的关系：那里给出约束问题的 KKT 分支刻画，
    本文件用「h ≡ 0 + 约束不活跃」回收其非活跃分支，说明临近梯度不动点是
    约束不起作用时的 KKT 点。 -/

end Lattice
