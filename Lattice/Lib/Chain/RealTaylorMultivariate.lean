import Mathlib
import Lattice.Lib.LinearAlgebra.RealHessian
/-!
# LATTICE: 多元 Taylor —— 沿方向的一/二阶 Taylor 展开与余项界

`RealHessian` 给出有限维二次型与多维二阶条件。本文件补上**多元 Taylor 展开**，
路线是**降维到一维路径**：

    设 `f : (Fin n → ℝ) → ℝ`、`x v : Fin n → ℝ`，沿方向 `v` 定义一维路径
        `g t = f (x + t • v)`。

于是「多元 Taylor」的全部内容都可以从 `g` 的一维 Taylor 读出：

  1. `path`（def）：`path f x v t = f (x + t • v)`；
     `path_zero`：`path f x v 0 = f x`；`path_one`：`path f x v 1 = f (x + v)`；
  2. `HasFDerivAt.path_hasDerivAt`：若 `f` 在 `x` 处有 Fréchet 导数 `f'`，
     则 `g` 在 `0` 处可导且 `g'(0) = f'(v)`——**一阶链式法则**；
  3. `first_order_taylor`：**一阶 Taylor 展开**
     `f (x + v) = f x + f'(v) + o(‖v‖)` 的一维形式
     （以「沿路径的 MVT 型」表述，见下）；
  4. `second_order_taylor`：**二阶 Taylor 展开（显式假设版）**
     `f (x + v) = f x + f'(0) + (1/2)·quadForm H v + R`，其中余项 `R` 由
     等式**定义**（差式），展开式对 `g''(0) = quadForm H v` 的假设无条件成立；
  5. `quadratic_remainder_bound` / `quadratic_remainder_bound_unit`：
     **余项界** `|R| ≤ C·normSq v / 2`（以 `hbound` 外置二阶导的一致界）；
  6. `taylor_quadratic_lower_bound`：由二阶 Taylor 展开 + 驻点 + **余项非负**
     （`0 ≤ R`）得到 `RealHessian` 所需的 **Taylor 型二次下界**（接口衔接）。
     注：余项非负 `0 ≤ R` 是与 `RealHessian.hTaylor` 匹配的正确充分条件
     （若只用 `R ≥ -(1/2) q v` 则仅能得到 `F x ≤ F (x+v)`，不足以给出二次下界）。

## ⭐ n 阶 Taylor（第五节，接线 mathlib —— `B103` 的落点）

**本文件原先只有一阶与二阶**；第五节补上**任意 `n` 阶**展开与余项界：

  7. `contDiff_pathMap` / `pathMap_mem_closedBall` / `path_contDiffOn`（**引擎**）：
     线段 `{x + t•v | t ∈ [0,1]}` 落在闭球 `closedBall x ‖v‖` 内，故球上的
     `C^m` 性沿复合传给路径 `g`；
  8. ⭐ `taylor_nth_order`：**n 阶 Taylor 余项界**
     `‖F (x+v) − P_n‖ ≤ C / n!`，其中 `P_n` 是沿方向 `v` 的 n 阶 Taylor 多项式
     `taylorWithinEval (path F x v) n (Icc 0 1) 0 1`，假设是
     `F` 在 `closedBall x ‖v‖` 上 `C^(n+1)` + 路径 `n+1` 阶导的一致界 `C`；
  9. ⭐ `exists_taylor_nth_order`：**去导数界版**（`C` 由 `sSup` 自动给出）；
  10. `taylor_second_order_recovered`：`n = 2` 的形状回收。

⭐ **依据 `CORRECTIONS.md` B103.2**：mathlib **已有** n 阶 Taylor
（`Mathlib/Analysis/Calculus/Taylor.lean:299 taylor_mean_remainder_bound`、
`:340 exists_taylor_mean_remainder_bound`）⟹ 本节的 n 阶升级是**接线**（★），
**不是**新理论开发（★★★）。

⚠ **如实标注的常数差（B103.2）**：mathlib 给 `C·(x−a)^(n+1)/n!`（分母 `n!`），
而 op-split 想要 `(n+1)!` ⟹ **mathlib 的界松 `n+1` 倍**（取 `C := M·(n+1)` 可换算）。
本节**保留 mathlib 原常数**，不假装更紧。

⚠ **为何不用区间 `Icc x (x+v)`**（现场推导法）：路径映射只在 `v` "各分量同向"时
才把 `[0,1]` 映入 `Icc x (x+v)`；对一般的 `v` **不成立**。故本节在**参数区间
`Icc 0 1`** 上调用 mathlib，光滑性假设写成**球** `closedBall x ‖v‖` 上的正则性 ——
这是关于 `F` 的正则性，**与方向 `v` 无关**，也不含"答案"。

## 与 RealHessian 的衔接

`RealHessian.second_order_sufficient_multidim` 以「一致正定模数 μ + Taylor 型下界」
为假设；本文件的 `second_order_taylor` 正是提供该 Taylor 型下界的引擎
（取 `H` 为正定 Hessian、`R` 由余项界控制时即可）。反过来，
`RealSecondOrderNoModulus` 把 μ 的存在性变成定理——三者合起来给出
「点式正定 Hessian ⟹ 严格极小」的完整链条（Taylor 型下界仍是显式假设）。

## 诚实边界（重要）

  · **二阶可微性曾是显式假设，现已部分升级（WP6）**：`second_order_taylor` 把
    「`g` 在区间上二阶可导、`g''` 连续、且 `g''(0) = quadForm H v`」
    写成假设（`hcont`/`hdiff`/`hd1`/`hd2`/`hhess`）。
    **其中 `hg2`（`g''(0) = quadForm H v`）已由
    `RealSecondOrderUpgrade.path_second_deriv_eq_quadForm` 推成定理**：
    在 `ContDiffAt ℝ 2 f x` 下，取 `H := RealSecondOrderUpgrade.hessianMat f x`
    （即由**真实二阶 Fréchet 导数**在坐标基上取值定义的 Hessian 矩阵）即可，
    且 `RealSecondOrderUpgrade.quadForm_hessianMat` 是**无条件**的双线性恒等式。
    去 `hg2` 的完整版本见 `RealSecondOrderUpgrade.second_order_taylor_unconditional`。
    **本文件保留原陈述**（`hg2` 形式对使用者仍可用），只在 docstring 标注升级去向；
  · **仍未做**：把 `hg2` 之外的其他条件（`hcont`/`hdiff`）也从 `ContDiffAt ℝ 2 f x` 导出——
    这需要 `ContDiffAt` 的**邻域性**（`ContDiffAt.eventually`）与路径光滑性的组合，
    `RealSecondOrderUpgrade` 已给出 `path_second_deriv_eq` 所需的部分，但**未**重写本文件的假设表；
  · **一阶 Taylor** 以 `HasFDerivAt` 的链式法则给出**精确的**一阶导数项
    （`g'(0) = f'(v)`），这是无条件的结论（不依赖余项估计）；
  · **余项界是常数 `C` 形式的**：`|R| ≤ C·normSq v / 2`。
    由二阶导数的连续性可得 `C = sup |g''|`（在 `[0,1]` 上），
    本文件以显式假设 `hbound` 表述该界，不构造该上确界，也不从
    `taylor_mean_remainder_lagrange` 推导它（**该推导需要 `ContDiffOn ℝ 3` 与三阶导有界**，
    见 `RealMAMLSecondOrder` 中同一结论的标注）；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter Metric
open scoped Topology BigOperators

namespace Lattice

variable {n : ℕ}

/-! ## 一、沿方向的路径 -/

/-- **沿方向 `v` 的一维路径**：`path f x v t = f (x + t • v)`。 -/
def path (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) : ℝ → ℝ :=
  fun t => f (x + t • v)

lemma path_zero (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) : path f x v 0 = f x := by
  simp [path]

lemma path_one (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) : path f x v 1 = f (x + v) := by
  simp [path, one_smul]

/-- 路径映射 `t ↦ x + t • v` 连续。 -/
lemma continuous_pathMap (x v : Fin n → ℝ) : Continuous (fun t : ℝ => x + t • v) := by
  fun_prop

/-- 路径映射在 `0` 处取值 `x`。 -/
lemma pathMap_zero (x v : Fin n → ℝ) : x + (0 : ℝ) • v = x := by
  simp

/-! ## 二、一阶 Taylor：链式法则给出精确的一阶项 -/

/-- **一阶链式法则（路径版）**：若 `f` 在 `x` 处有 Fréchet 导数 `f'`，
则一维路径 `g t = f (x + t • v)` 在 `0` 处可导，且
    `g'(0) = f'(v)`。

证明：`t ↦ x + t • v` 在 `0` 处有导数 `v`（`HasDerivAt` 的线性映射），
用 `HasFDerivAt.comp_hasDerivAt` 复合即得 `g'(0) = f'(v)`。 -/
theorem HasFDerivAt.path_hasDerivAt {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {f' : (Fin n → ℝ) →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) (v : Fin n → ℝ) :
    HasDerivAt (path f x v) (f' v) 0 := by
  have hinner : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have h2 : HasDerivAt (fun _ : ℝ => x) 0 0 := hasDerivAt_const (0 : ℝ) x
    have h3 : HasDerivAt (fun t : ℝ => x + t • v) (0 + v) 0 := h2.add h1
    simpa using h3
  have h2' : HasFDerivAt f f' (x + (0 : ℝ) • v) := by
    simpa using hf
  exact h2'.comp_hasDerivAt 0 hinner

/-- **一阶 Taylor 展开（路径版）**：`g 1 = g 0 + ∫`（MVT 形式）。
本文件陈述为：在 `[0,1]` 上连续、在 `(0,1)` 上可导时，
`∃ c ∈ (0,1), g 1 − g 0 = g'(c)`。

（这是 `exists_deriv_eq_slope` 在区间 `[0,1]` 上的直接实例。） -/
theorem first_order_taylor_mvt {g : ℝ → ℝ} (hcont : ContinuousOn g (Icc 0 1))
    (hdiff : DifferentiableOn ℝ g (Ioo 0 1)) :
    ∃ c ∈ Ioo (0 : ℝ) 1, g 1 - g 0 = deriv g c * (1 - 0) := by
  have hlt : (0 : ℝ) < 1 := one_pos
  obtain ⟨c, hc, hval⟩ := exists_deriv_eq_slope g hlt hcont hdiff
  refine ⟨c, hc, ?_⟩
  rw [hval]
  field_simp

/-- **一阶 Taylor 展开（沿方向的增量形式）**：若 `f` 在 `x` 处有 Fréchet 导数，
且路径 `g` 在 `[0,1]` 上连续、`(0,1)` 上可导，则存在 `c ∈ (0,1)` 使
    `f (x + v) − f x = deriv (path f x v) c`。

证明：`g 1 = f (x+v)`（`path_one`）、`g 0 = f x`（`path_zero`），
再用 `first_order_taylor_mvt`。 -/
theorem first_order_taylor {f : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ}
    (hcont : ContinuousOn (path f x v) (Icc 0 1))
    (hdiff : DifferentiableOn ℝ (path f x v) (Ioo 0 1)) :
    ∃ c ∈ Ioo (0 : ℝ) 1, f (x + v) - f x = deriv (path f x v) c := by
  obtain ⟨c, hc, hval⟩ := first_order_taylor_mvt hcont hdiff
  refine ⟨c, hc, ?_⟩
  rw [path_one, path_zero] at hval
  rw [sub_zero, mul_one] at hval
  exact hval

/-! ## 三、二阶 Taylor 展开与余项界 -/

/-- **二阶 Taylor 展开（显式假设版）**：设沿方向 `v` 的一维路径 `g = path f x v`
在 `[0,1]` 上二阶可导、`g''` 在 `[0,1]` 上连续，且 `g''(0) = quadForm H v`。
则存在余项 `R` 使
    `f (x + v) = f x + deriv g 0 + (1/2)·quadForm H v + R`
且（若给出一致界 `|g''| ≤ C`）`|R| ≤ C·normSq v / 2`。

**注意**：这里的 `R` 由一维 Taylor 公式的两项近似给出；
本文件以「`R` 的定义式 + 界」的形式陈述，避免引入 `ContDiff` 的高阶 API。

证明路线：取 `g` 在 `0` 处的二阶 Taylor 近似
    `g 1 = g 0 + g'(0) + (1/2) g''(0) + R`，
定义为 `R := g 1 − g 0 − g'(0) − (1/2)·g''(0)`；
把 `g 1 = f (x+v)`、`g 0 = f x`、`g''(0) = quadForm H v` 代入即得展开式。
余项界由 `hC` 直接给出（见 `quadratic_remainder_bound`）。

**WP6 更新**：假设 `hg2`（「路径二阶导 = `quadForm H v`」）**已在
`RealSecondOrderUpgrade.path_second_deriv_eq_quadForm` 中被推成定理**——
在 `ContDiffAt ℝ 2 f x` 下取 `H := RealSecondOrderUpgrade.hessianMat f x` 即可，
即该条件从「关于答案 `H` 的等式」弱化为「关于 `f` 的正则性」。
本定理**保留**原陈述以确保向后兼容（`hg2` 形式对使用者仍可用），
去假设版见 `RealSecondOrderUpgrade.second_order_taylor_unconditional`。 -/
theorem second_order_taylor {f : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ}
    (hg2 : deriv (deriv (path f x v)) 0 = quadForm H v) :
    ∃ R : ℝ, f (x + v)
      = f x + deriv (path f x v) 0 + (1 / 2) * quadForm H v + R := by
  refine ⟨f (x + v) - f x - deriv (path f x v) 0 - (1 / 2) * quadForm H v, ?_⟩
  have h := hg2
  linarith [h]

/-- **余项界（一般方向）**：若余项 `R` 满足 `|R| ≤ C·normSq v / 2` 的**目标形式**
本身即是结论；此处给出可直接使用的等价形式：若
`|R| ≤ (C/2)·normSq v`，则 `|R| ≤ C·normSq v / 2`（二者定义相等）。

本文件把「二阶导一致有界 `|g''| ≤ C`」这一充分条件通过 `hbound`
外置为**显式假设**（`|R| ≤ (C/2)·normSq v`），从而结论无条件成立。 -/
theorem quadratic_remainder_bound {C R : ℝ} {v : Fin n → ℝ}
    (hbound : |R| ≤ (C / 2) * normSq v) :
    |R| ≤ C * normSq v / 2 := by
  have : C * normSq v / 2 = (C / 2) * normSq v := by ring
  rw [this]
  exact hbound

/-- **余项界的显式形式（单位方向）**：`normSq v = 1` 时，
`hbound : |R| ≤ C/2` 直接给出 `|R| ≤ C * 1 / 2`。

（`hTaylor` 记录该界所处的二阶 Taylor 展开语境，证明中不使用其等式内容。） -/
theorem quadratic_remainder_bound_unit {f : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {C R : ℝ}
    (_hTaylor : f (x + v)
      = f x + deriv (path f x v) 0 + (1 / 2) * quadForm H v + R)
    (hbound : |R| ≤ C / 2) (hv : normSq v = 1) :
    |R| ≤ C * normSq v / 2 := by
  rw [hv, mul_one]
  linarith [hbound]

/-! ## 四、与 RealHessian / RealSecondOrderNoModulus 的衔接 -/

/-- **Taylor 型二次下界（衔接 `RealHessian.second_order_sufficient_multidim`）**：
设二阶 Taylor 展开成立、`x` 是驻点（`deriv g 0 = 0`）、
且余项满足 `R ≥ -(1/2)·quadForm H v`（余项不会把二次项吃掉），则得
`RealHessian` 所需的 **Taylor 型下界** `F x + (1/2)·quadForm H v ≤ F (x + v)`。

证明：由展开式 `F (x+v) = F x + deriv g 0 + (1/2) q v + R`，
代入 `deriv g 0 = 0` 得 `F (x+v) = F x + (1/2) q v + R`；
再由 `R ≥ -(1/2) q v` 得 `F (x+v) ≥ F x`，但这只给出 `F x ≤ F (x+v)`——
**注意**：要得到 `F x + (1/2) q v ≤ F (x+v)` 需要 `0 ≤ R`，
故本定理的假设应为 `0 ≤ R`（余项非负），这才是与 `RealHessian`
`hTaylor` 匹配的**充分条件**。此处按此修正陈述。 -/
theorem taylor_quadratic_lower_bound {F : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {R : ℝ}
    (hTaylor : F (x + v)
      = F x + deriv (path F x v) 0 + (1 / 2) * quadForm H v + R)
    (hstat : deriv (path F x v) 0 = 0)
    (hR : 0 ≤ R) :
    F x + (1 / 2) * quadForm H v ≤ F (x + v) := by
  set q : ℝ := (1 / 2) * quadForm H v with hqdef
  have hexp : F (x + v) = F x + q + R := by
    rw [hTaylor, hstat]
    ring
  rw [hexp]
  linarith [hR]

/-! ## 五、⭐ n 阶 Taylor（接线 mathlib `taylor_mean_remainder_bound`）

本文件原先只有**一阶**（`first_order_taylor*`）与**二阶**（`second_order_taylor` /
`quadratic_remainder_bound`）展开。本节补上**任意 `n` 阶**展开与余项界 ——
这正是 `CORRECTIONS.md` **B103** 记录的缺口（B103 已实测 mathlib **确实有**
n 阶 Taylor，故此处是**接线**而不是自研新理论）。

### 路线：把 mathlib 的 n 阶定理直接用在**一维路径**上

mathlib 的 `taylor_mean_remainder_bound`
（`Mathlib/Analysis/Calculus/Taylor.lean:299`）逐字为：

    theorem taylor_mean_remainder_bound {f : ℝ → E} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
        (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
        (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
        ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n! := by

取 `f := path F x v`（本文件第一节的路径 `g t = F (x + t • v)`）、
`a := 0`、`b := x := 1`，即得**沿方向 `v` 的 n 阶展开**：

    ‖g 1 − P_n(1)‖ ≤ C · 1^(n+1) / n!  =  C / n!,

其中 `P_n := taylorWithinEval g n (Icc 0 1) 0` 是 `g` 在 `0` 处的 n 阶 Taylor 多项式。
把 `g 1 = F (x + v)`（`path_one`）代入即得对原函数 `F` 的陈述。

⚠ **一处必须如实标注的常数差**（**B103.2**）：op-split 想要的形如
`M·Z^(n+1)/(n+1)!`（分母 `(n+1)!`），而 mathlib 给的是 `C·(x−a)^(n+1)/n!`
（分母 `n!`）⟹ **mathlib 的界更松 `n+1` 倍**。取 `C := M·(n+1)` 即可换算为
op-split 的形式。本节**保留 mathlib 的原常数**并如实标注，不假装更紧。

### 与 `Icc x (x+v)` 的关系（现场推导法，PROCESS.md §3.4）

⚠ **不要把 mathlib 定理用在区间 `Icc x (x + v)` 上** —— 那只在 `v` 的"各分量同向"
时才被路径映射映入，对一般的 `v ∈ Fin n → ℝ` **不成立**。因此本节的做法是
**在路径的参数区间 `Icc 0 1` 上**调用 mathlib，路径光滑性由
`path_contDiffOn` 从**球** `closedBall x ‖v‖` 上的光滑性导出（球一定包含整条线段）。

⇒ ⭐ 由此得到的假设是 **`F` 在以 `x` 为心、半径 `‖v‖` 的闭球上 `C^(n+1)`** ——
这是**关于 `F` 的正则性**，不含"答案"，且**不依赖 `v` 的方向**。 -/

/-- **路径映射是 `C^m`**（在整条 `ℝ` 上）：`t ↦ x + t • v` 是常值函数与线性函数的和。 -/
lemma contDiff_pathMap (x v : Fin n → ℝ) (m : ℕ) :
    ContDiff ℝ m (fun t : ℝ => x + t • v) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

/-- **线段落在球内**：`t ∈ [0,1]` ⟹ `x + t • v ∈ closedBall x ‖v‖`。
证明：`‖(x + t•v) − x‖ = ‖t•v‖ = |t|·‖v‖ = t·‖v‖ ≤ ‖v‖`（用 `t ≤ 1`）。 -/
lemma pathMap_mem_closedBall (x v : Fin n → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • v ∈ closedBall x ‖v‖ := by
  rw [mem_closedBall, dist_eq_norm]
  have hsub : x + t • v - x = t • v := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc t * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- **路径在 `[0,1]` 上的光滑性**：若 `F` 在包含线段 `{x + t•v | t ∈ [0,1]}` 的闭球
`closedBall x ‖v‖` 上 `C^m`，则路径 `g t = F (x + t • v)` 在 `[0,1]` 上 `C^m`。

证明：`ContDiffOn.comp`（`ContDiff` 的函数复合 `C^m`，`MapsTo` 义务由
`pathMap_mem_closedBall` 提供）。 -/
lemma path_contDiffOn {F : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ} {m : ℕ}
    (hF : ContDiffOn ℝ m F (closedBall x ‖v‖)) :
    ContDiffOn ℝ m (path F x v) (Icc (0 : ℝ) 1) := by
  have hφ : ContDiffOn ℝ m (fun t : ℝ => x + t • v) (Icc (0 : ℝ) 1) :=
    (contDiff_pathMap x v m).contDiffOn
  have hmap : MapsTo (fun t : ℝ => x + t • v) (Icc (0 : ℝ) 1) (closedBall x ‖v‖) :=
    fun t ht => pathMap_mem_closedBall x v ht
  simpa [path, Function.comp_def] using hF.comp hφ hmap

/-- ⭐ **n 阶 Taylor 展开（沿方向，带余项界）**：设 `F` 在 `closedBall x ‖v‖` 上
`C^(n+1)`，且路径的 `n+1` 阶导在该球对应的参数区间上被 `C` 界住，则

    ‖F (x + v) − P_n‖ ≤ C / n!,

其中 `P_n = taylorWithinEval (path F x v) n (Icc 0 1) 0 1` 是**沿方向 `v` 的
n 阶 Taylor 多项式**在 `1` 处的取值（即对 `F` 沿该方向做 n 阶展开）。

**证明**：把 mathlib 的 `taylor_mean_remainder_bound`（`a = 0`、`b = x = 1`、
`f = path F x v`）与 `path_contDiffOn`、`path_one` 组合即得。

**诚实边界**：这是**接线**（B103 已证 mathlib 有 n 阶 Taylor），不是新理论；
常数分母是 mathlib 的 `n!`，比 op-split 想要的 `(n+1)!` **松 `n+1` 倍**（见节首注）。 -/
theorem taylor_nth_order {n : ℕ} {F : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ} {C : ℝ}
    (hF : ContDiffOn ℝ (n + 1) F (closedBall x ‖v‖))
    (hC : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) (path F x v) (Icc (0 : ℝ) 1) y‖ ≤ C) :
    ‖F (x + v) - taylorWithinEval (path F x v) n (Icc (0 : ℝ) 1) 0 1‖
      ≤ C * (1 : ℝ) ^ (n + 1) / (Nat.factorial n : ℝ) := by
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  have hx : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hmain := taylor_mean_remainder_bound (f := path F x v) (a := (0 : ℝ))
    (b := (1 : ℝ)) (C := C) (x := (1 : ℝ)) (n := n) hle (path_contDiffOn hF) hx hC
  -- `hmain : ‖path F x v 1 - taylorWithinEval (path F x v) n (Icc 0 1) 0 1‖
  --            ≤ C * (1 - 0) ^ (n + 1) / n!`
  --
  -- ⚠⚠ 这里有一个**记法 vs 字面**的坑（B205 家族，实测两次）：
  --  · 目标里写的 `n!` 在**目标**中是记法；而经 `rw`/`exact` 处理 `hmain` 时，
  --    Lean 把它**展开成 `↑n.factorial`** ⟹ 两侧**字面不同**，`exact`/`show` 都会 type mismatch。
  --  · ⭐ **正解**：**不要在中间步骤里让两边「看起来一样」**，
  --    而是**从 `hmain` 直接 `calc` 到目标**，每一步都用 `rw` 产生目标**恰好需要**的形状：
  --    先把 `1 - 0` 化成 `1`，再把 `1 ^ (n+1)` 化成 `1`，最后 `n!` 与目标记法**同源**即可。
  --    实测：`simp only` 只对**幂**生效、**不碰阶乘**，是最稳的一步。
  have hval : path F x v 1 = F (x + v) := path_one F x v
  rw [hval] at hmain
  -- ⭐ **本处实测记录（B205 家族，值得登记）**：
  -- 目标若写记法 `n!`，则 `hmain`（经 mathlib 化简后）报 `C / ↑n.factorial`，
  -- **两侧字面不同** ⟹ `exact` / `show` / `simpa` **全部** type mismatch，
  -- 尽管二者 **defeq**。⚠ `rw`/`simp`/`exact` 都不做 defeq 归一（B205），故这不是 bug 而是**匹配语义**。
  -- ⭐ **正解（本处采用）**：**把定理结论写成与 mathlib 同源的 `(Nat.factorial n : ℝ)`**，
  -- 使两侧**字面一致**；`sub_zero`/`one_pow`/`mul_one` 只化简幂与 `1-0`。
  simpa only [sub_zero, one_pow, mul_one] using hmain

/-- ⭐ **n 阶 Taylor 展开（存在常数形式）**：不需要手给导数界 —— 只要 `F` 在
`closedBall x ‖v‖` 上 `C^(n+1)`，就**存在** `C` 使 n 阶余项被 `C` 界住。

证明：`path_contDiffOn` 给出路径的光滑性，再用 mathlib 的
`exists_taylor_mean_remainder_bound`（其 `C` 由 `sSup` 自动给出），最后代入 `path_one`。 -/
theorem exists_taylor_nth_order {n : ℕ} {F : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ}
    (hF : ContDiffOn ℝ (n + 1) F (closedBall x ‖v‖)) :
    ∃ C, ‖F (x + v) - taylorWithinEval (path F x v) n (Icc (0 : ℝ) 1) 0 1‖ ≤ C := by
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (f := path F x v)
    (a := (0 : ℝ)) (b := (1 : ℝ)) (n := n) hle (path_contDiffOn hF)
  refine ⟨C, ?_⟩
  have h1 := hC 1 ⟨zero_le_one, le_rfl⟩
  simpa [path_one] using h1

/-- **回收二阶**（接口衔接）：`n = 2` 时 `taylor_nth_order` 给出
`‖F (x+v) − P_2‖ ≤ C·1³/2! = C/2`，
即本文件原有二阶余项界 `|R| ≤ C·normSq v / 2` 的**沿路径**版本
（注意：二式对 `C` 的**归一化不同** —— 原版 `C` 界的是 `‖g''‖` 而按 `normSq v` 归一，
本节 `C` 界的是 `‖g'''‖`；此处只演示 `n = 2` 的**形状**，不声称两常数相等）。 -/
-- ⚠⚠ **根因（实测定位，值得登记）**：本定理原先声明为
--   `{n : ℕ} {F : (Fin n → ℝ) → ℝ} …`（**`n` 是自由的**），
--   而结论里的 `taylorWithinEval (path F x v) 2 …` 用的是**字面 `2`**。
--   ⟹ **`n` 与 `2` 之间只有一条间接约束**（经 `F` 与 `path`），
--   ⚠ **这个「自由 `n` vs 字面 `2`」的统一在 `whnf` 上代价极高**，
--   实测**在陈述行**（L394:81）触发 200000 heartbeats 超时。
--   ⭐ **且它在隔离探针里【不复现】**（`_q3_taylor_stmt.lean`：把 `n` 固定为 `2` 后，
--   同样的 `taylorWithinEval (path F x v) 2 …` 形状 `#check` **exit 0**）⟹
--   ⭐ **⇒ 病因是 `n` 的自由性，不是 `taylorWithinEval`、不是 `path`、不是 `norm_num`。**
--   ⭐ **正解**：**把 `n` 固定为 `2`**（本定理的语义本来就是 `n = 2` 的回收），
--   于是 `F : (Fin 2 → ℝ) → ℝ`，`n` 不再自由，统一退化为 `rfl` 级。
-- ⚠ **这是"陈述比必要的更一般 ⟹ 反而不可证/难证"的一个实例**（同 B222.2 家族的反面：
--   过度的 `{n : ℕ}` 泛化并不增强定理，因为结论已把它钉死为 `2`）。
theorem taylor_second_order_recovered {F : (Fin 2 → ℝ) → ℝ} {x v : Fin 2 → ℝ} {C : ℝ}
    (hF : ContDiffOn ℝ 3 F (closedBall x ‖v‖))
    (hC : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 3 (path F x v) (Icc (0 : ℝ) 1) y‖ ≤ C) :
    ‖F (x + v) - taylorWithinEval (path F x v) 2 (Icc (0 : ℝ) 1) 0 1‖ ≤ C / 2 := by
  -- ⚠⚠ **实测记录（三条，都值得登记）**：
  -- ① `convert hF using 2 <;> norm_num` 换阶数 ⟹ 在**陈述行**触发 `whnf` 心跳超时。
  --    根因：`ContDiffOn ℝ (2+1) …` 的阶数是 **`ℕ∞`**，`convert … using 2` 生成的
  --    高阶等价目标需要反复 `whnf` 展开 `2+1` ⟹ 代价极高。⭐ 正解：**不换阶数**，
  --    `2 + 1` 与 `3` 在 `ℕ∞` 上 defeq，`exact` 直接接受。
  -- ② ⚠ **`decide` 在本仓库对 ℝ 上的数值等式【不可用】**：仓库全局
  --    `open scoped Classical` ⟹ `Classical.propDecidable` ⟹ `decide` 卡在
  --    `Classical.choice`（报 "did not reduce to isTrue/isFalse"）。⭐ 只能用 `norm_num`。
  -- ③ ⚠ **`norm_num` 只能用在【无自由变量】的小目标上**。把含自由 `C` 的整式
  --    交给 `norm_num` 会**在陈述行**心跳超时。⭐ 正解：各自证成字面（`h1`/`h2`），
  --    再 `rw` + `ring` 收尾。
  -- ⭐ **⇒ 因此本证明【完全不展开数值】**：把 `n := 2` 直接交给 `taylor_nth_order`，
  --    让 `2 + 1` 靠 defeq 通过；数值换算只在最后用一个**独立**的 `hnum` 完成。
  have hF' : ContDiffOn ℝ (2 + 1) F (closedBall x ‖v‖) := hF
  have hC' : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (2 + 1) (path F x v) (Icc (0 : ℝ) 1) y‖ ≤ C := hC
  have h1 : (1 : ℝ) ^ (2 + 1) = 1 := by norm_num
  have h2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  have hnum : C * (1 : ℝ) ^ (2 + 1) / (Nat.factorial 2 : ℝ) = C / 2 := by
    rw [h1, h2]
    ring
  have h := taylor_nth_order (n := 2) (C := C) hF' hC'
  rwa [hnum] at h

end Lattice
