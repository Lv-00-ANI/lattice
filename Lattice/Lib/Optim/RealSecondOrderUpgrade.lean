import Mathlib
import Lattice.Lib.LinearAlgebra.RealHessian
import Lattice.Lib.Optim.RealSecondOrderNoModulus
import Lattice.Lib.Convex.RealKKTSecondOrder
import Lattice.Lib.Chain.RealTaylorMultivariate
/-!
# LATTICE: 二阶假设升级 —— 把 `fderiv² f x` 与 `quadForm H` 桥接起来

本文件是 ROADMAP B1（「把显式假设升级为定理」）在**二阶导数层**的落地，
承接 `RealSecondOrderNoModulus`（把一致正定模数 μ 从假设变成定理）的范式。

## 被升级的假设

`RealTaylorMultivariate.second_order_taylor` 的核心外置假设是

    hg2 : deriv (deriv (path f x v)) 0 = quadForm H v

它把「`H` 确实是 `f` 在 `x` 处的 Hessian」这一**实质性数学内容**写成了假设。

本文件把它推成定理：
  · 由**真实二阶 Fréchet 导数**定义 Hessian 矩阵 `hessianMat f x`；
  · 证明 `quadForm (hessianMat f x) v = fderiv ℝ (fderiv ℝ f) x v v`（双线性恒等式，无条件）；
  · 证明 `deriv (deriv (path f x v)) 0 = fderiv ℝ (fderiv ℝ f) x v v`
    （链式法则，前提 `ContDiffAt ℝ 2 f x`）；
  · 由上两式得 `deriv (deriv (path f x v)) 0 = quadForm (hessianMat f x) v`。

## 主结果一览

  1. `hessianMat`（def）：`hessianMat f x i j = fderiv ℝ (fderiv ℝ f) x (eᵢ) (eⱼ)`；
  2. `quadForm_hessianMat`：`quadForm (hessianMat f x) v = fderiv ℝ (fderiv ℝ f) x v v`
     —— **纯双线性代数恒等式，无任何可微性假设**；
  3. `hasFDerivAt_fderiv_of_contDiffAt`：`ContDiffAt ℝ 2 f x` ⟹
     `HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x`（由 `ContDiffAt.fderiv_right`）；
  4. `path_second_deriv_eq`：`ContDiffAt ℝ 2 f x` ⟹
     `deriv (deriv (path f x v)) 0 = fderiv ℝ (fderiv ℝ f) x v v`；
  5. `path_second_deriv_eq_quadForm`：同前提 ⟹
     `deriv (deriv (path f x v)) 0 = quadForm (hessianMat f x) v`（**回收 `hg2`**）；
  6. `second_order_taylor_unconditional`：**去 `hg2` 假设**的二阶 Taylor 展开；
  7. `hessianMat_symm` / `hessianMat_isSymmMat`：`ContDiffAt ℝ 2 f x` ⟹
     `hessianMat f x` 对称（一般 n 维 Schwarz，用 `ContDiffAt.isSymmSndFDerivAt`）；
  8. **`RealHessian` 审计的回收**（Task 3）：`hhess_of_contDiffAt` 把
     `RealHessian.second_order_necessary_multidim` 的 `hhess` 假设
     （「路径二阶导 = `quadForm H v`」）变成定理；
     `second_order_necessary_multidim_no_hhess` 给出其去 `hhess` 版本。

## 对 `RealHessian` 的只读审计结论（Task 3）

| 位置 | 显式假设 | 可否升级为定理 |
|:--|:--|:--|
| `second_order_necessary_multidim` | `hhess`（路径二阶导 = `quadForm H v`） | ✅ **本文件升级**（`hhess_of_contDiffAt`） |
| 同上 | `hcont`/`hdiff`/`hd1`/`hd2`（路径光滑性） | ⚠️ 需 `F` 在 `x` **邻域** C²（非点条件），**未做** |
| `second_order_sufficient_multidim` | `hH`（一致正定模数 μ） | ✅ 已由 `RealSecondOrderNoModulus.exists_modulus_of_posDef` 升级 |
| 同上 | `hTaylor`（Taylor 型二次下界） | ⚠️ 需 `ContDiffOn ℝ 3`（二次余项），**未做** |
| `hessian_symmetric` | 仅二维**二次型函数**上的混合偏导交换 | ⊘ 两条独立路线，不构成特例—推广关系（见下） |
| `PosDefQ`/`PosSemidefQ` 与 mathlib `Matrix.PosDef` 的桥接 | 原文件标为「后续工作」 | ⚠️ **未做**（需 `IsHermitian` 与 `dotProduct` 对齐） |

## 诚实边界（**重要**）

  · **`hg2` 的消除是「条件化的」**：`path_second_deriv_eq` 需要
    `ContDiffAt ℝ 2 f x`（`f` 在 `x` 处 C²）。这不是免费的——但它比原来的 `hg2`
    **严格更弱且更标准**：`hg2` 是一个**关于 `H` 的等式**（要求使用者提供正确的 `H`
    与整个二阶 Taylor 结构），而 `ContDiffAt ℝ 2 f x` 是**关于 `f` 的正则性假设**，
    不含任何「答案」。换言之：条件从「答案」变成了「正则性」——这是真正的升级
    （`H` 现在由 `f` **算出**，见 `hessianMat`）；
  · **`quadForm_hessianMat` 是无条件的**（纯双线性性），它是本文件最干净的一条；
  · **未做**：把 `RealTaylorMultivariate` 的**余项界** `|R| ≤ C·normSq v / 2`
    从 `taylor_mean_remainder_bound` 推出（需 `ContDiffOn ℝ 3` 并取 `C = sup‖f'''‖`）；
    本文件只消除 `hg2`，余项界仍以显式 `hbound` 留在原文件（原文件的 docstring 已标注）；
  · `hessianMat_symm` 依赖 mathlib 4.14 的混合偏导交换（`ContDiffAt ℝ 2`），
    前提**显式写出**；`RealHessian.hessian_symmetric` 是二维**二次型函数**
    （`F(a,b) = quadForm M ![a,b]`，对任意矩阵成立、仅需 `quadForm` 的代数性）
    上的混合偏导交换特例，与本文件的 `hessianMat_symm`（作用于任意
    `ContDiffAt ℝ 2` 的 `f`）是两条独立路线，**不构成特例—推广关系**；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter Metric
open scoped Topology BigOperators

namespace Lattice

variable {n : ℕ}

/-! ## 一、由真实二阶 Fréchet 导数定义 Hessian 矩阵 -/

/-- **Hessian 矩阵（由二阶 Fréchet 导数定义）**：
`hessianMat f x i j = fderiv ℝ (fderiv ℝ f) x (eᵢ) (eⱼ)`，
`eᵢ = Pi.single i 1` 是坐标基向量。

与 `RealHessian.quadForm` 的接口：`quadForm (hessianMat f x) v` 恰是二阶 Fréchet 导数
在 `(v, v)` 上的取值（见 `quadForm_hessianMat`）。 -/
def hessianMat (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)

/-- `hessianMat` 的定义展开（`rfl` 级）。 -/
lemma hessianMat_apply_def (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    hessianMat f x i j = fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := rfl

/-- 坐标基展开：`∑ i, v i • eᵢ = v`。 -/
lemma sum_smul_single_eq (v : Fin n → ℝ) :
    (∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) = v := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb)]
    simp
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **辅助（连续线性映射对坐标基展开）**：
`L (∑ j, c j • eⱼ) = ∑ j, c j • L (eⱼ)`。 -/
lemma clm_apply_sum_smul_single (L : (Fin n → ℝ) →L[ℝ] ℝ) (c : Fin n → ℝ) :
    L (∑ j : Fin n, c j • (Pi.single j (1 : ℝ) : Fin n → ℝ))
      = ∑ j : Fin n, c j • L (Pi.single j (1 : ℝ)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]

/-- **二次型恒等式（纯双线性性，无任何可微性假设）**：
    `quadForm (hessianMat f x) v = fderiv ℝ (fderiv ℝ f) x v v`。

证明：把两个变元上的 `v` 都用坐标基展开（`sum_smul_single_eq`），
再用连续线性映射对和与标量乘的线性性把两边化成同一个双重和。

实现：把「对任意 `A` 的两侧展开式」提成引理 `key`，
再对 `A := fderiv ℝ (fderiv ℝ f) x` 与 `quadForm` 的定义分别归约，最后两边取同一形状。 -/
lemma quadForm_hessianMat (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (v : Fin n → ℝ) :
    quadForm (hessianMat f x) v = fderiv ℝ (fderiv ℝ f) x v v := by
  -- 统一的展开形状
  have key : ∀ (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ),
      A v v = ∑ i : Fin n, ∑ j : Fin n, v i * (v j * A (Pi.single i 1) (Pi.single j 1)) := by
    intro A
    -- 一级展开：`A (∑ i, v i • eᵢ) = ∑ i, v i • A eᵢ`
    have h1 : A (∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ))
        = ∑ i : Fin n, v i • A (Pi.single i (1 : ℝ)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    -- 二级展开：每个 `A eᵢ` 再作用在 `∑ j, v j • eⱼ` 上
    have h2 : ∀ i : Fin n,
        (A (Pi.single i (1 : ℝ))) (∑ j : Fin n, v j • (Pi.single j (1 : ℝ) : Fin n → ℝ))
          = ∑ j : Fin n, v j * ((A (Pi.single i (1 : ℝ))) (Pi.single j (1 : ℝ))) := by
      intro i
      rw [clm_apply_sum_smul_single]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]
    -- 两次代入：先左变元、再右变元
    calc A v v
        = A (∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) v := by
            rw [sum_smul_single_eq v]
      _ = (∑ i : Fin n, v i • A (Pi.single i (1 : ℝ))) v := by rw [h1]
      _ = ∑ i : Fin n, (v i • A (Pi.single i (1 : ℝ))) v := by
            rw [ContinuousLinearMap.sum_apply]
      _ = ∑ i : Fin n, v i • ((A (Pi.single i (1 : ℝ))) v) := by
            exact Finset.sum_congr rfl fun i _ => by rw [ContinuousLinearMap.smul_apply]
      _ = ∑ i : Fin n, v i • ((A (Pi.single i (1 : ℝ)))
              (∑ j : Fin n, v j • (Pi.single j (1 : ℝ) : Fin n → ℝ))) := by
            exact Finset.sum_congr rfl fun i _ => by rw [sum_smul_single_eq v]
      _ = ∑ i : Fin n, v i • (∑ j : Fin n, v j * ((A (Pi.single i (1 : ℝ)))
              (Pi.single j (1 : ℝ)))) := by
            exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
      _ = ∑ i : Fin n, ∑ j : Fin n, v i * (v j * A (Pi.single i 1) (Pi.single j 1)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]
  have key2 : quadForm (hessianMat f x) v
      = ∑ i : Fin n, ∑ j : Fin n,
          v i * (v j * fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)) := by
    rw [quadForm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hessianMat]
    ring
  rw [key2, key]

/-! ## 二、C² 蕴含 `fderiv` 可导（为链式法则供能） -/

/-- **`ContDiffAt ℝ 2 f x` ⟹ `fderiv ℝ f` 在 `x` 处有 Fréchet 导数 `fderiv ℝ (fderiv ℝ f) x`**。

证明：`ContDiffAt.fderiv_right`（取 `m = 1`, `n = 2`，故 `1 + 1 ≤ 2`）给出
`ContDiffAt ℝ 1 (fderiv ℝ f) x`；`ContDiffAt ℝ 1` 即 `DifferentiableAt ℝ`，
其 `HasFDerivAt` 的导数正是 `fderiv ℝ (fderiv ℝ f) x`（`fderiv` 的定义）。 -/
lemma hasFDerivAt_fderiv_of_contDiffAt {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by norm_num)).hasFDerivAt

/-! ## 三、核心桥接：路径二阶导 = 二阶 Fréchet 导数 -/

/-- **路径二阶导 = 二阶 Fréchet 导数在 `(v, v)` 上的取值**（前提 `ContDiffAt ℝ 2 f x`）：

    `deriv (deriv (path f x v)) 0 = fderiv ℝ (fderiv ℝ f) x v v`

证明（两级链式法则）：
  · 记 `A := fderiv ℝ (fderiv ℝ f) x`；
  · 路径映射 `φ t = x + t • v` 在任意 `t` 处有导数 `v`；
  · `f` 在 `φ t` 处的 Fréchet 导数为 `fderiv ℝ f (φ t)`；
  · 复合得 `HasFDerivAt (f ∘ φ) ((fderiv ℝ f (φ t)).comp (smulRight 1 v)) t`，
    它在 `1` 上的取值是 `(fderiv ℝ f (φ t)) v`，故
    `deriv (path f x v) t = (fderiv ℝ f (x + t • v)) v`（逐点，即 `=ᶠ`）；
  · 对 `t ↦ (fderiv ℝ f (x + t • v)) v` 再用一次链式法则：由
    `hasFDerivAt_fderiv_of_contDiffAt` 得 `fderiv ℝ f` 在 `x` 处导数为 `A`，
    复合 `φ` 得 `HasDerivAt (fun t => fderiv ℝ f (x + t • v)) (A v) 0`；
    再用 `HasFDerivAt.clm_apply`（求值双线性）把 `→L` 值映成 `A v v`。 -/
theorem path_second_deriv_eq {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (v : Fin n → ℝ) :
    deriv (deriv (path f x v)) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
  -- 路径映射 `φ s = x + s • v` 的导数（处处为 `v`）
  have hφ_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    have h2 : HasDerivAt (fun _ : ℝ => x) 0 t := hasDerivAt_const t x
    simpa using h2.add h1
  -- `f` 在 `x` 的邻域内处处 C²（`ContDiffAt.eventually`），故在 `x` 附近处处可微
  have hev2 : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
  have hev1 : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hev2] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  -- 一阶：在 `0` 的邻域内 `deriv (path f x v) t = (fderiv ℝ f (x + t • v)) v`
  have hφ_cont : Continuous (fun s : ℝ => x + s • v) := by fun_prop
  have h1 : deriv (path f x v) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ => (fderiv ℝ f (x + t • v)) v := by
    have hφ0' : (fun s : ℝ => x + s • v) 0 = x := by simp
    have hev1' : ∀ᶠ y in 𝓝 ((fun s : ℝ => x + s • v) 0), HasFDerivAt f (fderiv ℝ f y) y := by
      rw [hφ0']; exact hev1
    have hpre : ∀ᶠ t in 𝓝 (0 : ℝ), HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) :=
      hφ_cont.continuousAt.eventually hev1'
    filter_upwards [hpre] with t ht
    have hcomp : HasFDerivAt (fun s : ℝ => f (x + s • v))
        ((fderiv ℝ f (x + t • v)).comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v)) t :=
      ht.comp t (hφ_deriv t).hasFDerivAt
    have hd : HasDerivAt (path f x v)
        (((fderiv ℝ f (x + t • v)).comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v)) 1) t :=
      hcomp.hasDerivAt
    rw [hd.deriv]
    simp [path, ContinuousLinearMap.smulRight_apply]
  rw [Filter.EventuallyEq.deriv_eq h1]
  -- 二阶：对 `t ↦ (fderiv ℝ f (x + t • v)) v` 在 `0` 处求导
  have hφ0 : x + (0 : ℝ) • v = x := by simp
  have hbase : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v))
      ((fderiv ℝ (fderiv ℝ f) x) v) 0 := by
    have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x + (0 : ℝ) • v) := by
      rw [hφ0]; exact hasFDerivAt_fderiv_of_contDiffAt hf
    exact hfd'.comp_hasDerivAt 0 (hφ_deriv 0)
  have hv_deriv : HasDerivAt (fun _ : ℝ => v) 0 0 := hasDerivAt_const (0 : ℝ) v
  have h2 : HasDerivAt (fun t : ℝ => (fderiv ℝ f (x + t • v)) v)
      (((fderiv ℝ (fderiv ℝ f) x) v) v) 0 := by
    have hclm : HasDerivAt (fun t : ℝ => (fderiv ℝ f (x + t • v)) v)
        (((fderiv ℝ (fderiv ℝ f) x) v) v + (fderiv ℝ f (x + (0 : ℝ) • v)) 0) 0 :=
      hbase.clm_apply hv_deriv
    rw [hφ0, map_zero, add_zero] at hclm
    exact hclm
  exact h2.deriv

/-- **回收 `RealTaylorMultivariate.second_order_taylor` 的 `hg2` 假设**（前提 `ContDiffAt ℝ 2 f x`）：
    `deriv (deriv (path f x v)) 0 = quadForm (hessianMat f x) v`。

由 `path_second_deriv_eq` 与**无条件**的 `quadForm_hessianMat` 复合而成。 -/
theorem path_second_deriv_eq_quadForm {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (v : Fin n → ℝ) :
    deriv (deriv (path f x v)) 0 = quadForm (hessianMat f x) v := by
  rw [path_second_deriv_eq hf, quadForm_hessianMat]

/-! ## 四、去假设的二阶 Taylor 展开 -/

/-- **二阶 Taylor 展开（回收 `hg2` 版）**：把
`RealTaylorMultivariate.second_order_taylor` 的假设 `hg2` 去掉，`H` 取为由 `fderiv²`
定义的 `hessianMat f x`，只余 `ContDiffAt ℝ 2 f x`：

    ∃ R, f (x + v) = f x + deriv (path f x v) 0
                      + (1/2) * quadForm (hessianMat f x) v + R

证明：调用原定理，`hg2` 由 `path_second_deriv_eq_quadForm` 提供。 -/
theorem second_order_taylor_unconditional {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (v : Fin n → ℝ) :
    ∃ R : ℝ, f (x + v)
      = f x + deriv (path f x v) 0 + (1 / 2) * quadForm (hessianMat f x) v + R :=
  second_order_taylor (f := f) (x := x) (v := v) (H := hessianMat f x)
    (path_second_deriv_eq_quadForm hf v)

/-! ## 五、一般 n 维 Schwarz 对称性 -/

/-- **Hessian 矩阵对称（一般 n 维 Schwarz 定理）**：`ContDiffAt ℝ 2 f x` ⟹
`hessianMat f x` 对称，即 `hessianMat f x i j = hessianMat f x j i`。

证明：`ContDiffAt.isSymmSndFDerivAt`（取 `n = 2`，故 `2 ≤ 2`）给出
`IsSymmSndFDerivAt ℝ f x`，即 `∀ v w, fderiv (fderiv f) x v w = fderiv (fderiv f) x w v`；
取 `v = eᵢ`、`w = eⱼ` 并用 `hessianMat` 的定义即得。`RealHessian.hessian_symmetric`
则是二维**二次型函数**上的混合偏导交换（对任意矩阵成立、仅需 `quadForm` 的代数性），
与本定理是两条独立路线，**不是**本定理的 `n = 2` 回收。

**诚实标注**：前提 `ContDiffAt ℝ 2 f x` **显式写出且不可省**——对仅「二阶可微」的
`f`，混合偏导未必交换（经典反例），故这不是无条件命题。 -/
theorem hessianMat_symm {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    hessianMat f x i j = hessianMat f x j i :=
  (hf.isSymmSndFDerivAt (𝕜 := ℝ) (n := (2 : WithTop ℕ∞)) (by norm_num))
    (Pi.single i 1) (Pi.single j 1)

/-- **二次型的对称性回收**：`ContDiffAt ℝ 2 f x` ⟹
`quadForm (hessianMat f x) v = quadForm (hessianMat f x)ᵀ v`，
即二次型只依赖 Hessian 的对称部分（与 `RealHessian.quadForm_transpose` 衔接）。

由 `hessianMat_symm` 得 `hessianMat f x` 自身对称，再用转置不变性。 -/
theorem hessianMat_isSymmMat {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) : IsSymmMat (hessianMat f x) := by
  unfold IsSymmMat
  ext i j
  simp only [Matrix.transpose_apply]
  exact hessianMat_symm hf j i

/-! ## 六、回收 `RealHessian` 的 `hhess` 假设（Task 3 审计结果）

对 `RealHessian` 做**只读**审计后，其剩余「显式假设」有三类：

  | 位置 | 假设 | 可否升级 |
  |:--|:--|:--|
  | `second_order_necessary_multidim` L345–L348 | `hcont`/`hdiff`/`hd1`/`hd2` | 成立 由 `ContDiffOn ℝ 2` 一次性产出（同 `RealKKTSecondOrder` 第七节路线），本文件提供 `hhess` 一条 |
  | 同上 L349 | **`hhess`**：`∀v, deriv (deriv (fun t => F (x + t•v))) 0 = quadForm H v` | 成立 **本文件升级**（见下 `path_second_deriv_eq` 的直接回收） |
  | `second_order_sufficient_multidim` L404 | `hH`：模数界 | 成立 已由 `RealSecondOrderNoModulus.exists_modulus_of_posDef` 升级 |
  | 同上 L405 | `hTaylor`：Taylor 型二次下界 | 注意 **需 `ContDiffOn ℝ 3`**（二次余项），非无条件；未做 |

下面给出 `hhess` 的回收：`RealHessian` 中的路径写成 `fun t => F (x + t • v)`，
与 `path F x v` **定义相等**，故 `path_second_deriv_eq` 直接给出 `hhess` 的 `H`。 -/

/-- **`RealHessian` 的路径形式与 `path` 定义相等**（便于把两者互译）。 -/
lemma hessian_path_eq (F : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) :
    (fun t : ℝ => F (x + t • v)) = path F x v := rfl

/-- **回收 `RealHessian.second_order_necessary_multidim` 的 `hhess` 假设**：
`ContDiffAt ℝ 2 F x` ⟹ 原文件所需的
`∀ v, deriv (deriv (fun t => F (x + t • v))) 0 = quadForm (hessianMat F x) v`。

即：**`H` 不必外部提供**——取 `H := hessianMat F x` 即可。 -/
theorem hhess_of_contDiffAt {F : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 F x) :
    ∀ v : Fin n → ℝ,
      deriv (deriv (fun t : ℝ => F (x + t • v))) 0 = quadForm (hessianMat F x) v :=
  fun v => path_second_deriv_eq_quadForm hf v

/-! ## 七、`RealHessian.second_order_necessary_multidim` 的去假设版

把 `hhess` 换成 `ContDiffAt ℝ 2 F x`，其余假设（路径光滑性）保留——
**结论与 `RealHessian` 版完全一致**：`∀ v, 0 ≤ quadForm (hessianMat F x) v`（Hessian 半正定）。

**诚实标注**：路径光滑性假设 `hcont`/`hdiff`/`hd1`/`hd2` **保留**（未升级）——
它们可由 `ContDiffOn ℝ 2` 按 `RealKKTSecondOrder.contDiff_two_gives_interval_hypotheses`
的同一路线产出，但需要把 `F` 在 `x` 的**邻域**上的 C² 性（`ContDiffAt` 只给点条件，
而 `Ioo (-1) 1` 上的路径光滑性需要 `F` 在 `x` 附近 C²），故此处**不假称已升级**。 -/
theorem second_order_necessary_multidim_no_hhess {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ}
    (hmin : IsLocalMin F x)
    (hcont : ∀ v : Fin n → ℝ, ContinuousOn (fun t : ℝ => F (x + t • v)) (Ioo (-1) 1))
    (hdiff : ∀ v : Fin n → ℝ, DifferentiableOn ℝ (fun t : ℝ => F (x + t • v)) (Ioo (-1) 1))
    (hd1 : ∀ v : Fin n → ℝ, ContinuousOn (deriv (fun t : ℝ => F (x + t • v))) (Ioo (-1) 1))
    (hd2 : ∀ v : Fin n → ℝ, ContinuousAt (deriv (deriv (fun t : ℝ => F (x + t • v)))) 0)
    (hf : ContDiffAt ℝ 2 F x) :
    ∀ v : Fin n → ℝ, 0 ≤ quadForm (hessianMat F x) v :=
  second_order_necessary_multidim hmin hcont hdiff hd1 hd2 (hhess_of_contDiffAt hf)

end Lattice
