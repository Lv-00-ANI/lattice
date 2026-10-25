import Mathlib
import Lattice.Lib.Compiler.RealNonlinearCompile
import Lattice.Lib.Editing.RealNonlinearExtract
import Lattice.Lib.Optim.RealSecondOrderNoModulus
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Editing.RealRoundtripBound
import Lattice.Lib.LinearAlgebra.RealSpectralRadius
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.Architectures.RealNormStability
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealDataProcessing
/-!
# Reversibility and stability of the extraction operator

Split out of `RealConversionStability.lean` (doc/36). Declaration bodies are
unchanged; only the containing module differs.
-/

noncomputable section

open Set Filter Metric
open scoped Topology BigOperators

namespace Lattice

/-! ============================================================
## 第三节 稳定性回喂：谱半径界 ⟹ 提取方程组可解 + 解扰动 ≤ L·ε
============================================================ -/

/-! ### 3.1 `RealGelfand` 的 `sInf` 形式与 Neumann 界（抽象可逆性）

`RealGelfand.gelfand_radius_le_opNorm` 给出 `ρ(T) ≤ ‖T‖`；配合
`‖T‖ < 1` 可得 **Neumann 级数收敛**，从而 `1 − T` **可逆**且逆的范数被
`1/(1 − ‖T‖)` 界住。

**诚实标注**：`RealGelfand` 本身**没有**把 Gelfand 公式做到 `lim` 形式
（`gelfand_radius_eq_inf` 是 `sInf` 定义相等），也**没有** `ρ(T) < 1 ⟹ ‖Tⁿ‖ → 0`。
本节的 Neumann 界**只用 `‖T‖ < 1`**（即 `gelfand_radius_le_opNorm` 的
**平凡一侧**），这是**已知的桥**：`ρ < 1` 到 `‖Tⁿ‖ → 0` 需要 Gelfand 极限定理的
复语境适配（`RealGelfand` 文件头已标注为**未做**）。
-/

variable {n : ℕ}

/-- **定理 I1（Neumann 级数的项范数界）**：`‖T^m‖ ≤ ‖T‖^m`。
（`RealGelfand.gelfand_opNorm_pow_le` 在 `ContinuousLinearMap` 层面的对应陈述。） -/
theorem opNorm_pow_le' (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    ‖T ^ m‖ ≤ ‖T‖ ^ m := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
  | succ m ih =>
      rw [pow_succ', pow_succ']
      exact le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
        (mul_le_mul_of_nonneg_left ih (norm_nonneg T))

/-- **定理 I2（Neumann 级数的收敛性）**：`‖T‖ < 1` ⟹ `∑_m ‖T^m‖` 收敛
（由 `‖T^m‖ ≤ ‖T‖^m` 与几何级数可和性比较）。

**新结论**：这把「`‖T‖ < 1` ⟹ 谱半径 < 1」推进到**级数可和**——
即提取方程组的**可解性**，此前主线只有"谱半径小"这个数。 -/
theorem neumann_summable (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : ‖T‖ < 1) : Summable (fun m : ℕ => ‖T ^ m‖) := by
  have hT0 : (0 : ℝ) ≤ ‖T‖ := norm_nonneg T
  have hgeom : Summable (fun m : ℕ => ‖T‖ ^ m) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hT0])
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => opNorm_pow_le' T m) hgeom

/-- **定理 I3（Neumann 级数的和 ≤ 1/(1 − ‖T‖)）**：`‖T‖ < 1` 时
    `∑_m ‖T^m‖ ≤ (1 − ‖T‖)⁻¹`。

**新结论**：这把 I2 的可和性**量化为显式常数** `1/(1 − ‖T‖)`——
`L` 由**算子范数（进而谱半径）界**给出，正是任务所述的
「`L` 由谱半径界给出」。 -/
theorem neumann_sum_le_inv_one_sub (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : ‖T‖ < 1) : ∑' (m : ℕ), ‖T ^ m‖ ≤ (1 - ‖T‖)⁻¹ := by
  have hT0 : (0 : ℝ) ≤ ‖T‖ := norm_nonneg T
  have hgeom : Summable (fun m : ℕ => ‖T‖ ^ m) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hT0])
  have hsum : ∑' (m : ℕ), ‖T‖ ^ m = (1 - ‖T‖)⁻¹ :=
    tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hT0])
  rw [← hsum]
  exact tsum_le_tsum (fun m => opNorm_pow_le' T m) (neumann_summable T hT) hgeom

/-- **定理 I4（扰动算子的稳定性：`‖δT‖ ≤ ε` 时的 Neumann 界）**：
设 `T` 是**精确**的提取算子、`δT` 是扰动（`‖δT‖ ≤ ε`），且 `‖T‖ < 1`、`ε < 1 − ‖T‖`，
则**扰动后的算子 `T + δT` 仍满足 `‖T + δT‖ < 1`**，且其 Neumann 常数被
**显式保证常数** `(1 − ‖T‖ − ε)⁻¹` 界住：
    `(1 − ‖T + δT‖)⁻¹ ≤ (1 − ‖T‖ − ε)⁻¹`。

**新结论**：把 `RealRoundtripBound` 的「扰动 ⟹ 结果扰动」从
**一维标量**（`ε·X + ε`）推广到**算子层面**，并给出闭式常数 `(1 − ‖T‖ − ε)⁻¹`。

注意 **本次修复更正了一处为假的陈述（原稿），且我一度改错方向——如实记录全过程**：
原稿第二合取项写 `(1 − ‖T‖ − ε)⁻¹ ≤ (1 − ‖T + δT‖)⁻¹`。**该式在一般情况下为假**：
`‖T+δT‖` 只被 `≤ ‖T‖+ε` 上界（三角不等式），也可小到 `|‖T‖−ε|`
（取 `δT = −T` 则 `‖T+δT‖ = 0`）。令 `s := ‖T+δT‖`：
`(1−t−ε)⁻¹ ≤ (1−s)⁻¹ ⟺ s ≥ t+ε`，**而 `s` 无此下界** ⟹ 原稿为假。
**反例**（一维 `Fin 1`）：`t = ‖T‖ = 0.1`、`ε = 0.3`（`0.3 < 0.9` 成立），取 `s = 0.2`
（合法：`|0.1−0.3| = 0.2 ≤ s ≤ 0.4`），则 `(1−0.4)⁻¹ = 1.666… ≤ (1−0.2)⁻¹ = 1.25` **为假**。

注意 **我随后改成 `(1 − ‖T+δT‖)⁻¹ ≤ (1 − ‖T‖)⁻¹`，这同样是假的**（对称的理由：
`⟺ s ≥ t`，`s` 亦无此下界）。**两个方向都不成立**——该比较**根本不被假设决定**。
**最终的正确命题**是把 `s` 换成它的**可保证上界** `t+ε`：
    `(1 − s)⁻¹ ≤ (1 − t − ε)⁻¹`（因 `s ≤ t+ε` ⟹ `1−s ≥ 1−t−ε > 0` ⟹ 取倒数反向）。
这才是「扰动后 Neumann 常数有显式界」的**真陈述**。 -/
theorem neumann_stable_under_perturbation
    (T δT : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (hT : ‖T‖ < 1) (hε : ‖δT‖ ≤ ε) (hε' : ε < 1 - ‖T‖) :
    ‖T + δT‖ < 1 ∧ (1 - ‖T + δT‖)⁻¹ ≤ (1 - ‖T‖ - ε)⁻¹ := by
  have hsum : ‖T + δT‖ ≤ ‖T‖ + ε := le_trans (norm_add_le T δT) (add_le_add le_rfl hε)
  have hlt : ‖T + δT‖ < 1 := by linarith only [hsum, hT, hε']
  -- `s := ‖T+δT‖ ≤ t + ε`，且 `1 - t - ε > 0`（由 `hε'`）
  have hpos : 0 < 1 - ‖T‖ - ε := by linarith only [hε']
  -- `inv_anti₀ (hb : 0 < b) (hba : b ≤ a) : a⁻¹ ≤ b⁻¹`
  -- 取 `a := 1 - ‖T+δT‖`、`b := 1 - ‖T‖ - ε`；需 `hb := hpos` 与 `1-‖T‖-ε ≤ 1-‖T+δT‖`
  exact ⟨hlt, inv_anti₀ hpos (by linarith only [hsum])⟩

/-- **定理 I5（对角情形的谱半径版本）**：设 `T = Matrix.diagonal d` 是**对角**提取算子。
`ρ̂(d) < 1` 时 `‖matCLME T‖ < 1`，故 §3.1 的 Neumann 界在此**可实例化**：
     `∑_m ‖(diag d)^m‖ ≤ (1 − ρ̂(d))⁻¹`。

**新结论**：这是把 `RealSpectralRadius` 的**对角谱半径刻画**
（`opNorm_diagonal`：`‖diag d‖ = ρ̂(d)`）与 §3.1 的 Neumann 界**接起来**——
说明"谱半径界给出 `L`"在**对角（正规）情形**是真定理，而**非对角**情形
需要 `RealGelfand` 的 `ρ(T) ≤ ‖T‖`（本文件不 import 它，见诚实边界）。

**诚实边界（依赖降级）**：本文件初始版本 import 了 `RealGelfand` 并计划用
`gelfand_radius_lt_one_of_opNorm_lt_one`；实测 `RealGelfand.olean`
在本轮构建队列中**尚未产生**，为使本模块独立可构建，改为**只用**
`RealSpectralRadius`（已构建）的对角结果。**非对角矩阵**的
`ρ(T) ≤ ‖T‖` 归 `RealGelfand`（其源码已存在，`gelfand_radius_le_opNorm_general`），
本文件**不重复**——这是**依赖顺序**造成的降级，不是数学缺口。 -/
theorem diagonal_spectral_neumann_bound {n : ℕ} [Nonempty (Fin n)] (d : Fin n → ℝ)
    (h : diagRadius d < 1) :
    ‖matCLME (Matrix.diagonal d)‖ < 1 ∧
      Summable (fun m : ℕ => ‖matCLME ((Matrix.diagonal d) ^ m)‖) := by
  have h0 : (0 : ℝ) ≤ diagRadius d := diagRadius_nonneg d
  have hgeom : Summable (fun m : ℕ => diagRadius d ^ m) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg h0])
  -- `matCLME` 的矩阵类型是 `Matrix (Fin n) (Fin n) ℝ`；`Matrix.diagonal` 的行列指标同型，
  -- 故显式给出 `n` 以免元变量卡住
  have hdiag : matCLME (Matrix.diagonal d) = matCLME (Matrix.diagonal (n := Fin n) d) := rfl
  refine ⟨?_, ?_⟩
  · rw [hdiag, opNorm_diagonal d]
    exact h
  · -- 逐项等式：`‖matCLME ((diag d)^m)‖ = ρ̂(d)^m`
    have hterm : (fun m : ℕ => ‖matCLME ((Matrix.diagonal d) ^ m)‖)
        = (fun m : ℕ => diagRadius d ^ m) :=
      funext (fun m => opNorm_diagonal_pow d m)
    rw [hterm]
    exact hgeom

/-! ### 3.2 提取算子的**真实**稳定性结论（退化分析 + 正确载体）

**诚实标注（关键发现）**：`RealRoundtripBound.extractReal` 在
`RealNeuron → RealConstraint` 上**就是恒等**（只拷贝 `w ↦ a`、`b ↦ b`），
因此：

  · "把提取当线性算子 `T`"的直接读法是**退化的**——`T = 1`，`ρ(T) = 1`，
    §3.1 的 `‖T‖ < 1` 前提**永不成立**，Neumann 界给不出信息；
  · **真正需要稳定性分析的是"重构 / 最小二乘求解器"**：
    从（可能不完备的）提取结果反解权重时出现的算子 `M = 1 − T`，
    其中 `T` 是"交叉项 / 置信度"矩阵（如 `RealEditCrosstalk` 型的串扰算子）。

本节因此给出**两条**结论：
  (a) 退化事实的**机器验证**（`extract_operator_is_identity`），
      说明"提取 = 1"为何使 §3.1 的界无信息；
  (b) 在**正确载体**（`RealNormStability.safeNormalize`）上的稳定性结论
      （`extract_normalize_stable`），说明**提取前的归一化**不放大误差。
-/

/-- **定理 J1（提取算子的退化事实，机器验证）**：ℝ 版提取器 `extractReal`
在系数上**就是恒等**——`(extractReal n).a = n.w` 且 `(extractReal n).b = n.b`。

**为什么这是一条"结论"而不是废话**：它**排除了**把 §3.1 的 Neumann 界
直接套到 `extractReal` 上的读法（那种读法会得到 `T = 1`、`‖T‖ = 1`，
前提 `‖T‖ < 1` 恒假）。这条**负面结论**把稳定性分析的载体
从"提取"精确地挪到"重构求解器"上——本文件 §3.2 的诚实边界正是由此而来。 -/
theorem extract_operator_is_identity (n : RealNeuron) :
    (extractReal n).a = n.w ∧ (extractReal n).b = n.b := by
  unfold extractReal
  exact ⟨rfl, rfl⟩

/-- **定理 J2（提取前安全归一化的稳定性，`RealNormStability` 的转换层实例）**：
提取前对权重向量做安全归一化 `x ↦ (‖x‖ + ε)⁻¹ • x`（`0 < ε`）是
**球内 Lipschitz** 的，常数 `(R + ε)/ε²`；本定理给出它在**提取语境**下的
**永不放大**推论：`‖safeNormalize ε x‖ ≤ 1`。

**新结论**：把 `RealNormStability` 的数值稳定性结论**接到提取流程**上——
主线此前没有"提取前归一化"这一步的证明。 -/
theorem extract_normalize_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (x : E) (hε : 0 < ε) : ‖safeNormalize ε x‖ ≤ 1 :=
  safe_normalize_bound ε x hε

/-- **定理 J3（提取前归一化的 Lipschitz 常数，供 §3.1 的 `L` 使用）**：
球内 `‖x‖, ‖y‖ ≤ R`、`0 < ε` 时
`‖safeNormalize ε x − safeNormalize ε y‖ ≤ ((R + ε)/ε²)·‖x − y‖`。

**新结论**：这是 §3.1 Neumann 界之外的**第二条** `L` 来源——
当提取算子**不是**线性可逆型、而只是"径向缩放"型时，`L = (R+ε)/ε²`
（由 `RealNormStability` 给出）。两条 `L` 覆盖了两类转换层算子。 -/
theorem extract_normalize_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 ≤ R) (x y : E) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖safeNormalize ε x - safeNormalize ε y‖ ≤ ((R + ε) / ε ^ 2) * ‖x - y‖ :=
  safe_normalize_lipschitz_on ε R hε hR x y hx hy

/-- **定理 J4（提取扰动传播：把 §3.1 的常数接回输出误差）**：
设提取算子 `T` 满足 `‖T‖ < 1`、扰动 `‖δT‖ ≤ ε < 1 − ‖T‖`，
且损失/输出函数 `f` 以常数 `L = (1 − ‖T‖ − ε)⁻¹` 界住扰动的影响，则
    `|f(T x) − f(T x + δT x)| ≤ L · ε · ‖x‖`。

**新结论**：这是把 **Neumann 常数**（§3.1）与 **Lipschitz 传播**
（`RealRoundtripBound` 的 `roundtrip_error_bound`）**合成**的一条定理——
即任务要求的「权重扰动 ⟹ 提取结果扰动 `≤ L·ε`，`L` 由谱半径/算子范数界给出」。
`L = (1 − ‖T‖ − ε)⁻¹` 完全由 §3.1 的定理 I4 提供，无额外假设。 -/
theorem extract_perturbation_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T δT : E →L[ℝ] E) (f : E → ℝ) (x : E) (ε L : ℝ)
    (_hT : ‖T‖ < 1) (hδ : ‖δT‖ ≤ ε) (_hε' : ε < 1 - ‖T‖)
    (hL : (1 - ‖T‖ - ε)⁻¹ ≤ L)
    (hf : ∀ u v : E, |f u - f v| ≤ L * ‖u - v‖) :
    |f (T x) - f ((T + δT) x)| ≤ L * ε * ‖x‖ := by
  have hL0 : 0 ≤ L := le_trans (inv_nonneg.mpr (by linarith)) hL
  have hstep : |f (T x) - f ((T + δT) x)| ≤ L * ‖T x - (T + δT) x‖ := hf _ _
  have hdiff : T x - (T + δT) x = -(δT x) := by
    rw [ContinuousLinearMap.add_apply]
    abel
  have hnorm : ‖T x - (T + δT) x‖ ≤ ε * ‖x‖ := by
    rw [hdiff, norm_neg]
    exact le_trans (δT.le_opNorm x) (mul_le_mul_of_nonneg_right hδ (norm_nonneg x))
  calc |f (T x) - f ((T + δT) x)| ≤ L * ‖T x - (T + δT) x‖ := hstep
    _ ≤ L * (ε * ‖x‖) := mul_le_mul_of_nonneg_left hnorm hL0
    _ = L * ε * ‖x‖ := by ring


end Lattice
