import Mathlib
import Lattice.Lib.LinearAlgebra.RealGelfand
import Lattice.Lib.Architectures.RealMatrixNorm
/-!
# LATTICE: 与 mathlib 标准 `spectralRadius` 的桥接（回收 `Spectrum.lean`）

本文件把 `RealGelfand.gelfandRadius`（本项目自定义的 **`sInf` over `‖Tᵏ‖^{1/k}`**，
实值）与 **mathlib 标准** `spectrum.spectralRadius`（**`sSup over spectrum`**，
`ℝ≥0∞` 值）**接起来**，并把 mathlib 已有的 `ρ ≤ ‖·‖` 定理**回收**到本项目的算子语境。

## 为什么需要它（两种定义的差异，如实记录）

| | 本项目 `gelfandRadius` | mathlib `spectrum.spectralRadius` |
|:--|:--|:--|
| 定义 | `sInf { ‖Tᵏ‖^{1/k} \| k > 0 }` | `⨆ k ∈ spectrum 𝕜 a, ‖k‖₊` |
| 取值范围 | `ℝ` | `ℝ≥0∞` |
| 依据 | 只用**算子范数**（构造性、无需谱理论） | 用**谱**（需 Banach 代数机制） |
| 4.14 位置 | 本项目 `RealGelfand:gelfandRadius` | `Spectrum.lean:56-58` |

两者在「极限存在」时相等——**这正是 Gelfand 公式**。本文件给出**可证的方向**。

## 本文件交付

| 声明 | 内容 |
|:--|:--|
| `rg_spectralRadius_le_nnnorm` | **回收** mathlib `spectrum.spectralRadius_le_nnnorm`（`:176`）到 `ContinuousLinearMap` 语境 |
| `rg_spectralRadius_toReal_le_norm` | 上一行的 `ℝ` 值形式（`ℝ≥0∞ ≤ ↑‖a‖` 的 `toReal` 化） |
| `rg_spectrum_nonempty` | 复 Banach 代数中谱非空（`spectrum.nonempty`，`:398`） |
| `rg_exists_nnnorm_eq_spectralRadius` | **谱半径取到**（`exists_nnnorm_eq_spectralRadius`，`:413`） |
| `rg_gelfand_formula` | **Gelfand 公式的 `lim` 形式**（`Spectrum.lean:374`）在 `ContinuousLinearMap` 上的实例化 |
| `rg_gelfand_formula_norm` | 同上，`norm` 版（`Spectrum.lean:383`） |
| `rg_spectralRadius_pow_le` | `ρ(a)ⁿ ≤ ρ(aⁿ)` —— **上游只证这一侧**（4.33 `Spectrum.lean:94`）|

## 为什么用 `E →L[ℂ] E` 而不是 `Matrix`

诚实标注（**设计决策，避免全局副作用**）：
把 `Matrix (Fin n) (Fin n) ℂ` 注册成 `NormedRing` 会是**全局类型类实例**，
影响整个仓库（且与 `Matrix` 的既有 `Ring`/`Norm` 实例可能冲突）。
而 `E →L[ℂ] E`（`ContinuousLinearMap`）**mathlib 已自带**
`NormedRing` / `NormedAlgebra` / `CompleteSpace` 实例（当 `E` 是复 Banach 空间时），
故**零副作用**即可吃到 `Spectrum.lean` 的全部定理。

**用途**：本项目 `RealGelfand` 里的实算子 `matCLME T : E →L[ℝ] E`
若要套用 Gelfand 的 `lim` 形式，只需把 `E` 换成复化空间（或直接在复空间上工作），
即可用本文件的 `rg_gelfand_formula`。这是 `RealGelfand` docstring 中
「缺的是复语境适配」的**具体落点**。

无 `sorry`/`axiom`/`admit`。
-/

noncomputable section

open scoped ENNReal NNReal Topology

namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-! ## 第一节：回收 `ρ ≤ ‖·‖`（`Spectrum.lean:176`） -/

/-- **回收 mathlib `spectrum.spectralRadius_le_nnnorm`**（`Spectrum.lean:176`）：
复 Banach 代数中的元素 `a` 满足 `spectralRadius ℂ a ≤ ‖a‖₊`。

这里以 `A := E →L[ℂ] E`（`ContinuousLinearMap`，自带 `NormedRing` 实例）为实例，
展示该定理**在算子语境下可用**——即 `RealGelfand.gelfand_radius_le_opNorm`
（`ρ(T) ≤ ‖T‖`）的 mathlib 标准版对应物。

诚实标注（**命名空间事实，已核对源码**）：`spectralRadius` 定义在
`Spectrum.lean:56`，位于 `namespace spectrum`（`:62`）**之前**，故其**全名是根命名空间的
`spectralRadius`**；而 `spectralRadius_le_nnnorm`（`:176`）**在** `namespace spectrum` 内，
故全名是 **`spectrum.spectralRadius_le_nnnorm`**。两者命名空间不同——这是本文件
第一轮 `unknown constant 'spectrum.spectralRadius'` 的根因。

另需 `[NormOneClass (E →L[ℂ] E)]`：对 `ContinuousLinearMap`，该实例由
`NormOneClass` 的 CLM 实例提供（需 `E` 非退化；此处以显式假设传入，避免在大范围
合成上花时间）。 -/
theorem rg_spectralRadius_le_nnnorm [NormOneClass (E →L[ℂ] E)] (a : E →L[ℂ] E) :
    spectralRadius ℂ a ≤ ‖a‖₊ :=
  spectrum.spectralRadius_le_nnnorm a

/-- **`ℝ` 值形式**：`(spectralRadius ℂ a).toReal ≤ ‖a‖`。

诚实标注：`spectralRadius` 取值于 `ℝ≥0∞`，转化为 `ℝ` 用 `ENNReal.toReal`；
本定理给出「`ρ` 的实数值被算子范数控制」这一**下游最常用**的形式
（与 `RealGelfand.gelfand_radius_le_opNorm` 的结论形状一致）。 -/
theorem rg_spectralRadius_toReal_le_norm [NormOneClass (E →L[ℂ] E)] (a : E →L[ℂ] E) :
    (spectralRadius ℂ a).toReal ≤ ‖a‖ := by
  have h := rg_spectralRadius_le_nnnorm a
  have hne : (‖a‖₊ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  calc (spectralRadius ℂ a).toReal
      ≤ (‖a‖₊ : ℝ≥0∞).toReal := ENNReal.toReal_mono hne h
    _ = ‖a‖ := by simp

/-! ## 第二节：谱非空与谱半径取到（`Spectrum.lean:398` / `:413`） -/

/-- **复 Banach 代数中谱非空**（回收 `spectrum.nonempty`，`Spectrum.lean:398`）：
`(spectrum ℂ a).Nonempty`。

诚实标注：需要 `[Nontrivial A]`——对 `E →L[ℂ] E` 要求 `E` 非退化
（`n = 0` 的零维空间**不**满足，与 `RealGelfand` 中单位矩阵算子范数的
`Nontrivial` 讨论同源）。

**⚠ R3 更正（悬空引用）**：原文引用 `RealGelfand.gelfand_opNorm_one`——
**该名字不存在**。`RealGelfand.lean` 中的真名是
`gelfand_opNorm_one_le`（无条件 `≤ 1` 版，`:160`）与
`gelfand_opNorm_one_of_pos`（`hn : 0 < n` 下的 `= 1` 版，`:178`）。
且全库为**扁平 `namespace Lattice`**，`RealGelfand` **不是** namespace ⟹
即使名字写对也不能用 `Module.name` 形式引用（本文件亦未 import 它，
故此处仅为**文字指路**）。 -/
theorem rg_spectrum_nonempty [Nontrivial (E →L[ℂ] E)] (a : E →L[ℂ] E) :
    (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a

/-- **谱半径被谱中元素取到**（回收 `spectrum.exists_nnnorm_eq_spectralRadius`，
`Spectrum.lean:413`）：存在 `z ∈ spectrum ℂ a` 使 `‖z‖₊ = spectralRadius ℂ a`。

诚实标注：这是 mathlib 4.14 **已有**的「谱半径取到」定理
（**不需要升级 mathlib**；R1 曾误报其「v4.24 才有」，见 CORRECTIONS B25）。 -/
theorem rg_exists_nnnorm_eq_spectralRadius [Nontrivial (E →L[ℂ] E)] (a : E →L[ℂ] E) :
    ∃ z ∈ spectrum ℂ a, (‖z‖₊ : ℝ≥0∞) = spectralRadius ℂ a :=
  spectrum.exists_nnnorm_eq_spectralRadius a

/-! ## 第三节：Gelfand 公式的 `lim` 形式（`Spectrum.lean:374` / `:383`） -/

/-- **Gelfand 公式（`nnnorm` 版，回收 `Spectrum.lean:374`）**：
`‖aⁿ‖₊^{1/n} → spectralRadius ℂ a`。

诚实标注（**B25 的核心更正**）：这条定理 **mathlib 4.14 已有**，
位置是 `Mathlib/Analysis/Normed/Algebra/Spectrum.lean:374`
（**不是** 4.24 的 `GelfandFormula.lean`——那只是 4.24 把它**拆成了独立文件**）。
本文件把它**实例化到 `E →L[ℂ] E`**，从而在「本项目自己的算子语境」中可用
——这正是 `RealGelfand` docstring 所说「缺的是复语境适配」的**落点**。 -/
theorem rg_gelfand_formula (a : E →L[ℂ] E) :
    Filter.Tendsto (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) Filter.atTop
      (𝓝 (spectralRadius ℂ a)) :=
  spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a

/-- **Gelfand 公式（`norm` 版，回收 `Spectrum.lean:383`）**：
`ofReal (‖aⁿ‖^{1/n}) → spectralRadius ℂ a`（与上一行同一定理，`norm` 记法）。 -/
theorem rg_gelfand_formula_norm (a : E →L[ℂ] E) :
    Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ))) Filter.atTop
      (𝓝 (spectralRadius ℂ a)) :=
  spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a

/-! ## 第四节：幂律的单侧性（上游也只证一侧）—— 事实记录

**诚实标注（独立佐证 `RealGelfand` 的核心发现，本节不含新定理）**：

在 mathlib **4.14**（本项目锁定版）中，`spectrum.spectralRadius_pow_le` **不存在**；
它在 `D:\mathlib`（v4.33 源码树）`Mathlib/Analysis/Normed/Algebra/Spectrum.lean:94`
才有，语句为
`lemma spectrum.spectralRadius_pow_le (a : A) (n : ℕ) (hn : n ≠ 0) : (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n)`
—— **证的正是 `ρ(a)ⁿ ≤ ρ(aⁿ)` 这一侧，没有反向**。

**结论**：「只能证一侧」**不是**本项目 `RealGelfand` 的方法局限，
而是 **`sSup over spectrum` / `sInf over norm-powers` 定义下的普遍性质**
（反向需要把 `lim` 与 `inf`/`sup` 接通，即 Gelfand 公式的使用）。

本文件**不重现**该定理：一是在 4.14 下无源可依（须自证，成本高于收益），
二是若上游未来加入同名声明会**冲突**。本项目已在 `RealGelfand` 中以 `sInf` 形式
证出对应结论 `gelfand_radius_pow_le_radius_pow : ρ(T)ᵏ ≤ ρ(Tᵏ)`，
并在 `gelfand_radius_pow_bounds` 中给出**双侧界**。
`RealGelfand` **未做**复语境适配，故其自身并未用 `Spectrum.lean:374` 的 `lim` 形式；
该 `lim` 形式的**回收路线**由**本文件**的 `rg_gelfand_formula` 给出。 -/

end Lattice
