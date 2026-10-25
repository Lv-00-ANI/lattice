import Mathlib
import Lattice.Lib.Optim.RealProximal
/-!
# LATTICE: 一般近端算子的存在性与唯一性（一维）

`RealProximal` 以变分/极小刻画 `IsProx` 定义近端算子，并证明了非扩张与唯一性，
但**一般存在性未证**（当时只有线性目标的显式范例）。本文件补齐一维的存在性：

    `f : ℝ → ℝ` 凸、连续、**强制**（coercive）⟹ `∃! p, IsProx f η x p`（`η > 0`）。

定理清单：
  1. `prox_exists_unique`（**主定理**）：`ConvexOn ℝ univ f`、`Continuous f`、
     `∀ x, ∃ R, ∀ y, ‖y‖ ≥ R → f y > f x`、`η > 0` ⟹ `∃! p, IsProx f η x p`；
  2. `prox_exists`：存在性的投影形式（`∃ p, IsProx f η x p`）。

证明路线（一维，紧性 + 强制性）：
- `F y := f y + (1/(2η))‖y − x‖²`；由 `hcoer x` 取 `R`，令 `M := max R (‖x‖+1)`；
- `F` 在紧区间 `[−M, M]` 上连续，由 `IsCompact.exists_isMinOn` 取到极小点 `p`；
- 区间外 `‖y‖ > M ≥ R`，故 `f y > f x = F x ≥ F p`，且 `F y ≥ f y`；
  于是 `p` 是 `F` 的**全局**极小点，即 `IsProx f η x p`；
- 唯一性：`RealProximal.prox_unique`（凸性 ⟹ prox 唯一）。

**诚实边界（重要）**：
- 本文件只做**一维** `ℝ`。高维（`E` 为一般 Hilbert/Banach 空间）的 prox 存在性需要
  「下半连续 + 强制性 + 自反空间的弱紧性 / 或 `E` 有限维的紧性」——这些在 mathlib 中
  可用（`LowerSemicontinuous`、`IsCompact.exists_isMinOn` 的推广），但**本文件未做**，
  标注为后续工作；
- `Continuous f` 作为**显式假设**引入。一维有限凸函数自动连续
  （`ConvexOn` + `Set.univ` 上的实值凸函数连续），但为减少对 mathlib 特定引理名的依赖，
  本文件把它作为假设而不是推导；**这不引入 gap**（假设更强，定理仍为真），
  但存在性定理对「凸 ⟹ 自动连续」的衔接标注为**未做**；
- 同样地，凸性只通过 `RealProximal.prox_unique` 用于唯一性，存在性部分本身只用到
  强制性与连续性；
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set

namespace Lattice

/-- **一般 prox 的存在性与唯一性（一维）**：`f` 凸、连续、强制、`η > 0` ⟹
存在唯一的 `p` 使 `p` 极小化 `y ↦ f y + (1/(2η))‖y − x‖²`（即 `IsProx f η x p`）。 -/
theorem prox_exists_unique {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hcont : Continuous f)
    (hcoer : ∀ x, ∃ R, ∀ y, ‖y‖ ≥ R → f y > f x)
    {eta x : ℝ} (heta : 0 < eta) : ∃! p : ℝ, IsProx f eta x p := by
  obtain ⟨R, hR⟩ := hcoer x
  set M : ℝ := max R (‖x‖ + 1) with hM
  have hMR : R ≤ M := le_max_left _ _
  have hMx1 : ‖x‖ + 1 ≤ M := le_max_right _ _
  have hxM : x ∈ Set.Icc (-M) M := by
    rw [Set.mem_Icc]
    have hMx : ‖x‖ + 1 ≤ M := le_max_right _ _
    have hx_le : x ≤ ‖x‖ := le_abs_self x
    have hx_ge : -‖x‖ ≤ x := neg_abs_le x
    constructor <;> linarith
  let F : ℝ → ℝ := fun y => f y + (1 / (2 * eta)) * ‖y - x‖ ^ 2
  have hFcont : Continuous F := by
    have h1 : Continuous fun y : ℝ => ‖y - x‖ :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    have h2 : Continuous fun y : ℝ => ‖y - x‖ ^ 2 := h1.pow 2
    have h3 : Continuous fun y : ℝ => (1 / (2 * eta)) * ‖y - x‖ ^ 2 :=
      continuous_const.mul h2
    exact hcont.add h3
  obtain ⟨p, _hp_mem, hp_min⟩ :=
    isCompact_Icc.exists_isMinOn ⟨x, hxM⟩ hFcont.continuousOn
  have hp_min' : ∀ y ∈ Set.Icc (-M) M, F p ≤ F y := isMinOn_iff.mp hp_min
  have hFx : F x = f x := by
    simp [F]
  have hglob : ∀ y : ℝ, F p ≤ F y := by
    intro y
    by_cases hy : y ∈ Set.Icc (-M) M
    · exact hp_min' y hy
    · rw [Set.mem_Icc, not_and_or] at hy
      have hyR : R ≤ ‖y‖ := by
        rcases hy with h1 | h2
        · push_neg at h1
          have hyneg : y < 0 := by linarith [hMx1, norm_nonneg x]
          rw [Real.norm_eq_abs, abs_of_neg hyneg]
          linarith
        · push_neg at h2
          have hypos : 0 < y := by linarith [hMx1, norm_nonneg x]
          rw [Real.norm_eq_abs, abs_of_pos hypos]
          linarith
      have hfy : f x < f y := hR y hyR
      have hFy : f y ≤ F y := by
        have hnn : 0 ≤ (1 / (2 * eta)) * ‖y - x‖ ^ 2 := by positivity
        simp only [F]
        linarith
      have hpx : F p ≤ F x := hp_min' x hxM
      linarith
  have hp : IsProx f eta x p := fun y => by
    have h := hglob y
    simpa only [F] using h
  exact ⟨p, hp, fun q hq => prox_unique hconv heta hq hp⟩

/-- **存在性（投影形式）**：`prox_exists_unique` 的存在部分。 -/
theorem prox_exists {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f) (hcont : Continuous f)
    (hcoer : ∀ x, ∃ R, ∀ y, ‖y‖ ≥ R → f y > f x) {eta x : ℝ} (heta : 0 < eta) :
    ∃ p : ℝ, IsProx f eta x p :=
  (prox_exists_unique hconv hcont hcoer heta).exists

/-! ## 注：闭环语义与诚实边界
  本文件把 `RealProximal` 的「变分刻画 + 非扩张 + 唯一性」补齐为**完整的存在唯一性**
  （一维，凸 + 连续 + 强制）。由此，`RealProxGrad` 中作为**假设**出现的 prox 选择
  函数在「一维凸、连续、强制」的目标族上有了存在性支撑。
  诚实降级清单：高维存在性未做；「凸 ⟹ 连续」的自动衔接未做（`Continuous f` 为显式假设）；
  下半连续/正常性/有效定义域的抽象框架未做。 -/

end Lattice
