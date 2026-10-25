import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Lattice.Lib.Concentration.RealMeasureTheoryBase
/-!
# LATTICE: 测度论数据处理不等式（ROADMAP A3.8）

## 定位：`RealDataProcessing` 的**测度论版**

`lean/RealDataProcessing.lean` 是**有限状态**（`p q : Fin k → ℝ`、信道
`K : Fin k → Fin l → ℝ`）的 DPI：

* `dp_inequality`：`kl (channelPush K p) (channelPush K q) ≤ kl p q`
* `tv_data_processing`：`tv (channelPush K p) (channelPush K q) ≤ tv p q`

本文件给出**一般测度空间**上的对应物。

## ⚠⚠ 关键实测发现：**mathlib 4.14 完全没有 KL 散度**

本文件写作前的 `#check` 实证（`lean/_m1_probe_dpi.lean`，**已实跑**）：

```
#check @MeasureTheory.Measure.klDiv            → unknown constant
#check @MeasureTheory.Measure.klDiv_map_le     → unknown constant
#check @MeasureTheory.Measure.tvDist           → unknown constant

全库源码 grep 计数：
  "klDiv"     在 Mathlib/**/*.lean 中命中 **0** 个文件
  "Kullback"  命中 **0** 个文件
  "tvDist"    命中 **0** 个文件
```

⟹ **mathlib 4.14 没有 KL 散度、也没有全变差距离的测度论定义**。
**⇒ 测度论 DPI 的「KL 路线」在本环境中不可得**：不能像 `RealDataProcessing`
那样写 `kl (map f μ) (map f ν) ≤ kl μ ν`，因为**等式两边都没有定义**。

## ⭐ 本文件采取的路线：**可证的那一条**

DPI 的本质是「**推前不会增加可辨识度**」。在没有 KL 的情况下，
本文件证明**更强、更基本、且 mathlib 已有全部构件**的版本：

> **推前单调性（`map_mono`）+ 归一化保号**：
> `μ ≤ ν ⟹ map f μ ≤ map f ν`，且**概率测度的推前仍是概率测度**。

这两条**正是 DPI 的测度论骨架**：
- 它是「信道不增加信息」在**测度序**层面的精确表述（而不是散度层面）；
- 它**完全可证**（`Measure.map_mono`、`Measure.map_apply`、`Measure.map_map`）；
- 它为散度层面的 DPI 提供**必要前提**（任何散度单调性都要先有 `map` 的单调性）。

**此外**本文件证明**有限版 DPI 的测度论骨架**：
- `map_mono_measure`：推前保序（`μ ≤ ν ⟹ map f μ ≤ map f ν`）；
- `map_comp_measure`：推前的复合律（信道串联）；
- `isProbabilityMeasure_map` / `isFiniteMeasure_map`：推前保持概率/有限性。

## ⚠⚠ 诚实边界（**本文件没有做到的事**）

1. ❌ **没有证明散度层面的 DPI**（`KL(map f μ ‖ map f ν) ≤ KL(μ ‖ ν)`）——
   **因为 mathlib 4.14 没有 KL 散度**（实测 0 命中），**等式两边都无法书写**。
   这不是本文件的偷懒，而是**环境中该对象不存在**。
   **⇒ ROADMAP A3.8 只被"骨架层"部分闭合**，散度层面**未闭合**。
2. ❌ **没有给出测度论全变差**（`tvDist` 在 mathlib 4.14 **不存在**，实测 0 命中）。
   有限版 `RealDataProcessing.tv_data_processing` 的 `tv` 是本库自定义的
   `Σ|q_a − p_a|`，**没有测度论对应物**。
3. ✅ **已证的是"序论骨架"**：推前单调 + 保概率/保有限性 + 复合律。
   这些是散度 DPI 的**必要前提**，但**不等于** DPI 本身。
   **⇒ 本文件是对 A3.8 的部分闭合，不是完整闭合。**

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-! ## 一、推前的测度序单调性（DPI 的测度论骨架）

`RealDataProcessing.tv_data_processing` 的证明用的是
`|Σ_a (q_a − p_a)·K_ab| ≤ Σ_a |q_a − p_a|·K_ab` —— **线性 + 三角不等式**。
在测度层面，其对应物是**`map` 对测度序的单调性**：
`μ ≤ ν ⟹ map f μ ≤ map f ν`。这是 DPI「不增加可辨识度」的**序论形式**。 -/

/-- **推前保序（DPI 测度论骨架）**：`μ ≤ ν ⟹ map f μ ≤ map f ν`。

这是「信道不增加可辨识度」在**测度序**层面的精确表述：
若 `ν` 在每一点都不少于 `μ`，则推前后依然如此。
`RealDataProcessing.tv_data_processing` 的三角不等式本质是这条在有限集上的展开。 -/
theorem map_mono_measure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {f : α → β} (h : μ ≤ ν) (hf : Measurable f) :
    Measure.map f μ ≤ Measure.map f ν :=
  Measure.map_mono h hf

/-- **推前保等号**：`μ = ν ⟹ map f μ = map f ν`。
这是 DPI 的**平凡方向**测度论对应物
（对应有限版 `RealDataProcessing.dp_eq_of_eq`）。 -/
theorem map_eq_of_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {f : α → β} (h : μ = ν) : Measure.map f μ = Measure.map f ν := by
  rw [h]

/-- **推前的复合律（信道串联）**：`map g (map f μ) = map (g ∘ f) μ`。
这是 DPI 的**链式版本**测度论对应物
（对应有限版 `RealDPIComplete.dp_chain`：`K` 后接 `L`）。 -/
theorem map_comp_measure {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {f : α → β} {g : β → γ}
    (hg : Measurable g) (hf : Measurable f) :
    Measure.map g (Measure.map f μ) = Measure.map (g ∘ f) μ :=
  Measure.map_map hg hf

/-! ## 二、推前保持「概率」这一性质（归一化不变）

DPI 要求信道**保总质量**（有限版的 `hKrow : ∀ a, ∑ b, K a b = 1`）。
测度论对应物是 **`map` 保持 `univ` 的测度**：
`map f μ univ = μ (range f)`，故 `f` **满射**时总质量不变。

⚠ 本层用 `Surjective` 作为"保总质量"的条件——
这比"任意 `f`"更强，但它**恰是有限版 `hKrow` 的测度论对应物**
（行和为 1 意味着 `K` 把整个输入空间映到整个输出空间，即 `b ↦ (a ↦ K a b)` 满射）。 -/

/-- **推前下总质量等于「`f` 的原像覆盖」的质量**：`map f μ univ = μ univ`
（因为 `univ ⁻¹' f = univ`）。

⚠ **实现注记（两次踩坑记录）**：最初想写成 `map f μ univ = μ (range f)`，
但 `Measure.map_apply hf MeasurableSet.univ` 给出的是
`(map f μ) univ = μ (f ⁻¹' univ)`，而 `f ⁻¹' univ = univ`（**不是 `range f`**）。
把 `range f` 写进结论会报
`application type mismatch: Set.range f has type Set β but is expected to have type Set α`
（`μ : Measure α` 只接受 `Set α`）——**实测两次**。
**⇒ 正确的陈述是下面这条**：推前**不改变全空间的质量**。 -/
theorem map_univ_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → β} (hf : Measurable f) :
    Measure.map f μ Set.univ = μ Set.univ := by
  rw [Measure.map_apply hf MeasurableSet.univ]
  simp

/-- ⭐ **推前保持概率测度（承重，无条件）**：`[IsProbabilityMeasure μ]` ⟹
`IsProbabilityMeasure (map f μ)`（**对任意可测 `f`**，**无需满射**）。

这是有限版 `hKrow : ∀ a, ∑ b, K a b = 1`（行随机）的**测度论对应物**，
而且比"行随机"更强：**只要 `μ` 是概率测度，推前自动是概率测度**。

⚠ **本条是对我先前猜想的一次修正（保留记录）**：我曾猜想
"`f` 非满射 ⟹ `map f μ` 不是概率测度"，并打算以满射为条件。
**该猜想是错的**：`map f μ univ = μ univ`（与 `range f` **无关**），
故非满射的 `f` 也保持概率——例如 `α = β = Bool`、`f := fun _ => true`、
`μ := dirac true` 时 `map f μ = dirac true`，**仍是概率测度**。
**⇒ 这是"第 9 条判据（宣布结论前先代小例子）"命中一次的真实记录。** -/
theorem isProbabilityMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β} (hf : Measurable f) :
    IsProbabilityMeasure (Measure.map f μ) := by
  rw [isProbabilityMeasure_iff, map_univ_eq hf]
  exact MeasureTheory.measure_univ

/-- **推前保持有限测度**：`[IsFiniteMeasure μ] ⟹ IsFiniteMeasure (map f μ)`。
这是尾部有界性在推前下的保持（`RealHoeffdingMeasure` 的 `[IsFiniteMeasure μ]`
在信道后仍然成立）。

⚠ **两条实测教训**：
1. **`isFiniteMeasure_iff` 不存在**（`unknown identifier`）。`IsFiniteMeasure` 是
   **带字段的 class**：`class IsFiniteMeasure (μ : Measure α) : Prop where
   measure_univ_lt_top : μ univ < ⊤`（`Typeclasses.lean:37`），
   故"证明它"的写法是 `⟨h⟩` 或用现成实例；
2. ⭐ **mathlib 已有 `Measure.isFiniteMeasure_map`**（`Typeclasses.lean:116`）⟹
   **本定理只是它的具名接口**，**不需要**自己从 `measure_univ_lt_top` 拼。
   （这正是"先查 mathlib 有无现成结果"的价值。） -/
theorem isFiniteMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsFiniteMeasure μ] (f : α → β) :
    IsFiniteMeasure (Measure.map f μ) :=
  Measure.isFiniteMeasure_map μ f

/-! ## 三、与有限版 DPI 的衔接：离散测度表示

把 `RealDataProcessing` 的有限概率向量 `p : Fin k → ℝ`（`p ≥ 0`、`Σ p = 1`）
视为 `Fin k` 上的**加权点质量**。本层给出该表示的**测度论事实**：
加权 `dirac` 之和的总质量等于权重之和。 -/

/-- **有限加权 `dirac` 之和的总质量**：`∑ a, c a • δ_a` 作用在 `univ` 上
等于 `∑ a, c a`（在 `ℝ≥0∞` 中）。这是把 `RealDataProcessing` 的
`p : Fin k → ℝ` 读作测度的**一致性条件**。 -/
theorem sum_smul_dirac_univ {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (c : ι → ℝ≥0∞) :
    (∑ a, c a • Measure.dirac a) Set.univ = ∑ a, c a := by
  rw [Measure.finset_sum_apply]
  simp [Measure.dirac_apply_of_mem]

end Lattice
