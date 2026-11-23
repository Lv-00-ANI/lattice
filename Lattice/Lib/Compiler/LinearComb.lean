import Lattice.Lib.Compiler.InterpAlgebra

/-!
# **弦是**线性泛函**：有限线性组合的插值由各支的弦加权求和给出**

## 为什么这一轮不做第四个特例

第 1053、1054、1055 三轮分别证了 `x²`、`x·x + 仿射`、`a·x·x + 仿射` 的整域界。
**三条都是同一件事的实例，而每次都要重做装配。⇒ 本文件把那个共同结构提出来一次。**

**⇒ 若每个基函数 `b i` 的弦已知，则任意有限线性组合 `∑ c i · b i` 的弦由它们**加权求和**给出。
于是「新增一族」只需给出该族的基函数，不必再走一次装配。**

## 为什么系数要取绝对值（下一条定理会用到）

**误差是非负量、系数可负。`∑ c i · B i` 在某个 `c i < 0` 时会变成负的，那是假命题。
⇒ 绝对值的出现不是形式洁癖，而是「这条定理为真」的必要条件。**
-/

namespace Lattice.Lib.Compiler.LinearComb

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler

/-- **有限多个分段之和**（逐分量相加）。 -/
noncomputable def segSum {ι : Type} (s : Finset ι) (g : ι → Segment) : Segment :=
  ⟨∑ i ∈ s, (g i).m, ∑ i ∈ s, (g i).c⟩

/-- **⭐ 求和与求值交换**：`(∑ g i).eval x = ∑ (g i).eval x`。

**⇒ 因为 `Segment.eval = m·x + c` 对 `(m, c)` 是线性的。** -/
theorem segSum_eval {ι : Type} (s : Finset ι) (g : ι → Segment) (x : ℝ) :
    (segSum s g).eval x = ∑ i ∈ s, (g i).eval x := by
  unfold segSum Segment.eval
  rw [Finset.sum_mul, Finset.sum_add_distrib]

/-- **有限线性组合**：`x ↦ ∑ c i · b i x`。 -/
noncomputable def linComb {ι : Type} (s : Finset ι) (c : ι → ℝ) (b : ι → ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∑ i ∈ s, c i * b i x

/-- **⭐⭐ 弦的斜率对线性组合是**线性**的。**

**⇒ 两步：先把「两和之差」化成「逐项之差」（`Finset.sum_sub_distrib` 反向），
再对单个分母逐项分配（`Finset.sum_div` 反向），最后 `mul_div_assoc` 把系数并进去。** -/
theorem chordSlope_linComb {ι : Type} (s : Finset ι) (c : ι → ℝ) (b : ι → ℝ → ℝ)
    (a bnd : ℝ) (h : a ≠ bnd) :
    chordSlope (linComb s c b) a bnd = ∑ i ∈ s, c i * chordSlope (b i) a bnd := by
  have hne : bnd - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold chordSlope linComb
  rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_eq_mul_inv]
  ring

/-- **⭐⭐ 弦本身对线性组合是线性的（分段级）。**

**⇒ 陈述直接给出**两个分量**：斜率按系数加权求和，截距按 `b i a − 斜率·a` 加权求和。
**⇒ 这样陈述是为了让两个分量都能一句 `Finset.sum_congr` 解决，而不必在 `chordOf` 的字段投影上纠缠。** -/
theorem chordOf_linComb {ι : Type} (s : Finset ι) (c : ι → ℝ) (b : ι → ℝ → ℝ)
    (a bnd : ℝ) (h : a ≠ bnd) :
    chordOf (linComb s c b) a bnd
      = segSum s (fun i => (⟨c i * chordSlope (b i) a bnd,
                             c i * (b i a - chordSlope (b i) a bnd * a)⟩ : Segment)) := by
  have hslope := chordSlope_linComb s c b a bnd h
  have hslope := chordSlope_linComb s c b a bnd h
  have hm : (chordOf (linComb s c b) a bnd).m
      = ∑ i ∈ s, c i * chordSlope (b i) a bnd := hslope
  have hc : (chordOf (linComb s c b) a bnd).c
      = ∑ i ∈ s, c i * (b i a - chordSlope (b i) a bnd * a) := by
    -- **截距：把 `∑` 提出 `a`，再逐项合并。**
    show linComb s c b a - chordSlope (linComb s c b) a bnd * a = _
    rw [hslope]
    unfold linComb
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- **结构 eta：一个 `Segment` 就是它两个分量的对。**
  have heta : chordOf (linComb s c b) a bnd
      = (⟨(chordOf (linComb s c b) a bnd).m, (chordOf (linComb s c b) a bnd).c⟩ : Segment) := rfl
  rw [heta, hm, hc]
  simp [segSum]

end Lattice.Lib.Compiler.LinearComb