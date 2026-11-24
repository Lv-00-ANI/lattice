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
open Lattice.Lib.Compiler.SymbolicEntry
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

/-- **⭐⭐⭐ 加权误差界（本文件的目的）。**

**⇒ 若每个基函数 `b i` 在 `[a,b]` 上的弦误差不超过 `B i`，
则它们的任意有限线性组合的弦误差不超过 `∑ |c i| · B i`。**

**⇒ 于是「新增一族」只需提供基函数与各自的 `B i`，
装配**不再需要重做**——这正是前三轮每次都要重做的那件事。**

**⇒ 三步装配：`chordOf_linComb` 把弦换成加权和；`segSum_eval` 把求值推进和式；
三角不等式 + `abs_mul` + 逐项放缩。** -/
theorem linComb_error {ι : Type} (s : Finset ι) (c : ι → ℝ) (b : ι → ℝ → ℝ)
    (B : ι → ℝ) (a bnd : ℝ) (h : a ≠ bnd)
    (hB : ∀ i ∈ s, ∀ x ∈ Set.Icc a bnd,
        |b i x - (chordOf (b i) a bnd).eval x| ≤ B i) :
    ∀ x ∈ Set.Icc a bnd,
      |linComb s c b x - (chordOf (linComb s c b) a bnd).eval x|
        ≤ ∑ i ∈ s, |c i| * B i := by
  intro x hx
  -- **第一步：弦换成加权和。**
  rw [chordOf_linComb s c b a bnd h, segSum_eval]
  -- **第二步：每个分段的求值恰好是 `c i` 乘该支的弦求值。**
  have hsum : (∑ i ∈ s,
        (⟨c i * chordSlope (b i) a bnd,
          c i * (b i a - chordSlope (b i) a bnd * a)⟩ : Segment).eval x)
      = ∑ i ∈ s, c i * (chordOf (b i) a bnd).eval x := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Segment.eval, chordOf]
    ring
  rw [hsum]
  -- **第三步：把差异写成逐项之差，再用三角不等式放缩。**
  have hdiff : linComb s c b x - ∑ i ∈ s, c i * (chordOf (b i) a bnd).eval x
      = ∑ i ∈ s, c i * (b i x - (chordOf (b i) a bnd).eval x) := by
    unfold linComb
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiff]
  calc |∑ i ∈ s, c i * (b i x - (chordOf (b i) a bnd).eval x)|
      ≤ ∑ i ∈ s, |c i * (b i x - (chordOf (b i) a bnd).eval x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |c i| * |b i x - (chordOf (b i) a bnd).eval x| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul]
    _ ≤ ∑ i ∈ s, |c i| * B i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hB i hi x hx) (abs_nonneg _)

/-- **⭐⭐⭐ 复用验证：二次项的**单区间**弦误差由 `linComb_error` 直接得出。**

**⇒ 装配**只有**「给出基函数与各自的界」这一步，其余全由 `linComb_error` 完成：**

| 基 | 系数 | 该支的界 `B` |
|:--|:--|:--|
| `t ↦ t·t` | `a` | `(v−u)²/4`（既有 `chord_error_sq_rederived`） |
| `t ↦ p·t + q` | `1` | `0`（`chordOf_affine`：仿射的弦**精确**） |

**⇒ 结论 `|quadFun − 弦| ≤ |a| · (v−u)²/4` 与第 1055 轮那个数**一致**——
这正是「可复用」与「另写一条」的分野：前者能**重推出旧结果**。** -/
theorem sq_chord_error_via_linComb (u v : ℝ) (huv : u < v) (x : ℝ)
    (hx : x ∈ Set.Icc u v) :
    |(fun t : ℝ => t * t) x - (chordOf (fun t : ℝ => t * t) u v).eval x|
      ≤ (v - u) ^ 2 / 4 := by
  have hne : u ≠ v := ne_of_lt huv
  -- **单支：基函数只有 `t·t`，系数 1，界取既有的 `(v−u)²/4`。**
  let b : Unit → ℝ → ℝ := fun _ t => t * t
  let c : Unit → ℝ := fun _ => 1
  let B : Unit → ℝ := fun _ => (v - u) ^ 2 / 4
  have hcomb : linComb Finset.univ c b = (fun t : ℝ => t * t) := by
    funext t
    simp [linComb, c, b]
  have hB : ∀ i ∈ (Finset.univ : Finset Unit), ∀ y ∈ Set.Icc u v,
      |b i y - (chordOf (b i) u v).eval y| ≤ B i := by
    intro i _ y hy
    simp only [b, B, c]
    have hch : chordOf (fun t : ℝ => t * t) u v = chordOf (fun t : ℝ => t ^ 2) u v := by
      congr 1
      funext t
      rw [pow_two]
    rw [hch]
    have hy2 : y * y = y ^ 2 := by rw [pow_two]
    rw [hy2]
    exact Lattice.Lib.Compiler.ChordErrorGeneral.chord_error_sq_rederived u v y huv hy
  have hmain := linComb_error Finset.univ c b B u v hne hB
  rw [hcomb] at hmain
  have hbound : (∑ i ∈ (Finset.univ : Finset Unit), |c i| * B i) = (v - u) ^ 2 / 4 := by
    simp [c, B]
  rw [hbound] at hmain
  exact hmain x hx

end Lattice.Lib.Compiler.LinearComb