import Lattice.Lib.Compiler.ArtifactStitch
import Lattice.Lib.Compiler.SecondDerivBound

/-!
# **一般幂次 `x^d`：一条界覆盖所有度数，常数恰为 `d(d−1)/8`**

## 动机是一个**数值吻合**，不是猜想

**前三轮手工推出 `x²` 的 `1/4`、`x³` 的 `3/4`、`x⁴` 的 `3/2`（都以 `C/n²` 形式）。
⇒ `d(d−1)/8` 给出 `2/8 = 1/4`、`6/8 = 3/4`、`12/8 = 3/2`——**三条全部对上**。**

**⇒ 故它们不是三个独立结果，而是**同一个公式**的三个实例。而树里已有
`chord_error_of_second_deriv_bound`（`|f''| ≤ M ⟹ 弦误差 ≤ M(b−a)²/8`），
⇒ 一般幂次应当**由它实例化**。**

## 为什么这比继续手工分解更强

**手工分解要证 `x^d − chord = (x−a)(x−b)·Q_d`，`Q_d` 是双和；对任意 `d` 需要有限和与几何级数的机器。
⇒ 二阶导路线只需**一次求导**：`deriv²(t ↦ t^d) = d(d−1)·t^{d−2}`，再在 `(a,b) ⊂ [0,1]` 上压 `|t^{d−2}| ≤ 1`。

**⇒ 代价是它给出 `M(b−a)²/8` 形式，理论上可能比尖顶估计松；但在 `d = 2,3,4` 上**完全一致**，
⇒ 故这条一般界的常数**不是**松的。**
-/

namespace Lattice.Lib.Compiler.PowChord

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.GridBound
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler

/-- **⭐ `t^d` 的一阶导（函数级）：`d · t^{d−1}`。** -/
theorem deriv_pow_fun (d : ℕ) :
    deriv (fun t : ℝ => t ^ d) = fun t => (d : ℝ) * t ^ (d - 1) := by
  funext t
  exact deriv_pow d

/-- **⭐⭐ `t^d` 的二阶导（函数级）：`d(d−1) · t^{d−2}`。**

**⇒ 常数写成**自然数乘积再强转**（`↑(d*(d−1))`），使它与 `d(d−1)/8` 这个公式**字面一致**。** -/
theorem deriv_deriv_pow (d : ℕ) :
    deriv (fun t : ℝ => (d : ℝ) * t ^ (d - 1))
      = fun t => ((d * (d - 1) : ℕ) : ℝ) * t ^ (d - 2) := by
  funext t
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `d = 0`\uff1a`t^(-1)` \u7684\u62c9\u65af\u4e3a `0`\uff0c\u4e24\u8fb9\u90fd\u662f\u96f6\u3002
    simp
  have hd1 : 1 ≤ d := hd
  -- **\u70b9\u6001\uff1a\u5e38\u6570\u4e58\u4e0e `t^(d\u22121)` \u7684\u5bfc\u6570\u3002**
  rw [deriv_const_mul (d : ℝ) (differentiableAt_pow (d - 1))]
  rw [deriv_pow (d - 1)]
  -- **\u4e24\u4e2a\u81ea\u7136\u6570\u5dee\u90fd\u53ef\u7b97\uff1a`(d\u22121)\u22121 = d\u22122`\u3002**
  have h2 : d - 1 - 1 = d - 2 := by omega
  rw [h2]
  push_cast [hd1]
  ring

/-- **⭐⭐ `deriv^[2]` 形式**（树里那条定理用的就是它）。** -/
theorem deriv2_pow (d : ℕ) :
    deriv^[2] (fun t : ℝ => t ^ d) = fun t => ((d * (d - 1) : ℕ) : ℝ) * t ^ (d - 2) := by
  show deriv (deriv (fun t : ℝ => t ^ d)) = _
  rw [deriv_pow_fun]
  exact deriv_deriv_pow d

/-- **⭐⭐⭐ 一般幂次的**单区间**弦误差界：`≤ d(d−1)(b−a)²/8`。** -/
theorem pow_chord_error (d : ℕ) (hd : 2 ≤ d) (a b x : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hx : x ∈ Set.Icc a b) :
    |x ^ d - (chordOf (fun t : ℝ => t ^ d) a b).eval x|
      ≤ ((d * (d - 1) : ℕ) : ℝ) * (b - a) ^ 2 / 8 := by
  have hdiff : Differentiable ℝ (fun t : ℝ => t ^ d) := by fun_prop
  have hdiff' : DifferentiableOn ℝ (deriv (fun t : ℝ => t ^ d)) (interior (Set.Icc a b)) := by
    rw [deriv_pow_fun d]
    fun_prop
  have hM2 : ∀ t ∈ interior (Set.Icc a b),
      |deriv^[2] (fun t : ℝ => t ^ d) t| ≤ ((d * (d - 1) : ℕ) : ℝ) := by
    intro t ht
    have ht' : t ∈ Set.Ioo a b := by simpa [interior_Icc] using ht
    rw [deriv2_pow d]
    have ht0 : 0 ≤ t := by linarith [ht'.1, ha0]
    have ht1 : t ≤ 1 := by linarith [ht'.2, hb1]
    have hpow : |t ^ (d - 2)| = t ^ (d - 2) := abs_of_nonneg (pow_nonneg ht0 _)
    rw [abs_mul, hpow]
    have hle : t ^ (d - 2) ≤ 1 := pow_le_one₀ ht0 ht1
    have hnn : (0 : ℝ) ≤ ((d * (d - 1) : ℕ) : ℝ) := by positivity
    calc |((d * (d - 1) : ℕ) : ℝ)| * t ^ (d - 2)
        = ((d * (d - 1) : ℕ) : ℝ) * t ^ (d - 2) := by rw [abs_of_nonneg hnn]
      _ ≤ ((d * (d - 1) : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hle hnn
      _ = ((d * (d - 1) : ℕ) : ℝ) := by ring
  exact Lattice.Lib.Compiler.SecondDerivBound.chord_error_of_second_deriv_bound
    (fun t : ℝ => t ^ d) a b ((d * (d - 1) : ℕ) : ℝ) hab (by positivity) hdiff hdiff' hM2 x hx

/-- **⭐⭐⭐ 一般幂次的**整域界**：`≤ d(d−1)·(1/n)²/8`。

**⇒ 路径是一族一装的入口：`pow_chord_error`（单区间）+ `gridEval_bound_of_segmentwise`。**
**⇒ 段宽 `(k+1)/n − k/n = 1/n`，故界退化为 `d(d−1)·(1/n)²/8`。** -/
theorem pow_uniform_bound (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1,
      |x ^ d - gridEval (interpFamily n (fun t : ℝ => t ^ d)) n x|
        ≤ ((d * (d - 1) : ℕ) : ℝ) * (1 / (n : ℝ)) ^ 2 / 8 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  intro x hx
  apply gridEval_bound_of_segmentwise (fun k => interpFamily n (fun t : ℝ => t ^ d) k) n hn
    (fun t : ℝ => t ^ d) (((d * (d - 1) : ℕ) : ℝ) * (1 / (n : ℝ)) ^ 2 / 8)
  · intro k hk y hy
    have hseg : interpFamily n (fun t : ℝ => t ^ d) k
        = chordOf (fun t : ℝ => t ^ d) ((k : ℝ) / n) (((k : ℝ) + 1) / n) := rfl
    rw [hseg]
    have hlt : ((k : ℝ) / n) < (((k : ℝ) + 1) / n) := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by field_simp
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      linarith
    have hleft : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    have hright : (((k : ℝ) + 1) / n) ≤ 1 := by
      rw [div_le_one hn']
      exact_mod_cast Nat.succ_le_of_lt hk
    have hb := pow_chord_error d hd ((k : ℝ) / n) (((k : ℝ) + 1) / n) y
      hleft hlt hright hy
    have hwidth : ((((k : ℝ) + 1) / n) - ((k : ℝ) / n)) ^ 2 = (1 / (n : ℝ)) ^ 2 := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by field_simp
      rw [heq]
    rw [hwidth] at hb
    exact hb
  · exact hx

/-! ## 一、一般公式**重推出**三条手工结果 -/

/-- **⭐⭐ `d = 2` 时常数是 `1/4`**——与第 1056 轮手工推出的值**逐字相同**。 -/
theorem constant_two : (((2 * (2 - 1) : ℕ)) : ℝ) / 8 = 1 / 4 := by norm_num

/-- **⭐⭐ `d = 3` 时常数是 `3/4`**——与第 1060 轮的值一致。 -/
theorem constant_three : (((3 * (3 - 1) : ℕ)) : ℝ) / 8 = 3 / 4 := by norm_num

/-- **⭐⭐ `d = 4` 时常数是 `3/2`**——与第 1073 轮的值一致。 -/
theorem constant_four : (((4 * (4 - 1) : ℕ)) : ℝ) / 8 = 3 / 2 := by norm_num

/-- **⭐⭐⭐ 一般公式与三条手工结果一致**——这是本文件存在的理由。

**⇒ `d(d−1)/8` 在 `d = 2,3,4` 处分别给出 `1/4`、`3/4`、`3/2`，
而那三个数是前三轮**各自独立推导**出来的。**
**⇒ 故三条不是三个事实，而是**同一公式的三个实例**；而一般定理覆盖所有度数。** -/
theorem general_formula_matches_hand_derived :
    (((2 * (2 - 1) : ℕ)) : ℝ) / 8 = 1 / 4
      ∧ (((3 * (3 - 1) : ℕ)) : ℝ) / 8 = 3 / 4
      ∧ (((4 * (4 - 1) : ℕ)) : ℝ) / 8 = 3 / 2 :=
  ⟨constant_two, constant_three, constant_four⟩

end Lattice.Lib.Compiler.PowChord