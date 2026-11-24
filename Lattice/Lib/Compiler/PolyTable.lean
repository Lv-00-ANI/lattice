import Lattice.Lib.Compiler.CapabilityTable

/-!
# **按度数索引的能力表：从「查表」到「编排」**

## 这一层补什么

**`CapabilityTable.select` 只在一个**固定列表**里查找。规划 §2.1 第 4 层要的是「能力与**证明编排**」，
而编排的前提是：能力**可以按某个参数索引**，从而「先试小的、再试大的」。

**⇒ 本文件引入 `polyRow : ℕ → Option CapabilityRow`：给定**多项式度数**，返回覆盖该度数的行（若库里有）。**

**⇒ 于是「选择」变成**沿度数递增的阶梯**：`d = 1, 2, 3` 依次尝试。
而这正是「低度优先」的机制——**低度行（尤其精确的仿射行）更便宜**，故先试它。**

## 为什么返回值是 `Option` 而不是 `CapabilityRow`

**因为库**并不覆盖所有度数**。`polyRow 0 = none`（常函数不是本文件的关注对象）、
`polyRow 4 = none`（四次族尚未建立）。**⇒ 用 `Option` 就把「未覆盖」写成**类型的一部分**，
而不是靠调用者去猜。**

**⇒ 而「未覆盖」在本文件里也是**被证明**的（`polyRow_four`），不是文档里的一句话。**
-/

namespace Lattice.Lib.Compiler.PolyTable

open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.CapabilityTable

/-- **按度数索引的行**：库覆盖 `1`、`2`、`3` 三档；其余为 `none`。 -/
noncomputable def polyRow : ℕ → Option CapabilityRow
  | 1 => some affineFamilyRow
  | 2 => some squareRow
  | 3 => some cubeRow
  | _ => none

/-- **⭐ 度数 1 对应无参的仿射**族行**（常数 0）。** -/
theorem polyRow_one : polyRow 1 = some affineFamilyRow := rfl

/-- **⭐ 度数 2 对应二次行（常数 `1/4`）。** -/
theorem polyRow_two : polyRow 2 = some squareRow := rfl

/-- **⭐ 度数 3 对应三次行（常数 `3/4`）。** -/
theorem polyRow_three : polyRow 3 = some cubeRow := rfl

/-- **⭐ 度数 0 未覆盖。** -/
theorem polyRow_zero : polyRow 0 = none := rfl

/-- **⭐⭐ 度数 4 未覆盖**——四次族尚未建立。

**⇒ 这条是**如实**的边界：不是「四次不可能」，而是「本库还没有它的界」。
⇒ 若将来证出四次族的界，只需在此函数上加一支，而**其余各层不动**。** -/
theorem polyRow_four : polyRow 4 = none := rfl

/-- **⭐⭐ 未覆盖的度数**恰好是 `0` 与 `≥ 4`。** -/
theorem polyRow_none_iff (d : ℕ) : polyRow d = none ↔ d = 0 ∨ 4 ≤ d := by
  constructor
  · intro h
    match d with
    | 0 => exact Or.inl rfl
    | 1 => rw [polyRow_one] at h; exact absurd h (by simp)
    | 2 => rw [polyRow_two] at h; exact absurd h (by simp)
    | 3 => rw [polyRow_three] at h; exact absurd h (by simp)
    | Nat.succ (Nat.succ (Nat.succ (Nat.succ _))) => exact Or.inr (by omega)
  · rintro (rfl | h)
    · rfl
    · match d with
      | 0 => omega
      | 1 => omega
      | 2 => omega
      | 3 => omega
      | Nat.succ (Nat.succ (Nat.succ (Nat.succ _))) => simp [polyRow]

/-- **⭐⭐ 按度数递增尝试**：`1, 2, 3` 依次，取第一个适用的。 -/
noncomputable def selectByDegree (req : Request) : Option CapabilityRow :=
  select req [affineFamilyRow, squareRow, cubeRow]

/-! ## 一、两个新的否证事实：度数之间的区别

**阶梯要成立，必须证明「上一档不适用」。⇒ 下面两条都是**三点定值**的变体。** -/

/-- **⭐⭐ `t ↦ t³` 不属仿射族。** -/
theorem cube_not_affine :
    ¬ ∃ c d : ℝ, (fun t : ℝ => t ^ 3) = fun t : ℝ => c * t + d := by
  rintro ⟨c, d, h⟩
  have h0 : c * 0 + d = (0 : ℝ) ^ 3 := by simpa using (congrFun h 0).symm
  have h1 : c * 1 + d = (1 : ℝ) ^ 3 := by simpa using (congrFun h 1).symm
  have h2 : c * 2 + d = (2 : ℝ) ^ 3 := by simpa using (congrFun h 2).symm
  norm_num at h0 h1 h2
  linarith

/-- **⭐⭐ `t ↦ t²` 与 `t ↦ t³` 不是同一个函数**（在 `t = 2` 处取值不同）。** -/
theorem square_ne_cube : (fun t : ℝ => t ^ 2) ≠ (fun t : ℝ => t ^ 3) := by
  intro h
  have h2 : (2 : ℝ) ^ 2 = (2 : ℝ) ^ 3 := by simpa using congrFun h 2
  norm_num at h2

/-! ## 二、阶梯的两个落点 -/

/-- **⭐⭐ 二次目标在三次行被排除后**落到度数 2**。** -/
theorem square_not_cube_row (req : Request) (hgoal : req.goal = fun t : ℝ => t ^ 2) :
    ¬ sufficient cubeRow req := by
  intro h
  obtain ⟨hcov, _⟩ := h
  have hcov' : req.goal = fun t : ℝ => t ^ 3 := hcov
  have : (fun t : ℝ => t ^ 2) = fun t : ℝ => t ^ 3 := by
    rw [← hgoal]
    exact hcov'
  exact square_ne_cube this

/-- **⭐⭐ 度数 3 的目标准时落到三次行**（仿射与二次两档都被排除）。** -/
theorem cube_not_square_row (req : Request) (hgoal : req.goal = fun t : ℝ => t ^ 3) :
    ¬ sufficient squareRow req := by
  intro h
  obtain ⟨hcov, _⟩ := h
  have hcov' : req.goal = fun t : ℝ => t ^ 2 := hcov
  have : (fun t : ℝ => t ^ 3) = fun t : ℝ => t ^ 2 := by
    rw [← hgoal]
    exact hcov'
  exact square_ne_cube this.symm

/-- **⭐⭐ 度数 3 不属仿射族**（于是 `affineFamilyRow` 也被跳过）。** -/
theorem affineFamily_not_sufficient_for_cube (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 3) :
    ¬ sufficient affineFamilyRow req := by
  intro h
  obtain ⟨hcov, _⟩ := h
  obtain ⟨c, d, hcd⟩ := hcov
  have hcube : (fun t : ℝ => t ^ 3) = fun t : ℝ => c * t + d := by
    rw [← hgoal]
    exact hcd
  exact cube_not_affine ⟨c, d, hcube⟩

end Lattice.Lib.Compiler.PolyTable