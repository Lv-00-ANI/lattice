import Mathlib


/-!
# LATTICE: N 约束组合律架桥（批量验证判定）

把 ConvertLinear.lean 的 even_combo_preserves（2 个约束）推广到任意有限 N 个：
  (∀ x ∈ xs, EvenSat x)  ⟺  sumEven xs = 0

含义：验证器不需要逐条验证每个约束，只需检查"所有输出的和为零"——
这是 VerifyLoopProgress（批量验证判定）的最小模型。
表示层只用 Nat/List 核心类型；本文件 import Mathlib 以取用 omega/norm_num 等 tactic。
-/

namespace Lattice

/-! ## 单个约束与输出 -/

def EvenSat (x : Nat) : Prop := x % 2 = 0
def EvenOut (x : Nat) : Nat := x % 2

/-! ## N 个输出的和（foldr，便于归纳） -/

def sumEven (xs : List Nat) : Nat :=
  (xs.map EvenOut).foldr (fun a b => a + b) 0

/-! ## 引理：和为 0 ⟺ 每项为 0
Nat 上各项非负，和为零 ⟹ 每项为零（omega）。-/

lemma sumEven_eq_zero_iff (xs : List Nat) :
    sumEven xs = 0 ↔ ∀ x ∈ xs, EvenSat x := by
  unfold sumEven EvenSat
  induction xs with
  | nil =>
      simp
  | cons h t ih =>
      constructor
      · intro hsum x hx
        simp at hx
        rcases hx with rfl | ht
        · -- x = h：和为零 ⟹ 首项为零
          exact (Nat.add_eq_zero.mp hsum).1
        · -- x ∈ t：和为零 ⟹ 余项和为零
          have hrest : (t.map EvenOut).foldr (fun a b => a + b) 0 = 0 :=
            (Nat.add_eq_zero.mp hsum).2
          exact (ih.mp hrest) x ht
      · intro hall
        have hh : h % 2 = 0 := hall h (by simp)
        have ht : ∀ x ∈ t, x % 2 = 0 := fun x hx => hall x (by simp [hx])
        have hrest : (t.map EvenOut).foldr (fun a b => a + b) 0 = 0 := ih.mpr ht
        simp [EvenOut, hh, hrest]

/-! ## 定理：N 约束组合保语义
全部满足 ⟺ 输出和为零（批量验证判定）。-/

theorem comboN_preserves (xs : List Nat) :
    (∀ x ∈ xs, EvenSat x) ↔ sumEven xs = 0 := by
  exact (sumEven_eq_zero_iff xs).symm

/-! ## 推论：批量验证器
给定输出和为零，即可判定全部约束满足（避免逐条验证）。-/

theorem comboN_verify (xs : List Nat) (h : sumEven xs = 0) : ∀ x ∈ xs, EvenSat x :=
  (comboN_preserves xs).mpr h

/-! ## 空列表与单元素边界 -/

theorem comboN_empty : sumEven [] = 0 := by
  simp [sumEven]

theorem comboN_single (x : Nat) : EvenSat x ↔ sumEven [x] = 0 := by
  simp [sumEven, EvenSat, EvenOut]

end Lattice
