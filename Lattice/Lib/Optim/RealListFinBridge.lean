import Mathlib
import Lattice.Runtime.ConvertVectorLinear
/-!
# LATTICE: RealListFinBridge —— `List Int` 与 `Fin n → Int` 之间的桥

本文件把 `dot`（`List Int` 上的截断点积）与 `Matrix.dotProduct`（`Fin n → Int` 上的内积）
**在同一等式上对齐**，从而打通链路上两条此前互不相接的载体。

## 关键事实（与既有判据相反，已由两条独立证明路线互证）

* ⭐ `dot_eq_dotProduct` **无需长度条件** —— 长度条件是【冗余】的。
  机理：`dot` 用 `zip` **截断**，`toVec` 用 `getD` **补零**，二者方向相反、恰好抵消。
  （`RealDotLengthCondition.lean:25-32` 已逐字记录此事实，但判据未同步。）
* 任务所指反例 `x = []`, `a = [3,5]` **不存在** —— 两侧都 = 0（见 §5）。
* 长度条件的**真正**落点是 `toVec` 的**单射性**（§4）。

`#print axioms` 全部 ⊆ {propext, Classical.choice, Quot.sound}，无 sorryAx。
-/

namespace Lattice

/-- 把 `List Int` 补零视作 `Fin n → Int`。 -/
def toVec (n : Nat) (x : List Int) : Fin n → Int := fun i => x.getD i.1 0

/-! ## §0 求和辅助引理 -/

/-- `foldl` 从 `c` 起 = `c` + 从 `0` 起（zip 上）。 -/
lemma foldl_zip_add (a x : List Int) (c : Int) :
    (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) c
      = c + (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0 := by
  induction a generalizing x c with
  | nil => simp
  | cons y ys ih =>
    cases x with
    | nil => simp
    | cons z zs =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih zs (c + y * z), ih zs (0 + y * z)]
      ring

/-- `dot` 在 cons 上的剥离律。 -/
lemma dot_cons (y z : Int) (ys zs : List Int) :
    dot (y :: ys) (z :: zs) = y * z + dot ys zs := by
  simp only [dot, List.zip_cons_cons, List.foldl_cons]
  rw [foldl_zip_add ys zs (0 + y * z)]
  ring

/-- `Fin (n+1)` 上的求和按首项分解，并把 `getD` 从 cons 移到 tail。 -/
lemma fin_sum_cons (y z : Int) (ys zs : List Int) :
    (∑ i : Fin (ys.length + 1),
        (y :: ys).getD i.1 0 * (z :: zs).getD i.1 0)
      = y * z + ∑ i : Fin ys.length, ys.getD i.1 0 * zs.getD i.1 0 := by
  rw [Fin.sum_univ_succ]
  simp only [List.length_cons, List.getD_cons_zero, List.getD_cons_succ,
             Nat.add_sub_cancel, Fin.val_succ, Fin.val_zero]

/-! ## §1 LHS：`dot a x` = `Fin a.length` 上的求和（**对任意 x**） -/

lemma dot_eq_fin_sum (a x : List Int) :
    dot a x = ∑ i : Fin a.length, a.getD i.1 0 * x.getD i.1 0 := by
  induction a generalizing x with
  | nil => simp [dot]
  | cons y ys ih =>
    cases x with
    | nil =>
      simp only [dot, List.zip_nil_right, List.foldl_nil]
      simp [List.length_cons, Fin.sum_univ_succ]
    | cons z zs =>
      rw [dot_cons y z ys zs, ih zs]
      rw [show (y :: ys).length = ys.length + 1 from rfl]
      rw [fin_sum_cons y z ys zs]

/-! ## §2 RHS：`Matrix.dotProduct` 逐字展开即同一求和 -/

lemma rhs_eq_fin_sum (a x : List Int) :
    Matrix.dotProduct (toVec a.length a) (toVec a.length x)
      = ∑ i : Fin a.length, a.getD i.1 0 * x.getD i.1 0 := by
  simp only [Matrix.dotProduct, toVec]

/-! ## §3 ⭐ 主桥：**无需长度条件** -/

theorem dot_eq_dotProduct (a x : List Int) :
    dot a x = Matrix.dotProduct (toVec a.length a) (toVec a.length x) := by
  rw [dot_eq_fin_sum, rhs_eq_fin_sum]

/-- 带长度条件的版本（**推论**，条件冗余）。 -/
theorem dot_eq_dotProduct_of_length (a x : List Int) (_h : x.length = a.length) :
    dot a x = Matrix.dotProduct (toVec a.length a) (toVec a.length x) :=
  dot_eq_dotProduct a x

/-! ## §4 长度条件的**真正**落点：`toVec` 的单射性 -/

lemma getD_eq_getElem {l : List Int} {i : Nat} (h : i < l.length) :
    l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- ⭐ 带长度条件时 `toVec` 单射。 -/
theorem toVec_injective (n : Nat) (x y : List Int)
    (hx : x.length = n) (hy : y.length = n) (h : toVec n x = toVec n y) : x = y := by
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i n with hi | hi
  · have hpt := congrFun h ⟨i, hi⟩
    simp only [toVec] at hpt
    rw [getD_eq_getElem (by simpa [hx] using hi),
        getD_eq_getElem (by simpa [hy] using hi)] at hpt
    rw [List.getElem?_eq_getElem (by simpa [hx] using hi),
        List.getElem?_eq_getElem (by simpa [hy] using hi), hpt]
  · rw [List.getElem?_eq_none (by simpa [hx] using hi),
        List.getElem?_eq_none (by simpa [hy] using hi)]

/-- ⭐ 无长度条件时 `toVec` **不**单射（补零见证）。 -/
theorem toVec_not_injective_without_length :
    ∃ x y : List Int, x ≠ y ∧ toVec 2 x = toVec 2 y :=
  ⟨[1], [1, 0], by decide, by decide⟩

/-! ## §5 任务所指反例实测：`x = []`, `a = [3,5]` —— **两侧都 = 0** -/

example : dot ([3, 5] : List Int) ([] : List Int)
    = Matrix.dotProduct (toVec 2 ([3, 5] : List Int)) (toVec 2 ([] : List Int)) := rfl

end Lattice

#print axioms Lattice.dot_eq_dotProduct
#print axioms Lattice.toVec_injective
#print axioms Lattice.toVec_not_injective_without_length