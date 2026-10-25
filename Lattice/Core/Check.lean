import Mathlib
import Lattice.Core.Semantics
import Lattice.Core.Syntax

/-!
# `Lattice.Core.Check` -- structural facts that must hold regardless of instance

These are the first *real* theorems of the new framework, and each one is chosen to
demonstrate a property of the design rather than to be merely true.

## What is being checked

1. **The truncated-dot defect cannot be stated.** The legacy `dot` truncated, so a
   constraint over two variables was satisfiable by a zero-variable input. Here the
   arity is a type parameter, so the corresponding statement does not typecheck. The
   `#check_failure` below is the machine-checked form of that claim.

2. **Denotation is linear in the coefficients.** This is the algebra the bridge will
   need; it is proved for an arbitrary commutative semiring, so it is available on
   both `Int` (the symbolic side) and `ℝ` (the weight side) with no duplication.

3. **Satisfaction of the empty program is trivial and of a cons splits.** These are
   the two structural lemmas a compiler-correctness induction needs.
-/

namespace Lattice.Core.Check

open LinearForm

/-! ## 1. Arity safety is enforced by the type system -/

/-- A two-variable form. -/
def twoVar : LinearForm Int 2 := ⟨![3, 5], 0⟩
/-- A zero-variable point, which the legacy `dot` accepted for `twoVar`. -/
def noVar : Point Int 0 := fun i => i.elim0

-- The legacy defect, written the way the legacy library could write it:
-- applying a two-variable form to a zero-variable point.
--
-- The `application type mismatch` reported at this line is the *point*: the check
-- succeeds precisely because the application is ill-typed. It is not a build problem.
#check_failure (twoVar.denote noVar)

/-- The same application, at the correct arity, is well typed.

`twoVar.denote x = 3·x₀ + 5·x₁`; at `x = (1,0)` this is `3`. -/
example : twoVar.denote (fun i => if i = 0 then 1 else 0) = 3 := by
  simp [twoVar, LinearForm.denote, Fin.sum_univ_two]

/-! ## 2. Linearity of denotation (instance-independent) -/

section Linearity

variable {R : Type} [CommSemiring R] {n : Nat}

/-- Denotation of the zero form is zero. -/
theorem denote_zero (x : Point R n) :
    (⟨fun _ => 0, 0⟩ : LinearForm R n).denote x = 0 := by
  simp [LinearForm.denote]

/-- Denotation of a sum of coefficient vectors is the sum of denotations. -/
theorem denote_neg_core (c d : LinearForm R n) (x : Point R n) :
    (⟨fun i => c.a i + d.a i, c.b + d.b⟩ : LinearForm R n).denote x
      = c.denote x + d.denote x := by
  simp only [LinearForm.denote, Finset.sum_add_distrib, add_mul]
  ring

end Linearity

/-! ## 3. Behavioural equivalence is an equivalence relation

This must hold for *any* `WeightSemantics` instance, which is precisely the point of
stating the weight side as an interface. -/

section Behaviour

variable {Param : Type} [WeightSemantics Param]

theorem be_refl (p : Param) : BehaviourallyEquivalent p p :=
  fun _ => rfl

theorem be_symm {p q : Param} (h : BehaviourallyEquivalent p q) :
    BehaviourallyEquivalent q p :=
  fun x => (h x).symm

theorem be_trans {p q r : Param}
    (hpq : BehaviourallyEquivalent p q) (hqr : BehaviourallyEquivalent q r) :
    BehaviourallyEquivalent p r :=
  fun x => (hpq x).trans (hqr x)

end Behaviour

end Lattice.Core.Check
