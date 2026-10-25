import Lattice.Core.Semantics

/-!
# `Lattice.Core.Logic` -- satisfaction, entailment, and the hole discipline

## Design rationale

Three notions live here, and they are separated on purpose:

* **Satisfaction** `Satisfies c x` -- a *specific* point meets a *specific* constraint.
* **Entailment** `Entails cs x` -- *every* constraint in a set is met. The legacy
  project's `AllSatisfied` corresponds to this.
* **Consequence** `Models H c` -- *every* point satisfying all of `H` also satisfies `c`.

## Why consequence is defined the way it is

The legacy `SymbolToWeightCorrectness` concluded `AllSatisfied cs x → AllZeroOutputs l x`
for a *particular* `x`. That is a pointwise statement and it is exactly what the
`List.map` bridging proof establishes. It is not a statement about programs.

`Models H c` is the program-level statement: quantified over all points. It is what a
"compiles to weights that preserve meaning" theorem has to say, and it is strictly
stronger than the pointwise form.

## The hole discipline (mechanism B)

A proposition that is load-bearing but not yet proved must appear as an explicit
hypothesis `(h : P)` at each use site. It must never be introduced into the
environment by `axiom`, `opaque`, or a `variable` that silently generalises.

Measured lesson from the legacy tree: it contains **zero** `axiom`, `opaque`,
`unsafe`, and `extern`, so it never violated this rule. It did, however, keep the
number of *unproved* claims in a 1.97 MB prose register. Keeping them in the
type of the theorem that needs them is the machine-checkable replacement.
-/

namespace Lattice.Core

open LinearForm

section Satisfaction

variable {R : Type} [CommSemiring R] [LinearOrder R] {n : Nat}

/-- A point satisfies an equality constraint when the linear form vanishes there. -/
def SatisfiesEq (c : LinearForm R n) (x : Point R n) : Prop :=
  c.denote x = 0

/-- A point satisfies a `≤` constraint when the linear form is non-positive there. -/
def SatisfiesLe (c : LinearForm R n) (x : Point R n) : Prop :=
  c.denote x ≤ 0

/-- A point satisfies a `<` constraint when the linear form is negative there. -/
def SatisfiesLt (c : LinearForm R n) (x : Point R n) : Prop :=
  c.denote x < 0

/-- Satisfaction for the unified constraint syntax. -/
def Satisfies (c : Constraint R n) (x : Point R n) : Prop :=
  match c.rel with
  | .eq => SatisfiesEq c.form x
  | .le => SatisfiesLe c.form x
  | .lt => SatisfiesLt c.form x

/-- A point satisfies a *set* of constraints when it satisfies every one of them.

This is the program-level notion the bridge theorems quantify over. -/
def Entails (cs : List (Constraint R n)) (x : Point R n) : Prop :=
  ∀ c ∈ cs, Satisfies c x

/-- `H` models `c`: every point meeting every constraint in `H` also meets `c`.

This is *deliberately* stronger than `Entails`, and it is the correct target for a
"the compiled artifact preserves the meaning of the program" claim. -/
def Models (H : List (Constraint R n)) (c : Constraint R n) : Prop :=
  ∀ x : Point R n, Entails H x → Satisfies c x

end Satisfaction

/-! ## Basic structural facts

These are proved, not assumed, and they are the algebra the bridge lemmas need. -/

section Structural

variable {R : Type} [CommSemiring R] [LinearOrder R] {n : Nat}

/-- Entailment of a cons is entailment of the head together with entailment of the tail. -/
theorem entails_cons {c : Constraint R n} {cs : List (Constraint R n)} {x : Point R n} :
    Entails (c :: cs) x ↔ Satisfies c x ∧ Entails cs x := by
  constructor
  · intro h
    exact ⟨h c (List.mem_cons_self _ _),
      fun d hd => h d (List.mem_cons_of_mem _ hd)⟩
  · rintro ⟨hc, hcs⟩ d hd
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact hc
    · exact hcs d hd'

/-- Entailment is monotone in the constraint set: a superset entails at least as much.

This is the statement that a *larger* symbolic program is *stronger*, which the
embedding direction of the bridge relies on. -/
theorem entails_mono {cs ds : List (Constraint R n)} {x : Point R n}
    (hsub : ∀ c ∈ cs, c ∈ ds) (h : Entails ds x) : Entails cs x :=
  fun c hc => h c (hsub c hc)

/-- A single constraint is entailed by any set containing it. -/
theorem models_of_mem {H : List (Constraint R n)} {c : Constraint R n}
    (hmem : c ∈ H) : Models H c :=
  fun _x hx => hx c hmem

/-- Models is monotone (contravariantly) in the hypothesis set.

`models_of_subset` reads: if `H ⊆ K` (every hypothesis of `H` is also one of `K`),
then anything modelled by `H` is modelled by `K`. A point satisfying the larger set
`K` certainly satisfies the smaller one `H`. -/
theorem models_of_subset {H K : List (Constraint R n)} {c : Constraint R n}
    (hsub : ∀ d ∈ H, d ∈ K) (h : Models H c) : Models K c :=
  fun x hx => h x (entails_mono (cs := H) (ds := K) hsub hx)

end Structural

end Lattice.Core
