import Mathlib
import Lattice.Core.Syntax

/-!
# `Lattice.Core.Semantics` -- denotation, and the semantic interface for weights

## Design rationale (mechanism C of the framework)

The project's central difficulty is a *bridge* between the symbolic representation
and the weight representation. A bridge can only be stated if **both ends are
interfaces**: if either end is a fixed concrete type, every theorem about the bridge
is really a theorem about that particular type, and swapping the type invalidates it.

The legacy tree had this problem in its sharpest form. Its entire notion of "weight"
was

```lean
structure LinearNeuron where
  w : Int
  b : Int
```

so `SymbolToWeightCorrectness` proved that copying `(a,b)` into `(w,b)` preserves
satisfaction -- true, but a statement about field renaming. There was no tensor, no
parameter space, no shape, and consequently no way to state a theorem that would
still be true of a real network.

This file fixes that by declaring `WeightSemantics` as a *class*. Any concrete
notion of weights -- the legacy `Int × Int`, a real-valued linear form, a shaped
tensor tree, an external framework -- becomes an instance, and theorems proved
against the class survive a change of instance untouched.

## Why `denote` takes a point of the arity the form demands

`LinearForm.denote` is defined for a `Point R n` and nothing else. Because `n` is a
type parameter, the truncated-dot defect cannot arise: there is no way to pass a
vector of the wrong length.
-/

namespace Lattice.Core

open LinearForm

/-- The value of a linear form at a point: `Σ_i aᵢ xᵢ + b`.

This is the *only* definition of "the value of a linear form" in the project. -/
noncomputable def LinearForm.denote {R : Type} [CommSemiring R] {n : Nat}
    (c : LinearForm R n) (x : Point R n) : R :=
  (Finset.univ.sum fun i : Fin n => c.a i * x i) + c.b

/-! ## The semantic interface for the weight side -/

/-- An abstract notion of *weights*.

Nothing below depends on what a parameter is. A legacy-compatible instance takes
`Param := LinearForm R n` with `act := denote`; a tensor-based instance takes `Param`
to be a shaped tree. Theorems written against `WeightSemantics` hold for both.

The inputs and outputs are *fields* of the class rather than type parameters so that
a single instance can freely choose strongly-typed spaces, which is what makes the
arity indexing survive at the interface boundary. -/
class WeightSemantics (Param : Type) where
  /-- The input space the weights act on. -/
  Input : Type
  /-- The output space. -/
  Output : Type
  /-- Forward application: what the parameterised object *does*. -/
  act : Param → Input → Output

/-- Two parameters are behaviourally equivalent when no input distinguishes them.

This is the relation in which "extraction equivalence" must be stated: the legacy
project already established (and machine-checked a counterexample for) the fact that
the *semantic* layer is not injective, so object-level identity is the wrong target. -/
def BehaviourallyEquivalent {Param : Type} [WeightSemantics Param]
    (p q : Param) : Prop :=
  ∀ x : WeightSemantics.Input (Param := Param),
    WeightSemantics.act p x = WeightSemantics.act q x

/-- A linear form, viewed as a weighted object: parameters are the coefficients,
inputs are points, and the action is denotation.

This is the instance that makes the legacy `Int × Int` fragment a *special case* of
the general framework rather than a separate formalisation. -/
@[reducible] noncomputable def LinearForm.instWeightSemantics {R : Type} [CommSemiring R]
    {n : Nat} : WeightSemantics (LinearForm R n) where
  Input := Point R n
  Output := R
  act := fun c x => c.denote x

end Lattice.Core
