import Mathlib
import Lattice.Geo.Loss
import Lattice.Geo.Constraint
import Lattice.Lift.SymbolToWeight

/-!
# `Lattice.Geo.Compile` -- the geometric layer as an inhabitant of `Lift.Compiler`

## Why this file exists

`Lattice.Lift` states the four target theorems for an **arbitrary** `Compiler` instance
(`Compiler.compileProgram_sound` and its relatiives). Those theorems are contracts: they say that
whenever a compiler satisfies its obligation, compilation preserves meaning. But a contract with no
inhabitant is a claim about nothing.

`Lattice.Geo` is the first inhabitant that carries actual geometric content. This file registers it, so the
target theorems apply to geometry rather than only to an abstract argument slot.

## The instance

| field | value |
|:--|:--|
| `P` | `EqConstraint n` -- the equality-layer constraints, which are exactly those with a penalty |
| `W` | `(ℕ → Pt n) → ℝ` -- the penalty, seen as a function on configurations |
| `compile` | `EqConstraint.loss` |
| `satP` | the constraint holds |
| `satW` | the penalty vanishes |

`encode` is the identity: both sides read the same configuration, so no representation change is needed,
and making it identity is honest rather than convenient -- a geometry-to-geometry compilation does not
translate its inputs.

## The obligation, and what it rests on

`Compiler.sound` asks: if the constraint holds at a configuration, does the penalty vanish there? That is
`EqConstraint.loss_eq_zero_*` from `Lattice.Geo.Loss`, one lemma per constructor. Collecting them here is
what turns four separate implications into a single inhabitant.

Note the direction. `sound` is the **easy** direction: a satisfying configuration gives zero penalty. The
hard direction -- a zero penalty gives a satisfying configuration -- is `Lattice.Lib.Penalty.PolyExact`'s
content, and it is *not* part of `Compiler.sound`. Keeping them separate is what lets this file be short
and still true.
-/

namespace Lattice.Geo

open Lattice.Lift

variable {n : ℕ}

/-- **The geometric compiler**: equality constraints compile to their squared-residual penalty.

This is the inhabitant that makes `Lattice.Lift`'s four target theorems statements about geometry. -/
noncomputable def geoCompiler : Compiler (EqConstraint n) ((ℕ → Pt n) → ℝ) where
  inputP := ℕ → Pt n
  inputW := ℕ → Pt n
  encode := id
  compile := fun c => EqConstraint.loss c
  satP := fun c pts =>
    -- A constraint "holds" when its residual polynomial vanishes. Using the residual rather than a
    -- per-constructor predicate keeps `satP` uniform, and it is equivalent for every constructor by
    -- `Lattice.Geo.Loss.loss_eq_zero_*`.
    EqConstraint.poly c pts = 0
  satW := fun L pts => L pts = 0
  sound := by
    intro c x hx
    -- the penalty is the square of the residual
    show EqConstraint.loss c x = 0
    unfold EqConstraint.loss
    rw [hx]
    ring

/-! ## What compilation means for geometry -/

/-- **Compilation preserves meaning, for geometry.**

Every constraint in a list, compiled to its penalty, accepts a configuration whenever the constraint did.
This is `Compiler.sound` read pointwise over a list, and it is the geometric instance of the target's
first theorem: the chain from `EqConstraint` to `EqConstraint.loss` does not lose solutions.

Stated directly rather than by applying `Compiler.compileProgram_sound`, because the abstract theorem
speaks about `List W` (the compiled penalties) while the geometric statement is more legible as a `∀`
over the source list. Both say the same thing; this form is the one a reader can check against the
definitions. -/
theorem geo_compile_preserves (cs : List (EqConstraint n)) (pts : ℕ → Pt n)
    (h : ∀ c ∈ cs, EqConstraint.poly c pts = 0) :
    ∀ c ∈ cs, EqConstraint.loss c pts = 0 := by
  intro c hc
  have hp := h c hc
  unfold EqConstraint.loss
  rw [hp]
  ring

/-- **The compiler is an inhabitant of `Lift.Compiler` with this behaviour.** Recorded so that the
registration is visible as a fact rather than only as a `def`. -/
theorem geoCompiler_compile (c : EqConstraint n) (pts : ℕ → Pt n) :
    geoCompiler.compile c pts = EqConstraint.loss c pts := rfl

end Lattice.Geo
