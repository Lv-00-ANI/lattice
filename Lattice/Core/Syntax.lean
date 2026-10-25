/-!
# `Lattice.Core.Syntax` -- symbolic programs as syntactic objects

## Design rationale

The legacy linear fragment represented a constraint as

```lean
structure VectorConstraint where
  a : List Int      -- coefficient vector
  b : Int           -- constant
```

and its satisfaction predicate as `dot a x + b = 0` where

```lean
def dot (a x : List Int) : Int :=
  (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0
```

`List.zip` **silently truncates to the shorter list**, so `dot [3,5] [] = 0` and a
two-variable constraint is *satisfied* by the zero-variable input `x = []`.  That is
a false positive in the meaning of "constraint satisfaction", and it was registered
against the project as `sat_ragged_false_positive`.

The legacy fix was to add a *second*, index-carrying type alongside the first,
leaving every existing use-point on the truncated semantics. This file takes the
other route: **there is exactly one representation and its length is part of its
type**, so truncation cannot be written down at all.

## Why `Fin n -> Int` and not `List Int`

`Fin n -> Int` makes the length a *parameter*, so a constraint over `n` variables
cannot be applied to a vector of `m ≠ n` variables: the application does not
typecheck. The defect is removed by the type system rather than by a side condition
that a future author could forget.

## Generality

Coefficients are `R`-valued for an arbitrary `R`, not fixed to `Int`. The linear
fragment is the case `R = Int`; the training-theoretic fragment is `R = ℝ`. This is
what lets the same syntax serve both the discrete symbolic side and the continuous
weight side without a second inductive type.
-/

namespace Lattice.Core

/-- A linear form over `n` variables with coefficients in `R`, together with an
inhomogeneous constant.

`lin c` denotes the function `x ↦ c.a · x + c.b`. -/
structure LinearForm (R : Type) (n : Nat) where
  /-- Coefficients, one per variable. The index set is `Fin n`, so the arity is
  carried by the type. -/
  a : Fin n → R
  /-- Inhomogeneous constant term. -/
  b : R

/-- The evaluation point type of a `LinearForm R n`: one `R` per variable. -/
abbrev Point (R : Type) (n : Nat) := Fin n → R

namespace LinearForm

variable {R : Type} {n : Nat}

/-- The scalar comparison a constraint asserts. Kept abstract so that `=`-constraints
and inequality-constraints can share one syntax. -/
inductive Rel where
  | eq
  | le
  | lt
  deriving DecidableEq, Repr

/-- A linear constraint: a linear form compared against zero. -/
structure Constraint (R : Type) (n : Nat) where
  form : LinearForm R n
  rel : Rel

end LinearForm

end Lattice.Core
