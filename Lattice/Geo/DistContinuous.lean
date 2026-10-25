import Mathlib
import Lattice.Geo.Dist

/-!
# `Lattice.Geo.DistContinuous` -- continuity of `sqDist`

## Why this file exists

Round 114 found that closing the `.samePoint` branch of `EqConstraint.poly` needs a *path* argument rather than a
single overwrite: `IsLocalMin` is a neighbourhood condition, so refuting it requires a nearby point with a smaller
value, and an exact coordinate overwrite can land arbitrarily far away.

The path argument needs `sqDist` to be continuous. Round 115 measured the codebase: **there was no continuity
statement about `sqDist` at all** -- `Lattice.Geo.Differentiable` covers `coordProj`, `segComp` and the perpendicular
residual, but not the distance term. This file supplies the part of that infrastructure that could be established.

## What is here, and what is not

* `sqDist_eq_sum` -- the definition unfolded to a finite sum, the form continuity arguments consume.
* `continuous_sqDist_right` -- `sqDist p ·` is continuous in the second argument.

**Not here:** continuity in *both* arguments jointly. A probe attempting it hit `aesop: internal error during proof
reconstruction`, which is a tool failure rather than a mathematical one, but the statement is recorded as absent
rather than left as a stub. It is also not what the `.samePoint` path argument turns out to need: the path holds
`pts b` fixed and varies only one coordinate of `pts`.

The `.samePoint` branch is therefore still open, with the remaining obligations named in
`Lattice.Geo.PolyNondegenerate`: a continuous path, strict decrease along it, and a step small enough to stay inside the
neighbourhood.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **`sqDist` unfolded to a finite sum.** The form every continuity argument here consumes; the definition itself
goes through `sqNorm` and `diff`, which `simp` will not rewrite under an integral-like binder on its own. -/
theorem sqDist_eq_sum (p q : Pt n) :
    sqDist (n := n) p q = ∑ i : Fin n, (p i - q i) ^ 2 := by
  simp [sqDist, Lib.Linear.PenaltyVector.sqNorm, diff]

/-- **`sqDist p ·` is continuous in its second argument.**

A finite sum of squared coordinate differences: subtraction and squaring are continuous, and a finite sum of
continuous real-valued functions is continuous.
-/
theorem continuous_sqDist_right (p : Pt n) :
    Continuous (fun q : Pt n => sqDist (n := n) p q) := by
  simp only [sqDist, Lib.Linear.PenaltyVector.sqNorm, diff]
  continuity

end Lattice.Geo
