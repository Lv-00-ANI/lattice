import Mathlib
import Lattice.Core.Invariant
import Lattice.Reference.Geometry.Geometry.Loop
import Lattice.Reference.Geometry.Geometry.LoopPerp
import Lattice.Lib.Linear.Residual

/-!
# `Lattice.Geo.Unified` -- one statement about every repair in the project

## What this closes

`KNOWN-GAPS` item 7 recorded that the `Repair` interface has inhabitants in two places -- the geometry
(`samePointRepair`, `perpRepair`) and the linear algebra (`linearRepair`) -- but that no theorem mentioned both.
Each side had its own instantiation of `preserves_of_sat`, which showed the interface is shared yet never said so
in one place.

This file states the shared property once, for all three, and proves the linear and geometric halves satisfy it
identically. The value is not a new fact but a **unified one**: a reader can now see that the two carriers are
instances of the same scheme rather than two parallel developments that happen to look alike.

## The shared scheme

Every `Repair` in this project is conservative: at a satisfying state it does not move. Consequently it preserves
every predicate there. That is `Lattice.Core.Invariant.preserves_of_sat`, and the three theorems below are its
specialisations -- each one line, which is the point: the interface carries the content and the carriers only
supply their data.

## What is *not* unified

The three operators differ at **unsatisfying** states, and that difference is the content of
`Lattice.Geo.RepairQuality`. Unifying the conservative half must not be mistaken for unifying the operators: a
copying repair and a projecting repair share their behaviour at solutions and nowhere else.
-/

namespace Lattice.Geo

open Lattice.Core

variable {n : ℕ}

/-- **The geometric repairs are conservative in the shared sense.** At a satisfying configuration, `samePointRepair`
preserves every predicate. -/
theorem samePointRepair_unified (a b : ℕ) (pts : ℕ → Pt n)
    (h : (samePointRepair a b).Sat pts) (P : (ℕ → Pt n) → Prop) :
    P pts → P ((samePointRepair a b).fix pts) :=
  preserves_of_sat (samePointRepair a b) P pts h

/-- **The projecting repair is conservative in the shared sense.** Named separately because its `fix` is a
projection rather than a copy -- the shape of the operator differs, the conservativity does not. -/
theorem perpRepair_unified (a b c e : ℕ) (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n, (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) (h : (perpRepair a b c e hab hcb heb hv).Sat pts)
    (P : (ℕ → Pt n) → Prop) :
    P pts → P ((perpRepair a b c e hab hcb heb hv).fix pts) :=
  preserves_of_sat (perpRepair a b c e hab hcb heb hv) P pts h

end Lattice.Geo

namespace Lattice.Lib.Linear

open Lattice.Core

/-- **The linear repair is conservative in the same sense**, on a different carrier.

Three theorems, three carriers (`ℕ → Pt n` twice and `ℚ` once), one scheme. Together they show that `Repair`'s
conservativity is a property of the interface rather than of geometry. -/
theorem linearRepair_unified (a b : ℚ) (ha : a ≠ 0) (x : ℚ)
    (h : (linearRepair a b ha).Sat x) (P : ℚ → Prop) :
    P x → P ((linearRepair a b ha).fix x) :=
  preserves_of_sat (linearRepair a b ha) P x h

end Lattice.Lib.Linear

namespace Lattice.Geo

open Lattice.Core

/-- **The unified statement, quantified over the carrier.**

This is what item 7 asked for: a single theorem whose statement mentions no particular carrier, instantiated by
all three operators above. `α` ranges over `ℕ → Pt n` and `ℚ` alike, which is exactly the level of generality the
`Repair` interface was introduced to provide.

The theorem is not new -- it is `preserves_of_sat` restated -- and that is precisely the finding: the three
carriers' conservativity *is* the interface's, with nothing geometric or linear left over. -/
theorem every_repair_preserves_at_sat {α : Type} (R : Lattice.Core.Repair α) (x : α)
    (h : R.Sat x) (P : α → Prop) : P x → P (R.fix x) :=
  preserves_of_sat R P x h

end Lattice.Geo
