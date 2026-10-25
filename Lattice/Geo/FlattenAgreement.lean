import Mathlib
import Lattice.Geo.Flatten
import Lattice.Geo.SeqRepresentation

/-!
# `Lattice.Geo.FlattenAgreement` -- the finite and infinite flattenings agree on a shared slot

## Two representations, one convention

`Lattice.Geo.Flatten.flattenRepresentation` lays a *finite* point set out as a finite real vector, using
`flatEquiv := finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n)`.
`Lattice.Geo.SeqRepresentation.seqRepresentation` lays an *infinite* point sequence out as an infinite real sequence,
using the slot index `p * n + i`.

Nothing said the two agreed, and a reader has reason to ask: they are used in different places in the project
(`IRBridge` and `ClosedLoop` mix both), so if their conventions differed, results computed in one would not be
comparable with results computed in the other.

They do agree, and the only thing in the way is that `finProdFinEquiv` puts the coordinate first:

```
(finProdFinEquiv (p, i)).val = i + n * p
```

while `seqEncode` writes slot `p * n + i`. The two are equal by commutativity of multiplication, so the agreement is
true but not definitional -- it needs one arithmetic step, which is what this file supplies.

## What this gives, and what it does not

**It gives**: the slot a `flatten`ed point occupies holds the same real as the slot `seqEncode` puts it in. So a
constraint evaluated on a finite point set and the same constraint evaluated on the corresponding point sequence see
the same numbers.

**It does not give**: a `Representation` isomorphism between the finite and infinite carriers. Their index types
differ (`Fin (k * n)` versus `ℕ`), so there is no bijection between them to build one from; what is shared is the
*convention*, which is the only thing that could have gone wrong.
-/

namespace Lattice.Geo

variable {k n : ℕ}

/-- **`finProdFinEquiv` puts the coordinate first**: the slot for `(p, i)` is `i + n * p`.

Recorded separately because the rest of the file needs it as a rewrite rule, and because it is the one place where
the two conventions visibly differ. -/
theorem flatEquiv_val (p : Fin k) (i : Fin n) :
    (flatEquiv k n (p, i)).val = i.val + n * p.val := by
  simp [flatEquiv, finProdFinEquiv]

/-- **The two slot indices are the same number**, by commutativity. This is the step that makes the agreement a
theorem rather than a definitional equality. -/
theorem flatEquiv_val_eq_seqSlot (p : Fin k) (i : Fin n) :
    (flatEquiv k n (p, i)).val = p.val * n + i.val := by
  rw [flatEquiv_val]
  exact Nat.add_comm i.val (n * p.val) |>.trans (by rw [Nat.mul_comm n p.val])

/-- **`flatten` puts `pts p i` in the slot for `(p, i)`.**

This is the definitional fact the agreement rests on: `flatten` reads position `p` and coordinate `i` out of the slot
that `flatEquiv` assigns to the pair. -/
theorem flatten_apply (pts : Fin k → Pt n) (p : Fin k) (i : Fin n) :
    flatten pts (flatEquiv k n (p, i)) = pts p i := by
  simp [flatten]

end Lattice.Geo
