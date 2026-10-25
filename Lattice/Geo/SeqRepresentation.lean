import Mathlib
import Lattice.Geo.Expr
import Lattice.Lift.Extraction

/-!
# `Lattice.Geo.SeqRepresentation` -- the object-level round trip over an infinite index

## Why this file exists

`Lattice.Geo.Flatten.flattenRepresentation` gives a `Representation (Fin k → Pt n) (Fin (k * n) → ℝ)`: a finite point
set laid out as a finite real vector. The repair operators, however, act on `ℕ → Pt n` -- `samePointRepair`,
`perpRepair`, `conjRepair` -- because the constraint language indexes points by `ℕ`.

A `Repair` must live on the same type as the `Representation` it is paired with, so combining the two needs a
`Representation` indexed by `ℕ`. This file supplies it.

## The construction

Flatten `(ℕ → Pt n)` to `(ℕ → ℝ)` by the usual row-major indexing: point `p`, coordinate `i` lands at slot
`p * n + i`. That is exactly what `flatten` does for a finite set, with `Fin k` replaced by `ℕ`.

Reading back is `j / n` for the point and `j % n` for the coordinate, which inverts the encoding because
`(p % n) < n` -- **this is where `0 < n` enters**. With `n = 0` there is no coordinate to put anywhere, `Fin 0` is
empty, and no such bijection exists; the hypothesis is not a convenience.

## What it does not give

A round trip that returns the *original weight*. As with the finite case, the round trip here is between two
objects -- a point sequence and a real sequence -- and `Lattice.Geo.Semantic.semantic_not_injective` says the semantic
quotient has no right inverse. Object level bijective, semantic level not: the same two facts, stated for the
infinite index.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **Row-major flattening of a point sequence**: point `p`, coordinate `i` maps to slot `p * n + i`. -/
noncomputable def seqEncode (n : ℕ) (hn : 0 < n) (pts : ℕ → Pt n) : ℕ → ℝ :=
  fun j => pts (j / n) ⟨j % n, Nat.mod_lt _ hn⟩

/-- **Reading a point sequence back** out of a real sequence. -/
noncomputable def seqDecode (n : ℕ) (v : ℕ → ℝ) : ℕ → Pt n :=
  fun p i => v (p * n + i.val)

/-- **The flattening and the reading-back are inverse**: decoding the encoding returns the original sequence.

The proof is the two arithmetic facts `(p * n + i) / n = p` and `(p * n + i) % n = i`, both of which hold because
`i < n` for `i : Fin n`. -/
theorem seqDecode_encode (hn : 0 < n) (pts : ℕ → Pt n) :
    seqDecode n (seqEncode n hn pts) = pts := by
  funext p i
  show pts ((p * n + i.val) / n) ⟨(p * n + i.val) % n, Nat.mod_lt _ hn⟩ = pts p i
  have hi : i.val < n := i.isLt
  have hdiv : (p * n + i.val) / n = p := by
    rw [Nat.add_comm (p * n) i.val, Nat.add_mul_div_right i.val p hn,
        Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod : (p * n + i.val) % n = i.val := by
    rw [Nat.add_comm (p * n) i.val, Nat.add_mul_mod_self_right i.val p n,
        Nat.mod_eq_of_lt hi]
  rw [hdiv]
  congr 1
  exact Fin.ext hmod

/-- **The encoding and the reading-back are inverse in the other direction too**, which the round-trip obligation
alone does not ask for but which makes the pair a bijection rather than only an injection. Reading back and
re-encoding recovers every slot, including the ones outside the finite rows. -/
theorem seqEncode_decode (hn : 0 < n) (v : ℕ → ℝ) :
    seqEncode n hn (seqDecode n v) = v := by
  funext j
  show v (j / n * n + (j % n)) = v j
  have h : j / n * n + j % n = j := by
    have hh := Nat.div_add_mod j n
    rw [Nat.mul_comm n (j / n)] at hh
    exact hh
  rw [h]

/-- **The object-level `Representation` over `ℕ`**, so a `Repair` on `ℕ → Pt n` can be paired with one.

Built as `seqEncode` / `seqDecode` directly rather than through `Lattice.Lift.ofEquiv`, because that constructor wants an
`≃` and the two inverse laws here are proved above; the round-trip field is `seqDecode_encode`. -/
noncomputable def seqRepresentation (hn : 0 < n) :
    Lattice.Lift.Representation (ℕ → Pt n) (ℕ → ℝ) where
  inputP := ℕ → Pt n
  inputW := ℕ → ℝ
  encode := seqEncode n hn
  decode := seqDecode n
  compile := seqEncode n hn
  extract := seqDecode n
  roundtrip := fun pts => seqDecode_encode hn pts

/-- **The round trip of `seqRepresentation`**, stated as its own theorem rather than unfolded from the structure. -/
theorem seqRepresentation_roundtrip (hn : 0 < n) (pts : ℕ → Pt n) :
    (seqRepresentation (n := n) hn).extract ((seqRepresentation (n := n) hn).compile pts) = pts :=
  seqDecode_encode hn pts

/-- **... and the other direction**, which makes it a bijection rather than only a left inverse. -/
theorem seqRepresentation_compile_extract (hn : 0 < n) (v : ℕ → ℝ) :
    (seqRepresentation (n := n) hn).compile ((seqRepresentation (n := n) hn).extract v) = v :=
  seqEncode_decode hn v

end Lattice.Geo
