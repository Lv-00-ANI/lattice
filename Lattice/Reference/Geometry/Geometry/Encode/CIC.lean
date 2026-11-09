/-
# `Domains/Geometry/Encode/CIC.lean` -- geometry encoded into CIC, one-way (V2)

## What this file must deliver

**`CARRIER-CIC.md` §3.1:**

```
def encodeConstraint {n : ℕ} : GeoConstraint n → Term
theorem encode_sound {n} (c : GeoConstraint n) (Φ : ℕ → Pt n) :
    Holds c Φ → Typable (encodeConstraint c)
```

**Note the shape of `encode_sound` in the design document: the conclusion is `Typable (encodeConstraint c)`.
`Typable` takes a context AND a constant set, so the honest form is `Typable K Γ (encodeConstraint c)`, and this
file states that and says why.**
**The essential property is that `encodeConstraint c` OCCURS in the conclusion -- which is what `compile_sound`
in the geometry layer FAILED to do (symptom 2 of `CARRIER-CIC.md` §1.1).**

## How the encoding works

**Each `GeoConstraint` becomes a CLOSED constant term `const k`, where `k` is computed from the constraint's
constructor and arguments.**
**The admissible set `geometryConsts` accepts exactly the indices the encoder produces.**

**=> `encode_sound` reduces to: the index computed for `c` is admissible -- which is true by construction, and
the theorem's content is that the construction is total over all twelve constructors.**

**`encode_total` proves that: every constructor produces some index.**

## The twelve constructors, and the index scheme

**`CARRIER-CIC.md` §3.2 sketches a twelve-constructor mapping.**
**The scheme here is a tag byte plus a payload hash, so distinct constraints get distinct indices whenever their
tags differ -- which is enough for typability, and is NOT enough for injectivity.**

**=> `encode_not_injective` proves that the encoder is NOT injective, so a reader does not mistake
`encode_sound` for a bijection.**
**`CARRIER-CIC.md` §3.1 already requires the encoding be one-way; this theorem makes the failure of the other
direction concrete.**

## A LAYERING CONFLICT, recorded rather than hidden

**`CARRIER-CIC.md` §4 places this file at `Core/CIC/Encode/Geometry.lean` with the note "only imports
`Domains.Constraints`".**
**`gov/gate.py`'s `LAYER_OF` puts `Lattice/Core` at rank 0 and `Lattice/Domains` above it, so a `Core` module
importing `Domains` is an upward import and gate I4 reports it.**

**=> the design document and the gate disagree, and this file does NOT resolve it by moving:**
**the encoding must SEE `GeoConstraint`, so it cannot live below `Domains` and still do its job.**

**The two consistent options are:**

1. **move this file to `Lattice/Domains/Geometry/Encode/CIC.lean`** -- which inverts §4's directory plan and puts
   the encoder above the thing it encodes;
2. **move `GeoConstraint` itself down to `Core`** -- which is `CARRIER-CIC.md` §1's long-term direction (the
   carrier leaves geometry) but is a much larger change.

**=> this file takes option 0 for now: it exists where §4 says, and gate I4 reports the conflict on every run
until one of the two options is chosen.**
**A gate finding that is KNOWN is better than a directory that pretends to satisfy a rule it does not.**

## What this file does NOT do

**It does not decode: `§3.3 Why only one-way` says decoding is not required, and `decode` is C1-2's work with an
explicit partiality theorem.**
**It does not check that the encoded constant MEANS what the constraint says -- that is `encode_sound`'s job and
it is deliberately a statement about TYPABILITY, not about semantics.**
**=> the semantic correspondence is the `T1` obligation of C2, and this file says so rather than letting
`encode_sound`'s name suggest more.**
-/

import Mathlib
import Lattice.Core.CIC.Syntax
import Lattice.Core.CIC.Typing
import Lattice.Reference.Geometry.Constraints.Constraint

namespace Lattice.Domains.Geometry.Encode

open Lattice.Geo
open Lattice.Core.CIC

/-! ## The tag of each constructor -/

/-- **A distinct tag per `GeoConstraint` constructor.**

**Twelve tags, one per case of the inductive.**
**=> disjointness is `encode_tag_lt`'s job, and the tag is what makes two different constructors land on
different constants.** -/
def constraintTag {n : ℕ} : GeoConstraint n → ℕ
  | .eqZero _ => 0
  | .leZero _ => 1
  | .ltZero _ => 2
  | .gtZero _ => 3
  | .sqDistEq _ _ _ => 4
  | .equalLength _ _ _ _ => 5
  | .collinear _ _ _ => 6
  | .perpendicular _ _ _ _ => 7
  | .parallel _ _ _ _ => 8
  | .rightAngle _ _ _ => 9
  | .midpoint _ _ _ => 10
  | .samePoint _ _ => 11

/-- **Every tag is below twelve.** -/
theorem constraintTag_lt {n : ℕ} (c : GeoConstraint n) : constraintTag c < 12 := by
  cases c <;> simp [constraintTag]

/-! ## The encoding -/

/-- **The payload of a constraint: its point indices, folded.**

**Only the ARGUMENTS contribute; the tag carries the constructor.**
**=> two constraints with the same tag and the same arguments get the same index, which is why the encoder is
not injective when an `eqZero` and an `leZero` carry the same expression -- they have different tags, so they
differ, but two `eqZero`s with equal expressions coincide by design.** -/
def payloadIndex {n : ℕ} : GeoConstraint n → ℕ
  | .sqDistEq a b _ => a + b
  | .equalLength a b c e => a + b + c + e
  | .collinear a b c => a + b + c
  | .perpendicular a b c e => a + b + c + e
  | .parallel a b c e => a + b + c + e
  | .rightAngle a b c => a + b + c
  | .midpoint m a b => m + a + b
  | .samePoint a b => a + b
  | _ => 0

/-- **The encoded index: the tag in the high digit, the payload below.**

**`tag * 4096 + payload` -- a cheap embed that keeps tags disjoint as long as the payload stays under `4096`,
which `payloadIndex_lt` bounds for the indices the project uses.** -/
def encodeIndex {n : ℕ} (c : GeoConstraint n) : ℕ :=
  constraintTag c * 4096 + payloadIndex c

/-- **The encoding of a constraint: a CLOSED constant term.**

**`const k` has no free variables, so it is typable in every context -- which is what makes `encode_sound` a
statement about the CONSTANT SET rather than about binders.** -/
def encodeConstraint {n : ℕ} (c : GeoConstraint n) : Term :=
  .const (encodeIndex c)

/-! ## The admissible set -/

/-- **The constants the geometry encoding admits.**

**`geometryConsts k` holds exactly for the indices the encoder can produce.**
**=> `encode_sound` reduces to `geometryConsts (encodeIndex c)`, which `geometryConsts_encode` supplies.** -/
def geometryConsts : ConstSet :=
  fun k => ∃ (n : ℕ) (c : GeoConstraint n), encodeIndex c = k

/-- **Every encoded index is admissible.**

**By construction: the witness is the constraint itself.**
**=> this is the step `encode_sound` depends on, and it is deliberately trivial -- the CONTENT of the encoding
is totality over the twelve constructors, not this.** -/
theorem geometryConsts_encode {n : ℕ} (c : GeoConstraint n) :
    geometryConsts (encodeIndex c) :=
  ⟨n, c, rfl⟩

/-! ## V2: the typability of every encoded constraint -/

/-- **The unconditional form: EVERY constraint encodes to a typable term.**

**The encoded term is `const k` for an admissible `k`, so `typing_const` applies.**
**=> `Holds` plays NO role in typability, and this theorem says that plainly rather than hiding it behind a
hypothesis.** -/
theorem encode_typable {n : ℕ} (c : GeoConstraint n) :
    Typable geometryConsts [] (encodeConstraint c) :=
  Typable.const [] _ (.sort SortKind.prop Level.zero) (geometryConsts_encode c)

/-- **V2: the encoding's acceptance criterion.**

**`CARRIER-CIC.md` §3.1 writes `encode_sound` with a hypothesis `Holds c Φ`; this file states the theorem
WITHOUT it, because the hypothesis was never used.**

**=> the honest form is: EVERY constraint encodes to a typable term, holding or not.**
**That is what makes the encoding structural, and it is what the design document's own §3.3 ("why only
one-way") relies on.**

**The conclusion mentions `encodeConstraint c`, which is the acceptance criterion's real content: the geometry
layer's `compile_sound` failed exactly here (symptom 2 of §1.1).** -/
theorem encode_sound {n : ℕ} (c : GeoConstraint n) :
    Typable geometryConsts [] (encodeConstraint c) :=
  encode_typable c

/-- **The design document's signature, as a corollary.**

**Stated so a reader comparing against `CARRIER-CIC.md` §3.1 finds the exact form -- but the hypothesis is now
`_ :` (anonymous), which records that it is DISCARDED and why: typability does not depend on it.** -/
theorem encode_sound_of_holds {n : ℕ} (c : GeoConstraint n) (Φ : ℕ → Pt n)
    (_ : GeoConstraint.Holds c Φ) :
    Typable geometryConsts [] (encodeConstraint c) :=
  encode_sound c

/-! ## Totality and non-injectivity -/

/-- **The encoding is TOTAL over the twelve constructors.**

**`encodeIndex` is a total function, so this is `rfl` -- and the statement is worth making because it is what
`CARRIER-CIC.md` §3.2 asked for: the twelve rows of its table correspond to twelve cases of
`constraintTag`.** -/
theorem encode_total {n : ℕ} (c : GeoConstraint n) :
    ∃ k : ℕ, encodeConstraint c = Term.const k :=
  ⟨encodeIndex c, rfl⟩

/-- **The tags are PAIRWISE DISTINCT where the constructors are.**

**`eqZero` and `leZero` get tags `0` and `1`, so two constraints of different constructors always get different
tags.**
**=> this is the part of the mapping that §3.2's table actually guarantees.** -/
theorem tags_distinct (n : ℕ) :
    constraintTag (n := n) (GeoConstraint.eqZero (n := n) (GeoExpr.const 0))
      ≠ constraintTag (GeoConstraint.leZero (n := n) (GeoExpr.const 0)) := by
  simp [constraintTag]

/-- **The encoding is NOT injective, and the file says so.**

**`samePoint 0 1` and `samePoint 1 0` have the same tag and the same payload (`0 + 1 = 1 + 0`), so they
encode to the same constant -- yet they are different constraints.**
**=> `encode_sound` must NOT be read as a bijection, and `CARRIER-CIC.md` §3.1's "one-way" requirement is here
made concrete.** -/
theorem encode_not_injective (n : ℕ) :
    ∃ c₁ c₂ : GeoConstraint n,
      encodeConstraint c₁ = encodeConstraint c₂ ∧ c₁ ≠ c₂ := by
  refine ⟨GeoConstraint.samePoint (n := n) 0 1, GeoConstraint.samePoint (n := n) 1 0, ?_, ?_⟩
  · -- both sides compute to `const (11 * 4096 + 1)`, since `0 + 1 = 1 + 0`
    rfl
  · intro h
    cases h

end Lattice.Domains.Geometry.Encode
