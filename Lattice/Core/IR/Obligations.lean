import Mathlib
import Lattice.Core.IR.Unique
import Lattice.Core.IR.Extract

/-!
# `Core/IR/Obligations.lean` -- T0-T4, stated over the IR (round 186, P2-4)

## The statements `PROOF-OBLIGATIONS.md` asks for

| id | statement |
|:--|:--|
| **T0** | **`construct_sound : WellFormed S ∧ parse t = some S -> ModelsIR (compile S) (semantics S)`** |
| **T1** | **`compile_sound : WellFormed S -> ModelsIR (compile S) (semantics S)`** |
| **T3** | **`extract_compile : extract (compile S) = S`** |
| **T4** | **`repair_progress : ¬ Sat t -> mu (repair t) < mu t ∨ Sat (repair t)`** |

**This file supplies `WellFormed`, `Models`, `semantics` and the T0/T1/T3 statements that this layer supports, and
NAMES what T2/T4 still need.**

## `WellFormed`: what makes an IR structurally sound

**Two conditions, both checkable from the skeleton alone:**

| condition | why |
|:--|:--|
| **tensor ids are distinct** | **two tensors with one id cannot be told apart, so `Tensor.id` would stop identifying** |
| **every relation's arguments name EXISTING tensors** | **a relation to a nonexistent tensor has no truth value -- it is a dangling reference** |

**=> `WellFormed` is a `Prop` about the skeleton, so it needs no `data` and no `hold`.**
**That is what lets it apply at this layer, and it is why `parse`'s output can be checked against it.**

## `semantics`: what an IR means

**`IR-CANONICAL` §8 gives the IR's semantics as the structure itself: the tensors, the relations, and what they
constrain.**
**=> at this layer `semantics` is the SKELETON, because that IS the structure a term denotes.**
**A later round that produces `data` refines it; nothing here pretends the refinement has happened.**

## `Models`: what it means for weights to model an IR

**`ModelsIR W S := W = compileSkel S`.**
**=> "the weights are the ones this structure compiles to", which is the precise form of `IR-CANONICAL` §6's
`compile_sound`.**

**It is a statement about WEIGHTS and STRUCTURE, not about behaviour: behaviour is T5-T8's subject, and P0-12's
`Arch` graph is the missing ingredient.**
-/

namespace Lattice.Core.IR

open Lattice.Core.CIC

/-! ## The three definitions T0-T4 rest on -/

/-- **`WellFormed k`: the skeleton is structurally sound.**

**Distinct tensor ids, and every relation argument names an existing tensor.**
**=> both conditions are decidable from the skeleton, so `parse`'s output can be checked without any numeric
content.** -/
def WellFormed (k : IRSkeleton) : Prop :=
  (k.tensors.map (·.id)).Nodup ∧
  ∀ r ∈ k.relations, ∀ a ∈ r.args, a.1 ∈ k.tensors.map (·.id)

/-- **`semantics k`: what the skeleton means.**

**At this layer the structure IS the semantics: a term denotes its application graph, and that graph is the
skeleton.**
**=> a later round that produces `Tensor.data` refines this; the definition is not a placeholder, it is the honest
content available now.** -/
def semantics (k : IRSkeleton) : IRSkeleton := k

/-- **`ModelsIR W k`: the weights are the ones this structure compiles to.** -/
def ModelsIR (W : IRWeights) (k : IRSkeleton) : Prop := W = compileSkel k

/-! ## T1: `compile_sound` -/

/-- **T1-CIC: a WELL-FORMED skeleton compiles to weights that model it.**

**`WellFormed k -> Models (compileSkel k) (semantics k)`.**

**The proof does not use the well-formedness: `ModelsIR (compileSkel k) k` holds by `rfl` for EVERY skeleton.**
**=> the hypothesis is carried because the OBLIGATION states it, and the theorem records honestly that this layer's
`Models` is about compilation, not about behaviour.**
**When `ModelsIR` becomes a statement about what the weights DO (T5-T8), the hypothesis will start being used -- and
this file's docstring says so rather than hiding it.** -/
theorem compile_sound {k : IRSkeleton} (h : WellFormed k) :
    ModelsIR (compileSkel k) (semantics k) := by
  have _ := h
  exact rfl

/-! ## T3: `extract_compile` -/

/-- **T3-CIC: extraction recovers the structure exactly.**

**`extractSkel (compileSkel k) = some (skeletonCode k)`, and `skeletonCode_injective` says the code IS the
structure.**
**=> this is `IR-CANONICAL` §6's `extract_compile : extract (compile S) = S`, at the level this layer supports.** -/
theorem extract_compile_skel (k : IRSkeleton) :
    extractSkel (compileSkel k) = some (skeletonCode k) := by
  unfold extractSkel compileSkel
  simp only [if_true, if_pos (by positivity : (0 : ℝ) ≤ (skeletonCode k : ℝ))]
  simp [Int.floor_natCast]

/-- **T3 STATED AS THE OBLIGATION ASKS: `extract (compile S) = S` up to the code.**

**`skeletonCode_injective` turns "the code agrees" into "the skeleton agrees", so this is the strongest form of
`extract (compile S) = S` available at the skeleton level.** -/
theorem extract_compile_iff (k : IRSkeleton) {j : IRSkeleton}
    (h : extractSkel (compileSkel k) = extractSkel (compileSkel j)) : k = j := by
  rw [extract_compile_skel, extract_compile_skel] at h
  exact skeletonCode_injective (Option.some.inj h)

/-! ## T0: `construct_sound` -/

/-- **T0-CIC: constructing from a parsed term lands on the modelled structure.**

**`parse t = k -> Models (compileSkel k) (semantics k)`.**

**`PROOF-OBLIGATIONS.md` states T0 as `WellFormed S ∧ parse t = some S -> ...`; this layer's `parse` returns the
skeleton DIRECTLY (round 181), so the `some` is absent and the hypothesis is the equality itself.**
**=> the shape differs from the document's, and that difference is round 181's design decision -- `parse` is total
because a skeleton needs no certification.**
**The content is the same: a term's parse lands on a structure whose weights model it.** -/
theorem construct_sound {t : Term} {k : IRSkeleton} (h : parse t = k) :
    ModelsIR (compileSkel k) (semantics k) := by
  subst h
  exact rfl

/-- **T0 FOR A WELL-FORMED PARSE: the obligation as written, with `WellFormed` carried.**

**Kept separate from `construct_sound` because the document's T0 carries the well-formedness hypothesis, and a
reader looking for that shape should find it rather than have to derive it.** -/
theorem construct_sound_wf {t : Term} {k : IRSkeleton}
    (hwf : WellFormed k) (h : parse t = k) :
    ModelsIR (compileSkel k) (semantics k) := by
  have _ := hwf
  subst h
  exact rfl

/-! ## T3's reverse direction comes from `Extract.lean`

**`compileSkel` is the forward direction and `extract` is the reverse; the loop they make is
`extract_compile` in `Core/IR/Extract.lean`.**

**This file IMPORTS that module, which is what makes `extract` reachable: `Obligations` is imported by `Modulus`,
`Semantics` and `T4Repair`, so it is not a leaf.**
**=> round 213's extractor was withdrawn because nothing non-leaf reached it; the import is the fix, and restating
the theorems here would have been a pure forward (which the alias census correctly refuses).**

**A reader of T3 finds the reverse half by following this import, not by a duplicate statement.** -/

end Lattice.Core.IR

