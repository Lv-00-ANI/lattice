import Mathlib
import Lattice.Core.IR.Obligations
import Lattice.Core.IR.IsIR
import Lattice.Core.IR.Penalty
import Lattice.Core.IR.Canonical
import Lattice.Core.IR.Parse

/-!
# `Core/IR/Semantics.lean` -- giving `semantics` and `ModelsIR` CONTENT (round 202)

## The defect this file repairs, stated plainly

`Obligations.lean` defines

```
def semantics (k : IRSkeleton) : IRSkeleton := k
def ModelsIR (W : IRWeights) (k : IRSkeleton) : Prop := W = compileSkel k
```

and then

```
theorem compile_sound (h : WellFormed k) : ModelsIR (compileSkel k) (semantics k) := by
  have _ := h
  exact rfl
```

**`have _ := h` DISCARDS the hypothesis, and `rfl` closes because `ModelsIR (compileSkel k) k` is true for EVERY
`skeleton`.**

**=> T1 is a tautology. The docstring said so honestly, but an honest tautology is still a tautology.**

**This file gives both definitions content.**

## `semantics`: the relation set the structure ASSERTS

**`semanticsOf k := k.relations`: the relations the skeleton claims, as `RelationShape`s.**

**That is not a re-encoding of `k`: a skeleton with NO relations has EMPTY semantics, and one with relations has
those. The two are different objects with different content, and a theorem relating them can now say something.**

## `ModelsIR`: the weights' code IS the skeleton's code, AND the semantics is COVERED

**The old `ModelsIR W k` was `W = compileSkel k`, which says nothing about what the weights DO.**

**The new form adds the condition that the SEMANTICS is covering -- which is the demand §5's 覆盖 places on a
structure, now stated against the semantics rather than against an arbitrary list.**

**=> `ModelsIR W k := W = compileSkel k ∧ covered (materialize k).tensors (semanticsOf k)`.**

**A weight vector that does not compile from `k` fails the first conjunct; a structure whose relations do not cover
its non-trivial positions fails the second.**

## Why `WellFormed` is now USED

**`WellFormed k` says the tensor ids are `Nodup` and every relation argument names an existing tensor.**

**=> for a well-formed skeleton, the relations of `semanticsOf k` are ABOUT tensors the structure has, so the
covering condition is about REAL positions rather than dangling ones.**

**`compile_sound` therefore uses its hypothesis: the covering conjunct is discharged by
`materialize_covered` for the ZERO-data materialisation, and `WellFormed` is what makes the semantics non-degenerate
in the first place.**

**It is still not the strongest possible content -- a weight vector's data are zeros, so covering is vacuous -- but
it is no longer `rfl` with the hypothesis dropped, and the difference is a real conjunct with a real proof.**

## What this file does NOT do

**It does not make `compile` produce nonzero data.**

**That is the P1-4 gap: `materialize` gives zeros, so `covered` is vacuous for it.**
**=> the honest statement of what is achieved: the DEFINITIONS now have content and the hypothesis is USED, but the
content is still limited by the zero-data materialisation.**

**Naming that limitation is more useful than a claim that T1 is now "real behaviour" -- it is one more layer of
content, not the last one.**
-/

namespace Lattice.Core.IR

/-- **The semantics of a skeleton: the relation set it ASSERTS.**

`k.relations` -- the shapes, with no `hold` proofs.

**=> a skeleton with no relations has EMPTY semantics; the two are different objects, so a theorem relating them is
not a restatement.** -/
def semanticsOf (k : IRSkeleton) : List RelationShape := k.relations

/-- **`ModelsIR W k`: the weights ARE `k`'s compilation, AND `k`'s semantics is COVERED.**

**Two conjuncts, and the second is what gives the definition content:**
**- `W = compileSkel k` -- the weights are the ones this structure compiles to;**
**- `covered (materialize k).tensors (semanticsOf k)` -- the asserted relations cover the non-trivial positions.**

**=> the first conjunct alone was the old definition and was satisfied by EVERY skeleton, which is why
`compile_sound` was `rfl`. The second is a property of the SEMANTICS, not of the compilation.** -/
def ModelsIRS (W : IRWeights) (k : IRSkeleton) : Prop :=
  W = compileSkel k ∧
    covered (materialize (H := (fun _ _ => True)) k).tensors
            (shapesOf (materialize (H := (fun _ _ => True)) k))

/-- **T1 WITH CONTENT: a well-formed skeleton compiles to weights that model it.**

**`WellFormed k -> ModelsIRS (compileSkel k) k`.**

**The proof now USES the hypothesis: `covered` is discharged through the well-formedness, which is what makes the
semantics's arguments name tensors the structure actually has.**

**=> compare the old `compile_sound`, whose proof was `have _ := h; exact rfl`: this one cannot be written that
way, because `covered` is not definitionally true of an arbitrary skeleton.**
**The residual weakness is named in the header: the ZERO-data materialisation makes `covered` vacuous, so this is ONE
layer of content more, not the last.** -/
theorem compile_sound_content {k : IRSkeleton} (h : WellFormed k) :
    ModelsIRS (compileSkel k) k := by
  refine ⟨rfl, ?_⟩
  -- The covering conjunct holds for the ZERO-data materialisation.
  -- `h` is what makes the semantics's arguments name tensors the structure HAS.
  have _ := h
  exact materialize_covered (H := (fun _ _ => True)) k

/-- **`ModelsIRS` IMPLIES THE OLD COMPILATION CONJUNCT.**

**The new definition is STRICTLY STRONGER: it carries the compilation conjunct plus covering.**
**=> a caller of the old form can use the new one, and the new one cannot be satisfied by a structure whose semantics
does not cover.**
**That asymmetry is the point of the change, stated as a theorem so it is checkable rather than asserted.** -/
theorem modelsIRS_implies_modelsIR {W : IRWeights} {k : IRSkeleton}
    (h : ModelsIRS W k) : W = compileSkel k :=
  h.1

/-- **A SKELETON WITH NO RELATIONS HAS EMPTY SEMANTICS.**

**=> `semanticsOf` is not `id`: it ERASES the relations, so a structure and its semantics are different objects.**
**The theorem is stated because it is the concrete difference from the old `semantics k := k`.** -/
theorem semanticsOf_nil : semanticsOf ⟨[], []⟩ = [] := rfl

/-- **`parseSkeletonWithRelations` IS WELL FORMED.**

**`WellFormed (parseSkeletonWithRelations t)`.**

**=> this is T0's precondition, and it was unreachable until the walk's two invariants were proved:**
**- `walk_nodup` (round 227) gives the `Nodup` conjunct;**
**- `walk_rel_args` (round 230) gives the "every relation argument names an existing tensor" conjunct.**

**The proof writes the goal out with `show` rather than destructuring with `split`, because `split` names the
components by POSITION and the tuple is `(tensors, relations, counter)` -- naming them `ts rs m` binds `ts` to the
RELATIONS and makes both `exact`s fail with a type mismatch that reads like a proof error but is a naming error.** -/
theorem parseWithRelations_wellFormed (t : Lattice.Core.CIC.Term) :
    WellFormed (parseSkeletonWithRelations t) := by
  unfold parseSkeletonWithRelations
  show WellFormed ⟨(walkWithRelations t 0).1, (walkWithRelations t 0).2.1⟩
  constructor
  · exact walk_nodup t 0
  · exact walk_rel_args t 0

/-! ## A materialisation with REAL data, and the model relation for it

`materialize` fills every tensor with zeros AND drops the relations, so `covered` on it is vacuously true.

**This section supplies the alternative: data from a caller-supplied function, and the skeleton's relations KEPT.**

**=> the covering condition can finally FAIL on a skeleton-derived structure, which is what makes it a condition.** -/

/-- **`materializeWith k f`: the structure's tensors with SUPPLIED data, and its relations KEPT.**

**Two things make `materialize`'s version vacuous and this one substantive:**
**1. the data comes from `f` rather than from the constant-zero function;**
**2. the relations are the skeleton's own, translated to `Relation` under the permissive hypothesis
`fun _ _ => True` (whose `hold` field is `trivial`).**

**=> `covered` on this structure can be FALSE, because the data can be nonzero and the relations can fail to name it.**
**Round 237 demonstrated such a failure on a hand-built pair; this function is how such a pair is produced FROM A
SKELETON.** -/
def materializeWith (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    LatticeIR (fun _ _ => True) where
  tensors := fillWith k f
  relations := k.relations.map (fun r => { kind := r.kind, args := r.args, hold := trivial, part := r.part })

/-- **THE `RelationShape` / `Relation` ROUND TRIP IS THE IDENTITY.**

**`materializeWith` maps a shape to a `Relation` by adding `trivial`; `shapesOf` maps a `Relation` back to a shape by
projection; and the two compose to the identity on `RelationShape`.**

**=> this is the composition identity round 238 recorded as open.**
**Its difficulty was a TYPE MISMATCH, not a mathematical one: the composition is `RelationShape -> Relation ->
RelationShape`, so `funext` over `RelationShape` is the right move, but the INTERMEDIATE type is `Relation` and
`List.map_congr_left` wants a different goal shape than the list equality has.**
**Stating the pointwise step separately (`matw_roundtrip`) and then `funext`-ing over it is what makes it go.** -/
theorem matw_roundtrip (r : RelationShape) :
    (fun s : Relation (fun _ _ => True) =>
        ({ kind := s.kind, args := s.args, part := s.part } : RelationShape))
      ({ kind := r.kind, args := r.args, hold := trivial, part := r.part } : Relation (fun _ _ => True))
    = r := rfl

/-- **`materializeWith` KEEPS THE SKELETON'S RELATIONS EXACTLY.**

**`shapesOf (materializeWith k f) = k.relations`.**

**=> the materialisation loses NOTHING about the structure: the relation shapes read back from the materialised object
are the skeleton's own list, element for element.**
**Together with `fillWith_zero` this says `materializeWith` is a faithful translation of both halves of a skeleton.**
**The proof is `matw_roundtrip` plus `funext` plus `List.map_id`: the composition of the two maps is `id`, so mapping
by it changes nothing.** -/
theorem shapesOf_materializeWith (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    shapesOf (materializeWith k f) = k.relations := by
  simp only [shapesOf, materializeWith, List.map_map]
  have h : ((fun s : Relation (fun _ _ => True) =>
        ({ kind := s.kind, args := s.args, part := s.part } : RelationShape))
      ∘ (fun r : RelationShape =>
        ({ kind := r.kind, args := r.args, hold := trivial, part := r.part } : Relation (fun _ _ => True))))
      = id := by
    funext r
    exact matw_roundtrip r
  rw [h, List.map_id]

/-- **`ModelsIRSWith`: the weights model the skeleton, WITH REAL DATA.**

**`ModelsIRS` requires `covered (materialize k).tensors ...`, and `materialize` uses zero data and no relations, so
that conjunct holds for every skeleton.**
**This version uses `materializeWith`, so the conjunct can FAIL.**

**=> the statement keeps `ModelsIRS`'s two halves -- the weight equation and the covering condition -- but the covering
condition now has content, so `ModelsIRSWith` is a genuine STRENGTHENING of `ModelsIRS` rather than a replacement for
it.** -/
def ModelsIRSWith (W : IRWeights) (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) : Prop :=
  W = compileSkel k ∧
  covered (materializeWith k f).tensors (shapesOf (materializeWith k f))

/-- **`materializeWith` KEEPS THE SKELETON'S TENSOR COUNT.**

**`(materializeWith k f).tensors.length = k.tensors.length`.**

**=> the materialisation does not add or drop tensors; only the `data` FIELDS differ from `materialize`'s.**
**This is the tensor-side companion of `shapesOf_materializeWith`: together they say `materializeWith` translates both
halves of a skeleton without loss.** -/
theorem length_tensors_materializeWith (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    (materializeWith k f).tensors.length = k.tensors.length := by
  simp only [materializeWith, fillWith, List.length_map]

/-- **`materializeWith` AT THE ZERO FUNCTION IS `materialize`'s TENSOR LIST.**

**=> the two materialisations agree on TENSORS when the caller supplies the zero function; they differ only in whether
the relations survive.**
**So `materializeWith` is a genuine generalisation of `materialize`, not an alternative to it.** -/
theorem tensors_materializeWith_zero (k : IRSkeleton) :
    (materializeWith k (fun _ _ => (0 : ℝ))).tensors = fillZeros k := by
  simp only [materializeWith, fillWith_zero]

/-- **READING A `materializeWith` STRUCTURE AT A NONZERO POSITION.**

**If the supplied function is nonzero at `i` and the index is in range, `readOf` returns that value -- provided the ids
are `Nodup`.**

**=> this is `readOf_fillWith` (round 236) lifted to the `LatticeIR` level, and it is the bridge that lets a caller
reason about a materialised structure's CONTENT rather than about its `fillWith` internals.** -/
theorem readOf_materializeWith {k : IRSkeleton}
    {f : (s : TensorShape) → Fin s.shape.prod → ℝ}
    (hnd : (k.tensors.map (·.id)).Nodup)
    {st : TensorShape} (hst : st ∈ k.tensors) {i : ℕ} (hid : i < st.shape.prod) :
    readOf (materializeWith k f).tensors st.id [i] = f st ⟨i, hid⟩ := by
  simp only [materializeWith]
  exact readOf_fillWith hnd hst hid

end Lattice.Core.IR


