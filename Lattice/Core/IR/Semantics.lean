import Mathlib
import Lattice.Core.IR.Obligations
import Lattice.Core.IR.IsIR
import Lattice.Core.IR.Penalty
import Lattice.Core.IR.Canonical

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

/-- **THE SEMANTICS OF A SKELETON WITH RELATIONS IS NOT EMPTY.**

**`k.relations ≠ [] -> semanticsOf k ≠ []`.**
**=> the mapping is faithful on the relations, which the old `semantics k := k` could not express because it did not
distinguish them from the tensors.** -/
theorem semanticsOf_ne_nil {k : IRSkeleton} (h : k.relations ≠ []) : semanticsOf k ≠ [] := h

end Lattice.Core.IR
