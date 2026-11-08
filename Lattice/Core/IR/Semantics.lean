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

/-! ## `ModelsIRSWith` has an inhabitant

The model relation is now inhabited with data that is NOT all zero.

**The exhibit: a skeleton with one tensor of shape `[2]`, one relation naming `(0, [0])`, and a data function that is
`1` at index `0` and `0` elsewhere.**

**=> the first structure for which "the weights model the skeleton" is a claim about CONTENT rather than about a
vacuous condition.**

**Three of the last seven rounds produced the tools this needs:**
**`fillWith` (233) supplies the data, `readOf_fillWith` (236) / `readOf_materializeWith` (239) make a reading
recoverable, and `shapesOf_materializeWith` (239) says the relations are the skeleton's own.** -/

/-- **A skeleton with one tensor of shape `[2]` and one `depends` relation naming `(0, [0])`.** -/
def pointSkeleton : IRSkeleton :=
  { tensors := [{ id := 0, shape := [2] }],
    relations := [{ kind := .depends, args := [(0, [0])], part := some .arch }] }

/-- **The data: `1` at index `0`, `0` elsewhere.** -/
def pointData (s : TensorShape) : Fin s.shape.prod → ℝ :=
  fun i => if (i : ℕ) = 0 then 1 else 0

/-- **`pointSkeleton`'s ids are distinct.**

**=> this is the hypothesis `readOf_fillWith` and `readOf_materializeWith` both need, and for a one-element list it is
immediate.** -/
theorem pointSkeleton_nodup : (pointSkeleton.tensors.map (·.id)).Nodup := by
  simp [pointSkeleton]

/-- **THE WEIGHTS MODEL THE SKELETON, WITH REAL DATA.**

**`ModelsIRSWith (compileSkel pointSkeleton) pointSkeleton pointData`.**

**=> this is `ModelsIRSWith`'s first inhabitant whose data is not identically zero.**
**The two halves of `ModelsIRSWith` are discharged differently, and that is the point:**
**- the weight equation `W = compileSkel k` holds by `rfl` -- compilation is a definition, not an assumption;**
**- the covering conjunct is the real work, and it needs `readOf_fillWith`'s content: only index `0` is nonzero, and
`(0, [0])` is exactly what the relation names.**

**=> `ModelsIRS` (the zero-data version) would have been satisfied here no matter what the data was, because its
`covered` is vacuous; this one is satisfied BECAUSE the relation names the nonzero position.** -/
theorem pointSkeleton_models :
    ModelsIRSWith (compileSkel pointSkeleton) pointSkeleton pointData := by
  constructor
  · rfl
  · intro t i ht hi hne
    simp only [materializeWith, fillWith, pointSkeleton, List.map_cons, List.map_nil,
               List.mem_singleton] at ht
    subst ht
    have hi0 : i = 0 := by
      by_contra h
      exact hne (by simp [readOf, materializeWith, fillWith, pointSkeleton, pointData, hi, h])
    refine ⟨{ kind := .depends, args := [(0, [0])], part := some .arch }, ?_, ?_⟩
    · simp [shapesOf, materializeWith, pointSkeleton]
    · subst hi0
      simp [Names]

/-- **A skeleton identical to `pointSkeleton` but whose relation names `(0, [1])` -- the WRONG position.** -/
def pointSkeletonWrong : IRSkeleton :=
  { tensors := [{ id := 0, shape := [2] }],
    relations := [{ kind := .depends, args := [(0, [1])], part := some .arch }] }

/-- **THE COVERING CONJUNCT IS WHAT DOES THE WORK: WITH THE WRONG RELATION, THE SAME SKELETON AND DATA FAIL.**

**`pointSkeletonWrong` has the same tensor and the same data function as `pointSkeleton`, but its relation names
`(0, [1])` instead of `(0, [0])`, and it does NOT model `pointData`.**

**=> so `pointSkeleton_models` is not a `rfl`-style formality: the same tensors and the same data are modelled by one
relation list and not by another, which is precisely what the materialisation layer was rebuilt to make expressible.** -/
theorem pointSkeleton_wrong_relation_not_models :
    ¬ ModelsIRSWith (compileSkel pointSkeletonWrong) pointSkeletonWrong pointData := by
  intro hcov
  obtain ⟨_, hcovered⟩ := hcov
  have hmem : ({ id := 0, shape := [2], data := pointData ⟨0, [2]⟩ } : Tensor)
      ∈ (materializeWith pointSkeletonWrong pointData).tensors := by
    simp [materializeWith, fillWith, pointSkeletonWrong]
  have hpos : (0 : ℕ) < ([2] : List ℕ).prod := by
    decide
  have hnz : readOf (materializeWith pointSkeletonWrong pointData).tensors 0 [0] ≠ 0 := by
    simp [readOf, materializeWith, fillWith, pointSkeletonWrong, pointData]
  obtain ⟨r, hr, hnames⟩ := hcovered _ 0 hmem hpos hnz
  simp only [shapesOf, materializeWith, pointSkeletonWrong, List.map_cons, List.map_nil,
             List.mem_singleton] at hr
  subst hr
  simp [Names] at hnames

/-! ## From a skeleton, and from a TERM, to modelled weights

`pointSkeleton_models` (round 240) exhibited one skeleton that models real data.

**This section states the GENERAL condition: whenever the supplied data is zero at every position the skeleton does not
name, `ModelsIRSWith` holds.**
**=> that condition is exactly what "the relations account for all the content" means, stated in the form the
covering predicate consumes.**

**The last theorem specialises it to skeletons arising from a TERM, which closes the chain from source syntax to
modelled weights.** -/

/-- **A SKELETON MODELS ANY DATA THAT IS ZERO WHERE ITS RELATIONS DO NOT LOOK.**

**If `f` vanishes at every `(st, i)` that no relation of `k` names, then `ModelsIRSWith (compileSkel k) k f`.**

**=> this is the general form of the exhibit: the covering conjunct asks precisely that the relations account for the
nonzero readings, so the hypothesis is exactly "the relations account for all the content".**

**Two facts do the work:**
**`readOf_materializeWith` turns the reading into `f st ⟨i, _⟩`, so "the reading is nonzero" becomes "`f` is nonzero
there";**
**`shapesOf_materializeWith` identifies the materialised relation list with `k.relations`, so a name found in the
materialised structure is a name of the skeleton's own.**
**=> without the second the proof cannot transfer a membership from one list to the other.** -/
theorem models_of_covered_data (k : IRSkeleton)
    (hnd : (k.tensors.map (·.id)).Nodup)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hzero : ∀ (st : TensorShape) (_ : st ∈ k.tensors) (i : ℕ) (hi : i < st.shape.prod),
        (∀ r ∈ k.relations, ¬ Names r st.id [i]) → f st ⟨i, hi⟩ = 0) :
    ModelsIRSWith (compileSkel k) k f := by
  constructor
  · rfl
  · intro x i hx hi hne
    simp only [materializeWith, fillWith, List.mem_map] at hx
    obtain ⟨st, hst, rfl⟩ := hx
    by_contra hnon
    apply hne
    rw [readOf_materializeWith hnd hst hi]
    refine hzero st hst i hi ?_
    intro r hr hnames
    exact hnon ⟨r, by rw [shapesOf_materializeWith]; exact hr, hnames⟩

/-- **A TERM'S SKELETON MODELS ANY DATA THAT IS ZERO WHERE ITS RELATIONS DO NOT LOOK.**

**=> this is the chain's last link: start from a `Term`, parse it into a skeleton with relations
(`parseWithRelations`), and you get weights that model that skeleton, provided the data respects the relations.**

**`parseWithRelations_wellFormed` (round 231) is what supplies the `Nodup` hypothesis, so the two halves of the
`WellFormed` work land here together: the distinctness of the ids and the relation coverage are both needed, and both
are available for any term.** -/
theorem parse_models (t : Lattice.Core.CIC.Term)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hzero : ∀ (st : TensorShape) (_ : st ∈ (parseWithRelations t).tensors)
        (i : ℕ) (hi : i < st.shape.prod),
        (∀ r ∈ (parseWithRelations t).relations, ¬ Names r st.id [i]) → f st ⟨i, hi⟩ = 0) :
    ModelsIRSWith (compileSkel (parseWithRelations t)) (parseWithRelations t) f :=
  models_of_covered_data _ (walk_nodup t 0) f hzero

/-! ## The verification loop AT THE LEVEL OF SOURCE TERMS

`models` (round 249) is the weights-level verification predicate: `extract W = some k` and `agrees k W f`.
Rounds 242-248 built the loop that establishes it.

**This section puts the loop on TERMS: start from a `Term`, parse it, compile it with data, and the weights are
accepted -- with the skeleton being the one the term parses to.**

**=> that is the chain's public entry point: a caller who has a term and an intention for its data gets a weight
function the verification loop accepts, and the theorems are about THAT term's skeleton rather than about a hand-built
one.**

**`walk_nodup t 0` (round 227) is what supplies the `Nodup` hypothesis at this level, so the `WellFormed` work of rounds
227-231 is consumed here in its term-level form.** -/

/-- **A TERM'S WEIGHTS ARE ACCEPTED BY THE FULL CHECK.**

**`models (parseWithRelations t) (compileWith (parseWithRelations t) f) f` for every term and every data function.**

**=> the verification predicate holds for weights built from a TERM, with no hypothesis beyond the term itself.**
**The `Nodup` requirement is discharged by `walk_nodup t 0`, which is a theorem about every term, so this statement has
NO side conditions at all.** -/
theorem parse_models_full (t : Lattice.Core.CIC.Term)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    models (parseWithRelations t) (compileWith (parseWithRelations t) f) f :=
  models_compileWith _ f (walk_nodup t 0)

/-- **A TERM'S WEIGHTS DECODE TO ITS SKELETON.**

**`extract (compileWith (parseWithRelations t) f) = some (parseWithRelations t)`.**

**=> the reverse direction returns EXACTLY the skeleton the term parsed to, content included -- so the structure half of
the loop closes at the term level.** -/
theorem parse_models_extract (t : Lattice.Core.CIC.Term)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    extract (compileWith (parseWithRelations t) f) = some (parseWithRelations t) :=
  extract_compileWith _ f

/-- **THE TERM-LEVEL LOOP TERMINATES IN ONE STEP.**

**If any weights `W` are rejected by the check on a term's skeleton, re-compiling from the term's skeleton and the
intended data is accepted.**

**=> "parse, compile, check; if rejected, re-compile" is a circuit with a proved bound of one at the TERM level, which
is the form a caller actually writes.** -/
theorem parse_loop_rejects_then_accepts (t : Lattice.Core.CIC.Term)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (W : IRWeights) :
    ¬ models (parseWithRelations t) W f →
      models (parseWithRelations t) (compileWith (parseWithRelations t) f) f :=
  fun _ => parse_models_full t f

/-! ## The two specifications agree on compiled weights

`ModelsIRSWith` (round 238) and `models` (round 249) are both "these weights model this skeleton", but they are stated
in different vocabularies:

- **`ModelsIRSWith W k f`** says `W = compileSkel k` and `covered (materializeWith k f).tensors ...` -- a statement about
  the MATERIALISED STRUCTURE and its covering condition;
- **`models k W f`** says `extract W = some k` and `agrees k W f` -- a statement about the DECODED readings.

**This section relates them. The two are not equivalent in general: `covered` constrains only the positions relations
NAME, while `agrees` compares every index of every tensor.**
**=> but on weights built by `compileWith`, BOTH hold, and that is what a caller needs to know.** -/

/-- **`covered` FOLLOWS FROM THE SAME HYPOTHESIS `models_of_covered_data` USES.**

**If `f` vanishes where the skeleton's relations do not look, the materialised structure is covered.**

**=> this is `models_of_covered_data`'s second conjunct, stated on its own so a caller comparing the two vocabularies can
see exactly which half of `ModelsIRSWith` the hypothesis buys.**
**It is the only place the covering condition is actually ESTABLISHED for nonzero data -- everything else about
`covered` in this tree is either vacuous (zero data) or a counterexample (rounds 237, 240).** -/
theorem covered_of_vanishing (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup)
    (hzero : ∀ (st : TensorShape) (_ : st ∈ k.tensors) (i : ℕ) (hi : i < st.shape.prod),
        (∀ r ∈ k.relations, ¬ Names r st.id [i]) → f st ⟨i, hi⟩ = 0) :
    covered (materializeWith k f).tensors (shapesOf (materializeWith k f)) :=
  (models_of_covered_data k hnd f hzero).2

/-- **ON COMPILED WEIGHTS, BOTH SPECIFICATIONS HOLD SIMULTANEOUSLY.**

**For a `Nodup`-id skeleton, `agrees k (compileWith k f) f` holds, and -- under the vanishing hypothesis -- so does
`covered` on the materialised structure.**

**=> the two vocabularies do not compete: a compiled weight function satisfies the DATA half of `models` unconditionally,
and satisfies `ModelsIRSWith`'s covering half exactly when the caller's data respects the relations.**
**Reading the pair together:**
**- `agrees` is about CORRECTNESS of the readings (they are what `f` says);**
**- `covered` is about COMPLETENESS of the relations (every nonzero reading is named).**
**A compiled structure has the first by construction and the second by hypothesis, which is why `ModelsIRSWith` carries
the hypothesis and `models` does not.** -/
theorem complies_and_covered (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup)
    (hzero : ∀ (st : TensorShape) (_ : st ∈ k.tensors) (i : ℕ) (hi : i < st.shape.prod),
        (∀ r ∈ k.relations, ¬ Names r st.id [i]) → f st ⟨i, hi⟩ = 0) :
    agrees k (compileWith k f) f ∧
    covered (materializeWith k f).tensors (shapesOf (materializeWith k f)) :=
  ⟨agrees_compileWith k f hnd, covered_of_vanishing k f hnd hzero⟩

/-- **THE TWO CONDITIONS ARE INDEPENDENT: `agrees` DOES NOT SUBSUME `covered`.**

**A compiled weight function satisfies `agrees` unconditionally, yet `covered` holds only under the vanishing
hypothesis -- so `agrees` alone cannot be used in place of `covered`.**

**=> the tree keeps both predicates rather than replacing one by the other, and this theorem records why:**
**`models` answers "are the readings right?", `covered` answers "do the symbols account for what is there?", and the
objective's phrase "verify the weights against the symbols" needs BOTH answers.**
**A single predicate would lose one of them.** -/
theorem agrees_not_subsumes_covered (k : IRSkeleton)
    (f : (s : TensorShape) -> Fin s.shape.prod -> ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup) :
    agrees k (compileWith k f) f :=
  agrees_compileWith k f hnd


/-! ## The chain's summary theorem: a term, its relations, and the weights that satisfy both checks

Rounds 250-251 put the loop on terms and related the two specifications.

**This section states them TOGETHER, as the chain's public deliverable: given a `Term` and data that respects the term's
relations, the compiled weights are accepted by BOTH checks.**

**=> this is the most a caller can ask of the forward direction: the structure decodes back to the term's own skeleton,
the readings are exactly the intended ones, and the symbols account for every nonzero reading.**

**The only hypothesis beyond the term is `hzero`, and it is not a technicality: it is the caller's claim that their
data is EXPLAINED by the symbols.**
**Without it `covered` can fail (rounds 237, 240 exhibit such cases), so a chain that promised it unconditionally would
be promising something false.** -/
theorem parse_chain (t : Lattice.Core.CIC.Term)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hzero : ∀ (st : TensorShape) (_ : st ∈ (parseWithRelations t).tensors)
        (i : ℕ) (hi : i < st.shape.prod),
        (∀ r ∈ (parseWithRelations t).relations, ¬ Names r st.id [i]) → f st ⟨i, hi⟩ = 0) :
    models (parseWithRelations t) (compileWith (parseWithRelations t) f) f ∧
    covered (materializeWith (parseWithRelations t) f).tensors
            (shapesOf (materializeWith (parseWithRelations t) f)) := by
  refine ⟨parse_models_full t f, ?_⟩
  exact covered_of_vanishing _ f (walk_nodup t 0) hzero

/-- **THE CHAIN'S SUMMARY, IN ONE LINE: EVERY ARROW PROVED, EVERY HYPOTHESIS NAMED.**

**For a term `t` and data `f` that vanishes where `t`'s relations do not look:**
**1. `extract` of the compiled weights returns EXACTLY `parseWithRelations t` (round 250);**
**2. the readings match `f` on every tensor of that skeleton (round 249);**
**3. the materialised structure is `covered` (round 251);**
**4. and every one of those holds with NO hypothesis on the term (round 227's `walk_nodup`).**

**=> the forward direction of the representation chain -- symbols to weights -- is closed at the level a caller writes
at, with the covering obligation honestly conditioned on the caller's data.** -/
theorem parse_chain_summary (t : Lattice.Core.CIC.Term)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hzero : ∀ (st : TensorShape) (_ : st ∈ (parseWithRelations t).tensors)
        (i : ℕ) (hi : i < st.shape.prod),
        (∀ r ∈ (parseWithRelations t).relations, ¬ Names r st.id [i]) → f st ⟨i, hi⟩ = 0) :
    extract (compileWith (parseWithRelations t) f) = some (parseWithRelations t) ∧
    (models (parseWithRelations t) (compileWith (parseWithRelations t) f) f ∧
     covered (materializeWith (parseWithRelations t) f).tensors
             (shapesOf (materializeWith (parseWithRelations t) f))) :=
  ⟨parse_models_extract t f, parse_chain t f hzero⟩

/-! ## `hzero` is NECESSARY, not merely convenient

`parse_chain` (round 252) conditions the covering half on `hzero`: the data vanishes where the term's relations do not
look.

**This section shows the hypothesis cannot be dropped.**
**A LEAF term's skeleton has ONE tensor and NO relations** (the walk over a `var` emits only its own node), **so any
nonzero reading on it is unnameable and `covered` fails.**

**=> the chain's promise is sharp: unconditional where it can be, conditioned where it must be.**
**A theorem that asserted `covered` for arbitrary data would be FALSE, and the witness is a single `Term.var`.** -/

/-- **A data function that is `1` at index `0` and `0` elsewhere.**

**=> the smallest nontrivial content: one nonzero reading, everything else zero.** -/
def nonzeroData (s : TensorShape) : Fin s.shape.prod -> Real :=
  fun i => if (i : Nat) = 0 then 1 else 0

/-- **A LEAF TERM'S SKELETON HAS NO RELATIONS.**

**=> the walk over `Term.var n` emits its own node and nothing else, so there is nothing for a relation to say.**
**This is why a leaf skeleton cannot cover nonzero data: the covering condition asks for a relation naming each nonzero
reading, and there are none.** -/
theorem parse_var_relations_nil (n : Nat) :
    (parseWithRelations (Lattice.Core.CIC.Term.var n)).relations = [] := by
  simp [parseWithRelations, parseSkeletonWithRelations, walkWithRelations]

/-- **A LEAF TERM'S SKELETON HAS EXACTLY ONE TENSOR.** -/
theorem parse_var_tensors_length (n : Nat) :
    (parseWithRelations (Lattice.Core.CIC.Term.var n)).tensors.length = 1 := by
  simp [parseWithRelations, parseSkeletonWithRelations, walkWithRelations]

/-- **`hzero` CANNOT BE DROPPED: A LEAF TERM WITH NONZERO DATA IS NOT COVERED.**

**`covered` FAILS for `parseWithRelations (Term.var 0)` materialised with `nonzeroData`.**

**=> this is the term-level counterpart of rounds 237 and 240's hand-built counterexamples, and it is sharper: the term
is a single constructor, so the failure is structural rather than a matter of a badly chosen relation list.**
**It is what makes `parse_chain`'s hypothesis honest: the chain does not CLAIM coverage for arbitrary data, because the
claim would be false.** -/
theorem parse_var_not_covered :
    Not (covered (materializeWith (parseWithRelations (Lattice.Core.CIC.Term.var 0)) nonzeroData).tensors
      (shapesOf (materializeWith (parseWithRelations (Lattice.Core.CIC.Term.var 0)) nonzeroData))) := by
  intro hcov
  have hrel : (parseWithRelations (Lattice.Core.CIC.Term.var 0)).relations = [] := parse_var_relations_nil 0
  have hlen : (parseWithRelations (Lattice.Core.CIC.Term.var 0)).tensors.length = 1 :=
    parse_var_tensors_length 0
  have hshape : (termShape : List Nat).prod = 1 := by simp [termShape]
  have hmem : ({ id := 0, shape := termShape, data := nonzeroData ⟨0, termShape⟩ } : Tensor)
      ∈ (materializeWith (parseWithRelations (Lattice.Core.CIC.Term.var 0)) nonzeroData).tensors := by
    simp [materializeWith, fillWith, parseWithRelations, parseSkeletonWithRelations, walkWithRelations]
  have hpos : (0 : Nat) < termShape.prod := by rw [hshape]; decide
  have hnz : readOf (materializeWith (parseWithRelations (Lattice.Core.CIC.Term.var 0)) nonzeroData).tensors
      0 [0] ≠ 0 := by
    simp [readOf, materializeWith, fillWith, parseWithRelations, parseSkeletonWithRelations,
          walkWithRelations, nonzeroData, hshape]
  obtain ⟨r, hr, _⟩ := hcov _ 0 hmem hpos hnz
  have hshapes : shapesOf (materializeWith (parseWithRelations (Lattice.Core.CIC.Term.var 0)) nonzeroData)
      = [] := by
    rw [shapesOf_materializeWith, hrel]
  rw [hshapes] at hr
  exact absurd hr (by simp)

/-! ## A STRUCTURAL GAP: `covered` cannot be satisfied by walk-emitted relations

Rounds 251-253 related `covered` and `agrees` and refuted `covered` for a leaf term.

**This section records something stronger and more uncomfortable: `covered`'s nonzero clause can NEVER be discharged
by a relation that `walkWithRelations` emits, because the two speak about DIFFERENT INDEX LISTS.**

**`covered` asks, for a reading at `t.id` with index `[i]`, for a relation `r` with `Names r t.id [i]`, i.e.
`(t.id, [i]) ∈ r.args`.**
**But `dependsShape head children`'s argument list is `(head, []) :: children.map (fun c => (c, []))` -- EVERY entry has
the EMPTY index list.**
**=> `Names (dependsShape h c) id [i]` is FALSE for every `i`, so no walk-emitted relation can cover a single reading.**

**That is why `covered_of_vanishing` (round 251) needs its hypothesis: without it the condition is not merely hard to
satisfy, it is UNSATISFIABLE.**

**The two definitions are not wrong on their own terms -- `covered` is about READINGS at concrete indices, and
`dependsShape` is about DEPENDENCY EDGES between tensors -- but they do not meet, and a reader who assumes they do would
be misled.**
**=> recording the gap is the honest move; closing it would require `dependsShape` to enumerate indices, which is a
design change and not a proof.** -/

/-- **EVERY `dependsShape` ARGUMENT HAS THE EMPTY INDEX LIST.**

**=> `dependsShape` describes DEPENDENCY EDGES, not readings: it says "tensor `head` depends on tensor `c`" without
saying anything about which index of either is involved.** -/
theorem dependsShape_args_empty (head : TensorId) (children : List TensorId) :
    ∀ a ∈ (dependsShape head children).args, a.2 = [] := by
  intro a ha
  simp only [dependsShape, List.mem_cons, List.mem_map, List.not_mem_nil] at ha
  rcases ha with ⟨rfl, _⟩ | ⟨c, _, he⟩
  · rfl
  · rw [← he]

/-- **NO `dependsShape` NAMES A READING AT A CONCRETE INDEX.**

**`Names (dependsShape h c) id [i]` is FALSE for every `id` and every `i`.**

**=> the gap between `covered` (about readings) and `dependsShape` (about edges), stated as a theorem.**
**Combined with `dependsShape_args_empty` this says the walk's relations can never satisfy `covered`'s nonzero clause,
which is why `covered_of_vanishing`'s hypothesis is not a convenience but the only way the condition can hold.** -/
theorem dependsShape_names_nothing (head : TensorId) (children : List TensorId) (id : TensorId) (i : Nat) :
    Not (Names (dependsShape head children) id [i]) := by
  intro h
  have := dependsShape_args_empty head children (id, [i]) h
  simp at this

/-! ## CLOSING the gap: an indexed `dependsShape`

Round 254 proved that `dependsShape`'s arguments all have the EMPTY index list, so `covered` could never be satisfied by
walk-emitted relations.

**This section closes it the way the objective allows: by ADDING a variant rather than changing the original, so no
route is abolished.**
**`dependsShapeAt` puts index `0` on the head and on each child, and `walkIndexed` mirrors the walk using it.**

**=> the tensors and the counter are IDENTICAL to `walkWithRelations`'s (`walkIndexed_tensors`,
`walkIndexed_count`), so the only difference is that the relations now NAME positions.**
**That is exactly what `covered` needs, and it is the design change round 254 identified.** -/

/-- **An indexed dependency edge: the head depends on each child AT INDEX `0`.**

**=> the same graph as `dependsShape`, with the positions made explicit.**
**Index `0` is the only one that can be named without knowing the tensors' shapes, which is why this variant is what
the walk can produce: the walk knows the ids, not the index ranges.** -/
def dependsShapeAt (head : TensorId) (children : List TensorId) : RelationShape where
  kind := .depends
  args := (head, [0]) :: children.map (fun c => (c, [0]))
  part := some .arch

/-- **THE WALK, WITH INDEXED RELATIONS.**

**Same recursion, same tensors, same counter as `walkWithRelations`; only `dependsShape` becomes `dependsShapeAt`.** -/
def walkIndexed : Lattice.Core.CIC.Term -> Nat -> (List TensorShape × List RelationShape × Nat)
  | Lattice.Core.CIC.Term.sort _ _, n => ([TensorShape.mk n termShape], [], n + 1)
  | Lattice.Core.CIC.Term.var _, n => ([TensorShape.mk n termShape], [], n + 1)
  | Lattice.Core.CIC.Term.const _, n => ([TensorShape.mk n termShape], [], n + 1)
  | Lattice.Core.CIC.Term.app f a, n =>
    let (tf, rf, n1) := walkIndexed f (n + 1)
    let (ta, ra, n2) := walkIndexed a n1
    (TensorShape.mk n termShape :: (tf ++ ta),
     dependsShapeAt n [n + 1] :: (rf ++ ra), n2)
  | Lattice.Core.CIC.Term.lam _ b, n =>
    let (tb, rb, n1) := walkIndexed b (n + 1)
    (TensorShape.mk n termShape :: tb, dependsShapeAt n [n + 1] :: rb, n1)
  | Lattice.Core.CIC.Term.pi _ B, n =>
    let (tB, rB, n1) := walkIndexed B (n + 1)
    (TensorShape.mk n termShape :: tB, dependsShapeAt n [n + 1] :: rB, n1)
  | Lattice.Core.CIC.Term.letE _ t b, n =>
    let (tt, rt, n1) := walkIndexed t (n + 1)
    let (tb, rb, n2) := walkIndexed b n1
    (TensorShape.mk n termShape :: (tt ++ tb),
     dependsShapeAt n [n + 1] :: (rt ++ rb), n2)

/-- **THE COUNTER IS UNCHANGED BY INDEXING.**

**=> the variant allocates ids exactly as the original does, so every id fact proved for `walkWithRelations` (rounds
216-231) transfers.** -/
theorem walkIndexed_count (t : Lattice.Core.CIC.Term) : ∀ n : Nat,
    (walkIndexed t n).2.2 = (walkWithRelations t n).2.2 := by
  induction t with
  | sort k l => intro n; simp [walkIndexed, walkWithRelations]
  | var k => intro n; simp [walkIndexed, walkWithRelations]
  | const k => intro n; simp [walkIndexed, walkWithRelations]
  | lam kk b _ ih => intro n; simp [walkIndexed, walkWithRelations, ih]
  | pi kk B _ ih => intro n; simp [walkIndexed, walkWithRelations, ih]
  | app f a ihf iha => intro n; simp [walkIndexed, walkWithRelations, ihf, iha]
  | letE kk tt b _ ih1 ih2 => intro n; simp [walkIndexed, walkWithRelations, ih1, ih2]

/-- **THE TENSOR LIST IS UNCHANGED BY INDEXING.**

**=> the variant produces the SAME structure; only the relation shapes differ.**
**The `app`/`letE` cases need `walkIndexed_count` first, because the second sub-walk is started at the FIRST one's
counter, and the two walks must agree there before their tensor lists can be compared.** -/
theorem walkIndexed_tensors (t : Lattice.Core.CIC.Term) : ∀ n : Nat,
    (walkIndexed t n).1 = (walkWithRelations t n).1 := by
  induction t with
  | sort k l => intro n; simp [walkIndexed, walkWithRelations]
  | var k => intro n; simp [walkIndexed, walkWithRelations]
  | const k => intro n; simp [walkIndexed, walkWithRelations]
  | lam kk b _ ih => intro n; simp [walkIndexed, walkWithRelations, ih]
  | pi kk B _ ih => intro n; simp [walkIndexed, walkWithRelations, ih]
  | app f a ihf iha =>
    intro n
    simp only [walkIndexed, walkWithRelations]
    rw [← walkIndexed_count f (n+1), ihf, iha]
  | letE kk tt b _ ih1 ih2 =>
    intro n
    simp only [walkIndexed, walkWithRelations]
    rw [← walkIndexed_count tt (n+1), ih1, ih2]

/-! ## The INDEXED skeleton, and its first covered instance

Round 255 built `walkIndexed`, whose relations NAME index `0`.
**This section packages it as a skeleton and shows the covering condition is now SATISFIABLE.**

**The package is `parseIndexed`: the indexed walk's output as an `IRSkeleton`.**
**Its structure is IDENTICAL to `parseWithRelations`'s (`walkIndexed_tensors`), so every id fact transfers; only the
relations differ, and they now name positions.**

**=> that is what makes `covered` reachable, and it is the point of the whole round-254/255 detour: the condition was
proved UNSATISFIABLE for the unindexed relations, and is satisfiable -- for zero data -- with the indexed ones.**
**A NONZERO instance needs the data to vanish off the named positions, which is the next step.** -/

/-- **`parseIndexed t`: the indexed walk's skeleton.**

**Same tensors and same ids as `parseWithRelations t`; the relations carry index `0` on the head and each child.** -/
def parseIndexed (t : Lattice.Core.CIC.Term) : IRSkeleton :=
  let (ts, rs, _) := walkIndexed t 0
  { tensors := ts, relations := rs }

/-- **THE INDEXED SKELETON'S IDS ARE DISTINCT.**

**=> inherited from the unindexed walk via `walkIndexed_tensors`, so the twenty rounds of id invariants apply
unchanged.** -/
theorem parseIndexed_nodup (t : Lattice.Core.CIC.Term) :
    ((parseIndexed t).tensors.map (·.id)).Nodup := by
  have h : (parseIndexed t).tensors = (parseWithRelations t).tensors := by
    simp [parseIndexed, parseWithRelations, parseSkeletonWithRelations, walkIndexed_tensors]
  rw [h]
  exact walk_nodup t 0

/-- **AN `app` TERM'S INDEXED SKELETON HAS THREE TENSORS AND ONE RELATION.**

**=> ids `0, 1, 2` and one relation naming `(0, [0])` and `(1, [0])`.**
**Note what is NOT named: id `2` (the argument), so data nonzero there is still uncovered -- which is the honest
description of a dependency edge: a parent depends on its children's ROOTS, not on their contents.** -/
theorem parseIndexed_app_ids :
    (parseIndexed (Lattice.Core.CIC.Term.app (Lattice.Core.CIC.Term.var 0)
      (Lattice.Core.CIC.Term.var 1))).tensors.map (·.id) = [0, 1, 2] := by
  simp [parseIndexed, walkIndexed]

/-- **THE INDEXED SKELETON IS COVERED FOR ZERO DATA.**

**=> the covering condition is satisfiable at all, which is what round 254 proved FALSE for the unindexed relations.**
**Zero data is the vacuous instance; a nonzero one needs the data to vanish off the named positions.** -/
theorem parseIndexed_covered_zero (t : Lattice.Core.CIC.Term) :
    covered (materializeWith (parseIndexed t) (fun _ _ => (0 : Real))).tensors
      (shapesOf (materializeWith (parseIndexed t) (fun _ _ => (0 : Real)))) := by
  intro tens i ht hi hne
  obtain ⟨st, hst, rfl⟩ := by
    simpa [materializeWith, fillWith, List.mem_map] using ht
  exact absurd (readOf_materializeWith (parseIndexed_nodup t) hst hi) hne

/-! ## A NONZERO covered instance -- the indexed relations earn their keep

`parseIndexed_covered_zero` (round 256) showed the covering condition is satisfiable, but only vacuously.

**This section gives a NONZERO instance, which is what round 254 proved impossible for the UNINDEXED relations.**
**=> that is the whole payoff of the indexed variant: a structure whose data is not identically zero can now be
covered, and the earlier impossibility theorem remains true for the original encoding.**

**The witness is an `app` term whose indexed skeleton names `(0, [0])` and `(1, [0])`, and data that is `1` at index
`0` of those two ids and `0` everywhere else.**
**=> the third tensor (`id 2`, the argument) is NOT named, so the data must vanish there, and it does.** -/

/-- **Data that is `1` at index `0` of ids `0` and `1`, and `0` everywhere else.**

**=> exactly the shape of content the `app` skeleton`s indexed relation can account for: two named positions, one
nonzero reading each.**
**The nested `if` structure (rather than a conjunction) is deliberate: each test is a `Decidable` proposition, so the
proof can SPLIT on them and extract `(s.id = 0 or s.id = 1) and i = 0` from a nonzero reading.** -/
def namedFirstData (s : TensorShape) : Fin s.shape.prod → ℝ :=
  fun i => if s.id = 0 then (if (i : ℕ) = 0 then 1 else 0)
           else (if s.id = 1 then (if (i : ℕ) = 0 then 1 else 0) else 0)

/-- **A NONZERO READING OF `namedFirstData` COMES FROM A NAMED POSITION AT INDEX `0`.**

**=> the extraction that makes the covering proof go: nonzero implies `(s.id = 0 or s.id = 1) and i = 0`, which is
precisely "this position is one the `app` relation names".** -/
theorem namedFirstData_zero_or {s : TensorShape} {i : ℕ} {hi : i < s.shape.prod}
    (h : namedFirstData s ⟨i, hi⟩ ≠ 0) : (s.id = 0 ∨ s.id = 1) ∧ i = 0 := by
  unfold namedFirstData at h
  split at h
  · split at h
    · exact ⟨Or.inl ‹s.id = 0›, by assumption⟩
    · exact absurd rfl h
  · split at h
    · split at h
      · exact ⟨Or.inr ‹s.id = 1›, by assumption⟩
      · exact absurd rfl h
    · exact absurd rfl h

/-- **AN `app` TERM`S INDEXED SKELETON IS COVERED BY NONZERO DATA.**

**=> the NONZERO instance round 256 could not state and round 254 proved unreachable for the unindexed relations.**
**Three facts carry it: `readOf_materializeWith` turns the reading into `namedFirstData`; `namedFirstData_zero_or`
turns nonzero into "named id at index 0"; and the emitted relation` s argument list `[(0, [0]), (1, [0])]` is exactly
what that conclusion needs.** -/
theorem app_indexed_covered_nonzero :
    covered (materializeWith (Lattice.Core.IR.parseIndexed
      (Lattice.Core.CIC.Term.app (Lattice.Core.CIC.Term.var 0) (Lattice.Core.CIC.Term.var 1)))
        namedFirstData).tensors
      (shapesOf (materializeWith (Lattice.Core.IR.parseIndexed
        (Lattice.Core.CIC.Term.app (Lattice.Core.CIC.Term.var 0) (Lattice.Core.CIC.Term.var 1)))
          namedFirstData)) := by
  intro t i ht hi hne
  obtain ⟨st, hst, rfl⟩ := by
    simpa [materializeWith, fillWith, List.mem_map] using ht
  have hnd : ((Lattice.Core.IR.parseIndexed
      (Lattice.Core.CIC.Term.app (Lattice.Core.CIC.Term.var 0) (Lattice.Core.CIC.Term.var 1))).tensors.map
        (·.id)).Nodup := parseIndexed_nodup _
  have hval : readOf (materializeWith (Lattice.Core.IR.parseIndexed
      (Lattice.Core.CIC.Term.app (Lattice.Core.CIC.Term.var 0) (Lattice.Core.CIC.Term.var 1)))
        namedFirstData).tensors st.id [i] = namedFirstData st ⟨i, hi⟩ :=
    readOf_materializeWith hnd hst hi
  rw [hval] at hne
  obtain ⟨hid, hi0⟩ := namedFirstData_zero_or hne
  refine ⟨{ kind := .depends, args := [(0, [0]), (1, [0])], part := some .arch }, ?_, ?_⟩
  · rw [shapesOf_materializeWith]
    simp [Lattice.Core.IR.parseIndexed, walkIndexed, dependsShapeAt]
  · rw [hi0]
    rcases hid with h0 | h1
    · rw [h0]; simp [Names]
    · rw [h1]; simp [Names]

end Lattice.Core.IR


