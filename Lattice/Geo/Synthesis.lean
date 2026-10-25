import Mathlib
import Lattice.Geo.Invariant
import Lattice.Geo.Initialise

/-!
# `Lattice.Geo.Synthesis` -- executable sample generation from a constraint

## What was missing

`Lattice.Geo.Invariant` proved that translation and positive scaling preserve several geometric constraints, and
`Lattice.Geo.Initialise` produced a satisfying configuration without searching. Both are *facts*; neither is a
generator. The objective asks for **data synthesis** among the three forward paths, and a fact about
invariance only becomes synthesis when it is turned into a list of samples.

This file builds that list and proves every element of it satisfying.

## The shape, and why it is the right one

```
seed configuration  ──transformations──>  list of configurations, all satisfying
       ▲
       └── supplied by `Lattice.Geo.Initialise`
```

A transformation family is finite -- we can only write down finitely many -- so the generator produces a
finite list. That is honest: `samples` is not a stream and does not pretend to enumerate the orbit. What it
does provide is that **each sample is certified**, which is the property a training set needs and the one a
hand-written fixture does not have.

## The limit worth stating

Samples along one orbit are highly correlated: they are all translates or scalings of one seed. Genuine
diversity needs *several seeds*, and producing those is the initialisation path's job, not this file's. So the
two paths are complementary rather than redundant -- initialisation supplies the seeds, synthesis amplifies
each into a certified family.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- Translation by a fixed vector, as an endomap of configuration space -- so it can appear in a list. -/
noncomputable def translateBy (t : Pt n) : (ℕ → Pt n) → (ℕ → Pt n) := fun pts => translate t pts

/-- Scaling by a fixed factor, as an endomap of configuration space. -/
noncomputable def scaleBy (s : ℝ) : (ℕ → Pt n) → (ℕ → Pt n) := fun pts => scale s pts

/-- **A sample family generated from a seed** by applying each transformation. -/
noncomputable def samples (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n) :
    List (ℕ → Pt n) := Ts.map (fun T => T seed)

/-- **Every generated sample satisfies the constraint**, provided the transformations preserve it and the seed
does.

This is the theorem that makes `samples` a *certified* training set rather than a list of guesses: the
preservation laws of `Lattice.Geo.Invariant` are exactly the hypothesis `hT`. -/
theorem samples_sound (c : GeoConstraint n) (Ts : List ((ℕ → Pt n) → (ℕ → Pt n)))
    (seed : ℕ → Pt n)
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseed : GeoConstraint.Holds c seed) :
    ∀ s ∈ samples Ts seed, GeoConstraint.Holds c s := by
  intro s hs
  unfold samples at hs
  obtain ⟨T, hTmem, rfl⟩ := List.mem_map.mp hs
  exact hT T hTmem seed hseed

/-- The identity transformation, so that a family always includes its own seed. -/
noncomputable def idT : (ℕ → Pt n) → (ℕ → Pt n) := id

/-- It preserves everything, trivially. -/
theorem idT_preserves (c : GeoConstraint n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds c pts) : GeoConstraint.Holds c (idT pts) := h

/-- **A standard family**: the seed itself, three translations, and two scalings.

Small on purpose. The family's size is not the point -- certification is -- and each element additionally
needs its own preservation proof to enter, which is what keeps the list from growing for free.
-/
noncomputable def standardFamily : List ((ℕ → Pt n) → (ℕ → Pt n)) :=
  [idT, translateBy (fun _ => 1), translateBy (fun i => (i : ℝ)),
   scaleBy 2, scaleBy 3]

/-- **A single transformation preserves perpendicularity.** This is the shape `samples_sound` consumes: a
statement quantified over all configurations, not over a fixed one. -/
theorem perpTransform_preserves (a b c e : ℕ) (T : (ℕ → Pt n) → (ℕ → Pt n))
    (hT : T = idT ∨ T = translateBy (fun _ => 1) ∨ T = translateBy (fun i => (i : ℝ))
      ∨ T = scaleBy 2 ∨ T = scaleBy 3) :
    ∀ pts, GeoConstraint.Holds (.perpendicular a b c e) pts →
      GeoConstraint.Holds (.perpendicular a b c e) (T pts) := by
  intro pts h
  rcases hT with rfl | rfl | rfl | rfl | rfl
  · exact h
  · exact perpendicular_translate a b c e _ pts h
  · exact perpendicular_translate a b c e _ pts h
  · exact perpendicular_scale a b c e 2 pts h
  · exact perpendicular_scale a b c e 3 pts h

/-- **Every member of the standard family preserves perpendicularity**, in the quantified form
`samples_sound` needs. -/
theorem standardFamily_preserves_perpendicular (a b c e : ℕ)
    (T : (ℕ → Pt n) → (ℕ → Pt n)) (hT : T ∈ standardFamily) :
    ∀ pts, GeoConstraint.Holds (.perpendicular a b c e) pts →
      GeoConstraint.Holds (.perpendicular a b c e) (T pts) := by
  apply perpTransform_preserves a b c e T
  simp only [standardFamily, List.mem_cons, List.not_mem_nil, or_false] at hT
  exact hT

/-- **Data synthesis, end to end, for perpendicularity.**

Starting from any satisfying configuration, the standard family yields five certified samples. This is the
composite of the two forward paths that previously sat apart: `Lattice.Geo.Invariant` supplies preservation, this
file supplies the enumeration, and the conclusion is about a *list* -- which is what training consumes. -/
theorem synthesize_perpendicular_samples (a b c e : ℕ) (seed : ℕ → Pt n)
    (hseed : GeoConstraint.Holds (.perpendicular a b c e) seed) :
    ∀ s ∈ samples standardFamily seed, GeoConstraint.Holds (.perpendicular a b c e) s :=
  samples_sound (.perpendicular a b c e) standardFamily seed
    (standardFamily_preserves_perpendicular a b c e) hseed

/-- **The seed supplied by initialisation is a valid starting point.** `Lattice.Geo.Initialise` produces a
configuration satisfying the linear layers; here that fact is used to obtain a nonempty sample family, closing
the initialisation-to-synthesis path. -/
theorem synthesize_from_initialisation (G : List (GeoConstraint n))
    (h : ∀ c ∈ G, ∃ a b : ℕ, c = .samePoint a b) (a b : ℕ) :
    ∃ seed : ℕ → Pt n, ∀ s ∈ samples standardFamily seed,
      GeoConstraint.Holds (.samePoint a b) s := by
  refine ⟨allSame, ?_⟩
  exact samples_sound (.samePoint a b) standardFamily allSame
    (by
      intro T hT pts hpts
      simp only [standardFamily, List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl
      · exact hpts
      · exact samePoint_translate a b _ pts hpts
      · exact samePoint_translate a b _ pts hpts
      · exact samePoint_scale a b 2 pts hpts
      · exact samePoint_scale a b 3 pts hpts)
    (allSame_samePoint a b)

end Lattice.Geo
