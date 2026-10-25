import Mathlib
import Lattice.Geo.Invariant
import Lattice.Geo.Extract

/-!
# `Lattice.Geo.Semantic` -- the semantic layer is not invertible, in general

## The layered statement the objective requires

> 可逆性必须分层陈述：对象层已证双射，语义层已机器验证不可逆

The object layer is settled: `Lattice.Geo.Flatten.flatten` is a bijection and both round-trips are `simp`
lemmas. This file supplies the semantic half **as a general theorem**, replacing the single instance in
`Lattice.Geo.Extract` (`perp_neg_iff`, which spoke only about perpendicularity under negation).

## What "the semantic layer" means here

Not the configuration, but the constraint set a configuration satisfies:

```
semantics : (ℕ → Pt n) → Set (GeoConstraint n)
semantics pts := { c | Holds c pts }
```

The object layer's map is injective. This one is not, and the reason is structural rather than incidental:
**a configuration and its translate satisfy exactly the same translation-invariant constraints.** A geometry
built out of displacements cannot see where the whole figure sits.

## The boundary, stated rather than glossed

Translation invariance is *not* a property of every constraint in `GeoConstraint`. Four constructors take a
`GeoExpr` evaluated at absolute coordinates (`eqZero`, `leZero`, `ltZero`, `gtZero`), and an expression may
mention `coord p axis`, so those constraints can detect translation. `Translatable` below names exactly the
constructors that cannot, and the general theorem is stated for those.

This is the honest form: a blanket claim "no geometric constraint sees translation" would be false and
provable-looking. The four exceptions are not defects -- they are how a user says "this point is at the
origin", which is precisely a statement about absolute position.
-/

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

variable {n : ℕ}

/-- **The constraints that are stated through displacements**, hence cannot see where the figure sits.

Seven of the twelve constructors qualify. The five excluded ones all mention a `GeoExpr`:
`eqZero`, `leZero`, `ltZero`, `gtZero` take one directly, and `sqDistEq` takes one as the right-hand side.
A `GeoExpr` may contain `coord p axis`, whose value changes under translation, so those constraints *can*
detect where the figure sits -- which is exactly what a user means by writing "this point is at the
origin".

`equalLength` is included while `sqDistEq` is not, even though both mention distances: `equalLength`
compares two squared distances, and translation moves both by the same amount, whereas `sqDistEq` compares a
squared distance against an arbitrary expression.
-/
def Translatable : GeoConstraint n → Prop
  | .eqZero _ => False
  | .leZero _ => False
  | .ltZero _ => False
  | .gtZero _ => False
  | .sqDistEq _ _ _ => False
  | .equalLength _ _ _ _ => True
  | .collinear _ _ _ => True
  | .perpendicular _ _ _ _ => True
  | .parallel _ _ _ _ => True
  | .rightAngle _ _ _ => True
  | .midpoint _ _ _ => True
  | .samePoint _ _ => True

/-- **Translation does not change a squared distance.** The displacement is what `sqDist` reads. -/
theorem sqDist_translate (t : Pt n) (pts : ℕ → Pt n) (p q : ℕ) :
    sqDist (n := n) (translate t pts p) (translate t pts q) = sqDist (n := n) (pts p) (pts q) := by
  unfold sqDist sqNorm diff translate
  congr 1
  funext i
  ring

/-- **A translatable constraint, once satisfied, stays satisfied under translation.**

One direction is all the semantic non-invertibility needs: it says the constraint cannot distinguish a
configuration from its translate, which is exactly the information loss. Stating it as an implication rather
than an equivalence also keeps every case a direct citation of an `Lattice.Geo.Invariant` lemma.
-/
theorem holds_translate_of_translatable (c : GeoConstraint n) (h : Translatable c)
    (t : Pt n) (pts : ℕ → Pt n) :
    GeoConstraint.Holds c pts → GeoConstraint.Holds c (translate t pts) := by
  match c with
  | .equalLength a b c' e =>
    show GeoConstraint.Holds (.equalLength a b c' e) pts →
      GeoConstraint.Holds (.equalLength a b c' e) (translate t pts)
    intro hp
    show sqDist (n := n) (translate t pts a) (translate t pts b)
        = sqDist (n := n) (translate t pts c') (translate t pts e)
    rw [sqDist_translate t pts a b, sqDist_translate t pts c' e]
    exact hp
  | .collinear a b c' => exact collinear_translate a b c' t pts
  | .perpendicular a b c' e => exact perpendicular_translate a b c' e t pts
  | .parallel a b c' e => exact parallel_translate a b c' e t pts
  | .rightAngle a b c' => exact rightAngle_translate a b c' t pts
  | .midpoint m a b => exact midpoint_translate m a b t pts
  | .samePoint a b => exact samePoint_translate a b t pts
  | .eqZero e => exact absurd h (by simp [Translatable])
  | .leZero e => exact absurd h (by simp [Translatable])
  | .ltZero e => exact absurd h (by simp [Translatable])
  | .gtZero e => exact absurd h (by simp [Translatable])

/-! ## The semantic layer is not invertible -/

/-- **A non-zero translation moves any configuration.** The object layer distinguishes the two, so if the
semantic layer does not, the latter is not injective. -/
theorem translate_ne_self (t : Pt n) (hne : ∃ i : Fin n, t i ≠ 0) (pts : ℕ → Pt n) :
    translate t pts ≠ pts := by
  intro h
  obtain ⟨i, hi⟩ := hne
  apply hi
  have hp : translate t pts 0 i = pts 0 i := by rw [h]
  unfold translate at hp
  linarith [hp]

/-- **Translation can be undone.** The inverse of `translate t` is `translate (-t)`, which is what lets the
invariance direction be upgraded to an equivalence.

Written with `simp only [translate]` first because the term is a *nested* application: `translate (-t)
(translate t pts) p i` needs the inner lambda beta-reduced before `ring` can see a linear expression in
`t i`. An earlier attempt unfolded both at once and left a redex, which is the same obstruction recorded in
`_archive` for `fixPerp`.
-/
theorem translate_neg (t : Pt n) (pts : ℕ → Pt n) :
    translate (-t) (translate t pts) = pts := by
  funext p i
  show pts p i + t i + -t i = pts p i
  ring

/-- **A translatable constraint is satisfied by a configuration exactly when it is satisfied by any
translate.** The forward direction is `holds_translate_of_translatable`; the reverse composes it with
`translate_neg`.

With this, translation is a **non-trivial action on configurations that is the identity on the semantic
layer** -- the precise form of the objective's "semantic layer is not invertible".
-/
theorem holds_translate_iff_of_translatable (c : GeoConstraint n) (h : Translatable c)
    (t : Pt n) (pts : ℕ → Pt n) :
    GeoConstraint.Holds c pts ↔ GeoConstraint.Holds c (translate t pts) := by
  refine ⟨fun hp => holds_translate_of_translatable c h t pts hp, ?_⟩
  intro hp
  have hback := holds_translate_of_translatable c h (-t) (translate t pts) hp
  rwa [translate_neg] at hback

/-- **The semantic layer loses information: a configuration and its translate satisfy every translatable
constraint alike.**

`flatten` is a bijection, so the two configurations are *different objects*; `holds_translate_of_translatable`
says no translatable constraint can tell them apart. Therefore the map from a configuration to the set of
constraints it satisfies is not injective -- the objective's "semantic layer is not invertible", at the level
of a general theorem rather than one instance.

`Lattice.Geo.Extract.perp_neg_iff` was the earlier, single-constraint form of this; it is a consequence of
nothing here, but both say the same thing about one construction: the semantic layer quotients configurations.
-/
theorem semantic_not_injective (t : Pt n) (hne : ∃ i : Fin n, t i ≠ 0) (pts : ℕ → Pt n) :
    translate t pts ≠ pts ∧
      ∀ c : GeoConstraint n, Translatable c →
        (GeoConstraint.Holds c pts ↔ GeoConstraint.Holds c (translate t pts)) :=
  ⟨translate_ne_self t hne pts,
   fun c hc => holds_translate_iff_of_translatable c hc t pts⟩

/-- **The invariance direction, restated as the quotient statement.** A set of translatable constraints
satisfied by `pts` is satisfied by every translate of `pts`. -/
theorem models_translate (G : List (GeoConstraint n))
    (hG : ∀ c ∈ G, Translatable c) (t : Pt n) (pts : ℕ → Pt n)
    (h : ∀ c ∈ G, GeoConstraint.Holds c pts) :
    ∀ c ∈ G, GeoConstraint.Holds c (translate t pts) :=
  fun c hc => holds_translate_of_translatable c (hG c hc) t pts (h c hc)

end Lattice.Geo
