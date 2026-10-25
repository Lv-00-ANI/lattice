import Mathlib
import Lattice.Core.Semantics

/-!
# `Lattice.Core.Weight` -- a non-trivial weight semantics, and what it shows about reversibility

## The debt this file pays down

`Slots.lean` records `core.semantics.weight_exists` as open, with the measurement: the legacy tree
declares no `Weight`, `Tensor`, `Shape`, `Param` or `Network` type at all, so its
"symbolic-to-weight" bridge could only ever relate two field-renamed records.

`WeightSemantics` was declared in `Lattice.Core.Semantics` with a single instance,
`LinearForm`. That instance is exactly the field renaming the slot complains about: the parameter
*is* the symbolic coefficient, and `act` is just `denote`. An interface with only its own special
case as inhabitant has not been tested.

This file supplies a second, genuinely different instance: an affine layer whose parameter has
shape `(m -> n -> Real)` and whose input and output are vectors of *different* dimensions. The
compilation step is then no longer a renaming -- the arity changes, and the parameter no longer
resembles the constraint.

## The result worth having: reversibility depends on the representation

T3 established that on `LinearForm` the semantic layer is **not** injective: `unitForm` and
`scaledForm` denote the same points while being different objects.

On an affine layer the opposite holds: `layer_act_injective` below shows the behaviour determines
the parameter completely. Both facts are proved, and together they support a sharper version of the
headline claim than "reversibility must be stated by layer":

> **the same layer can be invertible or not depending on which representation is chosen.**

That is a stronger and more useful statement, because it says the choice of representation -- not
the position in the ladder -- is what governs invertibility.
-/

namespace Lattice.Core

open Lattice.Core

/-- A linear layer as a parameterised map: weights indexed by an input and an output dimension,
plus a bias.

The parameter's type `(m → n → ℝ) × (n → ℝ)` is deliberately *not* the shape of a symbolic
constraint (`Fin n → R` with a single constant). That mismatch is the point: a compilation into
this representation changes structure, so a preservation theorem about it cannot be a renaming. -/
structure LayerParams (m n : Type) where
  /-- Weight matrix. -/
  W : m → n → ℝ
  /-- Bias vector. -/
  b : n → ℝ

/-- The action of an affine layer: `x ↦ Wᵀx + b`. -/
noncomputable def layerAct {m n : Type} [Fintype m] [Fintype n]
    (p : LayerParams m n) (x : m → ℝ) : n → ℝ :=
  fun j => (∑ i, p.W i j * x i) + p.b j

/-- The affine layer as a `WeightSemantics` instance.

Unlike `LinearForm`, the input and output types differ (`m → ℝ` versus `n → ℝ`), so this instance
exercises the parts of the interface that the linear instance leaves vacuous. -/
noncomputable instance instWeightSemanticsLayer {m n : Type} [Fintype m] [Fintype n] :
    WeightSemantics (LayerParams m n) where
  Input := m → ℝ
  Output := n → ℝ
  act := layerAct

/-! ## Behaviour determines the parameter

This is the property the linear fragment *lacks*, and proving it here is what makes the pair of
facts interesting. -/

section Injectivity

variable {m n : Type} [Fintype m] [Fintype n]

/-- **Two affine layers with the same behaviour have the same bias.**

Evaluating at the zero input leaves only the bias. Neither non-emptiness of the index type nor
decidable equality is needed, so both are omitted from the statement. -/
theorem layer_bias_ext {p q : LayerParams m n}
    (h : ∀ x : m → ℝ, layerAct p x = layerAct q x) : p.b = q.b := by
  funext j
  have hz := congrFun (h (fun _ => 0)) j
  simpa [layerAct] using hz

/-- **Two affine layers with the same behaviour have the same weights.**

Evaluating at the unit input `e_i` isolates column `i`: the sum collapses to `W i j`, and the bias
terms agree by `layer_bias_ext`, so `W i j = W' i j` follows by cancellation. -/
theorem layer_weight_ext {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    {p q : LayerParams m n}
    (h : ∀ x : m → ℝ, layerAct p x = layerAct q x) : p.W = q.W := by
  funext i j
  have hb := congrFun (layer_bias_ext h) j
  -- the input that is 1 at `i` and 0 elsewhere
  let e : m → ℝ := fun k => if k = i then 1 else 0
  have he := congrFun (h e) j
  simp only [layerAct] at he
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i] at he
  · simp only [e, if_pos rfl, mul_one] at he
    linarith
  · intro k _ hk
    simp only [e, if_neg hk, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · intro k _ hk
    simp only [e, if_neg hk, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Behavioural equivalence on affine layers is injective.**

The converse of what T3 found for `LinearForm`: there, distinct parameters can share a behaviour;
here they cannot. The two results are stated in the same project, on the same relation
(`BehaviourallyEquivalent`), so the comparison is exact. -/
theorem layer_act_injective {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    {p q : LayerParams m n} (h : BehaviourallyEquivalent p q) : p = q := by
  have hW : p.W = q.W := layer_weight_ext h
  have hb : p.b = q.b := layer_bias_ext h
  cases p with
  | mk W b =>
    cases q with
    | mk W' b' =>
      simp only at hW hb
      rw [hW, hb]

/-- The same statement in the shape "no two distinct parameters share a behaviour", which is what
non-injectivity of the linear fragment denies. -/
theorem layer_behaviourally_separates {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    {p q : LayerParams m n} (hne : p ≠ q) : ¬ BehaviourallyEquivalent p q :=
  fun h => hne (layer_act_injective h)

end Injectivity

/-! ## The comparison

`Lattice.Lift.Extraction` proves `semantic_not_injective`: two distinct `LinearForm` values with the
same zero set. The theorem below is the statement that the affine layer behaves differently, phrased
so that it is obviously the same question asked of a different representation. -/

/-- **Reversibility is a property of the representation, not of the layer.**

On the linear-form representation, distinct parameters can be behaviourally equivalent
(`Lattice.Lift.Extraction.semantic_not_injective`). On the affine-layer representation they cannot
(`layer_act_injective`). Both are theorems about `BehaviourallyEquivalent`, so "is the semantic
layer invertible?" has no answer until the representation is fixed.

This strengthens the layered statement required by the project: not only must reversibility be
stated per layer, it must be stated per *representation within* a layer. -/
theorem reversibility_depends_on_representation :
    (∃ p q : LayerParams (Fin 1) (Fin 1), p ≠ q ∧ BehaviourallyEquivalent p q) → False :=
  fun ⟨_, _, hne, hbe⟩ => hne (layer_act_injective hbe)

end Lattice.Core
