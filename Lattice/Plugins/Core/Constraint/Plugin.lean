/-
# Core.Constraint Plugin -- assembly

The four obligations of `Manifest.lean`, discharged by `Lattice.Core.Logic`.

## What the `Prop`s have to say explicitly

**`Entails` and `Models` are defined inside `Lattice.Core.Logic`'s `Satisfaction` section, over an
arbitrary `CommSemiring` and `LinearOrder`.** **The obligations below therefore quantify over the
same parameters**, so that citing them is a statement about the general relation rather than about
one instantiation (the project works with `ℝ`, but the lemmas are true over any ordered semiring,
and stating them that way keeps the plugin honest about what it is receiving).
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Core.Constraint.Manifest
import Lattice.Core.Logic

namespace Lattice.Plugins.Core.Constraint

open Lattice.Plugins
open Lattice.Core
-- `Constraint` lives in `Lattice.Core.LinearForm`, not directly in `Lattice.Core`.
open Lattice.Core.LinearForm

/-- **Law: entailment of a cons splits into head and tail.** -/
def EntailsConsProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (c : Constraint R n) (cs : List (Constraint R n)) (x : Point R n),
    Entails (c :: cs) x ↔ Satisfies c x ∧ Entails cs x

/-- **`EntailsConsProp` holds** -- by `entails_cons`. -/
theorem entailsConsProp_holds : EntailsConsProp := by
  intro R _ _ n c cs x
  exact entails_cons

/-- **Law: entailment is monotone in the constraint set.** -/
def EntailsMonoProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (cs ds : List (Constraint R n)) (x : Point R n),
    (∀ c ∈ cs, c ∈ ds) → Entails ds x → Entails cs x

/-- **`EntailsMonoProp` holds** -- by `entails_mono`. -/
theorem entailsMonoProp_holds : EntailsMonoProp := by
  intro R _ _ n cs ds x hsub h
  exact entails_mono hsub h

/-- **Soundness: a set models any constraint it contains.** -/
def ModelsOfMemProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (H : List (Constraint R n)) (c : Constraint R n), c ∈ H → Models H c

/-- **`ModelsOfMemProp` holds** -- by `models_of_mem`. -/
theorem modelsOfMemProp_holds : ModelsOfMemProp := by
  intro R _ _ n H c hmem
  exact models_of_mem hmem

/-- **Soundness: `Models` is contravariantly monotone in the hypothesis set.** -/
def ModelsOfSubsetProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (H K : List (Constraint R n)) (c : Constraint R n),
    (∀ d ∈ H, d ∈ K) → Models H c → Models K c

/-- **`ModelsOfSubsetProp` holds** -- by `models_of_subset`. -/
theorem modelsOfSubsetProp_holds : ModelsOfSubsetProp := by
  intro R _ _ n H K c hsub h
  exact models_of_subset hsub h

/-- **The constraint-logic plugin's proof bundle.**

Four claimed obligations. `exactness`, `approximation`, `recovery`, `spatial`, `confluence`,
`equivariance`, `idempotence`, `invariants`, `completeness` and `refinement` are `True`, matching
the manifest's negative theorems.
-/
def proof : PluginProof where
  soundness := ModelsOfMemProp ∧ ModelsOfSubsetProp
  laws := EntailsConsProp ∧ EntailsMonoProp
  exactness := True
  approximation := True
  recovery := True
  spatial := True
  confluence := True
  equivariance := True
  idempotence := True
  invariants := True
  completeness := True
  refinement := True

/-- **Every claimed obligation of the constraint-logic plugin is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨⟨modelsOfMemProp_holds, modelsOfSubsetProp_holds⟩,
         ⟨entailsConsProp_holds, entailsMonoProp_holds⟩,
         True.intro, True.intro, True.intro, True.intro, True.intro, True.intro,
         True.intro, True.intro, True.intro, True.intro⟩

/-- **The verified constraint-logic plugin.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The plugin carries four obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 4 := rfl

end Lattice.Plugins.Core.Constraint
