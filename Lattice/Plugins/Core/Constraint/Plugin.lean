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
import Lattice.Core.RepairModule.ConstraintProofs
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

/-- **`EntailsAppendProp`：**两个约束集拼接后的蕴含拆成两半**。**

**⇒ `recovery`（时间可组合性）：拼接的蕴含恰好是两段蕴含的**合取**——
这是约束作为组合机制的核心事实，而不是「长一点的集合也能推导」。
由 `Entails` 的展开与 `List.mem_append`。** -/
def EntailsAppendProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (cs ds : List (Constraint R n)) (x : Point R n),
    Entails (cs ++ ds) x ↔ Entails cs x ∧ Entails ds x

/-- **`EntailsAppendProp` holds** — 展开 `Entails`，两个方向各用一次 `List.mem_append`。 -/
theorem entailsAppendProp_holds : EntailsAppendProp := by
  intro R _ _ n cs ds x
  unfold Entails
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
           fun c hc => h c (List.mem_append_right _ hc)⟩
  · intro ⟨h1, h2⟩ c hc
    rcases List.mem_append.mp hc with h | h
    · exact h1 c h
    · exact h2 c h

/-- **`EntailsSingletonProp`：**单元素约束集的蕴含退化为满足性**。**

**⇒ `refinement`：抽象的「蕴含」在最小非平凡的情形上**与具体的 `Satisfies` 一致**——
若二者在这里不一致，那么「蕴含」就不是满足性的推导。
由 `Entails` 的展开与 `List.mem_singleton`。** -/
def EntailsSingletonProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (c : Constraint R n) (x : Point R n),
    Entails [c] x ↔ Satisfies c x

/-- **`EntailsSingletonProp` holds** — 两个方向各用一次 `List.mem_singleton`。 -/
theorem entailsSingletonProp_holds : EntailsSingletonProp := by
  intro R _ _ n c x
  unfold Entails
  constructor
  · intro h
    exact h c (List.mem_singleton.mpr rfl)
  · intro h d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact h

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
  recovery := EntailsAppendProp
  spatial := True
  confluence := True
  equivariance := True
  idempotence := True
  invariants := True
  completeness := True
  refinement := EntailsSingletonProp

/-- **Every claimed obligation of the constraint-logic plugin is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨⟨modelsOfMemProp_holds, modelsOfSubsetProp_holds⟩,
         ⟨entailsConsProp_holds, entailsMonoProp_holds⟩,
         True.intro, True.intro, entailsAppendProp_holds, True.intro, True.intro, True.intro,
         True.intro, True.intro, True.intro, entailsSingletonProp_holds⟩

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
