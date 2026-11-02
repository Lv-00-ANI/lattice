/-
# Domains.Constraints.Tokens Plugin -- assembly

The seven obligations of `Manifest.lean`, discharged by the domain library's theorems.

## The one structure that carries most of the content

`Flatten.flattenRepresentation : Representation (Fin k → Pt n) (Fin (k * n) → ℝ)` is the
project's own `Representation` structure, so the round trip is not an ad-hoc equality: it is
an instance of the abstraction the reverse direction is built on.
**`flattenRepresentation_roundtrip` is therefore simultaneously a T1 statement (compile) and a
T3 statement (extract)** -- which is why the manifest lists it under `laws`.

## The two-level reversibility boundary, stated together

`flatten_injective` (parameter layer: invertible) and `penaltyLoss_not_injective` (semantic
layer: not invertible) are claimed by the same plugin on purpose.
**Together they are exactly `no_extractor_preserves_both`'s content at this carrier: you cannot
have both layers invertible at once.** **Having them in one manifest makes that impossible to
misread as a contradiction.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Domains.Constraints.Tokens.Manifest
import Lattice.Domains.Constraints.Flatten
import Lattice.Domains.Constraints.SeqRepresentation
import Lattice.Domains.Constraints.LossExtraction

namespace Lattice.Plugins.Domains.Constraints.Tokens

open Lattice.Plugins
open Lattice.Geo
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss

/-- **`flatten` is injective**: distinct point clouds flatten to distinct vectors.

Stated in UNFOLDED form (`∀ a b, flatten a = flatten b → a = b`) rather than as
`Function.Injective flatten`. The folded form is `rfl`-equal to this one, but `exact` would
leave it as a `Function.Injective` proposition that the elaborator does not automatically
beta-reduce, and the resulting "type mismatch: `Function.Injective flatten` vs
`flatten a = flatten b → a = b`" is noise about presentation, not about content. -/
def FlattenInjectiveProp : Prop :=
  ∀ {k n : ℕ}, ∀ a b : Fin k → Pt n, flatten a = flatten b → a = b

/-- **`FlattenInjectiveProp` holds** -- by `Flatten.flatten_injective`. -/
theorem flattenInjectiveProp_holds : FlattenInjectiveProp := by
  intro k n a b h
  exact flatten_injective h

/-- **`flatten` is surjective**: every flat vector is realised.

Also unfolded, for the same reason. -/
def FlattenSurjectiveProp : Prop :=
  ∀ {k n : ℕ}, ∀ v : Fin (k * n) → ℝ, ∃ pts : Fin k → Pt n, flatten pts = v

/-- **`FlattenSurjectiveProp` holds** -- by `Flatten.flatten_surjective`. -/
theorem flattenSurjectiveProp_holds : FlattenSurjectiveProp := by
  intro k n v
  exact flatten_surjective v/-- **The flattening round trip**: extract after compile returns the original cloud. -/
def FlattenRoundtripProp : Prop :=
  ∀ (k n : ℕ) (pts : Fin k → Pt n),
    (flattenRepresentation k n).extract ((flattenRepresentation k n).compile pts) = pts

/-- **`FlattenRoundtripProp` holds** -- by `Flatten.flattenRepresentation_roundtrip`. -/
theorem flattenRoundtripProp_holds : FlattenRoundtripProp := by
  intro k n pts
  exact flattenRepresentation_roundtrip k n pts

/-- **Decoding the encoding returns the original sequence.** -/
def SeqDecodeEncodeProp : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (pts : ℕ → Pt n), seqDecode n (seqEncode n hn pts) = pts

/-- **`SeqDecodeEncodeProp` holds** -- by `SeqRepresentation.seqDecode_encode`. -/
theorem seqDecodeEncodeProp_holds : SeqDecodeEncodeProp := by
  intro n hn pts
  exact seqDecode_encode hn pts

/-- **Encoding the decoding returns the original vector.** -/
def SeqEncodeDecodeProp : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (v : ℕ → ℝ), seqEncode n hn (seqDecode n v) = v

/-- **`SeqEncodeDecodeProp` holds** -- by `SeqRepresentation.seqEncode_decode`. -/
theorem seqEncodeDecodeProp_holds : SeqEncodeDecodeProp := by
  intro n hn v
  exact seqEncode_decode hn v

/-- **The penalty loss is NOT injective in the CONSTRAINT**: two distinct constraints
(`leZero e` and `ltZero e`) have the same loss function.

This is the semantic layer's non-invertibility. -/
def LossNotInjectiveProp : Prop :=
  ∀ {n : ℕ} (e : GeoExpr n),
    ¬ Function.Injective (fun c : GeoConstraint n => (penaltyLoss c : (ℕ → Pt n) → ℝ))

/-- **`LossNotInjectiveProp` holds** -- by `LossExtraction.penaltyLoss_not_injective`. -/
theorem lossNotInjectiveProp_holds : LossNotInjectiveProp := by
  intro n e
  exact penaltyLoss_not_injective e

/-- **No section of the loss map exists**: there is no `extract` recovering a CONSTRAINT from
its loss function.

This is the reverse direction's most literal formalisation, and it is false -- which is the
whole point of claiming it. -/
def NoSectionProp : Prop :=
  ∀ {n : ℕ} (e : GeoExpr n),
    ¬ ∃ extract : ((ℕ → Pt n) → ℝ) → GeoConstraint n,
        ∀ c : GeoConstraint n, extract (penaltyLoss c) = c

/-- **`NoSectionProp` holds** -- by `LossExtraction.no_loss_to_constraint_section`. -/
theorem noSectionProp_holds : NoSectionProp := by
  intro n e
  exact no_loss_to_constraint_section e

/-- **The tokenisation plugin's proof bundle.**

Seven claimed obligations. The unclaimed fields are `True`, matching the manifest's five
negative theorems.
-/
def proof : PluginProof where
  soundness := LossNotInjectiveProp ∧ NoSectionProp
  laws := FlattenRoundtripProp ∧ SeqDecodeEncodeProp ∧ SeqEncodeDecodeProp
  exactness := FlattenInjectiveProp
  completeness := FlattenSurjectiveProp
  approximation := True
  recovery := True
  spatial := True
  confluence := True
  equivariance := True
  idempotence := True
  invariants := True
  refinement := True

/-- The twelve fields of `proof` are exactly the `Prop`s declared above.

Useful because `proof_holds` has to reason about them by name rather than positionally. -/
theorem proof_soundness : proof.soundness = (LossNotInjectiveProp ∧ NoSectionProp) := rfl

/-- The bundle's `exactness` field is the flattening injectivity. -/
theorem proof_exactness : proof.exactness = FlattenInjectiveProp := rfl

/-- The bundle's `completeness` field is the flattening surjectivity. -/
theorem proof_completeness : proof.completeness = FlattenSurjectiveProp := rfl

/-- **Every claimed obligation of the tokenisation plugin is discharged.

Each conjunct is named so the correspondence to the manifest is auditable: three of them are
compound (`soundness`, `laws`, `exactness`), the rest are `True` because the manifest claims
nothing for them. -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof_soundness, proof_exactness, proof_completeness, proof]
  exact ⟨⟨lossNotInjectiveProp_holds, noSectionProp_holds⟩,
         ⟨flattenRoundtripProp_holds, seqDecodeEncodeProp_holds, seqEncodeDecodeProp_holds⟩,
         flattenInjectiveProp_holds,
         True.intro, True.intro, True.intro, True.intro, True.intro,
         True.intro, True.intro,
         flattenSurjectiveProp_holds,
         True.intro⟩

/-- **The verified tokenisation plugin.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The plugin carries seven obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 7 := rfl

end Lattice.Plugins.Domains.Constraints.Tokens
