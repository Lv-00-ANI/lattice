/-
# Penalty Plugin -- assembly

This file is where the plugin's claim meets its proofs. It imports the domain modules, so it
is the ONE file in the plugin that depends on the library proper; `Manifest.lean` stays free
of that dependency, per `PLUGIN-PROOFS.md` §8's rule that proof files do not reach upward.

## How the bundle is assembled

`PluginProof`'s fields are `Prop`s, and Lean's `Prop` is proof-irrelevant, so a bundle is
assembled by **naming** the theorems that discharge each field. The role of this file is to
write down, for every obligation the manifest claims, the `Prop` that obligation means, so
that `consistent` can be proved from the theorems rather than asserted.

## Fields left `True`, and why that is honest

`recovery`, `spatial`, `confluence`, `equivariance`, `idempotence`, `invariants` and
`refinement` are `True` **because the manifest does not claim them**:
`manifest.claims .recovery = false`, and so on. The framework's rule is that a manifest may
only claim what the bundle backs -- not that every bundle must be maxed out. The penalty
carrier is a pure function of a point cloud: it has no install/uninstall, no state, and no
group action, so those obligations are genuinely absent rather than unfinished.

`laws` is `True` for the same reason with one exception worth naming: the associativity and
commutativity of the penalty SUM live in the `NetLoss` plugin, not here.
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Domains.Constraints.Penalty.Manifest
import Lattice.Domains.Constraints.NetLossDerivative
import Lattice.Domains.Constraints.PenaltyLoss

namespace Lattice.Plugins.Domains.Constraints.Penalty

open Lattice.Plugins

-- The domain library's namespaces. `penaltyLoss` itself lives in `Lattice.Geo.PenaltyLoss`,
-- while the exactness theorems live in `Lattice.Geo`; both must be opened, exactly as
-- `NetLossDerivative.lean` does.
open Lattice.Geo
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open Lattice.Core
open scoped BigOperators

/-- **The soundness obligation**: the loss is invariant under the substitutions the repair
loop performs, up to the index bound the loop respects.

`penaltyLoss_congr_of_indicesBelow` is the theorem; this `Prop` is its statement, written so
that the registry can require it without importing the proof term. -/
def SoundnessProp : Prop :=
  ∀ {n : ℕ} (c : GeoConstraint n) (K : ℕ), ConstraintIndicesBelow c K →
    ∀ (Φ Ψ : ℕ → Pt n), (∀ k, k < K → Φ k = Ψ k) → penaltyLoss c Φ = penaltyLoss c Ψ

/-- **`SoundnessProp` holds** -- by `penaltyLoss_congr_of_indicesBelow`. -/
theorem soundnessProp_holds : SoundnessProp := by
  intro n c K hK Φ Ψ h
  exact penaltyLoss_congr_of_indicesBelow c K hK Φ Ψ h

/-- **The exactness obligation**: for the five squared families, a vanishing loss is
EQUIVALENT to the constraint holding.

This is the strongest statement the penalty carrier has and the theorem T2 is built on. -/
def ExactnessProp : Prop :=
  ∀ {n : ℕ} (Φ : ℕ → Pt n),
    (∀ (e : GeoExpr n), penaltyLoss (.eqZero e) Φ = 0 ↔ Holds (.eqZero e) Φ) ∧
    (∀ (a b : ℕ) (d : GeoExpr n),
      penaltyLoss (.sqDistEq a b d) Φ = 0 ↔ Holds (.sqDistEq a b d) Φ) ∧
    (∀ (a b c e : ℕ),
      penaltyLoss (.equalLength a b c e) Φ = 0 ↔ Holds (.equalLength a b c e) Φ) ∧
    (∀ (a b c e : ℕ),
      penaltyLoss (.perpendicular a b c e) Φ = 0 ↔ Holds (.perpendicular a b c e) Φ) ∧
    (∀ (a b c : ℕ),
      penaltyLoss (.rightAngle a b c) Φ = 0 ↔ Holds (.rightAngle a b c) Φ)

/-- **`ExactnessProp` holds** -- by `penaltyLoss_eq_zero_iff_holds_sq`. -/
theorem exactnessProp_holds : ExactnessProp := by
  intro n Φ
  exact penaltyLoss_eq_zero_iff_holds_sq Φ

/-- **The inequality half of exactness**: `leZero` is the layer where an inequality (rather
than an equation) is encoded, and its exactness is stated separately. -/
def ExactnessInequalityProp : Prop :=
  ∀ {n : ℕ} (e : GeoExpr n) (Φ : ℕ → Pt n),
    penaltyLoss (.leZero e) Φ = 0 ↔ Holds (.leZero e) Φ

/-- **`ExactnessInequalityProp` holds** -- by `penaltyLoss_eq_zero_iff_holds_leZero`. -/
theorem exactnessInequalityProp_holds : ExactnessInequalityProp := by
  intro n e Φ
  exact penaltyLoss_eq_zero_iff_holds_leZero e Φ

/-- **The completeness obligation**: the `max a 0` encoding represents every inequality, and
`max a 0 = 0` is exactly `a <= 0`.

This is totality in the only sense the penalty carrier can have: every inequality constraint
has a loss that vanishes precisely on its feasible set. -/
def CompletenessProp : Prop :=
  ∀ a : ℝ, max a 0 = 0 ↔ a ≤ 0

/-- **`CompletenessProp` holds** -- by `max_zero_eq_zero_iff`, stated in both directions so
that the obligation carries the encoding's full content rather than one half of it.

Fully qualified, because the same theorem exists in both `Lattice.Geo` and
`Lattice.Geo.PenaltyLoss`; the two are stated identically and both hold, so this is not a
disagreement, but the plugin must name one of them. -/
theorem completenessProp_holds : CompletenessProp := by
  intro a
  constructor
  · intro h
    exact (Geo.max_zero_eq_zero_iff a).mp h
  · intro h
    exact (Geo.max_zero_eq_zero_iff a).mpr h

/-- **The approximation obligation for the equality family**: the loss is Lipschitz in the
point cloud, with a constant stated in terms of the expression's Lipschitz and bound data.

Exactness says WHEN the loss vanishes; this says how fast it can move. Both are needed: an
exact penalty with no modulus would not let a repair loop make quantitative progress. -/
def ApproximationEqZeroProp : Prop :=
  ∀ {n k : ℕ} {e : GeoExpr n} {K B : ℝ}, 0 ≤ B → LipschitzK n k e K → BoundedV n e B →
    ∀ (pts pts' : ℕ → Pt n),
      |penaltyLoss (.eqZero e) pts - penaltyLoss (.eqZero e) pts'|
        ≤ 2 * B * (K * rho n k pts pts')

/-- **`ApproximationEqZeroProp` holds** -- by `eqZero_lipschitz`. -/
theorem approximationEqZeroProp_holds : ApproximationEqZeroProp := by
  intro n k e K B hB hK hBd pts pts'
  exact eqZero_lipschitz hB hK hBd pts pts'

/-- **The penalty plugin's proof bundle.**

`soundness`, `exactness`, `completeness` and `approximation` are instantiated at the `Prop`s
above, whose inhabitance is proved immediately above by the real theorems. The remaining
fields are `True` because the manifest does not claim them. -/
def proof : PluginProof where
  soundness := SoundnessProp
  laws := True
  exactness := ExactnessProp ∧ ExactnessInequalityProp
  approximation := ApproximationEqZeroProp
  recovery := True
  spatial := True
  confluence := True
  equivariance := True
  idempotence := True
  invariants := True
  completeness := CompletenessProp
  refinement := True

/-- **Every claimed obligation of the penalty plugin is discharged.**

This is the `consistent` field for `VerifiedPlugin`: if the manifest declares obligations, the
bundle holds. Each conjunct is `exact` at a theorem proved in this file, which in turn is
`exact` at a theorem of the domain library -- so the chain from manifest to library is
`penaltyLoss_eq_zero_iff_holds_sq` and friends, with no gaps. -/
theorem proof_holds : proof.Holds := by
  refine ⟨?_, trivial, ?_, ?_, trivial, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩
  · exact soundnessProp_holds
  · exact ⟨exactnessProp_holds, exactnessInequalityProp_holds⟩
  · exact approximationEqZeroProp_holds
  · exact completenessProp_holds

/-- **The verified penalty plugin.**

The registry may now admit it: the manifest's seven obligations are exactly the four
`Prop`s discharged above, so `consistent` is immediate. -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The registered plugin carries seven obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 7 := rfl

end Lattice.Plugins.Domains.Constraints.Penalty
