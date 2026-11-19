/-
# Penalty Plugin -- Manifest

The pilot plugin for the migration (P2-2). It is deliberately the FIRST one migrated,
because the penalty carrier is where the project's exactness story is most developed:
`penaltyLoss_eq_zero_iff_holds_*` already says, for each algebraic layer, that a vanishing
loss is EQUIVALENT to the constraint holding. That is the `Exactness/` obligation filled in
by the tree rather than promised by a document.

## What a manifest is for

The manifest is the plugin's claim, and `Registry.VerifiedPlugin` is where the claim is
discharged. Splitting them matters: the manifest can be written (and reviewed) before the
proof bundle is assembled, and the registry refuses to accept a manifest whose obligations
are not backed by theorems that actually exist.

## Where the theorems live

The obligations below name theorems in `Lattice/Domains/Constraints/`, extending
`Lattice.Core.VariableDerivative`'s style of naming: the theorem name states the property,
and the `file` field says where to find it so that an obligation can be checked mechanically
against the tree instead of being taken on trust.

**Round 550 note.** The plugin's `Semantics.lean` and `Plugin.lean` import the domain
modules; the manifest does NOT, because a manifest is data (strings and a taxonomy) and
importing the proofs into it would create the reverse dependency that `PLUGIN-PROOFS.md` §8
forbids.
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Domains.Constraints.Penalty.PenaltyLoss
import Lattice.Plugins.Domains.Constraints.Penalty.NetLossDerivative

namespace Lattice.Plugins.Domains.Constraints.Penalty

open Lattice.Plugins
open Lattice.Geo
open Lattice.Geo.PenaltyLoss

-- **Round 770 (STAGE 3): the seven obligations now CARRY their propositions.**

/-- **`penaltyLoss_eq_zero_iff_holds_sq`: 平方类约束的惩罚为零当且仅当它成立。** -/
def penaltyLoss_eq_zero_iff_holds_sqProp : Prop :=
  ∀ {n : ℕ} (Φ : ℕ → Pt n),
    (∀ (e : GeoExpr n), penaltyLoss (GeoConstraint.eqZero e) Φ = 0 ↔ (GeoConstraint.eqZero e).Holds Φ) ∧
      (∀ (a b : ℕ) (d : GeoExpr n),
          penaltyLoss (GeoConstraint.sqDistEq a b d) Φ = 0 ↔ (GeoConstraint.sqDistEq a b d).Holds Φ) ∧
        (∀ (a b c e : ℕ),
            penaltyLoss (GeoConstraint.equalLength a b c e) Φ = 0
              ↔ (GeoConstraint.equalLength a b c e).Holds Φ) ∧
          (∀ (a b c e : ℕ),
              penaltyLoss (GeoConstraint.perpendicular a b c e) Φ = 0
                ↔ (GeoConstraint.perpendicular a b c e).Holds Φ) ∧
            ∀ (a b c : ℕ),
              penaltyLoss (GeoConstraint.rightAngle a b c) Φ = 0
                ↔ (GeoConstraint.rightAngle a b c).Holds Φ

/-- **`penaltyLoss_eq_zero_iff_holds_leZero`: `leZero` 的惩罚为零当且仅当它成立。** -/
def penaltyLoss_eq_zero_iff_holds_leZeroProp : Prop :=
  ∀ {n : ℕ} (e : GeoExpr n) (Φ : ℕ → Pt n),
    penaltyLoss (GeoConstraint.leZero e) Φ = 0 ↔ (GeoConstraint.leZero e).Holds Φ

/-- **`penaltyLoss_congr_of_indicesBelow`: 惩罚只看涉及的下标。** -/
def penaltyLoss_congr_of_indicesBelowProp : Prop :=
  ∀ {n : ℕ} (c : GeoConstraint n) (K : ℕ),
    ConstraintIndicesBelow c K → ∀ (Φ Ψ : ℕ → Pt n), (∀ k < K, Φ k = Ψ k)
      → penaltyLoss c Φ = penaltyLoss c Ψ

/-- **`eqZero_lipschitz`: `eqZero` 的惩罚按 `rho` 是 Lipschitz 的。** -/
def eqZero_lipschitzProp : Prop :=
  ∀ {n k : ℕ} {e : GeoExpr n} {K B : ℝ},
    0 ≤ B → LipschitzK n k e K → BoundedV n e B →
      ∀ (pts pts' : ℕ → Pt n),
        |penaltyLoss (GeoConstraint.eqZero e) pts - penaltyLoss (GeoConstraint.eqZero e) pts'|
          ≤ 2 * B * (K * rho n k pts pts')

/-- **`gtZero_lipschitz`: `gtZero` 的惩罚按 `rho` 是 Lipschitz 的。** -/
def gtZero_lipschitzProp : Prop :=
  ∀ {n k : ℕ} {e : GeoExpr n} {K B : ℝ},
    0 ≤ B → LipschitzK n k e K → BoundedV n e B →
      ∀ (pts pts' : ℕ → Pt n),
        |penaltyLoss (GeoConstraint.gtZero e) pts - penaltyLoss (GeoConstraint.gtZero e) pts'|
          ≤ 2 * B * (K * rho n k pts pts')

/-- **`equalLength_lipschitz`: `equalLength` 的惩罚按 `rho` 是 Lipschitz 的。**

**=> 第 771 轮补上了完整参数化：四条下标界、常数非负、两个配置的有界性，以及界里的常数
`2·(8nB²)·(8nB + 8nB)·rho`。** -/
def equalLength_lipschitzProp : Prop :=
  ∀ {n k a b c e : ℕ} {B : ℝ},
    a < k → b < k → c < k → e < k → 0 ≤ B →
      ∀ (pts pts' : ℕ → Pt n),
        (∀ (p : ℕ) (i : Fin n), |pts p i| ≤ B) →
          (∀ (p : ℕ) (i : Fin n), |pts' p i| ≤ B) →
            |penaltyLoss (GeoConstraint.equalLength a b c e) pts
                - penaltyLoss (GeoConstraint.equalLength a b c e) pts'|
              ≤ 2 * (8 * (n : ℝ) * B * B)
                  * (8 * (n : ℝ) * B * rho n k pts pts' + 8 * (n : ℝ) * B * rho n k pts pts')

/-- **`max_zero_eq_zero_iff`: `max 0 x = 0 ↔ x ≤ 0`。** -/
def max_zero_eq_zero_iffProp : Prop :=
  ∀ (a : ℝ), (a ⊔ (0 : ℝ)) = 0 ↔ a ≤ 0

/-- **七条命题与七条定理的关系。**

**=> 第 771 轮补齐了 `equalLength_lipschitz` 的完整参数化，因此**七条全部**被机器验证等于定理。** -/
theorem penalty_props_hold :
    penaltyLoss_eq_zero_iff_holds_sqProp ∧ penaltyLoss_eq_zero_iff_holds_leZeroProp
      ∧ penaltyLoss_congr_of_indicesBelowProp ∧ eqZero_lipschitzProp
      ∧ gtZero_lipschitzProp ∧ equalLength_lipschitzProp ∧ max_zero_eq_zero_iffProp :=
  ⟨penaltyLoss_eq_zero_iff_holds_sq, penaltyLoss_eq_zero_iff_holds_leZero,
   penaltyLoss_congr_of_indicesBelow, eqZero_lipschitz, gtZero_lipschitz,
   @equalLength_lipschitz, @PenaltyLoss.max_zero_eq_zero_iff⟩

/-- **The penalty plugin's manifest.**

Layer `domains`, because the penalty carrier is a domain carrier: it turns a geometric
constraint into a real-valued loss. It consumes nothing (`requires = []`) and offers the
single capability `penalty.loss`, which is what a downstream `NetLoss` or `Repair` plugin
would require.
-/
def manifest : PluginManifest where
  name := "Domains.Constraints.Penalty"
  layer := .domains
  requires := []
  provides := ["penalty.loss"]
  obligations := [
    -- **Round 770: all seven go through `verifiedObligation`, so each CARRIES a proposition.**
    verifiedObligation "penalty_loss_zero_iff_holds_sq" .exactness
        "Lattice/Plugins/Domains/Constraints/Penalty/NetLossDerivative.lean"
        "penaltyLoss_eq_zero_iff_holds_sq" penaltyLoss_eq_zero_iff_holds_sqProp (by exact penaltyLoss_eq_zero_iff_holds_sq),
    verifiedObligation "penalty_loss_zero_iff_holds_leZero" .exactness
        "Lattice/Plugins/Domains/Constraints/Penalty/NetLossDerivative.lean"
        "penaltyLoss_eq_zero_iff_holds_leZero" penaltyLoss_eq_zero_iff_holds_leZeroProp (by exact penaltyLoss_eq_zero_iff_holds_leZero),
    verifiedObligation "penalty_loss_congr_of_indicesBelow" .soundness
        "Lattice/Plugins/Domains/Constraints/Penalty/NetLossDerivative.lean"
        "penaltyLoss_congr_of_indicesBelow" penaltyLoss_congr_of_indicesBelowProp (by exact penaltyLoss_congr_of_indicesBelow),
    verifiedObligation "penalty_loss_lipschitz_eqZero" .approximation
        "Lattice/Plugins/Domains/Constraints/Penalty/PenaltyLoss.lean"
        "eqZero_lipschitz" eqZero_lipschitzProp (by exact eqZero_lipschitz),
    verifiedObligation "penalty_loss_lipschitz_gtZero" .approximation
        "Lattice/Plugins/Domains/Constraints/Penalty/PenaltyLoss.lean"
        "gtZero_lipschitz" gtZero_lipschitzProp (by exact gtZero_lipschitz),
    verifiedObligation "penalty_loss_lipschitz_equalLength" .approximation
        "Lattice/Plugins/Domains/Constraints/Penalty/PenaltyLoss.lean"
        "equalLength_lipschitz" equalLength_lipschitzProp (by exact equalLength_lipschitz),
    verifiedObligation "penalty_max_zero_eq_zero_iff" .completeness
        "Lattice/Plugins/Domains/Constraints/Penalty/PenaltyLoss.lean"
        "max_zero_eq_zero_iff" max_zero_eq_zero_iffProp (by exact PenaltyLoss.max_zero_eq_zero_iff)
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims exactly the seven obligations listed above. -/
theorem manifest_obligation_count : manifest.obligations.length = 7 := rfl

/-- **The manifest carries at least one obligation.**

Derived from `manifest_obligation_count`: if the list were `[]` its length would be `0`, contradicting
the stated count.
**This is what `NonVacuousFor` consumes. Having it as a NAMED lemma per manifest means a future edit
that empties the obligation list breaks HERE, rather than silently reopening the fake-completion
path.** -/
theorem manifest_nonempty : manifest.obligations ≠ [] := by
  intro hnil
  have hlen := manifest_obligation_count
  rw [hnil] at hlen
  exact absurd hlen (by decide)

/-- The manifest belongs to the `domains` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.domains := rfl

/-- The plugin offers exactly one capability. -/
theorem manifest_provides : manifest.provides = ["penalty.loss"] := rfl

/-- The plugin requires no other plugin. -/
theorem manifest_requires_nothing : manifest.requires = [] := rfl

/-- The manifest claims exactness -- the obligation T2 rests on. -/
theorem manifest_claims_exactness : manifest.claims .exactness = true := rfl

/-- The manifest claims approximation -- the quantitative half. -/
theorem manifest_claims_approximation : manifest.claims .approximation = true := rfl

/-- The manifest does NOT claim refinement: the C backend is out of scope. -/
theorem manifest_no_refinement : manifest.claims .refinement = false := rfl

/-- The manifest does NOT claim recovery: the penalty carrier has no install/uninstall. -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- The manifest does NOT claim spatial: the penalty carrier has no spatial extent. -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- The manifest does NOT claim confluence: the penalty carrier has no effects to order. -/
theorem manifest_no_confluence : manifest.claims .confluence = false := rfl

/-- The manifest does NOT claim idempotence: the penalty carrier is not applied twice. -/
theorem manifest_no_idempotence : manifest.claims .idempotence = false := rfl

end Lattice.Plugins.Domains.Constraints.Penalty
