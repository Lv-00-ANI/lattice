/-
# Domains.Constraints.Tokens Plugin -- Manifest

The third migrated plugin (P3-1). It is the **T1 Compile / T3 Extract** carrier for the
`Domains/Constraints` directory: constraints become token sequences, point clouds become flat
vectors, and both round trips are proved.

## Name: why `Tokens` and not `Constraints`

`Domains/Constraints/` already owns a plugin named `Domains.Constraints.Penalty`. A plugin
named `Domains.Constraints` would be the SIBLING of `Penalty` and also its superset, which
makes the ownership relation ambiguous. This plugin is the tokenisation + flattening part, so
it is named after that part.

## What this manifest records, and the one thing it must NOT claim

**Proved and claimed below**: the token encoding round-trips on both sides (`seqDecode_encode`,
`seqEncode_decode`), the flattening is a bijection (`flatten_injective`, `flatten_surjective`)
with an equality-form round trip, and the loss's non-injectivity is recorded with its sharpened
form (`no_loss_to_constraint_section`).

**NOT claimed, because it does not exist**: **`penalty_min_to_violation`** -- the plan's T2
obligation `IsLocalMin (loss p) x → violation p x ≤ g ε`.
**That `IsLocalMin` machinery lives in `Domains/Geometry`, not here**, and nothing in this
directory bridges a local minimum of the loss to a bound on the violation.
**A manifest that stayed silent on this would let a reader assume T2 was done.**

## Why `flatten_injective` and `penaltyLoss_not_injective` sit in the same plugin

They look contradictory and are not. **`flatten` is a bijection between a point CLOUD and a flat
vector, so it IS invertible. `penaltyLoss` collapses many point clouds onto one real number, so it
is NOT.** **Two different maps; together they are the reversibility boundary the reverse direction
has to live inside** -- the parameter layer round-trips, the semantic layer does not.
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Domains.Constraints.Tokens.Flatten
import Lattice.Plugins.Domains.Constraints.Tokens.LossExtraction
import Lattice.Plugins.Domains.Constraints.Tokens.SeqRepresentation
open Lattice.Geo

namespace Lattice.Plugins.Domains.Constraints.Tokens

open Lattice.Plugins

-- **Round 769 (STAGE 3): the seven obligations now CARRY their propositions.**

/-- **`flatten_injective`: 展平是单射。** -/
def flatten_injectiveProp : Prop :=
  ∀ {k n : ℕ}, Function.Injective (flatten (k := k) (n := n) : (Fin k → Pt n) → Fin (k * n) → ℝ)

/-- **`flatten_surjective`: 展平是满射。** -/
def flatten_surjectiveProp : Prop :=
  ∀ {k n : ℕ}, Function.Surjective (flatten (k := k) (n := n) : (Fin k → Pt n) → Fin (k * n) → ℝ)

/-- **`flattenRepresentation_roundtrip`: 展平表示的往返复原。** -/
def flattenRepresentation_roundtripProp : Prop :=
  ∀ (k n : ℕ) (pts : Fin k → Pt n),
    (flattenRepresentation k n).extract ((flattenRepresentation k n).compile pts) = pts

/-- **`seqDecode_encode`: 序列编码被解码复原。** -/
def seqDecode_encodeProp : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (pts : ℕ → Pt n), seqDecode n (seqEncode n hn pts) = pts

/-- **`seqEncode_decode`: 序列编码是解码的左逆。** -/
def seqEncode_decodeProp : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (v : ℕ → ℝ), seqEncode n hn (seqDecode n v) = v

/-- **`penaltyLoss_not_injective`: 惩罚损失不是单射 —— 逆向**必然**有损。** -/
def penaltyLoss_not_injectiveProp : Prop :=
  ∀ {n : ℕ}, GeoExpr n →
    ¬Function.Injective (fun c : GeoConstraint n => PenaltyLoss.penaltyLoss c)

/-- **`no_loss_to_constraint_section`: 不存在从损失回到约束的截面。**

**=> 第 771 轮补上了 `g` 的显式类型 `((ℕ → Pt n) → ℝ) → GeoConstraint n`：
`penaltyLoss` 的第一个参数是**配置**（`ℕ → Pt n`），返回 `ℝ`，而 `g` 必须把它映回约束。
不写这个类型，Lean 在 `∃` 绑定处无法定出 `g` 的 domains。** -/
def no_loss_to_constraint_sectionProp : Prop :=
  ∀ {n : ℕ}, GeoExpr n →
    ¬ ∃ g : ((ℕ → Pt n) → ℝ) → GeoConstraint n,
        ∀ (c : GeoConstraint n), g (PenaltyLoss.penaltyLoss c) = c

/-- **七条命题就是七条定理的类型。** -/
theorem token_props_hold :
    flatten_injectiveProp ∧ flatten_surjectiveProp ∧ flattenRepresentation_roundtripProp
      ∧ seqDecode_encodeProp ∧ seqEncode_decodeProp
      ∧ penaltyLoss_not_injectiveProp ∧ no_loss_to_constraint_sectionProp :=
  ⟨@flatten_injective, @flatten_surjective, flattenRepresentation_roundtrip,
   @seqDecode_encode, @seqEncode_decode, @penaltyLoss_not_injective,
   @no_loss_to_constraint_section⟩

/-- **The constraint-tokenisation plugin's manifest.**

Layer `domains`. It requires the penalty carrier (`penalty.loss`, provided by
`Domains.Constraints.Penalty`) because the loss lemmas it claims are the penalty's, and offers
constraint tokenisation plus the flattening bijection.
-/
def manifest : PluginManifest where
  name := "Domains.Constraints.Tokens"
  layer := .domains
  requires := ["penalty.loss"]
  provides := ["constraint.tokens", "constraint.flatten"]
  obligations := [
    -- **Round 769: all seven go through `verifiedObligation`, so each CARRIES its proposition.**
    verifiedObligation "flatten_injective" .exactness
        "Lattice/Plugins/Domains/Constraints/Tokens/Flatten.lean"
        "flatten_injective" flatten_injectiveProp (by intro k n; exact flatten_injective),
    verifiedObligation "flatten_surjective" .completeness
        "Lattice/Plugins/Domains/Constraints/Tokens/Flatten.lean"
        "flatten_surjective" flatten_surjectiveProp (by exact flatten_surjective),
    verifiedObligation "flatten_roundtrip" .laws
        "Lattice/Plugins/Domains/Constraints/Tokens/Flatten.lean"
        "flattenRepresentation_roundtrip" flattenRepresentation_roundtripProp (by exact flattenRepresentation_roundtrip),
    verifiedObligation "seq_decode_encode" .laws
        "Lattice/Plugins/Domains/Constraints/Tokens/SeqRepresentation.lean"
        "seqDecode_encode" seqDecode_encodeProp (by exact seqDecode_encode),
    verifiedObligation "seq_encode_decode" .laws
        "Lattice/Plugins/Domains/Constraints/Tokens/SeqRepresentation.lean"
        "seqEncode_decode" seqEncode_decodeProp (by exact seqEncode_decode),
    verifiedObligation "penalty_loss_not_injective" .soundness
        "Lattice/Plugins/Domains/Constraints/Tokens/LossExtraction.lean"
        "penaltyLoss_not_injective" penaltyLoss_not_injectiveProp (by exact penaltyLoss_not_injective),
    verifiedObligation "no_loss_to_constraint_section" .soundness
        "Lattice/Plugins/Domains/Constraints/Tokens/LossExtraction.lean"
        "no_loss_to_constraint_section" no_loss_to_constraint_sectionProp (by exact no_loss_to_constraint_section)
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims seven obligations. -/
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

/-- The plugin lives in the `domains` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.domains := rfl

/-- It requires the penalty carrier's loss. -/
theorem manifest_requires : manifest.requires = ["penalty.loss"] := rfl

/-- It offers constraint tokenisation and the flattening bijection. -/
theorem manifest_provides :
    manifest.provides = ["constraint.tokens", "constraint.flatten"] := rfl

/-- It claims exactness -- the flattening injectivity. -/
theorem manifest_claims_exactness : manifest.claims .exactness = true := rfl

/-- It claims laws -- the round trips. -/
theorem manifest_claims_laws : manifest.claims .laws = true := rfl

/-- It claims soundness -- the negative reversibility statements. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- It does NOT claim spatial composability. -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- It does NOT claim confluence. -/
theorem manifest_no_confluence : manifest.claims .confluence = false := rfl

/-- It does NOT claim recovery. -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- It does NOT claim refinement. -/
theorem manifest_no_refinement : manifest.claims .refinement = false := rfl

end Lattice.Plugins.Domains.Constraints.Tokens
