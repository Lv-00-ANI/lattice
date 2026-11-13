/-
# Core.Constraint Plugin -- Manifest

The constraint LOGIC plugin (P3-4). It is the **T1 Compile** carrier's formal basis: before
anything can be compiled, "the program entails this constraint" has to mean something, and this
plugin is where that meaning lives.

## The two notions, and why both are needed

**`Entails cs x`**: the point `x` satisfies every constraint in the list `cs`. **Point-level.**

**`Models H c`**: EVERY point meeting every constraint in `H` also meets `c`. **Set-level, and
deliberately stronger** -- it is the correct target for "the compiled artifact preserves the
program's meaning", because a compiled artifact must work for all inputs, not one.

**=> `models_of_mem` and `models_of_subset` are the two lemmas that move between them, and they are
what a compiler's soundness proof consumes.**

## Why this is a separate plugin from `Domains.Constraints.Penalty`

**`Penalty` is about a real-valued LOSS** (a numeric relaxation). **`Constraint`, here, is about the
DISCRETE satisfiability relation.** **The loss is exact precisely when the two agree, and that
agreement is `Penalty`'s `exactness` obligation -- but the discrete side comes first and must stand
on its own.** **Splitting them keeps the direction of explanation honest: the loss is justified BY
satisfiability, never the reverse.**
-/

import Lattice.Plugins.Manifest
import Lattice.Core.RepairModule.ConstraintProofs
open Lattice.Core

namespace Lattice.Plugins.Core.Constraint

open Lattice.Plugins

/-- **`entails_cons` 的命题：`c :: cs` 的蕴涵等价于 `c` 单独成立且 `cs` 成立。** -/
def entails_consProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    {c : LinearForm.Constraint R n} {cs : List (LinearForm.Constraint R n)} {x : Point R n},
    Entails (c :: cs) x ↔ Satisfies c x ∧ Entails cs x

/-- **`entails_mono` 的命题：约束集变大，蕴涵变弱。** -/
def entails_monoProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    {cs ds : List (LinearForm.Constraint R n)} {x : Point R n},
    (∀ c ∈ cs, c ∈ ds) → Entails ds x → Entails cs x

/-- **`models_of_mem` 的命题：集合内的每条约束都被该集合模型化。** -/
def models_of_memProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    {H : List (LinearForm.Constraint R n)} {c : LinearForm.Constraint R n},
    c ∈ H → Models H c

/-- **`models_of_subset` 的命题：模型化在超集上保持。** -/
def models_of_subsetProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    {H K : List (LinearForm.Constraint R n)} {c : LinearForm.Constraint R n},
    (∀ d ∈ H, d ∈ K) → Models H c → Models K c

/-- **四条命题就是四条定理的类型。**

**=> 若定理改名或改陈述，本定理失败 —— 这正是 `proof` 字段要保证的事。** -/
theorem constraint_props_hold :
    entails_consProp ∧ entails_monoProp ∧ models_of_memProp ∧ models_of_subsetProp :=
  ⟨@entails_cons, @entails_mono, @models_of_mem, @models_of_subset⟩

/-- **The constraint-logic plugin's manifest.**

Layer `core`. It requires nothing -- this is the base of the semantic stack -- and offers
`constraint.satisfies`, `constraint.entails` and `constraint.models`, the three notions a compiler's
soundness theorem is stated over.
-/
def manifest : PluginManifest where
  name := "Core.Constraint"
  layer := .core
  requires := []
  provides := ["constraint.satisfies", "constraint.entails", "constraint.models"]
  obligations := [
    -- **Round 768: all four obligations go through `verifiedObligation`, so each CARRIES its
    -- proposition.** Before this, the manifest named a theorem as a `String`; a manifest could name
    -- a theorem that did not exist and nothing in the tree could tell.
    verifiedObligation "entails_cons" .laws
      "Lattice/Plugins/Core/Constraint/Proofs.lean"
      "entails_cons" entails_consProp,
    verifiedObligation "entails_mono" .laws
      "Lattice/Plugins/Core/Constraint/Proofs.lean"
      "entails_mono" entails_monoProp,
    verifiedObligation "models_of_mem" .soundness
      "Lattice/Plugins/Core/Constraint/Proofs.lean"
      "models_of_mem" models_of_memProp,
    verifiedObligation "models_of_subset" .soundness
      "Lattice/Plugins/Core/Constraint/Proofs.lean"
      "models_of_subset" models_of_subsetProp
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims four obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 4 := rfl

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

/-- The plugin lives in the `core` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.core := rfl

/-- It is the base of the semantic stack: it requires nothing. -/
theorem manifest_requires_nothing : manifest.requires = [] := rfl

/-- It offers the three semantic notions. -/
theorem manifest_provides :
    manifest.provides =
      ["constraint.satisfies", "constraint.entails", "constraint.models"] := rfl

/-- It claims laws -- the structural recursion and monotonicity. -/
theorem manifest_claims_laws : manifest.claims .laws = true := rfl

/-- It claims soundness -- the two `Models` lemmas. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- **It does NOT claim exactness**: the discrete satisfiability relation has no loss to be exact
about. That obligation belongs to `Domains.Constraints.Penalty`, which relates the two. -/
theorem manifest_no_exactness : manifest.claims .exactness = false := rfl

/-- **It does NOT claim approximation.** -/
theorem manifest_no_approximation : manifest.claims .approximation = false := rfl

/-- **It does NOT claim recovery.** -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- **It does NOT claim spatial composability.** -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- **It does NOT claim completeness**: not every constraint set is decidable, so "the compiler
handles everything" is not asserted here. -/
theorem manifest_no_completeness : manifest.claims .completeness = false := rfl

end Lattice.Plugins.Core.Constraint
