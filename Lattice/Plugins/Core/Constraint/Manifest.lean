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

namespace Lattice.Plugins.Core.Constraint

open Lattice.Plugins

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
    -- LAW: entailment of a cons splits into head and tail. This is the structural recursion
    -- that lets a compiler walk the program.
    { name := "entails_cons"
      kind := .laws
      theoremName := "entails_cons"
      file := "Lattice/Plugins/Core/Constraint/Proofs.lean" },
    -- LAW: entailment is monotone in the constraint set -- a larger program is stronger.
    { name := "entails_mono"
      kind := .laws
      theoremName := "entails_mono"
      file := "Lattice/Plugins/Core/Constraint/Proofs.lean" },
    -- SOUNDNESS: a set models any constraint it contains.
    { name := "models_of_mem"
      kind := .soundness
      theoremName := "models_of_mem"
      file := "Lattice/Plugins/Core/Constraint/Proofs.lean" },
    -- SOUNDNESS: models is contravariantly monotone in the hypothesis set.
    { name := "models_of_subset"
      kind := .soundness
      theoremName := "models_of_subset"
      file := "Lattice/Plugins/Core/Constraint/Proofs.lean" }
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
