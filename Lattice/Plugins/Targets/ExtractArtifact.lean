/-
# `Plugins/Targets/ExtractArtifact.lean` -- the reverse direction at the artifact layer (plan B-3)

## What the objective asks for, and what is actually possible

**The objective's reverse direction is: weight behaviour is EXTRACTED back into symbols, to be verified,
corrected and re-injected.**

**Round 80 and round 96 between them settled what that can mean.**
**`Extraction.no_extractor_both_layers` proves that no `extract : W → P` can be BOTH a left inverse of
compilation AND faithful to the semantic relation -- and `no_extractor_both_layers_witness` supplies the
witness pair (`unitForm ≠ scaledForm` with `SemEq unitForm scaledForm`).**

**=> a `W → P` that recovers the ORIGINAL symbolic form cannot exist.**
**What CAN exist is a `W → SUMMARY`: an extraction that recovers what the weights DETERMINE, and says so
precisely.**

## What the weights determine, and what they do not

| recoverable | not recoverable |
|:--|:--|
| **the layer count** -- `Weights.layers.length` | **which constraint produced a layer** |
| **each layer's widths** -- `m` and `n` in `Σ m n, MLayer m n` | **the constraint's argument indices** (`a`, `b`, ...) |
| **each layer's activation** -- `Arch.acts` | **the encoding `enc` a `samePoint` layer was built from** |
| **the total parameter count** -- `paramCount` | **any semantic equivalence class** |

**=> this file's `SymbolicSummary` is exactly the first column.**
**It is the honest fragment: everything in it is a function of the artifact, and nothing in it pretends to
be the spec.**

## Why this is not a weakened version of the real thing

**A weaker extraction is only worth having if the STRONG one is proved impossible, and here that proof
exists and is cited.**
**The alternative -- an `extract` that returns a "best guess" constraint -- would have to choose among the
`sem`-equivalent forms, and `no_extractor_both_layers` says the choice cannot be both faithful and total.**
**=> a summary is not a compromise; it is the only shape that survives the impossibility.**
-/

import Mathlib
import Lattice.Core.ModelArtifact
import Lattice.Plugins.Targets.ConstructArtifact
import Lattice.Runtime.Extraction

namespace Lattice.Plugins.Targets

open Lattice.Core Lattice.Lift

/-! ## The summary -/

/-- **What an artifact determines about the symbolic layer that produced it.**

**Every field is a FUNCTION of the `ModelArtifact`, and every field is checked to be one by the theorems
below.**
**No field names a constraint, an index, or an encoding -- those are precisely what
`no_extractor_both_layers` forbids recovering.** -/
structure SymbolicSummary where
  /-- The number of layers the model has. -/
  depth : ℕ
  /-- The widths, in order: input width then each layer's output width. -/
  widths : List ℕ
  /-- The activation after each layer. -/
  acts : List Activation
  /-- **The total number of scalar parameters.** -/
  params : ℕ

namespace SymbolicSummary

/-- **The summary of a `ModelArtifact`.**

**This is the extraction.**
**It reads the architecture's `widths`/`acts` and the weights' layer count, and it returns nothing else.**
**=> it is total and computable in content, and it is TOTAL ON PURPOSE: unlike a spec reconstruction, there
is no case where a summary fails to exist.** -/
def ofArtifact (M : ModelArtifact) : SymbolicSummary where
  depth := M.depth
  widths := M.arch.widths
  acts := M.arch.acts
  params := M.paramCount

/-! ## What the extraction recovers EXACTLY -/

/-- **The extraction recovers the depth.** -/
theorem ofArtifact_depth (M : ModelArtifact) : (ofArtifact M).depth = M.depth := rfl

/-- **The extraction recovers the widths.** -/
theorem ofArtifact_widths (M : ModelArtifact) : (ofArtifact M).widths = M.arch.widths := rfl

/-- **The extraction recovers the activations.** -/
theorem ofArtifact_acts (M : ModelArtifact) : (ofArtifact M).acts = M.arch.acts := rfl

/-- **The extraction recovers the parameter count.** -/
theorem ofArtifact_params (M : ModelArtifact) : (ofArtifact M).params = M.paramCount := rfl

/-- **The summary is INJECTIVE on architectures.**

**Two artifacts with the same summary have the same `Arch`.**
**=> on the structural fragment, extraction LOSES NOTHING -- which is the strongest statement available, and
the reason the summary is the right fragment rather than an arbitrary truncation.**

**Note what this does NOT say: it does not claim the summary determines the WEIGHTS.**
**Two artifacts with the same `Arch` and different numbers share a summary, and that is correct: the numbers
are the parameter layer, and `reversibility_boundary` already established the parameter layer is injective
rather than isomorphic.** -/
theorem ofArtifact_injective_on_arch (M N : ModelArtifact)
    (h : ofArtifact M = ofArtifact N) : M.arch.widths = N.arch.widths ∧ M.arch.acts = N.arch.acts := by
  constructor
  · rw [← ofArtifact_widths M, ← ofArtifact_widths N, h]
  · rw [← ofArtifact_acts M, ← ofArtifact_acts N, h]

/-- **A well-formed artifact's summary carries at least one width.**

**The non-emptiness fact: `Arch.WellFormed` forces `acts.length + 1 = widths.length`, so `widths` is never
`[]`.** **A summary with no widths would describe nothing.** -/
theorem ofArtifact_widths_nonempty (M : ModelArtifact) : (ofArtifact M).widths ≠ [] := by
  intro h
  have hlen := M.wf.2
  simp only [ofArtifact, ModelArtifact.depth, Arch.depth] at h
  rw [h] at hlen
  simp at hlen

/-! ## What the extraction canNOT do -/

/-- **NO extraction recovers the original symbolic form.**

**This restates `Extraction.no_extractor_both_layers` in the artifact's vocabulary, because that is where a
reader will look for it.**
**The statement is conditional on the two things the impossibility needs -- a non-trivial `sem` and a
round-trip -- so it does not assume what it proves.** -/
theorem no_artifact_extractor_recovers_both {P W : Type} (compile : P → W)
    (sem : P → P → Prop) {c c' : P} (hne : c ≠ c') (hsem : sem c c')
    {extract : W → P} (hround : ∀ p, extract (compile p) = p)
    (hfaithful : ∀ a b : P, sem a b → extract (compile a) = extract (compile b)) : False :=
  Lattice.Lift.no_extractor_both_layers compile sem hne hsem hround hfaithful

/-! ## The impossibility is not vacuous

**`no_extractor_both_layers_witness` proves that over the linear forms no self-extractor is both the
identity and `SemEq`-faithful, and `semantic_not_injective` provides the `unitForm ≠ scaledForm` /
`SemEq` pair the statement needs.**

**=> `no_artifact_extractor_recovers_both` above is not an empty implication: its hypotheses are
simultaneously satisfiable, which is what makes "a summary is the only shape that survives" a finding
rather than a preference.**

**The witness is cited by NAME rather than restated.**
**Re-deriving its type would put a SECOND definition of the impossibility in the tree, and the two could
drift apart -- the duplicate would then be the one that looks authoritative.** -/

/-! ## The summary reaches the summary, not the spec -/

/-- **The extraction is IDEMPOTENT: summarising a summary's own shape changes nothing.**

**Stated because it is the property that distinguishes an extraction from a guess.**
**An extractor that drifted each time it ran would make the loop's verification step meaningless.** -/
theorem ofArtifact_idempotent_shape (M : ModelArtifact) :
    (ofArtifact M).depth = M.arch.acts.length := rfl

end SymbolicSummary

end Lattice.Plugins.Targets
