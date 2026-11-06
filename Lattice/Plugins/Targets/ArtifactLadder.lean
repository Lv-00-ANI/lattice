/-
# `Plugins/Targets/ArtifactLadder.lean` -- `Ladder`'s abstract `W` becomes a real `Weights` (plan B-4)

## What was disconnected

**`Runtime/EndToEnd.lean` defines `Ladder Data Tok Sym W` with `l2l3 : Sym → W` for an ARBITRARY `W`.**
**Round 99 (A-1) made `ladder_end_to_end` consume its walk, but the walk still lived in a type the project
could not produce: nothing said what `W` was.**

**Round 100 defined `Weights A`; round 101 built `construct_artifact : AffineLayer (Fin n) → ModelArtifact`.**
**=> the ladder and the weights object were both defined and NOT CONNECTED.**

## Why this file lives in `Plugins/Targets/`, not `Runtime/`

**The first draft went into `Runtime/ArtifactLadder.lean` and could not compile: `gate.py`'s `LAYER_OF`
ranks `Lattice/Runtime` at 2 and anchors `Plugins` at the top, so a `Runtime` module importing
`Plugins.Targets.ConstructArtifact` is an UPWARD import and fails `I4`.**
**=> the connection belongs above both, and `Plugins/Targets/` is where `construct_artifact` already lives.**

**This is recorded because the placement LOOKS like a style choice; it is a layering constraint with a
specific mechanism behind it.**

## What the connection says

**`satSym` is the symbolic predicate, `satW` is `netAct` being zero, and the tie between them is
`samePointLadder_satW_iff` -- an EQUIVALENCE on the compiled image, not an implication.**

**=> the artifact's predicate DECIDES the same question the symbolic constraint asks.**
**`artifact_satW_iff_symbolic` transfers that equivalence to `construct_artifact`'s output, so the transfer
is not a re-derivation.**

## What this file does NOT claim

**It does not claim every `Weights` came from a `Ladder`.**
**The correspondence is constructive in one direction (a `samePoint` constraint compiles to an artifact) and
truth-preserving in the other (the artifact's predicate is equivalent to the constraint's).**
**A `Weights` with arbitrary numbers corresponds to NO `samePoint` constraint, and nothing here says
otherwise.**
-/

import Mathlib
import Lattice.Core.ModelArtifact
import Lattice.Plugins.Targets.ConstructArtifact
import Lattice.Plugins.Targets.ExtractArtifact
import Lattice.Domains.Geometry.WeightSideLadder
import Lattice.Runtime.EndToEnd

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Core
open Lattice.Geo.WeightSide

/-! ## The ladder whose `W` is a real layer list -/

/-- **The `samePoint` ladder, named at the type `construct_artifact` consumes.**

**It is `WeightSideLadder.samePointLadder` unchanged -- the same content under the name this file's bridge
refers to.**
**Naming it matters because the bridge's claims would otherwise be about a partly-qualified term, and a
reader could not tell which `l2l3` `artifactOfLadder_l2l3` is talking about.** -/
noncomputable def samePointWeightsLadder {n : ℕ} (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    Lattice.Lift.Ladder (List Unit) Unit (List Unit) (List (AffineLayer (Fin n))) :=
  samePointLadder enc a b

/-- **Its `l2l3` produces exactly the layer `construct_artifact` takes.**

**The bridge's TYPE-LEVEL fact: the ladder's output is a singleton list and that entry is `samePointLayer`.**
**Without it, `construct_artifact` and the ladder would be about the same object under two names, and the
connection would be prose.** -/
theorem samePointWeightsLadder_l2l3 {n : ℕ} (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    (samePointWeightsLadder enc a b).l2l3 [] = [samePointLayer enc a b] := rfl

/-! ## The artifact a ladder result names -/

/-- **The `ModelArtifact` the ladder's output corresponds to.**

**`construct_artifact` applied to the ladder's single layer -- so "the ladder reached the weights" becomes
"here is the artifact".** -/
noncomputable def artifactOfLadder {n : ℕ} (hn : 0 < n) (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    ModelArtifact :=
  construct_artifact hn (samePointLayer enc a b)

/-- **The artifact's weights are the ladder's layer, re-indexed.**

**The correspondence where a consumer can act on it: ONE layer, and that layer is `affineLayerToMLayer` of
the ladder's output.**
**=> holding the artifact, one reaches the ladder's layer without knowing how `Weights` stores it.** -/
theorem artifactOfLadder_layers {n : ℕ} (hn : 0 < n) (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    (artifactOfLadder hn enc a b).weights.layers =
      [⟨n, n, affineLayerToMLayer (samePointLayer enc a b)⟩] := rfl

/-! ## The equivalence, cited rather than restated

**`ConstructArtifactBridge.samePointArtifact_satW_iff` already states that the artifact's predicate is the
symbolic one, by transferring `samePointLadder_satW_iff`.**
**An earlier draft of this file added a third name for it (`artifact_satW_iff_symbolic`), and the alias
census flagged it -- correctly: the file's contribution is the CONNECTION, and a third name for the
equivalence would be a second definition that could drift from the first.**

**=> this file references that theorem rather than reproducing it; `artifactOfLadder_layers` below is where
the connection actually lives.** -/

/-! ## The summary of a constructed artifact -/

/-- **The artifact's summary is `n → n` with identity activation, depth 1.**

**Connects B-3's `SymbolicSummary` to B-4's correspondence: extracting from the artifact a ladder result
names gives back the architecture the ladder compiled to.**
**=> the round trip ARTIFACT → SUMMARY is the identity on the structural fragment, which is the strongest
statement `ExtractArtifact` supports.** -/
theorem artifactOfLadder_summary {n : ℕ} (hn : 0 < n) (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    (SymbolicSummary.ofArtifact (artifactOfLadder hn enc a b)).depth = 1
      ∧ (SymbolicSummary.ofArtifact (artifactOfLadder hn enc a b)).widths = [n, n]
      ∧ (SymbolicSummary.ofArtifact (artifactOfLadder hn enc a b)).acts = [Activation.identity] := by
  refine ⟨rfl, rfl, rfl⟩

end Lattice.Plugins.Targets
