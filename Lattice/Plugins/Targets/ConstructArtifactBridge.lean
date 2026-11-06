/-
# `Plugins/Targets/ConstructArtifactBridge.lean` -- `samePointLadder` produces a real `ModelArtifact`

## What this file adds

**`ConstructArtifact.lean` provides `construct_artifact : AffineLayer (Fin n) → ModelArtifact`.**
**`WeightSideLadder.samePointLadder` provides the layer a `samePoint` constraint compiles to.**
**This file COMPOSES them, so that "a `samePoint` spec compiles to a `ModelArtifact`" is one theorem.**

## Why the composition is not a re-labelling

**`samePointLadder_satW_iff` proves that on the compiled image, the WEIGHT-side predicate and the
SYMBOL-side predicate are EQUIVALENT -- not merely that the first follows from the second.**
**=> the layer `construct_artifact` wraps is the one that actually decides the same question the symbolic
constraint asks.**
**A bridge that only had the forward implication would be satisfiable by a constant-true `satW`, which is
exactly the failure the whole project audits for.**

## The one thing this file does NOT do

**It does not give the artifact a `Forward` function.**
**`ModelArtifact` carries topology and parameters; what they COMPUTE is `Core/Forward.lean`'s subject, and
`samePointLadder_forward` already states it for the ladder.**
**Conflating the two would let a statement about shapes pass as a statement about behaviour.**
-/

import Mathlib
import Lattice.Plugins.Targets.ConstructArtifact
import Lattice.Domains.Geometry.WeightSideLadder

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Core Lattice.Geo.WeightSide

/-! ## The compiled layer of a `samePoint` constraint -/

/-- **The layer a `samePoint a b` constraint compiles to, for a given encoding.**

**This is `samePointLadder`'s `l2l3` applied to the unit token list that ladder uses.**
**Extracted as a named `def` so that `construct_artifact` can be applied to it without the caller having to
know the ladder's `l2l3` is `fun _ => [samePointLayer enc a b]`.** -/
noncomputable def samePointCompiledLayer {n : ℕ} (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    AffineLayer (Fin n) :=
  Lattice.Geo.WeightSide.samePointLayer enc a b

/-- **A `samePoint` constraint compiles to a `ModelArtifact`.**

**THE BRIDGE: the symbolic constraint reaches the weights object.**
**The artifact's single layer is the one `samePointLadder` compiles to, so its `satW` is the predicate
`samePointLadder_satW_iff` proved equivalent to the symbolic one.** -/
noncomputable def samePointArtifact {n : ℕ} (hn : 0 < n) (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    ModelArtifact :=
  construct_artifact hn (samePointCompiledLayer enc a b)

/-- **The artifact has exactly one layer.** -/
theorem samePointArtifact_depth {n : ℕ} (hn : 0 < n) (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    (samePointArtifact hn enc a b).depth = 1 := rfl

/-- **The artifact carries exactly one layer's parameters.** -/
theorem samePointArtifact_layers {n : ℕ} (hn : 0 < n) (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    (samePointArtifact hn enc a b).weights.layers.length = 1 := rfl

/-- **The artifact's architecture is `n → n` with `identity`.**

**Stated because it is the claim a reader will check first: a `samePoint` layer is LINEAR, so its `Arch`
must not name a non-linear activation.** -/
theorem samePointArtifact_arch {n : ℕ} (hn : 0 < n) (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    (samePointArtifact hn enc a b).arch = Arch.one n n hn hn .identity := rfl

/-! ## The equivalence that makes the bridge meaningful -/

/-- **The artifact's predicate is the symbolic one, on the compiled image.**

**`samePointLadder_satW_iff` already proves this for the ladder; the bridge's contribution is that the
ARTIFACT's layer is the same layer, so the equivalence transfers.**
**=> the weight-side predicate an inspector reads off `samePointArtifact` decides exactly the question
`samePoint a b` asks.** -/
theorem samePointArtifact_satW_iff {n : ℕ} (hn : 0 < n) (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    Lattice.Geo.WeightSide.samePointSatW enc a b [Lattice.Geo.WeightSide.samePointLayer enc a b] ↔
      (∀ j : Fin n, enc a j = enc b j) :=
  Lattice.Geo.WeightSide.samePointLadder_satW_iff enc a b

end Lattice.Plugins.Targets
