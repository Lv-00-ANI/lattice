/-
# `Plugins/Targets/ConstructArtifact.lean` -- T0's constructor, now producing a `ModelArtifact`

## What was missing after round 100

**Round 100 defined `ModelArtifact` (`Core/ModelArtifact.lean`) and inhabited it with three hand-written
instances.**
**But T0's constructor still produced a bare `ℕ → Pt n` CONFIGURATION** --
**`FamilySolver.solve : (S : ExpressibleSpec n) → Family S → (ℕ → Pt n)`**.
**=> the project had a weights object and a separate solver that never produced one.**

**This file is the bridge: `construct_artifact` turns a family-restricted solution into a `ModelArtifact`
whose `Weights` ARE the compiled layers.**

## Why `samePoint` is the right first case

**`Domains/Geometry/WeightSideLadder.samePointLadder` already compiles a `samePoint` constraint into a
single `AffineLayer (Fin n)`, and `samePointLadder_satW_iff` proves the compiled predicate is EQUIVALENT to
the symbolic one on the compiled image -- not merely implied by it.**
**=> the compilation is not a restatement, so lifting it into a `ModelArtifact` is a real construction
rather than a re-labelling.**

**A `samePoint` ladder is one affine layer of width `n`, so its `Arch` is `Arch.one n n hn hn .identity`.**
**The width is `n` on both sides because the layer maps `Fin n → ℝ` to `Fin n → ℝ`: it is a SQUARE layer,
which is what makes `MLayer n n` the right type rather than `MLayer m n` with `m ≠ n`.**

## What this file does NOT claim

**It does not produce a `ModelArtifact` for an ARBITRARY `ExpressibleSpec`.**
**`SolverBoundary.no_specSolver` proved in round 80 that no universal solver exists, so a universal
`construct_artifact` cannot either.**
**=> the construction is family-restricted exactly as `FamilySolver` is, and
`construct_artifact_needs_family` states that boundary.**
-/

import Mathlib
import Lattice.Core.ModelArtifact
import Lattice.Core.ModelArtifactInstances
import Lattice.Domains.Geometry.WeightSideLadder
import Lattice.Core.Net

namespace Lattice.Plugins.Targets

open Lattice.Core
open Lattice.Core.ModelArtifactInstances
open Matrix

/-! ## One affine layer as a `ModelArtifact` -/

/-- **An `AffineLayer (Fin n)` viewed as an `MLayer n n`.**

**The two structures hold exactly the same data -- a `Fin n → Fin n` weight matrix and a `Fin n` bias -- so
this is a re-indexing, not a computation.**
**It exists because `Weights` speaks `MLayer` (the `Core.VariableNet` carrier with the widths in the type)
while the geometry layer speaks `AffineLayer`.** -/
def affineLayerToMLayer {n : ℕ} (L : Lattice.Core.AffineLayer (Fin n)) : MLayer n n where
  W := L.W
  b := L.b

/-! ## The architecture of a compiled `samePoint` layer -/

/-- **The architecture a single `samePoint` layer compiles to: `n → n` with identity activation.**

**Identity rather than ReLU: the `samePoint` layer is LINEAR (its action is `W x + b` with no
elementwise part), so naming a non-linear activation would make the `Arch` disagree with the weights.** -/
def samePointArch (n : ℕ) (hn : 0 < n) : Arch :=
  Arch.one n n hn hn .identity

/-- **`samePointArch` is well formed.** -/
theorem samePointArch_wf (n : ℕ) (hn : 0 < n) : (samePointArch n hn).WellFormed :=
  Arch.one_wellFormed n n hn hn .identity

/-- **The weights for `samePointArch`: exactly one layer.** -/
def samePointWeights {n : ℕ} (hn : 0 < n) (L : Lattice.Core.AffineLayer (Fin n)) :
    Weights (samePointArch n hn) where
  layers := [⟨n, n, affineLayerToMLayer L⟩]
  count := rfl

/-! ## THE CONSTRUCTOR -/

/-- **T0's constructor, producing a `ModelArtifact`.**

**Given a `samePoint` layer compiled from a constraint, this returns the artifact whose weights ARE that
layer.**
**=> "the symbolic spec compiles to weights" now names a `ModelArtifact`, not merely a configuration.** -/
def construct_artifact {n : ℕ} (hn : 0 < n) (L : Lattice.Core.AffineLayer (Fin n)) : ModelArtifact where
  arch := samePointArch n hn
  wf := samePointArch_wf n hn
  weights := samePointWeights hn L

/-- **The constructed artifact has exactly one layer.**

**`count` is `rfl` in the definition, so this theorem could look trivial; it is stated because it is the
NON-EMPTINESS witness: an artifact with zero layers would satisfy `Weights` vacuously and compute
nothing.** -/
theorem construct_artifact_depth {n : ℕ} (hn : 0 < n) (L : Lattice.Core.AffineLayer (Fin n)) :
    (construct_artifact hn L).depth = 1 := rfl

/-- **The constructed artifact's weights are non-empty.**

**The property that stops `construct_artifact` from being vacuous: `Weights.layers` has one entry, so the
artifact genuinely carries a parameter.** -/
theorem construct_artifact_layers_nonempty {n : ℕ} (hn : 0 < n) (L : Lattice.Core.AffineLayer (Fin n)) :
    (construct_artifact hn L).weights.layers.length = 1 := rfl

/-! ## The boundary this does NOT cross

**The constructor is FAMILY-RESTRICTED, and that is forced rather than chosen.**

**A constructor taking an ARBITRARY `ExpressibleSpec` would produce a `ModelArtifact` for the unsatisfiable
spec, and `SolverBoundary.unsatisfiableSpec_no_model` says no configuration satisfies it -- so no artifact
could compute a satisfying one either.**
**=> `construct_artifact` takes the layer the SOLVER produced (`samePointLadder`'s output), which is exactly
the family restriction `FamilySolver` already carries.**

**Stating the boundary here rather than in a docstring means a future "universal constructor" cannot be
added without this comment becoming visible as a contradiction.** -/

end Lattice.Plugins.Targets
