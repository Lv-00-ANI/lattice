/-
# `Plugins/Architectures/CarrierAdditions.lean` -- the three new carriers as `ProofComplete` conjuncts (plan P2)

## The defect this file repairs

**Rounds 126-128 built `Conv`, `Attention` and `DAG`, and all three are registered in `proofRegistry`.**
**=> `ProofComplete`'s `PluginRegistryComplete` conjunct now covers them -- but only at the REGISTRY level.**

**What `PluginRegistryComplete` checks about a plugin is that its manifest is well-formed and its proof bundle
is discharged.**
**It does NOT check that any particular capability is NON-TRIVIAL: a plugin whose `equivariance` slot is `True`
satisfies the registry exactly as well as one whose `equivariance` is a real theorem.**

**=> the three carriers' actual content -- two equivariances and one confluence -- is NOT what the predicate
asserts, even though the plugins are registered.**

## What this file conjoins

| conjunct | content |
|:--|:--|
| **`a_conv_equivariance`** | **convolution is translation-equivariant** |
| **`a_attention_equivariance`** | **attention is permutation-equivariant** |
| **`a_dag_confluence`** | **commuting nodes give the same result reversed** |

**=> these are the three NON-`True` capabilities the carriers claim, and conjoining them makes the predicate
assert that the capabilities are real rather than merely declared.**

## Why not conjoin the whole `proof.Holds` of each plugin

**`PluginProof.Holds` is a conjunction of TWELVE slots, and in these three plugins nine of them are `True`.**
**Conjoining `proof.Holds` would therefore add nothing beyond what `PluginRegistryComplete` already implies,
while making the reader think twelve facts had been checked.**

**=> the three substantive slots are conjoined individually, and the file says why the other nine are not.**

## What this does NOT claim

**It does not claim the carriers are CORRECT as implementations of convolution, attention or DAG scheduling.**
**Each theorem is about a small mathematical model -- cross-correlation, softmax pooling, list evaluation -- and
the files say where each model stops.**
**=> conjoining them asserts that the MODELS have the stated properties, which is what the plugins claim, and
nothing more.**
-/

import Mathlib
import Lattice.Plugins.Architectures.Conv.Plugin
import Lattice.Plugins.Architectures.Attention.Plugin
import Lattice.Plugins.Architectures.DAG.Plugin

namespace Lattice.Plugins.Architectures

/-! ## The three substantive capabilities -/

/-- **`Conv`'s equivariance, at the manifest's vocabulary.** -/
def a_conv_equivariance : Prop :=
  Conv.ConvEquivarianceProp

/-- **`Attention`'s equivariance, at the manifest's vocabulary.** -/
def a_attention_equivariance : Prop :=
  Attention.AttentionPermEquivarianceProp

/-- **`DAG`'s confluence, at the manifest's vocabulary.** -/
def a_dag_confluence : Prop :=
  DAG.DAGConfluenceProp

/-! ## The three together -/

/-- **The architecture carriers' contribution to `ProofComplete`.**

**Three non-`True` capabilities, conjoined as a unit.**
**=> the predicate now asserts that the carriers' equivariance and confluence claims are THEOREMS, not just
manifests.** -/
def ArchCarrierAdditions : Prop :=
  a_conv_equivariance ∧ a_attention_equivariance ∧ a_dag_confluence

/-- **`ArchCarrierAdditions` holds.** -/
theorem archCarrierAdditions_holds : ArchCarrierAdditions :=
  ⟨Conv.convEquivarianceProp_holds, Attention.attentionPermEquivarianceProp_holds,
   DAG.dagConfluenceProp_holds⟩

end Lattice.Plugins.Architectures
