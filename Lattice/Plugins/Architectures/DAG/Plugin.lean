/-
# Architectures.DAG Plugin -- the verified carrier

The three obligations of `Manifest.lean`, discharged by
`Lattice/Plugins/Architectures/DAG/Proofs.lean`.

## The three propositions

| proposition | content |
|:--|:--|
| **`DAGConfluenceProp`** | **commuting nodes give the same result in either direction** |
| **`DAGDenoteSeqProp`** | **a concatenation evaluates as the composition** |
| **`DAGDenoteParProp`** | **parallel composition denotes as concatenation** |

**The first is the `confluence` slot -- the FIRST non-`True` `confluence` in an architecture plugin in this
tree.**

## What this plugin does NOT claim

**`idempotence` and `equivariance` are `True`, because a program is neither idempotent nor a group action.**
**=> the slots that would be vacuous are marked `True` rather than given a weakened statement that would look
like a claim.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Architectures.DAG.Manifest
import Lattice.Plugins.Architectures.DAG.Proofs

namespace Lattice.Plugins.Architectures.DAG

open Lattice.Plugins

/-- **Confluence: commuting nodes give the same result as their reverse.** -/
def DAGConfluenceProp : Prop :=
  ∀ {α : Type} (fs : DagProgram α),
    (∀ f ∈ fs, ∀ g ∈ fs, DagCommute f g) → ∀ x : α, dagEval fs x = dagEval fs.reverse x

/-- **`laws` 槽位：`dagEval` 是 `List` 幺半群在 `α → α` 上的**作用**。** -/
def DAGEvalMonoidActionProp : Prop :=
  (∀ {α : Type} (x : α), dagEval (∅ : DagProgram α) x = x) ∧
  (∀ {α : Type} (p q : DagProgram α) (x : α),
      dagEval (p ++ q) x = dagEval q (dagEval p x)) ∧
  (∀ {α : Type} (p q r : DagProgram α) (x : α),
      dagEval ((p ++ q) ++ r) x = dagEval (p ++ (q ++ r)) x)

/-- **`DAGEvalMonoidActionProp` holds** -- by the three `dagEval_*` laws. -/
theorem dagEvalMonoidActionProp_holds : DAGEvalMonoidActionProp := by
  refine ⟨?_, ?_, ?_⟩
  · intro α x; exact dagEval_nil x
  · intro α p q x; exact dagEval_append p q x
  · intro α p q r x; exact dagEval_append_assoc p q r x

/-- **`DAGConfluenceProp` holds** -- by `dag_confluence`. -/
theorem dagConfluenceProp_holds : DAGConfluenceProp := by
  intro α fs h x
  exact dag_confluence fs h x

/-- **Soundness: a concatenation evaluates as the composition.** -/
def DAGDenoteSeqProp : Prop :=
  ∀ {α : Type} (p q : DagProgram α) (x : α), dagEval (dagSeq p q) x = dagEval q (dagEval p x)

/-- **`DAGDenoteSeqProp` holds** -- by `dag_denote_seq`. -/
theorem dagDenoteSeqProp_holds : DAGDenoteSeqProp := by
  intro α p q x
  exact dag_denote_seq p q x

/-- **Exactness: parallel composition denotes as concatenation.** -/
def DAGDenoteParProp : Prop :=
  ∀ {α : Type} (p q : DagProgram α) (x : α), dagEval (dagPar p q) x = dagEval q (dagEval p x)

/-- **`DAGDenoteParProp` holds** -- by `dag_denote_par`. -/
theorem dagDenoteParProp_holds : DAGDenoteParProp := by
  intro α p q x
  exact dag_denote_par p q x

/-- **The computation-graph carrier's proof bundle.**

**`confluence` filled here -- the first non-`True` confluence in an architecture plugin.** -/
def proof : PluginProof where
  soundness := DAGDenoteSeqProp
  laws := DAGEvalMonoidActionProp
  exactness := DAGDenoteParProp
  approximation := True
  recovery := True
  spatial := True
  confluence := DAGConfluenceProp
  equivariance := True
  idempotence := True
  invariants := True
  completeness := True
  refinement := True

/-- **Every claimed obligation of the computation-graph carrier is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨dagDenoteSeqProp_holds,
         dagEvalMonoidActionProp_holds,
         dagDenoteParProp_holds,
         True.intro, True.intro, True.intro,
         dagConfluenceProp_holds,
         True.intro, True.intro, True.intro, True.intro, True.intro⟩

/-- **The verified computation-graph carrier.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The carrier claims three obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 3 := rfl

end Lattice.Plugins.Architectures.DAG
