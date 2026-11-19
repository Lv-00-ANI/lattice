/-
# Architectures.DAG Plugin -- Manifest

The COMPUTATION-GRAPH carrier (plan P1). It is the last of the four architecture plugins, and it closes the
`confluence` obligation `ARCHITECTURE-CARRIERS.md` listed for it while no such plugin existed.

## Why a computation graph is an architecture carrier

**A domain plugin turns a CONSTRAINT into a loss or a token sequence.**
**An architecture carrier turns a PROGRAM into another program of the same shape** -- it is a *transformation of
the representation*, not a statement about what the representation means.

**=> the two are different layers, and `PluginLayer.architectures` is where the second lives.**

## What this plugin actually proves

**`denote_seq`**: evaluating a concatenation is the composition of the evaluations --
**the sequential form, and the lemma the other three are built on.**

**`denote_par`**: parallel branches evaluate as concatenation --
**which is what makes "parallel" a SCHEDULING notion rather than a semantic one.**

**`denote_resid`**: a refinement branch composes the same way.

**`dag_confluence`**: a program of PAIRWISE COMMUTING nodes gives the same result as its reverse --
**the `confluence` obligation, and the property that makes a DAG's evaluation order irrelevant.**

## What it does NOT claim

**No `idempotence`**: re-running a program is not a no-op.
**No `equivariance`**: a program transforms a value; it does not act on a group.

**No explicit edge set**: a real DAG has a partial order, and topologically sorting it produces the list this
file evaluates.
**=> the file works AFTER the sort, and `dag_confluence` is the statement that the sort's choice does not
matter -- which is the property that makes sorting worth doing.**

**Confluence needs the COMMUTING hypothesis: `noncommuting_counterexample` shows two nodes whose order changes
the result.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Architectures.DAG.Proofs

namespace Lattice.Plugins.Architectures.DAG

open Lattice.Plugins

/-- **The computation-graph carrier's manifest.**

Layer `architectures`. It requires the point-cloud representation (`domain.points`) and offers the capability
`arch.schedule`.
-/
def manifest : PluginManifest where
  name := "Architectures.DAG"
  version := ⟨1, 0, 0⟩
  layer := .architectures
  requires := ["domain.points"]
  provides := ["arch.schedule"]
  obligations := [
    -- CONFLUENCE: commuting nodes give the same result regardless of traversal direction.
    -- CARRIES ITS PROOF (`PARAMETERIZATION-AUDIT.md` item 3): the `${}` in the proposition is the statement
    -- the manifest means, not a pointer to a name that might not exist.
    verifiedObligation "dag_confluence" .confluence
      "Lattice/Plugins/Architectures/DAG/Proofs.lean" "dag_confluence"
      (∀ {α : Type} (fs : DagProgram α),
        (∀ f ∈ fs, ∀ g ∈ fs, DagCommute f g) →
        ∀ x : α, dagEval fs x = dagEval fs.reverse x) (by exact dag_confluence),
    -- SOUNDNESS: evaluation of a concatenation is the composition of evaluations.
    verifiedObligation "dag_denote_seq" .soundness
      "Lattice/Plugins/Architectures/DAG/Proofs.lean" "dag_denote_seq"
      (∀ {α : Type} (p q : DagProgram α) (x : α),
        dagEval (dagSeq p q) x = dagEval q (dagEval p x)) (by exact dag_denote_seq),
    -- EXACTNESS: parallel composition denotes the same as concatenation.
    verifiedObligation "dag_denote_par" .exactness
      "Lattice/Plugins/Architectures/DAG/Proofs.lean" "dag_denote_par"
      (∀ {α : Type} (p q : DagProgram α) (x : α),
        dagEval (dagPar p q) x = dagEval q (dagEval p x)) (by exact dag_denote_par)
  ]

/-- **The carrier claims three obligations, so its obligation list is not empty.** -/
theorem manifest_nonempty : manifest.obligations ≠ [] := by
  simp [manifest]

end Lattice.Plugins.Architectures.DAG
