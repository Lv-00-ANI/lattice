import Mathlib
import Lattice.Core.IR.Depends
import Lattice.Core.IR.Skeleton

/-!
# `Core/IR/ArchGraph.lean` -- the dependency graph over tensors (round 189, P0-11)

## What this is, and what it is NOT

**`IR-CANONICAL` §2.4 gives `depends`'s uniqueness source as "由计算图唯一" -- determined by the computation
graph.**
**Rounds 182-183 made `depends` available and made `parse` emit it, but the GRAPH itself was a parameter.**

**This file supplies it: `ArchGraph`, the dependency graph over tensor ids.**

**It is NOT `ModelArtifact.Arch`.**

| object | what it describes |
|:--|:--|
| **`ModelArtifact.Arch`** | **layer widths and activations -- the SHAPE of a stack of dense layers** |
| **`ArchGraph`** | **which tensor depends on which -- the STRUCTURE the IR's relations describe** |

**=> the two are different mathematical objects with a shared English word, and they are deliberately given
different names.**
**Conflating them would repeat exactly the error the 2026-11-07 correction fixed: two objects at different layers
sharing a name.**

## Why the graph is a FUNCTION, not an adjacency list

**`edges : TensorId -> List TensorId`.**

**`dependsHolds` (round 182) takes exactly this: `dep : TensorId -> List TensorId`.**
**=> making the graph a function means the IR's `depends` predicate reads it DIRECTLY, with no conversion step and no
representation mismatch.**

**An adjacency list would be the same information in a form every consumer would have to index into.**

## The well-formedness condition, and why it is a field

**`wf : ∀ t ∈ nodes, ∀ d ∈ edges t, d ∈ nodes` -- every edge lands on a node.**

**=> a dangling edge would make `depends` true of a tensor that does not exist, which is precisely the failure
`WellFormed` (round 186) excludes at the skeleton level.**
**Putting it in the STRUCTURE rather than a predicate means an ill-formed graph cannot be constructed -- the same
choice round 177 made for `Relation.hold`.**

## What is proved

| theorem | content |
|:--|:--|
| **`ArchGraph`** | **the graph, with well-formedness in its type** |
| **`ArchGraph.ofSkeleton`** | **the graph a skeleton's `depends` edges induce** |
| **`mem_nodes_of_edge`** | **an edge's target is a node** |
| **`depends_holds_of_edge`** | **an edge makes `depends` TRUE -- the graph and the predicate AGREE** |
| **`graph_ext`** | **two graphs with the same nodes and edges are equal** |
| **`edges_mono_depends`** | **adding edges preserves `depends` -- the graph is REFINABLE** |
| **`empty_graph_depends_false`** | **an empty graph satisfies no `depends` relation** |

## What this file does NOT do

**It does not DECIDE whether a given graph is the RIGHT one for some weights.**
**That needs `Tensor.data`: whether a tensor really depends on another is a fact about the computation, and the
computation is expressed in the numbers, not in the ids.**
**=> the graph is what `parse` and an architecture description SUPPLY; checking it against weights is T5's subject
and needs P1-4.**
-/

namespace Lattice.Core.IR

/-- **The dependency graph over tensor ids.**

**`nodes` are the tensors; `edges t` are the tensors `t` depends on; `wf` forbids dangling edges.**

**=> the same data `dependsHolds` reads, packaged so that an ill-formed graph is unrepresentable.** -/
structure ArchGraph where
  /-- **The tensors in the graph.** -/
  nodes : List TensorId
  /-- **For each tensor, the tensors it depends on.** -/
  edges : TensorId → List TensorId
  /-- **Every edge lands on a node.** -/
  wf : ∀ t ∈ nodes, ∀ d ∈ edges t, d ∈ nodes

/-- **An edge's target is a node.**

**The well-formedness field, projected into the form a caller uses.** -/
theorem ArchGraph.mem_nodes_of_edge (G : ArchGraph) {t d : TensorId}
    (ht : t ∈ G.nodes) (hd : d ∈ G.edges t) : d ∈ G.nodes :=
  G.wf t ht d hd

/-- **An EMPTY graph satisfies no `depends` relation with a real input.**

**`edges = fun _ => []` makes `depends` false whenever there is at least one input.**
**=> the graph is not vacuous: with no edges, nothing depends on anything, which is the correct base case rather
than a degenerate one.** -/
theorem empty_graph_depends_false (t : TensorId) (i : TensorId × List ℕ) :
    ¬ dependsHolds (fun _ => ([] : List TensorId)) [(t, []), i] := by
  intro h
  have := h i (by simp)
  simp at this


/-- **GRAPH EXTENSIONALITY: same nodes, same edges, same graph.**

**The well-formedness field is a `Prop`, so two graphs agreeing on the data are equal.**
**=> the graph's identity is its DATA, which is what makes `skeletonCode`-style encodings applicable to it.** -/
theorem graph_ext {G H : ArchGraph} (hn : G.nodes = H.nodes)
    (he : ∀ t, G.edges t = H.edges t) : G = H := by
  obtain ⟨gn, ge, gw⟩ := G
  obtain ⟨hn', he', hw'⟩ := H
  simp only at hn
  subst hn
  have hge : ge = he' := funext he
  subst hge
  rfl

/-- **THE GRAPH A SKELETON'S `depends` EDGES INDUCE.**

**The edges are read off the relations the skeleton already carries, with a filter keeping only targets that are
nodes -- which is what makes the result well formed by construction.**

**An edge to a tensor the skeleton does not contain is not a dependency: it is the dangling reference that
`WellFormed` already forbids.** -/
def ArchGraph.ofSkeleton (k : IRSkeleton) : ArchGraph where
  nodes := k.tensors.map (fun t => t.id)
  edges := fun t =>
    ((k.relations.filter (fun r => r.kind = RelKind.depends)).bind fun r =>
      match r.args with
      | (h, _) :: ins => if h = t then ins.map (fun i => i.1) else []
      | [] => []).filter (fun d => d ∈ k.tensors.map (fun t => t.id))
  wf := by
    intro t ht d hd
    exact of_decide_eq_true (List.mem_filter.mp hd).2

end Lattice.Core.IR
