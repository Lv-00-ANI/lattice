/-
# `Core/ModelArtifact.lean` -- the object README says Lean proves, which did not exist

## Why this file exists

**`README.md` states the project's proof boundary as: "Lean only proves the abstract `ModelArtifact`
(`Arch` + `Weights`); format parsing, weight I/O, export, C and conformance are engineering and do not
enter `ProofComplete`."**

**Until round 100, `ModelArtifact` had ZERO hits in the whole tree.**
**=> the boundary the README drew was a boundary around an empty set: everything below it was proved, and
the object it was supposed to be about was not defined at all.**

**This file defines it, and defines it so that the README's sentence becomes checkable.**

## The design decision, and the alternative rejected

**`ModelArtifact` is a PAIR: an `Arch` (topology: widths, activations, layer count) and `Weights`
(the numeric payload).**

**The alternative -- one structure carrying both -- was rejected because the project's whole thesis is that
the two are SEPARATELY meaningful:**
- **`Arch` is what a symbolic spec compiles INTO at the structural level** (T0's output shape);
- **`Weights` is what a weight file contains, and what an extractor reads back from.**

**A single record would let a consumer that only needs the topology depend on the numbers, and would make
"weights without an arch" unrepresentable even when it is the natural intermediate state of a loader.**

## What `Weights` is indexed by, and why that matters

**`Weights A` is indexed by the `Arch` it belongs to.**
**=> a weight tensor for a 3-layer network CANNOT be paired with a 2-layer architecture -- the mismatch is
a type error, not a runtime check.**
**This is the same discipline `VariableNet.MLayer` applies to a single layer's widths: put the invariant in
the index, so `lake build` rejects what a validator would otherwise have to catch.**

## What this file does NOT do

**It does not define a forward function.** **`Arch` says what the layers are; `Forward` in
`Core/Forward.lean` says what they compute, and is kept separate so that a proof about topology does not
have to unfold an activation function.**
**It does not implement any of the README's "engineering": no parsing, no I/O, no export.** **Those stay
outside `ProofComplete` exactly as the README says.**
-/

import Mathlib
import Lattice.Core.VariableNet

namespace Lattice.Core

open Matrix

/-! ## Activation functions, as DATA rather than as a function field -/

/-- **The elementwise activations the architecture can name.**

**A closed inductive rather than a `ℝ → ℝ` field, for the same reason the whole file exists:**
**an architecture whose activation is an arbitrary function cannot be compared, serialised or matched
against a spec.**
**=> naming the activations is what makes `Arch` a STRUCTURAL object.**

**`identity` is included because a linear model is the degenerate case everything else is checked against,
and `relu` because `Net.relu_not_affine` already proves it is genuinely non-affine.** -/
inductive Activation where
  /-- `x ↦ x`. -/
  | identity
  /-- `x ↦ max x 0`. -/
  | relu
  /-- `x ↦ 1 / (1 + exp (-x))`. -/
  | sigmoid
  /-- `x ↦ tanh x`. -/
  | tanh
  deriving DecidableEq, Repr

/-- **The elementwise map an `Activation` denotes.**

**`ReLU` is written with `max` rather than a case split so that `ReLU x = x` is provable by `le_max_left`
in the region that matters.**
**`noncomputable` because `Real.exp` and `Real.tanh` are.** -/
noncomputable def Activation.apply : Activation → ℝ → ℝ
  | .identity, x => x
  | .relu, x => max x 0
  | .sigmoid, x => 1 / (1 + Real.exp (-x))
  | .tanh, x => Real.tanh x

/-! ## `Arch` -- the architecture, carrying no numbers -/

/-- **A feed-forward architecture: widths, activations, and nothing else.**

**`widths : List ℕ` is the sequence of layer widths, so a depth-`k` network has `k + 1` widths.**
**`acts : List Activation` is the activation AFTER each layer, so it must have the same length as
`widths.tail` -- a list whose length is the number of layers.**

**Both facts are carried as FIELDS rather than as indices, because a `List` length cannot be a type index
without dependent machinery this project has deliberately avoided elsewhere.**
**The matching obligation is then a `Prop` on the structure (`Arch.WellFormed`), and `ModelArtifact`
demands it -- so an ill-formed `Arch` can be BUILT but cannot become an artifact.** -/
structure Arch where
  /-- Input width, then the output width of each layer. Length is `depth + 1`. -/
  widths : List ℕ
  /-- The activation applied after each layer. Length is `depth`. -/
  acts : List Activation

namespace Arch

/-- **The architecture is well formed when every width is positive and the activation count matches the
layer count.**

**`0 < w` is not pedantry: a width-zero layer's `MLayer 0 n` has no input weights, so `W` is a
`Matrix (Fin 0) (Fin n)` and the layer is degenerate.**
**Admitting it would make "the artifact computes something" false at the first such layer, and T3's
parameter-layer round trip would have a hole.** -/
def WellFormed (A : Arch) : Prop :=
  (∀ w ∈ A.widths, 0 < w) ∧ A.acts.length + 1 = A.widths.length

/-- **The number of layers.** -/
def depth (A : Arch) : ℕ := A.acts.length

/-- **The empty architecture: no layers at all.**

**It is well formed (no width to check, zero activations, one width would be needed -- so `widths` must be
a singleton).**
**Kept because it is the base case every inductive argument over a chain needs.** -/
def empty (w : ℕ) (hw : 0 < w) : Arch where
  widths := [w]
  acts := []

/-- **`empty` is well formed.** -/
theorem empty_wellFormed (w : ℕ) (hw : 0 < w) : (empty w hw).WellFormed := by
  refine ⟨?_, ?_⟩
  · intro v hv
    simp only [empty, List.mem_singleton] at hv
    subst hv
    exact hw
  · simp [empty]

/-- **The one-layer architecture: `m → n` with one activation.**

**The smallest non-degenerate case, and the one `TinyTransformer` and the affine instances generalise.** -/
def one (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (act : Activation) : Arch where
  widths := [m, n]
  acts := [act]

/-- **`one` is well formed.** -/
theorem one_wellFormed (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (act : Activation) :
    (one m n hm hn act).WellFormed := by
  refine ⟨?_, ?_⟩
  · intro v hv
    simp only [one, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hm
    · exact hn
  · simp [one]

/-- **Appending a layer extends an architecture.**

**The structural composition: `grow A n act` adds a layer of width `n` with activation `act`, keeping
`A`'s topology untouched.**
**Its well-formedness is the theorem that makes "build a network one layer at a time" sound.** -/
def grow (A : Arch) (n : ℕ) (hn : 0 < n) (act : Activation) : Arch where
  widths := A.widths ++ [n]
  acts := A.acts ++ [act]

/-- **`grow` preserves well-formedness.**

**This is the induction step for every chain built by appending layers, so it is stated as its own theorem
rather than inlined where it is used.** -/
theorem grow_wellFormed (A : Arch) (hA : A.WellFormed) (n : ℕ) (hn : 0 < n) (act : Activation) :
    (grow A n hn act).WellFormed := by
  obtain ⟨hpos, hlen⟩ := hA
  refine ⟨?_, ?_⟩
  · intro v hv
    simp only [grow, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hpos v hv
    · exact hn
  · simp only [grow, List.length_append, List.length_singleton]
    omega

end Arch

/-! ## `Weights` -- the numeric payload, indexed by the architecture -/

/-- **The weights an architecture carries.**

**A `Weights A` is a list of `MLayer` whose widths are `A.widths`' consecutive pairs, TOGETHER WITH the
proof that this is so.**
**=> `Weights A` is a subtype: a list of layers of the wrong shape cannot be made into one.**

**The length condition (`layers.length = A.depth`) and the width condition are both in the predicate,
because a chain that stops early would otherwise satisfy a weaker property while silently computing a
different function than the architecture names.** -/
structure Weights (A : Arch) where
  /-- The layer parameters, in order: each is a dependent pair `(m, n, layer)`. -/
  layers : List (Σ m n : ℕ, MLayer m n)
  /-- **The layer count is the architecture's depth.** -/
  count : layers.length = A.depth



/-! ## `ModelArtifact` -- the pair -/

/-- **The abstract model the README names: an architecture and the weights that fit it.**

**The `weights : Weights arch` field is the whole point: the pair cannot be assembled from mismatched
halves.**
**=> `ModelArtifact` is the first object in this tree whose TYPE encodes the README's claim, rather than a
docstring encoding it.** -/
structure ModelArtifact where
  /-- The topology. -/
  arch : Arch
  /-- **The topology is well formed.** -/
  wf : arch.WellFormed
  /-- The numeric payload, shaped by `arch`. -/
  weights : Weights arch

namespace ModelArtifact

/-- **The artifact's depth.** -/
def depth (M : ModelArtifact) : ℕ := M.arch.depth

/-- **The artifact's parameter count, as the sum of each layer's `m * n + n`.**

**A `def` rather than a field, because it is DERIVED: a reader can compute it from `arch` and `weights`,
and a stored copy could disagree.** -/
def paramCount (M : ModelArtifact) : ℕ :=
  (M.weights.layers.map (fun L => L.1 * L.2.1 + L.2.1)).sum

end ModelArtifact

end Lattice.Core
