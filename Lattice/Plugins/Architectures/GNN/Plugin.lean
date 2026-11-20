/-
# Architectures.GNN Plugin -- assembly

The eleven obligations of `Manifest.lean`, discharged by
`Lattice.Lib.Architectures.RealGNNEquivariance`.

## Why the two group-action laws are obligations and not decoration

**`permActFeat_mul` / `permActFeat_one` and `permActAdj_mul` / `permActAdj_one` say that the two
permutation "actions" really ARE actions in the algebraic sense.**

**Without them, "equivariance" would be a statement about a family of maps indexed by
permutations, not about a GROUP action -- and the word would be doing no work.**
**With them, `msgPass_equivariant` is a genuine naturality square: the diagram
`h ↦ msgPass A h` commutes with the group action.**
**=> the laws are the premise that makes the equivariance statement meaningful, which is why they
sit in the same manifest.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Architectures.GNN.Manifest
import Lattice.Plugins.Architectures.GNN.Proofs
namespace Lattice.Plugins.Architectures.GNN

open Lattice.Plugins

/-- **Equivariance: one message-passing step commutes with node relabelling.** -/
def MsgPassEquivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ) (h : ι → ℝ),
    msgPass (permActAdj π A) (permActFeat π h) = permActFeat π (msgPass A h)

/-- **`MsgPassEquivariantProp` holds** -- by `msgPass_equivariant`. -/
theorem msgPassEquivariantProp_holds : MsgPassEquivariantProp := by
  intro ι _ _ π A h
  exact msgPass_equivariant π A h

/-- **Equivariance: a full layer does too.** -/
def GnnLayerEquivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (W : ℝ) (σ : ℝ → ℝ) (h : ι → ℝ),
    gnnLayer (permActAdj π A) W σ (permActFeat π h)
      = permActFeat π (gnnLayer A W σ h)

/-- **`GnnLayerEquivariantProp` holds** -- by `gnnLayer_equivariant`. -/
theorem gnnLayerEquivariantProp_holds : GnnLayerEquivariantProp := by
  intro ι _ _ π A W σ h
  exact gnnLayer_equivariant π A W σ h

/-- **Equivariance composes along depth: any finite stack of layers is equivariant.** -/
def LayerStackEquivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (W : ℝ) (σ : ℝ → ℝ) (k : ℕ) (h : ι → ℝ),
    layerStack (permActAdj π A) W σ k (permActFeat π h)
      = permActFeat π (layerStack A W σ k h)

/-- **`LayerStackEquivariantProp` holds** -- by `layerStack_equivariant`. -/
theorem layerStackEquivariantProp_holds : LayerStackEquivariantProp := by
  intro ι _ _ π A W σ k h
  exact layerStack_equivariant π A W σ k h

/-- **Law: the feature action is multiplicative.** -/
def PermActFeatMulProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π σ : Equiv.Perm ι) (h : ι → ℝ),
    permActFeat (π * σ) h = permActFeat π (permActFeat σ h)

/-- **`PermActFeatMulProp` holds** -- by `permActFeat_mul`. -/
theorem permActFeatMulProp_holds : PermActFeatMulProp := by
  intro ι _ _ π σ h
  exact permActFeat_mul π σ h

/-- **Law: the feature action is unital.** -/
def PermActFeatOneProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → ℝ), permActFeat 1 h = h

/-- **`PermActFeatOneProp` holds** -- by `permActFeat_one`. -/
theorem permActFeatOneProp_holds : PermActFeatOneProp := by
  intro ι _ _ h
  exact permActFeat_one h

/-- **Law: the adjacency action is multiplicative.** -/
def PermActAdjMulProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π σ : Equiv.Perm ι) (A : ι → ι → ℝ),
    permActAdj (π * σ) A = permActAdj π (permActAdj σ A)

/-- **`PermActAdjMulProp` holds** -- by `permActAdj_mul`. -/
theorem permActAdjMulProp_holds : PermActAdjMulProp := by
  intro ι _ _ π σ A
  exact permActAdj_mul π σ A

/-- **Law: the adjacency action is unital.** -/
def PermActAdjOneProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ℝ), permActAdj 1 A = A

/-- **`PermActAdjOneProp` holds** -- by `permActAdj_one`. -/
theorem permActAdjOneProp_holds : PermActAdjOneProp := by
  intro ι _ _ A
  exact permActAdj_one A

/-- **Invariant: the sum readout does not depend on the labelling.** -/
def ReadoutInvariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (h : ι → ℝ),
    ∑ i, permActFeat π h i = ∑ i, h i

/-- **`ReadoutInvariantProp` holds** -- by `readout_invariant`. -/
theorem readoutInvariantProp_holds : ReadoutInvariantProp := by
  intro ι _ _ π h
  exact readout_invariant π h

/-- **Invariant: an invariant readout survives any depth of equivariant layers.**

Note the right-hand side: `Φ (layerStack A W σ k h)`, NOT `Φ (permActFeat π (layerStack …))` --
because `Φ` is ALREADY assumed permutation-invariant, the relabelling collapses and the statement
becomes an equality between the readout of the permuted input and the readout of the original. -/
def ReadoutInvariantOfLayerStackProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (W : ℝ) (σ : ℝ → ℝ) (Φ : (ι → ℝ) → ℝ),
    (∀ (τ : Equiv.Perm ι) (f : ι → ℝ), Φ (permActFeat τ f) = Φ f) →
    ∀ (k : ℕ) (h : ι → ℝ),
      Φ (layerStack (permActAdj π A) W σ k (permActFeat π h))
        = Φ (layerStack A W σ k h)

/-- **`ReadoutInvariantOfLayerStackProp` holds** -- by `readout_invariant_of_layerStack`. -/
theorem readoutInvariantOfLayerStackProp_holds : ReadoutInvariantOfLayerStackProp := by
  intro ι _ _ π A W σ Φ hΦ k h
  exact readout_invariant_of_layerStack π A W σ Φ hΦ k h

/-- **Soundness: sparse message passing agrees with the dense one.** -/
def SparseAgreesDenseProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (E : Finset (ι × ι)) (h : ι → ℝ),
    sparseMsgPass E h = msgPass (indicator E) h

/-- **`SparseAgreesDenseProp` holds** -- by `sparseMsgPass_eq_msgPass`. -/
theorem sparseAgreesDenseProp_holds : SparseAgreesDenseProp := by
  intro ι _ _ E h
  exact sparseMsgPass_eq_msgPass E h

/-- **Approximation: a pointwise bound on one message-passing step.**

The bound is `M * ∑ j, |A (π.symm i) j|` -- **a per-row bound, not a global one**, and the
permutation appears because the adjacency has been relabelled. -/
def MsgPassBoundProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (h : ι → ℝ) (M : ℝ), (∀ j, |h j| ≤ M) →
    ∀ i : ι, |msgPass (permActAdj π A) (permActFeat π h) i|
      ≤ M * ∑ j, |A (π.symm i) j|

/-- **`MsgPassBoundProp` holds** -- by `msgPass_bound_perm`. -/
theorem msgPassBoundProp_holds : MsgPassBoundProp := by
  intro ι _ _ π A h M hM i
  exact msgPass_bound_perm π A h M hM i

/-- **堆叠恰好就是迭代**：`layerStack A W σ k h = (gnnLayer A W σ)^[k] h`。

**⇒ 这条排除了「堆叠里还藏着别的操作」这一可能：`layerStack` 由计数递归定义，
而递归的每一步都只是再套一层 `gnnLayer`，所以它**别无非是**那个函数的 `k` 次迭代。** -/
theorem gnnLayerStack_eq_iterate {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ) (k : ℕ) (h : ι → ℝ) :
    layerStack A W σ k h = (gnnLayer A W σ)^[k] h := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    show layerStack A W σ k (gnnLayer A W σ h) = (gnnLayer A W σ)^[k + 1] h
    rw [ih]
    simp only [Function.iterate_succ_apply, Function.iterate_succ_apply']

/-- **两段堆叠拼接**：`layerStack (m + n) h = layerStack m (layerStack n h)`。 -/
theorem gnnLayerStack_add {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ) (m n : ℕ) (h : ι → ℝ) :
    layerStack A W σ (m + n) h = layerStack A W σ m (layerStack A W σ n h) := by
  simp only [gnnLayerStack_eq_iterate, Function.iterate_add_apply]

/-- **`GNNLayerStackComposeProp`（`recovery`）：堆叠是可组合的。**

**⇒ 先堆 `n` 层再堆 `m` 层，与一次堆 `m + n` 层相同。**
**这是「层堆叠」作为时间操作的可组合性——与 `equivariance` 槽说的（置换与堆叠可交换）
是两件不同的事。** -/
def GNNLayerStackComposeProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ)
    (m n : ℕ) (h : ι → ℝ),
    layerStack A W σ (m + n) h = layerStack A W σ m (layerStack A W σ n h)

/-- **`GNNLayerStackComposeProp` holds** — 由 `gnnLayerStack_add`。 -/
theorem gnnLayerStackComposeProp_holds : GNNLayerStackComposeProp :=
  fun A W σ m n h => gnnLayerStack_add A W σ m n h

/-- **`GNNLayerStackIsIterateProp`（`completeness`）：堆叠**恰好**是迭代，别无他物。**

**⇒ 任何 `k` 层堆叠都等于 `gnnLayer` 的 `k` 次迭代。**
**这不是一句同义反复：`layerStack` 由**计数递归**定义，本条说的是
「递归的每一步都只是再套一层，没有隐藏的额外操作」——也就是这个表示的**完备性**。** -/
def GNNLayerStackIsIterateProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ)
    (k : ℕ) (h : ι → ℝ),
    layerStack A W σ k h = (gnnLayer A W σ)^[k] h

/-- **`GNNLayerStackIsIterateProp` holds** — 由 `gnnLayerStack_eq_iterate`。 -/
theorem gnnLayerStackIsIterateProp_holds : GNNLayerStackIsIterateProp :=
  fun A W σ k h => gnnLayerStack_eq_iterate A W σ k h

/-- **The graph-network carrier's proof bundle.**

Eleven claimed obligations, including the registry's FIRST `equivariance` and FIRST `invariants`
witnesses.
-/
def proof : PluginProof where
  soundness := SparseAgreesDenseProp
  laws := PermActFeatMulProp ∧ PermActFeatOneProp ∧ PermActAdjMulProp ∧ PermActAdjOneProp
  exactness := True
  approximation := MsgPassBoundProp
  recovery := GNNLayerStackComposeProp
  spatial := True
  confluence := True
  equivariance := MsgPassEquivariantProp ∧ GnnLayerEquivariantProp ∧ LayerStackEquivariantProp
  idempotence := True
  invariants := ReadoutInvariantProp ∧ ReadoutInvariantOfLayerStackProp
  completeness := GNNLayerStackIsIterateProp
  refinement := True

/-- **Every claimed obligation of the graph-network carrier is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨sparseAgreesDenseProp_holds,
         ⟨permActFeatMulProp_holds, permActFeatOneProp_holds,
          permActAdjMulProp_holds, permActAdjOneProp_holds⟩,
         True.intro,
         msgPassBoundProp_holds,
         gnnLayerStackComposeProp_holds, True.intro, True.intro,
         ⟨msgPassEquivariantProp_holds, gnnLayerEquivariantProp_holds,
          layerStackEquivariantProp_holds⟩,
         True.intro,
         ⟨readoutInvariantProp_holds, readoutInvariantOfLayerStackProp_holds⟩,
         gnnLayerStackIsIterateProp_holds, True.intro⟩

/-- **The verified graph-network carrier.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The carrier claims eleven obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 11 := rfl

end Lattice.Plugins.Architectures.GNN
