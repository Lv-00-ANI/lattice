import Mathlib

/-!
# `Lattice.Core.Simulation` -- forward simulation, the shape of every correctness theorem

## Why this file exists

Every "the transformation preserves meaning" theorem in the project -- whether the
transformation is a compiler pass, a symbol-to-weight embedding, or a repair step --
has the same shape: **each behaviour of the source is matched by a behaviour of the
target, under a relation between their states.**

Rather than restate that shape once per theorem, it is stated once here and reused.
This follows the CompCert organisation (a forward simulation per pass, composed along
the pipeline) and reuses the skeleton that the legacy tree had already built in
`RealSemanticsPreservation` but never connected to anything: that file imported only
`Mathlib` and no LATTICE module at all, so its `sim_comp` had zero consumers.

## What was kept and what was generalised

Kept verbatim in meaning: `LTS`, `Star`, `ForwardSim`, `sim_id`, `sim_comp`, `sim_mono`.

Generalised:

* the legacy `Star` was fixed to a *single* label `l` for the whole path. Here both
  the single-label `Star` and an arbitrary-label `StarAny` are provided, because
  pipelines use a fixed transition label while verifying a *program* needs sequences
  of distinct labels.
* the legacy version had no notion of *initial* and *final* states, so it could only
  state "each step is matched", not "each run is matched". `run_preserved` closes that:
  it lifts stepwise simulation to whole executions.
-/

namespace Lattice.Core

/-- A labelled transition system.

`step s l t` means: from state `s`, the system may take a transition labelled `l`
and arrive at `t`. -/
structure LTS (S : Type*) (L : Type*) where
  /-- The transition relation. -/
  step : S → L → S → Prop

/-- Multi-step reachability under a single fixed label. -/
abbrev Star {S L : Type*} (R : S → L → S → Prop) (s : S) (l : L) (t : S) : Prop :=
  Relation.ReflTransGen (fun a b => R a l b) s t

/-- Multi-step reachability under an arbitrary sequence of labels.

Defined by recursion on the label list rather than through a product relation, so
that the induction principle is the list's own and proofs stay short. -/
inductive StarAny {S L : Type*} (R : S → L → S → Prop) : S → List L → S → Prop
  | nil (s : S) : StarAny R s [] s
  | cons {s t u : S} {l : L} {ls : List L} :
      R s l t → StarAny R t ls u → StarAny R s (l :: ls) u


/-- **Forward simulation.** Every single step of the source has a matching step of the
target, and the relation between states is preserved along it.

This is the minimal obligation for "the transformation preserves semantics": it says
nothing about *which* states are reachable, only that reachability is not lost. -/
def ForwardSim {S T L : Type*} (R : S → L → S → Prop) (R' : T → L → T → Prop)
    (φ : S → T) : Prop :=
  ∀ s l s', R s l s' → R' (φ s) l (φ s')

/-- Identity is a forward simulation. -/
theorem sim_id {S L : Type*} (R : S → L → S → Prop) : ForwardSim R R id :=
  fun _ _ _ h => h

/-- **Forward simulations compose.** This is what makes a multi-pass pipeline correct
by construction: check each pass, get the whole pipeline for free. -/
theorem sim_comp {S T U L : Type*}
    {R : S → L → S → Prop} {R' : T → L → T → Prop} {R'' : U → L → U → Prop}
    {φ : S → T} {ψ : T → U}
    (hφ : ForwardSim R R' φ) (hψ : ForwardSim R' R'' ψ) :
    ForwardSim R R'' (ψ ∘ φ) :=
  fun s l s' h => hψ (φ s) l (φ s') (hφ s l s' h)

/-- Forward simulation is monotone in the target relation: if `R'` is contained in
`R''`, a simulation into `R'` is a simulation into `R''`.

This is the lemma that lets a proof target a *weaker* specification than the one it
established, which is how "we proved a sharper bound than required" is used. -/
theorem sim_mono {S T L : Type*}
    {R : S → L → S → Prop} {R' R'' : T → L → T → Prop} {φ : S → T}
    (h : ForwardSim R R' φ) (hsub : ∀ a l b, R' a l b → R'' a l b) :
    ForwardSim R R'' φ :=
  fun s l s' hstep => hsub _ _ _ (h s l s' hstep)

/-- **Forward simulation is a preorder** on transition relations over a fixed state space.

The three combination laws proved above -- identity, composition, weakening -- are the reflexivity, transitivity
and monotonicity of a preorder. Stating them as one fact rather than three makes the structure visible: a caller
who needs to know that simulation is transitive gets it from the structure, not from remembering a lemma name.

This is the statement the file header promises when it says the shape is "stated once here and reused". It is
worth noting that until recently nothing imported this file, so the promise was aspirational -- the theorem below
does not change that by itself, but it makes the content sharp enough for a consumer to be worth writing. -/
theorem forwardSim_preorder {S L : Type*} :
    -- reflexivity
    (∀ R : S → L → S → Prop, ForwardSim R R id) ∧
    -- transitivity
    (∀ (R : S → L → S → Prop) (R' R'' : S → L → S → Prop),
        ForwardSim R R' id → ForwardSim R' R'' id → ForwardSim R R'' id) ∧
    -- weakening
    (∀ R R' : S → L → S → Prop, (∀ s l s', R s l s' → R' s l s') → ForwardSim R R' id) :=
  ⟨fun R => sim_id R,
   fun R R' R'' h1 h2 => sim_comp h1 h2,
   fun R R' h => h⟩


/-- **Whole runs are preserved.** A stepwise simulation lifts to arbitrary-length
reachability: if `s` can reach `t` by label `l`, then `φ s` reaches `φ t` by the
same label.

This is the statement one actually wants ("the compiled program can do whatever the
source could"), and it is *not* a restatement of `ForwardSim` -- it requires induction
over `ReflTransGen`. -/
theorem run_preserved {S T L : Type*}
    {R : S → L → S → Prop} {R' : T → L → T → Prop} {φ : S → T}
    (h : ForwardSim R R' φ) {s t : S} {l : L} (hs : Star R s l t) :
    Star R' (φ s) l (φ t) := by
  induction hs with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact Relation.ReflTransGen.tail ih (h _ l _ hlast)

/-- **Whole runs are preserved, with a varying label sequence.**

This is the general form needed for programs: a program is a *sequence* of primitive
steps, not repetitions of one label. -/
theorem runs_preserved {S T L : Type*}
    {R : S → L → S → Prop} {R' : T → L → T → Prop} {φ : S → T}
    (h : ForwardSim R R' φ) {s t : S} {ls : List L} (hs : StarAny R s ls t) :
    StarAny R' (φ s) ls (φ t) := by
  induction hs with
  | nil s => exact StarAny.nil (φ s)
  | cons hstep _ ih => exact StarAny.cons (h _ _ _ hstep) ih

end Lattice.Core
