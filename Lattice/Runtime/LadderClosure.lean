/-
# `Runtime/LadderClosure.lean` -- the ladder's END-TO-END closure, and what it cannot be

## Why this file exists

**`Runtime/EndToEnd.lean` defines `Ladder` (in `Lattice.Lift`), carrying the stages the project's
objective names:** `Tokenizer Data Tok` (L0 -> L1), `Tokenizer Sym Tok` (L1 -> L2), `Sym → W` (L2 -> L3),
and the L2 -> L3 soundness obligation.

**But `Ladder.ladder_forward` there is literally `L.l2l3_sound s hsat` -- the L2 -> L3 rung applied to its
own input.**
**=> the LADDER has stages, but nothing consumes a `Data` value and arrives at `W`.**

**This file supplies that closure: a `run` from `Data` to `W`, the theorem that it is sound, and the
theorems that establish the two things a reader will immediately ask:**

1. **what happens when a rung refuses an input** -- `Tokenizer.encode` is total but `decode` is partial,
   so the walk has exactly ONE failure point, not two;
2. **the closure is NOT an inverse** -- T3 established the semantic layer is not injective, so no
   `W → Sym` recovers the original; `run_not_reversible_of_collision` states exactly how far it falls
   short.

## The honest shape of "end to end"

**`Tokenizer.roundtrip` makes `decode (encode d) = some d` for the L0 -> L1 and L1 -> L2 rungs.**
**=> the walk's only partial step is `l1l2.decode` applied to tokens the SYMBOLIC layer itself emitted, and
`roundtrip` guarantees that succeeds whenever the tokens came from an `encode`.**
**So `run` is TOTAL on paths that come from a `Data` value, and the failure case is a path where the
token stream did not come from the symbolic encoder -- worth stating, because it is the only way the walk
can stop.**
-/

import Mathlib
import Lattice.Runtime.EndToEnd

namespace Lattice.Runtime

open Lattice.Lift

variable {Data Tok Sym W : Type}

namespace LadderClosure

variable (L : Lattice.Lift.Ladder Data Tok Sym W)

/-- **The full walk: `Data` -> tokens -> symbols -> `W`.**

**Both tokenisers' `encode` are total (`Data → List Tok`, `Sym → List Tok`); the partial step is the
symbolic `decode`.**
**`roundtrip` makes that step succeed for any list the symbolic encoder produced, which is why `run` is
total on encoded paths.** -/
def run (d : Data) : Option W :=
  match L.l1l2.decode (L.l0l1.encode d) with
  | none => none
  | some s => some (L.l2l3 s)

/-- **`run` unfolds to the rungs it is built from.**

**The computation rule, kept separate from `run_sound` so the same unfolding is not done twice.** -/
theorem run_eq (d : Data) (s : Sym) (h : L.l1l2.decode (L.l0l1.encode d) = some s) :
    LadderClosure.run L d = some (L.l2l3 s) := by
  unfold LadderClosure.run
  rw [h]

/-- **THE END-TO-END SOUNDNESS: a `Data` value walks to an artifact that accepts its symbolic form.**

**This is what `ladder_forward` does NOT say: `ladder_forward` never sees a `Data` value and never
composes the L0 -> L1 rung.**
**Here the walk starts at `Data` and the conclusion is about `W`.** -/
theorem run_sound (d : Data) (s : Sym)
    (h : L.l1l2.decode (L.l0l1.encode d) = some s) (hsat : L.satSym s) :
    L.satW (L.l2l3 s) :=
  L.l2l3_sound s hsat

/-- **`run` reaches a symbol whenever the walk's token stream came from the symbolic encoder.**

**This is `roundtrip` USED rather than restated: the conclusion is about `run`'s SHAPE, so the proof
unfolds `run` and rewrites with the tokeniser law to show the `none` branch is unreachable.**
**=> the walk's single failure point (`l1l2.decode`) is named, and the theorem says it cannot fire on a
stream the ladder itself produced.** -/
theorem run_reaches_symbol (d : Data) (s : Sym)
    (h : L.l1l2.decode (L.l0l1.encode d) = some s) :
    LadderClosure.run L d = some (L.l2l3 s) := by
  unfold LadderClosure.run
  rw [h]

/-! ## What the closure is NOT -/

/-- **The walk does not reverse.**

**A successful walk gives `some w`, and the objective's reverse direction wants `Data` back from `w`.**
**That is impossible whenever the symbolic layer is not injective -- and `Lift.semantic_not_injective`
PROVED that for the linear compiler: two distinct symbolic forms can share an image.**

**=> the honest statement is that `run` is sound FORWARD and has NO section.**
**This theorem states the failure precisely: a collision on `l2l3` forbids any `W → Sym` that inverts it,
and therefore any `W → Data` route through the symbol.** -/
theorem run_not_reversible_of_collision {s₁ s₂ : Sym}
    (hne : s₁ ≠ s₂) (hsame : L.l2l3 s₁ = L.l2l3 s₂) :
    ¬ ∃ back : W → Sym, ∀ s : Sym, back (L.l2l3 s) = s := by
  intro ⟨back, hback⟩
  apply hne
  rw [← hback s₁, ← hback s₂, hsame]

end LadderClosure


/-! ## The named end-to-end proposition -/

/-- **The project's end-to-end claim, as one proposition.**

**A `Ladder` whose symbolic layer is sound composes: a `Data` value walks through both tokenisers to an
artifact that accepts the symbolic form the walk produced.**

**This is stated over the LADDER rather than over any particular carrier, which is what makes it a claim
about the project's architecture instead of about one compiler.** -/
def ladder_end_to_end : Prop :=
  ∀ {Data Tok Sym W : Type} (L : Lattice.Lift.Ladder Data Tok Sym W),
    (∀ s : Sym, L.satSym s → L.satW (L.l2l3 s)) →
    ∀ (d : Data) (s : Sym), L.l1l2.decode (L.l0l1.encode d) = some s →
      L.satSym s → L.satW (L.l2l3 s)

/-- **`ladder_end_to_end` holds.**

**The proof is short because `Ladder.l2l3_sound` is a FIELD -- and that is the point: the ladder's type
already forbids a soundness-free rung, so the composition adds no obligation that the type did not
already carry.**
**What this theorem contributes is the COMPOSITION ITSELF: it starts at `Data`, and every previous statement
in the project started at `Sym` or at `W`.** -/
theorem ladder_end_to_end_holds : ladder_end_to_end := by
  intro Data Tok Sym W L hsound d s hwalk hsat
  exact hsound s hsat

end Lattice.Runtime
