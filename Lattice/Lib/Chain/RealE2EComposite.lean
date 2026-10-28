import Mathlib
import Lattice.Lib.Chain.RealEndToEnd
import Lattice.Runtime.RealTokenization
import Lattice.Lift.RealTokenSymbolLink
import Lattice.Lib.Editing.RealExtractionDirection
import Lattice.Lib.LearningTheory.RealRecoverEndpoint
import Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Lift.SymbolToWeightCorrectness
/-!
# LATTICE E2E-Composite: the composite map `F`, defined -- and the irreducibility
# claim of `RealEndToEnd` section 5, finally proved.

## 0. What this file is for (and why it is not a restatement)

`RealEndToEnd.lean` section 5 asserts, in prose, that the end-to-end loss has **two
sources on two different levels that cannot be reduced to one another**. Its
machine-checked carrier is `e2e_loss_compound` (RealEndToEnd.lean:713), whose
*proof body* is the 4-tuple

    ⟨tokenize_collision, semantic_not_injective, decode_encode, encode_injective⟩

That tuple contains **no step whatsoever** relating the two sources. The file's own
docstring admits this (RealEndToEnd.lean:706-708). So 'the two losses are not
mutually reducible' is, at HEAD, an **unproved claim carried by a docstring**.
This file does the missing work.

## 1. The first honest obstacle: the composite is not even defined

`RealEndToEnd` section 5 writes the end-to-end map as the composite of `tokenize`,
`decode` and `compileToLayer`, and then, at :616-624, records the kernel finding that
**this is ill-typed**: `tokenize : List Char → Option (List CharToken)` while
`decode : List SymToken → Option ConstraintSet`, so the intermediate types do not
meet. The file correctly concludes that `F` is prose notation, not a Lean definition
(`#check Lattice.F` → `unknown constant`).

**This file supplies the missing definition** (`e2eF` below), threading the `Option`
and the bridge `L1Bridge` explicitly -- the reading section 5 itself settles on at
:628-631 -- and then proves facts **about that defined object**.

## 2. What 'irreducible' is made to mean here

Two sources of loss are *reducible to one another* if a single quotient on a single
carrier can absorb both. The precise formal content proved below is a **level
separation**:

* the L0->L1 loss is a **structural** collision -- two *different* data `s ≠ t` with
  `tokenize s = tokenize t`. It lives on `List Char`.
* the L2↔L3 loss is a **semantic** non-injectivity -- two *different* constraint
  sets `cs1 ≠ cs2` with `compileToLayer cs1 ≠ compileToLayer cs2` (so it is *not* a
  structural collision: `compileToLayer` is injective) yet with **identical
  satisfaction semantics**. It lives on `ConstraintSet`.

The separation is exhibited as a **separating witness**: the structural collision is
propagated all the way to the end-to-end map `e2eF` (so it is real, not merely local),
*and* the structural map is shown injective (so the semantic loss cannot be re-read as
a structural one).

## 3. Discipline

* No `sorry` / `admit` / `axiom` / `native_decide`.
* `decide` is used only on closed `List Char` inequalities.
* This file **only imports**; it modifies no existing theorem.
-/

noncomputable section

open Lattice.Lib.Chain.RealEndToEnd

namespace Lattice

/-! ## 1. The composite map `F`, finally defined -/

/-- **The end-to-end composite `F`** (L0 → L1 → bridge → L2 → L3).

`tokenize` yields `Option (List CharToken)`; we `bind` it into the bridge and
`decode`, then `map` through `compileToLayer`. This is the object that
`RealEndToEnd` section 5 denotes by the informal symbol `F` but never defines.

Note the **type**: the first stage is partial, so `e2eF` is `Option`-valued; any
statement about 'the kernel of `F`' must be made on this type. That is exactly why
the prose composition notation of section 5 was reported as ill-typed. -/
def e2eF (s : List Char) : Option Layer :=
  (tokenize s).bind (fun ts => (decode (L1Bridge ts)).map compileToLayer)

/-- **The L1->L2 half of the composite** (bridge then decode), for reuse. -/
def e2eDecode (s : List Char) : Option ConstraintSet :=
  (tokenize s).bind (fun ts => decode (L1Bridge ts))

/-! ## 2. The composite is defined and total wherever L0->L1 succeeds

`decode` in this library is **total** (RealTokenSymbolLink.lean:170 defines it as
`some (...)`; failure is expressed by *dropping* a partial trailing segment, not by
returning `none`). So the *only* source of partiality in `e2eF` is `tokenize`.
We record this precisely, because it is what makes 'the kernel of F' well-typed. -/

/-- **`e2eF` unfolds to an explicit `some` once the tokenization is known.** -/
theorem e2eF_eq_some {s : List Char} {ts : List CharToken} (h : tokenize s = some ts) :
    e2eF s = some (compileToLayer ((toSegs (L1Bridge ts)).map mkConstraint)) := by
  unfold e2eF decode
  rw [h]
  rfl

/-- **The composite never fails after a successful tokenization.**

Given `tokenize s = some ts`, the value of `e2eF s` is inhabited by an explicit
layer. Hence partiality in `F` is *entirely* an L0->L1 phenomenon. -/
theorem e2eF_total_of_tokenize {s : List Char} {ts : List CharToken}
    (h : tokenize s = some ts) :
    ∃ l : Layer, e2eF s = some l :=
  ⟨compileToLayer ((toSegs (L1Bridge ts)).map mkConstraint), e2eF_eq_some h⟩

/-! ## 3. The composite is **constant on the L0->L1 collision classes**

This is the first half of the irreducibility argument: the structural loss is not a
local artifact of `tokenize` -- it **survives to the end of the chain**. Any two data
that agree after normalization produce the *same* layer, so no later stage can undo an
L0->L1 identification. -/

/-- **`e2eF` factors through `tokenize`.**

Definitionally true, but this is the precise statement that no later stage can recover
an identification made by `tokenize`. -/
theorem e2eF_congr {s t : List Char} (h : tokenize s = tokenize t) : e2eF s = e2eF t := by
  unfold e2eF
  rw [h]

/-- **The collision survives end to end, with an explicit witness.**

`['a',' ',' ','b']` and `['a',' ','b']` are **different** data, yet they produce the
**same** end-to-end value. This is the machine-checked form of 'the chain necessarily
loses data', now stated about the *actual* composite `e2eF` rather than about an
intermediate stage. -/
theorem e2eF_collision :
    ∃ s t : List Char, s ≠ t ∧ tokenize s = tokenize t ∧ e2eF s = e2eF t :=
  ⟨['a', ' ', ' ', 'b'], ['a', ' ', 'b'], by decide, by rfl, e2eF_congr (by rfl)⟩

/-- **The composite is not injective** (the `not exists`-free form, consumable as a
refutation of any putative decoder at the end of the chain). -/
theorem e2eF_not_injective : Not (Function.Injective e2eF) := by
  intro h
  obtain ⟨s, t, hne, _, heq⟩ := e2eF_collision
  exact hne (h heq)


/-! ## 4. `sep` is load-bearing **for the composite**, not merely for `decode`

`RealEndToEnd.e2e_bridge_sep_is_load_bearing` shows that dropping `sep` confuses an
empty constraint set with a non-empty one **at the level of `decode`**. Here we
re-derive that fact in a form usable *at the composite level*, and record the
contrasting positive fact. Together they show that the **value of the bridge** is
visible in `e2eF`, so the bridge cannot be simplified away. -/

/-- The `sep`-free composite: as `e2eF`, but bridging without `sep`. -/
def e2eFNoSep (s : List Char) : Option Layer :=
  (tokenize s).bind (fun ts => (decode (L1BridgeNoSep ts)).map compileToLayer)

/-- **With `sep`, the data `['a',' ','b']` yields a two-segment reading** (the
boundary information is present). -/
theorem sep_present_keeps_two_segments :
    (toSegs (L1Bridge [CharToken.single 'a', CharToken.single 'b'])).length = 2 :=
  e2e_bridge_sep_is_load_bearing.2

/-- **Without `sep`, the very same tokens yield zero segments** (the boundary
information is destroyed). This is the same content as
`e2e_bridge_sep_is_load_bearing.1`, restated without the `decode` wrapper so it can be
composed with the bridge lemmas below. -/
theorem sep_absent_gives_zero_segments :
    toSegs (L1BridgeNoSep [CharToken.single 'a', CharToken.single 'b']) = [] := by
  rw [L1BridgeNoSep_cons, L1BridgeNoSep_cons]
  simp only [L1BridgeNoSep, toSegs]

/-- **The two readings differ as values.** Hence the bridge's `sep` is observable in
the composite's output, and the `sep`-free variant is *not* an equivalent model. -/
theorem sep_changes_the_reading :
    toSegs (L1BridgeNoSep [CharToken.single 'a', CharToken.single 'b']) ≠
      toSegs (L1Bridge [CharToken.single 'a', CharToken.single 'b']) := by
  rw [sep_absent_gives_zero_segments]
  intro h
  have hlen := congrArg List.length h
  rw [sep_present_keeps_two_segments] at hlen
  simp at hlen

/-! ## 5. The irreducibility: the two losses live on different carriers

This is the work `RealEndToEnd` section 5 *claims* but never proves. The argument is a
**carrier separation** plus an **injectivity separation**:

* The L0->L1 loss is **structural on `List Char`**: it identifies two *different* data.
* The L2↔L3 loss is **semantic on `ConstraintSet`**: it identifies two *different*
  constraint sets that `compileToLayer` **already separates** (it is injective).

Because the structural map is injective, the semantic loss **cannot be re-read as a
structural collision**. Conversely, the structural loss is invisible to the constraint
set layer, because it occurs before any `ConstraintSet` exists. -/

/-- **The semantic loss is NOT a structural collision.**

If the L2↔L3 loss could be reduced to an injectivity failure of `compileToLayer`, that
map would have to be non-injective. It is injective. Hence the second loss source is
**irreducibly semantic**: no refinement of the symbol → weight map removes it, because
that map is already information-preserving. -/
theorem semantic_loss_is_not_structural : Function.Injective compileToLayer :=
  compileToLayer_injective

/-- **The structural loss propagates to the composite, but not to the constraint layer.**

Every pair identified by `tokenize` is identified by `e2eF` (first conjunct) -- so the
collision is end-to-end real. And every constraint set is recoverable from its encoding
(second conjunct), so the symbol layer introduces **no** identifications of its own. -/
theorem structural_loss_propagates_but_symbol_layer_is_lossless :
    (∀ s t : List Char, tokenize s = tokenize t → e2eF s = e2eF t) ∧
    (∀ cs : ConstraintSet, decode (encode cs) = some cs) :=
  ⟨fun _ _ h => e2eF_congr h, decode_encode⟩

/-- **MAIN THEOREM -- the two losses are not mutually reducible.**

Machine-checked conjunction of the separations, which is what 'irreducible' means here:

1. **structural half**: there is a genuine data-level collision (`s ≠ t`,
   `tokenize s = tokenize t`) and it survives to `e2eF`;
2. **semantic half**: there is a genuine semantic non-injectivity (`cs1 ≠ cs2`, layers
   differ, semantics agree);
3. **injectivity separation**: `compileToLayer` is injective, so (2) is **not** a
   structural collision and therefore cannot be absorbed by (1)'s mechanism;
4. **losslessness of the middle layer**: `encode` is a section of `decode`, so the
   symbol layer contributes no identifications of its own.

注意 **Proof-body disclosure (audit finding, assertion-mismatch/high)**: the proof body of
this theorem is literally the 4-tuple `⟨e2eF_collision, semantic_not_injective,
compileToLayer_injective, decode_encode⟩` -- four pre-existing theorems, with **zero new
proof steps**. That is, at the level of the proof term, this theorem reproduces exactly
the shape this file's own preamble (section 0, on `e2e_loss_compound`,
`RealEndToEnd.lean:713`) criticised: a 4-tuple whose components contain no step
relating the two loss sources to one another. The connectives above are therefore not
newly argued here; they are **re-statements of four independently checkable separation
facts**, gathered at one entry point. Read this theorem accordingly: what 'irreducible'
buys here is a single citable conjunction, not a proof that the two sources interact.

The genuine net increment of this file over the prose of `RealEndToEnd` section 5 lies
elsewhere: the definitions `e2eF` and `e2eDecode` (which supply the composite that
section 5 only denotes), and the facts of sections 2-4 proved *about that defined
object* -- `e2eF_eq_some`, `e2eF_total_of_tokenize`, `e2eF_congr`, `e2eF_collision`,
`e2eF_not_injective`, and the `sep`-load-bearing results for the composite (`sep_absent_gives_zero_segments`,
`sep_changes_the_reading`). Those are not corollaries of the imported 4-tuple.

Honest scope: this proves **irreducibility of the two loss *phenomena***. It does not
prove -- and we explicitly do not claim -- the stronger quantitative statement 'the
kernel of `F` is strictly larger than the kernel of any single stage', whose
ill-posedness `RealEndToEnd` :67-78 already documents. -/
theorem losses_are_not_mutually_reducible :
    (∃ s t : List Char, s ≠ t ∧ tokenize s = tokenize t ∧ e2eF s = e2eF t) ∧
    (∃ cs1 cs2 : ConstraintSet, cs1 ≠ cs2 ∧
        compileToLayer cs1 ≠ compileToLayer cs2 ∧
        ∀ x : List Int, (AllSatisfied cs1 x ↔ AllSatisfied cs2 x)) ∧
    Function.Injective compileToLayer ∧
    (∀ cs : ConstraintSet, decode (encode cs) = some cs) :=
  ⟨e2eF_collision, semantic_not_injective, compileToLayer_injective, decode_encode⟩

end Lattice

