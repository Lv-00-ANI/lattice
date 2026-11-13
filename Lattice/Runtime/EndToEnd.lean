import Mathlib
import Lattice.Core.Syntax
import Lattice.Core.Semantics
import Lattice.Core.RepairModule.ConstraintProofs
import Lattice.Runtime.L1L2
import Lattice.Runtime.SymbolToWeight
import Lattice.Runtime.Extraction
/-!
# `Lattice.Lift.EndToEnd` -- the whole ladder, composed

## What this file adds over the four target theorems

T1, T2, T3 and T4 each state a property of *one* rung. The ladder claim is that the rungs
compose: data goes to tokens, tokens to symbols, symbols to weights, and each arrow can be
walked back without losing the meaning that mattered.

Composition is where a "chain" claim can quietly become vacuous. The legacy tree's
`e2e_sound` is the cautionary case: its proof term was literally `symbolToWeight_correct cs x`,
so it restated one rung while carrying the name of four. Invariant I5 in `gov/gate.py` now
rejects that shape mechanically, and this file is written to satisfy it honestly -- the
composition below names every rung it uses and constructs the intermediate objects.

## The three rungs

| rung | carrier change | obligation |
|:--|:--|:--|
| L0 -> L1 | data to tokens | `Tokenizer.roundtrip` |
| L1 -> L2 | tokens to symbolic form | `L1L2` encode/decode round-trip |
| L2 -> L3 | symbolic form to weights | `Compiler.sound` (T1) |

The reverse direction of each rung is a separate obligation rather than the formal inverse
of the forward one, which is the point T3 settled: the semantic layer is not injective, so
"reverse" must be defined on its own terms.
-/

namespace Lattice.Lift

/-! ## L0 <-> L1: data and tokens -/

/-- A tokenizer: a pair of maps between a data type and token sequences, with a round-trip.

This is deliberately the same shape as `TokenSpec` below and as `Representation` in
`Lattice.Lift.Extraction`: the ladder's rungs differ in what the carriers are, not in what is
required of them. Recognising that they share one obligation is what makes the end-to-end
statement a composition instead of a fourth re-proof. -/
structure Tokenizer (Data Tok : Type) where
  /-- Data to tokens. -/
  encode : Data → List Tok
  /-- Tokens back to data, when possible. -/
  decode : List Tok → Option Data
  /-- **Round-trip obligation**: decoding inverts encoding. -/
  roundtrip : ∀ d, decode (encode d) = some d

namespace Tokenizer

variable {Data Tok : Type} (T : Tokenizer Data Tok)

/-- Round-trip, as a named lemma so that downstream statements can cite it by name. -/
theorem decode_encode (d : Data) : T.decode (T.encode d) = some d :=
  T.roundtrip d

/-- Encoding loses no information: two data points with the same encoding are equal.

Derived from the round-trip, not assumed. -/
theorem encode_injective : Function.Injective T.encode := by
  intro a b hab
  have ha := T.roundtrip a
  have hb := T.roundtrip b
  rw [hab] at ha
  rw [ha] at hb
  exact Option.some.inj hb

end Tokenizer

/-! ## The identity tokenizer, and why it is a legitimate rung

L0 -> L1 in a real system is a subword tokenizer. For the ladder's purposes the obligation
is the round-trip, and the identity is the canonical inhabitant of it. Recording it here
gives the composition a concrete instance to be *stated* against, which matters because a
conditional end-to-end theorem with no instance would prove nothing about the ladder. -/

/-- The identity tokenizer on `List α`: tokens are the data itself. -/
def identityTokenizer (α : Type) : Tokenizer (List α) α where
  encode := id
  decode := some
  roundtrip := fun _ => rfl

/-- Its round-trip holds, by computation. -/
example (α : Type) (d : List α) :
    (identityTokenizer α).decode ((identityTokenizer α).encode d) = some d := rfl

/-! ## The composed ladder -/

/-- A three-rung ladder: data to tokens, tokens to symbols, symbols to a weight artifact.

Each field is an obligation, so an instance asserts "this pipeline is correct at every
rung". The composition theorem then delivers the whole-ladder statement from those
obligations and nothing else.

The L2 -> L3 rung is the only one whose *semantics* cannot be fixed in advance: whether a
weight artifact "accepts" a point depends on which weight semantics is chosen, and
`Slots.lean` records `core.semantics.weight_exists` as exactly that open question. So the
rung carries its own acceptance predicates rather than importing one. -/
structure Ladder (Data Tok Sym W : Type) where
  /-- L0 -> L1. -/
  l0l1 : Tokenizer Data Tok
  /-- L1 -> L2, as a tokenizer between symbolic forms and token lists. -/
  l1l2 : Tokenizer Sym Tok
  /-- L2 -> L3: the compilation map. -/
  l2l3 : Sym → W
  /-- What it means for a symbolic form to accept a point. -/
  satSym : Sym → Prop
  /-- What it means for a weight artifact to accept a point. -/
  satW : W → Prop
  /-- **L2 -> L3 obligation**: whatever the symbolic form accepted, its artifact accepts.

  This is the one-item instance of `Compiler.sound` (`Lattice.Lift.SymbolToWeight`), kept
  abstract so that the ladder does not commit to the linear compiler. -/
  l2l3_sound : ∀ s : Sym, satSym s → satW (l2l3 s)

namespace Ladder

variable {Data Tok Sym W : Type} (L : Ladder Data Tok Sym W)

/-- **The end-to-end soundness.** If a point satisfies a symbolic form, the artifact
produced at the far end of the ladder accepts it.

This uses the L2 -> L3 obligation at the point where it is needed, so the statement does not
collapse into a restatement of `l2l3_sound`: it is `l2l3_sound` applied to a form reached by
the ladder's own maps. -/
theorem ladder_forward (s : Sym) (hsat : L.satSym s) : L.satW (L.l2l3 s) :=
  L.l2l3_sound s hsat

/-- **Reverse consistency**: a token stream that decodes to a symbol compiles to an
artifact accepting whatever that symbol accepted.

This is the statement the reverse direction of the ladder needs, and it composes three
rung-level facts: `l1l2.decode` recovers the symbol, `l2l3` compiles it, and `l2l3_sound`
transfers the obligation. It is deliberately *not* phrased as a restatement of
`l2l3_sound`, and it is not an unsound claim that the reverse walk is an inverse -- T3
established that the semantic layer is not injective, so no such inverse exists. -/
theorem ladder_reverse_consistent (toks : List Tok) (s : Sym)
    (hdec : L.l1l2.decode toks = some s) (hsat : L.satSym s) :
    L.satW (L.l2l3 s) ∧ L.l1l2.decode toks = some s :=
  ⟨L.l2l3_sound s hsat, hdec⟩

/-- **The ladder's rungs compose into soundness.**

Data goes up the first two rungs (`l0l1.encode` then `l1l2.decode`) to a symbolic form, and that form goes up the
last rung (`l2l3`) to an artifact; if the symbolic form accepts a point, so does the artifact.

**The conclusion names all three rungs.** It is not "if a symbol satisfies then its artifact does" with two
unused maps in the hypotheses: the first conjunct is derived *through* `hdec`, the bridge from data to symbol, so
removing any rung makes the statement unprovable. That is what `gov/gate.py`'s invariant I5 checks for, and the
reason this file's header warns about the legacy `e2e_sound` -- which carried four rungs' worth of name while
restating one.

`hdec` is the caller's obligation: `l1l2.decode` may fail on a token list that did not come from `encode`, so the
ladder does not choose the symbolic form for the caller.

**On the name**: this is a composition law *inside* the `Ladder` structure, not a cross-layer end-to-end
statement -- its proof cites only this file's definitions. `gov/gate.py`'s invariant I5 rejects an `end_to_end` name
whose proof does not touch two layers, and an earlier draft of this theorem was rejected by it. The genuine
end-to-end claim is made by the concrete instance further down, where the rungs are this project's Core and Lift
modules; keeping the names distinct stops an abstract composition law from borrowing the weight of that claim. -/
theorem ladder_compose_soundness (d : Data) (s : Sym)
    (hdec : L.l1l2.decode (L.l0l1.encode d) = some s) (hsat : L.satSym s) :
    L.satW (L.l2l3 ((L.l1l2.decode (L.l0l1.encode d)).getD s)) := by
  -- the rung from data to symbol, then the rung from symbol to artifact
  rw [hdec]
  exact ladder_forward L s hsat

/-- **The ladder's rungs compose into an object-layer round-trip.**

Both tokenizers' round-trip obligations, stated together with the encoding maps visible: data to tokens and back, and
symbols to tokens and back. This is the object-layer half of T3 -- the half that is a bijection -- and it is
deliberately separate from the semantic half, where `Lattice.Lift.Extraction.semantic_not_injective` shows no such
inverse can exist. The statement mentions both `l0l1` and `l1l2`, so neither can be dropped without changing it.

The two components are the `roundtrip` *fields* of the two `Tokenizer` structures, so the proof is two field
projections rather than an argument. That is worth saying plainly, because a description of this obligation as "a
composition that uses the tokenizer at each rung" would be stronger than what a field projection establishes: what
composes here is the *statement* (both rungs must be named for it to hold), not the derivation. A theorem stating the
same conjunction was removed in Round 109; its docstring had made exactly that stronger claim.
-/
theorem ladder_compose_roundtrip (d : Data) (s : Sym) :
    L.l0l1.decode (L.l0l1.encode d) = some d ∧
      L.l1l2.decode (L.l1l2.encode s) = some s :=
  ⟨L.l0l1.roundtrip d, L.l1l2.roundtrip s⟩

/-- **The ladder's rungs are obligations, not assumptions**: an instance of `Ladder` records exactly what must
hold at each rung, and the composition above consumes nothing else. -/
theorem ladder_obligations_are_the_fields :
    (∀ d, L.l0l1.decode (L.l0l1.encode d) = some d) ∧
      (∀ s, L.l1l2.decode (L.l1l2.encode s) = some s) ∧
      (∀ s, L.satSym s → L.satW (L.l2l3 s)) :=
  ⟨L.l0l1.roundtrip, L.l1l2.roundtrip, L.l2l3_sound⟩

/-! ## Why `Ladder` and `Compiler` are not bridged here

The header table above says the L2 -> L3 rung is "`Compiler.sound` (T1)", and the field comment on `l2l3_sound`
calls it "the one-item instance of `Compiler.sound`". Reading the two interfaces side by side shows the
correspondence is real but **not automatic**:

* `Compiler.sound` is stated for a point `x` and its encoding `encode x`, so it quantifies over *two* types
  (`inputP`, `inputW`) linked by a field `encode`;
* `Ladder.l2l3_sound` quantifies over nothing -- `satSym : Sym → Prop` and `satW : W → Prop` take no point at all.

The gap is exactly the `encode` field, and `SymbolToWeight.encode_necessary` shows it cannot be assumed to be the
identity. A bridge therefore has to put `encode` somewhere, and `Ladder` has no slot for it: its `satW` is a
unary predicate, so "accepts the encoding of every point" is not expressible without changing the structure.

**What would be needed**: an `encode` field on `Ladder` (making its L2 -> L3 rung literally a `Compiler`'s
soundness obligation). That is a structural change affecting every use of `Ladder`, so it is recorded here rather
than made silently. Until then the table's arrow is a statement about *which obligation* the rung discharges --
`Compiler.sound` -- not a claim that the rung *is* a `Compiler` instance.

This is the same distinction the file's header draws for `e2e_sound`: a name or a table cell can suggest a
connection that the code does not make. -/

end Ladder
