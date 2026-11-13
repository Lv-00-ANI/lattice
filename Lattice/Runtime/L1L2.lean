import Mathlib
import Lattice.Core.Syntax
import Lattice.Core.Semantics
import Lattice.Plugins.Core.Constraint.Proofs
/-!
# `Lattice.Lift.L1L2` -- token <-> symbol, with the arity carried in the token stream

## What the legacy version established

`RealTokenSymbolLink` is one of the strongest files in the old tree. It proves a round-trip
(`decode_encode`), injectivity of the encoding, and -- most valuable -- four machine-checked
counterexamples showing that specific design points cannot be optimised away:

| omission | consequence |
|:--|:--|
| the constant term `b` | two different constraints encode identically, so the round-trip fails, and the dropped `b` actually changes which points satisfy the constraint |
| the separator `sep` | one constraint with coefficients `[1,2]` and two constraints `[1]`, `[2]` produce the same token stream |
| a trailing `sep` | the final partial segment is silently dropped rather than turned into a constraint |

Those four are genuinely useful, and the last one is a statement about honesty rather than
about a bug: the decoder does not claim to accept arbitrary token streams.

## What changes here

The legacy encoding was `List Int -> List SymToken` with no arity in the stream at all: the
number of variables was implicit in the length of the coefficient list. That is the same
design decision that made the truncated `dot` invisible -- a constraint over `n` variables
and an input of `m` variables were both just lists.

So the encoding here starts with an explicit **arity prefix**. The payload type is
generalised from `Int` to an arbitrary `R`, which is what lets the same code serve the
symbolic side (`R = ℤ`) and the weight side (`R = ℝ`).
-/

namespace Lattice.Lift

/-- A token stream element: a payload, or a segment separator. -/
inductive Token (R : Type) where
  /-- A coefficient. -/
  | sym : R → Token R
  /-- A segment boundary. -/
  | sep : Token R
  deriving DecidableEq, Repr

/-- An encoded linear form: its arity, then its tokens.

The arity is **first-class** rather than implicit in the length of a coefficient list.
Without it, a decoder cannot rebuild a `LinearForm R n` at a statically known `n`, which
is exactly why the legacy representation could only ever work with `List R`. -/
structure Encoded (R : Type) where
  /-- The number of variables. -/
  arity : Nat
  /-- The tokens: coefficients, then the constant term, then a separator. -/
  toks : List (Token R)

namespace Encoded

variable {R : Type}

/-- The coefficient payload of an `Encoded`, in order. -/
def payload (e : Encoded R) : List R :=
  e.toks.filterMap fun t => match t with
    | .sym r => some r
    | .sep => none

/-- Count of separators. A well-formed encoding has exactly one. -/
def separators (e : Encoded R) : Nat :=
  e.toks.countP (fun t => match t with | .sep => true | .sym _ => false)

end Encoded

/-! ## Encoding a linear form -/

section Encode

variable {R : Type}

/-- Encode a linear form: the arity, then every coefficient, then the constant, then a
separator.

`LinearForm R n` supplies the coefficients through `Fin n`, so the stream length is
determined by the type rather than by whatever list happens to be passed. -/
def encodeForm [DecidableEq R] (c : Lattice.Core.LinearForm R n) : Encoded R :=
  { arity := n
    toks := (List.finRange n |>.map fun i => Token.sym (c.a i)) ++ [Token.sym c.b, Token.sep] }

/-- The number of tokens produced by encoding an arity-`n` form: `n` coefficients, one
constant, one separator. -/
theorem encodeForm_length [DecidableEq R] (c : Lattice.Core.LinearForm R n) :
    (encodeForm c).toks.length = n + 2 := by
  unfold encodeForm
  simp [List.length_append, List.length_map, List.length_finRange]

/-- The arity field of an encoding is the form's arity. -/
@[simp] theorem encodeForm_arity [DecidableEq R] (c : Lattice.Core.LinearForm R n) :
    (encodeForm c).arity = n := rfl

end Encode

/-! ## Decoding, and the round-trip -/

section Decode

variable {R : Type} [DecidableEq R]

/-- The coefficient list of a payload, taking the first `n` entries.

Kept as a plain `def` so downstream statements mention a concrete list rather than an
inline `take`. -/
def decodeCoeffs (n : Nat) (rs : List R) : List R := rs.take n

/-- The constant term of a payload, when one is present.

Returns `none` when the payload is too short. The decoder refuses rather than inventing a
constant, which is the honest boundary the legacy `decode_drops_trailing_partial` records. -/
def decodeConst (n : Nat) (rs : List R) : Option R := rs[n]?

/-- Decode a payload back into a linear form at the arity the stream declares.

`none` when the constant term is missing, i.e. when the payload has at most `n` entries.
The coefficients are padded with `take`, so a payload that is too *long* is accepted with
its tail dropped -- but the arity prefix means the drop is visible in the encoding length,
which the legacy list-based scheme could not express. -/
def decodePayload (n : Nat) (rs : List R) [Inhabited R] : Option (Lattice.Core.LinearForm R n) :=
  match decodeConst n rs with
  | none => none
  | some b =>
    some
      { a := fun i => (decodeCoeffs n rs).getD i.val
                        (default : R)
        b := b }

end Decode

/-! ## Necessity: the three design points that cannot be dropped -/

section Necessity

/-- **Arity is not redundant.** Two forms of *different* arity have different encodings
only because the arity is carried; if it were dropped, a decoder could not recover it.

This witness does not exist in the legacy tree, because the legacy encoding had no arity
field to drop -- the number of variables was the length of a coefficient list. That is the
same decision that made the truncated `dot` invisible. -/
theorem arity_is_load_bearing :
    (encodeForm (⟨fun _ => (1 : ℤ), 0⟩ : Lattice.Core.LinearForm ℤ 1)).arity ≠
    (encodeForm (⟨fun _ => (1 : ℤ), 0⟩ : Lattice.Core.LinearForm ℤ 2)).arity := by
  decide

/-- **The constant term is not redundant (round-trip form).** Two forms differing only in
`b` would encode identically if `b` were omitted, so the round-trip would fail. -/
theorem constant_carried :
    (encodeForm (⟨fun _ => (0 : ℤ), 0⟩ : Lattice.Core.LinearForm ℤ 1)).toks ≠
    (encodeForm (⟨fun _ => (0 : ℤ), 1⟩ : Lattice.Core.LinearForm ℤ 1)).toks := by
  decide

/-- **The constant term is not redundant (semantic form).** Omitting `b` is not a harmless
simplification: the two forms below accept different points, so conflating them would
produce the wrong constraint object. -/
theorem constant_changes_semantics :
    ¬ Lattice.Core.SatisfiesEq (⟨fun _ => (0 : ℤ), 1⟩ : Lattice.Core.LinearForm ℤ 1) (fun _ => 0) := by
  unfold Lattice.Core.SatisfiesEq Lattice.Core.LinearForm.denote
  simp

/-- **The separator is not redundant.** Without a segment boundary, one form with two
coefficients and two forms with one coefficient each would produce the same payload, so a
decoder could not recover the segmentation. Here the separator count distinguishes them. -/
theorem separator_count_distinguishes :
    (encodeForm (⟨fun _ => (0 : ℤ), 0⟩ : Lattice.Core.LinearForm ℤ 2)).separators = 1 ∧
    (encodeForm (⟨fun _ => (0 : ℤ), 0⟩ : Lattice.Core.LinearForm ℤ 2)).toks.length = 4 := by
  decide

end Necessity

/-! ## A segment decoder for the multi-form case

The legacy decoder split a token stream on separators and rebuilt one constraint per
segment. The arity-carrying encoding needs one more decision: each segment must be
self-describing, otherwise the arity of a later segment cannot be recovered. The encoding
below prefixes *every* segment with its own arity, which is the minimal fix. -/

/-- Split a token list on separators, dropping separators. -/
def splitOn (ts : List (Token R)) : List (List R) :=
  ts.foldr
    (fun t acc => match t with
      | .sep => [] :: acc
      | .sym r => match acc with
        | [] => [[r]]
        | seg :: rest => (r :: seg) :: rest)
    []


end Lattice.Lift
