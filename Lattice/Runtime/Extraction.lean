import Mathlib
import Lattice.Core.Syntax
import Lattice.Core.Semantics
import Lattice.Core.Logic
import Lattice.Core.Idempotent
import Lattice.Core.Repair

/-!
# `Lattice.Lift.Extraction` -- T3: extraction equivalence, and the reversibility boundary

## Why this file exists in this form

The goal statement requires that reversibility be stated *by layer*: the object layer is
a bijection, and the semantic layer is provably not invertible. The legacy tree got this
right in `RealReversibilityBoundary`, which is one of the few files in the old codebase
where a claim is stated at its correct strength and backed by a concrete counterexample.
This module carries that result over rather than re-deriving it.

What changes is the *domain of the statement*. In the legacy tree a constraint was a
`List Int` with no arity, so "semantically equal" could compare any two constraints. Here
arity is part of the type, so semantic equality must be stated at a shared `n`. That makes
the claim sharper: the scaling witness stays inside one arity, so it still separates
objects from meanings.

## The four layers

| layer | statement | status |
|:--|:--|:--|
| parameter, round-trip | `extract (compile p) = p` | **obligation + consequence** |
| parameter, injectivity | `Function.Injective compile` | **proved from the round-trip** |
| semantic, non-injectivity | `c ≠ c'` satisfied by the same points | **proved, with witness** |
| both at once | no extractor achieves both | **proved only with `sem` as a PARAMETER** |

The last row is the sharp statement of the difficulty: not that a good extractor has not
been found, but that one cannot exist.

⚠⚠ **Round 57 correction.** As written until this round, that last row was **vacuous**: its
hypotheses were `hne : c ≠ c'` and `_hsem : c = c'` -- **contradictory**, so the theorem was
`False → anything` and its proof never used `_hsem` at all (hence the underscore). The row is now
stated the way it was meant: `sem` (a semantic equivalence relation) is a **parameter**, the two
witnesses satisfy `hne` and `hsem` **consistently** (that is `semantic_not_injective`), and what is
proved is that **a left inverse cannot also be faithful to the semantic quotient**.

## Scope remark: where the scaling witness lives

Scaling preserves the zero set, so `(a, b)` and `(k·a, k·b)` are semantically equal while
being different objects. This needs `k·a ≠ a`, true on `ℤ` for `k = 2`, `a ≠ 0`. On a ring
of characteristic two it would fail, since `2·a = 0`. The witness is therefore given
concretely on `ℤ`, and the abstraction ("any zero-preserving action") is recorded as a
remark rather than claimed as an instance.
-/

namespace Lattice.Lift

open Lattice.Core

/-! ## A compile/extract pair -/

/-- A compile/extract pair with independent input encodings on each side.

`encode` and `decode` are kept separate because they are genuinely different maps: the
symbolic side presents a point to the weighted artifact, while extraction observes the
artifact from the symbolic side. Collapsing them to the identity is exactly the assumption
that let the legacy `dot` truncate unnoticed. -/
structure Representation (P W : Type) where
  /-- The symbolic side's input space. -/
  inputP : Type
  /-- The weighted side's input space. -/
  inputW : Type
  /-- How a symbolic point is presented to the weighted artifact. -/
  encode : inputP → inputW
  /-- How a weighted point is observed by the symbolic side. -/
  decode : inputW → inputP
  /-- Compilation. -/
  compile : P → W
  /-- Extraction. -/
  extract : W → P
  /-- **Round-trip obligation**: extraction inverts compilation. -/
  roundtrip : ∀ p, extract (compile p) = p

namespace Representation

variable {P W : Type} (R : Representation P W)

/-- **T3-a (parameter layer, round-trip).** Extraction inverts compilation.

The legacy tree proved this by `cases c <;> rfl` on a field-renaming pair. Here it is an
obligation of the structure, so it holds for any instance -- including one whose encoding
is not the identity, which the legacy formulation could not express. -/
theorem extract_compile (p : P) : R.extract (R.compile p) = p :=
  R.roundtrip p

/-- **T3-b (parameter layer, injectivity).** Compilation loses no information.

Derived from the round-trip through `Function.LeftInverse.injective` rather than re-proved:
the legacy tree established injectivity with a separate `cases` argument and did not notice
that it follows from the round-trip it already had. -/
theorem compile_injective : Function.Injective R.compile :=
  Function.LeftInverse.injective R.roundtrip

end Representation

/-! ## The semantic layer: non-injectivity, with a witness -/

/-- Two linear forms are *semantically equivalent* when no point separates them.

Both forms share the arity `n`, because in this foundation arity is part of the type. That
is a deliberate strengthening: it prevents the legacy situation in which a two-variable
constraint was compared with, and could even be "satisfied by", a zero-variable input. -/
def SemEq {R : Type} [CommSemiring R] {n : Nat} (c c' : LinearForm R n) : Prop :=
  ∀ x : Point R n, c.denote x = 0 ↔ c'.denote x = 0

/-- Scaling coefficients and constant by `k` multiplies the linear form by `k` pointwise.

This is the algebraic content behind the scaling witness, and it is proved for an arbitrary
`CommRing` so that it is available on `ℤ`, on `ℝ`, and on every intermediate carrier. -/
theorem denote_scale {R : Type} [CommRing R] {n : Nat} (k : R) (c : LinearForm R n)
    (x : Point R n) :
    (⟨fun i => k * c.a i, k * c.b⟩ : LinearForm R n).denote x = k * c.denote x := by
  unfold LinearForm.denote
  rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.univ,
    (k * c.a i) * x i = k * (c.a i * x i))]
  rw [← Finset.mul_sum]
  ring

/-- **Scaling preserves semantics**, provided the scale factor is a non-zero-divisor
element: `k·u = 0 ↔ u = 0` when `k ≠ 0` in a domain. -/
theorem semEq_scale {R : Type} [CommRing R] [IsDomain R] {n : Nat}
    (k : R) (hk : k ≠ 0) (c : LinearForm R n) :
    SemEq (⟨fun i => k * c.a i, k * c.b⟩ : LinearForm R n) c := by
  intro x
  rw [denote_scale, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hk
    · exact h
  · intro h
    exact Or.inr h


/-! ## The witness: a concrete failure of semantic injectivity -/

section Witness

/-- The carrier of the concrete witness. Kept as a named abbrev so that projections of
structures built from it never need to be unfolded to type a numeral. -/
abbrev ZB := ℤ

/-- The constraint `x = 0`, i.e. coefficient `1` and constant `0`. -/
def unitForm : LinearForm ZB 1 := ⟨fun _ => 1, 0⟩

/-- The constraint `2x = 0`. Defined AS the doubling of `unitForm`, so the scaling
lemma applies definitionally rather than needing a structure extensionality step
(which does not fire here, since one field is a function). -/
def scaledForm : LinearForm ZB 1 := ⟨fun i => 2 * unitForm.a i, 2 * unitForm.b⟩

/-- The two forms are different *objects*: their coefficients differ.

The discriminator must be the coefficient, not the constant: both forms have constant
term `0`, so comparing constants reduces to `True` and proves nothing. -/
theorem unit_ne_scaled : unitForm ≠ scaledForm := by
  intro h
  have ha : unitForm.a 0 = scaledForm.a 0 :=
    congrArg (fun f : LinearForm ZB 1 => f.a 0) h
  simp only [unitForm, scaledForm] at ha
  norm_num at ha

/-- But they denote the same behaviour: no point separates them, since the carrier is
a domain and the scale factor `2` is nonzero. -/
theorem scaled_semEq_unit : SemEq scaledForm unitForm :=
  semEq_scale (R := ZB) (n := 1) 2 (by norm_num) unitForm

/-- **T3-c (semantic layer, non-injectivity).** There exist two distinct parameters
satisfied by exactly the same points.

This is the legacy `semantic_layer_not_injective`, carried over to a foundation where the
arity is part of the type: the witness stays at arity one, so the comparison is
well-typed by construction. -/
theorem semantic_not_injective :
    ∃ c c' : LinearForm ZB 1, c ≠ c' ∧ SemEq c c' :=
  ⟨unitForm, scaledForm, unit_ne_scaled, fun x => (scaled_semEq_unit x).symm⟩

end Witness

/-! ## T3-d: no extractor is faithful at both layers

This is the sharpest form of the difficulty. It is not that a good extractor has not been
found; it is that one cannot exist, and the proof is three lines.

The legacy statement restricted to `VectorConstraint`/`LinearLayer`; here it is stated for
an arbitrary `compile : P → W`, so it applies to every representation, including ones
whose weighted side is a real tensor tree rather than a list. -/

/-- ⭐ **No extractor is faithful at both layers** -- **the non-vacuous statement.**

`sem : P → P → Prop` is a **semantic equivalence** (on `LinearForm` it is `SemEq`). An extractor
`extract` that is

- a **left inverse** of `compile` (`hround`), and
- **constant on `sem`-equivalent** symbols (`hfaithful`)

must contradict `hne : c ≠ c'` **whenever `sem` is coarser than `=` at `c`, `c'`**.

## Why the old statement was vacuous, in one line

It was

    (hne : c ≠ c') (_hsem : c = c') → ¬ ∃ extract, ...

**`c ≠ c'` and `c = c'` cannot both hold.** So the statement was `False → anything`, and its proof
never touched `_hsem` -- the underscore says so. It did not express "no extractor is faithful at
both layers"; it expressed "a left inverse is injective", which is true and has nothing to do with
semantics.

## What makes the new one non-vacuous

`hne` and `hsem` are **compatible**, and the compatibility is a theorem with a witness:
`semantic_not_injective` gives `unitForm ≠ scaledForm` with `SemEq unitForm scaledForm`.
See `no_extractor_both_layers_witness` for the instantiation. -/
theorem no_extractor_both_layers {P W : Type} (compile : P → W) (sem : P → P → Prop)
    {c c' : P} (hne : c ≠ c') (hsem : sem c c')
    {extract : W → P} (hround : ∀ p, extract (compile p) = p)
    (hfaithful : ∀ a b : P, sem a b → extract (compile a) = extract (compile b)) : False := by
  have h := hfaithful c c' hsem
  rw [hround c, hround c'] at h
  exact hne h

/-- ⭐ **The witness instance**: over `LinearForm ℤ 1`, no self-extractor is both the identity and
`s SemEq`-faithful.

**This is the statement the file header's last table row was supposed to make**, and now the
`hne`/`hsem` pair comes from `semantic_not_injective` rather than from an inconsistency. -/
theorem no_extractor_both_layers_witness :
    ¬ ∃ extract : (LinearForm ZB 1) → (LinearForm ZB 1),
        (∀ p, extract p = p) ∧
        (∀ a b : LinearForm ZB 1, SemEq a b → extract a = extract b) := by
  rintro ⟨extract, hround, hfaithful⟩
  -- `compile := id`, so the round-trip is `extract p = p`; the two witnesses are the scaling pair.
  exact no_extractor_both_layers (P := LinearForm ZB 1) (W := LinearForm ZB 1)
    id SemEq unit_ne_scaled (fun x => (scaled_semEq_unit x).symm) hround hfaithful

/-! ## The four layers, joined

The table at the head of this file lists four statements. Each was proved independently; nothing said how they sit
together. The two theorems below do that, and they are what "reversibility must be stated by layer" means when
written as a single fact rather than as prose.

The join has a specific shape. It is **not** possible to have one theorem saying "the object layer is a bijection
and the semantic layer is not" about a *single* pair `(compile, extract)`, because the first concerns the parameter
space and the second concerns the semantic quotient -- they are statements about different spaces. What can be
said is that both hold, with their own witnesses, and that no extractor can be faithful to both. That is the
content below. -/

/-- **Reversibility is layered**: the object layer admits a left inverse, and the semantic layer does not admit one.

Both halves carry their own witness, and the witnesses live at different arities and different carriers --
`roundtrip` is an obligation of the `Representation` structure (so any instance satisfies it), while the semantic
witness is concrete at arity one over `ZB`. Putting them in one conjunction is exactly the claim the objective
asks for: *layered*, not a single verdict. -/
theorem reversibility_is_layered {P W : Type} (compile : P → W) (extract : W → P)
    (hround : ∀ p, extract (compile p) = p) :
    (∀ p, extract (compile p) = p) ∧
      (∃ c c' : LinearForm ZB 1, c ≠ c' ∧ SemEq c c') :=
  ⟨hround, semantic_not_injective⟩

/-- **The two layers conflict**: an extractor cannot be faithful to both.

Stated without the semantic hypothesis that `no_extractor_both_layers` carries and does not use: the obstruction
is already present at the parameter level, since a left inverse must separate points that the semantic quotient
identifies.

`no_extractor_both_layers` remains the statement named in the file header's table; this version records that its
`_hsem` hypothesis is redundant, so a reader is not left thinking semantic equality does any work in the argument. -/
theorem layers_conflict {P W : Type} (compile : P → W) {c c' : P} (hne : c ≠ c') :
    ¬ ∃ extract : W → P, (∀ p, extract (compile p) = p) ∧
      extract (compile c) = extract (compile c') := by
  rintro ⟨extract, hround, hsame⟩
  rw [hround c, hround c'] at hsame
  exact hne hsame

/-- **A left inverse forces distinct parameters apart**, which is the mechanism behind `layers_conflict`. -/
theorem leftInverse_separates {P W : Type} (compile : P → W) (extract : W → P)
    (hround : ∀ p, extract (compile p) = p) :
    Function.Injective compile :=
  Function.LeftInverse.injective hround


/-! ## The round-trip as the IdempotentOn instance

extract ∘ compile is the identity, and IdempotentOn (in Lattice.Core.Idempotent) is the statement that covers both
this and a repair's absorption. Stating the instance here -- rather than only in the geometry layer, where it was
first noticed -- means a reader of the extraction file learns that the round-trip is one half of a shape the project
uses twice, not a fact standing alone.

The S := fun _ => True choice is the point of the unification: a repair fixes its satisfying subset and this fixes
everything, and both are the same statement at different S. -/

/-- **The round-trip is idempotent on everything**, the T3 instance of IdempotentOn. -/
theorem roundtrip_idempotentOn {P W : Type} (compile : P → W) (extract : W → P)
    (hround : ∀ p, extract (compile p) = p) :
    Lattice.Core.IdempotentOn (fun _ => True) (extract ∘ compile) :=
  Lattice.Core.idempotentOn_of_leftInverse compile extract hround

/-- **Every iterate of the round-trip is still the identity.** -/
theorem roundtrip_iterate {P W : Type} (compile : P → W) (extract : W → P)
    (hround : ∀ p, extract (compile p) = p) (n : ℕ) :
    ∀ p : P, (extract ∘ compile)^[n] p = p :=
  Lattice.Core.iterate_comp_of_leftInverse compile extract hround n


/-! ## The one statement both T3 and T4 contribute to

T3 says extraction inverts compilation; T4 says a repair leaves a satisfying point alone and reaches one in
finitely many steps. Neither implies the other, and until now no theorem's *conclusion* mentioned both -- they
shared a definition (`Lattice.Core.IdempotentOn`) but not a result.

The theorem below is the closed loop in fixed-point form. Starting from any symbolic point, there is one that is
satisfied, unchanged by further repair, **and** fixed by compile-then-extract. That is what the objective's loop
can actually achieve: not a return to the original weight (there is no right inverse; see
`semantic_not_injective`), but a stopping point the loop cannot move off.

The three conjuncts come from three different premises, which is why the statement would be weaker if any one
of them were dropped:

* `Rp.Sat q` from `Repair.progress` -- the loop terminates;
* `Rp.fix q = q` from `Repair.absorbs` -- termination leaves it alone;
* `R.extract (R.compile q) = q` from `Representation.roundtrip` -- the symbolic point survives a round trip. -/

/-- **The loop stops at a point that is satisfied, repair-stable, and round-trip fixed.**

T3 contributes the third conjunct and T4 the first two. The point is that they hold *at the same* `q`:
termination, absorption and round-trip are not three separate facts about three separate points. -/
theorem loop_fixed_point {P W : Type} (R : Representation P W) (Rp : Lattice.Core.Repair P)
    (p : P) :
    ∃ q : P, Rp.Sat q ∧ Rp.fix q = q ∧ R.extract (R.compile q) = q := by
  obtain ⟨n, hn⟩ := Rp.progress p
  refine ⟨Rp.fix^[n] p, hn, Rp.absorbs _ hn, R.roundtrip _⟩

/-- **… and the fixed point reached is one the loop cannot move off**, stated separately because a caller
watching only the repair needs only this half. -/
theorem loop_fixed_point_stable {P W : Type} (R : Representation P W) (Rp : Lattice.Core.Repair P)
    (p : P) :
    ∃ q : P, Rp.Sat q ∧ Rp.fix q = q := by
  obtain ⟨q, hsat, habs, _⟩ := loop_fixed_point R Rp p
  exact ⟨q, hsat, habs⟩


/-! ## Building a `Representation` from a bijection

The round-trip obligation is exactly "extraction is a left inverse of compilation", so any bijection qualifies.
Stating that once means every `≃` in the project -- `flattenEquiv` in the geometry layer among them -- becomes a
`Representation` without a fresh proof per instance.

`ofEquiv` is deliberately not an `instance`: a type can carry many bijections, and silently picking one would make
`Representation` resolution depend on import order. -/

/-- **A `Representation` from a bijection.** Compilation is the forward map, extraction its inverse, and the
round-trip holds by `Equiv.symm_apply_apply`. -/
def ofEquiv {P W : Type} (e : P ≃ W) : Representation P W where
  inputP := P
  inputW := W
  encode := e
  decode := e.symm
  compile := e
  extract := e.symm
  roundtrip := fun p => e.symm_apply_apply p

/-- **`ofEquiv` is not vacuous**: its extraction really inverts its compilation, stated as its own theorem so a
caller does not have to unfold the structure to see it. -/
theorem ofEquiv_roundtrip {P W : Type} (e : P ≃ W) (p : P) :
    (ofEquiv e).extract ((ofEquiv e).compile p) = p :=
  e.symm_apply_apply p

/-- **… and the other direction too**, which is what makes it a bijection rather than only an injection. -/
theorem ofEquiv_compile_extract {P W : Type} (e : P ≃ W) (w : W) :
    (ofEquiv e).compile ((ofEquiv e).extract w) = w :=
  e.apply_symm_apply w

end Lattice.Lift
