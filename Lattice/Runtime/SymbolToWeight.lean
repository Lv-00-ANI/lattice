import Mathlib
import Lattice.Core.Syntax
import Lattice.Core.Semantics
import Lattice.Plugins.Core.Constraint.Proofs
/-!
# `Lattice.Lift.SymbolToWeight` -- T1: compilation preserves meaning

## The theorem

For a symbolic program `ps : List P`, its compilation to a weighted artifact must
accept everything the program accepts, under the input translation the compiler
declares:

```
Compiler.EntailsP ps x  →  Compiler.EntailsW (compileProgram ps) (encode x)
```

This is quantified over every `Compiler`, so it holds for the linear fragment and for
any future compiler (non-linear, tensor-valued, external) without reproof.

## Why the legacy version is not this theorem

`SymbolToWeightCorrectness.symbolToWeight_correct` states

```
AllSatisfied cs x → AllZeroOutputs (compileToLayer cs) x
```

for a *fixed* `x`. That is a pointwise identity between two lists built by `List.map`,
proved by `forall_mem_map_iff`; it never leaves the list structure. It is a true and
useful sanity check, but "for this `x`, mapping preserves the predicate" is not the
same claim as "the compiled artifact models the program", and it is why the legacy
chain could not compose with anything above it.

What is added here:

* **a model-level form** (`compileProgram_models`), which is what later passes consume;
* **an explicit `encode`**, without which the theorem is false (see `encode_necessary`);
* **instance-independence**, so swapping the semantics cannot invalidate it.

## Why `encode` is load-bearing

A compiler may legitimately change how an input is represented: packing, casting `ℤ`
to `ℝ`, reordering, adding a bias slot. The legacy interface had no such slot, because
it assumed both sides consume the same `List Int` -- and that assumption is exactly
what let the truncated `dot` pass unnoticed.
-/

namespace Lattice.Lift

open Lattice.Core

/-- A compilation from a symbolic side `P` to a weighted side `W`.

The fields are the *obligations* a compiler discharges; the theorems below then hold
for every inhabitant automatically. -/
structure Compiler (P : Type) (W : Type) (inputP : Type) (inputW : Type) where
  /-- How a symbolic input is presented to the weighted artifact. -/
  encode : inputP → inputW
  /-- The compile function itself. -/
  compile : P → W
  /-- What it means for a symbolic item to accept a point. -/
  satP : P → inputP → Prop
  /-- What it means for a weighted item to accept a point. -/
  satW : W → inputW → Prop
  /-- **The obligation.** Each compiled item accepts whatever its source accepted,
  once the input is translated. -/
  sound : ∀ (p : P) (x : inputP), satP p x → satW (compile p) (encode x)

namespace Compiler

variable {P W inputP inputW : Type} (C : Compiler P W inputP inputW)

/-- Program-level compilation: every item compiled, order preserved. -/
def compileProgram (ps : List P) : List W := ps.map C.compile

/-- A point satisfies a program when it satisfies every item. -/
def EntailsP (ps : List P) (x : inputP) : Prop := ∀ p ∈ ps, C.satP p x

/-- A point satisfies a compiled program when it satisfies every compiled item. -/
def EntailsW (ws : List W) (y : inputW) : Prop := ∀ w ∈ ws, C.satW w y

/-- **T1, list level.** If every item is accepted at `x`, every compiled item is
accepted at `encode x`.

An induction on the list uses nothing but the per-item obligation. No property of
`compile`, `encode` or the predicates is assumed, which is precisely why the result
survives a change of instance. -/
theorem compileProgram_sound (ps : List P) (x : inputP) :
    C.EntailsP ps x → C.EntailsW (C.compileProgram ps) (C.encode x) := by
  intro h w hw
  rw [Compiler.compileProgram, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  exact C.sound p x (h p hp)

/-- **T1, model level.** A compiled item accepts every point that the program accepts.

This is the form the rest of the ladder consumes: it composes with `Models` and is
strictly stronger than stating the property at one point. -/
theorem compileProgram_models (ps : List P) (c : P) (hmem : c ∈ ps) :
    ∀ x : inputP, C.EntailsP ps x → C.satW (C.compile c) (C.encode x) :=
  fun x hx => C.compileProgram_sound ps x hx (C.compile c)
    (List.mem_map_of_mem (f := C.compile) hmem)

/-- Compilation commutes with concatenation: a program compiled in two halves equals
the compilation of the whole. This is what lets a pipeline be checked piecewise. -/
theorem compileProgram_append (ps qs : List P) :
    C.compileProgram (ps ++ qs) = C.compileProgram ps ++ C.compileProgram qs := by
  unfold Compiler.compileProgram
  exact List.map_append _ _ _

end Compiler

/-! ## Necessity: `encode` cannot be dropped

The legacy interface had no `encode`, i.e. it assumed both sides consume the same
input type and `encode = id`. The counterexample below is written *without* a
structure projection, so that no reduction of a field type is needed to state it: it
compares the two obligations directly. -/

section Necessity

/-- Source accepts negative integers. -/
def srcAccepts (x : ℤ) : Prop := x < 0

/-- Target accepts positive integers. -/
def tgtAccepts (y : ℤ) : Prop := 0 < y

/-- The input translation: negation. -/
def toTargetInput (x : ℤ) : ℤ := -x

/-- **With the translation, the obligation holds.** -/
theorem with_encode :
    ∀ x : ℤ, srcAccepts x → tgtAccepts (toTargetInput x) := by
  intro x h
  have hx : x < 0 := h
  simp only [srcAccepts, tgtAccepts, toTargetInput]
  linarith

/-- **Without the translation, the obligation fails**: at `x = -1` the source accepts
while the target rejects. This is why `encode` is a required field of `Compiler` and
not a convenience. -/
theorem encode_necessary : ¬ ∀ x : ℤ, srcAccepts x → tgtAccepts x := by
  intro h
  have h1 : srcAccepts (-1) := by simp only [srcAccepts]; norm_num
  have h2 : tgtAccepts (-1) := h (-1) h1
  simp only [tgtAccepts] at h2
  norm_num at h2

/-- **`encode` is a necessary field, not a convenience.**

The two theorems above are its two halves: with the input translation the obligation holds, and without it the
obligation fails. Stating them as one conjunction is what makes "necessary" a formal claim rather than a label --
a reader who sees only the two names has to guess how they relate.

**What "necessary" does *not* mean**: it is not that `x ↦ -x` is the only translation that works (it is not --
`x ↦ -x - 1` also maps the source's region into the target's -- a remark, not a theorem). The claim is only that the *identity* fails, which
is exactly the counterexample below. A stronger claim would be false, and this file does not make one. -/
theorem encode_is_necessary :
    (∀ x : ℤ, srcAccepts x → tgtAccepts (toTargetInput x)) ∧
      ¬ (∀ x : ℤ, srcAccepts x → tgtAccepts x) :=
  ⟨with_encode, encode_necessary⟩

end Necessity
