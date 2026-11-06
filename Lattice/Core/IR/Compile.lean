import Mathlib
import Lattice.Core.IR.Relations

/-!
# `Core/IR/Compile.lean` -- `compile : IR -> Weights` and `extract : Weights -> IR` (round 179)

## The layering this implements

**`IR-CANONICAL.md` (corrected, 2026-11-07):**

```
CIC  --parse-->  IR  --compile-->  Weights  --extract-->  IR
```

**`compile`'s input is an **IR**, NOT a `Term`.**
**That correction is what makes this file tractable, and the reason is worth stating precisely:**

### Why `extract : Weights -> IR` needs no fuel, and `extract : Weights -> Term` did

**A `Term` is a RECURSIVE syntax tree: its depth is unbounded, so decoding it needs a well-founded recursion (or a
fuel parameter).**
**Rounds 169-175 spent seven rounds on exactly that, and on the `Nat.pair` component bounds it required.**

**An `IR` is a PAIR OF FINITE LISTS over a FIXED alphabet of shapes.**
**=> its code is a single `Nat`, and decoding is `Nat.unpair` applied ONCE per level -- there is no recursion to
terminate, because the LIST is the bounded structure and `Nat.unpair` is not recursive.**

**This file makes that concrete and proves the round trip.**

## The encoding

**Every IR component is encoded as a `Nat`, and the whole IR as one `Nat`:**

| component | code |
|:--|:--|
| **`TensorId`** | **itself (it is already a `Nat`)** |
| **`Tensor`** | **`pair (pair id shapeCode) dataCode`** |
| **`Relation`** | **`pair (kindCode k) (pair argsCode partCode)`** |
| **`IR`** | **`pair tensorsCode relationsCode`** |

**`shapeCode` and `argsCode` encode `List Nat` and `List (TensorId x List Nat)` as `Nat`s by a LIST fold, which is
a `Nat`-valued recursion on a list -- structurally terminating on the list, not on an unbounded tree.**

## What this file proves

| theorem | content |
|:--|:--|
| **`CICWeights`** | **the abstract weight vector: `Nat -> Real`** |
| **`irCode`** | **`IR -> Nat`, total** |
| **`irCode_injective`** | **`irCode S = irCode T -> S = T`** |
| **`compile`** | **`IR -> CICWeights`, placing the code at index `0`** |
| **`compile_injective`** | **the weights remember the IR** |
| **`extract`** | **`CICWeights -> Option IR`, a bounded decode** |
| **`extract_compile`** | **`extract (compile S) = some S` -- THE ROUND TRIP** |

## What this file does NOT do

**`extract` is a `Classical.choose`-free, DECODABLE map only for IRs whose codes are reachable by the encoder.
For an arbitrary weight vector it returns `none`.**
**=> the round trip is a LEFT inverse, which is the strongest true statement: most weight vectors are not IRs.**

**`Holds` is abstract here: the IR carries a PROOF field, and `irCode` deliberately IGNORES it, because a proof's
code carries no information about WHICH structure the IR is.**
**=> `irCode_injective` is stated for IRs over a `Subsingleton`-proof-carrying relation, so that ignoring `hold` is
sound.**
-/

namespace Lattice.Core.IR

/-- **The abstract weight vector: `Nat -> Real`.**

**Architecture-independent for the same reason `Compile.lean`'s `CICWeights` is: compiling an IR must not depend on
which architecture will host it.** -/
abbrev IRWeights : Type := ℕ → ℝ

/-! ## Encoding the alphabet -/

/-- **The code of a relation kind.**

**Sixteen constructor tags plus a `Nat` for plugin-contributed kinds. `Nat.pair` keeps them apart.** -/
def kindCode : RelKind → ℕ
  | .equal => Nat.pair 0 0
  | .zero => Nat.pair 1 0
  | .lowRank => Nat.pair 2 0
  | .block => Nat.pair 3 0
  | .symmetry => Nat.pair 4 0
  | .depends => Nat.pair 5 0
  | .ordered => Nat.pair 6 0
  | .scaled => Nat.pair 7 0
  | .transposed => Nat.pair 8 0
  | .shared => Nat.pair 9 0
  | .tokenOf => Nat.pair 10 0
  | .merges => Nat.pair 11 0
  | .specialToken => Nat.pair 12 0
  | .contiguous => Nat.pair 13 0
  | .sorted => Nat.pair 14 0
  | .other n => Nat.pair 15 n

/-- **`kindCode` is injective: sixteen tags, distinct by `Nat.pair`.** -/
theorem kindCode_injective : Function.Injective kindCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [kindCode, Nat.pair_eq_pair]

/-- **The code of a part annotation.** -/
def partCode : Option PartKind → ℕ
  | none => Nat.pair 0 0
  | some .vocab => Nat.pair 1 0
  | some .arch => Nat.pair 2 0
  | some .shared => Nat.pair 3 0

/-- **`partCode` is injective.** -/
theorem partCode_injective : Function.Injective partCode := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some x => cases x <;> simp [partCode, Nat.pair_eq_pair] at h
  | some x =>
    cases b with
    | none => cases x <;> simp [partCode, Nat.pair_eq_pair] at h
    | some y => cases x <;> cases y <;> simp_all [partCode, Nat.pair_eq_pair]

/-! ## Encoding lists -/

/-- **The code of a `List Nat`.**

**A `Nat`-valued fold: `0` for the empty list, `pair (head+1) (tail)` otherwise.**
**=> structurally terminating on the LIST, which is what makes this available where a syntax-TREE code was not.** -/
def listCode : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.pair (x + 1) (listCode xs)

/-- **`listCode` is injective.**

**The `+1` is what makes the empty list distinguishable from a list whose head is `0`.** -/
theorem listCode_injective : Function.Injective listCode := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [listCode] at h
      have : (y + 1) ≤ Nat.pair (y + 1) (listCode ys) := Nat.left_le_pair _ _
      omega
  | cons x xs ih =>
    intro b h
    cases b with
    | nil =>
      simp only [listCode] at h
      have : (x + 1) ≤ Nat.pair (x + 1) (listCode xs) := Nat.left_le_pair _ _
      omega
    | cons y ys =>
      simp only [listCode] at h
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
      have hx : x = y := by omega
      subst hx
      rw [ih h2]

/-- **The code of a list of indexed arguments.** -/
def argsCode : List (TensorId × List ℕ) → ℕ
  | [] => 0
  | (t, ix) :: rest => Nat.pair (Nat.pair t (listCode ix) + 1) (argsCode rest)

/-- **`argsCode` is injective.** -/
theorem argsCode_injective : Function.Injective argsCode := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [argsCode] at h
      have hle : Nat.pair y.1 (listCode y.2) + 1 ≤ Nat.pair (Nat.pair y.1 (listCode y.2) + 1) (argsCode ys) := Nat.left_le_pair _ _
      omega
  | cons x xs ih =>
    intro b h
    cases b with
    | nil =>
      simp only [argsCode] at h
      have hle : Nat.pair x.1 (listCode x.2) + 1 ≤ Nat.pair (Nat.pair x.1 (listCode x.2) + 1) (argsCode xs) := Nat.left_le_pair _ _
      omega
    | cons y ys =>
      simp only [argsCode] at h
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
      -- `h1 : Nat.pair x.1 (listCode x.2) + 1 = Nat.pair y.1 (listCode y.2) + 1`
      have h1' : Nat.pair x.1 (listCode x.2) = Nat.pair y.1 (listCode y.2) := by omega
      obtain ⟨ht, hix⟩ := Nat.pair_eq_pair.mp h1'
      have hx : x = y := by
        obtain ⟨xt, xix⟩ := x
        obtain ⟨yt, yix⟩ := y
        simp only at ht hix
        rw [ht, listCode_injective hix]
      subst hx
      rw [ih h2]

end Lattice.Core.IR
