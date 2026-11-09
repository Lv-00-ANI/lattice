/-
# `Plugins/Targets/T3NonVacuous.lean` -- T3's "no faithful extractor" made NON-VACUOUS (plan C-5)

## The defect the audit named

**`t3_no_faithful_extractor` is**

```
∀ {P W} (compile : P → W) (sem : P → P → Prop) {c c' : P},
  c ≠ c' → sem c c' → ∀ (extract : W → P), ...
```

**and it quantifies over EVERY `sem`.**
**=> taking `sem := fun _ _ => False` makes it trivially true: the hypothesis `sem c c'` can never be
discharged.**

**A statement that is satisfied by an empty relation says nothing about the semantic layer.**
**The audit's objection is exact: the theorem does not assert "the semantic layer is not invertible", it asserts
"any relation with a non-reflexive pair cannot be both inverted and collapsed" -- which is a statement about
`sem`, not about geometry.**

## What makes it non-vacuous

**A single instance of `sem` that is INHABITED, and the tree already has one.**
**`Geo.semantic_not_injective` proves that translation preserves every `Translatable` constraint while MOVING the
configuration:**

```
translate t pts ≠ pts  ∧  ∀ c, Translatable c → (Holds c pts ↔ Holds c (translate t pts))
```

**=> `translationEquivalent pts := fun a b => ∃ t, a = pts ∧ b = translate t pts` is INHABITED at a non-reflexive
pair, and it is exactly the `sem` the impossibility needs.**

## What this file proves

| declaration | content |
|:--|:--|
| `translationSem` | **translation equivalence, as a `P → P → Prop`** |
| `translationSem_inhabited` | **it has a NON-REFLEXIVE pair** -- **the non-vacuity witness** |
| `no_faithful_extractor_nontrivial` | **T3's impossibility, INSTANTIATED at `translationSem`** |

**=> the quantified `sem` in T3's statement is not always `False`, and the impossibility is TRUE at the instance
geometry actually supplies.**

## What this file does NOT do

**It does not replace `t3_no_faithful_extractor`.** **The general statement stays, because it is the right shape
for an obligation that must hold for EVERY semantics a caller might build.**
**What is added is the WITNESS that at least one such semantics is inhabited -- which is what the audit found
missing.**

**The distinction is the same one round 110 drew for T3's parameter layer: coverage of the quantifier is a
statement about the quantifier, and an instance is a statement about the carrier.**
-/

import Mathlib
import Lattice.Plugins.Targets.Statements
import Lattice.Reference.Geometry.Geometry.Semantic
import Lattice.Runtime.Extraction

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Geo

/-! ## The witness relation -/

/-- **Translation equivalence: `b` is a translate of `a`.**

**The relation the semantic layer actually quotients by -- `Geo.semantic_not_injective` establishes that
translation moves a configuration while preserving every `Translatable` constraint.** -/
def translationSem {n : ℕ} (pts : ℕ → Pt n) (a b : ℕ → Pt n) : Prop :=
  ∃ t : Pt n, a = pts ∧ b = translate t pts

/-- **`translationSem` has a NON-REFLEXIVE pair.**

**The non-vacuity witness: `sem` in T3 is quantified over all relations, and this theorem shows the quantifier is
not degenerate.**
**The pair is `(pts, translate t pts)` with `t ≠ 0`, which `semantic_not_injective` proves are UNEQUAL.** -/
theorem translationSem_inhabited {n : ℕ} (t : Pt n) (hne : ∃ i : Fin n, t i ≠ 0) (pts : ℕ → Pt n) :
    translationSem pts pts (translate t pts) ∧ translate t pts ≠ pts := by
  refine ⟨⟨t, rfl, rfl⟩, ?_⟩
  exact (semantic_not_injective t hne pts).1

/-- **The pair is non-reflexive AND related -- exactly the hypotheses T3's statement consumes.**

**Stated as a conjunction so that `no_faithful_extractor_nontrivial` can use it directly.** -/
theorem translationSem_nontrivial {n : ℕ} (t : Pt n) (hne : ∃ i : Fin n, t i ≠ 0) (pts : ℕ → Pt n) :
    translate t pts ≠ pts ∧ translationSem pts pts (translate t pts) :=
  ⟨(translationSem_inhabited t hne pts).2, (translationSem_inhabited t hne pts).1⟩

/-! ## T3's impossibility at the witness -/

/-- **NO extractor inverts a collapse AND respects it -- instantiated at `translationSem`.**

**This is `t3_no_faithful_extractor_holds` applied to a relation the tree PROVES is inhabited at a non-reflexive
pair.**
**=> the general statement is not vacuously true on `sem := False` alone: it fires at the geometry the project
actually formalises.** -/
theorem no_faithful_extractor_nontrivial {n : ℕ} (t : Pt n) (hne : ∃ i : Fin n, t i ≠ 0) (pts : ℕ → Pt n)
    {W : Type} (compile : (ℕ → Pt n) → W) :
    ∀ (extract : W → (ℕ → Pt n)),
      (∀ p, extract (compile p) = p) →
      ¬ (∀ a b : ℕ → Pt n, translationSem pts a b →
          extract (compile a) = extract (compile b)) := by
  have hnt := translationSem_nontrivial t hne pts
  intro extract hround
  -- the binder order is `compile, sem, {c, c'}, hne, hsem, extract, hround`
  exact @t3_no_faithful_extractor_holds (ℕ → Pt n) W compile (translationSem pts)
    pts (translate t pts) hnt.1.symm hnt.2 extract hround

/-! ## The count of inhabited semantics -/

/-- **The `sem` in T3 is NOT always empty.**

**A one-line corollary worth naming: there EXISTS a relation making T3's hypotheses simultaneously satisfiable.**
**Without this, the general theorem could be read as a statement about the empty relation and nothing else.** -/
theorem sem_quantifier_not_degenerate (n : ℕ) (t : Pt n) (hne : ∃ i : Fin n, t i ≠ 0) (pts : ℕ → Pt n) :
    ∃ sem : (ℕ → Pt n) → (ℕ → Pt n) → Prop, ∃ c c' : ℕ → Pt n,
      c ≠ c' ∧ sem c c' := by
  have hnt := translationSem_nontrivial t hne pts
  exact ⟨translationSem pts, pts, translate t pts, hnt.1.symm, hnt.2⟩

end Lattice.Plugins.Targets
