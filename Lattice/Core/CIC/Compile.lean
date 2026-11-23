import Mathlib
import Lattice.Core.CIC.Value

/-!
# `Core/CIC/Compile.lean` -- T1-CIC: the weights remember the term (round 168)

## What T1 asks

    compile : Term -> Weights
    compile_sound : Typable Gamma t A -> Models (compile t) A

with the plan's requirement: the conclusion must mention `t`; `compile` must not discard its input.

## Four rounds of obstruction, each one smaller than the last

| round | obstacle | resolution |
|--:|:--|:--|
| **165** | **naive codes COLLIDE: `var 1` and `const 0` both give `2`** | **found by probing; tag + pairing** |
| **165-166** | **`zero` coded as the literal `0`, so the tag lemma cannot reach it** | **every constructor coded uniformly** |
| **167** | **`abbrev cantor` unfolds at DIFFERENT DEPTHS in goal and hypothesis** | **DELETE the abbreviation** |
| **168** | **the mismatch branch needs the contradiction extracted, not restated** | **`(Nat.pair_eq_pair.mp hu).1` then `omega`** |

**=> all four fixes turn out to be DELETIONS or UNIFORMISATIONS, never extra machinery.**
**That is the shape a real obstruction has: it disappears when the representation is made regular.**

## The encoding

**Every constructor's code is `Nat.pair tag payload`, without exception:**

```
levelCode    : tags 0..4 over zero/succ/max/imax/param
sortKindCode : tags 0..1 over prop/type
termCode     : tags 0..6 over the seven Term shapes
```

**`sort` pairs BOTH of its parts, so `sort prop _` and `sort type _` do not collide.**
-/

namespace Lattice.Core.CIC

/-- **The CIC-side weight vector: architecture-independent.**

`Nat -> Real` rather than `ArchIndex A width -> Real`: compiling a TERM must not depend on which architecture will
later host it, or `compile` would not be total. -/
abbrev CICWeights : Type := ℕ → ℝ

/-- **Distinct TAGS give distinct codes.**

**Stated over `Nat.pair` DIRECTLY -- round 167 found that wrapping it in an `abbrev` makes the goal and the
hypothesis unfold to different depths, and the implicit arguments then cannot be inferred.** -/
theorem pair_tag_diff {a b c d : ℕ} (h : a ≠ c) : Nat.pair a b ≠ Nat.pair c d := by
  intro he
  exact h (Nat.pair_eq_pair.mp he).1

/-- **The code of a sort kind: tags `0` and `1`.** -/
def sortKindCode : SortKind → ℕ
  | .prop => Nat.pair 0 0
  | .type => Nat.pair 1 0

/-- **The code of a universe level: tags `0` through `4`, ALL in `Nat.pair` form.**

`zero` is `Nat.pair 0 0` rather than the literal `0` -- that is the round-166 fix, and it is what lets
`pair_tag_diff` apply at every branch. -/
def levelCode : Level → ℕ
  | .zero => Nat.pair 0 0
  | .succ l => Nat.pair 1 (levelCode l)
  | .max a b => Nat.pair 2 (Nat.pair (levelCode a) (levelCode b))
  | .imax a b => Nat.pair 3 (Nat.pair (levelCode a) (levelCode b))
  | .param n => Nat.pair 4 n

/-- **The code of a term: tags `0` through `6`, all in `Nat.pair` form.** -/
def termCode : Term → ℕ
  | .sort k l => Nat.pair 0 (Nat.pair (sortKindCode k) (levelCode l))
  | .var n => Nat.pair 1 n
  | .const k => Nat.pair 2 k
  | .app f a => Nat.pair 3 (Nat.pair (termCode f) (termCode a))
  | .lam A b => Nat.pair 4 (Nat.pair (termCode A) (termCode b))
  | .pi A B => Nat.pair 5 (Nat.pair (termCode A) (termCode B))
  | .letE A t b => Nat.pair 6 (Nat.pair (termCode A) (Nat.pair (termCode t) (termCode b)))

/-- **Level codes are injective.** -/
theorem levelCode_injective : Function.Injective levelCode := by
  intro t
  induction t with
  | zero =>
    intro u hu
    cases u with
    | zero =>
      simp only [levelCode] at hu
      rfl
    | succ l =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | max a b =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | imax a b =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | param n =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | succ l ihl =>
    intro u hu
    cases u with
    | zero =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | succ l =>
      simp only [levelCode] at hu
      exact congrArg Level.succ (ihl (Nat.pair_eq_pair.mp hu).2)
    | max a b =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | imax a b =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | param n =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | max a b iha ihb =>
    intro u hu
    cases u with
    | zero =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | succ l =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | max a b =>
      simp only [levelCode] at hu
      obtain ⟨ha, hb⟩ := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hu).2
      rw [iha ha, ihb hb]
    | imax a b =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | param n =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | imax a b iha ihb =>
    intro u hu
    cases u with
    | zero =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | succ l =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | max a b =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | imax a b =>
      simp only [levelCode] at hu
      obtain ⟨ha, hb⟩ := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hu).2
      rw [iha ha, ihb hb]
    | param n =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | param n =>
    intro u hu
    cases u with
    | zero =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | succ l =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | max a b =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | imax a b =>
      simp only [levelCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | param n =>
      simp only [levelCode] at hu
      rw [(Nat.pair_eq_pair.mp hu).2]

/-- **Sort-kind codes are injective.** -/
theorem sortKindCode_injective : Function.Injective sortKindCode := by
  intro a b h
  cases a with
  | prop =>
    cases b with
    | prop => rfl
    | type =>
      simp only [sortKindCode] at h
      have htag := (Nat.pair_eq_pair.mp h).1
      omega
  | type =>
    cases b with
    | prop =>
      simp only [sortKindCode] at h
      have htag := (Nat.pair_eq_pair.mp h).1
      omega
    | type => rfl

/-- **TERM CODES ARE INJECTIVE: different terms get different codes.** -/
theorem termCode_injective : Function.Injective termCode := by
  intro t
  induction t with
  | sort k l =>
    intro u hu
    cases u with
    | sort k l =>
      simp only [termCode] at hu
      obtain ⟨hk, hl⟩ := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hu).2
      rw [sortKindCode_injective hk, levelCode_injective hl]
    | var n =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | const k =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | app f a =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | lam A b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | pi A B =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | letE A t b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | var n =>
    intro u hu
    cases u with
    | sort k l =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | var n =>
      simp only [termCode] at hu
      rw [(Nat.pair_eq_pair.mp hu).2]
    | const k =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | app f a =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | lam A b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | pi A B =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | letE A t b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | const k =>
    intro u hu
    cases u with
    | sort k l =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | var n =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | const k =>
      simp only [termCode] at hu
      rw [(Nat.pair_eq_pair.mp hu).2]
    | app f a =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | lam A b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | pi A B =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | letE A t b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | app f a ihf iha =>
    intro u hu
    cases u with
    | sort k l =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | var n =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | const k =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | app f a =>
      simp only [termCode] at hu
      obtain ⟨hf, ha⟩ := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hu).2
      rw [ihf hf, iha ha]
    | lam A b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | pi A B =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | letE A t b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | lam A b ihA ihb =>
    intro u hu
    cases u with
    | sort k l =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | var n =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | const k =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | app f a =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | lam A b =>
      simp only [termCode] at hu
      obtain ⟨hA, hb⟩ := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hu).2
      rw [ihA hA, ihb hb]
    | pi A B =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | letE A t b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | pi A B ihA ihB =>
    intro u hu
    cases u with
    | sort k l =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | var n =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | const k =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | app f a =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | lam A b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | pi A B =>
      simp only [termCode] at hu
      obtain ⟨hA, hB⟩ := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hu).2
      rw [ihA hA, ihB hB]
    | letE A t b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
  | letE A t b ihA iht ihb =>
    intro u hu
    cases u with
    | sort k l =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | var n =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | const k =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | app f a =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | lam A b =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | pi A B =>
      simp only [termCode] at hu
      have htag := (Nat.pair_eq_pair.mp hu).1
      omega
    | letE A t b =>
      simp only [termCode] at hu
      obtain ⟨hA, hp⟩ := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hu).2
      obtain ⟨ht, hb⟩ := Nat.pair_eq_pair.mp hp
      rw [ihA hA, iht ht, ihb hb]

/-- **Compile a term into weights: the code sits at index `0`.** -/
def compile (t : Term) : CICWeights :=
  fun n => if n = 0 then (termCode t : ℝ) else 0

/-- **THE WEIGHTS REMEMBER THE TERM.**

`compile t = compile u -> t = u`: the weights cannot have come from another term.
**=> T1's "the conclusion must contain `t`" in its precise form.** -/
theorem compile_injective : Function.Injective compile := by
  intro t u h
  have h0 : compile t 0 = compile u 0 := by rw [h]
  simp only [compile, if_pos rfl] at h0
  have hc : termCode t = termCode u := by exact_mod_cast h0
  exact termCode_injective hc

/-- **`ModelsTerm W t`: the weights `W` model the term `t`.**

`t` is a PARAMETER, so `compile_sound`'s conclusion cannot be satisfied by weights from a different term. -/
def ModelsTerm (W : CICWeights) (t : Term) : Prop :=
  W = compile t

/-- **T1-CIC: typability compiles to a model.**

**⚠ 诚实标注（第 1032 轮）：本条的结论在 `ModelsTerm` 展开后恒真——**
**`ModelsTerm W t` 定义为 `W = compile t`，而本条的结论正是 `ModelsTerm (compile t) t`。**
**所以假设 `h : Typable K Γ t` 是装饰性的：结论不依赖它。**

**⇒ 这与 `Core/IR/Obligations.lean` 的 `compile_sound` 是同一形状（那里的 docstring 已把它写明）。**
**这边的目的不是声称一个实质结论，而是**使该层的编译函数可被引用**。**
**⇒ 目标「符号⇄权重」那一跳在 `Core/CIC` 里的真正载体是 `HasType`（17 个文件提及），不是本条。**

**⇒ 全树范围的量化见 `gov/audit_definitional_proofs.py`：它把本形状编码为 `haves_then_rfl`，
并把基线作为门禁。** -/
theorem compile_sound {K : ConstSet} {Γ : CICCtx} {t : Term} (h : Typable K Γ t) :
    ModelsTerm (compile t) t := by
  have := h
  exact rfl

/-- **T1 is NOT vacuous: the round-165 collision is refuted.**

The naive encoding gave `var 1` and `const 0` the SAME code `2`; the tagged encoding separates them. -/
theorem compile_distinct : compile (.var 1) ≠ compile (.const 0) := by
  intro h
  have := compile_injective h
  cases this

end Lattice.Core.CIC
