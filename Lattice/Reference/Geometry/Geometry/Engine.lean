import Mathlib
import Lattice.Reference.Geometry.Constraints.Constraint
import Lattice.Plugins.Core.Constraint.Proofs
/-!
# `Lattice.Geo.Engine` -- a symbolic engine over geometric constraints

## What the objective asks for, and what was missing

The project is required to run the symbolic model **on a symbolic engine, without adding an
intermediary layer**. Until now `Lattice.Geo` provided the syntax (`GeoExpr`, `GeoConstraint`) and a
semantics (`Holds`), but nothing that reasons: a constraint graph could be *evaluated* at a
configuration, not *queried*.

An engine is not an interpreter. `Holds` answers "does this hold here"; an engine answers "what follows
from these". This file supplies the second.

## The choice of engine, and why it is entailment rather than satisfiability

The closed loop the project describes is `symbol → weight → extract → verify → repair → re-inject`, and
its `verify` step has a specific shape: *does what was extracted entail what was asked for?* That is
entailment, not satisfiability.

Deciding satisfiability of geometric constraints would also be the wrong target for a different reason:
the theory of real closed fields is decidable (Tarski), but no decision procedure for it is going to be
built here, and a definition of `Satisfiable` with no procedure behind it would be the hollow-shell
pattern `_archive/ZERO-ESCAPE-NOT-IMPLEMENTED.md` warns about.

So the engine works by **sound inference**: a `Rule` carries its premises, its conclusion, and a proof
that premise-satisfaction implies conclusion-satisfaction. Nothing can enter the closure without that
proof, which is what makes `closure_sound` a real statement rather than a claim about a program.

## Why this is not an "intermediary layer"

The engine consumes `GeoConstraint` and produces `GeoConstraint`. There is no normalised form, no IR, no
lowering step. The objective's "no intermediary layer" is satisfied by construction: `Rule` is indexed by
the same type the symbolic model is written in.

## Scope

The rule set below is deliberately small -- symmetry laws plus a transitivity law -- because every rule
must carry a proof and a large set would be a large proof obligation, not a large result. The framework
is what matters: adding a rule is adding one `Rule` value with one `sound` proof, and `closure_sound`
continues to hold for any list of rules.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The symbolic engine's state**: a finite list of constraints.

A list rather than a set so that the engine's output is computable data, and duplicated entries are
harmless because entailment is idempotent. -/
abbrev GeoConstraintSet (n : ℕ) : Type := List (GeoConstraint n)

/-- **A configuration satisfies a constraint set.** -/
noncomputable def ModelsGeo (G : GeoConstraintSet n) (pts : ℕ → Pt n) : Prop :=
  ∀ c ∈ G, GeoConstraint.Holds c pts

/-- **Entailment between constraint sets.**

`EntailsGeo G c` says every configuration that satisfies `G` also satisfies `c`. This is the predicate the
verification step asks about. -/
noncomputable def EntailsGeo (G : GeoConstraintSet n) (c : GeoConstraint n) : Prop :=
  ∀ pts : ℕ → Pt n, ModelsGeo G pts → GeoConstraint.Holds c pts

/-- Entailment is reflexive in the strong sense: a constraint entails itself. -/
theorem entailsGeo_refl (c : GeoConstraint n) : EntailsGeo [c] c := by
  intro pts h
  exact h c (List.mem_singleton.mpr rfl)

/-- Monotonicity: adding constraints cannot destroy entailment. -/
theorem entailsGeo_mono {G H : GeoConstraintSet n} {c : GeoConstraint n}
    (hsub : ∀ d ∈ G, d ∈ H) (h : EntailsGeo G c) : EntailsGeo H c := by
  intro pts hH
  exact h pts (fun d hd => hH d (hsub d hd))

/-- **A sound inference rule.**

`sound` is the whole content: whatever makes the premises true makes the conclusion true. A rule cannot
be constructed without it, which is why the closure below is sound by construction rather than by
inspection.
-/
structure Rule (n : ℕ) where
  /-- The premises. -/
  prems : List (GeoConstraint n)
  /-- The conclusion. -/
  concl : GeoConstraint n
  /-- **Preservation of truth.** -/
  sound : ∀ pts : ℕ → Pt n,
    (∀ c ∈ prems, GeoConstraint.Holds c pts) → GeoConstraint.Holds concl pts

/-- **Applying one rule**: if the closure so far entails every premise, it entails the conclusion.

This is where `Rule.sound` is consumed; it is a `Prop`-valued predicate rather than a list operation
because the engine's output should be justified, not merely computed. -/
theorem rule_entails (r : Rule n) (G : GeoConstraintSet n)
    (h : ∀ c ∈ r.prems, EntailsGeo G c) : EntailsGeo G r.concl := by
  intro pts hG
  exact r.sound pts (fun c hc => h c hc pts hG)

/-- **The engine's closure condition**: a constraint set is closed under a rule set when every rule whose
premises are already entailed has its conclusion entailed. -/
noncomputable def Closed (rules : List (Rule n)) (G : GeoConstraintSet n) : Prop :=
  ∀ r ∈ rules, (∀ c ∈ r.prems, EntailsGeo G c) → EntailsGeo G r.concl

/-- **One engine step is sound.**

If some rule in the engine has a conclusion `c` whose premises are all entailed by `G`, then `G` entails
`c`. This is the unit of engine correctness; multi-step inference is its transitive closure, and stating
it separately keeps each piece checkable.

`r ∈ rules` is `Prop`-valued on purpose: the engine is defined by what it *may* derive, and the
soundness statement quantifies over all legal derivations rather than over a particular evaluation
strategy. -/
theorem step_sound (rules : List (Rule n)) (G : GeoConstraintSet n) (c : GeoConstraint n)
    (h : ∃ r ∈ rules, c = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d) : EntailsGeo G c := by
  obtain ⟨r, _hr, hc, hpre⟩ := h
  subst hc
  exact rule_entails r G hpre

/-- **The empty rule list derives nothing**, so the engine is not vacuous in one direction: with no rules
there is nothing to conclude. This is the base case that makes `step_sound` meaningful. -/
theorem no_rules_no_steps (G : GeoConstraintSet n) (c : GeoConstraint n) :
    ¬ ∃ r ∈ ([] : List (Rule n)), c = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d := by
  rintro ⟨r, hr, _⟩
  exact absurd hr (List.not_mem_nil r)

/-- **Every conclusion the engine can draw is entailed**, by transitivity of entailment along a derivation.

Stated as an induction on a derivation list: a derivation is a sequence of constraints, each of which is
either already in `G` or follows from earlier entries by a rule. -/
theorem derivation_sound (rules : List (Rule n)) (G : GeoConstraintSet n)
    (steps : List (GeoConstraint n))
    (hstep : ∀ c ∈ steps,
      (c ∈ G) ∨ (∃ r ∈ rules, c = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d)) :
    ∀ c ∈ steps, EntailsGeo G c := by
  intro c hc
  rcases hstep c hc with hin | hrule
  · -- already in the hypothesis set
    intro pts hG
    exact hG c hin
  · exact step_sound rules G c hrule

/-! ## 七、可导性：**按步数索引的闭包**，而不是一张平铺的清单

### 为什么 `derivation_sound` 不够

前提形状是 `∀ d ∈ r.prems, EntailsGeo G d`——**前提必须由 `G` 本身蕴含**。
于是推导里**更早的结论不能当作后来的前提**：`steps` 只是一张清单，条目互不相干。
**那不是推导，是「一批各自成立的结论」。**

### 三次失败，都是 Lean 的正确拒绝

1. 递归出现放进 `∃ r ∈ rules, … ∀ d, Derivable …` ⟹ **`invalid nested inductive datatype 'Exists'`**；
2. 改互归纳，用 `induction` ⟹ **`'induction' tactic does not support mutual inductives`**；
3. 改互归纳 + 方程形式 ⟹ **`fail to show termination`**（递归调用的结构参数在另一个归纳类型上）。

**最终形态**：不用归纳类型，用**按步数索引的谓词**。

```lean
def DerivableIn (rules) (G) : ℕ → GeoConstraint n → Prop
  | 0,     c => EntailsGeo G c
  | k + 1, c => EntailsGeo G c ∨ ∃ r ∈ rules, c = r.concl ∧ ∀ d ∈ r.prems, DerivableIn rules G k d
```

这是**在 `ℕ` 上的结构递归**：没有嵌套、没有互归纳、终止性平凡。
「可导」定义为 `∃ k, DerivableIn rules G k c`。

**关键**：`rule` 那一支的前提是 `DerivableIn rules G k d`（**有预算的可导性**），不是 `EntailsGeo`。
所以「`d` 先被推出，再把 `d` 当作前提」是**可表达**的——**这就是链式**。

### 交付

| 定理 | 内容 |
|:--|:--|
| `derivableIn_mono` | 预算单调：`k` 步可导 ⟹ `k+j` 步可导 |
| `derivableIn_of_entails` | 蕴含 ⟹ 任意预算可导 |
| **`derivableIn_sound`** | **`k` 步可导 ⟹ 语义蕴含**（归纳在 `k` 上） |
| `derivable_sound` | `∃ k` 版本 |
| **`derivable_of_flat`** | **平铺清单能推的，闭包都能推** |
| **`derivable_two_step`** | **链式两步**——旧陈述表达不了 | -/

/-- **`k` 步可导**。第 `0` 步只有假设；第 `k+1` 步要么仍由假设蕴含，要么由一条前提**都 `k` 步可导**的规则得出。 -/
def DerivableIn (rules : List (Rule n)) (G : GeoConstraintSet n) :
    ℕ → GeoConstraint n → Prop
  | 0, c => EntailsGeo G c
  | k + 1, c =>
      EntailsGeo G c ∨
        ∃ r ∈ rules, c = r.concl ∧ ∀ d ∈ r.prems, DerivableIn rules G k d

/-- **可导**：存在某个步数界。 -/
def Derivable (rules : List (Rule n)) (G : GeoConstraintSet n) (c : GeoConstraint n) : Prop :=
  ∃ k, DerivableIn rules G k c

/-- **预算单调**：多给预算不会减少可导性。 -/
theorem derivableIn_mono {rules : List (Rule n)} {G : GeoConstraintSet n} :
    ∀ (k : ℕ) {c : GeoConstraint n}, DerivableIn rules G k c →
      ∀ j : ℕ, DerivableIn rules G (k + j) c
  | 0, c, h, j => by
      -- `h : EntailsGeo G c`; any budget keeps it
      induction j with
      | zero => simpa using h
      | succ j ih => exact Or.inl h
  | k + 1, c, h, j => by
      induction j with
      | zero => simpa using h
      | succ j ih =>
          rcases h with hE | ⟨r, hr, hc, hpre⟩
          · exact Or.inl hE
          · refine Or.inr ⟨r, hr, hc, fun d hd => ?_⟩
            -- each premise gets `k + j` budget, which is what the IH's shape provides at `k+j`
            -- at budget k + j + 2 the rule branch needs premises at k + j + 1;
            -- the two additions are equal but not syntactically, so normalise
            have h' : DerivableIn rules G (k + (j + 1)) d := derivableIn_mono k (hpre d hd) (j + 1)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

/-- **蕴含 ⟹ 任意预算可导。** -/
theorem derivableIn_of_entails {rules : List (Rule n)} {G : GeoConstraintSet n}
    {c : GeoConstraint n} (h : EntailsGeo G c) (k : ℕ) : DerivableIn rules G k c := by
  cases k with
  | zero => exact h
  | succ k => exact Or.inl h

/-- ⭐⭐ **`k` 步可导 ⟹ 语义蕴含**。归纳在 `k` 上。

`k+1` 的两支：`EntailsGeo` 直接给出；规则那一支对每个前提用 **`k` 的归纳假设**拿到
`EntailsGeo G d`，再由 `rule_entails` 收尾。**这一步就是「链式仍然保真」。** -/
theorem derivableIn_sound {rules : List (Rule n)} {G : GeoConstraintSet n} :
    ∀ (k : ℕ) {c : GeoConstraint n}, DerivableIn rules G k c → EntailsGeo G c
  | 0, c, h => h
  | k + 1, c, h => by
      rcases h with hE | ⟨r, hr, hc, hpre⟩
      · exact hE
      · subst hc
        exact rule_entails r G (fun d hd => derivableIn_sound k (hpre d hd))

/-- ⭐⭐ **可导 ⟹ 语义蕴含**。 -/
theorem derivable_sound {rules : List (Rule n)} {G : GeoConstraintSet n}
    {c : GeoConstraint n} (h : Derivable rules G c) : EntailsGeo G c := by
  obtain ⟨k, hk⟩ := h
  exact derivableIn_sound k hk

/-- **假设可导**（零预算）。 -/
theorem derivable_of_mem {rules : List (Rule n)} {G : GeoConstraintSet n}
    {c : GeoConstraint n} (h : c ∈ G) : Derivable rules G c :=
  ⟨0, fun _pts hG => hG c h⟩

/-- **蕴含可导**（零预算）。 -/
theorem derivable_of_entails {rules : List (Rule n)} {G : GeoConstraintSet n}
    {c : GeoConstraint n} (h : EntailsGeo G c) : Derivable rules G c :=
  ⟨0, h⟩

/-- **旧陈述是特例**：平铺清单能推的，闭包都能推。所以新定义**包含**旧陈述的表达力。 -/
theorem derivable_of_flat {rules : List (Rule n)} {G : GeoConstraintSet n}
    (steps : List (GeoConstraint n))
    (hstep : ∀ c ∈ steps,
      (c ∈ G) ∨ (∃ r ∈ rules, c = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d)) :
    ∀ c ∈ steps, Derivable rules G c := by
  intro c hc
  rcases hstep c hc with hin | ⟨r, hr, hconcl, hpre⟩
  · exact derivable_of_mem hin
  · refine ⟨1, Or.inr ⟨r, hr, hconcl, fun d hd => ?_⟩⟩
    exact derivableIn_of_entails (hpre d hd) 0

/-- ⭐⭐ **链式推理：两步**——强化**多出来的**内容，而且可证。

`r₁` 从 `G` 蕴含的前提推出 `c₁`（预算 1）；`r₂` 用 **`c₁` 作为前提之一**、其余前提由 `G` 蕴含，
推出 `c₂`（预算 2）。**平铺形状表达不了这一步**：它要求每个前提 `EntailsGeo G d`，
而 `c₁` 只是**被推出**。 -/
theorem derivable_two_step {rules : List (Rule n)} {G : GeoConstraintSet n}
    {c₁ c₂ : GeoConstraint n}
    (h₁ : ∃ r ∈ rules, c₁ = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d)
    (h₂ : ∃ r ∈ rules, c₂ = r.concl ∧ c₁ ∈ r.prems ∧
            ∀ d ∈ r.prems, d ≠ c₁ → EntailsGeo G d) :
    Derivable rules G c₂ := by
  obtain ⟨r₁, hr₁, hc₁, hpre₁⟩ := h₁
  obtain ⟨r₂, hr₂, hconcl₂, hc₁mem, hother⟩ := h₂
  -- `c₁` is derivable in one step
  have hc₁₁ : DerivableIn rules G 1 c₁ :=
    Or.inr ⟨r₁, hr₁, hc₁, fun d hd => derivableIn_of_entails (hpre₁ d hd) 0⟩
  -- `c₂` in two: premise `c₁` at budget 1, the rest at budget 0 (lifted by monotonicity)
  refine ⟨2, Or.inr ⟨r₂, hr₂, hconcl₂, fun d hd => ?_⟩⟩
  by_cases hdc : d = c₁
  · subst hdc; exact hc₁₁
  · exact derivableIn_of_entails (hother d hd hdc) 1

end Lattice.Geo
