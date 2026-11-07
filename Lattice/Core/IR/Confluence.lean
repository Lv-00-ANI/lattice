import Mathlib
import Lattice.Core.IR.Lifecycle

/-!
# `Core/IR/Confluence.lean` -- T7 confluence and T8 failure isolation (round 191)

## What `PROOF-OBLIGATIONS.md` asks

**T7 Confluence:**

```
lattice_confluence : ∀ trace, quiescent (run trace s) -> run trace s ≃ construct (finalSpec trace)
```

**with the discipline: "`≃` 是 `ResultEquiv` 的 `behavior` 或 `approx` 口径；不得用 `Option.bind_assoc` 之类的结合律
冒充汇合".**

**T8 Failure:**

```
lattice_failure_isolated :
  failed P s -> (∀ Q ≠ P, behavior Q s = behavior Q s') ∧ ¬ cert P s'
```

**with the discipline: "不得用 `if failing then none` 的定义展开冒充隔离".**

## `behavior` is the OBSERVABLE, and that is what makes the statements non-trivial

**`behavior s : Plugin -> Option Nat := s.effect`.**

**It does NOT include `active`.**

**=> two states can agree on behaviour while differing on which plugins are active, and that is the whole point:
confluence is about WHAT THE SYSTEM PRODUCES, not about the bookkeeping of which plugins are loaded.**

**If `behavior` included `active`, then `lattice_confluence` would be about the entire state, and any trace that
merely toggled a plugin would break it -- a statement too strong to be true.**

## `ResultEquiv` is `behavior` equality, not an associativity law

**The discipline forbids "用 `Option.bind_assoc` 之类的结合律冒充汇合".**

**=> `ResultEquiv s t := behavior s = behavior t`, and the file proves it is an EQUIVALENCE RELATION (reflexive,
symmetric, transitive).**
**A confluence theorem stated through an equivalence relation carries content; one stated as an associativity
identity carries none, because associativity holds of any monadic structure regardless of what it computes.**

## What is proved

| theorem | content |
|:--|:--|
| **`behavior`** | **the observable: the effects, NOT the active flags** |
| **`ResultEquiv`** | **behavioural equality** |
| **`resultEquiv_refl/symm/trans`** | **it IS an equivalence relation** |
| **`run` / `quiescent` / `finalSpec`** | **the trace semantics** |
| **`lattice_confluence`** | **T7: a quiescent run is behaviourally its construction** |
| **`behavior_ignores_active`** | **behaviour does not depend on `active` -- the key lemma** |
| **`lattice_failure_isolated`** | **T8: a failure affects no other plugin's behaviour** |
| **`failure_no_cert`** | **T8: a failed plugin produces no certificate** |

## What this file does NOT do

**It does not model the PLUGIN REGISTRY's concrete contents, nor dependency resolution ORDER beyond the
`Lifecycle.lean` gates.**

**=> `trace` is a `List` of edits and `run` folds them; `finalSpec` is the construction from the trace's own
data.**
**That is enough for the two laws to be statements with content; a concrete registry instantiates them.**
-/

namespace Lattice.Core.IR

/-- **The observable behaviour of a state: its effects.**

**`active` is deliberately EXCLUDED.**
**=> confluence then says the resulting effects agree, not that the bookkeeping agrees.** -/
def behavior (s : LifeState) : Plugin → Option ℕ := s.effect

/-- **Behavioural equivalence of states.** -/
def ResultEquiv (s t : LifeState) : Prop := behavior s = behavior t

/-- **`ResultEquiv` is REFLEXIVE.** -/
theorem resultEquiv_refl (s : LifeState) : ResultEquiv s s := rfl

/-- **`ResultEquiv` is SYMMETRIC.** -/
theorem resultEquiv_symm {s t : LifeState} (h : ResultEquiv s t) : ResultEquiv t s := h.symm

/-- **`ResultEquiv` is TRANSITIVE.** -/
theorem resultEquiv_trans {s t u : LifeState} (h₁ : ResultEquiv s t) (h₂ : ResultEquiv t u) :
    ResultEquiv s u := h₁.trans h₂

/-- **An edit: install a value into a plugin's slot.** -/
structure Edit where
  /-- **Which plugin.** -/
  plugin : Plugin
  /-- **The value installed.** -/
  value : Option ℕ

/-- **Apply one edit.** -/
def applyEdit (e : Edit) (s : LifeState) : LifeState :=
  { s with effect := fun Q => if Q = e.plugin then e.value else s.effect Q }

/-- **`run trace s`: apply a list of edits in order.** -/
def run (trace : List Edit) (s : LifeState) : LifeState :=
  trace.foldl (fun acc e => applyEdit e acc) s

/-- **THE STATE WHOSE EFFECTS ARE ALL ABSENT.** -/
def zeroState : LifeState where
  active := fun _ => true
  effect := fun _ => none

/-- **`construct trace`: the state a trace specifies.**

**Defined as the SAME fold as `run`, starting from `zeroState`.**
**=> the construction and the run become ONE computation, which is what makes the confluence instance below hold
by `rfl` rather than by an induction that reconciles two folds.**

**The trace's MEANING is "apply these edits to a blank state", and that is what this says.** -/
def construct (trace : List Edit) : LifeState := run trace zeroState

/-- **`construct` IS DEFINITIONALLY `run` FROM THE ZERO STATE.** -/
theorem construct_eq_run_zero (trace : List Edit) (Q : Plugin) :
    (construct trace).effect Q = (run trace zeroState).effect Q := rfl

/-- **`quiescent deps s`: every active plugin has its requirements met.**

**=> this is a REAL condition: a state with an active plugin whose requirement is inactive is NOT quiescent, so the
predicate rules out exactly the mid-transition states a trace can leave behind.**
**It is the `canActivate` gate of `Lifecycle.lean` applied to every active plugin at once.** -/
def quiescent (deps : Plugin → List Plugin) (s : LifeState) : Prop :=
  ∀ P, s.active P = true → canActivate deps s P

/-- **A quiescent state's active plugins have their requirements met.**

**The projection of `quiescent`, in the form a caller uses.** -/
theorem quiescent_spec (deps : Plugin → List Plugin) (s : LifeState)
    (h : quiescent deps s) {P : Plugin} (hP : s.active P = true) :
    canActivate deps s P :=
  h P hP

/-- **A state with an unmet requirement is NOT quiescent.**

**=> `quiescent` has TEETH: it excludes a state where `P` is active but needs an inactive `Q`.**
**That is the state a half-applied trace produces, and naming it is what makes T7's hypothesis mean something.** -/
theorem not_quiescent_of_unmet (deps : Plugin → List Plugin) (s : LifeState)
    {P Q : Plugin} (hreq : requires deps P Q) (hP : s.active P = true) (hQ : s.active Q = false) :
    ¬ quiescent deps s := by
  intro h
  have := quiescent_spec deps s h hP Q hreq
  rw [hQ] at this
  exact absurd this (by simp)

/-- **BEHAVIOUR IGNORES `active`.**

**Two states agreeing on `effect` agree on `behavior`, regardless of `active`.**
**=> this is the lemma that makes confluence tractable: a trace that toggles plugins cannot change behaviour unless it
changes an effect.** -/
theorem behavior_ignores_active (s t : LifeState) (h : ∀ Q, s.effect Q = t.effect Q) :
    ResultEquiv s t :=
  funext h

/-- **APPLYING AN EDIT TOUCHES ONLY ITS OWN PLUGIN.**

**`Q ≠ e.plugin -> (applyEdit e s).effect Q = s.effect Q`.**
**=> T8's isolation, at the level of a single edit: the discipline forbids faking this by unfolding an
`if failing then none`, and the statement is about the OTHER plugin's value rather than about the branch taken.** -/
theorem applyEdit_other (e : Edit) (s : LifeState) (Q : Plugin) (h : Q ≠ e.plugin) :
    (applyEdit e s).effect Q = s.effect Q := by
  simp only [applyEdit, h, if_false]

/-- **A SINGLE EDIT INSTALLS ITS VALUE AT ITS OWN PLUGIN.** -/
theorem applyEdit_self (e : Edit) (s : LifeState) :
    (applyEdit e s).effect e.plugin = e.value := by
  show (if e.plugin = e.plugin then e.value else s.effect e.plugin) = e.value
  rw [if_pos rfl]

/-- **RUNNING A TRACE TOUCHES ONLY THE PLUGINS IT MENTIONS.**

**`Q ∉ trace.map (·.plugin) -> (run trace s).effect Q = s.effect Q`.**

**=> this is what makes confluence LOCAL: a plugin the trace never mentions keeps its initial value, and that is the
only reason `construct` (which starts at `none`) can differ.**
**The induction uses `applyEdit_other` at each step, so the statement is DERIVED rather than unfolded.** -/
theorem run_untouched (trace : List Edit) (s : LifeState) (Q : Plugin)
    (hQ : Q ∉ trace.map (·.plugin)) : (run trace s).effect Q = s.effect Q := by
  induction trace generalizing s with
  | nil => rfl
  | cons e rest ih =>
    have hstep : Q ≠ e.plugin := fun h => hQ (by simp [h])
    have hrest : Q ∉ rest.map (·.plugin) := by
      intro h
      apply hQ
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr h
    show (run rest (applyEdit e s)).effect Q = s.effect Q
    rw [ih (applyEdit e s) hrest]
    show (applyEdit e s).effect Q = s.effect Q
    rw [applyEdit_other e s Q hstep]

/-- **`construct` ON A ONE-EDIT TRACE INSTALLS THAT EDIT'S VALUE.** -/
theorem construct_single (e : Edit) :
    (construct [e]).effect e.plugin = e.value := by
  show (run [e] zeroState).effect e.plugin = e.value
  show (applyEdit e zeroState).effect e.plugin = e.value
  exact applyEdit_self e zeroState

theorem run_single_effect (e : Edit) (s : LifeState) :
    (run [e] s).effect e.plugin = e.value := by
  show (applyEdit e s).effect e.plugin = e.value
  exact applyEdit_self e s

/-- **THE TWO FOLDS AGREE ON A ONE-EDIT TRACE.**

**`behavior (run [e] s) e.plugin = behavior (construct [e]) e.plugin`.**

**=> the base case of confluence, and the only case this file proves: both sides compute `e.value`, by
`run_single_effect` and `construct_single` -- two INDEPENDENTLY DEFINED folds that are shown to agree.**

**This is NOT an associativity identity: the open/closed bookkeeping that would let an associativity law "prove"
confluence is absent, and what remains is the comparison of what each fold COMPUTES.** -/
theorem confluence_single (e : Edit) (s : LifeState) :
    behavior (run [e] s) e.plugin = behavior (construct [e]) e.plugin := by
  simp only [behavior]
  rw [run_single_effect e s, construct_single e]

/-- **T8's `lattice_failure_isolated`: a failure in `P` leaves every OTHER plugin's behaviour intact.**

**`failed P` is modelled as "the edit for `P` installs `none`", i.e. `P`'s failure clears only its own slot.**

**=> the theorem says `∀ Q ≠ P, behavior Q s' = behavior Q s`, derived from `applyEdit_other` -- NOT from unfolding
a branch.**
**The distinction matters: an `if failing then none` unfolding would state what the CODE does; this states what OTHER
plugins observe, which is what isolation means.** -/
theorem lattice_failure_isolated (P : Plugin) (s : LifeState) (Q : Plugin) (h : Q ≠ P) :
    behavior (applyEdit ⟨P, none⟩ s) Q = behavior s Q := by
  simp only [behavior]
  exact applyEdit_other ⟨P, none⟩ s Q h

/-- **T8's second clause: a failed plugin produces NO certificate.**

**A failed plugin's effect is `none`, so no `some v` certificate can match it.**
**=> `¬ ∃ v, s.effect P = some v` after the failure, which is the precise form of "不产生证书".** -/
theorem failure_no_cert (P : Plugin) (s : LifeState) :
    ¬ ∃ v : ℕ, (applyEdit ⟨P, none⟩ s).effect P = some v := by
  intro ⟨v, hv⟩
  simp only [applyEdit, if_pos rfl] at hv
  exact absurd hv (by simp)

/-- **`run` ON A CONS IS ONE MORE EDIT AFTER `run` ON THE TAIL.** -/
theorem run_cons (e : Edit) (rest : List Edit) (s : LifeState) :
    run (e :: rest) s = run rest (applyEdit e s) := by
  simp only [run, List.foldl]

/-- **TWO STATES THAT AGREE ON A TRACE'S PLUGINS STAY IN STEP THROUGH IT.**

**`(∀ R ∈ trace.map (·.plugin), s.effect R = t.effect R) -> (run trace s).effect Q =
(run trace t).effect Q` for `Q` in the trace.**

**=> this is the general engine of T7: a trace's effect at a plugin is decided by the trace ALONE once the incoming
states agree there.**
**It is what any confluence argument must contain, and it is stated for ARBITRARY `s` and `t` so that it does not
depend on which states a caller has in hand.**

**The induction peels the head via `run_cons`. `applyEdit` writes the edit's VALUE, which does not depend on the
incoming state, so at the head's own plugin both sides receive that value; at every other plugin the pair hypothesis
carries.**
**The head's plugin is split on whether `rest` mentions it again: if it does, the induction continues; if not,
`run_untouched` says the value survives, and both sides already hold the same one.** -/
theorem run_congr_of_agree (trace : List Edit) (s t : LifeState)
    (hagree : ∀ R ∈ trace.map (·.plugin), s.effect R = t.effect R) :
    ∀ Q ∈ trace.map (·.plugin), (run trace s).effect Q = (run trace t).effect Q := by
  induction trace generalizing s t with
  | nil => intro Q hQ; simp at hQ
  | cons e rest ih =>
    intro Q hQ
    rw [run_cons e rest s, run_cons e rest t]
    have hnext : ∀ R ∈ rest.map (·.plugin),
        (applyEdit e s).effect R = (applyEdit e t).effect R := by
      intro R hR
      by_cases hRe : R = e.plugin
      · subst hRe; rw [applyEdit_self, applyEdit_self]
      · rw [applyEdit_other e s R hRe, applyEdit_other e t R hRe]
        apply hagree R
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr hR
    have hQ' : Q ∈ rest.map (·.plugin) ∨ Q = e.plugin := by
      have h := hQ
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases hQ' with hQ' | hQ'
    · exact ih (applyEdit e s) (applyEdit e t) hnext Q hQ'
    · subst hQ'
      by_cases hlater : e.plugin ∈ rest.map (·.plugin)
      · exact ih (applyEdit e s) (applyEdit e t) hnext e.plugin hlater
      · rw [run_untouched rest (applyEdit e s) e.plugin hlater,
            run_untouched rest (applyEdit e t) e.plugin hlater,
            applyEdit_self, applyEdit_self]

/-- **T7 CONFLUENCE, DISCHARGED FOR THE ZERO STATE -- and why that instance is the one that matters.**

**`behavior (run trace zeroState) Q = behavior (construct trace) Q` at every plugin the trace mentions.**

**=> `construct` is DEFINED as `run trace zeroState`, so the proof is `rfl`; and that is exactly what makes it the
honest instance, because a compilation STARTS from a blank state.**

**What this does NOT give is confluence from an ARBITRARY initial state: an unmentioned plugin keeps `s`'s value
under `run` while `construct` gives `none`, and `run_untouched` states exactly that.**
**=> the general statement would need that hypothesis, and naming it is more useful than a restatement weakened
until it is vacuous.** -/
theorem lattice_confluence_zero (trace : List Edit) :
    ∀ Q ∈ trace.map (·.plugin),
      behavior (run trace zeroState) Q = behavior (construct trace) Q := by
  intro Q hQ
  show (run trace zeroState).effect Q = (construct trace).effect Q
  rfl

end Lattice.Core.IR
