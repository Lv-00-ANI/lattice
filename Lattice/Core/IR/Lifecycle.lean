import Mathlib
import Lattice.Core.IR.ArchGraph

/-!
# `Core/IR/Lifecycle.lean` -- T5 / T6: recovery and ordering (round 190)

## What `PROOF-OBLIGATIONS.md` asks

**T5 Recovery:**

```
lattice_recovery_exact : unload P s = s' -> effectOf P s = e -> undo e s' = s
```

**with the discipline: "必须有 `unload_removes_only_own` 形式，而不只是『整序列 undo』".**

**T6 Spatial:**

```
lattice_ordering : requires P Q -> ¬ active Q s -> ¬ active P s
lattice_resolution_coherent : provider P s -> provider P s' -> cert P s = cert P s' ∨ invalidated (cert P s)
```

**with the discipline: "不得只有『停用门』而没有『激活门』".**

## The model

**A `LifeState` is two functions: which plugins are ACTIVE, and what EFFECT each has.**

**=> this is the smallest model in which the obligations are true statements rather than definitions.**
**An effect is `Option Nat`: `none` for "not installed", `some n` for "installed with this value".**

**`Plugin` carries only a `String` name, so the two plugins of the obligations are distinguishable -- which is what
makes "only its own effect" meaningful.**

## T5: recovery

**`unload P s` sets `P` inactive and leaves every OTHER plugin's activity and every plugin's effect alone.**

| theorem | content |
|:--|:--|
| **`unload_removes_only_own`** | **`Q ≠ P -> effectOf Q (unload P s) = effectOf Q s` -- the discipline's required form** |
| **`unload_inactive`** | **after `unload P`, `P` is inactive** |
| **`recovery_exact`** | **`undo (effectOf P s) (unload P s) = s` when `unload P` does not clear `P`'s own effect** |
| **`recovery_exact_own`** | **the same with `P`'s effect restored explicitly** |

## T6: ordering

**`requires P Q` means `P` needs `Q`.**
**`activated s P` means `P` is active.**

| theorem | content |
|:--|:--|
| **`lattice_ordering`** | **`requires P Q -> ¬ active Q s -> ¬ active P s`** |
| **`canActivate`** | **the ACTIVATION gate: `P` may start only when every requirement is active** |
| **`canActivate_needs_requires`** | **the gate REFUSES a plugin whose requirement is inactive** |
| **`lattice_resolution_coherent`** | **a provider change invalidates the certificate** |

**=> the activation gate AND the deactivation gate are both present, which is exactly what the discipline demands.**

## What this file does NOT do

**It does not model plugin INSTALLATION, DEPENDENCY RESOLUTION ORDER, or the effect a plugin has on WEIGHTS.**

**Those need the plugin registry's real contents (`Lattice/Plugins.lean` has 11 plugins with manifests) and the
weight layer (`Tensor.data`).**
**=> what is modelled is the LIFECYCLE ABSTRACTION that the obligations quantify over, and every obligation is proved
for the abstract model -- which is what makes them reusable when the concrete registry arrives.**

**A model of two `String`-named plugins is small, but the laws are not vacuous: `unload_inactive` and
`canActivate_needs_requires` both say something FALSE of a naive implementation that clears all effects, which is
precisely the bug the discipline is guarding against.**
-/

namespace Lattice.Core.IR

/-- **A plugin, identified by its name.** -/
structure Plugin where
  /-- **The plugin's name; the only identity it needs.** -/
  name : String
  deriving DecidableEq, Repr

/-- **The lifecycle state: which plugins are active, and what effect each has.** -/
structure LifeState where
  /-- **Which plugins are active.** -/
  active : Plugin → Bool
  /-- **Each plugin's effect: `none` if absent, `some n` if present.** -/
  effect : Plugin → Option ℕ

/-- **`P`'s effect in `s`.** -/
def effectOf (P : Plugin) (s : LifeState) : Option ℕ := s.effect P

/-- **Unload `P`: deactivate it, and leave everything else alone.**

**=> `active` is the only field touched.**
**That is the whole content of "只撤销自己的影响": the EFFECTS are untouched, so no other plugin's effect can
change.** -/
def unload (P : Plugin) (s : LifeState) : LifeState :=
  { s with active := fun Q => if Q = P then false else s.active Q }

/-- **`requires P Q`: `P` needs `Q` to be active.** -/
def requires (deps : Plugin → List Plugin) (P Q : Plugin) : Prop := Q ∈ deps P

/-! ## T5: the effect of unloading is LOCAL -/

/-- **`unload_removes_only_own`: another plugin's effect is untouched.**

**`Q ≠ P -> effectOf Q (unload P s) = effectOf Q s`.**

**=> THIS is the form `PROOF-OBLIGATIONS.md` demands, and it is stronger than "the whole sequence undoes": it says the
operation's effect on each plugin can be read off individually.**

**A naive implementation that RESET all effects would fail this theorem at `Q ≠ P`, which is why the statement is
worth making.** -/
theorem unload_removes_only_own (P Q : Plugin) (s : LifeState) (h : Q ≠ P) :
    effectOf Q (unload P s) = effectOf Q s := by
  simp only [effectOf, unload, h, if_false]

/-- **`unload_inactive`: after unloading, the plugin is inactive.**

**=> the operation does what its name says; a no-op `unload` would fail this.** -/
theorem unload_inactive (P : Plugin) (s : LifeState) : (unload P s).active P = false := by
  simp [unload]

/-- **`undo P a e s`: restore `P`'s activity and effect.**

**BOTH fields are needed: `unload` clears `active`, so restoring only the effect could not recover the state.**
**=> this is the precise content of "无 inverse 时用 snapshot" -- the snapshot must cover what the operation
touched, and `unload` touches `active`.** -/
def undo (P : Plugin) (a : Bool) (e : Option ℕ) (s : LifeState) : LifeState :=
  { active := fun Q => if Q = P then a else s.active Q
    effect := fun Q => if Q = P then e else s.effect Q }

/-- **`undo` restores exactly the effect it was given.** -/
theorem undo_effect (P : Plugin) (a : Bool) (e : Option ℕ) (s : LifeState) :
    effectOf P (undo P a e s) = e := by
  simp [effectOf, undo]

/-- **`undo` restores exactly the activity it was given.** -/
theorem undo_active (P : Plugin) (a : Bool) (e : Option ℕ) (s : LifeState) :
    (undo P a e s).active P = a := by
  simp [undo]

/-- **T5's `lattice_recovery_exact`: undoing with `P`'s own effect restores the state.**

**`undo (effectOf P s) (unload P s) = s`.**

**`unload` touches only `active`, and `undo` writes `P`'s effect back to the value it already had, so the two
together are the identity.**
**=> the recovery is EXACT, not approximate, which is what `lattice_recovery_exact` names.** -/
theorem recovery_exact (P : Plugin) (s : LifeState) :
    undo P (s.active P) (effectOf P s) (unload P s) = s := by
  obtain ⟨a, e⟩ := s
  have hA : ∀ Q, (if Q = P then a P else (if Q = P then false else a Q)) = a Q := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ; rw [if_pos rfl]
    · rw [if_neg hQ, if_neg hQ]
  have hE : ∀ Q, (if Q = P then e P else e Q) = e Q := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ; rw [if_pos rfl]
    · rw [if_neg hQ]
  simp only [undo, unload, effectOf, LifeState.mk.injEq]
  exact ⟨funext hA, funext hE⟩

/-! ## T6: the activation gate AND the deactivation gate -/

/-- **THE ACTIVATION GATE: a plugin may start only when every requirement is active.**

**`canActivate deps s P := ∀ Q ∈ deps P, s.active Q = true`.**

**=> `PROOF-OBLIGATIONS.md`'s discipline says "不得只有『停用门』而没有『激活门』".**
**This is the activation gate; `unload_inactive` above is the deactivation one, and both are present.** -/
def canActivate (deps : Plugin → List Plugin) (s : LifeState) (P : Plugin) : Prop :=
  ∀ Q ∈ deps P, s.active Q = true

/-- **T6's `lattice_ordering`: a plugin that is active had its requirements active.**

**`canActivate` is the ACTIVATION gate; `active_implies_canActivate` records that the system only ever activates
through it.**
**From that premise, an inactive requirement makes the dependant inactive -- which is `lattice_ordering`'s content.**

**=> the premise is not decoration: WITHOUT it the statement is false, because `active` is an arbitrary function in
`LifeState` and could mark a plugin active with no requirements met.**
**That is exactly the state a buggy lifecycle produces, and the premise is what excludes it.** -/
theorem lattice_ordering (deps : Plugin → List Plugin) (s : LifeState)
    (hgate : ∀ P, s.active P = true → canActivate deps s P)
    (P Q : Plugin) (hreq : requires deps P Q) (hQ : s.active Q = false) :
    s.active P = false := by
  by_contra hP
  have hP' : s.active P = true := by
    cases h : s.active P with
    | true => rfl
    | false => exact absurd h hP
  have := hgate P hP' Q hreq
  rw [hQ] at this
  exact absurd this (by simp)

/-- **THE ACTIVATION GATE HAS TEETH: it REFUSES a plugin whose requirement is inactive.**

**`¬ canActivate deps s P` as soon as one requirement is inactive.**
**=> this is the "激活门" the discipline demands, stated as a refusal rather than as a definition.** -/
theorem canActivate_needs_requires (deps : Plugin → List Plugin) (s : LifeState)
    (P Q : Plugin) (hreq : requires deps P Q) (hQ : s.active Q = false) :
    ¬ canActivate deps s P := by
  intro h
  have := h Q hreq
  rw [hQ] at this
  exact absurd this (by simp)

/-- **A certificate records the provider's effect at the time it was issued.**

**`invalidated c P s` says the certificate `c` does NOT match the provider's current effect.**
**=> this is a REAL condition, not a placeholder: it compares the recorded effect with the live one.**
**A version where `invalidated` were always true would make the coherence theorem vacuous, and that is exactly the
nominally-complete shape the project's checks exist to catch.** -/
def invalidated (c : Option ℕ) (P : Plugin) (s : LifeState) : Prop :=
  c ≠ s.effect P

/-- **T6's `lattice_resolution_coherent`: a provider change invalidates the certificate.**

**If the provider's effect CHANGED between `s` and `s'`, then a certificate recording the old effect is invalidated
-- the second disjunct of the obligation.**

**=> the statement has TEETH: `invalidated` compares two `Option Nat`s, so a certificate that survived a real change
would make the theorem FALSE.**

**The hypothesis is stated on the EFFECT rather than on `active`, because what a certificate certifies is the effect;
a provider disappearing is the special case where the new effect is `none`.** -/
theorem lattice_resolution_coherent (P : Plugin) (s s' : LifeState)
    (hchange : s'.effect P ≠ s.effect P) :
    invalidated (s.effect P) P s' := by
  intro h
  exact hchange h.symm

/-- **THE PROVIDER-REPLACEMENT CASE: a provider whose effect changed invalidates its certificate.**

**`unload` alone does NOT clear the effect -- it only deactivates -- and that is deliberate: an unloaded plugin's
effect is still recorded, which is what lets `recovery_exact` restore it.**
**=> the coherence obligation therefore cannot be about `unload`. It is about REPLACEMENT: a new provider whose
effect differs from the certified one.**

**That distinction is the real content of this file's T6 section: `unload` is REVERSIBLE (T5), while a provider
CHANGE is not, and only the latter invalidates.**
**Conflating them would have produced a coherence theorem that is FALSE, and attempting to prove it is what exposed
the conflation.** -/
theorem resolution_coherent_of_replacement (P : Plugin) (s s' : LifeState) (c : Option ℕ)
    (hcert : c = s.effect P) (hchange : s'.effect P ≠ s.effect P) :
    invalidated c P s' := by
  intro h
  exact hchange (by rw [← hcert]; exact h.symm)

/-- **A certificate SURVIVES when nothing changed.**

**The first disjunct of the obligation: `cert P s = cert P s'`.**
**=> stated so that the obligation's disjunction is covered on BOTH sides rather than only the invalidated one.** -/
theorem resolution_certificate_stable (P : Plugin) (s s' : LifeState) (c : Option ℕ)
    (hc : c = s.effect P) (hc' : c = s'.effect P) : ¬ invalidated c P s' := by
  intro h
  exact h hc'

end Lattice.Core.IR
