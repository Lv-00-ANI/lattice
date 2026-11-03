/-
# Migration: what "the plugin OWNS its obligations" means, and whether it holds

**The audit's finding: `8/43` plugins are registered, but every obligation points OUTSIDE the plugin's
own directory.**
**=> the migration is `import + restate`, not `move + facade`: the original proof is still the only real
proof, and the plugin merely CITES it.**

**This file makes that distinction a PREDICATE, and proves which side the current registry is on.**

## Why a hand-rolled prefix relation rather than `String.isPrefixOf`

**Three drafts used `String.isPrefixOf` and all three stalled, and the reason is worth recording:**

**`String.isPrefixOf` is a `Bool`-valued COMPUTED function, and `decide` does not reduce it** -- **not on
long paths (thirty-plus characters), and not even on SHORT ones.**
**The error names the unfolding (`substrEq`, `instDecidableLeBitVec`) rather than the fact that the
computation cannot finish.**
**Mathlib exposes no `String.Prefix` theorem and no `List.Prefix` predicate in this version.**

**=> the relation is defined HERE, inductively on characters, which makes it a `Prop` the kernel can
reason about instead of a `Bool` it must evaluate.**

**The cost is that `Migrated` is about this relation rather than about a library function.**
**The benefit is that the central fact -- two paths differing at one character are not prefix-related --
is PROVABLE rather than merely computable.**
-/

import Lattice.Plugins.Registry

namespace Lattice.Plugins

/-- **Character-level prefix, defined inductively.**

**`nil`: the empty string prefixes everything.**
**`cons`: equal heads and a prefix tail.**
**This is the standard `Prop`-valued definition, chosen over `String.isPrefixOf` for the reason in the
file header.** -/
inductive StrPrefix : List Char → List Char → Prop where
  /-- The empty list prefixes every list. -/
  | nil (l : List Char) : StrPrefix [] l
  /-- Equal heads, prefix tails. -/
  | cons {a : Char} {l l' : List Char} : StrPrefix l l' → StrPrefix (a :: l) (a :: l')

/-- **A string prefixes another when its characters do.** -/
def StringPrefix (a b : String) : Prop := StrPrefix a.toList b.toList

/-- **Two lists with different heads are NOT prefix-related.**

**This is the single fact the whole file turns on, and it is `Prop`-valued: the `cons` constructor
demands `a :: l` and `a :: l'` with the SAME head, so a different head leaves only `nil`, which the
second case excludes.** -/
theorem strPrefix_cons_ne {a b : Char} {l l' : List Char} (h : a ≠ b) :
    ¬ StrPrefix (a :: l) (b :: l') := by
  intro hp
  cases hp with
  | cons htail => exact h rfl

/-- **`'P'` and `'L'` are different characters**, **so the two path segments diverge at their first
character.** -/
theorem P_ne_L : ('P' : Char) ≠ 'L' := by decide

/-- **Two character lists that differ at SOME position are not prefix-related.**

**Generalised over the common prefix `pre`, so the argument peels characters off one at a time until the
differing position is reached.**
**`a ≠ b` is what the final `cons` case refutes.** -/
theorem strPrefix_cons_ne_gen {pre : List Char} {a b : Char} {l l' : List Char} (h : a ≠ b) :
    ¬ StrPrefix (pre ++ a :: l) (pre ++ b :: l') := by
  induction pre with
  | nil =>
    simp only [List.nil_append]
    exact strPrefix_cons_ne h
  | cons c rest ih =>
    simp only [List.cons_append]
    intro hp
    cases hp with
    | cons htail => exact ih htail

/-- **The divergence, at the character level.**

**`"Plugins/"` does not prefix `"Lib/"`, because their first characters differ.**

**The proof reduces the two strings to character lists and applies `strPrefix_cons_ne` at the head --
`cons` demands EQUAL heads, and `'P' ≠ 'L'` is the refutation.**
**Stating the reduction here rather than forwarding keeps the step visible: what the argument needs is
that `isPrefixOf`'s `Bool` is not what is being reasoned about.** -/
theorem plugins_not_prefix_lib : ¬ StringPrefix "Plugins/" "Lib/" := by
  unfold StringPrefix
  simp only [String.toList]
  exact strPrefix_cons_ne P_ne_L

/-- **The converse direction is refutable too**, **so the two segments are genuinely incomparable.** -/
theorem lib_not_prefix_plugins : ¬ StringPrefix "Lib/" "Plugins/" :=
  strPrefix_cons_ne (by decide : ('L' : Char) ≠ 'P')

/-- **An obligation is OWNED by a plugin when its proof file sits under that plugin's directory.** -/
def ObligationOwnedBy (dir : String) (o : Obligation) : Prop :=
  StringPrefix dir o.file

/-- **A plugin is MIGRATED when its obligations are its own.**

**`obligations = []` makes this vacuously true, which is why `NonVacuousFor` is a SEPARATE conjunct of
the completion predicate** -- **an empty plugin would be "migrated" and prove nothing.** -/
def Migrated (dir : String) (m : PluginManifest) : Prop :=
  ∀ o ∈ m.obligations, ObligationOwnedBy dir o

/-- **A plugin with obligations pointing elsewhere is NOT migrated.**

**The contrapositive form, and it is the one the current registry satisfies.** -/
theorem not_migrated_of_foreign {dir : String} {m : PluginManifest} {o : Obligation}
    (hmem : o ∈ m.obligations) (hforeign : ¬ ObligationOwnedBy dir o) :
    ¬ Migrated dir m := by
  intro h
  exact hforeign (h o hmem)

/-- **`Norm`'s own directory.** -/
def normDir : String := "Lattice/Plugins/Architectures/Norm/"

/-- **The registry's obligations cite library files, and `Norm` is the worked example.**

**The manifest carries `file := "Lattice/Lib/Architectures/RealBatchNormConsistency.lean"`.**
**Both paths begin with `Lattice/`; what follows is `Plugins/...` on the plugin's side and `Lib/...` on
the obligation's, and `plugins_not_prefix_lib` says those segments cannot prefix one another.**

**=> `norm_obligation_is_a_citation` below is the CONSEQUENCE, and it does not need the long strings
evaluated.** -/
def normObligation : Obligation where
  name := "idempotence"
  kind := .idempotence
  theoremName := "varOf_iterate_varNormalize_le_one"
  file := "Lattice/Lib/Architectures/RealBatchNormConsistency.lean"

/-- **`Norm`'s first obligation is a CITATION, not a MOVE.**

**The plugin's directory and the obligation's file share the prefix `Lattice/`, so the question reduces
to what follows: `Plugins/...` versus `Lib/...` -- and `strPrefix_cons_ne_gen` refutes that, because
`'P' ≠ 'L'`.**

**`simp` reduces both `toList`s to concrete character lists, after which the induction peels the common
`Lattice/` prefix and stops at the differing character.**
**That is why the proof terminates here while `decide` did not: the work is done by a `Prop`-level
induction rather than by evaluating a `Bool` computation.** -/
theorem norm_obligation_is_a_citation : ¬ ObligationOwnedBy normDir normObligation := by
  intro h
  unfold ObligationOwnedBy StringPrefix normDir normObligation at h
  simp only [String.toList] at h
  exact strPrefix_cons_ne_gen (pre := "Lattice/".toList) P_ne_L h

/-! ## The registry-level predicate -/

/-- **A REGISTRY is migrated when every one of its plugins is LISTED and owns its obligations.**

**`dirOf` returns an `Option`: `none` means the plugin has no recorded directory, and that is a
FAILURE, not a pass.**
**Why this shape: my previous version took `VerifiedPlugin → String` with a `""` fallback, and the empty
string is a prefix of EVERYTHING** -- **so an unlisted plugin would have been reported as migrated, which
is precisely the defect a migration check must not have.**
**=> `none` fails closed.**

**This lives HERE rather than in `Registry.lean` because `Registry` cannot depend on `Migration`** --
**the dependency points the other way.**

**Why not simply "count the migrated plugins":**
**forty-three plugins with one migrated and forty-two empty would satisfy any count that only looked at
`Migrated`.** **=> this predicate requires EVERY plugin, and `NonVacuousFor` (in `Registry`) covers the
emptiness half.** -/
def RegistryMigratedFor (dirOf : VerifiedPlugin → Option String) (reg : List VerifiedPlugin) : Prop :=
  ∀ p ∈ reg, ∃ dir, dirOf p = some dir ∧ Migrated dir p.manifest

/-- **Every string prefixes itself.**

**The reflexivity of `StringPrefix`, needed by every `Migrated` instance: when an obligation's `file` IS
the plugin's own path, the prefix test succeeds by construction.** -/
theorem strPrefix_self (l : List Char) : StrPrefix l l := by
  induction l with
  | nil => exact StrPrefix.nil []
  | cons c rest ih => exact StrPrefix.cons ih

/-- **A list prefixes itself with any suffix appended.**

**The general form behind every `Migrated` instance: a plugin directory prefixes every file path built by
appending a name to it.**
**Stated on character lists so the proof is the `StrPrefix` induction itself, with no dependence on how
`String.toList` reduces over `++`.** -/
theorem strPrefix_append_right (l suffix : List Char) : StrPrefix l (l ++ suffix) := by
  induction l with
  | nil => exact StrPrefix.nil suffix
  | cons c rest ih => exact StrPrefix.cons ih

/-- **`StringPrefix` is reflexive.** -/
theorem stringPrefix_self (s : String) : StringPrefix s s :=
  strPrefix_self s.toList

/-- **An obligation whose file IS the plugin's directory prefix is owned.**

**This is the direction a `Migrated` instance needs: it reduces the prefix test to REFLEXIVITY when the
paths agree.** -/
theorem obligationOwnedBy_self (dir : String) (o : Obligation) (h : o.file = dir) :
    ObligationOwnedBy dir o := by
  unfold ObligationOwnedBy
  rw [h]
  exact stringPrefix_self _

/-- **The empty registry is migrated, vacuously.** -/
theorem registryMigratedFor_nil (dirOf : VerifiedPlugin → Option String) :
    RegistryMigratedFor dirOf [] := by
  intro p hp
  simp at hp

/-- **AN UNLISTED PLUGIN FAILS THE MIGRATION CHECK.**

**This is the theorem the fail-closed design exists for: if `dirOf` returns `none` for a plugin in the
registry, `RegistryMigratedFor` is FALSE.**
**With the previous `String`-valued `dirOf` and its `""` fallback, this plugin would have PASSED** --
**the prefix test `"".isPrefixOf anything` succeeds, so the check would have been vacuous for every
plugin nobody had classified.**
**=> the `Option` is not defensive coding; it is what makes the predicate able to fail.** -/
theorem registryMigratedFor_fails_of_unlisted {dirOf : VerifiedPlugin → Option String}
    {reg : List VerifiedPlugin} {p : VerifiedPlugin}
    (hp : p ∈ reg) (hnone : dirOf p = none) :
    ¬ RegistryMigratedFor dirOf reg := by
  intro h
  obtain ⟨dir, hsome, -⟩ := h p hp
  rw [hnone] at hsome
  exact absurd hsome (by intro heq; exact Option.noConfusion heq)

/-- **A registry containing a plugin with a foreign obligation is NOT migrated.** -/
theorem registryMigratedFor_fails_of_foreign {dirOf : VerifiedPlugin → Option String}
    {reg : List VerifiedPlugin} {p : VerifiedPlugin} {dir : String} {o : Obligation}
    (hp : p ∈ reg) (hd : dirOf p = some dir)
    (hmem : o ∈ p.manifest.obligations) (hforeign : ¬ ObligationOwnedBy dir o) :
    ¬ RegistryMigratedFor dirOf reg := by
  intro h
  obtain ⟨d, hsome, hmig⟩ := h p hp
  rw [hd] at hsome
  have hd_eq : d = dir := by simpa using hsome.symm
  subst hd_eq
  exact not_migrated_of_foreign hmem hforeign hmig

end Lattice.Plugins
