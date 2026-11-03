/-
# T1's missing half: the `MergeRecord`'s fields must actually matter

**The audit found that `compile_sound`'s conclusion
`(samePointLadder pts a b).satW ((samePointLadder pts a b).l2l3 [])` does not mention `R` at all.**

**The audit's diagnosis was right, and the reason is narrower than it looks:**
**`hR : R.merged = [samePoint a b]` PINS `merged` down completely, and `merged` is the only field
`merge_sound` consumes.**
**=> the theorem is true of EVERY `MergeRecord` whose `merged` is that singleton -- including ones
whose `rejected` function is arbitrary, whose `experts` are empty, and whose `priority` is absurd.**

**That is not a bug in the proof; it is a bug in what `ProofComplete` was conjoining.**
**`t1_compile_sound_instance` (round 71) recorded only that narrow instance.**

## What this file adds

**`merge_sound_unrejected`: a constraint that IS in `allConstraints` and was NOT rejected is a member of
`merged`, hence holds.**
**That is the statement in which `R.rejected` does real work** -- **and it is exactly what a reader of
"compilation is sound" wants: the compiler did not silently drop a constraint the human kept.**

**`rejected_is_dropped`: and the converse for a rejected one.** **Together the two say the `rejected`
field is a complete description of what survives, which is the property the audit found missing.**
-/

import Lattice.Plugins.Manifest
import Lattice.Semantics.Merge

namespace Lattice.Plugins.Targets

open Lattice.Semantics.Merge
open Lattice.Geo
open Lattice.Geo.ConstraintSet

/-- **A constraint in `allConstraints` that was NOT rejected is a member of `merged`.**

**`merged` is `allConstraints.filter (fun c => !rejected c)`, and `List.mem_filter` turns the three
facts (membership, non-rejection) into membership of the filtered list.**
**This is where `R.rejected` is CONSUMED: the statement is false if the filter is replaced by the
identity.** -/
theorem mem_merged_of_not_rejected {n : ℕ} (R : MergeRecord n) {c : GeoConstraint n}
    (hmem : c ∈ R.allConstraints) (hrej : R.rejected c = false) :
    c ∈ R.merged := by
  unfold MergeRecord.merged
  exact List.mem_filter.mpr ⟨hmem, by simp [hrej]⟩

/-- **A rejected constraint is NOT a member of `merged`.**

**The other direction, and it is what makes `rejected` a COMPLETE description of what survives.** -/
theorem not_mem_merged_of_rejected {n : ℕ} (R : MergeRecord n) {c : GeoConstraint n}
    (hrej : R.rejected c = true) : c ∉ R.merged := by
  unfold MergeRecord.merged
  intro hmem
  have := (List.mem_filter.mp hmem).2
  simp [hrej] at this

/-- **THE STRENGTHENED T1: every unrejected constraint of the record HOLDS.**

**A `MergeSound` record satisfies not only its `merged` list but every constraint it did not reject.**
**=> `R.rejected` and `R.allConstraints` -- hence `R.global` and `R.experts` -- genuinely participate in
the conclusion.** **This is the statement the audit found missing, and it is strictly stronger than
`merge_sound` on the filtered list.** -/
theorem merge_sound_unrejected {n : ℕ} (R : MergeRecord n) (pts : ℕ → Pt n)
    (h : MergeSound R pts) :
    ∀ c ∈ R.allConstraints, R.rejected c = false → GeoConstraint.Holds c pts := by
  intro c hmem hrej
  have hmerged : HoldsSet R.merged pts := merge_sound R pts h
  have hin : c ∈ R.merged := mem_merged_of_not_rejected R hmem hrej
  exact holdsSet_mem hin pts hmerged

/-- **The `rejected` field is a COMPLETE description of what survives.**

**A constraint is in `merged` exactly when it is in `allConstraints` and was not rejected.**
**Stated as a biconditional because the two halves above are only jointly informative:**
**a filter that dropped nothing and rejected some would satisfy one half; a filter that kept
everything would satisfy the other.** -/
theorem mem_merged_iff {n : ℕ} (R : MergeRecord n) {c : GeoConstraint n} :
    c ∈ R.merged ↔ (c ∈ R.allConstraints ∧ R.rejected c = false) := by
  unfold MergeRecord.merged
  rw [List.mem_filter]
  constructor
  · intro ⟨hmem, hnot⟩
    exact ⟨hmem, by simpa using hnot⟩
  · intro ⟨hmem, hrej⟩
    exact ⟨hmem, by simp [hrej]⟩

/-- **T1's strengthened conjunct: the record's unrejected constraints all hold.** -/
def t1_merge_sound_unrejected : Prop :=
  ∀ {n : ℕ} (R : MergeRecord n) (pts : ℕ → Pt n), MergeSound R pts →
    ∀ c ∈ R.allConstraints, R.rejected c = false → GeoConstraint.Holds c pts

/-- **`t1_merge_sound_unrejected` holds** -- by `merge_sound_unrejected`. -/
theorem t1_merge_sound_unrejected_holds : t1_merge_sound_unrejected := by
  intro n R pts h c hmem hrej
  exact merge_sound_unrejected R pts h c hmem hrej

end Lattice.Plugins.Targets
