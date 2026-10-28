import Mathlib
import Lattice.Runtime.ConvertLinear
/-!
# C-28: the repair metric that `VerifyLoopProgress` says is missing

## What this file is (B398)

`VerifyLoopProgress.lean:44-56` states, in prose, the honest reading of its own
situation:

> ⚠ **不要**据此认为"验证回路保持语义"是错的或空洞的**命题** —— 它是**正确但在此实例上
> 退化的**陈述。真实内容需要**非恒等**的 `repair`，即要求它是解集上的**投影**：
> （i）保持已满足点，**且**（ii）从任意点**有限步到达**解集。
> ⇒ 一般收敛定理**未证**，理由是结构性的：`LinearConstraint` 上的 `ConstraintSat`
> **未给出任何序/度量**，故"下降性"无量可依；补它需要先选一个度量（如 `|a·x+b|` 严格递减），
> **属新工作而非本最小版的接线**。

and at `:48-49` it points at `_r5_p15_repair.lean` -- a probe that
`.gitignore:37` (`lean/_*`) excludes from version control. So the file that
records the two laws, and the worked non-trivial instance, is **not tracked**,
**not in `roots`**, and **imported by nothing**.

This file recovers that content into version control and registers it. Two
things are deliberately kept from the probe, because they are its best parts:

  * the B234.4 substitution test (`repair_preserves_is_identity_statement`),
    which shows the shipped statement is about `id` rather than about `repair`;
  * the concrete counterexample (`shift_by_one_fails_to_preserve`), so the
    degradation is proved NECESSARY rather than merely asserted.

⚠ **Provenance**: adapted from `lean/_r5_p15_repair.lean` (untracked, 133 lines),
whose `exit code: 0` I re-verified before moving it. No new mathematics is
claimed here; the point is that this content must not live only in a file that
git ignores.

设计约定（对齐既有 Lean 形式化实践）：
  注意：订正 B400：此处原写「纯 Std + ConvertLinear」，而**本文件第 1 行就是 `import Mathlib`**
  （所 import 的 `ConvertLinear` 亦然）—— 自相矛盾。
  真实情况是：**本文件的表示层/数学内容只用到 `Int`/`Nat` 等核心类型**
  （`LinearConstraint` 的字段、`ConstraintSat` 的判定、`repairTo` 与 `IsRepair` 的陈述皆落在 `Int` 上，
  所依据的 `ConvertLinear` 构造亦然，不依赖 mathlib 的专用结构），但**文件整体 import 了 Mathlib**
  （本文件中 `simp` 等 tactic 即由 Mathlib 提供，并非 Lean core 内置）。
  ⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。**以本段为准。**
其余为真：无 sorry/axiom/admit/native_decide。
-/

namespace Lattice

/-! ## 1. The B234.4 substitution: what `repair_preserves` is actually about

If the statement below elaborates, then `VerifyLoopProgress.repair_preserves`
is not a statement *about* `repair` -- the identity inlines and the constraint
argument `c` dies, leaving `ConstraintSat c x → ConstraintSat c x`. That is the
"`fun h => h` compiles but says nothing" pattern. -/

/-- **`repair_preserves` with the identity inlined and `c` dead.**
注意：`c` is deliberately left in the signature (not `_c`) so the elaboration
warning stays visible rather than hidden. -/
theorem repair_preserves_is_identity_statement (c : LinearConstraint) (x : Int)
    (h : ConstraintSat c x) : ConstraintSat c x :=
  h

/-! ## 2. The quantifier test: preservation is not a property of repairs in general -/

/-- **A concrete counter-`f`**: `fun _ _ => x + 1` fails to preserve the
constraint `a = 1, b = 0` (whose only solution is `x = 0`; `0 + 1 = 1 ≠ 0`).
This is the negative control: it proves the degradation is necessary. -/
theorem shift_by_one_fails_to_preserve :
    ¬ (∀ (f : LinearConstraint → Int → Int) (c : LinearConstraint) (x : Int),
        ConstraintSat c x → ConstraintSat c (f c x)) := by
  intro h
  have hbad := h (fun _ y => y + 1) ⟨1, 0⟩ 0 (by simp [ConstraintSat])
  simp [ConstraintSat] at hbad

/-- **⇒ The honest reading**: `repair_preserves` holds of the identity *because
the identity is the identity*, not because verification loops preserve
semantics. The projection form of the latter needs an actual projection law,
which `VerifyLoopProgress` does not have. -/
theorem preservation_needs_a_projection_law :
    ∃ (f : LinearConstraint → Int → Int) (c : LinearConstraint) (x : Int),
      ConstraintSat c x ∧ ¬ ConstraintSat c (f c x) :=
  ⟨fun _ y => y + 1, ⟨1, 0⟩, 0, by simp [ConstraintSat], by simp [ConstraintSat]⟩

/-! ## 3. What a NON-trivial repair looks like -- the metric the docstring asks for

A genuine repair is a **projection onto the solution set**: it must (i) preserve
satisfied points and (ii) actually *reach* the solution set from unsatisfied
ones. The identity satisfies (i) and fails (ii) completely.

⭐ This is the "度量" `VerifyLoopProgress:54-56` says is missing, made explicit. -/

/-- **The two laws a real repair must satisfy.** Law 2 is stated as the thing a
convergence proof consumes: finite-step arrival, which is exactly the metric
shape the shipped file lacks. -/
structure IsRepair (c : LinearConstraint) (f : Int → Int) : Prop where
  /-- Law 1 (what the shipped file has, trivially): satisfied points are fixed. -/
  preserves : ∀ x : Int, ConstraintSat c x → ConstraintSat c (f x)
  /-- ⭐ Law 2 (what the shipped file LACKS): unsatisfied points are driven into
  the solution set in finitely many steps. -/
  decreases : ∀ x : Int, ¬ ConstraintSat c x → ∃ n : Nat, ConstraintSat c ((f^[n]) x)

/-- The identity iterated any number of times is the identity (proved locally,
because `Function.iterate_id` does not match the `(fun y => y)^[n]` form under
`rw`). -/
theorem iterate_id_apply (n : Nat) (x : Int) : ((fun y : Int => y)^[n]) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Function.iterate_succ_apply'] using ih

/-- **⇒ A repair with BOTH laws is not the identity**: if an unsatisfied point
exists, the identity violates law 2. This is precisely the triviality
`VerifyLoopProgress` flags about itself. -/
theorem id_is_not_a_repair_when_unsat_exists (c : LinearConstraint) (x : Int)
    (hx : ¬ ConstraintSat c x) : ¬ IsRepair c (fun y => y) := by
  intro h
  obtain ⟨n, hn⟩ := h.decreases x hx
  rw [iterate_id_apply n x] at hn
  exact hx hn

/-! ## 4. A REAL repair on this very constraint type -- law 2 in one step

For `c = ⟨1, -k⟩` the constraint is `x - k = 0`, i.e. `x = k`. The constant map
`fun _ => k` is a genuine repair: both laws hold, law 2 in ONE step. So the
non-trivial shape is reachable at low cost, on the type the shipped file uses.
`VerifyLoopProgress:54-56` calls this "新工作"; it is ~20 lines. -/

/-- Constant repair to `k`: the projection onto `{x | x = k}`. -/
def repairTo (k : Int) : Int → Int := fun _ => k

/-- ⭐ **The repair lands on the solution set from EVERY input** -- the
substantive form the identity repair can never satisfy. -/
theorem repairTo_lands (k x : Int) : ConstraintSat ⟨1, -k⟩ (repairTo k x) := by
  simp [ConstraintSat, repairTo]

/-- ⭐ **Law 1 holds non-trivially here**: `repairTo k` maps the *whole* space
into the solution set, so it preserves satisfied points, and unlike the shipped
`repair_preserves` it does **not** need `ConstraintSat c x` -- because it is not
the identity. 注意：`_h` is marked by the AUTHOR, not silenced by a linter: its
absence is the point (contrast PROCESS.md §3.5's ban on masking). -/
theorem repairTo_preserves (k x : Int) (_h : ConstraintSat ⟨1, -k⟩ x) :
    ConstraintSat ⟨1, -k⟩ (repairTo k x) :=
  repairTo_lands k x

/-- ⭐ **Law 2 in one step from ANY starting point** -- the substantive content
the identity repair cannot have. -/
theorem repairTo_converges (k x : Int) :
    ∃ n : Nat, ConstraintSat ⟨1, -k⟩ ((repairTo k)^[n] x) :=
  ⟨1, by simp [Function.iterate_succ, ConstraintSat, repairTo]⟩

/-- **It really moves** (so it is not a re-labelled identity): for `x ≠ k` the
repaired value differs from the input. -/
theorem repairTo_moves (k x : Int) (h : x ≠ k) : repairTo k x ≠ x := by
  simpa [repairTo] using (Ne.symm h)

/-- ⭐⭐ **The two laws are jointly satisfiable** (non-vacuity of `IsRepair`):
`repairTo k` is a repair for `⟨1, -k⟩`. Without this, `IsRepair` could be an
empty structure and `id_is_not_a_repair_when_unsat_exists` would say nothing. -/
theorem repairTo_is_a_repair (k : Int) : IsRepair ⟨1, -k⟩ (repairTo k) where
  preserves := fun _ _ => repairTo_lands k _
  decreases := fun x _ => ⟨1, by simp [Function.iterate_succ, ConstraintSat, repairTo]⟩

end Lattice
