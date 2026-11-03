/-
# Plugin dependencies and safe activation

**A runtime that loads plugins cannot unload one that another still needs.**
**That is a REACHABILITY property, and it is the operational content of `spatial` for a plugin host:
a plugin's space is the set of plugins that may not be removed while it is live.**

## The statement

**A dependency graph `dep : Name → List Name` records, for each plugin, the plugins it needs.**
**`Reaches dep a b` says `b` is reachable from `a` along dependency edges.**
**`canDeactivate dep live x` says no LIVE plugin reaches `x` -- so removing `x` breaks nothing.**

**`deactivate_before_unload` then says: if `y` is live and reaches `x`, then `x` cannot be deactivated.**
**That is exactly the guarantee a loader must have, and it is about the GRAPH, not about any particular
plugin -- which is why it is stated over an arbitrary `dep`.**

## Why reachability rather than a one-step check

**A transitive dependency is still a dependency.** **Checking only direct edges would permit removing a
plugin that a live plugin needs through two hops** -- **the classic unload bug.**
**=> `Reaches` is the transitive closure, and `canDeactivate` quantifies over it.**
-/

import Lattice.Plugins.Runtime.Spatiotemporal.Fail

namespace Lattice.Plugins.Runtime.Spatiotemporal

/-- **Reachability in the dependency graph, as an inductive relation.**

**`refl`/`step` make this the TRANSITIVE closure** -- **`step` chains, which is what a one-step-only
predicate (and a loaders' one-step check) gets wrong.** -/
inductive Reaches {Name : Type} (dep : Name → List Name) : Name → Name → Prop where
  /-- Every plugin reaches itself. -/
  | refl (a : Name) : Reaches dep a a
  /-- If `a` needs `b` directly, it reaches `b`. -/
  | step {a b : Name} : b ∈ dep a → Reaches dep a b
  /-- And reachability chains. -/
  | trans {a b c : Name} : Reaches dep a b → Reaches dep b c → Reaches dep a c

/-- **A plugin may be deactivated when no live plugin reaches it.** -/
def canDeactivate {Name : Type} (dep : Name → List Name) (live : List Name) (x : Name) : Prop :=
  ∀ y, y ∈ live → ¬ Reaches dep y x

/-- **T6, dependency form: a live plugin's dependency cannot be deactivated.**

**If `x` is reachable from a live `y`, then `canDeactivate dep live x` is FALSE.**
**The proof is immediate from the definition, and that IS the point:** **the guarantee follows from
stating `canDeactivate` over the transitive closure rather than over direct edges.**
**A one-step version would not imply this, which is why the closure is the right carrier.** -/
theorem deactivate_before_unload {Name : Type} (dep : Name → List Name) (live : List Name)
    (x y : Name) (hy : y ∈ live) (hreach : Reaches dep y x) :
    ¬ canDeactivate dep live x := by
  intro hcan
  exact hcan y hy hreach

/-- **A plugin nobody live depends on CAN be deactivated.**

**The positive half: the definition is not vacuous.**
**Witnessed by leaving `live` empty -- which is the state a loader starts in.** -/
theorem canDeactivate_of_nil_live {Name : Type} (dep : Name → List Name) (x : Name) :
    canDeactivate dep [] x := by
  intro y hy
  simp at hy

/-- **Reachability is reflexive for every plugin.**

**Recorded because it is the step that makes `canDeactivate` non-trivial: a live plugin blocks its OWN
deactivation through `refl`.** -/
theorem reaches_self {Name : Type} (dep : Name → List Name) (a : Name) :
    Reaches dep a a :=
  Reaches.refl a

end Lattice.Plugins.Runtime.Spatiotemporal
