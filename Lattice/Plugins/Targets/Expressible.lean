/-
# `ExpressibleSpec` -- the prerequisite T0 was missing

**T0's five obligations (`construct_sound`, `construct_complete`, `construct_canonical`,
`construct_approx`, `construct_from_scratch`) are all restricted to `ExpressibleSpec`, and that type
did not exist.**
**This file defines it and proves the two facts that make it non-trivial.**

## What "expressible" means here, and why it is NOT `Prop`

**A spec is a list of constraints. A constraint is EXPRESSIBLE when its algebraic layer can be turned
into a polynomial -- `Layer.poly` (already polynomial) or `Layer.square` (polynomial after squaring a
distance, at the cost of the sign).**
**`Layer.existential` needs a witness eliminated first, and `Layer.transc` cannot become polynomial at
all.**

## Why this definition and not a `Prop`-valued predicate on lists

**A `Prop`-valued `IsExpressible : List (GeoConstraint n) → Prop` would be satisfiable by an arbitrary
witness and could be assumed by hypothesis.**
**=> `ExpressibleSpec n` is a SUBTYPE: it CARRIES the list together with the membership proof.**
**A function taking `ExpressibleSpec n` therefore cannot be handed a non-expressible spec at all,
which is exactly the restriction T0 needs.**

## The two facts proved below

**`mem_expressible`**: membership in a spec implies expressibility. **The carrier's guarantee.**
**`not_mem_of_transc` / `not_mem_of_existential`**: a transcendental or existential constraint is NOT a
member of any spec. **The exclusion, which is what makes the subtype informative.**
-/

import Lattice.Plugins.Manifest
import Lattice.Reference.Geometry.Constraints.Constraint

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Geo

/-- **The two algebraic layers that can be made polynomial WITHOUT eliminating a witness.**

**`poly`: already a polynomial equation or inequality.**
**`square`: polynomial after squaring a distance -- exact at the cost of the sign, which is why the
penalty carrier needs the `leZero`/`ltZero` distinction.**
**`existential` is excluded because its witness must be eliminated first, and `transc` because no
elimination exists.** -/
def ExpressibleLayer (L : Lattice.Geo.Layer) : Prop :=
  L = Lattice.Geo.Layer.poly ∨ L = Lattice.Geo.Layer.square

/-- **The expressible layers, as a decidable predicate.** -/
instance ExpressibleLayer.decidable (L : Lattice.Geo.Layer) : Decidable (ExpressibleLayer L) := by
  unfold ExpressibleLayer
  infer_instance

/-- **A constraint is EXPRESSIBLE when its layer is.** -/
def IsExpressible {n : ℕ} (c : GeoConstraint n) : Prop := ExpressibleLayer (c.layer)

/-- **`IsExpressible` is decidable**, because `GeoConstraint.layer` is a function into a finite
inductive type with decidable equality. -/
instance isExpressibleDecidable {n : ℕ} (c : GeoConstraint n) : Decidable (IsExpressible c) := by
  unfold IsExpressible
  infer_instance

/-- **An expressible SPEC: a constraint list, carried together with the proof that every member is
expressible.**

**The proof is part of the VALUE, not a hypothesis.** **A function that takes `ExpressibleSpec n`
therefore cannot be given a spec containing a transcendental constraint -- the type forbids it.**
**That is the whole reason this is a subtype rather than a `Prop`-valued predicate.** -/
structure ExpressibleSpec (n : ℕ) where
  /-- The constraints the spec consists of. -/
  constraints : List (GeoConstraint n)
  /-- Every member is expressible. -/
  expressible : ∀ c ∈ constraints, IsExpressible c

/-- **The empty spec is expressible**, and it is the base case `construct_from_scratch` starts from. -/
def ExpressibleSpec.empty (n : ℕ) : ExpressibleSpec n where
  constraints := []
  expressible := by intro c hc; simp at hc

/-- **A single expressible constraint forms a spec.** -/
def ExpressibleSpec.single {n : ℕ} (c : GeoConstraint n) (hc : IsExpressible c) :
    ExpressibleSpec n where
  constraints := [c]
  expressible := by
    intro d hd
    simp only [List.mem_singleton] at hd
    subst hd
    exact hc

/-- **The carrier's guarantee: every member of a spec is expressible.** -/
theorem mem_expressible {n : ℕ} (S : ExpressibleSpec n) {c : GeoConstraint n}
    (hc : c ∈ S.constraints) : IsExpressible c :=
  S.expressible c hc

/-- **The exclusion, in its general form: a constraint whose layer is neither `poly` nor `square` is
NOT a member of any spec.**

**This is what makes the subtype informative -- without it, `ExpressibleSpec` would be a wrapper
around `List` with a vacuous proof.**

**Note the statement is about the LAYER, not about a constructor: the library has no
`GeoConstraint.transc` constructor at all** -- **`Layer.transc` is a classification, and no current
constraint falls into it.** **So the exclusion has to be said about layers, and it is: any layer that
is not `poly` and not `square` is excluded, which covers `existential` and `transc` uniformly.** -/
theorem not_mem_of_layer {n : ℕ} (S : ExpressibleSpec n) (c : GeoConstraint n)
    (hL : c.layer ≠ Lattice.Geo.Layer.poly) (hL2 : c.layer ≠ Lattice.Geo.Layer.square) :
    c ∉ S.constraints := by
  intro hmem
  have hexp : IsExpressible c := mem_expressible S hmem
  unfold IsExpressible ExpressibleLayer at hexp
  rcases hexp with h | h
  · exact hL h
  · exact hL2 h

/-- **`collinear` is NOT expressible** -- its layer is `existential` (a scalar multiple must be
exhibited). -/
theorem collinear_not_expressible {n : ℕ} (a b c : ℕ) :
    ¬ IsExpressible (n := n) (GeoConstraint.collinear a b c) := by
  unfold IsExpressible ExpressibleLayer
  rw [show (GeoConstraint.collinear a b c).layer = Lattice.Geo.Layer.existential from rfl]
  intro h
  rcases h with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **`parallel` is NOT expressible**, for the same reason. -/
theorem parallel_not_expressible {n : ℕ} (a b c e : ℕ) :
    ¬ IsExpressible (n := n) (GeoConstraint.parallel a b c e) := by
  unfold IsExpressible ExpressibleLayer
  rw [show (GeoConstraint.parallel a b c e).layer = Lattice.Geo.Layer.existential from rfl]
  intro h
  rcases h with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **`samePoint` IS expressible** -- its layer is `poly`. -/
theorem samePoint_expressible {n : ℕ} (a b : ℕ) :
    IsExpressible (n := n) (GeoConstraint.samePoint a b) := by
  unfold IsExpressible ExpressibleLayer
  exact Or.inl rfl

/-- **`rightAngle` IS expressible** -- its layer is `poly`. -/
theorem rightAngle_expressible {n : ℕ} (a b c : ℕ) :
    IsExpressible (n := n) (GeoConstraint.rightAngle a b c) := by
  unfold IsExpressible ExpressibleLayer
  exact Or.inl rfl

/-- **`sqDistEq` IS expressible** -- its layer is `square`. -/
theorem sqDistEq_expressible {n : ℕ} (a b : ℕ) (d : GeoExpr n) :
    IsExpressible (n := n) (GeoConstraint.sqDistEq a b d) := by
  unfold IsExpressible ExpressibleLayer
  exact Or.inr rfl

/-- **`equalLength` IS expressible** -- its layer is `square`. -/
theorem equalLength_expressible {n : ℕ} (a b c e : ℕ) :
    IsExpressible (n := n) (GeoConstraint.equalLength a b c e) := by
  unfold IsExpressible ExpressibleLayer
  exact Or.inr rfl

/-- **`midpoint` IS expressible** -- its layer is `poly`. -/
theorem midpoint_expressible {n : ℕ} (m a b : ℕ) :
    IsExpressible (n := n) (GeoConstraint.midpoint m a b) := by
  unfold IsExpressible ExpressibleLayer
  exact Or.inl rfl

/-- **`perpendicular` IS expressible** -- its layer is `poly`. -/
theorem perpendicular_expressible {n : ℕ} (a b c e : ℕ) :
    IsExpressible (n := n) (GeoConstraint.perpendicular a b c e) := by
  unfold IsExpressible ExpressibleLayer
  exact Or.inl rfl

end Lattice.Plugins.Targets
