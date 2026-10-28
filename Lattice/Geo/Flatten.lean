import Mathlib
import Lattice.Geo.Expr
import Lattice.Runtime.Extraction
/-!
# `Lattice.Geo.Flatten` -- configurations as finite vectors

## Why a configuration has to become a vector

`GeoExpr.evalPts` is interpreted in `pts : ℕ → Pt n` -- a family of points indexed by `ℕ`, because a
constraint *mentions* points by number and does not know how many the ambient figure has.

Every theorem in `Lattice.Lib` about weights, however, is about a **finite-dimensional** vector: `MLayer m n`
acts on `Fin n → ℝ`, `PenaltyMatrix` on `Fin n → ℝ`, `PolyExact` differentiates in a Banach space. So the
two sides cannot meet until the configuration is finitised.

This file does the finitisation and proves it is lossless:

```
flatten   : (Fin k → Pt n) → (Fin (k * n) → ℝ)
unflatten : (Fin (k * n) → ℝ) → (Fin k → Pt n)
```

with `unflatten (flatten c) = c` and `flatten (unflatten v) = v`.

## The bijection is the object-layer statement of requirement (5)

The project is required to state reversibility **by layer**, and to record that the object layer is a
bijection while the semantic layer is not. This file is where the first half lives for the geometric
chain: encoding a configuration as a vector loses nothing, and `flatten_unflatten` /
`unflatten_flatten` are the two halves of that.

The semantic half is *not* true and is proved elsewhere: two distinct configurations can satisfy the same
constraint, and the project's `Extraction.semantic_not_injective` records the linear analogue.

## Encoding choice

`flatten` uses the equivalence `Fin k × Fin n ≃ Fin (k * n)`, so the vector layout is
"point 0's coordinates, then point 1's, ...". Any bijection would do; this one is chosen because it is
the one mathlib already gives a name to, so the two round-trip laws are proved by `simp` rather than by
hand-written index arithmetic.
-/

namespace Lattice.Geo

variable {k n : ℕ}

/-- **The layout equivalence** between "a point index and a coordinate" and "a coordinate of the
flattened vector".

Stated as a `def` rather than used inline so that the round-trip lemmas below can be proved once. -/
def flatEquiv (k n : ℕ) : Fin k × Fin n ≃ Fin (k * n) := finProdFinEquiv

/-- **Flatten a configuration** of `k` points in `n` dimensions to a single real vector.

This is the operation that lets the geometric layer speak to the weight layer: after it, a constraint is
a function on `Fin (k * n) → ℝ`, which is exactly a `Lattice.Lib` vector. -/
noncomputable def flatten (pts : Fin k → Pt n) : Fin (k * n) → ℝ :=
  fun i => pts (flatEquiv k n |>.symm i).1 (flatEquiv k n |>.symm i).2

/-- **Unflatten a vector** back into a configuration. -/
noncomputable def unflatten (v : Fin (k * n) → ℝ) : Fin k → Pt n :=
  fun p q => v (flatEquiv k n (p, q))

/-- **The object layer is a bijection**: unflattening a flattened configuration recovers it.

This is the "对象层已证双射" half of the reversibility requirement, for the geometric chain. -/
@[simp] theorem unflatten_flatten (pts : Fin k → Pt n) : unflatten (flatten pts) = pts := by
  funext p q
  unfold unflatten flatten
  simp [flatEquiv]

/-- **The object layer is a bijection**: flattening an unflattened vector recovers it.

The other half. Together with `unflatten_flatten` this makes `flatten` an equivalence, which is what
allows a statement about configurations to be transported to a statement about weights without loss. -/
@[simp] theorem flatten_unflatten (v : Fin (k * n) → ℝ) : flatten (unflatten v) = v := by
  funext i
  unfold flatten unflatten
  rw [Equiv.apply_symm_apply]

/-- `flatten` is injective, as a bijection must be. -/
theorem flatten_injective : Function.Injective (flatten (k := k) (n := n)) := by
  intro a b h
  have := congrArg unflatten h
  simpa using this

/-- `flatten` is surjective. -/
theorem flatten_surjective : Function.Surjective (flatten (k := k) (n := n)) :=
  fun v => ⟨unflatten v, flatten_unflatten v⟩

/-- **The configuration space is equivalent to a finite-dimensional real vector space.**

The bundled form of the two round-trip laws; useful when a theorem wants `Nonempty (A ≃ B)` rather than
the two directions. -/
noncomputable def flattenEquiv : (Fin k → Pt n) ≃ (Fin (k * n) → ℝ) where
  toFun := flatten
  invFun := unflatten
  left_inv := unflatten_flatten
  right_inv := flatten_unflatten

/-! ## `flatten` as a `Representation`

`flattenEquiv` is a bijection, and `Lattice.Lift.Extraction.ofEquiv` turns any bijection into a `Representation`.
Putting them together gives the geometry layer its **object-level** compile/extract pair: compilation lays the
finite point set out as a real vector, extraction reads it back, and the round trip holds because `flatten` and
`unflatten` invert each other.

This is the layer G9 calls "the object level", where the bijection is proved. It is *not* the semantic layer --
`Lattice.Geo.Semantic.semantic_not_injective` shows no right inverse survives the quotient there. Both facts are
needed, and they are about different things: that is what the objective's "reversibility must be stated in
layers" asks for. -/

/-- **The geometry layer's `Representation`**, built from `flattenEquiv`. -/
noncomputable def flattenRepresentation (k n : ℕ) :
    Lattice.Lift.Representation (Fin k → Pt n) (Fin (k * n) → ℝ) :=
  Lattice.Lift.ofEquiv (flattenEquiv (k := k) (n := n))

/-- **`flattenRepresentation` is not the identity**: its round trip goes through `flatten` and `unflatten`, so the
statement is about those two functions rather than reducing to `p = p`. -/
theorem flattenRepresentation_roundtrip (k n : ℕ) (pts : Fin k → Pt n) :
    (flattenRepresentation k n).extract ((flattenRepresentation k n).compile pts) = pts :=
  flattenEquiv (k := k) (n := n) |>.symm_apply_apply pts

/-- **... and it is genuinely two-directional**, which the round-trip obligation alone does not demand. -/
theorem flattenRepresentation_compile_extract (k n : ℕ) (v : Fin (k * n) → ℝ) :
    (flattenRepresentation k n).compile ((flattenRepresentation k n).extract v) = v :=
  flattenEquiv (k := k) (n := n) |>.apply_symm_apply v

end Lattice.Geo
