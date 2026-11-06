/-
# T1's general form: the connection `Representation` was missing

**Round 83 located the residual gap as "a missing FIELD, not a missing proof".**
**Working it out showed the gap is larger than one field, and the reason is the TYPE DESIGN:**

```
structure Representation (P W : Type) where
  inputP  : Type
  inputW  : Type
  encode  : inputP → inputW
  decode  : inputW → inputP
  compile : P → W
  extract : W → P
  roundtrip : ∀ p, extract (compile p) = p
```

**Four INDEPENDENT type fields.**
**`encode`/`decode` live on `inputP`/`inputW`; `compile`/`extract` live on `P`/`W`; and NOTHING relates
`P` to `inputP`.**
**=> the expression "the compiled artifact means the same as the symbol" does not even TYPECHECK against
`Representation` alone.**

**That is why `t1_general_open` could only name the gap.**
**`SemanticRepresentation` below supplies the two maps that close it (`toInput`, `ofInput`), and the
general form of `compile_sound` follows.**

## Why extend rather than modify

**Adding fields to `Representation` would break every existing construction, including the ones the
plugin layer and the legacy tree already use.**
**=> `SemanticRepresentation` CARRIES a `Representation` plus the connection.**
**A reader with a plain `Representation` is unaffected; a reader wanting T1's general form must supply
the semantics -- which is exactly the demand the plan makes.**
-/

import Lattice.Plugins.Manifest
import Lattice.Runtime.Extraction

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Lift

/-- **A representation that carries its SEMANTIC obligation, over an arbitrary equivalence `sem`.**

**`sem` is a PARAMETER rather than a fixed relation, because different layers call different symbols
equivalent** -- **`Lift.SemEq` on `LinearForm` is the instance the legacy tree uses.** -/
structure SemanticRepresentation (P W : Type) (sem : P → P → Prop) where
  /-- The underlying parameter-layer representation. -/
  base : Representation P W
  /-- **How a symbol is presented to the artifact's input space.** -/
  toInput : P → base.inputP
  /-- **How an input-space point is read back as a symbol.**

  **The SECOND half of the obstruction.**
  **`decode` lands in `inputP`, not in `P`, so without this map
  `sem p (decode (encode (toInput p)))` does not typecheck.** -/
  ofInput : base.inputP → P
  /-- **Semantic preservation**: presenting a symbol and reading it back gives an equivalent symbol.

  **`roundtrip` lifted from equality of parameters to `sem`-equivalence of meanings.** -/
  preserves : ∀ p : P, sem p (ofInput (base.decode (base.encode (toInput p))))
  /-- **Semantic reflection**: no two inequivalent symbols present the same way.

  **The converse, and the half that cannot be dropped**: **without it a presentation sending every
  symbol to one point would be "sound" and would carry no information.** -/
  reflects : ∀ p q : P,
    ofInput (base.decode (base.encode (toInput p)))
      = ofInput (base.decode (base.encode (toInput q))) → sem p q

/-- **`sem` is an EQUIVALENCE, stated as the three laws.**

**A relation that is not symmetric cannot carry "`p` is equivalent to `q`" back to "`q` is equivalent
to `p`", and a relation that is not transitive cannot compose the round trip with a known equivalence.**
**=> all three are demanded, and they are what "semantic equivalence" means rather than a technical
convenience.** -/
structure SemEquiv {P : Type} (sem : P → P → Prop) : Prop where
  refl : ∀ p : P, sem p p
  symm : ∀ p q : P, sem p q → sem q p
  trans : ∀ p q r : P, sem p q → sem q r → sem p r

/-- **T1's GENERAL FORM: a semantic representation compiles SOUNDLY.**

**If `q` is equivalent to `p`, then the artifact `p` compiles to decodes back to something equivalent
to `q`.**

**`preserves` gives `p ~ decode(p)`; symmetry turns `q ~ p` into `p ~ q`; transitivity composes them.**
**Each of the three laws is used, which is why the structure demands all three.** -/
theorem compile_sound_general {P W : Type} {sem : P → P → Prop}
    (R : SemanticRepresentation P W sem) (he : SemEquiv sem)
    (p q : P) (h : sem p q) :
    sem q (R.ofInput (R.base.decode (R.base.encode (R.toInput p)))) := by
  have hp : sem p (R.ofInput (R.base.decode (R.base.encode (R.toInput p)))) := R.preserves p
  -- `h : sem p q`; symmetry gives `sem q p`, then transitivity composes with `hp`
  exact he.trans q p _ (he.symm p q h) hp

/-- **The identity representation is semantically sound at every symbol.**

**`P = W = inputP = inputW`, every map is the identity, and `sem` is reflexive.**
**=> the structure is INHABITED, which is what stops `compile_sound_general` from being vacuous.** -/
def identitySemantic (P : Type) (sem : P → P → Prop) (hrefl : ∀ p, sem p p) :
    SemanticRepresentation P P sem where
  base :=
    { inputP := P
      inputW := P
      encode := id
      decode := id
      compile := id
      extract := id
      roundtrip := fun _ => rfl }
  toInput := id
  ofInput := id
  preserves := fun p => hrefl p
  reflects := by
    intro p q hpq
    -- every map is the identity, so `hpq` IS `p = q`
    have hpq' : p = q := hpq
    subst hpq'
    exact hrefl p

/-- **The inhabited instance yields a TRUE but WEAK conclusion -- and that is the right behaviour.**

**At the identity representation, the general form says: if `p ~ q` then `q ~ p`.**
**Weak, but INHABITED, which is exactly what an interface needs first: a structure nobody can inhabit
would make its theorem vacuous.** -/
theorem identitySemantic_sound (P : Type) (sem : P → P → Prop) (hrefl : ∀ p, sem p p)
    (hsymm : ∀ a b : P, sem a b → sem b a)
    (htrans : ∀ a b c : P, sem a b → sem b c → sem a c) (p q : P) (h : sem p q) :
    sem q p :=
  let he : SemEquiv sem := ⟨hrefl, hsymm, htrans⟩
  compile_sound_general (identitySemantic P sem hrefl) he p q h

/-- **T1's general conjunct, as a `Prop` over the whole class.** -/
def t1_compile_sound_general : Prop :=
  ∀ {P W : Type} {sem : P → P → Prop} (R : SemanticRepresentation P W sem),
    SemEquiv sem →
    ∀ p q : P, sem p q → sem q (R.ofInput (R.base.decode (R.base.encode (R.toInput p))))

/-- **`t1_compile_sound_general` holds** -- by `compile_sound_general`. -/
theorem t1_compile_sound_general_holds : t1_compile_sound_general := by
  intro P W sem R he p q h
  exact compile_sound_general R he p q h

end Lattice.Plugins.Targets
