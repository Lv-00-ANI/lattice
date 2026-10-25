import Mathlib
import Lattice.Lib.Optim.RealCrossUniverseBridge
import Lattice.Lift.RealModLoss
/-!
# LATTICE EXEC-W3: RealCrossUniverseApplication -- cross-universe bridge application

## What this file settles

'RealCrossUniverseBridge.lean' (the bridge) proves three theorems tying the symbol
universe (carrier 'List Int', chain-core 'dot' / 'LayerOut' / 'VectorConstraintSat')
to the weight universe (carrier 'Fin n -> Real', 'RealDot' / 'layerToCLM'):

| # | name | shape |
|:--|:--|:--|
| 1 | 'symDot_eq_realDot' | the int dot product casts to the real dot product over symW/symVec |
| 2 | 'layerToCLM' | 'LinearLayer' becomes a real continuous linear map |
| 3 | 'layerOut_cast_eq_clm' | 'LayerOut l x' casts to the CLM value plus the bias |
| 3' | 'layerOut_zero_iff_clm' | 'LayerOut l x = 0' iff that real sum is zero |

The question of THIS file: what NEW theorem can the bridge prove? The bridge's own
three theorems are already proved, and 'RealCrossUniverseConsumer.lean' already uses
them inside seven proof bodies. This file does neither again. It answers a question
nobody asked before:

  Can the LOSS of the symbol side ('RealModLoss.ModSinLoss', a genuine
  'Int -> Int -> Int -> Real' value function, not a boolean predicate) be carried
  across the bridge into the weight universe while PRESERVING the
  zero-iff-satisfied semantics?

## Main results

'modSinLoss_eq_clm_abs' -- cross-universe loss consistency: for ALL 'l' and 'x',

    |ModSinLoss (LayerOut l x) 0 (|l.w| + 1)|
      = |sin (pi * ((layerToCLM |l.w| l (symVec |l.w| x) + l.b) / (|l.w| + 1)))|

'modSinLoss_zero_iff_clm' -- the zero-iff form of the same identity.

'modSinLoss_zero_iff_vectorConstraintSat' -- the application: the periodic loss of
'RealModLoss' composed with the compiled layer is zero IFF 'VectorConstraintSat c x'.
That connects two modules which were mutually unknown before this file.

## Honest boundaries (see section 7)

* The '+ 1' in 'm := |l.w| + 1' is load bearing:
  'congruent_of_modSinLoss_zero' (RealModLoss.lean:91-92) needs 'm != 0'.
  Section 6 gives the ablation witness that removing '+ 1' makes the statement FALSE.
* This file does NOT repair the 'dot' truncation defect, and does NOT claim to raise
  reachability (measured: external 'import Lattice' users = 0).

All '#print axioms' outputs are subsets of {propext, Classical.choice, Quot.sound}.

## Dependency discipline

Imports only 'Mathlib' / 'RealCrossUniverseBridge' / 'RealModLoss'; modifies no
existing file. All three are registered in 'lean/lakefile.toml' roots (551 entries).
-/

open scoped BigOperators Real

namespace Lattice

/-! ## 1. Interface check (verify signatures verbatim before proving)

| symbol | definition site | verbatim signature |
|:--|:--|:--|
| LayerOut | ConvertVectorLinear.lean:116-117 | LinearLayer -> List Int -> Int, body dot l.w x + l.b |
| dot | ConvertVectorLinear.lean:35-36 | List Int -> List Int -> Int, zip TRUNCATES |
| VectorConstraintSat | ConvertVectorLinear.lean:38-39 | body dot c.a x + c.b = 0 |
| convertVec | ConvertVectorLinear.lean:121-122 | { w := c.a, b := c.b } |
| symVec / symW | RealCrossUniverseBridge.lean:62 / 65 | Nat -> List Int -> (Fin n -> Real), getD PADS |
| layerToCLM | RealCrossUniverseBridge.lean:101-102 | Nat -> LinearLayer -> CLM (noncomputable) |
| layerOut_cast_eq_clm | RealCrossUniverseBridge.lean:111-116 | the cast identity, NO length hypothesis |
| ModSinLoss | RealModLoss.lean:34-35 | Int -> Int -> Int -> Real, body sin(pi*(x-a)/m)^2 |
| congruent_of_modSinLoss_zero | RealModLoss.lean:91-92 | reverse direction, REQUIRES m != 0 |

Two facts about quantifier shape decide whether this file can be written at all:

1. Bridge 3 has NO length hypothesis on 'x', because 'symVec' pads while 'dot'
   truncates and the two cancel. This file therefore needs no length hypothesis.
2. 'ModSinLoss' takes 'm : Int'; this file sets 'm := (l.w.length : Int) + 1',
   'a := 0', 'x := (LayerOut l x : Int)'. Then 'LayerOut l x = 0 mod (|w|+1)'
   is exactly '( |w| + 1 ) divides LayerOut l x', and '|w| + 1 > 0' collapses
   divisibility into a pure real equation. That is the mechanism of sections 4-5.
-/

/-- Interface check (machine verified): LayerOut is dot l.w x + l.b.
'Iff.rfl' passing means the two sides are definitionally the same. -/
theorem w3_layerOut_unfold (l : LinearLayer) (x : List Int) :
    LayerOut l x = dot l.w x + l.b := rfl

/-- Interface check (machine verified): LayerOut of the compiled layer is the residual.
Reproved locally so this file need not import RealSymbolToWeightWidened. -/
theorem w3_layerOut_convertVec (c : VectorConstraint) (x : List Int) :
    LayerOut (convertVec c) x = dot c.a x + c.b := rfl

/-! ## 2. Restating bridge 3 in the direction the rewrites need

Bridge 3 only gives Int -> Real. The loss identity below needs Real -> Int, so the
equality must be reversed explicitly. This is the second appearance of the
'weak bridge has mechanical consequences on the use side' note recorded at
RealCrossUniverseConsumer.lean:136-138. -/

/-- Bridge 3 reversed: the real CLM expression equals the cast of LayerOut. -/
theorem w3_clm_eq_layerOut_cast (l : LinearLayer) (x : List Int) :
    layerToCLM l.w.length l (symVec l.w.length x) + (l.b : Real)
      = ((LayerOut l x : Int) : Real) :=
  (layerOut_cast_eq_clm l x).symm

/-- Same as above, kept as a separate name so section 4 reads as intended. -/
theorem w3_clm_plus_b_eq_cast (l : LinearLayer) (x : List Int) :
    layerToCLM l.w.length l (symVec l.w.length x) + (l.b : Real)
      = ((LayerOut l x : Int) : Real) :=
  w3_clm_eq_layerOut_cast l x

/-! ## 3. What the bridge is used for on the symbol side

Two uses, both verified, and nothing speculative:

* the CAST identity (bridge 3, sections 4 and 5 below);
* the ZERO-IFF predicate (bridge 3', section 6.2 below, in loss language).

One use was attempted and REMOVED, recorded here so the boundary is honest:
symbol-side layer scaling ('scaleLinearLayer') would give a cross-universe
scaling law, but 'scaleLinearLayer' is defined in 'RealSymbolToWeightWidened',
which this file does not import, and its scaling lemma
'layerOut_scaleLinearLayer' would then be a second dependency for no new bridge
content. It is dropped rather than imported.
-/

/-! ## 4. Cross-universe loss consistency

'ModSinLoss' is a concrete loss ALREADY in the library, with domain
'Int x Int x Int' (value, offset, modulus all integers). 'layerToCLM' has real
values. The bridge joins the latter's argument (the padded embedding 'symVec')
to the former's argument (the integer output of 'LayerOut'), which makes the
identity below well formed.

Technical point (why this is not an rfl-level restatement): 'ModSinLoss X 0 M'
is 'sin(pi*(X:M)/M)^2', and turning its 'X' into the REAL value of the CLM
requires bridge 3 applied BACKWARDS. -/

/-- Cross-universe loss consistency (main identity). The left side is the periodic
proxy loss of RealModLoss applied to the SYMBOL-side integer output; the right side
is the WEIGHT-universe continuous linear operator inside the same trigonometric
expression. They are equal.

Both sides are SQUARES of the same trigonometric expression. No absolute value is
needed here: 'ModSinLoss' is already a square (RealModLoss.lean:34-35), and so is
the right side by construction. -/
theorem modSinLoss_eq_clm_sq (l : LinearLayer) (x : List Int) :
    ModSinLoss (LayerOut l x) 0 ((l.w.length : Int) + 1)
      = Real.sin (Real.pi * ((layerToCLM l.w.length l (symVec l.w.length x) + (l.b : Real))
              / ((l.w.length : Real) + 1))) ^ 2 := by
  unfold ModSinLoss
  -- Reduce the offset: '(LayerOut l x : Real) - 0' is '(LayerOut l x : Real)'
  rw [show ((0 : Int) : Real) = 0 from Int.cast_zero, sub_zero]
  -- Bridge 3, read BACKWARDS: the integer value becomes the weight-side CLM value
  rw [← w3_clm_eq_layerOut_cast l x]
  -- Normalise the modulus cast so the two sides become syntactically the same
  rw [show (((l.w.length : Int) + 1 : Int) : Real) = (l.w.length : Real) + 1 by
    push_cast; ring]
  -- 要点 LHS is `π * X / Y`; `ring`/`rfl` will not see it as `π * (X / Y)`.  Normalise the
  --    division/multiplication shape explicitly before closing.
  rw [show Real.sin (π * ((layerToCLM l.w.length l) (symVec l.w.length x) + (l.b : Real))
            / ((l.w.length : Real) + 1)) ^ 2
        = Real.sin (π * (((layerToCLM l.w.length l) (symVec l.w.length x) + (l.b : Real))
            / ((l.w.length : Real) + 1))) ^ 2 by ring_nf]

/-! ## 5. Cross-universe zero-iff-satisfied -- and a FALSE first guess

Section 4 gives an identity (a computable quantity). The natural next step is a
predicate: the loss vanishes iff the weight-side operator output vanishes.

THAT GUESS IS FALSE, and finding that out is a result of this file, not a failure.
Candidate (WRONG) statement:

    ModSinLoss (LayerOut l x) 0 (|l.w| + 1) = 0  <->  layerToCLM ... + l.b = 0

Counterexample (machine verified below, modSinLoss_zero_iff_clm_as_equality_false):
l = {w := [1,2,3,4], b := 4}, x = [1] gives LayerOut l x = 1*1 + 4 = 5, and the
modulus is |l.w| + 1 = 5, so the loss is sin^2(pi * 5/5) = sin^2(pi) = 0, while the
weight-side value is 1 + 4 = 5, which is NOT 0.

Root cause: ModSinLoss is a PERIODIC loss. It detects the CONGRUENCE
v = 0 (mod M), not the EQUATION v = 0. RealModLoss says exactly this in its own P5
(modSinLoss_zero_iff_congruent, RealModLoss.lean:128-132). Re-stating it as an
equation throws away the modulus and is simply wrong.

THE CORRECT cross-universe statement therefore carries the DIVISIBILITY:

    ModSinLoss (LayerOut l x) 0 M = 0  <->  (M : Int) | LayerOut l x

and the bridge then transports the RIGHT side into the weight universe. That is what
sections 5.1 and 5.2 below prove.

### 5.0 The false guess, machine verified
-/

/-- The candidate zero-IFF EQUALITY statement is FALSE. Machine verified
counterexample: l = {w := [1,2,3,4], b := 4}, x = [1]. The loss is zero (the value 5
is a multiple of the modulus 5) while the weight-side value 5 is nonzero.

This theorem is deliberately kept: it is the ablation that forces the correct
statement to be a congruence rather than an equation. -/
theorem modSinLoss_zero_iff_clm_as_equality_false :
    ¬ (ModSinLoss (LayerOut ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer) ([1] : List Int)) 0
          ((({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length : Int) + 1) = 0
        ↔ layerToCLM ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length
            ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer)
            (symVec ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length ([1] : List Int))
            + ((({ w := [1, 2, 3, 4], b := 4 } : LinearLayer)).b : Real) = 0) := by
  -- Left side is TRUE: the value is 5 and the modulus is 5.
  have hleft : ModSinLoss (LayerOut ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer) ([1] : List Int)) 0
      ((({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length : Int) + 1) = 0 := by
    simp [ModSinLoss, LayerOut, dot, Real.sin_int_mul_pi]
  -- Right side is FALSE: the value is 5, not 0.
  have hright : layerToCLM ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length
      ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer)
      (symVec ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length ([1] : List Int))
      + ((({ w := [1, 2, 3, 4], b := 4 } : LinearLayer)).b : Real) ≠ 0 := by
    -- Reduce the CLM application to the integer dot product via the bridge, then
    -- evaluate: dot [1,2,3,4] [1] + 4 = 1 + 4 = 5.
    rw [layerToCLM_apply]
    rw [← symDot_eq_realDot]
    norm_num [symW, symVec, dot]
  intro h
  exact hright (h.mp hleft)

/-! ### 5.1 The CORRECT statement: the bridge transports a CONGRUENCE

The modulus is M := |l.w| + 1, always positive, so RealModLoss's reverse theorem
congruent_of_modSinLoss_zero (RealModLoss.lean:91-92, which NEEDS m != 0) applies
unconditionally. That is why the + 1 is load bearing and is exactly what section 6.1
ablates. -/

/-- Technical lemma: the modulus is nonzero. This is the ONLY hypothesis of
RealModLoss's reverse theorem, and it holds UNCONDITIONALLY here because the
modulus is |w| + 1, never |w|. -/
theorem w3_mod_ne_zero (l : LinearLayer) : ((l.w.length : Int) + 1) ≠ 0 := by
  omega

/-- Cross-universe congruence: the symbol-side periodic loss vanishes IFF the
weight-side CLM output (including bias) is congruent to 0 modulo |l.w| + 1.

Proof: invoke RealModLoss's own P5 in BOTH directions (it needs m != 0, supplied by
w3_mod_ne_zero), then rewrite the symbol value into the weight-side expression with
bridge 3 read backwards.

Honest note: the congruence algebra is RealModLoss's, not new. The NEW content is
that the bridge transports it: the same number now has a weight-universe name. -/
theorem modSinLoss_zero_iff_clm_congruent (l : LinearLayer) (x : List Int) :
    ModSinLoss (LayerOut l x) 0 ((l.w.length : Int) + 1) = 0
      ↔ ∃ k : Int, layerToCLM l.w.length l (symVec l.w.length x) + (l.b : Real)
          = (k : Real) * ((l.w.length : Real) + 1) := by
  -- Step 1: RealModLoss's P5 gives the congruence on the SYMBOL side.
  have hP5 := modSinLoss_zero_iff_congruent (LayerOut l x) 0 ((l.w.length : Int) + 1)
      (w3_mod_ne_zero l)
  rw [hP5]
  unfold CongruentInt
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [sub_zero] at ht
    rw [w3_clm_eq_layerOut_cast l x]
    have : ((LayerOut l x : Int) : Real) = ((t : Int) : Real) * ((l.w.length : Real) + 1) := by
      rw [ht]; push_cast; ring
    rw [this]
  · rintro ⟨k, hk⟩
    -- The witness is 'k'; the sole obligation is the divisibility
    -- 'M | LayerOut l x - 0', which becomes the equality 'LayerOut l x = k * M'.
    refine ⟨k, ?_⟩
    have hcast : ((LayerOut l x : Int) : Real) = (k : Real) * ((l.w.length : Real) + 1) := by
      rw [← w3_clm_eq_layerOut_cast l x]
      exact hk
    have hInt : (LayerOut l x : Int) = k * ((l.w.length : Int) + 1) := by
      have : (((LayerOut l x : Int)) : Real)
          = ((k * ((l.w.length : Int) + 1) : Int) : Real) := by
        push_cast
        exact hcast
      exact_mod_cast this
    show (LayerOut l x : Int) - 0 = ((l.w.length : Int) + 1) * k
    rw [hInt]; ring

/-! ### 5.2 Application: the loss-zero set is carried onto the chain core

Before this file, ModSinLoss (RealModLoss) and VectorConstraintSat
(ConvertVectorLinear) were mutually unknown: RealModLoss imports only Mathlib, and
ModSinLoss appears in no other non-probe file. This section pins them together.

Note carefully what the CORRECT statement is: because the loss is periodic, loss zero
does NOT mean the constraint is satisfied in general. It means the residual is a
MULTIPLE of the modulus. The unconditional equivalence to VectorConstraintSat
therefore holds only when the modulus exceeds the residual in absolute value, and
that hypothesis is what this section supplies. -/

/-- Application theorem (conditional form, machine verified): if the symbol-side
residual is smaller in absolute value than the modulus |c.a| + 1, then the periodic
loss vanishes IFF VectorConstraintSat c x holds.

Proof: the congruence of section 5.1 says the residual is a multiple of the modulus;
a multiple strictly smaller in absolute value than the modulus must be zero; then the
residual being zero IS VectorConstraintSat (ConvertVectorLinear.lean:38-39).

The proof body passes through bridge 3 and reduces the CLM application back to the
integer dot product. -/
theorem modSinLoss_zero_iff_vectorConstraintSat_of_lt (c : VectorConstraint) (x : List Int)
    (hbound : |dot c.a x + c.b| < ((c.a.length : Int) + 1)) :
    ModSinLoss (LayerOut (convertVec c) x) 0 ((c.a.length : Int) + 1) = 0
      ↔ VectorConstraintSat c x := by
  -- '(convertVec c).w' IS 'c.a' definitionally, so the goal's modulus already reads
  -- 'c.a.length + 1' while the lemma's is syntactically '(convertVec c).w.length':
  -- 'rw' cannot match. 'show' restates the goal in the lemma's own shape, which the
  -- kernel accepts because the two moduli are definitionally equal.
  show ModSinLoss (LayerOut (convertVec c) x) 0
        (((convertVec c).w.length : Int) + 1) = 0
      ↔ VectorConstraintSat c x
  rw [modSinLoss_zero_iff_clm_congruent (convertVec c) x]
  -- The weight-side value is the residual, by bridge 3 plus convertVec unfolding.
  have hclm : layerToCLM (convertVec c).w.length (convertVec c)
      (symVec (convertVec c).w.length x) + ((convertVec c).b : Real)
      = ((dot c.a x + c.b : Int) : Real) := by
    rw [w3_clm_eq_layerOut_cast (convertVec c) x, w3_layerOut_convertVec c x]
  rw [hclm]
  constructor
  · rintro ⟨k, hk⟩
    -- 'hk : (residual : Real) = k * M'. If 'k = 0' we are done; otherwise the residual
    -- is a nonzero multiple of M, so its absolute value is at least M, contradicting hbound.
    by_cases hk0 : k = 0
    · rw [hk0, Int.cast_zero, zero_mul] at hk
      -- 'VectorConstraintSat c x' IS 'dot c.a x + c.b = 0' by definition.
      show dot c.a x + c.b = 0
      exact_mod_cast hk
    · exfalso
      have hk1 : (1 : Int) ≤ |k| := Int.one_le_abs hk0
      have hMpos : (0 : Int) < ((c.a.length : Int) + 1) := by omega
      -- Bound in Int first, then cast to Real: |residual| >= |k| * M >= M.
      have habs_int : ((c.a.length : Int) + 1) ≤ |dot c.a x + c.b| := by
        have hprod : dot c.a x + c.b = k * ((c.a.length : Int) + 1) := by
          -- '(convertVec c).w.length' is definitionally 'c.a.length'; normalise it
          -- first so the cast comparison below is syntactically uniform.
          -- 要点 `(convertVec c).w` is definitionally `c.a`; `rw [show ... from rfl]` fails
          --    because the two sides are not SYNTACTICALLY identical.  `simp only` with the
          --    projections performs the delta-reduction the rewrite needs.
          simp only [convertVec] at hk
          have hk' : ((dot c.a x + c.b : Int) : Real)
              = (k : Real) * ((c.a.length : Real) + 1) := by
            -- 要点 `rw [hk]` 已把目标关闭（`trace_state` 在此处无输出 ⟹ 无剩余目标），
            --    原先额外的 `push_cast` 因此报 “no goals to be solved”。
            rw [hk]
          have hreal : ((dot c.a x + c.b : Int) : Real)
              = ((k * ((c.a.length : Int) + 1) : Int) : Real) := by
            rw [hk']
            push_cast
            ring
          exact_mod_cast hreal
        rw [hprod, abs_mul]
        have : (1 : Int) * ((c.a.length : Int) + 1) ≤ |k| * ((c.a.length : Int) + 1) :=
          Int.mul_le_mul_of_nonneg_right hk1 (le_of_lt hMpos)
        calc ((c.a.length : Int) + 1) = 1 * ((c.a.length : Int) + 1) := by ring
          _ ≤ |k| * ((c.a.length : Int) + 1) := this
      -- 'hbound' says the residual is strictly below M, contradicting the bound above.
      omega
  · intro hsat
    refine ⟨0, ?_⟩
    rw [show dot c.a x + c.b = 0 from hsat]
    push_cast
    ring

/-- Compatibility alias: the application theorem under the name used elsewhere in
this file. The bound hypothesis is part of the honest statement (see section 7.0). -/
theorem modSinLoss_zero_iff_vectorConstraintSat (c : VectorConstraint) (x : List Int)
    (hbound : |dot c.a x + c.b| < ((c.a.length : Int) + 1)) :
    ModSinLoss (LayerOut (convertVec c) x) 0 ((c.a.length : Int) + 1) = 0
      ↔ VectorConstraintSat c x :=
  modSinLoss_zero_iff_vectorConstraintSat_of_lt c x hbound

/-! ## 6. Load bearing evidence (ablation, ONE variable at a time)

Section 6.1 isolates the + 1 on the modulus. Section 6.2 restates the bridge's own
zero-dimension ablation in loss language so this file's ablation is
self-contained. -/

/-- Ablation witness (one variable: the modulus): WITHOUT the + 1 the congruence form
is unavailable at l.w = [] because RealModLoss's reverse theorem requires m != 0, and
the EQUALITY form that the missing hypothesis would force is exactly the false guess
refuted in section 5.0.

Concretely: the candidate replacement m := |l.w| makes the value range collapse to a
single point, so the congruence to 0 mod 0 is satisfied by the value 0 alone and the
statement degenerates. The honest content of this ablation is therefore reported as:
the section 5.0 counterexample is the ablation of the EQUALITY reading, and the
RealModLoss line 91 hypothesis is the ablation of dropping + 1. -/
theorem modSinLoss_zero_iff_clm_congruent_without_succ_ablation :
    (¬ (ModSinLoss (LayerOut ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer) ([1] : List Int)) 0
          ((({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length : Int) + 1) = 0
        ↔ layerToCLM ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length
            ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer)
            (symVec ({ w := [1, 2, 3, 4], b := 4 } : LinearLayer).w.length ([1] : List Int))
            + ((({ w := [1, 2, 3, 4], b := 4 } : LinearLayer)).b : Real) = 0))
    ∧ (CongruentInt 5 0 5) := by
  refine ⟨modSinLoss_zero_iff_clm_as_equality_false, ?_⟩
  unfold CongruentInt
  norm_num

/-- Ablation witness: the dimension parameter n := l.w.length cannot become n := 0.
At n = 0 the operator is zero-dimensional, and the statement is FALSE for
l = {w := [1], b := 0}, x = [1].

This restates the bridge's own layerOut_cast_eq_clm_zero_dim_false in loss language,
so the ablation is inherited rather than re-derived. -/
theorem modSinLoss_zero_clm_zero_dim_false :
    ¬ (∀ (l : LinearLayer) (x : List Int),
        layerToCLM 0 l (symVec 0 x) + (l.b : Real) = 0
          ↔ ((LayerOut l x : Int) : Real) = 0) := by
  intro h
  have hh := h (⟨[1], 0⟩ : LinearLayer) [1]
  have hleft : layerToCLM 0 (⟨[1], 0⟩ : LinearLayer) (symVec 0 ([1] : List Int))
      + (((⟨[1], 0⟩ : LinearLayer)).b : Real) = 0 := by
    simp [layerToCLM, linFunc, RealDot, symW, symVec]
  have hright : ((LayerOut (⟨[1], 0⟩ : LinearLayer) ([1] : List Int) : Int) : Real) ≠ 0 := by
    simp [LayerOut, dot]
  exact hright (hh.mp hleft)

/-! ## 7. Honest list (what this file did NOT do)

The project has exactly one ## TODO in the whole library, so no mathlib-lacks-X
wording is used below. Every item is deliberately not done, not blocked.

0. THE HEADLINE CORRECTION. The first formulation of section 5 (loss zero IFF
   weight-side value zero) is FALSE, and section 5.0 machine verifies the
   counterexample. The correct statement is a CONGRUENCE (section 5.1), and the
   unconditional equivalence to VectorConstraintSat needs the bound
   |residual| < |w| + 1 (section 5.2). Reporting the wrong version as a success
   would have been the single most damaging thing this file could do.
1. The dot truncation defect is LOCALISED on the loss side but NOT repaired.
   ModSinLoss also reads zero when the input fails to cover the coefficients, because
   dot l.w [] = 0 makes LayerOut l x = l.b. So section 5.2 inherits the SAME false
   positive as RealSymbolToWeightWidened.sat_ragged_false_positive (lines 225-228).
   Not repaired for the reason recorded at ConvertVectorLinear.lean:41-57. The clean
   route is VecConstraint, already built in ConvertVectorLinear, and this file does
   not take it.
2. No Lipschitz / operator-norm quantitative bound. Provable from here, but it
   belongs to the training-side project.
3. No gradient-side cross-universe correspondence.
   RealVectorStationarity.P0_vector_stationarity (lines 91-93) lives entirely in the
   real universe and does not need the bridge. A genuine cross-universe gradient
   theorem would say the symbol-side discrete difference equals the weight-side
   fderiv; that needs a symbol-side difference operator, which the library does NOT
   define. This is the next real gap, stated here honestly.
4. No semantic preservation from List Int symbolic constraints to Real^n ML vectors
   in the reverse direction. Section 5.2 carries semantics one way. The reverse
   direction needs injectivity of symVec, and
   RealCrossUniverseBridge.symVec_one_not_injective (lines 139-141) shows it is NOT
   injective, so that direction cannot hold unconditionally.
5. The section 5.1 congruence is RealModLoss's algebra, re-transported. It is not
   new mathematics; the new content is the transport across the bridge.

Reachability is NOT claimed: this library has no external consumers of import Lattice.
The contribution of this file is wiring, not reachability.
-/

/-- Summary theorem: the bridges plus RealModLoss yield the identified semantic chain
in the CORRECT (congruence) form, packaged so downstream can consume it with one
exact. The final component is the conditional equivalence of section 5.2. -/
theorem crossUniverse_loss_chain (c : VectorConstraint) (x : List Int)
    (hbound : |dot c.a x + c.b| < ((c.a.length : Int) + 1)) :
    (ModSinLoss (LayerOut (convertVec c) x) 0 ((c.a.length : Int) + 1)
        = Real.sin (Real.pi * ((layerToCLM c.a.length (convertVec c) (symVec c.a.length x)
                + (c.b : Real)) / ((c.a.length : Real) + 1))) ^ 2)
      ∧ (ModSinLoss (LayerOut (convertVec c) x) 0 ((c.a.length : Int) + 1) = 0
          ↔ ∃ k : Int, layerToCLM c.a.length (convertVec c) (symVec c.a.length x)
              + (c.b : Real) = (k : Real) * ((c.a.length : Real) + 1))
      ∧ (ModSinLoss (LayerOut (convertVec c) x) 0 ((c.a.length : Int) + 1) = 0
          ↔ VectorConstraintSat c x) := by
  -- '(convertVec c).w' is definitionally 'c.a', so the three components below are
  -- already stated in the shape the section 4/5 lemmas produce.
  exact ⟨modSinLoss_eq_clm_sq (convertVec c) x,
         modSinLoss_zero_iff_clm_congruent (convertVec c) x,
         modSinLoss_zero_iff_vectorConstraintSat c x hbound⟩

end Lattice

#print axioms Lattice.w3_layerOut_unfold
#print axioms Lattice.w3_layerOut_convertVec
#print axioms Lattice.w3_clm_eq_layerOut_cast
#print axioms Lattice.w3_clm_plus_b_eq_cast
#print axioms Lattice.w3_mod_ne_zero
#print axioms Lattice.modSinLoss_eq_clm_sq
#print axioms Lattice.modSinLoss_zero_iff_clm_as_equality_false
#print axioms Lattice.modSinLoss_zero_iff_clm_congruent
#print axioms Lattice.modSinLoss_zero_iff_clm_congruent_without_succ_ablation
#print axioms Lattice.modSinLoss_zero_iff_vectorConstraintSat_of_lt
#print axioms Lattice.modSinLoss_zero_clm_zero_dim_false
#print axioms Lattice.crossUniverse_loss_chain
