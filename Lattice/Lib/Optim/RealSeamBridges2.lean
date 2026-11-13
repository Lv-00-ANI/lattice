import Mathlib
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lib.Convex.RealKKTSecondOrder
import Lattice.Lib.Optim.RealSaddlePoint
import Lattice.Lib.Quantization.RealCompressedSensing
import Lattice.Lib.LinearAlgebra.RealSparseCoding
import Lattice.Lib.Architectures.RealNormSharpConstant
import Lattice.Lib.Architectures.RealRMSNormSharpness
import Lattice.Lib.Architectures.RealLayerPropagation
import Lattice.Lib.Chain.RealModelFamilyChainWiring
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lib.Optim.RealListFinBridge
import Lattice.Lib.LearningTheory.RealDecisionTheory
import Lattice.Lib.LearningTheory.RealBayesOptimality
import Lattice.Plugins.Architectures.Norm.Proofs
import Lattice.Lib.Chain.RealCrossUniverseConsumer
import Lattice.Lib.Optim.RealCrossUniverseBridge
import Lattice.Lib.Editing.RealExtractCanonical
import Lattice.Lib.Editing.RealExtractSurjectivity
import Lattice.Lib.Editing.RealCompileExtractClosed

open Lattice.Lift.SymbolToWeightCorrectness

/-!
# LATTICE: RealSeamBridges2 -- seam bridges, batch 2 (EXEC-X2)

## Why this file exists

The EXEC-V2 census of lattices/lean found 91 groups of "same signature, never
written as an identity" zero-import seams. lean (batch 1) landed
bridges 1/2/6. This module lands the remaining joinable seams from Top 6-20.

Mechanism (EXEC-V2): a seam is not "the author did not think of it"; it is
"namespace name collision forced the author to drop the import and redefine
in place". Hence the correct shape of a bridge is: a NEW module that imports
BOTH ends and states the identity with FULLY QUALIFIED names. No existing
module is modified (doing so triggers "environment already contains").

Scope of that mechanism (narrowed): it holds for PART OF the seams only --
e.g. the batch-mean, indicator-function and LV (LayerNorm triple) groups.
Bridge 18 is a DIFFERENT case, and its zero-import has a different cause:
there the two ends use two different predicate families -- mathlib's WEAK
IsLocalMin / IsLocalMax on the IsSaddle side, versus the STRICT IsStrictLocalMin
/ IsStrictLocalMax defined in the two ends -- so the equivalence EXEC-V2
proposed for it is simply FALSE (see section 1 and section 7.1 below). What
this module proves for bridge 18 is therefore NOT "the same definition that was
written twice, joined up", but an arithmetic relation between two DIFFERENT
definitions: the strict-extremum duality
isStrictLocalMax_eq_neg_isStrictLocalMin.

Precedent: RealTemporalLayer.lean:178-179 (gazeUp_eq_intent / gazeDown_eq_extent, both rfl).

## Shape discipline (identity > iff > identical function)

EXEC-V2 section 5.1 admits that bridges 8/9/11/12/15/17/18/19 were only
signature-checked, not body-checked. This module READS EVERY BODY VERBATIM and
then picks the strongest TRUE shape:

* bodies verbatim equal      -> pointwise identity  f x = g x   (rfl)
* bodies are exact complements -> Iff (Iff.rfl), NOT a Prop-equality
* bodies DIFFER (bridge 11)  -> reported NON-SEAM, not forced

## Excluded candidates (reported as NON-SEAM)

* Bridge 11 rmsNormE vs lnE: rmsNormE x = sqrt n . ((1/||x||) . x) (pure RMS),
  while lnE x = rmsNormE (ctr x) with ctr the centering map
  (lean:245). RMSNorm != LayerNorm; the bodies have
  DIFFERENT types. Section 4 gives a machine-checked witness instead.
* Bridge 17 admissible_iff_not_dominated: ALREADY IN THE LIBRARY
  (lean:89; 1 hit in _EXISTING_THEOREMS.txt). Not reopened.
* Bridge 9 layerToCLM vs compiledToCLM: the two ends are ALREADY CONNECTED.
* Bridge 15 toFinVec vs toVec: the two ends form an import CYCLE.

## Honest boundaries

* This module adds NO new mathematics; it pins definition pairs that already exist.
* No sorry / axiom / admit / native_decide.
* #print axioms all subset {propext, Classical.choice, Quot.sound}; no sorryAx.
* No claim of the form "mathlib is missing X".
* Roots registration is the coordinator's job; this executor does not touch lakefile.toml.
-/

noncomputable section

open scoped BigOperators

namespace Lattice

open Lattice.Lift.SymbolToWeightCorrectness (ConstraintSet AllSatisfied AllZeroOutputs compileToLayer Layer)
namespace Seam2


/-! =====================================================================
## 1. Bridge 18 -- saddle point vs strict local extremum

* lean:77  IsStrictLocalMin f x := exists d > 0, forall y, y != x ->
                                 |y - x| < d -> f x < f y
* lean:64    IsStrictLocalMax f x := exists d > 0, forall y, y != x ->
                                 |y - x| < d -> f y < f x
* lean:58    IsSaddle f x := deriv f x = 0 / not IsLocalMin f x
                                 / not IsLocalMax f x

The two STRICT extremum bodies are verbatim the same shape (only f x < f y vs
f y < f x swapped). But IsSaddle uses MATHLIB's IsLocalMin / IsLocalMax (the
WEAK notions), NOT the two STRICT notions above. Hence the statement EXEC-V2
proposed for bridge 18 (IsSaddle iff not strict-min and not strict-max) is
FALSE in general: strict implies weak, so "not weak" does not give "not strict".
This module therefore proves only the TRUE half: the duality between the two
strict-extremum definitions across the two modules.
===================================================================== -/

/-- BRIDGE: the two modules' STRICT local extremum bodies are verbatim the same
    shape (only the inequality is swapped). This is a genuine seam: the two ends
    were zero-import before (RealKKTSecondOrder -> RealSaddlePoint = false,
    RealSaddlePoint -> RealKKTSecondOrder = true). -/
theorem isStrictLocalMax_eq_neg_isStrictLocalMin (f : ℝ → ℝ) (x : ℝ) :
    IsStrictLocalMax f x =
      IsStrictLocalMin (fun y : ℝ => -f y) x := by
  -- 要点 两端的定义体不相同（`f y < f x` vs `-f y < -f x`），故 **不是** `rfl`；
  --    需要 `propext` + `neg_lt_neg_iff` 把不等式方向翻过来。
  unfold IsStrictLocalMax IsStrictLocalMin
  -- 要点 `propext` 是**定理**（`(a ↔ b) → a = b`），不是 tactic ⟹ 用 `apply`。
  apply propext
  constructor
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun y hy hlt => neg_lt_neg_iff.mpr (h y hy hlt)⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun y hy hlt => neg_lt_neg_iff.mp (h y hy hlt)⟩

/-- NON-VACUITY WITNESS: the identity above is not "both ends collapsed to the
    same constant" -- it really forks: the RealSaddlePoint side carries
    IsStrictLocalMax.toIsLocalMax (lean:83), which the
    RealKKTSecondOrder side does not have. -/
theorem isStrictLocalMax_toIsLocalMax_via_saddle {f : Real -> Real} {x : Real}
    (h : IsStrictLocalMax f x) :
    IsLocalMax f x := IsStrictLocalMax.toIsLocalMax h

/-! =====================================================================
## 2. Bridge 12 -- the two definitions of sparsity

* lean:1429        def IsSparse  {n} (k : Nat) (x : Fin n -> Real) : Prop := l0Norm x <= k
* lean:205    abbrev IsKSparse {n} (k : Nat) (x : Fin n -> Real) : Prop := l0Norm x <= k

The bodies are verbatim equal AND both consume the SAME l0Norm (RealCompressedSensing
gets it transitively from RealSparseCoding). The proposition is therefore an Iff,
NOT a Prop-equality: on Prop, rfl-equality is strictly weaker and more awkward
than Iff (Iff is itself defined as the two-way implication, so Iff.rfl closes it).

Reachability: RealCompressedSensing -> RealSparseCoding = true, reverse = false.
===================================================================== -/

/-- BRIDGE: the two sparsity predicates are verbatim synonymous. -/
theorem IsKSparse_iff_IsSparse {n : Nat} (k : Nat) (x : Fin n -> Real) :
    IsKSparse k x <-> IsSparse k x := Iff.rfl

/-- NON-VACUITY WITNESS: after unfolding, both sides really do land on the SAME
    l0Norm -- so the bridge transports the whole RealSparseCoding theory of L0
    norms onto the RealCompressedSensing side. -/
theorem IsKSparse_iff_l0Norm_le {n : Nat} (k : Nat) (x : Fin n -> Real) :
    IsKSparse k x <-> l0Norm x <= k := Iff.rfl

/-! =====================================================================
## 3. Bridge 16 -- constraint conversion, layer propagation vs chain wiring

* lean:86-90
    coreVecToReal n x := fun i => ((toVec n x) i : Real)
    coreConstraintToReal n c := { a := coreVecToReal n c.a, b := (c.b : Real) }
* lean:46-51
    toRealVec n x := fun i => ((toVec n x) i : Real)
    castConstraint n c := { a := toRealVec n c.a, b := (c.b : Real) }

The two STRUCTURE bodies are verbatim identical; only the helper names differ
(coreVecToReal vs toRealVec), and BOTH delegate to the same toVec.
The signature is (n : Nat) (c : VectorConstraint) : RealVectorConstraint (Fin n).
The True, Strongest shape is the pointwise equality of the two structure values.
===================================================================== -/

/-- HELPER BRIDGE: the two field-mapping helpers are the same function. -/
theorem coreVecToReal_eq_toRealVec (n : Nat) (x : List Int) :
    coreVecToReal n x = toRealVec n x := rfl

/-- BRIDGE: the two constraint converters produce the SAME structure value. -/
theorem coreConstraintToReal_eq_castConstraint (n : Nat)
    (c : VectorConstraint) :
    coreConstraintToReal n c
      = castConstraint n c := rfl

/-- Projection: the bias components agree. -/
theorem coreConstraintToReal_b_eq (n : Nat) (c : VectorConstraint) :
    (coreConstraintToReal n c).b
      = (castConstraint n c).b := rfl

/-- Projection: the coefficient components agree pointwise. -/
theorem coreConstraintToReal_a_eq (n : Nat) (c : VectorConstraint) :
    (coreConstraintToReal n c).a
      = (castConstraint n c).a := rfl

/-- NON-VACUITY WITNESS: the chain-wiring side's own wording of the bias identity
    (lean:58) is reached through the bridge as well. -/
theorem castConstraint_b_eq_convertVec_b (n : Nat)
    (c : VectorConstraint) :
    (castConstraint n c).b
      = (((convertVec c).b : Int) : Real) :=
  convertVec_bias_eq_convertRealVec_bias n c

/-! =====================================================================
## 4. Bridge 11 -- NOT A SEAM: rmsNormE (RMSNorm) vs lnE (LayerNorm)

EXEC-V2 section 2.2 bridge 11 treats the two ends as "to be proved equal, direction
undecided". Reading the bodies verbatim decides it: NOT EQUAL.

* lean:165-166
    rmsNormE x := (Real.sqrt n) . ((1 / ||x||) . x)        -- no centering
* lean:185-186
    lnE x := rmsNormE (ctr x)                              -- centering first
  with lean:245-246
    ctr z := fun i => z i - (sum j, z j) / (n : Real)      -- centering

So lnE = rmsNormE after ctr. These are two DIFFERENT mathematical operations
(RMSNorm does not center; LayerNorm does). A "seam" by definition requires the two
bodies to be the same definition repeated, so bridge 11 is NOT a seam at all.

Below: lnE is literally definitionally rmsNormE composed with ctr (rfl), and the
two maps are shown to DIFFER at a concrete point, refuting EXEC-V2's direction A
(rmsNormE x = lnE x for all x).
===================================================================== -/

/-- The TRUE structural relation: lnE is DEFINITIONALLY rmsNormE after centering. -/
theorem lnE_eq_rmsNormE_ctr {n : Nat} (x : EuclideanSpace Real (Fin n)) :
    lnE x = rmsNormE (ctr x) := rfl

/-- The point (3, 5) in Real^2. -/
def p35 : EuclideanSpace Real (Fin 2) := fun i => if i = 0 then 3 else 5

/-- The centered direction `(-1, 1)`, used as the second half of the decisive witness. -/
def pNeg : EuclideanSpace Real (Fin 2) := fun i => if i = 0 then (-1 : Real) else 1

/-- Centering (3, 5) gives (-1, 1): the coordinate form of ctr. -/
theorem ctr_p35 : ctr p35 = fun i : Fin 2 => if i = 0 then (-1 : Real) else 1 := by
  funext i
  fin_cases i <;>
    simp [ctr, p35, Fin.sum_univ_two] <;> norm_num

/-- DECISIVE WITNESS: rmsNormE pins the DIRECTION of (3, 5), so it is a POSITIVE
    multiple of (3, 5), whereas lnE centers first and is a multiple of (-1, 1).
    The two therefore cannot be equal: their coordinates have opposite signs. -/
theorem lnE_p35_eq_ne_rmsNormE : lnE p35 ≠ rmsNormE p35 := by
  intro h
  have hctr : ctr p35 = fun i : Fin 2 => if i = 0 then (-1 : Real) else 1 := ctr_p35
  rw [lnE, hctr] at h
  have h1 := congrFun h 0
  have h2 := congrFun h 1
  simp only [rmsNormE, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, p35,
    Fin.sum_univ_two, Fin.isValue] at h1 h2
  -- h1, h2 : scalar relations; the scalar is sqrt 2 / ||(3,5)||
  have hnorm : ‖(p35 : EuclideanSpace Real (Fin 2))‖ = Real.sqrt (9 + 25) := by
    rw [EuclideanSpace.norm_eq]
    simp [p35, Fin.sum_univ_two, Real.sq_sqrt (by norm_num : (0:Real) <= 9 + 25)]
    norm_num
  simp only [hnorm] at h1 h2
  -- 要点 先把 `√(9+25)` 规范成 `√34`，**再**做 `field_simp`（顺序反了会重复除）。
  have h34 : Real.sqrt (9 + 25) = Real.sqrt 34 := by norm_num
  rw [h34] at h1 h2
  have hspos : 0 < Real.sqrt 34 := Real.sqrt_pos.mpr (by norm_num)
  have hsne : Real.sqrt 34 ≠ 0 := ne_of_gt hspos
  -- 要点 分母 `‖(-1,1)‖` 也要化到 √2。注意 `h1/h2` 已被上面的 `simp` 写成复合形式，
  --    故用 `simp only [hn2]`（它能在子项里重写），而不是 `rw`。
  -- 要点 `h1/h2` 里的分母是 `ctr_p35` 给出的**匿名 lambda**。`pNeg` 从未出现在它们中，
  --    故 `simp only [pNeg]` 类改写无效。改为：先证 `‖pNeg‖ = √2`，再用 `pNeg` 的
  --    **定义等式**把 `h1/h2` 的分母整体换成 `pNeg`（`← hpNeg` 方向）。
  have hn2 : ‖(pNeg : EuclideanSpace Real (Fin 2))‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    simp [pNeg, Fin.sum_univ_two, Real.sq_sqrt (by norm_num : (0:Real) <= 2)]
  have hpNeg : pNeg = (fun i : Fin 2 => if i = 0 then (-1 : Real) else 1) := rfl
  rw [← hpNeg] at h1 h2
  simp only [hn2] at h1 h2
  -- 两个分母（√34 与 √2）都非零，先清掉再交给 `nlinarith`。
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2
  field_simp [hsne, hs2ne] at h1 h2
  -- 要点 `h1/h2` 里的 `pNeg 0`、`p35 0` 等尚未展开成具体数值，`nlinarith` 看不出矛盾。
  --    展开后：`pNeg 0 * √34 = √2 * p35 0` 变成 `-√34 = 3√2`（左负右正）。
  -- 要点 `simp only [pNeg, p35]` 展开了定义，但留下未化简的 `if`：
  --    `(if True then -1 else 1) * √34 = √2 * if True then 3 else 5`。
  --    故一并化简 `if`（`Fin.isValue` 让 `1 = 0` 可判定）。
  simp only [pNeg, p35, Fin.isValue, Fin.zero_eta, reduceIte, if_true, if_false,
             Fin.val_zero, Fin.val_one] at h1 h2
  norm_num at h1 h2
  nlinarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 34),
             Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)]

end Seam2

/-! =====================================================================
# EXEC-X4 -- batch 4: the normalization family, the extract chain, and the
# three anchors.  Everything below was written after READING EVERY BODY
# VERBATIM.  Where the bodies do NOT agree, this section reports a NON-SEAM
# and supplies a machine-checked witness instead of a forced identity.
===================================================================== -/

namespace Seam4

/-! =====================================================================
## 5. THE NORMALIZATION FAMILY (EXEC-V2 group 4, the highest-value seam)

EXEC-V2 group 4 lists  varNormalize :432,
RealLayerNorm.center :29, RealLayerNorm.normalize :80, RealRMSNorm.rmsNorm :32
as one signature class spanning three zero-import modules.  Reading the bodies
verbatim splits them into TWO DIFFERENT codomain classes, and that split is
the finding.

  RealBatchNorm.lean:29        bmean    X : (iota -> Real) : Real
    = (sum i, X i) / (Fintype.card iota : Real)
  RealBatchNormConsistency:75  batchMean X : (iota -> Real) : Real
    = (sum i, X i) / (Fintype.card iota : Real)          <- VERBATIM SAME
  RealLayerNorm.lean:26        mean     x : (iota -> Real) : Real
    = (sum i, x i) / (Fintype.card iota : Real)          <- VERBATIM SAME
  RealRMSNorm.lean:27          rms      x : (iota -> Real) : Real
    = Real.sqrt ((sum i, x i ^ 2) / (Fintype.card iota : Real))
                                                        <- DIFFERENT (RMS)

  RealBatchNorm.lean:32        bcenter X : (iota -> Real) : iota -> Real
    = fun i => X i - bmean X
  RealLayerNorm.lean:29        center  x : (iota -> Real) : iota -> Real
    = fun i => x i - mean x                              <- VERBATIM SAME
  RealBatchNormConsistency:432 varNormalize x : (iota -> Real) : iota -> Real
    = fun i => x i / Real.sqrt (varOf x)
      with varOf x = (sum i, x i ^ 2) / (Fintype.card iota : Real)
                                                        <- RMS-TYPE, NOT center
  RealLayerNorm.lean:80        normalize x = fun i => center x i / sqrt (centerSq x)
                                                        <- LN-TYPE, NOT varNormalize
  RealRMSNorm.lean:32          rmsNorm  x = fun i => x i / rms x
                                                        <- RMS-TYPE, NOT center

Reachability(measured, EXEC-X4): RealBatchNorm -> RealLayerNorm = false both ways;
RealRMSNorm -> {RealBatchNorm, RealLayerNorm, RealBatchNormConsistency} = false both ways;
RealBatchNormConsistency -> RealLayerNorm = true (one way only).
So bmean/batchMean are one-way connected while center is not, and
varNormalize (both ends) has NEVER been pinned to rmsNorm.  That last pair is
the genuinely unclaimed seam.

Signature caveat (EXEC-V2 section 5.3 caveat 2): V2 grouped varNormalize with
center/normalize/rmsNorm because its signature normalizer does no alpha-renaming
and does not discriminate the codomain shape.  Reading the bodies shows
{x : iota -> R} : R  (bmean/batchMean/mean/rms) and
{x : iota -> R} : iota -> R  (bcenter/center/varNormalize/normalize/rmsNorm)
are TWO classes, not one.
===================================================================== -/

/-- BRIDGE 1a (group 4): bmean and batchMean are the same statistic.
    Bodies verbatim identical: (sum i, X i) / (Fintype.card iota : Real).
    This is a rfl-level DEFINITION EXPANSION, so the proof body is a bare
    identity -- the substantive content is the identification across modules. -/
theorem bmean_eq_batchMean {ι : Type*} [Fintype ι] (X : ι → ℝ) :
    Lattice.bmean X = Lattice.batchMean X := rfl

/-- BRIDGE 1b (group 4): bmean and mean are the same statistic.
    Bodies verbatim identical: (sum i, x i) / (Fintype.card iota : Real).
    NOTE: at this point BOTH Lattice.bmean (RealBatchNorm) and
    Lattice.batchMean (RealBatchNormConsistency) are in scope, so the bare
    name mean is unambiguous ONLY because RealLayerNorm.mean is the unique
    mean in the whole library (verified by a library-wide grep: the sole
    declaration named mean is RealLayerNorm.lean:26).  It is still written
    fully qualified below to keep the seam explicit. -/
theorem bmean_eq_mean {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Lattice.bmean x = Lattice.mean x := rfl

/-- BRIDGE 1c (group 4): batchMean and mean agree.
    Composed from 1a and 1b; listed separately so downstream can cite the
    RealBatchNormConsistency <-> RealLayerNorm edge directly. -/
theorem batchMean_eq_mean {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Lattice.batchMean x = Lattice.mean x := rfl

/-- BRIDGE 1d (group 4, THE UNCLAIMED SEAM): bcenter and center are the same
    centering map.  Bodies verbatim identical: fun i => x i - <mean> x, and by
    1b the two means are the same term. -/
theorem bcenter_eq_center {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Lattice.bcenter x = Lattice.center x := rfl

/-- BRIDGE 2 (group 4, THE UNCLAIMED SEAM): varNormalize and rmsNorm are the
    same RMS-type normalization.  This pair had ZERO prior theorem layer:
    _EXISTING_THEOREMS.txt has varNormalize => 5 and rmsNorm => 31 names but
    no name in EITHER family mentions the other symbol.

    Bodies: varOf x = (sum i, x i ^ 2) / (Fintype.card iota : Real) and
    rms x = Real.sqrt ((sum i, x i ^ 2) / (Fintype.card iota : Real)), so
    sqrt (varOf x) = rms x definitionally.  The identity below is therefore a
    genuine definitional expansion once varOf is unfolded. -/
theorem varNormalize_eq_rmsNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Lattice.varNormalize x = Lattice.rmsNorm x := rfl

/-- HELPER (group 4): the two RMS-type variances are the same real number.
    varOf x = rms x ^ 2 is what makes bridge 2 a rfl rather than a rewriting
    argument; it is stated separately because it is the reusable half of the
    identification. -/
theorem varOf_eq_rms_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Lattice.varOf x = Lattice.rms x ^ 2 := by
  unfold Lattice.varOf Lattice.rms
  rw [Real.sq_sqrt]
  exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)

/-- NON-VACUITY WITNESS for bridge 2 (the point of this section): the two ends
    are NOT inert copies of each other.  RealRMSNorm carries
    rmsNorm_scale_invariant (RealRMSNorm.lean:65) and RealBatchNormConsistency
    carries varOf_varNormalize_eq_one (:435) and varOf_varNormalize_le_one
    (:461).  Composing through the bridge transports the RMSNorm scale-invariance
    theory onto the variance-pinning theory across a previously zero-import edge.

    Concretely: after the bridge the variance-pinning statement can be read as
    a statement about rmsNorm, which was impossible before (the two symbols
    could not appear in the same term in this environment). -/
theorem varOf_varNormalize_eq_one_via_rmsNorm {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (h : Lattice.varOf x ≠ 0) :
    Lattice.varOf (Lattice.rmsNorm x) = 1 := by
  rw [← varNormalize_eq_rmsNorm x]
  exact Lattice.varOf_varNormalize_eq_one x h

/-- The counterexample vector (3,5) in the Fin 2 shape that the EXEC-V2 census
    actually grouped (its group 4 signature is (x : iota -> R) : iota -> R). -/
def x35 : Fin 2 → ℝ := fun i => if i = 0 then 3 else 5

/-- THE DECISIVE NON-SEAM (group 4): EXEC-V2 group 4 lumps varNormalize with
    RealLayerNorm.normalize under one signature.  The bodies REFUTE that:
    normalize CENTERS first (fun i => center x i / sqrt (centerSq x)) while
    varNormalize does NOT (fun i => x i / sqrt (varOf x)).  These are the
    LayerNorm vs RMSNorm distinction -- the two codomains agree but the
    operations differ.

    Witness: varNormalize (3,5) is a POSITIVE multiple of (3,5), while
    normalize (3,5) is a multiple of the CENTERED vector (-1,1); their first
    coordinates therefore have opposite signs, so the two maps cannot agree. -/
theorem varNormalize_x35_ne_normalize_x35 :
    Lattice.varNormalize x35 ≠ Lattice.normalize x35 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Lattice.varNormalize, Lattice.normalize, Lattice.center, Lattice.mean,
    Lattice.varOf, Lattice.centerSq, x35, Fin.sum_univ_two] at h0 h1
  -- 要点 矛盾在 `h0` 里：左边是正数（varNormalize 的正倍数），右边是负数
  --    （normalize 沿 **中心化** 方向）。`norm_num` 单独不会产生 `False`，
  --    故显式分离出这个矛盾。
  -- 要点 `h0 : 3/√17 = -1/√2`：左边【正】、右边【负】。`norm_num at h0` 不会自动产生
  --    `False`（它不比较两边的符号），故显式给出两边的符号反证。
  norm_num at h0
  -- 要点 `positivity` 证明的是 `0 < x`；这里第二个目标是 **`x < 0`**，故显式构造。
  have hpos : (0:ℝ) < 3 / Real.sqrt 17 := by positivity
  have hneg : -1 / Real.sqrt 2 < (0:ℝ) := by
    have h2pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact div_neg_of_neg_of_pos (by norm_num) h2pos
  linarith

end Seam4

namespace Seam5

/-! =====================================================================
## 6. THE EXTRACT CHAIN (EXEC-V2 group 13 / bridge-3 family)

EXEC-V2 section 2.2 already records that
  lean:150  extractLayer_eq_extractLayer
EXISTS and closes by rfl.  It is NOT reopened here.  What is still open is the
FAN-OUT around it:

* extractLayer   :100  (ls : Layer) : ConstraintSet
* extractLayer_alt   :143  (ls : Layer) : ConstraintSet
  -> ALREADY BRIDGED (:150).  Verified present in _EXISTING_THEOREMS.txt
     (extractLayer_eq_extractLayer => 1).

The unclaimed content is therefore NOT another copy of the same identity but
its CONSEQUENCES on the round-trip / surjectivity theorems.  Before this
module the environment could state the round-trip only about extractLayer and
the surjectivity only about the same object, but never consume both families
in one term.  The lemmas below transport the round-trip results onto the
extractLayer_alt spelling and then consume BOTH in a single statement. -/

/-- BRIDGE 3a: the surjectivity of compileToLayer re-keyed onto extractLayer_alt.
    This is the extractLayer_alt-flavoured reading of
    extractLayer_surjective (:163); it is obtained by
    transporting along the EXISTING bridge :150 rather than by re-proving. -/
theorem extractLayer_alt_surjective (ls : Lattice.Lift.SymbolToWeightCorrectness.Layer) :
    ∃ cs : Lattice.Lift.SymbolToWeightCorrectness.ConstraintSet, Lattice.Lift.SymbolToWeightCorrectness.compileToLayer cs = ls := by
  refine ⟨Lattice.extractLayer_alt ls, ?_⟩
  rw [Lattice.extractLayer_eq_extractLayer]
  exact Lattice.compileToLayer_extractLayer ls

/-- BRIDGE 3b: left inverse stated for extractLayer_alt -- the exact composite
    that extractLayer_leftInverse (:138) states for
    extractLayer.  The transport is the rw on the existing rfl bridge; it is
    NOT a re-proof and NOT a bare rfl of a Prop. -/
theorem extractLayer_alt_leftInverse :
    Function.LeftInverse Lattice.extractLayer_alt Lattice.Lift.SymbolToWeightCorrectness.compileToLayer := by
  intro cs
  rw [Lattice.extractLayer_eq_extractLayer]
  exact Lattice.extractLayer_compileToLayer cs

/-- BRIDGE 3c: right inverse for extractLayer_alt. -/
theorem extractLayer_alt_rightInverse :
    Function.RightInverse Lattice.extractLayer_alt Lattice.Lift.SymbolToWeightCorrectness.compileToLayer := by
  intro ls
  rw [Lattice.extractLayer_eq_extractLayer]
  exact Lattice.compileToLayer_extractLayer ls

/-- NON-VACUITY WITNESS: the two ends really do carry different theorem layers.
    RealExtractSurjectivity owns the INJECTIVITY / SURJECTIVITY / range side
    (extractVec_injective :100, extractVec_range_eq_univ :118,
    extractVec_range_ne_proper :124) while RealCompileExtractClosed owns the
    ROUND-TRIP side (extractLayer_compileToLayer :112,
    compileToLayer_extractLayer :126).  This lemma is the first statement in
    the environment that consumes BOTH families in one term. -/
theorem extractLayer_range_and_roundtrip (ls : Lattice.Lift.SymbolToWeightCorrectness.Layer) :
    (∃ cs : Lattice.Lift.SymbolToWeightCorrectness.ConstraintSet, Lattice.Lift.SymbolToWeightCorrectness.compileToLayer cs = ls) ∧
      Lattice.Lift.SymbolToWeightCorrectness.compileToLayer (Lattice.extractLayer_alt ls) = ls :=
  ⟨extractLayer_alt_surjective ls, by
    rw [Lattice.extractLayer_eq_extractLayer]
    exact Lattice.compileToLayer_extractLayer ls⟩

end Seam5

namespace Seam6

/-! =====================================================================
## 7. THE THREE ANCHORS (groups 5, 6, 7)

EXEC-V2 bridges 18 / 17 / 9.  All three were re-read verbatim here; the
findings differ from EXEC-V2's proposals in two of the three cases.

### 7.1 KKT vs Saddle (bridge 18) -- V2's proposal is FALSE, the dual is TRUE
  lean:77  IsStrictLocalMin f x :=
      exists d > 0, forall y, y != x -> |y - x| < d -> f x < f y
  lean:64     IsStrictLocalMax f x :=
      exists d > 0, forall y, y != x -> |y - x| < d -> f y < f x
  lean:58     IsSaddle f x :=
      deriv f x = 0 /\ not IsLocalMin f x /\ not IsLocalMax f x
  V2 proposed IsSaddle f x <-> not IsStrictLocalMin f x /\ not
  IsStrictLocalMax f x.  That is FALSE: IsSaddle uses MATHLIB's WEAK
  IsLocalMin/IsLocalMax, and STRICT implies WEAK, so "not weak" cannot yield
  "not strict" -- a strict local min has not IsLocalMin = false.  What IS a
  genuine seam is the DUALITY between the two modules' strict notions, already
  proved once in batch 2 as
  Seam2.isStrictLocalMax_eq_neg_isStrictLocalMin and NOT duplicated here.

### 7.2 Decision theory (bridge 17) -- ALREADY IN THE LIBRARY, not reopened
  lean:83  def Dominated L d := exists d', (forall th,
      risk L th d' <= risk L th d) /\ exists th, risk L th d' < risk L th d
  RealBayesOptimality:439     def Admissible L d := not (exists d', ...)  -- the
      SAME existential, negated, VERBATIM.
  admissible_iff_not_dominated (:89) already states
  Admissible L d <-> not Dominated L d by Iff.rfl.
  CONFIRMED PRESENT: _EXISTING_THEOREMS.txt hits
  admissible_iff_not_dominated => 1.
  => NOT a seam any more.  The only thing bridge 17 can add is the
  FULLY-QUALIFIED cross-module spelling, since RealDecisionTheory imports
  RealBayesOptimality (one-way) yet the identity was never written with both
  qualified names.  That is what 7.2 proves -- and it is honestly a
  re-spelling, NOT new mathematics.

### 7.3 Cross-universe CLM (bridge 9) -- compiledToCLM IS a pure alias
  lean:101  layerToCLM n l := (linFunc n l).toContinuousLinearMap
  RealCrossUniverseConsumer:110     compiledToCLM n l := layerToCLM n l  <- PURE ALIAS
  check-cross-universe-edge.py flags :110 as ALIAS-NOT-AN-EDGE.  Re-read
  verbatim here: CONFIRMED.  compiledToCLM adds NO content whatsoever, and the
  edge was ALREADY drawn because RealCrossUniverseConsumer imports
  RealCrossUniverseBridge (line 2 of that file).  Consequently bridge 9 is NOT
  a zero-import seam at all -- EXEC-V2's "zero import" claim for this pair is
  REFUTED here.  The identity is still recorded below for completeness, and its
  proof body is a bare definitional unfolding, which is exactly the ALIAS
  signature the checker warned about.
===================================================================== -/

/-- ANCHOR 6 (bridge 17, RE-SPELLING ONLY): Admissible (RealBayesOptimality)
    and Dominated (RealDecisionTheory) are verbatim complements, now stated
    with BOTH names fully qualified so the cross-module edge exists as a term.
    This is NOT new mathematics: admissible_iff_not_dominated
    (:89) already asserts it, and that name is present in
    _EXISTING_THEOREMS.txt.  Recorded here only to close the qualified-name gap. -/
theorem admissible_iff_not_dominated_qualified {n m : ℕ}
    (L : Lattice.Loss n m) (δ : Lattice.DecisionRule m) :
    Lattice.Admissible L δ ↔ ¬ Lattice.Dominated L δ := Iff.rfl

/-- NON-VACUITY WITNESS: the Admissible side really carries independent content
    -- unique_bayes_admissible (:450) is a SUFFICIENT
    condition for Admissible that the Dominated side never proves, and it is
    reached here through the newly written qualified edge. -/
theorem admissible_of_unique_bayes_qualified {n m : ℕ} {prior : Fin n → ℝ}
    [Nonempty (Fin n)] (hp : Lattice.ProbVec prior) (hpos : ∀ θ, 0 < prior θ)
    {L : Lattice.Loss n m} {δ : Lattice.DecisionRule m} [Nonempty (Fin m)]
    (huniq : ∀ δ' : Lattice.DecisionRule m,
      Lattice.bayesRisk prior L δ' < Lattice.bayesRisk prior L δ → False) :
    Lattice.Admissible L δ :=
  Lattice.unique_bayes_admissible hp hpos huniq

/-- ANCHOR 7 (bridge 9): compiledToCLM is a PURE ALIAS of layerToCLM.
    The proof body is a bare definitional unfolding -- this is the ALIAS
    signature flagged by check-cross-universe-edge.py for
    lean:110.  It is recorded for completeness and
    explicitly NOT claimed as a zero-import seam: RealCrossUniverseConsumer
    imports RealCrossUniverseBridge on its line 2, so the edge already existed.
    EXEC-V2's zero-import claim for this pair is REFUTED here. -/
theorem compiledToCLM_eq_layerToCLM_alias (n : Nat)
    (l : Lattice.LinearLayer) :
    Lattice.compiledToCLM n l = Lattice.layerToCLM n l := rfl

/-- ALIAS CONSEQUENCE (bridge 9): because the two names are the same function,
    they have the same operator norm in EVERY argument.  This is the
    machine-checked form of "compiledToCLM is an alias, not a seam": there is
    no argument on which the two can be told apart. -/
theorem compiledToCLM_opNorm_eq (n : Nat) (l : Lattice.LinearLayer) :
    ‖Lattice.compiledToCLM n l‖ = ‖Lattice.layerToCLM n l‖ := rfl

end Seam6


end Lattice
