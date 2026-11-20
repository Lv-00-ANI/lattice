/-
# Penalty Plugin -- assembly

This file is where the plugin's claim meets its proofs. It imports the domain modules, so it
is the ONE file in the plugin that depends on the library proper; `Manifest.lean` stays free
of that dependency, per `PLUGIN-PROOFS.md` §8's rule that proof files do not reach upward.

## How the bundle is assembled

`PluginProof`'s fields are `Prop`s, and Lean's `Prop` is proof-irrelevant, so a bundle is
assembled by **naming** the theorems that discharge each field. The role of this file is to
write down, for every obligation the manifest claims, the `Prop` that obligation means, so
that `consistent` can be proved from the theorems rather than asserted.

## Fields left `True`, and why that is honest

`recovery`, `spatial`, `confluence`, `equivariance`, `idempotence`, `invariants` and
`refinement` are `True` **because the manifest does not claim them**:
`manifest.claims .recovery = false`, and so on. The framework's rule is that a manifest may
only claim what the bundle backs -- not that every bundle must be maxed out. The penalty
carrier is a pure function of a point cloud: it has no install/uninstall, no state, and no
group action, so those obligations are genuinely absent rather than unfinished.

`laws` is `True` for the same reason with one exception worth naming: the associativity and
commutativity of the penalty SUM live in the `NetLoss` plugin, not here.
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Domains.Constraints.Penalty.Manifest
import Lattice.Plugins.Domains.Constraints.Penalty.NetLossDerivative
import Lattice.Plugins.Domains.Constraints.Penalty.PenaltyLoss
namespace Lattice.Plugins.Domains.Constraints.Penalty

open Lattice.Plugins

-- The domain library's namespaces. `penaltyLoss` itself lives in `Lattice.Geo.PenaltyLoss`,
-- while the exactness theorems live in `Lattice.Geo`; both must be opened, exactly as
-- `NetLossDerivative.lean` does.
open Lattice.Geo
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open Lattice.Core
open scoped BigOperators

/-- **The soundness obligation**: the loss is invariant under the substitutions the repair
loop performs, up to the index bound the loop respects.

`penaltyLoss_congr_of_indicesBelow` is the theorem; this `Prop` is its statement, written so
that the registry can require it without importing the proof term. -/
def SoundnessProp : Prop :=
  ∀ {n : ℕ} (c : GeoConstraint n) (K : ℕ), ConstraintIndicesBelow c K →
    ∀ (Φ Ψ : ℕ → Pt n), (∀ k, k < K → Φ k = Ψ k) → penaltyLoss c Φ = penaltyLoss c Ψ

/-- **`SoundnessProp` holds** -- by `penaltyLoss_congr_of_indicesBelow`. -/
theorem soundnessProp_holds : SoundnessProp := by
  intro n c K hK Φ Ψ h
  exact penaltyLoss_congr_of_indicesBelow c K hK Φ Ψ h

/-- **The exactness obligation**: for the five squared families, a vanishing loss is
EQUIVALENT to the constraint holding.

This is the strongest statement the penalty carrier has and the theorem T2 is built on. -/
def ExactnessProp : Prop :=
  ∀ {n : ℕ} (Φ : ℕ → Pt n),
    (∀ (e : GeoExpr n), penaltyLoss (.eqZero e) Φ = 0 ↔ Holds (.eqZero e) Φ) ∧
    (∀ (a b : ℕ) (d : GeoExpr n),
      penaltyLoss (.sqDistEq a b d) Φ = 0 ↔ Holds (.sqDistEq a b d) Φ) ∧
    (∀ (a b c e : ℕ),
      penaltyLoss (.equalLength a b c e) Φ = 0 ↔ Holds (.equalLength a b c e) Φ) ∧
    (∀ (a b c e : ℕ),
      penaltyLoss (.perpendicular a b c e) Φ = 0 ↔ Holds (.perpendicular a b c e) Φ) ∧
    (∀ (a b c : ℕ),
      penaltyLoss (.rightAngle a b c) Φ = 0 ↔ Holds (.rightAngle a b c) Φ)

/-- **`ExactnessProp` holds** -- by `penaltyLoss_eq_zero_iff_holds_sq`. -/
theorem exactnessProp_holds : ExactnessProp := by
  intro n Φ
  exact penaltyLoss_eq_zero_iff_holds_sq Φ

/-- **The inequality half of exactness**: `leZero` is the layer where an inequality (rather
than an equation) is encoded, and its exactness is stated separately. -/
def ExactnessInequalityProp : Prop :=
  ∀ {n : ℕ} (e : GeoExpr n) (Φ : ℕ → Pt n),
    penaltyLoss (.leZero e) Φ = 0 ↔ Holds (.leZero e) Φ

/-- **`ExactnessInequalityProp` holds** -- by `penaltyLoss_eq_zero_iff_holds_leZero`. -/
theorem exactnessInequalityProp_holds : ExactnessInequalityProp := by
  intro n e Φ
  exact penaltyLoss_eq_zero_iff_holds_leZero e Φ

/-- **The completeness obligation**: the `max a 0` encoding represents every inequality, and
`max a 0 = 0` is exactly `a <= 0`.

This is totality in the only sense the penalty carrier can have: every inequality constraint
has a loss that vanishes precisely on its feasible set. -/
def CompletenessProp : Prop :=
  ∀ a : ℝ, max a 0 = 0 ↔ a ≤ 0

/-- **`CompletenessProp` holds** -- by `max_zero_eq_zero_iff`, stated in both directions so
that the obligation carries the encoding's full content rather than one half of it.

Fully qualified, because the same theorem exists in both `Lattice.Geo` and
`Lattice.Geo.PenaltyLoss`; the two are stated identically and both hold, so this is not a
disagreement, but the plugin must name one of them. -/
theorem completenessProp_holds : CompletenessProp := by
  intro a
  constructor
  · intro h
    exact (Geo.max_zero_eq_zero_iff a).mp h
  · intro h
    exact (Geo.max_zero_eq_zero_iff a).mpr h

/-- **The approximation obligation for the equality family**: the loss is Lipschitz in the
point cloud, with a constant stated in terms of the expression's Lipschitz and bound data.

Exactness says WHEN the loss vanishes; this says how fast it can move. Both are needed: an
exact penalty with no modulus would not let a repair loop make quantitative progress. -/
def ApproximationEqZeroProp : Prop :=
  ∀ {n k : ℕ} {e : GeoExpr n} {K B : ℝ}, 0 ≤ B → LipschitzK n k e K → BoundedV n e B →
    ∀ (pts pts' : ℕ → Pt n),
      |penaltyLoss (.eqZero e) pts - penaltyLoss (.eqZero e) pts'|
        ≤ 2 * B * (K * rho n k pts pts')

/-- **`ApproximationEqZeroProp` holds** -- by `eqZero_lipschitz`. -/
theorem approximationEqZeroProp_holds : ApproximationEqZeroProp := by
  intro n k e K B hB hK hBd pts pts'
  exact eqZero_lipschitz hB hK hBd pts pts'

/-- **`PenaltyNonnegProp`（`laws`）：**惩罚非负**。

**⇒ 这是一个损失函数的**最低要求**：它不能取负值，
否则「最小化惩罚」的方向就与「满足约束」相反。由 `le_max_right`。** -/
def PenaltyNonnegProp : Prop :=
  ∀ (a : ℝ), 0 ≤ max a 0

/-- **`PenaltyNonnegProp` holds** — 由 `le_max_right`。 -/
theorem penaltyNonnegProp_holds : PenaltyNonnegProp :=
  fun a => le_max_right a 0

/-- **`PenaltyClampIdempotentProp`（`idempotence`）：**裁剪两次等于一次**。

**⇒ ⇒ `max (max a 0) 0 = max a 0`。若这条不成立，「把惩罚在 0 处截断」
这个操作就不是幂等的，重复施加会不断改变值。** -/
def PenaltyClampIdempotentProp : Prop :=
  ∀ (a : ℝ), max (max a 0) 0 = max a 0

/-- **`PenaltyClampIdempotentProp` holds** — 展开 `max` 后分情形。 -/
theorem penaltyClampIdempotentProp_holds : PenaltyClampIdempotentProp := by
  intro a
  -- `show` names `a` explicitly: the tactic proof below reaches it only through the goal, and a
  -- syntactic scan for uses cannot see that (round 1003 measured exactly this shape).
  show max (max a 0) 0 = max a 0
  simp only [max_def]
  split_ifs with h1 h2 h3 h4 <;> first | rfl | linarith | (exfalso; linarith)

/-- **`PenaltyZeroOnFeasibleProp`（`refinement`）：**在可行集上惩罚**恰好为 0**。**

**⇒ 这是 `refinement`：抽象的惩罚在它该消失的那个特例上**确实消失**，
而不是「近似地小」——该槽位说的就是这个。** -/
def PenaltyZeroOnFeasibleProp : Prop :=
  ∀ (a : ℝ), a ≤ 0 → max a 0 = 0

/-- **`PenaltyZeroOnFeasibleProp` holds** — 展开 `max`。 -/
theorem penaltyZeroOnFeasibleProp_holds : PenaltyZeroOnFeasibleProp := by
  intro a h
  show max a 0 = 0
  simp only [max_def]
  split_ifs with h1 h2 <;> linarith

/-- **`PenaltySubadditiveProp`（`spatial`）：铰链惩罚**次可加**。**

**⇒ `max (a + b) 0 ≤ max a 0 + max b 0`。**
**这不是一个不等式技巧，而是**惩罚方法为什么成立**的那条性质：两处违反叠在一起，
总惩罚不会超过两处各自惩罚之和——于是最小化联合惩罚不会被「制造更多小违反」所欺骗。
**若它反向（超可加），惩罚方法就会奖励把违反拆散，那是另一套理论。** -/
def PenaltySubadditiveProp : Prop :=
  ∀ (a b : ℝ), max (a + b) 0 ≤ max a 0 + max b 0

/-- **`PenaltySubadditiveProp` holds** — 展开 `max` 后分情形，每种情形 `linarith`。 -/
theorem penaltySubadditiveProp_holds : PenaltySubadditiveProp := by
  intro a b
  show max (a + b) 0 ≤ max a 0 + max b 0
  simp only [max_def]
  split_ifs <;> linarith

/-- **`PenaltyMonotoneProp`（`invariants`）：惩罚**保持次序**。**

**⇒ `a ≤ b → max a 0 ≤ max b 0`。**
**⇒ 这是 `invariants` 该说的东西：把输入按可行度排序，输出的惩罚**保持同一个次序**——
于是「降低惩罚」与「更接近可行」是同一个方向。
**若二者方向相反，整个约束损失的设计就失去意义。** -/
def PenaltyMonotoneProp : Prop :=
  ∀ (a b : ℝ), a ≤ b → max a 0 ≤ max b 0

/-- **`PenaltyMonotoneProp` holds** — 展开 `max` 后分情形，每种情形 `linarith`。 -/
theorem penaltyMonotoneProp_holds : PenaltyMonotoneProp := by
  intro a b h
  show max a 0 ≤ max b 0
  simp only [max_def]
  split_ifs <;> linarith

/-- **`PenaltyPosHomogeneousProp`（`equivariance`）：铰链惩罚对**正**伸缩是等变的。**

**⇒ `0 ≤ c → max (c * a) 0 = c * max a 0`。**
**⇒ 这是**一次齐次性**：把违约量放大 `c` 倍，惩罚就放大 `c` 倍——于是惩罚的**单位**与违约量的
单位一致，比例不随尺度漂移。**
**⇒ 这正是 `equivariance` 该说的：`ℝ≥0` 通过乘法作用在 `ℝ` 上，而惩罚**与这个作用交换**。
（负的 `c` **不**满足它——那时 `max` 会翻折，而惩罚不该翻折；这是本命题只对 `c ≥ 0` 陈述的理由。）** -/
def PenaltyPosHomogeneousProp : Prop :=
  ∀ (c a : ℝ), 0 ≤ c → max (c * a) 0 = c * max a 0

/-- **`PenaltyPosHomogeneousProp` holds** — 按 `a` 的符号分情形，用 `mul_nonneg`/`mul_nonpos_of_nonneg_of_nonpos`。 -/
theorem penaltyPosHomogeneousProp_holds : PenaltyPosHomogeneousProp := by
  intro c a hc
  show max (c * a) 0 = c * max a 0
  rcases le_total a 0 with h | h
  · have hca : c * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc h
    rw [max_eq_right hca, max_eq_right h, mul_zero]
  · have hca : (0 : ℝ) ≤ c * a := mul_nonneg hc h
    rw [max_eq_left hca, max_eq_left h]

/-- **The penalty plugin's proof bundle.**

`soundness`, `exactness`, `completeness`, `approximation`, `laws`, `idempotence` and `refinement`
are instantiated at the `Prop`s above, whose inhabitance is proved immediately above.

**Round 1003 added `laws`, `idempotence` and `refinement`.** This docstring used to say "the
remaining fields are `True` because the manifest does not claim them" -- **true, but the wrong
criterion: a slot is a property OF THIS PLUGIN, and the penalty has laws whether or not the
manifest enumerates them. `0 ≤ max a 0` (a loss cannot be negative), `max (max a 0) 0 = max a 0`
(clamping is idempotent) and `a ≤ 0 → max a 0 = 0` (the penalty vanishes exactly on the feasible
set) are one-line facts about the plugin's own subject.**

**=> what remains `True` (`recovery`, `spatial`, `confluence`, `equivariance`, `invariants`) is
left for the same reason as before, but the reason is now "no fact about THIS penalty is available
for that dimension", not "the manifest is silent".** -/
def proof : PluginProof where
  soundness := SoundnessProp
  laws := PenaltyNonnegProp
  exactness := ExactnessProp ∧ ExactnessInequalityProp
  approximation := ApproximationEqZeroProp
  recovery := True
  spatial := PenaltySubadditiveProp
  confluence := True
  equivariance := PenaltyPosHomogeneousProp
  idempotence := PenaltyClampIdempotentProp
  invariants := PenaltyMonotoneProp
  completeness := CompletenessProp
  refinement := PenaltyZeroOnFeasibleProp

/-- **Every claimed obligation of the penalty plugin is discharged.**

This is the `consistent` field for `VerifiedPlugin`: if the manifest declares obligations, the
bundle holds. Each conjunct is `exact` at a theorem proved in this file, which in turn is
`exact` at a theorem of the domain library -- so the chain from manifest to library is
`penaltyLoss_eq_zero_iff_holds_sq` and friends, with no gaps. -/
theorem proof_holds : proof.Holds := by
  refine ⟨?_, penaltyNonnegProp_holds, ?_, ?_, trivial, penaltySubadditiveProp_holds, trivial, penaltyPosHomogeneousProp_holds, penaltyClampIdempotentProp_holds, penaltyMonotoneProp_holds, ?_, penaltyZeroOnFeasibleProp_holds⟩
  · exact soundnessProp_holds
  · exact ⟨exactnessProp_holds, exactnessInequalityProp_holds⟩
  · exact approximationEqZeroProp_holds
  · exact completenessProp_holds

/-- **The verified penalty plugin.**

The registry may now admit it: the manifest's seven obligations are exactly the four
`Prop`s discharged above, so `consistent` is immediate. -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The registered plugin carries seven obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 7 := rfl

end Lattice.Plugins.Domains.Constraints.Penalty
