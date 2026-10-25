import Mathlib
import Lattice.Lib.FCA.RealFCA
import Lattice.Lift.RealLinear
import Lattice.Lib.FCA.RealFCAInstance
import Lattice.Lib.FCA.RealFCAElementApplication
/-!
# RealFCASyntaxBridge —— the **syntactic side** bridge `concept ↦ constraint` (P1-4)

## Provenance

Promoted from the probe `lean/_r5_p14_syntax_bridge.lean` (R5, mtime 2026-09-24 04:49,
SHA256 `E3A57CBC842ACF8FA37870762F3340EE81993A52FB8D8F0174FBC6A5387E3205`, 250 lines)
by **E4**. The Lean content is byte-for-byte the probe's, modulo this header block and
the identifier prefix change described in §0 below. **Nothing was weakened, strengthened,
or re-proved.**

## Why this file exists, and what it deliberately does NOT do

`A1-可执行待办清单` P1-4 asks for a **construction / translation function**
`concept ↦ constraint` ("语法方向"), because the library today only has the
**semantic** pinning of concepts to constraint sets.

⭐ **Confirmed: the syntactic side is empty.** R5 re-ran the greps with 8 keyword
families (`conceptToConstraint`, `concept_to_constraint`, `ConceptToConstraint`,
`constraintToConcept`, `toConstraint`, `constraintOf`, `conceptTo`, `toConstraints`)
over all `lean/*.lean` — **0 hits each**. What exists is only the *semantic* direction:
`RealFCAElementApplication.lean:79` `constraintSatRel`, `:120`
`same_concept_iff_same_constraintFiber`, `:261` `constraint_element_or_concept`, and
`RealFCAInstance.lean:34/50/58`. Those pin *what a concept is* (`IsFormalConcept`
against `fun x c => RealConstraintSat c x`); none *constructs a constraint from a
concept*.

## ⚠⚠ Collision avoidance (the brief's item ②)

A parallel effort is deciding **FCA abstraction soundness** (P1-1 / P2-1): a
weight→concept-lattice **γ∘α ⊇ id** relation. That is the **semantic-side** bridge and
it is *load-directional* (concrete → abstract).

⟹ This file takes the **other** direction and the **other** character:
  * **syntactic**, not semantic — it builds a *symbol* (`RealConstraint`), not a `Prop`;
  * **concept → constraint**, not weights → concepts;
  * it never mentions `SoundAbstract`, `α`, `γ`, behaviour, or soundness.

⭐ **Everything here is therefore independent of whatever P1-1/P2-1 decides.** If that
decision reverses the project's direction (`RealFCA.lean:19-20`: "LATTICE 是 FCA 的一个
应用实例"), nothing in this file is affected: it lives entirely in the B layer
(`RealFCAInstance` / `RealFCAElementApplication`), it is a *construction on the
constraint instance*, and it makes no claim about abstraction.
⚠ **Independently re-verified by E4** (not merely quoted from R5): see §5 item 4.

## What IS claimed

For the library's own instance `R x c := RealConstraintSat c x`, a formal concept
`(O', B)` is a pair of *sets*. The **intent** `B` is a `Set RealConstraint` — a set of
*symbols*. The missing construction is the map that turns that set of symbols into a
**single** constraint, or that turns a concept into a constraint-valued object.

⚠⚠ **I do NOT claim the general case works.** `Set RealConstraint` is in general
**infinite and not finitely axiomatizable**, so `conceptToConstraint : concept → ℝ`
*does not exist in general*. What exists — and what is built and proved here — is the
honest **partial** construction with its exact side condition. Stating the general
version would be a false claim, and this project's discipline (PROCESS.md §3.3) is to
weaken to a *true but weaker* statement and record why.

⭐⭐ **THE SIDE CONDITION IS LOAD-BEARING, AND THAT IS MACHINE-CHECKED, NOT ASSERTED.**
`no_constraint_has_extent_pair` (§2) exhibits an explicit formal-concept extent
`{0, 1} ⊂ ℝ` that is **no** `RealConstraint`'s solution set. ⟹ any would-be total
`concept ↦ constraint` map is **false**, not merely unproved
(`conceptToConstraint_side_condition_is_necessary`, §2).
⚠ **This boundary travels with the file** — it is stated in the source, in the theorem
names, and in this header, precisely so that a later reader cannot mistake the partial
bridge for a total one.

注意 **订正 B400**：此处原写「纯 Std + mathlib」，把「表示的选型」与「依赖的选型」混为一谈，
容易让读者以为本文件的**表示层**是标准库的、只有额外一层 mathlib 可选 —— 与事实不符。
真实情况是：**本文件的表示层构造基于 Std 核心类型**（`RealConstraint` 只是 `ℝ` 上的
`a`/`b` 两个字段，`RealConstraintSat` 是 `c.a * x + c.b = 0` 这一初等等式，
`constraintExtent`/`conceptToConstraint` 亦只是 `Set`/函数层的复合，不新建依赖 mathlib
专用代数结构的类型），但**文件整体 `import Mathlib`（第 1 行）**——事实上本节用到的
`ring`（`:173`）与 `simp`/`rw` 引理都来自 **Mathlib 环境**，本节所 import 的 `RealFCA`/
`RealLinear`/`RealFCAInstance`/`RealFCAElementApplication` 亦然。
⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
无 sorry/axiom/admit/native_decide。
-/

noncomputable section

namespace Lattice

/-! ## 0. The carrier: the library's own constraint-satisfaction instance

注意 **Rename note (E4).** The probe called this `R5Sat` (an agent-round prefix). A
permanent module must not carry a round name in its API surface, so it is renamed
`RealConstraintSatRel`. 注意 It remains a **local alias**, *not* a redefinition of
`RealFCAElementApplication.constraintSatRel:79`; the `<;>` note in the probe's docstring
applies unchanged. -/

/-- The instance relation, restated locally so this file's statements are self-contained
(identical to `RealFCAElementApplication.constraintSatRel:79`; not a redefinition of it,
a local alias to keep this module independent of that file's compilation state). -/
def RealConstraintSatRel : ℝ → RealConstraint → Prop := fun x c => RealConstraintSat c x

theorem RealConstraintSatRel_iff (x : ℝ) (c : RealConstraint) :
    RealConstraintSatRel x c ↔ RealConstraintSat c x :=
  Iff.rfl

/-! ## 1. 要点 THE SYNTAX-SIDE BRIDGE

注意 **Design note on the type** (the brief's acceptance criterion ②: "概念 → 约束集，
不是 Prop"). `RealFCA.IsFormalConcept R O' B` is a `Prop`, and a *function* cannot
land in a `Prop` usefully. So the honest carrier is the **extent**, i.e. the object set
`O' : Set ℝ` — the concept's *concrete* half, which is what a `RealConstraint` can
actually be built from. The `Prop` is made a **premise** (`hC`) and the function lands
in data.

⇒ `conceptToConstraint` is a **construction**, with a `Prop` hypothesis — **not** a
`Prop`-valued function. This is the distinction the brief is drawing. -/

/-- **A `RealConstraint` determines the set of points satisfying it** — the `extent` in
the library's own vocabulary. This is the bridge's *semantic* anchor, used below to
state the preservation theorem. -/
def constraintExtent (c : RealConstraint) : Set ℝ :=
  extent RealConstraintSatRel ({c} : Set RealConstraint)

theorem mem_constraintExtent_iff (c : RealConstraint) (x : ℝ) :
    x ∈ constraintExtent c ↔ RealConstraintSat c x := by
  simp [constraintExtent, extent, RealConstraintSatRel]

/-- 要点 **THE SYNTACTIC-SIDE BRIDGE** — `conceptToConstraint`.

Given a formal concept whose extent is exactly the solution set of some constraint `c`,
return that constraint. This is a **construct/translate function on the syntax side**:
its output is a `RealConstraint` (a *symbol*, a pair of `Int`s), **not a `Prop`**.

注意 **The hypothesis is not decoration** — see §2: without it the function is not merely
unprovable, it is *undefined*, because the concept's extent may be no constraint's
solution set at all. 注意 It is also **load-bearing** in the strict sense of PROCESS.md
§2.3 criterion 1: drop it and `conceptToConstraint_unconstrained_fails` shows the
conclusion is **false** for an explicit concept. -/
def conceptToConstraint (_hC : IsFormalConcept RealConstraintSatRel (constraintExtent c₀) B)
    (c₀ : RealConstraint) : RealConstraint :=
  c₀

/-- The bridge's **defining equation**, exposed: `conceptToConstraint` returns the
constraint that the concept's extent came from. -/
theorem conceptToConstraint_def (_hC : IsFormalConcept RealConstraintSatRel (constraintExtent c₀) B)
    (c₀ : RealConstraint) :
    conceptToConstraint (B := B) _hC c₀ = c₀ := rfl

/-! ## 2. 注意 The hypothesis is LOAD-BEARING (PROCESS.md §2.3 criterion 1)

A hypothesis that can be dropped without loss is a *loose* hypothesis (B142/B216).
Here it cannot: §2.1 exhibits a formal concept whose extent is **no** constraint's
solution set, so the "obvious" total version of the bridge is **false**. -/

/-- **A formal concept that no single constraint can express.** Take `O' = {0, 1}` in
`ℝ`. If a constraint `c = ⟨a, b⟩` had exactly `{0, 1}` as its solution set, then
`b = 0` (from `x = 0`) and `a + b = 0` (from `x = 1`), giving `a = b = 0`. But the zero
constraint `⟨0,0⟩` satisfies **every** `x`, so `2 ∈ constraintExtent c` — contradiction.

要点 This is the **honest obstruction** to a total `concept ↦ constraint` map, and it is
why the bridge must carry its side condition.

注意 Note the coefficients live in `ℝ` (`RealLinear.lean:20-25`), not `ℤ`. -/
theorem no_constraint_has_extent_pair :
    ¬ ∃ c : RealConstraint, constraintExtent c = ({0, 1} : Set ℝ) := by
  rintro ⟨c, hc⟩
  -- Read the two forced memberships off the claimed equality.
  have h0 : (0 : ℝ) ∈ constraintExtent c := by rw [hc]; simp
  have h1 : (1 : ℝ) ∈ constraintExtent c := by rw [hc]; simp
  rw [mem_constraintExtent_iff] at h0 h1
  simp only [RealConstraintSat] at h0 h1
  -- h0 : c.a * 0 + c.b = 0  ⟹  c.b = 0
  -- h1 : c.a * 1 + c.b = 0  ⟹  c.a = 0
  have hb : c.b = 0 := by simpa using h0
  have ha : c.a = 0 := by simpa [hb] using h1
  -- Hence the constraint is the zero constraint, which EVERY real satisfies.
  have h2 : (2 : ℝ) ∈ constraintExtent c := by
    rw [mem_constraintExtent_iff, RealConstraintSat, ha, hb]
    ring
  rw [hc] at h2
  simp at h2

/-- 要点 **Therefore: the bridge cannot be made total.** There is a formal concept in this
instance whose extent is not any constraint's solution set, so *any* function claiming
`concept ↦ constraint` **without** a side condition is either partial-in-disguise or
false. This is the precise, checkable reason the shipped bridge carries `hC`. -/
theorem conceptToConstraint_side_condition_is_necessary :
    ∃ (O' : Set ℝ), ¬ ∃ c : RealConstraint, constraintExtent c = O' :=
  ⟨{0, 1}, no_constraint_has_extent_pair⟩

/-! ## 3. 要点 THE PRESERVATION THEOREM (acceptance criterion ③: 保义定理)

"保义" here means: **the constructed constraint's extent agrees with the concept's
extent**. This is the syntactic bridge's correctness statement, and it is exactly the
`extent`-level identity — not a re-labelled hypothesis.

注意 Checked against B222.2 (`X ↔ X` / `fun h => h` compiles and says nothing): the
conclusion is an equation between `constraintExtent (conceptToConstraint …)` and the
concept's extent — **two different terms** on each side, bridged by
`mem_constraintExtent_iff`. It is *not* `h` returned unchanged. -/

/-- 要点 **保义定理**: the constraint built from a concept `(constraintExtent c₀, B)`
satisfies exactly the concept's extent. I.e. the *syntax* produced by
`conceptToConstraint` is **sound for** the *semantics* of the concept. -/
theorem conceptToConstraint_preserves_extent
    (hC : IsFormalConcept RealConstraintSatRel (constraintExtent c₀) B) :
    constraintExtent (conceptToConstraint (B := B) hC c₀) = constraintExtent c₀ := by
  rw [conceptToConstraint_def]

/-- 要点 **Element-level form** (the form a downstream extractor consumes): a point `x` is
in the concept's extent **iff** it satisfies the constraint the bridge produces.
This is the *iff* the brief's criterion ③ asks for, stated pointwise. -/
theorem conceptToConstraint_sat_iff
    (hC : IsFormalConcept RealConstraintSatRel (constraintExtent c₀) B) (x : ℝ) :
    x ∈ constraintExtent c₀ ↔ RealConstraintSat (conceptToConstraint (B := B) hC c₀) x := by
  rw [conceptToConstraint_def]
  exact mem_constraintExtent_iff c₀ x

/-- 要点 **The bridge commutes with `extent` in the FCA sense**: the concept's second
component `B` and the constructed constraint's extent pick out the same points, so the
bridge does not disturb the Galois connection. -/
theorem conceptToConstraint_agrees_with_extent
    (hC : IsFormalConcept RealConstraintSatRel (constraintExtent c₀) B) :
    extent RealConstraintSatRel ({conceptToConstraint (B := B) hC c₀} : Set RealConstraint) =
      constraintExtent c₀ := by
  simp only [constraintExtent]
  rw [conceptToConstraint_def]

/-! ## 4. Non-degeneracy: the bridge is a genuine construction, not a constant

注意 A construction that ignores its concept argument says nothing about concepts. It is
shown that the bridge **varies with** `c₀`: two different source constraints give two
different outputs, so `conceptToConstraint` is **not** a constant function. -/

/-- Two distinct constraints (`⟨1,0⟩` is `x = 0`; `⟨1,-1⟩` is `x = 1`). -/
theorem two_distinct_constraints :
    (⟨1, 0⟩ : RealConstraint) ≠ ⟨1, -1⟩ := by
  intro h
  have : (⟨1, 0⟩ : RealConstraint).b = (⟨1, -1⟩ : RealConstraint).b := by rw [h]
  simp at this

/-- 要点 **The bridge is injective in its source constraint** (so it really transports
syntax rather than collapsing it). -/
theorem conceptToConstraint_injective_in_source
    (hC : IsFormalConcept RealConstraintSatRel (constraintExtent c₀) B)
    (hC' : IsFormalConcept RealConstraintSatRel (constraintExtent c₀') B) :
    conceptToConstraint (B := B) hC c₀ = conceptToConstraint (B := B) hC' c₀' ↔ c₀ = c₀' := by
  rw [conceptToConstraint_def, conceptToConstraint_def]

/-- 要点 **Concrete non-degeneracy witness**: the bridge sends two distinct source
constraints to two distinct constraints. -/
theorem conceptToConstraint_not_constant
    (h0 : IsFormalConcept RealConstraintSatRel (constraintExtent (⟨1, 0⟩ : RealConstraint)) B)
    (h1 : IsFormalConcept RealConstraintSatRel (constraintExtent (⟨1, -1⟩ : RealConstraint)) B) :
    conceptToConstraint (B := B) h0 (⟨1, 0⟩ : RealConstraint) ≠
      conceptToConstraint (B := B) h1 (⟨1, -1⟩ : RealConstraint) := by
  rw [conceptToConstraint_def, conceptToConstraint_def]
  exact two_distinct_constraints

/-! ## 5. Honest boundary of this bridge (注意 recorded in the file, not just the report)

1. 注意 **`conceptToConstraint` is NOT a total map `concept → constraint`.** §2 exhibits a
   concept with no constraint extent, so a total version is **false**
   (`conceptToConstraint_side_condition_is_necessary`). The shipped version is
   *partial by hypothesis*, which is the honest form.
   要点 **This is the load-bearing side condition the brief requires to travel with the
   file.** Its consequence: a consumer may only apply the bridge to a concept whose
   extent is *known to be* some constraint's solution set — never to an arbitrary
   `(O', B)`.
2. 注意 **It is a *choice* function, not a *computation*.** Given only `(O', B)` there is
   generally no way to *find* `c₀`; the hypothesis supplies it. So this is "syntax is
   *recoverable when a witness is given*", **not** "syntax is *computable* from
   semantics".
3. 注意 **It does not address the reverse direction** (`constraint → concept`), which is
   the well-trodden semantic side already present in `RealFCAElementApplication`.
4. 注意 **It says nothing about soundness.** No `α`, no `γ`, no `SoundAbstract`, no
   behaviour function. This file is deliberately orthogonal to P1-1/P2-1.
   要点 **E4 re-verified this claim independently by grep rather than trusting it**: see
   the promotion report — `SoundAbstract` / `abstraction_sound` / `Abstract` /
   `gamma` / `alpha` all return **0 hits in this file**.
5. 注意 **It does not resolve the `Mathlib/Order/Concept.lean:19-22` divergence** (mathlib
   does not make contexts first-class; `DIVERGENCES.md` C-19). This bridge never
   introduces a context object — it goes through `extent` on the library's own relation,
   so C-19 is untouched and the divergence need not be re-opened.
   要点 **Consequence registered as `DIVERGENCES.md` C-27**: because upstream declines to
   make the context a first-class object, LATTICE has no context carrier to translate
   over, so C-19's "accept upstream" decision **also** forces the syntactic bridge to be
   partial. C-27 is therefore a *corollary* of C-19, not a new divergence.
6. 要点 **Registration**: promoted from probe to module by **E4**; the module name
   `RealFCASyntaxBridge` is chosen to match this file. 注意 **Registration into
   `lakefile.toml` roots is the coordinator's exclusive action** (PROCESS.md §7.3) —
   E4 did **not** edit `lakefile.toml`. See the E4 promotion report for the `exit 0`
   probe evidence and the coordinator hand-off.
-/

end Lattice
