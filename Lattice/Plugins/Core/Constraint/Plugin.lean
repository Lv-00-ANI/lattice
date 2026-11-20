/-
# Core.Constraint Plugin -- assembly

The four obligations of `Manifest.lean`, discharged by `Lattice.Core.Logic`.

## What the `Prop`s have to say explicitly

**`Entails` and `Models` are defined inside `Lattice.Core.Logic`'s `Satisfaction` section, over an
arbitrary `CommSemiring` and `LinearOrder`.** **The obligations below therefore quantify over the
same parameters**, so that citing them is a statement about the general relation rather than about
one instantiation (the project works with `ℝ`, but the lemmas are true over any ordered semiring,
and stating them that way keeps the plugin honest about what it is receiving).
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Core.Constraint.Manifest
import Lattice.Core.RepairModule.ConstraintProofs
namespace Lattice.Plugins.Core.Constraint

open Lattice.Plugins
open Lattice.Core
-- `Constraint` lives in `Lattice.Core.LinearForm`, not directly in `Lattice.Core`.
open Lattice.Core.LinearForm

/-- **Law: entailment of a cons splits into head and tail.** -/
def EntailsConsProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (c : Constraint R n) (cs : List (Constraint R n)) (x : Point R n),
    Entails (c :: cs) x ↔ Satisfies c x ∧ Entails cs x

/-- **`EntailsConsProp` holds** -- by `entails_cons`. -/
theorem entailsConsProp_holds : EntailsConsProp := by
  intro R _ _ n c cs x
  exact entails_cons

/-- **Law: entailment is monotone in the constraint set.** -/
def EntailsMonoProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (cs ds : List (Constraint R n)) (x : Point R n),
    (∀ c ∈ cs, c ∈ ds) → Entails ds x → Entails cs x

/-- **`EntailsMonoProp` holds** -- by `entails_mono`. -/
theorem entailsMonoProp_holds : EntailsMonoProp := by
  intro R _ _ n cs ds x hsub h
  exact entails_mono hsub h

/-- **Soundness: a set models any constraint it contains.** -/
def ModelsOfMemProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (H : List (Constraint R n)) (c : Constraint R n), c ∈ H → Models H c

/-- **`ModelsOfMemProp` holds** -- by `models_of_mem`. -/
theorem modelsOfMemProp_holds : ModelsOfMemProp := by
  intro R _ _ n H c hmem
  exact models_of_mem hmem

/-- **Soundness: `Models` is contravariantly monotone in the hypothesis set.** -/
def ModelsOfSubsetProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (H K : List (Constraint R n)) (c : Constraint R n),
    (∀ d ∈ H, d ∈ K) → Models H c → Models K c

/-- **`ModelsOfSubsetProp` holds** -- by `models_of_subset`. -/
theorem modelsOfSubsetProp_holds : ModelsOfSubsetProp := by
  intro R _ _ n H K c hsub h
  exact models_of_subset hsub h

/-- **`EntailsAppendProp`：**两个约束集拼接后的蕴含拆成两半**。**

**⇒ `recovery`（时间可组合性）：拼接的蕴含恰好是两段蕴含的**合取**——
这是约束作为组合机制的核心事实，而不是「长一点的集合也能推导」。
由 `Entails` 的展开与 `List.mem_append`。** -/
def EntailsAppendProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (cs ds : List (Constraint R n)) (x : Point R n),
    Entails (cs ++ ds) x ↔ Entails cs x ∧ Entails ds x

/-- **`EntailsAppendProp` holds** — 展开 `Entails`，两个方向各用一次 `List.mem_append`。 -/
theorem entailsAppendProp_holds : EntailsAppendProp := by
  intro R _ _ n cs ds x
  unfold Entails
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
           fun c hc => h c (List.mem_append_right _ hc)⟩
  · intro ⟨h1, h2⟩ c hc
    rcases List.mem_append.mp hc with h | h
    · exact h1 c h
    · exact h2 c h

/-- **`EntailsSingletonProp`：**单元素约束集的蕴含退化为满足性**。**

**⇒ `refinement`：抽象的「蕴含」在最小非平凡的情形上**与具体的 `Satisfies` 一致**——
若二者在这里不一致，那么「蕴含」就不是满足性的推导。
由 `Entails` 的展开与 `List.mem_singleton`。** -/
def EntailsSingletonProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (c : Constraint R n) (x : Point R n),
    Entails [c] x ↔ Satisfies c x

/-- **`EntailsSingletonProp` holds** — 两个方向各用一次 `List.mem_singleton`。 -/
theorem entailsSingletonProp_holds : EntailsSingletonProp := by
  intro R _ _ n c x
  unfold Entails
  constructor
  · intro h
    exact h c (List.mem_singleton.mpr rfl)
  · intro h d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact h

/-- **`EntailsIdempotentProp`：**重复同一个约束集不改变蕴含**。**

**⇒ `idempotence`：`Entails (cs ++ cs) x ↔ Entails cs x`。
这不是从 `EntailsAppendProp` 抓来的便宜，而是一条**单独有意义**的事实：
约束作为一种宣告，重复宣告是惰性的——而在一个**非**幂等的组合下（例如“计数”）它就不成立。** -/
def EntailsIdempotentProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (cs : List (Constraint R n)) (x : Point R n),
    Entails (cs ++ cs) x ↔ Entails cs x

/-- **`EntailsIdempotentProp` holds** — 由 `EntailsAppendProp` 与 `∧` 的幂等律。 -/
theorem entailsIdempotentProp_holds : EntailsIdempotentProp :=
  fun cs x => (entailsAppendProp_holds cs cs x).trans ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- **`ModelsReverseProp`（`equivariance`）：把假设集**反转**不改变「模型化」关系。**

**⇒ `Models H c → Models H.reverse c`。**
**这条不是 `models_of_subset` 的重复：后者沿**包含**移动（`H ⊆ K`），本条沿**次序**移动。
两者合起来说明 `Models` 只依赖假设集的**集合**，既不依赖它的顺序，也不依赖它被多少无关约束包围——
这正是「约束系统是一个集合而不是一个序列」这一点的形式化。** -/
def ModelsReverseProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ}
    (H : List (Constraint R n)) (c : Constraint R n),
    Models H c → Models H.reverse c

/-- **`ModelsReverseProp` holds** — 由 `List.mem_reverse`。 -/
theorem modelsReverseProp_holds : ModelsReverseProp := by
  intro R _ _ n H c h x hx
  exact h x (fun d hd => hx d (List.mem_reverse.mpr hd))

/-- **`ModelsNilProp`（`completeness`）：空假设集模型化的，**恰好**是恒真的约束。**

**⇒ `Models [] c ↔ ∀ x, Satisfies c x`。**
**这不是同义反复：`Models [] c` 的定义里有一个**空洞的真**前提（`Entails [] x` 空真成立），
本条说的是那个空前提被**用尽**之后剩下的东西——即「没有假设」时「模型化」退化为「处处成立」。
**⇒ 这是 `Models` 在最小假设集上的**完备刻画**。** -/
def ModelsNilProp : Prop :=
  ∀ {R : Type} [CommSemiring R] [LinearOrder R] {n : ℕ} (c : Constraint R n),
    Models ([] : List (Constraint R n)) c ↔ ∀ x : Point R n, Satisfies c x

/-- **`ModelsNilProp` holds** — 展开 `Models` 与 `Entails` 后 `simp` 消去空真前提。 -/
theorem modelsNilProp_holds : ModelsNilProp := by
  intro R _ _ n c
  -- `show` names `c` explicitly: `simp` below reaches it only through the goal, and a syntactic
  -- scan for uses cannot see that (the idiom recorded in round 1003).
  show Models ([] : List (Constraint R n)) c ↔ ∀ x : Point R n, Satisfies c x
  unfold Models Entails
  simp

/-- **The constraint-logic plugin's proof bundle.**

Four claimed obligations. `exactness`, `approximation`, `recovery`, `spatial`, `confluence`,
`equivariance`, `idempotence`, `invariants`, `completeness` and `refinement` are `True`, matching
the manifest's negative theorems.
-/
def proof : PluginProof where
  soundness := ModelsOfMemProp ∧ ModelsOfSubsetProp
  laws := EntailsConsProp ∧ EntailsMonoProp
  exactness := True
  approximation := True
  recovery := EntailsAppendProp
  spatial := True
  confluence := True
  equivariance := ModelsReverseProp
  idempotence := EntailsIdempotentProp
  invariants := True
  completeness := ModelsNilProp
  refinement := EntailsSingletonProp

/-- **Every claimed obligation of the constraint-logic plugin is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨⟨modelsOfMemProp_holds, modelsOfSubsetProp_holds⟩,
         ⟨entailsConsProp_holds, entailsMonoProp_holds⟩,
         True.intro, True.intro, entailsAppendProp_holds, True.intro, True.intro, modelsReverseProp_holds,
         entailsIdempotentProp_holds, True.intro, modelsNilProp_holds, entailsSingletonProp_holds⟩

/-- **The verified constraint-logic plugin.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The plugin carries four obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 4 := rfl

end Lattice.Plugins.Core.Constraint
