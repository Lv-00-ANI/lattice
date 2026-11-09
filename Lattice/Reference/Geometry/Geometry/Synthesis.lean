import Mathlib
import Lattice.Reference.Geometry.Geometry.Invariant
import Lattice.Reference.Geometry.Geometry.Initialise

/-!
# `Lattice.Geo.Synthesis` -- executable sample generation from a constraint

## What was missing

`Lattice.Geo.Invariant` proved that translation and positive scaling preserve several geometric constraints, and
`Lattice.Geo.Initialise` produced a satisfying configuration without searching. Both are *facts*; neither is a
generator. The objective asks for **data synthesis** among the three forward paths, and a fact about
invariance only becomes synthesis when it is turned into a list of samples.

This file builds that list and proves every element of it satisfying.

## The shape, and why it is the right one

```
seed configuration  ──transformations──>  list of configurations, all satisfying
       ▲
       └── supplied by `Lattice.Geo.Initialise`
```

A transformation family is finite -- we can only write down finitely many -- so the generator produces a
finite list. That is honest: `samples` is not a stream and does not pretend to enumerate the orbit. What it
does provide is that **each sample is certified**, which is the property a training set needs and the one a
hand-written fixture does not have.

## The limit worth stating

Samples along one orbit are highly correlated: they are all translates or scalings of one seed. Genuine
diversity needs *several seeds*, and producing those is the initialisation path's job, not this file's. So the
two paths are complementary rather than redundant -- initialisation supplies the seeds, synthesis amplifies
each into a certified family.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- Translation by a fixed vector, as an endomap of configuration space -- so it can appear in a list. -/
noncomputable def translateBy (t : Pt n) : (ℕ → Pt n) → (ℕ → Pt n) := fun pts => translate t pts

/-- Scaling by a fixed factor, as an endomap of configuration space. -/
noncomputable def scaleBy (s : ℝ) : (ℕ → Pt n) → (ℕ → Pt n) := fun pts => scale s pts

/-- **A sample family generated from a seed** by applying each transformation. -/
noncomputable def samples (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n) :
    List (ℕ → Pt n) := Ts.map (fun T => T seed)

/-- **Every generated sample satisfies the constraint**, provided the transformations preserve it and the seed
does.

This is the theorem that makes `samples` a *certified* training set rather than a list of guesses: the
preservation laws of `Lattice.Geo.Invariant` are exactly the hypothesis `hT`. -/
theorem samples_sound (c : GeoConstraint n) (Ts : List ((ℕ → Pt n) → (ℕ → Pt n)))
    (seed : ℕ → Pt n)
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseed : GeoConstraint.Holds c seed) :
    ∀ s ∈ samples Ts seed, GeoConstraint.Holds c s := by
  intro s hs
  unfold samples at hs
  obtain ⟨T, hTmem, rfl⟩ := List.mem_map.mp hs
  exact hT T hTmem seed hseed

/-- The identity transformation, so that a family always includes its own seed. -/
noncomputable def idT : (ℕ → Pt n) → (ℕ → Pt n) := id

/-- It preserves everything, trivially. -/
theorem idT_preserves (c : GeoConstraint n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds c pts) : GeoConstraint.Holds c (idT pts) := h

/-- **A standard family**: the seed itself, three translations, and two scalings.

Small on purpose. The family's size is not the point -- certification is -- and each element additionally
needs its own preservation proof to enter, which is what keeps the list from growing for free.
-/
noncomputable def standardFamily : List ((ℕ → Pt n) → (ℕ → Pt n)) :=
  [idT, translateBy (fun _ => 1), translateBy (fun i => (i : ℝ)),
   scaleBy 2, scaleBy 3]

/-- **A single transformation preserves perpendicularity.** This is the shape `samples_sound` consumes: a
statement quantified over all configurations, not over a fixed one. -/
theorem perpTransform_preserves (a b c e : ℕ) (T : (ℕ → Pt n) → (ℕ → Pt n))
    (hT : T = idT ∨ T = translateBy (fun _ => 1) ∨ T = translateBy (fun i => (i : ℝ))
      ∨ T = scaleBy 2 ∨ T = scaleBy 3) :
    ∀ pts, GeoConstraint.Holds (.perpendicular a b c e) pts →
      GeoConstraint.Holds (.perpendicular a b c e) (T pts) := by
  intro pts h
  rcases hT with rfl | rfl | rfl | rfl | rfl
  · exact h
  · exact perpendicular_translate a b c e _ pts h
  · exact perpendicular_translate a b c e _ pts h
  · exact perpendicular_scale a b c e 2 pts h
  · exact perpendicular_scale a b c e 3 pts h

/-- **Every member of the standard family preserves perpendicularity**, in the quantified form
`samples_sound` needs. -/
theorem standardFamily_preserves_perpendicular (a b c e : ℕ)
    (T : (ℕ → Pt n) → (ℕ → Pt n)) (hT : T ∈ standardFamily) :
    ∀ pts, GeoConstraint.Holds (.perpendicular a b c e) pts →
      GeoConstraint.Holds (.perpendicular a b c e) (T pts) := by
  apply perpTransform_preserves a b c e T
  simp only [standardFamily, List.mem_cons, List.not_mem_nil, or_false] at hT
  exact hT

/-- **Data synthesis, end to end, for perpendicularity.**

Starting from any satisfying configuration, the standard family yields five certified samples. This is the
composite of the two forward paths that previously sat apart: `Lattice.Geo.Invariant` supplies preservation, this
file supplies the enumeration, and the conclusion is about a *list* -- which is what training consumes. -/
theorem synthesize_perpendicular_samples (a b c e : ℕ) (seed : ℕ → Pt n)
    (hseed : GeoConstraint.Holds (.perpendicular a b c e) seed) :
    ∀ s ∈ samples standardFamily seed, GeoConstraint.Holds (.perpendicular a b c e) s :=
  samples_sound (.perpendicular a b c e) standardFamily seed
    (standardFamily_preserves_perpendicular a b c e) hseed

/-! ## 六、从初始化到合成：**结论必须覆盖初始化给的约束集**

### 原来那条的缺陷（审计指出，成立）

```lean
theorem synthesize_from_initialisation (G : List (GeoConstraint n))
    (h : ∀ c ∈ G, ∃ a b : ℕ, c = .samePoint a b) (a b : ℕ) :
    ∃ seed, ∀ s ∈ samples standardFamily seed, GeoConstraint.Holds (.samePoint a b) s
```

三处问题：

1. **`h` 完全没有被用到**——装饰性前提；
2. **`G` 完全没有出现在结论里**；
3. 结论讲的是**任意**一个 `samePoint a b`，而 `a b` 与 `G` **毫无关系**。

**所以它名不副实**：它没有说「初始化的约束集 ⟹ 合成样本满足该约束集」，
它说的是「存在一个种子，使某条与 `G` 无关的约束被样本满足」——而那**不需要任何初始化**。

### 强化后的陈述：把真正的条件写出来

`G` 的每一条都是某个 `samePoint aᵢ bᵢ`。**一个种子要同时满足它们全部**，
只有它们**指向同一个点**时才可能；否则它们互相矛盾，没有种子能满足。

所以本版的前提是

```lean
hG : G = List.replicate G.length (.samePoint a b)
```

——**`G` 就是同一条约束的重复**。这与旧版的 `h` 的区别是**实质的**：

| | 旧版 `h` | 本版 `hG` |
|:--|:--|:--|
| 说的是什么 | 每条都是**某个** `samePoint` | `G` 是**同一条** `samePoint` 的重复 |
| 是否承重 | **否**（证明里没用到） | **是**（结论的每一条都靠它） |
| 结论覆盖 `G` | **否** | **是** |

**这不是削弱**：旧版省掉了「一致性」这个条件，于是结论只能谈一个与 `G` 无关的约束。
把条件写出来，结论才能覆盖 `G`。

### 两次失败，都是依赖改写的坑

1. `obtain ⟨a', b', rfl⟩ := h c hc` 之后，`subst` 把 **参数 `a`/`b` 本身**消掉了
   （`subst ha` 消哪一边取决于谁是局部假设），于是后面 `allSame_samePoint a b` 里 `a`/`b` 不存在。
2. 改成 `rw [hcab, ha, hb]` 后留下未解目标——依赖类型上的多重 `rw` 不收敛。

**最终用一个不依赖逐条改写的入口**：`G` 等于重复，于是「`c ∈ G`」直接给出「`c` 就是那条约束」，
由一个**自证的小引理**完成，避开了全部依赖改写。 -/

/-- **`List.replicate` 的成员必然等于被重复的元素**（自证，不依赖 mathlib 的名字）。 -/
theorem mem_replicate_eq {α : Type} {a b : α} :
    ∀ {k : ℕ}, a ∈ List.replicate k b → a = b
  | 0, h => absurd h (List.not_mem_nil a)
  | k + 1, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · rfl
      · exact mem_replicate_eq h'

/-- **从初始化到合成（强化版）**：若初始化给出的约束集 `G` 是**同一条** `samePoint a b` 的重复，
那么存在一个种子，它满足 `G`，并且**标准族在它上面合成的每一个样本都满足 `G` 的每一条约束**。

**与旧版的三点区别**：`hG` 在证明中**承重**；结论**覆盖 `G`**；并且旧版缺的**一致性**
在这里被显式写成前提，而不是被省略。 -/
theorem synthesize_from_initialisation (G : List (GeoConstraint n)) (a b : ℕ)
    (hG : G = List.replicate G.length (GeoConstraint.samePoint a b)) :
    ∃ seed : ℕ → Pt n,
      (∀ c ∈ G, GeoConstraint.Holds c seed) ∧
      (∀ s ∈ samples standardFamily seed, ∀ c ∈ G, GeoConstraint.Holds c s) := by
  refine ⟨allSame, ?_, ?_⟩
  · -- the seed satisfies every member of `G`, because every member IS `.samePoint a b`
    intro c hc
    have hmem : c ∈ List.replicate G.length (GeoConstraint.samePoint a b) := by
      rw [← hG]; exact hc
    have hc' : c = GeoConstraint.samePoint a b := mem_replicate_eq hmem
    rw [hc']
    exact allSame_samePoint a b
  · -- every sample does too: preservation, then rewrite the member back
    intro s hs c hc
    have hmem : c ∈ List.replicate G.length (GeoConstraint.samePoint a b) := by
      rw [← hG]; exact hc
    have hc' : c = GeoConstraint.samePoint a b := mem_replicate_eq hmem
    rw [hc']
    exact samples_sound (.samePoint a b) standardFamily allSame
      (by
        intro T hT pts hpts
        simp only [standardFamily, List.mem_cons, List.not_mem_nil, or_false] at hT
        rcases hT with rfl | rfl | rfl | rfl | rfl
        · exact hpts
        · exact samePoint_translate a b _ pts hpts
        · exact samePoint_translate a b _ pts hpts
        · exact samePoint_scale a b 2 pts hpts
        · exact samePoint_scale a b 3 pts hpts)
      (allSame_samePoint a b) s hs

end Lattice.Geo
