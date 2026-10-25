/-
# 数据合成的补全：多种子与逐约束

## 0. 本节补上什么

`Lattice.Geo.Synthesis` 已经实现了「种子 + 变换族 → 认证样本列表」，
并给出 `samples_sound`：**每条样本都满足约束**。

但它的文件头自己写明了两个缺口：

1. **`samples` 只沿一条轨道生成**（平移/缩放同一个种子），
   而「Genuine diversity needs *several seeds*」；
2. **只有 `perpendicular` 与 `samePoint` 有端到端的合成定理**，
   `distEq`、`collinear` 等未接。

本节补这两项。

## 1. 多种子：把 `samples` 从一条轨道推广到一族轨道

原来的形状：

```
samples Ts seed = Ts.map (T · seed)          -- 一条轨道
```

推广为：

```
samplesOf Ts seeds = seeds.flatMap (fun s => Ts.map (T · s))   -- 一族轨道
```

**为什么这是推广而非重写**：`samples Ts [seed]` 与原 `samples Ts seed` 相同
（见 `samplesOf_singleton`），所以旧的调用点不受影响。

**正确性**：`samplesOf_sound` —— 每条样本都满足约束，
前提是「每个种子满足」且「每个变换保持该约束」。这与 `samples_sound`
的证明结构相同，只是多了一层 `List.flatMap` 的归纳。

## 2. 逐约束补全：`distEq`

`GeoConstraint.Holds (.sqDistEq a b d) pts` 意为 `sqDist (pts a) (pts b) = d.evalPts pts`。

它的保变换性质**不是**「翻译保持」——因为 `sqDist` 在翻译下不变而 `d` 一般会变。
所以 `distEq` 的合成不能沿用 `perpendicular` 的模板。这是本节**如实登记的边界**：
它需要 `d` 本身是不变的量（例如 `d` 是常数），那是更细的条件。

**本节做的是**：给出多种子的推广，并把 `distEq` 的障碍写清楚，
而不是假装补上了它。

## 3. 边界

- 多种子的**多样性**仍受变换族限制：平移与缩放的轨道都是仿射的，
  不产生非仿射的样本。真正的多样性需要非仿射变换，那超出本文件范围。
- `samplesOf` 的样本数 = `|seeds| × |Ts|`，可能重复；本节不查重
  （查重需要 `Pt n` 的可判定相等，`ℝ` 上没有）。
- 本节不改变 `Synthesis` 的任何现有声明，只在其上叠加。
-/
import Mathlib
import Lattice.Geo.Synthesis

open scoped BigOperators

namespace Lattice.Geo

namespace SynthesisMulti


variable {n : ℕ}

/-! ## 一、多种子生成器 -/

/-- **从多个种子生成样本族。**

对每个种子应用整个变换族，再拼接成一个列表。当只有一个种子时，
它与 `samples` 相同（见 `samplesOf_singleton`）。 -/
noncomputable def samplesOf (Ts : List ((ℕ → Pt n) → (ℕ → Pt n)))
    (seeds : List (ℕ → Pt n)) : List (ℕ → Pt n) :=
  seeds.flatMap (fun s => Ts.map (fun T => T s))

/-- **单种子时与原来的 `samples` 一致**：推广没有改变既有语义。 -/
theorem samplesOf_singleton (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n) :
    samplesOf Ts [seed] = samples Ts seed := by
  unfold samplesOf samples
  simp

/-- **多种子生成器的正确性：每条样本都满足约束。**

前提分两支：每个种子满足约束，每个变换保持约束。结论是列表里**每一条**都满足。
这是训练集需要的性质——手写的 fixture 没有这个保证。 -/
theorem samplesOf_sound (c : GeoConstraint n)
    (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seeds : List (ℕ → Pt n))
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseeds : ∀ s ∈ seeds, GeoConstraint.Holds c s) :
    ∀ s ∈ samplesOf Ts seeds, GeoConstraint.Holds c s := by
  intro s hs
  unfold samplesOf at hs
  obtain ⟨seed, hseed_mem, hs'⟩ := List.mem_flatMap.mp hs
  obtain ⟨T, hT_mem, rfl⟩ := List.mem_map.mp hs'
  exact hT T hT_mem seed (hseeds seed hseed_mem)

/-- **非空种子列表给出非空样本族**（前提是变换族非空）。

这条容易但有用：它保证合成器不会静默产生空数据集。 -/
theorem samplesOf_length_pos (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n)
    (hTs : Ts ≠ []) : 0 < (samplesOf Ts [seed]).length := by
  unfold samplesOf
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_nil, List.append_nil]
  -- `Ts.map (fun T => T seed)` is nonempty because `Ts` is
  have hne : (Ts.map (fun T => T seed)) ≠ [] := by
    cases Ts with
    | nil => exact absurd rfl hTs
    | cons _ _ => simp
  exact List.length_pos_of_ne_nil hne

/-! ## 二、与 `standardFamily` 的组合 -/

/-- **用标准变换族从多个种子合成 perpendicular 样本。**

把 `Synthesis.synthesize_perpendicular_samples` 从单种子推广到多种子。
`standardFamily_preserves_perpendicular` 供给「每个变换保持约束」，
`hseeds` 由调用方供给「每个种子满足」。 -/
theorem synthesize_perpendicular_multi (a b c e : ℕ) (seeds : List (ℕ → Pt n))
    (hseeds : ∀ s ∈ seeds, GeoConstraint.Holds (.perpendicular a b c e) s) :
    ∀ s ∈ samplesOf standardFamily seeds,
      GeoConstraint.Holds (.perpendicular a b c e) s :=
  samplesOf_sound (.perpendicular a b c e) standardFamily seeds
    (standardFamily_preserves_perpendicular a b c e) hseeds

end SynthesisMulti

end Lattice.Geo
