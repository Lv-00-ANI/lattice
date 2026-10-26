/-
# 多种子合成的覆盖率：多样性保证的推广

## 0. 本节补什么

第 77 轮（`Geo/SynthesisCoverage.lean`）给了**单种子**合成的多样性保证：

```
samples_separated : 平移向量间距 ≥ ρ  ⟹  样本间距 ≥ ρ
synth_coverage    :  加上样本互异
```

后来 `Geo/SynthesisMulti.lean` 把 `samples` 推广到**多种子**的 `samplesOf`，
并给了三条定理：`samplesOf_singleton`（退化一致）、`samplesOf_sound`（正确性）、
`samplesOf_length_pos`（非空）。

**但多样性保证没有跟着推广。** 多种子下 `synth_coverage` 不适用——
它的陈述是关于 `samples Ts seed`（单种子）的。

⇒ **本节补这个缺口。**

## 1. 证明思路

多种子样本是 `seeds.flatMap (fun s => Ts.map (fun T => T s))`，
所以任意两个样本来自某个 (种子, 变换) 对。

**分工况：**

| 情形 | 两个样本的关系 | 多样性来自 |
|:--|:--|:--|
| 同变换、同种子 | **同一个样本** | 无从谈起（它就是一个元素） |
| 同变换、不同种子 | `dist (T s₁) (T s₂)` | **变换保距 ⟹ 等于 `dist s₁ s₂`** |
| 不同变换 | 无一般结论 | **需额外假设** |

**关键**：平移族下，「不同变换」的距离可以算（第 77 轮的 `sqDist_translateBy`）。
但**多种子 + 多变换的组合**下，两个不同变换的平移量之差与种子无关，
所以距离仍然可算：

```
dist (translate t₁ seed₁) (translate t₂ seed₂)  =  dist (t₁ + seed₁ - seed₂) t₂     -- 形如
```

**这个表达式依赖种子之差**，所以不是常数。

### 1.1 因此正确的陈述是什么

**不能说「所有样本两两距离 ≥ ρ」**（不同变换的情形依赖于种子）。

**正确的陈述**：**固定一个变换，不同种子给出的样本保持种子的间距。**

这是**真正的多样性保证**：合成把「种子的多样性」**保留**下来了。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `SynthesisCoverage.sqDistAt_translate_both` | 两个平移样本的逐点距离可算 |
| **`samplesOf_same_transform_separated`** | **同变换、不同种子 ⟹ 样本保持种子间距** |
| `samplesOf_length_mul` | 样本总数 = 种子数 × 变换数 |
| `samplesOf_coverage` | 汇总 |

## 3. 边界

- **只对平移族证明**：与第 77 轮一致（`scaleBy` 不保距）。
- **不声称所有样本两两分离**：那在多种子下是假的（见 §1）。
- 本节**不改** `SynthesisCoverage` 的既有定理，只补多种子情形。
-/
import Mathlib
import Lattice.Geo.SynthesisCoverage
import Lattice.Geo.SynthesisMulti
import Lattice.Geo.Synthesis

open scoped BigOperators

namespace Lattice.Geo

namespace MultiSeedCoverage



variable {n : ℕ}

/-! ## 一、两个平移样本的逐点距离 -/

/-- **两个平移样本的逐点距离可算**：`translateBy` 对每个点加同一个向量，
所以两个平移样本在第 `k` 点的差**恰是两个平移向量之差**，与种子无关。

这是第 77 轮 `sqDist_translateBy` 的逐点版本，此处独立陈述以便多种子使用。 -/
theorem SynthesisCoverage.sqDistAt_translate_apply (s t : Pt n) (seed : ℕ → Pt n) (k : ℕ) :
    SynthesisCoverage.sqDistAt (translateBy s seed k) (translateBy t seed k) = SynthesisCoverage.sqDistAt s t := by
  unfold SynthesisCoverage.sqDistAt
  congr 1
  funext i
  simp only [translateBy, translate]
  ring

/-! ## 二、同变换、不同种子 -/

/-- **同变换、不同种子 ⟹ 样本保持种子的间距。**

`T` 取一个平移 `translateBy t`：两个种子的样本在第 `k` 点的距离
等于两个种子的间距（平移不改距离）。

⇒ **合成不压缩种子的多样性。** -/
theorem same_transform_separated (t : Pt n) (seed₁ seed₂ : ℕ → Pt n) {ρ : ℝ}
    (k : ℕ) (h : ρ ≤ SynthesisCoverage.sqDistAt (seed₁ k) (seed₂ k)) :
    ρ ≤ SynthesisCoverage.sqDistAt (translateBy t seed₁ k) (translateBy t seed₂ k) := by
  -- translateBy t acts on the SEED (a configuration), so compare point k of both results
  -- the shift is the same `t`, hence the difference cancels
  unfold SynthesisCoverage.sqDistAt translateBy translate
  have h2 : ∀ i, (seed₁ k i + t i - (seed₂ k i + t i)) = (seed₁ k i - seed₂ k i) := by
    intro i; ring
  simp only [h2]
  exact h

/-! ## 三、样本总数的算术 -/

/-- **样本总数 = 种子数 × 变换数**（当变换族作用于多种子时）。

这是「合成多少样本」的最直接答案。

证明按种子列表归纳；归纳步用 `Nat.mul_succ` 把 `Ts.length * (n+1)` 拆开，
避免在 `List.length_cons` 的形状上和 `ring` 纠缠。 -/
theorem samplesOf_length (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seeds : List (ℕ → Pt n)) :
    (SynthesisMulti.samplesOf Ts seeds).length = seeds.length * Ts.length := by
  unfold SynthesisMulti.samplesOf
  induction seeds with
  | nil => simp
  | cons s rest ih =>
      rw [List.flatMap_cons, List.length_append, List.length_map, ih]
      rw [List.length_cons, Nat.succ_mul]
      ring

/-- **一个种子时退化为变换数**。 -/
theorem samplesOf_length_single (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n) :
    (SynthesisMulti.samplesOf Ts [seed]).length = Ts.length := by
  rw [samplesOf_length]
  simp

/-! ## 四、结论 -/

/-- **多种子合成的覆盖率**。

| 性质 | 结论 |
|:--|:--|
| 正确性 | `samplesOf_sound`（既有） |
| 非空 | `samplesOf_length_pos`（既有） |
| **样本数** | **种子数 × 变换数（本节）** |
| **多样性** | **同变换下保持种子间距（本节）** |

**注意**：不声称「所有样本两两分离」——多种子下不同变换的距离依赖种子之差，
所以那不是定理。**这是诚实的边界。** -/
theorem samplesOf_coverage (t : Pt n) (seed₁ seed₂ : ℕ → Pt n)
    (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) {ρ : ℝ} (k : ℕ)
    (h : ρ ≤ SynthesisCoverage.sqDistAt (seed₁ k) (seed₂ k)) :
    (ρ ≤ SynthesisCoverage.sqDistAt (translateBy t seed₁ k) (translateBy t seed₂ k)) ∧
    ((SynthesisMulti.samplesOf Ts [seed₁, seed₂]).length = 2 * Ts.length) :=
  ⟨same_transform_separated t seed₁ seed₂ k h, by
    rw [samplesOf_length]
    simp⟩

end MultiSeedCoverage

end Lattice.Geo
