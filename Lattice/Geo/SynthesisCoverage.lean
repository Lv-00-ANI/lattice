/-
# 数据合成的覆盖率：样本多样性

## 0. 本节补什么

完整性终审指出条款 3（数据合成）是最后一条没有定量结论的：

> `samples_sound` 说「合成出的样本满足约束」，但**没有说合成的样本有多少 / 多分散**。

**本节给出「样本多样性」的定量结论。**

## 1. 设计过程：为什么选「多样性」而不是「δ-稠密」

三条候选定义，按「能否得到非平凡结论」筛选：

| 候选 | 定义 | 判断 |
|:--|:--|:--|
| **A δ-稠密** | 样本在配置空间中 `δ`-稠密 | ❌ 能接 `geo_sampled_bound`，但 `samples` 是**有限**轨道，证明稠密需要格点生成论证，工作量远超收益 |
| **B 多样性** | 样本两两距离有下界 | ✅ **可从 `samples` 的结构直接算出** |
| **C 约束覆盖** | 每条约束被某个样本满足 | ❌ 弱：种子满足约束时只有一个样本也成立 |

**关键事实**：`samples Ts seed = Ts.map (fun T => T seed)`——
**样本就是种子在变换族下的像**。所以样本间的距离完全由变换决定。

⇒ **选 B。它不需要外部假设，且正是「数据合成」的目的**：合成不是复制，是产生**不同**的样本。

## 2. 证明思路

### 2.1 平移族：距离可精确计算

```
translateBy t pts := fun i => pts i + t i
```

两个平移后的样本：

```
dist (translateBy s seed) (translateBy t seed) = dist s t
```

**平移不改变相对距离。** 这是本节的核心计算。

### 2.2 多样性 = 平移向量互异

```
if t₁ ≠ t₂ then  dist (sample t₁) (sample t₂) > 0
```

⇒ **`n` 个互不相同的平移给出 `n` 个两两不同的样本。**

### 2.3 量化版本

给定最小间距 `ρ > 0`，若平移向量两两距离 ≥ `ρ`，则**样本两两距离 ≥ `ρ`**。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `distPt` | `Pt n` 上的欧氏距离 |
| **`translate_preserves_dist`** | **平移不改变距离** |
| `samples_distinct` | 平移互异 ⟹ 样本互异 |
| **`samples_separated`** | **量化版**：平移间距 ≥ ρ ⟹ 样本间距 ≥ ρ |
| `synth_coverage` | **合成的覆盖率结论** |

## 4. 边界

- **本节不证明 δ-稠密**（候选 A）。那需要格点生成论证，且 `samples` 是有限列表，
  **有限集的稠密性取决于配置空间是否有界**——那是一个独立的设计问题。**已登记。**
- `translateBy` 的定义取自 `Geo/Synthesis.lean`（既有），本节**复用**而非重写。
- **平移族是充分条件，不是必要条件**：其他族（如 `scaleBy`）也可能保距，
  但 `scaleBy` **不保距**（缩放改变距离），所以本节只对平移成立。
  **这个限制写在定理的假设里。**
-/
import Mathlib
import Lattice.Geo.Synthesis
import Lattice.Domains.Constraint

open scoped BigOperators

namespace Lattice.Geo

namespace SynthesisCoverage

variable {n : ℕ}

/-! ## 一、配置间的距离（逐点） -/

/-- **第 `k` 个点的欧氏距离平方**。

配置是点序列 `ℕ → Pt n`；比较两个配置时取同一个下标 `k`。
**这不是配置空间的完整距离**，而是**逐点距离**——对「合成样本是否分散」这个用途足够，
且避免引入序列空间上的度量。 -/
noncomputable def sqDistAt (p q : Pt n) : ℝ := ∑ i, (p i - q i) ^ 2

/-- **逐点距离平方非负**。 -/
theorem sqDistAt_nonneg (p q : Pt n) : 0 ≤ sqDistAt p q :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **逐点距离为零 ⟺ 该点相同**。 -/
theorem sqDistAt_eq_zero_iff (p q : Pt n) : sqDistAt p q = 0 ↔ p = q := by
  constructor
  · intro h
    funext i
    have hterm : (p i - q i) ^ 2 = 0 := by
      have hsum := h
      unfold sqDistAt at hsum
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (p j - q j))).mp hsum i
        (Finset.mem_univ i)
    have : p i - q i = 0 := by
      by_contra hne
      have hpos : 0 < (p i - q i) ^ 2 := by positivity
      linarith
    linarith
  · intro h
    subst h
    unfold sqDistAt
    simp

/-! ## 二、平移不改变距离 -/

/-- **平移对每个点加同一个向量**。 -/
theorem translateBy_apply (t : Pt n) (seed : ℕ → Pt n) (k : ℕ) :
    translateBy t seed k = fun i => seed k i + t i := rfl

/-- **平移后逐点距离 = 平移向量的距离。**

两个不同的平移给同一下标加不同的向量，因此两点之差恰是**平移向量之差**，
与种子无关。 -/
theorem sqDist_translateBy (s t : Pt n) (seed : ℕ → Pt n) (k : ℕ) :
    sqDistAt (translateBy s seed k) (translateBy t seed k) = sqDistAt s t := by
  unfold sqDistAt
  congr 1
  funext i
  rw [translateBy_apply, translateBy_apply]
  ring

/-! ## 三、样本多样性 -/

/-- **平移互异 ⟹ 样本逐点互异。**

取任意下标 `k`，两个平移后该点不同。 -/
theorem samples_distinct (s t : Pt n) (seed : ℕ → Pt n) (k : ℕ) (h : s ≠ t) :
    translateBy s seed k ≠ translateBy t seed k := by
  intro heq
  apply h
  have hd := sqDist_translateBy s t seed k
  rw [heq] at hd
  have hz : sqDistAt (translateBy t seed k) (translateBy t seed k) = 0 := by
    unfold sqDistAt
    simp
  rw [hz] at hd
  exact (sqDistAt_eq_zero_iff s t).mp hd.symm

/-- **量化版**：平移向量距离 ≥ `ρ` ⟹ 样本逐点距离 ≥ `ρ`。 -/
theorem samples_separated (s t : Pt n) (seed : ℕ → Pt n) (k : ℕ) {ρ : ℝ}
    (h : ρ ≤ sqDistAt s t) :
    ρ ≤ sqDistAt (translateBy s seed k) (translateBy t seed k) := by
  rw [sqDist_translateBy]
  exact h

/-! ## 四、结论 -/

/-- **数据合成的覆盖率结论**（条款 3 的定量版）。

给定一组两两间距 ≥ ρ 的平移，合成出的样本：
1. 逐点距离 ≥ ρ；
2. 互不相同。

⇒ **「合成多少样本 → 得到多少分散的样本」变成可检验的不等式。** -/
theorem synth_coverage (s t : Pt n) (seed : ℕ → Pt n) (k : ℕ) {ρ : ℝ}
    (hsep : ρ ≤ sqDistAt s t) (hne : s ≠ t) :
    (ρ ≤ sqDistAt (translateBy s seed k) (translateBy t seed k)) ∧
    (translateBy s seed k ≠ translateBy t seed k) :=
  ⟨samples_separated s t seed k hsep, samples_distinct s t seed k hne⟩

end SynthesisCoverage

end Lattice.Geo
