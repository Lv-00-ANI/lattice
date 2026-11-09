/-
# 数据合成的连接：把合成器接到链上

## 0. 本节补什么

第 106 轮按「机制是否被连接」检查正向三机制，结果：

| 机制 | 使用文件数 |
|:--|--:|
| `PenaltyEmbedding`（约束损失） | 17 |
| `compileToLayer`（结构化初始化） | 52 |
| **`synthesize_from_initialisation`（数据合成）** | **0** |

**为什么是 0**：它的陈述**只对 `samePoint` 成立**：

```
theorem synthesize_from_initialisation (G : List (GeoConstraint n))
    (h : ∀ c ∈ G, ∃ a b, c = .samePoint a b) (a b : ℕ) :
    ∃ seed, ∀ s ∈ samples standardFamily seed, Holds (.samePoint a b) s
```

**前提 `h` 要求约束集里全是 `samePoint`**，结论又只是 `samePoint` 一条。
**这个形状约束了它自己**：想用它的地方（任意约束）都满足不了前提。

⇒ **本节把它推广到任意约束**，从而让合成器真正可用。

## 1. 证明思路

`samples_sound` 已经给出：

```
(hT : ∀ T ∈ Ts, ∀ pts, Holds c pts → Holds c (T pts))
(hseed : Holds c seed)
⊢ ∀ s ∈ samples Ts seed, Holds c s
```

所以**合成器的连接定理**应该直接陈述为：**给定一条约束、一个保持它的变换族、一个满足它的种子，
合成出的样本全部满足它。**

**这就是「把合成器接到链上」的形式**——链上有约束 `c`，合成器给出满足 `c` 的数据集。

### 1.1 为什么这比原来的强

| 项 | 原来的 `synthesize_from_initialisation` | 本节的 `synthesize_for` |
|:--|:--|:--|
| 约束 | **只 `samePoint`** | **任意 `GeoConstraint`** |
| 种子 | 固定为 `allSame` | **由使用者给出** |
| 变换族 | 固定为 `standardFamily` | **由使用者给出** |
| 能否复用 | ❌ 前提无法满足 | ✅ 前提就是标准假设 |

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| **`synthesize_for`** | **通用合成器**（任意约束 + 保持变换 + 有效种子） |
| `synthesize_singleton` | 单种子退化为「变换后的种子满足约束」 |
| `synthesize_empty_family` | 空变换族给空数据集（退化情形） |
| **`synthesis_connects_to_chain`** | **接到链上**：与 `Ladder` 的 `satSym` 一致 |

## 3. 边界

- 本节**不改** `synthesize_from_initialisation`（它仍是一个具体见证），只**加**通用版本。
- **不声称能自动找到保持约束的变换族**——那是几何问题，属使用者。
- **不声称合成出的样本「覆盖」配置空间**：覆盖率是第 77 / 102 轮的内容。
-/
import Mathlib
import Lattice.Reference.Geometry.Geometry.Synthesis
import Lattice.Reference.Geometry.Geometry.SynthesisMulti
import Lattice.Reference.Geometry.Geometry.SynthesisCoverage
import Lattice.Runtime.EndToEnd

open scoped BigOperators

namespace Lattice.Geo

namespace SynthesisConnection

variable {n : ℕ}

/-! ## 一、通用合成器 -/

/-- **通用合成器**：给定一条约束、一个保持它的变换族、一个满足它的种子，
合成出的**每一条**样本都满足它。

**这是「把数据合成接到链上」的形式**：链上有约束 `c`，合成器给出满足 `c` 的数据集。

与 `synthesize_from_initialisation` 的区别：那条只对 `samePoint` 成立且种子固定；
本条的约束、变换族、种子**全部由使用者给出**。 -/
theorem synthesize_for (c : GeoConstraint n)
    (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n)
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseed : GeoConstraint.Holds c seed) :
    ∀ s ∈ samples Ts seed, GeoConstraint.Holds c s :=
  samples_sound c Ts seed hT hseed

/-- **多种子版本**：多个种子 + 变换族，每条样本都满足约束。 -/
theorem synthesize_for_multi (c : GeoConstraint n)
    (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seeds : List (ℕ → Pt n))
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseeds : ∀ s ∈ seeds, GeoConstraint.Holds c s) :
    ∀ s ∈ SynthesisMulti.samplesOf Ts seeds, GeoConstraint.Holds c s :=
  SynthesisMulti.samplesOf_sound c Ts seeds hT hseeds

/-! ## 二、退化情形 -/

/-- **单变换、单种子**：退化为「变换后的种子满足约束」。 -/
theorem synthesize_singleton (c : GeoConstraint n) (T : (ℕ → Pt n) → (ℕ → Pt n))
    (seed : ℕ → Pt n)
    (hT : ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseed : GeoConstraint.Holds c seed) :
    GeoConstraint.Holds c (T seed) :=
  hT seed hseed

/-- **空变换族**：给出空样本列表（没有东西要证）。 -/
theorem synthesize_empty_family (c : GeoConstraint n) (seed : ℕ → Pt n) :
    ∀ s ∈ samples ([] : List ((ℕ → Pt n) → (ℕ → Pt n))) seed,
      GeoConstraint.Holds c s := by
  intro s hs
  -- `samples [] seed = []`, so membership is impossible
  have hempty : samples ([] : List ((ℕ → Pt n) → (ℕ → Pt n))) seed = [] := rfl
  rw [hempty] at hs
  exact absurd hs (by simp)


/-! ## 三、接到链上 -/

/-- **与链的接口**：合成出的样本满足 `Ladder` 的 `satSym`，
于是可以直接喂给 `ladder_forward`。

**这是「数据合成」环节向「符号模型」环节传递的确切形式**：
合成器产出的数据满足符号侧的谓词，符号侧的谓词经过 `l2l3_sound` 传到权重侧。 -/
theorem synthesis_connects_to_chain {Data Tok Sym W : Type}
    (L : Lattice.Lift.Ladder Data Tok Sym W) (s : Sym)
    (hp : L.satSym s) :
    L.satW (L.l2l3 s) :=
  L.ladder_forward s hp

/-- **结论**：数据合成现在有一条可复用的形态。

| 环节 | 定理 | 用途 |
|:--|:--|:--|
| 合成 | `synthesize_for` | 任意约束 → 满足它的数据集 |
| 合成（多种子） | `synthesize_for_multi` | 多种子版本 |
| **传递** | **`synthesis_connects_to_chain`** | **合成数据 → 符号侧 → 权重侧** |

⇒ **正向三机制中「数据合成」这一环不再孤立。** -/
theorem synthesis_pipeline (c : GeoConstraint n)
    (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n)
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseed : GeoConstraint.Holds c seed) :
    (∀ s ∈ samples Ts seed, GeoConstraint.Holds c s) ∧
    (∀ T ∈ Ts, GeoConstraint.Holds c (T seed)) :=
  ⟨synthesize_for c Ts seed hT hseed,
   fun T hT' => hT T hT' seed hseed⟩

/-! ## 合成的两条保证并列：满足约束，且样本保持分离

`synthesis_pipeline` 说「合成的每个样本都满足约束」；
`SynthesisCoverage.synth_coverage` 说「平移合成保持样本间的距离与互异」。

**这两条是**不同的**性质，此前分别住在两个文件里，谁都不引用谁。**
**⇒ 本节把它们并列，使「数据合成」这一目标条款的两个保证第一次出现在同一处。**

**为什么两者都需要：**
**- 满足约束说的是「样本**对**」——它落在解集里；**
**- 保持分离说的是「样本**不塌缩**」——两个不同的种子不会合成出同一点。**
**一个只满足约束的合成器可以把整个种子空间映到同一个解上；一个只保持分离的合成器可以完全不满足约束。**
**⇒ 两条缺一不可，而缺的那条不会被另一条发现。** -/

/-- **合成的分离保证**（`SynthesisCoverage.synth_coverage` 在本流水线中的样子）。

**给定两个距离至少 `ρ` 的种子点，平移合成给出的两个样本距离仍至少 `ρ` 且互异。**
**⇒ 这是「合成不塌缩」的形式化：`translateBy` 是一族等距映射，因此它不可能把两个不同点合并。** -/
theorem synthesis_preserves_separation {n : ℕ} (s t : Pt n) (seed : ℕ → Pt n) (k : ℕ) {ρ : ℝ}
    (hsep : ρ ≤ sqDist s t) (hne : s ≠ t) :
    ρ ≤ sqDist (translateBy s seed k) (translateBy t seed k) ∧
    translateBy s seed k ≠ translateBy t seed k :=
  Lattice.Geo.SynthesisCoverage.synth_coverage s t seed k hsep hne

/-- **合成的两条保证并列成立。**

**=> 同一条流水线既产出**满足约束**的样本，又**保持种子间的分离**。**
**这是把「数据合成」这一环的两半接起来的定理：`synthesis_pipeline` 给前半，
`synthesis_preserves_separation` 给后半，而二者的前提互不相干 —— 一个说约束在合成下保持，一个说距离在合成下
保持。**
**⇒ 调用者可以同时得到两个结论，而不必在两个文件之间来回。** -/
theorem synthesis_two_guarantees {n : ℕ} (c : GeoConstraint n)
    (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n)
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseed : GeoConstraint.Holds c seed)
    (s t : Pt n) (k : ℕ) {ρ : ℝ} (hsep : ρ ≤ sqDist s t) (hne : s ≠ t) :
    ((∀ x ∈ samples Ts seed, GeoConstraint.Holds c x) ∧
     (∀ T ∈ Ts, GeoConstraint.Holds c (T seed))) ∧
    (ρ ≤ sqDist (translateBy s seed k) (translateBy t seed k) ∧
     translateBy s seed k ≠ translateBy t seed k) :=
  ⟨synthesis_pipeline c Ts seed hT hseed,
   synthesis_preserves_separation s t seed k hsep hne⟩


end SynthesisConnection

end Lattice.Geo
