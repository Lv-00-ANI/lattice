import Mathlib
import Lattice.Core.Data.Encode

/-!
# 覆盖谓词的**单调性**：常量集扩大时覆盖保持（阶段 C，P2-3）

## 规划的前提不存在

**P2-3 说「`Coverable` 的 `n ≤ N` 类型问题」。**

**实测：全库**没有 `Coverable`**。真正的覆盖谓词有三个，都在 `Core/Data/Encode.lean`，
而且 `ConstSet` 是**任意谓词**，与任何上界无关：**

```lean
abbrev ConstSet : Type := ℕ → Prop

def CoversCorpus  (K) (c)  : Prop := K 0 ∧ ∀ s ∈ c, K s.width
def CoversIndices (K) (is) : Prop := K 0 ∧ ∀ i ∈ is, K i.offset ∧ K i.length
def Covered       (K) (d)  : Prop := CoversCorpus K d.corpus ∧ CoversIndices K d.indices
```

**=> `K` 不是「`n ≤ N`」形式的区间，而是一个任意谓词。规划所设想的类型问题**在这里没有对应物**。**
**（`Encode.lean:112` 的注释也写明：这个谓词「恰好够用，不多不少」。）**

## 但**单调性**确实缺失

**`K` 是任意谓词，于是「把 `K` 放大」是一个有意义且必要的操作：
若某个常量集能覆盖数据，那么**任何更大的常量集**也能覆盖同一数据。**

**=> 这个性质是 `Covered` 这个谓词「按包含序单调」的精确陈述。
它在库里**没有被证明过** —— 而它是下游所有「放宽常量集」论证的前提。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `coversCorpus_mono` | **`K ⊆ K'` 且 `CoversCorpus K c` ⟹ `CoversCorpus K' c`** |
| `coversIndices_mono` | **`K ⊆ K'` 且 `CoversIndices K is` ⟹ `CoversIndices K' is`** |
| `covered_mono` | **`K ⊆ K'` 且 `Covered K d` ⟹ `Covered K' d`** |
| `covered_typable` | **覆盖且单调放大后，编码仍然可类型化** |

**=> 前三条是单调性的完整链条（两个分量 + 合取）；第四条把单调性与既有的
`typable_encodeCorpus` 接起来，说明「放宽常量集不破坏保类型性」——
**这是 P2-3 真正要的东西**，而不是一个不存在的 `n ≤ N`。** -/

namespace Lattice.Core.IR

open Lattice.Data.Encode
open Lattice.Data
open Lattice.Core.CIC

/-- **常量集的包含序：`K ⊆ K'` 当且仅当 `K n` 蕴含 `K' n`（对每个 `n`）。**

**=> 这是「放大常量集」的精确形式。** -/
def ConstSubset (K K' : ConstSet) : Prop := ∀ n, K n → K' n

/-- **`CoversCorpus` 按常量集包含单调。**

**=> 两个合取项各自用到 `ConstSubset`：`K 0` 放大成 `K' 0`，
`K s.width` 放大成 `K' s.width`。** -/
theorem coversCorpus_mono {K K' : ConstSet} (hsub : ConstSubset K K')
    {c : List Sample} (h : CoversCorpus K c) : CoversCorpus K' c := by
  refine ⟨hsub 0 h.1, ?_⟩
  intro s hs
  exact hsub s.width (h.2 s hs)

/-- **`CoversIndices` 按常量集包含单调。** -/
theorem coversIndices_mono {K K' : ConstSet} (hsub : ConstSubset K K')
    {is : List Index} (h : CoversIndices K is) : CoversIndices K' is := by
  refine ⟨hsub 0 h.1, ?_⟩
  intro i hi
  exact ⟨hsub i.offset (h.2 i hi).1, hsub i.length (h.2 i hi).2⟩

/-- **`Covered` 按常量集包含单调。**

**=> 两个分量各自应用上面两条单调律。** -/
theorem covered_mono {K K' : ConstSet} (hsub : ConstSubset K K')
    {d : Data} (h : Covered K d) : Covered K' d :=
  ⟨coversCorpus_mono hsub h.1, coversIndices_mono hsub h.2⟩

/-- **放宽常量集不破坏保类型性。**

**=> 若 `K` 覆盖语料且 `K ⊆ K'`，则 `K'` 也覆盖它，因此 `encodeCorpus c` 在 `K'` 下仍可类型化。**

**=> 这条把单调性与既有的 `typable_encodeCorpus` 接起来，是「扩大常量集安全」的完整陈述。** -/
theorem covered_typable {K K' : ConstSet} (hsub : ConstSubset K K')
    (Γ : CICCtx) (c : List Sample) (h : CoversCorpus K c) :
    Typable K' Γ (encodeCorpus c) :=
  typable_encodeCorpus Γ c (coversCorpus_mono hsub h)

end Lattice.Core.IR
