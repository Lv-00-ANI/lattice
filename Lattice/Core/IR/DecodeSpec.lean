import Mathlib
import Lattice.Core.IR.Skeleton

/-!
# **P1-8 规格层：一个精确符合审计要求的解码器**（阶段 O，O-2 方案 B）

## 审计的要求，逐字

**`T3-DECODE-DESIGN.md` 记录：**

> **审计的 P1-8 要求 `decode : ℕ → Option IRSkeleton`，对**不是**任何骨架的码返回 `none`。**

**要求只有两条：**
1. **它是 `ℕ → Option IRSkeleton`；**
2. **`n` 不是任何骨架的码时，结果为 `none`。**

**=> 它**没有**要求解码是算法。**

## 现有解码器为什么不满足

**第 973 轮的 `decodeTensorShape_not_faithful` 证明了：现有的燃料式解码器是**宽松**的**
**——它只看码的第一分量，因此把一批**非码**也解成 `some`。**

**=> 所以「方案 A（把可计算解码器改严）」是一个**真问题**，但它是**严格更强**的要求。**

## 方案 B：只要规格，就用单射性直接构造

**`skeletonCode_injective`（`Skeleton.lean:175`）保证：码在像中时有**唯一**原像。**

```lean
noncomputable def decodeSpec (n : ℕ) : Option IRSkeleton :=
  if h : ∃ k : IRSkeleton, skeletonCode k = n then some h.choose else none
```

**=> 像上返回唯一原像，像外返回 `none`。规格**逐字**满足。**

**=> 代价是 `Classical.choose`：这不是算法。**
**=> 而这一点被明确记录，不假装它是算法。**

## 为什么这仍然值得交付

**它把 O-2 从「十二轮不明所以的失败」变成一条**有名字的分界线**：**

| 层 | 内容 | 状态 |
|:--|:--|:--|
| **规格层** | `ℕ → Option IRSkeleton`，像外为 `none` | **本文件，已证** |
| **算法层** | 同一函数**可计算**（无需 `Classical.choose`） | **开放**，即方案 A；`T3-DECODE-DESIGN.md` 的十二轮正是在打它 |

**=> 一个规格若只能由非可计算函数满足，那是**规格的**信息，不是失败。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`decodeSpec`** | **⭐⭐⭐ 规格合规的解码器（非可计算）** |
| **`decodeSpec_none_of_not_code`** | **⭐⭐⭐ 像外返 `none`——审计要件，逐字满足** |
| **`decodeSpec_some_code`** | **⭐⭐⭐ 码上返回原骨架** |
| **`decodeSpec_eq_some_iff`** | **⭐⭐⭐ 完整刻画：`decodeSpec n = some k ↔ skeletonCode k = n`** |
| **`decodeSpecOfWeights`** | **⭐⭐ 权重 → 码 → 骨架，像外为 `none`** | -/

namespace Lattice.Core.IR

/-- **⭐⭐⭐ 规格合规的解码器：码在像中则给唯一原像，否则 `none`。**

**=> 唯一性来自 `skeletonCode_injective`。**

**⚠ **非可计算**（`Classical.choose`）。这是**有意**的：审计的规格不要求可计算，
而可计算版本（方案 A）是 `T3-DECODE-DESIGN.md` 记录的开放问题。** -/
noncomputable def decodeSpec (n : ℕ) : Option IRSkeleton := by
  classical
  exact if h : ∃ k : IRSkeleton, skeletonCode k = n then some h.choose else none

/-- **⭐⭐⭐ 像外返回 `none`——审计 P1-8 的核心要件，逐字满足。** -/
theorem decodeSpec_none_of_not_code (n : ℕ) (h : ¬ ∃ k : IRSkeleton, skeletonCode k = n) :
    decodeSpec n = none := by
  classical
  simp only [decodeSpec, dif_neg h]

/-- **⭐⭐⭐ 在码上返回原骨架。**

**=> 由单射性，`choose` 取到的原像**就是** `k`。** -/
theorem decodeSpec_some_code (k : IRSkeleton) : decodeSpec (skeletonCode k) = some k := by
  classical
  have hex : ∃ k' : IRSkeleton, skeletonCode k' = skeletonCode k := ⟨k, rfl⟩
  simp only [decodeSpec, dif_pos hex]
  exact congrArg some (skeletonCode_injective hex.choose_spec)

/-- **⭐⭐⭐ 完整刻画：`decodeSpec n = some k` 恰好当 `k` 是 `n` 的骨架。**

**=> 这条把「解码器」与「编码单射」**等价地**连起来，
并且它同时给出审计要的两个方向。** -/
theorem decodeSpec_eq_some_iff (n : ℕ) (k : IRSkeleton) :
    decodeSpec n = some k ↔ skeletonCode k = n := by
  constructor
  · intro h
    classical
    by_cases hex : ∃ k' : IRSkeleton, skeletonCode k' = n
    · simp only [decodeSpec, dif_pos hex] at h
      have hk : hex.choose = k := Option.some.inj h
      rw [← hk]
      exact hex.choose_spec
    · simp only [decodeSpec, dif_neg hex] at h
      exact absurd h (by simp)
  · intro h
    rw [← h]
    exact decodeSpec_some_code k

/-- **⭐⭐ 从权重到骨架：先取码，再解码；非码得 `none`。**

**=> `extractCode` 总是给出一个 `ℕ`；`decodeSpecOfWeights` 才回答「这个数是不是一个骨架」，
并把「不是」显式表示为 `none`。** -/
noncomputable def decodeSpecOfWeights (W : IRWeights) : Option IRSkeleton :=
  match extractCode W with
  | some n => decodeSpec n
  | none => none

/-- **⭐⭐ 若权重提取出的码恰是 `k` 的码，则解码得 `k`。** -/
theorem decodeSpecOfWeights_of_code (W : IRWeights) (k : IRSkeleton)
    (h : extractCode W = some (skeletonCode k)) : decodeSpecOfWeights W = some k := by
  simp only [decodeSpecOfWeights, h]
  exact decodeSpec_some_code k

end Lattice.Core.IR
