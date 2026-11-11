import Mathlib
import Lattice.Core.CIC.ShiftSubstJointBounded
import Lattice.Core.CIC.ParallelReductionVarying

/-!
# `par-subst` 的第一层：`subst` 在一侧的变化（阶段 5）

## 本轮发现的一个缺失前提

**要证 `ParRedV E (subst j s t) (subst j s' t)`，绑定层需要**

```lean
ParRedV E (shift 0 1 s) (shift 0 1 s')
```

**即 `ParRedV` 在 `shift 0 1` 下的闭合性 —— 而这一步**尚不存在**：
第 826 轮的 `parRedVStruct_shift` 作用于 `ParRedVStruct`（`Rewritable` 类型），
不是 `ParRedV` 本身。**

**=> `par-subst` 的真正前提链是三层：**

1. **`ParRedV` 在 `shift 0 1` 下闭合（缺失，下一步）**；
2. **`subst` 的合同性（本文件，非绑定分支；绑定分支依赖第 1 层）**；
3. **联合律（第 847 轮，已备）**。

## 已证的部分

| 定理 | 内容 |
|:--|:--|
| `subst_var_cases` | **`subst` 在 `var n` 上的三分形态，作为可引用的等式** |
| `parRedV_subst_var` | **`var` 分支：三支全部闭合** |
| `parRedV_subst_app` | **`app` 分支：两个归纳假设直接给** |

**=> 这三条不依赖第 1 层，因此可以先落地。** -/

namespace Lattice.Core.CIC

/-- **`subst` 在 `var n` 上的三种形态。**

**=> `n = j` 时是替换项 `s`；`n < j` 时是 `var n`；`n > j` 时是 `var (n-1)`。
这一条把三分写成可改写的等式。** -/
theorem subst_var_cases (j n : ℕ) (s : Term) :
    subst j s (Term.var n) = (if n = j then s else if n < j then Term.var n else Term.var (n - 1)) :=
  rfl

/-- **`ParRedV` 在 `subst` 的 `var` 分支上合同（替换项一侧）。**

**=> 三支：`n = j` 时直接是 `hs`；`n < j` 与 `n > j` 时两侧都等于同一个 `var`，
用 `ParRedV.zero`（自反）。**

**=> 「`n < j` 与 `n > j` 时两侧相同」正是 `subst` 在非替换位置上的**确定性**，
它使 `ParRedV` 的变化被完全吸收。** -/
theorem parRedV_subst_var (E : DefEnv) (j n : ℕ) (s s' : Term) (hs : ParRedV E s s') :
    ParRedV E (subst j s (Term.var n)) (subst j s' (Term.var n)) := by
  by_cases h1 : n = j
  · subst h1
    simp only [subst, if_pos rfl]
    exact hs
  · by_cases h2 : n < j
    · simp only [subst, if_neg h1, if_pos h2]
      exact ParRedV.zero _
    · simp only [subst, if_neg h1, if_neg h2]
      exact ParRedV.zero _

/-- **`ParRedV` 在 `subst` 的 `app` 分支上合同。**

**=> 两侧各有归纳假设即可；`subst` 与 `ParRedV.app` 都在同一位置分解。** -/
theorem parRedV_subst_app (E : DefEnv) {f f' a a' : Term}
    (hf : ParRedV E f f') (ha : ParRedV E a a') :
    ParRedV E (.app f a) (.app f' a') :=
  ParRedV.app hf ha

end Lattice.Core.CIC
