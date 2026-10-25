import Mathlib

/-!
# LATTICE：`I + W` 的范数下界与单射性（`B412` 的项目交付）

## 一、本文件证什么

`hreach`（`RealModelChain.lean:234-239` 等）是一条**前提**，要把它升格为定理，
需要「**块输出的预激活不塌缩**」。`B410` 已证**无条件 `hreach` 为假**
（`RealHreachConditional.hreach_unconditional_false`），其**条件版**依赖
`M + Lw < 1`（对真实 transformer 一般不成立）。

⭐ **`B412` 的原始计划是建 `σ_min`（最小奇异值）层，但可行性研究证明【那一层不必要】。**
`hreach` 需要的是「`‖(I + W)h‖` 有正下界」这个**性质**，**不是 `σ_min` 这个数**。
三角不等式就够了 —— **不需要** `σ_min`、**不需要**变分刻画、**不需要** Neumann 级数。

```
‖h + W h‖ ≥ ‖h‖ − ‖W h‖ ≥ ‖h‖ − Lw‖h‖ = (1 − Lw)‖h‖
```

⚠ **本文件【不】定义 `def σ_min`。** 见 §三。

## 二、`PROCESS.md §2.2` 要求的回答：「这条定理比它的**定义**多说了什么？」

- **`one_add_lower_bound`**：映射 `h ↦ h + W h` 的**定义**（加法与连续线性映射的应用）
  **对该映射的范数什么都没断言**。本定理给出一个**下界**，且该下界只依赖 `‖W‖`
  的**上界** `Lw` —— 这是**定义中不存在**的信息。✅ **多说了。**
  ⚠ **本定理甚至不需要 `Lw < 1`**（见 §四（一））：它对**任意** `Lw ≥ ‖W‖` 成立。
- **`one_add_injective`**：**单射性不是线性映射定义的一部分**（定义只要求可加、齐次）。
  本定理在 `Lw < 1` 下**断言**单射。✅ **多说了。**
  ⭐ 且它**承重地**使用 `Lw < 1`：`1 − Lw > 0` 是「下界为正」的唯一来源，
  而只有下界为正才能把 `‖x − y‖ = 0` 推出来。
- **`one_add_needs_hLw`**：**反例**，说明 `Lw < 1` **不是装饰**。
  ✅ 它断言的是**否定性**内容（不存在单射性），**不是**定义展开。

## 三、⚠ 明确【不】做的事（依 `PROCESS.md §2.2` 的拒绝类）

> **不定义 `def σ_min` 并配一条 `‖A h‖ ≥ σ_min A * ‖h‖`。**

理由是那条「定理」**只是把定义展开一遍**，**零内容** —— 与本项目已拒绝的
`residual(0) = 0` **同族**。若发现自己在做定义搬运，**停手并上报**。

## 四、诚实边界

**（一）`hLw` 已从 `one_add_lower_bound` 的签名中【删除】。**
首稿带 `(hLw : Lw < 1)`，内核报 **`unused variable 'hLw'`** ——
依 `PROCESS.md §4.6` 这是「**假设写松**」的最强机械信号。
核查病因：`mul_le_mul_of_nonneg_right` 只需 `0 ≤ ‖h‖`（由 `norm_nonneg` 免费），
**不需要 `Lw < 1`**。⇒ **删除是【加强】**（假设更少），
且**未**用 `set_option linter.unusedVariables false` 静音（`B224.5` 禁止掩盖）。
**`Lw < 1` 保留在 `one_add_injective` 中，那里它是承重的。**

**（二）本文件给出的是【性质】而非【谱估计】。**
`one_add_injective` 是「`I + W` 单射」；由有限维可得可逆，但**本文件不证可逆性**
（在一般赋范空间上单射 ⟹ 可逆需要额外结构）。⚠ **不声称超出已证内容。**

**（三）与 `M + Lw < 1` 的关系。**
本文件提供的是**替代** `hreach` 条件版的**工具**，**不是**它本身。
把 `hreach` 真正升格为定理**仍需**（另需）：把 `W` 与注意力项同时纳入下界，
并处理 `SoftmaxAttnOp` 项。⚠ **本文件不声称 `hreach` 已闭合。**

**（四）未验证。**
⚠ 未跑完整 `lake build`；本文件经 `probe.ps1` 类型检查（**不产出 olean**），
故**在协调者注册 roots 并构建前不可被 import**。
⚠ 未核 mathlib 的 Neumann 机制（`isUnit_one_sub_of_norm_lt_one` 等）
是否适用于 `E →L[ℝ] E` 载体 —— 因为**本路线用不到它们**。

## 五、本文件依赖的 mathlib 引理（均已实测存在）

| 引理 | 陈述 |
|:--|:--|
| `ContinuousLinearMap.le_opNorm` | `‖W h‖ ≤ ‖W‖ * ‖h‖` |
| `abs_norm_sub_norm_le` | `\|‖a‖ − ‖b‖\| ≤ ‖a − b‖`（**反向三角不等式**） |
| `sub_neg_eq_add` | `a − (−b) = a + b` |
| `norm_neg` | `‖−a‖ = ‖a‖` |

⚠ **注意**：`le_norm_sub`（可行性研究草稿所用）在本版 mathlib **不存在**，
实测报 `unknown identifier`；正确的引理是 **`abs_norm_sub_norm_le`**。
-/

namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **`I + W` 的范数下界**。

若 `‖W‖ ≤ Lw`，则对任意 `h` 有 `(1 − Lw) * ‖h‖ ≤ ‖h + W h‖`。

⚠ **不需要 `Lw < 1`** —— 该假设在本定理中不被使用（见文件头 §四（一））。
`Lw < 1` 在 `one_add_injective` 才是承重的。

证明：`‖h + W h‖ ≥ ‖h‖ − ‖−W h‖ = ‖h‖ − ‖W h‖ ≥ ‖h‖ − Lw‖h‖`。 -/
theorem one_add_lower_bound
    (W : E →L[ℝ] E) (Lw : ℝ) (hW : ‖W‖ ≤ Lw) (h : E) :
    (1 - Lw) * ‖h‖ ≤ ‖h + W h‖ := by
  have hWb : ‖W h‖ ≤ Lw * ‖h‖ := by
    calc ‖W h‖ ≤ ‖W‖ * ‖h‖ := W.le_opNorm h
      _ ≤ Lw * ‖h‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg h)
  -- 反向三角不等式：‖h‖ − ‖−(W h)‖ ≤ ‖h − (−(W h))‖
  have hrt : ‖h‖ - ‖W h‖ ≤ ‖h + W h‖ := by
    have h1 := abs_norm_sub_norm_le h (-(W h))
    rw [abs_le] at h1
    rw [norm_neg, sub_neg_eq_add] at h1
    exact h1.2
  calc (1 - Lw) * ‖h‖ = ‖h‖ - Lw * ‖h‖ := by ring
    _ ≤ ‖h‖ - ‖W h‖ := by linarith
    _ ≤ ‖h + W h‖ := hrt

/-- **`I + W` 的单射性**（`‖W‖ ≤ Lw < 1` 时）。

⭐ 这里 `hLw : Lw < 1` 是**承重**的：它给出 `1 − Lw > 0`，
配合 `one_add_lower_bound` 才能把 `‖x − y‖` 夹成 `0`。

⚠ 本定理只断言**单射**，**不**断言可逆（见文件头 §四（二））。 -/
theorem one_add_injective
    (W : E →L[ℝ] E) (Lw : ℝ) (hW : ‖W‖ ≤ Lw) (hLw : Lw < 1) :
    Function.Injective (fun h : E => h + W h) := by
  intro x y hxy
  have hxy' : x + W x = y + W y := hxy
  -- (x − y) + W (x − y) = 0
  have hsub : (x - y) + W (x - y) = 0 := by
    have hWsub : W (x - y) = W x - W y := by simp
    have hexp : (x - y) + (W x - W y) = (x + W x) - (y + W y) := by abel
    rw [hWsub, hexp, hxy', sub_self]
  have hb := one_add_lower_bound W Lw hW (x - y)
  rw [hsub, norm_zero] at hb
  have hnorm : ‖x - y‖ = 0 := by
    by_contra hne
    have h1 : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have h2 : 0 < 1 - Lw := by linarith
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- ⭐ **承重见证：`Lw < 1` 不是装饰**（依 `PROCESS.md §3.3` 第 ⑤ 步**固化为定理**）。

取 `W = −id`（即 `h ↦ h + (−1) * h`）与 `Lw = 1`：
该映射是**常零映射**（`h ↦ h − h = 0`），**故非单射** ——
`0` 与 `1` 的像都是 `0`。

⇒ 去掉 `Lw < 1` 后，`one_add_injective` 的结论**可被反驳** ⟹ **`Lw < 1` 承重**。 -/
theorem one_add_needs_hLw :
    ¬ Function.Injective (fun h : ℝ => h + (-1 : ℝ) * h) := by
  intro hf
  have h : (0 : ℝ) + (-1) * 0 = 1 + (-1) * 1 := by norm_num
  have := hf h
  norm_num at this

end Lattice
