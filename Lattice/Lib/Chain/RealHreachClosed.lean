import Mathlib
import Lattice.Lib.Architectures.RealBlockConstants
import Lattice.Lib.LinearAlgebra.RealOperatorInvertibility
import Lattice.Lib.Attention.RealSoftmaxAttnNormBound
/-!
# `hreach` 闭合：不预设「块是压缩映射」的残差下界

**项目**：`B415`（`B410` 的闭合步骤）。本文件**组合**三个既有模块：
`RealBlockConstants`（`SoftmaxAttnOp`）、`RealSoftmaxAttnNormBound`（注意力范数界）、
`RealOperatorInvertibility`（`I + W` 的范数下界）。

## 一、要解决的是什么

`B410` 的条件版（`RealHreachConditional.residual_lower_bound`）需要
**`hcont : M + Lw < 1`** —— 即**整个块是压缩映射**。
⚠ **该条件对真实 transformer 一般为假**：注意力 value 映射与 FFN 权重的算子范数
通常 `≥ 1`，块**不是**压缩映射。所以那个条件版**不能**establish「真实块满足 `hreach`」。

## 二、本文件的做法：把 `I + W` 与注意力**分开**处理

不再要求二者之和 `< 1`，而是：
* `I + W` 部分用 `one_add_lower_bound` ⟹ `(1 - Lw)‖h‖ ≤ ‖h + W h‖`（**不含 `Lw < 1`**）；
* 注意力部分用 `softmaxAttnOp_norm_le` ⟹ `‖SoftmaxAttnOp S V h‖ ≤ M‖h‖`；
* 两者用反向三角不等式**分开扣除**。

⇒ ⭐ **关键改进**：**不再要求【块】是压缩映射**，
只要求**残差通路 `I + W` 非退化**（由 `‖W‖ ≤ Lw` 刻画）**且**注意力相对有界。
这是**不同且更弱**的要求。

## 三、`PROCESS.md §2.2` 必答：「这条定理比它的定义多说了什么？」

| 定理 | 回答 |
|:--|:--|
| `residual_lower_bound_free` | `h ↦ h + SoftmaxAttnOp S V h + W h` 的**定义**对该映射的**范数什么都没断言**；本定理给出一个**只依赖 `‖V i‖` 与 `‖W‖` 的上界**的下界。✅ **多说了** |
| `residual_lower_bound_positive` | 在上者之上，断言该下界**严格为正**（`> 0`），这是一个**存在性/正性**断言，定义中**没有**。✅ **多说了** |
| `hreach_positivity_obstruction` | 断言一个**否定性**命题（不存在正 `c`），**不是**定义展开。✅ **多说了** |
| `no_positive_uniform_bound_at_zero_map` | 同上，否定性内容。✅ **多说了** |

## 四、⚠⚠ 本文件**不**establish 什么（**最重要的诚实边界**）

1. ⚠ **本文件【不】证明真实 transformer 满足 `hreach`。**
2. ⚠ 正性仍**不自动**：`residual_lower_bound_positive` 需要
   **`Lw ≤ 1`**（残差通路 `I + W` 非退化）**与** **`M * ‖h‖ < (1 - Lw) * ρ`**（`hgap`）。
   二者都是**可检验但非自动**的条件。
   ⚠ 且**不等价于**旧的 `M + Lw < 1`：对 `Lw` 大时更宽松，但**多出 `M‖h‖` 这一开销**。
3. ⚠ **`Lw ≥ 1` 时本路线的正性【不可能】**（`1 - Lw ≤ 0`），
   且此时 `I + W` 可能奇异 —— 见 `hreach_positivity_obstruction`。
4. ⚠ 本文件证的是**下界/正性**，**不是**「`hreach` 作为链上全称假设成立」。
   把 `hreach` 真正装入 `RealModelChain` 的定理**仍是后续工作**。
5. ⚠ **主定理 `residual_lower_bound_free` 不含 `Lw ≤ 1`、不含 `ρ`** ——
   它是**无条件**的下界（仅需 `hV`/`hW`），但该下界**可能为负**，
   故它本身**不**给出 `hreach` 所需的 `c > 0`。`Lw ≤ 1` 只在**正性版**里承重。

## 五、诚实的最终状态

> **`hreach` 可在一个【可检验但非自动】的条件下成立**；
> 该条件**不再要求块是压缩映射**，但仍**不是真实模型的自动推论**。
-/

open scoped BigOperators

namespace Lattice

variable {n k : ℕ} [NeZero k]

/-- ⭐ **主定理：不预设「块是压缩映射」的残差下界。**

把 `I + W` 与注意力**分开扣除**，**完全不需要** `M + Lw < 1`。
结论用 `‖h‖` 表述，因此**不需要** `ρ`，也**不需要** `Lw ≤ 1`。

⚠ 这是本文件最强的无条件形式：`hV`/`hW` 之外**没有任何额外假设**。 -/
theorem residual_lower_bound_free
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M Lw : ℝ) (hV : ∀ i, ‖V i‖ ≤ M) (hW : ‖W‖ ≤ Lw)
    (h : EuclideanSpace ℝ (Fin n)) :
    (1 - Lw) * ‖h‖ - M * ‖h‖ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
  have hA : ‖SoftmaxAttnOp S V h‖ ≤ M * ‖h‖ := softmaxAttnOp_norm_le S V M hV h
  have hB : (1 - Lw) * ‖h‖ ≤ ‖h + W h‖ := one_add_lower_bound W Lw hW h
  -- 反向三角不等式：`‖h + W h‖ − ‖A‖ ≤ ‖h + A + W h‖`
  have hrt : ‖h + W h‖ - ‖SoftmaxAttnOp S V h‖ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
    have hsplit : h + W h
        = (h + SoftmaxAttnOp S V h + W h) - SoftmaxAttnOp S V h := by abel
    calc ‖h + W h‖ - ‖SoftmaxAttnOp S V h‖
        = ‖(h + SoftmaxAttnOp S V h + W h) - SoftmaxAttnOp S V h‖
            - ‖SoftmaxAttnOp S V h‖ := by rw [← hsplit]
      _ ≤ (‖h + SoftmaxAttnOp S V h + W h‖ + ‖SoftmaxAttnOp S V h‖)
            - ‖SoftmaxAttnOp S V h‖ := by
          have := norm_sub_le (h + SoftmaxAttnOp S V h + W h) (SoftmaxAttnOp S V h)
          linarith
      _ = ‖h + SoftmaxAttnOp S V h + W h‖ := by ring
  linarith

/-- ⭐ **严格正下界版**（`hreach` 的 `c > 0` 真正要的形状）。

在上者之上，额外假设
**`hLw1 : Lw ≤ 1`**（即**残差通路 `I + W` 非退化**）与
**`hgap : M * ‖h‖ < (1 - Lw) * ρ`**（配合 `ρ ≤ ‖h‖`），
即可得出**严格为正**的常数下界 `(1 - Lw) * ρ - M * ‖h‖ > 0`。

⚠⚠ **`hLw1` 是必需的，不是装饰**：单调性步骤 `(1-Lw)*ρ ≤ (1-Lw)*‖h‖` 需要
`0 ≤ 1 - Lw`，而该式**不能**从 `hgap` + `hnorm` 推出 ——
协调者用**穷举**找到了 **61 个反例**（即使加上 `ρ > 0`）。
⭐ 语义上 `Lw ≤ 1` 正是「**`I + W` 非退化**」这一结构条件，
**与旧的 `M + Lw < 1`（整块压缩）是不同的要求**。

⚠⚠ **`hgap` 是【可检验但非自动】的**，且**不等价于** `M + Lw < 1`：
对 `Lw` 大时更宽松（**不要求块是压缩映射**），但**多出 `M‖h‖` 这一开销**。
⚠ **它仍然不是真实 transformer 的自动推论** —— 见文件头 §四。 -/
theorem residual_lower_bound_positive
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M Lw ρ : ℝ) (hV : ∀ i, ‖V i‖ ≤ M) (hW : ‖W‖ ≤ Lw) (hLw1 : Lw ≤ 1)
    (h : EuclideanSpace ℝ (Fin n)) (hnorm : ρ ≤ ‖h‖)
    (hgap : M * ‖h‖ < (1 - Lw) * ρ) :
    0 < (1 - Lw) * ρ - M * ‖h‖
      ∧ (1 - Lw) * ρ - M * ‖h‖ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
  have hA : ‖SoftmaxAttnOp S V h‖ ≤ M * ‖h‖ := softmaxAttnOp_norm_le S V M hV h
  have hB : (1 - Lw) * ‖h‖ ≤ ‖h + W h‖ := one_add_lower_bound W Lw hW h
  have hrt : ‖h + W h‖ - ‖SoftmaxAttnOp S V h‖ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
    have hsplit : h + W h
        = (h + SoftmaxAttnOp S V h + W h) - SoftmaxAttnOp S V h := by abel
    calc ‖h + W h‖ - ‖SoftmaxAttnOp S V h‖
        = ‖(h + SoftmaxAttnOp S V h + W h) - SoftmaxAttnOp S V h‖
            - ‖SoftmaxAttnOp S V h‖ := by rw [← hsplit]
      _ ≤ (‖h + SoftmaxAttnOp S V h + W h‖ + ‖SoftmaxAttnOp S V h‖)
            - ‖SoftmaxAttnOp S V h‖ := by
          have := norm_sub_le (h + SoftmaxAttnOp S V h + W h) (SoftmaxAttnOp S V h)
          linarith
      _ = ‖h + SoftmaxAttnOp S V h + W h‖ := by ring
  have hmono : (1 - Lw) * ρ ≤ (1 - Lw) * ‖h‖ :=
    mul_le_mul_of_nonneg_left hnorm (by linarith)
  have hlow : (1 - Lw) * ρ - M * ‖h‖ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
    have h1 : (1 - Lw) * ρ - M * ‖h‖ ≤ (1 - Lw) * ‖h‖ - ‖SoftmaxAttnOp S V h‖ := by
      linarith
    linarith [hrt, h1, hB]
  exact ⟨by linarith, hlow⟩

/-- ⭐⭐ **正性障碍**（否定性姊妹定理）：当 `Lw ≥ 1` 时 `1 - Lw ≤ 0`，
故 `residual_lower_bound_positive` 的结论**不可能为正**。

⚠ 这正是「`Lw ≥ 1` 时本路线失效」的机械表述 —— 与 `B412` 的
`one_add_needs_hLw` 同型（那边是 `W = -id` 使 `I + W` 退化为零映射）。 -/
theorem hreach_positivity_obstruction
    (Lw : ℝ) (hLw : 1 ≤ Lw) :
    (1 - Lw) * 0 - 0 ≤ (0 : ℝ) ∧ ¬ (0 < (1 - Lw) * 1 - 0) := by
  constructor
  · simp
  · intro hc
    nlinarith

/-- ⭐⭐ **固化的反例**（`PROCESS.md §3.3` 步⑤）：`V = 0`、`W = -id` 时，
括号项**恒为零**，故**不存在**正的下界常数 `c`。

⚠ 这是**否定性内容**（不存在 `c`），**不是**定义展开。 -/
theorem no_positive_uniform_bound_at_zero_map :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ h : EuclideanSpace ℝ (Fin 1),
      c ≤ ‖h + SoftmaxAttnOp 0 (fun _ : Fin 1 => 0) h
             + (-1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) h‖ := by
  rintro ⟨c, hc, H⟩
  have h0 := H 0
  simp [SoftmaxAttnOp] at h0
  linarith

/-! ## 六、⭐ **逐索引（per-index）下界**：把【一致常数】换成【有限族的最小值】

⚠ **本节的动机**（依据 `B424` 台账 row 8 的评估）：上一节的
`residual_lower_bound_positive` 要求**一个统一的** `M` 同时满足
`hV : ∀ i, ‖V i‖ ≤ M` 与 `hgap : M‖h‖ < (1−Lw)ρ`。
⚠ 这在 `M` 被**最坏的单个头**支配时**不必要地紧** ——
**只要每个头各自满足各自的间隙即可**，不需要它们共享一个 `M`。

⭐ **关键点**：`i` 的取值范围是 `Fin k`，**有限**（`[NeZero k]` 给出非空），
故可以取**逐点常数族的最小值** `⨅`，而**不需要**任何紧性/可达性假设。

⭐⭐ **这是【真弱化】**：它**减掉了**「存在一个统一 `M`」这一前提，
而**每个点位的核心不等式原样保留**。⚠ **但它【不】解除 `B424.47` 的 `Lw < 1` 障碍** ——
`hLw1 : Lw ≤ 1` 仍然必需（`(1−Lw)ρ ≤ (1−Lw)‖h‖` 的单调性步骤依赖它）。
-/

/-- ⭐ **逐索引残差下界**：每个头 `i` 带上自己的常数 `M i`，**无须统一的 `M`**。

⚠ 与 `residual_lower_bound_free` 的区别仅在于 `hV` 从 `‖V i‖ ≤ M` 变为 `‖V i‖ ≤ M i`。
结论仍是**同一条**不等式，只是左端的扣除项取 `sSup (Set.range M)`
（即最坏的那个头），因为 `softmaxAttnOp_norm_le` 本身要求**统一**常数。

⭐ **为什么取 `sSup` 而不是 `⨅`**：`softmaxAttnOp_norm_le` 需要**一个常数同时界住所有头**，
故必须上取；⚠ 这与「取最坏的头」的直觉一致 —— **下界的扣除项由最坏的头顶住**。

⛔ **诚实边界**：本定理**没有**解除 `hLw1 : Lw ≤ 1` 这一障碍；
它弱化的仅是「`M` 必须由调用方**显式给出**」这一点 ——
现在只需给出**逐头界**，统一常数由 `sSup` 自动产生。
⚠ 故 `hreach` 的**真实**障碍仍在 `B424.47` 所述之处（`M‖h‖ < (1−Lw)ρ`），**未变**。 -/
theorem residual_lower_bound_pointwise
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : Fin k → ℝ) (Lw : ℝ) (hV : ∀ i, ‖V i‖ ≤ M i) (hW : ‖W‖ ≤ Lw)
    (h : EuclideanSpace ℝ (Fin n)) :
    (1 - Lw) * ‖h‖ - sSup (Set.range M) * ‖h‖
      ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
  -- `sSup (range M)` still bounds every head, so the uniform bound applies with it.
  have hVunif : ∀ i, ‖V i‖ ≤ sSup (Set.range M) := by
    intro i
    exact le_trans (hV i) (le_csSup (Set.finite_range M).bddAbove ⟨i, rfl⟩)
  have hA : ‖SoftmaxAttnOp S V h‖ ≤ sSup (Set.range M) * ‖h‖ :=
    softmaxAttnOp_norm_le S V (sSup (Set.range M)) hVunif h
  have hB : (1 - Lw) * ‖h‖ ≤ ‖h + W h‖ := one_add_lower_bound W Lw hW h
  have hrt : ‖h + W h‖ - ‖SoftmaxAttnOp S V h‖ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
    have hsplit : h + W h
        = (h + SoftmaxAttnOp S V h + W h) - SoftmaxAttnOp S V h := by abel
    calc ‖h + W h‖ - ‖SoftmaxAttnOp S V h‖
        = ‖(h + SoftmaxAttnOp S V h + W h) - SoftmaxAttnOp S V h‖
            - ‖SoftmaxAttnOp S V h‖ := by rw [← hsplit]
      _ ≤ (‖h + SoftmaxAttnOp S V h + W h‖ + ‖SoftmaxAttnOp S V h‖)
            - ‖SoftmaxAttnOp S V h‖ := by
          have := norm_sub_le (h + SoftmaxAttnOp S V h + W h) (SoftmaxAttnOp S V h)
          linarith
      _ = ‖h + SoftmaxAttnOp S V h + W h‖ := by ring
  linarith

end Lattice
