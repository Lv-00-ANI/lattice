import Mathlib
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Architectures.RealBlockConstants
import Lattice.Lib.Chain.RealModelChain
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Attention.RealSoftmaxAttnNormBound
/-!
# LATTICE：`hreach` 的**条件版**下界 + **无条件版为假**的固化反例

## 背景：`hreach` 是被传入的前提，三文件均自陈不证明它

`RealModelChain.lean:234-240`（镜像在 `:283-288`、`:342-347`）把
`hreach : ∀ j ≤ m, c ≤ ‖ChainFwd … j x + SoftmaxAttnOp S V (ChainFwd … j x) + W (ChainFwd … j x)‖`
作为**显式前提**传入。三文件**逐字自陈不证明**真实块链满足它：

* `RealModelChain.lean:58-60`：「**诚实边界**：本文件**不证明**真实 transformer 块链满足 `hreach`
  （那需要「块输出范数下界」的实质分析，**是后续独立立项**）」
* `RealModelChainHetero.lean:54-55`：同
* `RealMixedAttention.lean:68`：同

本文件**不**声称证明了 `hreach`。它做两件**可机器验证**的事：

1. **条件版下界**（§一）：给出 `hreach` 在**收缩前提**下**成立**的充分条件
   （`M + Lw < 1` 且 `ρ ≤ ‖h‖`）。
2. ⭐ **无条件版为假**（§二）：把反例**固化为定理**，使「不假设 `c` 就能拿到下界」
   这一错误陈述**无法复活**（依 `PROCESS.md §3.3` 第 ⑤ 步「把反例固化为定理」）。

---

## ⭐⭐ 非平凡性自答（`PROCESS.md §2.2` 要求逐字回答）

> **「这条定理比它的**定义**多说了什么？」**

**§一 `residual_lower_bound`**：定义只给出 `‖h + a + b‖` 这一**式子**；
定理给出「在 `M + Lw < 1` 且 `ρ ≤ ‖h‖` 下，该式 ≥ `(1 - M - Lw) * ρ`」——
一个**正的、显式的下界**。⚠ 证明体**不是** `rfl`、也不是 `fun h => h`
（先证两个算子范数界，再反向三角不等式）；§三 机器验证**去掉 `hcont` 后命题为假**。

**§二 `hreach_unconditional_false`**：⚠ **不是**「`残差(0) = 0`」——
那只是定义展开（`ChainFwd Fs 0 x = x`，`(V i) 0 = 0`），**什么也没多说**。
本定理的内容是**否定性**的：**不存在**正的 `c` 使下界对**所有** `h` 成立。
这是一个**不可能性**陈述，不可能由定义展开或 `rfl` 得到。

---

## ⚠⚠ 必须携带的诚实边界（勿让定理名过度声称）

### 1. `M + Lw < 1` 对**真实 transformer 一般是假的**

真实 transformer 的注意值映射与 FFN 权重通常 `‖·‖ ≥ 1`，块**不是压缩映射**。
⇒ 本定理给出的是「**非退化输入上的下界**」，
**不是**「真实 transformer 块满足 `hreach`」。**不得**据本文件声称后者。

### 2. 真正的结构性障碍：`I + W` 奇异时**没有现成载体**

要**无条件**证明 `hreach`，需要 `(I + W)` 的**奇异值下界**（可逆性界）。
⚠ 本仓库现有载体中**没有**最小奇异值 / 可逆性下界的设施
（`RealSVD.lean` 有 SVD 结构，但未提供 `σ_min` 下界引理）。
⇒ 这是**真正的结构障碍**。本文件的条件版正是**绕开**它：
用 `M + Lw < 1` **替代**对 `I + W` 的谱估计。
-/

namespace Lattice

variable {n k : ℕ} [NeZero k]

/-! ## 一、条件版下界（本文件的正面结果） -/

/-- **`SoftmaxAttnOp` 在零点为零**。

⚠ **本引理单独看是定义展开**，但它使 §二 的反例可**精确计算**。 -/
theorem softmaxAttnOp_zero (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    SoftmaxAttnOp S V 0 = 0 := by
  unfold SoftmaxAttnOp
  simp

-- ⚠⚠ 引用限定（B410 审计订正，协调者落盘）
--
-- 本定理的名字暗示「对一般 `S/V/W` 的 `hreach` 被推翻」，但其**陈述把 `S`、`V`、`W`
-- 分别固定在 `0`、`negActivation`、`0`**，**并不对一般算子量化**。
-- ⇒ 引用时必须写明该限定，**不得**读作「真实 transformer 的 `hreach` 被推翻」。
--
-- ⭐ 本定理的逻辑内容 = 一条**通用模式** + 一个定义性事实（`f 0 = 0`）：
--     theorem no_positive_uniform_lower_bound_of_zero {X} [NormedAddCommGroup X]
--         (f : X → X) (hf : f 0 = 0) : ¬ ∃ c : ℝ, 0 < c ∧ ∀ h : X, c ≤ ‖f h‖
--   该模式**不提注意力、不提 softmax**，已由协调者独立编译通过（exit 0）。
--   本定理是它取 `f h := h + SoftmaxAttnOp 0 negActivation h + 0 h` 的实例。
-- ⇒ ⚠ **其中没有注意力特有的数学。** 但 `:= rfl` **关不掉**它，
--   故项目标准的「`rfl` ⇒ 空洞」判据**不触发** —— 这不是空洞，是**内容偏薄**。
-- ⭐ **要引用这条结果，请引用上面的通用模式（可复用），而不是本实例。**


-- MERGED (B410): the duplicate re-proof of `softmaxAttnOp_norm_le` that lived here
-- was removed; the canonical version is imported from RealSoftmaxAttnNormBound.
-- Same name, same statement, so every use below is unchanged.
-- Rationale for keeping the canonical copy there is recorded in that file's header.
theorem residual_lower_bound
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M Lw ρ : ℝ) (hV : ∀ i, ‖V i‖ ≤ M)
    (hW : ‖W‖ ≤ Lw) (hcont : M + Lw < 1)
    (h : EuclideanSpace ℝ (Fin n)) (hnorm : ρ ≤ ‖h‖) :
    (1 - M - Lw) * ρ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
  have hA : ‖SoftmaxAttnOp S V h‖ ≤ M * ‖h‖ := softmaxAttnOp_norm_le S V M hV h
  have hB : ‖W h‖ ≤ Lw * ‖h‖ := by
    calc ‖W h‖ ≤ ‖W‖ * ‖h‖ := ContinuousLinearMap.le_opNorm W h
      _ ≤ Lw * ‖h‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg h)
  have hnh : (0:ℝ) ≤ ‖h‖ := norm_nonneg h
  have hMh : M * ‖h‖ ≤ M * ‖h‖ := le_rfl
  -- 反向三角不等式：‖h‖ ≤ ‖h+a+b‖ + ‖a‖ + ‖b‖ ⟹ ‖h‖ - ‖a‖ - ‖b‖ ≤ ‖h+a+b‖
  have htri : ‖h‖ - ‖SoftmaxAttnOp S V h‖ - ‖W h‖
      ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := by
    have h1 : ‖h‖ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ + ‖SoftmaxAttnOp S V h‖ + ‖W h‖ := by
      calc ‖h‖ = ‖(h + SoftmaxAttnOp S V h + W h) - SoftmaxAttnOp S V h - W h‖ := by
              congr 1; abel
        _ ≤ ‖(h + SoftmaxAttnOp S V h + W h) - SoftmaxAttnOp S V h‖ + ‖W h‖ :=
              norm_sub_le _ _
        _ ≤ (‖h + SoftmaxAttnOp S V h + W h‖ + ‖SoftmaxAttnOp S V h‖) + ‖W h‖ := by
              have := norm_sub_le (h + SoftmaxAttnOp S V h + W h) (SoftmaxAttnOp S V h)
              linarith
    linarith
  have hlow : (1 - M - Lw) * ‖h‖ ≤ ‖h‖ - ‖SoftmaxAttnOp S V h‖ - ‖W h‖ := by
    have : ‖SoftmaxAttnOp S V h‖ + ‖W h‖ ≤ (M + Lw) * ‖h‖ := by
      have : M * ‖h‖ + Lw * ‖h‖ = (M + Lw) * ‖h‖ := by ring
      linarith
    linarith
  calc (1 - M - Lw) * ρ ≤ (1 - M - Lw) * ‖h‖ := by
        apply mul_le_mul_of_nonneg_left hnorm
        linarith
    _ ≤ ‖h‖ - ‖SoftmaxAttnOp S V h‖ - ‖W h‖ := hlow
    _ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ := htri

-- ⭐ **与 `RealHreachClosed.lean` 的分工（B416 协调者裁定）**
--
-- 本定理**不退役、不删除**，且**未**被 `RealHreachClosed` 取代 —— 它是**更强的特例**：
--   · 本定理前提 `M + Lw < 1`【严格强于】新形式所需，而**假设更强 ⟹ 结论更强**：
--     它给出**显式的正 `c`**（`0 < (1 - M - Lw) * ρ`）；
--   · `RealHreachClosed.residual_lower_bound_free` 假设最少，但**可能为负**，
--     `residual_lower_bound_positive` 需 `Lw ≤ 1` **且** `M‖h‖ < (1-Lw)ρ`。
-- ⇒ ⭐ **两者并存，各司其职**：用新形式（前提更弱、对真实模型更可能成立）
--   **或**用本定理（前提更强、但给出显式正下界）。**引用时须指明用的是哪一个。**
-- ⚠ 本文件与 `RealHreachClosed` **importer 均为 0**（实测），故退役与否**无机械影响** ——
--   这是**治理问题**（哪个陈述是权威），而**不是**编译问题。
-- ⚠ **不删除的理由**：删掉会**销毁一条真定理**并**失去历史记录**（`B243.4`；
--   `extractLayer`/`EvenSat` 同类处置均为「登记而不删」）。

/-- ⭐ **正下界版**（`hreach` 真正要的形状）：在 `ρ > 0` 与 `M + Lw < 1` 下，
残差被一个**严格正**的常数下界控住。

⭐ **比定义多说了什么**：给出 `0 < (1 - M - Lw) * ρ`（**严格正**）
且 `≤ 残差` —— 这正是 `hreach` 所要求的「`c` 存在且显式」。
`hcont` 与 `hrho` 在此**都承重**：去掉任一个，结论不再给出**正**下界。

⚠ **本定理【不】声称真实 transformer 满足前提** —— 见文件头 §1 诚实边界
（`M + Lw < 1` 对真实块一般不成立）。 -/
theorem residual_lower_bound_pos
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M Lw ρ : ℝ) (hV : ∀ i, ‖V i‖ ≤ M)
    (hW : ‖W‖ ≤ Lw) (hcont : M + Lw < 1)
    (hrho : 0 < ρ)
    (h : EuclideanSpace ℝ (Fin n)) (hnorm : ρ ≤ ‖h‖) :
    0 < (1 - M - Lw) * ρ
      ∧ (1 - M - Lw) * ρ ≤ ‖h + SoftmaxAttnOp S V h + W h‖ :=
  ⟨mul_pos (by linarith) hrho,
   residual_lower_bound S V W M Lw ρ hV hW hcont h hnorm⟩

/-! ## 二、⭐⭐ 无条件版**为假**（固化反例，防复活）

> 依 `PROCESS.md §3.3` 第 ⑤ 步：**把反例固化为定理**。
>
> ⚠ **本条【不是】「残差(0) = 0」**（那只是定义展开）。
> 本条是**否定性**的：**不存在**正的 `c` 使下界对**所有** `h` 成立。

机制：取 `S = 0`、`W = 0`、`V i = -I`（对每个 `i`）。
则对**任意** `h`，`SoftmaxAttnOp S V h = ∑ softmax(0)ᵢ • (-h) = -(∑ softmax(0)ᵢ) • h = -h`
（权重和 = 1）⟹ 括号恒为 `0` ⟹ 任何正的 `c` 都被否证。 -/

/-- ⭐ **承载反例的具体载体**：`S = 0`、`V i = -1`（恒等映射的相反数）、`W = 0`。 -/
noncomputable def negActivation :
    Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fun _ => -1

/-- ⭐⭐ **无条件版为假**：不存在正的 `c` 使残差下界对任意 `h` 成立。

`¬ ∃ c > 0, ∀ h, c ≤ ‖h + SoftmaxAttnOp S V h + W h‖`，
见证载体 `S = 0, V = negActivation, W = 0`。 -/
theorem hreach_unconditional_false :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ h : EuclideanSpace ℝ (Fin n),
        c ≤ ‖h + SoftmaxAttnOp (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
                negActivation h
              + (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) h‖ := by
  rintro ⟨c, hc, H⟩
  have hval := H 0
  have hcancel : (0 : EuclideanSpace ℝ (Fin n))
      + SoftmaxAttnOp (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ)) negActivation 0
      + (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) 0 = 0 := by
    rw [softmaxAttnOp_zero]
    simp
  rw [hcancel, norm_zero] at hval
  exact absurd hval (not_le.mpr hc)

/-! ## 三、承重性见证（`hcont` 去掉即为假） -/

/-- ⭐ **承重性见证**：`W = 0`、`V i = -I` 时，对**任意** `h` 括号**恒等于 0**。

⇒ 任何正的 `c` 都不成立（见 `hreach_unconditional_false`），
且下界系数 `1 - M - Lw` 在 `M ≥ 1` 时**非正**，界**不提供正下界**。 -/
theorem residual_vanishes_witness (h : EuclideanSpace ℝ (Fin n)) :
    h + SoftmaxAttnOp (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
          negActivation h
        + (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) h = 0 := by
  -- 关键：softmax(0) 是概率分布（权重和 = 1），故加权和 = -h，残差 = h + (-h) + 0 = 0
  have hsum : SoftmaxAttnOp (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
        negActivation h = -h := by
    unfold SoftmaxAttnOp negActivation
    simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply,
               ContinuousLinearMap.one_apply]
    -- 令 w i := softmax 0 i，则 ∑ i, w i • (-h) = -(∑ i, w i) • h = -1 • h = -h
    simp only [smul_neg, Finset.sum_neg_distrib]
    -- 令 w x := softmax 0 x，则 ∑ x, w x • h = (∑ x, w x) • h = 1 • h = h
    rw [← Finset.sum_smul, softmax_sum_one, one_smul]
  rw [hsum, ContinuousLinearMap.zero_apply]
  simp

end Lattice
