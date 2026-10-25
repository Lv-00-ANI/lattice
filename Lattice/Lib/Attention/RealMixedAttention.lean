import Mathlib
import Lattice.Lib.Attention.RealCausalAttention
import Lattice.Lib.Attention.RealAttentionLipschitz
import Lattice.Lib.Attention.RealSoftmaxLipschitz
import Lattice.Lib.Architectures.RealBlockConstants
import Lattice.Lib.Chain.RealModelChainHetero
import Lattice.Lib.Architectures.RealBlockLipschitz
/-!
# LATTICE: 混合架构（双向 + 因果注意力）—— 行随机凸组合统一与异质链端到端

VERIFICATION.md §5「结构」行「混合架构（含因果/双向混合）」的实现：
把 RealModelChainHetero 的异质块链实例化为**每块类型不同但都有 Lipschitz
常数**的混合 transformer 前向链——前 p 块用**双向注意力**（full softmax，
RealAttention/RealBlockConstants），后 m−p 块用**因果注意力**（causal masked
softmax，RealCausalAttention），每块仍为
Block(z) = RMSNorm(z + Attn(z) + W_i z)（W_i 逐块不同，异质骨架）。

**关键观察**：两类注意力都产生**行随机权重**（非负 + 和 1）：
  · 双向：softmax_nonneg / softmax_sum_one（RealAttention）；
  · 因果：causalSoftmax_nonneg / causalSoftmax_sum_one（RealCausalAttention）。
⟹ (a) 两类块的 Lipschitz 组装完全相同（block_lipschitz_bound 只看权重
的凸组合性质，见 mixed_block_lipschitz：抽象注意力 A 的块界，双向/因果
共用）；(b) **权重随输入变化的数字注意力常数也完全相同**——本文件证明
因果 softmax 的坐标 Lipschitz（与 RealSoftmaxLipschitz.softmax_lipschitz_coord
同构，掩码位置两侧都为零、可见前缀内用 abs_div_sub 分解），常数同为
(k+1)·e^{4M'}，⟹ causal_attention_lipschitz_numeric 的常数 = 双向
attention_lipschitz_numeric 的常数 = attnNumericConstant S M B。
故混合链的逐块常数统一为 heteroBlockLb S W M B c i（差异只来自 ‖W_i‖）。

定理链（全部数字常数闭式，无 open 假设）：
  1. causal_convComb_lipschitz：因果权重（causalSoftmax 输出，行随机）的
     固定权重凸组合 Lipschitz ≤ M·‖x−y‖（复用 convComb_lipschitz_prob，
     它只需要权重非负 + 和 1）；
  2. causalDenom_lower / causalDenom_diff_bound：因果分母（掩码分母）的
     下界与差界（RealSoftmaxLipschitz 的 z_bound_lower / z_diff_bound 的
     因果版：掩码只截去非负项，界不放大）；
  3. causal_softmax_lipschitz_coord：因果 softmax 坐标 Lipschitz
     |w_j(x) − w_j(y)| ≤ (k+1)·e^{4M}·‖x−y‖∞；
  4. causal_weight_l1_diff_bound：Σ_j |w_j(x) − w_j(y)|
     ≤ k·(k+1)·e^{4M'}·LinfNorm（逐坐标求和，维度因子 k）；
  5. causal_attention_lipschitz_numeric（核心之一）：因果注意力算子
     A(x) = Σ_j causalSoftmax(Sx) q j • (V_j x) 的完整数字 Lipschitz
     = M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)——与双向常数**完全相同**
     （实例化 attention_lipschitz_weighted，w = causalSoftmax∘S 逐行）；
  6. mixed_block_lipschitz：抽象注意力 A（La-Lipschitz）的块组装
     RMSNorm∘(id+A+W) ≤ (√n/c)·(1+La+‖W‖)——双向/因果共用同一组装
     （block_lipschitz_bound：加法/残差/复合组合律）；
  7. causal_model_block_lipschitz_numeric：因果块（CausalModelBlock）的
     数字 Lipschitz = (√n/c)·(1 + attnNumericConstant + ‖W‖)
     （**⚠ v14（B53）** 域前提设在**内层残差和**上、点对形式）；
  8. mixed_block_lipschitz_numeric：混合块（MixedBlock，按 i < p 分派
     双向/因果）逐块 Lb_i-Lipschitz（Lb_i = heteroBlockLb S W M B c i）；
  9. mixed_chain_numeric_bound（核心）：m 块混合链端到端
     ≤ (∏ᵢ Lb_i)·‖x−y‖——实例化**点对版**链骨架
     `RealModelChain.chainN_dom_bound`（= RealModelChainHetero 的块函数替换，
     常数同为 heteroBlockLb）；**⚠ 额外带可满足的 `hreach`**（B53 降级）；
  10. mixed_chain_numeric_bound_split：∏ 按 p 拆分
      (∏_{i<p} Lb_i)·(∏_{p≤i<m} Lb_i)·‖x−y‖（Finset.prod_range_add）；
  11. mixed_to_causal / mixed_to_encoder：p=0（全因果）/ p=m（全双向）
      退化特例——全双向链即 RealModelChainHetero 的异质链
      （hetero_chain_numeric_bound），全因果链是本文件因果块链。

⚠ **B53 修复总体形态**：本文件的域前提（RMSNorm 定义域）**一律改到 RMSNorm 的
实际输入**即**内层残差和** `z + A z + W z` 上（**不是** `z` 本身），且改为
**点对**形式（旧 `hxdom : ∀ z` 与 `hc : 0 < c` 矛盾、使定理空洞）。
链式定理（9/10/11）另带**显式、可满足**的 `hreach`（链上可达性，**有意作为
前提传入**，B53.7 允许的降级），本文件**不证明**真实混合链满足它。

诚实假设（模型无关，与 RealBlockConstants / RealModelChainHetero 相同）：
  · [NeZero n] [NeZero k]：嵌入维数/注意力指标非零（块数字常数所需）；
  · hc : 0 < c：RMSNorm 定义域范数下界为正（Lf = √n/c 的分母）；
  · hM：value 投影界 max‖Vᵢ‖ ≤ M；
  · hB：数据范数上界 ∀z, ‖z‖ ≤ B（softmax 分数有界 |S z| ≤ ‖S‖·B 的前提）；
  · hx、hy（单块/逐块定理）：**点对**定义域前提，设在 **RMSNorm 的实际输入**
    即**内层残差和**上：`c ≤ ‖x + A x + W x‖`、`c ≤ ‖y + A y + W y‖`。
    —— **⚠ v14（B53 修复）**：旧稿此处写 `hxdom：∀z, c ≤ ‖z‖`（**去掉了限定、
    暗示全空间**），与 `hc : 0 < c` **矛盾**（`z := 0` ⟹ `c ≤ 0`）
    ⟹ **前提不可满足、定理空洞**（CORRECTIONS B53）。
    ⚠ **位置要点**：是对**内层和**而不是对 `x` 设域——RMSNorm 作用在内层和上，
    对 `x` 设域**无法**支撑证明（会需要 `‖x‖ ≤ ‖u‖` 对任意 `u`，是**假的**）。
    **可满足性见证**：取 `A := 0`（恒等/零注意力）、`W := 0`（零 FFN）、
    `x = y = c • e₀` ⟹ 内层和 = `c • e₀`，`‖·‖ = c` 成立；
  · hreach（链式定理 7/8/9/10）：**链上每个中间激活都在定义域内**。
    **⚠ 有意作为前提传入**（B53 允许的降级；**可满足**：恒等链 + `c • e₀`）。
    **诚实边界**：本文件不证真实混合块链满足 `hreach`。
因果块的查询位置 q : Fin k 是自由参数（本框架按既有单凸组合块建模：
每个注意力块输出一个凸组合，q 对应解码器某位置；完整解码器逐位置
掩码的向量化建模留给后续——数字常数与 q 无关，本文件结论对任意 q 成立）。

关键诚实点：因果版数字注意力常数与双向版**完全相同**（同为
attnNumericConstant），故混合链的常数差异只来自逐块 FFN 权重 ‖W_i‖
（heteroBlockLb 逐块不同）；若未来引入常数不同的注意力变体，
hetero 骨架（hetero_chain_numeric_bound，RealModelChainHetero）直接
承接，本文件不改动任何既有文件。全部证明无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 定理一：因果权重的凸组合 Lipschitz（固定权重版）
因果权重 w = causalSoftmax s i 是行随机分布（causalSoftmax_nonneg +
causalSoftmax_sum_one，RealCausalAttention），⟹ 固定权重的凸组合映射
x ↦ Σ_j w_j·(V_j x) 是 M-Lipschitz（M = max‖V_j‖）——复用
convComb_lipschipsitz_prob（它只需要权重非负 + 和 1，不看权重来源）。-/

theorem causal_convComb_lipschitz {n : ℕ} (s : Fin n → ℝ) (i : Fin n)
    (V : Fin n → E →L[ℝ] F) (M : ℝ) (hM : ∀ j : Fin n, ‖V j‖ ≤ M) :
    ∀ x y,
      ‖(∑ j : Fin n, causalSoftmax s i j • (V j x)) - (∑ j : Fin n, causalSoftmax s i j • (V j y))‖
        ≤ M * ‖x - y‖ := by
  intro x y
  exact convComb_lipschitz_prob (causalSoftmax s i) V M
    (fun j => causalSoftmax_nonneg s i j) (causalSoftmax_sum_one s i) hM x y

/-! ## 引理一：因果分母（掩码分母）下界
causalDenom x i = Σ_{k ≤ i} exp(x k) ≥ exp(x i) ≥ e^{−M}（x i ≥ −M，
自身项为正 + 掩码内各项非负）——softmax_lipschitz_coord 中
z_bound_lower 的因果版。 -/

lemma causalDenom_lower {k : ℕ} (M : ℝ) (x : Fin k → ℝ)
    (hx : ∀ j : Fin k, -M ≤ x j) (i : Fin k) :
    Real.exp (-M) ≤ causalDenom x i := by
  calc
    Real.exp (-M) ≤ Real.exp (x i) := Real.exp_le_exp.mpr (hx i)
    _ ≤ causalDenom x i := by
          unfold causalDenom
          have hnonneg : ∀ j : Fin k, 0 ≤ (if j ≤ i then Real.exp (x j) else 0) := by
            intro j
            by_cases h : j ≤ i
            · simp [h]
              exact le_of_lt (Real.exp_pos (x j))
            · simp [h]
          have hle : Real.exp (x i) ≤ ∑ j : Fin k, (if j ≤ i then Real.exp (x j) else 0) := by
            simpa using
              (Finset.single_le_sum (s := Finset.univ)
                (f := fun j : Fin k => if j ≤ i then Real.exp (x j) else 0)
                (fun j hj => hnonneg j) (Finset.mem_univ i))
          exact hle

/-! ## 引理二：因果分母差界
|causalDenom x i − causalDenom y i| ≤ k·e^M·‖x−y‖∞（掩码分母的差
≤ 全分母的差（z_diff_bound 的论证，逐坐标 exp Lipschitz + Linf 界）；
掩码只截去非负项，差界不放大）。 -/

lemma causalDenom_diff_bound {k : ℕ} (M : ℝ) (x y : Fin k → ℝ)
    (hx : ∀ j : Fin k, x j ≤ M) (hy : ∀ j : Fin k, y j ≤ M) (i : Fin k) :
    |causalDenom x i - causalDenom y i| ≤ k * Real.exp M * LinfNorm (x - y) := by
  unfold causalDenom
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin k, ((if j ≤ i then Real.exp (x j) else 0) - (if j ≤ i then Real.exp (y j) else 0))|
        ≤ ∑ j : Fin k, |(if j ≤ i then Real.exp (x j) else 0) - (if j ≤ i then Real.exp (y j) else 0)| :=
          Finset.abs_sum_le_sum_abs (fun j : Fin k => (if j ≤ i then Real.exp (x j) else 0) - (if j ≤ i then Real.exp (y j) else 0)) Finset.univ
    _ ≤ ∑ j : Fin k, |Real.exp (x j) - Real.exp (y j)| := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hji : j ≤ i <;> simp [hji]
    _ ≤ ∑ j : Fin k, Real.exp M * |x j - y j| := by
          apply Finset.sum_le_sum
          intro j hj
          exact exp_lipschitz_on M (x j) (y j) (hx j) (hy j)
    _ ≤ ∑ j : Fin k, Real.exp M * LinfNorm (x - y) := by
          apply Finset.sum_le_sum
          intro j hj
          have hz : |x j - y j| = |(x - y) j| := by rfl
          rw [hz]
          exact mul_le_mul_of_nonneg_left (le_csSup (bddAbove_abs (x - y)) (by exact ⟨j, rfl⟩)) (le_of_lt (Real.exp_pos M))
    _ = k * (Real.exp M * LinfNorm (x - y)) := by simp [Finset.sum_const]
    _ = k * Real.exp M * LinfNorm (x - y) := by ring

/-! ## 定理二：因果 softmax 坐标 Lipschitz
|causalSoftmax x i j − causalSoftmax y i j| ≤ (k+1)·e^{4M}·‖x−y‖∞
（x、y 坐标均在 [−M, M]，M ≥ 0）。与 softmax_lipschitz_coord 同构：
  · j > i（掩码外）：两侧权重都为零，平凡；
  · j ≤ i（可见前缀内）：w = exp(x j)/causalDenom x i，用 abs_div_sub
    分解为「分子差 + 分母差」两项——分母换为掩码分母
    （causalDenom_pos / causalDenom_lower / causalDenom_diff_bound）。-/

theorem causal_softmax_lipschitz_coord {k : ℕ} (M : ℝ) (x y : Fin k → ℝ)
    (hM : 0 ≤ M) (hx : ∀ i : Fin k, -M ≤ x i ∧ x i ≤ M)
    (hy : ∀ i : Fin k, -M ≤ y i ∧ y i ≤ M) (i j : Fin k) :
    |causalSoftmax x i j - causalSoftmax y i j| ≤ (k + 1) * Real.exp (4 * M) * LinfNorm (x - y) := by
  by_cases hji : j ≤ i
  · -- 可见前缀内：w_j = exp(x j)/causalDenom x i（abs_div_sub 分解）
    have hZx : 0 < causalDenom x i := causalDenom_pos x i
    have hZy : 0 < causalDenom y i := causalDenom_pos y i
    have hdec := abs_div_sub (Real.exp (x j)) (Real.exp (y j))
      (causalDenom x i) (causalDenom y i) hZx hZy
    have hZx_low : Real.exp (-M) ≤ causalDenom x i := causalDenom_lower M x (fun j => (hx j).1) i
    have hZy_low : Real.exp (-M) ≤ causalDenom y i := causalDenom_lower M y (fun j => (hy j).1) i
    -- 1/causalDenom z i ≤ e^M（分母下界 e^{−M} ⟹ 倒数上界 e^M）
    have h1gen : ∀ z : Fin k → ℝ, (∀ j : Fin k, -M ≤ z j) → 1 / (causalDenom z i) ≤ Real.exp M := by
      intro z hz
      have hzpos : 0 < causalDenom z i := causalDenom_pos z i
      have hzlow : Real.exp (-M) ≤ causalDenom z i := causalDenom_lower M z hz i
      have hpos : 0 < Real.exp M := Real.exp_pos M
      rw [div_le_iff₀ hzpos]
      have hle : Real.exp M * Real.exp (-M) ≤ Real.exp M * (causalDenom z i) :=
        mul_le_mul_of_nonneg_left hzlow (le_of_lt hpos)
      have hone : Real.exp M * Real.exp (-M) = 1 := by
        rw [← Real.exp_add]
        simp
      rwa [hone] at hle
    have h1x : 1 / (causalDenom x i) ≤ Real.exp M := h1gen x (fun j => (hx j).1)
    calc
      |causalSoftmax x i j - causalSoftmax y i j|
          = |Real.exp (x j) / (causalDenom x i) - Real.exp (y j) / (causalDenom y i)| := by
            unfold causalSoftmax
            simp [hji]
      _ ≤ |Real.exp (x j) - Real.exp (y j)| / (causalDenom x i)
          + |Real.exp (y j)| * |(causalDenom x i) - (causalDenom y i)|
            / ((causalDenom x i) * (causalDenom y i)) := hdec
      _ ≤ (Real.exp M * |x j - y j|) / (causalDenom x i)
          + (Real.exp M) * (k * Real.exp M * LinfNorm (x - y))
            / ((causalDenom x i) * (causalDenom y i)) := by
            have hzdiff : |(causalDenom x i) - (causalDenom y i)|
                ≤ k * Real.exp M * LinfNorm (x - y) :=
              causalDenom_diff_bound M x y (fun j => (hx j).2) (fun j => (hy j).2) i
            have hb1 : |Real.exp (y j)| ≤ Real.exp M := by
              rw [abs_of_nonneg (le_of_lt (Real.exp_pos (y j)))]
              exact Real.exp_le_exp.mpr (hy j).2
            exact add_le_add
              (div_le_div_of_nonneg_right (exp_lipschitz_on M (x j) (y j) (hx j).2 (hy j).2) (le_of_lt hZx))
              (by
                have hprod : 0 < (causalDenom x i) * (causalDenom y i) := mul_pos hZx hZy
                have hmul : |Real.exp (y j)| * |(causalDenom x i) - (causalDenom y i)|
                    ≤ Real.exp M * (k * Real.exp M * LinfNorm (x - y)) := by
                  exact mul_le_mul hb1 hzdiff (abs_nonneg _) (by positivity)
                exact div_le_div_of_nonneg_right hmul (le_of_lt hprod))
      _ ≤ (Real.exp M * LinfNorm (x - y)) / (causalDenom x i)
          + (Real.exp M) * (k * Real.exp M * LinfNorm (x - y))
            / ((causalDenom x i) * (causalDenom y i)) := by
            have hz : |x j - y j| ≤ LinfNorm (x - y) := by
              have hz' : |x j - y j| = |(x - y) j| := by rfl
              rw [hz']
              exact le_csSup (bddAbove_abs (x - y)) (by exact ⟨j, rfl⟩)
            exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz (le_of_lt (Real.exp_pos M))) (le_of_lt hZx)) le_rfl
      _ ≤ (k + 1) * Real.exp (4 * M) * LinfNorm (x - y) := by
            -- 收尾与 softmax_lipschitz_coord 相同：第一项 ≤ e^{2M}·Linf，第二项 ≤ k·e^{4M}·Linf
            have hterm1 : (Real.exp M * LinfNorm (x - y)) / (causalDenom x i)
                ≤ Real.exp M * Real.exp M * LinfNorm (x - y) := by
              calc
                (Real.exp M * LinfNorm (x - y)) / (causalDenom x i)
                    = Real.exp M * LinfNorm (x - y) * (1 / (causalDenom x i)) := by ring
                _ ≤ Real.exp M * LinfNorm (x - y) * Real.exp M := by
                      exact mul_le_mul_of_nonneg_left h1x (mul_nonneg (le_of_lt (Real.exp_pos M)) (linfNorm_nonneg _))
                _ = Real.exp M * Real.exp M * LinfNorm (x - y) := by ring
            have hZxy_low : Real.exp (-2 * M) ≤
                (causalDenom x i) * (causalDenom y i) := by
              have hprod_le : Real.exp (-M) * Real.exp (-M) ≤
                  (causalDenom x i) * (causalDenom y i) :=
                mul_le_mul hZx_low hZy_low (le_of_lt (Real.exp_pos (-M))) (le_of_lt hZx)
              have hone : Real.exp (-M) * Real.exp (-M) = Real.exp (-2 * M) := by
                rw [← Real.exp_add]
                ring
              rwa [hone] at hprod_le
            have h2 : 1 / ((causalDenom x i) * (causalDenom y i)) ≤ Real.exp (2 * M) := by
              have hpos : 0 < Real.exp (2 * M) := Real.exp_pos (2 * M)
              have hdenpos : 0 < (causalDenom x i) * (causalDenom y i) := mul_pos hZx hZy
              rw [div_le_iff₀ hdenpos]
              have hle : Real.exp (2 * M) * Real.exp (-2 * M)
                  ≤ Real.exp (2 * M) * ((causalDenom x i) * (causalDenom y i)) :=
                mul_le_mul_of_nonneg_left hZxy_low (le_of_lt hpos)
              have hone : Real.exp (2 * M) * Real.exp (-2 * M) = 1 := by
                rw [← Real.exp_add]
                simp
              rwa [hone] at hle
            have hterm2 : (Real.exp M) * (k * Real.exp M * LinfNorm (x - y))
                / ((causalDenom x i) * (causalDenom y i))
                ≤ k * Real.exp (4 * M) * LinfNorm (x - y) := by
              calc
                (Real.exp M) * (k * Real.exp M * LinfNorm (x - y))
                    / ((causalDenom x i) * (causalDenom y i))
                    = k * (Real.exp M * Real.exp M * LinfNorm (x - y))
                        * (1 / ((causalDenom x i) * (causalDenom y i))) := by ring
                _ ≤ k * (Real.exp M * Real.exp M * LinfNorm (x - y)) * Real.exp (2 * M) := by
                      exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (Nat.cast_nonneg k)
                        (mul_nonneg (mul_nonneg (le_of_lt (Real.exp_pos M)) (le_of_lt (Real.exp_pos M))) (linfNorm_nonneg _)))
                _ ≤ k * Real.exp (4 * M) * LinfNorm (x - y) := by
                      have hone : Real.exp M * Real.exp M * Real.exp (2 * M) = Real.exp (4 * M) := by
                        rw [← Real.exp_add, ← Real.exp_add]
                        ring
                      have hA : k * (Real.exp M * Real.exp M * LinfNorm (x - y)) * Real.exp (2 * M)
                          = k * Real.exp (4 * M) * LinfNorm (x - y) := by
                        calc
                          k * (Real.exp M * Real.exp M * LinfNorm (x - y)) * Real.exp (2 * M)
                              = k * (Real.exp M * Real.exp M * Real.exp (2 * M)) * LinfNorm (x - y) := by ring
                          _ = k * Real.exp (4 * M) * LinfNorm (x - y) := by rw [hone]
                      exact le_of_eq hA
            have hterm1' : Real.exp M * Real.exp M * LinfNorm (x - y) ≤ Real.exp (4 * M) * LinfNorm (x - y) := by
              have hle : Real.exp M * Real.exp M ≤ Real.exp (4 * M) := by
                have h2M : 2 * M ≤ 4 * M := by nlinarith [hM]
                have hpow : Real.exp M * Real.exp M = Real.exp (2 * M) := by
                  rw [← Real.exp_add]
                  ring
                rw [hpow]
                exact Real.exp_le_exp.mpr h2M
              exact mul_le_mul_of_nonneg_right hle (linfNorm_nonneg _)
            nlinarith [hterm1, hterm1', hterm2]
  · -- 掩码外：j > i，两侧权重都为零（等价于分数 −∞）
    have hzero : |causalSoftmax x i j - causalSoftmax y i j| = 0 := by
      rw [causalSoftmax_eq_zero_of_gt x i j hji, causalSoftmax_eq_zero_of_gt y i j hji]
      simp
    rw [hzero]
    have h1 : 0 ≤ (k : ℝ) + 1 := by positivity
    have h2 : 0 ≤ Real.exp (4 * M) := le_of_lt (Real.exp_pos (4 * M))
    exact mul_nonneg (mul_nonneg h1 h2) (linfNorm_nonneg _)

/-! ## 引理三：因果权重 L1 差界
Σ_j |causalSoftmax sx i j − causalSoftmax sy i j|
≤ k·(k+1)·e^{4M}·LinfNorm(sx − sy)（坐标 Lipschitz 逐坐标求和，
维度因子 k——weight_l1_diff_bound 的因果版）。 -/

lemma causal_weight_l1_diff_bound {k : ℕ} (M : ℝ) (hM : 0 ≤ M) (sx sy : Fin k → ℝ)
    (hsx : ∀ i : Fin k, -M ≤ sx i ∧ sx i ≤ M)
    (hsy : ∀ i : Fin k, -M ≤ sy i ∧ sy i ≤ M) (i : Fin k) :
    (∑ j : Fin k, |causalSoftmax sx i j - causalSoftmax sy i j|)
      ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M) * LinfNorm (sx - sy) := by
  have hper : ∀ j : Fin k, |causalSoftmax sx i j - causalSoftmax sy i j|
      ≤ ((k : ℝ) + 1) * Real.exp (4 * M) * LinfNorm (sx - sy) := by
    intro j
    simpa using (causal_softmax_lipschitz_coord M sx sy hM hsx hsy i j)
  calc
    (∑ j : Fin k, |causalSoftmax sx i j - causalSoftmax sy i j|)
        ≤ ∑ j : Fin k, ((k : ℝ) + 1) * Real.exp (4 * M) * LinfNorm (sx - sy) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hper j
    _ = (k : ℝ) * (((k : ℝ) + 1) * Real.exp (4 * M) * LinfNorm (sx - sy)) := by
          simp [Finset.sum_const]
    _ = (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M) * LinfNorm (sx - sy) := by ring

/-! ## 定理三：完整因果注意力 Lipschitz（数字常数，核心之一）
A(x) = Σ_j causalSoftmax(Sx) q j · (V_j x)（因果权重随输入，查询位置 q），
分数 S 线性、数据域 ‖z‖ ≤ B、value 界 M ⟹
‖A(x) − A(y)‖ ≤ M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)·‖x−y‖。
与双向 attention_lipschitz_numeric（RealBlockConstants）常数**完全相同**
——实例化 attention_lipschitz_weighted，权重 w x j = causalSoftmax (S x) q j
（因果权重也是行随机凸组合：非负 + 和 1；L1-Lipschitz 由
causal_weight_l1_diff_bound ∘ score_lin_lipschitz 给出）。-/

theorem causal_attention_lipschitz_numeric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} [NeZero k] (S : E →L[ℝ] (Fin k → ℝ))
    (V : Fin k → E →L[ℝ] E) (M B : ℝ)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M) (q : Fin k) :
    -- B371 (P0-2): UNSATISFIABLE hB (B357) dropped; the bound is needed only at
    -- the two points the conclusion names.
    ∀ x y : E, ‖x‖ ≤ B → ‖y‖ ≤ B →
      ‖(∑ j : Fin k, causalSoftmax (S x) q j • (V j x)) - (∑ j : Fin k, causalSoftmax (S y) q j • (V j y))‖
        ≤ M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖)) * ‖x - y‖ := by
  intro x y hBx hBy
  have hM0 : 0 ≤ M := by
    rcases (Fin.pos_iff_nonempty.mp (NeZero.pos k)) with ⟨i₀⟩
    linarith [hM i₀, norm_nonneg (V i₀)]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg x) hBx
  -- 分数上界 M' = ‖S‖·B（数据域 + 算子范数 ⟹ |S z ᵢ| ≤ ‖S‖·B）
  let M' : ℝ := ‖S‖ * B
  have hM' : 0 ≤ M' := by
    dsimp [M']
    exact mul_nonneg (norm_nonneg S) hB0
  -- B371: bound as a per-point parameter (template from B369/B370)
  have hscore : ∀ (z : E), ‖z‖ ≤ B → ∀ i : Fin k, |(S z) i| ≤ M' := by
    intro z hz i
    dsimp [M']
    calc
      |(S z) i| ≤ ‖S z‖ := by
            rw [← linfNorm_eq_norm (S z)]
            exact le_csSup (bddAbove_abs (S z)) (by exact ⟨i, rfl⟩)
      _ ≤ ‖S‖ * ‖z‖ := S.le_opNorm z
      _ ≤ ‖S‖ * B := mul_le_mul_of_nonneg_left hz (norm_nonneg S)
  -- 因果权重 L1-Lipschitz：Lw = k·(k+1)·e^{4M'}·‖S‖（因果坐标 Lipschitz ∘ 分数 Lipschitz）
  have hwlip : ∀ (u v : E), ‖u‖ ≤ B → ‖v‖ ≤ B →
      (∑ i : Fin k, |causalSoftmax (S u) q i - causalSoftmax (S v) q i|)
      ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) * ‖u - v‖ := by
    intro u v hu hv
    have h1 := causal_weight_l1_diff_bound (k := k) M' hM' (S u) (S v)
      (fun i => abs_le.mp (hscore u hu i)) (fun i => abs_le.mp (hscore v hv i)) q
    have h2 := score_lin_lipschitz S u v
    calc
      (∑ i : Fin k, |causalSoftmax (S u) q i - causalSoftmax (S v) q i|)
          ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (S u - S v)) := h1
      _ ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) * ‖u - v‖ := by
            have hcoef : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') := by positivity
            calc
              ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (S u - S v))
                  = ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M')) * LinfNorm (S u - S v) := by ring
              _ ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M')) * (‖S‖ * ‖u - v‖) :=
                    mul_le_mul_of_nonneg_left h2 hcoef
              _ = ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) * ‖u - v‖ := by ring
  -- 抽象定理实例化（w = causalSoftmax∘S，行随机 + L1-Lipschitz）
  have hA := attention_lipschitz_weighted (w := fun z i => causalSoftmax (S z) q i) V M
    ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) B
    (by intro x i; exact causalSoftmax_nonneg (S x) q i)
    (by intro x; exact causalSoftmax_sum_one (S x) q)
    hwlip hM x y hBx hBy
  simpa [M'] using hA

/-! ## 因果注意力算子（掩码 softmax 权重随输入，查询位置 q） -/

def CausalSoftmaxAttnOp {n k : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (q : Fin k) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∑ j : Fin k, causalSoftmax (S x) q j • (V j x)

/-! ## 因果块（块组装同双向：RMSNorm ∘ (id + Attn + FFN)） -/

def CausalModelBlock {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (q : Fin k) (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  RMSNormOp (z + CausalSoftmaxAttnOp S V q z + W z)

/-! ## 混合块（前 p 块双向 ModelBlock，后 m−p 块因果 CausalModelBlock）
块 i 的分派：i < p ⟹ 双向（ModelBlock S V (W i)，RealModelChain）；
i ≥ p ⟹ 因果（CausalModelBlock S V (W i) q，本文件）。 -/

def MixedBlock {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : ℕ) (q : Fin k) (i : ℕ) (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  if i < p then ModelBlock S V (W i) z else CausalModelBlock S V (W i) q z

/-! ## 引理四：混合块的分派语义（i < p ⟹ 双向；i ≥ p ⟹ 因果） -/

lemma mixed_block_eq_model_of_lt {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : ℕ) (q : Fin k) (i : ℕ) (h : i < p) (z : EuclideanSpace ℝ (Fin n)) :
    MixedBlock S V W p q i z = ModelBlock S V (W i) z := by
  unfold MixedBlock
  exact if_pos h

lemma mixed_block_eq_causal_of_ge {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : ℕ) (q : Fin k) (i : ℕ) (h : ¬ i < p) (z : EuclideanSpace ℝ (Fin n)) :
    MixedBlock S V W p q i z = CausalModelBlock S V (W i) q z := by
  unfold MixedBlock
  exact if_neg h

/-! ## 定理四：抽象注意力块的统一组装（双向/因果共用）
任意 La-Lipschitz 注意力 A（双向 SoftmaxAttnOp 或因果 CausalSoftmaxAttnOp
均满足）⟹ Block = RMSNorm∘(id + A + W) 是 (√n/c)·(1+La+‖W‖)-Lipschitz。
组装只看组件的 Lipschitz 常数（block_lipschitz_bound：加法/残差/复合
组合律），不看权重来源——两类注意力的结构统一在此。

**⚠ 常数收紧（Z1-5，v14）**：Lf 由松弛版 2√n/c 改为已证紧常数 √n/c
（`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`）。

**⚠ v14（B53 修复）定义域前提为点对**：RMSNorm 只作用在**内层残差和**
`x + A x + W x`、`y + A y + W y` 上，故域前提应设在这两点上：
`(hx : c ≤ ‖x + A x + W x‖) (hy : c ≤ ‖y + A y + W y‖)`
（旧 `hxdom : ∀ z` 与 `hc : 0 < c` 矛盾、使定理空洞）。
**⚠ 注意不是** `c ≤ ‖x‖`——那是**错误的**点对化（内层和不等于 `x`）。
**可满足性见证**：取 `A := 0`、`W := 0`、`x = y = c • e₀`
（则 `x + A x + W x = c • e₀`，`‖·‖ = c`）；即**恒等注意力 + 零 FFN**
的退化块，此时 `hx`/`hy` 均成立。 -/

theorem mixed_block_lipschitz {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (La c B : ℝ) (hc : 0 < c)
    (hA : ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ B → ‖y‖ ≤ B → ‖A x - A y‖ ≤ La * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin n))
    (hBx : ‖x‖ ≤ B) (hBy : ‖y‖ ≤ B)
    (hx : c ≤ ‖x + A x + W x‖) (hy : c ≤ ‖y + A y + W y‖) :
    ‖RMSNormOp (x + A x + W x) - RMSNormOp (y + A y + W y)‖
      ≤ (Real.sqrt n / c) * (1 + La + ‖W‖) * ‖x - y‖ := by
  -- `block_lipschitz_bound` 需要**全局**的 F-Lipschitz 性；而点对前提只覆盖
  -- 内层和这两点。故此处不用通用组装引理，直接对这两点用
  -- rmsNormE_sqrt_lipschitz + 内层和的 Lipschitz 展开。
  have hF : ‖RMSNormOp (x + A x + W x) - RMSNormOp (y + A y + W y)‖
      ≤ (Real.sqrt n / c) * ‖(x + A x + W x) - (y + A y + W y)‖ := by
    rw [RMSNormOp_eq_rmsNormE (x + A x + W x), RMSNormOp_eq_rmsNormE (y + A y + W y)]
    exact rmsNormE_sqrt_lipschitz _ _ c hc hx hy
  have hG : ∀ x y : EuclideanSpace ℝ (Fin n), ‖W x - W y‖ ≤ ‖W‖ * ‖x - y‖ := by
    intro x y
    exact linear_map_lipschitz W x y
  have hLf : 0 ≤ Real.sqrt n / c := by positivity
  -- 内层和 (1+La+‖W‖)-Lipschitz（加法/残差组合律，逐点）
  have hin : ‖(x + A x + W x) - (y + A y + W y)‖ ≤ (1 + La + ‖W‖) * ‖x - y‖ := by
    -- B371: `lipschitz_add` demands UNCONDITIONAL Lipschitz hypotheses, which is
    -- what forced a global data bound.  Only this pair is needed, so the triangle
    -- inequality is applied directly (same move as B366).
    have h1 : ‖(x + A x) - (y + A y)‖ ≤ (1 + La) * ‖x - y‖ := by
      calc
        ‖(x + A x) - (y + A y)‖ = ‖(x - y) + (A x - A y)‖ := by abel
        _ ≤ ‖x - y‖ + ‖A x - A y‖ := norm_add_le _ _
        _ ≤ ‖x - y‖ + La * ‖x - y‖ := add_le_add_left (hA x y hBx hBy) _
        _ = (1 + La) * ‖x - y‖ := by ring
    calc
      ‖(x + A x + W x) - (y + A y + W y)‖
          = ‖((x + A x) - (y + A y)) + (W x - W y)‖ := by abel
      _ ≤ ‖(x + A x) - (y + A y)‖ + ‖W x - W y‖ := norm_add_le _ _
      _ ≤ (1 + La) * ‖x - y‖ + ‖W‖ * ‖x - y‖ :=
            add_le_add h1 (linear_map_lipschitz W x y)
      _ = (1 + La + ‖W‖) * ‖x - y‖ := by ring
  calc
    ‖RMSNormOp (x + A x + W x) - RMSNormOp (y + A y + W y)‖
        ≤ (Real.sqrt n / c) * ‖(x + A x + W x) - (y + A y + W y)‖ := hF
    _ ≤ (Real.sqrt n / c) * ((1 + La + ‖W‖) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left hin hLf
    _ = (Real.sqrt n / c) * (1 + La + ‖W‖) * ‖x - y‖ := by ring

/-! ## 定理五：因果块的数字 Lipschitz（单块）
CausalModelBlock = RMSNorm∘(id + CausalSoftmaxAttnOp + W) 是
(√n/c)·(1 + attnNumericConstant S M B + ‖W‖)-Lipschitz
（因果注意力常数 = 双向常数，定理三；块组装 = 定理四）。

**⚠ v14（B53 修复）**：域前提设在**内层残差和**上（RMSNorm 的实际输入），
**可满足**（见证：恒等注意力 + 零 FFN + `x = y = c • e₀`）。 -/

theorem causal_model_block_lipschitz_numeric {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (q : Fin k) (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (x y : EuclideanSpace ℝ (Fin n))
    (hBx : ‖x‖ ≤ B) (hBy : ‖y‖ ≤ B)
    (hx : c ≤ ‖x + CausalSoftmaxAttnOp S V q x + W x‖)
    (hy : c ≤ ‖y + CausalSoftmaxAttnOp S V q y + W y‖) :
    ‖CausalModelBlock S V W q x - CausalModelBlock S V W q y‖
      ≤ (Real.sqrt n / c)
          * (1 + (M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖))) + ‖W‖)
          * ‖x - y‖ := by
  let La : ℝ := M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖))
  have hA : ∀ u v : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ B → ‖v‖ ≤ B →
      ‖CausalSoftmaxAttnOp S V q u - CausalSoftmaxAttnOp S V q v‖ ≤ La * ‖u - v‖ := by
    intro u v hu hv
    have h := causal_attention_lipschitz_numeric (E := EuclideanSpace ℝ (Fin n)) S V M B hM q u v hu hv
    simpa [CausalSoftmaxAttnOp, La] using h
  simpa [CausalModelBlock, La] using
    (mixed_block_lipschitz (CausalSoftmaxAttnOp S V q) W La c B hc hA x y hBx hBy hx hy)

/-! ## 引理五：因果块逐块 hetero 常数（链骨架代入用）
CausalModelBlock S V (W i) 的常数 = heteroBlockLb S W M B c i
（= (√n/c)·(1 + attnNumericConstant S M B + ‖W i‖)，定理五读出）。

**⚠ v14（B53 修复）**：域前提设在**内层残差和**上，**可满足**。 -/

lemma causal_block_lipschitz_numeric {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (q : Fin k) (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    -- B371 (P0-2): UNSATISFIABLE hB (B357) dropped; single-step theorem.
    (i : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    (hBx : ‖x‖ ≤ B) (hBy : ‖y‖ ≤ B)
    (hx : c ≤ ‖x + CausalSoftmaxAttnOp S V q x + W i x‖)
    (hy : c ≤ ‖y + CausalSoftmaxAttnOp S V q y + W i y‖) :
    ‖CausalModelBlock S V (W i) q x - CausalModelBlock S V (W i) q y‖
      ≤ heteroBlockLb S W M B c i * ‖x - y‖ := by
  have hb := causal_model_block_lipschitz_numeric S V (W i) q M B c hc hM x y hBx hBy hx hy
  simpa [heteroBlockLb, attnNumericConstant] using hb

/-! ## 定理六：混合块逐块数字 Lipschitz
块 i 是 Lb_i = heteroBlockLb S W M B c i-Lipschitz：
  · i < p（双向）：ModelBlock（hetero_block_lipschitz_numeric，既有）；
  · i ≥ p（因果）：CausalModelBlock（引理五，本文件）。
两类块的常数统一（注意力常数相同），差异只来自逐块 FFN 权重 ‖W_i‖。

**⚠ v14（B53 修复）**：域前提设在 `MixedBlock` 的**内层残差和**上（RMSNorm 的实际
输入）。⚠ 但两类分支的内层和**形式不同**（双向用 `SoftmaxAttnOp`、因果用
`CausalSoftmaxAttnOp`），而 `i` 与 `p` 的关系决定走哪支 ⟹ 这里**分别接收两支的
域前提**（`hx`/`hy` 为双向形式，`hx'`/`hy'` 为因果形式），由 `by_cases` 选用。
二者都是**点对、可满足**的（见证：恒等注意力 + 零 FFN + `x = y = c • e₀`）。 -/

theorem mixed_block_lipschitz_numeric {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : ℕ) (q : Fin k) (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (i : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    (hBx : ‖x‖ ≤ B) (hBy : ‖y‖ ≤ B)
    (hx : c ≤ ‖x + SoftmaxAttnOp S V x + W i x‖)
    (hy : c ≤ ‖y + SoftmaxAttnOp S V y + W i y‖)
    (hx' : c ≤ ‖x + CausalSoftmaxAttnOp S V q x + W i x‖)
    (hy' : c ≤ ‖y + CausalSoftmaxAttnOp S V q y + W i y‖) :
    ‖MixedBlock S V W p q i x - MixedBlock S V W p q i y‖
      ≤ heteroBlockLb S W M B c i * ‖x - y‖ := by
  by_cases h : i < p
  · have hb := hetero_block_lipschitz_numeric S V W M B c hc hM i x y hBx hBy hx hy
    simpa [MixedBlock, h] using hb
  · have hb := causal_block_lipschitz_numeric S V W q M B c hc hM i x y hBx hBy hx' hy'
    simpa [MixedBlock, h] using hb

/-! ## 定理七：m 块混合链的端到端数字界（核心）
m 块混合链（前 p 块双向 + 后 m−p 块因果，每块 Lb_i-Lipschitz）串成链，
端到端误差 ≤ (∏ᵢ Lb_i)·‖x−y‖——实例化**点对版**链骨架
`RealModelChain.chainN_dom_bound`（把全局 Lipschitz 前提弱化为沿链逐点；
块函数为 MixedBlock，常数同为 heteroBlockLb）。

**⚠ v14（B53 修复）链式可达性作为显式前提**：每层的域条件只能由链上实际
中间激活给出。故显式传入 `hreach`（**有意作为前提**，B53 允许的降级；
**可满足**：恒等链 + `x = c • e₀`）。本文件不证真实混合链满足它。 -/

theorem mixed_chain_numeric_bound {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : ℕ) (q : Fin k) (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    -- B371 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).
    -- CHAIN theorem: the bound is needed at every visited point.
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j (x)‖ ≤ B
      ∧ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j (y)‖ ≤ B)
    (hreach : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x)
              + W j (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x)‖
      ∧ c ≤ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y)
              + W j (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y)‖)
    (hreach' : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x
              + CausalSoftmaxAttnOp S V q (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x)
              + W j (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x)‖
      ∧ c ≤ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y
              + CausalSoftmaxAttnOp S V q (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y)
              + W j (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y)‖) :
    ‖ChainFwd (MixedBlock S V W p q) m x - ChainFwd (MixedBlock S V W p q) m y‖
      ≤ (∏ i in Finset.range m, heteroBlockLb S W M B c i) * ‖x - y‖ := by
  exact chainN_dom_bound (MixedBlock S V W p q)
    (fun i : ℕ => heteroBlockLb S W M B c i) m x y
    (fun i hi =>
      mixed_block_lipschitz_numeric S V W p q M B c hc hM i
        (ChainFwd (MixedBlock S V W p q) i x) (ChainFwd (MixedBlock S V W p q) i y)
        (hBc i (Nat.le_of_lt hi)).1 (hBc i (Nat.le_of_lt hi)).2
        (hreach i (Nat.le_of_lt hi)).1 (hreach i (Nat.le_of_lt hi)).2
        (hreach' i (Nat.le_of_lt hi)).1 (hreach' i (Nat.le_of_lt hi)).2)
    (fun i _ => hetero_block_lb_nonneg S V W M B c hc hM
      (le_trans (norm_nonneg _) (hBc 0 (Nat.zero_le m)).1) i)

/-! ## 定理八：混合链端到端界的 p 拆分版
∏ 按 p 拆分为「前 p 块（双向）常数连乘 × 后 m−p 块（因果）常数连乘」：
端到端 ≤ (∏_{i<p} Lb_i)·(∏_{0≤j<m−p} Lb_{p+j})·‖x−y‖
（Finset.prod_range_add；p ≤ m）。

**⚠ v14（B53 修复）**：与定理七同，`hreach` 为**有意传入的可满足前提**。 -/

theorem mixed_chain_numeric_bound_split {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : ℕ) (q : Fin k) (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    -- B371 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).
    -- CHAIN theorem: the bound is needed at every visited point.
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j (x)‖ ≤ B
      ∧ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j (y)‖ ≤ B)
    (hreach : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x)
              + W j (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x)‖
      ∧ c ≤ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y)
              + W j (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y)‖)
    (hreach' : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x
              + CausalSoftmaxAttnOp S V q (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x)
              + W j (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j x)‖
      ∧ c ≤ ‖ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y
              + CausalSoftmaxAttnOp S V q (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y)
              + W j (ChainFwd (fun i : ℕ => MixedBlock S V W p q i) j y)‖)
    (hpm : p ≤ m) :
    ‖ChainFwd (MixedBlock S V W p q) m x - ChainFwd (MixedBlock S V W p q) m y‖
      ≤ (∏ i in Finset.range p, heteroBlockLb S W M B c i) *
        (∏ i in Finset.range (m - p), heteroBlockLb S W M B c (p + i)) * ‖x - y‖ := by
  have hb := mixed_chain_numeric_bound S V W p q M B c hc hM m x y hBc hreach hreach'
  have hsplit : (∏ i in Finset.range m, heteroBlockLb S W M B c i)
      = (∏ i in Finset.range p, heteroBlockLb S W M B c i) *
        (∏ i in Finset.range (m - p), heteroBlockLb S W M B c (p + i)) := by
    calc
      (∏ i in Finset.range m, heteroBlockLb S W M B c i)
          = ∏ i in Finset.range (p + (m - p)), heteroBlockLb S W M B c i := by
            rw [Nat.add_sub_of_le hpm]
      _ = (∏ i in Finset.range p, heteroBlockLb S W M B c i) *
          (∏ i in Finset.range (m - p), heteroBlockLb S W M B c (p + i)) := by
            exact Finset.prod_range_add (heteroBlockLb S W M B c) p (m - p)
  rw [hsplit] at hb
  exact hb

/-! ## 定理九：退化特例 p = 0（全因果链）
p = 0 时 MixedBlock 的 if 恒取因果分支（¬ i < 0），混合链退化为
全因果块链（CausalModelBlock S V (W i) q）——端到端界不变
（∏ᵢ Lb_i 常数体系相同）。

**⚠ v14（B53 修复）**：`hreach` 为**有意传入的可满足前提**
（可直接由本文件的 `hdef` 把 MixedBlock 版化为因果版，故下述 `hreach` 用
因果内层和书写）。 -/

theorem mixed_to_causal {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (q : Fin k) (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    -- B371 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).
    -- CHAIN theorem: the bound is needed at every visited point.
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) j (x)‖ ≤ B
      ∧ ‖ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) j (y)‖ ≤ B)
    (hreach : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) j x
              + CausalSoftmaxAttnOp S V q (ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) j x)
              + W j (ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) j x)‖
      ∧ c ≤ ‖ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) j y
              + CausalSoftmaxAttnOp S V q (ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) j y)
              + W j (ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) j y)‖) :
    ‖ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) m x
      - ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) m y‖
      ≤ (∏ i in Finset.range m, heteroBlockLb S W M B c i) * ‖x - y‖ := by
  have hdef : MixedBlock S V W 0 q = fun i : ℕ => CausalModelBlock S V (W i) q := by
    funext i z
    unfold MixedBlock
    simp [Nat.not_lt_zero]
  -- p = 0 时 MixedBlock 恒取**因果**分支 ⟹ 链上每块都用引理五（因果形式）。
  -- ⇒ 直接用点对版链骨架 + 因果逐块定理，**不需要**定理七那条（p 通用、
  -- 要求双向形式的 `hreach`）——那在 p = 0 下根本用不上。
  have hb := chainN_dom_bound (fun i : ℕ => CausalModelBlock S V (W i) q)
    (fun i : ℕ => heteroBlockLb S W M B c i) m x y
    (fun i hi =>
      causal_block_lipschitz_numeric S V W q M B c hc hM i
        (ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) i x)
        (ChainFwd (fun i : ℕ => CausalModelBlock S V (W i) q) i y)
        (hBc i (Nat.le_of_lt hi)).1 (hBc i (Nat.le_of_lt hi)).2
        (hreach i (Nat.le_of_lt hi)).1 (hreach i (Nat.le_of_lt hi)).2)
    (fun i _ => hetero_block_lb_nonneg S V W M B c hc hM
      (le_trans (norm_nonneg _) (hBc 0 (Nat.zero_le m)).1) i)
  exact hb

/-! ## 定理十：退化特例 p = m（全双向链 = 异质链）
全双向链（每块 ModelBlock S V (W i)，RealModelChain）恰是
RealModelChainHetero.hetero_chain_numeric_bound 的异质链本身
（混合链的 encoder 端：p = m 时块 0..m−1 全为 i < p 的 ModelBlock，
mixed_block_eq_model_of_lt）。端到端界 = (∏ᵢ Lb_i)·‖x−y‖
（q 与全双向链无关，故不出现于陈述）。

**⚠ v14（B53 修复）**：`hreach` 为**有意传入的可满足前提**，形式与
`hetero_chain_numeric_bound` 完全一致（同一块函数）。 -/

theorem mixed_to_encoder {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    -- B371 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).
    -- CHAIN theorem: the bound is needed at every visited point.
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j x‖ ≤ B
      ∧ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j y‖ ≤ B)
    (hreach : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j x
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j x)
              + W j (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j x)‖
      ∧ c ≤ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j y
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j y)
              + W j (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j y)‖) :
    ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) m x
      - ChainFwd (fun i : ℕ => ModelBlock S V (W i)) m y‖
      ≤ (∏ i in Finset.range m, heteroBlockLb S W M B c i) * ‖x - y‖ := by
  exact hetero_chain_numeric_bound S V W M B c hc hM m x y hBc hreach

/-! ## 注：混合架构收官闭环
  因果权重行随机（causalSoftmax_nonneg/sum_one，RealCausalAttention）
  ⟹ 固定权重凸组合 Lipschitz（定理一）⟹ 因果 softmax 坐标 Lipschitz
  （定理二，与 softmax_lipschitz_coord 同构）⟹ 完整因果注意力数字常数
  （定理三，= 双向 attention_lipschitz_numeric 的常数）⟹ 统一块组装
  （定理四，双向/因果共用 block_lipschitz_bound）⟹ 因果块常数
  （定理五/引理五，= heteroBlockLb）⟹ 混合块逐块 Lipschitz（定理六）
  ⟹ 端到端 (∏ᵢ Lb_i)·‖x−y‖（定理七 = chainN_error_bound 实例化，
  常数与 RealModelChainHetero.hetero_chain_numeric_bound 相同体系）
  ⟹ p 拆分（定理八）⟹ 退化特例 p=0 全因果 / p=m 全双向（定理九/十）。
  全部常数显式：维度因子 n/k、exp 上界 e^{4‖S‖B}、算子范数 ‖S‖/‖W_i‖、
  value 界 M、数据域 B、规范化 √n/c。唯一场景假设：数据范数上下界
  （B 有界域、c 非退化）——与 RealBlockConstants / RealModelChainHetero
  完全相同，链骨架未引入任何新假设。因果/双向的统一性来自行随机凸组合
  结构（两类权重都非负 + 和 1），数字常数因此相同。
  VERIFICATION.md §5「结构」行「混合架构（含因果/双向混合）」收官。-/

end Lattice
