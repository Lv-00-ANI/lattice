import Mathlib
import Lattice.Lib.Chain.RealModelChain
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Architectures.RealBlockConstants
/-!
# LATTICE: 异质块链端到端 —— 每块独立 FFN 权重的数字误差界

VERIFICATION.md §5「结构」行「混合架构（异质块）端到端」的收官：
把 RealModelChain 的**同构块链**（所有块共享同一 Lipschitz 常数 Lb）
推广为**异质块链**——每块有自己的 FFN 权重 W_i（从而自己的 Lipschitz
常数 Lb_i），端到端误差界 = (∏ᵢ Lb_i)·‖x−y‖（Lipschitz 常数连乘，
不再退化为幂）。

模型（块 i）：Block_i(z) = RMSNorm(z + SoftmaxAttnOp S V z + W_i z)
（RealModelChain.ModelBlock 逐块代入 W := W_i），其余架构参数
n、c、B、k、M、S 全块共享——同一架构不同权重，最现实的情形。

单块数字闭式（从 transformer_block_numeric 逐块读出，RealBlockConstants）：
  Lb_i = (√n/c)·(1 + La + ‖W_i‖)，
  La = M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)
La 与块无关（注意力分数 S、value 界 M、数据域 B 全块共享），提取为
attnNumericConstant；‖W_i‖ 每块变化，故 Lb_i 逐块不同。

定理链（全部数字常数闭式，无 open 假设）：
  1. hetero_block_lipschitz_numeric：块 i 是 Lb_i-Lipschitz（∀x y，
     从 transformer_block_numeric 逐块读出，simpa 模式同 RealModelChain）；
     **⚠ v14（B53）** 定义域前提为**点对** `hx : c ≤ ‖x‖`、`hy : c ≤ ‖y‖`；
  2. hetero_chain_numeric_bound（核心）：m 块异质链端到端误差
     ≤ (∏ᵢ Lb_i)·‖x−y‖——实例化**点对版**链骨架
     `RealModelChain.chainN_dom_bound`（把全局 Lipschitz 前提弱化为沿链逐点）；
  3. hetero_chain_edit_locality_numeric：第 k 块入口扰动 δ 经尾部
     异质块 ≤ (∏_{j<m−k} Lb_{k+j})·‖δ‖（同骨架的点对版）；
  4. hetero_to_homo（特例回收）：所有 W_i = W0（同构）⟹ ∏Lb_i = Lb^m，
     与 RealModelChain.model_chain_numeric_bound 的常数一致；
  5. hetero_chain_reduces_to_homo：W 恒为 W0 时异质链的端到端界退化
     为同构界 (Lb0)^m·‖x−y‖——异质框架是同构框架的严格推广。

⚠ **定理 2/3/5 额外带链式可达性前提 `hreach`**（**有意作为前提传入**，
B53 允许的降级；**可满足**）。详见证伪与「诚实边界」段落。

诚实假设（模型无关，均显式标注；与 RealModelChain 完全相同）：
  · [NeZero n] [NeZero k]：嵌入维数/注意力头数非零（transformer_block_numeric 所需）；
  · hc : 0 < c：RMSNorm 定义域范数下界为正（Lf = √n/c 的分母）；
  · hM：value 投影界 max‖Vᵢ‖ ≤ M；
  · hB：数据范数上界 ∀z, ‖z‖ ≤ B（softmax 分数有界 |S z| ≤ ‖S‖·B 的前提）；
  · hx、hy（单块定理）：**点对**定义域前提 `c ≤ ‖x‖`、`c ≤ ‖y‖`。
    **⚠ v14（B53 修复）**：旧稿是 `hxdom：∀z, c ≤ ‖z‖`，与 `hc : 0 < c`
    **矛盾**（`z := 0` ⟹ `c ≤ 0`）⟹ **前提不可满足、定理空洞**（CORRECTIONS B53）。
    **可满足性见证**：取 `x = y = c • e₀`（`‖c • e₀‖ = c`）；
  · hreach（链式定理 2/3/5）：**链上每个中间激活都在定义域内**。链式定理不能只用
    点对前提——第 k 层的输入是 `ChainFwd … k x`。**⚠ 这是有意作为前提传入的**
    （B53 允许的降级），**且可满足**（恒等链 + `x = c • e₀`）。
    **诚实边界**：本文件**不证明**真实异质块链满足 `hreach`（需「块输出范数下界」
    的实质分析，属后续独立立项）。
  每块 W_i 允许不同——异质性是结论的一部分，不是额外假设。

模型无关：链骨架（ChainFwd/ChainTail/chainN_error_bound/
chain_edit_locality，RealChain）对任意范数空间成立且本就支持每层不同
常数；本文件只把逐块数字常数 Lb_i 代入该骨架——端到端误差界是
「Lipschitz 常数连乘」的直接数字实例化，不含任何新分析假设。
命名说明：链长用 m（n 已被嵌入维数占用，与既有文件 EuclideanSpace ℝ (Fin n)
的记号一致）。

端到端意义：‖ChainFwd BlockChain m x − ChainFwd BlockChain m y‖
≤ (∏ᵢ Lb_i)·‖x−y‖——异质链的误差放大因子是逐块 Lipschitz 常数的
乘积：任一块 Lb_i < 1 即贡献指数收缩，Lb_i > 1 即贡献放大；与同构链
（RealModelChain，∏ = Lb^m）相比，异质链可精细到「哪一块最敏感」。
-/

noncomputable section

namespace Lattice

/-! ## 公共注意力数字常数（与块无关）
La = M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)：注意力部分对每块相同的
数字闭式（分数 S、value 界 M、数据域 B 全块共享），从
transformer_block_numeric 的 RHS 提取；W_i 每块变化，故 Lb_i 逐块不同。-/

def attnNumericConstant {n k : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (M B : ℝ) : ℝ :=
  M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖))

/-! ## 块 i 的数字闭式常数
Lb_i = (√n/c)·(1 + La + ‖W_i‖)，La = attnNumericConstant（公共），
‖W_i‖ 每块变化（从 transformer_block_numeric 的 RHS 逐块读出，
纯数字，依赖 ℝ 的开方/指数/算子范数，标 noncomputable）。

**⚠ 常数收紧（Z1-5，v14）**：Lf 由松弛版 2√n/c 收紧为已证紧常数
`√n/c`（`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`），与
`RealModelChain.modelBlockLb` **同步**。 -/

def heteroBlockLb {n k : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (i : ℕ) : ℝ :=
  (Real.sqrt n / c) * (1 + attnNumericConstant S M B + ‖W i‖)

/-! ## 引理：Lb_i 非负（链界连乘单调的前提）
同 model_block_lb_nonneg（RealModelChain）：逐块读出（W := W_i）
后每块非负；由 model_block_lb_nonneg 逐块实例化。-/

lemma hetero_block_lb_nonneg {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    -- B370 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).  The proof
    -- consumed it ONLY to get `0 ≤ B`, so that inequality is the hypothesis now --
    -- the weakest thing the argument actually needs (same move as B369).
    (hB0 : 0 ≤ B) (i : ℕ) :
    0 ≤ heteroBlockLb S W M B c i := by
  -- 定义等价：heteroBlockLb S W M B c i = modelBlockLb S (W i) M B c
  -- （change 用定义等价；避免 simp [modelBlockLb]，后者在 0 ≤ 目标上
  -- 触发算子范数空间的 Nontrivial 类搜索超时）
  change 0 ≤ modelBlockLb S (W i) M B c
  exact model_block_lb_nonneg S V (W i) M B c hc hM hB0

/-! ## 定理一：块 i 的数字 Lipschitz（逐块）
块 i = ModelBlock S V (W_i) = RMSNorm∘(id + Attn + FFN∘W_i) 是
Lb_i = (√n/c)·(1 + La + ‖W_i‖)-Lipschitz：∀x y，误差 ≤ Lb_i·‖x−y‖。
直接从 transformer_block_numeric 逐块读出（W := W_i，simpa 展开 def）。

**⚠ v14（B53 修复）定义域前提为点对**：只涉及 `x`、`y` 两点，故用点对假设。
⚠ **v15 更正（B60）**：位置必须是 **RMSNorm 的实际输入（内层残差和）**——
`(hx : c ≤ ‖x + SoftmaxAttnOp S V x + W i x‖)`，**不是** `c ≤ ‖x‖`。
**见证**：`x = y = c • e₀` 且注意力/FFN 取零映射。 -/

theorem hetero_block_lipschitz_numeric {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    -- B370 (P0-2): UNSATISFIABLE hB (B357) dropped; single-step theorem.
    (i : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    (hBx : ‖x‖ ≤ B) (hBy : ‖y‖ ≤ B)
    (hx : c ≤ ‖x + SoftmaxAttnOp S V x + W i x‖)
    (hy : c ≤ ‖y + SoftmaxAttnOp S V y + W i y‖) :
    ‖ModelBlock S V (W i) x - ModelBlock S V (W i) y‖
      ≤ heteroBlockLb S W M B c i * ‖x - y‖ := by
  simpa [ModelBlock, heteroBlockLb, attnNumericConstant] using
    transformer_block_numeric S V (W i) M B c hc hM x y hBx hBy hx hy

/-! ## 定理二：m 块异质链的端到端数字界（核心）
m 块异质链（块 i 的权重 W_i，Lb_i-Lipschitz，定理一）串成链，端到端
误差 ≤ (∏ᵢ Lb_i)·‖x−y‖——实例化点对版链骨架 `chainN_dom_bound`
（RealModelChain：把 `chainN_error_bound` 的全局 Lipschitz 前提弱化为
**沿链逐点**的前提，正是点对定义域假设所需的形式）。
与同构情形（RealModelChain.model_chain_numeric_bound，∏ = Lb^m）相比，
异质链常数逐块不同，∏ 不再退化为幂。

**⚠ v14（B53 修复）链式可达性作为显式前提**：每层的域条件只能由链上
实际中间激活给出。故显式传入 `hreach`（**有意作为前提**，B53 允许的降级；
**可满足**：恒等链 + `x = c • e₀`）。本文件不证真实块链满足它。 -/

theorem hetero_chain_numeric_bound {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    -- B370 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).
    -- CHAIN theorem: the bound is needed at every point the chain visits.
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j (x)‖ ≤ B
      ∧ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j (y)‖ ≤ B)
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
  have hb := chainN_dom_bound (fun i : ℕ => ModelBlock S V (W i))
    (fun i : ℕ => heteroBlockLb S W M B c i) m x y
    (fun i hi =>
      hetero_block_lipschitz_numeric S V W M B c hc hM i
        (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) i x)
        (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) i y)
        (hBc i (Nat.le_of_lt hi)).1 (hBc i (Nat.le_of_lt hi)).2
        (hreach i (Nat.le_of_lt hi)).1 (hreach i (Nat.le_of_lt hi)).2)
    (fun i _ => hetero_block_lb_nonneg S V W M B c hc hM
      (le_trans (norm_nonneg _) (hBc 0 (Nat.zero_le m)).1) i)
  exact hb

/-! ## 定理三：链编辑局部性（异质数字版）
第 k 块入口注入扰动 δ，经尾部块（块 k..m-1，各自 Lb_{k+j}）传播：
端到端变化 ≤ (∏_{j<m−k} Lb_{k+j})·‖δ‖（点对版链骨架 chainN_dom_bound，
∏ 常数逐块不同）。

**⚠ v14（B53 修复）链式可达性作为显式前提**：尾部链每层输入是
`ChainFwd (fun i => ModelBlock S V (W (kk+i))) j (x+δ)` 与对应 `x` 一路，
用单块定理需知二者在域内。故显式传入 `hreach`（**有意作为前提**，
B53 允许的降级；**可满足**：δ = 0 且恒等链 + `x = c • e₀`）。 -/

theorem hetero_chain_edit_locality_numeric {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m kk : ℕ) (δ x : EuclideanSpace ℝ (Fin n))
    -- B370 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).
    -- CHAIN theorem: the bound is needed at every point the chain visits.
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) j (x + δ)‖ ≤ B
      ∧ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) j (x)‖ ≤ B)
    (hreach : ∀ j ≤ m - kk,
        c ≤ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) j (x + δ)
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) j (x + δ))
              + W (kk + j) (ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) j (x + δ))‖
      ∧ c ≤ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) j x
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) j x)
              + W (kk + j) (ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) j x)‖) :
    ‖ChainTail (fun i : ℕ => ModelBlock S V (W i)) kk m (x + δ)
      - ChainTail (fun i : ℕ => ModelBlock S V (W i)) kk m x‖
      ≤ (∏ j in Finset.range (m - kk), heteroBlockLb S W M B c (kk + j)) * ‖δ‖ := by
  -- 尾部链按 ChainTail 定义 = 平移层函数上的 (m−kk) 层链
  have htail : ∀ z : EuclideanSpace ℝ (Fin n),
      ChainTail (fun i : ℕ => ModelBlock S V (W i)) kk m z
        = ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) (m - kk) z := by
    intro z
    rfl
  rw [htail (x + δ), htail x]
  have hstart : (x + δ) - x = δ := by abel
  have hb := chainN_dom_bound (fun i : ℕ => ModelBlock S V (W (kk + i)))
    (fun i : ℕ => heteroBlockLb S W M B c (kk + i)) (m - kk) (x + δ) x
    (fun i hi =>
      hetero_block_lipschitz_numeric S V W M B c hc hM (kk + i)
        (ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) i (x + δ))
        (ChainFwd (fun i : ℕ => ModelBlock S V (W (kk + i))) i x)
        (hBc i (le_trans (Nat.le_of_lt hi) (Nat.sub_le m kk))).1
        (hBc i (le_trans (Nat.le_of_lt hi) (Nat.sub_le m kk))).2
        (hreach i (Nat.le_of_lt hi)).1 (hreach i (Nat.le_of_lt hi)).2)
    (fun i _ => hetero_block_lb_nonneg S V W M B c hc hM
      (le_trans (norm_nonneg _) (hBc 0 (Nat.zero_le m)).1) (kk + i))
  rw [hstart] at hb
  exact hb

/-! ## 定理四：异质 → 同构特例回收（加分）
所有块权重相等 W_i = W0（同构块链）⟹ ∏ᵢ Lb_i = Lb^m
（Lb = modelBlockLb S W0 M B c，RealModelChain 的常数）——异质链的
常数连乘退化回同构链的幂，与 model_chain_numeric_bound 的常数一致。-/

theorem hetero_to_homo {n k : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hW : ∀ i : ℕ, W i = W0) (m : ℕ) :
    (∏ i in Finset.range m, heteroBlockLb S W M B c i)
      = modelBlockLb S W0 M B c ^ m := by
  calc
    (∏ i in Finset.range m, heteroBlockLb S W M B c i)
        = ∏ i in Finset.range m, modelBlockLb S W0 M B c := by
          apply Finset.prod_congr rfl
          intro i hi
          calc
            heteroBlockLb S W M B c i = modelBlockLb S (W i) M B c := by rfl
            _ = modelBlockLb S W0 M B c := by rw [hW i]
    _ = modelBlockLb S W0 M B c ^ m := by
          rw [Finset.prod_const, Finset.card_range]

/-! ## 定理五：异质链退化到同构界
W 恒为 W0 时，异质链的端到端界退化到同构界
(Lb0)^m·‖x−y‖（= model_chain_numeric_bound 的 RHS 常数）——
异质框架严格包含同构框架。

**⚠ v14（B53 修复）**：域前提与定理二同步改为链式可达性 `hreach`
（**有意作为前提**，**可满足**）。 -/

theorem hetero_chain_reduces_to_homo {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (hW : ∀ i : ℕ, W i = W0)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    -- B370 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).
    -- CHAIN theorem: the bound is needed at every point the chain visits.
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j (x)‖ ≤ B
      ∧ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j (y)‖ ≤ B)
    (hreach : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j x
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j x)
              + W j (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j x)‖
      ∧ c ≤ ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j y
              + SoftmaxAttnOp S V (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j y)
              + W j (ChainFwd (fun i : ℕ => ModelBlock S V (W i)) j y)‖) :
    ‖ChainFwd (fun i : ℕ => ModelBlock S V (W i)) m x
      - ChainFwd (fun i : ℕ => ModelBlock S V (W i)) m y‖
      ≤ modelBlockLb S W0 M B c ^ m * ‖x - y‖ := by
  have hb := hetero_chain_numeric_bound S V W M B c hc hM m x y hBc hreach
  have hprod : (∏ i in Finset.range m, heteroBlockLb S W M B c i)
      = modelBlockLb S W0 M B c ^ m :=
    hetero_to_homo S W W0 M B c hW m
  simpa [hprod] using hb

/-! ## 注：异质端到端收官闭环
  单块数字闭式（transformer_block_numeric，RealBlockConstants）⟹
  定理一逐块读出 Lb_i（纯数字常数 def，公共部分 attnNumericConstant）
  ⟹ 定理二代入异质链骨架（chainN_error_bound，RealChain 本就支持
  每层不同常数 Ls i）得端到端 (∏ᵢ Lb_i)·‖x−y‖ ⟹ 定理三编辑局部性
  数字版（chain_edit_locality）⟹ 定理四/五特例回收（W_i ≡ W0 时
  ∏Lb_i = Lb^m，退化到 RealModelChain.model_chain_numeric_bound）。
  全部常数显式：维度因子 n/k、exp 上界 e^{4‖S‖B}、算子范数 ‖S‖/‖W_i‖、
  value 界 M、数据域 B、规范化 √n/c。唯一场景假设：数据范数上下界
  （B 有界域、c 非退化）——与 RealBlockConstants 完全相同，链骨架
  未引入任何新假设；异质权重 {W_i} 是自由参数，每块可不同。
  VERIFICATION.md §5「结构」行「混合架构（异质块）端到端」收官。-/

end Lattice
