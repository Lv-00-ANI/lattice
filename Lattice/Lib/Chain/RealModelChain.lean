import Mathlib
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Architectures.RealBlockLipschitz
import Lattice.Lib.Architectures.RealBlockInstance
import Lattice.Lib.Architectures.RealBlockConstants
/-!
# LATTICE: 端到端常数代入 n 块链 —— 完整模型前向链的数字闭式收官

VERIFICATION.md §5「结构」行「通用化方向：端到端常数代入 n 块链」的收官：
把 v4 已证的单块**数字闭式**（RealBlockConstants.transformer_block_numeric）
代入 n 块同构链（RealBlockLipschitz.chainN_identical_blocks_bound /
RealChain.chainN_error_bound 的常数连乘骨架），得到完整模型前向链的
**端到端纯数字常数误差界**。

**⚠ 常数收紧（Z1-5，v14）**：本文件的 Lf 由松弛版 `2√n/c` 收紧为**已证紧常数**
`√n/c`（`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`）；`RealRMSNormSharpness`
经 `RealBlockInstance` / `RealBlockConstants` **传递导入**，本文件不需新增 import。
下游端到端常数 `Lb` 相应整体收紧 2 倍。松弛版仍是有效上界
（`RealBlockInstance.transformer_block_closed_relaxed`）。

模型（块）：Block(z) = RMSNorm(z + Attn(z) + FFN(z))，
Attn(z) = Σᵢ softmax(Sz)ᵢ·(Vᵢ z)（softmax 权重随输入的完整注意力，RealBlockConstants），
FFN(z) = W z（线性层）。

单块数字闭式（来自 transformer_block_numeric，本文件仅读出为常数 def）：
  Lb = (√n/c)·(1 + La + ‖W‖)，La = M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)
其中 n = 嵌入维数、k = 注意力头数、S = 分数线性映射（如 QKᵀ/√d）、
V = value 投影、W = FFN 线性层、M = max‖Vᵢ‖、B = 数据范数上界、
c = RMSNorm 数据范数下界。

定理链（全部数字常数闭式，无 open 假设）：
  1. model_block_lipschitz_numeric：单块 Lb-Lipschitz（∀x y），
     Block = RMSNorm∘(id + Attn + FFN)；
  2. model_chain_numeric_bound（核心）：m 个同构块串成链的端到端误差
     ≤ Lb^m·‖x−y‖（把数字常数 Lb 代入 chainN_identical_blocks_bound）；
  3. model_chain_edit_locality_numeric：第 k 块入口扰动 δ 经尾部块放大
     ≤ Lb^(m−k)·‖δ‖（chain_edit_locality 的数字常数版）；
  4. model_chain_numeric_expanded：Lb 完全展开的端到端界（纯数字，
     显式含 n、c、B、k、‖S‖、M、‖W‖）。

诚实假设（模型无关，均显式标注；与 RealBlockConstants 完全相同）：
  · [NeZero n] [NeZero k]：嵌入维数/注意力头数非零（RMSNorm 非退化
    + softmax 分母为正的前提，transformer_block_numeric 所需）；
  · hc : 0 < c：RMSNorm 定义域范数下界为正（Lf = √n/c 的分母）；
  · hM：value 投影界 max‖Vᵢ‖ ≤ M；
  · hB：数据范数上界 ∀z, ‖z‖ ≤ B（softmax 分数有界 |S z| ≤ ‖S‖·B 的前提）；
  · hx、hy：**点对**定义域前提 `c ≤ ‖x‖`、`c ≤ ‖y‖`（RMSNorm 非退化域）。
    **⚠ v14（B53 修复）**：旧稿写的是 `hxdom：∀z, c ≤ ‖z‖`，它与 `hc : 0 < c`
    **矛盾**（`z := 0` ⟹ `c ≤ 0`）⟹ **前提不可满足、定理空洞**（CORRECTIONS B53）。
    现改为点对形式——这才是 `RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`
    本来需要的契约。**可满足性见证**：取 `x = y = c • e₀`（`e₀` 为单位基向量，
    `‖c • e₀‖ = c`）即同时满足 `hx`/`hy`；
  · hreach（链式定理 2/3/4 专有）：**链上每个中间激活都在定义域内**。链式定理不能只用
    点对前提——第 k 层的输入是 `ChainFwd … k x`，要用单块定理就必须知道**它**也在域内。
    **⚠ 这是有意作为前提传入的**（B53 允许的降级：可达性作为显式前提），
    而**不是**被证结论。它**可满足**：`Fs` 取恒等链、`x = c • e₀` 时每个迭代都等于 `x`。
    **诚实边界**：本文件**不证明**真实 transformer 块链满足 `hreach`（那需要
    「块输出范数下界」的实质分析，是后续独立立项）；`hreach` 是**显式的、可满足的**
    假设，其地位与 `hB`/`hM` 完全相同，故定理**不再是空洞的**。

模型无关：链骨架（ChainFwd/ChainTail/chainN_error_bound/chain_edit_locality）
对任意范数空间成立；本文件只把单块数字常数代入该骨架——端到端误差界是
「Lipschitz 常数连乘」的直接数字实例化，不含任何新分析假设。
命名说明：链长用 m（n 已被嵌入维数占用，与既有文件 EuclideanSpace ℝ (Fin n)
的记号一致）。

端到端意义：‖ChainFwd Block m x − ChainFwd Block m y‖ ≤ (Lb)^m·‖x−y‖——
模型任意两输入在 m 层前向后的距离被 Lb^m 放大/压缩：Lb < 1 即指数收缩
（编辑遗忘/初始化收缩），Lb > 1 即误差指数放大（敏感度上界）。
-/

noncomputable section

namespace Lattice

/-! ## 完整 transformer 块算子（数字闭式实例化）
Block(z) = RMSNorm(z + SoftmaxAttnOp S V z + W z)，与
RealBlockConstants.transformer_block_numeric 的被证算子完全一致。-/

def ModelBlock {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  RMSNormOp (z + SoftmaxAttnOp S V z + W z)

/-! ## 单块数字闭式常数
Lb = (√n/c)·(1 + La + ‖W‖)，La = M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)
（从 transformer_block_numeric 的 RHS 读出，纯数字，依赖 ℝ 的
开方/指数/算子范数，标 noncomputable）。

**⚠ 常数收紧（Z1-5，v14）**：旧稿 Lf = 2√n/c（松弛 2 倍），现改为已证的
紧常数 `√n/c`（`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`）——
本定义与 `transformer_block_numeric` 的 RHS **同步**收紧。 -/

def modelBlockLb {n k : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) : ℝ :=
  (Real.sqrt n / c)
    * (1 + (M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖))) + ‖W‖)

/-! ## 引理：Lb 非负（幂不等式 Lb^m 单调放大的前提）
M ≥ 0（由 value 界 + 范数非负）、B ≥ 0（由数据上界在 0 处）、
各因子（√n、k、k+1、e^{4‖S‖B}、‖S‖、‖W‖）非负 ⟹ Lb ≥ 0。-/

lemma model_block_lb_nonneg {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    -- B369 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).  The proof
    -- consumed it ONLY to obtain `0 ≤ B` (:122), so that is what it now takes --
    -- the weakest hypothesis the argument actually needs.
    (hB0 : 0 ≤ B) :
    0 ≤ modelBlockLb S W M B c := by
  -- M ≥ 0：[NeZero k] 保证存在指标 i₀，0 ≤ ‖V i₀‖ ≤ M
  have hM0 : 0 ≤ M := by
    rcases (Fin.pos_iff_nonempty.mp (NeZero.pos k)) with ⟨i₀⟩
    linarith [hM i₀, norm_nonneg (V i₀)]
  dsimp [modelBlockLb]
  -- 因子一：Lf = √n/c ≥ 0（√n ≥ 0、c > 0）
  have hLf : 0 ≤ Real.sqrt n / c := by positivity
  -- 因子二：k·(k+1)·e^{4‖S‖B} ≥ 0（RealBlockConstants 已证同形 positivity）
  have hcoef : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) := by positivity
  have hfac : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖ :=
    mul_nonneg hcoef (norm_nonneg S)
  have hbrack : 0 ≤ 1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖) := by
    nlinarith [mul_nonneg hB0 hfac]
  have hmain : 0 ≤ M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖)) :=
    mul_nonneg hM0 hbrack
  have hsum : 0 ≤ 1 + (M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖))) + ‖W‖ := by
    nlinarith [hmain, norm_nonneg W]
  exact mul_nonneg hLf hsum

/-! ## 定理一：单块数字 Lipschitz
Block = RMSNorm∘(id + Attn + FFN)（SoftmaxAttnOp 完整注意力）是
Lb = (√n/c)·(1 + La + ‖W‖)-Lipschitz：∀x y，误差 ≤ Lb·‖x−y‖。
直接从 transformer_block_numeric 读出常数（simpa 展开两个 def）。

**⚠ v14（B53 修复）定义域前提为点对**：只涉及 `x`、`y` 两点，故用点对假设。
⚠ **v15 更正（B60）**：位置必须是 **RMSNorm 的实际输入（内层残差和）**，
即 `(hx : c ≤ ‖x + SoftmaxAttnOp S V x + W x‖)`——**不是** `c ≤ ‖x‖`
（设在 `x` 上会让下游 `transformer_block_numeric` 的点对前提无法满足）。
**见证**：`x = y = c • e₀` 且注意力/FFN 取零映射。 -/

theorem model_block_lipschitz_numeric {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    -- B369 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).  Single-step
    -- theorem -- the bound is needed only at x and y.
    (x y : EuclideanSpace ℝ (Fin n))
    (hBx : ‖x‖ ≤ B) (hBy : ‖y‖ ≤ B)
    (hx : c ≤ ‖x + SoftmaxAttnOp S V x + W x‖)
    (hy : c ≤ ‖y + SoftmaxAttnOp S V y + W y‖) :
    ‖ModelBlock S V W x - ModelBlock S V W y‖
      ≤ modelBlockLb S W M B c * ‖x - y‖ := by
  simpa [ModelBlock, modelBlockLb] using
    transformer_block_numeric S V W M B c hc hM x y hBx hBy hx hy

/-! ## 辅助引理：定义域受限的点对链界（B53 修复的基础设施）
`chainN_dom_bound`：把 `RealChain.chainN_error_bound` 的**全局** Lipschitz 前提
`∀ x y, …` 弱化为**沿链逐点**的前提——每层只需对**该层实际输入的那一对点**成立。
这正是「点对定义域假设」下的链式组合所需的形式（B53 的核心难点）。

前提：
  · `hL`：对每个 `i`，`Fs i` 在**点对** `(ChainFwd Fs i x, ChainFwd Fs i y)` 上
    `Ls i`-Lipschitz；
  · `hL0`：常数非负。
结论：`‖ChainFwd Fs m x − ChainFwd Fs m y‖ ≤ (∏_{i<m} Ls i)·‖x−y‖`。

⚠ 本引理**不引入任何不可满足的前提**：`hL` 只谈链上真实出现的点。 -/

theorem chainN_dom_bound {X : Type*} [NormedAddCommGroup X]
    (Fs : ℕ → X → X) (Ls : ℕ → ℝ) (m : ℕ) (x y : X)
    (hL : ∀ i, i < m →
      ‖Fs i (ChainFwd Fs i x) - Fs i (ChainFwd Fs i y)‖
        ≤ Ls i * ‖ChainFwd Fs i x - ChainFwd Fs i y‖)
    (hL0 : ∀ i, i < m → 0 ≤ Ls i) :
    ‖ChainFwd Fs m x - ChainFwd Fs m y‖ ≤ (∏ i in Finset.range m, Ls i) * ‖x - y‖ := by
  -- ⚠ `generalizing x y`：归纳假设必须对**任意**起点两点成立
  -- （下游各定理传入的是 `ChainFwd … j x` 这类随 `m` 变化的点）。
  induction m generalizing x y with
  | zero => simp [ChainFwd]
  | succ m ih =>
      -- 前 m 层的界（前提按 i < m 收缩）
      have ih' : ‖ChainFwd Fs m x - ChainFwd Fs m y‖
          ≤ (∏ i in Finset.range m, Ls i) * ‖x - y‖ :=
        ih x y (fun i hi => hL i (Nat.lt_trans hi (Nat.lt_succ_self m)))
          (fun i hi => hL0 i (Nat.lt_trans hi (Nat.lt_succ_self m)))
      -- 第 m 层（索引 m）在链上该对点处的 Lipschitz 性
      have hstep : ‖Fs m (ChainFwd Fs m x) - Fs m (ChainFwd Fs m y)‖
          ≤ Ls m * ‖ChainFwd Fs m x - ChainFwd Fs m y‖ := hL m (Nat.lt_succ_self m)
      calc
        ‖ChainFwd Fs (m + 1) x - ChainFwd Fs (m + 1) y‖
            = ‖Fs m (ChainFwd Fs m x) - Fs m (ChainFwd Fs m y)‖ := rfl
        _ ≤ Ls m * ‖ChainFwd Fs m x - ChainFwd Fs m y‖ := hstep
        _ ≤ Ls m * ((∏ i in Finset.range m, Ls i) * ‖x - y‖) :=
              mul_le_mul_of_nonneg_left ih' (hL0 m (Nat.lt_succ_self m))
        _ = (∏ i in Finset.range (m + 1), Ls i) * ‖x - y‖ := by
              rw [Finset.prod_range_succ]
              ring

/-! ## 定理二：m 个同构块链的端到端数字界（核心）
m 个同构块（每块 Lb-Lipschitz，定理一）串成链，端到端误差
≤ Lb^m·‖x−y‖——把数字常数 Lb 代入 `chainN_dom_bound`（本文件辅助引理，
点对定义域版链骨架；`∏` 常数 = 幂）。

**⚠ v14（B53 修复）链式可达性作为显式前提**：第 k 层要对 `ChainFwd … k x`
用单块定理，就必须知道**它**在 RMSNorm 定义域内——点对前提不足以代替。
故这里显式传入 `hreach`（链上每个中间激活的范数下界）。⚠ **`hreach` 是有意
作为前提传入的**（B53 允许的降级），**可满足**：恒等链 + `x = c • e₀`。
本文件不证真实块链满足它（见文件头「诚实边界」）。 -/

theorem model_chain_numeric_bound {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    -- B369 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).  This
    -- is a CHAIN theorem: the proof passes `ChainFwd … i x`, which varies
    -- with i, so a pointwise bound cannot discharge it.  Stated on the
    -- visited set -- finite, therefore satisfiable (V11's D1).
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ ≤ B
      ∧ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j y‖ ≤ B)
    (hreach : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x
              + SoftmaxAttnOp S V (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x)
              + W (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x)‖
      ∧ c ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j y
              + SoftmaxAttnOp S V (ChainFwd (fun _ : ℕ => ModelBlock S V W) j y)
              + W (ChainFwd (fun _ : ℕ => ModelBlock S V W) j y)‖) :
    ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) m x
      - ChainFwd (fun _ : ℕ => ModelBlock S V W) m y‖
      ≤ (modelBlockLb S W M B c) ^ m * ‖x - y‖ := by
  have hLb : 0 ≤ modelBlockLb S W M B c :=
    model_block_lb_nonneg S V W M B c hc hM (le_trans (norm_nonneg _) (hBc 0 (Nat.zero_le m)).1)
  -- 用点对版链骨架：每层的域条件（内层残差和）由 hreach 在该下标处提供
  have hb := chainN_dom_bound (fun _ : ℕ => ModelBlock S V W)
    (fun _ : ℕ => modelBlockLb S W M B c) m x y
    (fun i hi =>
      model_block_lipschitz_numeric S V W M B c hc hM
        (ChainFwd (fun _ : ℕ => ModelBlock S V W) i x)
        (ChainFwd (fun _ : ℕ => ModelBlock S V W) i y)
        (hBc i (Nat.le_of_lt hi)).1 (hBc i (Nat.le_of_lt hi)).2
        (hreach i (Nat.le_of_lt hi)).1 (hreach i (Nat.le_of_lt hi)).2)
    (fun _ _ => hLb)
  simpa [Finset.prod_const, Finset.card_range] using hb

/-! ## 定理三：链编辑局部性（数字版）
第 k 块入口注入扰动 δ，经尾部块（块 k..m-1）传播：
端到端变化 ≤ Lb^(m−k)·‖δ‖（chain_edit_locality 的 Ls 全取 Lb 的
数字实例化，∏ 常数 = 幂）。

**⚠ v14（B53 修复）链式可达性作为显式前提**：尾部链的每层输入是
`ChainFwd F j (x+δ)` 与 `ChainFwd F j x`（`F = ModelBlock S V W`，
`j ≤ m−kk`），用单块定理需知二者在域内。故显式传入 `hreach`（**有意作为
前提**，B53 允许的降级）：两条轨迹在尾部各层的范数下界。**可满足**：
δ = 0 时退化为定理二的情形（恒等链 + `x = c • e₀`）。 -/

theorem model_chain_edit_locality_numeric {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m kk : ℕ) (δ x : EuclideanSpace ℝ (Fin n))
    -- B369 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).  This
    -- is a CHAIN theorem: the proof passes `ChainFwd … i x`, which varies
    -- with i, so a pointwise bound cannot discharge it.  Stated on the
    -- visited set -- finite, therefore satisfiable (V11's D1).
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j (x + δ)‖ ≤ B
      ∧ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ ≤ B)
    (hreach : ∀ j ≤ m - kk,
        c ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j (x + δ)
              + SoftmaxAttnOp S V (ChainFwd (fun _ : ℕ => ModelBlock S V W) j (x + δ))
              + W (ChainFwd (fun _ : ℕ => ModelBlock S V W) j (x + δ))‖
      ∧ c ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x
              + SoftmaxAttnOp S V (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x)
              + W (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x)‖) :
    ‖ChainTail (fun _ : ℕ => ModelBlock S V W) kk m (x + δ)
      - ChainTail (fun _ : ℕ => ModelBlock S V W) kk m x‖
      ≤ (modelBlockLb S W M B c) ^ (m - kk) * ‖δ‖ := by
  have hLb : 0 ≤ modelBlockLb S W M B c :=
    model_block_lb_nonneg S V W M B c hc hM (le_trans (norm_nonneg _) (hBc 0 (Nat.zero_le m)).1)
  -- 尾部链按 ChainTail 定义就是「平移后的层函数」上的 (m−kk) 层链；
  -- 同构链的层函数与下标无关（`fun j => F (kk+j)` 与 `F` 定义等价），故平移可吸收。
  have htail : ∀ z : EuclideanSpace ℝ (Fin n),
      ChainTail (fun _ : ℕ => ModelBlock S V W) kk m z
        = ChainFwd (fun _ : ℕ => ModelBlock S V W) (m - kk) z := by
    intro z
    rfl
  rw [htail (x + δ), htail x]
  -- 起点两点的差恰为 δ
  have hstart : (x + δ) - x = δ := by abel
  -- 用点对版链骨架：每层的域由 hreach 提供
  have hb := chainN_dom_bound (fun _ : ℕ => ModelBlock S V W)
    (fun _ : ℕ => modelBlockLb S W M B c) (m - kk) (x + δ) x
    (fun i hi =>
      model_block_lipschitz_numeric S V W M B c hc hM
        (ChainFwd (fun _ : ℕ => ModelBlock S V W) i (x + δ))
        (ChainFwd (fun _ : ℕ => ModelBlock S V W) i x)
        -- B369: hi : i < m - kk (domain of hreach), but hBc is stated over
        -- j <= m.  Bridge with le_trans on the index.
        (hBc i (le_trans (Nat.le_of_lt hi) (Nat.sub_le m kk))).1
        (hBc i (le_trans (Nat.le_of_lt hi) (Nat.sub_le m kk))).2
        (hreach i (Nat.le_of_lt hi)).1 (hreach i (Nat.le_of_lt hi)).2)
    (fun _ _ => hLb)
  rw [hstart] at hb
  simpa [Finset.prod_const, Finset.card_range] using hb

/-! ## 定理四：完全展开的端到端数字界
与定理二同内容，但把 Lb 完全展开为纯数字常数（显式含
n、c、B、k、‖S‖、M、‖W‖），便于直接数值代入。

**⚠ v14（B53 修复）**：域前提与定理二同步改为链式可达性 `hreach`
（**有意作为前提**，**可满足**），详见定理二 docstring 与文件头「诚实边界」。 -/

theorem model_chain_numeric_expanded {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ) (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    -- B369 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE (B357).  This
    -- is a CHAIN theorem: the proof passes `ChainFwd … i x`, which varies
    -- with i, so a pointwise bound cannot discharge it.  Stated on the
    -- visited set -- finite, therefore satisfiable (V11's D1).
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ ≤ B
      ∧ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j y‖ ≤ B)
    (hreach : ∀ j ≤ m,
        c ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x
              + SoftmaxAttnOp S V (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x)
              + W (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x)‖
      ∧ c ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j y
              + SoftmaxAttnOp S V (ChainFwd (fun _ : ℕ => ModelBlock S V W) j y)
              + W (ChainFwd (fun _ : ℕ => ModelBlock S V W) j y)‖) :
    ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) m x
      - ChainFwd (fun _ : ℕ => ModelBlock S V W) m y‖
      ≤ (((Real.sqrt n / c)
          * (1 + (M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1)
              * Real.exp (4 * (‖S‖ * B)) * ‖S‖))) + ‖W‖)) ^ m)
        * ‖x - y‖ := by
  simpa [modelBlockLb] using
    model_chain_numeric_bound S V W M B c hc hM m x y hBc hreach

/-! ## 注：端到端收官闭环
  单块数字闭式（transformer_block_numeric，RealBlockConstants）⟹
  定理一读出 Lb（纯数字常数 def）⟹ 定理二代入同构块链（
  chainN_identical_blocks_bound）得端到端 (Lb)^m·‖x−y‖ ⟹ 定理三
  编辑局部性数字版（chain_edit_locality）⟹ 定理四完全展开。
  全部常数显式：维度因子 n/k、exp 上界 e^{4‖S‖B}、算子范数 ‖S‖/‖W‖、
  value 界 M、数据域 B、规范化 √n/c。唯一场景假设：数据范数上下界
  （B 有界域、c 非退化）——与 RealBlockConstants 完全相同，链骨架
  未引入任何新假设。VERIFICATION.md §5「结构」行收官。-/

end Lattice
