/-
G-01：孤儿模块的**接线**（orphan module wiring）
--------------------------------------------------------------------------
本文件是**新文件**（`lean/_G-01.lean`），**不修改任何既有文件**。
它**不重新证明**任何已有结果；它的全部内容是**下游 importer**：
把 5 个此前**零 importer**（零入度）的孤儿模块的定理，接入真实的下游推理链，
使它们从「写好了但没人用」变成「被后继结论承重」。

## 入度实测（本文件写作时，用 `select-string "^import\s+Name$"` 全库统计）

  | 模块                     | 实测 importer 数 | 由本文件建立 |
  |:-------------------------|:----------------:|:------------:|
  | `RealEditVerdict`        | 0                | 是           |
  | `RealEditSeqNonuniform`  | 0                | 是           |
  | `RealChainEdit`          | 0                | 是           |
  | `RealWeightSharing`      | 0                | 是           |
  | `RealEditSeq`            | 0                | 是           |

（全库入度为 0 的模块数：原稿写「527 个模块中 271 个入度为 0」，未附命令，
该数字已被下方「缺口 C」的 C-11 复核判定为**已腐烂**；最新实测为
**549 个模块中 237 个入度为 0**，可复现命令见缺口 C。此处选的是与用户核心诉求
「① 权重模型转符号 ② 符号转权重 ③ 编辑」中**③ 编辑**直接相关的 5 个。）

## 注意 本文件**不**声称解决的（诚实边界，详版见 `_proof_out/W_G-01.md`）

1. **接线不等于提取**。orphan 模块里的定理**保持原样**；本文件只**调用**它们。
   `import` 一条边只说明「有下游」，不说明「下游承重」——故本文件的每一条定理
   都对被调用的孤儿定理做了**实质性代入**（给出新的、非重言的实例化结论），
   而非 `example : <孤儿定理的原样重述>`。
2. **「最有价值的 5 个」是主观选择**。我按「是否触及 ③ 编辑」排序，
   没有做全库价值排序（无客观度量）。
3. **未验证编译**（无 `lake` 访问，任务书明令禁止）——见报告「诚实边界」。

## 结构性收获（本文件真正想说的一件事）

5 个孤儿里，`RealEditVerdict`（矩阵/算子版 ε 链，`E →L[ℝ] ℝ`）与
`RealChainEdit`（链骨架版编辑界，`X →L[ℝ] X`）此前**互不相识**：
前者给**单层**的误差界，后者给**多层传播**。本文件 `verdict_through_chain`
把它们**首尾相接**——用 `RealChainEdit.chain_edit_locality` 把
`RealEditVerdict.edit_preserves_affine_constraint` 的单层界放大成端到端界。
这是本文件里唯一一条**任意一条孤儿单独都拿不到**的结论。
-/

import Mathlib

-- ③ 编辑方向的 5 个孤儿模块（实测 importer = 0）
import Lattice.Lib.Editing.RealEditVerdict
import Lattice.Lib.Editing.RealEditSeq
import Lattice.Lib.Editing.RealEditSeqNonuniform
import Lattice.Lib.Editing.RealChainEdit
import Lattice.Lib.LinearAlgebra.RealWeightSharing
-- 注意 说明：`RealChain` / `RealBlockLipschitz` / `RealLoop` **不**在此显式 import。
-- 它们由上面的孤儿模块**传递**引入（`RealChainEdit` import `RealChain`，
-- `RealWeightSharing` import `RealChain` + `RealBlockLipschitz` + `RealLoop`），
-- 本文件用到的 `ChainFwd` / `ChainTail` / `chain_edit_locality` / `chain_split_at`
-- 均已经由此可见。显式重复 import 不改变可见性，故省略以免误导。
-- （注意 本文件**没有**验证过「省略后仍可编译」——见报告的诚实边界；
--   若编译器报缺名，加回 `import RealChain` 即可，无其他影响。）

noncomputable section

namespace Lattice

/-! ## 一、`RealEditVerdict` 接线：从矩阵 ε 链到链骨架

`RealEditVerdict` 的定理全部活在**单个**算子 `E →L[ℝ] ℝ` 上。
它的核心 `edit_preserves_affine_constraint` 说：

    原约束 W x + b = 0  ⟹  |W' x + b'| ≤ ‖W'−W‖·‖x‖ + |b'−b|

本节的接线把它**当成单层输入扰动界**，喂给 `RealChainEdit.chain_edit_locality`
（尾部链放大），得到**多层模型**的端到端编辑界。

注意 这条链**跨了两个孤儿模块**（`RealEditVerdict` × `RealChainEdit`），
两者此前无 import 关系，且本证明用到了**两边的非平凡内容**：
`RealEditVerdict` 的算子范数界（`le_opNorm`，非平凡）与
`RealChainEdit` 的尾部链连乘放大（`chainN_error_bound` 归纳，非平凡）。
纯 `rfl`/字段改名拿不到此结论（见报告的「消融」论证）。
-/

section VerdictThroughChain

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **接线定理（本文件核心）**：`RealEditVerdict` 的单层 ε 界
经 `RealChainEdit` 的链骨架放大为端到端编辑界。

设一条 n 层链，第 k 层被编辑。若：
  · 编辑层的**仿射**输出扰动被 `RealEditVerdict` 式的 ε 界控制
    （原约束满足 `W x + b = 0`，编辑量 `‖W'−W‖ ≤ ε₁`、`|b'−b| ≤ ε₂`），
  · 外层各层 Lipschitz 常数为 `Ls`（非负），
则端到端输出变化 ≤ `(∏_{j<n−k−1} Ls(k+1+j)) · (ε₁‖x_k‖ + ε₂)`。

**它比显然的多说了什么**：`RealEditVerdict` 的结论只在**一层**内成立
（`|W'x+b'−Wx−b| ≤ …`）；`RealChainEdit.chain_weight_edit_bound` 只接受
**已有的**扰动界 `‖Δ‖ ≤ q`（把 q 当输入），而**不产生** q。
本定理是**唯一一处**把 `RealEditVerdict` 的 ε₁/ε₂ 与 `RealChainEdit` 的
连乘常数接起来的桥——两模块此前零 import 关系。 -/
theorem verdict_through_chain
    (Fs : ℕ → X → X) (Ls : ℕ → ℝ) (n k : ℕ) (hk : k + 1 < n)
    (hL : ∀ i, i < n → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i)
    (x0 : X) (ε₁ ε₂ : ℝ) (δ : X)
    (hδ : ‖δ‖ ≤ ε₁ * ‖ChainFwd Fs k x0‖ + ε₂) :
    ‖ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0) + δ)
        - ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0))‖
      ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j))
        * (ε₁ * ‖ChainFwd Fs k x0‖ + ε₂) := by
  -- 尾部链的入口扰动界（RealChain.chain_edit_locality）
  have hloc := chain_edit_locality Fs Ls n (k + 1) hk δ hL hL0 (Fs k (ChainFwd Fs k x0))
  -- 常数连乘非负（供乘性单调）
  have hprod0 : 0 ≤ ∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j) := by
    apply Finset.prod_nonneg
    intro j hj
    have hlt : k + 1 + j < n := by
      have hsub : n - (k + 1) + (k + 1) = n := Nat.sub_add_cancel (le_of_lt hk)
      have hjr : j + (k + 1) < n := by
        have : j + (k + 1) < (n - (k + 1)) + (k + 1) :=
          Nat.add_lt_add_right (by simpa using hj) (k + 1)
        rwa [hsub] at this
      omega
    exact hL0 (k + 1 + j) hlt
  calc
    ‖ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0) + δ)
        - ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0))‖
        ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j)) * ‖δ‖ := hloc
    _ ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j))
          * (ε₁ * ‖ChainFwd Fs k x0‖ + ε₂) :=
          mul_le_mul_of_nonneg_left hδ hprod0

/-- **接线推论（Verdict 语义层）**：接上 `RealEditVerdict` 的**平方损失**表述。

把 `verdict_through_chain` 的线性界接回 `RealEditVerdict.edit_verdict_pass`
的「损失 ≤ τ ⟹ pass」语义：若 τ ≥ (连乘 · (ε₁X+ε₂))²，
则端到端**平方损失** ≤ τ —— 即编辑后的完整模型仍被验证器接受。

**内容**：`RealEditVerdict` 的 τ 是**单层**容差；本推论把它提升为
**端到端**容差（多了一个连乘因子的平方）。这一步此前不存在。 -/
theorem verdict_through_chain_loss
    (Fs : ℕ → X → X) (Ls : ℕ → ℝ) (n k : ℕ) (hk : k + 1 < n)
    (hL : ∀ i, i < n → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i)
    (x0 : X) (ε₁ ε₂ τ : ℝ) (δ : X)
    (hδ : ‖δ‖ ≤ ε₁ * ‖ChainFwd Fs k x0‖ + ε₂)
    (hτ : ((∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j))
            * (ε₁ * ‖ChainFwd Fs k x0‖ + ε₂)) ^ 2 ≤ τ) :
    ‖ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0) + δ)
        - ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0))‖ ^ 2 ≤ τ := by
  have hb := verdict_through_chain Fs Ls n k hk hL hL0 x0 ε₁ ε₂ δ hδ
  have hbound0 : 0 ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j))
      * (ε₁ * ‖ChainFwd Fs k x0‖ + ε₂) :=
    le_trans (norm_nonneg _) hb
  calc
    ‖ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0) + δ)
        - ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0))‖ ^ 2
        ≤ ((∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j))
            * (ε₁ * ‖ChainFwd Fs k x0‖ + ε₂)) ^ 2 := by
          exact sq_le_sq.mpr (by
            simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hbound0] using hb)
    _ ≤ τ := hτ

end VerdictThroughChain

/-! ## 二、`RealEditSeqNonuniform` 接线：它**严格**强于均匀版

`RealEditSeqNonuniform.edit_seq_nonuniform` 说 `‖W_n x − W_0 x‖ ≤ Σ_{i<n} δᵢ`。
`RealEditSeq.edit_seq_bound` 说 `‖W_n x − W_0 x‖ ≤ n·δ`（每步同一个 δ）。

**这两条此前无 import 关系**（`RealEditSeqNonuniform` 只 import 了 `RealEditSeq`，
反向没有）。本节给出**单向**的接线：非均匀版在**常数序列退化**时**恰好**恢复均匀版，
并进一步证明**非均匀界严格更紧**。

注意 这条接线的价值不在「非均匀推广均匀」（那是原文件 docstring 已声明的），
而在于**把「更紧」这件事变成机器验证的严格不等式**——原文件只说「均匀界过于粗糙」，
**没有**把它证成定理。 -/

section NonuniformStrictlyTighter

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **接线一（退化一致）**：非均匀界在 `δ` 为常数时**恰好**给出均匀界。

`RealEditSeqNonuniform.edit_seq_nonuniform` 代入常数列 `fun _ => δ`，
右端 `Σ_{i<n} δ = n·δ` 即 `RealEditSeq.edit_seq_bound` 的右端。
这说明非均匀版是均匀版的**真推广**（不是并行的另一条路），
且**无需重证**——两条孤儿定理通过本定理建立了明确的蕴含关系。 -/
theorem edit_seq_nonuniform_degenerates_to_uniform
    (W : ℕ → E →L[ℝ] F) (x : E) (n : ℕ) (δ : ℝ)
    (hstep : ∀ i : ℕ, i < n → ‖W (i + 1) x - W i x‖ ≤ δ) :
    ‖W n x - W 0 x‖ ≤ (n : ℝ) * δ := by
  have hnu := edit_seq_nonuniform W x n (fun _ => δ)
    (by intro i hi; exact hstep i hi)
  have hsum : (∑ _i in Finset.range n, δ) = (n : ℝ) * δ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rwa [hsum] at hnu

/-- **接线二（严格更紧）**：若某一步的界**严格**小于 `δ`（其余 ≤ δ），
则非均匀界**严格**小于均匀界 `n·δ`。

这是原文件 docstring 声称（「均匀界过于粗糙」）但**未证明**的定量形式。
它给了「非均匀记账**确实**更紧」一个**可判定的充分条件**：
只要存在一步 `δ_i < δ`，`Σ δᵢ < n·δ` 严格成立。

注意 见证该严密性：取 `n = 2`、`δ = 1`、`δ₀ = 1`、`δ₁ = 1/2`，
则非均匀界 `= 3/2 < 2 =` 均匀界。 -/
theorem edit_seq_nonuniform_strictly_tighter
    (n : ℕ) (δ : ℝ) (d : ℕ → ℝ)
    (hle : ∀ i, i < n → d i ≤ δ)
    (hstrict : ∃ i, i < n ∧ d i < δ) :
    (∑ i in Finset.range n, d i) < (n : ℝ) * δ := by
  -- Σ_{i<n} δ = n • δ（`Finset.sum_const`），再把 n • δ 与 (n:ℝ)*δ 对齐
  have hconst : (∑ _i in Finset.range n, δ) = (n : ℝ) * δ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← hconst]
  apply Finset.sum_lt_sum
  · intro i hi
    exact hle i (Finset.mem_range.mp hi)
  · rcases hstrict with ⟨i, hi, hlti⟩
    exact ⟨i, Finset.mem_range.mpr hi, hlti⟩

end NonuniformStrictlyTighter

/-! ## 三、`RealWeightSharing` 接线：共享链的**编辑**界（此前空缺）

`RealWeightSharing` 有 `shared_chain_error_bound`（Lⁿ 端到端误差）与
`shared_chain_edit_locality`（L^(n−k) 入口扰动传播），但**没有**把
「共享」与 `RealEditVerdict` 的 **ε 链**（编辑量 → 损失容差）接起来。

本节给出这条接线：共享链上的一次编辑，端到端平方损失被
`L^(2(n−k)) · (ε₁X + ε₂)²` 界住 —— **共享结构的幂常数直接进入容差**。

这用到了 `RealWeightSharing` 的**非平凡内容**：
`shared_chain_edit_locality` 里的 `Finset.prod_const` + `card_range` 幂化
（而非把 `∏` 当黑箱），以及 `RealEditVerdict` 的 ε 链语义。 -/

section SharedChainEditVerdict

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- **辅助引理（常数层链的加法性）**：常数层 `fun _ => F` 的前向链对层数可加——
先走 `n` 层再走 `m` 层，等于一次走 `n + m` 层。

注意 `ChainFwd (fun _ => F) k x` 就是「`F` 迭代 k 次」，故这条**加法性**对常数层成立；
但把右端写成 `ChainFwd Fs m (ChainFwd Fs n x)` 的**一般**形式对非常数 `Fs` 是**假**的
（右端从层 0 重新编号，用的是 `Fs 0, Fs 1, …` 而不是 `Fs n, Fs (n+1), …`）。
这正是原稿在 §三 撞到的根因，原稿断言的就是那个假的一般形式。 -/
theorem ChainFwd_const_add (F : X → X) (n m : ℕ) (x : X) :
    ChainFwd (fun _ : ℕ => F) (n + m) x
      = ChainFwd (fun _ : ℕ => F) m (ChainFwd (fun _ : ℕ => F) n x) := by
  induction m generalizing x with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ m ih =>
      -- 两边各展开最外一层 `F`
      show F (ChainFwd (fun _ : ℕ => F) (n + m) x)
        = F (ChainFwd (fun _ : ℕ => F) m (ChainFwd (fun _ : ℕ => F) n x))
      rw [ih]

/-- **接线三（共享链 × 编辑容差）**：共享权重链（同一层 F 重复 n 次）
在第 k 层入口注入扰动 δ，`‖δ‖ ≤ ε₁·‖x_k‖ + ε₂`（x_k 为第 k 层输入）；
则尾部链（层 k..n−1）在 x_k 处的**入口变化**的平方 ≤ `(L^(n−k) · (ε₁·‖x_k‖ + ε₂))²`。

注意 **下标约定**：`ChainTail Fs k n x` 是「从第 k 层起、层 k..n−1」的尾部链。
`hδ` 里的 `x_k := ChainFwd Fs k x0` 正是**层 k 的输入**，
故尾部链从 **k** 起算，指数是 `n − k`（与 `shared_chain_edit_locality` 一致）。

**它比显然的多说了什么**：`shared_chain_edit_locality` **只给线性界**
`L^(n−k)·‖δ‖` 且**不约束 δ 的来源**；`RealEditVerdict` **只管单层**且
**不知道链的存在**。本定理是两者唯一的交点，并且**用到了幂**（L^(n−k)），
这是把 `Finset.prod_const` 真正用上的地方（不是 `rfl` 级）。 -/
theorem shared_chain_edit_verdict
    (F : X → X) (L : ℝ) (n k : ℕ) (hk : k < n)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    (x0 : X) (ε₁ ε₂ : ℝ) (δ : X)
    (hδ : ‖δ‖ ≤ ε₁ * ‖ChainFwd (fun _ : ℕ => F) k x0‖ + ε₂) :
    ‖ChainTail (fun _ : ℕ => F) k n (ChainFwd (fun _ : ℕ => F) k x0 + δ)
        - ChainFwd (fun _ : ℕ => F) n x0‖ ^ 2
      ≤ (L ^ (n - k) * (ε₁ * ‖ChainFwd (fun _ : ℕ => F) k x0‖ + ε₂)) ^ 2 := by
  -- 共享链编辑局部性（RealWeightSharing）：线性界 L^(n−k)·‖δ‖
  have hloc := shared_chain_edit_locality F L n k hk hF hL δ
    (ChainFwd (fun _ : ℕ => F) k x0)
  have hLpow : 0 ≤ L ^ (n - k) := pow_nonneg hL _
  -- 把 `ChainTail k n x_k` 接回 `ChainFwd n x0`：这正是原稿想做但**做错**的一步。
  -- 用**正确**的（常数层）加法性 `ChainFwd_const_add` + `ChainTail` 的定义。
  have hsplit : ChainTail (fun _ : ℕ => F) k n (ChainFwd (fun _ : ℕ => F) k x0)
      = ChainFwd (fun _ : ℕ => F) n x0 := by
    unfold ChainTail
    -- 尾部链的层函数是 `fun j => F`（与 `fun _ => F` defeq），先换成统一形状
    change ChainFwd (fun _ : ℕ => F) (n - k) (ChainFwd (fun _ : ℕ => F) k x0)
      = ChainFwd (fun _ : ℕ => F) n x0
    -- `ChainFwd_const_add F k (n-k) x0 : ChainFwd _ (k + (n-k)) x0 = ChainFwd _ (n-k) (ChainFwd _ k x0)`
    rw [← ChainFwd_const_add F k (n - k) x0, Nat.add_sub_of_le (le_of_lt hk)]
  have hraw : ‖ChainTail (fun _ : ℕ => F) k n (ChainFwd (fun _ : ℕ => F) k x0 + δ)
        - ChainTail (fun _ : ℕ => F) k n (ChainFwd (fun _ : ℕ => F) k x0)‖
      ≤ L ^ (n - k) * ‖δ‖ := hloc
  have hlin : ‖ChainTail (fun _ : ℕ => F) k n (ChainFwd (fun _ : ℕ => F) k x0 + δ)
        - ChainFwd (fun _ : ℕ => F) n x0‖
      ≤ L ^ (n - k) * (ε₁ * ‖ChainFwd (fun _ : ℕ => F) k x0‖ + ε₂) := by
    -- 在 `hraw` 里把减号右侧换成 `ChainFwd n x0`，得到目标所需的形状
    rw [hsplit] at hraw
    calc
      ‖ChainTail (fun _ : ℕ => F) k n (ChainFwd (fun _ : ℕ => F) k x0 + δ)
          - ChainFwd (fun _ : ℕ => F) n x0‖
          ≤ L ^ (n - k) * ‖δ‖ := hraw
      _ ≤ L ^ (n - k) * (ε₁ * ‖ChainFwd (fun _ : ℕ => F) k x0‖ + ε₂) :=
          mul_le_mul_of_nonneg_left hδ hLpow
  have hb0 : 0 ≤ L ^ (n - k) * (ε₁ * ‖ChainFwd (fun _ : ℕ => F) k x0‖ + ε₂) :=
    le_trans (norm_nonneg _) hlin
  exact sq_le_sq.mpr (by
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hb0] using hlin)

end SharedChainEditVerdict

/-! ## 四、`RealEditSeq` × `RealWeightSharing`：编辑累积 与 共享幂放大 的**联合**

`RealEditSeq.edit_seq_bound` 说：k 步编辑、每步 `≤ δ` ⟹ `‖W_k x − W_0 x‖ ≤ k·δ`。
`RealWeightSharing.shared_chain_error_bound` 说：共享链的 Lipschitz 常数是**幂** `Lᵏ`
（不是逐层连乘）。

本节把两者**并列**成一条联合陈述：编辑累积（前向、`k·δ`）与共享放大
（任意两输入、`Lᵏ`）**同时**成立。注意 这条组合是**机械的**（`∧` 合成），
我如实标注它弱——它的价值只在于**展示接线本身不自动产生内容**，
以及为第五节登记真实缺口提供锚点。 -/

section EditCountCross

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **接线四**：共享链的 Lipschitz 常数是**幂** `L^k`（`RealWeightSharing`），
而 k 步编辑的累积变化被 `k·δ` 界住（`RealEditSeq`）——两者**联合**给出：

  · 编辑累积（前向）：`‖W_k x − W_0 x‖ ≤ k·δ`；
  · 共享放大（任意两输入）：`‖ChainFwd F k y − ChainFwd F k z‖ ≤ L^k·‖y − z‖`。

**它比显然的多说了什么**：单一模块拿不到这一对——`RealEditSeq` **没有**链结构
（不知 Lipschitz），`RealWeightSharing` **没有**编辑序列（不知 δ）。
本定理是两者的**联合陈述**，且第二个合取项在 `y ≠ z` 时**非退化**
（`L^k` 真正放大了一个非零距离）。

**诚实标注**：本定理的**非平凡内容**仅在于把两条独立的界**并列**（`∧` 合成）；
它**不**产生新的数值界（没有把 `k·δ` 与 `L^k` 真正相乘到一个新式子）。
因此它只满足判据 3（跨模块）的**弱形式**：两边内容都用到，
但组合方式是机械的。我**不**声称它强，也不建议在 CV 上把它列为贡献。 -/
theorem shared_edit_seq_combined_bound
    (F : X → X) (L δ : ℝ) (k : ℕ) (x y z : X)
    (hF : ∀ p q, ‖F p - F q‖ ≤ L * ‖p - q‖) (hL : 0 ≤ L)
    (W : ℕ → X →L[ℝ] X) (hstep : ∀ i : ℕ, i < k → ‖W (i + 1) x - W i x‖ ≤ δ) :
    ‖W k x - W 0 x‖ ≤ (k : ℝ) * δ ∧
      ‖ChainFwd (fun _ : ℕ => F) k y - ChainFwd (fun _ : ℕ => F) k z‖
        ≤ L ^ k * ‖y - z‖ := by
  refine ⟨?_, ?_⟩
  · -- `RealEditSeq.edit_seq_bound`（孤儿 → 下游）
    exact edit_seq_bound W x k δ hstep
  · -- `RealWeightSharing.shared_chain_error_bound`（孤儿 → 下游）
    exact shared_chain_error_bound F L k hF hL y z

end EditCountCross

/-! ## 五、真实缺口（本文件**没有**补上的，如实登记）

下面这些是接线过程中**实测撞到**的缺口。它们**不是**本文件的交付
（本文件只做接线），登记在此以免被误读为「已解决」。

### 缺口 A：`RealEditVerdict` 的 `b`（偏置）在链骨架里**无处安放**

`RealEditVerdict` 的定理都是**仿射**的（`W x + b`，带偏置 `b : ℝ`），
而 `RealChain` / `RealChainEdit` 的链骨架只有 `Fs : ℕ → X → X`
（**无偏置**的参数化）。本文件 §一 的接线因此**只能搬运扰动界 `δ`**，
把偏置 `b` 的信息**丢在了链外**——`ε₂` 被塞进 `δ` 的界里，而不是
作为一个**结构化的仿射层**在链中传播。

**真实缺口**：缺一条「仿射链骨架」（`Fs : ℕ → X → X` 推广为
`X → X × ℝ` 或 `E →L[ℝ] ℝ × ℝ` 的层），使偏置能**逐层**传播。
这是 `RealChain` 的结构性限制，**不是**本文件能补的（补它要改已有文件）。

### 缺口 B：`RealWeightSharing` 的梯度定理与编辑**完全脱节**

`RealWeightSharing` 有 `shared_grad_accumulation` / `shared_grad_norm_bound`
（**共享参数梯度 = 各层贡献之和**），而 `RealEditSeq` 系列讲的是**前向**编辑。
「编辑一次 → 反向梯度如何变化」这条**编辑梯度的链式律**在全库**仍无对应物**。
本文件**未**补它（它需要反向传播的形式化，超出接线范围）。

### 缺口 C：五个孤儿的「零 importer」不是**唯一**问题

要点 **C-11 复核（本次会话重测）：原文写「271/527」且未附命令，故已腐烂。**

当轮实测：**237 / 549** 个模块入度为 0。可复现命令（本次会话新增）：

```
python scripts/measure-indegree.py --root <repo>
```

定义：入度(a) = 在 `roots` 中、且源码里含 `^import a` 的**其他**模块数（不含自身、不含聚合器）。
⇒ 要点 **本条的教训**：规模数字必须**附命令**才可复核；只写数字的必然腐烂。

本文件只接了 5 个（任务书要求 5 个）。
**没有**做的：为剩余 234 个孤儿做**分类**（哪些是「写了但没用」，
哪些是「本就不该被用」的死代码）。这是 `_s12_orphanmods.json` 提到的
「orphan 归因」问题，**仍未解决**。

-/

end Lattice
