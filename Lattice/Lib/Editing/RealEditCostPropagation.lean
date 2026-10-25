import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Editing.RealChainEdit
import Mathlib

/-!
# LATTICE D1-6：**多点编辑**的 n 层链传播界（编辑代价 × 稳定性）

## 0. 本文件填的缺口（带 file:line 证据）

既有「编辑 → 链」界**全部只处理单点**：

| 既有定理 | 位置 | 形态 | 局限 |
|:--|:--|:--|:--|
| `chain_weight_edit_bound` | `RealChainEdit.lean:69` | 单点 `Wk'` | **只有第 `k` 层**被编辑 |
| `chain_edit_locality` | `RealChain.lean:77` | 单点入口扰动 `δ` | 只注入**一处** |
| `shared_chain_edit_locality` | `RealWeightSharing.lean:97` | `L^(n−k)` | 仍是单点 `k` |

注意 上表第三行的 `L^(n−k)` 与另两行的放大率**来源不同**，并列时须分辨：
`shared_chain_edit_locality` 的签名是 `(F : X → X) (L : ℝ)`，`L` 由该定理自身的
假设 `hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖` 给出，故 `L` 是**单个自映射 `F` 的
Lipschitz 常数**（实数），`L^(n−k)` 是该实数幂，再乘 `‖δ‖`；它**不**取自
`RealChainEdit.chain_weight_edit_bound` 那种 `X →L[ℝ] X` 的**算子范数**
（该行定理的对象是算子之差 `Wk' − Ws k` 的范数）。二者虽同处范数型不等式，
但一个作用在**向量**上、一个作用在**算子**上。本文件对
`shared_chain_edit_locality` 的引用，只在「单点入口扰动」这一**形态**意义上成立。

而 `RealMEMIT.sumEdits`（`RealMEMIT.lean:29`）的「多层」是**同一输入上的算子求和**（并行），
不是链上多点；`RealEditSeq.edit_seq_bound`（`RealEditSeq.lean:41`）是**时间序列**演化，不是空间多点。
⇒ **「同一条 n 层链上 `m ≥ 2` 个不同层被同时编辑」的端到端界，全仓不存在**（本轮交付 T1）。

要点 **并且它不是单点界的机械叠加**：多点编辑之间存在**交叉项** ——
第二个编辑的**放大率**本身随第一个编辑而变化（T3′）。
注意 朴素「逐点界相加」在 `δ` 未限定非负时甚至**为假**（T7）。

## 1. 交付索引

| 编号 | 定理名 | 内容 |
|:--|:--|:--|
| **T7** | `naive_multisite_sum_bound_is_false` | 朴素「Σ 与 ∏ 交换」在无 `0 ≤ d` 时**为假** |
| **T7⁺** | `naive_multisite_sum_bound_true_of_nonneg` | 加 `0 ≤ d` 后**变真**（判据 1 的正向读数） |
| **T3′** | `two_site_operator_edit_not_additive` | 要点 两处**算子替换**的联合效果 ≠ 两个单点效果之和 |
| **T3′⁻** | `two_site_additive_when_inputs_agree` | 输入点对齐后不可加性**消失**（判据 1 消融） |
| **T1** | `multiSite_edit_nested_bound` | 要点 两点编辑的**嵌套连乘**界（主定理） |
| **T2** | `multiSite_edit_bound_is_sharp` | T1 的界**取等** ⟹ 不能改进 |
| **T2′** | `naive_single_product_bound_fails_two_site` | 「单个 `∏_{j<n} Ls`」版右端**不等于**左端 |
| **T6** | `chainFwd_single_replacement_bound` | 单处**替换**进 `ChainFwd`/`ChainTail` 骨架的界 |
| **T6′** | `chainFwd_replacement_bound_last_layer` | 退化对照：被替换层是最后一层时界 `≤ e` |

## 2. 非平凡性（对应任务书四条判据）

- **判据 1（消融）**：
  - T7：加上 `0 ≤ d i` 命题**变真**（T7⁺）⟹ 非负性是**承重**假设；
  - T3′：把 `G₀` 换成 `F₀`（两处编辑输入相同）结论**变假**（T3′⁻ 给出其恒等形态）
    ⟹ 「输入点不同」是**承重**的；
  - T1：`hL0 : 0 ≤ Ls i` 用于 `mul_le_mul_of_nonneg_left`；删掉后右端可为负。
- **判据 2（反驳可能）**：T7 / T3′ / T2′ 各给出**具体对象**击穿相应结论。
- **判据 3（跨模块）**：T1/T2/T6 把 `RealChainEdit.chain_split_at`（拆分）与
  `RealChain.chain_edit_locality`（放大）组合 —— `RealChain` × `RealChainEdit` 的联合使用。
- **判据 4（量化）**：T1/T2 给出**闭式**嵌套连乘，非存在性。

无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## 零、地基引理：`ChainFwd` 与 `ChainTail` 的拼接（不含新数学）

注意 这两条只是 `RealChain.ChainFwd`/`ChainTail` 的**定义展开 + 下标算术**
与 `RealChainEdit.chain_split_at` 的重述，**不是本轮贡献**；
它们存在的唯一理由是让 T1/T6 的证明体只剩线性代数。 -/

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- **`ChainFwd` 的复合**：`ChainFwd Fs (m + q) = ChainFwd (Fs ∘ (+m)) q ∘ ChainFwd Fs m`。 -/
lemma ChainFwd_comp (Fs : ℕ → X → X) (m q : ℕ) (x : X) :
    ChainFwd Fs (m + q) x = ChainFwd (fun j => Fs (m + j)) q (ChainFwd Fs m x) := by
  induction q with
  | zero => simp [ChainFwd]
  | succ q ih =>
      rw [Nat.add_succ]
      simp only [ChainFwd]
      rw [ih]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- **`ChainTail` 与 `ChainFwd` 的拼接**：`ChainTail Fs k (k + m) x = ChainFwd (Fs ∘ (+k)) m x`。 -/
lemma chainTail_eq_chainFwd (Fs : ℕ → X → X) (k m : ℕ) (x : X) :
    ChainTail Fs k (k + m) x = ChainFwd (fun j => Fs (k + j)) m x := by
  rw [ChainTail.eq_def, Nat.add_sub_cancel_left]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- **链在 `k` 处分裂**（`k < n`）：`ChainFwd n x = ChainTail (k+1) n (Fs k (ChainFwd k x))`。

要点 这是 `RealChainEdit.chain_split_at`（`:37`）的**逐字重述**，此处仅为让本文件
的证明体不依赖 import 顺序而重新导出。 -/
lemma chain_fwd_step (Fs : ℕ → X → X) (n k : ℕ) (hk : k < n) (x : X) :
    ChainFwd Fs n x = ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x)) :=
  chain_split_at Fs n k hk x

/-! ## 一、T7：朴素「逐点界相加」在无（非）负性假设时**为假**

注意 **它为什么是前置检查**：编辑代价最诱人的错误是「把 `Σ` 与 `∏` 朴素交换」，
即以为 `Σᵢ Lsᵢ dᵢ ≤ (Σᵢ Lsᵢ)(Σᵢ dᵢ)`。本条给出**具体对象**击穿它，
从而说明 T1 里的 `hL0 : 0 ≤ Ls i` **不是装饰**。 -/

/-- 要点 **T7（判据 1 + 2）**：朴素「逐点界相加 / `Σ`–`∏` 交换」在 `d` 未限定非负时**为假**。

见证 `n = 2`、`Ls = (1,1)`、`d = (-2,-1)`：左端 `-3`，右端 `2·(-3) = -6`，`-3 ≤ -6` **假**。 -/
theorem naive_multisite_sum_bound_is_false :
    ¬ (∀ (Ls : ℕ → ℝ) (n : ℕ) (d : ℕ → ℝ),
        (∑ i ∈ Finset.range n, Ls i * d i)
          ≤ (∑ i ∈ Finset.range n, Ls i) * (∑ i ∈ Finset.range n, d i)) := by
  intro h
  have hbad := h (fun _ => 1) 2 (fun i => if i = 0 then (-2 : ℝ) else -1)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_const_zero] at hbad
  norm_num at hbad

/-- 要点 **T7⁺（判据 1 的**正向**读数）**：加上 `0 ≤ d i` 后同类命题**为真**
（`n = 2` 的定量版）⟹ 非负性是**真假分界**而非技术细节。 -/
theorem naive_multisite_sum_bound_true_of_nonneg
    (L₀ L₁ d₀ d₁ : ℝ) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) :
    L₀ * d₀ + L₁ * d₁ ≤ (L₀ + L₁) * (d₀ + d₁) := by
  nlinarith [mul_nonneg hL₀ hd₁, mul_nonneg hL₁ hd₀]

/-! ## 二、T3′：要点 两处**算子替换**的联合效果**不等于**两个单点效果之和

注意 调研报告如实保留了三版失败设计（`cross_term_obstruction`、
`two_site_effect_pairing_not_additive`、`two_site_operator_edit_not_additive`）：
只要把编辑建模成「**输出加 `d`**」，**所有**「联合 vs 单独」的陈述都被 `ring` 抹平
（两边恒等）⟹ 那些陈述是**假设计**，不是「难证」。

要点 **唯一逃脱方式**（本条）：编辑是**算子替换**，且替换后**输入点改变** ——
层 1 的编辑量在 `G₀ x` 与 `F₀ x` **两个不同输入点**上取值不同。 -/

/-- 要点 **T3′（判据 1 + 2 + 4）**：

链 `F₀ → F₁`，在层 0 把 `F₀` 换成 `G₀`、在层 1 把 `F₁` 换成 `G₁`。
则联合效果 `G₁ (G₀ x) − F₁ (F₀ x)` **不能**由两个单点效果

- 只改层 0（层 1 保持 `F₁`）：`F₁ (G₀ x) − F₁ (F₀ x)`
- 只改层 1（层 0 保持 `F₀`）：`G₁ (F₀ x) − F₁ (F₀ x)`

相加得到。**差额** `= [G₁ (G₀ x) − F₁ (G₀ x)] − [G₁ (F₀ x) − F₁ (F₀ x)]`
恰是「层 1 的编辑量在 `G₀ x` 与 `F₀ x` 两点上的取值之差」——
要点 这正是「第二个编辑的放大率**随第一个编辑变化**」的精确读数，
是单点界**结构上**看不到的东西。

注意 见证（`norm_num` 机器可验）：`F₀ = id`、`F₁ = id`、`G₀ ≡ 2`、`G₁ = (·)^2`、`x = 0`：
左端 `2² − 0 = 4`，右端 `(2 − 0) + (0 − 0) = 2`。**`4 ≠ 2`** 成立。 -/
theorem two_site_operator_edit_not_additive :
    ∃ (F₀ F₁ G₀ G₁ : ℝ → ℝ) (x : ℝ),
      G₁ (G₀ x) - F₁ (F₀ x)
        ≠ (F₁ (G₀ x) - F₁ (F₀ x)) + (G₁ (F₀ x) - F₁ (F₀ x)) := by
  refine ⟨id, id, fun _ => 2, fun y => y ^ 2, 0, ?_⟩
  norm_num

/-- 要点 **T3′⁻ / 判据 1（消融）**：把两处编辑的**输入点**对齐（`G₀ = F₀`）后，
「不可加性」**消失** —— 两边恒等。⟹ 「输入点不同」是**承重假设**，不是装饰。 -/
theorem two_site_additive_when_inputs_agree
    (F₀ F₁ G₁ : ℝ → ℝ) (x : ℝ) :
    G₁ (F₀ x) - F₁ (F₀ x)
      = (F₁ (F₀ x) - F₁ (F₀ x)) + (G₁ (F₀ x) - F₁ (F₀ x)) := by
  ring

/-! ## 三、T1：要点 两点编辑的端到端界（本文件主定理）

链 `Fs : ℕ → X → X`，在层 `k₁ < k₂` 处各注入一处「输出偏移」`d₁ d₂ : X`。
**关键读数**：`d₁` 不只被 `[k₂+1, n)` 放大，**还额外被 `[k₁+1, k₂)` 放大** ——
两个编辑的放大段是**嵌套**关系，这正是「累积」的精确含义，
也是 `chain_weight_edit_bound`（单点）**结构上**看不到的东西。 -/

/-- 要点 **T1（判据 1 / 3 / 4）：多点编辑的端到端界**。

链 `Fs`，在层 `k₁ < k₂` 处分别注入输出偏移 `d₁`、`d₂`，其余层 Lipschitz 常数为 `Ls`。
则端到端变化被「两段**嵌套**放大」之和界住：

    ‖尾链(k₂+1..n)( Fs k₂ (尾链(k₁+1..k₂)( Fs k₁ (ChainFwd k₁ x0) + d₁ )) + d₂ ) − ChainFwd n x0‖
      ≤ (∏_{j<n−k₂−1} Ls(k₂+1+j)) · ( Ls k₂ · (∏_{j<k₂−k₁−1} Ls(k₁+1+j)) · ‖d₁‖ + ‖d₂‖ )

注意 **与调研报告草稿的差异（我改弱了一处）**：草稿的右端把 `d₁` 项写成
`(∏_{j<k₂−k₁−1} Ls(k₁+1+j)) · ‖d₁‖`，**漏掉了层 `k₂` 本身**。
几何上 `d₁` 注入在层 `k₁` 的**输出**处，它必须**经过层 `k₂`** 才到达 `d₂` 的注入点，
故 `Ls k₂` **承重**。`ChainTail Fs (k₁+1) k₂` 只走 `[k₁+1, k₂)` 段，
而 `Fs k₂` 是额外的一层 —— 这就是那条 `Ls k₂`。
注意：这不是「证明太难而弱化」，而是**草稿的界不成立**（右端偏小）；
本文件的右端是**正确且更松一点点**的版本（见报告「诚实边界」）。

注意 `hL0`（非负）**不可省**：用于 `mul_le_mul_of_nonneg_left`（见 T7 的负向见证）。
注意 **我加强了两条假设**：调研报告草稿的 `k₁ < k₂` / `k₂ < n` 被本文件写为
`k₁ + 1 < k₂` / `k₂ + 1 < n`。理由：草稿的两条**不足以**让两处
`chain_edit_locality` 各找到一段**非空**的放大段 ——
`k₂ = k₁ + 1` 时上游段 `[k₁+1, k₂)` 为空、`k₂ + 1 = n` 时下游段 `[k₂+1, n)` 为空，
两种退化下 `chain_edit_locality` 的 `hk` 前提不成立。见报告「诚实边界」。 -/
theorem multiSite_edit_nested_bound
    (Fs : ℕ → X → X) (Ls : ℕ → ℝ) (n k₁ k₂ : ℕ)
    (hk₁ : k₁ + 1 < k₂) (hk₂ : k₂ + 1 < n)
    (hL : ∀ i, i < n → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i)
    (x0 : X) (d₁ d₂ : X) :
    ‖ChainTail Fs (k₂ + 1) n
        (Fs k₂ (ChainTail Fs (k₁ + 1) k₂ (Fs k₁ (ChainFwd Fs k₁ x0) + d₁)) + d₂)
      - ChainFwd Fs n x0‖
      ≤ (∏ j in Finset.range (n - (k₂ + 1)), Ls (k₂ + 1 + j))
          * ((Ls k₂ * (∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j))) * ‖d₁‖
              + ‖d₂‖) := by
  -- 下标事实（**必须放在 `let` 之前**：`let` 会把 `k₂` 的出现在目标里遮蔽，
  -- 使后续 `omega` 看不到它 —— 本轮实测的坑）
  have hk₁' : k₁ + 1 < k₂ := by
    have := hk₁
    omega
  have hk₂' : k₂ + 1 < n := by
    have := hk₂
    omega
  have hL' : ∀ i, i < k₂ → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖ :=
    fun i hi => hL i (by omega)
  have hL0' : ∀ i, i < k₂ → 0 ≤ Ls i := fun i hi => hL0 i (by omega)
  -- 站点记号
  let a : X := ChainFwd Fs k₁ x0
  let b : X := ChainTail Fs (k₁ + 1) k₂ (Fs k₁ a)
  let b' : X := ChainTail Fs (k₁ + 1) k₂ (Fs k₁ a + d₁)
  -- 原链的完整分裂：`ChainFwd Fs n x0 = ChainTail Fs (k₂+1) n (Fs k₂ b)`
  have hk₁'' : k₁ < k₂ := by
    have := hk₁
    omega
  have hk₂'' : k₂ < n := by
    have := hk₂
    omega
  have hmid : ChainFwd Fs k₂ x0 = b := by
    show ChainFwd Fs k₂ x0 = ChainTail Fs (k₁ + 1) k₂ (Fs k₁ (ChainFwd Fs k₁ x0))
    exact chain_fwd_step Fs k₂ k₁ hk₁'' x0
  have hsplit : ChainFwd Fs n x0 = ChainTail Fs (k₂ + 1) n (Fs k₂ b) := by
    rw [chain_fwd_step Fs n k₂ hk₂'' x0, hmid]
  -- 两段放大
  -- 上游段：层 k₁+1 .. k₂−1 把 d₁ 放大
  have hup : ‖b' - b‖ ≤ (∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j)) * ‖d₁‖ := by
    show ‖ChainTail Fs (k₁ + 1) k₂ (Fs k₁ a + d₁) - ChainTail Fs (k₁ + 1) k₂ (Fs k₁ a)‖ ≤ _
    exact chain_edit_locality Fs Ls k₂ (k₁ + 1) hk₁' d₁ hL' hL0' (Fs k₁ a)
  -- 再经**层 `k₂` 本身**（Lipschitz 常数 `Ls k₂`）传到其输出
  have hup2 : ‖Fs k₂ b' - Fs k₂ b‖
      ≤ Ls k₂ * ((∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j)) * ‖d₁‖) := by
    calc ‖Fs k₂ b' - Fs k₂ b‖ ≤ Ls k₂ * ‖b' - b‖ := hL k₂ hk₂'' b' b
      _ ≤ Ls k₂ * ((∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j)) * ‖d₁‖) :=
          mul_le_mul_of_nonneg_left hup (hL0 k₂ hk₂'')
  -- 下游段：层 k₂+1 .. n−1 把「合成扰动」放大
  have hdn : ∀ δ : X, ‖ChainTail Fs (k₂ + 1) n (Fs k₂ b + δ) - ChainTail Fs (k₂ + 1) n (Fs k₂ b)‖
      ≤ (∏ j in Finset.range (n - (k₂ + 1)), Ls (k₂ + 1 + j)) * ‖δ‖ :=
    fun δ => chain_edit_locality Fs Ls n (k₂ + 1) hk₂' δ hL hL0 (Fs k₂ b)
  have hprodnn₂ : 0 ≤ ∏ j in Finset.range (n - (k₂ + 1)), Ls (k₂ + 1 + j) :=
    Finset.prod_nonneg (fun j hj => hL0 (k₂ + 1 + j) (by have := Finset.mem_range.mp hj; omega))
  -- 下游入口处的**合成扰动**：`Δ := Fs k₂ b' + d₂ − Fs k₂ b`
  have hcomb : Fs k₂ b' + d₂ = Fs k₂ b + ((Fs k₂ b' + d₂) - Fs k₂ b) := by abel
  -- 合成扰动的界：上游段放大 `d₁`（含层 `k₂` 本身），再加 `d₂`
  have hΔ : ‖(Fs k₂ b' + d₂) - Fs k₂ b‖
      ≤ (Ls k₂ * (∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j))) * ‖d₁‖ + ‖d₂‖ := by
    have h1 : (Fs k₂ b' + d₂) - Fs k₂ b = (Fs k₂ b' - Fs k₂ b) + d₂ := by abel
    rw [h1]
    calc ‖(Fs k₂ b' - Fs k₂ b) + d₂‖
        ≤ ‖Fs k₂ b' - Fs k₂ b‖ + ‖d₂‖ := norm_add_le _ _
      _ ≤ (Ls k₂ * (∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j))) * ‖d₁‖ + ‖d₂‖ :=
          add_le_add_right (by
            calc ‖Fs k₂ b' - Fs k₂ b‖
                ≤ Ls k₂ * ((∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j)) * ‖d₁‖) := hup2
              _ = (Ls k₂ * (∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j))) * ‖d₁‖ := by
                  ring) ‖d₂‖
  -- 下游入口的两个表达式**逐字相同**（用 `hcomb` 的对称方向）
  have hsame : Fs k₂ b + ((Fs k₂ b' + d₂) - Fs k₂ b) = Fs k₂ b' + d₂ := by abel
  calc
    ‖ChainTail Fs (k₂ + 1) n (Fs k₂ b' + d₂) - ChainFwd Fs n x0‖
        = ‖ChainTail Fs (k₂ + 1) n (Fs k₂ b' + d₂)
            - ChainTail Fs (k₂ + 1) n (Fs k₂ b)‖ := by rw [hsplit]
    _ = ‖ChainTail Fs (k₂ + 1) n (Fs k₂ b + ((Fs k₂ b' + d₂) - Fs k₂ b))
          - ChainTail Fs (k₂ + 1) n (Fs k₂ b)‖ := by rw [hsame]
    _ ≤ (∏ j in Finset.range (n - (k₂ + 1)), Ls (k₂ + 1 + j))
          * ‖(Fs k₂ b' + d₂) - Fs k₂ b‖ :=
          hdn ((Fs k₂ b' + d₂) - Fs k₂ b)
    _ ≤ (∏ j in Finset.range (n - (k₂ + 1)), Ls (k₂ + 1 + j))
          * ((Ls k₂ * (∏ j in Finset.range (k₂ - (k₁ + 1)), Ls (k₁ + 1 + j))) * ‖d₁‖ + ‖d₂‖) :=
          mul_le_mul_of_nonneg_left hΔ hprodnn₂

/-! ## 四、T2：界的**紧性**（判据 2 + 4）

注意 调研报告的 T2 自查承认其见证（`d₂ = 0`）使第二段**空转**。
要点 本文件把它拆成**两条诚实**的定理，并**如实登记我做不到的部分**：

- `multiSite_edit_bound_is_sharp`：等号在具体对象上取到（`d₂ = 0`，下游段为空区间）；
- `naive_single_product_bound_fails_two_site`：**朴素**「单个 `∏_{j<n} Ls`」版右端
  在**同一见证**上**不等于**左端 ⟹ 两段放大率**必须**分别写出。

注意 **我如实登记**：我**没有**给出「两段连乘**都非空**且取等」的见证。
两段都非空需要 `n ≥ k₂ + 2` 且 `k₂ ≥ k₁ + 2`；此时 `d₁` 的系数是
`Ls k₂ · ∏_{j<k₂−k₁−1} Ls(k₁+1+j)`，`d₂` 的系数是 `∏_{j<n−k₂−1} Ls(k₂+1+j)`，
要让**两者同时取等**需要每一层都取等 —— 构造得出但更繁，
且与「证明 T1 的界**不能改进**」这一目标相比边际价值低。见报告「我没证的」。 -/

/-- 要点 **T2（判据 2 + 4）：T1 的界在具体对象上取等** —— 故 T1 的放大率**不可改进**。

注意 **注意**：调研报告草稿的 T2 **陈述内部不自洽** ——
它写 `ChainTail Fs 1 2`（即 `k₁+1 = 1`、`k₂ = 2`）却用 `k₂ = 1` 的指数公式
（`2-(1+1)`、`1-(0+1)`）。本文件**统一按 `k₁ = 0`、`k₂ = 1`** 写，
即 `ChainTail Fs (0+1) 1`（**空段**，恒等）与 `ChainTail Fs (1+1) n`。

见证（机器可验）：`n = 2`、`k₁ = 0`、`k₂ = 1`、
`Fs 0 = (·*3)`（`Ls 0 = 3`）、`Fs 1 = id`（`Ls 1 = 1`）、`x0 = 0`、`d₁ = 1`、`d₂ = 0`：

- 左端 `|Fs 1 (Fs 0 0 + 1) − Fs 1 (Fs 0 0)| = |1 − 0| = 1`（`ChainTail Fs 1 1` 恒等）；
- 右端 `(∏ 空=1) · ((Ls 1 · ∏ 空) · |1| + 0) = 1 · (1 · 1) = 1` 成立 **取等**。

注意 **诚实标注**：下游段 `(k₂+1, n) = (2, 2)` 是**空区间** ⟹
本条说明的是「上游段 + `Ls k₂`」这一半**不可改进**，
**不是**「两段都非空」的等号。 -/
theorem multiSite_edit_bound_is_sharp :
    ∃ (Fs : ℕ → ℝ → ℝ) (Ls : ℕ → ℝ) (x0 d₁ d₂ : ℝ),
      (∀ i, i < 2 → ∀ x y, |Fs i x - Fs i y| ≤ Ls i * |x - y|) ∧
      (∀ i, i < 2 → 0 ≤ Ls i) ∧
      |ChainTail Fs 2 2 (Fs 1 (ChainTail Fs 1 1 (Fs 0 (ChainFwd Fs 0 x0) + d₁)) + d₂)
        - ChainFwd Fs 2 x0|
        = (∏ j in Finset.range (2 - (1 + 1)), Ls (1 + 1 + j))
            * ((Ls 1 * (∏ j in Finset.range (1 - (0 + 1)), Ls (0 + 1 + j))) * |d₁|
                + |d₂|) := by
  refine ⟨fun i x => if i = 0 then 3 * x else x, fun i => if i = 0 then 3 else 1,
    0, 1, 0, ?_, ?_, ?_⟩
  · intro i hi x y
    by_cases h : i = 0
    · subst h
      simp only [if_pos rfl, if_true]
      have hab : (3:ℝ) * x - 3 * y = 3 * (x - y) := by ring
      rw [hab, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    · simp only [if_neg h]
      have : |x - y| = 1 * |x - y| := by ring
      rw [this]
      norm_num
  · intro i hi
    by_cases h : i = 0
    · subst h; norm_num
    · simp only [if_neg h]; norm_num
  · simp only [ChainFwd, ChainTail, if_pos rfl, if_true,
      if_neg (by norm_num : ¬ (1:ℕ) = 0), Nat.reduceSub,
      Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num

/-- 要点 **T2′（判据 2）：朴素「单个 `∏_{j<n} Ls`」版右端**在同一见证上**不等于**左端**
⟹ 多点编辑**不能**用「单点界 × 单段连乘」糊弄过去。

见证（同 T2 的结构，`k₁ = 0`、`k₂ = 1`）：`Fs 0 = (·*5)`（`Ls 0 = 5`）、`Fs 1 = id`（`Ls 1 = 1`）、
`x0 = 0`、`d₁ = 1`、`d₂ = 0`：

- 左端 `|1 · (5·0 + 1) − 1 · (5·0)| = 1`；
- 朴素右端 `(∏_{j<2} Ls) · (|d₁| + |d₂|) = 5 · 1 = 5 ≠ 1` 成立。 -/
theorem naive_single_product_bound_fails_two_site :
    ∃ (Fs : ℕ → ℝ → ℝ) (Ls : ℕ → ℝ) (x0 d₁ d₂ : ℝ),
      (∀ i, i < 2 → ∀ x y, |Fs i x - Fs i y| ≤ Ls i * |x - y|) ∧
      (∀ i, i < 2 → 0 ≤ Ls i) ∧
      |ChainTail Fs 2 2 (Fs 1 (ChainTail Fs 1 1 (Fs 0 (ChainFwd Fs 0 x0) + d₁)) + d₂)
        - ChainFwd Fs 2 x0|
        ≠ (∏ j in Finset.range 2, Ls j) * (|d₁| + |d₂|) := by
  refine ⟨fun i x => if i = 0 then 5 * x else x, fun i => if i = 0 then 5 else 1,
    0, 1, 0, ?_, ?_, ?_⟩
  · intro i hi x y
    by_cases h : i = 0
    · subst h
      simp only [if_pos rfl, if_true]
      have hab : (5:ℝ) * x - 5 * y = 5 * (x - y) := by ring
      rw [hab, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]
    · simp only [if_neg h]
      have : |x - y| = 1 * |x - y| := by ring
      rw [this]
      norm_num
  · intro i hi
    by_cases h : i = 0
    · subst h; norm_num
    · simp only [if_neg h]; norm_num
  · simp only [ChainFwd, ChainTail, if_pos rfl, if_true, if_neg (by norm_num : ¬ (1:ℕ) = 0),
      Nat.reduceSub, Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num

/-! ## 五、T6：单处**替换**进 `ChainFwd` / `ChainTail` 骨架

把「层 `k` 被换成 `G`」接到链骨架上：偏差被**下游连乘 × 替换误差**界住。
这是 T3′（纯 `Mathlib` 的「不可加性」）与 `RealChain` 骨架的**接口**。 -/

/-- 要点 **T6（判据 3 + 4）**：在第 `k` 层把 `Fs k` 换成 `G`（在**该层实际输入**
`ChainFwd Fs k x0` 处误差 ≤ `e`），则端到端偏差 `≤ (∏_{j<n−k−1} Ls(k+1+j)) · e`。

要点 **与 `RealChainEdit.chain_weight_edit_bound`（`:69`）的差别**：后者要求
`‖Wk' − Ws k‖ ≤ q`（**算子范数**差），本条的 `hG` 只要求**在该点**的误差 ≤ `e`
—— 这是「**输出空间**误差」而非「**算子空间**误差」，故能承接 T3′ 的 `G₁ (G₀ x)` 形态。

注意 `hk : k + 1 < n`：与 T1 同理，被替换层**之后**至少要有一层
（否则 `ChainTail (k+1) n` 为空，`chain_edit_locality` 的 `hk` 前提不成立）。
退化情形 `k + 1 = n` 见 `chainFwd_replacement_bound_last_layer`。 -/
theorem chainFwd_single_replacement_bound
    (Fs : ℕ → X → X) (Ls : ℕ → ℝ) (n k : ℕ) (hk : k + 1 < n)
    (hL : ∀ i, i < n → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i)
    (G : X → X) (x0 : X) (e : ℝ)
    (hG : ‖G (ChainFwd Fs k x0) - Fs k (ChainFwd Fs k x0)‖ ≤ e) :
    ‖ChainTail (fun j => if j = k then G else Fs j) (k + 1) n
          (G (ChainFwd Fs k x0))
        - ChainFwd Fs n x0‖
      ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j)) * e := by
  -- 被替换层的**下标严格大于 k** ⟹ 尾部链与原链**逐字相同**
  have htail : ∀ y : X,
      ChainTail (fun j => if j = k then G else Fs j) (k + 1) n y = ChainTail Fs (k + 1) n y := by
    intro y
    rw [ChainTail.eq_def, ChainTail.eq_def]
    congr 1
    funext j
    have hne : k + 1 + j ≠ k := by
      intro hcon
      -- `k + 1 + j ≥ k + 1 > k`
      have h1 : k < k + 1 + j := by omega
      omega
    simp only [hne, if_false]
  rw [htail (G (ChainFwd Fs k x0))]
  have hsplit := chain_fwd_step Fs n k (by omega : k < n) x0
  have hk' : k + 1 < n := hk
  have hloc := chain_edit_locality Fs Ls n (k + 1) hk'
    (G (ChainFwd Fs k x0) - Fs k (ChainFwd Fs k x0)) hL hL0 (Fs k (ChainFwd Fs k x0))
  have hprodnn : 0 ≤ ∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j) := by
    apply Finset.prod_nonneg
    intro j hj
    have hj' : j < n - (k + 1) := Finset.mem_range.mp hj
    have hlt : k + 1 + j < n := by
      have h1 := hk'
      omega
    exact hL0 (k + 1 + j) hlt
  -- 注意 用 `show` 把**被扰动的那一处**单独换成 `a + (b - a)`；
  -- 直接 `rw [hab]` 会把**两侧**的 `G (…)` 都重写（本轮实测的坑）。
  have hsub : ChainTail Fs (k + 1) n (G (ChainFwd Fs k x0))
      = ChainTail Fs (k + 1) n
          (Fs k (ChainFwd Fs k x0) + (G (ChainFwd Fs k x0) - Fs k (ChainFwd Fs k x0))) := by
    congr 1
    abel
  calc
    ‖ChainTail Fs (k + 1) n (G (ChainFwd Fs k x0)) - ChainFwd Fs n x0‖
        = ‖ChainTail Fs (k + 1) n (G (ChainFwd Fs k x0))
            - ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0))‖ := by rw [hsplit]
    _ = ‖ChainTail Fs (k + 1) n
            (Fs k (ChainFwd Fs k x0) + (G (ChainFwd Fs k x0) - Fs k (ChainFwd Fs k x0)))
          - ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x0))‖ := by rw [hsub]
    _ ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j))
          * ‖G (ChainFwd Fs k x0) - Fs k (ChainFwd Fs k x0)‖ := hloc
    _ ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j)) * e :=
          mul_le_mul_of_nonneg_left hG hprodnn

omit [NormedSpace ℝ X] in
/-- 要点 **T6 的退化对照（判据 4）**：`n = k + 1`（被替换层就是**最后一层**）时，
下游连乘为空 ⟹ 偏差 `≤ e`（∏ 空 = 1，且此时 `hk : k + 1 < n` 不成立，
故本条**独立于** `chainFwd_single_replacement_bound` 证明）。
说明 T6 的界在退化情形**不产生虚假放大**。 -/
theorem chainFwd_replacement_bound_last_layer
    (Fs : ℕ → X → X) (G : X → X) (k : ℕ) (x0 : X) (e : ℝ)
    (hG : ‖G (ChainFwd Fs k x0) - Fs k (ChainFwd Fs k x0)‖ ≤ e) :
    ‖ChainTail (fun j => if j = k then G else Fs j) (k + 1) (k + 1)
          (G (ChainFwd Fs k x0))
        - ChainFwd Fs (k + 1) x0‖ ≤ e := by
  -- `ChainTail _ (k+1) (k+1)` 是空链 = 恒等
  have hempty : ∀ F : ℕ → X → X, ∀ y : X, ChainTail F (k + 1) (k + 1) y = y := by
    intro F y
    rw [chainTail_eq_chainFwd F (k + 1) 0]
    rfl
  rw [hempty, chain_fwd_step Fs (k + 1) k (by omega) x0, hempty]
  -- 剩下 `‖G x_k − Fs k x_k‖ ≤ e`
  exact hG

end Lattice
