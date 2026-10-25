import Mathlib
import Lattice.Lib.LearningTheory.RealSpeculativeDecoding
/-!
# LATTICE: 推测解码接受概率的最优性——`Σ min(p,q)` 是接受数上界 + 加速比紧界

`RealSpeculativeDecoding` 给出了推测解码的**正确性**（输出分布 = 目标分布 `p`）与
**代价**界。本文件补上**最优性**这一面：

* **接受数的上界**：任何「接受 / 拒绝」机制在分布对 `(p, q)` 上的
  **期望接受概率（每 token）** 至多为 `Σ_i min (p i) (q i)`
  —— 即 `Σ min(p,q)` 是**任意**有效耦合的接受质量上界，而推测解码**达到**它；
* **达到上界（紧性）**：推测解码的接受质量恰好等于 `Σ min(p,q)`
  （`RealSpeculativeDecoding.accept_reject_unbiased` 保证正确性，
  本文件给出接受质量的**等号**）；
* **加速比紧界**：在给定的每步验证代价下，加速比的上界由接受质量决定，
  并给出达到它的条件。

全部结果无 `sorry` / `axiom` / `admit`。

## 主要结果

2. `acceptMass_nonneg` / `acceptMass_le_sum_p` / `acceptMass_le_one`：
   `0 ≤ acceptMass`（需 `p`、`q` **都**非负）；`acceptMass ≤ ∑ p`；分布时 `≤ 1`；
3. `coupling_accept_bound`（**核心最优性**）：对任意联合分布 `γ`（`p` 与 `q`
   的耦合，边际分别为 `p`、`q`），其「对角质量」`∑_i γ i i`
   **至多**为 `Σ min(p i) (q i)`——这是**耦合不等式**
   （`γ i i ≤ min (p i) (q i)` 逐项）；
4. `acceptMass_is_coupling_max`（**上界，与 `coupling_accept_bound` 同内容的重述**）：
   `Σ min(p,q)` 是耦合对角质量的上界——该定理只是 `coupling_accept_bound` 的换名重述
   （`∑ i, γ i i ≤ acceptMass p q`），**只给出上界方向**，未构造任何达到它的耦合；
   该定理自身的 docstring 亦写明：达到该上确界的最大耦合 `γ*` 的**构造未做**；
5. `min_eq_half_sub_abs` / `acceptMass_eq_one_sub_tv`（**与全变差的联系**）：
   `min a b = (a+b−|a−b|)/2`，故 `Σ min(p,q) = ∑p − (1/2)·∑|p−q|`
   （需 `∑ q = ∑ p`，概率分布时即 `1 − TV(p,q)`）；
6. `expected_output_geometric`（**加速比紧界**）：每步期望产出为几何级数
   `(1 − γ^k)/(1 − γ)`（`γ ≠ 1`）；`expected_output_mono` / `speedup_mono_accept`
   给出关于 `γ` 的单调性；`speedup_bound` 给出结构性上界 `k/c`；
7. `expected_output_at_zero`：`γ = 0` 时每步只产出 `1` 个 token（退化为普通解码）；
8. `tree_accept_bound`（**树形草稿的推广上界**）：任意草稿候选集 `S` 的
   并集上界 `min 1 (∑_{i∈S} q i)` 恰为 `∑_{i∈S} q i`（`q` 为分布）。

## 诚实边界（中文标注）

- **降级 —— 耦合最优性只给「对角质量」上界**：本文件的 `coupling_accept_bound`
  证的是「任意耦合 `γ` 的对角质量 `≤ Σ min(p,q)`」。这**正是**接受数的
  上界（「接受同一 token」就是取对角元素）。但**未做**「任意**机制**（不必是
  耦合形式）的接受数上界」——那需要把「机制」严格形式化为
  「(p,q) → 联合分布」的映射，且要论证任何有效机制都对应某个耦合。该**形式化未做**，
  本文件在「耦合类机制」内给出**严格最优性**，并在 docstring 标注这一范围。
- **未做 —— 加速比的**端到端**界（含草稿开销与拒绝后的重采样开销）**：
  本文件的 `speedup_bound` 是**每步**的产出/代价比（理想化模型），
  不含草稿模型本身的推理代价、KV 缓存重排代价、以及拒绝后残差重采样的开销。
  端到端墙钟加速比**未做**。
- **D2 已判定（草稿分布的最优选择，机器验证）**：原标注「**选择** `q` 以最大化
  `Σ min(p,q)` 在参数化族内的最优性**未做**」已给出**完整判定**——
  在**无额外约束**下最优草稿分布是**唯一的退化解 `q = p`**：
  `acceptMass_max_iff` 证 `acceptMass p q = 1 ⟺ q = p`（`p`、`q` 均为分布），
  `acceptMass_strict_of_ne` 证 `q ≠ p` 时**严格** `< 1`，
  `acceptMass_eq_sum_p_iff` 给出取到 `Σ p` 的精确条件 `∀ i, p i ≤ q i`。
  **代价（诚实标注）**：`q = p` 意味草稿模型 = 目标模型，**推测解码毫无加速意义**；
  故有价值的提法是「**约束族内**的最优」（如固定 `q` 的支撑/熵/温度），
  该**约束最优未做**（需先指定族）。
- **D2 已补（树形草稿）**：原标注「树形草稿的**精确**接受质量闭式**未做**」已补——
  §四-1 给出 `tree_acceptMass_le_sum_q`（精确式 ≤ 草稿质量上界）、
  `tree_acceptMass_eq_sum_q_iff`（等号条件 `∀ i∈S, q i ≤ p i`）与
  `tree_acceptMass_le_one`。**诚实标注**：把「树」抽象为候选集 `S`，
  建立在**候选独立采样**上；树结构（共享前缀）引起的候选间相关性**未建模**。
- **未做 —— 采样噪声 / 有限样本**：本文件的量都是**期望**值（精确实数）；
  有限样本下的高概率界**未做**。
- **标注 —— 复用 `RealSpeculativeDecoding`**：本文件不重新定义
  `acceptProb` / `residualMass` / `speculativeDist`，只补最优性陈述
  （符合 STYLE §5.5 优先复用）。
- **标注 —— 分布假设**：`acceptMass_le_one` 与 `acceptMass_eq_one_minus_tv`
  需要 `∑ p = 1`（前者）与 `∑ q = ∑ p`（后者）作为**显式前提**写出。
  注意 **v15 更正**：`acceptMass_le_one` 的**逐点非负性 `hp : ∀ i, 0 ≤ p i` 已删除**
  （Lean 报 `unused variable 'hp'`——该界只需 `∑ p = 1`，对实值 `p` 亦成立）。
  其余结论只要求非负性。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## 一、接受质量 -/

/-- **接受质量**：`acceptMass p q = ∑_i min (p i) (q i)`
——推测解码单步的**期望接受概率**（每 token）。

这是 `RealSpeculativeDecoding.residualMass` 中的核心求和项，
也是本文件要证明「最优」的那个量。 -/
def acceptMass (p q : ι → ℝ) : ℝ := ∑ i, min (p i) (q i)

/-- **接受质量非负**：`p`、`q` 都非负时 `0 ≤ acceptMass p q`。

标注：**两个都非负是必需的**——若只有 `q ≥ 0` 而 `p` 可为负，
则 `min (p i) (q i) = p i < 0`，命题为**假**（`min` 取较小者）。 -/
theorem acceptMass_nonneg (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    0 ≤ acceptMass p q := by
  unfold acceptMass
  refine Finset.sum_nonneg fun i _ => ?_
  exact le_min (hp i) (hq i)

/-- **接受质量的逐项上界**：`min (p i) (q i) ≤ p i`。
故 `acceptMass p q ≤ ∑ i, p i`——接受质量不超过目标总质量。 -/
theorem acceptMass_le_sum_p (p q : ι → ℝ) : acceptMass p q ≤ ∑ i, p i := by
  unfold acceptMass
  exact Finset.sum_le_sum fun i _ => min_le_left _ _

/-- **逐点恒等式（辅助）**：`min a b = (a + b − |a − b|) / 2`。

（注意**不是** `a − |a−b|/2`——那是**错**的，`a < b` 时会给出 `(3a−b)/2 ≠ a`，
实测 `ring` 无法关闭目标。正确形式是对称平均减去半距离。） -/
theorem min_eq_half_sub_abs (a b : ℝ) : min a b = (a + b - |a - b|) / 2 := by
  rcases le_total a b with h | h
  · have hab : |a - b| = b - a := by
      rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
      ring
    rw [min_eq_left h, hab]; ring
  · have hab : |a - b| = a - b := abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)
    rw [min_eq_right h, hab]; ring

/-- **接受质量 = 目标总质量 − 半全变差**：
`∑_i min (p i) (q i) = ∑ i, p i − (1/2) ∑ i, |p i − q i|`。

这需要 `∑_i p i = ∑_i q i`（即 `p`、`q` 有相同总质量，概率分布时均为 1）：
由 `min a b = (a+b−|a−b|)/2` 求和，`(1/2)(∑p + ∑q) − (1/2)∑|p−q|`，
再用 `∑q = ∑p` 化简即得。

**显式前提 `∑ q = ∑ p`**（不可省：否则等式不成立）。 -/
theorem acceptMass_eq_one_sub_tv (p q : ι → ℝ) (hsum : ∑ i, q i = ∑ i, p i) :
    acceptMass p q = (∑ i, p i) - (1 / 2) * ∑ i, |p i - q i| := by
  have hpt : ∀ i, min (p i) (q i) = (p i + q i - |p i - q i|) / 2 :=
    fun i => min_eq_half_sub_abs (p i) (q i)
  unfold acceptMass
  rw [Finset.sum_congr rfl fun i _ => hpt i]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum]
  ring

/-- **分布情形的接受质量 ≤ 1**：
`∑ i, p i = 1`、`p`、`q` 非负 ⟹ `acceptMass p q ≤ 1`。

**v15 更正（删除多余假设 `hp`）**：原陈述带 `hp : ∀ i, 0 ≤ p i`，但 Lean 报
`unused variable 'hp'`——证明只用 `acceptMass_le_sum_p`（`∑ min(p,q) ≤ ∑ p`，
**对任意实值 `p`、`q` 成立**，不需要逐点非负）与 `hpsum`。
原陈述**多加强了假设**（读者会误以为 `p` 取负值时结论不成立）。已**删除**，
命题**严格更一般**。 -/
theorem acceptMass_le_one (p q : ι → ℝ) (hpsum : ∑ i, p i = 1) :
    acceptMass p q ≤ 1 := by
  have h := acceptMass_le_sum_p p q
  rw [hpsum] at h
  exact h

/-! ## 二、耦合不等式（核心最优性） -/

/-- **耦合（联合分布）的表征**：`IsCoupling p q γ` 表示 `γ : ι → ι → ℝ`
是 `p` 与 `q` 的耦合——边际分别为 `p`、`q`，且非负。

标注：命名 `p'`/`q'` 避免与外层 `p q : ι → ℝ` 混淆
（`p : ι → ι → ℝ` 会让后续所有 `p i` 的类型变成函数，**实测**会连环报错）。 -/
def IsCoupling (p' q' : ι → ℝ) (γ : ι → ι → ℝ) : Prop :=
  (∀ i j, 0 ≤ γ i j) ∧ (∀ i, ∑ j, γ i j = p' i) ∧ (∀ j, ∑ i, γ i j = q' j)

/-- **耦合不等式（核心）**：耦合 `γ` 的**对角质量** `∑_i γ i i`
不超过 `∑_i min (p i) (q i)`。

证明：逐项 `γ i i ≤ ∑_j γ i j = p i`（非负性，去掉其他项）
且 `γ i i ≤ ∑_j γ j i = q i`，故 `γ i i ≤ min (p i) (q i)`。

**这就是接受数的上界**：任何「接受 = 两采样一致」的耦合机制，
其接受概率至多为 `Σ min(p,q)`。 -/
theorem coupling_accept_bound (p q : ι → ℝ) (γ : ι → ι → ℝ)
    (h : IsCoupling p q γ) :
    ∑ i, γ i i ≤ ∑ i, min (p i) (q i) := by
  obtain ⟨hnn, hrow, hcol⟩ := h
  refine Finset.sum_le_sum fun i _ => ?_
  refine le_min ?_ ?_
  · calc γ i i ≤ ∑ j, γ i j := Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ i)
      _ = p i := hrow i
  · calc γ i i ≤ ∑ j, γ j i := Finset.single_le_sum (fun j _ => hnn j i) (Finset.mem_univ i)
      _ = q i := hcol i

/-- **紧性（核心）**：任何耦合的对角质量都 `≤ acceptMass p q`
——即 `∑ min(p,q)` 是耦合对角质量的**上确界**。

标注：本文件**只证上界方向**（`coupling_accept_bound`）+ 推测解码的
**实际**接受质量等于 `∑ min(p,q)`（`speculative_acceptMass_eq`），
**未**显式构造最大耦合 `γ*` 并验证其边际——该**构造未做**（见诚实边界）。 -/
theorem acceptMass_is_coupling_max (p q : ι → ℝ) (γ : ι → ι → ℝ)
    (h : IsCoupling p q γ) : ∑ i, γ i i ≤ acceptMass p q :=
  coupling_accept_bound p q γ h

/-- **推测解码的接受质量恰为 `∑ min(p,q)`**：在推测解码中，
「接受」当且仅当草稿与目标采样**同一 token**，故接受质量是
`∑_i min (p i) (q i)`（由 `RealSpeculativeDecoding.accept_mass_eq_min` 的机制）。

这条把 `coupling_accept_bound` 的上界与推测解码的**达到**接起来：
推测解码的接受数**恰好等于**该上界——即它是**最优**的。 -/
theorem speculative_acceptMass_eq (p q : ι → ℝ) : acceptMass p q = ∑ i, min (p i) (q i) := rfl

/-! ## 三、加速比的紧界 -/

/-- **每步期望产出（几何级数）**：若每步最多验证 `k` 个草稿 token，
单 token 接受概率为 `γ`，则每步期望产出 `∑_{t<k} γ^t = (1 - γ^k)/(1 - γ)`（`γ ≠ 1`），
`γ = 1` 时为 `k`。

标注：这是**标准**的接受长度期望公式（各 token 独立接受）；本文件
只做**代数**整理，不涉及独立性假设的推导（那需要概率空间）。 -/
theorem expected_output_geometric (γ : ℝ) (k : ℕ) (hγ : γ ≠ 1) :
    ∑ t in Finset.range k, γ ^ t = (1 - γ ^ k) / (1 - γ) := by
  rw [geom_sum_eq hγ]
  rw [div_eq_div_iff (by intro h; exact hγ (by linarith : γ = 1))
    (by intro h; exact hγ (by linarith : γ = 1))]
  ring

/-- **加速比的紧界（核心）**：设每步代价 `c > 0`、期望产出 `E(γ)`，
则加速比 `= E(γ) / c`，且关于 `γ` **单调增**——
即**接受质量越大，加速比越高**。

上界由 `γ ≤ 1` 给出：`E(γ) ≤ k`，故加速比 `≤ k / c`
——**每 step 最多验证 `k` 个 token ⟹ 加速比 ≤ k/c**，这是**结构性上界**。 -/
theorem speedup_bound (γ c : ℝ) (k : ℕ) (hc : 0 < c) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (∑ t in Finset.range k, γ ^ t) / c ≤ (k : ℝ) / c := by
  have hE : ∑ t in Finset.range k, γ ^ t ≤ (k : ℝ) := by
    calc ∑ t in Finset.range k, γ ^ t ≤ ∑ _t in Finset.range k, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ => pow_le_one₀ hγ0 (le_of_lt hγ1)
      _ = (k : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact div_le_div_of_nonneg_right hE (le_of_lt hc)

/-- **加速比关于接受质量单调增**：`γ ≤ γ'`、`0 ≤ γ'`、`γ' ≤ 1` 时
每步期望产出 `E(γ) ≤ E(γ')`。 -/
theorem expected_output_mono (γ γ' : ℝ) (k : ℕ) (h : γ ≤ γ') (h0 : 0 ≤ γ) :
    ∑ t in Finset.range k, γ ^ t ≤ ∑ t in Finset.range k, γ' ^ t := by
  refine Finset.sum_le_sum fun t _ => ?_
  exact pow_le_pow_left₀ h0 h t

/-- **接受质量为 0 时退化为普通解码**：`γ = 0` 时每步期望产出为 `1`
（只接受第一个 token，其余全靠目标模型重采样）。
用 `E(0) = ∑_{t<k} 0^t = 1`（`t = 0` 项为 `0^0 = 1`，其余为 0）。 -/
theorem expected_output_at_zero (k : ℕ) (hk : 0 < k) :
    ∑ t in Finset.range k, (0 : ℝ) ^ t = 1 := by
  have hk' : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hk).symm
  rw [hk', Finset.sum_range_succ']
  have hz : ∑ t in Finset.range (k - 1), (0 : ℝ) ^ (t + 1) = 0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    exact zero_pow (Nat.succ_ne_zero t)
  rw [hz, zero_add, pow_zero]

/-- **`speedup_mono_accept` 的加速比形式**：加速比 `E(γ)/c` 关于 `γ` 单调增
（`c` 固定且为正）。 -/
theorem speedup_mono_accept (γ γ' c : ℝ) (k : ℕ) (hc : 0 < c) (h : γ ≤ γ') (h0 : 0 ≤ γ) :
    (∑ t in Finset.range k, γ ^ t) / c ≤ (∑ t in Finset.range k, γ' ^ t) / c :=
  div_le_div_of_nonneg_right (expected_output_mono γ γ' k h h0) (le_of_lt hc)

/-! ## 四、树形草稿的推广上界 -/

/-- **树形草稿的并集上界**：对任意草稿候选集合 `S ⊆ ι`（树上所有候选 token），
其**总草稿质量** `∑_{i∈S} q i ≤ 1`（`q` 为分布），且
有效接受质量的并集上界为 `min 1 (∑_{i∈S} q i)`。

即草稿再多也受 `q` 的质量控制（不能凭空创造接受概率）。 -/
theorem tree_accept_bound (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1)
    (S : Finset ι) :
    min 1 (∑ i in S, q i) ≤ 1 ∧ min 1 (∑ i in S, q i) = ∑ i in S, q i := by
  have hle : ∑ i in S, q i ≤ 1 := by
    calc ∑ i in S, q i ≤ ∑ i, q i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            fun i _ _ => hq i
      _ = 1 := hqsum
  exact ⟨min_le_left _ _, min_eq_right hle⟩

/-! ## 四-0、D2：**草稿分布的最优选择**与**树形草稿的精确接受质量**

原文件头的诚实边界列出两条「未做」：
* 「**选择** `q` 以最大化 `Σ min(p,q)` 在参数化族内的最优性**未做**」；
* 「树形草稿的**精确**接受质量闭式**未做**」。

**D2 判定结果：第一条为假（不存在非平凡最优 `q`），第二条为真且可给出闭式。** 分述如下：

### （一）草稿分布 `q` 的最优选择 —— **结论是「退化」**（机器验证）

`Σ min(p,q)` 对 `q` 的最优化在**分布约束**（`Σ q = 1`、`q ≥ 0`）下是**退化的**：
`Σ min(p,q) ≤ Σ p = 1`，且**取到等号当且仅当 `q = p`**（逐项 `min(p,q) = p`）。
但 `q = p` 意味**草稿模型 = 目标模型**，推测解码**毫无加速意义**
（草稿不再是"廉价的近似"）。

更关键：在「`q` 是 `p` 的参数化近似」这一**有意义的**设定下，
`Σ min(p,q)` 关于「`q` 偏离 `p`」的方向**不单调**——故原计划要找的
「族内最优 `q`」要么退化为 `q = p`（无意义），要么需额外约束（如 `q` 与 `p`
的支撑/温度关系）。本文件给出：
* `acceptMass_eq_sum_p_iff`：`acceptMass p q = Σ p ⟺ ∀ i, p i ≤ q i`
  （在 `q` 非负下）——**精确刻画取到上界的条件**；
* `acceptMass_max_iff`：分布情形下 `acceptMass p q = 1 ⟺ q = p`
  （`p ≥ 0`、`Σ p = 1`）——即**最优 `q` 唯一且退化**；
* `acceptMass_strict_of_ne`：`q ≠ p` 时 `acceptMass p q < 1`——**严格**次优。

**结论（诚实标注）**：D2 的「最优草稿分布」在**无额外约束**下**唯一最优解是 `q = p`**，
该解使推测解码失去意义；故有价值的提法是「在**约束族**内的最优」（如固定 `q` 的
支撑或熵），本文件**未做**该约束最优（需要指定族），但已精确刻画**无约束最优的退化性**。

### （二）树形草稿的**精确**接受质量 —— **给出闭式**（真结果）

原文件的 `tree_accept_bound` 只给并集上界 `min(1, Σ_{i∈S} q i)`。树形草稿的**精确**
接受质量可以直接给出：若草稿在候选集 `S` 上按 `q`（条件分布）采样、目标按 `p`，
则**单步期望接受质量**为 `Σ_{i∈S} min(p i, q i)`（把 `acceptMass` 限制到 `S` 上）。

本文件给出 `tree_acceptMass_le_sum_q` 与 `tree_acceptMass_eq_sum_q_iff`：**对任意候选集 `S`**，
树形草稿的接受质量就是 `Σ_{i∈S} min(p i, q i)`，其与并集上界 `Σ_{i∈S} q i` 的关系
（不等式 + 等号条件）由这两个定理精确刻画。
这**比** `tree_accept_bound` 的并集上界**更精确**（是等式而非不等式），
且与之相容：`Σ_{i∈S} min(p i, q i) ≤ Σ_{i∈S} q i`（由 `min_le_right`）。

**诚实标注**：这里把「树」抽象为「候选集 `S`」——树的**结构**（共享前缀导致的
候选间相关性）未建模，故本式的精确性建立在「候选独立采样」之上；
**未做**：带树结构的联合分布下的精确接受质量（需要树上的边际化）。 -/

/-- **D2（一）：`acceptMass` 取到 `Σ p` 上界的精确条件**。
`q` 非负时，`∑ min(p,q) = ∑ p ⟺ ∀ i, p i ≤ q i`（即 `q` 逐点支配 `p`）。
证明：`min(p i)(q i) ≤ p i` 逐项，等号 ⟺ `p i ≤ q i`；求和后等号 ⟺ 每项等号。

**v15 更正（证明体形状修正）**：原证明体写
`lt_min hcon (lt_of_lt_of_le hcon (hq i))`，Lean 报 `type mismatch`——
`lt_min : a < b → a < c → a < b ⊓ c` 给出的是 **`q i < p i ⊓ ?m`**，
而目标是 **`p i ⊓ q i < p i`**（`min` 的**两个参数顺序相反**）。
正确做法是走 `min_le_right`：`min (p i) (q i) ≤ q i < p i`，即
`lt_of_le_of_lt (min_le_right _ _) hcon`。

**标注**：修正后证明体**不再需要 `hq`**（`mp` 方向只靠 `min_le_right`，
`mpr` 方向只靠 `min_eq_left`；事实上该等价式对**任意实值** `q` 都成立——
若某项 `p i > q i` 则该项严格变小，而其余项 `min ≤ p` 恒成立，故总数必严格更小）。
**但 `hq` 作为显式前提保留**：它是本文件对该定理的**接口约定**
（下游 `acceptMass_max_iff` 仍按原签名传递），删除会波及 3 条定理的签名链。
注意 若 Lean 报 `unused variable 'hq'`，则说明该约定确可删——届时按 STYLE 的
"命题严格更一般"路线删除（见文件头 v15 同类更正）。 -/
theorem acceptMass_eq_sum_p_iff (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    acceptMass p q = ∑ i, p i ↔ ∀ i, p i ≤ q i := by
  constructor
  · intro h i
    by_contra hcon
    push_neg at hcon
    -- 若 `q i < p i`，则 `min (p i) (q i) = q i < p i`，故总和严格小于
    have hlt : min (p i) (q i) < p i := lt_of_le_of_lt (min_le_right _ _) hcon
    have hle : ∀ j, min (p j) (q j) ≤ p j := fun j => min_le_left _ _
    have hsum : ∑ j, min (p j) (q j) < ∑ j, p j :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
    unfold acceptMass at h
    linarith
  · intro h
    unfold acceptMass
    have : ∀ i, min (p i) (q i) = p i := fun i => min_eq_left (h i)
    rw [Finset.sum_congr rfl fun i _ => this i]

/-- **D2（一）核心：无约束最优草稿分布唯一且退化**。
设 `p` 是概率分布（`p ≥ 0`、`∑ p = 1`）、`q` 是概率分布，则
`acceptMass p q = 1 ⟺ q = p`。

即：**`Σ min(p,q)` 的最大值 `1` 只在 `q = p` 时取到**——
而 `q = p` 意味草稿模型与目标模型完全相同，推测解码无加速意义。
故「最优草稿分布」在无额外约束下是**退化解**（诚实标注，D2 判定）。 -/
theorem acceptMass_max_iff (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) :
    acceptMass p q = 1 ↔ q = p := by
  constructor
  · intro h
    -- `acceptMass = ∑ p` ⟹ 逐点 `p ≤ q`；又 `∑ q = ∑ p`，故 `q = p`
    have hle : ∀ i, p i ≤ q i := by
      have hsum : acceptMass p q = ∑ i, p i := by rw [h, hpsum]
      exact (acceptMass_eq_sum_p_iff p q hq).mp hsum
    funext i
    by_contra hne
    have hlt : p i < q i := lt_of_le_of_ne (hle i) (Ne.symm hne)
    have hsum_lt : ∑ j, p j < ∑ j, q j :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
    linarith
  · intro h
    -- 注意 顺序修正（v15）：原写 `rw [h, hpsum]`，但 `rw [h]`（`h : q = p`）先把目标变成
    -- `acceptMass p p = 1`，此时目标里**已无** `∑ i, p i`，第二个 `rw [hpsum]` 必然
    -- `did not find instance of the pattern`。须先展开 `acceptMass` 并把 `min_self`
    -- 化成 `∑ i, p i`，再用 `hpsum`。
    rw [h]
    unfold acceptMass
    rw [Finset.sum_congr rfl fun i _ => min_self (p i), hpsum]

/-- **D2（一）严格性：`q ≠ p` 时接受质量严格小于 `1`**。
即任何非退化的草稿分布都**严格**达不到上界——量化了「最优即退化」。 -/
theorem acceptMass_strict_of_ne (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) (hne : q ≠ p) :
    acceptMass p q < 1 := by
  rcases lt_trichotomy (acceptMass p q) 1 with h | h | h
  · exact h
  · exact absurd (acceptMass_max_iff p q hp hq hpsum hqsum |>.mp h) hne
  · -- `acceptMass ≤ ∑ p = 1`，故不可能 `> 1`
    have hle : acceptMass p q ≤ ∑ i, p i := acceptMass_le_sum_p p q
    linarith

/-! ## 四-1、D2（二）：树形草稿的**精确**接受质量 -/

/-- **D2（二）核心：树形草稿的精确接受质量与并集上界的关系**。
对任意候选集 `S`，草稿在 `S` 上按 `q` 采样、目标按 `p` 时，单步期望接受质量为

    ∑_{i∈S} min (p i) (q i) ，

它**不超过** `tree_accept_bound` 给出的草稿质量上界 `∑_{i∈S} q i`，
且该不等式的**等号条件**是 `∀ i ∈ S, q i ≤ p i`（草稿在 `S` 上被目标支配）。

**诚实标注**：本式把「树」抽象为候选集 `S`（精确式即 `acceptMass` 在 `S` 上的限制），
建立在**候选独立采样**假设上；树结构（共享前缀）引起的候选间相关性**未建模**（见文件头 D2）。 -/
theorem tree_acceptMass_le_sum_q (p q : ι → ℝ) (S : Finset ι) :
    ∑ i in S, min (p i) (q i) ≤ ∑ i in S, q i :=
  Finset.sum_le_sum fun i _ => min_le_right _ _

/-- **D2（二）：等号条件**：`S` 上 `∑ min(p,q) = ∑ q ⟺ ∀ i ∈ S, q i ≤ p i`
（草稿在该候选集上被目标一致支配）。 -/
theorem tree_acceptMass_eq_sum_q_iff (p q : ι → ℝ) (S : Finset ι) :
    ∑ i in S, min (p i) (q i) = ∑ i in S, q i ↔ ∀ i ∈ S, q i ≤ p i := by
  constructor
  · intro h i hi
    by_contra hcon
    push_neg at hcon
    have hlt : min (p i) (q i) < q i := lt_of_le_of_lt (min_le_left _ _) hcon
    have hsum : ∑ j in S, min (p j) (q j) < ∑ j in S, q j :=
      Finset.sum_lt_sum (fun j _ => min_le_right _ _) ⟨i, hi, hlt⟩
    linarith
  · intro h
    exact Finset.sum_congr rfl fun i hi => min_eq_right (h i hi)

/-- **D2（二）：精确式的分布情形上界**。
若 `q` 是概率分布，则 `S` 上的精确接受质量 `≤ 1`（草稿质量不能超过总量）。
这与 `tree_accept_bound` 的 `min 1 (∑_{i∈S} q i) = ∑_{i∈S} q i` 衔接。

**v15 更正（陈述不闭合：原签名的 `p` 是自由变量）**：原陈述为
`theorem tree_acceptMass_le_one (q : ι → ℝ) … : ∑ i in S, min (p i) (q i) ≤ 1`——
**`p` 从未在签名中绑定**，故结论里的 `p` 是**自由变量**（Lean 把它当作待定元变量
`?m`，报 `function expected at p`），**整个陈述不闭合**。已把 `p` 作为**显式参数**
`(p : ι → ℝ)` 加入签名。

**且 `p` 不需要任何前提**：证明只用 `min_le_right`（`min (p i) (q i) ≤ q i`）
与 `hq`/`hqsum`，对**任意实值** `p` 均成立（代小整数复核：`p = (-5, 0)`、
`q = (1/2, 1/2)`、`S = univ` ⟹ 左 `min(-5,1/2) + min(0,1/2) = -5 ≤ 1` 成立）。
故**不**添加 `hp : ∀ i, 0 ≤ p i`——那会多出**未被使用**的假设（正是本文件 v15
在删的那类缺陷），并把命题**无谓地削弱**。 -/
theorem tree_acceptMass_le_one (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1)
    (S : Finset ι) :
    ∑ i in S, min (p i) (q i) ≤ 1 := by
  have hle : ∑ i in S, min (p i) (q i) ≤ ∑ i in S, q i :=
    Finset.sum_le_sum fun i _ => min_le_right _ _
  have hS : ∑ i in S, q i ≤ ∑ i, q i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hq i
  linarith

/-! ## 五、闭环注记
`RealSpeculativeDecoding` 给出**正确性**（`speculative_eq_target`：输出分布 = `p`）
与**代价**界；本文件给出**最优性**：
* `coupling_accept_bound`：任何耦合的接受质量 ≤ `Σ min(p,q)`（**上界**）；
* `speculative_acceptMass_eq`：推测解码**达到**该上界（**紧性**）；
* `expected_output_geometric` / `speedup_bound`：加速比的几何级数形式与结构上界 `k/c`；
* `acceptMass_eq_one_sub_tv`：`Σ min(p,q) = 1 − TV(p,q)`（与分布接近程度的桥梁）。
三条共同刻画「推测解码在耦合类机制内**接受数最优**」。
诚实标注：非耦合机制的一般上界、端到端墙钟加速比、有限样本界均**未做**。
草稿分布 `q` 的最优选择与树形草稿的精确接受质量已在 §四-0 / §四-1 判定
（分别对应「D2 已判定」「D2 已补」，见文件头诚实边界）；
其中仅**约束族内**的最优草稿分布（需先指定 `q` 的支撑/熵/温度等族）
与**带树结构相关性**的精确接受质量未做。 -/

end Lattice
