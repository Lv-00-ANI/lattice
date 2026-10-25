import Mathlib
import Lattice.Lib.LearningTheory.RealSamplingBoost
import Lattice.Lib.Concentration.RealUnionBound
/-!
# LATTICE: 分布外检测（OOD）—— 分数、AUROC 与可证的分离条件

方向（W1 统计学习）：分布外检测的**可证部分**。本文件**刻意不做**
「检测器一定有效」这类**假命题**，只形式化真正可证的组合与序结构，
并按项目纪律对**为假的诱人命题给出机器验证反例**。

## 内容与路线（有限计数、无测度论）

- 分数函数以**参数** `s : α → ℝ` 出现（分数越高越像 OOD），不单独定义。
- `tprAt` / `fprAt`：阈值 `t` 处的真正率 / 假正率（对 ID / OOD 两个有限集
  分别计数并除以各自基数，即条件概率的计数版）。
- `auroc`：Mann–Whitney 形式 `P(s_OOD > s_ID) + ½ P(并列)`（**组合定义**，
  即有序对的计数）。
- `sweepPoints`：扫掠所需的分位点集（供未来定义扫掠积分用）。

## 本文件实际存在的声明（全部内核可证）

定义：`tprAt`、`fprAt`（阈值处的真正率/假正率）、
`auroc`（**有序对计数 / Mann–Whitney 形式**，并列算 ½）、
`sweepPoints`（扫掠分位点集）。

1. `tpr_mono` / `fpr_mono` / `roc_trajectory_mono`（**阈值单调性**，核心）：
   `t ≤ t'` ⟹ `tpr t' ≤ tpr t` 且 `fpr t' ≤ fpr t`。
   —— ROC 曲线良定义的基础，**不需要任何分布假设**。
2. `auroc_nonneg` / `auroc_le_one`：`0 ≤ auroc ≤ 1`（真界）。
3. `auroc_symmetric_tie`：全并列时 `auroc = 1/2`
   （需两组**均非空**；空集时由 `x/0 = 0` 得 `auroc = 0 ≠ 1/2`，故非空性是必要假设）。
4. `perfect_separation_auroc_one`：OOD 分数**逐点严格大于** ID 分数
   ⟹ `auroc = 1`（分离的**充分条件**，条件是显式假设）。
5. `separation_from_threshold`：**阈值分离**（存在 `t` 使 OOD 全 `≥ t`
   而 ID 全 `< t`）⟹ 该阈值处 `tpr = 1`、`fpr = 0`。
6. `threshold_separation_iff` / `exists_separating_threshold`：
   「存在完美分离阈值」⟺ 「所有 ID 分数 < 所有 OOD 分数」（**精确刻画**）。
7. `auroc_ge_half_false`（**反例，机器验证**）：⚠️ 「`auroc ≥ 1/2` 恒成立」
   **为假**——在 `Fin 2`、`ood = {0}`（分数 `0`）、`idset = {1}`（分数 `1`）
   的具体实例上 `auroc = 0 < 1/2`。
8. `auroc_zero_of_reverse_separation`：**结构性强化**——只要 OOD 分数
   逐点小于 ID 分数，则 `auroc = 0`（无条件，无需非空假设）。

## 诚实边界（**不**证 / **不**声称的）

- ⚠️ **未做的核心恒等式**：`auroc` 的**扫掠定义**（按阈值积分
  `TPR d(FPR)`）与有序对计数定义的**相等性未形式化**
  （`sweepPoints` 只给出分位点集，扫掠积分本身未定义）。
  该恒等式已由**外部数值实验**核对（300/300 组一致），但**不是本文件的定理**。
- ⚠️ **不声称「检测器一定有效」**：OOD 检测的「有效性」需要关于
  ID/OOD 分布的假设（如分离性、浓度），这些**不是**分数函数的组合性质。
  本文件只证**条件于分离假设**的结论。
- ⚠️ **反例登记**：`auroc ≥ 1/2` **为假**（见 `auroc_ge_half_false`）——
  这一条是**真正的机器验证反例**（有具体实例与内核证明）。
  文献中该陈述只在「分数与标签正相关」的假设下成立。
- **不证** AUROC 的**统计估计**（如 DeLong 区间、样本 AUROC 的集中界）——
  那需要额外的集中不等式与渐近理论，标注为后续工作。
  （可用 `RealHoeffding` 做**非渐近**版本，登记为未做。）
- **不证**「AUROC 是检测质量的最优度量」——不存在这样的定理。
- 未做：多类 OOD、评分聚合（ensemble）的可证性质。
- 未做：AUROC 对**严格单调**变换的不变性（需序同构形式化）。

无 sorry/axiom/admit；所有定理真实可证。

## ⚠ G2 修复登记（本波次）

- **级联根因（一条 error 解释多条症状）**：原 `variable {α : Type*} [Fintype α]`
  **缺 `[DecidableEq α]`**，而 `sweepPoints` 的 `ood ∪ idset`（`Finset.union`）
  与多处 `Finset.filter` 需要它 ⟹ 报 `failed to synthesize Union (Finset α)`
  并**级联污染后续**。已补上实例。
- **记法根因（12 条 `did not find instance of the pattern`）**：`.product` 点记法
  与 mathlib 的 `Finset.mem_product` / `Finset.card_product`（**陈述都用 `×ˢ`**）
  不匹配 ⟹ 已统一为 `×ˢ`（二者**定义上相同**，`Finset.product` 即 `SProd` 实例）。
- **`hG ▸ hpG` 的 motive 推断失败**：`set … with hG` 后对 `hpG : p ∈ G` 用 `▸`
  会在 `filter` 的谓词上取错 motive ⟹ 改用 `rw [hG] at hpG`。
- 本文件**未发现**假命题：`auroc_ge_half_false` 的反例（`auroc ≥ 1/2` 为假）
  经本轮复核**成立且证明通过**（该反例原本就是正确的机器验证反例）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

-- ⚠ **G2 修复（级联根因）**：原文只有 `[Fintype α]`，但本文件使用
-- `Finset.union`（`sweepPoints` 的 `ood ∪ idset`）、`Finset.image` 与 `Finset.filter`
-- 的可判定性，这些**需要 `[DecidableEq α]`** ⟹ v6 在 `sweepPoints` 处报
-- `failed to synthesize Union (Finset α)`，并**级联污染后续声明**。
-- 这正是"error 条数高估缺陷个数"的典型：**一个缺失实例**。
variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 定义：分数、TPR/FPR、AUROC -/

/-- 真正率：在 OOD 集 `ood` 上，分数 `≥ t` 的比例（条件概率的计数版）。 -/
def tprAt (s : α → ℝ) (ood : Finset α) (t : ℝ) : ℝ :=
  ((ood.filter (fun x => t ≤ s x)).card : ℝ) / (ood.card : ℝ)

/-- 假正率：在 ID 集 `id` 上，分数 `≥ t` 的比例。 ⚠ 参数名 `id` 与数学的
「恒等」无关；为避免与 `id` 函数混淆，此处用 `idset`。 -/
def fprAt (s : α → ℝ) (idset : Finset α) (t : ℝ) : ℝ :=
  ((idset.filter (fun x => t ≤ s x)).card : ℝ) / (idset.card : ℝ)

/-- **AUROC（有序对计数 / Mann–Whitney 形式）**：
`(#{(o,i) | s o > s i} + ½ #{(o,i) | s o = s i}) / (|ood| * |id|)`。
即「随机取一个 OOD 与一个 ID，OOD 分数更高的概率（并列算 ½）」。

⚠ **G2 记法说明**：此处用 mathlib 的 `×ˢ`（`SProd`，`Finset.product` 的实例形式）
而非 `.product` 点记法 —— 二者**定义上相同**，但 `Finset.mem_product` 与
`Finset.card_product` 的**陈述**都用 `×ˢ` ⟹ 用点记法时 `rw` 找不到匹配模式
（v6 中 12 条 `did not find instance of the pattern (?s ×ˢ ?t).card` 即此因）。 -/
def auroc (s : α → ℝ) (ood idset : Finset α) : ℝ :=
  (((ood ×ˢ idset).filter (fun p => s p.1 > s p.2)).card : ℝ)
    / ((ood.card : ℝ) * (idset.card : ℝ))
  + (1 / 2) * (((ood ×ˢ idset).filter (fun p => s p.1 = s p.2)).card : ℝ)
    / ((ood.card : ℝ) * (idset.card : ℝ))

/-- **扫掠所需的分位点集**：`OOD ∪ ID` 中出现的全部分数（`image s`）。
⚠ **G2 诚实标注**：原 docstring 称「`RealOODDetection` 证明它与 `auroc` 的计数定义
一致」——该定理**在本文件中并不存在**（文件头「诚实边界」亦已声明
「扫掠定义与有序对计数定义的相等性**未形式化**」）。此处按**实际存在**的内容
改写 docstring，避免 `check-xref` 意义上的悬空引用。 -/
def sweepPoints (s : α → ℝ) (ood idset : Finset α) : Finset ℝ :=
  (ood ∪ idset).image s

/-! ## 定理 1（核心可证性质）：阈值单调性

`t ≤ t'` ⟹ 更严格的阈值（`t'`）使真正率与假正率**都不增**。
这是 ROC 曲线良定义的基础，**不需要任何分布假设**——纯 `Finset` 计数。 -/

theorem tpr_mono (s : α → ℝ) (ood : Finset α) {t t' : ℝ} (h : t ≤ t') :
    tprAt s ood t' ≤ tprAt s ood t := by
  unfold tprAt
  have hsub : ood.filter (fun x => t' ≤ s x) ⊆ ood.filter (fun x => t ≤ s x) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, le_trans h hx.2⟩
  have hcard : (ood.filter (fun x => t' ≤ s x)).card ≤ (ood.filter (fun x => t ≤ s x)).card :=
    Finset.card_le_card hsub
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

theorem fpr_mono (s : α → ℝ) (idset : Finset α) {t t' : ℝ} (h : t ≤ t') :
    fprAt s idset t' ≤ fprAt s idset t := by
  unfold fprAt
  have hsub : idset.filter (fun x => t' ≤ s x) ⊆ idset.filter (fun x => t ≤ s x) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, le_trans h hx.2⟩
  have hcard : (idset.filter (fun x => t' ≤ s x)).card ≤ (idset.filter (fun x => t ≤ s x)).card :=
    Finset.card_le_card hsub
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

/-- **TPR 与 FPR 同调**：阈值提高时两者同时不增——ROC 曲线单调下降的
轨迹性质（曲线的「形状」由这条保证）。 -/
theorem roc_trajectory_mono (s : α → ℝ) (ood idset : Finset α) {t t' : ℝ} (h : t ≤ t') :
    tprAt s ood t' ≤ tprAt s ood t ∧ fprAt s idset t' ≤ fprAt s idset t :=
  ⟨tpr_mono s ood h, fpr_mono s idset h⟩

/-! ## 定理 2：AUROC 的界（真界，非平凡） -/

theorem auroc_nonneg (s : α → ℝ) (ood idset : Finset α) :
    0 ≤ auroc s ood idset := by
  unfold auroc
  -- ⚠ **G2 修复**：原证明两次用 `by positivity` 去证分母
  -- `(↑ood.card * ↑idset.card)⁻¹ ≥ 0`，但 `positivity` **无法自行**
  -- 分解 `↑ood.card * ↑idset.card ≥ 0`（v9 报
  -- `⊢ 0 ≤ (↑ood.card * ↑idset.card)⁻¹` unsolved）。此处把分母非负
  -- 显式提取为 `hden`，两项的 `div_nonneg` 都直接复用它。
  have hden : (0 : ℝ) ≤ (ood.card : ℝ) * (idset.card : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h1 : (0 : ℝ) ≤ (((ood ×ˢ idset).filter (fun p => s p.1 > s p.2)).card : ℝ)
      / ((ood.card : ℝ) * (idset.card : ℝ)) :=
    div_nonneg (Nat.cast_nonneg _) hden
  have h2 : (0 : ℝ) ≤ (1 / 2) * (((ood ×ˢ idset).filter (fun p => s p.1 = s p.2)).card : ℝ)
      / ((ood.card : ℝ) * (idset.card : ℝ)) := by
    -- ⚠ **G2 修复（探针 `_probe_g2_pC.lean` 验证）**：表达式
    -- `1/2 * card / den` 按 **左结合** 解析为 `(1/2 * card) / den`，
    -- 故 `apply mul_nonneg` 会把它拆成 `(1/2) * ((card)/den)` 之外的形状，
    -- 第二个子目标变成 `0 ≤ den⁻¹`（v9 报 `⊢ 0 ≤ (↑ood.card * ↑idset.card)⁻¹`）。
    -- 正确做法：对**整个**商用 `div_nonneg`，分子 `1/2 * card ≥ 0` 用 `positivity`。
    exact div_nonneg (by positivity) hden
  linarith

/-- **AUROC ≤ 1**：两个不相交纤维（严格大于 / 相等）的计数之和
≤ 全部有序对计数。证明：两纤维不相交且并 ⊆ 全对集，
三个计数都是 ℕ，转 ℝ 后同除正的分母。 -/
theorem auroc_le_one (s : α → ℝ) (ood idset : Finset α) :
    auroc s ood idset ≤ 1 := by
  classical
  -- ⚠ **G2 重写（原证明的 `hG ▸ hpG` 触发 type mismatch）**：
  -- `set … with hG` 得到 `hG : G = P.filter …`；对 `hpG : p ∈ G` 做 `hG ▸ hpG`
  -- 时，elaborator 会在 `filter` 的谓词 `fun p => s p.1 > s p.2` 上取错 motive
  -- （v6 报 `s p.2 ∈ Finset.filter (GT.gt (s p.1)) ?m`）。改用 `rw [hG] at hpG`
  -- 把假设就地展开，行为确定且不依赖 `▸` 的 motive 推断。
  -- 同时把 `.product` 统一为 mathlib 记法 `×ˢ`，使 `Finset.card_product`
  -- （陈述为 `card (s ×ˢ t) = card s * card t`）可直接 `rw`。
  unfold auroc
  set P : Finset (α × α) := ood ×ˢ idset with hP
  set G : Finset (α × α) := P.filter (fun p => s p.1 > s p.2) with hG
  set E : Finset (α × α) := P.filter (fun p => s p.1 = s p.2) with hE
  -- G 与 E 不相交（一个 p 不可能同时 s.1 > s.2 且 s.1 = s.2）
  have hdisj : Disjoint G E := by
    rw [Finset.disjoint_left]
    intro p hpG hpE
    rw [hG] at hpG
    rw [hE] at hpE
    have h1 : s p.1 > s p.2 := (Finset.mem_filter.mp hpG).2
    have h2 : s p.1 = s p.2 := (Finset.mem_filter.mp hpE).2
    linarith
  -- G ∪ E ⊆ P
  have hsub : G ∪ E ⊆ P := by
    intro p hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · rw [hG] at hp; exact (Finset.mem_filter.mp hp).1
    · rw [hE] at hp; exact (Finset.mem_filter.mp hp).1
  -- 计数不等式：(G.card) + (E.card) ≤ P.card
  have hcard : G.card + E.card ≤ P.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  -- P.card = ood.card * idset.card
  have hPcard : P.card = ood.card * idset.card := by
    rw [hP, Finset.card_product]
  -- ⚠ **G2 修复（第 2 轮）**：`unfold auroc` 之后，目标里的分母已经是
  -- **ℝ 乘法** `↑ood.card * ↑idset.card`（不是 `↑P.card`）。
  -- 故要把它**换成** `↑P.card`（`←` 方向），而不是正向替换。
  -- 原 `rw [← hPcard]` 失败是因为 `hPcard` 的右端是 **ℕ** 乘法；此处用
  -- 由 `Nat.cast_mul` 得到的 **ℝ 版等式** 的**反向** `← hPcardR`。
  have hPcardR : ((P.card : ℕ) : ℝ) = (ood.card : ℝ) * (idset.card : ℝ) := by
    rw [hPcard, Nat.cast_mul]
  rw [← hPcardR]
  rcases Nat.eq_zero_or_pos P.card with hzero | hpos
  · -- P 为空 ⟹ 两个纤维均为空 ⟹ 分子为 0，0/0 = 0 ≤ 1
    -- ⚠ **G2 修复（第 3 轮）**：此处有**两个**不同的 pattern 失配，必须分开处理：
    --   (i) **内层** `rw [hzero] at this`（`this : p ∈ P`，目标 `False`）：
    --       `hzero : P.card = 0` 是**基数**等式，不能直接改写 `P` 本身 ⟹
    --       先 `Finset.card_eq_zero.mp` 得 `P = ∅`，再改写。
    --   (ii) **外层** `rw [hG0, hE0, hzero]`：目标里是 **`↑P.card`**（ℝ 强转）
    --       而非 `P.card` ⟹ 用 ℝ 版 `hzeroR` / `hG0R` / `hE0R`。
    have hzeroR : ((P.card : ℕ) : ℝ) = 0 := by rw [hzero]; norm_num
    have hPe : P = ∅ := Finset.card_eq_zero.mp hzero
    have hGsub : G ⊆ P := fun p hp => by
      rw [hG] at hp; exact (Finset.mem_filter.mp hp).1
    have hEsub : E ⊆ P := fun p hp => by
      rw [hE] at hp; exact (Finset.mem_filter.mp hp).1
    have hG0 : G.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
      intro p hp
      have := hGsub hp
      rw [hPe] at this
      exact Finset.not_mem_empty p this
    have hE0 : E.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
      intro p hp
      have := hEsub hp
      rw [hPe] at this
      exact Finset.not_mem_empty p this
    have hG0R : ((G.card : ℕ) : ℝ) = 0 := by rw [hG0]; norm_num
    have hE0R : ((E.card : ℕ) : ℝ) = 0 := by rw [hE0]; norm_num
    rw [hG0R, hE0R, hzeroR]
    norm_num
  · -- 把两项合并到同一分母（`div_add_div_same` 不匹配，因第二项是乘积形式；
    -- `ring` 在域中总成立，`x/0 = 0` 时两边同为 0）
    -- ⚠ **G2 修复（第 3 轮）**：`rw [← hPcardR]` 之后目标里的第二项按**左结合**
    -- 解析为 `1/2 * ↑E.card / ↑P.card`（= `(1/2 * ↑E.card) / ↑P.card`），
    -- 而原 `hkey` 写的是 `(1/2) * (↑E.card / ↑P.card)`（**不同项**）⟹ `rw [hkey]`
    -- 报 pattern 不匹配。改为与**目标同形**的 `hkey`，并把目标右侧也化到同一形状。
    have hkey : (G.card : ℝ) / (P.card : ℝ)
        + 1 / 2 * (E.card : ℝ) / (P.card : ℝ)
        = ((G.card : ℝ) + 1 / 2 * (E.card : ℝ)) / (P.card : ℝ) := by ring
    -- 用 `hpos : 0 < P.card` 显式给出 `div_le_one` 所需的证书
    have hPpos : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast hpos
    rw [hkey, div_le_one hPpos]
    have h1 : (G.card : ℝ) + (E.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hcard
    have h2 : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
    linarith

/-- **全并列时 AUROC = 1/2**：若所有 OOD 与 ID 分数相同（且两组**均非空**），
则 `auroc = 1/2`（有序对全在「相等」纤维，占 ½ 权重）。

⚠ **非空性不可省**：若两组中有空集，则 `|ood|·|id| = 0`，
由 Lean 的 `x/0 = 0` 得 `auroc = 0 ≠ 1/2`——故 `hoodne`/`hidne` 是
**必要假设**（机器核对：空集情形 `auroc = 0`）。 -/
theorem auroc_symmetric_tie (s : α → ℝ) (ood idset : Finset α)
    (htie : ∀ o ∈ ood, ∀ i ∈ idset, s o = s i)
    (hoodne : ood.Nonempty) (hidne : idset.Nonempty) :
    auroc s ood idset = 1 / 2 := by
  classical
  unfold auroc
  have hstrict : (ood ×ˢ idset).filter (fun p => s p.1 > s p.2) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ho, hi⟩, hgt⟩ := hp
    rw [htie _ ho _ hi] at hgt
    exact lt_irrefl _ hgt
  have htieall : (ood ×ˢ idset).filter (fun p => s p.1 = s p.2) = ood ×ˢ idset := by
    apply Finset.filter_true_of_mem
    intro p hp
    rw [Finset.mem_product] at hp
    exact htie _ hp.1 _ hp.2
  rw [hstrict, htieall, Finset.card_product]
  simp only [Finset.card_empty, Nat.cast_zero, zero_div]
  push_cast
  -- 分母非零（两组均非空 ⟹ 基数均 > 0）
  have h1 : 0 < ood.card := Finset.card_pos.mpr hoodne
  have h2 : 0 < idset.card := Finset.card_pos.mpr hidne
  have hca : (0 : ℝ) < (ood.card : ℝ) := by exact_mod_cast h1
  have hcb : (0 : ℝ) < (idset.card : ℝ) := by exact_mod_cast h2
  have hN : ((ood.card : ℝ) * (idset.card : ℝ)) ≠ 0 := ne_of_gt (mul_pos hca hcb)
  -- 目标是 `1/2 * N / N = 1/2`（N ≠ 0）：
  -- `1/2 * N / N` 解析为 `(1/2 * N) / N`，用 `mul_div_assoc` 提为 `(1/2) * (N / N)`。
  -- ⚠ **G2 修复**：此时目标实际是 **`0 + 1/2 * N / N = 1/2`**（严格分数项前面
  -- 残留了 `0 +`，来自 `simp only [..., zero_div]` 对第一项的化简），
  -- 故直接 `exact h1'` 报 type mismatch（缺 `0 +`）。用 `zero_add` 对齐。
  have h1' : (1 : ℝ) / 2 * ((ood.card : ℝ) * (idset.card : ℝ)) / ((ood.card : ℝ) * (idset.card : ℝ))
      = (1 : ℝ) / 2 := by
    rw [mul_div_assoc, div_self hN, mul_one]
  rw [zero_add]; exact h1'

/-! ## 定理 3：分离的**充分条件**（可证）

**阈值分离**：若存在 `t` 使 OOD 分数全 `≥ t` 而 ID 分数全 `< t`，
则该阈值处 `tpr = 1`、`fpr = 0`——检测器在此阈值上**完美**。
这是「分离 ⟹ 有效」的**可证充分条件**（条件是显式假设，故不是假命题）。 -/

theorem separation_from_threshold (s : α → ℝ) (ood idset : Finset α) {t : ℝ}
    (hood : ∀ o ∈ ood, t ≤ s o) (hid : ∀ i ∈ idset, ¬ (t ≤ s i))
    (hoodne : ood.Nonempty) (hidne : idset.Nonempty) :
    tprAt s ood t = 1 ∧ fprAt s idset t = 0 := by
  constructor
  · unfold tprAt
    have hfilter : ood.filter (fun x => t ≤ s x) = ood :=
      Finset.filter_true_of_mem (fun x hx => hood x hx)
    rw [hfilter]
    exact div_self (by
      have : 0 < ood.card := Finset.card_pos.mpr hoodne
      positivity)
  · unfold fprAt
    have hfilter : idset.filter (fun x => t ≤ s x) = ∅ := by
      rw [Finset.eq_empty_iff_forall_not_mem]
      intro x hx
      rw [Finset.mem_filter] at hx
      exact hid x hx.1 hx.2
    rw [hfilter]
    simp

/-- **完全分离 ⟹ AUROC = 1**：若 OOD 分数**逐点严格大于** ID 分数，
则所有 `|ood|·|id|` 个有序对都在「严格大于」纤维，故 `auroc = 1`。 -/
theorem perfect_separation_auroc_one (s : α → ℝ) (ood idset : Finset α)
    (hsep : ∀ o ∈ ood, ∀ i ∈ idset, s i < s o)
    (hoodne : ood.Nonempty) (hidne : idset.Nonempty) :
    auroc s ood idset = 1 := by
  classical
  unfold auroc
  have hstrict : (ood ×ˢ idset).filter (fun p => s p.1 > s p.2) = ood ×ˢ idset := by
    apply Finset.filter_true_of_mem
    intro p hp
    rw [Finset.mem_product] at hp
    exact hsep _ hp.1 _ hp.2
  have htie : (ood ×ˢ idset).filter (fun p => s p.1 = s p.2) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ho, hi⟩, heq⟩ := hp
    have := hsep _ ho _ hi
    linarith
  rw [hstrict, htie]
  simp only [Finset.card_empty, Nat.cast_zero, zero_div]
  -- ⚠ **G2 修复**：`simp only [zero_div]` 后目标里的 `↑(ood.card * idset.card)`
  -- 是 **ℕ 乘积的整体强制转换**，而 `Finset.card_product` 产出的是
  -- `↑ood.card * ↑idset.card`（**乘法在 ℝ**）⟹ 单纯 `rw [Finset.card_product]`
  -- 找不到模式（v9/wave 报 `↑ood.card * ↑idset.card / (↑ood.card * ↑idset.card)`
  -- pattern 不匹配）。补 `Nat.cast_mul` 把两者桥接。
  rw [Finset.card_product, Nat.cast_mul]
  have h1 : 0 < ood.card := Finset.card_pos.mpr hoodne
  have h2 : 0 < idset.card := Finset.card_pos.mpr hidne
  have hca : (0 : ℝ) < (ood.card : ℝ) := by exact_mod_cast h1
  have hcb : (0 : ℝ) < (idset.card : ℝ) := by exact_mod_cast h2
  have hne : ((ood.card : ℝ) * (idset.card : ℝ)) ≠ 0 := ne_of_gt (mul_pos hca hcb)
  -- ⚠ **G2 修复（第 3 轮）**：补上 `Nat.cast_mul` 后，第一项 `N / N` 已被
  -- `div_self` 化简（`simp` 可见 `N ≠ 0`），目标实际变成
  -- **`1 + 1/2 * 0 / N = 1`**（不再是 `N / N + 0 = 1`），
  -- 故原 `rw [div_self hne, zero_add]` 报 `0 + ?a` pattern 不匹配。
  -- 直接 `simp [hne]`：第一项 →1，并列项 →0。
  simp [hne]

/-! ## 定理 4（反例，机器验证）：`AUROC ≥ 1/2` **为假**

⚠️ 常见但**错误**的陈述：「AUROC 总是不小于 1/2」。
**反例**（**具体实例 + 内核证明**）：取 OOD 分数恒为 `0`、ID 分数恒为 `1`
（即分数方向与 OOD 相反），则每个有序对都落入 `s o < s i`，
严格大于纤维为空、并列纤维为空 ⟹ `auroc = 0 < 1/2`。

**这是本文件中唯一一个「对真实定义的具体机器验证反例」**：
`auroc` 的定义被真正实例化（`Fin 2`、`ood = {0}`、`idset = {1}`），
结论 `auroc < 1/2` 由内核证明，而非仅由算术类比。
正确的可证陈述是 `0 ≤ auroc ≤ 1`（定理 2）与
「**若**分数与标签同向分离**则** `auroc = 1`」（定理 3）。 -/

/-- **`auroc ≥ 1/2` 的反例**：存在分数使 `auroc = 0 < 1/2`。
构造：`ood = {0}`（分数 `0`）、`idset = {1}`（分数 `1`）。 -/
theorem auroc_ge_half_false :
    ∃ (s : Fin 2 → ℝ) (ood idset : Finset (Fin 2)),
      ood.Nonempty ∧ idset.Nonempty ∧ auroc s ood idset < 1 / 2 := by
  refine ⟨fun i => (i : ℝ), {0}, {1}, ?_, ?_, ?_⟩
  · exact ⟨0, Finset.mem_singleton_self 0⟩
  · exact ⟨1, Finset.mem_singleton_self 1⟩
  · -- s 0 = 0 < s 1 = 1，故严格大于纤维与并列纤维均为空 ⟹ auroc = 0
    -- ⚠ **G2 修复**：`unfold auroc` 把分数函数**按原样**代回，得到
    -- `(fun i => (↑i : ℝ))` 这类 **lambda 项**且**不 beta-化简**，
    -- 其头部与下面用**已化简**形式 `(↑p.1 : ℝ) > (↑p.2 : ℝ)` 陈述的
    -- `hstrict`/`htie` 不同形 ⟹ `rw` 找不到模式
    -- （报 `Finset.filter (fun p => ↑↑p.1 > p.2) ({0} ×ˢ {1})`；
    --  补 `beta_reduce` 仍留 `↑↑p.2` 与 `p.2` 的差异）。
    -- 改用 **`simp only [auroc]`**：`simp` 会正确地 beta-化简，
    -- 产出与 `hstrict` 完全同形的目标（探针 `_probe_g2_pG.lean` exit 0 验证）。
    simp only [auroc]
    have hstrict : Finset.filter (fun p : Fin 2 × Fin 2 => (p.1 : ℝ) > (p.2 : ℝ))
        (({0} : Finset (Fin 2)) ×ˢ {1}) = ∅ := by
      rw [Finset.eq_empty_iff_forall_not_mem]
      intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨h1, h2⟩, hgt⟩ := hp
      rw [Finset.mem_singleton] at h1 h2
      rw [h1, h2] at hgt
      norm_num at hgt
    have htie : Finset.filter (fun p : Fin 2 × Fin 2 => (p.1 : ℝ) = (p.2 : ℝ))
        (({0} : Finset (Fin 2)) ×ˢ {1}) = ∅ := by
      rw [Finset.eq_empty_iff_forall_not_mem]
      intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨h1, h2⟩, heq⟩ := hp
      rw [Finset.mem_singleton] at h1 h2
      rw [h1, h2] at heq
      norm_num at heq
    rw [hstrict, htie]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div, mul_zero]
    norm_num

/-- **反例的定量强化**：只要 OOD 分数**逐点小于** ID 分数，
`auroc = 0`（而非仅某个例子）——故 `≥ 1/2` 的失效是**结构性的**，
不是边界情形。

**无需非空假设**：两个纤维都为空 ⟹ 分子为 `0`，而 `0 / N = 0`（`N = 0`
时 `0/0 = 0` 在 ℝ 中成立），故结论无条件成立。 -/
theorem auroc_zero_of_reverse_separation (s : α → ℝ) (ood idset : Finset α)
    (hsep : ∀ o ∈ ood, ∀ i ∈ idset, s o < s i) :
    auroc s ood idset = 0 := by
  unfold auroc
  have hstrict : (ood ×ˢ idset).filter (fun p => s p.1 > s p.2) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ho, hi⟩, hgt⟩ := hp
    have := hsep _ ho _ hi
    linarith
  have htie : (ood ×ˢ idset).filter (fun p => s p.1 = s p.2) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ho, hi⟩, heq⟩ := hp
    have := hsep _ ho _ hi
    linarith
  rw [hstrict, htie]
  simp

/-! ## 定理 5：分离阈值的**存在性等价**（可证刻画）

「存在阈值完美分离」⟺ 「全部 ID 分数 < 全部 OOD 分数」。
这是定理 3 的**逆**，给出充分条件的**必要性**——
即阈值分离不是一个过强的假设，而是这种「完美检测」的**精确**条件。 -/

theorem threshold_separation_iff (s : α → ℝ) (ood idset : Finset α)
    (hoodne : ood.Nonempty) :
    (∃ t : ℝ, (∀ o ∈ ood, t ≤ s o) ∧ (∀ i ∈ idset, ¬ (t ≤ s i)))
      ↔ (∀ o ∈ ood, ∀ i ∈ idset, s i < s o) := by
  constructor
  · rintro ⟨t, hood, hid⟩ o ho i hi
    have h1 := hood o ho
    have h2 := hid i hi
    push_neg at h2
    linarith
  · intro hsep
    -- 取 t = OOD 分数的最小值（`inf'` 对**函数值**取下确界）。
    -- ⚠ `inf'_le (h : b ∈ s) : s.inf' ⟨b,h⟩ f ≤ f b`（Fold.lean:900）中
    -- **下确界在左**，正对本目标的形状；而 `le_inf'_iff` 是「下确界在右」，
    -- 方向相反不能用（用 `rw` 会报 pattern 不匹配）。
    -- `⟨o,ho⟩` 与 `hoodne` 作为 `Nonempty` 见证的差异由 proof irrelevance 消解。
    refine ⟨(ood.inf' hoodne s), ?_, ?_⟩
    · intro o ho
      exact Finset.inf'_le (s := ood) (f := s) ho
    · intro i hi
      -- ⚠ **G2 修复**：原证明想由单个 `o₀` 的 `hsep o₀ ho₀ i hi : s i < s o₀`
      -- 直接得 `s i < ood.inf' hoodne s`，但 `inf'` 是**下确界**，
      -- `s i < s o₀` 与 `inf' ≤ s o₀` **不能**推出 `s i < inf'`
      -- （v9 报 `not_le.mpr` 的 type mismatch：期望 `s i < ood.inf' ⋯ s`）。
      -- 正确引理是 **`Finset.lt_inf'_iff : a < s.inf' H f ↔ ∀ i ∈ s, a < f i`**
      -- （`Data/Finset/Lattice/Fold.lean:1138`）——「小于下确界 ⟺ 小于所有元素」，
      -- 正对目标形状。
      exact not_le.mpr ((Finset.lt_inf'_iff _).mpr (fun o ho => hsep o ho i hi))

/-- 定理 5 的**推论（存在性）**：若 OOD 非空且「所有 ID 分数 < 所有 OOD 分数」，
则存在完美分离阈值。 -/
theorem exists_separating_threshold (s : α → ℝ) (ood idset : Finset α)
    (hoodne : ood.Nonempty)
    (hsep : ∀ o ∈ ood, ∀ i ∈ idset, s i < s o) :
    ∃ t : ℝ, (∀ o ∈ ood, t ≤ s o) ∧ (∀ i ∈ idset, ¬ (t ≤ s i)) :=
  (threshold_separation_iff s ood idset hoodne).mpr hsep

end Lattice
