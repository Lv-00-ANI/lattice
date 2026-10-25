import Mathlib

/-!
# LATTICE: 课程顺序与折扣累积损失——**诚实边界版**（训练系统方向，W8-8）

## 建立什么

课程学习（curriculum learning）的核心直觉是「先易后难」。本文件把它化成
**关于累积损失的偏序陈述**，并**如实给出它实际能说什么、不能说什么**。

⚠⚠ **本文件经 Q1 审计后【降级定位】（B231）**：原稿标题为
「课程顺序的单调性——『先易后难』不劣于任意顺序的**条件**」，暗示本文件证明了
一条**有内容的单调性**。**审计结论是：该暗示不成立**，理由见下（已内核验证）：

| 结果 | 实际内容 |
|:--|:--|
| `curriculum_dominance_le` | ⚠ `hdom` **不是**「弱支配」，而是**强制两顺序同权重** ⟹ 结论是**等式**，`hc0` **冗余** |
| `curriculum_gamma_one_degenerate` | ⭐ 诚实的**否定性**结论：`γ = 1` 时顺序**完全无关** |
| `posWeight_sum_eq` / `posWeight_eq_of_le` | ⭐ **审计的形式化**：位置权重之和与顺序无关 ⟹ `hdom` 蕴含逐点相等 |

⇒ **本文件真正成立的内容是**：(a) 一条**重指标恒等式**（`cumLoss_eq_sum_posWeight`）、
(b) 一条**退化/否定性边界定理**（`γ = 1` 时顺序无关）、
(c) 两条**关于自身假设强度的元结果**（`posWeight_sum_eq` / `posWeight_eq_of_le`）。
⚠ **本文件【不】包含**「更好的课程顺序严格更优」这一命题——
那需要一个**`hdom` 之外的比较机制**（例如允许两顺序的样本集不同、
或让代价 `c` 依赖训练位置），**本文件未提供，且本文件实证该机制不可省**。

**模型**：训练顺序是**双射** `σ : Fin N ≃ α`（每个样本恰好训练一次，
`σ t` 在第 `t+1` 步训练）；单样本代价 `c : α → ℝ`（越难代价越大）；
折扣因子 `γ > 0`（早期样本影响更大时 `γ < 1`）。**折扣累积损失**

  `cumLoss γ c σ = Σ_{t : Fin N} γ^(t:ℕ) · c (σ t)`。

1. `cumLoss_eq_sum_posWeight`：**按时间求和 = 按样本求和**——
   `cumLoss γ c σ = Σ_a (γ^(σ⁻¹a)) · c a`（双射换指标）；
2. ⭐ `cumLoss_sub_eq`（**核心工具**）：两个顺序的累积损失差
   `= Σ_a (posWeight σ a - posWeight τ a) · c a`
   ——**纯位置量 × 纯代价量**的内积，故「顺序只通过位置起作用」；
3. 要点：`curriculum_dominance_le`（**原主定理，已降级**）：`0 < γ ≤ 1`、`c ≥ 0`、
   `∀ a, posWeight τ a ≤ posWeight σ a`（**弱支配**）⟹ `cumLoss γ c σ ≤ cumLoss γ c τ`；
   ⚠⚠ **本条已被本文件自查【重新定性】（B231）**：`hdom` 并非「弱支配」——
   由 `posWeight_sum_eq`（位置权重之和与顺序无关）+ 逐点 `≤` ⟹ **逐点相等**
   （`posWeight_eq_of_le`），故结论其实是**等式**，且 `hc0` **冗余**
   （`cumLoss_sum_eq_of_dom`）。**定理为真**，但**比原稿宣传的弱得多**；
4. `posWeight_le_one`：`0 < γ ≤ 1` ⟹ `posWeight γ σ a ≤ 1`（位置权重上界）；
5. ⭐ `curriculum_gamma_one_degenerate`：`γ = 1` ⟹
   `cumLoss 1 c σ = Σ_a c a`，**与顺序无关**。
   ⟹ **`γ = 1` 时所有顺序并列最优**（含**降序**）——
   这是本文件最重要的**诚实边界**定理。

## 依赖什么

纯 `Mathlib`。**不** import 任何 LATTICE 模块（保持零耦合）。

## 不做什么（诚实边界）

- **不**给出课程学习的**算法**（怎么求 `σ`）：本文件只给**判据与条件**；
- **不**涉及**非线性 / 顺序依赖**的代价：本文件的 `c` 是**与顺序无关**的
  单样本代价（真实训练中样本代价随参数演化，本文件**不**覆盖）；
- ⚠ **不**声称「先易后难总是最优」——**这是假命题**。
  只有当 `σ` **弱支配** `τ` 时才有 `cumLoss σ ≤ cumLoss τ`；
  对**不可比**的两个顺序，结论可以**任一方向**成立（本文件不给该断言）。
- ⚠⚠ **本文件自查的重要更正（B231）**：原稿把 `hdom` 称为「弱支配」，
  并据此宣传主定理为「课程顺序的单调性」。**该读法是错的**：
  对**双射** `σ τ`，位置权重之和恒为 `∑ k, γ^k`（与顺序无关），
  故 `hdom`（逐点 `≤`）⟹ **逐点相等**（`posWeight_eq_of_le`）。
  ⇒ 主定理的实际内容是「**同权重 ⟹ 同损失**」，
  **不是**「更好安排的顺序严格更优」。⚠ **严格的课程收益需要一个
  `hdom` 之外的比较机制**（例如允许两顺序的样本集不同、
  或让代价 `c` 依赖训练位置），**本文件【未】提供**。
  这是一个**结构性**的诚实边界，而不是可以靠补证明修好的技术缺口。
- **不**涉及 pivot / self-paced learning（另一族方法）。

## ⚠ 边界取等检查（本文件的关键）

- ⭐ **`γ = 1`（取等号处）**：`γ^(t:ℕ) = 1` 对所有 `t` 成立，
  故 `cumLoss 1 c σ = Σ_a c a` **与顺序无关** ⟹ **所有**顺序并列最优
  ⟹ 「最优必须非降排列」**不成立**（任何顺序都是最优，**包括降序**）。
  见证：`α = Fin 2`、`c = (0, 1)`、`N = 2`：升序 `cumLoss = 0 + 1 = 1`，
  降序 `= 1 + 0 = 1`，**相等**（`curriculum_gamma_one_all_orders_equal`）。
- **`γ ∈ (0,1]` 必须显式**：`γ ≤ 0` 时 `γ^(t:ℕ)` 的符号交替
  （`γ = -1` 时 `1, -1, 1, …`），`cumLoss` 的单调性**失效**。
  取 `γ = -1`、`α = Fin 2`、`c = (1, 0)`、`N = 2`：升序 `cumLoss = 1 + 0 = 1`，
  降序 `= 0 + (-1)·1 = -1`，**降序更小**——与 `γ > 0` 时的直觉**相反**。
  本文件所有定理带 `0 < γ`。
- **`N = 0`**：`Fin 0` 上无元素，`σ : Fin 0 ≃ α` 迫使 `α` 为空，
  `cumLoss = 0`——所有（唯一的）顺序并列。本文件的定理在 `N = 0` 时
  **仍成立**（空和），不构成反例。
- **`posWeight` 的界 `≤ 1` 依赖 `γ ≤ 1`**：`γ > 1` 时位置**越早权重越小**，
  「提前」反而**减小**权重，`curriculum_dominance_le` 的结论方向**反转**。
-/

noncomputable section

namespace Lattice

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **折扣累积损失**：`cumLoss γ c σ = Σ_{t : Fin N} γ^(t:ℕ) · c (σ t)`。

`σ 0` 是最早训练的样本，权重 `γ^0 = 1`；`γ < 1` 表示早期样本影响更大。
把「训练顺序」建模为**双射**（而非列表），使 `σ⁻¹` 与「按样本重新索引」良定义。 -/
def cumLoss {N : ℕ} (γ : ℝ) (c : α → ℝ) (σ : Fin N ≃ α) : ℝ :=
  ∑ t : Fin N, γ ^ (t : ℕ) * c (σ t)

/-- **位置权重**：`posWeight γ σ a = γ^((σ⁻¹ a):ℕ)`——样本 `a` 在顺序 `σ` 下
所受的折扣权重。

**它比定义多说了什么**：把 `cumLoss` 从「按训练时间」重新索引为「按样本」的
**载体**，使两个不同顺序的 `cumLoss` 之差可以**逐样本**比较，
无需对齐时间轴。 -/
def posWeight {N : ℕ} (γ : ℝ) (σ : Fin N ≃ α) (a : α) : ℝ :=
  γ ^ ((σ.symm a : Fin N) : ℕ)

/-- **按时间求和 = 按样本求和**：`cumLoss γ c σ = Σ_a posWeight γ σ a · c a`。

**它比定义多说了什么**：把「沿训练时间求和」重写成「沿样本求和」，
从而**两个不同顺序的 `cumLoss` 之差**可以**逐样本对齐**
（同一个 `a` 在两个顺序下的权重相减）。
**证明**：`Equiv.sum_comp σ`（双射换指标）+
`σ.symm (σ t) = t`。 -/
theorem cumLoss_eq_sum_posWeight {N : ℕ} (γ : ℝ) (c : α → ℝ) (σ : Fin N ≃ α) :
    cumLoss γ c σ = ∑ a : α, posWeight γ σ a * c a := by
  have h := Equiv.sum_comp σ (fun a : α => γ ^ ((σ.symm a : Fin N) : ℕ) * c a)
  simp only [Equiv.symm_apply_apply] at h
  simpa [cumLoss, posWeight] using h

/-- ⭐ **顺序差的逐样本公式（核心工具）**：
`cumLoss γ c σ - cumLoss γ c τ = Σ_a (posWeight γ σ a - posWeight γ τ a) · c a`。

**它比定义多说了什么**：把「两个课程的累积损失差」**完全解耦**为
「**纯位置量** `Δ_a := posWeight σ a - posWeight τ a`」与「**纯代价量** `c a`」的内积。
由此直接读到：
- 若 `Δ_a = 0`（两顺序给所有样本同权重位置——如 `γ = 1`），差为 `0`，**与 `c` 无关**；
- 顺序优化的**全部自由度**都在 `Δ` 上，`c` 只作为**权重**出现。

⚠ 这**不是** `ring` 级重述：它把两个**不同指标集**（`Fin N` 与 `α`）上的求和
通过双射对齐。**证明**：`cumLoss_eq_sum_posWeight` 两次 + `Finset.sum_sub_distrib`。 -/
theorem cumLoss_sub_eq {N : ℕ} (γ : ℝ) (c : α → ℝ) (σ τ : Fin N ≃ α) :
    cumLoss γ c σ - cumLoss γ c τ
      = ∑ a : α, (posWeight γ σ a - posWeight γ τ a) * c a := by
  rw [cumLoss_eq_sum_posWeight γ c σ, cumLoss_eq_sum_posWeight γ c τ,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **位置权重上界**：`0 < γ`、`γ ≤ 1` ⟹ `posWeight γ σ a ≤ 1`。

**它比定义多说了什么**：给出**位置的权重上界** `≤ 1`——`γ ∈ (0,1]` 时
**最早**位置的权重是 `γ^0 = 1`，之后都更小。
这是 `curriculum_dominance_le` 之外**唯一**用到的数值事实，
也是「`γ ≤ 1` 是必需的」的**载体**：`γ > 1` 时 `γ^k ≥ 1`，本引理为**假**。 -/
theorem posWeight_le_one {N : ℕ} (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (σ : Fin N ≃ α) (a : α) : posWeight γ σ a ≤ 1 := by
  unfold posWeight
  exact pow_le_one₀ (le_of_lt hγ0) hγ1

/-! ## 三-bis、⭐⭐ 本文件自查结论：`hdom` 强制「同权重」（**B231**）

⚠ 本节的两条定理**在声明上先于主定理**（`curriculum_dominance_le` 的修复
依赖它们），故放在这里。 -/

/-- ⭐ **位置权重之和与顺序无关**：`∑ a, posWeight γ σ a = ∑ k : Fin N, γ ^ (k : ℕ)`。

**为什么关键**：两个**不同**的顺序给出的是**同一个多重集** `{γ^k : k < N}`
（只是分配给了不同的样本），故**总和相同**。这是下一条的机械内核。 -/
theorem posWeight_sum_eq (γ : ℝ) {N : ℕ} (σ : Fin N ≃ α) :
    ∑ a : α, posWeight γ σ a = ∑ k : Fin N, γ ^ (k : ℕ) := by
  unfold posWeight
  rw [← Equiv.sum_comp σ (fun a : α => γ ^ ((σ.symm a : Fin N) : ℕ))]
  simp only [Equiv.symm_apply_apply]

/-- ⭐⭐ **`hdom` 强制逐点相等（本文件自查的形式化，B231）**：
`∀ a, posWeight γ τ a ≤ posWeight γ σ a` ⟹ `∀ a, posWeight γ σ a = posWeight γ τ a`。

**证明**：由 `posWeight_sum_eq`，两侧之和**相同**；
逐点差 `≥ 0` 且总和为 `0` ⟹ 每项差为 `0`
（`Finset.sum_eq_zero_iff_of_nonneg`）。

⚠ **这条推翻了 `curriculum_dominance_le` 的「弱支配」读法**：
`hdom` 不是「允许严格占优」的条件，而是**已经蕴含两边权重函数相同**。 -/
theorem posWeight_eq_of_le (γ : ℝ) {N : ℕ} (σ τ : Fin N ≃ α)
    (hdom : ∀ a, posWeight γ τ a ≤ posWeight γ σ a) :
    ∀ a, posWeight γ σ a = posWeight γ τ a := by
  have hsum : ∑ a : α, posWeight γ σ a = ∑ a : α, posWeight γ τ a := by
    rw [posWeight_sum_eq γ σ, posWeight_sum_eq γ τ]
  have hnn : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ posWeight γ σ a - posWeight γ τ a := by
    intro a _
    exact sub_nonneg.mpr (hdom a)
  have hzero : ∑ a : α, (posWeight γ σ a - posWeight γ τ a) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  intro a
  have hmem : a ∈ (Finset.univ : Finset α) := Finset.mem_univ a
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero a hmem
  rw [sub_eq_zero] at this
  exact this

/-- ⭐ **主定理：弱支配 ⟹ 不劣**。

`0 < γ ≤ 1`、`c ≥ 0`、`∀ a, posWeight γ τ a ≤ posWeight γ σ a`（**弱支配**）⟹
`cumLoss γ c σ ≤ cumLoss γ c τ`。

**它比定义多说了什么（本文件的主结论）**：⚠⚠ **经审计后，答案是「几乎没有多说什么」**
——见下（**B231**，已内核验证）。

**证明（重写后）**：由 `posWeight_eq_of_le`（见 §三-bis），`hdom` **已经强制**
`posWeight γ σ = posWeight γ τ` 逐点；再由 `cumLoss_eq_sum_posWeight` 两次即得
**等式** `cumLoss γ c σ = cumLoss γ c τ`（`le_of_eq`）。

注意：**假设承重情况的实测更正（本文件自查，B231）**：
本定理证明体**未使用** `hγ0`、`hγ1`（二者在证明体中无任何出现）；
但 `hc0` **被使用**——它参与构造中间量 `hnonneg`
（在 `Finset.sum_nonneg` 分支中经 `mul_nonneg h1 (hc0 a)` 调用）。
注意：**更正说明**：本节此前曾声称证明体「未使用 `hc0`」并触发对应的
`unused variable` 警告，该表述**与代码不符**（且 `hc0` 未加下划线前缀，
本就不在本文件会报该警告的范围内）。准确的说法是：
`hc0` 被用于构造 `hnonneg`，而 `hnonneg` 这一**中间量**最终未被使用
（结论走的是等式路线）。
**这不是「假设写松」而是「假设根本不需要」**：
`hdom` + 双射结构**已经蕴含结论**，与 `γ` 的取值、与 `c` 的符号**均无关**。
⇒ 本定理可**去假设化**为：

  `hdom ⟹ cumLoss γ c σ ≤ cumLoss γ c τ`（对任意 `γ : ℝ`、任意 `c : α → ℝ`）。

注意：**原稿的 `hc0` 承重背书是无效的**：原稿给「`c = (1, -1)`、`γ = 1/2`、
`σ`/`τ` 互反」作为 `hc0` 的承重反例，但该例**同时违反 `hdom`**
（对样本 `1`，`posWeight τ = 1 ≰ 1/2 = posWeight σ`），
故它**不是**「只去掉 `hc0`」的反例（**反例必须满足其余全部假设**）。

⭐⭐ **真因（已形式化）**：对**双射** `σ τ : Fin N ≃ α`，位置权重之和
`∑ a, posWeight γ σ a = ∑ k : Fin N, γ ^ (k:ℕ)` **与 `σ` 无关**（`posWeight_sum_eq`）。
故 `hdom`（逐点 `≤`）加上**总和相等** ⟹ **逐点相等**（`posWeight_eq_of_le`）。

注意：**因此 `hdom` 并非「弱支配」而是「强制同权重」**：
当 `N = Fintype.card α` 且权重 `γ^k` 互异时，`hdom` 只在
`posWeight σ = posWeight τ` 时成立 ⟹ 本定理的实际内容是
「两个顺序若给每个样本**相同**的位置权重，则累积损失**相同**」。
这比原稿宣传的「先易后难不劣于任意顺序」**弱得多**（后者需要
`hdom` 之外的、逐样本**严格**占优的可比性，而那样的 `σ τ` **不存在**）。
注意：该弱点**不是**「命题为假」——定理**为真**（已内核验证）；
是**表述的成就高于实际**（**B222.2 同族**）。已在下文登记为诚实边界。

注意：**保留 `hγ0`/`hγ1`/`hc0` 的决定**：为**兼容既有调用点**与保持接口稳定而保留，
并在 docstring 中如实标注它们**对本定理不承重**；
注意：**不得**用 `set_option linter.unusedVariables false` 掩盖（**B224.5 明确拒绝**）。 -/
theorem curriculum_dominance_le {N : ℕ} (γ : ℝ) (c : α → ℝ) (σ τ : Fin N ≃ α)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hc0 : ∀ a, 0 ≤ c a)
    (hdom : ∀ a, posWeight γ τ a ≤ posWeight γ σ a) :
    cumLoss γ c σ ≤ cumLoss γ c τ := by
  have hdiff : cumLoss γ c σ - cumLoss γ c τ
      = ∑ a : α, (posWeight γ σ a - posWeight γ τ a) * c a := cumLoss_sub_eq γ c σ τ
  have hnonneg : 0 ≤ ∑ a : α, (posWeight γ σ a - posWeight γ τ a) * c a := by
    refine Finset.sum_nonneg fun a _ => ?_
    -- `sub_nonneg : 0 ≤ a - b ↔ b ≤ a`，取 `a := posWeight σ a`、`b := posWeight τ a`
    have h1 : 0 ≤ posWeight γ σ a - posWeight γ τ a := sub_nonneg.mpr (hdom a)
    exact mul_nonneg h1 (hc0 a)
  -- 注意：**修复（B231）—— 本条的证明路径经审计后重写**。原稿是
  -- `linarith [hdiff, hnonneg]`，报 `linarith failed to find a contradiction`（实测）。
  -- **表层原因是 `linarith` 在含 `∑` 的等式上原子化不稳**（B213）；
  -- 但深查后发现**更深的问题**：
  --   `hdiff : cumLoss σ - cumLoss τ = Σ (pw_σ - pw_τ)·c`，
  --   而 `hdom : ∀ a, pw_τ a ≤ pw_σ a` 使 `(pw_σ - pw_τ) ≥ 0`，配合 `hc0` 得 `Σ ≥ 0`，
  --   即 `0 ≤ cumLoss σ - cumLoss τ`，由 `sub_nonneg.mp` 得 **`cumLoss τ ≤ cumLoss σ`**
  --   ——**与目标 `cumLoss σ ≤ cumLoss τ` 方向相反**！
  -- ⇒ 该 `≤` 路线**证不出**目标（除非取等）。**正确路线是走等式**：
  --   由本文件已证 `posWeight_eq_of_le`（**本节之后的 §三-bis**，故此处内联证明）
  --   `hdom` 强制 `pw_σ = pw_τ` 逐点，从而 `cumLoss σ = cumLoss τ`。
  --   注意：这**同时**说明 `hc0` 在证明中**根本不需要**（与 §三-bis 的结论一致）。
  have hsum : ∑ a : α, posWeight γ σ a = ∑ a : α, posWeight γ τ a := by
    rw [posWeight_sum_eq γ σ, posWeight_sum_eq γ τ]
  have hzero : ∑ a : α, (posWeight γ σ a - posWeight γ τ a) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hnn : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ posWeight γ σ a - posWeight γ τ a :=
    fun a _ => sub_nonneg.mpr (hdom a)
  have hpt : ∀ a, posWeight γ σ a = posWeight γ τ a := by
    intro a
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero a (Finset.mem_univ a)
    linarith
  have heq : cumLoss γ c σ = cumLoss γ c τ := by
    rw [cumLoss_eq_sum_posWeight γ c σ, cumLoss_eq_sum_posWeight γ c τ]
    exact Finset.sum_congr rfl fun a _ => by rw [hpt a]
  exact le_of_eq heq

/-- ⭐⭐ **推论：`hc0` 冗余，且结论为等式（B231）**：
在 `hdom` 之下，`∑ a, posWeight γ σ a * c a = ∑ a, posWeight γ τ a * c a`
对**任意** `c : α → ℝ` 成立——**不需要** `0 ≤ c a`。

注意：这是对原文件「`hc0` 不可省（有反例背书）」的**直接否定**：
原稿的反例**同时违反 `hdom`**，故不成立；而本条证明 `hc0` 在 `hdom` 下**确实可省**。 -/
theorem cumLoss_sum_eq_of_dom {N : ℕ} (γ : ℝ) (c : α → ℝ) (σ τ : Fin N ≃ α)
    (hdom : ∀ a, posWeight γ τ a ≤ posWeight γ σ a) :
    ∑ a : α, posWeight γ σ a * c a = ∑ a : α, posWeight γ τ a * c a := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [posWeight_eq_of_le γ σ τ hdom a]

/-- **`γ = 1` 的退化（边界取等的机器验证见证）**：`γ = 1` 时
`cumLoss 1 c σ = Σ_a c a`，**与顺序无关**。

**它比定义多说了什么**：**证明**「无折扣时课程顺序对累积损失毫无影响」，
从而**排除**「先易后难总是最优」这一读法——`γ = 1` 时**所有**顺序并列最优
（含**降序**）。这是本文件最重要的**诚实边界**定理：
一个只写 `curriculum_dominance_le` 的文件会让读者误以为课程总是有益的。

注意：**`γ = 1` 不可与 `γ < 1` 混同**：`γ < 1` 时位置权重**严格**递减
（`γ^k` 严格递减），故「提前易样本」**确实**有收益；
`γ = 1` 时收益**恰为零**。**证明**：`1 ^ k = 1` 逐项 +
`Finset.sum_congr`。 -/
theorem curriculum_gamma_one_degenerate {N : ℕ} (c : α → ℝ) (σ : Fin N ≃ α) :
    cumLoss 1 c σ = ∑ a : α, c a := by
  rw [cumLoss_eq_sum_posWeight]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold posWeight
  rw [one_pow, one_mul]

/-- **`γ = 1` 时所有顺序并列**：`cumLoss 1 c σ = cumLoss 1 c τ`（`σ`、`τ` 任意）。

**它比定义多说了什么**：把上一条的**顺序无关性**写成**任意两个顺序相等**，
直接说明**「最优顺序」在 `γ = 1` 时不唯一**（`Fin N ≃ α` 的全部元素并列）。
注意：**这依赖 `σ`、`τ` 有相同的定义域类型** `Fin N`
（不同 `N` 的顺序不可比——样本数不同）。 -/
theorem curriculum_gamma_one_all_orders_equal {N : ℕ} (c : α → ℝ) (σ τ : Fin N ≃ α) :
    cumLoss 1 c σ = cumLoss 1 c τ := by
  rw [curriculum_gamma_one_degenerate c σ, curriculum_gamma_one_degenerate c τ]

/-- **非平凡性见证：`γ < 1` 时位置权重严格递减**——
`k < l` ⟹ `γ^l < γ^k`（`0 < γ < 1`）。

**它比定义多说了什么**：证明 `γ = 1` 的退化是**边界现象**：
`γ < 1` 时位置**真的**不平衡，`cumLoss` **真的**依赖顺序。
注意：**但这【不】构成 `curriculum_dominance_le` 的非空洞性**：
由 `posWeight_eq_of_le`，满足 `hdom` 的两个**不同**顺序必然同权重、同损失，
故该定理在 `γ < 1` 时**同样只给出等式**（空洞性来自 `hdom` 本身，与 `γ` 的取值无关）。
注意：**`γ < 1` 与 `0 < γ` 都必需**：`γ = 1` 时 `γ^l = γ^k`（退化）；
`γ = 0` 时 `γ^0 = 1`、`γ^l = 0`（`l > 0`），仍有严格递减，但 `γ ≤ 0` 时
`pow_lt_pow_of_lt_left` 的底数非负前提失效。 -/
theorem curriculum_posWeight_strict {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {k l : ℕ}
    (hkl : k < l) : γ ^ l < γ ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkl
  have hd1 : γ ^ (d + 1) < 1 := pow_lt_one₀ (le_of_lt hγ0) hγ1 (by omega)
  rw [pow_add, pow_one] at hd1
  have hpos : 0 < γ ^ k := pow_pos hγ0 k
  calc γ ^ (k + d + 1) = γ ^ k * (γ ^ d * γ) := by ring
    _ < γ ^ k * 1 := by
        exact mul_lt_mul_of_pos_left (by linarith [hd1]) hpos
    _ = γ ^ k := by ring

end Lattice
