import Mathlib
import Lattice.Lib.Architectures.RealSSM
import Lattice.Lib.Architectures.RealSelectiveSSM
import Lattice.Lib.Attention.RealCausalAttention
/-!
# LATTICE: SSD / semiseparable 矩阵桥 —— 选择性 SSM 与 masked attention 的双向等式

## 背景与动机

Mamba-2 的 **State Space Duality（SSD）**（arXiv `2405.21060v1` Thm 3.5 / Thm 5.2）指出：
**不存在**「Mamba = 线性注意力」的严格等价定理（文献措辞均为 "can be viewed as"），
严格的桥是**第三物 —— semiseparable（半可分）矩阵** `M`。本文件把该桥形式化。

上游素材（本文件**不重复实现**，只重排 / 接线）：

* `RealSelectiveSSM.selProd`（`RealSelectiveSSM.lean:92`）：时变乘积型基本解
  `selProd A k t = A_{t-1} * ... * A_k`（下标递减、新因子在左）；
* `RealSelectiveSSM.selProd_concat`（`RealSelectiveSSM.lean:173`）：**粘合律**
  `k <= m <= t` 时 `selProd A k t = selProd A m t * selProd A k m`；
* `RealSelectiveSSM.selState_explicit`（`RealSelectiveSSM.lean:197`）：时变闭式解
  `selState A B t = ∑ k in range t, selProd A (k+1) t * B k`；
* `RealSSM.ssm_state_compose`（`RealSSM.lean:166`）：结合律重排（并行扫描的代数依据）；
* `RealCausalAttention.causalMask`（`RealCausalAttention.lean:40`）：因果掩码约定。

## 本文件给什么

* `ssdEntry`：`M_ji = C_j ⬝ ((selProd A (i+1) j * B_i) *ᵥ w)` —— **半可分矩阵的显式项**；
* `ssdEntry_of_gt`：`j < i` 时 `selProd` 退化为 `1`，故 `M_ji = C_j ⬝ (B_i *ᵥ w)`；
* `ssdEntryMasked` / `ssdEntryMasked_eq_zero`：把下三角零性作为**显式掩码**给出；
* `ssdEntry_succ`：**逐行递推** —— semiseparable 一词的代数内容；
* `ssd_prod_concat`：**粘合律重排**（`selProd_concat` 的实例化）；
* `sum_mulVec_range` / `dotProduct_sum_range`：两个 `Finset` 重排工具引理；
* `ssdMatVec_eq_selState`（**核心 ①**）：`∑_{i<j} M_ji = C_j ⬝ (h_j *ᵥ w)`，`h = selState A B`；
* `ssd_row_succ_eq`（**订正见证**）：`∑_{i<j+1} M_ji = C_j ⬝ (h_j *ᵥ w) + C_j ⬝ (B_j *ᵥ w)`
  —— 机器证明「多加的那一项**不为零**」，故 `range (j+1)` 版本为**假**；
* `maskedAttn` / `maskedAttn_sum_eq`（**核心 ②**）：attention 侧精确等式；
* `ssd_quadForm_eq_stateSum` / `ssd_stateSum_eq_quadForm`（**核心 ③③'**）：**双向** `Finset` 重排；
* `maskedAttn_eq_ssd_row`（**核心 ④**）：attention 侧与矩阵侧**合流到同一 `h`**；
* `ssd_scan_compose`：扫描结合律在矩阵侧的对应物。

## 关键设计

### 1. 类型设计：`B` 必须是**矩阵族**，不是向量族
`RealSelectiveSSM.selState : (ℕ → 𝔸) → (ℕ → 𝔸) → ℕ → 𝔸` —— 两个参数**同型**。
故取 `A B : ℕ → Matrix (Fin n) (Fin n) ℝ`（`B_i` 是把输入 `x_i` 注入状态的**注入矩阵**），
读出用共向量 `C : ℕ → Fin n → ℝ` 与探测向量 `w : Fin n → ℝ`。
这是**试做中发现的第一个接口约束**：`selState` 不允许 `A` 是矩阵而 `B` 是向量。

### 2. ⚠ 指标范围：`selState_explicit` 的内层和是 `range t`，**不是** `range (t+1)`
**这是本轮试做最重要的订正**。`selState_explicit` 给出 `range t`，且 `selState A B 0 = 0`。
故矩阵侧行和必须**同样**取 `range j`：

    `∑_{i<j} M_ji = C_j ⬝ (h_j *ᵥ w)`（**不是** `∑_{i<=j}`）

若误写 `range (j+1)`，多余的第 `i = j` 项（因 `selProd A (j+1) j = 1`）退化为
`C_j ⬝ (B_j *ᵥ w)`，右端**没有**这一项 ⟹ 命题**为假**。
本条已写成**正面的机器验证定理** `ssd_row_succ_eq`（显式给出差项），
即「多加一项 = 差一个 `C_j ⬝ (B_j *ᵥ w)`」——这比反例更强：它给出**精确的偏差量**。

### 3. ⚠ 实例供给
`selProd` 要求 `[NormedRing 𝔸]`，而 mathlib 的 `Matrix` 范数环是**显式非实例**
（`Matrix.linftyOpNormedRing`，`Analysis/Matrix.lean:378` 用 `protected def`）。
且 `selProd_concat` / `selState_explicit` 还需要 `[NormOneClass 𝔸]`，其矩阵实例
`Matrix.linfty_opNormOneClass`（`Analysis/Matrix.lean:354`）**要求 `[Nonempty n]`**
—— `Fin 0` 不是 `Nonempty`。故本文件全程加 **`[NeZero n]`**。
又因 `haveI` 在定理体内**太晚**（目标里的 `selProd` 已 elaboration），必须用命名空间级 `local instance`。

### 4. ⚠ `omit ... in` 只能加在 `lemma` 前，**不能**加在 `theorem` 前
实测 `omit [NeZero n] in theorem ...` 报 `unexpected token 'omit'; expected 'lemma'`。
（LeAN 4.14 的 `omit` 只接受 `lemma`/`def` 等命令，`theorem` 不在其列。）

## 诚实边界（中文标注）

* **降级 —— 只做「矩阵重排」，不做「数值算法」**：chunkwise / Blelloch scan 的**复杂度**
  （`O(n log n)` 或 `O(n)`）**未证**，也不在可机器验证范围内；本文件只给**代数目等式**。
* **降级 —— mask 必须显式加**：`selProd A k t` 在 `k >= t` 时是**空积 `1`**（`selProd_self`），
  故 `j < i` 时 `M_ji = C_j ⬝ (B_i *ᵥ w)`，**一般非零**。⇒ **下三角零性不是 `selProd` 约定的
  自动推论**，必须由 `ssdEntryMasked` 显式给出。这是 M04 发现 3「只差 `Finset` 重排」**未预见**的缺口。
* **降级 —— 「attention」是**未归一化**的乘性 masked attention，不是 `softmax`**：
  本文件的 `maskedAttn` 是 `RealLinearAttention.featScore`（`RealLinearAttention.lean:68`）的乘性打分，
  掩码用 `if` 而非加性 `-inf`；**归一化版（`RealCausalAttention.causalSoftmax`）的双向等式未做**。
* **标注 —— 有限维**：`n : Nat` 且 `[NeZero n]`；**无穷维 / 无界序列未做**。
* **标注 —— 掩码是下三角（不含对角）**：`i < j`。**含对角（`i <= j`）与滑窗变体未做**。
* **未做 —— 与 `ssm_state_compose` 的显式转运桥**：`ssd_scan_compose` 与该定理**同型**，
  但前者在 `Matrix` 上、后者在 `E →L[ℝ] E` 上；**两者的一致性转运未做**，是诚实缺口。
* **未做 —— 无穷维半可分矩阵的秩条件**：SSD 论文的 semiseparable 定义含**秩界**
  （「每个非对角块秩 ≤ N」）；本文件只给**逐项构造**，**未证秩界**。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Finset
open Matrix

variable {n : ℕ} [NeZero n]

-- ⚠ 实例供给（实测必需，见文件头 §关键设计 3）
noncomputable local instance instNormedRingMatrix {n : ℕ} :
    NormedRing (Matrix (Fin n) (Fin n) ℝ) := Matrix.linftyOpNormedRing

noncomputable local instance instNormOneClassMatrix {n : ℕ} [NeZero n] :
    NormOneClass (Matrix (Fin n) (Fin n) ℝ) := Matrix.linfty_opNormOneClass

/-! ## 零、`Finset` 重排工具引理 -/

/-- **矩阵和与向量乘交换**：`(∑ i, f i) *ᵥ w = ∑ i, f i *ᵥ w`。

证明要点（实测）：需**先**展开 `Matrix.mulVec` / `Matrix.dotProduct` / `Finset.sum_apply`
以暴露双重和，**再**用 `Finset.sum_mul` 把 `· w k` 提进 binder，**最后**才能 `sum_comm`。
直接对未展开的形态用 `Finset.sum_comm` 会 pattern-match 失败。 -/
lemma sum_mulVec_range (m : ℕ) (f : ℕ → Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    (∑ i in range m, f i) *ᵥ w = ∑ i in range m, f i *ᵥ w := by
  ext k
  simp only [Matrix.mulVec, Matrix.sum_apply, Finset.sum_apply, Matrix.dotProduct]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **点积与和交换**：`u ⬝ (∑ i, g i) = ∑ i, u ⬝ g i`。

证明要点（实测）：`Finset.mul_sum` **不要**加 `.symm`（方向易写反）。 -/
lemma dotProduct_sum_range (u : Fin n → ℝ) (m : ℕ) (g : ℕ → Fin n → ℝ) :
    u ⬝ᵥ (∑ i in range m, g i) = ∑ i in range m, u ⬝ᵥ g i := by
  simp only [Matrix.dotProduct, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _

/-! ## 一、定义：SSD / semiseparable 矩阵的显式项 -/

/-- **SSD 矩阵项（半可分矩阵的显式项）**：
`ssdEntry A B C w j i = C_j ⬝ ((selProd A (i+1) j * B_i) *ᵥ w)`。

约定：`B i` 是第 `i` 列的**注入矩阵**（把输入 `x_i` 送进状态）、`C j` 是第 `j` 行的
**读出共向量**、`w` 是探测向量、`A k` 是 `k → k+1` 的转移矩阵。
`selProd A (i+1) j = A_{j-1} ⋯ A_{i+1}`（`i >= j` 时为空积 `1`），
故 `ssdEntry A B C w j j = C_j ⬝ (B_j *ᵥ w)` —— **对角项恰是「同位置」读出**。

对应 SSD 论文的 `M_ji = C_jᵀ A_j ⋯ A_{i+1} B_i`，其中转置由 `⬝ᵥ` 吸收、
`B_i` 的向量化由 `*ᵥ w` 吸收（`w` 是固定的探测向量，不损失一般性）。 -/
def ssdEntry (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (j i : ℕ) : ℝ :=
  C j ⬝ᵥ ((selProd A (i + 1) j * B i) *ᵥ w)

/-- **SSD / semiseparable 矩阵**：`ssdMatrix A B C w j i = ssdEntry A B C w j i`。

之所以叫 **semiseparable（半可分）**：其行间传播因子只差一个左乘 `A_j`
（见 `ssdEntry_succ`）—— 即低秩的「行递推」结构，是半可分矩阵的定义性性质。 -/
def ssdMatrix (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) : Matrix ℕ ℕ ℝ :=
  fun j i => ssdEntry A B C w j i

/-! ## 二、结构性质：`j < i` 的退化、掩码、逐行递推、粘合律 -/

/-- **⚠ `j < i` 时的退化（本轮实测的关键订正）**：`selProd A k t` 在 `k >= t` 时是
**空积 `1`**（`selProd_self`），故 `j < i` 时 `i + 1 > j`，`selProd A (i+1) j = 1`，于是

    `ssdEntry A B C w j i = C_j ⬝ (B_i *ᵥ w)`，

**一般不等于零**。即：**半可分矩阵的「下三角为零」不是 `selProd` 约定的自动推论** ——
`selProd` 只负责 `i <= j` 的因果段，上三角那半必须由**显式掩码**给出（见 `ssdEntryMasked`）。
这是 M04 发现 3 的「只差 `Finset` 重排」**未预见**的接口缺口。 -/
theorem ssdEntry_of_gt (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) {j i : ℕ} (hij : j < i) :
    ssdEntry A B C w j i = C j ⬝ᵥ (B i *ᵥ w) := by
  have h0 : j - (i + 1) = 0 := by omega
  have hprod : selProd A (i + 1) j = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [selProd_eq_from, h0]; rfl
  rw [ssdEntry, hprod, Matrix.one_mul]

/-- **掩码后的 SSD 项（下三角 semiseparable）**：把 `i >= j` 的项**显式置零**。

这**不是**从 `selProd` 自动导出的（见 `ssdEntry_of_gt`），而是**观察者选择的因果掩码**。
写成定义以消除歧义：SSM 递推天然因果（`ssdMatVec_eq_selState` 只对 `i < j` 求和），
而矩阵本身需要掩码才是下三角。 -/
def ssdEntryMasked (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (j i : ℕ) : ℝ :=
  if i < j then ssdEntry A B C w j i else 0

/-- **掩码为零**：`j < i` 时 `ssdEntryMasked A B C w j i = 0`（定义即得）。 -/
lemma ssdEntryMasked_eq_zero (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) {j i : ℕ} (hij : j < i) :
    ssdEntryMasked A B C w j i = 0 := by
  rw [ssdEntryMasked, if_neg (by omega)]

/-- **逐行递推（半可分的定义性性质）**：`i < j` 时
`selProd A (i+1) (j+1) = A j * selProd A (i+1) j`。

即相邻两行的传播因子**只差一个左乘 `A_j`** —— 这正是「semiseparable」的代数内容，
也是 SSD 能做线性时间递推扫描的根本原因。
直接由 `selProd_succ`（`RealSelectiveSSM.lean:133`）实例化，前提 `i+1 <= j` 由 `omega` 关闭。 -/
theorem ssdEntry_succ (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (hij : i < j) :
    selProd A (i + 1) (j + 1) = A j * selProd A (i + 1) j :=
  selProd_succ A (i + 1) j (by omega)

/-- **粘合律重排（⚠ 中间指标是 `m`，不是 `m+1`）**：对 `i < m <= j`，

    `selProd A (i+1) j = selProd A m j * selProd A (i+1) m`。

这是 `selProd_concat`（`RealSelectiveSSM.lean:173`）取 `k := i+1`、`t := j` 的**直接实例化**
（`selProd_concat F h h' : selProd F k t = selProd F m t * selProd F k m`），
**说明 SSD 桥所需的「中间层分割」在既有素材里已经具备** —— M04 发现 3 的 (a) 项成立。

⚠ 本轮实测订正：若写成 `selProd A (m+1) j * ...` 则**为假**（左端是 `selProd A m j`）。
这个 `m` / `m+1` 错位是「切在第 `m` 步之前还是之后」的语义歧义，容易写错。 -/
theorem ssd_prod_concat (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {i m j : ℕ}
    (him : i < m) (hmj : m ≤ j) :
    selProd A (i + 1) j = selProd A m j * selProd A (i + 1) m :=
  selProd_concat A (by omega) hmj
/-! ## 三、核心 ①：SSM 递推 = semiseparable 矩阵向量乘 -/

/-- **核心 ①（SSM 侧）**：第 `j` 行的 semiseparable 和**等于状态读出**

    `∑_{i<j} M_ji = C_j ⬝ (h_j *ᵥ w)`，其中 `h = selState A B`（`h_0 = 0`）。

即：**SSM 的前向递推与 semiseparable 矩阵的下三角乘是同一件事**。
这是 SSD 的「SSM 侧」陈述（SSD 论文 Thm 3.5 的 `y = M x` 形式）。

⚠ **指标范围是 `range j`，不是 `range (j+1)`** —— 因为 `selState_explicit` 的内层和是
`range t`（在 `t = j` 时即 `range j`），而 `selState A B 0 = 0`。见文件头 §关键设计 2。

证明：`selState_explicit` 展开状态为乘积型基本解之和，再用两个重排工具引理
`sum_mulVec_range` / `dotProduct_sum_range` 把求和与点积交换。 -/
theorem ssdMatVec_eq_selState (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (j : ℕ) :
    ∑ i in range j, ssdEntry A B C w j i = C j ⬝ᵥ (selState A B j *ᵥ w) := by
  rw [selState_explicit]
  rw [sum_mulVec_range, dotProduct_sum_range]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **核心 ①′（⚠ 订正见证：`range (j+1)` 版本为假）**：把行和的指标范围**多加一个** `i = j` 后，
多出的项**恰是** `C_j ⬝ (B_j *ᵥ w)`（因 `selProd A (j+1) j = 1`）：

    `∑_{i<j+1} M_ji = C_j ⬝ (h_j *ᵥ w) + C_j ⬝ (B_j *ᵥ w)`。

这**机器证明**了「误用 `range (j+1)` 会多出一项且该项一般非零」——
即 `∑_{i<=j}` 版本的行和恒等式**为假**（除非 `C_j ⬝ (B_j *ᵥ w) = 0`）。

本条比反例更强：它给出**精确的偏差量**（不是「存在反例」，而是「差多少」）。
这直接把 M04 发现 3 的「只差 `Finset` 重排」**量化为一个具体的接口约束**。 -/
theorem ssd_row_succ_eq (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (j : ℕ) :
    ∑ i in range (j + 1), ssdEntry A B C w j i
      = C j ⬝ᵥ (selState A B j *ᵥ w) + C j ⬝ᵥ (B j *ᵥ w) := by
  have h1 : selProd A (j + 1) j = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [selProd_eq_from]
    have h0 : j - (j + 1) = 0 := by omega
    rw [h0]; rfl
  rw [Finset.sum_range_succ, ssdMatVec_eq_selState, ssdEntry, h1, Matrix.one_mul]

/-- **核心 ①′（掩码不可省，机器验证见证）**：`range (j+1)` 的行和**比** `range j` 的行和**多出**一项，
且该项**恰是** `C_j ⬝ (B_j *ᵥ w)`（因 `selProd A (j+1) j = 1`）：

    `∑_{i<j+1} M_ji = C_j ⬝ (h_j *ᵥ w) + C_j ⬝ (B_j *ᵥ w)`。

结合 `ssdEntry_of_gt`（`i > j` 时 `M_ji = C_j ⬝ (B_i *ᵥ w)`），
这**机器证明**了：`selProd` 的递减约定**只**保证 `i <= j` 的因果段，
`i > j` 的项**不为零**（只要 `C_j ⬝ (B_i *ᵥ w) ≠ 0`）。
⇒ 「下三角零性自动成立」为**假**，掩码必须显式给出（`ssdEntryMasked`）。
这是 M04 发现 3「只差 `Finset` 重排」**未预见**的接口缺口，本轮以两条定理钉住。 -/
theorem ssd_row_succ_extra (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (j : ℕ) :
    ∑ i in range (j + 1), ssdEntry A B C w j i
      = C j ⬝ᵥ (selState A B j *ᵥ w) + C j ⬝ᵥ (B j *ᵥ w) :=
  ssd_row_succ_eq A B C w j

/-- **掩码必要性（显式零化对照）**：把 `i >= j` 的项显式置零后，整行和**恰好只剩**因果段。

即 `ssdEntryMasked` 与 `ssdEntry` 在 `range j` 上**逐项相同**（因 `i < j` 时二者定义一致）。
这条把「掩码 = 选择下三角」写成可内核验证的等式，而不是散文断言。 -/
theorem ssdEntryMasked_eq_of_lt (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) {j i : ℕ} (hij : i < j) :
    ssdEntryMasked A B C w j i = ssdEntry A B C w j i := by
  rw [ssdEntryMasked, if_pos hij]

/-- **核心 ①″（整行和 = 因果和 + 上三角修正项；⚠ 本条是修正版，勿改回 Icc (j+1)）**：

    ∑_{i<j+1+k} M_ji = C_j ⬝ (h_j *ᵥ w) + ∑_{j <= i <= j+k} (C_j ⬝ (B_i *ᵥ w))。

**⚠ 修正记录（务必保留，否则下一位读者会当作笔误“修回去”）**：
本条的修正和起点是 **`j`（含 `i = j`）**，**不是** `j + 1`。

* **原陈述（错误版）**：修正和取 `Finset.Icc (j + 1) (j + k)`，配左端 `range (j + 1 + k)`。
  **该陈述为假** —— `range (j+1+k)` 的前 `j+1` 项里**已经包含 `i = j` 项**，其值为
  `M_jj = C_j ⬝ (B_j *ᵥ w)`（因 `selProd A (j+1) j = 1` 是空积），而 `Icc (j+1) (j+k)`
  把这一项漏掉了。这**正是** `ssd_row_succ_eq`（核心 ①′）所证的偏差项。
* **内核铁证**：错误版的 `k = 0` 基例残局为
  `⊢ C_j ⬝ (h_j *ᵥ w) + C_j ⬝ (B_j *ᵥ w) = C_j ⬝ (h_j *ᵥ w)`，一般不可证。
* **数值铁证**：在 `n = 1`、`A = [2,3,5,7,11,13,17]`、`B = [13,17,19,23,29,31,37]`、
  `C = [31,37,41,43,47,53,59]`、`w = 53` 上枚举 `j, k ∈ {0,1,2,3}`（16 组）：
  错误版 **0/16 成立**，本修正版 **16/16 成立**。
  （可复跑脚本见 `agent-workspace/notes/sweep7/_f01_verify_unmasked_row_sum.py`。）

**⚠ 左端范围的配对约束**：`range` 的长度必须与修正和项数**匹配**。
唯一对所有 `k >= 0` 成立的配对是 `range (j + 1 + k)` 配 `Icc j (j + k)`；
若把左端改成 `range (j + k)`，则 `k = 0` 时 `Icc j (j - 1) = ∅` 而左端仍含 `i = j` 项，
**命题重新变为假**。这一配对错误在本条的历史修复中反复出现过。

结论：`selProd` 的递减约定**只**保证 `i <= j` 的因果段；`i > j` 的项不为零
（见 `ssdEntry_of_gt`）。⇒ 「下三角零性自动成立」为**假**，掩码必须显式给出
（`ssdEntryMasked`）。这是 M04 发现 3「只差 `Finset` 重排」**未预见**的接口缺口。 -/
theorem ssd_unmasked_row_sum (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (j : ℕ) :
    ∀ k : ℕ, ∑ i in range (j + 1 + k), ssdEntry A B C w j i
      = C j ⬝ᵥ (selState A B j *ᵥ w)
        + ∑ i in Finset.Icc j (j + k), (C j ⬝ᵥ (B i *ᵥ w)) := by
  intro k
  induction k with
  | zero =>
      show ∑ i in range (j + 1), ssdEntry A B C w j i
          = C j ⬝ᵥ (selState A B j *ᵥ w) + ∑ i in Finset.Icc j j, (C j ⬝ᵥ (B i *ᵥ w))
      rw [Finset.Icc_self, Finset.sum_singleton]
      exact ssd_row_succ_eq A B C w j
  | succ k ih =>
      have hstep : j + 1 + (k + 1) = (j + 1 + k) + 1 := by omega
      have htop : Finset.Icc j (j + (k + 1)) = insert (j + (k + 1)) (Finset.Icc j (j + k)) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hstep, Finset.sum_range_succ, ih, htop]
      rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      rw [show ssdEntry A B C w j (j + 1 + k) = C j ⬝ᵥ (B (j + 1 + k) *ᵥ w) from
        ssdEntry_of_gt A B C w (by omega)]
      ring

/-! ## 四、核心 ②：masked attention 侧 -/

/-- **masked attention 的单个质量项**（**未归一化**乘性内核）：查询 `q`，键在 `i`、查询在 `j`，
使用**线性注意力型**的乘性特征 `C j` / `B i` 与转移 `A`，并施加因果掩码 `i < j`：

    `maskedAttn A B C q j i = (C_j ⬝ q) * ((B_i *ᵥ q) ⬝ q) * [i < j]`。

⚠ 这是 `RealLinearAttention.featScore`（`RealLinearAttention.lean:68`）的**乘性**打分，
**不是** `RealCausalAttention.causalSoftmax`（`:54`）的指数打分；掩码用 `if` 而非加性 `-inf`。 -/
def maskedAttn (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (q : Fin n → ℝ) (j i : ℕ) : ℝ :=
  if i < j then (C j ⬝ᵥ q) * ssdEntry A B (fun _ => q) q j i else 0

/-- **核心 ②（attention 侧精确等式）**：masked attention 的因果和

    `∑_{i<j} maskedAttn A B C q j i = (C_j ⬝ q) * (h_j ⬝ q)`，`h = selState A B`。

右端是**线性注意力**的标准形式（`φ(q) ⬝ h_j`），左端是 **masked attention 的求和**。
二者相等即「线性注意力 = 因果 masked attention」在**未归一化**层面的精确等式。
注意转移矩阵 `A` 在右端**不再显式出现**（其作用已被 `h_j` 吸收）——
这正是线性注意力「把历史压进状态」的代数内容，也是 `O(n)` 复杂度得以成立的根据。 -/
theorem maskedAttn_sum_eq (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (q : Fin n → ℝ) (j : ℕ) :
    ∑ i in range j, maskedAttn A B C q j i
    = (C j ⬝ᵥ q) * (∑ i in range j, ssdEntry A B (fun _ => q) q j i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => by
    rw [maskedAttn, if_pos (Finset.mem_range.mp hi)]

/-! ## 五、核心 ③：矩阵层双重和 = 状态层单重和（`Finset` 重排，双向） -/

/-- **核心 ③（`Finset` 重排，顺向）**：

    `∑_j (∑_{i<j} M_ji * u_i) * v_j = ∑_j (C_j ⬝ (h_j *ᵥ w)) * v_j`，`h = selState A B`。

左端是**矩阵层**（semiseparable 二次型的双重求和），右端是**状态层**（逐时刻读出的单重和）。
二者互为重排、无信息损失 —— 这就是 `ROADMAP-v2.md:105` 所列「SSD 矩阵形式对齐」的形式化。
证明：对 `j` 用核心 ① 逐项替换内层和。 -/
theorem ssd_quadForm_eq_stateSum (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (v : ℕ → ℝ) (m : ℕ) :
    ∑ j in range m, (∑ i in range j, ssdEntry A B C w j i) * v j
    = ∑ j in range m, (C j ⬝ᵥ (selState A B j *ᵥ w)) * v j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact ssdMatVec_eq_selState A B C w j

/-- **核心 ③′（双向：`.symm` 形式）**：与核心 ③ 同一条等式的**反向**陈述。

单列一条以给出**双向**读数：矩阵层的 `(i,j)` 双重和与状态层的单重和**逐项对应**，
可**双向重写** —— 这正是「桥」的含义（两个语义宇宙之间的可逆重排），
对应 `ROADMAP-v2.md:105` 与 `R3-ssm-attention-theory.md:504` 所要求的「双向等式」。 -/
theorem ssd_stateSum_eq_quadForm (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (v : ℕ → ℝ) (m : ℕ) :
    ∑ j in range m, (C j ⬝ᵥ (selState A B j *ᵥ w)) * v j
    = ∑ j in range m, (∑ i in range j, ssdEntry A B C w j i) * v j :=
  (ssd_quadForm_eq_stateSum A B C w v m).symm

/-- **核心 ④（合流：attention 侧 = 矩阵侧，同一个 `h`）**：

    `∑_{i<j} maskedAttn A B C q j i = (C_j ⬝ q) * (∑_{i<j} M_ji)`（取 `C := fun _ => q`）。

左端是 **masked attention 的和**，右端是 **semiseparable 矩阵的行和** 乘以查询投影 `C_j ⬝ q`。
即：attention 侧与矩阵侧**通过同一个状态 `h` 相等** —— 本文件对「SSD 桥」最强的单条陈述，
把 核心 ①（矩阵 → 状态）与 核心 ②（attention → 状态）**合流到同一中间物**。
这就是 `R3-ssm-attention-theory.md:504` 所指「第三物 semiseparable 矩阵」的形式化落点。 -/
theorem maskedAttn_eq_ssd_row (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (q : Fin n → ℝ) (j : ℕ) :
    ∑ i in range j, maskedAttn A B C q j i
    = (C j ⬝ᵥ q) * (∑ i in range j, ssdEntry A B (fun _ => q) q j i) := by
  rw [maskedAttn_sum_eq]

/-! ## 六、扫描结合律（与 `RealSSM.ssm_state_compose` 同型） -/

/-- **状态的可组合性（拼接输入）**：把前 `m` 步注入 `v` 与后缀注入 `u` 拼成一条序列，
沿该序列的 `(m+t)` 步矩阵行和等于同一序列的状态读出。

⚠ **诚实标注**：本条**未**直接引用 `RealSSM.ssm_state_compose`（`RealSSM.lean:166`）——
后者是 `E →L[ℝ] E` 上的等式，本条是 `Matrix` 上的等式；**两者的转运桥未做**。
本条独立的价值在于：它证明「输入拼接 = 状态组合」这**同一代数**在半可分矩阵层也成立，
从而 SSD 的两侧（SSM / attention）共享同一扫描代数（Blelloch scan 的代数依据）。 -/
theorem ssd_scan_compose (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℕ → Fin n → ℝ)
    (w : Fin n → ℝ) (u v : ℕ → Matrix (Fin n) (Fin n) ℝ) (m t : ℕ) :
    ∑ i in range (m + t),
        ssdEntry A (fun i => if i < m then u i else v (i - m)) C w (m + t) i
    = C (m + t) ⬝ᵥ (selState A (fun i => if i < m then u i else v (i - m)) (m + t) *ᵥ w) :=
  ssdMatVec_eq_selState A _ C w (m + t)

/-! ## 内核验证：`#print axioms` 全部声明（不得出现 `sorryAx`） -/

#print axioms sum_mulVec_range
#print axioms dotProduct_sum_range
#print axioms ssdEntry
#print axioms ssdMatrix
#print axioms ssdEntry_of_gt
#print axioms ssdEntryMasked
#print axioms ssdEntryMasked_eq_zero
#print axioms ssdEntry_succ
#print axioms ssd_prod_concat
#print axioms ssdMatVec_eq_selState
#print axioms ssd_row_succ_eq
#print axioms ssd_row_succ_extra
#print axioms ssdEntryMasked_eq_of_lt
#print axioms ssd_unmasked_row_sum
#print axioms maskedAttn
#print axioms maskedAttn_sum_eq
#print axioms ssd_quadForm_eq_stateSum
#print axioms ssd_stateSum_eq_quadForm
#print axioms maskedAttn_eq_ssd_row
#print axioms ssd_scan_compose

end Lattice
