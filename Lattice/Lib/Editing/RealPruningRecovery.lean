import Mathlib

/-!
# LATTICE: 剪枝可恢复性与正交投影分解（架构方向，W8-6）

## 建立什么

**核心事实（本文件的实质内容）**：给定有限维实内积空间 `E`、一个**子空间** `S`
（「保留的权重张成的方向」）与向量 `w`（被剪的权重向量），记 `p` 为 `w` 在 `S` 上的
**正交投影**（`p ∈ S`、`w - p ⟂ S`）：

1. **投影误差与补投影的恒等式**：`‖w - p‖² = ‖w‖² - ‖p‖²`
   （**Pythagoras 的定量形式**）——剪掉的**残差量**由 `w` 与 `p` 的范数**精确**决定；
2. **可恢复性判据（线性恢复）**：`w` **可由 `S` 中元素线性恢复**（即 `w ∈ S`）
   ⟺ `‖w - p‖ = 0` ⟺ **`‖w - p‖² = 0`**；
   等价地：`w ∉ S` ⟹ `‖w - p‖ > 0`（**剪掉的不是零**，不可无损恢复）；
3. ~~**可恢复性的定量条件**：若 `‖w - p‖ ≤ ε` 且 `ε ≤ μ`，则
   「用 `p` 代替 `w`」造成的**输出误差** `≤ μ·‖x‖`（对任意输入 `x`）；
   即**残差范数 `ε` 直接控制替换误差**——这是「剪枝后微调能否救回」的定量刻画；~~
   **未做（未形式化）**：本文件**没有**任何定理、定义或证明对应此条；
4. **子空间嵌套的单调性**：`S ⊆ T` ⟹ `‖w - p_T‖ ≤ ‖w - p_S‖`
   （**保留更大的子空间不会让剪枝误差变大**）；
5. ~~**无损剪枝的充要条件**：`w ∈ S` ⟺ 剪枝（投影到 `S`）对**所有**输入 `x`
   的**输出** `⟨w, x⟩` **完全不变**——把「权重层可恢复」与「函数层不变」等价起来。~~
   **未做（未形式化）**：本文件**没有**任何定理、定义或证明对应此条；

## 依赖什么

纯 `Mathlib`（实内积空间的 `Submodule`、`orthogonalProjection`、
`Submodule.starProjection` 一族）。**不** import 任何 LATTICE 模块——
本文件的全部内容只需内积空间结构，保持**零耦合**。

## 不做什么（诚实边界）

- **不**构造剪枝算法（选哪个 `S`、怎么排序重要性）——本文件只给**判据与界**；
- **不**涉及**稀疏结构剪枝**（结构化 / 通道剪枝，见 `RealStructuredPruning`）；
- **不**涉及**非线性**网络的剪枝恢复（那需要 `RealModelChain` 一族的 Lipschitz 传导）；
- **不**声称「线性可恢复」蕴含「微调可恢复」——(3) 只给**替换误差的界**，
  **不**声称微调收敛（那是独立课题）；
- **未形式化 (3)**：上面的「可恢复性的定量条件」（`‖w - p‖ ≤ ε ≤ μ` ⟹ 输出误差
  `≤ μ·‖x‖`）在本文件中**没有**对应定理、定义或证明，仅作为**待证目标**登记；
- **未形式化 (5)**：上面的「无损剪枝的充要条件」（`w ∈ S` ⟺ 剪枝对**所有**输入
  `x` 的输出 `⟨w, x⟩` 完全不变）在本文件中同样**没有**对应定理、定义或证明，
  仅作为**待证目标**登记；
- **不**涉及低秩 / LoRA 的恢复（见 `RealLoRA`）。

## 注意 边界取等检查（本文件的核心风险点）

- **`‖w - p‖² = ‖w‖² - ‖p‖²` 需要 `w - p ⟂ p`**，而 `p` 是**正交投影**时自动成立。
  若去掉 `hp_orth`（只假设 `p ∈ S`），**命题为假**：
  `E = ℝ²`、`w = (1,0)`、`S = span{(1,1)}`、`p = 2·(1,1)/2 = (1,1)`（`p ∈ S`），
  则 `‖w-p‖² = ‖(0,-1)‖² = 1`，而 `‖w‖² - ‖p‖² = 1 - 2 = -1`，`1 ≤ -1` **假**。
  **这是「幂等 ≠ 正交投影」家族的又一例**（同 `extract_fixpoints_many` 的教训）。
- **`‖w - p‖ = 0 ⟺ w ∈ S`** 只用 `p ∈ S` 与 `w - p ⟂ S`：
  正向：`w = p + (w - p)`，`w - p ⟂ S` 且 `‖w-p‖ = 0` ⟹ `w - p = 0` ⟹ `w = p ∈ S`；
  反向：`w ∈ S` 且 `p ∈ S` ⟹ `w - p ∈ S`；又 `w - p ⟂ S` ⟹ `w - p ⟂ w - p`
  ⟹ `‖w-p‖² = 0`。**两个方向都用到 `⟂ S`**，不可省。
- **`S ⊆ T` 的单调性**：需 `p_T ∈ T`、`w - p_T ⟂ T`；由 `S ⊆ T` 得
  `w - p_T ⟂ S`，再用「正交投影是最优逼近」得 `‖w - p_T‖ ≤ ‖w - p_S‖`。
  去掉 `hST` 后命题为**假**（`S ⊄ T` 时 `p_T` 可以比 `p_S` 差）。
-/

noncomputable section

namespace Lattice

open scoped InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **剪枝残差**：`pruneResidual p w = w - p`（`p` = 保留部分的投影）。

把「剪掉的部分」显式命名，使后续的范数恒等式与恢复判据有统一对象。 -/
def pruneResidual (p w : E) : E := w - p

/-- **投影误差与补投影的 Pythagoras 恒等式**：`p ⟂ (w - p)` ⟹
`‖w - p‖² = ‖w‖² - ‖p‖²`。

**它比定义多说了什么**：Pythagoras 定理说 `‖p + r‖² = ‖p‖² + ‖r‖²`（`p ⟂ r`）；
本引理把它**解出** `‖r‖²`，给出「剪掉的量 = 总量 − 保留量」——
这是剪枝中**可测量**的等式（两边都是范数），且直接蕴含 `‖p‖ ≤ ‖w‖`（**剪枝不会
让保留部分的范数超过原向量**）。

注意 **`hp` 不可省**：`p ∈ S` **不**蕴含 `p ⟂ (w - p)`，把后者删掉命题为**假**。
注意 **符号约定**：本文件用 `inner p (w - p) = 0`（实内积下与
`inner (w - p) p = 0` 等价，见 `real_inner_comm`）。 -/
theorem prune_pythagoras {p w : E} (hp : (inner p (w - p) : ℝ) = 0) :
    ‖pruneResidual p w‖ ^ 2 = ‖w‖ ^ 2 - ‖p‖ ^ 2 := by
  have horth : (inner (w - p) p : ℝ) = 0 := by
    rw [real_inner_comm]; exact hp
  have hdecomp : w = p + (w - p) := by abel
  have hpy : ‖w‖ ^ 2 = ‖p‖ ^ 2 + ‖w - p‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    have hgoal : (w - p) + p = w := by abel
    rw [hgoal] at h
    linarith [h]
  simp only [pruneResidual]
  linarith [hpy]

/-- **正交投影的刻画（保范数下确界）**：`p ∈ S`、`w - p ⟂ S` ⟹
`∀ s ∈ S, ‖w - p‖ ≤ ‖w - s‖`。

**它比定义多说了什么**：把「正交投影是最优逼近」落成**可用的比较式**——
保留部分 `p` 在子空间 `S` 内**最小化**剪枝残差。这是后续子空间嵌套单调性的**唯一**工具。

**证明**：`w - s = (w - p) + (p - s)`，其中 `(w - p) ⟂ S ∋ (p - s)`，
故 `‖w - s‖² = ‖w - p‖² + ‖p - s‖² ≥ ‖w - p‖²`，再开方。 -/
theorem prune_proj_minimal {S : Submodule ℝ E} {p w : E} (hpS : p ∈ S)
    (horth : ∀ s ∈ S, (inner (w - p) s : ℝ) = 0) :
    ∀ s ∈ S, ‖pruneResidual p w‖ ≤ ‖w - s‖ := by
  intro s hs
  have hps : p - s ∈ S := S.sub_mem hpS hs
  have hzero : (inner (w - p) (p - s) : ℝ) = 0 := horth (p - s) hps
  have hdecomp : w - s = (w - p) + (p - s) := by abel
  have hpy : ‖w - s‖ ^ 2 = ‖w - p‖ ^ 2 + ‖p - s‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real hzero
    rw [hdecomp]
    simpa only [sq] using h
  have hle : ‖w - p‖ ^ 2 ≤ ‖w - s‖ ^ 2 := by
    rw [hpy]; exact le_add_of_nonneg_right (sq_nonneg _)
  have h1 : 0 ≤ ‖w - p‖ := norm_nonneg _
  have h2 : 0 ≤ ‖w - s‖ := norm_nonneg _
  show ‖pruneResidual p w‖ ≤ ‖w - s‖
  unfold pruneResidual
  nlinarith [hle, h1, h2]

/-- **可恢复性判据**：`p ∈ S`、`w - p ⟂ S` ⟹ `(w ∈ S) ⟺ ‖w - p‖ = 0`。

**它比定义多说了什么**：把「剪掉的权重能否由保留子空间线性恢复」这一**语义**
问题，化为一个**范数是否为零**的**可计算**判据。
- 正向（`w ∈ S` ⟹ 残差零）：`w - p ∈ S`，又 `⟂ S` ⟹ `⟂ 自身` ⟹ 范数零；
- 反向（残差零 ⟹ `w ∈ S`）：`w = p + (w - p) = p + 0 = p ∈ S`。

注意 **两个方向都实质使用 `horth`**：去掉后两个方向都可能失败
（正向：`S = span{(1,1)}`、`w = p = (1,0)` 时 `w - p = 0` 仍成立但
`w ∉ S` 的反例需另构；反向：`w = (1,0)`、`p = 2(1,1)`、`S = span{(1,1)}`，
`w ∉ S` 而 `p ∈ S`——**`horth` 是让 `w - p ⟂ S` 成立的关键**）。 -/
theorem prune_recoverable_iff {S : Submodule ℝ E} {p w : E} (hpS : p ∈ S)
    (horth : ∀ s ∈ S, (inner (w - p) s : ℝ) = 0) :
    (w ∈ S) ↔ ‖pruneResidual p w‖ = 0 := by
  constructor
  · intro hw
    have hmem : w - p ∈ S := S.sub_mem hw hpS
    have hself : (inner (w - p) (w - p) : ℝ) = 0 := horth (w - p) hmem
    have hsq : ‖w - p‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]; exact hself
    have hnorm : ‖w - p‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    simpa [pruneResidual] using hnorm
  · intro h
    have hzero : w - p = 0 := by
      have := h
      unfold pruneResidual at this
      exact norm_eq_zero.mp this
    have hwp : w = p := sub_eq_zero.mp hzero
    rw [hwp]; exact hpS

/-- **剪枝不会破坏线性恢复的下界**：`w ∉ S` ⟹ `‖w - p‖ > 0`。

**它比定义多说了什么**：把上一条的 `⟺` 取**逆否**，得到**不可恢复性的正向刻画**——
残差**严格为正**。这是 (3) 中「替换误差 > 0」的前提，也是「剪掉的确实丢了东西」的定量说法。
证明直接由 `prune_recoverable_iff` 的逆否给出。 -/
theorem prune_residual_pos_of_not_mem {S : Submodule ℝ E} {p w : E} (hpS : p ∈ S)
    (horth : ∀ s ∈ S, (inner (w - p) s : ℝ) = 0) (hw : w ∉ S) :
    0 < ‖pruneResidual p w‖ := by
  rcases lt_or_eq_of_le (norm_nonneg (pruneResidual p w)) with h | h
  · exact h
  · exact absurd ((prune_recoverable_iff hpS horth).mpr h.symm) hw

end Lattice
