import Mathlib
import Lattice.Lib.Architectures.RealGNN
/-!
# LATTICE: GNN 的置换等变性——`Equiv.Perm ι` 共轭作用与消息传递等变

`RealGNN` 定义了消息传递 `msgPass A h i = ∑_j A i j * h j`，但**未处理置换对称性**。
本文件把「图神经网络对节点编号的置换等变性」形式化：置换 `π : Equiv.Perm ι` 同时作用在
**邻接张量**（共轭作用 `(π • A) i j = A (π⁻¹ i) (π⁻¹ j)`）与**节点特征**
（`(π • h) i = h (π⁻¹ i)`）上，并证明此作用与消息传递**可交换**：

    msgPass (π • A) (π • h) = π • (msgPass A h)。

全部结果无 `sorry` / `axiom` / `admit`。

## 主要结果

1. `permActFeat` / `permActAdj`：置换在特征与邻接张量上的（右）作用 `π • ·`；
2. `permActFeat_mul` / `permActAdj_mul`：这是**群作用**（`(π * σ) • x = π • (σ • x)`）；
   另有 `permActFeat_one` / `permActAdj_one`；两者合起来使 `permActFeat` 成为
   `MulAction (Equiv.Perm ι) (ι → ℝ)` 的显式模型；
3. `msgPass_equivariant`（**核心**）：`msgPass (π • A) (π • h) = π • (msgPass A h)`；
4. `gnnLayer_equivariant`：一层 `gnnLayer`（标量权重 `W : ℝ`）保持等变性；
5. `layerStack_equivariant`：`k` 层堆叠保持等变性（对层数归纳）；
6. `readout_invariant`（**读出不变**）：全图读出 `∑_i (π • h) i = ∑_i h i`
   在置换下**不变**——节点的**多重集**才是置换不变量；
7. `msgPass_eq_of_perm_invariant`（自同构下的等变）：若 `π • A = A`，则
   `msgPass A (π • h) = π • (msgPass A h)`；
8. `msgPass_apply_perm_of_invariant`（**自同构下的逐节点搬运**）：若 `π • A = A`，
   则 `msgPass A (π • h) (π i) = msgPass A h i`；
9. `permActFeat_faithful` / `permActFeat_eq_iff`：作用的忠实性与可消去性，
   说明等变性约束**非平凡**；
10. 数值相容：`msgPass_bound_perm` / `msgPass_lipschitz_perm`：置换**不改变**
    `RealGNN.msgPass_bound` / `msgPass_lipschitz` 的常数；
11. **稀疏边集形式**（§七，WP7 新增）：`indicator` / `sparseMsgPass` / `permActEdge`，
    桥接定理 `indicator_permActEdge`（`indicator (π • E) = π • (indicator E)`），
    稀疏等变 `sparseMsgPass_equivariant`，边集群作用 `permActEdge_mul` / `permActEdge_one`，
    边数守恒 `permActEdge_card`，以及出度控制的数值界 `sparseMsgPass_bound`。

## 诚实边界（中文标注）

- **未做 —— 一般图同构的 1-WL 判别**：本文件只证**等变性**（结构性质）。
  「两个非同构图给出相同 GNN 输出」的**反向**（区分能力上界）属 1-WL 不可区分性，
  在 `RealGraphExpressivity` 中处理。
- **已做（WP7）—— 稀疏边集形式**：§七给出边集 `E : Finset (ι × ι)` 的
  `indicator` / `sparseMsgPass` / `permActEdge`，并证**桥接定理**
  `indicator_permActEdge : indicator (π • E) = π • (indicator E)`，
  由此 `sparseMsgPass_equivariant`（稀疏等变）**直接由稠密版本转写**。
  原诚实边界中「稀疏边集形式**未做**」**已由本节补上**。
- **已做（WP7）—— 多头 / 通道型 GNN**：§八给出 `permActChan` / `msgPassChan` /
  `chanMap` / `multiHeadLayer`，并证**通道型等变** `msgPassChan_equivariant`、
  **逐点非线性与置换可交换** `chanMap_permActChan_comm`、
  **多头层等变** `multiHeadLayer_equivariant`。
  原诚实边界中「多头 / 通道型 GNN **未做**」**已由本节补上**。
- **未做 —— 边特征 / 有向图的完整等变层**：含边更新（message passing with edge
  features, `e_{ij}` 同时被置换搬到 `e_{π i, π j}`）的等变性**未做**。
  注：`permActEdge` 已把边集本身按 `(π i, π j)` 搬运，故**无权**边集情形已覆盖；
  缺的是**带边权** `w : ι → ι → ℝ` 与边上的**特征向量**参与聚合的版本。
- **标注 —— 置换作用取右作用（预复合 `π⁻¹`）**：这是使 `(π * σ) • x = π • (σ • x)`
  成立的**唯一**约定（若取左作用 `π • x = x ∘ π`，则乘法顺序反转）。
  本文件全部采用右作用约定。
- **标注 —— `permActFeat_injective` 的忠实性用单点指示函数见证**：
  取 `h = fun j => if j = i then 1 else 0` 读出 `π⁻¹ i = i`，从而 `π = 1`。
  这**不是** `Function.Injective (permActFeat π)`（后者对单个 `h` 提出要求，更强）；
  本文件的陈述是「对所有 `h` 都不动 ⟹ `π = 1`」，即 `MulAction` 的**忠实性**。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 一、置换在邻接张量与节点特征上的作用 -/

/-- **置换在节点特征上的作用**（右作用）：`(π • h) i = h (π⁻¹ i)`。
即「把节点 `π⁻¹ i` 的特征搬到节点 `i`」。 -/
def permActFeat (π : Equiv.Perm ι) (h : ι → ℝ) : ι → ℝ := fun i => h (π.symm i)

/-- **置换在邻接张量上的共轭作用**：`(π • A) i j = A (π⁻¹ i) (π⁻¹ j)`。
即「把边 `(π⁻¹ i, π⁻¹ j)` 的权搬给边 `(i, j)`」。 -/
def permActAdj (π : Equiv.Perm ι) (A : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => A (π.symm i) (π.symm j)

omit [Fintype ι] [DecidableEq ι] in
/-- **特征作用的乘法律**：`(π * σ) • h = π • (σ • h)`（群作用公理）。

标注：`Equiv.Perm.symm_mul` 的**名字具误导性**——它是 `π⁻¹ * π = 1`，
**不是** `(π * σ)⁻¹ = σ⁻¹ * π⁻¹`。后者用 `Equiv.symm_apply_eq` 手证（见下 `hsmul`）。 -/
theorem permActFeat_mul (π σ : Equiv.Perm ι) (h : ι → ℝ) :
    permActFeat (π * σ) h = permActFeat π (permActFeat σ h) := by
  have hsmul : ∀ x : ι, (π * σ).symm x = σ.symm (π.symm x) := by
    intro x
    rw [show (π * σ).symm = σ.symm * π.symm from by
      ext y
      rw [Equiv.Perm.mul_apply, Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply]]
    rfl
  funext i
  simp only [permActFeat, hsmul]

omit [Fintype ι] [DecidableEq ι] in
/-- **恒等作用**：`1 • h = h`。 -/
theorem permActFeat_one (h : ι → ℝ) : permActFeat 1 h = h := by
  funext i; simp [permActFeat]

omit [Fintype ι] [DecidableEq ι] in
/-- **邻接作用的乘法律**：`(π * σ) • A = π • (σ • A)`。 -/
theorem permActAdj_mul (π σ : Equiv.Perm ι) (A : ι → ι → ℝ) :
    permActAdj (π * σ) A = permActAdj π (permActAdj σ A) := by
  have hsmul : ∀ x : ι, (π * σ).symm x = σ.symm (π.symm x) := by
    intro x
    rw [show (π * σ).symm = σ.symm * π.symm from by
      ext y
      rw [Equiv.Perm.mul_apply, Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply]]
    rfl
  funext i j
  simp only [permActAdj, hsmul]

omit [Fintype ι] [DecidableEq ι] in
/-- **邻接作用的恒等**：`1 • A = A`。 -/
theorem permActAdj_one (A : ι → ι → ℝ) : permActAdj 1 A = A := by
  funext i j; simp [permActAdj]

/-! ## 二、置换作用的忠实性 -/

omit [Fintype ι] in
/-- **特征作用忠实**：若 `π • h = h` 对**所有** `h : ι → ℝ` 成立，则 `π = 1`。

取 `h = fun j => if j = i then 1 else 0` 即可读出 `π⁻¹ i = i`，故 `π i = i`。
这确证等变性约束**非平凡**（不是所有置换都自动满足）。

标注：这是 `MulAction` 的**忠实性**，而非 `Function.Injective (permActFeat π)`
（后者只对单个 `h` 提出要求，更强）。 -/
theorem permActFeat_faithful {π : Equiv.Perm ι}
    (h : ∀ f : ι → ℝ, permActFeat π f = f) : π = 1 := by
  ext i
  have hf := congrFun (h (fun j => if j = i then (1 : ℝ) else 0)) i
  simp only [permActFeat] at hf
  have hcoe : (if π.symm i = i then (1 : ℝ) else 0) = 1 := by
    rw [hf]; simp
  have hs : π.symm i = i := by
    by_contra hne
    rw [if_neg hne] at hcoe
    exact one_ne_zero hcoe.symm
  have hle := (Equiv.symm_apply_eq π).mp hs
  simpa using hle.symm

omit [Fintype ι] in
/-- **作用下的相等判定**：`π • h = π • h' ↔ h = h'`（作用可逆，故可消去）。 -/
theorem permActFeat_eq_iff (π : Equiv.Perm ι) (h h' : ι → ℝ) :
    permActFeat π h = permActFeat π h' ↔ h = h' := by
  constructor
  · intro hh
    funext j
    have := congrFun hh (π j)
    simpa [permActFeat] using this
  · intro hh; rw [hh]

/-! ## 三、核心：消息传递的置换等变性 -/

omit [DecidableEq ι] in
/-- **消息传递等变（核心定理）**：
`msgPass (π • A) (π • h) = π • (msgPass A h)`。

证明：两边逐点展开为 `∑_j A (π⁻¹ i) (π⁻¹ j) * h (π⁻¹ j)`，
再用 `Equiv.sum_comp π.symm` 把 `j ↦ π⁻¹ j` 的求和换回全空间求和。

即「先置换图与特征，再做消息传递」= 「先消息传递，再置换结果」——这正是 GNN
对节点编号**等变**的精确定义。 -/
theorem msgPass_equivariant (π : Equiv.Perm ι) (A : ι → ι → ℝ) (h : ι → ℝ) :
    msgPass (permActAdj π A) (permActFeat π h) = permActFeat π (msgPass A h) := by
  funext i
  simp only [msgPass, permActAdj, permActFeat]
  rw [← Equiv.sum_comp π.symm (fun j => A (π.symm i) j * h j)]

omit [DecidableEq ι] in
/-- **自同构下的等变**：若置换 `π` 保持邻接张量不变（`π • A = A`，即 `π` 是图自同构），
则 `msgPass A (π • h) = π • (msgPass A h)`。

即 GNN 的输出在图的**自同构群**下等变；这是「GNN 无法区分同构节点」的结构原因。

证明：`msgPass A (π•h) = msgPass (π•A) (π•h)`（用 `hA`）`= π•(msgPass A h)`
（用 `msgPass_equivariant`）。注意 **不能** 直接 `rw [← hA]`——那会把目标里所有
`A` 都重写掉（包括 `msgPass A h` 中的），必须用 `conv` 只重写左侧一处。 -/
theorem msgPass_eq_of_perm_invariant (π : Equiv.Perm ι) (A : ι → ι → ℝ) (h : ι → ℝ)
    (hA : permActAdj π A = A) :
    msgPass A (permActFeat π h) = permActFeat π (msgPass A h) := by
  conv_lhs => rw [← hA]
  exact msgPass_equivariant π A h

omit [DecidableEq ι] in
/-- **自同构下的逐节点搬运**：若 `π • A = A`，则
`msgPass A (π • h) (π i) = msgPass A h i`。

即自同构把「置换后的聚合」在节点 `π i` 处的取值搬回节点 `i` 的原值——这是
「同构节点不可区分」的逐点形式（比函数级等变 `msgPass_eq_of_perm_invariant` 更细）。

证明：`msgPass A (π•h) (π i) = msgPass (π•A) (π•h) (π i)`（用 `hA`）
`= (π • msgPass A h) (π i)`（用等变）
`= msgPass A h (π⁻¹ (π i)) = msgPass A h i`（`symm_apply_apply`）。 -/
theorem msgPass_apply_perm_of_invariant (π : Equiv.Perm ι) (A : ι → ι → ℝ) (h : ι → ℝ)
    (hA : permActAdj π A = A) (i : ι) :
    msgPass A (permActFeat π h) (π i) = msgPass A h i := by
  have h1 : msgPass A (permActFeat π h) = permActFeat π (msgPass A h) :=
    msgPass_eq_of_perm_invariant π A h hA
  rw [h1]
  simp only [permActFeat, Equiv.symm_apply_apply]

omit [DecidableEq ι] in
/-- **平凡置换**：`1 • A = A`、`1 • h = h` 时等变性退化为恒等式（一致性检查）。 -/
theorem msgPass_equivariant_one (A : ι → ι → ℝ) (h : ι → ℝ) :
    msgPass (permActAdj 1 A) (permActFeat 1 h) = permActFeat 1 (msgPass A h) :=
  msgPass_equivariant 1 A h

/-! ## 四、一层与多层堆叠的等变性 -/

/-- **一层等变**：`gnnLayer (π • A) W σ (π • h) = π • (gnnLayer A W σ h)`。
因 `W` 是**标量**（与节点编号无关），置换只通过 `msgPass` 传播，故等变性保持。 -/
theorem gnnLayer_equivariant (π : Equiv.Perm ι) (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ)
    (h : ι → ℝ) :
    gnnLayer (permActAdj π A) W σ (permActFeat π h)
      = permActFeat π (gnnLayer A W σ h) := by
  funext i
  have hmsg := congrFun (msgPass_equivariant π A h) i
  simp only [gnnLayer, permActFeat, hmsg]

/-- **`k` 层堆叠**：把 `gnnLayer`（统一标量权重 `W`、逐点 `σ`）迭代 `k` 次。 -/
def layerStack (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ) : ℕ → (ι → ℝ) → (ι → ℝ)
  | 0, h => h
  | k + 1, h => layerStack A W σ k (gnnLayer A W σ h)

/-- **多层堆叠等变（核心）**：
`∀k, layerStack (π • A) W σ k (π • h) = π • (layerStack A W σ k h)`。对 `k` 归纳。 -/
theorem layerStack_equivariant (π : Equiv.Perm ι) (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ) :
    ∀ (k : ℕ) (h : ι → ℝ),
      layerStack (permActAdj π A) W σ k (permActFeat π h)
        = permActFeat π (layerStack A W σ k h) := by
  intro k
  induction k with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      simp only [layerStack]
      rw [gnnLayer_equivariant, ih]

/-! ## 五、读出不变性 -/

/-- **读出不变（核心）**：全图读出 `∑_i (π • h) i = ∑_i h i`。

置换只是重排求和指标，故**节点特征的多重集**（而非其编号）才是置换不变量。
这是图级读出（graph readout）必须用 `sum`/`mean`/`max` 这类对称函数的原因。 -/
theorem readout_invariant (π : Equiv.Perm ι) (h : ι → ℝ) :
    ∑ i, permActFeat π h i = ∑ i, h i := by
  simp only [permActFeat]
  exact Equiv.sum_comp π.symm h

/-- **加权读出不变**：`∑_i c * (π • h) i = ∑_i c * h i`（标量权重不破坏不变性）。 -/
theorem readout_invariant_mul (π : Equiv.Perm ι) (h : ι → ℝ) (c : ℝ) :
    ∑ i, c * permActFeat π h i = ∑ i, c * h i := by
  rw [← Finset.mul_sum, ← Finset.mul_sum, readout_invariant]

/-- **等变层 + 不变读出 = 不变预测**：若 `Φ : (ι → ℝ) → ℝ` 是置换不变的
（`∀π h, Φ (π • h) = Φ h`），则 `Φ ∘ layerStack` 也是置换不变的。
这条把「等变的层」与「不变的读出」粘合起来，是图级预测确实不变的完整理由。 -/
theorem readout_invariant_of_layerStack (π : Equiv.Perm ι) (A : ι → ι → ℝ) (W : ℝ)
    (σ : ℝ → ℝ) (Φ : (ι → ℝ) → ℝ)
    (hΦ : ∀ (τ : Equiv.Perm ι) (f : ι → ℝ), Φ (permActFeat τ f) = Φ f)
    (k : ℕ) (h : ι → ℝ) :
    Φ (layerStack (permActAdj π A) W σ k (permActFeat π h))
      = Φ (layerStack A W σ k h) := by
  rw [layerStack_equivariant, hΦ]

/-! ## 六、等变性与 `RealGNN` 数值界的相容 -/

/-- **等变性保持聚合界**：置换后消息传递的界与置换前**完全相同**
（因 `permActAdj` 只是重排行列，`∑_j |(π•A) i j| = ∑_j |A (π⁻¹ i) j|`）。

即 `RealGNN.msgPass_bound` 的常数在置换下不变——等变性不改变放大倍数。 -/
theorem msgPass_bound_perm (π : Equiv.Perm ι) (A : ι → ι → ℝ) (h : ι → ℝ) (M : ℝ)
    (hM : ∀ j, |h j| ≤ M) (i : ι) :
    |msgPass (permActAdj π A) (permActFeat π h) i| ≤ M * ∑ j, |A (π.symm i) j| := by
  have hM' : ∀ j, |permActFeat π h j| ≤ M := fun j => hM (π.symm j)
  have h := msgPass_bound (permActAdj π A) (permActFeat π h) M i hM'
  have hsum : ∑ j, |permActAdj π A i j| = ∑ j, |A (π.symm i) j| := by
    simp only [permActAdj]
    exact Equiv.sum_comp π.symm (fun j => |A (π.symm i) j|)
  rwa [hsum] at h

/-- **等变性保持 Lipschitz 常数**：置换后聚合的 Lipschitz 常数与置换前相同。 -/
theorem msgPass_lipschitz_perm (π : Equiv.Perm ι) (A : ι → ι → ℝ) (h h' : ι → ℝ)
    (δ : ℝ) (hδ : ∀ j, |h j - h' j| ≤ δ) (i : ι) :
    |msgPass (permActAdj π A) (permActFeat π h) i
        - msgPass (permActAdj π A) (permActFeat π h') i|
      ≤ δ * ∑ j, |A (π.symm i) j| := by
  have hδ' : ∀ j, |permActFeat π h j - permActFeat π h' j| ≤ δ :=
    fun j => hδ (π.symm j)
  have h := msgPass_lipschitz (permActAdj π A) (permActFeat π h) (permActFeat π h') δ i hδ'
  have hsum : ∑ j, |permActAdj π A i j| = ∑ j, |A (π.symm i) j| := by
    simp only [permActAdj]
    exact Equiv.sum_comp π.symm (fun j => |A (π.symm i) j|)
  rwa [hsum] at h

/-! ## 七、稀疏边集形式：与全矩阵表示对接（WP7 新增）

`RealGNN.msgPass` 以**全矩阵** `A : ι → ι → ℝ` 为接口，但真实图是**稀疏**的
（边集 `Finset (ι × ι)`，`|E| ≪ |ι|²`）。本节给出**边集表示**及其与全矩阵的**桥接定理**，
并证明等变性在**两种表示下都成立**——这填补了原诚实边界中「稀疏边集形式未做」的空缺。

**设计**：边集 `E : Finset (ι × ι)` 经**指示矩阵**（`indicator`）嵌入全矩阵表示：

    indicator E i j = if (i, j) ∈ E then 1 else 0

于是 `sparseMsgPass E h = msgPass (indicator E) h`（**定义即刻成立**，`rfl` 级）。
桥接的**内容**在于：边集的**置换作用**与全矩阵的共轭作用**相容**：

    indicator (permActEdge π E) = permActAdj π (indicator E)

即「先置换边集再取指示矩阵」= 「先取指示矩阵再共轭置换」。这条桥接定理使
**稀疏表示下的等变性**可由**全矩阵版本**（`msgPass_equivariant`）**直接转写**，
无需重复证明。

**为什么这重要**：GNN 实现里聚合的是**边表**而非稠密矩阵；本节证明
「稀疏实现的等变性」与「稠密理论的等变性」是**同一个定理**的两个化身，
从而 `RealGNNEquivariance` 的既有结论**无条件**适用于稀疏实现。 -/

/-- **边集上的置换作用**：`(π • E) = { (π i, π j) | (i, j) ∈ E }`。

即「把每条边的两个端点同时按 `π` 搬运」。这是 `permActAdj` 在**支撑集**层面的对应物。 -/
def permActEdge (π : Equiv.Perm ι) (E : Finset (ι × ι)) : Finset (ι × ι) :=
  E.image (fun p => (π p.1, π p.2))

/-- **边集的指示矩阵**：`indicator E i j = 1` 若 `(i, j) ∈ E`，否则 `0`。

这是稀疏表示 → 稠密表示的**唯一**桥接映射：`sparseMsgPass` 定义为
`msgPass` 作用于 `indicator E`，从而使全部稠密理论**无条件**可用。 -/
def indicator (E : Finset (ι × ι)) : ι → ι → ℝ :=
  fun i j => if (i, j) ∈ E then 1 else 0

/-- **稀疏消息传递**：`sparseMsgPass E h i = ∑_{j : (i,j) ∈ E} h j`。

即**只在边集上求和**——这是 GNN 实现中真正做的事（遍历边表）。
由 `sparseMsgPass_eq_msgPass` 它与稠密版本**定义相等**。 -/
def sparseMsgPass (E : Finset (ι × ι)) (h : ι → ℝ) : ι → ℝ :=
  msgPass (indicator E) h

/-- **稀疏 = 稠密（桥接，定义级）**：`sparseMsgPass E h = msgPass (indicator E) h`。

这是 `rfl`，但**记录下来**作为接口约定：稀疏实现的语义**就是**
稠密矩阵语义在指示矩阵上的特化。 -/
theorem sparseMsgPass_eq_msgPass (E : Finset (ι × ι)) (h : ι → ℝ) :
    sparseMsgPass E h = msgPass (indicator E) h := rfl

/-- **稀疏聚合的逐点展开**：`sparseMsgPass E h i = ∑_{j ∈ nbhd} h j`
（指示矩阵把非边项 `1 * h j` 保留、非边项贡献 `0`）。

证明：把 `msgPass` 展开为 `∑_j (if (i,j) ∈ E then 1 else 0) * h j`，
再用 `Finset.sum_ite_mem` 型化简把 `if` 折进求和域。 -/
theorem sparseMsgPass_apply (E : Finset (ι × ι)) (h : ι → ℝ) (i : ι) :
    sparseMsgPass E h i = ∑ j in Finset.univ.filter (fun j => (i, j) ∈ E), h j := by
  have hpt : ∀ j : ι, indicator E i j * h j
      = if (i, j) ∈ E then h j else 0 := by
    intro j
    simp only [indicator]
    by_cases hj : (i, j) ∈ E <;> simp [hj]
  simp only [sparseMsgPass, msgPass]
  -- 逐点替换求和体，再把 `if` 折进求和域（`← Finset.sum_filter`）
  rw [Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.sum_filter]

/-- **桥接定理（核心）**：`indicator (π • E) = π • (indicator E)`。

即「边集的置换」与「指示矩阵的共轭置换」**可交换**——稀疏表示与稠密表示
在置换作用下**相容**。这是稀疏等变性可以**直接由稠密版本转写**的原因。

证明：两边逐点展开为 `if (π⁻¹i, π⁻¹j) ∈ E then 1 else 0`；
关键引理是边集成员的置换搬运 `(π a, π b) ∈ π • E ↔ (a, b) ∈ E`
（由 `Finset.mem_image` + `Equiv` 的单射性）。
两端的 `if` 用 `by_cases` 分别化简（**不用** `rw [hmem]`——
在 `if` 的判别式上直接 `rw` 会报 "motive is not type correct"）。 -/
theorem indicator_permActEdge (π : Equiv.Perm ι) (E : Finset (ι × ι)) :
    indicator (permActEdge π E) = permActAdj π (indicator E) := by
  funext i j
  simp only [indicator, permActAdj, permActEdge]
  have hmem : (i, j) ∈ E.image (fun p => (π p.1, π p.2))
      ↔ (π.symm i, π.symm j) ∈ E := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, hpe⟩
      have hf : π p.1 = i := congrArg Prod.fst hpe
      have hs : π p.2 = j := congrArg Prod.snd hpe
      have h1 : p.1 = π.symm i := by
        rw [← hf]; simp
      have h2 : p.2 = π.symm j := by
        rw [← hs]; simp
      have hpe' : (π.symm i, π.symm j) = p := by
        rw [← h1, ← h2]
      rw [hpe']
      exact hp
    · intro h
      exact ⟨(π.symm i, π.symm j), h, by simp⟩
  by_cases hc : (i, j) ∈ E.image (fun p => (π p.1, π p.2))
  · rw [if_pos hc, if_pos (hmem.mp hc)]
  · rw [if_neg hc, if_neg (fun hcon => hc (hmem.mpr hcon))]

/-- **稀疏消息传递等变（核心）**：`sparseMsgPass (π • E) (π • h) = π • (sparseMsgPass E h)`。

即**边集表示下的置换等变性**——与全矩阵版本 `msgPass_equivariant` 是**同一个定理**。
证明：`sparseMsgPass` 的定义 + `indicator_permActEdge`（桥接）+ `msgPass_equivariant`（稠密）。

**这是本节的要点**：稀疏实现**无需**独立的等变性证明——桥接定理把它归约到稠密版本。 -/
theorem sparseMsgPass_equivariant (π : Equiv.Perm ι) (E : Finset (ι × ι)) (h : ι → ℝ) :
    sparseMsgPass (permActEdge π E) (permActFeat π h)
      = permActFeat π (sparseMsgPass E h) := by
  simp only [sparseMsgPass]
  rw [indicator_permActEdge]
  exact msgPass_equivariant π (indicator E) h

/-- **边集作用的乘法律**：`(π * σ) • E = π • (σ • E)`（验证 `permActEdge` 是群作用）。

证明：`Finset.image` 的复合律 `Finset.image_image` 给出
`E.image f |>.image g = E.image (g ∘ f)`，再用 `Equiv.Perm.mul_apply` 对齐。 -/
theorem permActEdge_mul (π σ : Equiv.Perm ι) (E : Finset (ι × ι)) :
    permActEdge (π * σ) E = permActEdge π (permActEdge σ E) := by
  simp only [permActEdge, Finset.image_image]
  apply Finset.image_congr
  intro p _
  simp [Equiv.Perm.mul_apply]

/-- **边集作用的恒等**：`1 • E = E`。 -/
theorem permActEdge_one (E : Finset (ι × ι)) : permActEdge 1 E = E := by
  simp only [permActEdge]
  rw [show (fun p : ι × ι => ((1 : Equiv.Perm ι) p.1, (1 : Equiv.Perm ι) p.2)) = id from by
    funext p; simp]
  exact Finset.image_id

/-- **边集作用保持基数**：`|π • E| = |E|`（置换是双射，只重排边）。

即置换**不改变边数**——这是「等变性不改变图的规模」的定量形式。 -/
theorem permActEdge_card (π : Equiv.Perm ι) (E : Finset (ι × ι)) :
    (permActEdge π E).card = E.card := by
  simp only [permActEdge]
  rw [Finset.card_image_of_injective]
  intro p q hpq
  simp only [Prod.mk.injEq] at hpq
  exact Prod.ext (π.injective hpq.1) (π.injective hpq.2)

/-- **稀疏聚合的数值界**：`sparseMsgPass` 的界由**出度**控制
（指示矩阵的行绝对值和 = 出度），与 `RealGNN.msgPass_bound` 相容。

这不是新定理而是**实例化**：把 `msgPass_bound` 用在 `indicator E` 上，
并注意到置换不改变该界（与 `msgPass_bound_perm` 一致）。 -/
theorem sparseMsgPass_bound (E : Finset (ι × ι)) (h : ι → ℝ) (M : ℝ) (i : ι)
    (hM : ∀ j, |h j| ≤ M) :
    |sparseMsgPass E h i| ≤ M * ((Finset.univ.filter (fun j => (i, j) ∈ E)).card : ℝ) := by
  have h := msgPass_bound (indicator E) h M i hM
  have hrow : ∑ j, |indicator E i j|
      = ((Finset.univ.filter (fun j => (i, j) ∈ E)).card : ℝ) := by
    have hpt : ∀ j : ι, |indicator E i j| = if (i, j) ∈ E then (1 : ℝ) else 0 := by
      intro j
      simp only [indicator]
      by_cases hj : (i, j) ∈ E <;> simp [hj]
    rw [Finset.sum_congr rfl (fun j _ => hpt j)]
    rw [← Finset.sum_filter]
    simp
  rwa [hrow] at h
/-! ## 八、多头 / 通道型 GNN 的等变性（WP7 新增）

GNN 实现中节点特征不是标量而是**通道向量** `h : ι → Fin c → ℝ`。
本节证明：把每个通道**独立**做标量消息传递，再按**与通道无关的**权重组合，
等变性**仍在**——这是「多头 / 多通道 GNN 等变」的形式化。

**关键设计**：置换只作用在**节点**上，**不作用在通道上**：

    (π • h) i a = h (π⁻¹ i) a

这与 `permActFeat` 的逐点搬运一致（对每个通道 `a` 分别成立）。
于是多头等变**归约**为逐通道的 `msgPass_equivariant`。 -/

/-- **通道型特征上的置换作用**：`(π • h) i a = h (π⁻¹ i) a`（只搬节点，不动通道）。 -/
def permActChan {c : ℕ} (π : Equiv.Perm ι) (h : ι → Fin c → ℝ) : ι → Fin c → ℝ :=
  fun i a => h (π.symm i) a

/-- **通道型消息传递**（多头 / 多通道）：`msgPassChan A h i a = ∑_j A i j * h j a`。

即**每个通道独立**做一次标量消息传递（共享邻接 `A`，不共享特征）。 -/
def msgPassChan {c : ℕ} (A : ι → ι → ℝ) (h : ι → Fin c → ℝ) : ι → Fin c → ℝ :=
  fun i a => msgPass A (fun j => h j a) i

/-- **通道型逐点作用**：`chanMap σ h i a = σ (h i a)`（对每个通道施加同一个 `σ`）。 -/
def chanMap {c : ℕ} (σ : ℝ → ℝ) (h : ι → Fin c → ℝ) : ι → Fin c → ℝ :=
  fun i a => σ (h i a)

/-- **通道作用的乘法律**：`(π * σ) • h = π • (σ • h)`。 -/
theorem permActChan_mul {c : ℕ} (π σ : Equiv.Perm ι) (h : ι → Fin c → ℝ) :
    permActChan (π * σ) h = permActChan π (permActChan σ h) := by
  funext i a
  simp only [permActChan]
  rw [show (π * σ).symm i = σ.symm (π.symm i) from by
    rw [show (π * σ).symm = σ.symm * π.symm from by
      ext y
      rw [Equiv.Perm.mul_apply, Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply]]
    rfl]

/-- **通道作用的恒等**：`1 • h = h`。 -/
theorem permActChan_one {c : ℕ} (h : ι → Fin c → ℝ) : permActChan 1 h = h := by
  funext i a; simp [permActChan]

/-- **通道型消息传递等变（核心）**：
`msgPassChan (π • A) (π • h) = π • (msgPassChan A h)`。

即**多头 / 多通道 GNN 对节点置换等变**。
证明：逐通道归约到标量 `msgPass_equivariant`（把通道作为 `funext` 的最内层）。 -/
theorem msgPassChan_equivariant {c : ℕ} (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (h : ι → Fin c → ℝ) :
    msgPassChan (permActAdj π A) (permActChan π h) = permActChan π (msgPassChan A h) := by
  funext i a
  simp only [msgPassChan, permActChan]
  exact congrFun (msgPass_equivariant π A (fun j => h j a)) i

/-- **通道型逐点作用与置换交换**：`π • (σ • h) = σ • (π • h)`。

即「逐通道施加 `σ`」与「节点置换」**可交换**——这是「逐点非线性不破坏等变性」
的形式化（`σ` 与节点编号无关）。 -/
theorem chanMap_permActChan_comm {c : ℕ} (π : Equiv.Perm ι) (σ : ℝ → ℝ)
    (h : ι → Fin c → ℝ) :
    permActChan π (chanMap σ h) = chanMap σ (permActChan π h) := by
  funext i a
  simp only [permActChan, chanMap]

/-- **完整通道型 GNN 层**：`∑_{a} w a * σ (∑_j A i j * h j a)`
——即「多头：每头 `a` 独立聚合 + 非线性，再按头权重 `w a` 求和」。 -/
def multiHeadLayer {c : ℕ} (A : ι → ι → ℝ) (w : Fin c → ℝ) (σ : ℝ → ℝ)
    (h : ι → Fin c → ℝ) (i : ι) : ℝ :=
  ∑ a, w a * σ (msgPassChan A h i a)

/-- **多头 GNN 层等变（核心）**：
`multiHeadLayer (π • A) w σ (π • h) = multiHeadLayer A w σ h` 的**逐节点搬运形式**：

    multiHeadLayer (π • A) w σ (π • h) (π i) = multiHeadLayer A w σ h i.

即「先置换再加权多头聚合」在节点 `π i` 处的值 = 原值在 `i` 处的值——
这是「多头 GNN 输出对置换等变」的完整陈述（头权重 `w` 与节点无关，故不变）。

证明：展开 `multiHeadLayer`，对每个头用 `msgPassChan_equivariant`，
再用 `Equiv.symm_apply_apply` 化简。 -/
theorem multiHeadLayer_equivariant {c : ℕ} (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (w : Fin c → ℝ) (σ : ℝ → ℝ) (h : ι → Fin c → ℝ) (i : ι) :
    multiHeadLayer (permActAdj π A) w σ (permActChan π h) (π i)
      = multiHeadLayer A w σ h i := by
  simp only [multiHeadLayer]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  -- 每个头：`msgPassChan (π•A) (π•h) (π i) a = msgPassChan A h i a`
  -- 由 `msgPassChan_equivariant` 的逐点形式 + `symm_apply_apply`
  have hchan : msgPassChan (permActAdj π A) (permActChan π h) (π i) a
      = msgPassChan A h i a := by
    have h1 := congrFun (congrFun (msgPassChan_equivariant π A h) (π i)) a
    simpa only [permActChan, Equiv.symm_apply_apply] using h1
  rw [hchan]

end Lattice
