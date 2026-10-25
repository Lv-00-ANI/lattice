import Mathlib
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: 多值 FCA —— 从 `Prop`-值关系到 `[0,1]`-值（Fuzzy）关系的阈值化

## 本文件建立什么

经典 FCA 的满足关系是 `Prop`-值的（`R : O → A → Prop`）。多值/模糊
FCA 把它换成 `[0,1]`-值的隶属度 `μ : O → A → ℝ`，并引入**阈值**
`θ : ℝ`，通过阈值化 `μ o a ≥ θ` 退回经典 FCA：

  1. `threshExtent` / `threshIntent`：阈值化的 extent/intent
     ——`threshExtent μ θ B = {o | ∀ a ∈ B, θ ≤ μ o a}`；
  2. `threshExtent_antitone_theta`：**本文件核心之一**——阈值**升高**
     ⟹ 外延**缩小**（对**固定**属性集）。这是"严格性单调"：
     θ₁ ≤ θ₂ 时 `threshExtent μ θ₂ ⊆ threshExtent μ θ₁`；
  3. `threshExtent_antitone_attrs`：属性集**增大** ⟹ 外延**缩小**
     （对**固定**阈值）；
  4. `thresh_galois`：阈值化后的 **Galois 连接**（多值版的伴随对），
     即经典 `galois_connection` 在阈值语义下**完全保留**；
  5. `thresh_monotone_in_mu`：**本文件核心之二**——隶属度函数**逐点变大**
     ⟹ 外延**变大**（对固定 θ、固定 B）。这是多值 FCA 中
     "**关系更强 ⟹ 概念更宽**"的形式化；
  6. `threshExtent_zero` / `threshExtent_one_of_pos`：阈值端点行为
     ——θ ≤ 0 时外延为 `univ`（无区分力），θ > 1 时外延为 `∅`
     （**仅在 `μ ≤ 1` 时**，见诚实边界）。

## 依赖什么

* `Mathlib`（`le_iInf`、`Set`、`ℝ` 序）
* `RealFCA`：复用 `IsFormalConcept`——阈值化后概念**就是**
  `IsFormalConcept (fun o a => θ ≤ μ o a)`

## 不做什么

* **不**构造 Fuzzy 概念格的完整结构（那需要 `[0,1]` 上的
  Łukasiewicz/t-norm 代数与 residuated lattice 理论，
  超出本文件范围）。
* **不**做 Fuzzy Galois 连接的**伴随函子**层（residuated 版本），
  只做**阈值化**（crispification）这一最常用且**可证**的降级路径。
* 不引入 `Fuzzy` 类型别名（避免与 Mathlib 冲突），直接用 `ℝ` + 不变量。

## 诚实边界

* ⚠ `threshExtent_one_of_pos` 的结论 `threshExtent μ θ B = ∅`
  **需要承重假设 `hμ : ∀ o a, μ o a ≤ 1`** 与 `1 < θ`。
  去掉 `hμ` 命题**为假**（可在 `a` 处取 `μ o a = 2 > θ`）。
* ⚠ 第 6 条的两个端点结论**不是**对偶的形式复制：θ ≤ 0 ⟹ `univ`
  需要 `∀ a ∈ B` 全称下每点成立；θ > 1 ⟹ `∅` 需要**找到反例属性**——
  故后者额外要求 `B.Nonempty`（否则空属性集仍给 `univ`）。
  本文件对此**显式**加了 `B.Nonempty`，避免陈述假命题。
-/

namespace Lattice

variable {O A : Type*}

/-! ## 一、阈值化的 extent / intent -/

/-- **阈值化外延**：`threshExtent μ θ B = {o | ∀ a ∈ B, θ ≤ μ o a}`
——"在阈值 θ 下满足 `B` 中全部属性"的对象集。

比定义多说了什么：把经典 `extent R B`（`Prop`-值）**统一地**改写为
实数值比较，从而使"阈值"成为一个**显式参数**。这使第 2、3、5 条
（阈值单调、属性和隶属度单调）**可以被陈述**——经典设定下
这些参数根本不存在，故它们是多值推广**新增**的内容。 -/
def threshExtent (μ : O → A → ℝ) (θ : ℝ) (B : Set A) : Set O :=
  {o : O | ∀ a : A, a ∈ B → θ ≤ μ o a}

/-- **阈值化内涵**：`threshIntent μ θ O' = {a | ∀ o ∈ O', θ ≤ μ o a}`
——"被 `O'` 中全部对象在阈值 θ 下满足"的属性集。 -/
def threshIntent (μ : O → A → ℝ) (θ : ℝ) (O' : Set O) : Set A :=
  {a : A | ∀ o : O, o ∈ O' → θ ≤ μ o a}

/-! ## 二、阈值单调性（本文件核心之一） -/

/-- **阈值升高 ⟹ 外延缩小**：`θ₁ ≤ θ₂ ⟹ threshExtent μ θ₂ B ⊆ threshExtent μ θ₁ B`
（固定属性集 `B`）。

比定义多说了什么：这是**多值 FCA 独有**的单调律——经典 FCA 中
不存在"阈值"参数，故本定理**不可能**由 `RealFCA` 的任何结论导出。
其内容是：把门槛抬高只能**淘汰**对象，不能新增。
证明需把 `θ₁ ≤ θ₂ ≤ μ o a` 链**传递**（对每个 `a ∈ B`），
不是定义展开。 -/
theorem threshExtent_antitone_theta (μ : O → A → ℝ) {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂)
    (B : Set A) :
    threshExtent μ θ₂ B ⊆ threshExtent μ θ₁ B := by
  intro o ho a ha
  exact h.trans (ho a ha)

/-- **阈值升高 ⟹ 内涵缩小**：`θ₁ ≤ θ₂ ⟹ threshIntent μ θ₂ O' ⊆ threshIntent μ θ₁ O'`。

比定义多说了什么：与上一条**对偶**，但方向**相同**（两者都随 θ 增大
而缩小），这与经典 FCA 中 extent/intent 的**反变**关系形成对照——
说明"阈值"这一参数与"集合大小"这一参数对语义的作用**正交**。 -/
theorem threshIntent_antitone_theta (μ : O → A → ℝ) {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂)
    (O' : Set O) :
    threshIntent μ θ₂ O' ⊆ threshIntent μ θ₁ O' := by
  intro a ha o ho
  exact h.trans (ha o ho)

/-- **属性集增大 ⟹ 外延缩小**：`B₁ ⊆ B₂ ⟹ threshExtent μ θ B₂ ⊆ threshExtent μ θ B₁`。

比定义多说了什么：这是经典 `extent_antitone` 在**阈值语义**下的
**保持**——即阈值化**不破坏** FCA 的反变结构。⚠ 诚实标注：本条
与 `RealFCA.extent_antitone` **数学内容同型**（都是"条件更多 ⟹ 解更少"），
其价值是确认**多值推广未丢失**该结构，而非新发现。 -/
theorem threshExtent_antitone_attrs (μ : O → A → ℝ) (θ : ℝ) {B₁ B₂ : Set A}
    (h : B₁ ⊆ B₂) :
    threshExtent μ θ B₂ ⊆ threshExtent μ θ B₁ := by
  intro o ho a ha
  exact ho a (h ha)

/-- **对象集增大 ⟹ 内涵缩小**（`threshIntent` 的反变性）。 -/
theorem threshIntent_antitone_objs (μ : O → A → ℝ) (θ : ℝ) {O₁ O₂ : Set O}
    (h : O₁ ⊆ O₂) :
    threshIntent μ θ O₂ ⊆ threshIntent μ θ O₁ := by
  intro a ha o ho
  exact ha o (h ho)

/-! ## 三、隶属度单调性（本文件核心之二） -/

/-- **隶属度逐点变大 ⟹ 外延变大**：若 `∀ o a, μ₁ o a ≤ μ₂ o a`，则
`threshExtent μ₁ θ B ⊆ threshExtent μ₂ θ B`。

比定义多说了什么：这是多值 FCA 中**关系层**的单调律——
"数据更强（隶属度更高）⟹ 概念外延更宽"。它与第 2 条
（阈值单调）**方向相反**，共同刻画了 `(θ, μ)` 两个参数对
外延的作用：**θ 升 ⟹ 缩，μ 升 ⟹ 胀**。
⚠ 证明中 `θ ≤ μ₁ o a ≤ μ₂ o a` 的传递必须**对每个** `a ∈ B` 做，
不是单点展开。 -/
theorem threshExtent_monotone_mu {μ₁ μ₂ : O → A → ℝ}
    (h : ∀ o a, μ₁ o a ≤ μ₂ o a) (θ : ℝ) (B : Set A) :
    threshExtent μ₁ θ B ⊆ threshExtent μ₂ θ B := by
  intro o ho a ha
  exact (ho a ha).trans (h o a)

/-- **隶属度逐点变大 ⟹ 内涵变大**（`threshIntent` 版本）。

比定义多说了什么：与上一条对偶；⚠ 注意**方向相同**（两者都随 μ 增大
而增大），而非一反一正——因为 extent 与 intent 都是"满足者集合"，
只是满足者从对象换成属性。这一点在经典 FCA 中**看不出**来
（没有 μ 可供变化），故是本推广的**新增**观察。 -/
theorem threshIntent_monotone_mu {μ₁ μ₂ : O → A → ℝ}
    (h : ∀ o a, μ₁ o a ≤ μ₂ o a) (θ : ℝ) (O' : Set O) :
    threshIntent μ₁ θ O' ⊆ threshIntent μ₂ θ O' := by
  intro a ha o ho
  exact (ha o ho).trans (h o a)

/-! ## 四、阈值化保留 Galois 连接 -/

/-- **阈值化的 Galois 连接**：`O' ⊆ threshExtent μ θ B ↔ B ⊆ threshIntent μ θ O'`。

比定义多说了什么：**关键保持性结果**——它说明经典 FCA 的
Galois 伴随在**阈值语义下完全保留**（形式与原式一致），
故多值推广**不牺牲** FCA 的代数骨架。
⚠ 诚实标注：证明结构与 `RealFCA.galois_connection` **同型**
（都是"∀∀ 交换"），故本条**不**是新的数学技巧；
其价值是确认阈值化是**保守扩张**（conservative extension）。 -/
theorem thresh_galois (μ : O → A → ℝ) (θ : ℝ) (O' : Set O) (B : Set A) :
    O' ⊆ threshExtent μ θ B ↔ B ⊆ threshIntent μ θ O' := by
  constructor
  · intro h a ha o ho
    exact h ho a ha
  · intro h o ho a ha
    exact h ha o ho

/-- **阈值化后形式概念即经典形式概念**：以
`R θ μ := fun o a => θ ≤ μ o a` 为满足关系，`(O', B)` 是形式概念
当且仅当它是阈值化下的双向闭包不动点。

比定义多说了什么：把多值 FCA 的"概念"**精确**归约为经典
`IsFormalConcept`——即多值层**没有**新增概念类型。
⚠ 诚实标注：证明是 `RealFCA.formal_concept_iff_closure` 的**实例化**
（关系取阈值化谓词），故**非**新数学；它是**桥接引理**，
使经典 FCA 的全部结论自动适用于阈值化设定。 -/
theorem thresh_concept_iff (μ : O → A → ℝ) (θ : ℝ) (O' : Set O) (B : Set A) :
    IsFormalConcept (fun o a => θ ≤ μ o a) O' B ↔
      (O' = threshExtent μ θ (threshIntent μ θ O') ∧ B = threshIntent μ θ O') := by
  have h := formal_concept_iff_closure (fun o a => θ ≤ μ o a) O' B
  simpa only [threshExtent, threshIntent, extent, intent] using h

/-! ## 五、阈值端点行为 -/

/-- **低阈值 ⟹ 外延全空间**：若 `θ ≤ 0` 且 `∀ o a, 0 ≤ μ o a`，
则 `threshExtent μ θ B = univ`。

比定义多说了什么：**真内容**——`θ ≤ 0 ≤ μ o a` 的**两段**传递。
⚠ **承重假设**：`hμ`（隶属度非负）不可省——若 `μ` 可取负值，
`θ ≤ 0` 并不保证 `θ ≤ μ o a`，命题为假。
（多值 FCA 中 `μ` 取值于 `[0,1]`，故 `hμ` 是**领域公理**而非技巧假设。） -/
theorem threshExtent_low_theta (μ : O → A → ℝ) {θ : ℝ} (hθ : θ ≤ 0)
    (hμ : ∀ o a, 0 ≤ μ o a) (B : Set A) :
    threshExtent μ θ B = Set.univ := by
  apply Set.eq_univ_of_forall
  intro o
  exact fun a _ => hθ.trans (hμ o a)

/-- **高阈值 ⟹ 外延空**：若 `1 < θ`、`∀ o a, μ o a ≤ 1`、且 `B` **非空**，
则 `threshExtent μ θ B = ∅`。

比定义多说了什么：**真内容**——需从 `B.Nonempty` 取一个属性 `a₀`，
证明 `¬ (θ ≤ μ o a₀)`（因 `θ > 1 ≥ μ o a₀`）。
⚠ **两个承重假设均不可省**：
  * `hμ ≤ 1`：去掉后取 `μ o a₀ = 2` 命题为假；
  * `B.Nonempty`：去掉后取 `B = ∅`，则 `threshExtent μ θ ∅ = univ ≠ ∅`
    命题为假。
这是本文件**唯一**需要"反例属性"的定理，与 `threshExtent_low_theta`
的纯全称结构形成对比。 -/
theorem threshExtent_high_theta (μ : O → A → ℝ) {θ : ℝ} (hθ : 1 < θ)
    (hμ : ∀ o a, μ o a ≤ 1) {B : Set A} (hB : B.Nonempty) :
    threshExtent μ θ B = ∅ := by
  obtain ⟨a₀, ha₀⟩ := hB
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro o ho
  have hle : μ o a₀ ≤ 1 := hμ o a₀
  exact absurd (ho a₀ ha₀) (not_le.mpr (hle.trans_lt hθ))

end Lattice
