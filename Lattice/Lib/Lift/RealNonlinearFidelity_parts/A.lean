import Mathlib
import Lattice.Lift.RealNonlinear
import Lattice.Lib.Architectures.RealActComplete
import Lattice.Lib.Architectures.RealActDerivatives
import Lattice.Lib.Editing.RealSymbolToWeightNonlinear

/-!
# `RealNonlinearFidelity.lean` 的 `A` 部分

由原文件按语义分节拆分而来；节标题与内容未改动。
-/

/-!
# LATTICE: 非线性侧保真度的可判定判据

## ⚠ 导入拓扑约束（**本文件最重要的前提，先说清楚**）

⭐ **C-16 复核（本次会话实测）：本节原文所述的两个冲突【均不存在】。**

原文称 `Lattice.sigmoid` 被 `RealSwiGLU` 与 `RealExtractInvertibility` 各定义一次，
且同时 import 会报 `environment already contains 'Lattice.sigmoid'`。实测：

* 全库 `def sigmoid` 现在**只有** `RealSwiGLU.lean:31` **一处**；
  `RealExtractInvertibility.lean` 里**没有** `def sigmoid` —— 它定义的是
  **`extractSigmoid`（`:138`）**，名字不同，不构成冲突。
* 原文的 `geluTanh` 平行定义也不成立：`RealExtractInvertibility` **没有** `def geluTanh`，
  它定义的是 **`extractGeluTanh`（`:164`）**；而 `RealActClass` 的 `geluTanh` 在 **`:82`**
  （非原文的 `:74`）。三者名字互不相同。

⇒ ⭐ **保留本节是为了防止照旧文档重复「符号层同名冲突」立项**，
但**不得**再把它当作当前事实引用。本文件当前的 import 选择（沿 `RealActComplete` 侧、
不 import `RealExtractInvertibility`）**仍然是有效的工程决定**，只是理由不再是「硬冲突」。

**本文件的选择**：沿 `RealActComplete` 侧（即 `RealSwiGLU.sigmoid` + `RealActClass.geluSoftMask`），
**不** import `RealExtractInvertibility`。为了不丢失该文件的成果，凡本文件需要它的
定义（`geluGate x = (1 + tanh x)/2`），**就地给出局部等价定义并在 docstring 交叉引用**；
凡需要它的**定理**（门控单调/正性、`geluTanh` 可逆），本文件**独立重证**（见 §九）。
这是**导入拓扑**造成的工程事实，不是数学分歧：两边 `sigmoid` 的定义式逐字相同。

本文件把「非线性层编译保真」从**反例**（`RealSymbolToWeightNonlinear.reluZ_counterexample`，
CORRECTIONS B11）推进到**可判定充分条件**，并把非线性编译链的缺口一次收口：

  1. **零集假设的条件族（可判定充分条件，3 条 + 结构定理）**：
     `zeroFixingR_iff_unique_zero`（**骨架**：对**任意**函数 ⟺ 零集唯一 ∧ `σ 0 = 0`；
     单调性在此等价式中**根本不需要**——本轮探针的 `unused variable hmono` 暴露了这点）、
     `zeroFixingR_of_strictMono`（判据 1：严格单调 + `σ 0 = 0`）、
     `zeroFixingR_of_monotone_unique_zero`（判据 2：**严格性可放宽**为 `Monotone`）、
     `zeroFixingR_of_signPreserving`（判据 3：**符号保持**，单调性完全不需要）；
     `zeroFixing_components` / `zeroFixing_comp`（组合判据：逐分量 + 复合）；
     `zeroFixingR_of_zeroFixingZ` / `zeroFixingR_liftInt`（ℤ → ℝ 桥接）。
     **关键澄清（本轮纠正）**：`ZeroFixing` 是「**唯一零点**」而非「单调」——
     它与单射的关系是**单向**的（`injective_of_zeroFixing_sufficient`）；
     反向为**假**（`zeroFixing_not_imp_injective`，机器验证反例）。
  2. **ℝ 版零集假设与忠实层语义**：`ZeroFixingR` 与 `nonlinearFidelity_zero_iff`
     （「输出为零 ⟺ 约束满足」）、`nonlinearFidelity_unique_zero`（零点集恰为 `{0}`）。
  3. **可判定性内核（本轮最重要的工程发现）**：`decide (ZeroFixing act)` **不可用**
     ——Lean 不为 `∀ y : ℤ, …` 合成 `Decidable`（报
     `failed to synthesize Decidable (∀ (y : ℤ), …)`，`#eval` 也随之失败）。
     实际内核是 §四 的**有界穷举** `zeroFixingHoldsBounded act n`
     （`zeroFixingHoldsBounded_iff` / `zeroFixing_box_only` /
     `zeroFixing_of_bounded_no_witness`，全部**可执行**、可 `#eval`）。
     **⚠ 真空通过的坑**：若只检查「`act y = 0 → y = 0`」，则**零集为空**的激活
     （`act_sigmoidZ n = 2n+1`）会**平凡通过**而报 `true`，与 §六 的定理矛盾
     （实测输出确实是 `("sigmoidZ", true)`）。必须把 `act 0 = 0` 一并纳入穷举。
     证伪侧由 `zeroFixing_false_of_witness`（有非零零点）与
     `neg_zeroFixing_sigmoidZ`（零集为空，`σ 0 ≠ 0`）**两条入口**覆盖。
  4. **激活函数判定表**：§五/§六（ℤ 侧 12 个：`reluZ`/`leakyReluZ`/`siluZ`/`geluZ`/
     `sigmoidZ`/`softplusZ`/`hardswishZ`/`modreluZ`/`cube`/`neg`/`id`/`sign`）
     与 §七（ℝ 侧 9 个：`relu`/leakyRelu/`silu`/`geluTanh`/`sigmoid`/`softplus`/`hardSwish`
     + `abs`/`cube`/`sinh` 推论）；§十 的 `#eval zeroFixingTable` **打印**整张判定表，
     并由 `zeroFixingTable_true_consistent` / `zeroFixingTable_false_consistent` /
     `zeroFixingTable_empty_zero_set` 与定理**逐格对照**。
  5. **门控解析性质独立重证**（因导入冲突必须自足）：`tanh_pos_of_pos`、
     `neg_one_lt_tanh_fid`、`tanh_eq_zero_iff`、`tanh_nonpos_of_nonpos`、
     `abs_tanh_lt_one`、`geluGateFid_pos`/`geluGateFid_bounds`、
     `tanh_strictMonoOn_Ici_zero_fid`、`geluGateFid_monoOn`、
     `act_geluTanhR_strictMonoOn`、`act_geluTanhR_injOn`。

## 与 `RealExtractInvertibility` 的关系（诚实标注）

任务书要求「把 `RealExtractInvertibility` 的显式假设变成定理」。**已复核结论：
那里没有可升级的显式假设**（见下），但因导入冲突本文件改为**独立重证**同形结论。

- 第四节的条件定理 `geluTanh_injOn_of_gate`（假设 `0 ≤ gate 0`、`MonotoneOn gate (Ici 0)`、
  `∀ x > 0, 0 < gate x`）**早已被该文件自己的第五节无条件证明**
  （`geluGate_nonneg` / `geluGate_monoOn` / `geluGate_pos_of_pos`），
  并由零假设的 `geluTanh_strictMonoOn` / `geluTanh_injOn` 直接给出；
  该文件 docstring 也已写明「原第 6 节的显式假设已全部升级为定理」。
  （**行号提示**：该文件在 C4 工作期间被**其他包**并发编辑，行数已从 314 变到 260；
  上述引理仍存在，此处不锁定具体行号，只按名字引用。）
- 唯一仍带假设的 `geluTanh_injOn_of_strictMono` 是**有意的归约接口**（把单调性当输入），
  其前提由 `geluTanh_strictMonoOn` 直接满足，不是缺口。
- mathlib 4.14 **确实没有** `Real.tanh_pos_iff` / `Real.tanh_strictMonoOn_on` /
  `Real.neg_one_lt_tanh` / `Real.tanh_pos_of_pos`（已 grep
  `.lake/packages/mathlib` 全树确认：只有
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean` 的
  `Real.sinh_strictMono` / `sinh_pos_iff` / `sinh_neg_iff` / `sinh_nonneg_iff` /
  `cosh_lt_cosh`，**无任何 `Real.tanh` 的序结构引理**）。
  故本文件**就地重证**这三条（§七/§八/§九），全部走
  `Real.tanh_eq_sinh_div_cosh` + `Real.sinh_sub` + `Real.sinh_pos_iff`。
- 真正可补的**非线性侧可逆性缺口**（负半轴不可逆）已由 B10（ReLU 在 `(-∞,0]` 不可逆）
  覆盖；本文件把它提升为**结构性判据** `zeroFixing_not_strictMonoOfNeg`
  ——「`act 0 = 0` 且 `act (-1) = 0`」的激活**必然**不满足零集假设，
  这正是 `relu` / `leakyRelu` 在整数编译模型下失败的同一机制。

## 诚实边界（不证 / 不声称）

- **`modReLU` 不在判定表内（类型层面就不可能）**：`RealModReLU.modReLU (b : ℝ) : ℂ → ℂ`
  定义在 ℂ 上（`RealModReLU.lean:52-53`），与 `ZeroFixing : (ℤ → ℤ) → Prop` /
  `ZeroFixingR : (ℝ → ℝ) → Prop` 类型不同。经分析：其模长门控在 `b < 0` 时零集是
  **圆盘** `{|z| ≤ -b}`（非唯一零点 ⟹ 零集假设**不成立**），`b = 0` 时为恒等（**成立**），
  `b > 0` 时零集为空（**不成立**）。**这是分析结论，本文件不声称已机器验证**。
- **`RealActClass.geluSoftMask`（数值 GELU）的判定未做**：其内层
  `√(2/π)(x + 0.044715x³)` 的三次多项式严格单调性未证；且负半轴（`x ≈ -1.5` 附近）
  该激活再变号，由 `neg_zeroFixing_of_neg_neg_zero` 的形态可知其零集假设**为假**。
  本文件判定的是**纯 `tanh` 门控**版 `geluGateFid`（§七 判定 3）。
- **浮点/数值层的可判定性未做**：本文件判定在 **ℝ/ℤ 的精确语义**上进行；
  IEEE-754 语义下的零集判定属 `RealIEEE754` / `RealCompileFloatCorrectness` 范围。
- **多层复合的误差界未做**（任务书第 4 条）：`ZeroFixing` 保证的是**精确**零集对应
  （`nonlinearFidelity_zero_iff`）；Lipschitz 下多层的 ε 传播需要 `RealApprox` 的
  逐层界 + 列表归纳。**关键理由**：`RealRoundtripBound` 的界
  （`roundtrip_error_bound`：`≤ ε₁·X + ε₂`）与 `RealApprox.layer_out_error_bound`
  **都是线性层**（`RealNeuronOut`）的结论，对非线性层需要**先有** `σ` 的
  Lipschitz 常数与 `|σ y|` 的界；本项目里这些散落在
  `RealActDerivatives`（`softplus_lipschitz`、`sigmoid_deriv_le_quarter`）、
  `RealCounterexamples`（`cex_silu_globally_lipschitz`）、
  `RealModReLULipschitz`。把它们与 `ZeroFixing` 组合成**单一的**非线性层
  误差界定理是一条独立的工作线，本文件**未做**，只给出单层的确切对偶
  `zeroFixing_implies_relu_faithful` 与零点唯一性刻画 `nonlinearFidelity_unique_zero`。
- 本文件不引入任何未证假设；无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice


/-! ## 一、ℝ 版零集假设与忠实层语义 -/

/-- **真值引理**：在 ℝ 上 `x = 0 ↔ x = -0`（`neg_zero` 的 `iff` 形）。
仅用于让 §二 的条件族在**不依赖 Mathlib 引理名**的前提下与整数版逐句对齐。 -/
theorem real_eq_zero_iff_neg_zero (x : ℝ) : (x = 0) ↔ (x = -0) := by
  rw [neg_zero]

/-- **ℝ 版零集假设 `ZeroFixingR`**：`σ` 的零集恰为 `{0}`。
这是 `RealSymbolToWeightNonlinear.ZeroFixing`（整数版）的实数对应物——
编译侧在 ℤ 上工作，执行侧在 ℝ 上工作，本定义是两者的共同语义。 -/
def ZeroFixingR (act : ℝ → ℝ) : Prop := ∀ y, act y = 0 ↔ y = 0

/-- **忠实层语义**：带激活层的输出为零 ⟺ 线性前置为零
（`ZeroFixingR` 的定义展开，是「编译保真」的核心等式）。 -/
theorem nonlinearFidelity_zero_iff (act : ℝ → ℝ) (hσ : ZeroFixingR act) (y : ℝ) :
    act y = 0 ↔ y = 0 :=
  hσ y

/-- **零点的唯一性刻画**：`ZeroFixingR` 下 `act` 的零点集恰为 `{0}`。 -/
theorem nonlinearFidelity_unique_zero (act : ℝ → ℝ) (hσ : ZeroFixingR act) :
    {y : ℝ | act y = 0} = {0} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact hσ y

/-- **判据骨架（不需要单调性）**：对**任意** `act`，
零集假设 ⟺ 「零集至多单点 **且** `act 0 = 0`」。

**⚠ 本轮实测纠正**：初稿把这条陈述为「**单调**激活的零集假设 ⟺ …」，
但探针报 `unused variable hmono`——说明 `hmono` **根本没用到**。
复核后确认：该等价对任意函数成立（两个方向都只用 `ZeroFixing` 的定义）。
单调性只在「零集唯一」的**验证**中起作用（判据 2/3），
不是这个等价式本身的前提。故此处**删去 `hmono` 参数**，
命题**更强**（少一个前提），且不再有 linter 警告。

这把「何谓保真激活」化为**两个可逐点验证的命题**（零集唯一、零点归一）。 -/
theorem zeroFixingR_iff_unique_zero (act : ℝ → ℝ) :
    ZeroFixingR act ↔ (∀ y z, act y = 0 → act z = 0 → y = z) ∧ act 0 = 0 := by
  constructor
  · intro h
    exact ⟨fun y z hy hz => by rw [(h y).mp hy, (h z).mp hz], (h 0).mpr rfl⟩
  · rintro ⟨huniq, h0⟩ y
    exact ⟨fun hy => huniq y 0 hy h0, fun hy => hy ▸ h0⟩

/-- **判据骨架（单调版，保留作接口）**：`hmono` 在等价式本身中**不被使用**
（见 `zeroFixingR_iff_unique_zero`），此处保留该参数以提供与 §二 其余判据
同形的接口。

**STYLE 陷阱（本轮实测两处）**：
(i) `omit [Monotone act] in` **在 docstring 之前也解析失败**
（报 `unknown identifier 'act'`：`omit` 的 binder 在引理签名被 elaboration 前
无法解析 `act`），故本文件**不用 `omit`**，改用最简形式——
让引理**直接不含** `hmono` 参数（命题更强，且零警告）。
(ii) `omit ... in` 写在 docstring **之后**同样非法
（`unexpected token 'omit'; expected 'lemma'`）。 -/
theorem zeroFixingR_iff_of_monotone (act : ℝ → ℝ) :
    ZeroFixingR act ↔ (∀ y z, act y = 0 → act z = 0 → y = z) ∧ act 0 = 0 :=
  zeroFixingR_iff_unique_zero act

/-! ## 二、零集假设的充分条件族（逐条可判定） -/

/-- **判据 1（严格单调）**：`σ` 严格单调且 `σ 0 = 0` ⟹ 零集假设。
`RealSymbolToWeightNonlinear.zeroFixing_of_strictMono` 的实数版。 -/
theorem zeroFixingR_of_strictMono (act : ℝ → ℝ) (h0 : act 0 = 0) (hmono : StrictMono act) :
    ZeroFixingR act := by
  intro y
  constructor
  · intro hy
    rcases lt_trichotomy y 0 with hlt | heq | hgt
    · have hlt' : act y < act 0 := hmono hlt
      rw [h0] at hlt'
      linarith
    · exact heq
    · have hgt' : act 0 < act y := hmono hgt
      rw [h0] at hgt'
      linarith
  · intro hy0
    rw [hy0]
    exact h0

/-- **判据 2（单调 + 零集唯一）**：**单调性可放宽为 `Monotone`（不要求严格）**，
只需零集唯一且 `σ 0 = 0`。——这是对判据 1 的实质性放宽，
覆盖「常数段外严格、段内平坦」的激活（如 hard-swish 的近段）。

**诚实标注**：`hmono` 在**结论**里不被直接使用（单调性只用于**验证**零集唯一
这一步，见 `zeroFixingR_iff_of_monotone`），保留该参数只为接口形状；
为免 `unused variable` 警告且不依赖 `omit`（该 tactic 在本上下文不可用），
此处用 `_hmono` 命名。 -/
theorem zeroFixingR_of_monotone_unique_zero (act : ℝ → ℝ) (_hmono : Monotone act)
    (huniq : ∀ y z, act y = 0 → act z = 0 → y = z) (h0 : act 0 = 0) : ZeroFixingR act :=
  (zeroFixingR_iff_of_monotone act).mpr ⟨huniq, h0⟩

/-- **判据 2 是充要的**：零集假设 ⟺ 「零集唯一 ∧ `σ 0 = 0`」
（故该判据**不可再放宽**）。`hmono` 保留作接口形状（不参与证明）。 -/
theorem zeroFixingR_iff_of_monotone_and_mono (act : ℝ → ℝ) (_hmono : Monotone act) :
    ZeroFixingR act ↔
      (∀ y z, act y = 0 → act z = 0 → y = z) ∧ act 0 = 0 :=
  zeroFixingR_iff_of_monotone act

/-- **判据 3（符号保持）**：符号保持性 **完全不需要单调性**。
这是条件族中**最弱、最好用**的一条：只要能判定「`y` 与 `act y` 同号同零」，
零集假设自动成立（证明只需 `lt_trichotomy` 三分，全部可判定——
且**不经过任何单调性推理**，故可判定性内核不承担序传递义务）。 -/
theorem zeroFixingR_of_signPreserving (act : ℝ → ℝ)
    (h : ∀ y, (0 < y ↔ 0 < act y) ∧ (y < 0 ↔ act y < 0)) : ZeroFixingR act := by
  intro y
  constructor
  · intro hy
    rcases lt_trichotomy y 0 with hlt | heq | hgt
    · have hneg : act y < 0 := (h y).2.mp hlt
      linarith
    · exact heq
    · have hpos : 0 < act y := (h y).1.mp hgt
      linarith
  · intro hy
    rw [hy]
    rcases lt_trichotomy (act 0) 0 with hlt | heq | hgt
    · have hneg : (0 : ℝ) < 0 := (h 0).2.mpr hlt
      exact absurd hneg (lt_irrefl 0)
    · exact heq
    · have hpos : (0 : ℝ) < 0 := (h 0).1.mpr hgt
      exact absurd hpos (lt_irrefl 0)

/-! ## 三、整数（编译侧）判据与 ℝ↔ℤ 桥接 -/

/-- **整数版判据 1**：`act : ℤ → ℤ` 严格单调且 `act 0 = 0` ⟹ `ZeroFixing act`
（`RealSymbolToWeightNonlinear.zeroFixing_of_strictMono` 的回收，只读引用）。 -/
theorem zeroFixingZ_of_strictMono (act : ℤ → ℤ) (h0 : act 0 = 0) (hmono : StrictMono act) :
    ZeroFixing act :=
  zeroFixing_of_strictMono act h0 hmono

/-- **整数版判据 2**：单调（非严格）+ 零集唯一 + `act 0 = 0` ⟹ `ZeroFixing act`。
（与实数版 `zeroFixingR_of_monotone_unique_zero` 一致：单调性只用于**验证**
「零集唯一」这一步，在结论中不被直接使用；用 `_hmono` 命名避免 linter 警告。） -/
theorem zeroFixingZ_of_monotone_unique_zero (act : ℤ → ℤ) (_hmono : Monotone act)
    (huniq : ∀ y z, act y = 0 → act z = 0 → y = z) (h0 : act 0 = 0) : ZeroFixing act := by
  refine fun y => ⟨fun hy => ?_, fun hy => hy ▸ h0⟩
  exact huniq y 0 hy h0

/-- **整数版判据 3**：符号保持 ⟹ `ZeroFixing act`（整数三分 + `omega`）。 -/
theorem zeroFixingZ_of_signPreserving (act : ℤ → ℤ)
    (h : ∀ y, (0 < y ↔ 0 < act y) ∧ (y < 0 ↔ act y < 0)) : ZeroFixing act := by
  intro y
  constructor
  · intro hy
    rcases lt_trichotomy y 0 with hlt | heq | hgt
    · have := (h y).2.mp hlt
      omega
    · exact heq
    · have := (h y).1.mp hgt
      omega
  · intro hy
    rw [hy]
    rcases lt_trichotomy (act 0) 0 with hlt | heq | hgt
    · have := (h 0).2.mpr hlt
      omega
    · exact heq
    · have := (h 0).1.mpr hgt
      omega

/-- **组合判据（逐分量）**：`ZeroFixing` 在有限积上逐分量合成
（为多层/多神经元激活提供接口）。 -/
theorem zeroFixing_components {n : ℕ} (act : Fin n → ℤ → ℤ)
    (h : ∀ i, ZeroFixing (act i)) (y : Fin n → ℤ) :
    (∀ i, act i (y i) = 0) ↔ ∀ i, y i = 0 := by
  constructor
  · intro hy i
    exact (h i (y i)).mp (hy i)
  · intro hy i
    rw [hy i]
    exact (h i 0).mpr rfl

/-- **组合判据（复合）**：两个零集假设各自的复合仍满足零集假设。 -/
theorem zeroFixing_comp (σ τ : ℤ → ℤ) (hσ : ZeroFixing σ) (hτ : ZeroFixing τ) :
    ZeroFixing (σ ∘ τ) := by
  intro y
  rw [Function.comp_apply]
  constructor
  · intro h
    exact (hτ y).mp ((hσ (τ y)).mp h)
  · intro h
    rw [h]
    exact (hσ (τ 0)).mpr ((hτ 0).mpr rfl)

/-- **桥接**：整数零集假设 ⟹ 实数零集假设（沿 `ℤ → ℝ` 的**嵌入**）。
这保证编译侧（ℤ）判定的保真性在执行侧（ℝ）仍然有效。

**为什么必须用 `Int.cast` 而不是 `Int.floor`（首轮实测的坑）**：
`⌊y⌋ = 0` 只给出 `y ∈ [0, 1)`，**推不出** `y = 0`——首轮我用
`have hfy : (⌊y⌋ : ℝ) = y` 想强行闭合，`simp` 报 `made no progress`，
根因是这条等式**本身就是假的**（`y = 1/2` 时左边 `0`、右边 `1/2`）。

**为什么不用 `dite`/`dif_pos`（第二个实测坑）**：`dif_pos` 需要与**陈述里那个
`dite` 的 `Decidable` 实例**逐项对齐；引理体内的 `classical` 引入的实例与
陈述处 elaborator 用的不是同一个项，报
`did not find instance of the pattern dite (∃ n, y = ↑n) …`。
**最终解法**：把提升函数写成**不含 `Decidable` 的显式 lambda**
`fun x : ℝ => (act ⌈x⌉ : ℝ)`（`⌈·⌉ = Int.ceil` 是**全函数**，无需判定），
并把结论陈述在**整数点**上——该 lambda 在整数点上取值等于 `act n`，是 `rfl` 级等式
（见 `zeroFixingR_liftInt`；库中并无名为 `liftInt` 的具名定义），
零集结构沿单射 `Int.cast` 严格保持。这是本文件最终采用的**无副作用接口格式**。 -/
theorem zeroFixingR_of_zeroFixingZ (act : ℤ → ℤ) (hσ : ZeroFixing act) :
    ∀ n : ℤ, (((act n : ℤ) : ℝ) = 0) ↔ ((n : ℝ) = 0) := by
  intro n
  constructor
  · intro h
    have h' : act n = 0 := by exact_mod_cast h
    have := (hσ n).mp h'
    rw [this]
    norm_num
  · intro h
    have h' : n = 0 := by exact_mod_cast h
    rw [h', (hσ 0).mpr rfl]
    norm_num

/-- **桥接（函数版）**：把 ℤ 激活沿 `Int.ceil` 提升为全函数 `ℝ → ℝ`，
则它在**整数点**上的零集与 ℤ 版完全一致。
（`Int.ceil` 是全函数，故本陈述**不需要任何 `Decidable`**。） -/
theorem zeroFixingR_liftInt (act : ℤ → ℤ) (hσ : ZeroFixing act) (n : ℤ) :
    (fun x : ℝ => (act ⌈x⌉ : ℝ)) (n : ℝ) = 0 ↔ (n : ℝ) = 0 := by
  show ((act ⌈((n : ℤ) : ℝ)⌉ : ℤ) : ℝ) = 0 ↔ ((n : ℤ) : ℝ) = 0
  rw [Int.ceil_intCast]
  exact zeroFixingR_of_zeroFixingZ act hσ n

/-! ## 四、可判定性内核：零集假设的真值是可计算的

**关键实现细节（首轮实测的坑）**：`zeroFixing` 的 `∀ y : ℤ` 是全称量化，
Lean **不会**自动合成其 `Decidable` 实例——直接写
`decidable_of_iff (∀ y : ℤ, …) Iff.rfl` 会报
`failed to synthesize Decidable (∀ (y : ℤ), act y = 0 ↔ y = 0)`，
`#eval` 也随之失败（`aborting evaluation since the expression depends on the 'sorry' axiom`）。
正确写法是**显式给去量词过程**：本文件用「限定到 `[-n, n]` 上穷举」的
`decidableZeroFixingBounded`，再用 §六 的**单点判据**
（`¬ZeroFixing act ↔ ∃ y ≠ 0, act y = 0`）证明它与全称版一致。
「限定到盒子 + 见证搜索」正是**可判定性内核**的实际内容。 -/

/-- **有界判定过程**：在整数盒 `[-n, n]` 上穷举检验零集假设的**两个合取项**：
`act 0 = 0`（归一）与「非零处不为零」（唯一性）。
这是真正**可执行**的判定（`List.range` + `Int.decEq`），是全量判定的可计算内核。

**注意 首轮实测的坑（本文件最重要的实现教训）**：若只检验「`act y = 0 → y = 0`」，
则**零集为空的激活会真空通过**——`act_sigmoidZ n = 2n+1` 在 ℤ 上永不取 `0`，
于是「非零处不为零」平凡成立，判定的真值列会错误地报 `true`。
（实测输出确实是 `("sigmoidZ", true)`，与 §六 的定理 `neg_zeroFixing_sigmoidZ` **矛盾**。）
必须把 `act 0 = 0` 也纳入穷举，判定表才与定理一致。 -/
def zeroFixingHoldsBounded (act : ℤ → ℤ) (n : ℕ) : Bool :=
  decide (act 0 = 0) &&
    (List.range (2 * n + 1)).all fun k =>
      let y : ℤ := (k : ℤ) - (n : ℤ)
      decide (act y = 0 → y = 0)

/-- **可判定性内核**：盒 `[-n, n]` 上的穷举通过 ⟺ 「`act 0 = 0`」**且**盒内唯一性。
**STYLE 陷阱**：mathlib 4.14 **没有** `List.all_iff_forall_mem`；
正确名是 `List.all_eq_true`（配 `Bool.decide_eq_true`）。 -/
theorem zeroFixingHoldsBounded_iff (act : ℤ → ℤ) (n : ℕ) :
    (zeroFixingHoldsBounded act n = true) ↔
      act 0 = 0 ∧ ∀ k ∈ List.range (2 * n + 1),
        act ((k : ℤ) - (n : ℤ)) = 0 → ((k : ℤ) - (n : ℤ)) = 0 := by
  unfold zeroFixingHoldsBounded
  rw [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨of_decide_eq_true h1, fun k hk => of_decide_eq_true (h2 k hk)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨decide_eq_true_eq.mpr h1, fun k hk => decide_eq_true_eq.mpr (h2 k hk)⟩

/-- **可判定性内核（见证搜索版，充要）**：零集假设为假 ⟺ 存在非零 `y` 使 `act y = 0`。
这把「激活不行」化为**单点见证的搜索**（见 §五/§六）。证明不经任何分析引理。

**注意 这条判据的适用范围（本轮实测）**：它只覆盖「有非零零点」的失败机制，
**不覆盖「零集为空」（`σ 0 ≠ 0`）**——`act_sigmoidZ n = 2n+1` 没有零点，
但 `ZeroFixing` 仍为假（因 `act 0 = 1 ≠ 0`）。故本文件对否定侧**分两类**处理：
`zeroFixing_false_of_witness`（有非零零点）与 `σ 0 ≠ 0` 直接反证。 -/
theorem not_zeroFixing_iff_exists (act : ℤ → ℤ) (h0 : act 0 = 0) :
    (¬ ZeroFixing act) ↔ ∃ y : ℤ, y ≠ 0 ∧ act y = 0 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    refine h fun y => ⟨fun hy => ?_, fun hy => hy ▸ h0⟩
    by_contra hyne
    exact (hcon y hyne) hy
  · rintro ⟨y, hyne, hy⟩ h
    exact hyne ((h y).mp hy)

/-- **可判定性（否定侧的统一入口）**：只要能给出非零零点 `y`，零集假设即为假。
**注意本判据不需要 `σ 0 = 0`**——证法直接对 `y` 用零集假设的
`act y = 0 → y = 0` 方向（该方向对任何 `act` 都成立，无需归一前提）。

**注意 适用范围（本轮实测的教训）**：它只覆盖「**有非零零点**」这一失败机制，
**不覆盖「零集为空」（`σ 0 ≠ 0`）**——`act_sigmoidZ n = 2n+1` 在 ℤ 上无零点，
但 `ZeroFixing` 仍为假。故本文件对否定侧分两条入口：
本定理（有非零零点）与 `neg_zeroFixing_sigmoidZ`（`σ 0 ≠ 0` 直接反证）。 -/
theorem zeroFixing_false_of_witness (act : ℤ → ℤ) (y : ℤ) (hyne : y ≠ 0) (hy : act y = 0) :
    ¬ ZeroFixing act :=
  fun h => hyne ((h y).mp hy)

/-- **可判定性（盒内版）**：若盒 `[-n, n]` 上穷举通过，则零集假设在**盒内**成立。
这是 `zeroFixing_of_bounded_no_witness` 的核心一步。
（`y.natAbs ≤ n` 时 `y + n ∈ [0, 2n]`，故 `(y + n).toNat` 落在 `range (2n+1)` 内；
`rw [List.mem_range]` 后目标是纯 `ℤ`/`ℕ` 算术，交给 `omega`。） -/
theorem zeroFixing_box_only (act : ℤ → ℤ) (n : ℕ)
    (hbox : zeroFixingHoldsBounded act n = true) :
    ∀ y : ℤ, y.natAbs ≤ n → act y = 0 → y = 0 := by
  intro y hle hy
  have hmem : (y + (n : ℤ)).toNat ∈ List.range (2 * n + 1) := by
    rw [List.mem_range]
    omega
  have hkey := ((zeroFixingHoldsBounded_iff act n).mp hbox).2 ((y + (n : ℤ)).toNat) hmem
  have hcast : (((y + (n : ℤ)).toNat : ℤ) - (n : ℤ)) = y := by omega
  rw [hcast] at hkey
  exact hkey hy

/-- **可判定性（显式验证版）**：若 `act 0 = 0`、`act` 在某个足够大的盒上通过穷举检验，
且盒外不存在非零零点，则零集假设成立。
这把「可判定」拆成**可执行的有限检验 + 一条覆盖论证**。

（`h0` 用于零集假设的**逆方向** `0 = 0 → act 0 = 0`；
`hbox` 的第一分量已含 `act 0 = 0`，但显式传入使接口不必依赖内核的内部结构。） -/
theorem zeroFixing_of_bounded_no_witness (act : ℤ → ℤ) (n : ℕ) (h0 : act 0 = 0)
    (hbox : zeroFixingHoldsBounded act n = true)
    (hout : ∀ y : ℤ, n < y.natAbs → act y = 0 → y = 0) : ZeroFixing act := by
  refine fun y => ⟨fun hy => ?_, fun hy => hy ▸ h0⟩
  by_cases hle : y.natAbs ≤ n
  · exact zeroFixing_box_only act n hbox y hle hy
  · exact hout y (by omega) hy

/-! ## 五、激活函数判定表 —— 肯定侧（`ZeroFixing` 成立，机器验证） -/
