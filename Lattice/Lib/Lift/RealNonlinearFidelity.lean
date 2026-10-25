

import Lattice.Lib.Lift.RealNonlinearFidelity_parts.A
import Lattice.Lib.Lift.RealNonlinearFidelity_parts.B
import Lattice.Lib.Lift.RealNonlinearFidelity_parts.C

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
