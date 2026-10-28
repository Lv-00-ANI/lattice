import Mathlib
import Lattice.Runtime.RealNonlinear
import Lattice.Lib.Architectures.RealActComplete
import Lattice.Lib.Architectures.RealActDerivatives
import Lattice.Lib.Editing.RealSymbolToWeightNonlinear
import Lattice.Lib.Lift.RealNonlinearFidelity_parts.A

/-!
# `RealNonlinearFidelity.lean` 的 `B` 部分

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


/-! ### （0）整数激活：全部为非可计算 `def`，用于展示判定表 -/

/-- 整数 ReLU：`max n 0`（回收 `RealSymbolToWeightNonlinear.reluZ`）。 -/
def act_reluZ : ℤ → ℤ := reluZ

/-- 整数 leaky ReLU：`act n = if 0 ≤ n then 2n else n`。

**注意 为什么不用 `n / 2`（本轮实测的数值陷阱）**：直觉写法
`if 0 ≤ n then n else n / 2` 在 ℤ 上**不是**严格单调的——
`Int.ediv` 向零截断，`(-5) / 2 = -2` 且 `(-4) / 2 = -2`，
故 `-5 < -4` 但两像相等。**代小整数复核即知**（STYLE §5）。
这里改用**放大刻度**：负半轴斜率 `1`、正半轴斜率 `2`——
正负斜率比仍是标准的 `1/2`，但在 ℤ 上严格单调成立。 -/
def act_leakyReluZ (n : ℤ) : ℤ := if 0 ≤ n then 2 * n else n

/-- 整数 SiLU 的**可判定代用**：取 `n ↦ n`（恒等）——SiLU 的零集是 `{0}`
（`silu x = x·σ(x)` 且 `σ > 0`），整数恒等映射**恰好**有同一零集。
诚实标注：这是 SiLU **零集结构**的整数代用，**不是** SiLU 本身
（SiLU 的 `sigmoid` 因子需要实数除法；实数版判定见 §七 `zeroFixingR_silu`）。 -/
def act_siluZ (n : ℤ) : ℤ := n

/-- 整数 GELU(tanh) 的可判定代用：取 `n ↦ n`（零集同为 `{0}`，
因 `geluTanh x = x·gate x` 且 `gate` 恒正）。 -/
def act_geluZ (n : ℤ) : ℤ := n

/-- 整数 sigmoid 的代用：`n ↦ 2·n + 1`（严格单调、`0 ↦ 1`，零点在与 `-1/2` 对应处）。 -/
def act_sigmoidZ (n : ℤ) : ℤ := 2 * n + 1

/-- 整数 softplus 的代用：`n ↦ n + 1`（严格单调、零点在 `-1`，与 `log 2 > 0` 对应）。 -/
def act_softplusZ (n : ℤ) : ℤ := n + 1

/-- 整数 hardswish 门控的代用：`n ↦ n + 1`（严格单调，零点唯一）。 -/
def act_hswishZ (n : ℤ) : ℤ := n + 1

/-- 整数 modReLU 门控的代用：`n ↦ n + 1`（唯一零点；`b < 0` 的圆盘零点在整数上
退化为单点）。 -/
def act_mreluZ (n : ℤ) : ℤ := n + 1

/-! ### （1）判定表的肯定侧 -/

/-- **判定 0（零集 = `{0}`）**：`act_siluZ`（恒等）满足零集假设。 -/
theorem decidable_zeroFixing_siluZ : ZeroFixing act_siluZ := by
  intro y
  exact ⟨fun hy => hy, fun hy => hy ▸ rfl⟩

/-- **判定 1（零集 = `{0}`）**：`act_geluZ`（恒等）满足零集假设。 -/
theorem decidable_zeroFixing_geluZ : ZeroFixing act_geluZ := by
  intro y
  exact ⟨fun hy => hy, fun hy => hy ▸ rfl⟩

/-- **§四 可执行内核的实例化（演示「判定」的实际形态）**：
把 `zeroFixing_of_bounded_no_witness` 用在 `act_siluZ` 上——
盒取 `n = 3`（输出由 `decide` 在**编译期**穷举 `{-3,…,3}`），
盒外由 `|y| > 3` 直接给出。这条定理与 `decidable_zeroFixing_siluZ` 是
同一个结论的两条独立证据（一条走内核、一条走定义）。 -/
theorem decidable_zeroFixing_siluZ_via_kernel : ZeroFixing act_siluZ :=
  zeroFixing_of_bounded_no_witness act_siluZ 3 (by norm_num [act_siluZ]) (by decide)
    (fun y _ hy => by simpa [act_siluZ] using hy)

/-- **判定 2（严格单调激活）**：整数 leaky ReLU（负斜率 `1`、正斜率 `2`，比值 `1/2`）
满足零集假设（判据 1 的实例；证明走 `StrictMono` + `act 0 = 0`）。

**STYLE 陷阱规避（本轮实测两处）**：
(i) `omega` 对 `if` 项是黑的——`if_pos (by omega : 0 ≤ x)` 报
`omega could not prove the goal: No usable constraints found`；
必须在 `unfold` **之前**把条件取出。
(ii) **前提 `hxy : x < y` 本身推不出 `0 ≤ x`**（首轮实测：
`have hx0 : 0 ≤ x := by omega` 报
`a possible counterexample may satisfy b ≤ -1, a - b ≥ 1`）——
必须对 `x`/`y` 的符号**分四种情形**。 -/
theorem decidable_zeroFixing_leakyReluZ : ZeroFixing act_leakyReluZ := by
  have h0 : act_leakyReluZ 0 = 0 := by norm_num [act_leakyReluZ]
  refine zeroFixingZ_of_strictMono act_leakyReluZ h0 ?_
  intro x y hxy
  show act_leakyReluZ x < act_leakyReluZ y
  unfold act_leakyReluZ
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    by_cases hy : 0 ≤ y
    · rw [if_pos hy]; omega
    · exact absurd hxy (by omega)
  · rw [if_neg hx]
    by_cases hy : 0 ≤ y
    · rw [if_pos hy]; omega
    · rw [if_neg hy]; omega

/-- **判定 3（严格单调、零集为空）**：整数 sigmoid 代用 `n ↦ 2n+1` **不**满足零集假设。

**注意 数值复核（STYLE §5 的教训，本轮实测命中）**：`2n + 1 = 0` 在 ℤ 上**无解**
（解是 `n = -1/2`）——故该激活的**零集为空**，而不是「有非零零点」。
首轮我误写了见证 `-1`（其实 `act_sigmoidZ (-1) = -1 ≠ 0`），
`decide` 直接证伪了那条**假命题**。正确的失败机制是 `σ 0 ≠ 0`：
零集假设要求 `act 0 = 0`，而 `act 0 = 1`。故此处用 `(h 0).mpr rfl` 取 `act 0 = 0` 再矛盾。

对照 `RealExtractInvertibility.sigmoid_injective`：`sigmoid` 严格单调且**值域在 `(0,1)`**，
同样零集为空、`σ 0 = 1/2 ≠ 0`——`sigmoidZ` 是这个事实的整数刻度版。 -/
theorem neg_zeroFixing_sigmoidZ : ¬ ZeroFixing act_sigmoidZ := by
  intro h
  have h0 : act_sigmoidZ 0 = 0 := (h 0).mpr rfl
  exact absurd h0 (by norm_num [act_sigmoidZ])

/-- **判定 4（严格单调、零点平移）**：整数 softplus 代用 `n ↦ n+1` **不**满足零集假设
（见证 `n = -1`：`act_softplusZ (-1) = 0` 而 `-1 ≠ 0`；
与 `RealActDerivatives.softplus_strictMono` + `softplus_pos` 对照：
实数 `softplus` 处处为正，零集为空——**这是「实数零集为空」与「整数代用零点在 -1」
的差异，已在诚实边界标注**）。 -/
theorem neg_zeroFixing_softplusZ : ¬ ZeroFixing act_softplusZ :=
  zeroFixing_false_of_witness act_softplusZ (-1) (by norm_num) (by norm_num [act_softplusZ])

/-- **判定 5（严格单调、零点平移）**：整数 hardswish 门控代用 `n ↦ n+1`
**不**满足零集假设（`hardSigmoid` 在 `-3` 处取 `0`，整数代用把零点平移到 `-1`）。 -/
theorem neg_zeroFixing_hswishZ : ¬ ZeroFixing act_hswishZ :=
  zeroFixing_false_of_witness act_hswishZ (-1) (by norm_num) (by norm_num [act_hswishZ])

/-- **判定 6（严格单调、零点平移）**：整数 modReLU 门控代用 `n ↦ n+1`
**不**满足零集假设（对应 ℂ 上 `modReLU b`：`b < 0` 时零集是整个圆盘 `{|z| ≤ -b}`，
`b > 0` 时零集为空——都不是 `{0}`；仅 `b = 0` 时成立，那时它就是恒等映射）。 -/
theorem neg_zeroFixing_mreluZ : ¬ ZeroFixing act_mreluZ :=
  zeroFixing_false_of_witness act_mreluZ (-1) (by norm_num) (by norm_num [act_mreluZ])

/-! ## 六、激活函数判定表 —— 否定侧（`ZeroFixing` 为假，机器验证反例） -/

/-- **否定 1（ReLU）**：`reluZ` 不满足零集假设（回收 B11 的
`reluZ_not_zeroFixing`；见证 `reluZ (-4) = 0` 而 `-4 ≠ 0`）。 -/
theorem neg_zeroFixing_reluZ : ¬ ZeroFixing reluZ :=
  reluZ_not_zeroFixing

/-- **否定 2（符号保持的失效机制）**：整数 ReLU 在负半轴把 `y` 与 `y+1`
都送到 `0`，故**不是**单射——这是「零集假设不成立」的几何根源。 -/
theorem reluZ_not_injective : ¬ Function.Injective reluZ := by
  intro h
  have h1 : reluZ (-1) = reluZ 0 := by norm_num [reluZ]
  have : (-1 : ℤ) = 0 := h h1
  norm_num at this

/-- **否定 3（一般失败机制，结构性判据）**：若 `act 0 = 0` 且在整数负半轴上
「到 `-1` 为止」恒等，则 `act` **必然**不满足零集假设
（`act (-1) = 0` 把非零的 `-1` 送入零集）。

这是 ReLU / leaky ReLU 在整数编译模型下失败的**同一机制**的形式化：
两者在负半轴都有「把非零压到 0」的邻域。
（`h0` 与结论无关，保留作接口形状，用 `_h0` 命名避免 linter 警告。） -/
theorem zeroFixing_not_strictMonoOfNeg (act : ℤ → ℤ) (_h0 : act 0 = 0) (hneg : act (-1) = 0) :
    ¬ ZeroFixing act :=
  zeroFixing_false_of_witness act (-1) (by norm_num) hneg

/-- **否定 4（负—正—负的振荡零集 / 多重零点）**：若 `act (-1) = 0` 与 `act 2 = 0`
同时成立，则 `ZeroFixing` 为假（两个零点中至多一个是 `0`）。
用于覆盖**在负半轴取负后再变正**的激活（这类激活的零点既非唯一、也不单调）。

**实现说明**：`h2`（`act 1 = 0`）对结论多余，保留作接口形状，用 `_h2` 命名。 -/
theorem neg_zeroFixing_of_neg_neg_zero (act : ℤ → ℤ) (h1 : act (-1) = 0) (_h2 : act 1 = 0)
    (h3 : act 2 = 0) : ¬ ZeroFixing act := by
  intro h
  have hz1 : (-1 : ℤ) = 0 := (h (-1)).mp h1
  have hz3 : (2 : ℤ) = 0 := (h 2).mp h3
  omega

/-- **零集假设 ⟹ 单射 的分析（为什么它不成立）**：`ZeroFixing act` 只约束
`act` 的**零纤维** `act ⁻¹ {0}`，对非零值处的纤维**完全不加限制**。
故 `act x = act y ≠ 0` 且 `x ≠ y` 与 `ZeroFixing` 相容——
正确的反例见下一条。 -/
theorem zeroFixing_not_imp_injective :
    ¬ (∀ act : ℤ → ℤ, ZeroFixing act → Function.Injective act) := by
  intro h
  have hσ : ZeroFixing (fun y : ℤ => if y = 0 then (0 : ℤ) else 1) := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp
    · simp only [if_neg hy]
      exact ⟨fun h1 => absurd h1 (by norm_num : ¬((1 : ℤ) = 0)), fun h1 => absurd h1 hy⟩
  have hinj := h _ hσ
  have h12 : (fun y : ℤ => if y = 0 then (0 : ℤ) else 1) 1
      = (fun y : ℤ => if y = 0 then (0 : ℤ) else 1) 2 := by norm_num
  have : (1 : ℤ) = 2 := hinj h12
  norm_num at this

/-- **单射 + `σ 0 = 0` ⟹ 零集假设**（成立的反向蕴含）。
证法：`act y = 0` 与 `act 0 = 0`（`h0`）给出 `act y = act 0`，由单射得 `y = 0`。 -/
theorem injective_of_zeroFixing_sufficient (act : ℤ → ℤ) (h0 : act 0 = 0)
    (hinj : Function.Injective act) : ZeroFixing act := by
  intro y
  exact ⟨fun hy => hinj (hy.trans h0.symm), fun hy => hy ▸ h0⟩

/-- **三者的正确关系（本文件对判据结构的最终澄清）**：
- **单射 + `σ 0 = 0` ⟹ 零集假设**（`injective_of_zeroFixing_sufficient`，成立）；
- **零集假设 ⟹ 单射**为**假**（`zeroFixing_not_imp_injective`）；
- **单射 ⟹ 零集假设**为**假**（`sigmoid`：单射、处处非零，`σ 0 = 1/2 ≠ 0`）。

因此「严格单调 + `σ 0 = 0`」（判据 1）之所以是**充分条件**，
是因为 `StrictMono` 顺带给出单射、`σ 0 = 0` 给出归一——
两者合起来**恰好**落在 `injective_of_zeroFixing_sufficient` 的前提上；
而判据 2/3 则完全绕开单射、直接判定零集（故更弱、更通用）。

**STYLE §5 纪律的应用（本轮实测）**：本文件初稿曾把「单射 ⟺ 零集假设（在 `σ 0 = 0` 下）」
写成**双向**定理。**代小整数复核即知 mp 方向为假**
（`act y = if y = 0 then 0 else 1`：零集恰为 `{0}` 却不单射）——
故**改命题为单向**并留下机器验证反例，而非硬证一条假命题。 -/
theorem zeroFixing_relations_summary :
    (∀ σ : ℤ → ℤ, σ 0 = 0 → Function.Injective σ → ZeroFixing σ) ∧
      ¬ (∀ σ : ℤ → ℤ, ZeroFixing σ → Function.Injective σ) :=
  ⟨injective_of_zeroFixing_sufficient, zeroFixing_not_imp_injective⟩

/-! ## 七、ℝ 侧激活的可判定判定（引入既有激活定义）

以下 `act_relu` / `act_leakyRelu` / `act_siluR` / `act_geluTanhR` / `act_sigmoidR` /
`act_softplusR` / `act_hswishR` 是把 §五 的整数代用**沿既有实数激活的定义照抄**得到的
ℝ 版判定对象。`act_sigmoidR` 复用 `RealSwiGLU.sigmoid`（= `RealExtractInvertibility.sigmoid`
的逐字同式重定义），`act_siluR` 复用 `RealActComplete.silu`，`act_softplusR` 复用
`RealActDerivatives.softplus`，`act_hswishR` 复用 `RealActComplete.hardSwish`。

`act_geluTanhR` 需要 `geluGate x = (1 + tanh x)/2`——该定义在 `RealExtractInvertibility`
里，但如文件头所述**不能**通过 import 取得。故本文件**就地重定义 `geluGateFid`**
（与 `RealExtractInvertibility.geluGate` 逐字同式），并**独立重证**其零点唯一性与
§九 的门控单调/正性。 -/

/-- `RealExtractInvertibility.geluGate` 的**本地等价重定义**（避免 import 冲突；
两处定义式逐字相同：`(1 + tanh x)/2`）。 -/
def geluGateFid (x : ℝ) : ℝ := (1 + Real.tanh x) / 2

/-- ℝ 版 ReLU（回收 `RealNonlinear.relu`）。 -/
def act_relu (x : ℝ) : ℝ := relu x

/-- ℝ 版 leaky ReLU（负半轴斜率 `1/2`、正半轴斜率 `1`；ℝ 上除法无整数截断问题，
故与整数版**同一个约定**）。 -/
def act_leakyRelu (x : ℝ) : ℝ := if 0 ≤ x then x else x / 2

/-- ℝ 版 SiLU：`x · σ(x)`（回收 `RealActComplete.silu`）。 -/
def act_siluR (x : ℝ) : ℝ := silu x

/-- ℝ 版 GELU(tanh)：`x · (1 + tanh x)/2`（用本文件的 `geluGateFid`）。 -/
def act_geluTanhR (x : ℝ) : ℝ := x * geluGateFid x

/-- ℝ 版 sigmoid（复用 `RealSwiGLU.sigmoid`，经 `RealActComplete` 传递）。 -/
def act_sigmoidR (x : ℝ) : ℝ := sigmoid x

/-- ℝ 版 softplus（回收 `RealActDerivatives.softplus`）。 -/
def act_softplusR (x : ℝ) : ℝ := softplus x

/-- ℝ 版 hard-swish（回收 `RealActComplete.hardSwish`）。 -/
def act_hswishR (x : ℝ) : ℝ := hardSwish x

/-- **`tanh` 在正半轴为正**（`RealExtractInvertibility.tanh_pos_of_pos` 的独立重证——
本文件不能 import 该模块，故就地证明，供 §七 的 `tanh_eq_zero_iff` 使用）。
（mathlib 4.14 **没有** `Real.tanh_pos_iff` / `Real.tanh_pos_of_pos`
——已 grep `.lake/packages/mathlib` 确认
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean` 只有
`Real.sinh_strictMono`/`sinh_pos_iff`/`sinh_neg_iff`/`sinh_nonneg_iff`。） -/
theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) hcx

/-- **`tanh` 恒大于 `-1`**（`RealExtractInvertibility.neg_one_lt_tanh` 的独立重证——
mathlib 4.14 **没有** `Real.neg_one_lt_tanh`，故就地证明）。
证明：`tanh = sinh/cosh`，`-1 < sinh/cosh ⟺ -cosh < sinh ⟺ 0 < cosh + sinh = exp x`。

**STYLE 陷阱规避**：`lt_div_iff₀ hcx` 把 `-1 < sinh/cosh` 化为 `-1 * cosh x < sinh x`。
此时 `linarith` 需要把 `-1 * cosh x` 归一到 `-cosh x` 才能与
`cosh x + sinh x = exp x` 对齐，而**它不会自动归一**（首轮实测：
目标残留 `-1 * cosh x` 项，`linarith` 报 `failed to find a contradiction`）。
**安全写法**：先 `have hmul : -1 * Real.cosh x = -Real.cosh x := by ring`
显式归一，再把两者一起喂给 `linarith`。 -/
theorem neg_one_lt_tanh_fid (x : ℝ) : -1 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  rw [lt_div_iff₀ hcx]
  have hsum : Real.cosh x + Real.sinh x = Real.exp x := Real.cosh_add_sinh x
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have hmul : -1 * Real.cosh x = -Real.cosh x := by ring
  linarith [hsum, hpos, hmul]

/-- **`tanh` 的零点唯一**（`Real.tanh 0 = 0`，正半轴为正、负半轴为负）。
证明只用 `Real.tanh_neg`、`Real.tanh_zero` 与本文件的 `tanh_pos_of_pos`
——**不依赖** mathlib 4.14 缺失的 `Real.tanh_pos_iff`。 -/
theorem tanh_eq_zero_iff (x : ℝ) : Real.tanh x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hlt | heq | hgt
    · have hpos : 0 < Real.tanh (-x) := tanh_pos_of_pos (by linarith)
      rw [Real.tanh_neg, h] at hpos
      simp only [neg_zero] at hpos
      exact absurd hpos (lt_irrefl (0 : ℝ))
    · exact heq
    · exact absurd h (ne_of_gt (tanh_pos_of_pos hgt))
  · intro h
    rw [h, Real.tanh_zero]

/-- **ℝ 判定 2（门控无零点）**：`geluGateFid x = (1 + tanh x)/2` **恒不为零**
——值域在 `(0, 1)`。

**注意 数值复核纠正了一条假命题（STYLE §5 纪律，本轮实测命中）**：
本文件初稿把这里写成 **`geluGateFid x = 0 ↔ x = 0`**——**该命题为假**
`geluGateFid 0 = (1 + tanh 0)/2 = 1/2 ≠ 0`，门控在 `0` 处取 `1/2` 而非 `0`。
（探针报 `unsolved goals: ⊢ geluGateFid x = x`，正是这条假 iff 的反向分支。）
**真正满足零集假设的是乘积 `act_geluTanhR x = x · gate x`**（见判定 3），
其零集 `{0}` 来自**因子 `x`**，而非门控。
故此处把命题**改正**为门控的正性（值域 `(0,1)`），
它才是 `x · gate x` 零集推导所需的真事实。 -/
theorem geluGateFid_pos (x : ℝ) : 0 < geluGateFid x := by
  unfold geluGateFid
  have h := neg_one_lt_tanh_fid x
  linarith

/-- **门控值域含于 `(0,1)`**：`0 < gate x ∧ gate x < 1`。
下界取自 `neg_one_lt_tanh_fid`；上界 `tanh x < 1` 的证明与 §八 的
`abs_tanh_lt_one` 是同一段 `Real.cosh_sq` 论证的**复制**（§八 版本在 `abs`
下给出完整严格界），此处为就近使用而重复展开，并未调用 §八 的引理。 -/
theorem geluGateFid_bounds (x : ℝ) : 0 < geluGateFid x ∧ geluGateFid x < 1 := by
  refine ⟨geluGateFid_pos x, ?_⟩
  unfold geluGateFid
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  have hsq : Real.sinh x ^ 2 < Real.cosh x ^ 2 := by
    rw [Real.cosh_sq]; linarith [sq_nonneg (Real.sinh x)]
  have hs : |Real.sinh x| < Real.cosh x := by
    calc |Real.sinh x| = Real.sqrt (Real.sinh x ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (Real.cosh x ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
      _ = |Real.cosh x| := Real.sqrt_sq_eq_abs _
      _ = Real.cosh x := abs_of_pos hcx
  have htanh : Real.tanh x < 1 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_lt_one hcx]
    exact lt_of_le_of_lt (le_abs_self _) hs
  linarith

/-- **ℝ 判定 3（GELU(tanh) 满足零集假设）**：`x · gate x = 0 ↔ x = 0`。
证明只用 `geluGateFid_pos`（`gate` 恒正）与 `mul_eq_zero`——
**不使用任何单调性定理**，故这是零集判据的**独立证据**。 -/
theorem zeroFixingR_geluTanhR : ZeroFixingR act_geluTanhR := by
  intro y
  unfold act_geluTanhR
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact h1
    · exact absurd h2 (ne_of_gt (geluGateFid_pos y))
  · intro h
    rw [h]
    ring

/-- **ℝ 判定 4（ReLU 不满足零集假设）**：`relu (-1) = 0` 而 `-1 ≠ 0`
（回收 `RealExtractInvertibility.relu_not_injOn_nonpos` 的否定结构）。 -/
theorem neg_zeroFixingR_relu : ¬ ZeroFixingR act_relu := by
  intro h
  have h1 : act_relu (-1) = 0 := by norm_num [act_relu, relu]
  have : (-1 : ℝ) = 0 := (h (-1)).mp h1
  norm_num at this

/-- **ℝ 判定 5（leaky ReLU 满足零集假设）**：判据 3（符号保持）的实例。
关键观察：`0 ≤ y` 时分支取 `y` 本身，此时 **`y = 0` 当且仅当 `y = 0`**——
故 `|y| > 0` 的两种情形下用 `abs` 值即可关闭分支，无需相对 `0` 的不等式推理。
（此处刻意避免 `div_pos_of_neg_of_neg` / `div_neg_of_neg_of_pos`：
它们的**参数顺序**是「先分子后分母」，写反会报极具误导的 application type mismatch。） -/
theorem zeroFixingR_leakyRelu : ZeroFixingR act_leakyRelu := by
  intro y
  unfold act_leakyRelu
  by_cases h : 0 ≤ y
  · rw [if_pos h]
  · rw [if_neg h]
    constructor
    · intro hy
      -- 目标：`y = 0`。由 `y / 2 = 0` 两边乘 `2` 得 `y = 0`
      have hcancel : y / 2 * 2 = y := div_mul_cancel₀ y (by norm_num : (2 : ℝ) ≠ 0)
      rw [hy, zero_mul] at hcancel
      exact hcancel.symm
    · intro hy
      rw [hy]
      norm_num
  
/-- **ℝ 判定 6（SiLU 满足零集假设）**：`x · σ(x) = 0 ↔ x = 0`
（由 `σ > 0` 与 `mul_eq_zero`）。 -/
theorem zeroFixingR_silu : ZeroFixingR act_siluR := by
  intro y
  unfold act_siluR silu
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact h1
    · exact absurd h2 (ne_of_gt (sigmoid_bounds y).1)
  · intro h
    rw [h]
    ring

/-- **ℝ 判定 7（sigmoid 不满足零集假设）**：`sigmoid` 严格单调且值域在 `(0,1)`，
**没有**零点（`sigmoid 0 = 1/2 ≠ 0`）——与 `RealExtractInvertibility.sigmoid_injective`
对照，说明「严格单调 + 单射」**不**蕴含零集假设（还差 `σ 0 = 0`）。

**STYLE 陷阱规避**：`Real.exp (-0)` 在目标里显示为 `Real.exp (-0)`（**不是** `Real.exp 0`）
——`rw [Real.exp_zero]` 报 `did not find instance of the pattern Real.exp 0`。
必须先把 `-0` 归一：`simp only [neg_zero]` 或用 `show` 显式化。 -/
theorem neg_zeroFixingR_sigmoid : ¬ ZeroFixingR act_sigmoidR := by
  intro h
  have h1 : act_sigmoidR 0 = 0 := (h 0).mpr rfl
  unfold act_sigmoidR sigmoid at h1
  simp only [neg_zero] at h1
  rw [Real.exp_zero] at h1
  norm_num at h1

/-- **ℝ 判定 8（softplus 不满足零集假设）**：`softplus` 处处为正（`log (1 + e^x) > 0`），
零集为空。 -/
theorem neg_zeroFixingR_softplus : ¬ ZeroFixingR act_softplusR := by
  intro h
  have h1 : act_softplusR 0 = 0 := (h 0).mpr rfl
  unfold act_softplusR softplus at h1
  exact absurd h1 (ne_of_gt (softplus_pos 0))

/-- **ℝ 判定 9（hard-swish 不满足零集假设）**：`hardSwish x = x · hs x` 且
`hs` 在 `-3` 附近取到 `0`（`hardSigmoid (-3) = 0`），故 `-3` 是零点
（`hardSwish (-3) = 0`）而 `-3 ≠ 0`。 -/
theorem neg_zeroFixingR_hswish : ¬ ZeroFixingR act_hswishR := by
  intro h
  have h1 : act_hswishR (-3) = 0 := by
    unfold act_hswishR hardSwish hardSigmoid
    norm_num
  have : (-3 : ℝ) = 0 := (h (-3)).mp h1
  norm_num at this
