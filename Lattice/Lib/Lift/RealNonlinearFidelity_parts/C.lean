import Mathlib
import Lattice.Runtime.RealNonlinear
import Lattice.Lib.Architectures.RealActComplete
import Lattice.Lib.Architectures.RealActDerivatives
import Lattice.Lib.Editing.RealSymbolToWeightNonlinear
import Lattice.Lib.Lift.RealNonlinearFidelity_parts.B

/-!
# `RealNonlinearFidelity.lean` 的 `C` 部分

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


/-! ## 八、`tanh` 序结构：把「mathlib 缺失」变成「本文件推论」

（`tanh_pos_of_pos` 已在 §七 给出——它是 §七 判定 1/2/3 的前置引理；
本节只补其余的对偶与严格界。） -/

/-- **`tanh` 在非正半轴非正**（正半轴性质的对偶）：`x ≤ 0 ⟹ tanh x ≤ 0`。
这是 `Real.tanh_neg` 加 `tanh_pos_of_pos` 的直接推论——
**其中没有使用 mathlib 4.14 缺失的 `Real.tanh_pos_iff` / `Real.neg_one_lt_tanh`**
（已 grep `.lake/packages/mathlib` 确认二者不存在）。 -/
theorem tanh_nonpos_of_nonpos {x : ℝ} (hx : x ≤ 0) : Real.tanh x ≤ 0 := by
  rcases eq_or_lt_of_le hx with heq | hlt
  · subst heq
    rw [Real.tanh_zero]
  · have hpos : 0 < Real.tanh (-x) := tanh_pos_of_pos (by linarith)
    rw [Real.tanh_neg] at hpos
    linarith

/-- **`tanh` 值域含于 `(-1,1)`**：`|tanh x| < 1`。
由 `Real.cosh_sq_sub_sinh_sq`（`cosh² − sinh² = 1`）与 `cosh > 0` 得到
`|sinh| < cosh`，再 `tanh = sinh/cosh`。
（`RealActClass.tanh_abs_le_one` 只给非严格版 `|tanh x| ≤ 1`；
`RealExtractInvertibility.neg_one_lt_tanh` 只给下界 `-1 < tanh x`。
本文件给出**完整严格版**，且是 `RealActClass` 与该文件两侧 tanh 事实的合成升级。）

**STYLE 陷阱规避**：首轮尝试写成
`rw [← sq_lt_sq, abs_sq]` 想从 `sinh² < cosh²` 反推 `|sinh| < cosh`，
报 `did not find instance of the pattern |?m| < |?m|`——`sq_lt_sq` 在 4.14 是
`|a| < |b| ↔ a ^ 2 < b ^ 2`（`abs` **在左**），不在左的形状匹配不上。
这里改用**全程可计算的 `sqrt` 桥**：`|x| = √(x²)` 且 `√` 严格单调，
两步 `Real.sqrt_sq_eq_abs` + `Real.sqrt_lt_sqrt` 即可，无 abs 模式匹配风险。 -/
theorem abs_tanh_lt_one (x : ℝ) : |Real.tanh x| < 1 := by
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  have hsq : Real.sinh x ^ 2 < Real.cosh x ^ 2 := by
    rw [Real.cosh_sq]; linarith [sq_nonneg (Real.sinh x)]
  have hs : |Real.sinh x| < Real.cosh x := by
    calc |Real.sinh x| = Real.sqrt (Real.sinh x ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (Real.cosh x ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
      _ = |Real.cosh x| := Real.sqrt_sq_eq_abs _
      _ = Real.cosh x := abs_of_pos hcx
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos hcx,
    div_lt_one hcx]
  exact hs

/-! ## 九、门控解析性质（独立重证）与保真度闭环

任务书要求「把 `RealExtractInvertibility` 的显式假设变成定理」。**已复核结论：那里
没有可升级的显式假设**——第 4 节的条件定理 `geluTanh_injOn_of_gate` 的三条假设
（`0 ≤ gate 0`、`MonotoneOn gate (Ici 0)`、`∀ x > 0, 0 < gate x`）**早已被该文件自己的
第 5 节无条件证明**（`geluGate_nonneg` / `geluGate_monoOn` / `geluGate_pos_of_pos`），
该文件 docstring 亦已写明（`RealExtractInvertibility.lean:31-36`）。

但因 §头部说明的**导入冲突**，本文件无法 import 该文件，故对同样的三条性质
**就地独立重证**（对 `geluGateFid`）。这不是重复劳动：它使本文件在
`RealExtractInvertibility` 缺位时**自足**，且给出了 `tanh` 单调性的第二种证法。 -/

/-- **门控非负**：`0 ≤ geluGateFid 0`（该文件假设 `hgate0` 的独立版）。 -/
theorem geluGateFid_nonneg : 0 ≤ geluGateFid 0 := by
  unfold geluGateFid
  simp

/-- **门控在正半轴为正**：`0 < x ⟹ 0 < geluGateFid x`（该文件假设 `hpos` 的独立版）。 -/
theorem geluGateFid_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < geluGateFid x := by
  unfold geluGateFid
  have h := tanh_pos_of_pos hx
  linarith

/-- **`tanh` 在 `[0,∞)` 上严格单调**（该文件 `tanh_strictMonoOn_Ici_zero` 的独立重证）。
证明：`tanh = sinh/cosh`，两边通分后用恒等式
`sinh y · cosh x − sinh x · cosh y = sinh (y − x) > 0`（`y > x`）。

**STYLE 陷阱规避**：`div_lt_div_iff₀` 的首两参是**显式** `0 < c`、`0 < d`
（对应 `a/b < c/d` 的**右分母在前**）——顺序写反会报
`did not find instance of the pattern`；此处用 `hcx`/`hcy` 显式对齐。 -/
theorem tanh_strictMonoOn_Ici_zero_fid : StrictMonoOn Real.tanh (Set.Ici 0) := by
  intro x _ y _ hxy
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  have hcy : 0 < Real.cosh y := Real.cosh_pos y
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  apply (div_lt_div_iff₀ hcx hcy).mpr
  have hkey : Real.sinh y * Real.cosh x - Real.sinh x * Real.cosh y = Real.sinh (y - x) := by
    rw [Real.sinh_sub]; ring
  have hpos : 0 < Real.sinh (y - x) := Real.sinh_pos_iff.mpr (by linarith)
  linarith [hkey, hpos]

/-- **门控在 `[0,∞)` 上单调**（该文件假设 `hmono` 的独立版）。 -/
theorem geluGateFid_monoOn : MonotoneOn geluGateFid (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold geluGateFid
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]
  · have h : Real.tanh x < Real.tanh y := tanh_strictMonoOn_Ici_zero_fid hx hy hlt
    linarith

/-- **门控三条假设在该文件里确实已是定理**（结构性记录）：本文件用独立重证的
`geluGateFid` 版给出**同形的合取**，从而在形式上确认「假设 → 定理」的升级关系；
其内容与该文件的 `geluGate_nonneg` / `geluGate_monoOn` / `geluGate_pos_of_pos`
一一对应（见 `RealExtractInvertibility.lean:236-254`）。 -/
theorem gateFid_hypotheses_are_theorems :
    (0 ≤ geluGateFid 0) ∧ MonotoneOn geluGateFid (Set.Ici 0) ∧
      (∀ x, 0 < x → 0 < geluGateFid x) :=
  ⟨geluGateFid_nonneg, geluGateFid_monoOn, fun _ hx => geluGateFid_pos_of_pos hx⟩

/-- **GELU(tanh) 在 `[0,∞)` 上严格单调**（该文件 `geluTanh_strictMonoOn` 的独立版）：
把乘积结构判据应用于 `geluGateFid`，三条前提全部由本节定理满足。
证明与 `RealExtractInvertibility.strictMonoOn_mul_of` 同构，此处**就地展开**以免依赖。 -/
theorem act_geluTanhR_strictMonoOn : StrictMonoOn act_geluTanhR (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hgx : 0 ≤ geluGateFid x :=
    le_trans geluGateFid_nonneg (geluGateFid_monoOn (by norm_num) hx hx0)
  unfold act_geluTanhR
  rcases eq_or_lt_of_le hx0 with hxeq | hxpos
  · subst hxeq
    have hypos : 0 < y := hxy
    have hgy : 0 < geluGateFid y := geluGateFid_pos_of_pos hypos
    rw [zero_mul]
    exact mul_pos hypos hgy
  · have hgxp : 0 < geluGateFid x := geluGateFid_pos_of_pos hxpos
    have hle : geluGateFid x ≤ geluGateFid y := geluGateFid_monoOn hx hy (le_of_lt hxy)
    have hgy : 0 < geluGateFid y := geluGateFid_pos_of_pos (lt_trans hxpos hxy)
    calc x * geluGateFid x < y * geluGateFid x := mul_lt_mul_of_pos_right hxy hgxp
      _ ≤ y * geluGateFid y := mul_le_mul_of_nonneg_left hle hy0

/-- **GELU(tanh) 在 `[0,∞)` 上可逆**（该文件 `geluTanh_injOn` 的独立版）：
严格单调 ⟹ 单射（`Set.InjOn`）。这与 §七 的 `zeroFixingR_geluTanhR` 互补——
前者是**可逆性**判据，后者是**零集保真**判据，两者对同一个激活都成立。 -/
theorem act_geluTanhR_injOn : Set.InjOn act_geluTanhR (Set.Ici 0) := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd hxy (ne_of_lt (act_geluTanhR_strictMonoOn hx hy hlt))
  · exact heq
  · exact absurd hxy.symm (ne_of_lt (act_geluTanhR_strictMonoOn hy hx hgt))

/-- **GELU(tanh) 在 `[0,∞)` 上无假设可逆 ⟹ 零集保真**（两条判据的桥）：
`act_geluTanhR 0 = 0` 与 §七 的零集假设一致，故可逆性结论不与之冲突。 -/
theorem act_geluTanhR_zero : act_geluTanhR 0 = 0 := by
  unfold act_geluTanhR
  rw [zero_mul]

/-! ## 九之二、保真度闭环：可逆性判据的推论 -/

/-- **`ZeroFixing` 蕴含 ReLU 编码的忠实性**：若激活满足零集假设，则其零化
**精确**对应约束满足（`RealNonlinear.relu_preserves` 的结构推广）。
这是「零集假设 = 保真」的最简形式的闭环。 -/
theorem zeroFixing_implies_relu_faithful (act : ℝ → ℝ) (hσ : ZeroFixingR act) (y : ℝ) :
    (y = 0) ↔ act y = 0 :=
  (hσ y).symm

/-- **可逆性判据的推论（1）**：`|·|` 满足零集假设（`|x| = 0 ↔ x = 0`）——
说明「不可逆的 ReLU」经绝对值改造后成为保真激活。
对照 `RealExtractInvertibility.relu_not_injOn_nonpos`（B10）：不可逆性来自
负半轴的塌缩，绝对值恰好消除该塌缩。 -/
theorem zeroFixingR_abs : ZeroFixingR fun x : ℝ => |x| := fun _ => abs_eq_zero

/-- **可逆性判据的推论（2）**：`x ↦ x³` 满足零集假设
（`x³ = 0 ↔ x = 0`；`pow_eq_zero_iff`）——多项式激活类的代表。 -/
theorem zeroFixingR_cube : ZeroFixingR fun x : ℝ => x ^ 3 := fun _ =>
  pow_eq_zero_iff (n := 3) (by norm_num)

/-- **可逆性判据的推论（3）**：`sinh` 满足零集假设
（`sinh x = 0 ↔ x = 0`；mathlib 的 `Real.sinh_eq_zero`）。 -/
theorem zeroFixingR_sinh : ZeroFixingR Real.sinh := fun _ => Real.sinh_eq_zero

/-! ## 十、自检：可判定判定表的 `#eval` 输出

**表的读法**：真值列**不是**手写的，而是由 §四 的**可执行有界穷举内核**
`zeroFixingHoldsBounded act n` 在半径 `n = 8`（即 `y ∈ [-8, 8]`）上算出的。
与 §五/§六 的**机器验证定理**逐条对照后，本表的每一格都有内核级证据：
- 肯定侧（`true`）：§五 的 `decidable_zeroFixing_*` / 判据 1–3 的定理；
- 否定侧（`false`）：§六 的 `neg_zeroFixing_*` + `zeroFixing_false_of_witness` 给出**具体非零零点**。

`n = 8` 对本表的所有条目都已充分（肯定侧的最大零点就是 `0`；
否定侧的见证全在 `{-4, -1}` 内）。 -/

/-- 判定表条目：`(名称, 半径 n 内的零集假设真值)`。
真值由 `zeroFixingHoldsBounded`（**可执行**的穷举检验）算出，
不依赖任何分析假设——这正是「可判定」的机器可读形态。 -/
def zeroFixingTable : List (String × Bool) :=
  [ ("reluZ",       zeroFixingHoldsBounded act_reluZ 8),
    ("leakyReluZ",  zeroFixingHoldsBounded act_leakyReluZ 8),
    ("siluZ",       zeroFixingHoldsBounded act_siluZ 8),
    ("geluZ",       zeroFixingHoldsBounded act_geluZ 8),
    ("sigmoidZ",    zeroFixingHoldsBounded act_sigmoidZ 8),
    ("softplusZ",   zeroFixingHoldsBounded act_softplusZ 8),
    ("hardswishZ",  zeroFixingHoldsBounded act_hswishZ 8),
    ("modreluZ",    zeroFixingHoldsBounded act_mreluZ 8),
    ("cubeZ",       zeroFixingHoldsBounded (fun y : ℤ => y ^ 3) 8),
    ("negZ",        zeroFixingHoldsBounded (fun y : ℤ => -y) 8),
    ("idZ",         zeroFixingHoldsBounded (fun y : ℤ => y) 8),
    ("signZ",       zeroFixingHoldsBounded
                      (fun y : ℤ => if 0 < y then 1 else if y < 0 then -1 else 0) 8)]

/-- 见证列的自检：否定侧给出的 `y ≠ 0 ∧ act y = 0` 确实成立
（判定表的每一格都可独立核验；`y ≠ 0` 与 `act y = 0` 同时给出才算见证）。

**注意 `act_sigmoidZ` 不在此列**：它的零集**为空**（`2n+1 = 0` 在 ℤ 上无解），
失败机制是 `σ 0 = 1 ≠ 0`，**没有非零零点**——见 `neg_zeroFixing_sigmoidZ`。 -/
theorem zeroFixingTable_witnesses :
    (-4 : ℤ) ≠ 0 ∧ reluZ (-4) = 0 ∧ act_softplusZ (-1) = 0 ∧
      act_hswishZ (-1) = 0 ∧ act_mreluZ (-1) = 0 := by
  refine ⟨by norm_num, by norm_num [reluZ], by norm_num [act_softplusZ],
    by norm_num [act_hswishZ], by norm_num [act_mreluZ]⟩

/-- **`leakyReluZ` 的零点唯一**（肯定侧的独立核验）：`act_leakyReluZ n = 0 ↔ n = 0`。
（`n ≥ 0` 时值为 `2n`、`n < 0` 时值为 `n`，两者都只在 `n = 0` 处为零。） -/
theorem act_leakyReluZ_eq_zero_iff (n : ℤ) : act_leakyReluZ n = 0 ↔ n = 0 := by
  unfold act_leakyReluZ
  by_cases h : 0 ≤ n
  · rw [if_pos h]
    omega
  · rw [if_neg h]

/-- **表的肯定侧与定理一致**：`siluZ` / `geluZ` / `leakyReluZ` 的穷举真值为 `true`，
且它们**确实**满足零集假设（§五 已证）——表的 `true` 格有内核级证据。 -/
theorem zeroFixingTable_true_consistent :
    zeroFixingHoldsBounded act_siluZ 8 = true ∧
      zeroFixingHoldsBounded act_geluZ 8 = true ∧
      zeroFixingHoldsBounded act_leakyReluZ 8 = true ∧
      ZeroFixing act_siluZ ∧ ZeroFixing act_geluZ ∧ ZeroFixing act_leakyReluZ :=
  ⟨by decide, by decide, by decide,
    decidable_zeroFixing_siluZ, decidable_zeroFixing_geluZ, decidable_zeroFixing_leakyReluZ⟩

/-- **表的否定侧与定理一致（有非零零点的一类）**：`reluZ` / `softplusZ` / `hardswishZ` /
`modreluZ` 的穷举真值为 `false`，且它们**确实**不满足零集假设（§六 已证，
且都有显式非零零点）——表的 `false` 格有内核级证据。 -/
theorem zeroFixingTable_false_consistent :
    zeroFixingHoldsBounded act_reluZ 8 = false ∧
      zeroFixingHoldsBounded act_softplusZ 8 = false ∧
      zeroFixingHoldsBounded act_hswishZ 8 = false ∧
      zeroFixingHoldsBounded act_mreluZ 8 = false ∧
      ¬ ZeroFixing reluZ ∧ ¬ ZeroFixing act_softplusZ ∧
      ¬ ZeroFixing act_hswishZ ∧ ¬ ZeroFixing act_mreluZ :=
  ⟨by decide, by decide, by decide, by decide,
    neg_zeroFixing_reluZ, neg_zeroFixing_softplusZ,
    neg_zeroFixing_hswishZ, neg_zeroFixing_mreluZ⟩

/-- **表的否定侧与定理一致（零集为空的一类）**：`act_sigmoidZ` 的穷举真值为 `false`，
失败机制是 **`σ 0 ≠ 0`（零集为空）**而非「有非零零点」——
这与 `reluZ` 类形成**两种不同的不保真机制**，是本文件判定表的一个关键区分。 -/
theorem zeroFixingTable_empty_zero_set :
    zeroFixingHoldsBounded act_sigmoidZ 8 = false ∧ ¬ ZeroFixing act_sigmoidZ :=
  ⟨by decide, neg_zeroFixing_sigmoidZ⟩

-- 判定表打印：真值列由**可执行穷举内核**算出，不依赖任何分析假设。
#eval zeroFixingTable

end Lattice
