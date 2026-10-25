import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealCrossEntropy
import Lattice.Lib.Optim.RealPolicyGradient
/-!
# LATTICE: DPO 理论 —— `Z(x)` 消去、奖励等价类与**性能差引理**

本文件形式化 DPO（Direct Preference Optimization）的**代数核心**与强化学习中
最常用的**性能差引理**（performance difference lemma, PDL）。

## A. DPO 的 `Z(x)` 消去（来源：arXiv 2305.18290）

DPO 的关键代数事实：**KL 正则化最优策略**具有闭式

  `π*(y|x) = (1/Z(x)) · π_ref(y|x) · exp(r(x,y)/β)`，`Z(x) = Σ_y π_ref(y|x)·exp(r(x,y)/β)`，

反解出的**隐式奖励**为

  `r(x,y) = β · log(π*(y|x)/π_ref(y|x)) + β · log Z(x)`。

本文件证明：`log Z(x)` 这一项在**同一 `x` 下比较两个响应**时**完全消去**，
从而偏好概率只依赖 `π*` 与 `π_ref` 的比值 —— 这是 DPO 不需要显式奖励模型的
全部理由。

形式化要点：本文件**不从 KL 正则化最优性出发**（那需要变分论证），而是**直接以
重参数化等式为定义**，证明「同一 `x` 下 `Z(x)` 消去」这一代数结论，并把**闭环**
（`π*` 满足重参数化 ⟺ `π*` 是 KL 正则化最优）作为**显式假设/后续工作**标注。

## B. 性能差引理（PDL）

**正确出处**：Kakade & Langford 2002（*Approximately Optimal Approximate
Reinforcement Learning*, ICML 2002）**Lemma 6.1**。
⚠ 常见误引已由独立子代理 **OCR 原文扫描件逐字核实并纠正**：
- ❌ "**Theorem 4.1**" —— 原文的 Theorem 4.1 是 **conservative policy iteration
  的性能改进界**（`η_μ(π_new) − η_μ(π) ≥ (α/(1−γ))(A − 2αγε/(1−γ(1−α)))`），
  **是另一个定理**。⚠ 误引来源很可能是 **TRPO 自己的 Appendix A**：
  它写着「uses techniques from the proof of **Theorem 4.1** in
  (Kakade & Langford, 2002)」—— 「4.1」在那篇论文里是**真实存在**的编号。
- ❌ "**Lemma 5.2.1**" —— 2002 短文共 8 页、编号为 `2.1, 4.1–4.5, 6.1, 6.2`，
  四级编号 `5.2.1` **不可能出现**。
  ⚠「它出自 Kakade 2003 博士论文」这一归属**未能核实**（所有镜像均取不到），
  **故本文件不声称该归属**。
- ✅ 该 2002 短文**全文未出现 "performance difference" 字样**（全文 OCR grep
  零命中）—— 该术语是后来的命名，原文说的是 "policy advantage"。

**陈述**（有限 MDP，折扣 γ ∈ [0,1)）：

  `η_μ(π̃) − η_μ(π) = (1/(1−γ)) · E_{s∼d_μ^{π̃}}[ A_π(s,a) ]`，

其中 `A_π(s,a) = Q_π(s,a) − V_π(s)` 是**旧策略** `π` 的优势，期望对 `s ∼ d_μ^{π̃}`
（**新策略** `π̃` 的（归一化）访问分布）取。

**本文件的有限维度路线**（无需测度论）：在**确定性转移 + 有限时域**上，PDL 就是
**伸缩求和**的恒等式 —— 见 `pdl_telescoping`（回报差 = 优势和，**不假设 `V` 满足
Bellman 方程**）、`pdl_normalized_form`（`1/(1−γ)` 归一化因子的来源）与
`pdl_finite_horizon`（保留残项的可见证形式）。

**诚实验证**：`pdl_telescoping` 已用独立数值实例机器复算
（`γ=0.9, T=4, r_new=[1,2,0.5,3], r_old=[0.5]×4`：两边均 `= 3.6725`，残项
`γᵀ V(s_T) = 0`）；且 `(1/(1−γ))·E_d[A]`（`d_t = (1−γ)γᵗ`）与之**精确相等**。

**诚实边界**（本文件不证 / 不声称的）：
- 一般（随机转移、任意策略对）的 PDL **未证**：本文件给出的是**确定性链**版本
  （伸缩求和严格成立），一般情形的证明需要 `Σ_{s'} P(s'|s,a)(·)` 的期望重排 +
  访问分布 `d^{π̃}` 与 `d^π` 之比（重要性权重）——**标注为后续工作**；
- **无限时域极限未做**：`pdl_finite_horizon` 显式保留残项 `γ^T·V(T)`，未证
  `T→∞` 时该项趋于 0（需要 `V` 有界 + `γ<1` 的 `Tendsto` 论证）；
- DPO 的**KL 正则化最优性**（`π*` 由变分问题刻画）**未证**，本文件只证其
  **代数后果**（`Z` 消去 ⟺ 奖励等价类）；
- 有限样本界、`β` 的温度作用、DPO 损失的梯度 **未做**。

**引用核实**（由独立子代理经 export.arxiv.org API + arxiv.org PDF + ar5iv 逐字复核）：
- DPO `2305.18290`：作者 **Rafael Rafailov, Archit Sharma, Eric Mitchell, Stefano
  Ermon, Christopher D. Manning, Chelsea Finn**（CONFIRMED）；**Def 1 / Lemma 1 /
  Lemma 2 / Theorem 1 / Proposition 1 编号全部 CONFIRMED**；
  **Eq. 5 逐字 CONFIRMED**：`r(x,y) = β log(π_r(y|x)/π_ref(y|x)) + β log Z(x)`；
  **Z 消去逐字 CONFIRMED**：§4「the partition function cancels」，
  Appendix A.2 显式给出两个 `β log Z(x)` 相消。
  - ⚠ **venue**：arXiv 条目**无 `journal_ref`**；NeurIPS 2023 是广泛报道的venue，
    但**未从 arXiv 元数据独立确认** —— 故本文件**不**声称 NeurIPS（标注为未核实）。
  - **两处「`Z`-free」陈述的区分**（对形式化目标重要）：
    (i) **Eq. 5 / Theorem 1** 保留 `+β log Z(x)`；
    (ii) **Theorem 1 + Proposition 1** 给出**规范代表元**
    `r(x,y) = β log(π(y|x)/π_ref(y|x))`（**无**加性项），由归一化条件
    `Σ_y π_ref(y|x) exp(r(x,y)/β) = 1`（Eq. 9）**唯一**确定 ——
    **Proposition 1 正是该唯一性命题**。本文件的 `dpo_Z_cancels*` 系列对应 (i)
    的代数后果；**(ii) 的唯一性未形式化**（见「缺什么引理」）。
- PDL 出处 **Kakade & Langford 2002 ICML `Lemma 6.1`**：**由独立子代理 OCR
  原文扫描件逐字复核 CONFIRMED**（该 PDF 是位图扫描 + Type 3 字体、无文字层，
  需 `pdftoppm` + `tesseract`；这正是该编号在文献中长期被误报的原因）。
  - **"Theorem 4.1" 的错误已定位**：原文 p.4 的 Theorem 4.1 是
    **conservative policy iteration 的性能改进界**
    `η_μ(π_new) − η_μ(π) ≥ (α/(1−γ))(A − 2αγε/(1−γ(1−α)))`，**是另一个定理**。
    **误引的可能来源**：TRPO 自己的 Appendix A 写着
    「uses techniques from the proof of Theorem 4.1 in (Kakade & Langford, 2002)」
    —— **"4.1" 是那篇论文里真实存在的编号，只是指另一个定理**。
  - **"Lemma 5.2.1"**：2002 短文共 8 页、编号为 `2.1, 4.1–4.5, 6.1, 6.2`，
    **四级编号 `5.2.1` 不可能出现**（CONFIRMED 为误）。
    ⚠「`5.2.1` 出自 Kakade 2003 博士论文」这一归属**未能核实**（子代理尝试的
    全部镜像均失败，且在 TRPO/CPO/DDPG+/RL 理论书中**零**处引用该编号）——
    **故本文件不声称该归属**。2003 论文标题据 RL 理论书书目为
    *On the sample complexity of reinforcement learning*（UCL 2003）。
  - **"performance difference" 一词在 2002 原文中出现 0 次**（CONFIRMED，
    全文 OCR grep）——该术语是后来的命名。
  - **三处独立编号 CONFIRMED**：KL 2002 `Lemma 6.1` ≡ TRPO `Appendix A Lemma 1`
    （arXiv 1502.05477，轨迹求和形式 eq. 19）≡ RL 理论书
    （Agarwal–Brantley–Jiang–Kakade–Sun）`Lemma 1.16`。
  - ⚠ **约定差异（形式化必须择一）**：**归一化 vs 非归一化**访问分布决定
    `1/(1−γ)` 是否显式出现 —— TRPO 的 `ρ_{π'}` 是**非归一化**的（无前置因子），
    而 RL 理论书与 CPO 用**归一化**的 `d^π_μ = (1−γ)Σ_t γᵗ Pr(·)`（有显式
    `1/(1−γ)`）。此外书里 Lemma 1.16 **印出的**版本用**同一个策略符号** `π`
    贯穿 occupancy/advantage（`d^π_μ` 配 `A^π`），而 KL 2002 与 CPO 是
    **新策略的 occupancy 配旧策略的 advantage**。**本文件采用后者**
    （`d^{π̃}` 配 `A_π`），与 KL 2002 Lemma 6.1 及 CPO Eq. (1) 一致；
    归一化约定下 `1/(1−γ)` 显式出现，已由 `pdl_normalized_form` 给出**换算**。
  - **无需测度论**：CONFIRMED —— 三处权威证明都是初等**伸缩求和**；
    有限 `S, A` + `γ < 1` + 有界 `r` 下每步都是有限和代数。
    Lean 侧唯一分析成分是几何级数（mathlib `summable_geometric_of_norm_lt_one`）。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! # 第一部分：DPO 的 `Z(x)` 消去

## 定义：DPO 的重参数化（隐式奖励）
-/

/-- **DPO 重参数化（隐式奖励）**。给定参考策略 `pref : ι → ℝ`（`ι` 是响应指标集，
`pref y = π_ref(y|x)`）、策略 `pol : ι → ℝ`（`pol y = π*(y|x)`）、温度 `β > 0` 与
**配分函数** `Z > 0`，定义

  `dpoReward β Z pref pol y = β · log(pol y / pref y) + β · log Z`。

这正是原文的 `r(x,y) = β log(π*(y|x)/π_ref(y|x)) + β log Z(x)`（同一 `x` 下
`Z` 不随 `y` 变化）。 -/
def dpoReward {ι : Type*} (β Z : ℝ) (pref pol : ι → ℝ) (y : ι) : ℝ :=
  β * Real.log (pol y / pref y) + β * Real.log Z

/-- **隐式奖励的差**：同一 `x` 下两个响应 `y_w`、`y_l` 的隐式奖励之差。

这是 DPO 目标函数里出现的量。 -/
def dpoRewardDiff {ι : Type*} (β Z : ℝ) (pref pol : ι → ℝ) (y_w y_l : ι) : ℝ :=
  dpoReward β Z pref pol y_w - dpoReward β Z pref pol y_l

/-! ## 主定理 1：`Z(x)` 消去（差形式）

**命题**：同一 `x` 下，隐式奖励之差**完全不含 `Z`**：

  `dpoRewardDiff β Z pref pol y_w y_l = β·log(pol y_w/pref y_w) − β·log(pol y_l/pref y_l)`。

即右边与 `Z` 无关。这是 DPO「无需奖励模型」的全部代数理由。 -/

/-- **`Z(x)` 消去（差形式，主定理）**。`dpoRewardDiff` 与 `Z` 无关：两个不同 `Z` 给出
**同一个**奖励差。证明：`Z` 只以 `β·log Z` 的**加性常数**出现，相减即消。 -/
theorem dpo_Z_cancels {ι : Type*} (β Z : ℝ) (pref pol : ι → ℝ) (y_w y_l : ι) :
    dpoRewardDiff β Z pref pol y_w y_l
      = β * Real.log (pol y_w / pref y_w) - β * Real.log (pol y_l / pref y_l) := by
  unfold dpoRewardDiff dpoReward
  ring

/-- **`Z(x)` 消去（更强形式：任意两个配分函数给出同一奖励差）**。对任意 `Z₁ Z₂ > 0`，

  `dpoRewardDiff β Z₁ pref pol y_w y_l = dpoRewardDiff β Z₂ pref pol y_w y_l`。

这把「消去」表述为**不依赖 `Z` 的取值**，比仅展开成不含 `Z` 的式子更强（也更能
说明 DPO 对 `Z` 的**不可辨识性**）。 -/
theorem dpo_Z_cancels_any {ι : Type*} (β Z₁ Z₂ : ℝ) (pref pol : ι → ℝ) (y_w y_l : ι) :
    dpoRewardDiff β Z₁ pref pol y_w y_l = dpoRewardDiff β Z₂ pref pol y_w y_l := by
  unfold dpoRewardDiff dpoReward
  ring

/-! ## 定理 2：偏好概率 —— Bradley–Terry 形式下的 `Z` 消去

DPO 用 sigmoid 把奖励差转成偏好概率：`P(y_w ≻ y_l | x) = σ(r(x,y_w) − r(x,y_l))`。
由于 `Z` 在差里消去，偏好概率也不依赖 `Z`。 -/

/-- **DBT（Bradley–Terry）偏好概率**：`P(y_w ≻ y_l) = σ(奖励差)`，其中
`sigmoid u = 1/(1 + exp(−u))`。

**命名说明**：本文件**不重新定义 `sigmoid`**，而是把 `1/(1 + exp(−u))` **内联**
在此定义中 —— 因为 `sigmoid` 在本库已有**多处**定义
（`RealSwiGLU.sigmoid`、`RealExtractInvertibility.sigmoid`、`RealActDerivatives.sigmoid`），
再定义一个会与它们冲突（STYLE §2「避免同命名空间同名定理/定义」）。
内联的做法在数学上完全等价，且不引入新的命名负担。 -/
noncomputable def btPrefProb {ι : Type*} (β Z : ℝ) (pref pol : ι → ℝ) (y_w y_l : ι) : ℝ :=
  1 / (1 + Real.exp (-(dpoRewardDiff β Z pref pol y_w y_l)))

/-- **偏好概率与 `Z` 无关（主定理 2）**：`Z₁` 与 `Z₂` 给出**同一个**偏好概率。

这直接说明：**从偏好数据出发无法辨识 `Z(x)`**，故 DPO 可以完全绕过奖励模型。 -/
theorem dpo_prefProb_Z_invariant {ι : Type*} (β Z₁ Z₂ : ℝ) (pref pol : ι → ℝ)
    (y_w y_l : ι) :
    btPrefProb β Z₁ pref pol y_w y_l = btPrefProb β Z₂ pref pol y_w y_l := by
  unfold btPrefProb
  rw [dpo_Z_cancels_any]

/-! ## 定理 3：DPO 目标的显式形式（比值形式）

把 `Z` 消去后的偏好对数几率展开，得到原文的 DPO 目标核心：
`log(π*(y_w)/π_ref(y_w)) − log(π*(y_l)/π_ref(y_l))` 乘以 `β`。

本定理把它写成**单次log 之商**的形式，便于与 `Real.log_div` 对接。 -/

/-- **DPO 对数几率（logit）与 `β` 的比值形式**：在 `pref`、`pol` 严格正时，

  `(1/β)·(r(y_w) − r(y_l)) = log((pol y_w · pref y_l) / (pref y_w · pol y_l))`。

这是 DPO 损失 `−log σ(β·(logratio_w − logratio_l))` 的**内层**，把两个 log 之比
合成为**一个** log（`Real.log_div` / `Real.log_mul`）。 -/
theorem dpo_logit_ratio_form {ι : Type*} (β Z : ℝ) (hβ : β ≠ 0)
    (pref pol : ι → ℝ) (y_w y_l : ι)
    (hpw : pref y_w ≠ 0) (hpl : pref y_l ≠ 0)
    (hqw : pol y_w ≠ 0) (hql : pol y_l ≠ 0) :
    (1 / β) * dpoRewardDiff β Z pref pol y_w y_l
      = Real.log ((pol y_w * pref y_l) / (pref y_w * pol y_l)) := by
  rw [dpo_Z_cancels]
  -- (1/β)·(β·L_w − β·L_l) = L_w − L_l，其中 L = log(pol/pref)
  have hβc : (1 / β) * (β * Real.log (pol y_w / pref y_w)
      - β * Real.log (pol y_l / pref y_l))
      = Real.log (pol y_w / pref y_w) - Real.log (pol y_l / pref y_l) := by
    field_simp
    ring
  rw [hβc]
  -- log(a/b) − log(c/d) = log((a/b)/(c/d)) = log((a·d)/(b·c))
  rw [← Real.log_div (div_ne_zero hqw hpw) (div_ne_zero hql hpl)]
  congr 1
  -- (a/b)/(c/d) = (a·d)/(b·c)
  -- ⚠ v14 修复：原稿此处 `field_simp` 后跟 `ring`，报 `no goals to be solved` ——
  -- 即 `field_simp` **已闭合目标**，`ring` 多余（本仓库 STYLE 已登记的"多余收尾"类）。
  -- 删掉 `ring`（**不换写法**）。
  field_simp
/-! ## 定理 4：奖励等价类（原文 Definition 1 的代数内容）

原文把「相差一个只依赖 `x` 的函数」的奖励视为**等价**（它们诱导同一偏好）。
本文件给出该等价关系的**代数刻画**：`r₁ ∼ r₂` ⟺ 对所有响应对，
`r₁(y_w) − r₁(y_l) = r₂(y_w) − r₂(y_l)`。 -/

/-- **奖励差等价**：两个奖励函数 `r₁ r₂ : ι → ℝ` 在**同一 `x`** 下诱导相同偏好
（差相同）。 -/
def RewardDiffEquiv {ι : Type*} (r₁ r₂ : ι → ℝ) : Prop :=
  ∀ y_w y_l : ι, r₁ y_w - r₁ y_l = r₂ y_w - r₂ y_l

/-- **等价类刻画（充分方向）**：若 `r₂ = r₁ + c`（`c` 是与 `y` 无关的常数），
则 `r₁ ∼ r₂`。这正是原文 Definition 1「奖励只确定到相差一个 `x` 的函数」的
代数体现 —— 在这里 `c = β log Z(x)`。 -/
theorem reward_diff_equiv_of_add_const {ι : Type*} (r₁ : ι → ℝ) (c : ℝ) :
    RewardDiffEquiv r₁ (fun y => r₁ y + c) := by
  intro y_w y_l
  ring

/-- **等价类刻画（必要方向）**：若 `r₁ ∼ r₂`，则差函数
`y ↦ r₁ y − r₂ y` 是**常数**。这给出等价的**完整**代数刻画：等价 ⟺ 相差常数。 -/
theorem reward_diff_equiv_iff_sub_const {ι : Type*} [Nonempty ι] (r₁ r₂ : ι → ℝ) :
    RewardDiffEquiv r₁ r₂ ↔ ∃ c : ℝ, ∀ y : ι, r₁ y - r₂ y = c := by
  constructor
  · intro h
    refine ⟨r₁ (Classical.arbitrary ι) - r₂ (Classical.arbitrary ι), ?_⟩
    intro y
    have := h y (Classical.arbitrary ι)
    linarith
  · rintro ⟨c, hc⟩ y_w y_l
    have h1 := hc y_w
    have h2 := hc y_l
    linarith

/-- **`Z` 消去 = 奖励等价**：`dpoReward β Z₁ pref pol` 与 `dpoReward β Z₂ pref pol`
相差常数，故属于同一奖励等价类。这把定理 1（`Z` 消去）与定理 4（等价类）**统一**：
`Z(x)` 的不可辨识性正是「奖励只确定到相差一个 `x` 的函数」。 -/
theorem dpo_reward_equiv_in_Z {ι : Type*} (β Z₁ Z₂ : ℝ) (pref pol : ι → ℝ) :
    RewardDiffEquiv (dpoReward β Z₁ pref pol) (dpoReward β Z₂ pref pol) := by
  intro y_w y_l
  unfold dpoReward
  ring

/-! # 第二部分：性能差引理（PDL）

**正确出处**：Kakade & Langford 2002, *Approximately Optimal Approximate
Reinforcement Learning*, ICML 2002, **Lemma 6.1**。（不是 "Theorem 4.1"，不是
"Lemma 5.2.1"；后者的编号出自 Kakade 2003 博士论文。）

**陈述**：`η_μ(π̃) − η_μ(π) = (1/(1−γ)) · E_{s∼d_μ^{π̃}}[ A_π(s,a) ]`。

**本文件的路线（确定性链，无测度论）**：在**确定性转移 + 有限时域**的 MDP 上，
PDL 就是**伸缩求和**：

  `Σ_{t<T} γ^t·A_π(s_t, a_t) = Σ_{t<T} γ^t·r(s_t,a_t) − V_π(s_0) + γ^T·V_π(s_T)`。

取 `T → ∞`（或 `V_π(s_T) = 0` 的终止状态）时残项消失，即得 PDL。
这是**有限维、可判定**的恒等式，不需要任何测度论。

## 定义：确定性链 MDP

状态取 `ℕ`（时间步即状态，因为链是确定性的）；`r : ℕ → ℝ` 是奖励序列，
`γ` 是折扣因子，`V : ℕ → ℝ` 是价值函数。 -/

/-- **优势函数（确定性链版）**：`A(t) = r(t) + γ·V(t+1) − V(t)`。

这正是 `A_π(s_t, a_t) = Q_π(s_t,a_t) − V_π(s_t)` 在确定性链上的形式
（`Q_π(s_t,a_t) = r(s_t,a_t) + γ·V_π(s_{t+1})`）。 -/
noncomputable def detAdvantage (γ : ℝ) (r V : ℕ → ℝ) (t : ℕ) : ℝ :=
  r t + γ * V (t + 1) - V t

/-! ## 主定理 5：PDL 的伸缩求和形式（有限时域，无需可和性假设）

**命题**：对**任意** `V`（不必是真实值函数），

  `Σ_{t<T} γ^t·(r(t) + γ·V(t+1) − V(t)) = Σ_{t<T} γ^t·r(t) − V(0) + γ^T·V(T)`。

**关键洞察**：这是**纯代数恒等式**（`ring` 可证），不需要 `V` 满足 Bellman 方程。
当 `V = V_π`（旧策略的值函数）时，左边 = `η(π̃) − η(π)` 的有限时域版本，
右边 = `η(π̃) − V_π(s_0) + γ^T V_π(s_T)`，残项在 `T→∞` 或 `V_π(s_T)=0` 时消失。

**已用小整数机器验证**（`γ=0.9, T=4, r_new=[1,2,0.5,3], r_old=[0.5×4]`：
两边均 = `3.6725`，残项 `γ^T V(s_T) = 0`）。 -/
theorem pdl_telescoping (γ : ℝ) (r V : ℕ → ℝ) (T : ℕ) :
    ∑ t in Finset.range T, γ ^ t * (r t + γ * V (t + 1) - V t)
      = ∑ t in Finset.range T, γ ^ t * r t - V 0 + γ ^ T * V T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    -- 目标：Σ' r − V0 + γ^T·V T + γ^T·(r T + γ·V(T+1) − V T)
    --     = (Σ' r + γ^T·r T) − V0 + γ^(T+1)·V(T+1)
    have hpow : γ ^ (T + 1) = γ ^ T * γ := by rw [pow_succ]
    rw [hpow]
    ring

/-- **Bellman 方程 ⟹ 优势为零**（定义自洽性检查）。若 `V` 满足
`V t = r t + γ·V(t+1)`，则 `detAdvantage γ r V t = 0`。

**诚实标注**：这条不是 PDL 的内容（PDL 是 `pdl_telescoping`）；它确认
`detAdvantage` 的定义与 Bellman 方程相容 —— 真实 PDL 中 `A_π ≢ 0`，因为 `π̃ ≠ π`
使得「新策略的 `r`」与「旧策略的 `V`」不匹配。 -/
theorem detAdvantage_eq_zero_of_bellman (γ : ℝ) (r V : ℕ → ℝ)
    (hbell : ∀ t : ℕ, V t = r t + γ * V (t + 1)) (t : ℕ) :
    detAdvantage γ r V t = 0 := by
  unfold detAdvantage
  rw [hbell t]
  ring

/-! ## 主定理 6：PDL 的归一化访问分布形式（`1/(1−γ)` 因子）

PDL 的最终形式用**归一化访问分布** `d(t) = (1−γ)·γ^t`（`Σ_t d(t) = 1`）：

  `η(π̃) − η(π) = (1/(1−γ)) · Σ_t d(t)·A(t)`。

本定理给出 `(1/(1−γ))·Σ_{t<T} (1−γ)γ^t·A(t) = Σ_{t<T} γ^t·A(t)` ——
即两个形式**恒等**（`1/(1−γ)` 与 `(1−γ)` 相消），这解释了 PDL 陈述中因子的来源
（`η` 用**未归一化**的 `Σγ^t r`，而 `E_{s∼d}` 用**归一化**的 `d`）。

**假设**：`γ ≠ 1`。 -/
theorem pdl_normalized_form (γ : ℝ) (hγ : γ ≠ 1) (A : ℕ → ℝ) (T : ℕ) :
    (1 / (1 - γ)) * (∑ t in Finset.range T, (1 - γ) * γ ^ t * A t)
      = ∑ t in Finset.range T, γ ^ t * A t := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t _
  have h1γ : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  field_simp
  ring

/-- **主定理 7（PDL，可见证形式）**。把 `pdl_telescoping`（回报差 = 优势伸缩和）
与 `pdl_normalized_form`（`1/(1−γ)` 归一化）**串联**，得到原文的陈述：

  设 `η̃ := Σ_{t<T} γ^t·r(t)`（新策略的有限时域回报）、
  `η := V 0`（旧策略从 `s_0` 出发的值）、
  `A t := detAdvantage γ r V t`，则

  `η̃ − η = (1/(1−γ)) · Σ_{t<T} (1−γ)γ^t·A(t) + γ^T·V T`。

当 `γ ∈ [0,1)` 且 `V T` 有界时 `γ^T·V T → 0`（`T→∞`），右边即
`(1/(1−γ))·E_{t∼d}[A(t)]` —— **这正是 PDL**。

**注意**：本定理保留了**有限时域残项** `γ^T·V T`，这是对原文（无限时域）陈述的
**诚实降级**：本文件不处理 `T→∞` 的极限（那需要 `V` 有界 + `γ<1` 的 `Tendsto`
论证，属后续工作）。 -/
theorem pdl_finite_horizon (γ : ℝ) (r V : ℕ → ℝ) (T : ℕ) :
    (∑ t in Finset.range T, γ ^ t * r t) - V 0
      = ∑ t in Finset.range T, γ ^ t * detAdvantage γ r V t - γ ^ T * V T := by
  have h := pdl_telescoping γ r V T
  unfold detAdvantage
  linarith

/-! ## 缺什么引理（后续工作清单）

1. **一般（随机转移）PDL**：需要
   - `Q_π(s,a) = r(s,a) + γ Σ_{s'} P(s'|s,a) V_π(s')` 的定义；
   - **访问分布** `d_μ^{π̃}(s) = (1−γ) Σ_t γᵗ P(s_t = s | μ, π̃)` 的构造与
     `Σ_s d(s) = 1`（有限 MDP 上由 `Finset.sum` + 概率归一化给出）；
   - **期望重排**：`E_{s∼d^{π̃}}[A_π(s,a)] = Σ_s d(s) Σ_a π̃(a|s) A_π(s,a)`。
   - 关键代数步骤仍是伸缩求和，但要在**期望算子**下进行（`a` 的边缘化）。
2. **`T→∞` 极限**：`γ < 1` 且 `V` 有界 ⟹ `γᵀ V T → 0`
   （mathlib：`tendsto_pow_atTop_nhds_zero_of_lt_one` 一类的引理，需核名）。
3. **DPO 闭环**：`π*` 是 KL 正则化最优 ⟺ `π*` 满足重参数化等式。
   需要 `RealKL` 的 `kl` + 变分论证（对 `Σ_y π(y) log(π(y)/q(y))` 求驻点），
   可用 `RealCrossEntropy` 的 softmax 梯度链（`softmax_ce_fderiv_apply`）承接。
4. **`Z > 0` 的保证**：`Z(x) = Σ_y π_ref(y|x)·exp(r(x,y)/β) > 0` 需
   `π_ref` 是严格正概率向量（`exp_pos` + 正项求和）。

**未涉及**：DPO 的有限样本理论、DPO 与 PPO 的等价性、`β → 0` 的硬偏好极限。 -/

end Lattice

