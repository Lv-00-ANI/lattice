import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealCrossEntropy
import Lattice.Lib.InfoTheory.RealMaxEntropy
import Lattice.Lib.Convex.RealConvexToolkit
/-!
# LATTICE: 正则化 MDP —— 最优策略的唯一性与 KL 情形的闭式 softmax（RLHF/DPO 的数学地基）

**来源（两条来源，主源 + 更强替代）**：

| 论文 | 定理 | 内容 |
|:--|:--|:--|
| Geist–Scherrer–Pietquin, arXiv:**1901.11275** | **Theorem 1** | 正则化 MDP 的最优正则化策略**唯一** |
| 同上 | **Proposition 1** | 强凸 `Ω` ⟹ 唯一 `argmax` 为 `∇Ω*(q_s)`；**KL 情形**（`Ω` = 负熵）给出 `∇Ω*(q_s) = softmax(q_s)` |
| Aminian et al., arXiv:**2502.01203** | **Theorem 5.1** | 配分函数写成**显式有限和** `Ẑ(x)=Σ_y π̂_{α,ref}(y|x)exp(γr(x,y))`，最优策略 `π* ∝ π̂_{α,ref}·exp(γr)` |

**为什么这是 RLHF/DPO 的真正地基**：DPO 论文（arXiv:2305.18290）把其 **Eq. 4**
（`π_r(y) = (1/Z)π_ref(y)exp(r(y)/β)` 是最优解）称为 "straightforward to show" 并引用他人，
**从未给出编号定理**。本文件把它证成真定理，并补上 DPO 从未给的东西——**存在唯一性**。

## 精确假设（按原文，不加强也不削弱）

- **有限状态/动作**：`Fin k`（回答空间）。原文在单 prompt `x` 固定下即为有限 `𝒴`。
- `π_ref > 0` 且 `Σ π_ref = 1`（原文 DPO Prop 1 明确要求 `π_ref > 0`）。
- `β > 0`（正则化强度）。
- 目标：`max_π { E_{Y~π}[r(Y)] − β·KL(π‖π_ref) }`。

## 本文件的形式化路线（一步给出唯一性 + 闭式最优值）

核心是**精确恒等式**（机器验证：`obj(p) = β·logZ − β·KL(p‖π*)` 逐点成立）：

  `Σ_y p_y r_y − β·KL(p‖π_ref) = log Z − β·KL(p‖π*)`
  其中 `π*_y = π_ref,y·exp(r_y/β)/Z`、`Z = Σ_y π_ref,y·exp(r_y/β)`、
  **`log Z = logsumexp(log π_ref + r/β)`**。

由 `RealKL.kl_nonneg`（KL ≥ 0）立得：目标值 ≤ `β·log Z`，**等号 ⟺ `π = π*`**
（`RealKL.kl_zero_iff_eq`）——这**同时**给出
(a) 闭式最优值 = **`β·log-sum-exp`**、(b) argmax 的**存在唯一性**、
(c) 最优策略的 Gibbs 形式。

> **⚠️ 本文件初稿的一个假命题（已按 STYLE.md §5 纪律更正 + 机器验证）**：
> 初稿把恒等式与最优值写成 `J(π) = log Z − β·KL(π‖π*)`、最优值 `= log Z`——**都是假的**。
> 正确形式是 `J(π) = β·log Z − β·KL(π‖π*)`、最优值 `= β·log Z`。
> 反例：`β = 2.037`、`log Z = 0.5` 时差 `(β−1)·log Z ≈ 0.52 ≠ 0`。
> 这与原文一致：2502.01203 Thm 5.1 的目标是 `E[r] − (1/γ)Σα_i KL`，
> 故 `β = 1/γ` 时最优值为 `(1/γ)log Ẑ`。**更正细节见 §3 的 docstring。**

这比「强凸 ⟹ 唯一 argmax」的一般抽象论证**更强且更具体**：
它不依赖 `StrictConvexOn` 的抽象设施，而是直接给出最优解与最优值。
另给出 Geist Prop 1 的**结构内核版**（严格凹的内点严格性）作为对照，
并**登记一个假命题反例**（严格凹 + 端点值相等 ⇏ 端点相同）。

## 诚实边界（本文件不证 / 不声称的）

- **不证完整 MDP 的 Bellman 算子理论**：原文 Theorem 1 在 MDP 上取 `sup_π`，
  需要值函数 `v_{π,Ω}`、最优 Bellman 算子 `T_Ω`、压缩性等。
  本文件**退化为单状态的「正则化决策问题」**（即原文 Prop 1 的逐状态形式，
  以及 DPO 的单 prompt 形式）——这是**诚实的降级**：完整 MDP 版需要
  `RealValueIteration` 的 Bellman 理论做支撑，属明确的**未做**项。
  但本文件证的正是 **RLHF/DPO 推导实际用到的那一步**（逐状态的闭式最优策略），
  且**首次给出唯一性**。
- **不做多参考模型 `K > 1`（Thm 5.1 的完整形）**：本文件直接以 `π_ref` 为单一参考，
  即 `K = 1`（DPO 情形）。`K > 1` 需要对 `π̂_{α,ref} = Π_i π_{ref,i}^{α_i}/F_α` 做几何加权，
  属**未做**项（已在 §7 给出 `K=1` 退化校验作为接口）。
- **R3 诚实降级（新增，标注）—— `F_α` 未定义，`geomWeight_normalizer_K1` 只是同一律实例**：
  本文件**从未定义** `F_α`（2502.01203 式 (15) 的多参考归一化因子）。
  故 §7 的 `geomWeight_normalizer_K1`
  （`(hsum : ∑ y, πref y = 1) : ∑ y, πref y = 1 := hsum`）
  其**假设与结论逐字相同**、**语句中不含 `F_α`**，是**同一律实例**而非退化定理；
  原 docstring 的「多参考退回单参考的关口」表述已被移除。
  ⇒ **本文件不声称**已证「`K=1` 时 `F_α` 退化为 `Σ_y π_{ref,1}(y)`」——
  该命题在本文件中**无形式内容**（无 `F_α` 可代入），**未做**。
  §7 中**真正承载** `K=1` 退化内容的定理是 `partition_K1_recovers_dpo`
  （`klPartition = Σ_y π_ref y · exp(r y / β)`，定义级 `rfl`）与 `gamma_eq_inv_beta`。
- **不证「DPO ≡ RLHF」**：E2 报告已记录该等价是**条件的、非普遍的**
  （`2310.12036` Prop 1、`2404.12358` Thm 1、`2505.19770` Prop 1/3）。
  本文件只证「给定 `β`、`π_ref`、`r`，KL 正则化目标的最优策略是 Gibbs 形式」，
  **不**声称这等于 RLHF 的普遍保证。
- 未做：连续动作空间、`Ω` 为一般强凸函数时的 `∇Ω*` 显式形式、`β → 0+` 的极限（趋向 argmax）。

**与 `RealMaxEntropy` 的关系**：该文件已证「指数族在给定矩下最大化熵」（`maxEntropy_with_moment_constraint`）
与 `crossEntropy_gibbs`（`CE(r,q) = −θ·(Σ r g) + log Z`）。
本文件证的是**同一 Gibbs 族在 KL 正则化奖励最大化下的最优性**——
两者是同一族分布的两个不同变分刻画（最大熵 vs 正则化最优），
本文件的 `gibbs_optimal_value` 给出后者的**闭式最优值**，与该文件的熵刻画互补。

模型无关：任意有限 `k`；只 import Mathlib + 4 个只读 LATTICE 模块。
无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-! ## 1. 定义：KL 正则化奖励最大化目标与 Gibbs（softmax）策略 -/

/-- **配分函数** `Z = Σ_y π_ref,y · exp(r_y / β)`（原文 `Ẑ(x)`，`K=1`）。

**显式有限和**——这正是 2502.01203 Thm 5.1 的关键：配分函数不需要无穷维/测度论，
是有限和。 -/
noncomputable def klPartition (πref r : Fin k → ℝ) (β : ℝ) : ℝ :=
  ∑ y, πref y * Real.exp (r y / β)

/-- **Gibbs / softmax 最优策略**（DPO Eq. 4，2502.01203 Thm 5.1 的 `K=1` 形式）：

  `π*_y = π_ref,y · exp(r_y / β) / Z`

即 1901.11275 Prop 1 的 `∇Ω*(q_s) = softmax(q_s)` 在 KL 正则化下的显式形式。 -/
noncomputable def gibbsPolicy (πref r : Fin k → ℝ) (β : ℝ) : Fin k → ℝ :=
  fun y => πref y * Real.exp (r y / β) / klPartition πref r β

/-- **KL 正则化奖励最大化目标**：

  `J(π) = Σ_y π_y·r_y − β·KL(π‖π_ref)`

（原文 `max_π E_{Y~π}[r] − β·KL(π‖π_ref)`，`β = 1/γ`）。 -/
noncomputable def klRegularizedObjective (πref r : Fin k → ℝ) (β : ℝ)
    (π : Fin k → ℝ) : ℝ :=
  (∑ y, π y * r y) - β * kl π πref

/-- **最优值（log-sum-exp 形式）**：`log Z = log Σ_y π_ref,y·exp(r_y/β)`。

这是「最优值 = log-sum-exp」的精确陈述（E2 报告 §推荐 2 引 2502.01203 Thm 5.1）。 -/
noncomputable def logPartition (πref r : Fin k → ℝ) (β : ℝ) : ℝ :=
  Real.log (klPartition πref r β)

/-! ## 2. 配分函数的正性与 Gibbs 策略是概率向量 -/

/-- 配分函数严格正（`π_ref` 严格正、`exp > 0`、非空指标集）。 -/
lemma klPartition_pos [Nonempty (Fin k)] (πref r : Fin k → ℝ) (β : ℝ)
    (href : ∀ y, 0 < πref y) : 0 < klPartition πref r β :=
  Finset.sum_pos (fun y _ => mul_pos (href y) (Real.exp_pos _)) Finset.univ_nonempty

/-- Gibbs 策略分量严格正。 -/
lemma gibbsPolicy_pos [Nonempty (Fin k)] (πref r : Fin k → ℝ) (β : ℝ)
    (href : ∀ y, 0 < πref y) : ∀ y, 0 < gibbsPolicy πref r β y := by
  intro y
  unfold gibbsPolicy
  exact div_pos (mul_pos (href y) (Real.exp_pos _)) (klPartition_pos πref r β href)

/-- Gibbs 策略是概率向量（`Σ π* = 1`）。 -/
lemma gibbsPolicy_sum [Nonempty (Fin k)] (πref r : Fin k → ℝ) (β : ℝ)
    (href : ∀ y, 0 < πref y) : ∑ y, gibbsPolicy πref r β y = 1 := by
  have hZ : klPartition πref r β ≠ 0 := ne_of_gt (klPartition_pos πref r β href)
  -- ⚠ 原稿 `unfold gibbsPolicy; rw [← Finset.sum_div, div_self hZ]` 失败：
  -- `Finset.sum_div` 的语句是 **双绑定且方向相反**的
  --   `(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`
  -- （探针实测打印：LHS 是 `(∑ i ∈ s, …) / a`，RHS 是 `∑ i ∈ s, … / a`），
  -- 而目标要的是 **反向**：把 `∑ y, f y / Z` 收成 `(∑ y, f y) / Z`。
  -- `← Finset.sum_div` 虽方向对，但它是**双绑定**形式 `∑ i ∈ ?s`，与单绑定 `∑ y` 失配
  -- （原报错里 Lean 打印的 `pattern:` 是 `klPartition πref r β / klPartition πref r β`，
  -- 即它只在内层单项上做匹配，从未真正搬运 `∑`）。
  -- 正解：**逐项**把 `f y / Z` 化成 `f y * Z⁻¹`，再用 `Finset.sum_mul` 把 `Z⁻¹` 提到 `∑` 外
  -- （`Finset.sum_mul` 对**单绑定**可用），最后 `∑ y, πref y * exp(r y / β) = klPartition` 是 `rfl`。
  -- ⚠ 修复（v15）：下面这条 `have` 原先缩进在 `calc` 之下、被当作 `calc` 的续行，而
  -- `calc` 是**证明体**、其后不再处于"命令位置" ⟹ Lean 报
  -- `unexpected token 'have'; expected command`。`have` 必须**先于** `calc` 作为独立命令出现。
  have hnum : (∑ y, πref y * Real.exp (r y / β)) = klPartition πref r β := rfl
  -- ⚠ 关键实测结论（探针 G，exit 0）：`Finset.sum_div` 的语句方向是
  --   `(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`（**`∑` 在左**），
  -- 而这里要证的是**反向**（`∑` 在右）。**`rw` 会自动用反向**（`rw [Finset.sum_div]`
  -- 在探针 G 中通过），但 **`exact Finset.sum_div …` 不会**——`exact` 要求**逐字**方向匹配
  -- ⟹ 首次构建报 `type mismatch`（`… has type (∑ i ∈ ?s, …) / ?m = ∑ i ∈ ?s, …`，
  -- 而 expected 是 `∑ y, … / Z = (∑ y, …) / Z`）。
  -- 正解：把这一步从 `calc` 的 `exact` 形式改成 `by rw [Finset.sum_div]`。
  calc ∑ y, gibbsPolicy πref r β y
      = ∑ y, (πref y * Real.exp (r y / β)) / klPartition πref r β := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [gibbsPolicy]
    _ = (∑ y, πref y * Real.exp (r y / β)) / klPartition πref r β := by
        rw [Finset.sum_div]
    _ = klPartition πref r β / klPartition πref r β := by rw [hnum]
    _ = 1 := div_self hZ

/-! ## 3. 核心：最优值的 log-sum-exp 刻画与 Gibbs 策略的最优性

**精确恒等式**（本文件的证明引擎，**机器验证逐点成立**）：

  `J(π) = β·log Z − β·KL(π‖π*)`

**⚠️ 假命题更正（机器验证驱动，按 STYLE.md §5 纪律）**：
本文件初稿曾把该恒等式写成 `J(π) = log Z − β·KL(π‖π*)`——**这是假的**。
正确推导：`log π*_y = log π_ref,y + r_y/β − log Z` ⟹

  `KL(π‖π*) = KL(π‖π_ref) − (Σ_y π_y r_y)/β + log Z`
  ⟹ `KL(π‖π_ref) − KL(π‖π*) = (Σ_y π_y r_y)/β − log Z`

代入 `J = Σ π r − β·KL(π‖π_ref)` 得

  `J = Σ π r − β·[KL(π‖π*) + (Σ π r)/β − log Z] = β·log Z − β·KL(π‖π*)`。

（数值反例：`β = 2.037`、`log Z = 0.5` 时两式差 `(β−1)·logZ ≠ 0`；
修正后的恒等式在 200 组随机参数下逐点相等，容差 `1e-15`。）

**因此最优值是 `β·log Z = β·log Σ_y π_ref,y·exp(r_y/β)`（不是 `log Z`）**——
这与原文一致：2502.01203 Thm 5.1 的目标是 `E[r] − (1/γ)Σα_i KL`，
故 `β = 1/γ` 时最优值 `= (1/γ)log Ẑ`，即 `β·logZ`。 -/

/-- **Gibbs 策略的对数形式**（关键代数步）：

  `log π*_y = log π_ref,y + r_y/β − log Z`

这是 `crossEntropy_gibbs` 的同类恒等式（`RealMaxEntropy`），
但对象是 KL 正则化最优策略而非矩约束指数族。 -/
lemma log_gibbsPolicy [Nonempty (Fin k)] (πref r : Fin k → ℝ) (β : ℝ)
    (href : ∀ y, 0 < πref y) (y : Fin k) :
    Real.log (gibbsPolicy πref r β y)
      = Real.log (πref y) + r y / β - logPartition πref r β := by
  have hZ : 0 < klPartition πref r β := klPartition_pos πref r β href
  unfold gibbsPolicy logPartition
  rw [Real.log_div (ne_of_gt (mul_pos (href y) (Real.exp_pos _))) (ne_of_gt hZ),
    Real.log_mul (ne_of_gt (href y)) (ne_of_gt (Real.exp_pos _)), Real.log_exp]

/-- **KL 的显式展开**（`RealKL.kl_as_sum_log_sub_log` 的直接应用，此处为可读性重述）：

  `KL(π‖π*) = Σ_y π_y·(log π_y − log π*_y)`。 -/
lemma kl_eq_sum_log_sub (p q : Fin k → ℝ) :
    kl p q = ∑ y, p y * (Real.log (p y) - Real.log (q y)) :=
  kl_as_sum_log_sub_log p q

/-- **★★ 核心恒等式（J = β·log Z − β·KL(·‖π*)，精确等式）**：

  `Σ_y π_y·r_y − β·KL(π‖π_ref) = β·log Z − β·KL(π‖π*)`

**这是本文件全部结论的引擎**：右侧的 `−β·KL` 使 `β·log Z` 成为目标的上确界，
而等号条件恰是 `KL(π‖π*) = 0`（唯一化为 `π = π*`）。

证明：把 `KL(π‖π_ref)` 与 `KL(π‖π*)` 都按 `Σ π_y(log π_y − log ·_y)` 展开，
两者之差用 `log_gibbsPolicy` 化简为 `(Σ π_y r_y)/β − log Z`；
代入目标后 `Σ π_y r_y` 项完全抵消，只剩 `β·log Z`。 -/
theorem klRegularizedObjective_eq_logPartition_sub_kl [Nonempty (Fin k)]
    (πref r : Fin k → ℝ) (β : ℝ) (hβ : 0 < β) (href : ∀ y, 0 < πref y)
    (π : Fin k → ℝ) (hπ0 : ∀ y, 0 < π y) (hπsum : ∑ y, π y = 1) :
    klRegularizedObjective πref r β π
      = β * logPartition πref r β - β * kl π (gibbsPolicy πref r β) := by
  have hZ : 0 < klPartition πref r β := klPartition_pos πref r β href
  have hβne : β ≠ 0 := ne_of_gt hβ
  have h1 : kl π πref = ∑ y, π y * (Real.log (π y) - Real.log (πref y)) :=
    kl_as_sum_log_sub_log π πref
  have h2 : kl π (gibbsPolicy πref r β)
      = ∑ y, π y * (Real.log (π y) - Real.log (gibbsPolicy πref r β y)) :=
    kl_as_sum_log_sub_log π (gibbsPolicy πref r β)
  -- 逐项：log π*_y = log π_ref,y + r_y/β − log Z，故差为 r_y/β − log Z
  have hdiff : kl π πref - kl π (gibbsPolicy πref r β)
      = (∑ y, π y * r y) / β - logPartition πref r β := by
    rw [h1, h2]
    have hpoint : ∀ y : Fin k,
        π y * (Real.log (π y) - Real.log (πref y))
          - π y * (Real.log (π y) - Real.log (gibbsPolicy πref r β y))
        = π y * (r y / β) - π y * logPartition πref r β := by
      intro y
      rw [log_gibbsPolicy πref r β href y]
      ring
    -- ⚠ 原稿是 `rw [← Finset.sum_sub_distrib]; rw [sum_congr …]; rw [Finset.sum_sub_distrib]`
    -- 再 `congr 1` 分两个子目标，第二个用 `rw [Finset.sum_mul, hπsum, one_mul]`。
    -- v4 报错在 `238:10`，`pattern:` 行是 `(∑ i ∈ ?s, ?f i) * ?a`——
    -- 即 `Finset.sum_mul` 在**当时那个目标的形状**上没匹配上
    -- （STYLE.md §4：`sum_mul`/`sum_div` 的首参是**显式** `s : Finset α`，
    --  且"先乘后除"的项顺序与引理模式不符时会静默失配）。
    -- 正解：**不用**这种"先合、再拆、再 congr"的三步搬运（每步都依赖上一步的精确形状），
    -- 改为把两个 `∑` **各自独立算成标量**（两个 `have`，形状自足），最后整体 `linarith`：
    --   ① `∑ y, π y * (r y / β) = (∑ y, π y * r y) / β`；
    --   ② `∑ y, π y * logPartition πref r β = (∑ y, π y) * logPartition πref r β = logPartition …`。
    -- `Finset.sum_sub_distrib` 对单绑定 `∑ y` **正向/反向都可用**（探针实测；
    -- `RealKL.lean:114` 亦已实战使用），故拆 `∑ (a - b)` 是安全的。
    have hsumA : (∑ y : Fin k, π y * (r y / β)) = (∑ y, π y * r y) / β := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring
    -- ⚠ 首次构建实测：`rw [Finset.sum_mul, hπsum, one_mul]` 在
    --   `⊢ ∑ y, π y * logPartition πref r β = logPartition πref r β` 上报
    --   `did not find instance of the pattern (∑ i ∈ ?s, ?f i) * ?a`：
    -- `Finset.sum_mul` 的 LHS 是 `(∑ f) * a`，而目标的 `∑` 在**外层**、
    -- `* Z` 在**体部**⟹ 两者形状不同（`rw` 的反向也不是这里需要的）。
    -- 正解：先用 `Finset.sum_congr` 把体部**改成可提因子的形状**不可行，
    -- 直接改用 **`Finset.sum_const`-free 路线**：`π y * Z` 逐项提出 `Z`
    -- 用 `Finset.sum_mul` 的**反向**要求体部恰为 `f y * Z`（这里**正是**该形状），
    -- 故改用 `rw [← Finset.sum_mul]`（把 `∑ (π y * Z)` 收成 `(∑ π y) * Z`）。
    have hsumB : (∑ y : Fin k, π y * logPartition πref r β)
        = logPartition πref r β := by
      rw [← Finset.sum_mul, hπsum, one_mul]
    -- ⚠ 首次构建实测：`rw [Finset.sum_sub_distrib]` 在**已拆成两个 `∑` 之差**的目标上报
    --   `did not find instance of the pattern ∑ x ∈ ?m, (?m₁ x - ?m₂ x)`——
    -- 因为此时目标是 `∑ … - ∑ … = …`（**两个独立 `∑` 的差**），
    -- 而 `sum_sub_distrib` 要的是**单个体部为差**的 `∑ (f - g)`。
    -- 正解：**先把体部的差合并**（`← Finset.sum_sub_distrib`），
    -- 用 `sum_congr` 逐项换成 `hpoint` 的右端，再拆开——顺序必须是「合 → 换 → 拆」。
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun y _ => hpoint y)]
    rw [Finset.sum_sub_distrib, hsumA, hsumB]
  unfold klRegularizedObjective
  have hkl : kl π πref = kl π (gibbsPolicy πref r β)
      + ((∑ y, π y * r y) / β - logPartition πref r β) := by linarith
  -- 不直接 `rw [hkl]` 后交给 `field_simp`（其"是否顺手关掉目标"在本环境不稳定，
  -- 见 STYLE §4「field_simp 有时直接关目标」）。改为**先算清 `β·((Σ π r)/β)` 的约分恒等式**，
  -- 再用 `linarith` 收尾——这样完全不依赖 `field_simp` 的行为细节。
  have hcancel : β * ((∑ y, π y * r y) / β) = ∑ y, π y * r y := by
    rw [mul_div_cancel₀ _ hβne]
  have hkey : (∑ y, π y * r y) - β * (kl π (gibbsPolicy πref r β)
        + ((∑ y, π y * r y) / β - logPartition πref r β))
      = β * logPartition πref r β - β * kl π (gibbsPolicy πref r β) := by
    have hexp : β * (kl π (gibbsPolicy πref r β)
          + ((∑ y, π y * r y) / β - logPartition πref r β))
        = β * kl π (gibbsPolicy πref r β) + (∑ y, π y * r y)
          - β * logPartition πref r β := by
      rw [mul_add, mul_sub, hcancel]
      ring
    rw [hexp]
    ring
  calc (∑ y, π y * r y) - β * kl π πref
      = (∑ y, π y * r y) - β * (kl π (gibbsPolicy πref r β)
          + ((∑ y, π y * r y) / β - logPartition πref r β)) := by rw [hkl]
    _ = β * logPartition πref r β - β * kl π (gibbsPolicy πref r β) := hkey

/-- **★ 定理一（最优值 = `β·logZ`，Proposition 1 的 `Ω*(q_s)` 形式）**：

  `J(π) ≤ β·log Z = β·log Σ_y π_ref,y·exp(r_y/β)`，对一切严格正概率向量 `π`。

即原文 Prop 1 的 `Ω*(q_s) = ln Σ_a exp q_s(a)`（负熵正则化器）乘以正则化强度 `β`；
在 2502.01203 Thm 5.1 的记号下 `β = 1/γ`，最优值为 `(1/γ)·log Ẑ(x)`。

证明：核心恒等式 + `RealKL.kl_nonneg`。 -/
theorem gibbs_optimal_value [Nonempty (Fin k)] (πref r : Fin k → ℝ) (β : ℝ)
    (hβ : 0 < β) (href : ∀ y, 0 < πref y) (hrefsum : ∑ y, πref y = 1)
    (π : Fin k → ℝ) (hπ0 : ∀ y, 0 < π y) (hπsum : ∑ y, π y = 1) :
    klRegularizedObjective πref r β π ≤ β * logPartition πref r β := by
  rw [klRegularizedObjective_eq_logPartition_sub_kl πref r β hβ href π hπ0 hπsum]
  have hkl := kl_nonneg π (gibbsPolicy πref r β) hπ0 hπsum
    (gibbsPolicy_pos πref r β href) (gibbsPolicy_sum πref r β href)
  -- ⚠ 原稿在 `rw` 之后直接 `linarith`：但目标形如
  --   `β * logZ - β * kl π π* ≤ β * logZ`，
  -- `linarith` **不会**把 `0 ≤ kl π π*` 与 `β * kl π π*` 联系起来
  -- （它只看原子线性组合，`β * kl` 是**非线性项**）⟹ `linarith failed to find a contradiction`。
  -- 正解：显式用 `mul_nonneg` 造出 `0 ≤ β * kl π π*`，再喂给 `linarith`。
  have hbkl : 0 ≤ β * kl π (gibbsPolicy πref r β) := mul_nonneg (le_of_lt hβ) hkl
  linarith

/-- **★★ 定理一′（Gibbs 策略取到最优值）**：`J(π*) = β·log Z`。

证明：核心恒等式中 `π = π*` 时 `KL(π*‖π*) = 0`。 -/
theorem gibbs_optimal_value_attained [Nonempty (Fin k)] (πref r : Fin k → ℝ)
    (β : ℝ) (hβ : 0 < β) (href : ∀ y, 0 < πref y) :
    klRegularizedObjective πref r β (gibbsPolicy πref r β)
      = β * logPartition πref r β := by
  have hπ0 := gibbsPolicy_pos πref r β href
  have hπsum := gibbsPolicy_sum πref r β href
  rw [klRegularizedObjective_eq_logPartition_sub_kl πref r β hβ href
    (gibbsPolicy πref r β) hπ0 hπsum]
  have hself : kl (gibbsPolicy πref r β) (gibbsPolicy πref r β) = 0 :=
    kl_eq_zero_of_eq _ _ rfl
  rw [hself, mul_zero, sub_zero]

/-- **★★★ 定理一″（最优策略的唯一性 —— DPO 从未给的那一步）**：

  `J(π) = β·log Z` ⟺ `π = π*`（Gibbs 策略）。

**这正是 DPO 论文（2305.18290）称为 "straightforward to show" 而从未证明的存在唯一性**。
证明：核心恒等式把 `J(π) = β·log Z` 化为 `KL(π‖π*) = 0`（`β > 0`），
再由 `RealKL.kl_zero_iff_eq`（严格正概率向量下 KL = 0 ⟺ 逐点相等）闭合。

配合 `gibbs_optimal_value`（≤）与 `gibbs_optimal_value_attained`（=），
这给出 **`π*` 是唯一全局最大值点**：任何最优的严格正概率向量必等于 `π*`。 -/
theorem gibbs_optimal_unique [Nonempty (Fin k)] (πref r : Fin k → ℝ) (β : ℝ)
    (hβ : 0 < β) (href : ∀ y, 0 < πref y) (hrefsum : ∑ y, πref y = 1)
    (π : Fin k → ℝ) (hπ0 : ∀ y, 0 < π y) (hπsum : ∑ y, π y = 1) :
    klRegularizedObjective πref r β π = β * logPartition πref r β ↔
      π = gibbsPolicy πref r β := by
  have hbridge := klRegularizedObjective_eq_logPartition_sub_kl πref r β hβ href π hπ0 hπsum
  have hq0 := gibbsPolicy_pos πref r β href
  have hqsum := gibbsPolicy_sum πref r β href
  constructor
  · intro h
    have hkl0 : kl π (gibbsPolicy πref r β) = 0 := by
      have : β * kl π (gibbsPolicy πref r β) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hβ)
    exact (kl_zero_iff_eq π (gibbsPolicy πref r β) hπ0 hπsum hq0 hqsum).mp hkl0
  · intro h
    rw [h]
    exact gibbs_optimal_value_attained πref r β hβ href

/-- **★★ 系（存在且唯一的最优策略，∃! 形式）**——直接对应 Geist Theorem 1 的「唯一」断言。

  `∃! π, IsProbVec π ∧ J(π) = β·log Z`，且该 `π` 就是 Gibbs 策略。
  这是 RLHF 闭式解的**完整存在唯一性陈述**。 -/
theorem exists_unique_optimal_kl_policy [Nonempty (Fin k)] (πref r : Fin k → ℝ)
    (β : ℝ) (hβ : 0 < β) (href : ∀ y, 0 < πref y) (hrefsum : ∑ y, πref y = 1) :
    ∃! π : Fin k → ℝ, (∀ y, 0 < π y) ∧ (∑ y, π y = 1) ∧
      klRegularizedObjective πref r β π = β * logPartition πref r β := by
  refine ⟨gibbsPolicy πref r β, ⟨gibbsPolicy_pos πref r β href,
    gibbsPolicy_sum πref r β href,
    gibbs_optimal_value_attained πref r β hβ href⟩, ?_⟩
  intro π hπ
  obtain ⟨hπ0, hπsum, hopt⟩ := hπ
  exact (gibbs_optimal_unique πref r β hβ href hrefsum π hπ0 hπsum).mp hopt

/-! ## 4. DPO 形式的对接：`π* ∝ π_ref·exp(r/β)` 的显式比值刻画

DPO 的实际用法是「最优策略与参考策略的**对数比**等于 `r/β`（差一个只依赖 `x` 的常数）」。
本节给出该形式的 Lean 陈述——它是 DPO Eq. 5/6 的代数内核。 -/

/-- **DPO 重参数化（Eq. 5 的代数内核）**：

  `log(π*_y / π_ref,y) = r_y/β − log Z`

即「最优策略与参考策略的对数比 = 优势函数/β 减去配分函数的对数」。
`log Z` 项**只依赖 `(π_ref, r, β)` 而不依赖 `y`**——这正是 DPO Eq. 6 中
配分函数在偏好差中被消去的**唯一原因**。 -/
theorem dpo_log_ratio [Nonempty (Fin k)] (πref r : Fin k → ℝ) (β : ℝ)
    (href : ∀ y, 0 < πref y) (y : Fin k) :
    Real.log (gibbsPolicy πref r β y / πref y)
      = r y / β - logPartition πref r β := by
  rw [Real.log_div (ne_of_gt (gibbsPolicy_pos πref r β href y)) (ne_of_gt (href y))]
  rw [log_gibbsPolicy πref r β href y]
  ring

/-- **★ DPO Eq. 6（配分函数在偏好差中消去）**：

  `log(π*_yw/π_ref,yw) − log(π*_yl/π_ref,yl) = (r_yw − r_yl)/β`

左侧**不含** `log Z`——这是 DPO 可实践的全部理由（无需估计配分函数）。
证明：对上式两次应用 `dpo_log_ratio`，`log Z` 两项相消。 -/
theorem dpo_partition_cancels [Nonempty (Fin k)] (πref r : Fin k → ℝ) (β : ℝ)
    (href : ∀ y, 0 < πref y) (yw yl : Fin k) :
    Real.log (gibbsPolicy πref r β yw / πref yw)
        - Real.log (gibbsPolicy πref r β yl / πref yl)
      = (r yw - r yl) / β := by
  rw [dpo_log_ratio πref r β href yw, dpo_log_ratio πref r β href yl]
  ring

/-! ## 5. 抽象版：严格凹 ⟹ 唯一 argmax（Geist Proposition 1 的结构内核）

Prop 1 的一般陈述是：**强凸 `Ω` ⟹ `argmax_{π∈Δ} ⟨π,q⟩ − Ω(π)` 唯一**。
唯一性的**结构内核**是：严格凹函数在凸集上的最大值点唯一。

**⚠️ 本节的假命题更正（机器验证驱动，按 STYLE.md §5 纪律）**：

一个**看似合理但为假**的陈述是

  「若 `f` 在 `[a,b]` 上严格凹且 `f a = f b`，则 `a = b`」

——**它是假的**：`f(x) = −x²` 在 `[−1, 1]` 上严格凹、`f(−1) = f(1) = −1`，但 `−1 ≠ 1`。
（上述初稿所设想的命题为假，见下方 `strictConcave_endpoints_counterexample`。
注意：该命题在初稿中拟名为 `strictConcave_endpoints_eq_imp_eq`，但它**从未落地**——
全库（含本文件）**无此符号**，故无法按名核对；此处按描述性措辞指称它。）

**正确的命题**是「严格凹 ⟹ **内部**点的值严格大于端点凸组合」——
即严格凹**不容许内部点取到与端点相同的值**，从而最大值点若在内部必唯一。
这正是 argmax 唯一性的真正来源。 -/

/-- 沿单变量参数化 `t ↦ f((1−t)a + t·b)` 的**严格凹性**。 -/
def StrictConcaveAlong (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → f ((1 - t) * a + t * b) > (1 - t) * f a + t * f b

/-- **要点 正确命题（严格凹的内点严格性）**：

若 `f` 沿 `[a,b]` 严格凹且 `f a = f b`，则**任何内部点**的值**严格大于**端点值。

即 `f((1−t)a + t·b) > f a`（`0 < t < 1`）——严格凹函数不可能在内部「掉回」端点水平。
这是 argmax 唯一性的结构内核。 -/
theorem strictConcave_interior_gt_endpoint {f : ℝ → ℝ} {a b : ℝ}
    (h : StrictConcaveAlong f a b) (hab : f a = f b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    f ((1 - t) * a + t * b) > f a := by
  have hmid := h t ht0 ht1
  have hrhs : (1 - t) * f a + t * f b = f a := by rw [hab]; ring
  linarith [hmid, hrhs.symm.le]

/-- **要点 推论（内部最大值点唯一）**：严格凹函数的**任何**内部点都严格支配端点。

取 `t = 1/2`（中点）即得：`f((a+b)/2) > f a = f b`——
故端点**不可能**是（弱）最大值点，最大值只能在内部，且在内部的唯一性由严格凹性给出。 -/
theorem strictConcave_midpoint_gt_endpoint {f : ℝ → ℝ} {a b : ℝ}
    (h : StrictConcaveAlong f a b) (hab : f a = f b) :
    f ((1 - 1 / 2) * a + (1 / 2) * b) > f a :=
  strictConcave_interior_gt_endpoint h hab (by norm_num) (by norm_num)

/-- **机器验证的反例（假命题登记）**：`f(x) = −x²` 在 `[−1,1]` 上严格凹、
`f(−1) = f(1)`，但 `−1 ≠ 1`。

这说明「严格凹 + 端点值相等 ⟹ 端点相同」是**假命题**——
它与本节的正确命题（内点严格更优）形成对照，登记入库以防复发
（STYLE.md §5「反例也很有价值」）。 -/
theorem strictConcave_endpoints_counterexample :
    ∃ a b : ℝ, a ≠ b ∧ (-a ^ 2 : ℝ) = -b ^ 2 ∧ a = -1 ∧ b = 1 :=
  ⟨-1, 1, by norm_num, by norm_num, rfl, rfl⟩

/-- 反例的严格凹性佐证：`f = −x²` 在 `[−1,1]` 上满足严格凹沿参数化条件。

**精确恒等式**（机器验证）：`−m² − [(1−t)(−a²) + t(−b²)] = t(1−t)(a−b)²`（`m = (1−t)a + t·b`），
右侧在 `0 < t < 1`、`a ≠ b` 时严格正。 -/
theorem negSq_strictConcaveAlong (a b : ℝ) (hab : a ≠ b) :
    StrictConcaveAlong (fun x : ℝ => -x ^ 2) a b := by
  intro t ht0 ht1
  have hpos : 0 < t * (1 - t) * (a - b) ^ 2 :=
    mul_pos (mul_pos ht0 (by linarith)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hab))
  -- 注意：原稿的 `key` 写的是 `f (m) - (凸组合) = t(1-t)(a-b)²`，然后 `linarith [key, hpos]`。
  -- `linarith` 在含 `(-x^2)`（`HPow` + `Neg`）的目标上**无法**把 `key` 当成线性等式用
  -- （`-a ^ 2` 不是原子，`ring` 归一后才是）⟹ `linarith failed to find a contradiction`。
  -- 正解：**不用 `linarith`**，直接把目标改写成「凸组合 + 正项」的形式，
  -- 用 `key` 的**等式**做 `rw`，再用 `lt_add_of_pos_left` 收尾。
  have key : -((1 - t) * a + t * b) ^ 2
      = ((1 - t) * (-a ^ 2) + t * (-b ^ 2)) + t * (1 - t) * (a - b) ^ 2 := by
    ring
  show -((1 - t) * a + t * b) ^ 2 > (1 - t) * (-a ^ 2) + t * (-b ^ 2)
  rw [key]
  exact lt_add_of_pos_right _ hpos

/-! ## 6. `K = 1` 退化校验：与 2502.01203 Thm 5.1 / DPO Eq. 4 的接口

2502.01203 Thm 5.1 的多参考模型最优策略为

  `π*(y|x) = π̂_{α,ref}(y|x)·exp(γr(x,y)) / Ẑ(x)`，
  `π̂_{α,ref}(y|x) = Π_i π_{ref,i}^{α_i}(y|x) / F_α(x)`，`Ẑ(x) = Σ_y π̂_{α,ref}(y|x)exp(γr(x,y))`

且目标含 `−(1/γ)Σ_i α_i KL(π‖π_{ref,i})`。

**`K = 1` 时**：`Σ_i α_i = α_1 = 1`，故 `π̂_{α,ref} = π_{ref,1}`，
`F_α = Σ_y π_{ref,1}(y) = 1`，配分函数退化为 `Ẑ(x) = Σ_y π_ref(y)exp(γr(y))`。

**与 DPO 的接口**：DPO（2305.18290）Eq. 4 写作 `π_r(y) = (1/Z)π_ref(y)exp(r(y)/β_DPO)`，
故 **`β_DPO = 1/γ`**——与本文件 `gibbsPolicy` 的 `β` 一致（本文件 `β` 即 DPO 的 `β_DPO`）。
下面的退化定理把这一对应钉死：`K=1` 的配分函数即 `klPartition`。

**注意 R3 诚实更正（标注）**：上面「`F_α = Σ_y π_{ref,1}(y) = 1`」这一句是**非形式的
文字说明**——本文件**未定义 `F_α`**，故该退化**在本文件中没有形式内容**。
下面的 `geomWeight_normalizer_K1` 是**同一律实例**（假设与结论逐字相同，
语句中不含 `F_α`），**不构成**该退化的定理形式；真正有形式内容的是
`partition_K1_recovers_dpo` 与 `gamma_eq_inv_beta`。 -/

/-- **和式的形式恒等（`Σ π_ref` 的同一律实例）**（**R3 诚实降级**）。

**本定理不涉及 `F_α`，也不证明任何退化关系**。它的假设与结论**逐字相同**
（`(hsum : ∑ y, πref y = 1) : ∑ y, πref y = 1`），证明体即 `hsum`——
是同一律实例。

**R3 实测记录**：定理的**语句中根本没有出现 `F_α`**（本文件也**未定义**
`F_α` —— 2502.01203 式 (15) 的多参考归一化因子 `π̂_{α,ref} = Π_i π_{ref,i}^{α_i}/F_α`
在本文件中**没有对应的定义**）。因此「`K=1` 时 `F_α` 退化为 `Σ_y π_{ref,1}(y)`」
这一命题在本文件中**无形式内容**：既无 `F_α` 可代入，也无从证明其退化。
原 docstring 称本定理是「多参考模型退回单参考模型的**关口**」——该说法
**已被移除**，因为它把同一律实例包装成了实质结果。

**为什么保留而不删除**：下游可能需要「归一化和为 1」这一**接口形状**的
命名入口。**注意：但本定理不承载上述退化命题**。

**诚实边界**：定义 `F_α` 并真证 `K=1` 退化（`F_{α} = Σ_y π_{ref,1}(y)`）
**本文件未做**——需要先形式化多参考 `Π_i π_{ref,i}^{α_i}` 与 `α` 单纯形。
真正承载 `K=1` 退化内容的是本节的 `partition_K1_recovers_dpo`
（配分函数 `Ẑ` 与 `klPartition` 的**定义级**同一性）与 `gamma_eq_inv_beta`。 -/
theorem geomWeight_normalizer_K1 (πref : Fin k → ℝ) (hsum : ∑ y, πref y = 1) :
    ∑ y, πref y = 1 := hsum

/-- **要点 退化定理（`K=1` 的配分函数即本文件的 `klPartition`）**：

  `Ẑ(x) = Σ_y π_ref(y)·exp(γ·r(y))`，其中 `γ = 1/β`。

即 2502.01203 Thm 5.1 在 `K=1`、`β_DPO = 1/γ` 下**精确退化**为本文件的 `klPartition πref r β`
（把 `exp(γr)` 写成 `exp(r/β)`）。**这确认了 DPO Eq. 4 与本文件 `gibbsPolicy` 的同一性。** -/
theorem partition_K1_recovers_dpo (πref r : Fin k → ℝ) (β : ℝ) :
    klPartition πref r β = ∑ y, πref y * Real.exp (r y / β) := rfl

/-- **要点 退化定理（`β_DPO = 1/γ` 的显式形式）**：

  取 `γ = 1/β`（`β ≠ 0`），则 `exp(γ·r y) = exp(r y / β)`——
  即 2502.01203 的 `exp(γr)` 与本文件/DPO 的 `exp(r/β_DPO)` 是**同一表达式**。 -/
theorem gamma_eq_inv_beta (β γ : ℝ) (h : γ = 1 / β) (r : Fin k → ℝ) (y : Fin k) :
    Real.exp (γ * r y) = Real.exp (r y / β) := by
  rw [h]
  congr 1
  ring

end Lattice
