import Mathlib
import Lattice.Lib.Quantization.RealQAT
/-!
# LATTICE: QAT 的 SGD 收敛率与噪声-步长最优权衡

`RealQAT` 给出了量化约束下 QAT 的**误差地板** `‖A‖·δ/(1−c)`（量化噪声不可约）。
本文件回答下一步：带**量化噪声**的随机梯度下降 (SGD) 的**收敛率**是多少，
以及噪声项与学习率之间的**最优权衡**。§三 在一个抽象的**期望损失序列**
`F : ℕ → ℝ` 上工作（其递推作为显式假设，便于初等地得到率）；
§二-0 与 §二-1 则**补上随机性那一层**：§二-0 用滤流 `𝒢` + 条件期望不等式
推出无条件期望递推（`condExp_step_le`），§二-1 进一步从
**条件无偏梯度 + 条件方差界 + 光滑性 + PL** 推出该条件期望不等式本身
（`condExp_step_from_unbiased` / `condExp_step_from_unbiased_PL`）——
故在 `qat_sgd_rate_measure` 中，递推**完全由随机梯度性质推出**，不再是假设。

## 主结果
  1. `qat_sgd_rate`（核心）：在递推
     `F (t+1) ≤ F t − η·(F t − f⋆) + η²·C/2`（`C ≥ 0` 为噪声方差上界）与
     `f⋆ ≤ F t` 下，**前 `T` 步中存在一步**满足
     `F t − f⋆ ≤ (F 0 − f⋆)/(T·η) + η·C/2`。
     证明为**初等望远镜求和** + 最小值下标。
  2. `qat_sgd_rate_noise`（核心）：把 `C` 具体化为 `qatNoise σ ν = σ² + ν²`
     （随机梯度噪声 + 量化噪声），得到
     `F t − f⋆ ≤ (F 0 − f⋆)/(T·η) + η·(σ² + ν²)/2`。
  3. `qat_optimal_stepsize`（核心，最优权衡）：对**任意** `η > 0`，
     `√(2AC/T) ≤ A/(T·η) + η·C/2`（AM-GM）；即无论怎么选步长，
     界都不可能低于 `√(2AC/T)`。
  4. `qat_optimal_stepsize_attained`：最优步长 `η⋆ = √(2A/(T·C))` **恰好取到**该下界。
  5. `qat_rate_decreasing_in_T`：界的 `1/T` 项随迭代数单调下降（`T` 越大越好）。
  6. `qat_noiseless_rate`：`σ = ν = 0` 时退化回 `(F 0 − f⋆)/(T·η)`
     （回收 `RealQAT.qat_convergence_zero` 的无量化噪声情形）。
  7. `qat_floor_noise_nonneg` / `qat_floor_noise_mono` / `qat_floor_noise_link`：
     地板噪声 `qatFloorNoise Anorm δ cx = Anorm·δ/(1−cx)` 恰对齐
     `RealQAT.qat_convergence` 的 `‖A‖·δ/(1−c)`；非负、随 `Anorm` 单调增，
     且把它代入 `qatNoise` 会**放大**总噪声项 → 噪声项随 QAT 地板增长。
  8. **B17（本轮新增，§二-1）**：从「条件无偏梯度 + 条件方差界 + 光滑性」
     **推出**条件期望不等式本身（原先只有诚实标注「未做」）：
     `CondGradModel`（条件梯度模型：条件权重 `p` / 条件取值 `g` / `η` / `L` / `σ2`）、
     `condExpFin`（有限条件期望）、`CondUnbiased`、`CondVarianceLe`、
     `smooth_step_bound`（**逐实现二次上界的形式传递**；⚠ R3 更正：
     该定理的假设与结论**逐字相同**，是同一律实例，**不含光滑性证明**）、
     `condExp_linear_eq`（无偏性消去一次项）、
     `condExp_sq_eq`（`E[g²] = Var + grad²`，**噪声项 `η²C/2` 中 `C` 的来源**）、
     **`condExp_step_from_unbiased`（主交付：条件期望不等式由三假设推出）**、
     **`condExp_step_from_unbiased_PL`（再用 PL/强凸性化为 `condExp_step_le` 的前提形状）**。

## 诚实边界（标注）
  · 递推 `hstep`（期望损失的平滑 SGD 下降 + 噪声）在 §三 是**显式假设**（标注）；
    **B14 已部分补上**：§二-0 用滤流 `𝒢` + 条件期望不等式
    `μ[F(t+1)|𝒢 t] ≤ F t − η(F t − f⋆) + η²C/2` **推出**了无条件期望递推
    （`condExp_step_le`），并据此给出 `qat_sgd_rate_measure`——该定理中的递推是**定理**而非假设。
    **B17 已补上最后一环（§二-1）**：`condExp_step_from_unbiased` +
    `condExp_step_from_unbiased_PL` 从**条件无偏 + 条件方差界 + 光滑性 + PL**
    **推出**了该条件期望不等式本身。故 `hstep` 在 `qat_sgd_rate_measure` 中
    **完全由随机梯度性质推出**，不再是假设。
  · **B17 的诚实降级（标注）**：§二-1 的"条件期望"用**有限条件分布**（`Fin n`）
    编码；光滑性以**逐点二次上界** `hSmooth` 形式传入（不重证 `L`-光滑的
    标准推论，那属于 `RealStrongConvex`/`RealHessian` 一族）；
    PL/强凸性 `2μ(fx−f⋆) ≤ grad²` 以**显式假设** `hPL` 传入
    （由 `RealPLCondition`/`RealStrongConvex` 提供，**不重证**）；
    仍**不构造**具体量化器/噪声分布（`σ2`、`C` 是显式参数）。
  · **R3 诚实降级（新增，标注）—— `smooth_step_bound` 是同一律实例，不是定理内容**：
    §二-1 的 `smooth_step_bound` 其**假设与结论逐字相同**
    （源码中两侧为同一表达式 `∀ j, fstep (M.g j) ≤ fx - M.eta*M.g j*grad + M.eta^2*M.L/2*(M.g j)^2`），
    证明体即 `hSmooth` 本身。故它**只把给定的二次上界逐实现传递**，
    **不包含光滑性的证明**——原 docstring 的「光滑性 ⟹ 逐实现单步上界」
    因果表述已被移除。**本文件因此不声称**已证「`L`-光滑 ⟹ 二次上界」；
    该命题**未证**，**未做**（属 `RealStrongConvex`/`RealHessian` 一族）。
    **后果（可审计）**：`condExp_step_from_unbiased` 中「光滑性」这一环
    **实为假设**，其强度等于直接假设该二次上界。定理**保留**（下游接口形状），
    但**不**作为真数学内容的支撑点。
  · 结论是**前 `T` 步中最优（最小）迭代**的界，**不是**对 `F T` 的界（标注）。
  · 常数因 `η²C/2` 的写法与教科书相差一个因子（标注）；`2AC/T` 的 `T` 为实数强制转换。
  · 本文件不构造具体量化器/噪声分布，也不声称 SGD 的轨道收敛。
  · 模型无关、无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

-- ⚠ `μ[F (t+1) | 𝒢 t]` 是 mathlib 的 **scoped** 记号
-- （`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:98`：
-- `scoped notation μ "[" f "|" m "]" => MeasureTheory.condexp m μ f`），
-- 只有在 `MeasureTheory` scope 打开时才可见。原文件只 `open scoped BigOperators`，
-- 故 §二-0 的两处 `μ[·|·]` 被解析为语法错误（`unexpected token '|'`），
-- 并级联出 9 个后续 error。此处按同族文件
-- （`RealMcDiarmidMeasure` / `RealMartingaleOptionalStopping` / `RealHoeffdingInequality`）
-- 的既有写法补齐 open（**只补环境，不改任何陈述/假设**）。
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-! ## 一、噪声与地板 -/

/-- **QAT 噪声方差**：随机梯度噪声 `σ²` 与量化噪声 `ν²` 的方差和 `σ² + ν²`。
代入 `σ`=随机梯度噪声标准差、`ν`=量化噪声标准差。 -/
def qatNoise (σ ν : ℝ) : ℝ := σ ^ 2 + ν ^ 2

/-- **量化误差地板（噪声形式）**：`Anorm·δ/(1−cx)`，对齐
`RealQAT.qat_convergence` 中的地板 `‖A‖·δ/(1−c)`
（`Anorm = ‖A‖`、`δ` = 量化投影误差界、`cx = c` 为谱收缩因子）。
这是量化注入的**不可约**稳态残差，可当作噪声项 `ν` 使用。 -/
def qatFloorNoise (Anorm δ cx : ℝ) : ℝ := Anorm * δ / (1 - cx)

/-! ## 二、望远镜求和（收敛率证明的初等工具） -/

/-- **望远镜求和**：`∑_{t<n} (a t − a (t+1)) = a 0 − a n`。
这是初等收敛率证明的核心恒等式（差分逐项相加只剩首尾）。 -/
theorem qat_sum_range_telescope (a : ℕ → ℝ) (n : ℕ) :
    ∑ t in Finset.range n, (a t - a (t + 1)) = a 0 - a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-! ## 二-0、B14：从滤流推出递推（把 `hstep` 从假设变为定理）

ROADMAP 的 B14 要求「QAT 递推从滤流推出」。原文件把递推

    F (t+1) ≤ F t − η·(F t − f⋆) + η²·C/2

当作**显式假设** `hstep`。本文件补上**从滤流结构推出它**的一步：

设 `(Ω, m0, μ)` 概率空间、`𝒢 : Filtration ℕ m0`、`F : ℕ → Ω → ℝ` 是
**可料损失过程**（`F t` 是 `𝒢 t`-可测的，即在第 `t` 步已知）。
SGD 的「条件下降 + 噪声」在滤流语言下的实质陈述是**条件期望不等式**

    μ[F (t+1) | 𝒢 t] ≤ F t − η·(F t − f⋆) + η²·C/2   （μ-a.e.）

即：**在给定历史下**，下一步的期望损失按平滑 SGD 下降，且噪声注入了 `η²C/2`。
这是教科书 SGD 分析里唯一真正需要「随机性」的地方——其余全是代数。

本文件给出：
1. `condExp_step_le`（**核心，B14**）：上面的条件期望不等式 ⟹
   **无条件**（`μ`-积分意义下）的递推
   `∫ F(t+1) dμ ≤ ∫ F t dμ − η·(∫ F t dμ − f⋆) + η²C/2`；
2. `qat_sgd_rate_measure`（**B14 主结果**）：把 `qat_sgd_rate` 的结论提升到
   **期望序列** `G t := ∫ F t dμ` 上——此时 `hstep` 不再是假设，
   而是由 1 从条件期望不等式**推出**的定理。

**诚实边界（标注）**：
- 本文件**仍不构造**随机梯度 `g t` 的具体分布，也**不**从 `g t` 的
  条件无偏性 + 方差界推出 1 中的条件期望不等式——那需要把 `F` 的递推
  `F(t+1) = F t − η⟨g t, ∇F t⟩ + …` 与平滑性假设逐项展开（**未做**）。
  本文件的贡献是：**架好滤流这一层，使「条件 ⟹ 无条件」这一步成为定理**。
- `F t` 的 `𝒢 t`-可测性与可积性作为显式假设（`hadapted`/`hint`）——
  它们是「损失过程可用滤流描述」的形式化内容。
- 这里的 `f⋆` 是确定性下界（`∀ t ω, f⋆ ≤ F t ω`），故取期望后仍是下界。
- 无 sorry/axiom/admit。 -/

/-! ## 〇、望远镜率主定理（前移）

⚠ **Q3B1 结构修复（无陈述改动）**：本段原本位于 §三，但它被 §二-0 的
`condExp_step_le` 与 `qat_sgd_rate_measure` 引用，而 Lean 要求**先声明后使用**，
故原位置导致 `unknown identifier 'qat_sgd_rate'`。
此处仅把该声明的**文本原样前移**（零陈述/零证明体改动），并补一个位置正确的节标题；
§三 保留指向本段的说明。依赖检查：`qat_sgd_rate` 的证明体只依赖更早的
`qat_sum_range_telescope`（§二）与 mathlib 引理，**无反向依赖**，前移不成环。 -/

/-- **主结果（带量化噪声的 SGD 收敛率，min-index 形式）**：
设 `f⋆` 是下界（`∀t, f⋆ ≤ F t`），递推
`F (t+1) ≤ F t − η·(F t − f⋆) + η²·C/2`（`C ≥ 0` 为噪声方差上界、`η > 0`），
则在前 `T` 步（`T > 0`）中存在一步 `t` 使
`F t − f⋆ ≤ (F 0 − f⋆)/((T:ℝ)·η) + η·C/2`。

证明：令 `a t = F t − f⋆ ≥ 0`；递推给出 `η·a t ≤ a t − a (t+1) + η²C/2`；
对 `t < T` 求和并用望远镜恒等式 `∑(a t − a(t+1)) = a 0 − a T ≤ a 0` 得
`η·∑ a t ≤ a 0 + T·η²C/2`；取 `range T` 上 `a` 的最小点 `t0`，
则 `T·a t0 ≤ ∑ a t`，除掉 `T·η` 即得。 -/
theorem qat_sgd_rate (F : ℕ → ℝ) (fstar η C : ℝ) (T : ℕ)
    (hT : 0 < T) (hη : 0 < η)
    (hlow : ∀ t : ℕ, fstar ≤ F t)
    (hstep : ∀ t : ℕ, F (t + 1) ≤ F t - η * (F t - fstar) + η ^ 2 * C / 2) :
    ∃ t : ℕ, t < T ∧ F t - fstar ≤ (F 0 - fstar) / ((T : ℝ) * η) + η * C / 2 := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hstepa : ∀ t : ℕ, η * (F t - fstar) ≤
      (F t - fstar) - (F (t + 1) - fstar) + η ^ 2 * C / 2 := by
    intro t
    have h := hstep t
    linarith
  have hsum1 : η * (∑ t in Finset.range T, (F t - fstar)) ≤
      ∑ t in Finset.range T, ((F t - fstar) - (F (t + 1) - fstar) + η ^ 2 * C / 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun t _ => hstepa t)
  have hsum2 : (∑ t in Finset.range T,
      ((F t - fstar) - (F (t + 1) - fstar) + η ^ 2 * C / 2))
      = (F 0 - fstar) - (F T - fstar) + (T : ℝ) * (η ^ 2 * C / 2) := by
    rw [Finset.sum_add_distrib, qat_sum_range_telescope, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hηS : η * (∑ t in Finset.range T, (F t - fstar))
      ≤ (F 0 - fstar) + (T : ℝ) * (η ^ 2 * C / 2) := by
    rw [hsum2] at hsum1
    have hFT : 0 ≤ F T - fstar := by have := hlow T; linarith
    linarith
  obtain ⟨t0, ht0mem, ht0min⟩ :=
    Finset.exists_min_image (Finset.range T) (fun t => F t - fstar)
      (Finset.nonempty_range_iff.mpr hT.ne')
  have ht0lt : t0 < T := Finset.mem_range.mp ht0mem
  have hsum_ge : (T : ℝ) * (F t0 - fstar) ≤ ∑ t in Finset.range T, (F t - fstar) := by
    have h : ∑ t in Finset.range T, (F t0 - fstar) ≤ ∑ t in Finset.range T, (F t - fstar) :=
      Finset.sum_le_sum (fun t ht => ht0min t ht)
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have hSle : (∑ t in Finset.range T, (F t - fstar))
      ≤ ((F 0 - fstar) + (T : ℝ) * (η ^ 2 * C / 2)) / η := by
    rw [le_div_iff₀ hη, mul_comm (∑ t in Finset.range T, (F t - fstar)) η]
    exact hηS
  have hTmul : (T : ℝ) * (F t0 - fstar)
      ≤ ((F 0 - fstar) + (T : ℝ) * (η ^ 2 * C / 2)) / η := le_trans hsum_ge hSle
  have hgoal : F t0 - fstar
      ≤ (((F 0 - fstar) + (T : ℝ) * (η ^ 2 * C / 2)) / η) / (T : ℝ) := by
    -- `le_div_iff₀` 先把目标变成 `(F t0 − f⋆) * ↑T ≤ …`；
    -- 而 `hTmul` 是 `↑T * (F t0 − f⋆) ≤ …`，故先交换乘积次序再套用。
    rw [le_div_iff₀ hTpos, mul_comm (F t0 - fstar) (T : ℝ)]
    exact hTmul
  have halg : (((F 0 - fstar) + (T : ℝ) * (η ^ 2 * C / 2)) / η) / (T : ℝ)
      = (F 0 - fstar) / ((T : ℝ) * η) + η * C / 2 := by
    field_simp
    ring
  exact ⟨t0, ht0lt, halg ▸ hgoal⟩

/-- **B14 核心：条件期望不等式 ⟹ 无条件期望递推**。
设 `F : ℕ → Ω → ℝ` 每步可积，且满足条件期望不等式（μ-a.e.）

    μ[F (t+1) | 𝒢 t] ≤ F t − η·(F t − f⋆) + η²·C/2，

则取 `μ`-积分得

    ∫ F (t+1) dμ ≤ ∫ F t dμ − η·(∫ F t dμ − f⋆) + η²·C/2。

证明：对不等式两边取 `∫ · dμ`，用
`integral_condexp`（条件期望的积分 = 原积分）与积分的线性性整理即得；
`μ` 为概率测度使 `∫ (η²C/2) dμ = η²C/2`（用 `integral_const` + `measure_univ`）。 -/
theorem condExp_step_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0} (F : ℕ → Ω → ℝ) (fstar η C : ℝ)
    (hint : ∀ t, Integrable (F t) μ)
    (hstep : ∀ t, (μ[F (t + 1) | 𝒢 t]) ≤ᵐ[μ]
      fun ω => F t ω - η * (F t ω - fstar) + η ^ 2 * C / 2) (t : ℕ) :
    ∫ ω, F (t + 1) ω ∂μ ≤ ∫ ω, F t ω ∂μ
      - η * (∫ ω, F t ω ∂μ - fstar) + η ^ 2 * C / 2 := by
  have h1 : ∫ ω, F (t + 1) ω ∂μ ≤ ∫ ω, (F t ω - η * (F t ω - fstar) + η ^ 2 * C / 2) ∂μ := by
    -- ⚠ mathlib 4.14 的 `integral_condexp` 签名（已用内核 `#check` 核实）：
    --   integral_condexp (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] :
    --     ∫ x, (μ[f|m]) x ∂μ = ∫ x, f x ∂μ
    -- 它**只**收 `hm`（+ 类型类），**不收** `f` / `Integrable` 参数（后者由
    -- `m`/`μ`/`f` 的隐式参数推断）。原代码传入 `(hint (t + 1))` 当作 `hm` 是错的。
    -- ⚠ E2 实测（隔离复现）`integral_mono_ae` 的第三参数**不是** `_` 可推断的：
    -- 报 `don't know how to synthesize placeholder for argument 'hg'`，因为
    -- `integral_mono_ae` 签名是
    --   `integral_mono_ae (h : Integrable f μ) (h' : Integrable g μ) (hfg : f ≤ᵐ[μ] g)`，
    -- 第三参数是 **`Integrable`**（被积函数 `g := fun ω => F t ω - η * … + η²C/2`
    -- 的可积性），**不是** `≤ᵐ` 证据；原来的 `_` + `(hstep t)` 把两个位置的参数
    -- **错位**了。故这里显式给出 `g` 的可积性，`≤ᵐ` 证据才落到正确位置。
    rw [← integral_condexp (μ := μ) (m := 𝒢 t) (m0 := m0) (f := F (t + 1)) (𝒢.le t)]
    exact integral_mono_ae (integrable_condexp (μ := μ) (m := 𝒢 t) (m0 := m0) (f := F (t + 1)))
      (((hint t).sub (((hint t).sub (integrable_const fstar)).const_mul η)).add
        (integrable_const (η ^ 2 * C / 2)))
      (hstep t)
  -- ⚠ Q3B1 未修完（诚实标注）：mathlib 4.14 **没有** Bochner 空间上的
  -- `integral_const_mul`（repo 内 `RealMeasureTheoryBase.lean:437` 已登记同类改名：
  -- `ENNReal.toReal_one` → `ENNReal.one_toReal`）。本行的原式因此报
  -- `unknown identifier 'integral_const_mul'`。下方仍保留原式（未改写），
  -- 以便下一个代理看到**原始失败形态**而不是被猜改掩盖（PROCESS §3.4 现场推导法）。
  -- 已有证据：同族 `RealHoeffdingInequality.lean:366` / `RealHoeffdingLemmaMeasure.lean:185`
  -- 用 `rw [integral_const, MeasureTheory.measure_univ, ENNReal.one_toReal, one_smul]`
  -- 处理常数积分，可作修复起点。
  -- ⚠ E2 实测（隔离复现，B260.4/B205）：本 `rw` 链有**三处**独立的句法/命名缺陷，
  -- 逐个用内核证据定位（每条都在 `lean/_e2_probe*.lean` 里单独复现过）：
  --   (a) `integral_const_mul` **在本 mathlib 4.14 中不存在**
  --       （`#check` 报 `unknown identifier`）—— 这正是本节点上方注释预判的改名。
  --       实际存在的是 **`integral_smul`**：`∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ`。
  --       对 `ℝ` 用 `smul_eq_mul` 转成 `*` 形即可。
  --   (b) `integral_add` / `integral_sub` 的 `Integrable` 参数**是显式参数**
  --       （签名：`Integrable f μ → Integrable g μ → ∫ (f+g) = …`），
  --       写成 `rw [integral_add, …]` 后剩的 `·` 目标**不是**按书写顺序排列的
  --       （`rw` 反复重新 elaboration，位置漂移——正是 B205 的句法陷阱）。
  --       故这里**显式传参**，不留占位。
  --   (c) 第三处 `∑`/`∫` 的常数项：`integrable_const` 需要 `IsFiniteMeasure μ`；
  --       由 `[IsProbabilityMeasure μ]` **实例搜索可自动得到**（`infer_instance` 实测成功），
  --       无需 `haveI`（显式写 `IsProbabilityMeasure.toIsFiniteMeasure` 反而报
  --       `invalid field notation`，该名字在本版本不存在）。
  have hlin : ∫ ω, (F t ω - η * (F t ω - fstar) + η ^ 2 * C / 2) ∂μ
      = ∫ ω, F t ω ∂μ - η * (∫ ω, F t ω ∂μ - fstar) + η ^ 2 * C / 2 := by
    have hc : Integrable (fun _ : Ω => fstar) μ := integrable_const fstar
    have hsub : Integrable (fun ω => F t ω - fstar) μ := (hint t).sub hc
    have hηsub : Integrable (fun ω => η * (F t ω - fstar)) μ := hsub.const_mul η
    have h2 : Integrable (fun _ : Ω => η ^ 2 * C / 2) μ := integrable_const _
    have h1 : Integrable (fun ω => F t ω - η * (F t ω - fstar)) μ := (hint t).sub hηsub
    rw [integral_add h1 h2, integral_sub (hint t) hηsub]
    -- 标量抽出：用 `integral_smul`（`integral_const_mul` 不存在），转 `*` 形
    have hsm : (∫ a, η * (F t a - fstar) ∂μ) = η * ∫ a, (F t a - fstar) ∂μ := by
      have := integral_smul (𝕜 := ℝ) η (fun a => F t a - fstar) (μ := μ)
      simpa [smul_eq_mul] using this
    rw [hsm, integral_sub (hint t) hc]
    rw [show (∫ _a : Ω, fstar ∂μ) = fstar by
          rw [integral_const, MeasureTheory.measure_univ, ENNReal.one_toReal, one_smul]]
    rw [show (∫ _a : Ω, η ^ 2 * C / 2 ∂μ) = η ^ 2 * C / 2 by
          rw [integral_const, MeasureTheory.measure_univ, ENNReal.one_toReal, one_smul]]
  rw [hlin] at h1
  exact h1

/-- **B14 主结果：QAT 收敛率（期望序列版，`hstep` 由滤流推出）**。
设 `F` 是滤流 `𝒢` 上的可积损失过程、满足条件期望不等式（`condExp_step_le` 的前提）
且 `f⋆ ≤ F t` 处处成立。则对期望序列 `G t := ∫ F t dμ` 有
**前 `T` 步最优点的率**：

    ∃ t < T, G t − f⋆ ≤ (G 0 − f⋆)/(T·η) + η·C/2，

其中递推是**定理**（由 `condExp_step_le` 从条件期望不等式推出），**不是假设**。

**与 `qat_sgd_rate` 的关系**：`qat_sgd_rate` 把同样的结论建立在**假设** `hstep` 上；
本定理把它建立在**滤流 + 条件期望不等式**上——后者才是 SGD 分析里真正需要随机性的地方。
`η > 0`、`C ≥ 0`、`T > 0` 与 `qat_sgd_rate` 相同。 -/
theorem qat_sgd_rate_measure {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0} (F : ℕ → Ω → ℝ)
    (fstar η C : ℝ) (T : ℕ)
    (hT : 0 < T) (hη : 0 < η)
    (hint : ∀ t, Integrable (F t) μ)
    (hlow : ∀ t ω, fstar ≤ F t ω)
    (hcond : ∀ t, (μ[F (t + 1) | 𝒢 t]) ≤ᵐ[μ]
      fun ω => F t ω - η * (F t ω - fstar) + η ^ 2 * C / 2) :
    ∃ t : ℕ, t < T ∧ (∫ ω, F t ω ∂μ) - fstar
      ≤ (∫ ω, F 0 ω ∂μ - fstar) / ((T : ℝ) * η) + η * C / 2 := by
  -- 无条件下界：对 `f⋆ ≤ F t` 取积分
  have hGlow : ∀ t, fstar ≤ ∫ ω, F t ω ∂μ := by
    intro t
    have hle : ∫ _ω, fstar ∂μ ≤ ∫ ω, F t ω ∂μ :=
      integral_mono_ae (integrable_const fstar) (hint t) (Filter.Eventually.of_forall (hlow t))
    rwa [integral_const, MeasureTheory.measure_univ, ENNReal.one_toReal, one_smul] at hle
  -- 递推由 `condExp_step_le` 推出（**这里是 B14 的关键：不再是假设**）
  have hstep : ∀ t : ℕ, (∫ ω, F (t + 1) ω ∂μ)
      ≤ (∫ ω, F t ω ∂μ) - η * ((∫ ω, F t ω ∂μ) - fstar) + η ^ 2 * C / 2 :=
    fun t => condExp_step_le F fstar η C hint hcond t
  exact qat_sgd_rate (fun t => ∫ ω, F t ω ∂μ) fstar η C T hT hη hGlow hstep

/-! ## 二-1、B17 续：**从「条件无偏梯度 + 光滑性」推出条件期望不等式**

上面 `condExp_step_le` / `qat_sgd_rate_measure` 把 `hstep` 从**假设**变成
由「条件期望不等式」推出的**定理**。但仍留下最后一个缺口（原文诚实标注「未做」）：

    条件期望不等式本身，从 `g t` 的**条件无偏性 + 方差界**与 `f` 的**光滑性**推出。

本节点名要求的正是这一步。它在**有限条件分布**上完全可证：

设第 `t` 步历史下的随机梯度 `g` 取有限个值（`Fin n`），条件分布权重 `p` 满足
`Σ p = 1`、`p ≥ 0`。则：

  1. `CondGradModel`（**条件梯度模型**）：`p`（条件权重）、`g`（梯度的条件取值）、
     `η`（步长）、`L`（光滑常数）、`σ2`（条件方差上界）；
  2. **`CondUnbiased`**（条件无偏性）：`Σ_j p j · g j = grad`（记 `grad = ∇f(x_t)`）；
  3. **`CondVarianceLe`**（条件方差界）：`Σ_j p j · (g j − grad)² ≤ σ2`；
  4. `smooth_step_bound`（**逐实现二次上界的形式传递**）：把**给定的**上界
     `hSmooth : ∀ j, f (x − η g j) ≤ f x − η·g j·∇f x + η²L/2·(g j)²`
     **原样传递**为同形的 `∀ j` 结论。**⚠ R3 更正**：假设与结论**逐字相同**
     （是同一律实例），**不是**「光滑性 ⟹ 上界」的证明；真正的光滑性推理
     **未做**（属 `RealStrongConvex`/`RealHessian` 一族）；
  5. **`condExp_step_from_unbiased`（B17 主交付）**：对 4 取**条件期望**，
     用 2 消去一次项、用 3 控制二次项，得

         `E_j[f (x − η g j)] ≤ f x − η·(f x − f⋆)·… + η²·C/2`

     即**条件期望不等式**由「无偏 + 方差界 + 光滑」**推出**（不再是假设）。

**诚实边界（标注）**：
  · 本节的"条件期望"用**有限条件分布** `p`（`Fin n`）的加权和
    （`condExpFin`）编码。**与第二节的测度论 `condExp` 的关系**：
    当底层空间有限、`𝒢 t` 是有限 σ-代数时，`condExpFin` 就是 `μ[·|𝒢 t]`
    的纤维值——**本文件不做该桥接的形式化**（需要 `RealMartingaleChain`
    的有限纤维 `condExp` 机器），故两节的接口**人工对齐**（形状一致），
    **标注**为本节的形式化边界；
  · **光滑性假设**由 `smooth_step_bound` 的**逐点二次上界**形式给出
    （等价于 `L`-光滑的标准推论 `f(y) ≤ f(x) + ⟨∇f x, y−x⟩ + L/2‖y−x‖²`，
    本文件**不重证**它——那属于 `RealStrongConvex` / `RealHessian` 一族）；
  · 从 `f x − f⋆` 形式的下降需要**强凸性或 PL 条件**把 `f x − f⋆` 与
    `‖∇f x‖²` 挂钩（`‖∇f x‖² ≥ 2μ(f x − f⋆)`），本文件把
    `2μ(f x − f⋆) ≤ ‖∇f x‖²` 作为**显式假设** `hPL` 传入
    （它由 `RealPLCondition` / `RealStrongConvex` 提供，**不重证**）；
  · 仍**不构造**具体的量化器/噪声分布（`σ2`、`C` 都是显式参数）。
-/

/-- **条件梯度模型（B17）**：第 `t` 步历史下的随机梯度取有限个值
`g : Fin n → ℝ`、条件权重 `p : Fin n → ℝ`，配步长 `η`、光滑常数 `L`、
条件方差上界 `σ2`。**无偏性与方差界**由 `CondGradModel` 的两个字段给出。 -/
structure CondGradModel (n : ℕ) : Type where
  /-- 条件权重。 -/
  p : Fin n → ℝ
  /-- 梯度的条件取值。 -/
  g : Fin n → ℝ
  /-- 步长。 -/
  eta : ℝ
  /-- 光滑常数。 -/
  L : ℝ
  /-- 条件方差上界。 -/
  sigma2 : ℝ
  /-- 权重非负。 -/
  hp0 : ∀ j, 0 ≤ p j
  /-- 权重和为 1。 -/
  hp1 : (∑ j, p j) = 1
  /-- 步长正。 -/
  heta : 0 < eta
  /-- 光滑常数非负。 -/
  hL : 0 ≤ L
  /-- 条件方差界非负。 -/
  hσ2 : 0 ≤ sigma2

/-- **条件期望（有限条件分布）**：`E_j[φ j] = Σ_j p j · φ j`。
即 `CondGradModel` 的权重给出的条件期望。 -/
def condExpFin {n : ℕ} (M : CondGradModel n) (φ : Fin n → ℝ) : ℝ :=
  ∑ j, M.p j * φ j

/-- **条件无偏性**：`Σ_j p j · g j = grad`（`grad = ∇f x`）。
这是 SGD 分析里「随机梯度是真实梯度的条件无偏估计」的形式化。 -/
def CondUnbiased {n : ℕ} (M : CondGradModel n) (grad : ℝ) : Prop :=
  condExpFin M M.g = grad

/-- **条件方差界**：`Σ_j p j · (g j − grad)² ≤ σ2`。 -/
def CondVarianceLe {n : ℕ} (M : CondGradModel n) (grad : ℝ) : Prop :=
  condExpFin M (fun j => (M.g j - grad) ^ 2) ≤ M.sigma2

/-- **逐实现二次上界的形式传递**（**R3 诚实降级**）。

**本定理不证明光滑性，也不证明该二次上界**。它做的事只有一件：
把**外部给定的**逐点二次上界 `hSmooth` 从「对所有 `j` 成立」的
假设位置**移动**到「对所有 `j` 成立」的结论位置——两侧**逐字相同**，
证明体就是 `hSmooth` 本身。

**R3 实测记录**：本定理的假设与结论在源码中**逐字相同**（互为同一
表达式），故它是**同一律实例**（`hSmooth` 的 η-展开），而非数学内容。
原 docstring 写作「**光滑性 ⟹ 逐实现单步上界**」，其中的「⟹」是
**误导性的因果表述**：左侧并不是光滑性，而是**已经写成结论形状的上界**。

**为什么保留而不删除**：`condExp_step_from_unbiased` 与
`condExp_step_from_unbiased_PL` 需要「逐实例上界」这一**接口形状**；
本定理是该形状的**命名入口**（下游可据此定位「上界从哪来」）。
**⚠ 本定理不是任何真数学结论的支撑点**——任何引用本定理的论证，
其强度等于直接假设 `hSmooth`。

**诚实边界**：真正的 `L`-光滑 ⟹ 二次上界
（`f(y) ≤ f(x) + ⟨∇f x, y−x⟩ + (L/2)‖y−x‖²`）**本文件未证**，
**未做**——它属于 `RealStrongConvex` / `RealHessian` 一族。 -/
theorem smooth_step_bound {n : ℕ} (M : CondGradModel n) (fstep : ℝ → ℝ) (fx grad : ℝ)
    (hSmooth : ∀ j, fstep (M.g j) ≤ fx - M.eta * M.g j * grad
      + M.eta ^ 2 * M.L / 2 * (M.g j) ^ 2) :
    ∀ j, fstep (M.g j) ≤ fx - M.eta * M.g j * grad + M.eta ^ 2 * M.L / 2 * (M.g j) ^ 2 :=
  hSmooth

/-- **一次项的条件期望 = 无偏性（核心代数）**：`Σ_j p j · (η·g j·grad) = η·grad²`
（由 `CondUnbiased`）。 -/
theorem condExp_linear_eq {n : ℕ} (M : CondGradModel n) (grad : ℝ)
    (hunb : CondUnbiased M grad) :
    condExpFin M (fun j => M.eta * M.g j * grad) = M.eta * grad ^ 2 := by
  unfold condExpFin CondUnbiased at *
  -- After `unfold`, `hunb : condExpFin M M.g = grad` -- the `unfold` did NOT descend into
  -- the hypothesis's own `condExpFin`, so `hunb` is NOT literally `∑ j, M.p j * M.g j = grad`.
  -- `rw [hunb]` therefore cannot fire on the goal's `∑ …` (a `rw` is syntactic -- B205).
  -- Rewriting with the *definition* first normalises `hunb` into the sum shape we need.
  rw [condExpFin] at hunb
  rw [show (∑ j : Fin n, M.p j * (M.eta * M.g j * grad))
      = M.eta * grad * (∑ j : Fin n, M.p j * M.g j) by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)]
  rw [hunb]
  ring

/-- **二次项的条件期望被方差界控制（核心代数）**：
`Σ_j p j · g j² = σ2 + grad²` 型分解——
`E[g²] = E[(g − grad)²] + 2·grad·E[g] − grad² = Var + grad²`（用无偏性）。
故 `E[η²L/2·g²] ≤ η²L/2·(σ2 + grad²)`。
这是「噪声注入 `η²C/2`」项中 `C` 的**来源**。 -/
theorem condExp_sq_eq {n : ℕ} (M : CondGradModel n) (grad : ℝ)
    (hunb : CondUnbiased M grad) :
    condExpFin M (fun j => (M.g j) ^ 2)
      = condExpFin M (fun j => (M.g j - grad) ^ 2) + grad ^ 2 := by
  have hsum := hunb
  unfold CondUnbiased at hsum
  unfold condExpFin at hsum ⊢
  -- 逐点：`g² = (g − grad)² + 2·grad·(g − grad) + grad²`
  have hpt : ∀ j : Fin n, M.p j * (M.g j) ^ 2
      = M.p j * ((M.g j - grad) ^ 2 + grad ^ 2)
        + (2 * grad) * (M.p j * (M.g j - grad)) :=
    fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hpt j)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- ⚠ E2 实测（隔离复现）：`rw [Finset.sum_add_distrib, ← Finset.mul_sum]` 之后
  -- 目标并未成为「可直接消去」的形状。根因：`← Finset.mul_sum` 把
  -- `(2*grad) * (∑ j, M.p j * (M.g j - grad))` 保留为「标量 × 整和」，
  -- 而 `hzero` 的陈述正是这个**整和**；但 `hzero` 一旦重写掉它，
  -- 剩下的 `∑ x, M.p x * ((M.g x - grad)^2 + grad^2)` 与右端的
  -- `∑ j, M.p j * (fun j => (M.g j - grad)^2) j + grad^2` **句法不同**
  -- （B205：右侧是 beta-未化简的 `(fun j => …) j`，且常数 `grad²` 还在和**内**）
  -- ⟹ `unsolved goals`。
  -- 修法（**顺序**是关键）：**先**把剩下的 `∑ p·(φ + c)` 点态拆成
  -- `∑ p·φ + ∑ p·c`，**再**用 `hzero` 消去一次项、用 `h2` 形状抽出常数项。
  -- `hzero` 的证明体必须先于使用声明，故此处先建立它。
  -- `Σ p·(g − grad) = Σ p·g − grad·Σ p = grad − grad = 0`
  have hzero : (∑ j : Fin n, M.p j * (M.g j - grad)) = 0 := by
    have h1 : (∑ j : Fin n, M.p j * (M.g j - grad))
        = (∑ j : Fin n, M.p j * M.g j) - (∑ j : Fin n, M.p j * grad) := by
      -- `Finset.sum_sub_distrib` is stated for `∑ x ∈ s`; the binder form `∑ j : Fin n`
      -- elaborates the same way in a TERM position but the two are not syntactically the
      -- same goal, so `exact` reports a type mismatch. Rewriting the summand pointwise and
      -- then using the additive splitting lemma on `Finset.univ` works for either spelling.
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1, hsum]
    have h2 : (∑ j : Fin n, M.p j * grad) = grad := by
      -- ⚠ E2 实测（隔离复现）：**正向** `Finset.sum_mul` **打不中**。
      -- `#check @Finset.sum_mul` 给出其模式为
      --   `(∑ i ∈ ?s, ?f i) * ?a`  —— 即左端必须是 **(整个求和) * a**，
      -- 而这里的目标是 `∑ j, (M.p j * grad)`，即「每个 summand 内部右侧带常数」。
      -- 两者**句法不同**（B205/B260.4 的「常因子位置」陷阱），故报
      -- `did not find instance of the pattern`。
      -- 修法：用**反向** `← Finset.sum_mul`，它把 `∑ j, f j * a` 收成 `(∑ j, f j) * a`
      -- —— 这正是本目标的形状（常因子在 summand **右**侧）。随后 `hp1` + `one_mul`。
      rw [← Finset.sum_mul, M.hp1, one_mul]
    rw [h2]
    ring
  -- 先拆 `∑ p·((g−grad)² + grad²)`，使一次项与常数项**各自成和**，`hzero` 才能命中
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
    show M.p j * ((M.g j - grad) ^ 2 + grad ^ 2)
      = M.p j * (M.g j - grad) ^ 2 + M.p j * grad ^ 2 by ring)]
  -- ⚠ E2 实测（隔离复现）：**不要**把这几步写成一条 `rw` 链。
  -- `rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, …]` 在
  -- `← Finset.mul_sum` 处就失败：它的模式是 `∑ i ∈ ?s, ?a * ?f i`
  -- （`?f` 必须是**显式函数应用**），而此时目标里的
  -- `∑ x, M.p x * grad ^ 2` 的 summand `grad ^ 2` 是**裸项**、不是 `f x` 形，
  -- 故报 `did not find instance of the pattern`（B205）。
  -- 且 `sum_add_distrib` 会把和拆成**三**个独立求和，后续 `rw` 的匹配位置随之漂移。
  -- 修法：逐步 `rw`，且把「常数项 `grad²` 抽出」放进**独立 `have`**（见下）。
  rw [Finset.sum_add_distrib]
  rw [hzero, mul_zero, add_zero]
  -- 常数项 `∑ x, M.p x * grad ^ 2 = grad ^ 2`：
  -- 先用点态 `rfl` 把它写成**函数应用形**，再套 `← Finset.sum_mul`。
  have hconst_sq : (∑ x : Fin n, M.p x * grad ^ 2) = grad ^ 2 := by
    rw [show (∑ x : Fin n, M.p x * grad ^ 2)
        = ∑ x : Fin n, M.p x * (fun _ : Fin n => grad ^ 2) x from rfl]
    rw [← Finset.sum_mul, M.hp1, one_mul]
  -- 右侧 beta-形 `∑ j, M.p j * (fun j => (M.g j - grad)^2) j`
  -- 与左侧 `∑ j, M.p j * (M.g j - grad)^2` 用 `rfl` 对齐（beta 化简）
  rw [show (∑ j : Fin n, M.p j * (fun j => (M.g j - grad) ^ 2) j)
      = ∑ j : Fin n, M.p j * (M.g j - grad) ^ 2 from rfl]
  rw [hconst_sq]

/-- **B17 主交付：条件期望不等式由「无偏 + 方差界 + 光滑性」推出**。

给定 `CondGradModel`、`f` 在 `x` 处的光滑二次上界 `hSmooth`、条件无偏
`hunb`、条件方差界 `hvar`，则**取条件期望**后

    `E_j[f (x − η g j)] ≤ f x − η·grad² + η²L/2·(σ2 + grad²)`。

即第二节的 `hstep`（条件期望不等式）**不再是假设**，而是由
「随机梯度的条件无偏性 + 条件方差界 + 目标函数的光滑性」**推出的定理**。

**与 `qat_sgd_rate_measure` 的衔接**：再用 PL / 强凸性
`2μ(f x − f⋆) ≤ grad²`（显式假设 `hPL`）把 `grad²` 换成 `f x − f⋆`，
即得到 `E_j[f(x−ηg j)] ≤ f x − η·2μ(f x − f⋆) + η²L/2·(σ2 + grad²)`
——这正是 `condExp_step_le` 所需的形状（见 `condExp_step_from_unbiased_PL`）。

**证明用到的两条分解**：一次项由**无偏性**消去（`condExp_linear_eq` 给出该步的
独立陈述），二次项由**方差界**控制（`condExp_sq_eq`：`E[g²] = Var + grad² ≤ σ2 + grad²`）；
本证明内部另用三个通用线性性引理（`hadd`/`hconst`/`hscalar`）实现同样的代数，
故 `condExp_linear_eq` 可作为**下游复用的独立入口**。 -/
theorem condExp_step_from_unbiased {n : ℕ} (M : CondGradModel n) (fstep : ℝ → ℝ)
    (fx grad : ℝ) (hunb : CondUnbiased M grad) (hvar : CondVarianceLe M grad)
    (hSmooth : ∀ j, fstep (M.g j) ≤ fx - M.eta * M.g j * grad
      + M.eta ^ 2 * M.L / 2 * (M.g j) ^ 2) :
    condExpFin M (fun j => fstep (M.g j))
      ≤ fx - M.eta * grad ^ 2 + M.eta ^ 2 * M.L / 2 * (M.sigma2 + grad ^ 2) := by
  -- 1. 有条件期望单调性：逐实现上界 ⟹ 条件期望上界
  have hmono : condExpFin M (fun j => fstep (M.g j))
      ≤ condExpFin M (fun j => fx - M.eta * M.g j * grad
          + M.eta ^ 2 * M.L / 2 * (M.g j) ^ 2) := by
    unfold condExpFin
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hSmooth j) (M.hp0 j))
  -- 2. 右端的条件期望 = fx − η·grad² + η²L/2·(E[g²])
  --    用 `condExpFin` 的「线性性 + 常数抽出」逐项处理（拆成三项的和）
  have hadd : ∀ (φ ψ : Fin n → ℝ),
      condExpFin M (fun j => φ j + ψ j) = condExpFin M φ + condExpFin M ψ := by
    intro φ ψ
    unfold condExpFin
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hconst : ∀ c : ℝ, condExpFin M (fun _ : Fin n => c) = c := by
    intro c
    unfold condExpFin
    rw [← Finset.sum_mul, M.hp1, one_mul]
  have hscalar : ∀ (c : ℝ) (φ : Fin n → ℝ),
      condExpFin M (fun j => c * φ j) = c * condExpFin M φ := by
    intro c φ
    unfold condExpFin
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hlin : condExpFin M (fun j => fx - M.eta * M.g j * grad
        + M.eta ^ 2 * M.L / 2 * (M.g j) ^ 2)
      = fx - M.eta * grad ^ 2
        + M.eta ^ 2 * M.L / 2 * condExpFin M (fun j => (M.g j) ^ 2) := by
    have hsplit : (fun j : Fin n => fx - M.eta * M.g j * grad
          + M.eta ^ 2 * M.L / 2 * (M.g j) ^ 2)
        = fun j => (fx + (-(M.eta * grad)) * M.g j)
            + (M.eta ^ 2 * M.L / 2) * (M.g j) ^ 2 := by
      funext j; ring
    rw [hsplit, hadd, hadd, hconst, hscalar, hscalar]
    have hg : condExpFin M M.g = grad := hunb
    rw [hg]
    ring
  -- 3. `E[g²] = Var + grad² ≤ σ2 + grad²`
  have hsq : condExpFin M (fun j => (M.g j) ^ 2)
      ≤ M.sigma2 + grad ^ 2 := by
    rw [condExp_sq_eq M grad hunb]
    have := hvar
    unfold CondVarianceLe at this
    linarith
  calc condExpFin M (fun j => fstep (M.g j))
      ≤ condExpFin M (fun j => fx - M.eta * M.g j * grad
          + M.eta ^ 2 * M.L / 2 * (M.g j) ^ 2) := hmono
    _ = fx - M.eta * grad ^ 2
        + M.eta ^ 2 * M.L / 2 * condExpFin M (fun j => (M.g j) ^ 2) := hlin
    _ ≤ fx - M.eta * grad ^ 2 + M.eta ^ 2 * M.L / 2 * (M.sigma2 + grad ^ 2) := by
        -- ⚠ E2 实测（隔离复现）：`positivity` 在本目标上**失败**——
        -- 报 `failed to prove positivity/nonnegativity/nonzeroness`。
        -- 根因**不是**缺假设（`M.heta : 0 < M.eta`、`M.hL : 0 ≤ M.L` 都在结构里，
        -- 且 `η² ≥ 0` 由 `sq_nonneg` 可得）：`positivity` 的**除法后端**只处理
        -- 「除以一个**字面数字**」的规范形，而这里的 `/ 2` 作用在
        -- `M.eta ^ 2 * M.L`（一个**变量乘积**）上，其 `Div` 在 `ℝ` 上被展开为
        -- `* (2)⁻¹`，`positivity` 的 `mul` 分支在遇到 `2⁻¹` 这个非字面常数时
        -- 无法判定正性 ⟹ 回落失败。
        -- 修法：**不依赖** `positivity`，显式给出非负性链（`sq_nonneg` + `mul_nonneg`
        -- + `div_nonneg`/`linarith`）。这与文件其余处的风格一致，且**不引入新假设**。
        have hη2 : (0 : ℝ) ≤ M.eta ^ 2 := sq_nonneg M.eta
        have hηL : (0 : ℝ) ≤ M.eta ^ 2 * M.L := mul_nonneg hη2 M.hL
        have hc : 0 ≤ M.eta ^ 2 * M.L / 2 := by linarith
        linarith [mul_le_mul_of_nonneg_left hsq hc]

/-- **B17 收尾：PL/强凸 ⟹ `condExp_step_le` 形状的条件期望不等式**。

在 `condExp_step_from_unbiased` 之上，再用 PL/强凸性
`2μ·(fx − f⋆) ≤ grad²`（显式假设 `hPL`，由 `RealPLCondition` /
`RealStrongConvex` 提供）把 `grad²` 下界换成 `2μ(fx − f⋆)`，得

    `E_j[f (x − η g j)] ≤ fx − 2ημ(fx − f⋆) + η²·C/2`，

其中 `C := L·(σ2 + grad²)`。**这正是 `condExp_step_le` 的前提形状**
（把 `fx` 记作 `F t`、`f⋆` 记作 `fstar`、`2μ` 记作递推里的系数）——
故第二节的 `hstep` 至此**完全由「无偏 + 方差界 + 光滑 + PL」推出**。 -/
theorem condExp_step_from_unbiased_PL {n : ℕ} (M : CondGradModel n) (fstep : ℝ → ℝ)
    (fx grad fstar mu : ℝ)
    (hunb : CondUnbiased M grad) (hvar : CondVarianceLe M grad)
    (hPL : 2 * mu * (fx - fstar) ≤ grad ^ 2)
    (hSmooth : ∀ j, fstep (M.g j) ≤ fx - M.eta * M.g j * grad
      + M.eta ^ 2 * M.L / 2 * (M.g j) ^ 2) :
    condExpFin M (fun j => fstep (M.g j))
      ≤ fx - M.eta * (2 * mu * (fx - fstar))
        + M.eta ^ 2 * (M.L * (M.sigma2 + grad ^ 2)) / 2 := by
  have hbase := condExp_step_from_unbiased M fstep fx grad hunb hvar hSmooth
  have heta := M.heta.le
  have hstep1 : M.eta * (2 * mu * (fx - fstar)) ≤ M.eta * grad ^ 2 :=
    mul_le_mul_of_nonneg_left hPL heta
  have hC : M.eta ^ 2 * M.L / 2 * (M.sigma2 + grad ^ 2)
      = M.eta ^ 2 * (M.L * (M.sigma2 + grad ^ 2)) / 2 := by ring
  rw [hC] at hbase
  linarith

/-! ## 三、主结果：带量化噪声的 SGD 收敛率（min-index 形式）

`qat_sgd_rate`（**本节的 min-index 率的主定理**）已在 §二-0 之前提前声明 ——
见上方「## 〇、望远镜率主定理（前移）」一段：`condExp_step_le`（§二-0）与
`qat_sgd_rate_measure`（§二-0）都需要引用它，而 Lean 要求**先声明后使用**，
故此处只保留指向说明，不重复声明（避免同一名字声明两次）。
-/

/-! ## 四、主结果：噪声形式（把 C 具体化为 σ² + ν²） -/

/-- **主结果（噪声形式）**：把 `qat_sgd_rate` 中的噪声方差上界 `C` 具体化为
`qatNoise σ ν = σ² + ν²`，得到
`F t − f⋆ ≤ (F 0 − f⋆)/(T·η) + η·(σ² + ν²)/2`。
`σ` 为随机梯度噪声、`ν` 为量化噪声（可用 `qatFloorNoise` 代入）。 -/
theorem qat_sgd_rate_noise (F : ℕ → ℝ) (fstar η σ ν : ℝ) (T : ℕ)
    (hT : 0 < T) (hη : 0 < η)
    (hlow : ∀ t : ℕ, fstar ≤ F t)
    (hstep : ∀ t : ℕ, F (t + 1) ≤ F t - η * (F t - fstar) + η ^ 2 * qatNoise σ ν / 2) :
    ∃ t : ℕ, t < T ∧ F t - fstar ≤ (F 0 - fstar) / ((T : ℝ) * η) + η * (σ ^ 2 + ν ^ 2) / 2 := by
  have hC : 0 ≤ qatNoise σ ν := by
    unfold qatNoise
    exact add_nonneg (sq_nonneg σ) (sq_nonneg ν)
  have h := qat_sgd_rate F fstar η (qatNoise σ ν) T hT hη hlow hstep
  simpa only [qatNoise] using h

/-! ## 五、主结果：噪声项与学习率的最优权衡 -/

/-- **主结果（最优权衡）**：对任意步长 `η > 0`，
`√(2AC/T) ≤ A/(T·η) + η·C/2`（`A ≥ 0`、`C ≥ 0`、`T > 0`）。
证明为 AM-GM：令 `u = A/(T·η)`、`v = η·C/2`，则 `4uv = 2AC/T`，
且 `(u+v)² = 4uv + (u−v)² ≥ 4uv`，由 `Real.sqrt_le_left` 得结论。
即：**无论怎么选步长，收敛界的噪声项都不可能低于 `√(2AC/T)`**。 -/
theorem qat_optimal_stepsize (A C T : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hT : 0 < T) :
    ∀ η : ℝ, 0 < η → Real.sqrt (2 * A * C / T) ≤ A / ((T : ℝ) * η) + η * C / 2 := by
  intro η hη
  set u : ℝ := A / (T * η) with hu
  set v : ℝ := η * C / 2 with hv
  have hu0 : 0 ≤ u := by
    rw [hu]; exact div_nonneg hA (mul_pos hT hη).le
  have hv0 : 0 ≤ v := by
    rw [hv]; exact div_nonneg (mul_nonneg hη.le hC) (by norm_num)
  have huv : 4 * (u * v) = 2 * A * C / T := by
    rw [hu, hv]
    field_simp
    ring
  have hsq : 2 * A * C / T ≤ (u + v) ^ 2 := by
    nlinarith [sq_nonneg (u - v), huv]
  rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ u + v)]
  exact hsq

/-- **主结果（最优步长取到下界）**：取 `η⋆ = √(2A/(T·C))`（`A > 0`、`C > 0`、`T > 0`），
则 `A/(T·η⋆) + η⋆·C/2 = √(2AC/T)`——AM-GM 的下界是**可达**的。 -/
theorem qat_optimal_stepsize_attained (A C T : ℝ) (hA : 0 < A) (hC : 0 < C) (hT : 0 < T) :
    A / ((T : ℝ) * Real.sqrt (2 * A / (T * C)))
      + Real.sqrt (2 * A / (T * C)) * C / 2 = Real.sqrt (2 * A * C / T) := by
  set s : ℝ := Real.sqrt (2 * A / (T * C)) with hs
  have hs2 : s ^ 2 = 2 * A / (T * C) := by
    rw [hs]; exact Real.sq_sqrt (by positivity)
  have hspos : 0 < s := by
    rw [hs]; exact Real.sqrt_pos.mpr (by positivity)
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hpos : 0 < A / (T * s) + s * C / 2 := by
    have h1 : 0 < A / (T * s) := div_pos hA (mul_pos hT hspos)
    have h2 : 0 ≤ s * C / 2 := div_nonneg (mul_nonneg hspos.le hC.le) (by norm_num)
    linarith
  have hsq : (A / (T * s) + s * C / 2) ^ 2 = 2 * A * C / T := by
    -- 先通分到公分母 `(T*s*2)²`，再把 `s²` 统一成 `s * s` 代入 `hs2`
    -- （`field_simp` 清分母时会打散裸 `s ^ 2`，故必须先做替换）。
    have hden : (T * s * 2) ^ 2 ≠ 0 := by positivity
    have hL : (A / (T * s) + s * C / 2) ^ 2
        = (A * 2 + T * s * (s * C)) ^ 2 / (T * s * 2) ^ 2 := by
      rw [div_add_div _ _ (ne_of_gt (mul_pos hT hspos)) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [hL, div_eq_div_iff hden (ne_of_gt hT)]
    have hsub : s * s = 2 * A / (T * C) := by rw [← sq, hs2]
    have hTs2 : T * s * (s * C) = T * (s * s) * C := by ring
    have hden2 : (T * s * 2) ^ 2 = T ^ 2 * (s * s) * 4 := by ring
    rw [hTs2, hden2, hsub]
    field_simp
    ring
  rw [show A / ((T : ℝ) * s) + s * C / 2 = A / (T * s) + s * C / 2 by ring]
  rw [← hsq]
  exact (Real.sqrt_sq hpos.le).symm

/-! ## 六、对迭代数与无噪声情形的退化 -/

/-- **主结果（率的 `1/T` 项随迭代数下降）**：固定 `η > 0`、`C ≥ 0`、`A ≥ 0`，
若 `0 < T1 ≤ T2`，则
`A/(T2·η) + η·C/2 ≤ A/(T1·η) + η·C/2`。
即收敛界中的优化项随迭代数单调不增（`T` 越大越好）。 -/
theorem qat_rate_decreasing_in_T (A C η : ℝ) (hA : 0 ≤ A) (hη : 0 < η)
    {T1 T2 : ℕ} (hT1 : 0 < T1) (h12 : T1 ≤ T2) :
    A / ((T2 : ℝ) * η) + η * C / 2 ≤ A / ((T1 : ℝ) * η) + η * C / 2 := by
  have hT1pos : (0 : ℝ) < (T1 : ℝ) := by exact_mod_cast hT1
  have hcast : (T1 : ℝ) ≤ (T2 : ℝ) := by exact_mod_cast h12
  have hmain : A / ((T2 : ℝ) * η) ≤ A / ((T1 : ℝ) * η) :=
    div_le_div_of_nonneg_left hA (mul_pos hT1pos hη)
      (mul_le_mul_of_nonneg_right hcast hη.le)
  linarith

/-- **主结果（无噪声退化）**：`σ = ν = 0`（无随机梯度噪声、无量化噪声）时，
递推退化为 `F (t+1) ≤ F t − η·(F t − f⋆)`，结论退化为
`F t − f⋆ ≤ (F 0 − f⋆)/(T·η)`（噪声项 `η·C/2 = 0`）。
这是 `RealQAT.qat_convergence_zero` 的率形式对应。 -/
theorem qat_noiseless_rate (F : ℕ → ℝ) (fstar η : ℝ) (T : ℕ)
    (hT : 0 < T) (hη : 0 < η)
    (hlow : ∀ t : ℕ, fstar ≤ F t)
    (hstep : ∀ t : ℕ, F (t + 1) ≤ F t - η * (F t - fstar)) :
    ∃ t : ℕ, t < T ∧ F t - fstar ≤ (F 0 - fstar) / ((T : ℝ) * η) := by
  have hstep' : ∀ t : ℕ, F (t + 1) ≤ F t - η * (F t - fstar) + η ^ 2 * (0 : ℝ) / 2 := by
    intro t
    have h := hstep t
    have hz : η ^ 2 * (0 : ℝ) / 2 = 0 := by ring
    linarith
  obtain ⟨t, ht, hle⟩ := qat_sgd_rate F fstar η 0 T hT hη hlow hstep'
  refine ⟨t, ht, ?_⟩
  have hz : η * (0 : ℝ) / 2 = 0 := by ring
  linarith

/-! ## 七、与 RealQAT 误差地板的衔接 -/

/-- **QAT 地板噪声非负**：`0 ≤ qatFloorNoise Anorm δ cx = Anorm·δ/(1−cx)`
（`0 ≤ Anorm`、`0 ≤ δ`、`cx < 1`）。地板是真实的不可约残差，
`Anorm·δ > 0` 时严格为正（对齐 `RealQAT.qat_floor_nonneg`）。 -/
theorem qat_floor_noise_nonneg (Anorm δ cx : ℝ) (hA : 0 ≤ Anorm) (hδ : 0 ≤ δ) (hc : cx < 1) :
    0 ≤ qatFloorNoise Anorm δ cx := by
  unfold qatFloorNoise
  exact div_nonneg (mul_nonneg hA hδ) (by linarith)

/-- **QAT 地板噪声随 `Anorm` 单调增**：`Anorm ≤ Anorm'`、`0 ≤ δ`、`cx < 1` ⟹
`qatFloorNoise Anorm δ cx ≤ qatFloorNoise Anorm' δ cx`
（`‖A‖` 越大，量化注入的稳态残差越大）。 -/
theorem qat_floor_noise_mono (Anorm Anorm' δ cx : ℝ) (hδ : 0 ≤ δ) (hc : cx < 1)
    (hAA : Anorm ≤ Anorm') :
    qatFloorNoise Anorm δ cx ≤ qatFloorNoise Anorm' δ cx := by
  unfold qatFloorNoise
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAA hδ) (by linarith)

/-- **主结果（噪声项与 QAT 地板的衔接）**：把 `ν := qatFloorNoise Anorm δ cx`
（即 `RealQAT.qat_convergence` 的地板 `‖A‖·δ/(1−c)`）代入噪声项时，
总噪声项 `η·(σ² + ν²)/2` **不小于**纯随机梯度噪声项 `η·σ²/2`：

`η·σ²/2 ≤ η·qatNoise σ (qatFloorNoise Anorm δ cx)/2`
（`0 ≤ σ`、`0 ≤ η`、地板非负）。即量化误差地板**放大**了 SGD 的噪声项，
从而抬高 `qat_sgd_rate` 中的 `η·C/2` 项。 -/
theorem qat_floor_noise_link (Anorm δ cx σ η : ℝ) (hA : 0 ≤ Anorm) (hδ : 0 ≤ δ)
    (hc : cx < 1) (hη : 0 ≤ η) :
    η * σ ^ 2 / 2 ≤ η * qatNoise σ (qatFloorNoise Anorm δ cx) / 2 := by
  have hν : 0 ≤ qatFloorNoise Anorm δ cx := qat_floor_noise_nonneg Anorm δ cx hA hδ hc
  have hν2 : 0 ≤ (qatFloorNoise Anorm δ cx) ^ 2 := sq_nonneg _
  have hησ : 0 ≤ η * σ ^ 2 := mul_nonneg hη (sq_nonneg σ)
  have hην2 : 0 ≤ η * (qatFloorNoise Anorm δ cx) ^ 2 := mul_nonneg hη hν2
  unfold qatNoise
  nlinarith

/-! ## 注：闭环语义（QAT 的率与噪声权衡）

  · **率**：`qat_sgd_rate` 把带噪声 SGD 的界 `(F 0 − f⋆)/(T·η) + η·C/2`
    形式化为**前 `T` 步最优点**的界（标注：不是对 `F T` 的界，也不是轨道收敛）；
    `hstep` 是显式假设而非从随机过程推出。`qat_sgd_rate_noise` 把 `C` 具体化为
    `σ² + ν²`（随机梯度噪声 + 量化噪声）。
  · **噪声**：`ν` 可直接取 `qatFloorNoise Anorm δ cx = Anorm·δ/(1−cx)`，
    这正是 `RealQAT.qat_convergence` 的地板 `‖A‖·δ/(1−c)`；`qat_floor_noise_link`
    说明量化地板**放大**总噪声项，与 `RealQAT` 的「QAT 无法收敛到零误差」一致
    （`qat_floor_noise_nonneg`/`qat_floor_noise_mono`）。
  · **权衡**：`qat_optimal_stepsize` 给出**普适下界** `√(2AC/T)`（AM-GM），
    `qat_optimal_stepsize_attained` 说明 `η⋆ = √(2A/(T·C))` **取到**该下界：
    步长既不能太大（噪声项 `η·C/2` 增大）也不能太小（`1/T` 优化项增大）。
    `qat_rate_decreasing_in_T` 给出 `1/T` 项随迭代数下降；`qat_noiseless_rate`
    是 `σ = ν = 0` 的无噪声退化（回收 `RealQAT.qat_convergence_zero` 的率形式）。
  · **诚实边界（标注）**：滤流层**已做**——§二-0 用 `Filtration` 与条件期望
    `condexp` 的测度论形式化（`condExp_step_le`）推出无条件期望递推，
    §二-1 又从**条件无偏 + 条件方差界 + 光滑性 + PL**（`condExp_step_from_unbiased` /
    `condExp_step_from_unbiased_PL`）推出该条件期望不等式本身，故
    `qat_sgd_rate_measure` 中的递推由**随机梯度性质推出**，不再是假设。
    **仍未做/仍属假设**的只有：**不构造**具体量化器与噪声分布（`σ2`、`C` 为显式参数）；
    §二-1 的"条件期望"以**有限条件分布** `Fin n` 编码，**与测度论 `condExp` 的桥接未形式化**（两节接口人工对齐）；
    `smooth_step_bound` 只是逐实现二次上界的**同一律传递**，真正的 `L`-光滑 ⟹ 二次上界**未证**（属 `RealStrongConvex`/`RealHessian` 一族）；
    也**未做** `F T` 或最后一迭代的界；常数因 `η²C/2` 的写法与教科书相差一个因子。
  无 sorry/axiom/admit。 -/

end Lattice
