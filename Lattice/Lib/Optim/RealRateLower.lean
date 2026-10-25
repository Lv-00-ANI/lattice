import Mathlib
import Lattice.Lib.Optim.RealGradDescent
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Optim.RealStrongConvex
/-!
# LATTICE: 收敛率的下界 / 锐性 —— 二次函数上 GD 的界是紧的

RealStrongConvex 给出光滑强凸下 GD 的线性收敛**上界**（收缩系数 1 − μη 或
((L−μ)/(L+μ))²）。本文件从反方向给出**紧性（sharpness）与下界型结果**：

模型（与 RealGradDescent 的标量谱条件同口径）：f(x) = a·x²，∇f(x) = 2a·x，
极小点 x* = 0，GD 步长 η 的更新
    x_{n+1} = x_n − 2ηa·x_n = (1 − 2ηa)·x_n。

结果：
  1. `QuadIter_exact`：**精确**迭代公式 x_n = (1 − 2ηa)ⁿ·x_0（不是不等式）；
  2. `gd_sharpness`：0 ≤ 1 − 2ηa ⟹ ‖x_n‖ = (1 − 2ηa)ⁿ·‖x_0‖ —— 误差**恰好**是
     (1 − 2ηa)ⁿ·e_0（任务目标），且 `gd_sharpness_sq` 给出平方版
     ‖x_n‖² = (1 − 2ηa)^{2n}·‖x_0‖²；
  3. `no_faster_than_geometric`：任何对**所有**初值成立的一致几何界
     ‖x_n‖ ≤ cⁿ‖x_0‖ 必须满足 c ≥ 1 − 2ηa。即上界分析所给的率**不可改进**
     （n = 1 即已达紧）；
  4. `gd_oscillation_counterexample`（a = 1, η = 1，1 − 2ηa = −1）：迭代振荡
     x_n = (−1)ⁿx_0，误差恒为 ‖x_0‖ > 0 —— **不收敛**，步长条件不可去掉；
  5. `gd_divergence_counterexample`（a = 1, η = 2，1 − 2ηa = −3）：‖x_n‖ = 3ⁿ‖x_0‖
     —— 发散；
  6. `gd_upper_bound_tight`（跨文件对比）：对同一二次模型，RealStrongConvex 的
     光滑差距上界 `strong_convex_gap_bound`（L = 2a）给出 a·x² ≤ a·x²（等式），
     说明上界在二次函数上恰被取到 —— 界是紧的；
  7. `first_order_single_step_no_confusion`：一维中一次一阶询问 (f x, 0) 且
     函数凸时，x 已被钉为全局极小点（`Subgradient f x 0` ⟹ ∀ y, f x ≤ f y）。

诚实标注（一阶下界的降级说明）—— ⭐ **本节已按 R5 / P3-1 逐句分类：
哪句是定理、哪句是散文，均可核对**：

  · ⚠ **散文（PROSE，非定理）—— "一维不存在非平凡的一阶方法下界"**：
    ⚠ **本句不可作为定理陈述**，因为库中**没有**它所需的"一阶预言机模型"
    （算法类 / 对手 / 查询预算 / 度量）。`RealSubgradient.Subgradient f x g`
    （`RealSubgradient.lean:44`）是**逐点谓词** `∀ y, f y ≥ f x + g*(y-x)`，
    **无查询预算、无算法、无历史** ⟹ n 步下界**不可表达**。
    ⇒ ⭐ **本句的性质是"缺一个定义"，不是"缺一个难定理"**；
    ⚠ **故它保留为散文，并在此显式标注为散文，不冒充定理**（ROADMAP-v2:41 的 P3-1）。
    ⭐ **其实质内容在本文件第五节的 `first_order_single_step_no_confusion` 中
    以【可证命题】的形式给出**（见下条）——即"一次询问就把候选极小点钉住"。

  · ✅ **定理（THEOREM，已证）—— "一维中一阶方法能在一个梯度查询内读出曲率"**：
    ⚠ 原句的 `g = a·x_0` 中 `g` 与 `x_0` **是未绑定符号**（本文件从未命名梯度）。
    ⭐ **该句的可证形式已在本文件第五节【成为定理】**（命名梯度 + 唯一性）：
    `QuadGrad` / `QuadGrad_eq` / `curvature_recovered_in_one_query`
    （`a = QuadGrad a x₀ / (2 * x₀)`，需 `x₀ ≠ 0`）/
    `curvature_determined_by_one_query`（一次查询对 `a` **单射**）/
    `zero_query_collapses_curvatures`（证 `x₀ ≠ 0` **承重**）。
    ⚠ 等价形式另见 R5 探针 `_r5_p31_ratelower.lean`（**未进 roots**）。

  · ✅ **已证的替代物**：经典 Nesterov 下界需要高维稀疏结构 + 多步路径构造，
    超出本文件范围。任务允许「若完整证明太重则退化为具体反例构造」，
    本文件据此给出：精确等式（1）、紧性（3）与两个具体反例（4/5），
    并明确标注一般下界为后续工作；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、二次模型与精确迭代 -/

/-- 二次模型 f(x) = a·x²（梯度 2a·x，极小点 0）。 -/
def QuadF (a x : ℝ) : ℝ := a * x ^ 2

/-- 收缩因子 1 − 2ηa。 -/
def QuadRate (a η : ℝ) : ℝ := 1 - 2 * η * a

/-- GD 步：x' = x − 2ηa·x。 -/
def QuadStep (a η x : ℝ) : ℝ := x - 2 * η * a * x

/-- GD 迭代。 -/
def QuadIter (a η : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => QuadIter a η n (QuadStep a η x)

/-- 收缩因子形式：QuadStep a η x = (1 − 2ηa)·x。 -/
lemma QuadStep_eq (a η x : ℝ) : QuadStep a η x = QuadRate a η * x := by
  simp only [QuadStep, QuadRate]
  ring

/-- **精确迭代公式**：x_n = (1 − 2ηa)ⁿ·x_0。 -/
theorem QuadIter_exact (a η : ℝ) :
    ∀ (n : ℕ) (x : ℝ), QuadIter a η n x = (QuadRate a η) ^ n * x := by
  intro n
  induction n with
  | zero => intro x; simp [QuadIter]
  | succ n ih =>
      intro x
      calc
        QuadIter a η (n + 1) x = QuadIter a η n (QuadStep a η x) := rfl
        _ = (QuadRate a η) ^ n * QuadStep a η x := ih (QuadStep a η x)
        _ = (QuadRate a η) ^ n * ((QuadRate a η) * x) := by rw [QuadStep_eq]
        _ = (QuadRate a η) ^ (n + 1) * x := by ring

/-! ## 二、锐性：误差恰好是 (1 − 2ηa)ⁿ·e_0 -/

/-- **GD 锐性（任务目标）**：0 ≤ 1 − 2ηa ⟹
‖x_n‖ = (1 − 2ηa)ⁿ·‖x_0‖ —— 误差恰好是几何衰减，界不可改进。 -/
theorem gd_sharpness (a η : ℝ) (h0 : 0 ≤ QuadRate a η) :
    ∀ (n : ℕ) (x0 : ℝ), ‖QuadIter a η n x0‖ = (QuadRate a η) ^ n * ‖x0‖ := by
  intro n x0
  rw [QuadIter_exact, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg h0]

/-- 平方误差版：‖x_n‖² = (1 − 2ηa)^{2n}·‖x_0‖²。 -/
theorem gd_sharpness_sq (a η : ℝ) :
    ∀ (n : ℕ) (x0 : ℝ),
      (QuadIter a η n x0) ^ 2 = (QuadRate a η) ^ (2 * n) * x0 ^ 2 := by
  intro n x0
  rw [QuadIter_exact, mul_pow, ← pow_mul, Nat.mul_comm]

/-- **上界不可改进**：若对所有初值与所有 n 有 ‖x_n‖ ≤ cⁿ·‖x_0‖，则
1 − 2ηa ≤ c。即 (1 − 2ηa) 是任何一致几何界的最优常数（n = 1 即达紧）。 -/
theorem no_faster_than_geometric (a η c : ℝ) (h0 : 0 ≤ QuadRate a η)
    (h : ∀ (x0 : ℝ) (n : ℕ),
      ‖QuadIter a η n x0‖ ≤ c ^ n * ‖QuadIter a η 0 x0‖) :
    QuadRate a η ≤ c := by
  have hh := h 1 1
  have hL : ‖QuadIter a η 1 (1 : ℝ)‖ = QuadRate a η := by
    rw [QuadIter_exact]
    simp [Real.norm_eq_abs, abs_of_nonneg h0]
  have hR : ‖QuadIter a η 0 (1 : ℝ)‖ = 1 := by
    simp [QuadIter]
  rw [hL, hR, pow_one, mul_one] at hh
  exact hh

/-! ## 三、步长条件的必要性：两个具体反例 -/

/-- **振荡反例**（a = 1、η = 1，收缩因子 1 − 2 = −1）：误差恒为 ‖x_0‖ > 0，
故不收敛 —— 步长条件 η < 1/a 不可去掉。 -/
theorem gd_oscillation_counterexample (x0 : ℝ) (hx0 : x0 ≠ 0) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖QuadIter 1 1 n x0‖ < ε) := by
  intro h
  have hconst : ∀ n : ℕ, ‖QuadIter (1 : ℝ) 1 n x0‖ = ‖x0‖ := by
    intro n
    have hq : QuadRate (1 : ℝ) 1 = -1 := by norm_num [QuadRate]
    rw [QuadIter_exact, hq, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow]
    simp [abs_neg]
  have hx0n : 0 < ‖x0‖ := by
    rw [Real.norm_eq_abs]
    exact abs_pos.mpr hx0
  rcases h ‖x0‖ hx0n with ⟨n, hn⟩
  rw [hconst n] at hn
  exact lt_irrefl _ hn

/-- **发散反例**（a = 1、η = 2，收缩因子 1 − 4 = −3）：‖x_n‖ = 3ⁿ·‖x_0‖，
故发散。 -/
theorem gd_divergence_counterexample (x0 : ℝ) (hx0 : x0 ≠ 0) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖QuadIter 1 2 n x0‖ < ε) := by
  intro h
  have hconst : ∀ n : ℕ, ‖QuadIter (1 : ℝ) 2 n x0‖ = 3 ^ n * ‖x0‖ := by
    intro n
    have hq : QuadRate (1 : ℝ) 2 = -3 := by norm_num [QuadRate]
    rw [QuadIter_exact, hq, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow]
    simp [abs_neg]
  have hx0n : 0 < ‖x0‖ := by
    rw [Real.norm_eq_abs]
    exact abs_pos.mpr hx0
  rcases h ‖x0‖ hx0n with ⟨n, hn⟩
  rw [hconst n] at hn
  have hpow : (1 : ℝ) ≤ 3 ^ n := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 3) n
    simpa using hh
  nlinarith [hpow, hx0n, hn]

/-! ## 四、跨文件对比：RealStrongConvex 的光滑上界在二次函数上取等 -/

/-- 二次模型是 (2a)-强凸（在 x* = 0 处）。 -/
theorem quad_model_strong_convex (a : ℝ) :
    StrongConvex (2 * a) (QuadF a) (fun x : ℝ => 2 * a * x) := by
  intro x y
  simp only [QuadF]
  nlinarith

/-- 二次模型是 (2a)-光滑。 -/
theorem quad_model_smooth (a : ℝ) :
    Smooth (2 * a) (QuadF a) (fun x : ℝ => 2 * a * x) := by
  intro x y
  simp only [QuadF]
  nlinarith

/-- **上界取等（紧性）**：RealStrongConvex.strong_convex_gap_bound 在二次模型上给出
a·x² ≤ (2a/2)·x² = a·x²，即等式。 -/
theorem gd_upper_bound_tight (a : ℝ) (x : ℝ) :
    QuadF a x - QuadF a 0 ≤ (2 * a / 2) * (x - 0) ^ 2 :=
  strong_convex_gap_bound (quad_model_smooth a) (by ring : 2 * a * 0 = 0) x

/-- 上界与精确率的对比：取 η = 1/(2a)（即 Lip 常数的倒数），GD 一步到达极小点，
与 `gd_sharpness` 的 (1 − 2ηa)ⁿ = 0ⁿ 一致。 -/
theorem gd_one_step_sharp (a : ℝ) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) (x0 : ℝ) :
    QuadIter a (1 / (2 * a)) n x0 = 0 := by
  rw [QuadIter_exact]
  have hrate : QuadRate a (1 / (2 * a)) = 0 := by
    simp only [QuadRate]
    field_simp [show (2 * a) ≠ 0 from mul_ne_zero (by norm_num) ha]
  rw [hrate, zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_mul]

/-! ## 四点五、任务命名别名 -/

/-- 别名：**二次函数上 GD 的精确等式** e_n = (1 − 2ηa)ⁿ·e_0（0 ≤ 1 − 2ηa）。 -/
theorem gd_quadratic_exact (a η : ℝ) (h0 : 0 ≤ QuadRate a η) :
    ∀ (n : ℕ) (x0 : ℝ), ‖QuadIter a η n x0‖ = (QuadRate a η) ^ n * ‖x0‖ :=
  gd_sharpness a η h0

/-- 别名：**率是锐的**——上界 (1 − 2ηa)ⁿ 在 x_0 = 1 上取等。 -/
theorem gd_rate_is_sharp (a η : ℝ) (h0 : 0 ≤ QuadRate a η) (n : ℕ) :
    ‖QuadIter a η n 1‖ = (QuadRate a η) ^ n * ‖(1 : ℝ)‖ :=
  gd_sharpness a η h0 n 1

/-- 别名：**任何一致几何界不能优于 (1 − 2ηa)**。 -/
theorem no_better_than_geometric (a η c : ℝ) (h0 : 0 ≤ QuadRate a η)
    (h : ∀ (x0 : ℝ) (n : ℕ),
      ‖QuadIter a η n x0‖ ≤ c ^ n * ‖QuadIter a η 0 x0‖) :
    QuadRate a η ≤ c :=
  no_faster_than_geometric a η c h0 h

/-! ## 五、一阶信息的下界型说明（单步不可混淆）

⚠ **本节是 P3-1 的落点**：文件头 `:35-40` 的"一维无非平凡下界"是**散文**（已标注），
但其中**可证的那一半**（"一次查询读出曲率"）在此**以定理给出**，
并配一条**唯一性**定理，使"读出曲率"不是修辞而是可核对的断言。

⭐ **本节新增 `QuadGrad`** —— 文件头原句的 `g = a·x_0` 中 `g`/`x_0` 是**未绑定符号**；
命名梯度是**陈述该句的最低要求**（等价形式另见 R5 探针 `_r5_p31_ratelower.lean`）。 -/

/-- **二次模型的梯度**（命名文件头散文里的 `g`）：`∇(QuadF a)(x) = 2a·x`。 -/
def QuadGrad (a x : ℝ) : ℝ := 2 * a * x

/-- 定义性桥：`QuadGrad` **就是** `2a·x`（与文件头 `:12` 的散文一致）。 -/
theorem QuadGrad_eq (a x : ℝ) : QuadGrad a x = 2 * a * x := rfl

/-- ⭐ **一次查询读出曲率**（把文件头散文"x_0 ≠ 0 时直接解出 a"**升级为定理**）：
`x₀ ≠ 0` 时，单次梯度值 `g = QuadGrad a x₀` **唯一且显式地**确定 `a = g/(2x₀)`。

⚠ **这是散文里可证的那一半**；另一半（"无非平凡下界"）需要预言机模型，
见文件头标注与本节末的说明。 -/
theorem curvature_recovered_in_one_query (a x₀ : ℝ) (hx₀ : x₀ ≠ 0) :
    a = QuadGrad a x₀ / (2 * x₀) := by
  rw [QuadGrad_eq]
  field_simp
  ring

/-- ⭐ **由一次查询唯一确定**（"读出曲率"的严格含义）：两个二次函数在同一点
`x₀ ≠ 0` 给出同一梯度值 ⟹ **曲率相同**。即查询映射 `a ↦ QuadGrad a x₀` **单射**。 -/
theorem curvature_determined_by_one_query {a a' x₀ : ℝ} (hx₀ : x₀ ≠ 0)
    (h : QuadGrad a x₀ = QuadGrad a' x₀) : a = a' := by
  rw [QuadGrad_eq, QuadGrad_eq] at h
  have h' : 2 * x₀ * a = 2 * x₀ * a' := by linarith
  exact mul_left_cancel₀ (by positivity : (2 : ℝ) * x₀ ≠ 0) h'

/-- ⚠ **假设 `x₀ ≠ 0` 承重**（PROCESS.md §2.3 判据 1：去掉它结论必须变假）：
在 `x₀ = 0` 处**所有**二次函数都报梯度 `0`，故曲率**完全不可恢复**。 -/
theorem zero_query_collapses_curvatures (a a' : ℝ) : QuadGrad a 0 = QuadGrad a' 0 := by
  simp [QuadGrad]

/-- **单步一阶信息不可混淆**：若 (f x, 0) 是 x 处的一个一阶信息（0 是次梯度），
则 x 已是全局极小点。这说明「一次询问就把候选极小点钉住」。

⭐ **本条是散文"一维不存在非平凡下界"的【可证替代物】**：它证明的不是"下界不存在"
（那是散文），而是**下界无从谈起的原因** —— 一次询问后**没有任何信息不对称**可供
下界利用。⚠ **一般下界需高维多步构造**（Nesterov），本文件不做，已在文件头标注。 -/
theorem first_order_single_step_no_confusion {f : ℝ → ℝ} {x : ℝ}
    (hzero : Subgradient f x 0) : ∀ y : ℝ, f x ≤ f y := by
  intro y
  have h := hzero y
  linarith

/-! ## 注：闭环语义
  精确迭代（QuadIter_exact）→ 锐性（gd_sharpness）→ 界不可改进
  （no_faster_than_geometric）→ 步长条件必要的反例（振荡/发散）→
  与 RealStrongConvex 上界的取等对比（gd_upper_bound_tight）→
  **一次查询读出曲率（curvature_recovered_in_one_query /
  curvature_determined_by_one_query）**。
  ⚠ 一般一阶下界（Nesterov）在一维退化：本文件以锐性 + 具体反例 + **上述两条
  曲率定理**替代，并把"一维不存在非平凡下界"**显式标注为散文**（P3-1）。 -/

end Lattice
