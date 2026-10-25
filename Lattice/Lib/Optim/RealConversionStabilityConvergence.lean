import Mathlib
import Lattice.Lib.Compiler.RealNonlinearCompile
import Lattice.Lib.Editing.RealNonlinearExtract
import Lattice.Lib.Optim.RealSecondOrderNoModulus
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Editing.RealRoundtripBound
import Lattice.Lib.LinearAlgebra.RealSpectralRadius
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.Architectures.RealNormStability
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealDataProcessing
/-!
# Convergence of the compilation loss under gradient descent

Split out of `RealConversionStability.lean` (doc/36). Declaration bodies are
unchanged; only the containing module differs.
-/

noncomputable section

open Set Filter Metric
open scoped Topology BigOperators

namespace Lattice

/-! ============================================================
## 第一节 可微性 / 光滑性回喂
### 正定 ⟹ 显式模数 ⟹ 压缩 ⟹ 唯一不动点 + 几何收敛率
============================================================ -/

/-! ### 1.0 编译损失与梯度下降映射

把「编译损失」按 `doc/03` 的 `lv_total_loss` 语义读成一个实数函数；本节的结构性
条件只有「逐约束平方损失非负」（`lossComp_nonneg`，即 `sq_nonneg` 给出的东西）。
-/

/-- **逐约束编译损失**：符号侧约束 `c i` 在输入 `x` 处的平方损失
（`doc/03` 的 `lv_loss`，即「输出零化 ⟺ 约束满足」的损失形式）。 -/
def lossComp (c : Fin k → NlConstraint) (i : Fin k) (x : ℝ) : ℝ :=
  (nlCompile (c i) x).1 ^ 2 + (nlCompile (c i) x).2 ^ 2

/-- 逐约束编译损失非负。 -/
theorem lossComp_nonneg (c : Fin k → NlConstraint) (i : Fin k) (x : ℝ) :
    0 ≤ lossComp c i x := by
  unfold lossComp
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **梯度下降映射** `G_η(x) = x − η·∇L(x)`：转换层「不动点迭代」的载体。
（`∇L` 以显式参数 `grad` 给出——本文件不构造梯度，只做结构结论。） -/
def gdStep (η : ℝ) (grad : ℝ → ℝ) (x : ℝ) : ℝ := x - η * grad x

/-- **GD 映射的不动点刻画**：`η ≠ 0` 时 `x` 是不动点 ⟺ `grad x = 0`。
这就是「转换层的不动点 = 损失函数驻点」的精确含义。 -/
theorem gdStep_fixpoint_iff (η : ℝ) (hη : η ≠ 0) (grad : ℝ → ℝ) (x : ℝ) :
    gdStep η grad x = x ↔ grad x = 0 := by
  unfold gdStep
  constructor
  · intro h
    have h3 : η * grad x = 0 := by linarith
    exact (mul_eq_zero.mp h3).resolve_left hη
  · intro h
    rw [h]
    ring

/-! ### 1.1 压缩 ⟹ 唯一不动点 + 几何收敛率 -/

/-- **定理 A1（唯一不动点）**：若 `G` 是压缩映射（`|G x − G y| ≤ c·|x − y|`，
`0 ≤ c < 1`），则 `G` 在 ℝ 上**至多有一个**不动点。

证明：两个不动点 `x, y` 满足 `|x − y| = |G x − G y| ≤ c·|x − y|`，
由 `c < 1` 得 `|x − y| ≤ 0`，故 `x = y`。

**诚实标注**：这是「至多一个」；**存在性未证**（见文件头诚实边界）。 -/
theorem contraction_fixpoint_unique {G : ℝ → ℝ} {c : ℝ} (_hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcon : ∀ x y : ℝ, |G x - G y| ≤ c * |x - y|) :
    ∀ x y : ℝ, G x = x → G y = y → x = y := by
  intro x y hx hy
  have h1 : |x - y| ≤ c * |x - y| := by
    have h2 : |G x - G y| = |x - y| := by rw [hx, hy]
    -- `hcon` 是函数，不能 `rw at`；改为先取实例化再代入等式
    have h3 := hcon x y
    rw [h2] at h3
    exact h3
  have h3 : (0 : ℝ) ≤ |x - y| := abs_nonneg _
  have h4 : |x - y| ≤ 0 := by nlinarith only [h1, h3, hc1]
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h4 h3))

/-- **定理 A2（ε-终止）**：收缩 + 非负 ⟹ 转换层迭代对任意 `ε > 0` 有限步终止。
（`RealConvergence.contraction_converges` 的转换层入口。） -/
theorem contraction_eps_terminates {e : ℕ → ℝ} (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hstep : ∀ n : ℕ, e (n + 1) ≤ c * e n) (hnonneg : ∀ n : ℕ, 0 ≤ e n) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, e n < ε :=
  -- `contraction_converges` 的 `{e : ℕ → ℝ}` 是**隐式**首参，必须具名传入，
  -- 否则 `c` 会被当成 `e` 的实参（报 `c has type ℝ but expected ℕ → ℝ`）
  contraction_converges (e := e) c hc0 hc1 hstep hnonneg

/-- **定理 A3（复合收缩，多层收敛率的乘性法则）**：`G₁` 以 `c₁` 压缩、
`G₂` 以 `c₂` 压缩 ⟹ 复合 `G₁ ∘ G₂` 以 `c₁·c₂` 压缩。

**新结论**：主线此前只有**单层**的初等 Lipschitz 界（`RealRoundtripBound` 的
`extract_lipschitz_one`），没有任何跨越「复合层」的定量结论。
本定理给出乘性法则：`n` 层各以 `c` 压缩的转换网络收敛率是 `c^n`。 -/
theorem composition_contraction {G₁ G₂ : ℝ → ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁)
    (h₁ : ∀ x y : ℝ, |G₁ x - G₁ y| ≤ c₁ * |x - y|)
    (h₂ : ∀ x y : ℝ, |G₂ x - G₂ y| ≤ c₂ * |x - y|) :
    ∀ x y : ℝ, |(G₁ ∘ G₂) x - (G₁ ∘ G₂) y| ≤ (c₁ * c₂) * |x - y| := by
  intro x y
  have ha := h₂ x y
  have hb := h₁ (G₂ x) (G₂ y)
  calc |(G₁ ∘ G₂) x - (G₁ ∘ G₂) y| = |G₁ (G₂ x) - G₁ (G₂ y)| := rfl
    _ ≤ c₁ * |G₂ x - G₂ y| := hb
    _ ≤ c₁ * (c₂ * |x - y|) := mul_le_mul_of_nonneg_left ha hc₁
    _ = (c₁ * c₂) * |x - y| := by ring

/-- **定理 A4（给定不动点时的几何误差衰减）**：`G` 以 `c` 压缩、`x*` 是 `G` 的
不动点，则
    `|G^n(x₀) − x*| ≤ c^n · |x₀ − x*|`。

**新结论**：这是 `RealNonlinearCompile` 此前**完全没有**的**定量速率**陈述——
收敛率以闭式 `c^n` 给出，而不是"趋向于零"的定性说法。 -/
theorem gd_error_le_geometric {G : ℝ → ℝ} {c : ℝ} (hc0 : 0 ≤ c)
    (hcon : ∀ x y : ℝ, |G x - G y| ≤ c * |x - y|) (xstar x0 : ℝ) (hfix : G xstar = xstar) :
    ∀ n : ℕ, |(G^[n]) x0 - xstar| ≤ c ^ n * |x0 - xstar| := by
  have hstep : ∀ n : ℕ, |(G^[n + 1]) x0 - xstar| ≤ c * |(G^[n]) x0 - xstar| := by
    intro n
    -- 展开迭代器：`G^[n+1] x0 = G ((G^[n]) x0)`
    rw [Function.iterate_succ_apply']
    -- 目标：`|G ((G^[n]) x0) − xstar| ≤ c * |(G^[n]) x0 − xstar|`
    -- `hcon ((G^[n]) x0) xstar : |G ((G^[n]) x0) − G xstar| ≤ c * |(G^[n]) x0 − xstar|`
    -- ⟹ 只需把 **LHS 被减数位置**的 `xstar` 换成 `G xstar`（RHS 的 `xstar` 不能动）
    -- 注意 不能用 `rw [hfix']`：`rw` 会**同时命中 RHS** 里那个 `xstar`（我踩过这个坑）
    have hfix' : xstar = G xstar := hfix.symm
    nth_rewrite 1 [hfix']
    exact hcon ((G^[n]) x0) xstar
  have h := contraction_pow_bound c hc0 (e := fun n => |(G^[n]) x0 - xstar|) hstep
  simpa using h

/-! ### 1.2 从 `RealSecondOrderNoModulus` 的显式模数得到 GD 收缩

`RealSecondOrderNoModulus.exists_modulus_of_posDef` 把 `RealHessian` 的
「存在 `μ > 0`」**从假设升级成定理**（有限维紧性论证）。
本节把它接到转换层的压缩性上：

   点式正定 ⟹ 显式模数 μ ⟹ 沿方向的一致增长 μ|x−y| ≤ |g x − g y|
                            ⟹ 小步长下 x ↦ x − η·g x 是压缩的
                            ⟹ 唯一不动点（A1）+ 几何收敛率（A4）。
-/

/-- **定理 B1（单调 + Lipschitz 上界 ⟹ GD 压缩）**：设 `g` 满足
· **增长下界** `hmono : μ·|x − y| ≤ |g x − g y|`（由 `RealSecondOrderNoModulus` 的模数给出），
· **同号性** `hsign`（单调性），
· **Lipschitz 上界** `hlip : |g x − g y| ≤ L·|x − y|`，
且 `0 < η`、`η·μ ≤ 1`、`η·(L + μ) ≤ 2`，则 `x ↦ x − η·g x` 是压缩映射，系数 `c = 1 − η·μ`。

注意 **本次修复更正了一处为假的陈述（原稿——本文件此前的"主定理"）**：
原稿**没有** `hlip`（Lipschitz 上界），却断言同一结论。**该断言为假**，
且反例可在内核中验证（见下方 `gd_contraction_of_modulus_false`）：
取 `g x = 4x`、`μ = 1`、`η = 1/2`、`x = 1`、`y = 0`，则
· `hmono`：`|g 1 − g 0| = 4 ≥ μ·|1 − 0| = 1` 成立
· `hsign`：`x − y = 1 ≥ 0` 且 `g x − g y = 4 ≥ 0` 成立
· `hμ`、`hη`、`hημ = 1/2 ≤ 1` 成立
· 但 `|gdStep η g 1 − gdStep η g 0| = |−1 − 0| = 1`，而 `(1 − ημ)·|1 − 0| = 1/2`
⟹ `1 ≤ 1/2` **为假**。

**根因（诊断）**：`hmono` 只给 `|g x − g y|` 的**下界**，而结论需要**上界**来
控制 `η·(g x − g y)` 项。`RealNonlinearCompile` 缺失的那一跳**不是单调性一条**，
而是「单调性 **+ Lipschitz 上界**」两条；原稿补了前者、漏了后者。
（原稿 docstring 称"必须补上单调性"——**部分正确但不足**，本定理给出充分条件。）

**诚实标注**：`hlip` 是**必需**的显式假设，不是形式冗余——反例即其独立性证据。 -/
theorem gd_contraction_of_modulus {g : ℝ → ℝ} {μ η L : ℝ} (hμ : 0 < μ) (hη : 0 < η)
    (_hημ : η * μ ≤ 1) (hηLμ : η * (L + μ) ≤ 2)
    (hmono : ∀ x y : ℝ, μ * |x - y| ≤ |g x - g y|)
    (hsign : ∀ x y : ℝ, (0 ≤ x - y ∧ 0 ≤ g x - g y) ∨ (x - y ≤ 0 ∧ g x - g y ≤ 0))
    (hlip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|) :
    ∀ x y : ℝ, |gdStep η g x - gdStep η g y| ≤ (1 - η * μ) * |x - y| := by
  intro x y
  have hstep : gdStep η g x - gdStep η g y = (x - y) - η * (g x - g y) := by
    unfold gdStep; ring
  rw [hstep]
  -- 由同号性，`η(g x − g y)` 与 `x − y` **同号**；记 `d := x − y`、`Δ := g x − g y`。
  -- 情形一（`d ≥ 0`、`Δ ≥ 0`）：`ημd ≤ ηΔ`（增长下界），`ηΔ ≤ ηLd`（Lipschitz 上界）。
  --   若 `ηΔ ≤ d`：`|d − ηΔ| = d − ηΔ ≤ d − ημd = (1−ημ)d`。
  --   若 `ηΔ ≥ d`：`|d − ηΔ| = ηΔ − d`，需 `ηΔ ≤ (2−ημ)d`；由 `ηΔ ≤ ηLd` 与
  --   `η(L+μ) ≤ 2` 即 `ηL ≤ 2 − ημ` 得 `ηLd ≤ (2−ημ)d` 成立
  have hkey : ∀ d Δ : ℝ, 0 ≤ d → 0 ≤ Δ → μ * d ≤ Δ → Δ ≤ L * d →
      |d - η * Δ| ≤ (1 - η * μ) * d := by
    intro d Δ hd hΔ hlo hhi
    have h1 : η * (μ * d) ≤ η * Δ := mul_le_mul_of_nonneg_left hlo (le_of_lt hη)
    have h2 : η * Δ ≤ η * (L * d) := mul_le_mul_of_nonneg_left hhi (le_of_lt hη)
    -- `ηL ≤ 2 − ημ`（由 `η(L+μ) ≤ 2`）
    have hLb : η * L ≤ 2 - η * μ := by nlinarith only [hηLμ]
    have h2' : η * (L * d) ≤ (2 - η * μ) * d := by nlinarith only [hLb, hd]
    have h3 : η * Δ ≤ (2 - η * μ) * d := le_trans h2 h2'
    have hmm : 0 ≤ η * μ := mul_nonneg (le_of_lt hη) (le_of_lt hμ)
    have h4 : η * (μ * d) = (η * μ) * d := by ring
    rcases le_total (η * Δ) d with hcase | hcase
    · -- `ηΔ ≤ d`：绝对值取正号
      rw [abs_of_nonneg (by linarith)]
      nlinarith only [h1, h4, hmm, hd]
    · -- `ηΔ ≥ d`：绝对值取负号
      rw [abs_of_nonpos (by linarith)]
      nlinarith only [h3, hmm, hd]
  rcases hsign x y with ⟨hd, hΔ⟩ | ⟨hd, hΔ⟩
  · -- 情形一：`d ≥ 0` 且 `Δ ≥ 0`
    have hdx : |x - y| = x - y := abs_of_nonneg hd
    have hDx : |g x - g y| = g x - g y := abs_of_nonneg hΔ
    have hmon := hmono x y
    have hlp := hlip x y
    rw [hdx, hDx] at hmon hlp
    have hfin := hkey (x - y) (g x - g y) hd hΔ hmon hlp
    -- `hfin : |(x−y) − η(gx−gy)| ≤ (1−ημ)*(x−y)`；目标里 `|x−y|` 用 `hdx` 换掉
    rw [hdx]
    exact hfin
  · -- 情形二：`d ≤ 0` 且 `Δ ≤ 0`（取 `d' := -(x−y)`、`Δ' := -(g x − g y)` 归约到情形一）
    have hdx : |x - y| = -(x - y) := abs_of_nonpos hd
    have hDx : |g x - g y| = -(g x - g y) := abs_of_nonpos hΔ
    have hmon := hmono x y
    have hlp := hlip x y
    rw [hdx, hDx] at hmon hlp
    have hd' : 0 ≤ -(x - y) := neg_nonneg.mpr hd
    have hΔ' : 0 ≤ -(g x - g y) := neg_nonneg.mpr hΔ
    -- `(x−y) − η(gx−gy) = -(-(x−y) − η·(-(gx−gy)))`
    have hneg : (x - y) - η * (g x - g y) = -((-(x - y)) - η * (-(g x - g y))) := by ring
    have hfin := hkey (-(x - y)) (-(g x - g y)) hd' hΔ' hmon hlp
    rw [hneg, abs_neg, hdx]
    exact hfin

/-- **定理 B1′（原稿 B1 为假——机器验证反例）**：**存在** `g, μ, η, x, y` 使
原稿 `gd_contraction_of_modulus` 的**全部假设**成立（`0 < μ`、`0 < η`、`η·μ ≤ 1`、
增长下界 `hmono`、同号性 `hsign`），而**结论失败**。

取 `g x = 4x`、`μ = 1`、`η = 1/2`、`x = 1`、`y = 0`：
`|gdStep η g 1 − gdStep η g 0| = 1`，而 `(1 − η·μ)·|1 − 0| = 1/2`。

**这是本文件最重要的诚实产出之一**：它**精确指出**"点式正定模数 ⟹ GD 收缩"
这一步缺的桥**不只是单调性**（原稿 docstring 的判断），而是**单调性 + Lipschitz 上界**；
仅有增长下界时 `η·(g x − g y)` 无上界控制，压缩结论**为假**。
（对照：B1 现在带 `hlip`，才是真命题。） -/
theorem gd_contraction_of_modulus_false :
    ¬ (∀ (g : ℝ → ℝ) (μ η : ℝ), 0 < μ → 0 < η → η * μ ≤ 1 →
        (∀ x y : ℝ, μ * |x - y| ≤ |g x - g y|) →
        (∀ x y : ℝ, (0 ≤ x - y ∧ 0 ≤ g x - g y) ∨ (x - y ≤ 0 ∧ g x - g y ≤ 0)) →
        ∀ x y : ℝ, |gdStep η g x - gdStep η g y| ≤ (1 - η * μ) * |x - y|) := by
  intro h
  -- 全部假设用 `g x = 4x`、`μ = 1`、`η = 1/2` 实例化
  have hmono : ∀ x y : ℝ, (1 : ℝ) * |x - y| ≤ |4 * x - 4 * y| := by
    intro x y
    have : (4 : ℝ) * x - 4 * y = 4 * (x - y) := by ring
    rw [this, abs_mul]
    have : |(4 : ℝ)| = 4 := by norm_num
    rw [this]
    have hz : 0 ≤ |x - y| := abs_nonneg _
    linarith only [hz]
  have hsign : ∀ x y : ℝ, (0 ≤ x - y ∧ 0 ≤ 4 * x - 4 * y) ∨ (x - y ≤ 0 ∧ 4 * x - 4 * y ≤ 0) := by
    intro x y
    rcases le_total (x - y) 0 with hle | hle
    · right
      refine ⟨hle, ?_⟩
      nlinarith only [hle]
    · left
      refine ⟨hle, ?_⟩
      nlinarith only [hle]
  have hbad := h (fun x : ℝ => 4 * x) 1 (1/2) one_pos (by norm_num) (by norm_num) hmono hsign 1 0
  -- `gdStep (1/2) (4x) 1 = 1 − 2 = −1`；`gdStep (1/2) (4x) 0 = 0`
  have hL : gdStep (1/2) (fun x : ℝ => 4 * x) 1 = -1 := by unfold gdStep; norm_num
  have hR : gdStep (1/2) (fun x : ℝ => 4 * x) 0 = 0 := by unfold gdStep; norm_num
  rw [hL, hR, sub_zero, abs_neg, abs_one, sub_zero] at hbad
  norm_num at hbad

/-- **定理 B2（转换层的收敛率：模数 + Lipschitz 版）**：`G = gdStep η g` 以 `1 − η·μ` 压缩，
故其迭代以 `(1 − η·μ)^n` 几何衰减到任意不动点。 -/
theorem gd_convergence_rate {g : ℝ → ℝ} {μ η L : ℝ} (hμ : 0 < μ) (hη : 0 < η)
    (hημ : η * μ ≤ 1) (hηLμ : η * (L + μ) ≤ 2) (hmono : ∀ x y : ℝ, μ * |x - y| ≤ |g x - g y|)
    (hsign : ∀ x y : ℝ, (0 ≤ x - y ∧ 0 ≤ g x - g y) ∨ (x - y ≤ 0 ∧ g x - g y ≤ 0))
    (hlip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (xstar x0 : ℝ) (hfix : gdStep η g xstar = xstar) :
    ∀ n : ℕ, |((gdStep η g)^[n]) x0 - xstar| ≤ (1 - η * μ) ^ n * |x0 - xstar| :=
  gd_error_le_geometric (by linarith)
    (gd_contraction_of_modulus hμ hη hημ hηLμ hmono hsign hlip) xstar x0 hfix

/-- **定理 B3（模数 + Lipschitz 版收敛率 ⟹ 唯一不动点）**：把 A1 与 B1 串起来——
在「显式模数 + 单调性 + Lipschitz 上界 + 小步长」下，GD 映射的不动点**唯一**。
（`η·μ = 1` 时压缩系数为 `0`，仍是压缩，结论依然成立。） -/
theorem gd_fixpoint_unique_of_modulus {g : ℝ → ℝ} {μ η L : ℝ} (hμ : 0 < μ) (hη : 0 < η)
    (hημ : η * μ ≤ 1) (hηLμ : η * (L + μ) ≤ 2) (hmono : ∀ x y : ℝ, μ * |x - y| ≤ |g x - g y|)
    (hsign : ∀ x y : ℝ, (0 ≤ x - y ∧ 0 ≤ g x - g y) ∨ (x - y ≤ 0 ∧ g x - g y ≤ 0))
    (hlip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|) :
    ∀ x y : ℝ, gdStep η g x = x → gdStep η g y = y → x = y :=
  -- `c = 1 - η·μ`：`0 ≤ c` 由 `hημ`，`c < 1` 由 `0 < η·μ`
  contraction_fixpoint_unique (by linarith only [hημ])
    (by nlinarith only [hμ, hη])
    (gd_contraction_of_modulus hμ hη hημ hηLμ hmono hsign hlip)

/-- **定理 B4（同号性假设不可去——机器验证反例）**：仅有 `|g x − g y| ≥ μ|x − y|`
（`hmono`）而**无**同号性时，GD 映射**不是**压缩的。

取 `μ = 1`、`g x = −x`（此时 `|g x − g y| = |x − y|` 满足 `hmono`，
但 `x − y` 与 `g x − g y = −(x − y)` **反号**）、`η = 1/2`、`x = 1`、`y = 0`：
`gdStep η g x − gdStep η g y = 1.5`，而 `(1 − ημ)|x − y| = 0.5`，
**不等式 `1.5 ≤ 0.5` 为假**。

**诚实标注（"此路不通"的精确报告）**：这条反例说明
「点式正定模数 μ ⟹ GD 压缩」这一步**缺的桥是单调性（同号性）**——
仅有二阶模数**不足以**推出梯度下降映射的收缩性。B1 的 `hsign` 因此是**必需**的，
不是形式冗余。 -/
theorem gd_contraction_needs_monotone :
    ¬ (∀ (g : ℝ → ℝ) (μ η : ℝ), 0 < μ → 0 < η → η * μ ≤ 1 →
        (∀ x y : ℝ, μ * |x - y| ≤ |g x - g y|) →
        ∀ x y : ℝ, |gdStep η g x - gdStep η g y| ≤ (1 - η * μ) * |x - y|) := by
  intro h
  have hmono : ∀ x y : ℝ, (1 : ℝ) * |x - y| ≤ |(-x) - (-y)| := by
    intro x y
    -- 目标 `1 * |x - y| ≤ |(-x) - (-y)|`：先把 `(-x) - (-y)` 化成 `y - x`，
    -- 再用 `abs_sub_comm` 统一，最后 `one_mul` + `le_refl`。
    rw [show (-x) - (-y) = y - x by ring, abs_sub_comm, one_mul]
  have hbad := h (fun x : ℝ => -x) 1 (1/2) one_pos (by norm_num) (by norm_num) hmono 1 0
  -- gdStep (1/2) (fun x => -x) 1 = 3/2，gdStep (1/2) (fun x => -x) 0 = 0
  have hL : gdStep (1/2) (fun x : ℝ => -x) 1 = 3/2 := by unfold gdStep; norm_num
  have hR : gdStep (1/2) (fun x : ℝ => -x) 0 = 0 := by unfold gdStep; norm_num
  rw [hL, hR, sub_zero, abs_of_nonneg (by norm_num), sub_zero, abs_one] at hbad
  norm_num at hbad

/-! ### 1.3 与 `RealNonlinearExtract` 的 FCA 侧对齐

**诚实标注（避免假命题）**：把 `closureOperator` 写成"不动点唯一"是**假命题**——
`RealNonlinearExtract.extract_idempotent` 说明每个 `closureOperator R Ol` 都是不动点。
因此本节的"唯一不动点"结论**只**适用于 `gdStep` 那一支；下面把 FCA 侧的
**正确**结论收拢为可复用的"闭包代数"结构，并给出**精确的不动点刻画**。
-/

/-- **FCA 提取算子的闭包代数**：`extent R (intent R ·)` 是幂等 + 单调 + 扩张的算子。
打包成一个结构，便于下游以「闭包算子」整体使用。 -/
structure IsClosureOperator {α : Type*} (T : Set α → Set α) : Prop where
  /-- 幂等 -/
  idem : ∀ s, T (T s) = T s
  /-- 单调 -/
  mono : ∀ s t, s ⊆ t → T s ⊆ T t
  /-- 扩张 -/
  extensive : ∀ s, s ⊆ T s

/-- `RealNonlinearExtract` 的提取算子是**闭包算子**（三条性质同时成立）。 -/
theorem closureOperator_isClosureOperator {O A : Type*} (R : O → A → Prop) :
    IsClosureOperator (closureOperator R) where
  idem := extract_idempotent R
  mono := fun _ _ h => closureOperator_monotone R h
  extensive := closureOperator_extensive R

/-- **定理 C1（闭包算子的不动点 ⟺ 像集）**：`T` 是闭包算子时，
`s` 是不动点 ⟺ `s` 属于 `T` 的像。

**新结论**：把 `RealNonlinearExtract.extract_preserves_fixpoint`（不动点方向）
与"像都在不动点集里"（本定理右到左）**拼成了 iff**——
此前只有单向蕴含。 -/
theorem closure_fixpoint_iff_mem_range {α : Type*} {T : Set α → Set α}
    (hT : IsClosureOperator T) (s : Set α) : T s = s ↔ ∃ t, T t = s := by
  constructor
  · intro h
    -- 取 `t := s`，此时 `T t = s` 恰为 `h` 本身
    exact ⟨s, h⟩
  · rintro ⟨t, rfl⟩
    exact hT.idem t

/-- **定理 C2（闭包算子的极小不动点上界）**：闭包算子的不动点集对任意交封闭的
"弱形式"——若 `s` 是 `T` 的不动点且 `s ⊆ t`，则 `s ⊆ T t`。

证明：`s ⊆ T s`（扩张）且 `T s = s`，再由单调性 `T s ⊆ T t`。

**新结论**：这条把「不动点」与「任意超集」连起来，是 FCA 里
「闭集 = `↑↓` 像」这一族推理的可复用接口。 -/
theorem closure_fixpoint_subset_image {α : Type*} {T : Set α → Set α}
    (hT : IsClosureOperator T) {s t : Set α} (hfix : T s = s) (hsub : s ⊆ t) :
    s ⊆ T t := by
  -- `⊆` 是 `Set.Subset`（def），不能整体 `rw`；改在成员层做
  intro x hx
  rw [← hfix] at hx
  exact hT.mono s t hsub hx

/-- **定理 C3（提取算子的不动点不唯一——显式反例族）**：在 `Fin 2` 上取**恒等关系**
`R o a := o = a`，则 `∅` 与 `{0}` 都是提取算子的不动点且二者不同。

注意 **本次修复更正了一处为假的陈述（原稿）**：原稿用**常真关系**
`R := fun _ _ => True`，并断言 `∅` 与 `univ` 都是不动点。**该断言为假**：
常真关系下 `intent R S = univ`（对**任意** `S` 都成立，因为蕴含前件恒可满足），
故 `closureOperator R S = extent R univ = univ`——即**只有 `univ` 一个不动点**，
`∅` 根本不是不动点。原稿实际是 `RealNonlinearExtract.extract_idempotent`
（给出 `closureOperator R (closureOperator R ∅) = closureOperator R ∅`）的**误用**：
幂等说的是「`T` 作用两次等于一次」，**不是**「`∅` 是不动点」。
更正后的 `R o a := o = a` 使全部 4 个子集都是不动点，`∅ ≠ {0}` 即所需反例。

**诚实标注**：这条反例的作用是**划清本文件"唯一不动点"结论的适用边界**——
它只对 `gdStep`（及任何严格压缩算子）成立，对 `closureOperator` 不成立。
（把 `closureOperator` 写成"不动点唯一"会是**假命题**。） -/
theorem extract_fixpoints_many :
    ∃ s t : Set (Fin 2), s ≠ t ∧
      closureOperator (fun o a : Fin 2 => o = a) s = s ∧
      closureOperator (fun o a : Fin 2 => o = a) t = t := by
  refine ⟨∅, {0}, ?_, ?_, ?_⟩
  · -- `∅ ≠ {0}`（由 `0 ∈ {0}` 但 `0 ∉ ∅`）
    intro h
    have hmem : (0 : Fin 2) ∈ ({0} : Set (Fin 2)) := rfl
    rw [← h] at hmem
    exact hmem
  · -- `closureOperator R ∅ = ∅`：`intent R ∅ = univ`，
    -- 而 `extent R univ = {o | ∀ a, o = a} = ∅`（由 `0 ≠ 1` 在 `Fin 2` 中）
    unfold closureOperator extent intent
    ext o
    constructor
    · intro h
      -- `h : ∀ a, a ∈ ∅ → (fun o a => o = a) o a`；取 `a := 0`、`a := 1` 得 `0 = 1`，矛盾
      have h0 : o = 0 := h 0 (by simp)
      have h1 : o = 1 := h 1 (by simp)
      exact absurd (h0.symm.trans h1) (by decide)
    · intro h
      exact absurd h not_false
  · -- `closureOperator R {0} = {0}`：`intent R {0} = {a | 0 = a}`，
    -- 而 `extent R {a | 0 = a} = {o | o = 0} = {0}`
    unfold closureOperator extent intent
    ext o
    constructor
    · intro h
      -- `h 0 (by simp)`：把 `0 ∈ {0}` 化简后即 `o = 0`
      exact h 0 (by simp)
    · intro h a ha
      -- `ha : a ∈ {0}` 化简为 `a = 0`；`h : o = 0`；目标 `o = a`
      have ha' : a = 0 := by simpa using ha
      rw [ha']
      exact h

/-! ### 1.4 闭式实例：`piecewiseCompile` 的 Lipschitz 常数与区间二分

`RealNonlinearCompile.piecewiseCompile` 是分段仿射函数。本节给出两个**定量**结论：

  · **区间外 Lipschitz**：远离断点的同一分支内，Lipschitz 常数为该分支斜率的模；
  · **§1.4.2 的精确刻画**：`RealNonlinearCompile.piecewise_compile` 的"零化判据"
    与"两边极限归零"**不等价**——**断点处的跳跃被零化判据掩盖**，
    这是一个此前未被指出的**可靠性缺口**（给出机器验证反例）。
-/

/-- **定理 D1（单一分支上的 Lipschitz 界）**：若 `x, y` 同在左分支（`x ≤ c`、`y ≤ c`），
则 `|f(x) − f(y)| ≤ |fa|·|x − y|`。 -/
theorem piecewiseCompile_lipschitz_left (p : PiecewiseConstraint) {x y : ℝ}
    (hx : x ≤ p.c) (hy : y ≤ p.c) :
    |piecewiseCompile p x - piecewiseCompile p y| ≤ |p.fa| * |x - y| := by
  unfold piecewiseCompile
  rw [if_pos hx, if_pos hy]
  have : p.fa * x + p.fb - (p.fa * y + p.fb) = p.fa * (x - y) := by ring
  rw [this, abs_mul]

/-- **定理 D2（右分支上的 Lipschitz 界）**：`c < x`、`c < y` 时同款结论（斜率 `ga`）。 -/
theorem piecewiseCompile_lipschitz_right (p : PiecewiseConstraint) {x y : ℝ}
    (hx : p.c < x) (hy : p.c < y) :
    |piecewiseCompile p x - piecewiseCompile p y| ≤ |p.ga| * |x - y| := by
  unfold piecewiseCompile
  rw [if_neg (not_le.mpr hx), if_neg (not_le.mpr hy)]
  have : p.ga * x + p.gb - (p.ga * y + p.gb) = p.ga * (x - y) := by ring
  rw [this, abs_mul]

/-- **定理 D3（断点处的跳跃量精确闭式）**：分段编译器在断点 `c` 处的取值与
右极限之差恰为 `(ga − fa)·c + (gb − fb)`。

**新结论**：这给出「分段编译在断点处的**不连续幅度**」的精确表达式——
主线此前的 `piecewise_compile` 只处理"逐段成立"，从未量化断点行为。 -/
theorem piecewiseCompile_jump (p : PiecewiseConstraint) :
    piecewiseCompile p p.c - (p.ga * p.c + p.gb) = (p.fa - p.ga) * p.c + (p.fb - p.gb) := by
  unfold piecewiseCompile
  rw [if_pos le_rfl]
  ring

/-- **定理 D4（断点不连续性的可靠性缺口，机器验证反例）**：**存在**分段约束 `p`
与输入 `t`，使得

  1. `piecewiseCompile p` 在 `t` 处的**零化判据成立**（`= 0`），
  2. 但**右分支仿射值在 `t` 处非零**。

取 `p = ⟨0, 1, 0, 1, 1⟩`、`t = 0`：左段 `fa·x+fb = x` 在 `0` 处为 `0`
（判据报"满足"），而右段 `ga·x+gb = x+1` 在 `0` 处为 `1 ≠ 0`。

**诚实标注**：这不是"定理 D1–D3 有问题"，而是**指出 `piecewise_compile` 的
零化判据在断点处把"单侧满足"当成了"约束满足"**——转换层的规约需要
额外的**断点连续性假设**（`ga·c + gb = fa·c + fb`）才能恢复可靠性。
缺的桥就是这条假设；本文件给出反例而不是隐瞒。 -/
theorem piecewise_compile_breakpoint_unreliable :
    ∃ (p : PiecewiseConstraint) (t : ℝ),
      piecewiseCompile p t = 0 ∧ p.ga * t + p.gb ≠ 0 := by
  refine ⟨{ c := 0, fa := 1, fb := 0, ga := 1, gb := 1 }, 0, ?_, ?_⟩
  · unfold piecewiseCompile
    norm_num
  · norm_num

/-! ### 1.5 `RealNonlinearExtract` 的正区域可逆 + 本节的 Lipschitz 常数

`RealNonlinearExtract.relu_extract_on_positive` 给出 ReLU 在正区域的可逆性。
与 §1.4 的 Lipschitz 数据合起来，可以给出**提取（激活反演）的稳定性**：
`reluInv` 在 `[0, R]` 上以常数 `1` Lipschitz。 -/

/-- **定理 E1（激活反演的 Lipschitz 常数恰为 1）**：`reluInv`（恒等映射）
在 `x, y ≥ 0` 处满足 `|reluInv x − reluInv y| ≤ 1·|x − y|`。
即激活反演**不放大误差**——这是提取侧最干净的稳定性结论。 -/
theorem reluInv_lipschitz (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    |reluInv x - reluInv y| ≤ 1 * |x - y| := by
  unfold reluInv
  rw [one_mul]


end Lattice
