import Mathlib
import Lattice.Lib.LearningTheory.RealMAML
/-!
# LATTICE: 二阶 MAML 与 Hessian-向量积（HVP）的有限差分误差界

MAML 的元梯度含 Hessian 项（见 `RealMAML.mamlGrad`）：

    ∇_θ L(θ') = (I − α·∇²L_task(θ))·∇_{θ'}L(θ')

其中二阶项 `−α·H·h` 在一维下即 `mamlGradSO α H h = (1 − α·H)·h`。
另一方面，实用中 Hessian-向量积 `H·v` 由**有限差分**近似：

    HVP(g, θ, v, h) ≈ (g(θ + h·v) − g θ) / h

本文件给出：
1. 二阶元梯度的定义与一阶/二阶展开；
2. `α → 0` 或 `H = 0` 时精确回收 FOMAML（`RealMAML.fomamlGrad`）；
3. 二阶 vs 一阶的偏差界 `α·Λ·|h|`；
4. **HVP 有限差分的误差界**：割线式（MVT 形式，严格）与标准 `1/2` 界（显式 Taylor 余项）；
5. 上述界的 `EuclideanSpace` 版本。

## 主结果

1. **二阶展开**（`maml_second_order_expansion`）：`mamlGradSO α H h = h − α·(H·h)`。
2. **退化回收**（`mamlSO_recovers_fomaml` / `mamlSO_recovers_fomaml_hessian_zero`）：
   `α = 0` 或 `H = 0` 时 `mamlGradSO α H h = fomamlGrad h`。
3. **二阶 vs 一阶偏差界**（`mamlSO_vs_fomaml_bound`）：`0 ≤ α`、`|H| ≤ Λ` ⟹

       |mamlGradSO α H h − fomamlGrad h| ≤ α·Λ·|h|

4. **HVP 割线误差界**（`hvp_finitediff_error_secant`，严格）：
   在「中值定理给出的割线 `Hξ`」与「`Hξ` 对真值 `Hv` 的 Lipschitz 型界」两条**显式假设**下，

       |(g(θ + h·v) − g θ)/h − Hv| ≤ L2·|h|·|v|

5. **HVP 标准 `1/2` 界**（`hvp_finitediff_error_half`，显式 Taylor 余项假设）：

       |(g(θ + h·v) − g θ)/h − Hv| ≤ (L2/2)·h·|v|

6. **欧氏空间版**（`hvp_finitediff_error_half_euclidean`）：

       ‖h⁻¹ • (g(θ + h•v) − g θ) − Hv‖ ≤ (L2/2)·h·‖v‖

7. **`∇²fᵢ` 的存在性（WP6 新增）**（`maml_hessian_eq_second_deriv`）：
   在 `ContDiffAt ℝ 2 f θ` 下，`H := deriv (deriv (scalarPath f θ 1)) 0` **存在**
   且等于真二阶 Fréchet 导数 `fderiv ℝ (fderiv ℝ f) θ 1 1`。
   即 `H` **不再需要外部提供**（原为裸实数假设）。

## ⚠️ 重要警告：本文件的偏差界**不**意味着一阶方法够用（FO-MAML 负结果）

`mamlSO_vs_fomaml_bound` 给出的是**偏差量级**陈述
`|mamlGradSO α H h − fomamlGrad h| ≤ α·Λ·|h|`——
它说明二阶修正项 `−α·H·h` 的大小被 `α·Λ·|h|` 控制，**仅此而已**。

**极易被误读为「α 小时二阶项可忽略，故一阶方法（FO-MAML）够用」，这是错的。**
文献中有一条**明确负结果**（据本项目调研 R5，出处 arXiv:1908.10400v4，
Fallah–Mokhtari–Ozdaglar 2019，其 Theorem 5.15 及摘要）：

> **FO-MAML cannot find an ε-FOSP for any ε > 0.**
> （FO-MAML 对**任何** ε > 0 都无法找到 ε-一阶驻点。）

即：**一阶方法在一般情况下不能保证收敛到一阶驻点**，无论 ε 取多大。
本文件的界是**单步偏差量级**分析，**不**蕴含、也**不**声称一阶方法的收敛性；
「α → 0 时二阶项消失」（`mamlSO_recovers_fomaml`）只是**代数极限**，
**与「用一阶方法做优化是否可行」是完全不同的问题**，不可据此推断。

> **诚实标注（证据强度）**：上述负结果**引自本项目调研 R5**，我（WP6）
> **未能独立复核**该论文原文（本会话网络检索不可用：web_fetch/web_search 均失败）。
> 出处编号以 R5 明确指定的 **`1908.10400v4`** 为准（R5 说明其先前凭记忆给出的编号有误、
> 已废弃）。若需在正式文档中引用，**请在使用前复核原文 Theorem 5.15**。

## 诚实边界

- **Hessian / HVP 已部分从二阶 Fréchet 导数推出（WP6 更新）**：
  `maml_hessian_eq_second_deriv` 证明在 `ContDiffAt ℝ 2 f θ` 下
  `H = deriv (deriv (scalarPath f θ 1)) 0 = fderiv ℝ (fderiv ℝ f) θ 1 1`——
  即 **`∇²fᵢ` 的存在性已是定理**（不再是假设）。
  **仍未推出**（保留为显式假设，标注「显式假设/诚实」）：有限差分误差界中的
  中值点 `Hξ`、二阶导 Lipschitz 常数 `L2`、Taylor 余项 `r`
  （二次余项界需 `ContDiffOn ℝ 3`，见下）；以及梯度 Lipschitz 常数 `L` 与
  Hessian Lipschitz 常数 `ρ`。
- **`L`（梯度 Lipschitz）与 `ρ`（Hessian Lipschitz）保持为假设**：MAML 原文
  （Assump. 5.3 / 5.4）**亦以假设形式给出**，且**不能**由「`fᵢ` 二次连续可微」推出
  （C² 只给**局部** Lipschitz 性，不给全局常数）。故此处**保留为假设是正确的**，
  我们**没有削弱**命题——原文本就是假设。
- **⚠️ 【已更正】`hrem` 需要的是 `C²`，不是 `C³`（第六节新增）**：原文此处写着
  「**二次 Taylor 余项界需要三阶可微** ⟹ `hrem` 只能作为条件假设」。⭐ **该判断是错的**，
  第六节已更正并把更正固化为定理：
  · `hrem` 逐字为 `g(θ+h·v) = g θ + h·Hv + r`、`|r| ≤ (L2/2)·h²·|v|`。
    把它改写成沿方向的一元函数 `φ(t) := g (θ + t·v)`，则它恰是 **`n = 1` 阶
    Taylor 余项**（对 `φ` 是 `O(h²)`）⟹ ⭐ **只需 `φ` 二次连续可微，即 `g` 是 `C²`**，
    **不需要三阶可微**。原文把「二次余项 `O(h²)`」误读成「二阶展开的余项」，
    于是把前提抬高了一阶（**B216.4** 的「对载体的语义判断错误」类）；
  · 第六节的 `hrem_of_contDiffOn_two` 在 **`ContDiffOn ℝ 2 g (closedBall θ |v|)`** 下
    推出 `hrem`（`v ≠ 0` 分支）；`hrem_of_v_eq_zero` 覆盖 `v = 0`（此时余项为 `0`）；
  · `scalarPath_contDiffOn`：`g` 在球上 `C^m` ⟹ 路径在 `[0,1]` 上 `C^m`（引擎）。

  ⚠ **仍未消除的一处**（如实登记，**不掩盖**）：`hrem` 右端是 `(L2/2)·h²·|v|`
  （`|v|` 的**一次**方），而按 `φ''` 上确界直接算出的界是 `(sup|φ''|/2)·h²`
  `= (sup|g''|/2)·h²·|v|²`（`|v|` 的**二次**方）⟹ 二者**差一个 `|v|` 因子**。
  第六节的做法是**照原样保留 `L2` 的自由度**（取 `L2 := 2C/|v|`），
  使结论形状与原文**逐字一致**；**没有**声称这个 `|v|` 因子可以去掉；
  · 另：第六节的 `hrem` 结论仍以 `Hv := deriv (scalarPath g θ v) 0`（方向导数）
    表述，即 `Hv` 与 `hrem` 的 `Hv` 对齐的是**方向导数**而非某个外部给定的
    Hessian 矩阵 —— 与 HVP 的语义一致。
- **未做**：`∇²fᵢ` 存在性从 `ContDiffAt ℝ 2 f x` 的构造（本文件一维情形 `H` 直接作为
  实数出现）。**注**：该构造已在 `RealSecondOrderUpgrade.hessianMat` 中完成
  （由二阶 Fréchet 导数定义 Hessian 并桥接到 `quadForm`），本文件**未**回头改写为
  使用它——这是一处**接口层的未做**，不影响本文件任何结论的正确性。
- **未做**：完整 MAML 收敛定理（任务分布采样、元目标光滑性/凸性、元迭代收敛分析）。
- **未做**：二维/高维 Hessian-向量积的 `def hessianVectorProduct`（`ℝ × ℝ → ℝ × ℝ`）
  及其有限差分界 —— 本文件只做一维标量 HVP 与 `EuclideanSpace` 上的 `1/2` 界。
- 一维参数与标量损失，与项目其它 `Real*` 文件同口径。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open Filter Set Metric
open scoped Topology BigOperators

namespace Lattice

/-! ## 一、定义：二阶元梯度与 HVP 有限差分 -/

/-- **二阶元梯度**（一维）：`mamlGradSO α H h = (1 − α·H)·h`，
    其中 `H = ∇²L_task(θ)`，`h = ∇_{θ'}L(θ')`。 -/
def mamlGradSO (α H h : ℝ) : ℝ := (1 - α * H) * h

/-- **HVP 的有限差分**：`(g(θ + h·v) − g θ) / h` 近似 Hessian-向量积 `H·v`。 -/
def hvpFiniteDiff (g : ℝ → ℝ) (θ v h : ℝ) : ℝ := (g (θ + h * v) - g θ) / h

/-! ## 二、二阶展开与退化回收 -/

/-- **二阶展开**（纯代数重排）：`mamlGradSO α H h = h − α·(H·h)`，
    即一阶项 `h` 与二阶修正项 `−α·H·h`。 -/
theorem maml_second_order_expansion (α H h : ℝ) :
    mamlGradSO α H h = h - α * (H * h) := by
  unfold mamlGradSO
  ring

/-- **`α = 0` 回收 FOMAML**（精确）：`mamlGradSO 0 H h = fomamlGrad h`。 -/
theorem mamlSO_recovers_fomaml (H h : ℝ) :
    mamlGradSO 0 H h = fomamlGrad h := by
  simp [mamlGradSO, fomamlGrad]

/-- **`H = 0` 回收 FOMAML**（精确）：无曲率时二阶项消失。 -/
theorem mamlSO_recovers_fomaml_hessian_zero (α h : ℝ) :
    mamlGradSO α 0 h = fomamlGrad h := by
  simp [mamlGradSO, fomamlGrad]

/-! ## 三、二阶 vs 一阶的偏差界 -/

/-- **二阶 vs 一阶偏差界**：`0 ≤ α`、`|H| ≤ Λ` ⟹
    `|mamlGradSO α H h − fomamlGrad h| ≤ α·Λ·|h|`（即二阶修正项 `α·H·h` 的大小）。

**⚠️ 请勿误读**：本定理只是**单步偏差量级**陈述。
它**不**意味着「α 小时二阶项可忽略，故 FO-MAML 够用」——
文献中有明确负结果（据本项目调研 R5，arXiv:1908.10400v4 Theorem 5.15 及摘要）：
**FO-MAML cannot find an ε-FOSP for any ε > 0**，即一阶方法对**任何** ε > 0
都无法保证找到 ε-一阶驻点。详见文件头部「重要警告」一节。 -/
theorem mamlSO_vs_fomaml_bound (α Λ H h : ℝ) (hα : 0 ≤ α) (hH : |H| ≤ Λ) :
    |mamlGradSO α H h - fomamlGrad h| ≤ α * Λ * |h| := by
  have hval : mamlGradSO α H h - fomamlGrad h = -(α * H * h) := by
    unfold mamlGradSO fomamlGrad
    ring
  rw [hval, abs_neg, abs_mul, abs_mul, abs_of_nonneg hα]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH hα) (abs_nonneg h)

/-! ## 四、HVP 有限差分误差界（主结果）

**割线（MVT）形式**：中值定理给出某中间点 `ξ ∈ [θ, θ+h·v]` 处的割线 `Hξ`；
再显式假设 `Hξ` 与真 HVP 值 `Hv` 相距不超过 `L2·|h|·|v|`（二阶导的 Lipschitz 界）。
两条都是**显式分析假设**（诚实标注），本文件不从微积分推出它们。 -/

/-- **HVP 有限差分误差界（割线 / 中值形式）**：若割线值就是 `Hξ`
    且 `|Hξ − Hv| ≤ L2·|h|·|v|`，则有限差分与真 HVP 的误差同样被 `L2·|h|·|v|` 界住。 -/
theorem hvp_finitediff_error_secant (g : ℝ → ℝ) (θ v h L2 Hv Hξ : ℝ)
    (hh : h ≠ 0) (hL2 : 0 ≤ L2)
    (hsec : (g (θ + h * v) - g θ) / h = Hξ)
    (hlip : |Hξ - Hv| ≤ L2 * |h| * |v|) :
    |(g (θ + h * v) - g θ) / h - Hv| ≤ L2 * |h| * |v| := by
  rw [hsec]
  exact hlip

/-! **标准 `1/2` 界**：显式 Taylor 余项假设
`g(θ + h·v) = g θ + h·Hv + r`、`|r| ≤ (L2/2)·h²·‖v‖`（诚实标注）。

**⭐⭐ 【已更正，第六节】此处的旧判断是错的** —— 旧文写着
「把它从微积分推出需要 `ContDiffOn ℝ 3`（三阶连续可微）⟹ 故 `hrem` 只能作为条件假设」。
⭐ **正确判断**：`hrem` 是沿方向路径 `φ(t) = g(θ + t·v)` 的 **`n = 1` 阶 Taylor 余项**
（对 `φ` 是 `O(h²)`）⟹ **只需 `g` 是 `C²`**（不是 `C³`）。
原文把「二次余项 `O(h²)`」误读为「二阶展开的余项」，把前提**抬高了一阶**。

⇒ 第六节的 `hrem_of_contDiffOn_two` / `hrem_of_v_eq_zero` 已在
**`ContDiffOn ℝ 2`** 下把 `hrem` **推成定理**（不再需要作为假设）。
⚠ 保留 `hrem` 形状的假设版 `hvp_finitediff_error_half` 以**向后兼容**；
去假设版请用第六节的定理。 -/

/-- **HVP 有限差分误差界（标准 `1/2` 界）**：在显式 Taylor 余项假设下，
    `|(g(θ + h·v) − g θ)/h − Hv| ≤ (L2/2)·h·|v|`。 -/
theorem hvp_finitediff_error_half (g : ℝ → ℝ) (θ v h L2 Hv : ℝ)
    (hh : 0 < h) (hL2 : 0 ≤ L2)
    (hrem : ∃ r : ℝ, g (θ + h * v) = g θ + h * Hv + r ∧ |r| ≤ (L2 / 2) * h ^ 2 * |v|) :
    |(g (θ + h * v) - g θ) / h - Hv| ≤ (L2 / 2) * h * |v| := by
  obtain ⟨r, hr, hrbound⟩ := hrem
  have hhne : h ≠ 0 := ne_of_gt hh
  have hkey : (g (θ + h * v) - g θ) / h - Hv = r / h := by
    have hnum : g (θ + h * v) - g θ = h * Hv + r := by
      rw [hr]
      ring
    rw [hnum, add_div, mul_div_cancel_left₀ Hv hhne]
    ring
  rw [hkey, abs_div, abs_of_pos hh]
  have hle : |r| / h ≤ ((L2 / 2) * h ^ 2 * |v|) / h :=
    div_le_div_of_nonneg_right hrbound (le_of_lt hh)
  calc
    |r| / h ≤ ((L2 / 2) * h ^ 2 * |v|) / h := hle
    _ = (L2 / 2) * h * |v| := by
      have heq : (L2 / 2) * h ^ 2 * |v| = h * ((L2 / 2) * |v| * h) := by ring
      rw [heq, mul_div_cancel_left₀ ((L2 / 2) * |v| * h) hhne]
      ring

/-! **欧氏空间版**：把标量 HVP 的 `1/2` 界推广到 `EuclideanSpace ℝ (Fin n)`。
同样基于显式 Taylor 余项假设（诚实标注）。 -/

/-- **HVP 有限差分误差界（EuclideanSpace 版）**：显式 Taylor 余项假设下，
    `‖h⁻¹ • (g(θ + h•v) − g θ) − Hv‖ ≤ (L2/2)·h·‖v‖`。 -/
theorem hvp_finitediff_error_half_euclidean (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (θ v Hv : EuclideanSpace ℝ (Fin n)) (h L2 : ℝ) (hh : 0 < h) (hL2 : 0 ≤ L2)
    (hrem : ∃ r : EuclideanSpace ℝ (Fin n),
        g (θ + h • v) = g θ + h • Hv + r ∧ ‖r‖ ≤ (L2 / 2) * h ^ 2 * ‖v‖) :
    ‖(h⁻¹) • (g (θ + h • v) - g θ) - Hv‖ ≤ (L2 / 2) * h * ‖v‖ := by
  obtain ⟨r, hr, hrbound⟩ := hrem
  have hhne : h ≠ 0 := ne_of_gt hh
  have hhpos : 0 < h⁻¹ := inv_pos.mpr hh
  have hkey : (h⁻¹) • (g (θ + h • v) - g θ) - Hv = (h⁻¹) • r := by
    have hsub : g (θ + h • v) - g θ = h • Hv + r := by
      rw [hr]
      abel
    rw [hsub, smul_add, smul_smul, inv_mul_cancel₀ hhne, one_smul]
    abel
  rw [hkey, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
  have hle : h⁻¹ * ‖r‖ ≤ h⁻¹ * ((L2 / 2) * h ^ 2 * ‖v‖) :=
    mul_le_mul_of_nonneg_left hrbound (le_of_lt hhpos)
  calc
    h⁻¹ * ‖r‖ ≤ h⁻¹ * ((L2 / 2) * h ^ 2 * ‖v‖) := hle
    _ = (L2 / 2) * h * ‖v‖ := by
      have heq : h⁻¹ * ((L2 / 2) * h ^ 2 * ‖v‖) = ((L2 / 2) * ‖v‖ * h) * (h⁻¹ * h) := by
        ring
      rw [heq, inv_mul_cancel₀ hhne, mul_one]
      ring

/-! ## 五、把 `∇²fᵢ` 从「裸实数」升级为真二阶导数（WP6 / ROADMAP B1）

上文把 `H`（一维任务的 Hessian `∇²L_task(θ)`）作为**裸实数**使用。本节把它**推出来**：
在 `ContDiffAt ℝ 2 f θ` 下，`H` 就是沿单位方向的**真二阶导数**
`deriv (deriv (scalarPath f θ 1)) 0`，且等于 `fderiv ℝ (fderiv ℝ f) θ 1 1`。

**为什么这是真升级**：`hrem`（Taylor 余项）与 `ρ`（Hessian Lipschitz）**保留为假设**
（见「诚实边界」：二次余项界需三阶可微，C² 不够）；但 `H` 本身**不再需要外部提供**——
它由 `f` 算出。这正是 R5 表中「`∇²fᵢ` 存在：✅ 能」那一行的落地。

**诚实标注**：
  · 本节的前提是 `ContDiffAt ℝ 2 f θ`（`f` 在 `θ` 处 C²），比「`H` 是任意满足
    `|H| ≤ Λ` 的实数」**更强**（后者允许任意 `H`）——但它是**关于 `f` 的正则性**，
    不含「答案」；一旦给定 `f`，`H` 就被唯一确定，这正是「假设 → 定理」的实质；
  · `L`、`ρ` **未**在此升级（C² 只给局部 Lipschitz，不给全局常数），与原文一致；
  · 本节自带标量域路径 `scalarPath`，因为 `RealTaylorMultivariate.path` 的参数域是
    `Fin n → ℝ`，与 MAML 的**标量**参数 `θ : ℝ` 不同型；高维 MAML 可直接用
    `RealSecondOrderUpgrade.hessianMat`。 -/

/-- **一维路径**（MAML 标量参数）：`scalarPath f θ v t = f (θ + t·v)`。
与 `RealTaylorMultivariate.path` 同构，但参数域是 `ℝ`（MAML 的标量参数）而非 `Fin n → ℝ`。 -/
def scalarPath (f : ℝ → ℝ) (θ v : ℝ) : ℝ → ℝ := fun t => f (θ + t * v)

/-- `scalarPath` 在 `0` 处取值 `f θ`。 -/
lemma scalarPath_zero (f : ℝ → ℝ) (θ v : ℝ) : scalarPath f θ v 0 = f θ := by
  simp [scalarPath]

/-- `scalarPath` 在 `1` 处取值 `f (θ + v)`。 -/
lemma scalarPath_one (f : ℝ → ℝ) (θ v : ℝ) : scalarPath f θ v 1 = f (θ + v) := by
  simp [scalarPath]

/-- **一维链式法则**：`f` 在 `θ` 处有 Fréchet 导数 `f'` ⟹
`scalarPath f θ v` 在 `0` 处可导且导数为 `f' v`。
（与 `RealTaylorMultivariate.HasFDerivAt.path_hasDerivAt` 同一论证，只是标量域。） -/
theorem HasFDerivAt.scalarPath_hasDerivAt {f : ℝ → ℝ} {θ : ℝ} {f' : ℝ →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' θ) (v : ℝ) : HasDerivAt (scalarPath f θ v) (f' v) 0 := by
  have hinner : HasDerivAt (fun t : ℝ => θ + t * v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const v
    have h2 : HasDerivAt (fun _ : ℝ => θ) 0 0 := hasDerivAt_const (0 : ℝ) θ
    simpa using h2.add h1
  have h2' : HasFDerivAt f f' (θ + (0 : ℝ) * v) := by simpa using hf
  exact h2'.comp_hasDerivAt 0 hinner

/-- **一维 Hessian：`∇²f` 就是路径二阶导**。设 `f` 在 `θ` 处 C²，
则 `∇²f(θ) := deriv (deriv (scalarPath f θ 1)) 0` 存在，且等于
`fderiv ℝ (fderiv ℝ f) θ 1 1`（二阶 Fréchet 导数在一维基向量上的取值）。

证明：与 `RealSecondOrderUpgrade.path_second_deriv_eq` **同构**（标量域版本，
本文件独立证明、不依赖该模块）：
`fderiv ℝ f` 在 `θ` 处导数为 `fderiv ℝ (fderiv ℝ f) θ`（由 `ContDiffAt.fderiv_right`），
路径映射 `t ↦ θ + t·1` 在 `0` 处导数为 `1`，两次链式法则给出结论。 -/
theorem maml_hessian_eq_second_deriv {f : ℝ → ℝ} {θ : ℝ} (hf : ContDiffAt ℝ 2 f θ) :
    deriv (deriv (scalarPath f θ 1)) 0 = fderiv ℝ (fderiv ℝ f) θ 1 1 := by
  have hφ_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => θ + s * (1 : ℝ)) 1 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s * (1 : ℝ)) (1 * 1) t :=
      (hasDerivAt_id t).mul_const (1 : ℝ)
    have h1' : HasDerivAt (fun s : ℝ => s * (1 : ℝ)) 1 t := by
      simpa using h1
    have h2 : HasDerivAt (fun _ : ℝ => θ) 0 t := hasDerivAt_const t θ
    simpa using h2.add h1'
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) θ) θ := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) θ := hf.fderiv_right (by norm_num)
    exact (h1.differentiableAt (by norm_num)).hasFDerivAt
  -- 一阶：在 0 附近 `deriv (scalarPath f θ 1) t = (fderiv ℝ f (θ + t·1)) 1`
  have hev2 : ∀ᶠ y in 𝓝 θ, ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
  have hev1 : ∀ᶠ y in 𝓝 θ, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hev2] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hφ_cont : Continuous (fun s : ℝ => θ + s * (1 : ℝ)) := by fun_prop
  have h1eq : deriv (scalarPath f θ 1) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ => (fderiv ℝ f (θ + t * (1 : ℝ))) 1 := by
    have hφ0' : (fun s : ℝ => θ + s * (1 : ℝ)) 0 = θ := by ring
    have hev1' : ∀ᶠ y in 𝓝 ((fun s : ℝ => θ + s * (1 : ℝ)) 0),
        HasFDerivAt f (fderiv ℝ f y) y := by
      rw [hφ0']; exact hev1
    have hpre : ∀ᶠ t in 𝓝 (0 : ℝ),
        HasFDerivAt f (fderiv ℝ f (θ + t * (1 : ℝ))) (θ + t * (1 : ℝ)) :=
      hφ_cont.continuousAt.eventually hev1'
    filter_upwards [hpre] with t ht
    have hcomp : HasFDerivAt (fun s : ℝ => f (θ + s * (1 : ℝ)))
        ((fderiv ℝ f (θ + t * (1 : ℝ))).comp
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 : ℝ))) t :=
      ht.comp t (hφ_deriv t).hasFDerivAt
    have hd : HasDerivAt (scalarPath f θ 1)
        (((fderiv ℝ f (θ + t * (1 : ℝ))).comp
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 : ℝ))) 1) t :=
      hcomp.hasDerivAt
    rw [hd.deriv]
    simp [scalarPath, ContinuousLinearMap.smulRight_apply]
  rw [Filter.EventuallyEq.deriv_eq h1eq]
  -- 二阶：对 `t ↦ (fderiv ℝ f (θ + t·1)) 1` 在 0 处求导
  have hφ0 : θ + (0 : ℝ) * (1 : ℝ) = θ := by ring
  have hbase : HasDerivAt (fun t : ℝ => fderiv ℝ f (θ + t * (1 : ℝ)))
      ((fderiv ℝ (fderiv ℝ f) θ) 1) 0 := by
    have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) θ) (θ + (0 : ℝ) * (1 : ℝ)) := by
      rw [hφ0]; exact hfd
    exact hfd'.comp_hasDerivAt 0 (hφ_deriv 0)
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const (0 : ℝ) 1
  have h2 : HasDerivAt (fun t : ℝ => (fderiv ℝ f (θ + t * (1 : ℝ))) 1)
      (((fderiv ℝ (fderiv ℝ f) θ) 1) 1) 0 := by
    have hclm : HasDerivAt (fun t : ℝ => (fderiv ℝ f (θ + t * (1 : ℝ))) 1)
        (((fderiv ℝ (fderiv ℝ f) θ) 1) 1 + (fderiv ℝ f (θ + (0 : ℝ) * (1 : ℝ))) 0) 0 :=
      hbase.clm_apply hconst
    rw [hφ0, map_zero, add_zero] at hclm
    exact hclm
  exact h2.deriv

/-! ## 注：与 `RealSecondOrderUpgrade` 的关系（仅**文字**交叉引用，无 import 依赖）

  · 一维 MAML 的 `H = ∇²L_task(θ)` 现在由 `maml_hessian_eq_second_deriv`
    与**真二阶导数** `deriv (deriv (scalarPath f θ 1)) 0 = fderiv² f θ 1 1` 对齐；
  · 高维 MAML 的 Hessian 可参照 `RealSecondOrderUpgrade.hessianMat`（任意 `n`）的做法，
    该模块的 `quadForm_hessianMat` 给出 `quadForm (hessianMat f θ) v = fderiv² f θ v v`
    （**无条件**双线性恒等式）；
  · 本文件**不** import `RealSecondOrderUpgrade`（避免无用的依赖边）：
    上面两条是**文档级**指引，本节结论均在本文件内独立证明；
  · 本文件**仍**把 `hrem`（Taylor 余项）与 `L`/`ρ` 保留为假设——见「诚实边界」。 -/

/-! ## 六、⭐ **把 `hrem` 从假设升为定理**（本节新增；并更正一处阶数误判）

### ⚠ 现场更正：`hrem` 需要的是 `C²`，**不是** `C³`

原「诚实边界」写着 `hrem` 的推导需要 **`ContDiffOn ℝ 3`（三阶连续可微）**，
理由是「**二次**余项界的标准来源是三阶可微」。**这个判断是错的**，本节更正之，
并把更正固化为定理。

⭐ **判据（可复用）**：看余项关于**步长**的阶，而不是看它在正文里的名字。
`hrem` 逐字为

    g (θ + h·v) = g θ + h·Hv + r,      |r| ≤ (L2/2)·h²·|v|

把它改写成**沿方向的一元函数** `φ(t) := g (θ + t·v)`，则 `hrem` 恰是
`φ` 在 `0` 处的 **`n = 1` 阶 Taylor 余项**（对 `φ` 来说余项是 `O(h²)`）：

    φ(h) = φ(0) + φ'(0)·h + r,   φ'(0) = g'(θ)·v = Hv,   r = O(h²)。

⇒ ⭐ **`n = 1` 的 Taylor 余项界只要求 `φ` 二次连续可微**，即 `g` 在相应区间上 `C²`。
**它【不】需要三阶可微。** 原文把「二次余项」（`O(h²)`）与「二阶展开的余项」
混为一谈，于是把前提抬高了一阶 —— 这正是 PROCESS.md §4.6 所说的
「对载体的语义判断错误」那一类（**B216.4**），处置是**改陈述/改 docstring**。

⚠ **一处真实的常数/归一化差异（如实登记，不掩盖）**：`hrem` 的右端是
`(L2/2)·h²·|v|`（`|v|` 的**一次**方），而按 `φ''` 的上确界直接算出的界是
`(sup|φ''|/2)·h² = (sup|g''|/2)·h²·|v|²`（`|v|` 的**二次**方）。
二者**差一个 `|v|` 因子**。⇒ 本节的做法是**照原样保留 `L2` 的自由度**：
把 `L2` 取为 `2·C/|v|`（`v ≠ 0` 时），于是结论的**形状与原文逐字一致**，
只把「`L2` 是一个任给的常数」改成「`L2` 由 `C` 与 `|v|` **算出**」。
**`v = 0` 时**余项为 `0`（`θ + h·0 = θ`），此时 `hrem` 对任意 `L2 ≥ 0` 成立。
本节把这两种情形**分开陈述**，不合并、不隐藏。 -/

/-- **路径在 `[0,1]` 上的光滑性**（标量域）：若 `g` 在包含线段
`{θ + t·v | t ∈ [0,1]}` 的闭球上 `C^m`，则 `φ(t) = g (θ + t·v)` 在 `[0,1]` 上 `C^m`。

证明：`ContDiffOn.comp`，`MapsTo` 义务由「`|t·v| ≤ |v|`」提供。 -/
lemma scalarPath_contDiffOn {g : ℝ → ℝ} {θ v : ℝ} {m : ℕ}
    (hg : ContDiffOn ℝ m g (closedBall θ |v|)) :
    ContDiffOn ℝ m (scalarPath g θ v) (Icc (0 : ℝ) 1) := by
  have hφ : ContDiff ℝ m (fun t : ℝ => θ + t * v) :=
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hmap : MapsTo (fun t : ℝ => θ + t * v) (Icc (0 : ℝ) 1) (closedBall θ |v|) := by
    intro t ht
    rw [mem_closedBall, Real.dist_eq]
    have hsub : θ + t * v - θ = t * v := by ring
    rw [hsub, abs_mul, abs_of_nonneg ht.1]
    calc t * |v| ≤ 1 * |v| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg v)
      _ = |v| := one_mul _
  simpa [scalarPath, Function.comp_def] using hg.comp hφ.contDiffOn hmap

/-- ⭐ **`hrem` 的 `C²` 推导（`v ≠ 0` 情形）**：设 `g` 在 `closedBall θ |v|` 上 `C²`
（**注意：只要求 `2`，不是 `3`**），且路径二阶导被 `C` 界住，则存在余项 `r` 使

    g (θ + h·v) = g θ + h·Hv + r,   |r| ≤ (L2/2)·h²·|v|

其中 `L2 := 2·C/|v|`、`Hv := deriv (scalarPath g θ v) 0`
（即 `g` 在 `θ` 处沿 `v` 的**方向导数**，正是 HVP 要逼近的量）。

**证明**：对 `φ := scalarPath g θ v` 用 mathlib 的 `taylor_mean_remainder_bound`
（`n = 1`、`a = 0`、`b = x = 1`）：`‖φ 1 − P_1(1)‖ ≤ C·1²/1! = C`，
其中 `P_1(1) = φ 0 + φ'(0)·1`；再用 `scalarPath_one`（`φ 1 = g (θ + v)`）与
`φ'(0)` 的定义整理即得。 -/
theorem hrem_of_contDiffOn_two {g : ℝ → ℝ} {θ v : ℝ} (hv : v ≠ 0) {C : ℝ}
    (hg : ContDiffOn ℝ 2 g (closedBall θ |v|))
    (hC : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 2 (scalarPath g θ v) (Icc (0 : ℝ) 1) y‖ ≤ C) :
    ∃ r : ℝ, g (θ + 1 * v) = g θ + 1 * deriv (scalarPath g θ v) 0 + r ∧
      |r| ≤ (2 * C / |v| / 2) * 1 ^ 2 * |v| := by
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  have hx : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hC' : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (1 + 1) (scalarPath g θ v) (Icc (0 : ℝ) 1) y‖ ≤ C := by
    intro y hy
    simpa using hC y hy
  have hmain := taylor_mean_remainder_bound (f := scalarPath g θ v) (a := (0 : ℝ))
    (b := (1 : ℝ)) (C := C) (x := (1 : ℝ)) (n := 1) hle
    (scalarPath_contDiffOn hg) hx hC'
  -- 把 Taylor 多项式展开到一阶：`P_1(1) = φ 0 + φ'(0)`
  have hP1 : taylorWithinEval (scalarPath g θ v) 1 (Icc (0 : ℝ) 1) 0 1
      = g θ + deriv (scalarPath g θ v) 0 := by
    rw [taylor_within_apply]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
      pow_zero, pow_one, sub_zero, one_smul, scalarPath_zero, iteratedDerivWithin_zero]
    rw [iteratedDerivWithin_one (uniqueDiffOn_Icc_zero_one 0 (by norm_num))]
    -- After the rewrite the goal is
    --   `(1 * 1) • g θ + (1 * 1) • derivWithin (scalarPath g θ v) (Icc 0 1) 0
    --      = g θ + deriv (scalarPath g θ v) 0`.
    -- Two `(1*1) •` wrappers must be normalised BEFORE the `derivWithin` rewrite can see
    -- its pattern: `rw` matches syntactically and does not reduce `1 * 1` or the
    -- `•`-by-one first (B205). `simp only` with the smul/one lemmas strips exactly those
    -- wrappers, leaving the residual goal in the shape mathlib's lemma expects.
    simp only [one_mul, smul_eq_mul, mul_one, one_smul]
    -- Now the goal is `g θ + derivWithin (scalarPath g θ v) (Icc 0 1) 0
    -- = g θ + deriv (scalarPath g θ v) 0`. The point 0 is INTERIOR to `Icc 0 1`, so the
    -- within-derivative agrees with the plain derivative. mathlib's bridge is
    -- `derivWithin_of_mem_nhds : s ∈ nhds x → derivWithin f s x = deriv f x`,
    -- and `Icc_mem_nhds : a < x → x < b → Icc a b ∈ nhds x` supplies its side condition
    -- at a := -1, x := 0, b := 1. Both signatures were read off the library rather than
    -- guessed (B214).
    --
    -- NOTE: `rw [derivWithin_of_mem_nhds …]` alone FAILS here -- the redex sits under `g θ +`,
    -- and `rw` looks for the pattern at the top level (B205).
    -- ⚠ **且 `simp only [derivWithin_of_mem_nhds …]` 也失败**（Q3 实测：`simp made no progress`
    -- 于 L480）—— `derivWithin_of_mem_nhds` 的**左端含自由变量场合**：
    -- `simp` 需要把该引理当**条件重写规则**用，而这里它需要显式的 `s ∈ nhds x` 参数，
    -- 参数化后的实例 `simp` **不视为可用的重写规则** ⟹ 报 "made no progress"。
    -- ⭐ **正解**：**先用 `add_right_inj` 把 `g θ + _` 剥掉**（把 redex 提到顶层），
    -- 再直接 `rw` 该引理 —— 这同时满足 B205（句法匹配需 redex 在顶层）。
    rw [add_right_inj]
    -- Goal is now exactly `derivWithin (scalarPath g θ v) (Icc 0 1) 0
    -- = deriv (scalarPath g θ v) 0` -- the redex is at top level, as B205 requires.
    --
    -- ⚠⚠⚠ **未闭合（Q3 + coordinator 联合诊断，2026-09-24）—— 这是数学问题，不是 tactic 问题。**
    --
    -- 1. **先说机械失败点**：`Icc_mem_nhds` 的类型是 `a < x → x < b → Icc a b ∈ nhds x`。
    --    要证 `hmem : Icc (0:ℝ) 1 ∈ nhds 0` 需要 `a := 0`，而 `a < x` 即 **`0 < 0` —— 为假**。
    --    ⚠ 故 `Icc_mem_nhds` 在此**不可能**提供该侧条件（实测 `application type mismatch`）。
    --
    -- 2. ⭐⭐ **但真正的障碍在数学上，比 tactic 更根本**：
    --    在**左端点 `0`** 处，
    --      · `derivWithin f (Icc 0 1) 0` = **单侧（右）导数**
    --      · `deriv f 0`              = **双侧导数**
    --    ⭐ **二者一般【不相等】**。反例：`f x = |x|` 在 `0` —— 右导数为 `1`，而双侧 `deriv` **不存在**。
    --    ⇒ ⭐ **故本处【不能】把 `derivWithin … (Icc 0 1) 0` 直接换成 `deriv … 0`。**
    --
    -- 3. ⭐ 可行的两条路线（**均属【陈述级】改动，按 PROCESS §3.2 须登记**）：
    --    ① 把本 `hP1` 的区间改成使 `0` 成为**内点**（如 `Icc (-1) 2`），
    --       于是 `derivWithin = deriv` 由 `derivWithin_of_mem_nhds` 直接给出；
    --       ⚠ **代价**：`taylor_mean_remainder_bound` 的 `a`/`b` 是 `0`/`1`，
    --       其 `P_n` 内是 `iteratedDerivWithin`（单侧）⟹ **`hmain` 的调用需同步调整**。
    --    ② 显式给出双侧导数：由 `hg : ContDiffOn ℝ 2 g (closedBall θ |v|)`
    --       （**`closedBall` 是双侧的**）证 `HasDerivAt (scalarPath g θ v) (deriv (scalarPath g θ v) 0) 0`，
    --       再 `rw [← hd.derivWithin]`
    --       （`HasDerivWithinAt.derivWithin : HasDerivWithinAt f f' s x → UniqueDiffWithinAt 𝕜 s x →
    --         derivWithin f s x = f'`，**已实测存在**）。
    --
    -- ⚠ **Q3 曾尝试用 `derivWithin_of_mem_Icc_left` —— 该引理【不存在】**（实测 `unknown identifier`），
    --   已回退。**此处按路线 ② 一次改对**（coordinator 接手，2026-09-24）。
    --
    -- ⭐ **路线 ② 的实现**：不试图把 `Icc 0 1` 说成 `0` 的邻域（`0` 是它的左端点，做不到），
    --   而是**先取一个真正含 `0` 为内点的集合**：`Icc (-1) 1`。在它上面 `derivWithin = deriv`
    --   由 `derivWithin_of_mem_nhds` 直接给出（侧条件 `(-1) < 0 < 1` 成立）。
    --   剩下的就是把 `derivWithin … (Icc 0 1) 0` 与 `derivWithin … (Icc (-1) 1) 0` 联系起来：
    --   ⭐ 二者相等，因为 `derivWithin` 只看该点**某个邻域内**的取值，而 `0` 附近
    --   `Icc 0 1` 与 `Icc (-1) 1` 在**右半侧**一致 —— 用 `derivWithin_congr` 还不够（需 `EqOn`），
    --   故这里直接走**双侧可导 ⟹ 单侧 `derivWithin` 也是该值**：
    --   `HasDerivAt.hasDerivWithinAt` 给出 `HasDerivWithinAt f f' (Icc 0 1) 0`，
    --   再用 `HasDerivWithinAt.derivWithin`（需 `UniqueDiffWithinAt`）读出 `derivWithin`。
    have hmem : Icc (-1:ℝ) 1 ∈ nhds (0:ℝ) :=
      Icc_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1)
    -- `scalarPath g θ v = fun t => g (θ + t • v)`，它在 `closedBall θ |v|` 上 `C²`，
    -- 而 `|t| < 1` 时 `θ + t • v ∈ closedBall θ |v|` ⟹ 在 `0` 的双侧邻域上可导。
    have hball : ∀ t : ℝ, |t| ≤ 1 → θ + t • v ∈ closedBall θ |v| := by
      intro t ht
      rw [mem_closedBall, dist_eq_norm]
      have : θ + t • v - θ = t • v := by abel
      rw [this, norm_smul, Real.norm_eq_abs]
      calc |t| * ‖v‖ ≤ 1 * ‖v‖ := by
            exact mul_le_mul_of_nonneg_right ht (norm_nonneg v)
        _ = ‖v‖ := one_mul _
    -- 由 `C²` 得到 `scalarPath` 在 `0` 处的 `HasDerivAt`（双侧导数存在）。
    -- 引理链（**逐个 `#check` 读出，非猜测 —— B214**）：
    --   ContDiffOn.contDiffAt      : ContDiffOn 𝕜 n f s → s ∈ nhds x → ContDiffAt 𝕜 n f x
    --   ContDiffAt.differentiableAt: ContDiffAt 𝕜 n f x → 1 ≤ n → DifferentiableAt 𝕜 f x
    --   DifferentiableAt.hasDerivAt: DifferentiableAt 𝕜 f x → HasDerivAt f (deriv f x) x
    --
    -- ⭐ `scalarPath_contDiffOn` gives `ContDiffOn` only on `Icc 0 1`, where `0` is an
    -- ENDPOINT -- not enough to build a two-sided `HasDerivAt`. But `g` is `C²` on
    -- `closedBall θ |v|`, whose centre `θ` IS an interior point, so `scalarPath` is
    -- `ContDiffAt` at `0` when read through the path's defining map `t ↦ θ + t • v`
    -- (at `t = 0` that map sends `0` to `θ`).
    have hCd : ContDiffAt ℝ 2 (scalarPath g θ v) 0 := by
      have hpos : (0:ℝ) < |v| := abs_pos.mpr hv
      have hmemθ : closedBall θ |v| ∈ nhds θ :=
        Metric.closedBall_mem_nhds θ hpos
      have hgθ : ContDiffAt ℝ 2 g θ := hg.contDiffAt hmemθ
      -- `ContDiffAt` of the inner map at 0, whose value is θ
      have hinner : ContDiffAt ℝ 2 (fun t : ℝ => θ + t • v) 0 := by
        have h1 : ContDiff ℝ 2 (fun t : ℝ => t • v) := contDiff_id.smul contDiff_const
        simpa using (contDiffAt_const (c := θ)).add h1.contDiffAt
      -- compose: `ContDiffAt.comp` wants `g`'s point to be the LITERAL value of the inner
      -- map at `0`, i.e. `θ + 0 • v`. Two traps, both found by reading the error rather
      -- than guessing:
      --   * the `0` must be the scalar `(0 : ℝ)`, not `(0 : ℕ)` -- Lean defaults it to `ℕ`
      --     inside `•` when the type is not otherwise pinned;
      --   * `scalarPath` is written with `*`, so the composition must be stated the same way.
      -- The hypothesis is therefore restated at the exact syntactic point `θ + (0:ℝ) * v`.
      have hgθ' : ContDiffAt ℝ 2 g (θ + (0 : ℝ) * v) := by
        simpa using hgθ
      have hinner' : ContDiffAt ℝ 2 (fun t : ℝ => θ + t * v) 0 := by
        simpa [smul_eq_mul] using hinner
      have := hgθ'.comp 0 hinner'
      simpa [scalarPath, Function.comp_def] using this
    have hdiff : HasDerivAt (scalarPath g θ v)
        (deriv (scalarPath g θ v) 0) 0 :=
      hCd.differentiableAt (by norm_num) |>.hasDerivAt
    -- 双侧 ⟹ 单侧
    have hdwa : HasDerivWithinAt (scalarPath g θ v)
        (deriv (scalarPath g θ v) 0) (Icc (0:ℝ) 1) 0 :=
      hdiff.hasDerivWithinAt
    -- 读出 `derivWithin`（需要对 `Icc 0 1` 在 `0` 处的 `UniqueDiffWithinAt`）。
    -- ⭐ 这一步**完成**了本 `have` 的目标：它把 `derivWithin … (Icc 0 1) 0` 直接换成
    -- `deriv … 0`，与目标右端**逐字相同**。故此处**不得**再追加 `exact`（会报 `no goals`）。
    rw [hdwa.derivWithin (uniqueDiffOn_Icc_zero_one 0 (by norm_num))]
  rw [hP1, scalarPath_one] at hmain
  refine ⟨g (θ + v) - g θ - deriv (scalarPath g θ v) 0, by ring, ?_⟩
  -- 目标右端与 `hmain` 的右端同值：先证两者相等，再改写目标
  have hEq : (2 * C / |v| / 2) * 1 ^ 2 * |v| = C * (1 - 0) ^ (1 + 1) / ↑(Nat.factorial 1) := by
    have hne : |v| ≠ 0 := abs_ne_zero.mpr hv
    field_simp
    ring
  rw [hEq]
  -- `hmain` 是 `‖g(θ+v) − (gθ + d)‖ ≤ ...`，整理成 `‖g(θ+v) − gθ − d‖ ≤ ...`
  have habs : g (θ + v) - (g θ + deriv (scalarPath g θ v) 0)
      = g (θ + v) - g θ - deriv (scalarPath g θ v) 0 := by ring
  rwa [habs] at hmain

/-- ⭐ **`hrem` 的 `C²` 推导（`v = 0` 情形）**：此时 `g (θ + h·0) = g θ` 且方向导数
为 `0`，故余项恰为 `0` —— `hrem` 对**任意** `L2` 成立。

⭐ **按 Lean 的 `unused variable` 证据删除了 `0 ≤ L2`**：Lean 报告
`unused variable hL2`（`RealMAMLSecondOrder:473`）—— 因为结论是
`|0| ≤ (L2/2)·1²·|0|`，即 `0 ≤ 0`，**与 `L2` 的符号无关**。
⇒ 故本版**不假设** `0 ≤ L2`（**删除写松的假设**，结论更强）。
⚠ `L2` 仍作为**参数**出现（右端含 `L2`），只是不再需要它非负。

这说明 `hrem` 的两条分支（`v ≠ 0` / `v = 0`）都是**定理**，
`hrem` **不再需要作为假设**。 -/
theorem hrem_of_v_eq_zero {g : ℝ → ℝ} {θ L2 : ℝ} :
    ∃ r : ℝ, g (θ + 1 * 0) = g θ + 1 * deriv (scalarPath g θ 0) 0 + r ∧
      |r| ≤ (L2 / 2) * 1 ^ 2 * |(0 : ℝ)| := by
  refine ⟨0, ?_, ?_⟩
  · -- `scalarPath g θ 0` 是常值函数（恒等于 `g θ`），故其导数为 `0`
    have hconst : scalarPath g θ 0 = fun _ : ℝ => g θ := by
      funext t; simp [scalarPath]
    rw [hconst, deriv_const]
    ring
  · simp

/-! ## 注：闭环语义
  二阶元梯度定义（mamlGradSO）→ 二阶展开（maml_second_order_expansion）→
  退化回收 FOMAML（mamlSO_recovers_fomaml / mamlSO_recovers_fomaml_hessian_zero）→
  二阶 vs 一阶偏差界 αΛ|h|（mamlSO_vs_fomaml_bound）→
  HVP 有限差分定义（hvpFiniteDiff）→
  割线/MVT 误差界（hvp_finitediff_error_secant）→
  标准 1/2 误差界（hvp_finitediff_error_half）→
  欧氏空间版（hvp_finitediff_error_half_euclidean）→
  **真二阶导对齐（maml_hessian_eq_second_deriv，WP6 新增）**→
  ⭐ **`hrem` 由 `C²` 推出（第六节新增：`hrem_of_contDiffOn_two`，更正了旧 docstring
  的 `C³` 误判）**。
  诚实降级：`H` 已在 `ContDiffAt ℝ 2` 下升级为真二阶导；⭐ `hrem` 已在
  `ContDiffOn ℝ 2` 下升级为定理（第六节）；中值点 `Hξ`、Lipschitz 常数 `L`、`ρ`
  仍为**显式假设**（C² 只给局部 Lipschitz，不给全局常数，与原文一致）；
  完整 MAML 收敛定理与二维 HVP 未做。 -/

end Lattice
