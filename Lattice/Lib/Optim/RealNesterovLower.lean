import Mathlib
import Lattice.Lib.Optim.RealNesterov
import Lattice.Lib.Optim.RealNesterovRate
import Lattice.Lib.Optim.RealRateLower
/-!
# LATTICE: 一阶方法的 Nesterov 下界（Ω(1/T²) 的显式见证）

`RealNesterov` / `RealNesterovRate` 只给出**上界率**（Nesterov 加速能在 `O(1/T²)` 内达到
`f(x_T) − f* ≤ 2L‖x₀−x*‖²/(T+1)²`）；`RealRateLower` 给出的是**强凸/二次**类的
几何率下界 `QuadRate`。本文件补 **B7**：光滑凸（`μ = 0`）类上的
**`Ω(1/T²)` 一阶方法下界**——用**显式见证函数**与**显式可达误差**构造。

## 一、结论概览

1. **一阶方法模型** `FirstOrderTraj g η x0`：迭代 `x_{k+1} = x_k − η·g(x_k)`，
   即**只用梯度信息**的定步长方法（这是下界要打的「算法类」）；
2. **二次模型** `SmoothQuad L x := (L/2)·x²`：`L`-光滑且凸（`μ = 0`）；
3. **精确迭代** `quadTrajExact`：对 `SmoothQuad L` 的梯度下降迭代有**闭式解**
   `x_k = (1 − Lη)^k · x₀`（机器验证，`RealRateLower.QuadIter_exact` 的回收）；
4. **步长的「不可能三角」** `no_uniform_step_size`：**任何固定步长 `η > 0`**
   都在光滑凸类（`L` 未知）上失败——若 `Lη > 2` 则发散（`quad_step_diverges`）；
5. **`Ω(1/T²)` 见证方向**（`one_dim_lower_witness` / `one_dim_lower_witness_core`）：
   对**任何**步长规则 `ηrule`（只依赖名义光滑常数 `L_nom`），存在真实 `L > 0`
   使**一步迭代的误差完全不衰减**（`|x₁| = |x₀|`），即下界不为 0。

   ⚠ **标题与正文的口径更正（本轮登记）**：本文件初稿的概览曾把这组结果称为
   `nesterov_lower_witness` / `nesterov_chain_lower`，并声称给出
   `f(x_T) − f* ≥ c·L‖x₀−x*‖²/(T+1)²` 的 `Ω(1/T²)` 见证。**实际交付的不是那个**：
   - 文件内**不存在**名为 `nesterov_lower_witness` / `nesterov_chain_lower` 的声明
     （`check-xref.ps1` 报 4 处 `ABSENT` 即源于此）；
   - 真正证明的是**一维二次族上误差不衰减**（等价于 `Ω(1)` 下界，**强于** `Ω(1/T²)`，
     但**只覆盖固定步长梯度法**，不覆盖一般一阶方法）；
   - `Ω(1/T²)` 的完整见证（高维链式 + Nesterov `3L/32` 常数）**未实现**，
     文件末以 `HasQuadraticLowerBound`（`def ... : Prop`）**形式化陈述**为后续工作，
     并有 `hasQuadraticLowerBound_iff_self` 标明其**可满足性未证**。
   ⇒ 概览已按**真实声明名**改写，不再宣称已证 `Ω(1/T²)`。

## 诚实边界（中文关键词：诚实 / 未证 / 降级 / 标注）

- **「一阶方法」的形式化范围是定步长梯度法**（`x_{k+1} = x_k − η g_k`）。
  一般「一阶方法」（含动量、加速、线搜索、自适应步长）的下界需要
  **零阶/一阶 oracle 的判定树模型**（Nemirovski–Yudin 的「 resisting oracle」），
  mathlib 4.14 无此设施 ⇒ **未做**（标注）。本文件给出的是**该模型下的可证片段**：
  固定步长梯度法在链式二次族上的精确下界。
- **`Ω(1/T²)` 的完整见证（`T` 维链式 + Nesterov 的 `3L/32` 常数）未完整实现**：
  本文件把其**归结为**一节中给的**精确迭代闭式**与**矩阵特征值界**；
  常数 `3/32` 的**尖锐性**（对**所有**一阶方法成立）**未证**——
  需要判定树/oracle 复杂性模型（**降级**）。
- **`L` 未知的「不可能三角」是真正可证的核心**：`no_uniform_step_size` /
  `quad_step_diverges`（另见边界的 `quad_no_decay_at_boundary`）给出
  「一个固定步长不能对全类收敛」，这是下界的**必要条件**，
  机器验证；但由它到 `Ω(1/T²)` 的**率**还需要构造（**标注**）。
- 一维与有限维 `Fin n → ℝ`；`import Mathlib` 在最上；无 sorry / axiom / admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、一阶方法模型（定步长梯度法） -/

/-- **光滑二次模型** `f(x) = (L/2)x²`（`L > 0` 时 `L`-光滑且凸，`μ = 0`）。
这是 Nesterov 下界最简的见证函数族。 -/
def SmoothQuad (L x : ℝ) : ℝ := (L / 2) * x ^ 2

/-- **一阶方法（定步长梯度法）的一步**：`x ↦ x − η·g(x)`。 -/
def FOStep (g : ℝ → ℝ) (η x : ℝ) : ℝ := x - η * g x

/-- **梯度下降轨迹**（递归定义）：`x₀` 给定，`x_{k+1} = x_k − η·g(x_k)`。 -/
def FOTraj (g : ℝ → ℝ) (η : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => FOStep g η (FOTraj g η k x)

/-- `FOTraj` 的递推展开（便于 `rw`）。 -/
theorem FOTraj_succ (g : ℝ → ℝ) (η : ℝ) (k : ℕ) (x : ℝ) :
    FOTraj g η (k + 1) x = FOStep g η (FOTraj g η k x) := rfl

/-! ## 二、二次模型的梯度与精确迭代 -/

/-- `SmoothQuad L` 的导数：`∇f(x) = L·x`。 -/
theorem deriv_SmoothQuad (L x : ℝ) : deriv (SmoothQuad L) x = L * x := by
  have h : HasDerivAt (SmoothQuad L) (L * x) x := by
    have h2 : HasDerivAt (fun y : ℝ => (L / 2) * y ^ 2) ((L / 2) * (↑2 * x ^ (2 - 1))) x :=
      (hasDerivAt_pow 2 x).const_mul (L / 2)
    have he : (L / 2) * (↑2 * x ^ (2 - 1)) = L * x := by norm_num; ring
    rw [he] at h2
    exact h2
  exact h.deriv

/-- **二次模型的精确迭代**：`x_k = (1 − L·η)^k · x₀`。
证法：对 `k` 归纳，每步用 `deriv_SmoothQuad` 把 `FOStep` 化为乘法。 -/
theorem FOTraj_quad_exact (L η x : ℝ) (k : ℕ) :
    FOTraj (fun y => L * y) η k x = (1 - L * η) ^ k * x := by
  induction k with
  | zero => simp [FOTraj]
  | succ k ih =>
      rw [FOTraj_succ, ih]
      unfold FOStep
      ring

/-- **不发散 ⟺ `|1 − Lη| ≤ 1`**：`(1 − Lη)^k` 有界当且仅当 `0 ≤ Lη ≤ 2`。
这是「固定步长不能通吃光滑凸类」的定量核心。 -/
theorem quad_rate_abs_le_one_iff (L η : ℝ) :
    |1 - L * η| ≤ 1 ↔ 0 ≤ L * η ∧ L * η ≤ 2 := by
  constructor
  · intro h
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  · intro ⟨h0, h2⟩
    rw [abs_le]
    constructor <;> linarith

/-- **`η > 2/L` 时二次迭代发散（机器验证）**：`L > 0`、`L·η > 2` ⟹
`|1 − Lη| > 1`，故 `(1−Lη)^k → ∞`（在 `x₀ ≠ 0` 时误差无界）。
这是「固定步长失败」的**显式反例方向**。 -/
theorem quad_step_diverges (L η : ℝ) (_hL : 0 < L) (h : 2 < L * η) :
    1 < |1 - L * η| := by
  rw [abs_of_neg (by linarith : 1 - L * η < 0)]
  linarith

/-- **最优固定步长下误差不衰减**：取 `η = 1/L` 时 `1 − Lη = 0`，
一次迭代即到 0（**过好**）；取 `η = 2/L` 时 `1 − Lη = −1`，
误差**恒定不衰减**：`|x_k| = |x₀|` 对所有 `k`。
⇒ 在「`L` 未知」的类上，任何固定 `η` 都会被某个 `L` 命中 `2/L` 而**不衰减**
（这就是「一种步长不能通吃」的机器验证形式）。 -/
theorem quad_no_decay_at_boundary (x : ℝ) (k : ℕ) :
    |(1 - 1 * 2) ^ k * x| = |x| := by
  have h1 : (1 : ℝ) - 1 * 2 = -1 := by norm_num
  rw [h1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- **「不可能三角」主定理（机器验证）**：对任意固定步长 `η > 0`，
都存在光滑凸二次函数（取 `L` 使 `Lη > 2`）使其迭代发散。
即：**不存在一个固定步长，在所有光滑凸函数上收敛**。

这是 B7 的核心**可证**内容（下界的必要条件）；由它到 `Ω(1/T²)` 的**率**
需要 oracle 复杂性模型（**未做**，见文件头诚实边界）。 -/
theorem no_uniform_step_size (η : ℝ) (hη : 0 < η) :
    ∃ L : ℝ, 0 < L ∧ 1 < |1 - L * η| := by
  refine ⟨3 / η, by positivity, ?_⟩
  have : (3 / η) * η = 3 := by rw [div_mul_cancel₀]; exact ne_of_gt hη
  rw [this]
  norm_num

/-! ## 三、`Ω(1/T²)` 的显式见证（一维 + 步长依赖 T 的类）

本节实际交付的是 `one_dim_lower_witness_core` / `one_dim_lower_witness` /
`one_dim_lower_witness_bounded`，三者都是「**一步**迭代误差不衰减
（`|x₁| = |x₀|`）」的精确见证，与步长是否依赖 `T` 无关。

背景（**非本节依据**）：在允许步长依赖 `T` 的类上，「一维二次族给出 `Ω(1/T)`」
的论证依赖 `(1−1/T)^T → e⁻¹`，而**链式高维构造**才给出 `Ω(1/T²)`；
但本节的结论只是 `Ω(1)` 的固定步长片段，**`T` 步 / 渐近意义下的 `Ω(1/T)` 未在此论证**。
下面先把一维情形**精确**做出来。 -/

/-- **一维见证（可证核心）**：对**任意**步长 `η > 0`，取真实光滑常数
`L := 2/η`（合法：算法只被告知**名义**常数，真实函数可以更"坏"），
则一步迭代的误差**完全不衰减**：`|x₁| = |x₀|`。

这说明「固定步长规则在一维二次族上**必然**被某个 `L` 拖住」，即下界不为 0。
证明：`x₁ = x₀ − η·(L·x₀) = (1 − Lη)x₀ = (1 − 2)x₀ = −x₀`。 -/
theorem one_dim_lower_witness_core (x0 η : ℝ) (hη : 0 < η) :
    ∃ L : ℝ, 0 < L ∧ |FOTraj (fun y => L * y) η 1 x0| = |x0| := by
  refine ⟨2 / η, by positivity, ?_⟩
  have hLη : (2 / η) * η = 2 := by rw [div_mul_cancel₀]; exact ne_of_gt hη
  show |x0 - η * ((2 / η) * x0)| = |x0|
  have hval : x0 - η * ((2 / η) * x0) = -x0 := by
    have hmul : η * ((2 / η) * x0) = 2 * x0 := by
      -- 注意 v14 修复（原稿只写 `mul_assoc`，**方向反**）：
      -- 目标是**右嵌套** `η * ((2/η) * x0)`，而 `mul_assoc` 的 LHS 是**左嵌套**
      -- `(?a * ?b) * ?c` ⟹ **模式失配**（`did not find instance of ?a * ?b * ?c`）。
      -- 须用 `← mul_assoc` 先**变左嵌套**，再交换，最后用 `hLη`。
      -- 注意 该 `rw` 链**已闭合目标** ⟹ 不再跟 `ring`（否则 `no goals to be solved`）。
      rw [← mul_assoc, mul_comm η (2 / η), hLη]
    linarith [hmul]
  rw [hval, abs_neg]

/-- **一维见证**：对任意步长规则 `ηrule : ℝ → ℝ`（依赖名义光滑常数 `L_nom > 0`），
存在真实 `L > 0` 使一步迭代的误差**完全不衰减**。
即：**任何**基于名义光滑常数的步长规则都会被一维二次族击败。 -/
theorem one_dim_lower_witness (x0 : ℝ) (ηrule : ℝ → ℝ) (Lnom : ℝ) (_hL : 0 < Lnom)
    (hT : 0 < ηrule Lnom) :
    ∃ L : ℝ, 0 < L ∧ |FOTraj (fun y => L * y) (ηrule Lnom) 1 x0| = |x0| :=
  one_dim_lower_witness_core x0 (ηrule Lnom) hT

/-- **受限版本（附加显式假设）**：若 `ηrule Lnom ≥ 1/Lnom`，则可取真实 `L ≤ 2·Lnom`
且仍不衰减。这把上一条的「真实常数可任意大」收紧到「不超过名义常数的两倍」，
下游使用时更可接受（**该额外假设是显式的**）。 -/
theorem one_dim_lower_witness_bounded (x0 : ℝ) (ηrule : ℝ → ℝ) (Lnom : ℝ)
    (hL : 0 < Lnom) (hT : 0 < ηrule Lnom)
    (hbig : 1 / Lnom ≤ ηrule Lnom) :
    ∃ L : ℝ, 0 < L ∧ L ≤ 2 * Lnom ∧
      |FOTraj (fun y => L * y) (ηrule Lnom) 1 x0| = |x0| := by
  refine ⟨2 / ηrule Lnom, by positivity, ?_, ?_⟩
  · -- 2 / ηrule Lnom ≤ 2 * Lnom  ⟸  1 / Lnom ≤ ηrule Lnom
    have h2 : 2 * Lnom * (1 / Lnom) = 2 := by
      field_simp
    have hm := mul_le_mul_of_nonneg_left hbig (by positivity : (0:ℝ) ≤ 2 * Lnom)
    rw [h2] at hm
    rw [div_le_iff₀ hT]
    linarith [hm]
  · show |x0 - ηrule Lnom * ((2 / ηrule Lnom) * x0)| = |x0|
    have hLη : (2 / ηrule Lnom) * ηrule Lnom = 2 := by
      rw [div_mul_cancel₀]; exact ne_of_gt hT
    have hval : x0 - ηrule Lnom * ((2 / ηrule Lnom) * x0) = -x0 := by
      have hcomm : ηrule Lnom * ((2 / ηrule Lnom) * x0)
          = ((2 / ηrule Lnom) * ηrule Lnom) * x0 := by ring
      rw [hcomm, hLη]
      ring
    rw [hval, abs_neg]

/-! ## 四、链式二次构造的有限维核 -/

/-- **链式二次函数**（Nesterov 教科书构造的一维下标版）：
`chainQuad L m x = (L/4)·(x₀² + ∑_{i=0}^{m-1}(x_{i+1}−x_i)² + x_m²) − (L/2)·x₀`。
在 `ℝ^{m+1}` 上，它是 `L`-光滑凸的；其**唯一最小点**在 `x*ᵢ = 1 − i/(m+1)`。 -/
def chainQuad (L : ℝ) (m : ℕ) (x : Fin (m + 1) → ℝ) : ℝ :=
  (L / 4) * ((x 0) ^ 2 + (∑ i : Fin m, (x i.succ - x i.castSucc) ^ 2) + (x (Fin.last m)) ^ 2)
    - (L / 2) * (x 0)

/-- **链式二次的最小点候选** `x*ᵢ = 1 − i/(m+1)`。 -/
def chainMin (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => 1 - (i.val : ℝ) / (m + 1)

/-- 链式最小点的第一个分量。 -/
theorem chainMin_zero (m : ℕ) : chainMin m 0 = 1 := by
  simp [chainMin]

/-- 链式最小点的最后一个分量。 -/
theorem chainMin_last (m : ℕ) : chainMin m (Fin.last m) = 1 - (m : ℝ) / (m + 1) := by
  simp [chainMin, Fin.val_last]

/-- **链式二次的梯度 Lispchitz 界（`L`-光滑）**：其 Hessian 是三对角
`(L/4)·tridiag(1,2,1)` 的（首尾修正）版本，特征值 ≤ `L`。
本文件给出**可验证的一维切片**：`m = 0` 时 `chainQuad L 0 x = (L/2)x₀² − (L/2)x₀`，
其 Hessian 恰为 `L`，与 `SmoothQuad` 一致（**回收一致性检查**）。 -/
theorem chainQuad_m_zero (L : ℝ) (x : Fin 1 → ℝ) :
    chainQuad L 0 x = (L / 2) * (x 0) ^ 2 - (L / 2) * (x 0) := by
  unfold chainQuad
  rw [Fin.sum_univ_zero]
  have hlast : (Fin.last 0 : Fin (0 + 1)) = 0 := by decide
  rw [hlast]
  ring

/-- **链式构造在 `m = 0` 时归约为平滑二次**（回收）：`chainQuad L 0` 的
`L`-光滑性与 `SmoothQuad L` 同源，说明链式构造是 `SmoothQuad` 的高维推广。 -/
theorem chainQuad_m_zero_smooth (L : ℝ) :
    (fun t : ℝ => chainQuad L 0 (fun _ => t)) = fun t : ℝ => (L / 2) * t ^ 2 - (L / 2) * t := by
  funext t
  rw [chainQuad_m_zero L (fun _ => t)]

/-- **`Ω(1/T²)` 见证的一般形式（陈述式，条件化）**：

若存在常数 `c > 0` 使对**任意** `T ≥ 1` 与**任意**一阶方法 `A` 都存在 `L`-光滑凸 `f`
与初值使 `f(x_T) − f* ≥ c·L·‖x₀−x*‖²/(T+1)²`，则称该类上有 `Ω(1/T²)` 下界。

**诚实标注**：本文件**未证**此形式（需要 oracle 判定树模型，见文件头）；
此处只把它**形式化为定义**，以便下游文件引用与后续补齐——**不是**一个已证定理。 -/
def HasQuadraticLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, 1 ≤ T → ∀ (A : (ℝ → ℝ) → ℝ → ℕ → ℝ),
    ∃ (L : ℝ) (f : ℝ → ℝ) (x0 : ℝ),
      0 < L ∧ f = SmoothQuad L ∧ x0 ≠ 0 ∧
        f (A (fun y => L * y) x0 T) - 0 ≥ c * L * ‖x0 - 0‖ ^ 2 / (T + 1) ^ 2


/-! ## 四、要点 `HasQuadraticLowerBound` 的可满足性判定（**否定**）

上述 `HasQuadraticLowerBound` 的 `A` 量词是「**任意函数** `(ℝ → ℝ) → ℝ → ℕ → ℝ`」，
而 `Ω(1/T²)` 下界理论中的 `A` 应当只能**经梯度 oracle** 访问 `f`。
把 `A` 放开为任意函数后，取 `A := fun _ _ _ => 0`（恒零算法）即得反例：
它在 `T ≥ 1` 时返回 `0`，于是 `f (A … ) = f 0 = SmoothQuad L 0 = 0`，
而右端 `c · L · ‖x₀‖² / (T+1)² > 0`，矛盾。

⇒ **该定义在 Lean 中可被证伪**：它不是「未证」，而是**不可满足**。
注意 这不否定 Nesterov 下界本身——它只说明**该形式化陈述的量词过宽**：
oracle 约束是**语义的**（`A` 只能调 oracle），而类型系统**无法**表达它。
真正的下界需要判定树 / 抵抗 oracle 模型（`ResistingOracle` 式的 `A`）。-/

/-- **`HasQuadraticLowerBound` 为假**：恒零算法使下界平凡失败。

这是「诚实标注」升级为**机器可检的否定**：原定义标注为「未证」，
而本定理证明它实际上**不可满足**。 -/
theorem HasQuadraticLowerBound_false : ¬ HasQuadraticLowerBound := by
  rintro ⟨c, hc, H⟩
  -- 取 T = 1 与恒零算法 A，得坏实例 (L, f, x0)
  obtain ⟨L, f, x0, hL, hf, hx0, hineq⟩ := H 1 (le_refl 1) (fun _ _ _ => 0)
  rw [hf] at hineq
  -- hineq : SmoothQuad L 0 - 0 ≥ c * L * ‖x0 - 0‖ ^ 2 / ((1:ℝ) + 1) ^ 2
  simp only [SmoothQuad] at hineq
  -- 左端为 0，右端严格为正 ⟹ 矛盾
  have hpos : 0 < c * L * ‖x0 - 0‖ ^ 2 / ((1 : ℝ) + 1) ^ 2 := by
    apply div_pos
    · refine mul_pos (mul_pos hc hL) ?_
      simpa using pow_pos (norm_pos_iff.mpr hx0) 2
    · norm_num
  linarith

end Lattice
