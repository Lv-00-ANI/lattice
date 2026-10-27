import Mathlib
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: 黎曼（投影）梯度下降 —— 单位球面 S^{n-1} 上的约束优化

本文件形式化**具体流形**（单位球面）上的黎曼/投影梯度下降：

    S^{n-1} = Metric.sphere (0 : E) 1,   E 为实内积空间（具体实例：EuclideanSpace ℝ (Fin n)）

核心对象：

  1. `projSphere`：径向投影（归一化）P(x) = ‖x‖⁻¹ • x；
     证明 `projSphere_norm`：x ≠ 0 ⟹ ‖P(x)‖ = 1（P 的像在单位球面上），
     由此 `projSphere_mem_sphere`：P(x) ∈ Metric.sphere 0 1；
     `projSphere_idempotent`：P ∘ P = P（x ≠ 0）；`projSphere_smul`：正数伸缩不变；
     `projSphere_inner_eq_norm`：⟨x, P(x)⟩ = ‖x‖（故 ⟨x, P(x)⟩ ≥ 0，P(x) 与 x「同侧」）。
  2. `gradStep`：欧氏（提升）梯度步 x ↦ x − η·grad x；
     `sphereGD`：球面投影梯度步 x ↦ P(x − η·grad x)。
  3. `sphereGD_norm` / `sphereGD_mem_sphere`（**保约束，真证**）：‖x‖ = 1 且
     gradStep … ≠ 0 时 ‖sphereGD … x‖ = 1，即一步之后仍落在球面上（可行性保持）。
  4. **下降引理**：
     - `gradStep_descent_lemma`（**真证，无额外几何假设**）：L-光滑下欧氏步的下降
       f(x⁺) ≤ f(x) − η·(1 − Lη/2)·‖grad x‖²；
     - `sphereGD_descent_lemma`（**条件版，降级**）：球面步的下降
       f(x_{k+1}) ≤ f(x_k) − (η/2)·‖grad x_k‖²，
       其中「投影步 ≤ η·‖grad‖」与「梯度对齐 ⟨grad, x⁺−x⟩ ≤ −η‖grad‖²」
       作为**显式假设**给出（见「诚实边界」）。
  5. **收敛（真证）**：`grad_partial_sum_le`、`summable_grad_sq`（∑‖grad‖² 可和且有界）、
     `grad_tendsto_zero`（‖grad x_k‖ → 0，即收敛到临界点）、
     `min_grad_rate`（O(1/T) 率：存在 k < T 使 ‖grad x_k‖² ≤ (f(x₀)−f*) / (c·T)）、
     `sphereGD_sq_sum_bound`（把下降引理与可和性串起来）。
  6. `tangentSpace`：切空间 {v | ⟨x, v⟩ = 0} 与 `tangentSpace_smul`（切空间对伸缩封闭）。

**诚实边界**（本文件不证 / 不声称的，用「诚实/未证/未做/降级/标注」明示）：

- **B21 已做（`hretr`/`halign` 从 `projSphere` 推出，结论是「一真一假」）**：
  设 `‖x‖ = 1`、`⟨x,g⟩ = 0`（`g` 为黎曼梯度）、`s := ‖x − ηg‖`。
  · **`hretr` 可推出且为真**：`sphereGD_retr_bound` 证 `‖x⁺ − x‖ ≤ η‖g‖`；
  · **`halign` 按原陈述为假**：`sphereGD_align_eq` 给出**精确等式**
    `⟨g, x⁺−x⟩ = −(η/s)‖g‖²`，而 `s ≥ 1` 使 `η/s ≤ η`，故
    `−(η/s)‖g‖² ≥ −η‖g‖²`——**与原假设方向相反**，`halign` 恒不成立（除 `η‖g‖ = 0`）。
    数值见证 `x=(1,0)`、`g=(0,1)`、`η=1/2`：`−0.4472… > −0.5`；
    `halign_counterexample` 把该反例写成内核可验证的定理。
  故 `sphereGD_descent_lemma` 作为**条件命题仍然成立**（假设为假时命题空洞为真），
  但它**不能**被"从 `projSphere` 推出"——它的 `halign` 假设在此几何下不可满足。
  这解释了原文件为何把它标为「降级」：**不是缺工具，而是原假设与几何不符**。
- **未做**：一般黎曼流形（指数映射 / 收缩映射 / 黎曼梯度的抽象框架）、
  球面测地线步（γ(η) = cos η·x + sin η·v）与指数映射版本、非光滑 / 随机版本、
  以及「从投影算子推出切投影关系」这一步。
- **诚实**：欧氏步的常数取 η·(1 − Lη/2)（精确值）；球面条件版取**更保守**的 η/2：
  在 L·η ≤ 1/2 下 η·(1 − Lη/2) ≥ 3η/4 > η/2，故 η·(1 − Lη/2) 才是更**紧**（更强）的
  下降常数，η/2 只是它的**弱化**形式；本文件不追求该更紧的常数，只用 η/2
  （`step_descent_lemma` 的结论即固定为 η/2）。
- **诚实**：`sphereGD_norm` / `sphereGD_mem_sphere` 中的假设 ‖x‖ = 1 实际未被使用
  （径向投影的保范性只需 gradStep ≠ 0），保留它是为了与「从球面出发」的语义一致。
- `EuclideanSpace ℝ (Fin n)` 的实例：`euclidean_sphereGD_mem_sphere`（n = 2 即 S¹）。 -/

noncomputable section

open Filter

open scoped Topology

/-! 注意：**Q3B2 修复（必须保留此 `open scoped`）**：`RealRiemannianGD` 曾**从未编译成功**
（探针实测 `exit 1`、8 个 `: error:`，全部集中在 B21 一节）。
根因是 `inner` 的**语法**：`inner` 是类型类 `Inner (𝕜 E)` 的**字段**
（`Mathlib/Analysis/InnerProductSpace/Basic.lean:78`），其标量域 `𝕜` 是**隐式参数**；
而 `InnerProductSpace ℝ E` **不注册**一般的 `Inner ℝ E` 实例
（全 mathlib grep 只有 Quaternion 与 l2Space 有）。故裸写 `inner x g` 时
Lean 把 `𝕜` 与**第一个实参** `x` 统一，报
`failed to synthesize Inner ℕ E`（`x` 被当成 `ℕ`）。
⭐ **修法**：`open scoped RealInnerProductSpace` 引入**显式带标量的记法 `⟪x, y⟫`**
（`Basic.lean:90`），把全部 `inner x y` 改写为 `⟪x, y⟫`。
注意：该 `open scoped` **只提供记法、不提供实例** ——
光加上它而仍写裸 `inner x g` 依然失败（Q3B2 实测）。
**依据**：`PROCESS.md §4.4` / `B214`（先 grep 源码，源码写的是什么就是什么）。 -/

open scoped RealInnerProductSpace

namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 第一节：球面与径向投影 -/

/-- 单位球面（带中心 0 与半径 1 的度量球面）：S = Metric.sphere 0 1。 -/
def unitSphere (F : Type*) [NormedAddCommGroup F] : Set F := Metric.sphere (0 : F) 1

/-- 径向投影（归一化）：P(x) = ‖x‖⁻¹ • x。 -/
def projSphere (x : E) : E := (‖x‖)⁻¹ • x

/-- 径向投影的保范性：x ≠ 0 ⟹ ‖P(x)‖ = 1。 -/
theorem projSphere_norm (x : E) (hx : x ≠ 0) : ‖projSphere x‖ = 1 := by
  have hx0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  unfold projSphere
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ (ne_of_gt hx0)

/-- 径向投影的值落在单位球面上：x ≠ 0 ⟹ P(x) ∈ Metric.sphere 0 1。 -/
theorem projSphere_mem_sphere (x : E) (hx : x ≠ 0) :
    projSphere x ∈ Metric.sphere (0 : E) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  exact projSphere_norm x hx

/-- 径向投影幂等：x ≠ 0 ⟹ P(P(x)) = P(x)。 -/
theorem projSphere_idempotent (x : E) (hx : x ≠ 0) :
    projSphere (projSphere x) = projSphere x := by
  show (‖projSphere x‖)⁻¹ • projSphere x = projSphere x
  rw [projSphere_norm x hx]
  simp

/-- 正数伸缩下径向投影不变：c > 0 ⟹ P(c • x) = P(x)。 -/
theorem projSphere_smul (x : E) (c : ℝ) (hc : 0 < c) :
    projSphere (c • x) = projSphere x := by
  have hcne : c ≠ 0 := ne_of_gt hc
  unfold projSphere
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  congr 1
  calc
    (c * ‖x‖)⁻¹ * c = c⁻¹ * ‖x‖⁻¹ * c := by rw [mul_inv_rev]; ring
    _ = c⁻¹ * c * ‖x‖⁻¹ := by ring
    _ = 1 * ‖x‖⁻¹ := by rw [inv_mul_cancel₀ hcne]
    _ = ‖x‖⁻¹ := by ring

/-- 投影与原点同侧（定量版）：⟨x, P(x)⟩ = ‖x‖。 -/
theorem projSphere_inner_eq_norm (x : E) : inner x (projSphere x) = ‖x‖ := by
  by_cases hx : x = 0
  · subst hx
    simp [projSphere]
  · have hx0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    unfold projSphere
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    calc
      (‖x‖)⁻¹ * ‖x‖ ^ 2 = (‖x‖)⁻¹ * ‖x‖ * ‖x‖ := by ring
      _ = 1 * ‖x‖ := by rw [inv_mul_cancel₀ (ne_of_gt hx0)]
      _ = ‖x‖ := by ring

/-- 投影与原点同侧（非负版）：0 ≤ ⟨x, P(x)⟩。 -/
theorem projSphere_inner_nonneg (x : E) : (0 : ℝ) ≤ inner x (projSphere x) := by
  rw [projSphere_inner_eq_norm]
  exact norm_nonneg x

/-! ## 第二节：欧氏梯度步与球面投影梯度步 -/

/-- 欧氏（提升）梯度步：x ↦ x − η·grad x。 -/
def gradStep (eta : ℝ) (grad : E → E) (x : E) : E := x - eta • grad x

/-- 球面投影梯度（黎曼）步：x ↦ P(x − η·grad x)（先走欧氏步，再径向投影回球面）。 -/
def sphereGD (eta : ℝ) (grad : E → E) (x : E) : E := projSphere (gradStep eta grad x)

/-- **保约束**：从单位球面出发（‖x‖ = 1）、非退化（gradStep ≠ 0）时，
球面梯度步之后仍在单位球面上。 -/
theorem sphereGD_norm (eta : ℝ) (grad : E → E) (x : E) (_hx : ‖x‖ = 1)
    (hne : gradStep eta grad x ≠ 0) : ‖sphereGD eta grad x‖ = 1 :=
  projSphere_norm (gradStep eta grad x) hne

/-- **保约束（集合版）**：‖x‖ = 1 且 gradStep ≠ 0 ⟹ sphereGD … x ∈ Metric.sphere 0 1。 -/
theorem sphereGD_mem_sphere (eta : ℝ) (grad : E → E) (x : E) (hx : ‖x‖ = 1)
    (hne : gradStep eta grad x ≠ 0) :
    sphereGD eta grad x ∈ Metric.sphere (0 : E) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  exact sphereGD_norm eta grad x hx hne

/-- **保约束（unitSphere 版）**：与 `sphereGD_mem_sphere` 相同的命题，
用本文件定义的 `unitSphere` 表述。 -/
theorem sphereGD_mem_unitSphere (eta : ℝ) (grad : E → E) (x : E) (hx : ‖x‖ = 1)
    (hne : gradStep eta grad x ≠ 0) : sphereGD eta grad x ∈ unitSphere E :=
  sphereGD_mem_sphere eta grad x hx hne

/-! ## 第三节：下降引理 -/

/-! ### 三-0、B21：`hretr` 与 `halign` **真的能从 `projSphere` 推出**吗？

ROADMAP 的 B21 要求把 `sphereGD_descent_lemma` 的 `hretr`/`halign`
从 `projSphere` 的表达式推出。**代入检验的结论是：两条假设的真值不同。**

设 `‖x‖ = 1`、`⟨x, g⟩ = 0`（`g` 是**黎曼**梯度，切于球面）、`s := ‖x − ηg‖ = √(1 + η²‖g‖²)`。
记 `x⁺ := projSphere (x − ηg) = s⁻¹ • (x − ηg)`，则

    x⁺ − x = (s⁻¹ − 1) • x − (η·s⁻¹) • g 。

**（一）`hretr` 成立**：`‖x⁺ − x‖² = (s⁻¹−1)² + η²‖g‖²s⁻²`，可证 `≤ η²‖g‖²`
（即 `‖x⁺−x‖ ≤ η‖g‖`）。见 `sphereGD_retr_bound`。

**（二）`halign` 按原陈述为假**：由 `⟨x, g⟩ = 0` 得**等式**

    ⟨g, x⁺ − x⟩ = −(η / s)·‖g‖² ，

而原假设要求 `⟨g, x⁺−x⟩ ≤ −η‖g‖²`。由于 `s = √(1+η²‖g‖²) ≥ 1`，有 `η/s ≤ η`，
故 `−(η/s)‖g‖² ≥ −η‖g‖²`——**方向相反**，原假设**恒不成立**（除非 `η‖g‖ = 0`）。

数值见证：`x = (1,0)`、`g = (0,1)`、`η = 1/2` ⟹ `s = √1.25 ≈ 1.1180`，
`⟨g, x⁺−x⟩ = −0.447214…`，而 `−η‖g‖² = −0.5`，故 `−0.447 > −0.5`，**`halign` 假**。

下面的 `halign_counterexample` 把这一反例写成内核可验证的定理
（在 `EuclideanSpace ℝ (Fin 2)` 上，用 `Fin 2` 的两个坐标显式给出）。

**（三）正确的替代假设**：把 `halign` 换成**等式**
`⟨g, x⁺−x⟩ = −(η/s)‖g‖²`（`sphereGD_align_eq`），
或换成**弱不等式** `⟨g, x⁺−x⟩ ≤ −(η/(1+η²‖g‖²))·‖g‖² = −η‖g‖²/s²`。
**注意**：换成弱不等式后，`step_descent_lemma` 原有的证明**不再适用**
（它需要 `≤ −η‖g‖²` 才能得到 `f x' ≤ f x − (η/2)‖g‖²`）；
故本文件把 `sphereGD_descent_lemma` 的**条件版保留原状**（作为条件命题仍然成立）。
替代定理（用**真实可得**的对齐等式，结论相应减弱为
`f x' ≤ f x − (η/s)‖g‖² + (L/2)η²‖g‖²`，
即下降量自动带 `s⁻¹` 因子、仍为负当 `η` 足够小）
**本文件未落地**——`sphereGD_descent_lemma_true` 并未在本文件中定义，
它属**未做项**（本文件第五节之后即进入第六节 `euclidean_sphereGD_mem_sphere`）。 -/

/-- **欧氏步下降引理（真证，无额外几何假设）**。
L-光滑：f(y) ≤ f(x) + ⟨grad x, y − x⟩ + (L/2)‖y − x‖²。
取 y = gradStep η grad x = x − η·grad x，则
f(y) ≤ f(x) − η·(1 − Lη/2)·‖grad x‖²。 -/
theorem gradStep_descent_lemma (f : E → ℝ) (grad : E → E) (L eta : ℝ) (x : E)
    (hsmooth : f (gradStep eta grad x) ≤ f x
      + inner (grad x) (gradStep eta grad x - x)
      + (L / 2) * ‖gradStep eta grad x - x‖ ^ 2)
    (heta : 0 < eta) :
    f (gradStep eta grad x) ≤ f x - eta * (1 - L * eta / 2) * ‖grad x‖ ^ 2 := by
  have hdiff : gradStep eta grad x - x = -(eta • grad x) := by
    unfold gradStep
    abel
  have hinner : inner (grad x) (gradStep eta grad x - x) = -(eta * ‖grad x‖ ^ 2) := by
    rw [hdiff, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have hnorm : ‖gradStep eta grad x - x‖ ^ 2 = eta ^ 2 * ‖grad x‖ ^ 2 := by
    rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos heta]
    ring
  rw [hinner, hnorm] at hsmooth
  nlinarith [hsmooth, sq_nonneg ‖grad x‖, heta]

/-- **B21 正结果（`hretr` 可推出）**：设 `‖x‖ = 1`、`⟨x,g⟩ = 0`、`η ≥ 0`，则

    ‖sphereGD η g x − x‖ ≤ η·‖g‖ 。

证明：`s := ‖x − ηg‖ = √(1+η²‖g‖²)`（由 `⟨x,g⟩=0`），
`x⁺ − x = (s⁻¹−1)x − ηs⁻¹g`，两向量正交，故
`‖x⁺−x‖² = (s⁻¹−1)² + η²‖g‖²s⁻² ≤ η²‖g‖²`
（等价于 `s − 1 ≤ η‖g‖`，由 `s = √(1+η²‖g‖²) ≤ 1 + η‖g‖` 得）。 -/
theorem sphereGD_retr_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g x : E) (η : ℝ) (hx : ‖x‖ = 1) (horth : ⟪x, g⟫ = 0) (hη : 0 ≤ η) :
    ‖sphereGD η (fun _ => g) x - x‖ ≤ η * ‖g‖ := by
  set u : E := x - η • g with hu
  -- `‖u‖² = 1 + η²‖g‖²`
  have hsq : ‖u‖ ^ 2 = 1 + η ^ 2 * ‖g‖ ^ 2 := by
    -- 展开 `u = x − η•g`，用 `norm_sub_sq_real` 得
    -- `‖u‖² = ‖x‖² − 2⟪x, η•g⟫ + ‖η•g‖²`，再 `real_inner_smul_right` +
    -- `norm_smul` 把 η 提出来，最后 `horth`/`hx` 消去。
    rw [hu, norm_sub_sq_real, real_inner_smul_right, horth, hx, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hη]
    ring
  have hupos : (0 : ℝ) < ‖u‖ := by
    rw [norm_pos_iff]
    intro h0
    have : ‖u‖ = 0 := by rw [h0, norm_zero]
    rw [this] at hsq
    nlinarith [sq_nonneg η, sq_nonneg ‖g‖]
  -- 位移分解：`x⁺ − x = (‖u‖⁻¹−1)•x − (η‖u‖⁻¹)•g`
  have hxm : sphereGD η (fun _ => g) x - x = (‖u‖⁻¹ - 1) • x - (η * ‖u‖⁻¹) • g := by
    unfold sphereGD projSphere gradStep
    simp only [hu]
    module
  -- 只需证 `‖…‖ ≤ η‖g‖`；两边平方（两侧非负，用 `sq_le_sq` 的 `abs` 形式）
  rw [hxm]
  have hgoal2 : ‖(‖u‖⁻¹ - 1) • x - (η * ‖u‖⁻¹) • g‖ ^ 2 ≤ (η * ‖g‖) ^ 2 := by
    -- 上界方向：两边平方
    have hperp : ⟪(‖u‖⁻¹ - 1) • x, (η * ‖u‖⁻¹) • g⟫ = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, horth]; ring
    have hnorm2 : ‖(‖u‖⁻¹ - 1) • x - (η * ‖u‖⁻¹) • g‖ ^ 2
        = (‖u‖⁻¹ - 1) ^ 2 * ‖x‖ ^ 2 + (η * ‖u‖⁻¹) ^ 2 * ‖g‖ ^ 2 := by
      rw [norm_sub_sq_real, hperp, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    -- `‖x‖² = 1`（由 `hx : ‖x‖ = 1`）
    have hx2 : ‖x‖ ^ 2 = 1 := by rw [hx]; norm_num
    rw [hnorm2, hx2, mul_one]
    have huR : ‖u‖ ^ 2 = 1 + η ^ 2 * ‖g‖ ^ 2 := hsq
    have hgnn : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
    -- 通分：`(s⁻¹−1)² + (ηs⁻¹)²‖g‖² = (2s(s−1))/s²`，再证 `≤ (η‖g‖)²`
    have hsne : ‖u‖ ≠ 0 := ne_of_gt hupos
    have key : (‖u‖⁻¹ - 1) ^ 2 + (η * ‖u‖⁻¹) ^ 2 * ‖g‖ ^ 2
        = 2 * (‖u‖ - 1) / ‖u‖ := by
      field_simp
      nlinarith [huR]
    rw [key, div_le_iff₀ hupos]
    -- `2(s−1) ≤ (η‖g‖)²·s`
    nlinarith [huR, hupos, hgnn, hη, sq_nonneg (η * ‖g‖), sq_nonneg (‖u‖ - 1)]
  -- 从平方回到范数不等式：`‖v‖² ≤ (η‖g‖)²` 且两侧非负 ⟹ `‖v‖ ≤ η‖g‖`
  have hRhs : (0 : ℝ) ≤ η * ‖g‖ := mul_nonneg hη (norm_nonneg g)
  nlinarith [hgoal2, norm_nonneg ((‖u‖⁻¹ - 1) • x - (η * ‖u‖⁻¹) • g), hRhs,
    sq_nonneg (‖(‖u‖⁻¹ - 1) • x - (η * ‖u‖⁻¹) • g‖ - η * ‖g‖)]

/-- **B21 关键恒等式（对齐的精确值）**：设 `‖x‖ = 1`、`⟨x,g⟩ = 0`，则

    ⟨g, sphereGD η g x − x⟩ = −(η / ‖x − ηg‖)·‖g‖² 。

证明：`x⁺−x = (s⁻¹−1)x − ηs⁻¹g`（`s := ‖x−ηg‖`），
用 `⟨g,x⟩ = 0` 与 `⟨g,g⟩ = ‖g‖²` 展开即得。

**这是 `halign` 的正确版本**：原假设 `≤ −η‖g‖²` 差了一个因子 `s⁻¹`
（`s = √(1+η²‖g‖²) ≥ 1`，故真实值**不小于** `−η‖g‖²`）。 -/
theorem sphereGD_align_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g x : E) (η : ℝ) (horth : ⟪x, g⟫ = 0) :
    ⟪g, sphereGD η (fun _ => g) x - x⟫
      = -(η / ‖x - η • g‖) * ‖g‖ ^ 2 := by
  have hxm : sphereGD η (fun _ => g) x - x
      = (‖x - η • g‖⁻¹ - 1) • x - (η * ‖x - η • g‖⁻¹) • g := by
    unfold sphereGD projSphere gradStep
    module
  rw [hxm, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_comm x g, horth, real_inner_self_eq_norm_sq]
  ring

/-- **B21 反例（机器验证）：`halign` 按原陈述为假**。
取 `x = (1,0)`、`g = (0,1)`（`⟨x,g⟩ = 0`、`‖x‖ = 1`）、`η = 1/2`，则
`⟨g, x⁺ − x⟩ = −(η/s)‖g‖²` 且 `s = √(1+η²) > 1`，故
`⟨g, x⁺−x⟩ = −0.4472… > −0.5 = −η‖g‖²`——**`halign` 不成立**。

本定理在 `EuclideanSpace ℝ (Fin 2)` 上以显式坐标给出该反例。

注意：**Q3B2 重写说明（原实现从未编译）**：原实现有 **6 处**编译错误（探针实测），
已全部修复：
(i) 裸写 `inner x g`（见文件头 `open scoped RealInnerProductSpace` 的说明）；
(ii) `EuclideanSpace ℝ (Fin 2)` 的**逐点 λ 写法**无法被当成 `EuclideanSpace`
    的元素（`invalid constructor ⟨...⟩`）；
(iii) ⭐ **`![1, 0]` 矩阵记法在本文件的 `simp only` 集合下不可化约**——
    `EuclideanSpace.norm_eq` 不产生 `simp only` 期待的 `‖?x‖` 可匹配形态
    （实测 `tactic 'rewrite' failed … ‖?x‖`）；
(iv) `simp [EuclideanSpace.single]` 会**递归爆栈**（`maximum recursion depth`）。
⭐ **改用 `EuclideanSpace.single i a` 作为基向量**，全程走
`EuclideanSpace.norm_single` / `EuclideanSpace.inner_single_left` / `EuclideanSpace.single_apply`
（三者均已实测可用），**不再依赖 `![…]` 与 `Ei`-范数的 `simp` 归一化**。
（本文件已在别处用过 `![1, 0]` 记法，但那里不涉及 `norm`/`inner` 的化约。） -/
theorem halign_counterexample :
    ∃ (x g : EuclideanSpace ℝ (Fin 2)) (η : ℝ),
      ‖x‖ = 1 ∧ ⟪x, g⟫ = 0 ∧
      ¬ (⟪g, sphereGD η (fun _ => g) x - x⟫ ≤ -η * ‖g‖ ^ 2) := by
  -- 基向量：`x = e₀`、`g = e₁`（`EuclideanSpace.single 0 1` / `single 1 1`）。
  set x : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (1 : ℝ) with hx_def
  set g : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ) with hg_def
  refine ⟨x, g, (1 / 2 : ℝ), ?_, ?_, ?_⟩
  · -- `‖x‖ = 1`
    rw [hx_def, EuclideanSpace.norm_single]
    norm_num
  · -- `⟪x, g⟫ = 0`
    rw [hx_def, hg_def, EuclideanSpace.inner_single_left]
    simp [EuclideanSpace.single_apply]
  · -- 用 `sphereGD_align_eq` 把左边化成 `−(η/s)‖g‖²`，再判 `s > 1`
    intro hcon
    have hode : ⟪x, g⟫ = (0 : ℝ) := by
      rw [hx_def, hg_def, EuclideanSpace.inner_single_left]
      simp [EuclideanSpace.single_apply]
    have hal := sphereGD_align_eq (E := EuclideanSpace ℝ (Fin 2)) g x (1 / 2 : ℝ) hode
    rw [hal] at hcon
    -- `‖g‖² = 1`
    have hg2 : ‖g‖ ^ 2 = 1 := by
      rw [hg_def, EuclideanSpace.norm_single]
      norm_num
    -- 注意：`set` 会把目标与上下文中的 `‖x − ½g‖` **整体替换**成 `s`，
    -- 故此后一切都在 `s` 上进行，**不要**再试图 `rw` 回 `‖x − ½g‖`（实测失败）。
    set s : ℝ := ‖x - (1 / 2 : ℝ) • g‖ with hs
    -- `s² = 5/4`：由 `hs : s = ‖x − ½g‖` 单向改写，再算原始形态。
    have hs2 : s ^ 2 = 5 / 4 := by
      rw [hs]
      rw [norm_sub_sq_real, real_inner_smul_right, hx_def, hg_def,
        EuclideanSpace.inner_single_left, norm_smul, EuclideanSpace.norm_single,
        EuclideanSpace.norm_single, Real.norm_eq_abs]
      simp only [EuclideanSpace.single_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        ↓reduceIte, mul_one, mul_zero, RCLike.star_def, star_trivial, abs_of_pos]
      norm_num
    have hspos : 0 < s := by
      -- `s > 0`：`s² = 5/4 ≠ 0` 排除 `s = 0`；又 `s` 是范数故 `s ≥ 0`。
      have hsne0 : s ≠ 0 := by
        intro h0
        rw [h0] at hs2
        norm_num at hs2
      exact lt_of_le_of_ne (by positivity) (Ne.symm hsne0)
    have hs1 : 1 < s := by nlinarith [hs2, hspos, sq_nonneg (s - 1)]
    -- `hcon` 已在 `s` 上：`-(1/2/s) * ‖g‖² ≤ -(1/2) * ‖g‖²`；用 `hg2` 消去 `‖g‖²`
    rw [hg2, mul_one] at hcon
    -- 注意解析：`-(1/2)/s` 被 Lean 读作 `-((1/2)/s)`，而 `hcon` 里是 `-(1/2/s)`
    --   ——两者 defeq 但**句法不同**，`rw` 用句法匹配故失败（PROCESS.md 判据 7）。
    --   故直接用 `nlinarith` 配合 `field_simp` 消去除法，而不是试图 `rw` 形状。
    have hsne : s ≠ 0 := ne_of_gt hspos
    have key : (1 / 2 : ℝ) ≤ 1 / (2 * s) := by
      have : -(1 / 2 / s) = -(1 / (2 * s)) := by ring
      rw [this] at hcon
      linarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)] at key
    nlinarith [key, hs1]

/-- **抽象收缩步下降引理（真证）**：给定 L-光滑、收缩步长界与梯度对齐（两者为**显式假设**），
在 L·η ≤ 1/2 下得到 f(x') ≤ f(x) − (η/2)·‖g‖²。 -/
theorem step_descent_lemma (f : E → ℝ) (g x x' : E) (L eta : ℝ)
    (hsmooth : f x' ≤ f x + ⟪g, x' - x⟫ + (L / 2) * ‖x' - x‖ ^ 2)
    (hretr : ‖x' - x‖ ≤ eta * ‖g‖)
    (halign : ⟪g, x' - x⟫ ≤ -eta * ‖g‖ ^ 2)
    (heta : 0 < eta) (hL : 0 ≤ L) (hLeta : L * eta ≤ 1 / 2) :
    f x' ≤ f x - (eta / 2) * ‖g‖ ^ 2 := by
  have hgnn : 0 ≤ ‖g‖ := norm_nonneg g
  have hsq : ‖x' - x‖ ^ 2 ≤ (eta * ‖g‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg (x' - x)) hretr 2
  have hL2 : 0 ≤ L / 2 := by linarith
  have hsm2 : (L / 2) * ‖x' - x‖ ^ 2 ≤ (L / 2) * (eta * ‖g‖) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hL2
  have h1 : f x' ≤ f x + ⟪g, x' - x⟫ + (L / 2) * (eta * ‖g‖) ^ 2 :=
    le_trans hsmooth (add_le_add_left hsm2 _)
  have hprod : L * eta * (eta * ‖g‖ ^ 2) ≤ (1 / 2) * (eta * ‖g‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hLeta (mul_nonneg (le_of_lt heta) (sq_nonneg ‖g‖))
  have h2 : f x + inner g (x' - x) + (L / 2) * (eta * ‖g‖) ^ 2
      ≤ f x - (eta / 2) * ‖g‖ ^ 2 := by
    nlinarith [halign, hprod, sq_nonneg ‖g‖, heta, hL, hLeta, hgnn,
      mul_nonneg (le_of_lt heta) hgnn]
  linarith

/-- **球面投影梯度步的下降引理（条件版 / 降级）**。
真实证明中的两条几何事实作为**显式假设**：
  · `hretr`：一步的位移不超过 η·‖grad‖；
  · `halign`：梯度与位移对齐（≤ −η‖grad‖²）。
详见文件头「诚实边界」。 -/
theorem sphereGD_descent_lemma (f : E → ℝ) (grad : E → E) (L eta : ℝ) (x : ℕ → E) (k : ℕ)
    (hstep : x (k + 1) = sphereGD eta grad (x k))
    (hsmooth : f (x (k + 1)) ≤ f (x k) + ⟪grad (x k), x (k + 1) - x k⟫
      + (L / 2) * ‖x (k + 1) - x k‖ ^ 2)
    (hretr : ‖x (k + 1) - x k‖ ≤ eta * ‖grad (x k)‖)
    (halign : ⟪grad (x k), x (k + 1) - x k⟫ ≤ -eta * ‖grad (x k)‖ ^ 2)
    (heta : 0 < eta) (hL : 0 ≤ L) (hLeta : L * eta ≤ 1 / 2) :
    f (x (k + 1)) ≤ f (x k) - (eta / 2) * ‖grad (x k)‖ ^ 2 := by
  rw [hstep] at hsmooth hretr halign ⊢
  exact step_descent_lemma f (grad (x k)) (x k) (sphereGD eta grad (x k)) L eta
    hsmooth hretr halign heta hL hLeta

/-! ## 第四节：收敛到临界点 -/

omit [InnerProductSpace ℝ E] in
/-- 部分和上界：沿下降序列，∑_{k<T} ‖grad x_k‖² ≤ (f(x₀) − f*)/c。
证明：望远镜求和 c·∑a_k ≤ ∑(f(x_k) − f(x_{k+1})) = f(x₀) − f(x_T) ≤ f(x₀) − f*。

注意：**Q3B2**：Lean 报告 section 变量 `[InnerProductSpace ℝ E]` 在本定理中**未被使用**
（本引理只用范数，不用内积）⟹ 按 Lean 的建议 `omit` 掉，消除该 warning。 -/
theorem grad_partial_sum_le (f : E → ℝ) (grad : E → E) (x : ℕ → E) (fstar c : ℝ)
    (hc : 0 < c) (hdesc : ∀ k, f (x (k + 1)) + c * ‖grad (x k)‖ ^ 2 ≤ f (x k))
    (hbdd : ∀ k, fstar ≤ f (x k)) (T : ℕ) :
    ∑ k in Finset.range T, ‖grad (x k)‖ ^ 2 ≤ (f (x 0) - fstar) / c := by
  have htel : c * (∑ k in Finset.range T, ‖grad (x k)‖ ^ 2) ≤ f (x 0) - f (x T) := by
    induction T with
    | zero => simp
    | succ T ih =>
        have hk := hdesc T
        rw [Finset.sum_range_succ, mul_add]
        calc
          c * (∑ k in Finset.range T, ‖grad (x k)‖ ^ 2) + c * ‖grad (x T)‖ ^ 2
              ≤ (f (x 0) - f (x T)) + (f (x T) - f (x (T + 1))) := by
                exact add_le_add ih (by linarith)
          _ = f (x 0) - f (x (T + 1)) := by ring
  have hb := hbdd T
  rw [le_div_iff₀ hc]
  linarith

omit [InnerProductSpace ℝ E] in
/-- 🎯 **∑‖grad x_k‖² 可和且有界**：若沿序列每步下降
f(x_{k+1}) + c·‖grad x_k‖² ≤ f(x_k) 且 f 有下界 f*，则
∑' ‖grad x_k‖² ≤ (f(x₀) − f*)/c，特别地该级数可和。

注意：**Q3B2**：`omit [InnerProductSpace ℝ E]`（Lean 报告该 section 变量在本定理中未使用）。 -/
theorem summable_grad_sq (f : E → ℝ) (grad : E → E) (x : ℕ → E) (fstar c : ℝ)
    (hc : 0 < c) (hdesc : ∀ k, f (x (k + 1)) + c * ‖grad (x k)‖ ^ 2 ≤ f (x k))
    (hbdd : ∀ k, fstar ≤ f (x k)) :
    Summable (fun k => ‖grad (x k)‖ ^ 2) ∧
      ∑' k, ‖grad (x k)‖ ^ 2 ≤ (f (x 0) - fstar) / c := by
  have hnonneg : ∀ k, 0 ≤ ‖grad (x k)‖ ^ 2 := fun k => sq_nonneg _
  have hpart : ∀ T, ∑ k in Finset.range T, ‖grad (x k)‖ ^ 2 ≤ (f (x 0) - fstar) / c :=
    fun T => grad_partial_sum_le f grad x fstar c hc hdesc hbdd T
  have hsum : Summable (fun k => ‖grad (x k)‖ ^ 2) :=
    summable_of_sum_range_le hnonneg hpart
  exact ⟨hsum, tsum_le_of_sum_range_le hsum hpart⟩

omit [InnerProductSpace ℝ E] in
/-- 🎯 **收敛到临界点**：在 `summable_grad_sq` 的假设下，‖grad x_k‖ → 0
（即迭代序列的梯度范数趋于 0；步长序列的任何聚点都是临界点）。

注意：**Q3B2**：`omit [InnerProductSpace ℝ E]`（Lean 报告该 section 变量在本定理中未使用）。 -/
theorem grad_tendsto_zero (f : E → ℝ) (grad : E → E) (x : ℕ → E) (fstar c : ℝ)
    (hc : 0 < c) (hdesc : ∀ k, f (x (k + 1)) + c * ‖grad (x k)‖ ^ 2 ≤ f (x k))
    (hbdd : ∀ k, fstar ≤ f (x k)) :
    Tendsto (fun k => ‖grad (x k)‖) atTop (𝓝 0) := by
  have hs := (summable_grad_sq f grad x fstar c hc hdesc hbdd).1
  have h2 : Tendsto (fun k => Real.sqrt (‖grad (x k)‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    hs.tendsto_atTop_zero.sqrt
  simpa [Real.sqrt_sq, Real.sqrt_zero] using h2

/-- 辅助引理（最小值 ≤ 平均值）：∑_{k<T} a k ≤ B 且 T > 0 ⟹ ∃ k < T, a k ≤ B/T。
反证：若所有项都 > B/T，则和 > T·(B/T) = B，矛盾。 -/
theorem exists_le_of_sum_range_le {a : ℕ → ℝ} {T : ℕ} {B : ℝ} (hT : 0 < T)
    (h : ∑ k in Finset.range T, a k ≤ B) : ∃ k, k < T ∧ a k ≤ B / T := by
  by_contra hc
  push_neg at hc
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  obtain ⟨k0, hk0⟩ := Finset.nonempty_range_iff.mpr (ne_of_gt hT)
  have hlt : (∑ _k in Finset.range T, B / T) < ∑ k in Finset.range T, a k :=
    Finset.sum_lt_sum (fun k hk => le_of_lt (hc k (Finset.mem_range.mp hk)))
      ⟨k0, hk0, hc k0 (Finset.mem_range.mp hk0)⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hBT : (T : ℝ) * (B / T) = B := by
    field_simp
  rw [hBT] at hlt
  linarith

omit [InnerProductSpace ℝ E] in
/-- 🎯 **O(1/T) 收敛率**：存在 k < T 使 ‖grad x_k‖² ≤ (f(x₀) − f*)/(c·T)。
由部分和上界与「最小值 ≤ 平均值」（`exists_le_of_sum_range_le`）得到。

注意：**Q3B2**：`omit [InnerProductSpace ℝ E]`（Lean 报告该 section 变量在本定理中未使用）。
注意：另注：`_h0 : fstar ≤ f (x 0)` **下划线命名 = 有意不用**——
真正的下界由 `hbdd 0` 提供（`hbdd` 更强，`h0` 是其特例），故 `_h0` **冗余**；
保留（而非删除）是为了**不破坏调用点的按位置传参**（同 `RealDistillGeneralization`
`distill_excess_from_layer` 的处置原则）。 -/
theorem min_grad_rate (f : E → ℝ) (grad : E → E) (x : ℕ → E) (fstar c : ℝ) (T : ℕ)
    (hc : 0 < c) (hT : 0 < T) (_h0 : fstar ≤ f (x 0))
    (hdesc : ∀ k, f (x (k + 1)) + c * ‖grad (x k)‖ ^ 2 ≤ f (x k))
    (hbdd : ∀ k, fstar ≤ f (x k)) :
    ∃ k, k < T ∧ ‖grad (x k)‖ ^ 2 ≤ (f (x 0) - fstar) / (c * T) := by
  have h := exists_le_of_sum_range_le hT
    (grad_partial_sum_le f grad x fstar c hc hdesc hbdd T)
  obtain ⟨k, hkT, hk⟩ := h
  refine ⟨k, hkT, ?_⟩
  calc
    ‖grad (x k)‖ ^ 2 ≤ ((f (x 0) - fstar) / c) / T := hk
    _ = (f (x 0) - fstar) / (c * T) := by rw [div_div]

/-- 🎯 **串联**：若球面投影梯度步满足 `sphereGD_descent_lemma` 的（显式）几何假设与
L-光滑（对所有 k 一致成立），则梯度平方级数可和（从而 ‖grad x_k‖ → 0）。 -/
theorem sphereGD_sq_sum_bound (f : E → ℝ) (grad : E → E) (L eta fstar : ℝ) (x : ℕ → E)
    (heta : 0 < eta) (hL : 0 ≤ L) (hLeta : L * eta ≤ 1 / 2)
    (hstep : ∀ k, x (k + 1) = sphereGD eta grad (x k))
    (hsmooth : ∀ k, f (x (k + 1)) ≤ f (x k) + ⟪grad (x k), x (k + 1) - x k⟫
      + (L / 2) * ‖x (k + 1) - x k‖ ^ 2)
    (hretr : ∀ k, ‖x (k + 1) - x k‖ ≤ eta * ‖grad (x k)‖)
    (halign : ∀ k, ⟪grad (x k), x (k + 1) - x k⟫ ≤ -eta * ‖grad (x k)‖ ^ 2)
    (hbdd : ∀ k, fstar ≤ f (x k)) :
    Summable (fun k => ‖grad (x k)‖ ^ 2) := by
  refine (summable_grad_sq f grad x fstar (eta / 2) (by linarith) ?_ hbdd).1
  intro k
  have h := sphereGD_descent_lemma f grad L eta x k (hstep k) (hsmooth k) (hretr k)
    (halign k) heta hL hLeta
  linarith

/-! ## 第五节：切空间 -/

/-- 球面在 x 处的切空间（内积意义）：{v | ⟪x, v⟫ = 0}。 -/
def tangentSpace (x : E) : Set E := {v | ⟪x, v⟫ = (0 : ℝ)}

/-- 切空间对实数伸缩封闭。 -/
theorem tangentSpace_smul (x : E) (v : E) (hv : v ∈ tangentSpace x) (r : ℝ) :
    r • v ∈ tangentSpace x := by
  have hv' : ⟪x, v⟫ = (0 : ℝ) := hv
  show ⟪x, r • v⟫ = (0 : ℝ)
  rw [real_inner_smul_right, hv', mul_zero]

/-! ## 第六节：具体空间 `EuclideanSpace ℝ (Fin n)`（n = 2 即 S¹） -/

/-- 具体流形实例（n = 2 即单位圆 S¹）：EuclideanSpace ℝ (Fin n) 上的
球面投影梯度步保持球面约束。 -/
theorem euclidean_sphereGD_mem_sphere (n : ℕ) (eta : ℝ)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) (hne : gradStep eta grad x ≠ 0) :
    sphereGD eta grad x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  sphereGD_mem_sphere eta grad x hx hne

end Lattice
