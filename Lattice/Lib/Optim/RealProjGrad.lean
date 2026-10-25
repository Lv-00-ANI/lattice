import Lattice.Lib.Optim.RealGradDescent
import Mathlib

/-!
# LATTICE: 投影梯度法 —— 凸约束优化（驻点形态：约束版梯度下降的收敛）

§5 约束行「更多驻点形态」：投影梯度法（projected gradient descent）在平方损失
L(x) = ‖A·x - b‖² 上的收敛。约束集 C 为闭凸集；约束版更新为

    x_{t+1} = P_C (x_t − (2η)·A†(A·x_t − b))，        （P_C：到 C 的投影）

即无约束梯度步（RealGradDescent 的 `GDUpdate`）后跟投影。

核心引理链：
  1. `proj_nonexpansive`（投影非扩张）：‖P_C x − P_C y‖ ≤ ‖x − y‖（P_C 是 1-Lipschitz）；
  2. `projGD_contraction_to_solution`：设 x* ∈ C 是最优解（A x* = b），则
       ‖x_{t+1} − x*‖ ≤ ‖GDUpdate x_t − x*‖ ≤ c·‖x_t − x*‖
     （第一步：投影非扩张 + P_C x* = x*；第二步：无约束 GD 步对解的收缩）；
  3. `projGD_iterate_contraction` / `projGD_converges`：误差平方按 c² 收缩，
     0 ≤ c < 1 ⟹ ∀ ε > 0，∃ n，‖x_n − x*‖ < ε（ε-终止，接 RealConvergence）；
  4. `projGD_unconstrained_recovery`：C = 全空间 ⟹ 投影梯度 = 普通 GD（衔接 RealGradDescent）。

诚实边界（与数学教科书的差距，明确标注）：
  · **投影**：mathlib 只对**子空间**提供完备正交投影（`orthogonalProjection K`，
    K : Submodule 𝕜 E，需 `HasOrthogonalProjection K`；`HasOrthogonalProjection.ofCompleteSpace`
    在 K 完备时给出，闭子空间即满足）。本文件的 C 取为**闭子空间 K**；投影非扩张用
    `orthogonalProjection_norm_le`（‖P‖ ≤ 1）+ `le_opNorm` 给出，是线性算子的 1-Lipschitz。
    一般闭凸集的投影非扩张（变分不等式路线：存在性 `Convex.exists_nearest` +
    投影最优性 ⟹ ⟨x − Px, y − Px⟩ ≤ 0 ⟹ 非扩张）标注为后续工作。
  · **谱界**：误差（到解的距离）收缩需要 E 侧谱界 ‖1 − 2η·(A†∘A)‖ ≤ c，
    与 RealGradDescent 的残差谱界 ‖1 − 2η·(A∘A†)‖ ≤ c 是同一经典步长条件
    （AA† 与 A†A 的非零谱相同），本文件直接假设 E 侧版本。
  · **最优解**：假设 x* ∈ K 且 A x* = b（解存在且属于约束集）。

模型无关：任意 RCLike 𝕜 内积空间 + 实化假设；谱界是唯一数值假设。
-/

noncomputable section

namespace Lattice

/-! 投影部分只需要 E 的内积结构（无 ℝ 实化、无完备性假设）。 -/

variable {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## 一、投影：非扩张与不动点
P_K = orthogonalProjection K（K 闭子空间）：‖P x − P y‖ ≤ ‖x − y‖；x ∈ K ⟹ P x = x。-/

/-- 到子空间 K 的正交投影是非扩张的（1-Lipschitz）：‖P x − P y‖ ≤ ‖x − y‖。
mathlib 依据：`orthogonalProjection` 是范数 ≤ 1 的连续线性算子
（`orthogonalProjection_norm_le`）⟹ `le_opNorm` 给出 1-Lipschitz。 -/
lemma proj_nonexpansive (K : Submodule 𝕜 E) [HasOrthogonalProjection K] (x y : E) :
    ‖(orthogonalProjection K x : E) - (orthogonalProjection K y : E)‖ ≤ ‖x - y‖ := by
  have hlin : (orthogonalProjection K x : E) - (orthogonalProjection K y : E) =
      (orthogonalProjection K (x - y) : E) := by
    rw [← Submodule.coe_sub]
    rw [← map_sub]
  rw [hlin]
  calc
    ‖(orthogonalProjection K (x - y) : E)‖ ≤ ‖orthogonalProjection K‖ * ‖x - y‖ := by
      simpa using (orthogonalProjection K).le_opNorm (x - y)
    _ ≤ ‖x - y‖ := by
      calc
        ‖orthogonalProjection K‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (orthogonalProjection_norm_le K) (norm_nonneg (x - y))
        _ = ‖x - y‖ := by rw [one_mul]

/-- 约束集内的点是不动点：x ∈ K ⟹ P_K x = x（`orthogonalProjection_eq_self_iff`）。 -/
lemma proj_fixed (K : Submodule 𝕜 E) [HasOrthogonalProjection K] {v : E} (hv : v ∈ K) :
    (orthogonalProjection K v : E) = v :=
  (orthogonalProjection_eq_self_iff).2 hv

/-- 全空间投影是恒等：P_⊤ x = x。 -/
lemma proj_top_identity (x : E) :
    (orthogonalProjection (⊤ : Submodule 𝕜 E) x : E) = x := by
  rw [orthogonalProjection_eq_self_iff]
  trivial

/-! GD 与投影梯度部分需要 E、F 的内积 + 完备结构（伴随的存在性）。 -/

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-! ## 二、无约束 GD 步对最优解的收缩
x* 最优（A x* = b）⟹ GDUpdate x* = x*，且
GDUpdate x − x* = (1 − 2η·A†A)(x − x*)，于是 ‖GDUpdate x − x*‖ ≤ c·‖x − x*‖。 -/

/-- 最优解是 GDUpdate 的不动点：A x* = b ⟹ GDUpdate A b η x* = x*。 -/
lemma GDUpdate_solution_fixed (A : E →L[𝕜] F) (b : F) (η : ℝ) (xStar : E) (hx : A xStar = b) :
    GDUpdate A b η xStar = xStar := by
  unfold GDUpdate
  rw [hx]
  simp

/-- GDUpdate 的误差恒等式（E 侧）：任意 x y，GDUpdate x − GDUpdate y =
(1 − 2η·A†A)(x − y)（与 GD_error_identity 的 F 侧残差版对偶）。 -/
lemma GDUpdate_sub (A : E →L[𝕜] F) (b : F) (η : ℝ) (x y : E) :
    GDUpdate A b η x - GDUpdate A b η y =
      ((1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)) (x - y) := by
  unfold GDUpdate
  calc
    (x - (2 * η : 𝕜) • (A.adjoint (A x - b))) - (y - (2 * η : 𝕜) • (A.adjoint (A y - b)))
        = (x - y) - (2 * η : 𝕜) • (A.adjoint (A x - b) - A.adjoint (A y - b)) := by
          rw [smul_sub]
          abel
    _ = (x - y) - (2 * η : 𝕜) • (A.adjoint ((A x - b) - (A y - b))) := by
          rw [← map_sub]
    _ = (x - y) - (2 * η : 𝕜) • (A.adjoint (A x - A y)) := by
          rw [show (A x - b) - (A y - b) = A x - A y by abel]
    _ = (x - y) - (2 * η : 𝕜) • ((A.adjoint ∘L A) (x - y)) := by
          rw [← map_sub, ContinuousLinearMap.comp_apply]
    _ = ((1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)) (x - y) := by
          simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]

/-- x* 最优时：GDUpdate x − x* = (1 − 2η·A†A)(x − x*)。 -/
lemma GD_update_solution_error (A : E →L[𝕜] F) (b : F) (η : ℝ) (x xStar : E)
    (hx : A xStar = b) :
    GDUpdate A b η x - xStar =
      ((1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)) (x - xStar) := by
  calc
    GDUpdate A b η x - xStar = GDUpdate A b η x - GDUpdate A b η xStar := by
      rw [GDUpdate_solution_fixed A b η xStar hx]
    _ = ((1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)) (x - xStar) :=
      GDUpdate_sub A b η x xStar

/-- 无约束 GD 步对最优解的收缩（E 侧谱界）：‖GDUpdate x − x*‖ ≤ c·‖x − x*‖。 -/
theorem GD_contraction_solution (A : E →L[𝕜] F) (b : F) (η : ℝ) (x xStar : E) (c : ℝ)
    (hx : A xStar = b)
    (hspec : ‖(1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)‖ ≤ c) :
    ‖GDUpdate A b η x - xStar‖ ≤ c * ‖x - xStar‖ := by
  rw [GD_update_solution_error A b η x xStar hx]
  calc
    ‖((1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)) (x - xStar)‖
        ≤ ‖(1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)‖ * ‖x - xStar‖ :=
          ContinuousLinearMap.le_opNorm _ (x - xStar)
    _ ≤ c * ‖x - xStar‖ := by
      exact mul_le_mul_of_nonneg_right hspec (norm_nonneg (x - xStar))

/-! ## 三、投影梯度更新与单步收缩
x' = P_K (GDUpdate x)；‖x' − x*‖ ≤ c·‖x − x*‖（投影非扩张 + GD 收缩）。 -/

/-- 投影梯度更新：x' = P_K (GDUpdate A b η x)（约束集 K 的投影）。 -/
def ProjGDUpdate (A : E →L[𝕜] F) (b : F) (η : ℝ) (K : Submodule 𝕜 E)
    [HasOrthogonalProjection K] (x : E) : E :=
  (orthogonalProjection K (GDUpdate A b η x) : E)

/-- 投影梯度单步收缩到最优解：x* ∈ K、A x* = b、E 侧谱界 ⟹
‖x' − x*‖ ≤ c·‖x − x*‖。 -/
theorem projGD_contraction_to_solution (A : E →L[𝕜] F) (b : F) (η : ℝ)
    (K : Submodule 𝕜 E) [HasOrthogonalProjection K] (x xStar : E) (c : ℝ)
    (hxK : xStar ∈ K) (hx : A xStar = b)
    (hspec : ‖(1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)‖ ≤ c) :
    ‖ProjGDUpdate A b η K x - xStar‖ ≤ c * ‖x - xStar‖ := by
  unfold ProjGDUpdate
  calc
    ‖(orthogonalProjection K (GDUpdate A b η x) : E) - xStar‖
        = ‖(orthogonalProjection K (GDUpdate A b η x) : E) - (orthogonalProjection K xStar : E)‖ := by
          rw [proj_fixed K hxK]
    _ ≤ ‖GDUpdate A b η x - xStar‖ := proj_nonexpansive K (GDUpdate A b η x) xStar
    _ ≤ c * ‖x - xStar‖ := GD_contraction_solution A b η x xStar c hx hspec

/-! ## 四、迭代与 ε-终止
误差 e_n = ‖x_n − x*‖² 按 c² 收缩；0 ≤ c < 1 ⟹ 收敛到 x*。 -/

/-- 投影梯度迭代：x_{n+1} = P_K (GDUpdate x_n)。 -/
def ProjGDIterate (A : E →L[𝕜] F) (b : F) (η : ℝ) (K : Submodule 𝕜 E)
    [HasOrthogonalProjection K] : ℕ → E → E
  | 0, x => x
  | n + 1, x => ProjGDUpdate A b η K (ProjGDIterate A b η K n x)

/-- 投影梯度误差（平方）：e_n = ‖x_n − x*‖²。 -/
def ProjGDError (A : E →L[𝕜] F) (b : F) (η : ℝ) (K : Submodule 𝕜 E)
    [HasOrthogonalProjection K] (x0 xStar : E) (n : ℕ) : ℝ :=
  ‖ProjGDIterate A b η K n x0 - xStar‖ ^ 2

/-- 迭代收缩：e_{n+1} ≤ c²·e_n（每步误差平方收缩 c²）。 -/
theorem projGD_iterate_contraction (A : E →L[𝕜] F) (b : F) (η : ℝ)
    (K : Submodule 𝕜 E) [HasOrthogonalProjection K] (x0 xStar : E) (c : ℝ)
    (hxK : xStar ∈ K) (hx : A xStar = b) (hc0 : 0 ≤ c)
    (hspec : ∀ x : E, ‖(1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)‖ ≤ c) :
    ∀ n : ℕ, ProjGDError A b η K x0 xStar (n + 1) ≤ c ^ 2 * ProjGDError A b η K x0 xStar n := by
  intro n
  unfold ProjGDError
  have hstep : ‖ProjGDUpdate A b η K (ProjGDIterate A b η K n x0) - xStar‖ ≤
      c * ‖ProjGDIterate A b η K n x0 - xStar‖ :=
    projGD_contraction_to_solution A b η K (ProjGDIterate A b η K n x0) xStar c hxK hx
      (hspec (ProjGDIterate A b η K n x0))
  have hsq : ‖ProjGDUpdate A b η K (ProjGDIterate A b η K n x0) - xStar‖ ^ 2 ≤
      (c * ‖ProjGDIterate A b η K n x0 - xStar‖) ^ 2 := by
    exact sq_le_sq' (by
      nlinarith [mul_nonneg hc0 (norm_nonneg (ProjGDIterate A b η K n x0 - xStar)),
        norm_nonneg (ProjGDUpdate A b η K (ProjGDIterate A b η K n x0) - xStar)]) hstep
  calc
    ‖ProjGDIterate A b η K (n + 1) x0 - xStar‖ ^ 2
        = ‖ProjGDUpdate A b η K (ProjGDIterate A b η K n x0) - xStar‖ ^ 2 := by
          simp [ProjGDIterate]
    _ ≤ (c * ‖ProjGDIterate A b η K n x0 - xStar‖) ^ 2 := hsq
    _ = c ^ 2 * ‖ProjGDIterate A b η K n x0 - xStar‖ ^ 2 := by ring

/-- 投影梯度收敛（ε-终止）：0 ≤ c < 1、E 侧谱界 ⟹
∀ ε > 0，∃ n，‖x_n − x*‖ < ε（接 RealConvergence.contraction_converges）。 -/
theorem projGD_converges (A : E →L[𝕜] F) (b : F) (η : ℝ)
    (K : Submodule 𝕜 E) [HasOrthogonalProjection K] (x0 xStar : E) (c : ℝ)
    (hxK : xStar ∈ K) (hx : A xStar = b) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hspec : ∀ x : E, ‖(1 : E →L[𝕜] E) - (2 * η : 𝕜) • (A.adjoint ∘L A)‖ ≤ c) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖ProjGDIterate A b η K n x0 - xStar‖ < ε := by
  -- 收缩系数 c²：0 ≤ c² < 1
  have hc2_0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hc2_1 : c ^ 2 < 1 := by
    have hlt : c * c < 1 * 1 := mul_self_lt_mul_self hc0 hc1
    nlinarith
  -- 应用 RealConvergence.contraction_converges（误差平方序列）
  have hconv :
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ProjGDError A b η K x0 xStar n < ε :=
    contraction_converges (c ^ 2) hc2_0 hc2_1
      (projGD_iterate_contraction A b η K x0 xStar c hxK hx hc0 hspec)
      (fun n => by unfold ProjGDError; exact sq_nonneg _)
  intro ε hε
  -- 对 ε² 用收敛：∃ n，‖x_n − x*‖² < ε²
  rcases hconv (ε ^ 2) (sq_pos_of_pos hε) with ⟨n, hn⟩
  -- 非负两边开方：‖x_n − x*‖ < ε
  refine ⟨n, ?_⟩
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hε) hn

/-! ## 五、衔接：无约束恢复
C = 全空间（K = ⊤）⟹ 投影恒等（proj_top_identity）⟹ 投影梯度 = 普通 GD（RealGradDescent）。 -/

/-- 无约束恢复：K = ⊤ ⟹ ProjGDUpdate = GDUpdate（投影梯度退化为普通梯度下降）。 -/
theorem projGD_unconstrained_recovery (A : E →L[𝕜] F) (b : F) (η : ℝ) (x : E) :
    ProjGDUpdate A b η (⊤ : Submodule 𝕜 E) x = GDUpdate A b η x := by
  unfold ProjGDUpdate
  simp [proj_top_identity]

/-! ## 注：闭环语义
  约束驻点形态（本文件）：投影非扩张（1-Lipschitz）⟹ 约束 GD 单步收缩到最优解
  ⟹ 迭代平方收缩 ⟹ ε-终止（RealConvergence 骨架），并与无约束 GD（RealGradDescent）
  在 C = 全空间时精确衔接。
  诚实边界：C 取闭子空间（mathlib `orthogonalProjection`），一般闭凸集投影非扩张
  （变分不等式）标注为后续；谱界为 E 侧版本 ‖1 − 2η·A†A‖ ≤ c。 -/

end Lattice
