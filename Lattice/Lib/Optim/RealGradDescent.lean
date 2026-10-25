import Lattice.Lib.Optim.RealConvergence
import Mathlib

/-!
# LATTICE: 梯度下降的显式收缩 ⟹ 收敛（训练循环的终止证明）

把 RealConvergence 的抽象收缩骨架接到**真实训练算法**：
对平方损失 L(x) = ‖A·x - b‖²（一致系统），梯度下降更新

    x' = x - (2η)·A†(A·x - b)      （A† 是伴随，法方程梯度）

满足误差恒等式

    A·x' - b = (1 - (2η)·A∘A†)(A·x - b)

于是（谱界假设 ‖1 - (2η)·A∘A†‖ ≤ c < 1）单步收缩：

    ‖A·x' - b‖ ≤ c·‖A·x - b‖
    ‖A·x' - b‖² ≤ c²·‖A·x - b‖²

迭代后连接 RealConvergence：∀ ε > 0，∃ n，误差 < ε（训练收敛到满足）。

闭环：法方程（RealNormalEquationScalar：驻点⟺满足）→ 伴随梯度 →
显式收缩步（本文件）→ 收敛骨架（RealConvergence）→ 验证循环终止。

模型无关：任意 RCLike 𝕜 内积空间 + 实化假设；谱界是唯一的数值假设
（步长 η 使 2η·AA† 谱在 (0,2) 内，即经典梯度下降步长条件）。
-/

noncomputable section

namespace Lattice

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-! ## 梯度下降更新：x' = x - (2η)·A†(A·x - b) -/

def GDUpdate (A : E →L[𝕜] F) (b : F) (η : ℝ) (x : E) : E :=
  x - (2 * η : 𝕜) • (A.adjoint (A x - b))

/-! ## 定理一：误差恒等式
A·x' - b = (1 - (2η)·A∘A†)(A·x - b)。-/

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
lemma GD_error_identity (A : E →L[𝕜] F) (b : F) (η : ℝ) (x : E) :
    A (GDUpdate A b η x) - b =
      ((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) (A x - b) := by
  unfold GDUpdate
  calc
    A (x - (2 * η : 𝕜) • (A.adjoint (A x - b))) - b
        = (A x - A ((2 * η : 𝕜) • (A.adjoint (A x - b)))) - b := by
          rw [A.map_sub]
    _ = (A x - (2 * η : 𝕜) • A (A.adjoint (A x - b))) - b := by
          rw [A.map_smul]
    _ = (A x - b) - (2 * η : 𝕜) • ((A ∘L A.adjoint) (A x - b)) := by
          rw [← ContinuousLinearMap.comp_apply]
          abel
    _ = ((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) (A x - b) := by
          simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]

/-! ## 定理二：单步收缩（谱界）
‖1 - (2η)·A∘A†‖ ≤ c ⟹ ‖A·x' - b‖ ≤ c·‖A·x - b‖。-/

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem GD_contraction_step (A : E →L[𝕜] F) (b : F) (η : ℝ) (x : E) (c : ℝ)
    (hspec : ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (GDUpdate A b η x) - b‖ ≤ c * ‖A x - b‖ := by
  rw [GD_error_identity A b η x]
  calc
    ‖((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) (A x - b)‖
        ≤ ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ * ‖A x - b‖ :=
          ContinuousLinearMap.le_opNorm _ (A x - b)
    _ ≤ c * ‖A x - b‖ := by
      exact mul_le_mul_of_nonneg_right hspec (norm_nonneg (A x - b))

/-! ## 定理三：单步平方收缩
‖A·x' - b‖² ≤ c²·‖A·x - b‖²。-/

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem GD_sq_contraction_step (A : E →L[𝕜] F) (b : F) (η : ℝ) (x : E) (c : ℝ)
    (hc0 : 0 ≤ c) (hspec : ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (GDUpdate A b η x) - b‖ ^ 2 ≤ c ^ 2 * ‖A x - b‖ ^ 2 := by
  have h := GD_contraction_step A b η x c hspec
  have hsq : ‖A (GDUpdate A b η x) - b‖ ^ 2 ≤ (c * ‖A x - b‖) ^ 2 := by
    -- sq_le_sq'：-(c·‖b‖) ≤ ‖a‖ 且 ‖a‖ ≤ c·‖b‖（非负两边平方保序）
    exact sq_le_sq' (by
      nlinarith [mul_nonneg hc0 (norm_nonneg (A x - b)), norm_nonneg (A (GDUpdate A b η x) - b)]) h
  calc
    ‖A (GDUpdate A b η x) - b‖ ^ 2 ≤ (c * ‖A x - b‖) ^ 2 := hsq
    _ = c ^ 2 * ‖A x - b‖ ^ 2 := by ring

/-! ## 迭代 -/

def GDIterate (A : E →L[𝕜] F) (b : F) (η : ℝ) : ℕ → E → E
  | 0, x => x
  | n + 1, x => GDIterate A b η n (GDUpdate A b η x)

def GDError (A : E →L[𝕜] F) (b : F) (η : ℝ) (x0 : E) (n : ℕ) : ℝ :=
  ‖A (GDIterate A b η n x0) - b‖ ^ 2

/-! ## 引理：迭代与更新的交换
GDIterate n (GDUpdate x) = GDUpdate (GDIterate n x)（迭代 n 次再更新 = 更新再迭代 n 次）。-/

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
lemma GDIterate_comm_update (A : E →L[𝕜] F) (b : F) (η : ℝ) :
    ∀ (n : ℕ) (x : E), GDIterate A b η n (GDUpdate A b η x) = GDUpdate A b η (GDIterate A b η n x) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [GDIterate]
  | succ n ih =>
      intro x
      calc
        GDIterate A b η (n + 1) (GDUpdate A b η x)
            = GDIterate A b η n (GDUpdate A b η (GDUpdate A b η x)) := rfl
        _ = GDUpdate A b η (GDIterate A b η n (GDUpdate A b η x)) := ih (GDUpdate A b η x)
        _ = GDUpdate A b η (GDUpdate A b η (GDIterate A b η n x)) := by rw [ih x]
        _ = GDUpdate A b η (GDIterate A b η (n + 1) x) := by
          apply congrArg (GDUpdate A b η)
          simpa [GDIterate] using (ih x).symm

/-! ## 定理四：迭代收缩
每步误差平方收缩 c²：e(n+1) ≤ c²·e(n)。-/

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem GD_iterate_contraction (A : E →L[𝕜] F) (b : F) (η : ℝ) (x0 : E) (c : ℝ)
    (hc0 : 0 ≤ c) (hspec : ∀ _x : E, ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ ≤ c) :
    ∀ n : ℕ, GDError A b η x0 (n + 1) ≤ c ^ 2 * GDError A b η x0 n := by
  intro n
  unfold GDError
  -- x_{n+1} = GDUpdate x_n
  have hiter : GDIterate A b η (n + 1) x0 = GDUpdate A b η (GDIterate A b η n x0) := by
    rw [← GDIterate_comm_update A b η n x0]
    rfl
  rw [hiter]
  exact GD_sq_contraction_step A b η (GDIterate A b η n x0) c hc0 (hspec (GDIterate A b η n x0))

/-! ## 定理五：梯度下降收敛（ε-终止）
0 ≤ c < 1 谱界 ⟹ ∀ ε > 0，∃ n，误差 < ε（连接 RealConvergence）。-/

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem GD_converges (A : E →L[𝕜] F) (b : F) (η : ℝ) (x0 : E) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hspec : ∀ _x : E, ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ ≤ c) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, GDError A b η x0 n < ε := by
  -- 收缩系数 c²：0 ≤ c² < 1
  have hc2_0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hc2_1 : c ^ 2 < 1 := by
    have hlt : c * c < 1 * 1 := mul_self_lt_mul_self hc0 hc1
    nlinarith
  -- 应用 RealConvergence.contraction_converges
  exact contraction_converges (c ^ 2) hc2_0 hc2_1
    (GD_iterate_contraction A b η x0 c hc0 hspec)
    (fun n => by unfold GDError; exact sq_nonneg _)

/-! ## 注：闭环语义
  法方程（驻点⟺满足）→ 伴随梯度 → 显式收缩步 → 迭代收缩 →
  收敛骨架（contraction_converges）⟹ 训练 ε-终止。
  谱界 ‖1-2η·AA†‖≤c<1 是经典梯度下降步长条件（2η 在谱上界内）的算子形式，
  也是唯一的数值假设——模型无关性保持。-/

end Lattice
