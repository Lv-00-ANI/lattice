import Mathlib
import Lattice.Lib.InfoTheory.RealFisherInfo
import Lattice.Lib.LearningTheory.RealContinualLearning
/-!
# LATTICE: 矩阵 Fisher 信息 —— 多参数 score、PSD 二次型、零方向不可辨识与 EWC

`RealFisherInfo` 明确标注「**未做**：多参数（矩阵 Fisher）版本」。
本文件补上这一多参数版本。

设参数 `θ : Fin n → ℝ`，条件分布 `p : (Fin n → ℝ) → Fin k → ℝ`（`a : Fin k` 为观测）。
**逐坐标 score**（第 `i` 个偏坐标方向上的对数似然导数）与**矩阵 Fisher 信息**：

    logScoreAt p θ a i = ∂_{θ_i} log p_{θ}(a)
    fisherMatrix p θ i j = Σ_a p_θ(a)·logScoreAt p θ a i·logScoreAt p θ a j

本文件建立：
1. `fisherMatrix_symm`：Fisher 矩阵对称；
2. `fisherQuadForm` 与恒等式 `fisherQuadForm_eq_fisherMatrix`：
   `Σ_i Σ_j v_i·F_{ij}·v_j = Σ_a p_θ(a)·(Σ_i v_i·logScoreAt p θ a i)²`；
3. `fisherMatrix_psd`：`p ≥ 0` ⟹ 二次型非负（矩阵 Fisher 半正定）；
4. `fisherMatrix_zero_direction` / `fisherMatrix_zero_direction_score`：
   沿零方向 `F·v = 0` 的 score 方向导数为零（不可辨识方向的刻画）；
5. `ewcQuadratic` 与 `ewcQuadratic_nonneg`：EWC 矩阵二次惩罚的非负性；
6. `ewcQuadratic_one_dim`：一维退化到 `RealContinualLearning.ewcPenalty`；
7. `fisherMatrix_eq_fisherInfo_one_dim`：`n = 1` 时矩阵 Fisher 就是
   `RealFisherInfo.fisherInfo`（闭合维度退化）。

## 主结果

1. **对称性**（`fisherMatrix_symm`）：`F_{ij} = F_{ji}`。
2. **二次型恒等式**（`fisherQuadForm_eq_fisherMatrix`）：把矩阵二次型写成
   score 方向的平方和，这是 PSD 与零方向刻画的关键代数步骤。
3. **半正定性**（`fisherMatrix_psd`）：`Σ_a p_θ(a) ≥ 0` 逐项 ⟹
   `0 ≤ Σ_i Σ_j v_i·F_{ij}·v_j`。
4. **零方向的 score 为零**（`fisherMatrix_zero_direction_score`）：
   `p > 0` 且 `Σ_i F_{ij}·v_i = 0`（∀`j`）⟹ `Σ_i v_i·logScoreAt p θ a i = 0`（∀`a`）。
5. **EWC 二次型非负**（`ewcQuadratic_nonneg`）与**一维退化**（`ewcQuadratic_one_dim`）。
6. **维度退化兼容**（`fisherMatrix_eq_fisherInfo_one_dim`）：
   `fisherMatrix (fun t => q (t 0)) (fun _ => θ) 0 0 = fisherInfo q θ`。

## 诚实边界

- **Hessian / Fisher 对象是显式给出的**：`logScoreAt` 直接由 `deriv` 定义，
  矩阵 Fisher 由 `p` 与 score 的乘积求和定义；本文件**不从二阶 Fréchet 导数推导** Fisher
  矩阵，也不证明 `F = −E[∇² log p]`（该等式在 `RealFisherInfo` 中已作为显式假设处理）。
- **未做**：完整 MAML 收敛定理；Fisher 的 Cramér–Rao 等号刻画；
  自然梯度的收敛性；`Σ_a p_θ(a) = 1` 对多参数 `θ` 的微分恒等式
  （即多参数 score 期望为零 —— 本文件的零方向刻画只用到二次型非负性，不需该恒等式）。
- **显式假设/诚实降级**：`ewcQuadratic_nonneg` 中「`F` 半正定」**没有**从
  `∀ i j, 0 ≤ F i j` 与对称性推出（二者并不蕴含 PSD），而是作为**显式 PSD 假设** `hpsd` 给出，
  再对 `d := θ − θ*` 应用（标注降级）。
- **B12 判定（机器验证，重要）**：ROADMAP B12 要求「从逐项非负 + 对称推 PSD」，
  **该推导不成立且命题为假**。`ewc_psd_counterexample` 给出反例：
  `F = [[1,2],[2,1]]` 对称、逐项非负，但 `d = (1,−1)` 给出二次型 `−2 < 0`。
  因此本文件改为给出该计划**在正确条件下成立的部分**：
  `ewcQuadratic_nonneg_diagonal`（对角 `F`，无额外假设）与
  `ewcQuadratic_nonneg_one_dim`（`n = 1`）。
  一般非对角情形**未做且不可做**（不是缺工具，而是命题为假）；
  真正要 PSD 需额外结构（如 `fisherMatrix_psd` 所用的平方和形态 `Σ_a p_a s_a s_aᵀ`）。
- **范围**：有限维 `Fin n` / `Fin k`；一维退化（`n = 1`）连接 `RealFisherInfo` 与
  `RealContinualLearning`。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {n k : ℕ}

/-! ## 一、定义：逐坐标 score 与矩阵 Fisher 信息 -/

/-- **第 `i` 个偏坐标的 score**：
    `logScoreAt p θ a i = ∂_{θ_i} log p_θ(a)`，
    即沿第 `i` 个坐标方向对对数似然求偏导。 -/
def logScoreAt (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ) (a : Fin k) (i : Fin n) : ℝ :=
  deriv (fun t : ℝ => Real.log (p (Function.update θ i t) a)) (θ i)

/-- **矩阵 Fisher 信息**：`F_{ij}(θ) = Σ_a p_θ(a)·score_{a,i}·score_{a,j}`
    （`RealFisherInfo.fisherInfo` 的多参数版本）。 -/
noncomputable def fisherMatrix (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  ∑ a, p θ a * logScoreAt p θ a i * logScoreAt p θ a j

/-- **Fisher 二次型**（score 方向的平方和）：
    `fisherQuadForm p θ v = Σ_a p_θ(a)·(Σ_i v_i·logScoreAt p θ a i)²`。
    这是矩阵二次型恒等式的右端，便于分别证明 PSD 与零方向刻画。 -/
noncomputable def fisherQuadForm (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (v : Fin n → ℝ) : ℝ :=
  ∑ a, p θ a * (∑ i, v i * logScoreAt p θ a i) ^ 2

/-! ## 二、对称性 -/

/-- **Fisher 矩阵对称**：`F_{ij} = F_{ji}`（乘积交换）。 -/
theorem fisherMatrix_symm (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ) (i j : Fin n) :
    fisherMatrix p θ i j = fisherMatrix p θ j i := by
  unfold fisherMatrix
  apply Finset.sum_congr rfl
  intro a _
  ring

/-! ## 三、二次型恒等式（主结果）

`Σ_i Σ_j v_i·F_{ij}·v_j = Σ_a p_θ(a)·(Σ_i v_i·score_{a,i})²`。
证明路线：把 `F` 展开成 `a` 的求和（`Finset.mul_sum` / `Finset.sum_mul`），
交换求和次序（两次 `Finset.sum_comm`），对固定 `a` 用
`(Σ_i v_i·s_i)² = Σ_i Σ_j (v_i·s_i)·(v_j·s_j)`（`Finset.sum_mul_sum`）合并。 -/

/-- **Fisher 二次型恒等式**：矩阵二次型 = score 平方和的 `p` 加权和。 -/
theorem fisherQuadForm_eq_fisherMatrix (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (v : Fin n → ℝ) :
    fisherQuadForm p θ v = ∑ i, ∑ j, v i * fisherMatrix p θ i j * v j := by
  have hL : fisherQuadForm p θ v
      = ∑ a, ∑ i, ∑ j,
          v i * (p θ a * logScoreAt p θ a i * logScoreAt p θ a j) * v j := by
    unfold fisherQuadForm
    apply Finset.sum_congr rfl
    intro a _
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hR : (∑ i, ∑ j, v i * fisherMatrix p θ i j * v j)
      = ∑ a, ∑ i, ∑ j,
          v i * (p θ a * logScoreAt p θ a i * logScoreAt p θ a j) * v j := by
    calc
      (∑ i, ∑ j, v i * fisherMatrix p θ i j * v j)
          = ∑ i, ∑ j, ∑ a,
              v i * (p θ a * logScoreAt p θ a i * logScoreAt p θ a j) * v j := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            unfold fisherMatrix
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ i, ∑ a, ∑ j,
              v i * (p θ a * logScoreAt p θ a i * logScoreAt p θ a j) * v j :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ a, ∑ i, ∑ j,
              v i * (p θ a * logScoreAt p θ a i * logScoreAt p θ a j) * v j :=
            Finset.sum_comm
  rw [hL, hR]

/-- **Fisher 二次型非负**：`p_θ ≥ 0` 时逐项 `p_θ(a)·(…)² ≥ 0`。 -/
theorem fisherQuadForm_nonneg (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (v : Fin n → ℝ) (hp : ∀ a, 0 ≤ p θ a) :
    0 ≤ fisherQuadForm p θ v := by
  unfold fisherQuadForm
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (sq_nonneg _))

/-- **矩阵 Fisher 半正定（主结果）**：`p_θ ≥ 0` ⟹
    `0 ≤ Σ_i Σ_j v_i·F_{ij}·v_j`（点态 nonneg ⟹ PSD）。 -/
theorem fisherMatrix_psd (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ) (v : Fin n → ℝ)
    (hp : ∀ a, 0 ≤ p θ a) :
    0 ≤ ∑ i, ∑ j, v i * fisherMatrix p θ i j * v j := by
  rw [← fisherQuadForm_eq_fisherMatrix p θ v]
  exact fisherQuadForm_nonneg p θ v hp

/-! ## 四、零方向与不可辨识性

`F·v = 0` 时二次型 `vᵀFv = 0`；由「平方和非负且和为零 ⟹ 每项为零」
可得每个 `a` 的 score 方向导数 `Σ_i v_i·logScoreAt p θ a i = 0`。 -/

/-- **零方向 ⟹ 二次型为零**：若 `∀ j, Σ_i F_{ij}·v_i = 0`，则 `fisherQuadForm p θ v = 0`。 -/
theorem fisherMatrix_zero_direction (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (v : Fin n → ℝ) (hv : ∀ j, ∑ i, fisherMatrix p θ i j * v i = 0) :
    fisherQuadForm p θ v = 0 := by
  have hgoal : (∑ i, ∑ j, v i * fisherMatrix p θ i j * v j)
      = ∑ j, v j * (∑ i, fisherMatrix p θ j i * v i) := by
    calc
      (∑ i, ∑ j, v i * fisherMatrix p θ i j * v j)
          = ∑ j, ∑ i, v i * fisherMatrix p θ i j * v j := Finset.sum_comm
      _ = ∑ j, ∑ i, v j * fisherMatrix p θ j i * v i := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            rw [fisherMatrix_symm p θ j i]
            ring
      _ = ∑ j, v j * (∑ i, fisherMatrix p θ j i * v i) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
  have hzero : ∀ j, (∑ i, fisherMatrix p θ j i * v i) = 0 := by
    intro j
    rw [show (∑ i, fisherMatrix p θ j i * v i)
        = ∑ i, fisherMatrix p θ i j * v i from
      Finset.sum_congr rfl (fun i _ => by rw [fisherMatrix_symm p θ j i])]
    exact hv j
  rw [fisherQuadForm_eq_fisherMatrix, hgoal]
  exact Finset.sum_eq_zero (fun j _ => by rw [hzero j, mul_zero])

/-- **零方向的 score 方向导数为零（主结果，不可辨识性）**：
    `p_θ > 0` 且 `∀ j, Σ_i F_{ij}·v_i = 0` ⟹ `∀ a, Σ_i v_i·logScoreAt p θ a i = 0`。
    即方向 `v` 在 Fisher 度量下长度为 `0`，沿它的 score 变化亦为零。 -/
theorem fisherMatrix_zero_direction_score (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (v : Fin n → ℝ) (hp : ∀ a, 0 < p θ a)
    (hv : ∀ j, ∑ i, fisherMatrix p θ i j * v i = 0) :
    ∀ a, ∑ i, v i * logScoreAt p θ a i = 0 := by
  intro a
  have hq : fisherQuadForm p θ v = 0 := fisherMatrix_zero_direction p θ v hv
  have hterm : ∀ b, 0 ≤ p θ b * (∑ i, v i * logScoreAt p θ b i) ^ 2 :=
    fun b => mul_nonneg (le_of_lt (hp b)) (sq_nonneg _)
  have hsum : ∑ b, p θ b * (∑ i, v i * logScoreAt p θ b i) ^ 2 = 0 := by
    unfold fisherQuadForm at hq
    exact hq
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hterm b)).mp hsum a
    (Finset.mem_univ a)
  rcases mul_eq_zero.mp hb with h | h
  · exact absurd h (ne_of_gt (hp a))
  · exact pow_eq_zero h

/-! ## 五-0、B12：EWC 的 PSD **不能**从「逐项非负 + 对称」推出（机器验证反例）

ROADMAP 的 B12 要求「EWC 从逐项非负 + 对称推 PSD」。**代入检验的结论是该推导不成立**：

`F = [[1, 2], [2, 1]]` 对称且逐项非负，但取 `d = (1, −1)` 得
`dᵀFd = 1 − 2 − 2 + 1 = −2 < 0`，故 `F` **不是** PSD。

**成立的替代结论**（本文件给出，均无额外假设）：
1. `ewc_psd_counterexample`：上述反例（内核可验证），说明原推导**不可能**成立；
2. `ewcQuadratic_nonneg_diagonal`：**对角** `F`（`i ≠ j ⟹ F i j = 0`）时
   「逐项非负」**确实**推出二次型非负——这是原计划在正确条件下仍然成立的部分；
3. `ewcQuadratic_nonneg_one_dim`：`n = 1`（一维）时的特例。

**诚实标注**：一般情形（非对角）**未做且不可做**——不是缺工具，而是命题为假。
真正要 PSD 必须额外假设（如 `F = Σ_a p_a s_a s_a ᵀ`，这正是 `fisherMatrix_psd` 的形态）。 -/

/-- **B12 反例（机器验证）：逐项非负 + 对称 ⇏ PSD**。
`F = [[1, 2], [2, 1]]`（`Fin 2` 上）对称、逐项非负，但存在方向 `d` 使 `dᵀFd < 0`
（取 `d 0 = 1`、`d 1 = −1`，值为 `−2`）。 -/
theorem ewc_psd_counterexample :
    ∃ F : Fin 2 → Fin 2 → ℝ,
      (∀ i j, 0 ≤ F i j) ∧ (∀ i j, F i j = F j i) ∧
      ∃ d : Fin 2 → ℝ, ∑ i, ∑ j, d i * F i j * d j < 0 := by
  -- `F i j := if i = j then 1 else 2`（对角 1、非对角 2），对称且逐项非负
  refine ⟨fun i j => if i = j then (1 : ℝ) else 2, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : i = j <;> simp [h]
  · intro i j
    by_cases h : i = j
    · subst h; simp
    · have hji : ¬ (j = i) := fun hh => h hh.symm
      simp [h, hji]
  · -- 取 `d 0 = 1`、`d 1 = -1`，二次型 = 1 - 2 - 2 + 1 = -2 < 0
    refine ⟨fun i => if i = 0 then (1 : ℝ) else -1, ?_⟩
    norm_num [Fin.sum_univ_two]

/-! ## 五、EWC 的矩阵二次惩罚 -/

/-- **EWC 矩阵二次惩罚**：
    `ewcQuadratic F θ θ* = Σ_i Σ_j (θ_i − θ*_i)·F_{ij}·(θ_j − θ*_j)`
    （`RealContinualLearning.ewcPenalty` 的多参数马尔可夫矩阵版本）。 -/
def ewcQuadratic (F : Fin n → Fin n → ℝ) (θ θstar : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (θ i - θstar i) * F i j * (θ j - θstar j)

/-- **EWC 二次型非负（显式 PSD 假设，诚实降级）**：
    若 `F` 满足显式半正定假设 `hpsd`（对任意方向 `d` 的二次型非负），
    则取 `d := θ − θ*` 得 `0 ≤ ewcQuadratic F θ θ*`。
    **注意**：`∀ i j, 0 ≤ F i j` 与对称性**不**蕴含 PSD，故本定理以 `hpsd` 为显式假设。 -/
theorem ewcQuadratic_nonneg (F : Fin n → Fin n → ℝ) (θ θstar : Fin n → ℝ)
    (hpsd : ∀ d : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, d i * F i j * d j) :
    0 ≤ ewcQuadratic F θ θstar := by
  unfold ewcQuadratic
  exact hpsd (fun i => θ i - θstar i)

/-- **B12 正确版本（对角情形）**：若 `F` **对角**（`i ≠ j ⟹ F i j = 0`）且逐项非负，
则 `F` 的二次型非负——即 EWC 惩罚非负。

证明：对角性使双重和只剩 `Σ_i d_i² F_{ii}`，逐项非负。
**这是 B12 在正确条件下的成立部分**（一般非对角情形为假，见 `ewc_psd_counterexample`）。 -/
theorem ewcQuadratic_nonneg_diagonal (F : Fin n → Fin n → ℝ) (θ θstar : Fin n → ℝ)
    (hdiag : ∀ i j, i ≠ j → F i j = 0) (hnn : ∀ i j, 0 ≤ F i j) :
    0 ≤ ewcQuadratic F θ θstar := by
  unfold ewcQuadratic
  refine Finset.sum_nonneg fun i _ => ?_
  have hinner : (∑ j, (θ i - θstar i) * F i j * (θ j - θstar j))
      = (θ i - θstar i) * F i i * (θ i - θstar i) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hj
      simp only [hdiag i j hj.symm, zero_mul, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hinner]
  have hsq : (θ i - θstar i) * F i i * (θ i - θstar i)
      = (θ i - θstar i) ^ 2 * F i i := by ring
  rw [hsq]
  exact mul_nonneg (sq_nonneg _) (hnn i i)

/-- **B12 正确版本（一维情形）**：`n = 1` 时「逐项非负」**确实**推出 EWC 惩罚非负
（一维矩阵恒为对角，故退化为 `(θ₀ − θ*₀)² · F₀₀ ≥ 0`）。 -/
theorem ewcQuadratic_nonneg_one_dim (F : Fin 1 → Fin 1 → ℝ) (θ θstar : Fin 1 → ℝ)
    (hnn : ∀ i j, 0 ≤ F i j) :
    0 ≤ ewcQuadratic F θ θstar := by
  unfold ewcQuadratic
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  have hsq : (θ 0 - θstar 0) * F 0 0 * (θ 0 - θstar 0)
      = (θ 0 - θstar 0) ^ 2 * F 0 0 := by ring
  rw [hsq]
  exact mul_nonneg (sq_nonneg _) (hnn 0 0)

/-! ## 六、维度退化：连接 `RealContinualLearning` 与 `RealFisherInfo` -/

/-- **一维退化到 `ewcPenalty`（主结果）**：
    `ewcQuadratic F θ θ* = ewcPenalty (2·F 0 0) (θ 0) (θ* 0)`。 -/
theorem ewcQuadratic_one_dim (F : Fin 1 → Fin 1 → ℝ) (θ θstar : Fin 1 → ℝ) :
    ewcQuadratic F θ θstar = ewcPenalty (2 * F 0 0) (θ 0) (θstar 0) := by
  unfold ewcQuadratic ewcPenalty
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  ring

/-- **矩阵 Fisher 在一维退化为 `fisherInfo`（主结果）**：
    `fisherMatrix (fun t => q (t 0)) (fun _ => θ) 0 0 = fisherInfo q θ`。
    即 `n = 1` 时 `logScoreAt` 恰是 `RealFisherInfo.score`。 -/
theorem fisherMatrix_eq_fisherInfo_one_dim (q : ℝ → Fin k → ℝ) (θ : ℝ) :
    fisherMatrix (fun (t : Fin 1 → ℝ) => q (t 0)) (fun _ => θ) 0 0 = fisherInfo q θ := by
  unfold fisherMatrix fisherInfo
  apply Finset.sum_congr rfl
  intro a _
  have hscore : logScoreAt (fun (t : Fin 1 → ℝ) => q (t 0)) (fun _ : Fin 1 => θ) a 0
      = score q θ a := by
    unfold logScoreAt score
    have hfun : (fun t : ℝ => Real.log ((fun (s : Fin 1 → ℝ) => q (s 0))
          (Function.update (fun _ : Fin 1 => θ) 0 t) a))
        = fun t : ℝ => Real.log (q t a) := by
      funext t
      simp [Function.update]
    rw [hfun]
  rw [hscore]
  show q θ a * score q θ a * score q θ a = q θ a * score q θ a ^ 2
  ring

/-! ## 注：闭环语义
  逐坐标 score 定义（logScoreAt）→ 矩阵 Fisher（fisherMatrix）→
  对称性（fisherMatrix_symm）→ 二次型（fisherQuadForm）→
  二次型恒等式（fisherQuadForm_eq_fisherMatrix）→ 非负性（fisherQuadForm_nonneg）→
  半正定（fisherMatrix_psd）→ 零方向（fisherMatrix_zero_direction）→
  零方向的 score 为零（fisherMatrix_zero_direction_score）→
  EWC 矩阵二次惩罚（ewcQuadratic）→ 非负性（ewcQuadratic_nonneg，显式 PSD 假设）→
  一维退化（ewcQuadratic_one_dim → RealContinualLearning.ewcPenalty）→
  维度退化兼容（fisherMatrix_eq_fisherInfo_one_dim → RealFisherInfo.fisherInfo）。
  诚实降级：EWC 非负性以显式 PSD 假设 hpsd 给出（对称 + 逐项非负不足）；
  Fisher 不从二阶 Fréchet 导数推导；多参数 score 期望为零的微分恒等式未做；完整 MAML 收敛定理未做。 -/

end Lattice
