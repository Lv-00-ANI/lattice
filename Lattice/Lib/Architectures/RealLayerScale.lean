import Mathlib

/-!
# LATTICE: LayerScale —— 近恒等残差缩放的界与组合

CaiT 提出 LayerScale：在残差分支上加一个可学习的小对角缩放

    layerScale lam f x = x + lam · f x      （标量实例；向量形式为 x + diag(lam)·f(x)）

工程动机是**深网可训练性**：lam 初始化很小 ⟹ 每个 block 接近恒等 ⟹ 深度方向的
信号/梯度不被放大。本文件把这一动机形式化为可证命题（模型无关，`f` 任意）：

  1. `layerscale_zero`：lam = 0 时严格恒等；
  2. `layerscale_sub` / `layerscale_deviation_bound`：偏离恒等的量 = |lam|·|f x|；
  3. `layerscale_deviation_mono`：偏离量关于 |lam| 单调（lam 越小越接近恒等）；
  4. `layerscale_interpolate`：**lam ∈ [0,1] 时 LayerScale 是恒等与残差分支的凸组合**
       x + lam·f(x) = (1-lam)·x + lam·(x + f(x))；
  5. `layerscale_abs_le_convex`：由 4 得凸性型界 |LS| ≤ (1-lam)|x| + lam|x + f x|；
  6. `layerscale_lipschitz`：`f` 为 L-Lipschitz ⟹ LS 为 (1 + |lam|L)-Lipschitz；
  7. `layerscale_chain`：两块（mu 在 f 上、lam 在 g 上）组合的利普希茨常数为乘积
       (1+|mu|L)(1+|lam|M)（为深度方向常数估计提供归纳基元）；
  8. `layerscale_abs_le_two`：|lam| ≤ 1 且 |f x| ≤ |x| ⟹ |LS x| ≤ 2|x|。

**诚实边界**：
- 恒等性/凸组合/利普希茨三条是**精确恒等式与界**，无额外假设；
- 第 3 条只断言"偏离量随 |lam| 单调"，**并未**断言训练收敛性或梯度范数减小
  （那需要损失函数与反向传播模型，属训练线，本文件不涉及）；
- 深度方向的 `(1+|lam|L)^n` 增长律由 7 的归纳给出，本文未展开归纳（标注：未做）；
- 标量实例，向量化是逐坐标直和（与 `RealResidual` 的同类约定一致）。

无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-- LayerScale：`layerScale lam f x = x + lam·f x`。 -/
def layerScale (lam : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := x + lam * f x

/-- lam = 0 时 LayerScale 是恒等映射。 -/
theorem layerscale_zero (f : ℝ → ℝ) : layerScale 0 f = fun x => x := by
  funext x
  unfold layerScale
  ring

/-- 偏离恒等的精确表达式。 -/
theorem layerscale_sub (lam : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    layerScale lam f x - x = lam * f x := by
  unfold layerScale
  ring

/-- 偏离量 = |lam|·|f x|。 -/
theorem layerscale_deviation_bound (lam : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    |layerScale lam f x - x| = |lam| * |f x| := by
  rw [layerscale_sub, abs_mul]

/-- 偏离量关于 |lam| 单调：lam 越小，block 越接近恒等。 -/
theorem layerscale_deviation_mono {lam lam' : ℝ} (h : |lam| ≤ |lam'|) (f : ℝ → ℝ) (x : ℝ) :
    |layerScale lam f x - x| ≤ |layerScale lam' f x - x| := by
  rw [layerscale_deviation_bound, layerscale_deviation_bound]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

/-- lam ∈ [0,1] 时 LayerScale 是恒等与残差分支的凸组合。 -/
theorem layerscale_interpolate (lam : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    layerScale lam f x = (1 - lam) * x + lam * (x + f x) := by
  unfold layerScale
  ring

/-- 凸组合型界（lam ∈ [0,1]）。 -/
theorem layerscale_abs_le_convex {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (f : ℝ → ℝ) (x : ℝ) :
    |layerScale lam f x| ≤ (1 - lam) * |x| + lam * |x + f x| := by
  rw [layerscale_interpolate]
  calc |(1 - lam) * x + lam * (x + f x)| ≤ |(1 - lam) * x| + |lam * (x + f x)| := abs_add _ _
    _ = (1 - lam) * |x| + lam * |x + f x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam), abs_of_nonneg h0]

/-- `f` 为 L-Lipschitz ⟹ `layerScale lam f` 为 (1 + |lam|L)-Lipschitz。 -/
theorem layerscale_lipschitz {lam L : ℝ} (_hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) (x y : ℝ) :
    |layerScale lam f x - layerScale lam f y| ≤ (1 + |lam| * L) * |x - y| := by
  have h : layerScale lam f x - layerScale lam f y = (x - y) + lam * (f x - f y) := by
    unfold layerScale
    ring
  rw [h]
  calc |(x - y) + lam * (f x - f y)| ≤ |x - y| + |lam * (f x - f y)| := abs_add _ _
    _ = |x - y| + |lam| * |f x - f y| := by rw [abs_mul]
    _ ≤ |x - y| + |lam| * (L * |x - y|) := by
        have h2 : |lam| * |f x - f y| ≤ |lam| * (L * |x - y|) :=
          mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg _)
        linarith
    _ = (1 + |lam| * L) * |x - y| := by ring

/-- 两块 LayerScale 组合的利普希茨常数是两常数的乘积（深度方向的归纳基元）。 -/
theorem layerscale_chain {lam mu L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    {f g : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hg : ∀ x y, |g x - g y| ≤ M * |x - y|) (x y : ℝ) :
    |layerScale lam g (layerScale mu f x) - layerScale lam g (layerScale mu f y)|
      ≤ ((1 + |mu| * L) * (1 + |lam| * M)) * |x - y| := by
  have h1 : |layerScale mu f x - layerScale mu f y| ≤ (1 + |mu| * L) * |x - y| :=
    layerscale_lipschitz hL hf x y
  have h2 := layerscale_lipschitz (lam := lam) hM hg (layerScale mu f x) (layerScale mu f y)
  have hpos : 0 ≤ 1 + |lam| * M := by
    have h : 0 ≤ |lam| * M := mul_nonneg (abs_nonneg _) hM
    linarith
  calc |layerScale lam g (layerScale mu f x) - layerScale lam g (layerScale mu f y)|
      ≤ (1 + |lam| * M) * |layerScale mu f x - layerScale mu f y| := h2
    _ ≤ (1 + |lam| * M) * ((1 + |mu| * L) * |x - y|) := mul_le_mul_of_nonneg_left h1 hpos
    _ = ((1 + |mu| * L) * (1 + |lam| * M)) * |x - y| := by ring

/-- 缩放界：|lam| ≤ 1 且 |f x| ≤ |x| ⟹ |LS x| ≤ 2|x|。 -/
theorem layerscale_abs_le_two {lam : ℝ} (hlam : |lam| ≤ 1) (f : ℝ → ℝ) {x : ℝ}
    (hfx : |f x| ≤ |x|) : |layerScale lam f x| ≤ 2 * |x| := by
  have h : layerScale lam f x = x + lam * f x := rfl
  rw [h]
  calc |x + lam * f x| ≤ |x| + |lam * f x| := abs_add _ _
    _ = |x| + |lam| * |f x| := by rw [abs_mul]
    _ ≤ |x| + 1 * |x| := by
        have hb : |lam| * |f x| ≤ 1 * |x| := mul_le_mul hlam hfx (abs_nonneg _) zero_le_one
        linarith
    _ = 2 * |x| := by ring

end Lattice
