import Mathlib
import Lattice.Lib.Convex.RealSubgradient
/-!
# LATTICE: 近端算子（proximal operator）—— 变分刻画与非扩张性（约束优化线）

RealSubgradient 用次梯度刻画非光滑驻点；本文件引入**近端算子**（proximal operator），
即非光滑凸优化的标准「隐式梯度步」：

    prox_{η f}(x) = argmin_y [ f(y) + (1/(2η))·‖y − x‖² ]。

argmin 在 Lean 里不便直接形式化（需选择 + 唯一性），本文件改用**变分/极小刻画**：

  `IsProx f η x p`  ⟺  p 使 y ↦ f(y) + (1/(2η))‖y−x‖² 取到全局最小；

并引入由凸性推出的**变分不等式形式**：

  `ProxVI f η x p`  ⟺  ∀ y, f(p) + (1/η)·(x−p)·(y−p) ≤ f(y)   （一维，内积 = 乘法）。

定理清单：
  1. `prox_vi_aux`（辅助）：对 t ∈ (0,1]，由凸性 `ConvexOn ℝ univ f` + `IsProx` 得
        f(p) + (1/η)(x−p)(z−p) ≤ f(z) + (t/(2η))(z−p)²；
  2. `prox_vi_of_isProx`（**凸性桥**）：对 t → 0 取极限，得到标准近端变分不等式
        f(p) + (1/η)(x−p)(y−p) ≤ f(y)（∀y）；
  3. `prox_nonexpansive`（**核心**）：f 凸、p 是 x 的 prox、q 是 y 的 prox ⟹
        ‖p−q‖ ≤ ‖x−y‖。标准证明：两条变分不等式相加 ⟹ (1/η)‖p−q‖² ≤ (1/η)⟪x−y, p−q⟫
        ⟹ ‖p−q‖² ≤ ‖x−y‖·‖p−q‖ ⟹ 约去 ‖p−q‖；
  4. `prox_unique`：凸 f 的 prox 唯一（同一条变分不等式链，取 x = y）；
  5. `prox_self_of_minimizer`：全局最小点是自身的 prox（x = p，不动点视角）；
  6. `prox_linear`：f(y) = c·y 的 prox 显式解 x − η·c（existence 范例）；
     `prox_exists_linear`：该情形 prox 存在；
  7. `prox_grad_step_fixed`：线性目标时 prox 恰是梯度步 x − η·∇f(x)（与 RealGradDescent
     的无约束梯度步衔接）。

诚实边界：
  · **一般存在性未证**（需要 f 下半连续、凸、coercive 等条件；mathlib 无现成的
    一维 prox 存在性定理）——本文件只给出**线性目标**的存在性范例，并在下面显式标注；
  · 凸性一律用 mathlib 的 `ConvexOn ℝ Set.univ`；一维内积即乘法，故变分不等式写成
    普通实数乘积形式（与 ‖·‖² 的换元由 `real_norm_sq` 处理）；
  · 非扩张结论对**同一 η** 成立（两个 prox 必须用同一步长），这是标准形式。
-/

noncomputable section

namespace Lattice

/-! 辅助：实数范数平方 = 平方（`real_norm_sq`，`simp` 化）。 -/

@[simp] lemma real_norm_sq (a : ℝ) : ‖a‖ ^ 2 = a ^ 2 := by
  rw [Real.norm_eq_abs, sq_abs]

/-! ## 一、近端算子的两种刻画 -/

/-- **近端算子（极小刻画）**：p 使 y ↦ f(y) + (1/(2η))·‖y − x‖² 取到全局最小。
这是 `prox_{η f}(x) = argmin` 的无选择形式化。 -/
def IsProx (f : ℝ → ℝ) (η x p : ℝ) : Prop :=
  ∀ y : ℝ, f p + (1 / (2 * η)) * ‖p - x‖ ^ 2 ≤ f y + (1 / (2 * η)) * ‖y - x‖ ^ 2

/-- **近端变分不等式**：∀ y, f(p) + (1/η)·(x−p)·(y−p) ≤ f(y)。
凸 f 时与 `IsProx` 等价（正向 `prox_vi_of_isProx`）。 -/
def ProxVI (f : ℝ → ℝ) (η x p : ℝ) : Prop :=
  ∀ y : ℝ, f p + (1 / η) * ((x - p) * (y - p)) ≤ f y

/-! ## 二、凸性桥：IsProx ⟹ ProxVI

对 t ∈ (0,1] 取 z_t = (1−t)p + tz，分别用 `IsProx`（在 z_t 处）与凸性上界 f(z_t)，
消去 f(z_t) 后除以 t，再令 t → 0。 -/

/-- 辅助引理：t ∈ (0,1] 时
f(p) + (1/η)(x−p)(z−p) ≤ f(z) + (t/(2η))(z−p)²。 -/
lemma prox_vi_aux {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f) {η x p : ℝ} (z t : ℝ)
    (hη : 0 < η) (hprox : IsProx f η x p) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    f p + (1 / η) * ((x - p) * (z - p)) ≤ f z + (t / (2 * η)) * (z - p) ^ 2 := by
  have hηne : η ≠ 0 := ne_of_gt hη
  have h4η : (0 : ℝ) < 2 * η := by linarith
  set w : ℝ := t * z + (1 - t) * p with hw
  have hw_eq : w = p + t * (z - p) := by rw [hw]; ring
  -- 凸性：f(w) ≤ t·f z + (1−t)·f p
  have hconvw : f w ≤ t * f z + (1 - t) * f p := by
    have hcf := hconv.2
    have h := hcf (Set.mem_univ z) (Set.mem_univ p) (a := t) (b := 1 - t)
      (le_of_lt ht0) (by linarith) (by ring)
    simpa [hw, smul_eq_mul] using h
  -- IsProx 在 w 处
  have hproxw : f p + (1 / (2 * η)) * ‖p - x‖ ^ 2 ≤ f w + (1 / (2 * η)) * ‖w - x‖ ^ 2 := hprox w
  rw [real_norm_sq, real_norm_sq] at hproxw
  -- 差 (w−x)² − (p−x)² = 2t(p−x)(z−p) + t²(z−p)²
  have hdiff : (w - x) ^ 2 - (p - x) ^ 2
      = 2 * t * (p - x) * (z - p) + t ^ 2 * (z - p) ^ 2 := by
    rw [hw_eq]; ring
  -- 消去 f w：t(f p − f z) ≤ (1/(2η))((w−x)² − (p−x)²)
  have step1 : t * (f p - f z)
      ≤ t * ((1 / η) * (p - x) * (z - p) + (t / (2 * η)) * (z - p) ^ 2) := by
    have hbase : t * (f p - f z) ≤ (1 / (2 * η)) * ((w - x) ^ 2 - (p - x) ^ 2) := by
      nlinarith [hproxw, hconvw]
    have heq : (1 / (2 * η)) * ((w - x) ^ 2 - (p - x) ^ 2)
        = t * ((1 / η) * (p - x) * (z - p) + (t / (2 * η)) * (z - p) ^ 2) := by
      rw [hdiff]; field_simp; ring
    rwa [heq] at hbase
  -- 除以 t > 0
  have step2 := (mul_le_mul_left ht0).mp step1
  -- 收尾：(1/η)(p−x)(z−p) = −(1/η)(x−p)(z−p)
  have hneg : (1 / η) * ((x - p) * (z - p)) = -((1 / η) * (p - x) * (z - p)) := by ring
  rw [hneg]
  linarith

/-- **凸性桥**：f 凸、p 是 x 的 prox ⟹ 标准近端变分不等式
∀ y, f(p) + (1/η)(x−p)(y−p) ≤ f(y)。（由 `prox_vi_aux` 令 t → 0 取极限。） -/
theorem prox_vi_of_isProx {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f) {η x p : ℝ}
    (hη : 0 < η) (hprox : IsProx f η x p) : ProxVI f η x p := by
  intro z
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hd : (z - p) ^ 2 = 0
  · have h1 := prox_vi_aux hconv z 1 hη hprox (by norm_num) (by norm_num)
    rw [hd] at h1
    nlinarith
  · have hdpos : 0 < (z - p) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hd)
    have h4η : (0 : ℝ) < 2 * η := by linarith
    have hηne : η ≠ 0 := ne_of_gt hη
    set t : ℝ := min 1 (ε * (2 * η) / (z - p) ^ 2) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos (mul_pos hε h4η) hdpos)
    have ht1 : t ≤ 1 := min_le_left _ _
    have hb := prox_vi_aux hconv z t hη hprox ht0 ht1
    -- t·(z−p)² ≤ ε·(2η)
    have htd : t * (z - p) ^ 2 ≤ ε * (2 * η) := by
      have hle : t ≤ ε * (2 * η) / (z - p) ^ 2 := min_le_right _ _
      have h := mul_le_mul_of_nonneg_right hle (le_of_lt hdpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hdpos)] at h
    -- (t/(2η))·(z−p)² ≤ ε
    have hfin : (t / (2 * η)) * (z - p) ^ 2 ≤ ε := by
      have he : (t / (2 * η)) * (z - p) ^ 2 * (2 * η) = t * (z - p) ^ 2 := by
        field_simp
      have hmul : (t / (2 * η)) * (z - p) ^ 2 * (2 * η) ≤ ε * (2 * η) := by
        rw [he]; exact htd
      exact (mul_le_mul_right h4η).mp hmul
    linarith

/-! ## 三、核心：prox 非扩张 -/

/-- **核心定理（近端算子非扩张）**：f 凸、p 是 x 的 prox、q 是 y 的 prox（同步长 η > 0）
⟹ ‖p − q‖ ≤ ‖x − y‖。
证明：两条变分不等式（分别取 y := q、y := p）相减，得 (1/η)‖p−q‖² ≤ (1/η)⟪x−y, p−q⟫，
即 ‖p−q‖² ≤ (x−y)(p−q) ≤ ‖x−y‖·‖p−q‖，约去 ‖p−q‖。 -/
theorem prox_nonexpansive {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f) {η x y p q : ℝ}
    (hη : 0 < η) (hp : IsProx f η x p) (hq : IsProx f η y q) :
    ‖p - q‖ ≤ ‖x - y‖ := by
  have hVIp := prox_vi_of_isProx hconv hη hp
  have hVIq := prox_vi_of_isProx hconv hη hq
  have h1 : f p + (1 / η) * ((x - p) * (q - p)) ≤ f q := hVIp q
  have h2 : f q + (1 / η) * ((y - q) * (p - q)) ≤ f p := hVIq p
  -- 相加： (1/η)[(x−p)(q−p) + (y−q)(p−q)] ≤ 0
  have hkey : (1 / η) * ((p - q) * (p - q)) ≤ (1 / η) * ((x - y) * (p - q)) := by
    have hsum : (1 / η) * ((x - p) * (q - p)) + (1 / η) * ((y - q) * (p - q)) ≤ 0 := by
      linarith
    have hcomb : (1 / η) * ((x - p) * (q - p)) + (1 / η) * ((y - q) * (p - q))
        = (1 / η) * ((p - q) * (p - q)) - (1 / η) * ((x - y) * (p - q)) := by ring
    linarith
  have hηinv : (0 : ℝ) < 1 / η := by positivity
  have hsq : (p - q) * (p - q) ≤ (x - y) * (p - q) := (mul_le_mul_left hηinv).mp hkey
  -- 转绝对值并约去 ‖p−q‖
  have hbound : (p - q) ^ 2 ≤ |x - y| * |p - q| := by
    calc (p - q) ^ 2 = (p - q) * (p - q) := by ring
      _ ≤ (x - y) * (p - q) := hsq
      _ ≤ |(x - y) * (p - q)| := le_abs_self _
      _ = |x - y| * |p - q| := abs_mul _ _
  have habs : |p - q| ^ 2 ≤ |x - y| * |p - q| := by
    rwa [sq_abs]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases h0 : |p - q| = 0
  · rw [h0]; exact abs_nonneg _
  · have hpos : 0 < |p - q| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
    have h' : |p - q| * |p - q| ≤ |x - y| * |p - q| := by
      simpa [pow_two] using habs
    exact (mul_le_mul_right hpos).mp h'

/-! ## 四、唯一性与不动点 -/

/-- 凸 f 的 prox 唯一（两条变分不等式取 x = y 相加）。 -/
theorem prox_unique {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f) {η x p q : ℝ}
    (hη : 0 < η) (hp : IsProx f η x p) (hq : IsProx f η x q) : p = q := by
  have hVIp := prox_vi_of_isProx hconv hη hp
  have hVIq := prox_vi_of_isProx hconv hη hq
  have h1 : f p + (1 / η) * ((x - p) * (q - p)) ≤ f q := hVIp q
  have h2 : f q + (1 / η) * ((x - q) * (p - q)) ≤ f p := hVIq p
  have hsum : (1 / η) * ((x - p) * (q - p)) + (1 / η) * ((x - q) * (p - q)) ≤ 0 := by linarith
  have hcomb : (1 / η) * ((x - p) * (q - p)) + (1 / η) * ((x - q) * (p - q))
      = (1 / η) * ((p - q) * (p - q)) := by ring
  have hsq : (p - q) * (p - q) ≤ 0 := by
    have hηinv : (0 : ℝ) < 1 / η := by positivity
    have hz : (1 / η) * ((p - q) * (p - q)) ≤ 0 := by linarith
    exact (mul_le_mul_left hηinv).mp (by rw [mul_zero]; exact hz)
  have hz : (p - q) ^ 2 = 0 := by nlinarith [sq_nonneg (p - q)]
  have h0 : p - q = 0 := sq_eq_zero_iff.mp hz
  exact sub_eq_zero.mp h0

/-- 全局最小点是自身的 prox（不动点视角）：∀y, f p ≤ f y ⟹ IsProx f η p p（η > 0）。 -/
theorem prox_self_of_minimizer {f : ℝ → ℝ} {η p : ℝ} (hη : 0 < η)
    (hmin : ∀ y : ℝ, f p ≤ f y) : IsProx f η p p := by
  intro y
  have h1 : f p ≤ f y := hmin y
  have h2 : (0 : ℝ) ≤ (1 / (2 * η)) * ‖y - p‖ ^ 2 := by positivity
  have hp0 : ‖p - p‖ ^ 2 = 0 := by simp
  rw [hp0, mul_zero, add_zero]
  linarith

/-! ## 五、范例：线性目标的显式 prox（存在性）

    f(y) = c·y  ⟹  prox_{η f}(x) = x − η·c。

这给出 prox 的存在性范例，并说明「prox 是隐式梯度步」；一般 f 的存在性
（需下半连续 + 凸 + coercive）标注为后续工作。 -/

/-- **线性目标的显式 prox**：IsProx (c·) η x (x − ηc)。 -/
theorem prox_linear (c η x : ℝ) (hη : 0 < η) :
    IsProx (fun y : ℝ => c * y) η x (x - η * c) := by
  intro y
  have hηne : η ≠ 0 := ne_of_gt hη
  rw [real_norm_sq, real_norm_sq]
  have hpos : (0 : ℝ) < 1 / (2 * η) := by positivity
  have hnn : 0 ≤ (1 / (2 * η)) * (y - x + η * c) ^ 2 := mul_nonneg (le_of_lt hpos) (sq_nonneg _)
  have hdiff : c * y + 1 / (2 * η) * (y - x) ^ 2
      - (c * (x - η * c) + 1 / (2 * η) * (x - η * c - x) ^ 2)
      = (1 / (2 * η)) * (y - x + η * c) ^ 2 := by
    field_simp; ring
  linarith

/-- 线性目标的 prox 存在（`prox_exists` 的可证特例）。 -/
theorem prox_exists_linear (c η x : ℝ) (hη : 0 < η) :
    ∃ p : ℝ, IsProx (fun y : ℝ => c * y) η x p :=
  ⟨x - η * c, prox_linear c η x hη⟩

/-- **prox 与梯度步的关系（`prox_grad_step_fixed`）**：线性目标 f(y) = c·y 时，
prox 恰是梯度步 x − η·∇f(x)——即 prox 是无约束梯度步的隐式推广。 -/
theorem prox_grad_step_fixed (c η x : ℝ) (hη : 0 < η) :
    IsProx (fun y : ℝ => c * y) η x (x - η * deriv (fun y : ℝ => c * y) x) := by
  have hderiv : deriv (fun y : ℝ => c * y) x = c := by
    have h : HasDerivAt (fun y : ℝ => c * y) (c * 1) x := by
      simpa using (hasDerivAt_id x).const_mul c
    simpa using h.deriv
  rw [hderiv]
  exact prox_linear c η x hη

/-! ## 注：闭环语义
  近端算子 = 非光滑凸优化的隐式梯度步：`prox_nonexpansive` 说明它 1-Lipschitz，
  与 RealProjGrad 的投影（1-Lipschitz）同属「非扩张算子」家族——事实上指示函数
  ι_C 的 prox 正是 C 上的投影，本文件只在该线性范例中给出显式解。
  诚实边界：一般 f 的 prox 存在性（下半连续 + 凸 + coercive）与
  「prox 是 firmly nonexpansive（更强）」「prox ⟺ 投影的特殊情形」标注为后续工作。 -/

end Lattice
