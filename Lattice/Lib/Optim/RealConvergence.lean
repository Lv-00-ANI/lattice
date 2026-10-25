import Mathlib

/-!
# LATTICE: 循环收敛 —— 度量递减 ⟹ ε-终止（验证循环的终止语义）

控制流三要素的**终止条件**补全：
  · 不变量（RealLoop）：P 保持 ⟹ n 次迭代后 P 保持（循环正确性）；
  · **收敛（本文件）**：误差度量几何收缩 ⟹ 误差最终任意小（循环终止性）。

定理（通用骨架，模型无关）：
  若误差序列 e : ℕ → ℝ 满足
    1. 每步收缩：e(n+1) ≤ c·e(n)，0 ≤ c < 1；
    2. 非负：e(n) ≥ 0；
  则 ∀ ε > 0，∃ n，e(n) < ε（误差 ε-终止）。

证明：
  1. 上界：e(n) ≤ cⁿ·e(0)（归纳，收缩 + 乘法保序）；
  2. 等比序列 cⁿ → 0（tendsto_pow_atTop_nhds_zero_of_lt_one，mathlib）；
  3. 夹逼：e(n) ≤ cⁿ·e(0) < ε（ε 任意小 ⟹ cⁿ < ε/e(0)）。

实例化（衔接验证循环）：
  · even_loop_converges（奇偶修复器）是 e(n+1) ≤ c·e(n) 的特例；
  · VerifyLoopProgress 的回路终止条件 = 误差 ε-终止后验证器放行；
  · 梯度下降（平方损失）的收缩步满足此骨架（谱界假设下）。

模型无关：任意线性序域上的误差度量、任意收缩系数。
-/

noncomputable section

open Filter

open scoped Topology

namespace Lattice

/-! ## 定理一：几何上界（收缩 ⟹ 指数衰减）
e(n+1) ≤ c·e(n)（0 ≤ c）⟹ e(n) ≤ cⁿ·e(0)。-/

theorem contraction_pow_bound {e : ℕ → ℝ} (c : ℝ)
    (hc0 : 0 ≤ c) (hstep : ∀ n : ℕ, e (n + 1) ≤ c * e n) :
    ∀ n : ℕ, e n ≤ c ^ n * e 0 := by
  intro n
  induction n with
  | zero =>
      -- e 0 ≤ c⁰·e 0 = e 0
      simp
  | succ n ih =>
      calc
        e (n + 1) ≤ c * e n := hstep n
        _ ≤ c * (c ^ n * e 0) := mul_le_mul_of_nonneg_left ih hc0
        _ = c ^ (n + 1) * e 0 := by ring

/-! ## 定理二：等比序列最终任意小（c<1）
0 ≤ c < 1，0 ≤ e0 ⟹ ∀ ε > 0，∃ n，cⁿ·e0 < ε。-/

theorem geom_contraction_eventually (c : ℝ) (e0 : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (he0 : 0 ≤ e0) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, c ^ n * e0 < ε := by
  intro ε hε
  -- 情形 e0 = 0：cⁿ·0 = 0 < ε
  by_cases he0z : e0 = 0
  · rw [he0z]
    exact ⟨0, by simpa using hε⟩
  · -- e0 > 0：cⁿ → 0 ⟹ 存在 n 使 cⁿ < ε/e0
    have he0pos : 0 < e0 := lt_of_le_of_ne he0 (Ne.symm he0z)
    have hεdiv : 0 < ε / e0 := div_pos hε he0pos
    -- cⁿ → 0（0 ≤ c < 1）
    have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
    -- Iio (ε/e0) 是 0 的邻域（ε/e0 > 0）
    have hneigh : (Set.Iio (ε / e0)) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hεdiv
    -- 最终 cⁿ < ε/e0
    have hfreq : ∀ᶠ n in atTop, c ^ n < ε / e0 := hpow hneigh
    rcases (Filter.eventually_atTop.1 hfreq) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    calc
      c ^ N * e0 < (ε / e0) * e0 := mul_lt_mul_of_pos_right (hN N (le_refl N)) he0pos
      _ = ε := by field_simp [ne_of_gt he0pos]

/-! ## 定理三：误差 ε-终止（主定理）
收缩 + 非负 ⟹ ∀ ε > 0，∃ n，e(n) < ε。-/

theorem contraction_converges {e : ℕ → ℝ} (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hstep : ∀ n : ℕ, e (n + 1) ≤ c * e n) (hnonneg : ∀ n : ℕ, 0 ≤ e n) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, e n < ε := by
  intro ε hε
  -- e(n) ≤ cⁿ·e(0)（上界，从初始误差 e 0 出发）
  have hbound : ∀ n : ℕ, e n ≤ c ^ n * e 0 := contraction_pow_bound c hc0 hstep
  -- ∃ n，cⁿ·(e 0) < ε（等比序列收敛；e 0 非负由 hnonneg 0 给出）
  rcases (geom_contraction_eventually c (e 0) hc0 hc1 (hnonneg 0) ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  nlinarith [hbound N, hN, hnonneg N]

/-! ## 注：循环语义三要素齐备
  顺序（AllSatisfied/约束序列编译）✅
  分支（RealBranch 门控路由）✅
  循环（RealLoop 不变量 + 本文件收敛终止）✅
  —— 约束程序的循环控制流完整形式化；ε-终止正是 VerifyLoop
  回路「验证通过即停止」的量化语义。

实例化（衔接验证循环）：
  · even_loop_converges（奇偶修复器）对应 e(n+1) ≤ c·e(n) 的收缩步；
  · VerifyLoopProgress 回路在误差 < ε 后停止——本文件给出
    「∃ n，e(n) < ε」的量化保证（不变量 + 收敛 ⟹ 终止）。-/

end Lattice
