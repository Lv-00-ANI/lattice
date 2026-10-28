import Mathlib

/-!
# LATTICE: 同余约束的 sin² 周期代理损失

调研（research/embedding/README.md）标出的可微化**唯一缺口**：
同余约束 x ≡ a (mod m) 目前只有离散语义（ModConstraint.lean：m ∣ x-a），
没有可微的「零化 ⟺ 满足」损失代理。

本文件给出并证明 sin² 周期代理：
  L(x) = sin²(π · (x - a) / m)   （x, a, m : ℤ，m ≠ 0，L 为 ℝ 值）

定理（P5）：
  同余满足（m ∣ x - a） ⟺ 代理损失为零。

核心引理：Real.sin_eq_zero_iff（sin θ = 0 ⟺ θ ∈ ℤ·π，Mathlib）
+ sin_int_mul_pi（sin(nπ) = 0）+ π ≠ 0 消去 + Int↔ℝ 单射。

纯 ℝ（Mathlib）。
-/

namespace Lattice

open scoped Real

noncomputable section

/-! ## 同余约束（符号侧，Int） -/

def CongruentInt (x a m : ℤ) : Prop := m ∣ x - a

/-! ## sin² 周期代理损失（ℝ 值） -/

def ModSinLoss (x a m : ℤ) : ℝ :=
  (Real.sin (π * ((x : ℝ) - (a : ℝ)) / (m : ℝ))) ^ 2

/-! ## 引理一：π ≠ 0（实数） -/

lemma pi_ne_zero : π ≠ 0 := by
  exact Real.pi_ne_zero

/-! ## 引理二：sin(n·π) = 0（n : ℤ，Mathlib） -/

lemma sin_int_mul_pi_zero (n : ℤ) : Real.sin (n * π) = 0 := by
  exact Real.sin_int_mul_pi n

/-! ## 引理三：sin θ = 0 ⟺ ∃ n : ℤ, θ = n·π（Mathlib） -/

lemma sin_eq_zero_iff_int (θ : ℝ) : Real.sin θ = 0 ↔ ∃ n : ℤ, θ = n * π := by
  constructor
  · intro hs
    rcases (Real.sin_eq_zero_iff.mp hs) with ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact Real.sin_eq_zero_iff.mpr ⟨n, hn.symm⟩

/-! ## 定理一：同余满足 ⟹ 代理损失为零（正向）
m ∣ x - a ⟹ sin²(π(x-a)/m) = 0。 -/

theorem modSinLoss_of_congruent (x a m : ℤ) (h : CongruentInt x a m) :
    ModSinLoss x a m = 0 := by
  unfold ModSinLoss CongruentInt at *
  rcases h with ⟨k, hk⟩
  -- x - a = m·k ⟹ (x-a)/m = k（需 m ≠ 0）
  by_cases hm : (m : ℝ) = 0
  · -- m = 0：0 ∣ x-a ⟹ x - a = 0·k = 0；ℝ 中除以零 = 0，损失 = 0
    have hmz : m = 0 := Int.cast_eq_zero.mp hm
    have hx : (x : ℝ) - (a : ℝ) = 0 := by
      have : x - a = 0 := by simpa [hmz] using hk
      exact_mod_cast this
    simp [hx, hm]
  · -- m ≠ 0：消去（m·k = x-a ⟹ (x-a)/m = k）
    have hxma : ((x : ℝ) - (a : ℝ)) / (m : ℝ) = (k : ℝ) := by
      have hkR : ((x : ℝ) - (a : ℝ)) = ((m * k : ℤ) : ℝ) := by
        exact_mod_cast hk
      rw [hkR, Int.cast_mul]
      simpa [mul_comm] using mul_div_cancel_right₀ (k : ℝ) hm
    -- 括号调整后代入：(π·(x-a))/m = π·((x-a)/m)
    rw [mul_div_assoc, hxma]
    -- sin(π·k) = 0
    have hs : Real.sin (π * (k : ℝ)) = 0 := by
      -- π·k = k·π（交换）→ sin_int_mul_pi
      have : π * (k : ℝ) = (k : ℝ) * π := by ring
      rw [this]
      exact sin_int_mul_pi_zero k
    simp [hs]

/-! ## 定理二：代理损失为零 ⟹ 同余满足（反向）
sin²(π(x-a)/m) = 0 ⟹ m ∣ x - a（需 m ≠ 0）。 -/

theorem congruent_of_modSinLoss_zero (x a m : ℤ) (hm : m ≠ 0)
    (h : ModSinLoss x a m = 0) : CongruentInt x a m := by
  unfold ModSinLoss CongruentInt at *
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  -- sin²(θ) = 0 ⟹ sin θ = 0
  have hs : Real.sin (π * ((x : ℝ) - (a : ℝ)) / (m : ℝ)) = 0 := by
    have : (Real.sin (π * ((x : ℝ) - (a : ℝ)) / (m : ℝ))) ^ 2 = 0 := by simpa using h
    exact sq_eq_zero_iff.mp this
  -- sin θ = 0 ⟹ ∃ n, θ = n·π
  rcases (sin_eq_zero_iff_int _).mp hs with ⟨n, hn⟩
  -- π·(x-a)/m = n·π ⟹ (x-a)/m = n（π ≠ 0）
  have hdiv : ((x : ℝ) - (a : ℝ)) / (m : ℝ) = (n : ℝ) := by
    -- 两边除以 π（π ≠ 0 消去）
    have hπmul : π * (((x : ℝ) - (a : ℝ)) / (m : ℝ)) = π * (n : ℝ) := by
      calc
        π * (((x : ℝ) - (a : ℝ)) / (m : ℝ)) = π * ((x : ℝ) - (a : ℝ)) / (m : ℝ) := by
          rw [mul_div_assoc']
        _ = (n : ℝ) * π := by
          simpa using hn
        _ = π * (n : ℝ) := by ring
    exact mul_left_cancel₀ pi_ne_zero hπmul
  -- (x-a)/m = n ⟹ x-a = n·m（乘以 m，m ≠ 0）
  have hxma : (x : ℝ) - (a : ℝ) = (n : ℝ) * (m : ℝ) := by
    calc
      (x : ℝ) - (a : ℝ) = (((x : ℝ) - (a : ℝ)) / (m : ℝ)) * (m : ℝ) := by
        rw [div_mul_cancel₀ _ hmR]
      _ = (n : ℝ) * (m : ℝ) := by rw [hdiv]
  -- ℝ 等式 → Int 等式（Int 嵌入 ℝ 单射）→ 整除
  have hint : x - a = n * m := by
    have hc : ((x - a : ℤ) : ℝ) = ((n * m : ℤ) : ℝ) := by
      simpa using hxma
    exact Int.cast_inj.mp hc
  exact ⟨n, by simpa [mul_comm] using hint⟩

/-! ## 定理三：P5 完整形式 —— 零化 ⟺ 满足（m ≠ 0 时）
sin² 周期代理的「零损失点 = 同余满足点」。 -/

theorem modSinLoss_zero_iff_congruent (x a m : ℤ) (hm : m ≠ 0) :
    ModSinLoss x a m = 0 ↔ CongruentInt x a m := by
  constructor
  · exact congruent_of_modSinLoss_zero x a m hm
  · exact modSinLoss_of_congruent x a m

end

end Lattice
