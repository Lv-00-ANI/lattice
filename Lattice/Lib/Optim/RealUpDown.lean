import Mathlib

/-!
# LATTICE: ↑↓ 循环与可逆提取 —— pan-meme 移植（收敛/闭包/双射/N 算子）

移植 pan-meme（level0000x/pan-meme）中与 LATTICE 相关的数学
（价值筛选：↑↓ 收敛、完全闭包、往返双射、N 算子收缩；跳过
五维 ODE/谱聚类/信息作用量等与转换层无关部分）：

  1. 单调有限序列稳定（定理 4.1 的干净核心）：有限域上单调
     非减集合序列必在有限步稳定（S_N = S_{N+1}）——↑↓ 循环
     收敛的抽象形式（pan-meme 的字词实例单调性有缺陷
     [README 自述"数学基础有bug"]，此处取单调序列的干净核心）；
  2. 完全信息闭包：稳定后 ⋃_{k≤N} S_k = S_N（有限闭包 = 最大元素，
     定理 4.7 的抽象）；
  3. 往返双射：g(f(x)) = x 且 f(g(y)) = y ⟹ f 双射（编译-提取
     往返恒等 ⟹ 提取可逆，连接 roundtrip_extract）；
  4. N 算子收缩（Def 6.12 的 A/(A+B+ε) 结构）：比例算子的
     分量 Lipschitz + 组合界（归一化算子的收缩性，衔接收敛线）。

模型无关：任意有限论域、任意单调序列、任意非负输入。
-/

namespace Lattice

/-! ## 定理一：单调有限序列稳定（↑↓ 循环收敛的干净核心）
有限域上单调非减集合序列 {S_k} 必在有限步稳定：∃N，S_N = S_{N+1}。-/

theorem monotone_finite_sequence_stabilizes {α : Type*} [Fintype α] (S : ℕ → Set α)
    (hmono : ∀ k : ℕ, S k ⊆ S (k + 1)) :
    ∃ N : ℕ, S N = S (N + 1) := by
  by_contra hnot
  -- 无稳定点：∀N，S_N ≠ S_{N+1}
  have hne : ∀ k : ℕ, S k ≠ S (k + 1) := by
    intro k
    intro h
    exact hnot ⟨k, h⟩
  -- 严格包含：S_k ⊊ S_{k+1}（单调 + 不等）
  have hss : ∀ k : ℕ, S k ⊂ S (k + 1) := by
    intro k
    exact (Set.ssubset_iff_subset_ne).2 ⟨hmono k, hne k⟩
  -- 基数严格增：ncard(S_k) < ncard(S_{k+1})
  have hcard : ∀ k : ℕ, (S k).ncard < (S (k + 1)).ncard := by
    intro k
    exact Set.ncard_lt_ncard (hss k)
  -- 归纳：ncard(S_k) ≥ k
  have hbound : ∀ k : ℕ, k ≤ (S k).ncard := by
    intro k
    induction k with
    | zero => exact zero_le _
    | succ k ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hcard k))
  -- 取 k = card α + 1：下界 ≥ card α + 1 与上界 ≤ card α 矛盾
  have hbig : Fintype.card α + 1 ≤ (S (Fintype.card α + 1)).ncard :=
    hbound (Fintype.card α + 1)
  have hsmall : (S (Fintype.card α + 1)).ncard ≤ Fintype.card α := by
    calc
      (S (Fintype.card α + 1)).ncard ≤ (Set.univ : Set α).ncard :=
        Set.ncard_le_ncard (by exact Set.subset_univ _)
      _ = Fintype.card α := by
        rw [Set.ncard_univ]
        exact Nat.card_eq_fintype_card
  have hcon : Fintype.card α + 1 ≤ Fintype.card α := le_trans hbig hsmall
  exact (Nat.not_succ_le_self (Fintype.card α)) hcon

/-! ## 定理二：完全信息闭包（定理 4.7 的抽象）
若 S_N 是前 N 步的最大元素（∀k≤N，S_k ⊆ S_N），
则完全闭包 ⋃_{k≤N} S_k = S_N（闭包 = 最大稳定集）。-/

theorem union_le_stabilized {α : Type*} (S : ℕ → Set α) (N : ℕ)
    (h : ∀ k : ℕ, k ≤ N → S k ⊆ S N) :
    (⋃ k ∈ {k : ℕ | k ≤ N}, S k) = S N := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    simp at hx
    rcases hx with ⟨k, hk, hxk⟩
    exact h k hk hxk
  · intro hx
    simpa using (⟨N, le_rfl, hx⟩ : ∃ k : ℕ, k ≤ N ∧ x ∈ S k)

/-! ## 定理三：往返恒等 ⟹ 双射（提取可逆）
g(f(x)) = x 且 f(g(y)) = y ⟹ f 是双射（编译-提取往返恒等 ⟹
提取是可逆映射，pan-meme Φ⁻¹(Φ(I)) = I 的抽象）。-/

theorem roundtrip_bijective {X Y : Type*} (f : X → Y) (g : Y → X)
    (h₁ : ∀ x : X, g (f x) = x) (h₂ : ∀ y : Y, f (g y) = y) :
    Function.Bijective f := by
  constructor
  · -- 单射：f x₁ = f x₂ ⟹ x₁ = x₂（g 保序往返）
    intro x₁ x₂ h
    calc
      x₁ = g (f x₁) := (h₁ x₁).symm
      _ = g (f x₂) := by rw [h]
      _ = x₂ := h₁ x₂
  · -- 满射：∀y，∃x，f x = y（x = g y）
    intro y
    exact ⟨g y, h₂ y⟩

/-! ## 定理四：双射 ⟺ 有逆（可逆提取的存在）
f 双射 ⟹ 存在 g 满足往返恒等（提取逆存在 iff 提取是双射）。-/

theorem bijective_iff_inverse {X Y : Type*} (f : X → Y) :
    Function.Bijective f ↔ ∃ g : Y → X, (∀ x : X, g (f x) = x) ∧ (∀ y : Y, f (g y) = y) := by
  constructor
  · intro hf
    -- 由双射构造逆：g y = 唯一的 x 使 f x = y（选择）
    rcases (Function.bijective_iff_has_inverse.mp hf) with ⟨g, hg₁, hg₂⟩
    exact ⟨g, hg₁, hg₂⟩
  · intro h
    rcases h with ⟨g, hg₁, hg₂⟩
    exact roundtrip_bijective f g hg₁ hg₂

/-! ## N 算子收缩（Def 6.12 的 A/(A+B+ε) 结构）
N(x,y) = x/(x+y+ε) 对 x 的分量 Lipschitz：|N(x,y)−N(x',y)| ≤ |x−x'|/ε。-/

theorem ratio_norm_contracts_x {ε : ℝ} (hε : 0 < ε) (x x' y : ℝ)
    (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) :
    |x / (x + y + ε) - x' / (x' + y + ε)| ≤ (1 / ε) * |x - x'| := by
  have hden1 : 0 < x + y + ε := by nlinarith
  have hden2 : 0 < x' + y + ε := by nlinarith
  -- 代数：差 = (x−x')(y+ε)/[(x+y+ε)(x'+y+ε)]
  have hcalc : x / (x + y + ε) - x' / (x' + y + ε)
      = (x - x') * (y + ε) / ((x + y + ε) * (x' + y + ε)) := by
    field_simp [ne_of_gt hden1, ne_of_gt hden2]
    ring
  rw [hcalc]
  -- 分母下界：D ≥ (y+ε)² > 0
  have hD : (x + y + ε) * (x' + y + ε) ≥ (y + ε) * (y + ε) := by
    have h₁ : x + y + ε ≥ y + ε := by nlinarith
    have h₂ : x' + y + ε ≥ y + ε := by nlinarith
    have h₃ : 0 ≤ y + ε := by nlinarith
    have h₄ : 0 ≤ x + y + ε := by nlinarith
    exact mul_le_mul h₁ h₂ h₃ h₄
  have hpos : 0 < (x + y + ε) * (x' + y + ε) := mul_pos hden1 hden2
  have hyepos : 0 < y + ε := by nlinarith
  have hdenpos : 0 < (y + ε) * (y + ε) := mul_pos hyepos hyepos
  calc
    |(x - x') * (y + ε) / ((x + y + ε) * (x' + y + ε))|
        = |x - x'| * (y + ε) / ((x + y + ε) * (x' + y + ε)) := by
          rw [abs_div, abs_mul]
          rw [abs_of_nonneg (by nlinarith : 0 ≤ y + ε)]
          rw [abs_of_pos hpos]
    _ ≤ |x - x'| * (y + ε) / ((y + ε) * (y + ε)) := by
          -- D ≥ (y+ε)² 且分子非负：除以更大分母更小
          exact div_le_div_of_nonneg_left
            (mul_nonneg (abs_nonneg _) (by nlinarith : 0 ≤ y + ε)) hdenpos hD
    _ = |x - x'| * ((y + ε) / ((y + ε) * (y + ε))) := by ring
    _ = |x - x'| * (1 / (y + ε)) := by
          have hye : y + ε ≠ 0 := by nlinarith
          congr 1
          field_simp [hye]
    _ ≤ |x - x'| * (1 / ε) := by
          -- 1/(y+ε) ≤ 1/ε（y+ε ≥ ε > 0）
          have h1 : 1 / (y + ε) ≤ 1 / ε := by
            exact one_div_le_one_div_of_le hε (by linarith : ε ≤ y + ε)
          exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (1 / ε) * |x - x'| := by ring

/-! ## N 算子对 y 的分量 Lipschitz
|N(x,y)−N(x,y')| ≤ |y−y'|/(4ε)。-/

theorem ratio_norm_contracts_y {ε : ℝ} (hε : 0 < ε) (x y y' : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hy' : 0 ≤ y') :
    |x / (x + y + ε) - x / (x + y' + ε)| ≤ (1 / (4 * ε)) * |y - y'| := by
  have hden1 : 0 < x + y + ε := by nlinarith
  have hden2 : 0 < x + y' + ε := by nlinarith
  -- 代数：差 = x(y'−y)/[(x+y+ε)(x+y'+ε)]
  have hcalc : x / (x + y + ε) - x / (x + y' + ε)
      = x * (y' - y) / ((x + y + ε) * (x + y' + ε)) := by
    field_simp [ne_of_gt hden1, ne_of_gt hden2]
    ring
  rw [hcalc]
  -- 分母下界：D ≥ (x+ε)² > 0
  have hD : (x + y + ε) * (x + y' + ε) ≥ (x + ε) * (x + ε) := by
    have h₁ : x + y + ε ≥ x + ε := by nlinarith
    have h₂ : x + y' + ε ≥ x + ε := by nlinarith
    have h₃ : 0 ≤ x + ε := by nlinarith
    have h₄ : 0 ≤ x + y + ε := by nlinarith
    exact mul_le_mul h₁ h₂ h₃ h₄
  have hpos : 0 < (x + y + ε) * (x + y' + ε) := mul_pos hden1 hden2
  have hxepos : 0 < x + ε := by nlinarith
  have hdenpos : 0 < (x + ε) * (x + ε) := mul_pos hxepos hxepos
  -- x/(x+ε)² ≤ 1/(4ε)：4εx ≤ (x+ε)² ⟺ (x−ε)² ≥ 0
  have hquartic : x / (x + ε) ^ 2 ≤ 1 / (4 * ε) := by
    have hxle : 4 * ε * x ≤ (x + ε) ^ 2 := by
      nlinarith [sq_nonneg (x - ε)]
    have hden4 : 0 < 4 * ε := by nlinarith
    have hdenx : 0 < (x + ε) ^ 2 := by nlinarith
    rw [div_le_div_iff₀ hdenx hden4]
    nlinarith [hxle]
  calc
    |x * (y' - y) / ((x + y + ε) * (x + y' + ε))|
        = |x| * |y' - y| / ((x + y + ε) * (x + y' + ε)) := by
          rw [abs_div, abs_mul]
          rw [abs_of_pos hpos]
    _ = x * |y' - y| / ((x + y + ε) * (x + y' + ε)) := by
          rw [abs_of_nonneg hx]
    _ ≤ x * |y' - y| / ((x + ε) * (x + ε)) := by
          -- D ≥ (x+ε)² 且分子非负：除以更大分母更小
          exact div_le_div_of_nonneg_left (mul_nonneg hx (abs_nonneg _)) hdenpos hD
    _ = |y' - y| * (x / ((x + ε) * (x + ε))) := by ring
    _ = |y' - y| * (x / (x + ε) ^ 2) := by ring
    _ ≤ |y' - y| * (1 / (4 * ε)) := by
          exact mul_le_mul_of_nonneg_left hquartic (abs_nonneg _)
    _ = (1 / (4 * ε)) * |y' - y| := by ring
    _ = (1 / (4 * ε)) * |y - y'| := by
          rw [abs_sub_comm]

/-! ## N 算子组合 Lipschitz（双变量）
|N(x,y) − N(x',y')| ≤ (1/ε)·(|x−x'| + |y−y'|)。-/

theorem ratio_norm_lipschitz {ε : ℝ} (hε : 0 < ε) (x x' y y' : ℝ)
    (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) (hy' : 0 ≤ y') :
    |x / (x + y + ε) - x' / (x' + y' + ε)| ≤ (1 / ε) * (|x - x'| + |y - y'|) := by
  -- 三角：中项 x'/(x'+y+ε)
  calc
    |x / (x + y + ε) - x' / (x' + y' + ε)|
        = |(x / (x + y + ε) - x' / (x' + y + ε))
            + (x' / (x' + y + ε) - x' / (x' + y' + ε))| := by
          congr 1
          abel
    _ ≤ |x / (x + y + ε) - x' / (x' + y + ε)|
        + |x' / (x' + y + ε) - x' / (x' + y' + ε)| :=
          abs_add _ _
    _ ≤ (1 / ε) * |x - x'| + (1 / (4 * ε)) * |y - y'| := by
          exact add_le_add (ratio_norm_contracts_x hε x x' y hx hx' hy)
            (ratio_norm_contracts_y hε x' y y' hx' hy hy')
    _ ≤ (1 / ε) * |x - x'| + (1 / ε) * |y - y'| := by
          -- 1/(4ε) ≤ 1/ε
          have hle : 1 / (4 * ε) ≤ 1 / ε := by
            exact one_div_le_one_div_of_le hε (by nlinarith : ε ≤ 4 * ε)
          exact add_le_add_left (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) _
    _ = (1 / ε) * (|x - x'| + |y - y'|) := by ring

/-! ## 注：pan-meme 移植闭环
  ↑↓ 循环收敛（定理一，干净核心）+ 完全闭包（定理二）：
  有限论域上任何单调非减结构演化必稳定——验证/提取循环的
  有限收敛骨架；往返双射（定理三/四）：编译-提取往返恒等
  ⟹ 提取可逆（连接 roundtrip_extract）；N 算子收缩（定理
  五-七）：归一化比例 A/(A+B+ε) 的 Lipschitz——收缩映射
  的收敛（RealConvergence）实例。价值筛选：跳过五维 ODE/
  谱聚类/信息作用量（与转换层无关）。-/

end Lattice
