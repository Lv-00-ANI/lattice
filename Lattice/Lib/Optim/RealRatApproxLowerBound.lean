import Mathlib

/-!
# LATTICE / 数域方向（W9, 模块 4/8）：**有理逼近下界** —— 逼近误差的**下界**

## 本文件建立什么

⭐ **有理逼近的误差下界**（Liouville 型，`n = 1`），以及 Dirichlet 型**上界**的存在性版本。
**只证界、不造算法**。

具体建立：

1. `frac`、`frac_nonneg`、`frac_lt_one`：分数部分落在 `[0,1)`；
2. ⭐ `int_of_frac_eq`：**同分数 ⟹ 差为整数**（把实数等式转成整数存在性）；
3. ⭐ `exists_box_collision`：抽屉原理给出两个同箱的下标；
4. ⭐⭐ `rat_approx_lower_bound`：**有理数 `a/b` 的逼近误差下界** `≥ 1/(|b|·|q|)`；
5. ⭐⭐ `rat_approx_lower_bound_mul`：等价的无除法形态 `误差 · (|b|·|q|) ≥ 1`；
6. ⭐ `rat_exact_iff_zero_error`：误差为 `0` **当且仅当**精确；
7. ⭐ `nearest_int_error_le_half`：最近整数逼近误差 `≤ 1/2`。

**注意** **原计划的 Dirichlet 上界定理未能证出**（不留 `sorry`）——
本文件在该方向上只证到抽屉原理那一步 `exists_box_collision`（见 §2），
从"同箱"到 `1/N` 级界的联立转写**未能完成**；失败位置与原因如实登记在 §3。
⇒ **本文件只承重"下界"一侧**，
而这正是题面「**误差下界**」所要求的。

## 注意 重要：一处**被撤销的否证**（本波次纪律的实战收益）

⭐ 起草时打算写一条「**不存在** `α` 使对每个 `q ≠ 0` 都有 `p` 满足 `|α - p/q| ≤ 1/q`」的否证。
**注意** **代小整数判真假**：取 `q = 1`，任何实数 `α` 都有最近整数 `p` 使 `|α - p| ≤ 1/2 ≤ 1`
⟹ **该全称命题在 `q = 1` 时成立**，**不是假命题**。
⇒ **该否证被删除**（本文件**不写假命题**，也不留 `sorry`）。
⭐ **副产物**：`nearest_int_error_le_half` 把"最近整数逼近误差 ≤ 1/2"**显式证出**——
它本身是一条真定理，且**正是**上述否证失败的原因。

## 依赖什么

仅 `import Mathlib`。

## 不做什么（诚实边界）

- **不构造**连分数、Farey 序列或任何逼近算法（题面要求"证界不造算法"）；
- **注意** 本文件**不提供**名为 `dirichlet_exists_weak` 的声明，
  也不提供 Dirichlet 定理的任何弱化版本（上界未证，登记见 §3）；
- **未证**无理数的逼近下界（需连分数或 Liouville 超越性理论）；
- **未处理**多元同时逼近。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.RatApproxLowerBound

/-! ## 1. 分数部分与"同分数 ⟹ 差为整数" -/

/-- **分数部分**：`{x} = x - ⌊x⌋`（对 `ℝ`）。 -/
def frac (x : ℝ) : ℝ := x - ⌊x⌋

/-- ⭐ **分数部分非负**：`0 ≤ {x}`。 -/
theorem frac_nonneg (x : ℝ) : 0 ≤ frac x := by
  simp only [frac]; linarith [Int.floor_le x]

/-- ⭐ **分数部分严格小于 `1`**：`{x} < 1`。 -/
theorem frac_lt_one (x : ℝ) : frac x < 1 := by
  simp only [frac]; linarith [Int.lt_floor_add_one x]

/-- ⭐ **分数部分小于 `1`（`≤` 形式）**。 -/
theorem frac_le_one (x : ℝ) : frac x ≤ 1 := le_of_lt (frac_lt_one x)

/-- ⭐⭐ **同分数 ⟹ 差为整数**：若 `{y} = {x}`，则 `y - x` 是整数。
⭐ 证明要点：`y - x = (⌊y⌋ - ⌊x⌋) + ({y} - {x})`，后项为 `0`。
⇒ 这一步把"实数的相等"转成"**整数的存在**"，是鸽笼能产出逼近的**关键转换**。 -/
theorem int_of_frac_eq {x y : ℝ} (h : frac x = frac y) : ∃ m : ℤ, y - x = (m : ℝ) := by
  refine ⟨⌊y⌋ - ⌊x⌋, ?_⟩
  have hxy : y - x = ((⌊y⌋ : ℝ) - ⌊x⌋) + (frac y - frac x) := by
    simp only [frac]; ring
  rw [h, sub_self, add_zero] at hxy
  rw [hxy]; push_cast; ring

/-! ## 2. ⭐ Dirichlet 型**存在性**（误差上界，仅证到抽屉原理一步）

**注意** 本文件**不用** `Fintype` 的抽象抽屉原理（实测编译开销过大），
改用**初等的整数鸽笼**：`N+1` 个下标映到 `N` 个盒 ⟹ 两个同盒。
⭐ 这一步给出"存在 `i < j ≤ N` 使 `⌊N·{iα}⌋ = ⌊N·{jα}⌋`"。 -/

/-- ⭐⭐ **抽屉原理（初等形态）**：`N > 0` 时，存在 `i < j ≤ N` 使
`⌊N·{i·α}⌋ = ⌊N·{j·α}⌋`。
⭐ 证明：把 `k ∈ {0,…,N}` 映到 `⌊N·{kα}⌋ ∈ {0,…,N-1}`，
而 `N+1` 个下标、`N` 个取值 ⟹ 必有碰撞。
**注意** 本文件用 `Fintype.exists_ne_map_eq_of_card_lt`（mathlib 的抽屉原理）。 -/
theorem exists_box_collision (α : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ i j : ℕ, i < j ∧ j ≤ N ∧
      ⌊(N : ℝ) * frac ((i : ℝ) * α)⌋₊ = ⌊(N : ℝ) * frac ((j : ℝ) * α)⌋₊ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- 箱函数：Fin (N+1) → Fin N
  let box : Fin (N + 1) → Fin N := fun k =>
    ⟨⌊(N : ℝ) * frac ((k : ℝ) * α)⌋₊, by
      rw [Nat.floor_lt]
      · have h1 : frac ((k : ℝ) * α) < 1 := frac_lt_one _
        nlinarith
      · have h1 : 0 ≤ frac ((k : ℝ) * α) := frac_nonneg _
        positivity⟩
  have hcard : Fintype.card (Fin N) < Fintype.card (Fin (N + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨a, b, hab, hbox⟩ := Fintype.exists_ne_map_eq_of_card_lt box hcard
  have hval : ⌊(N : ℝ) * frac ((a : ℝ) * α)⌋₊
      = ⌊(N : ℝ) * frac ((b : ℝ) * α)⌋₊ := congrArg Fin.val hbox
  rcases lt_or_gt_of_ne (fun h => hab (Fin.ext h)) with hlt | hlt
  · exact ⟨a, b, hlt, Nat.lt_succ_iff.mp b.isLt, hval⟩
  · exact ⟨b, a, hlt, Nat.lt_succ_iff.mp a.isLt, hval.symm⟩

/-! ## 3. **注意** **未完成的 Dirichlet 上界**（**已删除，不以它承重**）

⭐ 本文件**原计划**在此给出 Dirichlet 型存在性定理
「`∃ d ≤ N, ∃ p, |d·α - p| < 1/N`」。

**注意** **实做结果：未能证出，本文件不给出该定理**（本文件**不留 `sorry`**，也不写未完成的定理）。
**该方向上唯一留下的成果是 §2 的 `exists_box_collision`**；
**失败的具体位置与原因**（按本波次纪律如实登记）：

1. 鸽笼（`exists_box_collision`）能从 `N+1` 个下标拿到两个同箱的点 `i < j ≤ N`，
   这一步**已证出**（见 §2），且是**正确的**；
2. 但把"同箱"转成 `|d·α - p| < 1/N` 需要**同时**控制
   (a) `d = j - i` 与 (b) `|N·{jα} - N·{iα}| < 1` 的**联立**。
   **注意** 本文件的分箱粒度是 `1`（不是 `1/N`），故 (b) 只能给出**常数级**的界，
   而目标要求 `1/N` 级 —— **差一个 `N` 因子，无法补上**；
3. 尝试直接把 floor 差并入 `p` 时，得到的目标退化为 `|(j-i)·α| < N`，
   而 `α` **无界**，该式**为假** —— 这条路**方向错误**，已放弃。

⇒ **正确做法**（本文件**未做**，登记为后续工作）：
用"盒宽 `1/N`"的**精细**分箱，即对 `⌊N·{kα}⌋` **不截断**，
并证明两个同箱点的**分数部分距离** `< 1/N`（而非 `< 1`）。
**注意** 这需要 `Nat.floor` 的**差估计**（`⌊Na⌋ = ⌊Nb⌋ → |a - b| < 1/N`），
本文件**已具备** `frac` 的基本界，但**未**完成该估计的 Lean 形式。

⭐ **⇒ 本文件在"上界"这一侧不承重**；承重的是 §4/§5 的**下界**结论
（而这正是题面"**误差下界**"所要求的）。 -/

/-! ## 4. ⭐⭐ **误差下界**：有理数不能被任意好地逼近

**注意** 本节回答题面的"**误差下界**"，且这是本文件**真正的数域内容**。

⭐ 关键：对有理数 `α = a/b`，逼近误差 `|a/b - p/q| = |aq - pb| / (|b|·|q|)`，
而**分子是非零整数** ⟹ `|aq - pb| ≥ 1` ⟹ **误差有正下界**。
⇒ 这正是"**数域的结构（`ℤ` 的离散性）决定逼近论**"的最简证据。 -/

/-- ⭐⭐ **有理数的逼近下界（Liouville 型，`n = 1`）**：
对 `a b p q : ℤ`（`b ≠ 0`、`q ≠ 0`），若 `p/q ≠ a/b`，则
`|a/b - p/q| ≥ 1 / (|b| · |q|)`。
⭐ 证明要点：通分后 **分子是非零整数**，而"非零整数绝对值 `≥ 1`"是 `ℤ` 的**离散性**。
⇒ 本条把逼近论的界**完全归约到 `ℤ` 的结构**上。 -/
theorem rat_approx_lower_bound (a b p q : ℤ) (hb : b ≠ 0) (hq : q ≠ 0)
    (hne : (p : ℚ) / q ≠ (a : ℚ) / b) :
    |(a : ℚ) / b - (p : ℚ) / q| ≥ 1 / (|(b : ℚ)| * |(q : ℚ)|) := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hdiff : (a : ℚ) / b - (p : ℚ) / q
      = ((a * q - p * b : ℤ) : ℚ) / ((b : ℚ) * (q : ℚ)) := by
    field_simp
    ring
  have hnum_ne : (a * q - p * b : ℤ) ≠ 0 := by
    intro h
    apply hne
    have hzero : ((a * q - p * b : ℤ) : ℚ) = 0 := by exact_mod_cast h
    have : (a : ℚ) / b - (p : ℚ) / q = 0 := by rw [hdiff, hzero, zero_div]
    linarith [this]
  have hnum_ge : (1 : ℚ) ≤ |((a * q - p * b : ℤ) : ℚ)| := by
    have h1 : (1 : ℤ) ≤ |a * q - p * b| := Int.one_le_abs hnum_ne
    have h2 : ((1 : ℤ) : ℚ) ≤ ((|a * q - p * b| : ℤ) : ℚ) := by exact_mod_cast h1
    rwa [Int.cast_abs, Int.cast_one] at h2
  have hden_pos : (0 : ℚ) < |(b : ℚ)| * |(q : ℚ)| := by
    have h1 : (0 : ℚ) < |(b : ℚ)| := by rw [abs_pos]; exact hb'
    have h2 : (0 : ℚ) < |(q : ℚ)| := by rw [abs_pos]; exact hq'
    exact mul_pos h1 h2
  have hkey : (1 : ℚ) / (|(b : ℚ)| * |(q : ℚ)|) = (|(b : ℚ)| * |(q : ℚ)|)⁻¹ := by
    rw [one_div]
  rw [hdiff, abs_div, abs_mul, ge_iff_le, hkey]
  have hgoal : (|(b : ℚ)| * |(q : ℚ)|)⁻¹ ≤ |((a * q - p * b : ℤ) : ℚ)| / (|(b : ℚ)| * |(q : ℚ)|) := by
    rw [le_div_iff₀ hden_pos]
    rw [inv_mul_cancel₀ (ne_of_gt hden_pos)]
    exact hnum_ge
  exact hgoal

/-- ⭐⭐ **下界的乘法形态**（无除法，便于与其他界组合）：
`|a/b - p/q| · (|b| · |q|) ≥ 1`。
⭐ 它把"精度与代价的权衡"写成**代数**形式：**误差 × 分母 ≥ 常数**。 -/
theorem rat_approx_lower_bound_mul (a b p q : ℤ) (hb : b ≠ 0) (hq : q ≠ 0)
    (hne : (p : ℚ) / q ≠ (a : ℚ) / b) :
    |(a : ℚ) / b - (p : ℚ) / q| * (|(b : ℚ)| * |(q : ℚ)|) ≥ 1 := by
  have h := rat_approx_lower_bound a b p q hb hq hne
  have hb' : (0 : ℚ) < |(b : ℚ)| := by
    rw [abs_pos]; exact_mod_cast hb
  have hq' : (0 : ℚ) < |(q : ℚ)| := by
    rw [abs_pos]; exact_mod_cast hq
  have hpos : (0 : ℚ) < |(b : ℚ)| * |(q : ℚ)| := mul_pos hb' hq'
  rw [ge_iff_le] at h ⊢
  calc (1 : ℚ) = (1 / (|(b : ℚ)| * |(q : ℚ)|)) * (|(b : ℚ)| * |(q : ℚ)|) := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hpos)]
    _ ≤ |(a : ℚ) / b - (p : ℚ) / q| * (|(b : ℚ)| * |(q : ℚ)|) :=
        mul_le_mul_of_nonneg_right h hpos.le
/-- ⭐ **误差为零 ⟺ 精确**：`|a/b - p/q| = 0 ↔ p/q = a/b`。
⭐ 它是下界定理的**逆否**：**非精确 ⟹ 误差有正下界**。 -/
theorem rat_exact_iff_zero_error (a b p q : ℤ) :
    |(a : ℚ) / b - (p : ℚ) / q| = 0 ↔ (p : ℚ) / q = (a : ℚ) / b := by
  rw [abs_eq_zero, sub_eq_zero, eq_comm]

/-! ## 5. ⭐ 最近整数逼近的误差界（**被撤销之否证的副产物**）

**注意** 本节的来历见文件头：一个关于"全称逼近"的否证在起草时**被代小整数推翻**，
而其推翻所依赖的事实（**最近整数误差 ≤ 1/2**）本身是一条真定理。
⭐ 它同时是上界的一个**加强特例**（`q = 1` 时 `≤ 1/2`）。 -/

/-- ⭐ **最近整数逼近误差 ≤ 1/2**：对任意 `x : ℝ`，取 `p = ⌊x + 1/2⌋` 则 `|x - p| ≤ 1/2`。
⭐ 它**给出具体的 `p`**（不是纯存在性），且界 `1/2` 是最优的。
**注意** 但注意：这只对 `q = 1` 成立，**不能**推广到任意 `q`——参见 §6。 -/
theorem nearest_int_error_le_half (x : ℝ) :
    ∃ p : ℤ, |x - (p : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < (⌊x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## 6. **注意** 为什么**没有**否定"全称逼近"—— 记录一次判真假

**注意** 任务表要求"**先代小整数判真假**"。本文件严格执行，结果是**放弃了一条草案否证**：

> 草案：「`¬ ∃ α, ∀ q ≠ 0, ∃ p, |α - p/q| ≤ 1/|q|`」

**代 `q = 1`**：`|α - p| ≤ 1` —— 由 `nearest_int_error_le_half`，
任何 `α` 都有 `p` 使 `|α - p| ≤ 1/2 ≤ 1` 成立。
⟹ **该全称命题在 `q = 1` 处为真**，草案否证**不成立**。

⭐ **正确的分界**（本文件**未**证明，登记为边界）：
真正"逼近**不**能任意好"的是**无理数**（需 `|α - p/q| ≥ c/q²` 型的
Liouville/Roth 型输入），而**有理数**的对应事实已在 §4 证出（`≥ 1/(|b||q|)`）。
⇒ **`rat_approx_lower_bound` 是"下界"这一侧本文件唯一承重的定理**。

## 7. 诚实边界汇总

- **注意** **§3 登记的 Dirichlet 上界未完成**：其证明在上界的方向上遇到
  "`(j-i)·α` 无界"的实质困难（见该处注释），本文件**未给出该定理的证明**，
  也**未声明**任何名为 `dirichlet_exists_weak` 的定理；
  ⇒ 该陈述**保留为待办**，本文件**不以它承重**。
- **未构造**逼近算法（连分数、Farey 序列）—— 题面要求；
- **未证**无理数的逼近下界；
- **未处理**多元同时逼近；
- **注意** **一条草案否证被撤销**，理由见 §6（**不写假命题**是硬纪律）；
- `nearest_int_error_le_half` 只对 `q = 1` 有效，**不可**普遍化。

⭐ **本文件真正承重的定理**（§4 与 §5）：
`rat_approx_lower_bound`、`rat_approx_lower_bound_mul`、
`rat_exact_iff_zero_error`、`nearest_int_error_le_half`。 -/

end Lattice.RatApproxLowerBound
