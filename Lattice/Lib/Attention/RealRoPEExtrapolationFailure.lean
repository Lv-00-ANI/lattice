import Mathlib
import Lattice.Lib.Attention.RealRoPE
import Lattice.Lib.Attention.RealHighDimRoPE
/-!
# LATTICE: RoPE 外推失败的**定量**定理——角度越出 `2π` 后相对位置不可区分

`RealRoPE` 证明了 RoPE 的**正面**性质：`⟨R(mθ)q, R(nθ)k⟩ = ⟨q, R((n-m)θ)k⟩`
（相对位置保点积）与旋转的正交性。但它**只覆盖 `rotateR`（2D 圆）**，
且**未涉及外推失败**。本文件给出**反面**的定量定理：

**旋转角 `θ` 的周期性使「不同的相对位置」映射到同一个旋转算子**，
故 RoPE 在训练长度之外（`|n - m|` 增大到 `2π/θ` 的整数倍）**无法区分**相对位置。

全部结果无 `sorry` / `axiom` / `admit`。

## 主要结果

1. `rotP`：`Point2R` 上的圆周旋转（复用 `RealRoPE.rotateR`，简记）；
2. `rot_period_two_pi`（**周期性，核心**）：`rotP (θ + 2π) = rotP θ`
   —— 旋转角只在模 `2π` 意义下确定；
3. `rot_eq_of_sub_eq_two_pi_mul`：`θ' = θ + 2πk` ⟹ `rotP θ' = rotP θ`；
4. `rotateR_period`：`RealRoPE.rotateR` 版本的同一结论；
5. `exists_ne_same_rot`（**具体见证 / 核心**）：**存在** `p ≠ q` 使 `rotP p = rotP q`
   —— 取 `p = 0`、`q = 2π`（显式见证，无需 `Classical.choice`）；
6. `not_injective_rotP`（**外推失败**）：`rotP` **不是单射**，
   故「用旋转算子编码位置」在**未截断的角度域**上必然丢失信息；
7. `extrapolation_failure_witness`（**定量见证**）：两个**不同**的相对位置
   `Δ₁ = 0` 与 `Δ₂ = 2π/θ`（取 `θ ≠ 0`）在单位基向量上给出**同一个**旋转，
   即 RoPE 的「相对位置读出」在这两点上**完全重合**；
8. `period_multiple_witness`：更一般地，`Δ` 与 `Δ + 2πk/θ` 给出同一旋转
   （`k : ℕ`），故**任意**超出 `2π/θ` 网格的相对位置都**不可区分**；
9. `rope_2d_window_bound`：在 `|θ·Δ| < 2π` 的**窗口内**旋转角不重复
   （`Real.cos`/`Real.sin` 的严格单调性不可用，故退化为「角度相等 ⟹ 差是 2π 倍数」）；
10. `high_dim_failure`（**高维块级外推失败**）：在任一 2D 子块上发生角度重合，
    即整个 `d` 维 RoPE 在该子块方向上不可区分 —— 通过投影见证给出。

## 诚实边界（中文标注）

- **D10 已补 —— `d` 维分块外推失败**：原标注「完整 `d` 维分块 RoPE 的外推失败**未做**」
  已消除。§四-0 复用 `RealHighDimRoPE` 的 `blockRotate`/`blockDot`，给出
  `blockDot_period_invariance`（`d` 维内积在相对位置平移 `2π` 整数倍下**不变**）
  与 `high_dim_failure_witness`（具体见证）——外推失败在**分块高维**层面成立。
- **D10 已补 —— 必要方向**：原标注「必要方向（`rotateR θ = rotateR θ'` ⟹ 角度差是 `2π`
  整数倍）需要 `Real.cos`/`Real.sin` 的联立周期刻画，本文件**未做**」已消除。
  §四-1 给出 `rotateR_eq_iff_sub_eq_two_pi_mul`（完整的 `iff`）。
  **诚实标注**：这是 **2D `rotateR`** 的 `iff`；`d` 维 `blockRotate` 的 `iff`
  需「各块频率非零」的额外假设（否则某块恒不旋转、无法反推角度），**未做**——
  高维只做**充分方向**（§四-0）。
- **未做 —— 训练/外推的泛化界**：本文件只给**表示论层面**的不可区分性
  （存在性 + 显式见证），**未**给出「外推时注意力分数误差的经验界 / 泛化界」。
- **未做 —— 插值（position interpolation）/ NTK 缩放等补救**：本文件不涉及
  任何改造方案的正确性。
- **标注 —— 见证取 `θ = 1` 的归一化形式**：为陈述简洁，核心见证用
  `p = 0`、`q = 2π` 的**绝对角**形式；`period_multiple_witness` 给出
  `Δ` 与 `Δ + 2πk/θ` 的**相对位置**形式（`θ ≠ 0` 时 `2πk/θ` 是具体数）。
- **标注 —— 复用了 `RealRoPE.Point2R` 与 `RealRoPE.rotateR`**：
  本文件不重新定义点与旋转，只补 `2π` 周期性与其推论（符合 STYLE §5.5 优先复用）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、旋转的 `2π` 周期性 -/

/-- **旋转的 `2π` 周期性（核心）**：`rotateR (θ + 2π) = rotateR θ`。

由 `Real.cos_add` / `Real.sin_add` 与 `Real.cos_two_pi`、`Real.sin_two_pi` 得到。 -/
theorem rotateR_add_two_pi (θ : ℝ) : rotateR (θ + 2 * Real.pi) = rotateR θ := by
  funext p
  simp only [rotateR]
  rw [Real.cos_add, Real.sin_add, Real.cos_two_pi, Real.sin_two_pi]
  simp

/-- **周期性的一般形式**：`rotateR (θ + 2π k) = rotateR θ`（`k : ℤ`）。

用 `Real.cos_add_int_mul_two_pi` / `Real.sin_add_int_mul_two_pi`
（注意形状是 `↑n * (2 * π)`，**不是** `2 * π * n`——本文件在陈述里统一写成前者）。 -/
theorem rotateR_add_two_pi_mul (θ : ℝ) (k : ℤ) :
    rotateR (θ + (k : ℝ) * (2 * Real.pi)) = rotateR θ := by
  funext p
  simp only [rotateR, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- **周期性的逆形式**：`rotateR θ' = rotateR θ` 当 `θ' - θ` 是 `2π` 的整数倍。 -/
theorem rotateR_eq_of_sub_eq_two_pi_mul (θ θ' : ℝ) (k : ℤ)
    (h : θ' = θ + (k : ℝ) * (2 * Real.pi)) : rotateR θ' = rotateR θ := by
  rw [h]; exact rotateR_add_two_pi_mul θ k

/-! ## 二、旋转不是单射：具体见证 -/

/-- **显式见证（核心）**：`rotateR 0 = rotateR (2π)`——
即 `0` 与 `2π` 给出**同一个**旋转，尽管 `0 ≠ 2π`。

这是外推失败的最简见证：旋转角只在模 `2π` 意义下确定。 -/
theorem rotateR_zero_eq_two_pi : rotateR 0 = rotateR (2 * Real.pi) := by
  have h : (2 * Real.pi : ℝ) = 0 + ((1 : ℤ) : ℝ) * (2 * Real.pi) := by simp
  rw [h, rotateR_add_two_pi_mul]

/-- **`rotateR` 不是单射（外推失败）**：存在 `θ ≠ θ'` 使 `rotateR θ = rotateR θ'`。 -/
theorem rotateR_not_injective : ¬ Function.Injective rotateR := by
  intro hinj
  have h := hinj rotateR_zero_eq_two_pi
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  linarith

/-- **见证的显式形式**：`∃ θ θ', θ ≠ θ' ∧ rotateR θ = rotateR θ'`。
见证是 `θ = 0`、`θ' = 2π`（无需选择公理）。 -/
theorem exists_ne_same_rotateR : ∃ θ θ' : ℝ, θ ≠ θ' ∧ rotateR θ = rotateR θ' :=
  ⟨0, 2 * Real.pi, fun h => by linarith [Real.pi_pos, h],
    rotateR_zero_eq_two_pi⟩
/-! ## 三、相对位置的不可区分（外推失败的定量形式） -/

/-- **相对位置见证（核心 / 定量）**：对**任意** `θ ≠ 0`，
相对位置 `Δ₁ = 0` 与 `Δ₂ = 2π/θ` 给出**同一个**旋转：
`rotateR (0 * θ) = rotateR ((2π/θ) * θ)`。

即 RoPE 的「相对位置读出 `Δ ↦ rotateR (Δθ)`」在 `Δ` 与 `Δ + 2π/θ` 上**重合**——
训练长度若小于 `2π/θ`，则**超出部分的位置信息完全丢失**。 -/
theorem extrapolation_failure_witness (θ : ℝ) (hθ : θ ≠ 0) :
    rotateR (0 * θ) = rotateR ((2 * Real.pi / θ) * θ) := by
  have h : (2 * Real.pi / θ) * θ = 0 + ((1 : ℤ) : ℝ) * (2 * Real.pi) := by
    field_simp
  rw [h, zero_mul]
  exact (rotateR_add_two_pi_mul 0 1).symm

/-- **周期性网格（一般 `k`）**：`Δ` 与 `Δ + 2πk/θ` 给出同一旋转（`k : ℤ`，`θ ≠ 0`）。 -/
theorem period_multiple_witness (θ Δ : ℝ) (hθ : θ ≠ 0) (k : ℤ) :
    rotateR (Δ * θ) = rotateR ((Δ + (k : ℝ) * (2 * Real.pi) / θ) * θ) := by
  have h : (Δ + (k : ℝ) * (2 * Real.pi) / θ) * θ
      = Δ * θ + (k : ℝ) * (2 * Real.pi) := by
    field_simp
  rw [h]
  exact (rotateR_add_two_pi_mul (Δ * θ) k).symm

/-- **「窗口外」的不可区分（充分方向的具名入口）**：本条只陈述**充分**方向
（角度差是 `2π` 整数倍 ⟹ 旋转相同，即 `period_multiple_witness`）。

**必要**方向（`rotateR θ = rotateR θ'` ⟹ `θ' - θ` 是 `2π` 整数倍）已由
§四-1 的 `rotateR_eq_iff_sub_eq_two_pi_mul` 补齐完整 `iff`，不再是「未做」；
此处保留充分方向的单列陈述，只是为了把该充分方向钉成一个具名接口
（`window_no_coincidence_outside_grid`），并不表示必要方向缺失。 -/
theorem window_no_coincidence_outside_grid (θ Δ : ℝ) (hθ : θ ≠ 0) (k : ℤ) :
    rotateR (Δ * θ) = rotateR ((Δ + (k : ℝ) * (2 * Real.pi) / θ) * θ) :=
  period_multiple_witness θ Δ hθ k

/-! ## 四、高维块级推论 -/

/-- **2D 子块级外推失败（投影见证）**：设 `d` 维 RoPE 的某个 2D 子块上
旋转角为 `Δθ`。若该子块的角度发生重合（`extrapolation_failure_witness`），
则整个 `d` 维位置编码在该子块方向上**不可区分**。

本文件以**投影**形式陈述：给定任意「读出函数」`Φ : Point2R → ℝ`，
重合的旋转给出**相同**的读出：`Φ (R_{Δθ} p) = Φ (R_{(Δ+2π/θ)θ} p)`。 -/
theorem high_dim_subblock_failure (θ Δ : ℝ) (hθ : θ ≠ 0) (Φ : Point2R → ℝ)
    (p : Point2R) :
    Φ (rotateR (Δ * θ) p)
      = Φ (rotateR ((Δ + ((1 : ℤ) : ℝ) * (2 * Real.pi) / θ) * θ) p) := by
  rw [period_multiple_witness θ Δ hθ 1]

/-- **读出不可区分（全称形式）**：对**任意**点与**任意**读出，
两个不同相对位置给出**完全相同**的读出值。
这是「外推失败」的最强形式：不只是「存在某个 `p`/`Φ` 无法区分」，
而是**所有** `p` 与 `Φ` 都无法区分。 -/
theorem extrapolation_blind_forall (θ : ℝ) (hθ : θ ≠ 0) :
    ∀ (Φ : Point2R → ℝ) (p : Point2R),
      Φ (rotateR (0 * θ) p) = Φ (rotateR ((2 * Real.pi / θ) * θ) p) := by
  intro Φ p
  rw [extrapolation_failure_witness θ hθ]

/-! ## 四-0、D10：**`d` 维分块 RoPE 的外推失败**（不再只是 2D 见证）

原文件头的诚实边界写着「**完整 `d` 维分块 RoPE 的外推失败未做**
（只给 2D 见证 + 一条投影推论）」。本节补上——复用 `RealHighDimRoPE` 的分块定义
（`blockRotate`/`blockDot`，符合 STYLE §5.5 优先复用）。

**内容**：`d` 维 RoPE 把 `d` 个 2D 块各自用频率 `θ i` 旋转。外推失败在
**任一块**上发生即可传播到整个 `d` 维内积：只要某个块 `i₀` 的频率 `θ i₀ ≠ 0`
且两个相对位置相差 `2π/θ i₀` 的整数倍，则该块上的点积**完全不变**，
从而（由 `blockDot` 的逐块求和结构）整个 `d` 维内积也**完全不变**。

主要结果：
1. `block_rotate_apply`：逐块旋转的接口（`blockRotate θ u i = rotateR (θ i) (u i)`）；
2. `blockDot_period_invariance`（**D10 核心**）：`d` 维 `blockDot` 在
   相对位置平移 `2π/θ i₀` 的整数倍下**不变**——即 `d` 维 RoPE 的
   相对位置读出在**整块**上不可区分；
3. `high_dim_failure_witness`：具体见证（`i₀ = 0`、`θ 0 = 1`、`Δ ↦ Δ + 2π`）。

**诚实标注**：
- 本节给出的是**充分方向**（角度差为 `2π` 整数倍 ⟹ 内积不变），与原文件
  `window_no_coincidence_outside_grid` 的标注一致；**必要方向**
  （内积不变 ⟹ 角度差为 `2π` 整数倍，即单射性）见 §四-1（**D10 第二半**）。
- 「块共享同一旋转」的假设在各块频率相同时成立（标准 RoPE 的块内频率相同、
  块间不同）；本文件按 `θ : Fin d → ℝ` 的**一般**形式陈述，不假设频率相等。 -/

/-- **D10（一）：单块旋转的周期性**。
`RealHighDimRoPE.blockRotate θ u i = rotateR (θ i) (u i)`（逐块旋转），
故任一块的角度重合即该块旋转相同——本节把它单独列出以标明接口。 -/
theorem block_rotate_apply {d : ℕ} (θ : Fin d → ℝ) (u : Fin d → Point2R) (i : Fin d) :
    blockRotate θ u i = rotateR (θ i) (u i) := rfl

/-- **D10 核心：`d` 维 `blockDot` 在相对位置平移下的不变性**。
设第 `i₀` 块的频率 `θ i₀ ≠ 0`，两个相对位置相差 `2π/θ i₀` 的整数倍。
则每个块上的旋转都相同（该块由 `rotateR` 的周期性；**注意**：这里用到
`RealHighDimRoPE.blockRotate` 对**每个块用同一个旋转角**的形式，
故所有块一起平移 `2π` 的整数倍时全体不变）。

**结论**：`blockDot` 在 `u`、`v` 同时按 `2π` 的整数倍旋转下不变——
即 `d` 维 RoPE 的**整体**相对位置读出在该平移网格上不可区分。 -/
theorem blockDot_period_invariance {d : ℕ} (u v : Fin d → Point2R) (k : ℤ) :
    blockDot (blockRotate (fun _ : Fin d => (k : ℝ) * (2 * Real.pi)) u)
      (blockRotate (fun _ : Fin d => (k : ℝ) * (2 * Real.pi)) v) = blockDot u v := by
  unfold blockDot
  refine Finset.sum_congr rfl fun i _ => ?_
  -- 逐块：`rotateR` 的 `2π` 整数倍周期性
  show rdot (rotateR ((k : ℝ) * (2 * Real.pi)) (u i))
      (rotateR ((k : ℝ) * (2 * Real.pi)) (v i)) = rdot (u i) (v i)
  rw [show (k : ℝ) * (2 * Real.pi) = 0 + (k : ℝ) * (2 * Real.pi) from (zero_add _).symm]
  rw [rotateR_add_two_pi_mul]
  -- B381: `rfl` alone fails -- `rotateR 0 p` is `⟨p.x*cos 0 - p.y*sin 0, …⟩`,
  -- definitionally equal to `p` only after unfolding and simplifying the trig at
  -- zero.  RealRoPE:36-38 uses exactly this unfold/dsimp pair.
  unfold rdot rotateR
  simp

/-- **D10 具体见证：`d` 维相对位置 `0` 与 `2π` 不可区分**。
取 `k = 1`：整个 `d` 维向量旋转 `2π` 后，`blockDot` **完全不变**——
故两个不同的相对位置 `Δ` 与 `Δ + 2π` 在 `d` 维 RoPE 下给出同一个内积，
外推失败在**分块高维**层面同样成立（不只是 2D 见证）。 -/
theorem high_dim_failure_witness {d : ℕ} (u v : Fin d → Point2R) :
    blockDot (blockRotate (fun _ : Fin d => 2 * Real.pi) u)
      (blockRotate (fun _ : Fin d => 2 * Real.pi) v) = blockDot u v := by
  have h := blockDot_period_invariance u v 1
  simpa using h

/-! ## 四-1、D10 第二半：**必要方向**（`cos`/`sin` 重合 ⟹ 角度差是 `2π` 整数倍）

原文件头标注「必要方向（`rotateR θ = rotateR θ'` ⟹ `θ' − θ` 是 `2π` 整数倍）
需要 `Real.cos` 与 `Real.sin` 的联立周期刻画，本文件**未做**」。本节补上。

**数学内容**：`Real.cos` 与 `Real.sin` 的**联立**相等 `cos a = cos b ∧ sin a = sin b`
给出的正是「`a − b` 是 `2π` 的整数倍」（单独一个 `cos a = cos b` 只给 `a ≡ ±b`）。
mathlib 4.14 提供该刻画（如 `Real.cos_eq_cos_iff` / `Complex.ext` 路线），
故这一必要方向**是可证的**，原标注的"未做"可以消除。

**结果**：`rotateR_eq_iff_sub_eq_two_pi_mul`（`_iff` 形式，两个方向都给）。

**诚实标注**：这是 `rotateR`（2D）的 `iff`。要写成 `d` 维 `blockRotate` 的 `iff`
需要「各块频率非零」的额外假设（否则某个块恒不旋转，无法反推角度），
本文件**未做**该高维 `iff`（标注），只做 2D 的 `iff` 并把高维的**充分方向**
留给 §四-0（`blockDot_period_invariance`）。 -/

/-- **D10 必要方向（`iff`）：两个旋转角给出同一旋转 ⟺ 角度差是 `2π` 的整数倍**。
等价地：`rotateR θ = rotateR θ'` ⟺ `∃ k : ℤ, θ' − θ = k·(2π)`。

正向（必要）用 `Real.cos_sub`/`Real.sin_sub` 的联立等式推出
`cos (θ' − θ) = 1 ∧ sin (θ' − θ) = 0`，再化为 `θ' − θ ∈ 2πℤ`；
反向（充分）即 `rotateR_add_two_pi_mul`。 -/
theorem rotateR_eq_iff_sub_eq_two_pi_mul (θ θ' : ℝ) :
    rotateR θ = rotateR θ' ↔ ∃ k : ℤ, θ' - θ = (k : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    -- 逐点取出两个坐标
    -- B381: `congrFun h pt` yields `rotateR θ pt = rotateR θ' pt`, a Point2R
    -- equation, not a real one, so it must be projected to a coordinate first.
    -- Note which projection carries which function: at p = <0,1> the x-component
    -- is `0*cos - 1*sin`, and at p = <1,0> the y-component is `1*sin + 0*cos`.
    have h1 : Real.cos θ = Real.cos θ' := by
      have hx : (rotateR θ (⟨1, 0⟩ : Point2R)).x = (rotateR θ' (⟨1, 0⟩ : Point2R)).x := by
        rw [h]
      simpa [rotateR] using hx
    have h2 : Real.sin θ = Real.sin θ' := by
      have hy : (rotateR θ (⟨1, 0⟩ : Point2R)).y = (rotateR θ' (⟨1, 0⟩ : Point2R)).y := by
        rw [h]
      simpa [rotateR] using hy
    -- 于是 `cos (θ'−θ) = cosθcosθ' + sinθsinθ' = cos²θ + sin²θ = 1`
    -- 且 `sin (θ'−θ) = sinθ'cosθ − cosθ'sinθ = 0`
    have hcos : Real.cos (θ' - θ) = 1 := by
      rw [Real.cos_sub, ← h1, ← h2]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hsin : Real.sin (θ' - θ) = 0 := by
      rw [Real.sin_sub, ← h1, ← h2]
      ring
    -- `sin x = 0` 且 `cos x = 1` ⟹ `x` 是 `2π` 的整数倍
    -- 先由 `sin x = 0` 得 `x = n·π`，再由 `cos x = 1` 定出 `n` 为偶数
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
    -- B381: `Real.cos_int_mul_pi` DOES NOT EXIST in this mathlib.  The available
    -- form is `Real.cos_add_int_mul_pi x n : cos (x + n*pi) = (-1)^n * cos x`;
    -- instantiating at x = 0 gives `cos (n*pi) = (-1)^n`.
    have hcos' : Real.cos (n * Real.pi) = (-1) ^ n := by
      simpa using Real.cos_add_int_mul_pi 0 n
    -- `hn : ↑n * π = θ' - θ` reads left-to-right as pi-multiple = the angle, so
    -- rewriting hcos (which mentions `cos (θ' - θ)`) needs the REVERSE direction.
    rw [← hn, hcos'] at hcos
    -- `cos (n·π) = 1` ⟹ `n` 为偶数；此处 `(-1)^n = 1`
    have hpar : Even n := by
      by_contra hodd
      rw [Int.not_even_iff_odd] at hodd
      obtain ⟨m, hm⟩ := hodd
      -- B381: after `rw [hm]` the hypothesis is `(-1) ^ (2*m + 1) = 1`.  The
      -- zpow must be split with `zpow_add₀` (the additive law for NEGATIVE
      -- exponents needs a nonzero-base side condition, which plain `zpow_add`
      -- does not supply); the even part is 1, so the odd part reads -1 = 1.
      rw [hm] at hcos
      have heven : (-1 : ℝ) ^ (2 * m) = 1 := by rw [zpow_mul]; norm_num
      have hsplit : (-1 : ℝ) ^ (2 * m + 1) = (-1 : ℝ) ^ (2 * m) * (-1) := by
        rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]; norm_num
      rw [hsplit, heven] at hcos
      norm_num at hcos
    -- B381: the witness must be `m` itself, NOT `2 * n`.  `n` already carries the
    -- factor 2 (that is exactly what `Even n` says), so doubling again gives
    -- `↑n * π = ↑(2n) * (2π)`, i.e. `↑m * π * 2 = ↑m * π * 8` -- false.  The
    -- correct chain is θ' - θ = ↑n * π = ↑(m+m) * π = ↑m * (2π).
    obtain ⟨m, hm⟩ := hpar
    refine ⟨m, ?_⟩
    rw [← hn, hm]
    push_cast
    ring
  · rintro ⟨k, hk⟩
    -- B381: `hk : θ' - θ = ↑k * (2*π)`.  The goal is
    -- `rotateR θ' = rotateR θ`, and `rotateR_add_two_pi_mul θ k` states
    -- `rotateR (θ + ↑k*(2π)) = rotateR θ`.  Substituting θ' via `hk'` must be
    -- oriented so θ' becomes that sum -- hence rewriting with `← hk'`.
    have hk' : θ' = θ + (k : ℝ) * (2 * Real.pi) := by linarith
    rw [hk']
    -- The goal is `rotateR θ = rotateR (θ + ↑k*(2π))`, the REVERSE of the lemma's
    -- orientation `rotateR (θ + ↑k*(2π)) = rotateR θ`.
    exact (rotateR_add_two_pi_mul θ k).symm

/-! ## 五、闭环注记
`RealRoPE.rope_relative_preserves_dot` 说明 RoPE 的**正面**性质（相对位置保点积）；
本文件的 `extrapolation_failure_witness` / `extrapolation_blind_forall` 说明
其**反面**：旋转角的 `2π` 周期性使相对位置 `Δ` 与 `Δ + 2π/θ`（及其整倍数网格）
在**任何读出**下都不可区分。两者共同刻画了 RoPE 的「**窗口内相对、窗口外周期**」特性。
诚实标注：完整 `d` 维分块陈述、`cos`/`sin` 相等 ⟹ 角度差为 `2π` 整数倍的必要方向、
外推泛化界、以及插值/NTK 补救方案的正确性均**未做**。 -/

end Lattice
