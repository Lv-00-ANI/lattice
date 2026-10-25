import Mathlib
import Lattice.Lib.LinearAlgebra.RealBanach
import Lattice.Lib.Architectures.RealLoopModel
import Lattice.Lib.LinearAlgebra.RealL2Operator
import Lattice.Lib.LinearAlgebra.RealMatrixStability
/-!
# LATTICE: 循环/收缩映射的不动点**存在性** —— 把三处「存在性未证」闭合

`RealBanach` 已经证明了价值迭代的收缩 ⟹ 不动点存在（`Fin n → ℝ` 上的 Bellman 算子）。
本文件把这个「完备 + 压缩 ⟹ 存在不动点」的骨架**一般化并显式实例化**到三个
此前只标注了「存在性未证」的位置：

  1. `RealLoopModel.loop_fixed_point_unique`：只证了 ρ < 1 ⟹ 不动点**至多一个**，
     未证存在性；本文件给出 `loop_fixed_point_exists` / `loop_fixed_point_existsUnique`
     （在 `{X} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]` 上，
      ρ = Lφ·‖W‖ < 1）；
  2. `RealL2Operator` 的诚实边界「不动点存在性未做（需要完备性 + ‖T‖ < 1）」：
     对**线性**算子 `T` 而言 `0` 永远是不动点（`linearMap_fixed_point_zero`，平凡），
     真正需要完备性的是**仿射**迭代 `x ↦ T x + b`；本文件给出
     `affine_fixed_point_exists` / `affine_fixed_point_unique`；
  3. `RealMatrixStability` 的诚实边界「不动点存在性未做」且
     「`n → ∞` 的收敛和 `‖b‖/(1-‖T‖)` 未证」：本文件给出
     `iterateStep_eq_iterate`（把 `RealMatrixStability.iterateStep` 接到仿射迭代上）、
     `affine_iterate_eq_geometric`（显式几何和 `∑_{k<n} T^k b`）、
     `affine_fixed_point_expansion`（不动点的精确展开）与
     `iterateStep_dist_fixedPoint_le`（到不动点的几何距离界）。

链条（每一步都是机器验证的）：
  `∀a b, ‖f a − f b‖ ≤ L‖a − b‖`（范数 Lipschitz）
    ⟹ `LipschitzWith ⟨L, hL0⟩ f`（`lipschitz_with_of_le`）
    ⟹ `ContractingWith ⟨L, hL0⟩ f`（`L < 1`，`contracting_of_lipschitz`）
    ⟹ `ContractingWith.exists_fixedPoint`（**唯一**用到完备性的一步）
    ⟹ 存在不动点 + 迭代收敛 + 几何误差界。

另外给出**导数形式**的压缩（中值定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`）：
`∀x, ‖f' x‖ ≤ C < 1` ⟹ `f` 是 `C`-压缩 ⟹ 完备空间上存在唯一不动点；
以及**有限维** `EuclideanSpace ℝ (Fin n)` 上的实例化（完备性由 mathlib 现成的
`FiniteDimensional.complete` 提供）。

诚实标注（无 sorry / axiom / admit）：
- **`CompleteSpace` 是本质假设，不可去掉**。整条链条中唯一消费完备性的地方是
  `ContractingWith.exists_fixedPoint`（`Mathlib/Topology/MetricSpace/Contracting.lean`）。
  即：三个文件「缺的一步」正是「为工作空间注册 `CompleteSpace` 实例」。
  **未证/未做**：本文件没有给出「不完备空间上压缩映射可以没有不动点」的
  机器验证反例（mathlib 里缺少一个方便的「只差完备性」的 ℝ-赋范空间）；
  该反例是经典事实（例如 `X = (C[0,1], ‖·‖₁)` 或 `ℓ¹` 的有限支撑子空间），
  这里**诚实标注为未做**，不声称已形式化。
- **`‖T‖ < 1` 的严格性不能放松**：已给机器验证反例
  `translation_no_fixed_point`（`x ↦ x + 1` 在 ℝ 上无不动点，其线性部分是
  `‖id‖ = 1`，不满足严格 `< 1`）。
- 定理 `linearMap_fixed_point_zero`：**线性**算子的不动点存在性是平凡的（`0`），
  真正有价值的是仿射/非线性版本；这是对 `RealL2Operator` 边界说明的一处修正。
- 导数形式需要 `f` **处处** Frechet 可导且导数范数一致界（比局部 Lipschitz 强）；
  只给全局版本，**未做**局部/凸集版本。
无 sorry / axiom / admit。
-/

noncomputable section

open Lattice.Lib.LinearAlgebra.RealMatrixStability

namespace Lattice

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## 一、从范数 Lipschitz 到 `ContractingWith`（显式链条的两步） -/

/-- **第一步：范数形式 ⟹ `LipschitzWith`**。
`0 ≤ L` 且 `∀a b, ‖f a − f b‖ ≤ L‖a − b‖` 时 `f` 是 `L`-Lipschitz（`L : ℝ≥0`）。
用 `LipschitzWith.of_dist_le_mul` 把 `dist` 与范数对齐。 -/
theorem lipschitz_with_of_le {L : ℝ} (hL0 : 0 ≤ L) (f : X → X)
    (hf : ∀ a b, ‖f a - f b‖ ≤ L * ‖a - b‖) :
    LipschitzWith ⟨L, hL0⟩ f := by
  refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
  simpa [dist_eq_norm] using hf a b

/-- **第二步：范数 Lipschitz + `L < 1` ⟹ `ContractingWith`**（`RealBanach` 中
`bellman_contracting` 的抽象形式）。 -/
theorem contracting_of_lipschitz {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1) (f : X → X)
    (hf : ∀ a b, ‖f a - f b‖ ≤ L * ‖a - b‖) :
    ContractingWith ⟨L, hL0⟩ f :=
  ⟨by exact_mod_cast hL1, lipschitz_with_of_le hL0 f hf⟩

/-! ## 二、一般收缩映射：完备 ⟹ 存在唯一不动点 -/

/-- **一般收缩映射的不动点存在性**（Banach 不动点定理在范数空间上的实例）。
这是本文件的核心骨架：三个文件的「存在性未证」都是它的实例化。 -/
theorem contraction_fixed_point_exists [CompleteSpace X] {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : X → X) (hf : ∀ a b, ‖f a - f b‖ ≤ L * ‖a - b‖) :
    ∃ p : X, f p = p := by
  have hc : ContractingWith ⟨L, hL0⟩ f := contracting_of_lipschitz hL0 hL1 f hf
  have hfin : edist (0 : X) (f 0) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨p, hp, _⟩ := hc.exists_fixedPoint (0 : X) hfin
  exact ⟨p, hp.eq⟩

/-- **一般收缩映射：存在唯一不动点**（存在性来自 Banach，唯一性来自压缩的代数论证）。 -/
theorem contraction_fixed_point_existsUnique [CompleteSpace X] {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : X → X) (hf : ∀ a b, ‖f a - f b‖ ≤ L * ‖a - b‖) :
    ∃! p : X, f p = p := by
  have hc : ContractingWith ⟨L, hL0⟩ f := contracting_of_lipschitz hL0 hL1 f hf
  have hfin : edist (0 : X) (f 0) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨p, hp, _⟩ := hc.exists_fixedPoint (0 : X) hfin
  exact ⟨p, hp.eq, fun q hq => hc.fixedPoint_unique' hq hp⟩

/-! ## 三、`RealLoopModel` 的闭环：RNN 隐状态映射的不动点存在性 -/

/-- **`RealLoopModel` 的「存在性未证」闭合（第一步）**：
固定输入下隐状态映射 `h ↦ φ(W h + U x)` 满足 Banach 收缩条件。
直接由 `RealLoopModel.loop_model_contraction`（已证的 `ρ`-Lipschitz）+ 第二步得到。 -/
theorem loopStepMap_contracting (φ : X → X) (W U : X →L[ℝ] X) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ)
    (hρ1 : Lφ * ‖W‖ < 1) (x : X) :
    ContractingWith ⟨Lφ * ‖W‖, mul_nonneg hLφ (norm_nonneg W)⟩ (loopStepMap φ W U x) :=
  contracting_of_lipschitz (mul_nonneg hLφ (norm_nonneg W)) hρ1 _
    (loop_model_contraction φ W U Lφ hφ hLφ x)

/-- **`RealLoopModel` 的「不动点存在性未证」闭合**：
完备范数空间 + ρ = Lφ·‖W‖ < 1 ⟹ 隐状态映射存在不动点。
这是 `RealLoopModel.loop_fixed_point_unique`（只给唯一性）的**存在性补全**。 -/
theorem loop_fixed_point_exists [CompleteSpace X] (φ : X → X) (W U : X →L[ℝ] X) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ)
    (hρ1 : Lφ * ‖W‖ < 1) (x : X) :
    ∃ p : X, loopStepMap φ W U x p = p := by
  have hc := loopStepMap_contracting φ W U Lφ hφ hLφ hρ1 x
  have hfin : edist x (loopStepMap φ W U x x) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨p, hp, _⟩ := hc.exists_fixedPoint x hfin
  exact ⟨p, hp.eq⟩

/-- **存在唯一性（本文件对 `RealLoopModel` 的完整闭合）**：
存在性由 Banach 给出（需要 `CompleteSpace`），唯一性直接复用
`RealLoopModel.loop_fixed_point_unique`（不需要完备性）——两条路线在此交叉验证。 -/
theorem loop_fixed_point_existsUnique [CompleteSpace X] (φ : X → X) (W U : X →L[ℝ] X) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ)
    (hρ1 : Lφ * ‖W‖ < 1) (x : X) :
    ∃! p : X, loopStepMap φ W U x p = p := by
  obtain ⟨p, hp⟩ := loop_fixed_point_exists φ W U Lφ hφ hLφ hρ1 x
  exact ⟨p, hp, fun q hq => loop_fixed_point_unique φ W U Lφ hφ hLφ hρ1 x q p hq hp⟩

/-- 交叉验证：Banach 路线得到的不动点与迭代极限一致——
`ContractingWith.exists_fixedPoint` 的收敛部分给出 `Tⁿ h₀ → p`，
而 `RealLoopModel.loop_converges_to_fixed_point` 给出几何误差界。
此处把两者拼成一条「迭代收敛到该不动点」的陈述（`Tendsto` 形式）。 -/
theorem loop_iterate_tendsto_fixedPoint [CompleteSpace X] (φ : X → X) (W U : X →L[ℝ] X) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ)
    (hρ1 : Lφ * ‖W‖ < 1) (x : X) :
    ∃ p : X, loopStepMap φ W U x p = p ∧
      Filter.Tendsto (fun n : ℕ => (loopStepMap φ W U x)^[n] x) Filter.atTop (nhds p) := by
  have hc := loopStepMap_contracting φ W U Lφ hφ hLφ hρ1 x
  have hfin : edist x (loopStepMap φ W U x x) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨p, hp, hconv, _⟩ := hc.exists_fixedPoint x hfin
  exact ⟨p, hp.eq, hconv⟩

/-! ## 四、仿射迭代 `x ↦ T x + b`（`RealL2Operator` / `RealMatrixStability` 的缺口） -/

/-- 仿射迭代步：`x ↦ T x + b`（线性算子 + 常向量）。
这是 `RealMatrixStability.iterateStep` 的「一步」形式。 -/
def affineStep (T : X →L[ℝ] X) (b : X) : X → X := fun x => T x + b

/-- 仿射步的 Lipschitz 性：`‖T‖`-Lipschitz（`b` 在差中抵消）。 -/
theorem affineStep_lipschitz (T : X →L[ℝ] X) (b : X) :
    ∀ a c, ‖affineStep T b a - affineStep T b c‖ ≤ ‖T‖ * ‖a - c‖ := by
  intro a c
  have h : affineStep T b a - affineStep T b c = T (a - c) := by
    simp only [affineStep, map_sub]
    abel
  rw [h]
  exact T.le_opNorm (a - c)

/-- **`‖T‖ < 1` ⟹ 仿射步是 `‖T‖`-收缩**（`RealL2Operator` 的算子范数进入 Banach 链条）。 -/
theorem affineStep_contracting (T : X →L[ℝ] X) (b : X) (hT : ‖T‖ < 1) :
    ContractingWith ⟨‖T‖, norm_nonneg T⟩ (affineStep T b) :=
  contracting_of_lipschitz (norm_nonneg T) hT _ (affineStep_lipschitz T b)

/-- **仿射不动点存在性**：完备范数空间 + `‖T‖ < 1` ⟹ `∃p, T p + b = p`。
这补上了 `RealL2Operator` / `RealMatrixStability` 中标注的「不动点存在性未做」
（注意：对**线性** `T` 而言不动点存在性是平凡的，见 `linearMap_fixed_point_zero`；
有价值的正是仿射版本）。 -/
theorem affine_fixed_point_exists [CompleteSpace X] (T : X →L[ℝ] X) (b : X) (hT : ‖T‖ < 1) :
    ∃ p : X, T p + b = p := by
  have hc := affineStep_contracting T b hT
  have hfin : edist (0 : X) (affineStep T b 0) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨p, hp, _⟩ := hc.exists_fixedPoint (0 : X) hfin
  exact ⟨p, hp.eq⟩

/-- **仿射不动点唯一性**（不需完备性）：`‖T‖ < 1` 时 `p − q = T(p − q)` 且
`‖p − q‖ ≤ ‖T‖‖p − q‖`，由 `1 − ‖T‖ > 0` 得 `p = q`。 -/
theorem affine_fixed_point_unique (T : X →L[ℝ] X) (b : X) (hT : ‖T‖ < 1) {p q : X}
    (hp : T p + b = p) (hq : T q + b = q) : p = q := by
  have hfix : T (p - q) = p - q := by
    have h1 : T (p - q) = (T p + b) - (T q + b) := by
      rw [map_sub]
      abel
    rw [h1, hp, hq]
  have hnorm : ‖p - q‖ ≤ ‖T‖ * ‖p - q‖ := by
    calc ‖p - q‖ = ‖T (p - q)‖ := by rw [hfix]
      _ ≤ ‖T‖ * ‖p - q‖ := T.le_opNorm (p - q)
  have hd0 : 0 ≤ ‖p - q‖ := norm_nonneg _
  have hpos : 0 < 1 - ‖T‖ := by linarith
  have hle : (1 - ‖T‖) * ‖p - q‖ ≤ 0 := by nlinarith
  have hzero : ‖p - q‖ = 0 :=
    le_antisymm (by nlinarith) hd0
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- **仿射不动点：存在唯一**。 -/
theorem affine_fixed_point_existsUnique [CompleteSpace X] (T : X →L[ℝ] X) (b : X)
    (hT : ‖T‖ < 1) : ∃! p : X, T p + b = p := by
  obtain ⟨p, hp⟩ := affine_fixed_point_exists T b hT
  exact ⟨p, hp, fun q hq => affine_fixed_point_unique T b hT hq hp⟩

/-- **线性算子的不动点存在性是平凡的**：`T 0 = 0` 对任意连续线性算子成立。
（诚实修正：`RealL2Operator` 标注的「不动点存在性未做」若指**线性**版本则无需完备性；
本文件因此只把仿射版本作为实质性缺口来闭合。） -/
theorem linearMap_fixed_point_zero (T : X →L[ℝ] X) : T 0 = 0 := map_zero T

/-! ## 五、几何和展开：`⋆` `RealMatrixStability.iterateStep` 的极限闭合 -/

/-- **仿射迭代的显式公式**：`(x ↦ T x + b)` 的 n 次迭代是
`x ↦ (∑_{k<n} T^k b) + T^n x`。 -/
theorem affine_iterate_eq_geometric (T : X →L[ℝ] X) (b x : X) (n : ℕ) :
    (affineStep T b)^[n] x = (∑ k in Finset.range n, (T ^ k) b) + (T ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      -- 展开 affineStep 与线性性
      simp only [affineStep, map_add]
      rw [map_sum, Finset.sum_range_succ']
      -- 把 T ((T^k) b) 归一为 T^(k+1) b
      have hshift : ∀ k : ℕ, T ((T ^ k) b) = (T ^ (k + 1)) b := by
        intro k
        rw [pow_succ']
        rfl
      simp only [hshift]
      rw [pow_succ', pow_zero, ContinuousLinearMap.one_apply]
      -- T ((T^n) x) 与 (T * T^n) x 是同一个东西
      rw [show T ((T ^ n) x) = (T * T ^ n) x from rfl]
      abel

/-- **不动点的精确展开**：若 `T p + b = p`，则 `p = (∑_{k<n} T^k b) + T^n p`。
这是「不动点 = 几何和的极限」的有限截断形式（`T^n p → 0`）。 -/
theorem affine_fixed_point_expansion (T : X →L[ℝ] X) (b p : X) (hp : T p + b = p) (n : ℕ) :
    p = (∑ k in Finset.range n, (T ^ k) b) + (T ^ n) p := by
  have hpq : affineStep T b p = p := by
    simp only [affineStep]
    exact hp
  have hiter : (affineStep T b)^[n] p = p := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hpq]
  -- 只把左侧的 p 换成迭代形式（用 conv 避免 rw 重写右侧的 p）
  conv_lhs => rw [← hiter]
  rw [affine_iterate_eq_geometric]

/-- **到几何和的距离按 `‖T‖ⁿ` 几何衰减**：`‖p − ∑_{k<n} T^k b‖ ≤ ‖T‖ⁿ‖p‖`。
这是 `RealMatrixStability` 中「`n → ∞` 收敛和未证」的可用替代形式
（极限值 `∑_{k<n} T^k b` 的误差被显式控制）。 -/
theorem affine_fixed_point_geometric_decay (T : X →L[ℝ] X) (b p : X) (hp : T p + b = p) (n : ℕ) :
    ‖p - ∑ k in Finset.range n, (T ^ k) b‖ ≤ ‖T‖ ^ n * ‖p‖ := by
  have hexp := affine_fixed_point_expansion T b p hp n
  have hsub : p - ∑ k in Finset.range n, (T ^ k) b = (T ^ n) p := by
    conv_lhs => rw [hexp]
    abel
  rw [hsub]
  exact op_norm_pow_apply_le T n p

/-- **`RealMatrixStability.iterateStep` 就是仿射迭代**：
`iterateStep T b n = (x ↦ T x + b)^[n] 0`（两者的递归方程相同）。
这一步把 `RealMatrixStability` 的迭代累积界接进本文件的不动点框架。 -/
theorem iterateStep_eq_iterate (T : X →L[ℝ] X) (b : X) (n : ℕ) :
    iterateStep T b n = (affineStep T b)^[n] (0 : X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterateStep_succ, ih, Function.iterate_succ_apply']
      rfl

/-- **`iterateStep` 的显式几何和形式**：`iterateStep T b n = ∑_{k<n} T^k b`。 -/
theorem iterateStep_eq_geometric (T : X →L[ℝ] X) (b : X) (n : ℕ) :
    iterateStep T b n = ∑ k in Finset.range n, (T ^ k) b := by
  rw [iterateStep_eq_iterate, affine_iterate_eq_geometric]
  simp

/-- **`iterateStep` 到仿射不动点的几何距离界**：
`‖iterateStep T b n − p‖ ≤ ‖T‖ⁿ‖p‖`（`p` 是任意仿射不动点）。
这给出了 `RealMatrixStability` 中 `∑_{k<n}‖T‖^k‖b‖` 之外的**收敛形式**。 -/
theorem iterateStep_dist_fixedPoint_le (T : X →L[ℝ] X) (b p : X) (hp : T p + b = p) (n : ℕ) :
    ‖iterateStep T b n - p‖ ≤ ‖T‖ ^ n * ‖p‖ := by
  rw [iterateStep_eq_geometric]
  have h := affine_fixed_point_expansion T b p hp n
  have hsub : (∑ k in Finset.range n, (T ^ k) b) - p = -((T ^ n) p) := by
    conv_lhs => rw [h]
    abel
  rw [hsub, norm_neg]
  exact op_norm_pow_apply_le T n p

/-- **`iterateStep` 收敛到不动点**（完备 + `‖T‖ < 1`）：
`n ↦ iterateStep T b n` 收敛到（唯一）仿射不动点。 -/
theorem iterateStep_tendsto_fixedPoint [CompleteSpace X] (T : X →L[ℝ] X) (b : X)
    (hT : ‖T‖ < 1) :
    ∃ p : X, T p + b = p ∧
      Filter.Tendsto (fun n : ℕ => iterateStep T b n) Filter.atTop (nhds p) := by
  have hc := affineStep_contracting T b hT
  have hfin : edist (0 : X) (affineStep T b 0) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨p, hp, hconv, _⟩ := hc.exists_fixedPoint (0 : X) hfin
  refine ⟨p, hp.eq, ?_⟩
  have hfun : (fun n : ℕ => iterateStep T b n)
      = fun n : ℕ => (affineStep T b)^[n] (0 : X) := by
    funext n
    exact iterateStep_eq_iterate T b n
  rw [hfun]
  exact hconv

/-! ## 六、导数形式的压缩（中值定理）与有限维实例化 -/

/-- **导数有界 ⟹ 压缩**（中值定理）：若 `f` 处处 Frechet 可导、导数 `f'` 的算子范数
一致地被 `C` 控制，则 `f` 是 `C`-Lipschitz。
用 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`（在 `univ` 上）。 -/
theorem contraction_of_deriv_bound (f : X → X) (f' : X → X →L[ℝ] X) (C : ℝ)
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hbound : ∀ x, ‖f' x‖ ≤ C) :
    ∀ a b, ‖f a - f b‖ ≤ C * ‖a - b‖ := by
  intro a b
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hf x).hasFDerivWithinAt) (fun x _ => hbound x) convex_univ
    (Set.mem_univ a) (Set.mem_univ b)

/-- **导数版本的不动点存在唯一性**：`∀x, ‖f' x‖ ≤ C < 1` 且空间完备 ⟹ 存在唯一不动点。 -/
theorem contraction_derivative_fixed_point_existsUnique [CompleteSpace X] (f : X → X)
    (f' : X → X →L[ℝ] X) {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C < 1)
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hbound : ∀ x, ‖f' x‖ ≤ C) :
    ∃! p : X, f p = p :=
  contraction_fixed_point_existsUnique hC0 hC1 f (contraction_of_deriv_bound f f' C hf hbound)

/-- **有限维 `EuclideanSpace` 上的导数版本**（`‖f'‖ < 1`）：
完备性由 mathlib 现成的 `FiniteDimensional.complete` 提供
（`EuclideanSpace ℝ (Fin n)` 是有限维的），因此「有限维完备」不是本文件的新假设，
而是直接调用 mathlib。 -/
theorem euclidean_derivative_fixed_point_existsUnique (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C < 1)
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hbound : ∀ x, ‖f' x‖ ≤ C) :
    ∃! p : EuclideanSpace ℝ (Fin n), f p = p := by
  haveI : CompleteSpace (EuclideanSpace ℝ (Fin n)) := FiniteDimensional.complete ℝ _
  exact contraction_derivative_fixed_point_existsUnique f f' hC0 hC1 hf hbound

/-- **有限维 `EuclideanSpace` 上的仿射版本**：`‖T‖ < 1` ⟹ `∃!p, T p + b = p`。 -/
theorem euclidean_affine_fixed_point_existsUnique (n : ℕ)
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (hT : ‖T‖ < 1) :
    ∃! p : EuclideanSpace ℝ (Fin n), T p + b = p := by
  haveI : CompleteSpace (EuclideanSpace ℝ (Fin n)) := FiniteDimensional.complete ℝ _
  exact affine_fixed_point_existsUnique T b hT

/-! ## 七、反例：`‖T‖ < 1` 的严格性不能去掉 -/

/-- **反例（机器验证）**：`‖T‖ = 1`（非严格收缩）时不动点可以不存在——
ℝ 上的平移 `x ↦ x + 1` 没有不动点。这与 `affine_fixed_point_exists`
所要求的 `‖T‖ < 1` 严格不等式形成对照：该假设**不可放松**。 -/
theorem translation_no_fixed_point : ¬ ∃ p : ℝ, p + 1 = p := by
  rintro ⟨p, hp⟩
  linarith

/-- **反例（仿射形式）**：`affineStep 1 1`（线性部分为恒等算子，`‖id‖ = 1`）没有不动点。 -/
theorem translation_affineStep_no_fixed_point :
    ¬ ∃ p : ℝ, affineStep (1 : ℝ →L[ℝ] ℝ) 1 p = p := by
  rintro ⟨p, hp⟩
  simp only [affineStep, ContinuousLinearMap.one_apply] at hp
  linarith

/-- 反例的算子范数注记：`‖(1 : ℝ →L[ℝ] ℝ)‖ = 1`，故严格不等式 `‖T‖ < 1` 不成立。 -/
theorem id_norm_eq_one : ‖(1 : ℝ →L[ℝ] ℝ)‖ = 1 := ContinuousLinearMap.norm_id

/-! ## 八、诚实缺口清单（本文件闭合了什么、没闭合什么）

闭合（均为机器验证的定理）：
  · `RealLoopModel` 的不动点存在性 —— `loop_fixed_point_exists` /
    `loop_fixed_point_existsUnique`（新增假设 `[CompleteSpace X]`）；
  · `RealL2Operator` 的仿射不动点存在性 —— `affine_fixed_point_exists`；
  · `RealMatrixStability` 的不动点存在性与几何收敛形式 ——
    `affine_fixed_point_expansion`、`iterateStep_dist_fixedPoint_le`、
    `iterateStep_tendsto_fixedPoint`；
  · 有限维 `EuclideanSpace` 上 `‖f'‖ < 1` 的导数版本。

未证 / 未做（诚实标注）：
  · 「不完备空间上压缩映射可以没有不动点」的**机器验证反例**：**未做**。
    只用文档说明完备性在链条中的确切位置（`ContractingWith.exists_fixedPoint`）。
  · `RealMatrixStability` 中 `n → ∞` 的**级数极限值** `‖b‖/(1−‖T‖)` 的等价形式：
    本文件给的是不动点误差界 `‖T‖ⁿ‖p‖`（等价且更强可用的形式），
    没有单独证明 `∑_{k<n} ‖T‖ᵏ‖b‖` 收敛到 `‖b‖/(1−‖T‖)`；
  · 局部（凸集上）导数版本：未做，只给全局版本。
-/

end Lattice
