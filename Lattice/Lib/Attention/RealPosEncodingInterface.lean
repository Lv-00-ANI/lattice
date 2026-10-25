import Mathlib
import Lattice.Lib.Attention.RealAbsPosEncoding
import Lattice.Lib.Attention.RealALiBi
import Lattice.Lib.Attention.RealRelPosEncoding
import Lattice.Lib.Attention.RealRoPE
/-!
# LATTICE: 位置编码统一接口（接口 + 三个实例 + 接口蕴含的端到端误差界）

`RealAbsPosEncoding.abs_vs_rope_vs_alibi` 把绝对编码 / ALiBi / RoPE 的刻画性事实
写成一个**合取式**。本文件把它**升级为接口**：

    structure PositionEncoding (ι)  —— 字段：实际编码 `phi`、参考距离 `distF`、
      界 `B` 与 Lipschitz 常数 `L`（含非负性证明）、
      **有界性** `bounded`、**Lipschitz** `lipschitz`、
      **平移性质类型** `shiftTag`（`.absolute` / `.additive` / `.rotational`）
      与承载该性质的**命题** `shiftLaw`（由 `shiftLaw_holds` 填充）

并为三种编码给出**实例**（每个字段都由既有具体定理填充，不是文字描述）：

  1. `absPosEncodingInterface`（`ι = ℝ`，`phi pos = absPosEnc d pos i`）：
     `B = 1`（`abs_pos_bounded`）、`L = 1`（`abs_pos_smooth`）、
     `shiftLaw` 由 `abs_pos_relative_shift`（逐频旋转）填充；
  2. `alibiPosEncodingInterface`（`ι = Fin n`，`phi i = alibiBias m i j₀`）：
     `B = m·(n−1)`（`alibi_is_bounded_perturbation`）、`L = m`（`alibi_bias_lipschitz`）、
     `shiftLaw = IsTranslationEquivariant (−m·dist)`（`alibi_bias_translation_equivariant`）；
  3. `ropePosEncodingInterface`（`ι = ℝ`，相位分量 `phi t = cos (θ·t)`）：
     `B = 1`（`Real.abs_cos_le_one`）、`L = |θ|`（`abs_cos_sub_cos_le`）、
     `shiftLaw =` RoPE 的相对点积恒等式（`rope_relative_preserves_dot`）。

以及**接口蕴含**的通用端到端误差界（对任意满足接口的编码自动成立）：

  * `PositionEncoding.error_bound`：`|(u+φx) − (v+φy)| ≤ |u−v| + L·distF x y`；
  * `PositionEncoding.error_bound_of_close`：`|u−v| ≤ ε`、`distF x y ≤ δ` ⟹
    `≤ ε + L·δ`；
  * `PositionEncoding.output_bound`：`|u+φx| ≤ |u| + B`；
  * `PositionEncoding.stack_error_bound`：n 项求和的**端到端**界
    `≤ n·(ε + L·δ)`；
  * `posenc_interface_instances`：三个实例同时存在（对照
    `RealAbsPosEncoding.abs_vs_rope_vs_alibi`）。

**诚实标注（中文关键词）**：
  · `distF` 是**显式传入的参考距离**（而非类型类 `dist`）——因为 `Fin n`
    不保证有 `PseudoMetricSpace` 实例，显式距离让三种编码可统一；
  · `shiftLaw` 是**承载平移性质类型的真命题**（每个实例都由具体定理填充），
    不是占位文字；
  · **未做**：把接口升级为「乘性/加性」两类算子的代数结构（本文件只做语义分类）；
  · **未证**：接口之间的**包含关系**（如 RoPE 实例是否也满足加性接口）。
  无 sorry/axiom/admit。
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、平移性质标签与统一接口 -/

/-- 位置编码的平移性质类型：绝对三角（非平移等变）/ 加性距离偏置 / 乘性相位旋转。 -/
inductive ShiftTag where
  | absolute
  | additive
  | rotational
  deriving DecidableEq

/-- **位置编码统一接口**。字段：编码函数 `phi`、参考距离 `distF`、
界 `B` 与 Lipschitz 常数 `L`（带非负性）、**有界性**、**Lipschitz 性**、
平移性质类型 `shiftTag` 与承载它的命题 `shiftLaw`。 -/
structure PositionEncoding (ι : Type*) where
  /-- 编码函数（标量分量） -/
  phi : ι → ℝ
  /-- 参考距离（显式传入，避免依赖 `PseudoMetricSpace (Fin n)`） -/
  distF : ι → ι → ℝ
  /-- 一致界 -/
  B : ℝ
  /-- Lipschitz 常数 -/
  L : ℝ
  hB : 0 ≤ B
  hL : 0 ≤ L
  /-- 有界性字段 -/
  bounded : ∀ i, |phi i| ≤ B
  /-- Lipschitz 字段 -/
  lipschitz : ∀ i j, |phi i - phi j| ≤ L * distF i j
  /-- 平移性质类型 -/
  shiftTag : ShiftTag
  /-- 平移性质命题（由具体定理填充） -/
  shiftLaw : Prop
  shiftLaw_holds : shiftLaw

/-! ## 二、接口蕴含的通用界 -/

/-- **接口蕴含（单步）**：`|(u+φx) − (v+φy)| ≤ |u−v| + L·distF x y`。 -/
theorem PositionEncoding.error_bound (E : PositionEncoding ι) (u v : ℝ) (x y : ι) :
    |(u + E.phi x) - (v + E.phi y)| ≤ |u - v| + E.L * E.distF x y := by
  have h : (u + E.phi x) - (v + E.phi y) = (u - v) + (E.phi x - E.phi y) := by ring
  rw [h]
  calc |(u - v) + (E.phi x - E.phi y)| ≤ |u - v| + |E.phi x - E.phi y| := abs_add _ _
    _ ≤ |u - v| + E.L * E.distF x y := by linarith [E.lipschitz x y]

/-- **接口蕴含（近似形式）**：`|u−v| ≤ ε`、`distF x y ≤ δ`（`δ ≥ 0`）⟹
`|(u+φx) − (v+φy)| ≤ ε + L·δ`。 -/
theorem PositionEncoding.error_bound_of_close (E : PositionEncoding ι) (u v : ℝ) (x y : ι)
    {eps delta : ℝ} (huv : |u - v| ≤ eps) (hxy : E.distF x y ≤ delta) (hdelta : 0 ≤ delta) :
    |(u + E.phi x) - (v + E.phi y)| ≤ eps + E.L * delta := by
  have hLd : E.L * E.distF x y ≤ E.L * delta := mul_le_mul_of_nonneg_left hxy E.hL
  calc |(u + E.phi x) - (v + E.phi y)| ≤ |u - v| + E.L * E.distF x y :=
        E.error_bound u v x y
    _ ≤ eps + E.L * delta := by linarith

/-- **接口蕴含（输出界）**：`|u + φx| ≤ |u| + B`。 -/
theorem PositionEncoding.output_bound (E : PositionEncoding ι) (u : ℝ) (x : ι) :
    |u + E.phi x| ≤ |u| + E.B := by
  calc |u + E.phi x| ≤ |u| + |E.phi x| := abs_add _ _
    _ ≤ |u| + E.B := by linarith [E.bounded x]

/-- **接口蕴含（端到端 / n 项求和）**：逐项误差 `≤ ε`、位置距离 `≤ δ` ⟹
`|Σ_k (u_k + φ x_k) − Σ_k (v_k + φ y_k)| ≤ n·(ε + L·δ)`。 -/
theorem PositionEncoding.stack_error_bound (E : PositionEncoding ι) {n : ℕ}
    (x y : Fin n → ι) (u v : Fin n → ℝ) {eps delta : ℝ}
    (huv : ∀ k, |u k - v k| ≤ eps) (hxy : ∀ k, E.distF (x k) (y k) ≤ delta)
    (hdelta : 0 ≤ delta) :
    |∑ k, (u k + E.phi (x k)) - ∑ k, (v k + E.phi (y k))|
      ≤ n * (eps + E.L * delta) := by
  have h1 : ∑ k, (u k + E.phi (x k)) - ∑ k, (v k + E.phi (y k))
      = ∑ k, ((u k + E.phi (x k)) - (v k + E.phi (y k))) := by
    rw [Finset.sum_sub_distrib]
  rw [h1]
  calc |∑ k, ((u k + E.phi (x k)) - (v k + E.phi (y k)))|
      ≤ ∑ k, |(u k + E.phi (x k)) - (v k + E.phi (y k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, (eps + E.L * delta) := by
        apply Finset.sum_le_sum
        intro k _
        exact E.error_bound_of_close (u k) (v k) (x k) (y k) (huv k) (hxy k) hdelta
    _ = n * (eps + E.L * delta) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 三、三个实例（每个字段都由既有定理填充） -/

/-- **实例 1：绝对三角位置编码**（`ι = ℝ`）。
`B = 1` ← `abs_pos_bounded`；`L = 1` ← `abs_pos_smooth`；
`shiftLaw` ← `abs_pos_relative_shift`（逐频旋转，非平移等变）。 -/
noncomputable def absPosEncodingInterface (d : ℕ) (i : Fin d) : PositionEncoding ℝ where
  phi := fun pos => absPosEnc d pos i
  distF := fun x y => |x - y|
  B := 1
  L := 1
  hB := zero_le_one
  hL := zero_le_one
  bounded := fun pos => abs_pos_bounded d pos i
  lipschitz := fun p q => by
    simpa using abs_pos_smooth d p q i
  shiftTag := ShiftTag.absolute
  shiftLaw := ∀ (pos k D : ℝ) (m : ℕ) (h1 : 2 * m < d) (h2 : 2 * m + 1 < d),
      absPosDenom d ⟨2 * m, h1⟩ = D → absPosDenom d ⟨2 * m + 1, h2⟩ = D →
        absPosEnc d (pos + k) ⟨2 * m, h1⟩
          = absPosEnc d pos ⟨2 * m, h1⟩ * Real.cos (k / D)
            + absPosEnc d pos ⟨2 * m + 1, h2⟩ * Real.sin (k / D)
  shiftLaw_holds := fun pos k D m h1 h2 hD1 hD2 =>
    (abs_pos_relative_shift d pos k D m h1 h2 hD1 hD2).1

/-- **实例 2：ALiBi 距离偏置**（`ι = Fin n`，固定键位置 `j₀`）。
`B = m·(n−1)` ← `alibi_is_bounded_perturbation`；`L = m` ← `alibi_bias_lipschitz`；
`shiftLaw` ← `alibi_bias_translation_equivariant`（平移等变）。 -/
noncomputable def alibiPosEncodingInterface (m : ℝ) (hm : 0 ≤ m) (n : ℕ) (j0 : Fin n) :
    PositionEncoding (Fin n) where
  phi := fun i => alibiBias m i.val j0.val
  distF := fun i j => dist i.val j.val
  B := m * ((n - 1 : ℕ) : ℝ)
  L := m
  hB := mul_nonneg hm (Nat.cast_nonneg _)
  hL := hm
  bounded := fun i => by
    simpa [alibiBias, dist_comm] using alibi_is_bounded_perturbation m hm j0 i
  lipschitz := fun i j => by
    simpa [alibiBias, dist_comm] using alibi_bias_lipschitz m hm j0.val i.val j.val
  shiftTag := ShiftTag.additive
  shiftLaw := IsTranslationEquivariant (fun i j : ℕ => alibiBias m i j)
  shiftLaw_holds := alibi_bias_translation_equivariant m

/-- **实例 3：RoPE 相位分量**（`ι = ℝ`，`phi t = cos (θ·t)`）。
`B = 1` ← `Real.abs_cos_le_one`；`L = |θ|` ← `abs_cos_sub_cos_le`；
`shiftLaw` ← `rope_relative_preserves_dot`（相对旋转保点积）。 -/
noncomputable def ropePosEncodingInterface (θ : ℝ) (q k : Point2R) : PositionEncoding ℝ where
  phi := fun t => Real.cos (θ * t)
  distF := fun x y => |x - y|
  B := 1
  L := |θ|
  hB := zero_le_one
  hL := abs_nonneg θ
  bounded := fun t => Real.abs_cos_le_one _
  lipschitz := fun x y => by
    have h := abs_cos_sub_cos_le (θ * x) (θ * y)
    have harg : θ * x - θ * y = θ * (x - y) := by ring
    rw [harg, abs_mul] at h
    simpa using h
  shiftTag := ShiftTag.rotational
  shiftLaw := ∀ a b : ℝ,
    rdot (rotateR (a * θ) q) (rotateR (b * θ) k) = rdot q (rotateR ((b - a) * θ) k)
  shiftLaw_holds := fun a b => rope_relative_preserves_dot a b θ q k

/-- **三实例同时存在**（接口化的 `abs_vs_rope_vs_alibi`）：
绝对编码、ALiBi、RoPE 都是 `PositionEncoding` 的成员，且各自带自己的平移性质。 -/
theorem posenc_interface_instances (d : ℕ) (i : Fin d) (m : ℝ) (hm : 0 ≤ m)
    (n : ℕ) (j0 : Fin n) (θ : ℝ) (q k : Point2R) :
    (∃ E : PositionEncoding ℝ, E.phi 0 = absPosEnc d 0 i ∧ E.B = 1 ∧ E.L = 1) ∧
    (∃ E : PositionEncoding (Fin n), E.B = m * ((n - 1 : ℕ) : ℝ) ∧ E.L = m) ∧
    (∃ E : PositionEncoding ℝ, E.B = 1 ∧ E.L = |θ|) :=
  ⟨⟨absPosEncodingInterface d i, rfl, rfl, rfl⟩,
   ⟨alibiPosEncodingInterface m hm n j0, rfl, rfl⟩,
   ⟨ropePosEncodingInterface θ q k, rfl, rfl⟩⟩

/-! ## 四、锐性（C8）：每个实例的 `B`/`L` 是否 sharp

§三 的三个实例给出 `B` 与 `L` 的具体值。**它们是最优的吗？** 本节逐个核查，
并**如实标注**：哪些已给出机器验证的取等见证、哪些只是可行上界、哪些**未做**。

⚠ **本节口径（重要，v14 修订）**：下列清单里**只有实际存在且陈述与声称相符的定理**
才被当作"已证"。**任何未形式化的名称一律是"计划/未做"，不是"已证"**——
本文件此前曾把 6 个**全库不存在**的名字（`rope_L_sharp_of_lt`、`rope_sharp_iff`、
`alibi_B_sharp`、`alibi_L_sharp`、`absPos_L_not_sharp`、`rope_L_sharp_sup`）
当作已证定理引用，属**声称层缺陷**（编译查不出），现已逐条标注。

### 4.1 RoPE（`phi t = cos (θ t)`）：`B = 1` **sharp**；`L = |θ|` 取等**未做**

  * **`rope_B_sharp`（已证）**：`t = 0` 时 `|cos 0| = 1 = B` —— `B = 1` **被取等**，
    不可能改进（`|cos| ≤ 1` 是紧的）；
  * **`L = |θ|` 的取等：未做（原声称有误）**。曾（错误地）引用
    `rope_L_sharp_of_lt`、`rope_sharp_iff` 作"取等/充要"见证，但
    **这两个名字在全库不存在，取等命题本身也不成立**——`cos` 是 1-Lipschitz，
    而取等需 `|θ|·|s| = 1` 与 `|cos(θs)| = 1` 同时成立，即 `π/2 = 1`，**不可能**
    （详见 `rope_L_sharp` 的 docstring，本文件**已撤回**该声称）。
    真正成立的是 **`sup` 意义下的最优常数**：`L = |θ|` 是 `cos(θ·)` 的最优
    Lipschitz 常数；**其形式化（差商 `s → 0⁺` 极限）为 `rope_L_sharp_sup`
    这一计划名，本文件未做**（该名字同样全库不存在）。

### 4.2 ALiBi（`phi i = −m·dist(i, j₀)`）：`B = m(n−1)` sharp、`L = m` sharp —— **均未形式化**

  * **`alibi_B_sharp`：未做**。素材**已具备**（`RealALiBi.alibi_fin_dist_le`，
    `RealALiBi.lean:106`：`dist i.val j.val ≤ n − 1`，且 `Fin n` 的两端点可取到
    `dist = n − 1`），但**本文件未写出该定理**——`alibi_B_sharp` 是全库不存在的名字；
  * **`alibi_L_sharp`：未做**。同上，素材在库（两端点 `dist = n−1` 与 `dist = 0`
    的取等），但**本文件未写出该定理**——`alibi_L_sharp` 亦是全库不存在的名字。
  * ⚠ 因此 4.2 的两条"取等"目前**零形式化内容**：接口实例的 `B = m·(n−1)` 与
    `L = m` 只是**可行界**（分别由 `alibi_is_bounded_perturbation`、
    `alibi_bias_lipschitz` 给出），**其最优性未被本文件证明**。

### 4.3 绝对编码（`absPosEnc`）：`B = 1` **sharp**（已证）；`L = 1` 的改进**部分已证**

  * **`absPos_B_sharp`（已证）**：显式取 `pos` 使 `pos/D = π`，则**奇分量**（`cos`）
    取 `|PE| = 1`（`cos π = −1`）—— `B = 1` **可达**（不是仅由 `|cos| ≤ 1` 得到的开界）。
    ⚠ **v14 修正**：本定理原先取**偶**分量（`sin`）并声称 `|PE| = 1`，
    但 `sin π = 0` ⟹ `|PE| = 0 ≠ 1`，**该陈述为假且编译报错**（`⊢ False`），已改取奇分量；
    ⚠ 此前散文称此处"由单位圆 `PE² + PE'² = 1` 故至少有一个达到 `1`，形式化为
    `abs_le_one_of_sq_add_sq`（原名 `exists_abs_eq_one_of_sq_add_sq`）"——**该描述有误**：
    该引理**实际只证 `|a| ≤ 1 ∧ |b| ≤ 1`**（原名字里的"eq_one"名不副实，已改名），
    而"至少一个达到 `1`"这一命题**为假**（反例 `a = b = √2/2`）；
    真正给出可达性的是本条的显式取等点；
  * **`absPos_L_not_sharp`：未做**（全库不存在的名字）。`L` 可收紧到 `1/D`
    （`D ≥ 1` 是分母、`absPosDenom_one_le`）这一**方向**成立，但：
      * **`absPos_smooth_sharp`（已证，但只是上界）**：
        `|PE p i − PE q i| ≤ (1/D)·|p − q|`。⚠ **这仅证明 `1/D` 是一个可行常数，
        未证明它是"紧"（最优）常数**——原 docstring 称"紧常数是 `1/D`"属**过度声称**，
        已修正（见其 docstring）；
      * **`absPos_L_improved`（已证，纯数值事实）**：`D > 1` 时 `1/D < 1`。
        ⚠ 这是关于**倒数**的算术事实，**不是**"Lipschitz 常数被严格改进"的陈述；
      * **`absPos_L_sharp_at_D_one`（已证，但非"取等"见证）**：`D = 1` 时
        `(1/D)⁻¹ = 1`。⚠ 其内容只是**代数重写**（`rw [hD, inv_one]`），
        **不含任何"界被取等/最优"的断言**——原 docstring 称"界取等、`|sin p − sin q|`
        可达 `|p−q|`（取 `p−q = π`）"是**假的**（`p−q = π` 时 `sin p − sin(p+π) = 0`）。
        事实上 `1/D` 在任何 `D` 上**都不被取等**（`sin`/`cos` 在非退化区间上
        `|f′|` 不恒为 `1/D`），最优常数只是 `sup`。

**诚实标注（C8）**：
  · 4.1 的 `B` 取等是**精确且已证**的（只依赖 `cos 0 = 1`）；
  · 4.1 的 `L = |θ|` 取等**已撤回**（取等命题为假，见 `rope_L_sharp` docstring）；
    `sup` 意义的最优性**未做**；
  · 4.2 的 `B`/`L` 取等**均未形式化**（素材在 `RealALiBi`，名字全库不存在）；
  · 4.3 的 `B = 1` 可达**已证**；`L` 的改进**只证到"`1/D` 是可行上界"**：
    `RealPosEncodingInterface.absPosEncodingInterface`（以及
    `RealAbsPosEncoding.abs_pos_smooth`）给出的 `L = 1` 确实**偏松**
    （`1/D ≤ 1`，且 `D > 1` 时严格更小），本文件**保留**旧的 `L = 1` 版本
    （仍是有效上界，符合 STYLE §5.3「不删旧版」），同时给出更紧的**上界**；
    ⚠ **但"`1/D` 是紧常数"这一声称未证且已撤回**（需差商/最优性论证，**未做**）；
  · **未做**：把 `absPosEncodingInterface` 的 `L` 字段**改为** `1/D` 会破坏
    接口的「常数与 `i` 无关」设计（`D` 依赖 `i`），故本文件**不**改接口，
    只给出逐 `i` 的更紧上界，**标注未做**。 -/

/-- **RoPE 的 `B = 1` 取等**：`t = 0` 时 `|cos 0| = 1`（`B = 1` 不可改进）。 -/
theorem rope_B_sharp (θ : ℝ) : |Real.cos (θ * 0)| = 1 := by
  simp

/-- **`θ/|θ| = ±1`**（`θ ≠ 0`）：分离辅助引理，避免在主证明里纠缠 `abs`/`div` 的重写。 -/
theorem div_abs_self_eq_pm_one (θ : ℝ) (hθ : θ ≠ 0) : θ / |θ| = 1 ∨ θ / |θ| = -1 := by
  rcases lt_or_gt_of_ne hθ.symm with h | h
  · -- `h : 0 < θ` ⟹ `|θ| = θ` ⟹ `θ/|θ| = 1`
    left
    rw [abs_of_pos h]
    exact div_self (ne_of_gt h)
  · -- `h : θ < 0` ⟹ `|θ| = -θ` ⟹ `θ/|θ| = θ/(-θ) = -(θ/θ) = -1`
    -- ⚠ `rw` 链已闭合目标（`div_neg_eq_neg_div` 给出 `-(θ/θ)`，`div_self` 化为 `-1`），
    -- 故**不可**再跟 `ring`（会报 `no goals to be solved`，见 STYLE §4 `field_simp` 同族坑）。
    right
    rw [abs_of_neg h, div_neg_eq_neg_div, div_self (ne_of_lt h)]

/-- **RoPE：`θ ≠ 0` 时 `|cos 0 − cos (θ s)| = 1`（`s = π/(2|θ|)`）**。

⚠ **定理名 `rope_L_sharp` 是历史名称，名不副实（保留不改以兼容既有引用）**：
本定理**不**声称 `L = |θ|` 被取等。它只证明：取 `s = π/(2|θ|)` 时
`|cos 0 − cos (θ s)| = 1`（用 `θ·s = ±π/2`，故 `cos (θ s) = 0`）。

**为什么不能声称 `L = |θ|` 取等**（**退回推理，保留自本文件早期版本**）：
`cos` 是 `1`-Lipschitz（`abs_cos_sub_cos_le`），而 `L = |θ|` 的界来自
「`cos(θ·)` 的 Lipschitz 常数 `= |θ|`」。**取等需要 `|θ|·|s| = 1` 且
`cos(θs) = 0` 同时成立**，即 `|θ|·|s| = 1` 与 `|θ s| = π/2` 同时成立
⟹ `π/2 = 1`，**不可能**。
（曾试两条路径并均被否：① `s = π/(2|θ|)` ⟹ 左端 `= |1 − 0| = 1`、
右端 `= |θ|·|s| = π/2`，**`1 ≠ π/2`**；② 取 `θs = ±π` 使 `cos(θs) = −1`
⟹ 左端 `|1 − (−1)| = 2`、右端 `|θ|·(π/|θ|) = π`，**仍不等**。）

因此本节**不**声称 `L = |θ|` 取等；真正成立的是 **`sup` 意义下的最优常数**
`= |θ|`（由「对任意 `c < |θ|`，存在 `s` 使 `|cos 0 − cos(θs)| > c·|s|`」刻画）。
⚠ **该 `sup` 版最优性本文件未做**：与之对应的计划名 `rope_L_sharp_sup`
（用 `s → 0⁺` 的差商极限）**在全库不存在**，故该路径**零形式化内容**。 -/
theorem rope_L_sharp (θ : ℝ) (hθ : θ ≠ 0) :
    |Real.cos (θ * 0) - Real.cos (θ * (Real.pi / (2 * |θ|)))| = 1 := by
  have harg : θ * (Real.pi / (2 * |θ|)) = (θ / |θ|) * (Real.pi / 2) := by ring
  have hpm := div_abs_self_eq_pm_one θ hθ
  have hzero : θ * 0 = 0 := mul_zero θ
  rw [hzero, harg, Real.cos_zero]
  rcases hpm with h | h
  · rw [h, one_mul, Real.cos_pi_div_two, sub_zero, abs_one]
  · rw [h, neg_one_mul, Real.cos_neg, Real.cos_pi_div_two, sub_zero, abs_one]

/-- **`a² + b² = 1` ⟹ `|a| ≤ 1 ∧ |b| ≤ 1`**（由 `sq_le_one_iff_abs_le_one`）。

⚠ **改名说明（v14）**：本定理原名 `exists_abs_eq_one_of_sq_add_sq`，
**名字暗示 `∃ …, |·| = 1`，与实际内容（`≤ 1`）不符**，已按内容改名。
**原"取等"命题为假**：`a² + b² = 1` **不**蕴含 `|a| = 1 ∨ |b| = 1`
（反例 `a = b = √2/2`，二者都 ≈ 0.707）。本文件对 `B = 1` 的**可达性**
改由显式取等点证明（见 `absPos_B_sharp`）。 -/
theorem abs_le_one_of_sq_add_sq {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    |a| ≤ 1 ∧ |b| ≤ 1 := by
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  exact ⟨(sq_le_one_iff_abs_le_one a).mp ha, (sq_le_one_iff_abs_le_one b).mp hb⟩

/-- **绝对编码的 `B = 1` sharp（显式取等点，奇分量）**：对满足 `2m+1 < d` 的频率，
**取 `pos` 使 `pos/D = π`**（`D = absPosDenom d ⟨2m+1,…⟩`），
则**奇分量**（`cos`）取 `|PE| = 1`（因 `cos π = −1`）。

即 `B = 1` 对绝对编码是**可达**的（不是仅由 `|cos| ≤ 1` 得到的开界）。

⚠ **v14 修正（原陈述为假）**：本定理原取**偶**分量（`2m`，即 `sin`）并声称
`|PE| = 1`，但 `sin π = 0` ⟹ `|PE| = 0 ≠ 1`——**该陈述不可证**（构建报
`unsolved goals ⊢ False`）。已改为**奇**分量（`cos`）：`cos π = −1` ⟹ `|−1| = 1` 成立。 -/
theorem absPos_B_sharp (d : ℕ) (m : ℕ) (h1 : 2 * m + 1 < d) :
    |absPosEnc d (Real.pi * absPosDenom d ⟨2 * m + 1, h1⟩) ⟨2 * m + 1, h1⟩| = 1 := by
  have hD : 0 < absPosDenom d ⟨2 * m + 1, h1⟩ := absPosDenom_pos d _
  have hmod : ¬ ((⟨2 * m + 1, h1⟩ : Fin d).val % 2 = 0) := fin_two_mul_add_one_not_mod d m h1
  have hval : Real.pi * absPosDenom d ⟨2 * m + 1, h1⟩ / absPosDenom d ⟨2 * m + 1, h1⟩
      = Real.pi :=
    mul_div_cancel_right₀ Real.pi (ne_of_gt hD)
  have hcos : Real.cos (Real.pi * absPosDenom d ⟨2 * m + 1, h1⟩ / absPosDenom d ⟨2 * m + 1, h1⟩)
      = -1 := by
    rw [hval, Real.cos_pi]
  have henc : absPosEnc d (Real.pi * absPosDenom d ⟨2 * m + 1, h1⟩) ⟨2 * m + 1, h1⟩ = -1 := by
    show (if (⟨2 * m + 1, h1⟩ : Fin d).val % 2 = 0
        then Real.sin (Real.pi * absPosDenom d ⟨2 * m + 1, h1⟩
              / absPosDenom d ⟨2 * m + 1, h1⟩)
        else Real.cos (Real.pi * absPosDenom d ⟨2 * m + 1, h1⟩
              / absPosDenom d ⟨2 * m + 1, h1⟩)) = -1
    rw [if_neg hmod, hcos]
  rw [henc, abs_neg, abs_one]

/-- **绝对编码的 `L`：`1/D` 是一个更紧的可行上界**：
`|PE p i − PE q i| ≤ (1/D)·|p − q|`，其中 `D = absPosDenom d i ≥ 1`。

**意义**：`RealAbsPosEncoding.abs_pos_smooth` 与接口字段用的 `L = 1` 是**偏松的**；
`1/D ≤ 1`，且 `D > 1` 时严格更小。

⚠ **诚实标注（v14 修正）**：本定理**只证明 `1/D` 是可行（admissible）常数**，
**未证明它是"紧"（最优）常数**。原 docstring 称"紧常数是 `1/D`"属**过度声称**。
数学上 `1/D` 确是最优 Lipschitz 常数（`sup|f′| = 1/D`），但**其最优性未形式化**
（需差商上确界论证，**未做**）；且该常数在任何 `D` 上**都不被取等**
（`sin`/`cos` 在非退化区间上 `|f′|` 不恒为 `1/D`），故不存在"取等见证"。 -/
theorem absPos_smooth_sharp (d : ℕ) (p q : ℝ) (i : Fin d) :
    |absPosEnc d p i - absPosEnc d q i| ≤ (absPosDenom d i)⁻¹ * |p - q| := by
  have hD : 0 < absPosDenom d i := absPosDenom_pos d i
  have hdiv : |p / absPosDenom d i - q / absPosDenom d i| ≤ (absPosDenom d i)⁻¹ * |p - q| := by
    have heq : p / absPosDenom d i - q / absPosDenom d i = (p - q) / absPosDenom d i := by ring
    rw [heq, abs_div, abs_of_nonneg (le_of_lt hD), div_eq_inv_mul, mul_comm]
  unfold absPosEnc
  by_cases h : i.val % 2 = 0
  · rw [if_pos h, if_pos h]
    exact le_trans (abs_sin_sub_sin_le _ _) hdiv
  · rw [if_neg h, if_neg h]
    exact le_trans (abs_cos_sub_cos_le _ _) hdiv

/-- **`1/D < 1`（`D > 1`）—— 一条关于倒数的纯算术事实**。

⚠ **诚实标注（v14 修正）**：本定理的陈述**只涉及数值 `1/D` 与 `1` 的大小关系**，
**不是**"`absPosEnc` 的 Lipschitz 常数被严格改进"的陈述（那需要先证 `1/D` 最优，
**未做**）。原 docstring 称"常数的 `1/1` 都被严格改进"易被误读为后者，已修正措辞。
它确实**支持**"`L = 1` 偏松"这一定性结论（配合 `absPos_smooth_sharp` 的上界）。 -/
theorem absPos_L_improved (d : ℕ) (i : Fin d) (hD : 1 < absPosDenom d i) :
    (absPosDenom d i)⁻¹ < 1 := by
  rw [inv_lt_one_iff₀]
  right
  exact hD

/-- **`D = 1` 时 `(1/D)⁻¹ = 1` —— 一条代数重写**。

⚠ **定理名 `absPos_L_sharp_at_D_one` 名不副实（保留不改以兼容既有引用）**：
本定理**不**声称"`L = 1` 在此取等/是 sharp"——其证明体只是 `rw [hD, inv_one]`，
**不含任何关于编码值、差商或最优性的内容**。原 docstring 称"界取等（在频率 1 上
`|sin p − sin q|` 可达 `|p−q|`，取 `p−q = π`）"是**假的**：
`p − q = π` 时 `sin p − sin(p+π) = 0 ≠ π`。事实上 `1/D` **在任何 `D` 上都不被取等**。
本定理的真实内容仅是：`D = 1` 时可行常数 `1/D` 的**数值**恰为 `1`。 -/
theorem absPos_L_sharp_at_D_one (d : ℕ) (i : Fin d) (hD : absPosDenom d i = 1) :
    (absPosDenom d i)⁻¹ = 1 := by
  rw [hD, inv_one]

/-! ## 注：诚实边界
  · `distF` 用**显式距离**而非类型类 `dist`：`Fin n` 在 mathlib 4.14 中不保证有
    `PseudoMetricSpace` 实例，显式距离让 ALiBi 的 `Fin n` 索引可用；
  · 每个实例的每个字段都由既有具体定理填充（**不是文字描述**）；
  · 接口蕴含定理（`error_bound` / `error_bound_of_close` / `output_bound` /
    `stack_error_bound`）对任意 `PositionEncoding` **自动成立**，与具体编码无关；
  · **未做**：接口的代数化（把加性/乘性算子结构形式化）、实例间包含关系；
  · **【本轮更新 C8 + v14 修订】接口的 sharp 常数只被部分解决**（见 §四）：
    **已证**：RoPE 的 `B = 1` 取等（`rope_B_sharp`）；绝对编码的 `B = 1` 可达
    （`absPos_B_sharp`）；绝对编码 `L` 的更紧**上界** `1/D`（`absPos_smooth_sharp`）。
    ⚠ **未做 / 已撤回**（原本轮声称"RoPE 的 `L = |θ|` 也取等"，**已撤回**）：
    `rope_L_sharp`（§4.1 的旧标题曾称"`B = 1` 与 `L = |θ|` 都 sharp"，本节旧文亦曾称"都取等"）
    **只证出左端 `= 1`**
    （`|cos 0 − cos(θ·π/(2|θ|))| = 1`），**未证 `L = |θ|` 取等**——该取等命题
    **为假**（需 `π/2 = 1`，见 `rope_L_sharp` docstring）；其 `sup` 意义下的最优性
    （计划名 `rope_L_sharp_sup`）**未做**。ALiBi 的 `B`/`L` 取等
    （`alibi_B_sharp`/`alibi_L_sharp`）**未形式化**（素材在 `RealALiBi.lean:106`）；
    绝对编码的 `absPos_L_not_sharp`、以及"`1/D` 是紧常数"这一声称**均未证**：
    `absPos_L_sharp_at_D_one` 只是代数重写，**不是取等见证**。
    **未做**：把接口的 `L` 字段改成 `1/D`——`D` 依赖 `i` 而 `L` 是**常数字段**，
    改造接口会破坏「常数与分量无关」的设计；故只给逐 `i` 的更紧上界，**标注未做**。
  无 sorry/axiom/admit。 -/

end Lattice
