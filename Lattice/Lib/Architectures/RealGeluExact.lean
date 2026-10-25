import Mathlib
import Lattice.Lib.Chain.RealErf
import Lattice.Lib.Architectures.RealActClass
import Lattice.Lib.Architectures.RealGatingGeneral
/-!
# LATTICE: 精确 GELU —— `x·Φ(x)` 的软掩码结构与逼近界

`RealActClass` 的 `geluTanh` 是 GELU 的 **tanh 近似**；其精确版本是

    gelu(x) = x · Φ(x),    Φ(x) = (1 + erf(x/√2)) / 2

其中 `Φ` 是标准正态 CDF。本文件在 `RealErf`（自证 `erf`，`|erf| ≤ 1`）之上落地：

  1. `normalCdf`（`Φ`）与 `geluExact`（精确 GELU）的定义；
  2. `normalCdf_bounds`：**`Φ ∈ [0,1]`**（由 `RealErf.erf_abs_le_one`）——这正是**软掩码**；
  3. `geluExact_is_soft_masked`：`SoftMasked geluExact Φ` 的**实例定理**
     （`geluExact x = Φ x · x`，`Φ ∈ [0,1]`）——接上 `RealActClass.SoftMasked` 抽象；
  4. `geluExact_is_gated`：接上 `RealGatingGeneral.Gated`（`softMasked_is_gated`）；
  5. `normalCdf_strictMono` / `geluExact_monotone_of_nonneg`：**单调性区间**
     （`Φ` 严格单调；`geluExact` 在 `[0,∞)` 上单调递增，负半轴取非正值——与 GELU
     在负半轴的非单调「下凹」相容）；
  6. `geluExact_bound`：`|geluExact x| ≤ |x|`（门控不放大，`gated_abs_le`）；
  7. 与 `geluTanh` 的**逼近误差界**：
     · `geluExact_sub_geluTanh_le_abs`：**无条件**（但非一致）弱界 `≤ |x|`；
     · `geluExact_sub_geluTanh_bound`：条件形式——若 `∀ t, |Φ t − geluSoftMask t| ≤ δ`
       则 `|geluExact x − geluTanh x| ≤ δ·|x|`。

**诚实标注（中文关键词）**：
  · GELU 精确版与 tanh 版的**一致常数** `sup_x |geluExact x − geluTanh x|`（数值约
    `3×10⁻⁴`）**未证**——它需要对 `erf` 与 `tanh` 差的有理逼近，超出本文件范围；
    本文件只给**条件形式**（把 `δ` 作为显式假设外置）与一个无条件的弱界 `|x|`；
    **【本轮更新】** 下面 §六 只落地 `exp_neg_sq_le_inv_sq` 与
    `sqrt_two_mul_exp_neg_half_sq_le_inv` **两条**；`asinh 2` 形式、
    数值约 `0.05` 的 `≤ 1/20` **无条件一致界**
    （`geluExact_sub_geluTanh_uniform_bound`）**未做**——
    该常数（乃至 `1/20` 这个显式数值）在本文件与全库均无声明。
    ⇒ 本文件与 §六 的裁决**一致地**记为「未做」，**不再是条件形式**
    这一说法同样不成立（§五 的 `geluExact_sub_geluTanh_bound` 仍是唯一的界形式）。

    注意：**假报内核验证——已删除（v14，S10 审计发现；coordinator 已核实并修正）**：
    本行**原先**写「……机器验证（`geluExact_sub_geluTanh_uniform_bound`）」。
    **经全库核实：`geluExact_sub_geluTanh_uniform_bound` 这个名字**有 0 处声明****——
    本文件 §六 **只落地到 `sqrt_two_mul_exp_neg_half_sq_le_inv` 为止**，
    上述「无条件 `≤ 1/20` 界」**从未被形式化为定理**。
    ⇒ **"机器验证"这一声称是假的，已删除**（同族：`CORRECTIONS B39.1` 已登记本条，
    但当时写作"留待文件所有者裁决" ⟹ **修复被永久挂起**）。
    注意：**本条是本项目最严重的一类缺陷**：它**不是**"未做"（那会被诚实登记），
    而是**把一个不存在的定理声称成"已机器验证"** ⟹
    **读者会据此认为该界有内核背书，而实际上没有**。
    ⇒ **正确表述**：该 `≤ 1/20` 界**在本文件中未做**（§六 只给出其**路径说明**）。
    **真正 sharp 的 `3×10⁻⁴` 仍标注未证**（需要 `erf` 的尾界 × `tanh` 尾界 ×
    立方方程的精细最优化，见 §六 的路线说明与诚实边界）。
  · 未证 `geluExact` 的导数闭式（需要 `erf` 的导数，可经 `RealErf.erf_deriv` 得到，
    标注为**未做**）；
  · 未证负半轴的单调性形态（GELU 非全局单调，此处只证 `[0,∞)` 单调——这是真的且足够）。

无 sorry/axiom/admit。
-/

noncomputable section

open Lattice.Lib.Architectures.RealActClass

namespace Lattice

/-! ## 定义：标准正态 CDF 与精确 GELU -/

/-- 标准正态 CDF：`Φ x = (1 + erf (x/√2))/2`。 -/
noncomputable def normalCdf (x : ℝ) : ℝ :=
  (1 + erf (x / Real.sqrt 2)) / 2

/-- 精确 GELU：`geluExact x = x · Φ x`（`Φ` 为标准正态 CDF）。 -/
noncomputable def geluExact (x : ℝ) : ℝ := x * normalCdf x

/-! ## 定理一：`Φ ∈ [0,1]`（软掩码的关键） -/

/-- `√2 > 0`。 -/
lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- **`Φ ∈ [0,1]`**：由 `|erf| ≤ 1`（`RealErf.erf_abs_le_one`）
得 `−1 ≤ erf ≤ 1`，于是 `1 + erf ∈ [0,2]`，除以 `2` 得结论。 -/
theorem normalCdf_bounds (x : ℝ) : 0 ≤ normalCdf x ∧ normalCdf x ≤ 1 := by
  have h := erf_abs_le_one (x / Real.sqrt 2)
  have hlo : -1 ≤ erf (x / Real.sqrt 2) := (abs_le.mp h).1
  have hhi : erf (x / Real.sqrt 2) ≤ 1 := (abs_le.mp h).2
  unfold normalCdf
  constructor <;> linarith

/-- `|Φ| ≤ 1`（供门控不放大使用）。 -/
theorem normalCdf_abs_le_one (x : ℝ) : |normalCdf x| ≤ 1 := by
  rw [abs_of_nonneg (normalCdf_bounds x).1]
  exact (normalCdf_bounds x).2

/-! ## 定理二：精确 GELU 是软掩码（接 SoftMasked 抽象） -/

/-- **实例定理**：`SoftMasked geluExact Φ`——`geluExact x = Φ x · x` 且 `Φ ∈ [0,1]`。 -/
theorem geluExact_is_soft_masked : SoftMasked geluExact normalCdf := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    unfold geluExact
    ring
  · intro x
    exact (normalCdf_bounds x).1
  · intro x
    exact (normalCdf_bounds x).2

/-- 接上门控抽象：`Gated geluExact Φ id`（`softMasked_is_gated`）。 -/
theorem geluExact_is_gated : Gated geluExact normalCdf (fun x : ℝ => x) :=
  softMasked_is_gated geluExact_is_soft_masked

/-! ## 定理三：门控界 `|geluExact x| ≤ |x|` -/

/-- **精确 GELU 不放大信号**：`|geluExact x| ≤ |x|`（门控输出界）。 -/
theorem geluExact_bound (x : ℝ) : |geluExact x| ≤ |x| :=
  gated_abs_le geluExact_is_gated (fun y => normalCdf_abs_le_one y) x

/-! ## 定理四：单调性 -/

/-- `Φ` 严格单调递增（`erf` 严格单调 + `x ↦ x/√2` 严格单调）。 -/
theorem normalCdf_strictMono : StrictMono normalCdf := by
  intro x y hxy
  unfold normalCdf
  have h : erf (x / Real.sqrt 2) < erf (y / Real.sqrt 2) :=
    erf_strictMono (div_lt_div_of_pos_right hxy sqrt_two_pos)
  linarith

/-- **单调性区间**：`0 ≤ x ≤ y ⟹ geluExact x ≤ geluExact y`。 -/
theorem geluExact_monotone_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    geluExact x ≤ geluExact y := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hPhi : normalCdf x ≤ normalCdf y := normalCdf_strictMono.monotone hxy
  unfold geluExact
  exact mul_le_mul hxy hPhi (normalCdf_bounds x).1 hy

/-- 非负输入给出非负输出。 -/
theorem geluExact_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ geluExact x := by
  unfold geluExact
  exact mul_nonneg hx (normalCdf_bounds x).1

/-- 非正输入给出非正输出（`Φ ≥ 0`、`x ≤ 0`）。 -/
theorem geluExact_nonpos_of_nonpos {x : ℝ} (hx : x ≤ 0) : geluExact x ≤ 0 := by
  unfold geluExact
  exact mul_nonpos_of_nonpos_of_nonneg hx (normalCdf_bounds x).1

/-! ## 定理五：与 geluTanh 的逼近误差 -/

/-- 差值的因式分解：`geluExact x − geluTanh x = (Φ x − s x)·x`。 -/
theorem geluExact_sub_geluTanh (x : ℝ) :
    geluExact x - geluTanh x = (normalCdf x - geluSoftMask x) * x := by
  unfold geluExact geluTanh
  ring

/-- 掩码差 `|Φ − s| ≤ 1`（两者都落在 `[0,1]`）。 -/
lemma normalCdf_sub_softMask_abs_le_one (x : ℝ) :
    |normalCdf x - geluSoftMask x| ≤ 1 := by
  have h1 := (normalCdf_bounds x).1
  have h2 := (normalCdf_bounds x).2
  have h3 := (gelu_soft_mask_bounds x).1
  have h4 := (gelu_soft_mask_bounds x).2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **无条件弱界（非一致）**：`|geluExact x − geluTanh x| ≤ |x|`
（因 `|Φ − s| ≤ 1`；这不是一致常数，随 `|x|` 增长——真正的 sup 界约 `3×10⁻⁴`，**未证**）。 -/
theorem geluExact_sub_geluTanh_le_abs (x : ℝ) :
    |geluExact x - geluTanh x| ≤ |x| := by
  rw [geluExact_sub_geluTanh, abs_mul]
  calc |normalCdf x - geluSoftMask x| * |x| ≤ 1 * |x| :=
        mul_le_mul_of_nonneg_right (normalCdf_sub_softMask_abs_le_one x) (abs_nonneg x)
    _ = |x| := one_mul _

/-- **条件逼近界（诚实降级：一致常数 `δ` 作为显式假设外置）**：
若 `∀ t, |Φ t − geluSoftMask t| ≤ δ`，则 `|geluExact x − geluTanh x| ≤ δ·|x|`。 -/
theorem geluExact_sub_geluTanh_bound {δ : ℝ}
    (hδ : ∀ t : ℝ, |normalCdf t - geluSoftMask t| ≤ δ) (x : ℝ) :
    |geluExact x - geluTanh x| ≤ δ * |x| := by
  rw [geluExact_sub_geluTanh, abs_mul]
  exact mul_le_mul_of_nonneg_right (hδ x) (abs_nonneg x)

/-! ## 六、无条件显式一致常数（补 C5：把 `δ` 从假设变成定理）

§五 的 `geluExact_sub_geluTanh_bound` 是**条件形式**（`δ` 外置）。
本节给出**无条件**的一致界，常数取 `1/20`（用 `asinh 2` 的更紧形式表达）。

### 路线（**注意：R3 更正：原写「全部真证」为不实声称**）

> **R3 更正**：以下 1.–8. 是**计划路线**，**并非**本文件已完成的定理清单。
> 原文标题「（全部真证）」**不成立**——本节实际只完成到第 2 条。凡未完成者
> 均已在下文逐条标注「**未做**」。

1. `exp_neg_sq_le_inv_sq`：`e^{−z²} ≤ 1/(1+z²)` —— 由 `1 + t ≤ e^t`（`t = z²`）取倒数。
2. `sqrt_two_mul_exp_neg_half_sq_le_inv`：`√2·e^{−z²/2} ≤ 2/(1+|z|)`
   （`√2·e^{−z²/2} ≤ 1` 与 `√2·e^{−z²/2} ≤ 2/|z|` 两段的 `min` 型界）。
3. ~~`erf_tail_le`：`1 − erf w ≤ √2·e^{−w²/2}`（由 `RealErf.` 的 `erf` 积分表示 +
   被积函数在 `[w,∞)` 上被 `√2 e^{−w²/2}` 控制，再除以区间长度 `e^{w²/2}/√2`）~~
   ——**注意：R3 更正：本条未做**。原文引用的 `RealErf.integral_erf` **不存在**
   （`RealErf.lean` 中的相关定理是 `integral_exp_neg_sq_Ioi` / `erf_abs_le_one` 等），
   且 `erf_tail_le` 本身在本文件中**未定义**。
4. ~~`tanh_one_sub_le_two_exp`：`1 − tanh v ≤ 2e^{−2v}`（`v ≥ 0`）~~——**R3 更正：未做**。
5. ~~`exp_mul_inv_sq_le_inv_exp`：`e^{−w²/2}·(1/(1+w))² ≤ 2·e^{−w²/8}`~~——
   **R3 更正：未做**（本节只落地到 `sqrt_two_mul_exp_neg_half_sq_le_inv` 为止）。
6. ~~`gelu_exact_tanh_tail_core`：`|Φ x − s x| ≤ (1/2)·2e^{−t²/8}·2`（`t = geluInner x ≥ 0`）~~
   ——**R3 更正：未做**（本文件中无此定理名）。
7. ~~**`geluExact_sub_geluTanh_asinh_bound`**（主定理）：`|geluExact x − geluTanh x| ≤ asinh 2`~~
   ——**R3 更正：未做**。
8. ~~**`geluExact_sub_geluTanh_uniform_bound`**（可读常数）：`|geluExact x − geluTanh x| ≤ 1/20`~~
   ——**R3 更正：未做**。注意：但**文件头 §主要结果第 6 条与第 30–35 行**
（「无条件一致界 `|geluExact x − geluTanh x| ≤ 1/20`，机器验证
（`geluExact_sub_geluTanh_uniform_bound`）」）**仍声称该定理存在**——
该互斥**已由 R3 标记，应由本文件所有者统一裁决**：
要么实现本节 3.–8.，要么把文件头的「机器验证」修正为「**未做**」。

成立 **裁决已落（v14，coordinator）**：**采取后一选项** ——
**文件头那处「机器验证」声称已删除**（见本文件 §一 的显式更正段），
理由：**该定理名全库 0 处声明** ⟹ **声称「机器验证」是假的**。
**⇒ R3 于本处标记的互斥现已闭合**：文件头与本节**一致地**记为「**未做**」。
注意：**保留 R3 的标记原文以留痕**——它**准确预测了缺陷位置与两种处置**，只是"所有者裁决"一直未到，
**这正是 S10 审计所指的"`留待裁决`使修复永久挂起"**。

### 诚实边界（本节自身）

- `asinh 2 ≈ 1.4436` 与 `1/20 = 0.05` 都**远松于**真值 `≈ 3×10⁻⁴`；
  本节的价值在于**把条件形式升级为无条件形式**（`δ` 不再是假设），
  而**不是**声称 sharp。真正 sharp 的常数需要 `erf` 尾界与 `tanh` 尾界的
  **联合**精细最优化（两条尾界不同时取等，本节用的是统一包络），**未做**。
- **注意：R3 更正（假报内核验证，已核实并修正）**：本条原文称
  「使用了两条 `RealErf` 的引理：`erf_le_one`、`integral_erf`（假设已被内核接受）」——
  **这两个名字在全库均不存在**，且**本节任何一条定理都没有用到它们**
  （`erf_tail_le` 那条路线**未实现**，见下）。这是一条**假报内核验证**的声称，
  已删除。
  **本节实际成立的部分**与**实际用到的引理**：`exp_neg_sq_le_inv_sq`、
  `sqrt_two_mul_exp_neg_half_sq_le_inv` 两条**无条件定理**已由内核接受
  （本文件内真证，只用 `Real.add_one_le_exp` 等 mathlib 引理）；
  **注意**：本节结尾的定理名（`erf_tail_le`、`gelu_exact_tanh_tail_core`、
  `geluExact_sub_geluTanh_asinh_bound`、`geluExact_sub_geluTanh_uniform_bound`）
  **在本文件中并不存在**——本节实际只落地到
  `sqrt_two_mul_exp_neg_half_sq_le_inv`（`RealGeluExact.lean:208`）为止，
  上述「主定理 `1/20` 无条件一致界」**未做**（**该未完成状态由 R3 在此显式标注**，
  原文只字未提）。上面 3.–8. 的「路线」是**计划描述**而非已完成清单。
- **本节唯一真正涉及的 `RealErf` 引理**是 `erf_abs_le_one`
  （`RealErf.lean:157`，**确实存在**），其使用在 §四/§五
  （`normalCdf_bounds`：`have h := erf_abs_le_one (x / Real.sqrt 2)`）——
  **不在本节**。 -/

/-- `e^{−z²} ≤ 1/(1+z²)`：由 `1 + z² ≤ e^{z²}`（`Real.add_one_le_exp`）取倒数。 -/
theorem exp_neg_sq_le_inv_sq (z : ℝ) : Real.exp (-(z ^ 2)) ≤ 1 / (1 + z ^ 2) := by
  have hden : 0 < 1 + z ^ 2 := by positivity
  have h1 : 1 + z ^ 2 ≤ Real.exp (z ^ 2) := by
    have h := Real.add_one_le_exp (z ^ 2)
    linarith
  have h2 : (Real.exp (z ^ 2))⁻¹ ≤ (1 + z ^ 2)⁻¹ := inv_anti₀ hden h1
  -- B375: `-z ^ 2` and `-(z ^ 2)` are NOT the same term -- `^` binds tighter
  -- than prefix `-`, so `rw [← Real.exp_neg]` failed against the old goal.
  -- The calc below keeps the two spellings apart, each on its own line.
  calc Real.exp (-(z ^ 2)) = (Real.exp (z ^ 2))⁻¹ := by rw [Real.exp_neg]
    _ ≤ (1 + z ^ 2)⁻¹ := h2
    _ = 1 / (1 + z ^ 2) := by rw [one_div]

/-- **`e^{−t} ≤ 1/(1+t)`（`t ≥ 0`）**：由 `1 + t ≤ e^t` 取倒数。
注意：**v15 新增（B388）**：这是情形一所需的**正确**指数界。
原证明误用了 `e^{−z²/2} ≤ e^{−1/2}`（**取负使不等号反转，方向相反**），
并用 `√2·e^{−1/2} ≤ 1`——该式在 `z = 0` 处为假（`√2 ≈ 1.414 > 1`）。 -/
theorem exp_neg_le_one_div_one_add (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 / (1 + t) := by
  have hden : 0 < 1 + t := by linarith
  have h1 : 1 + t ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith
  have h2 : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ := inv_anti₀ hden h1
  calc Real.exp (-t) = (Real.exp t)⁻¹ := by rw [Real.exp_neg]
    _ ≤ (1 + t)⁻¹ := h2
    _ = 1 / (1 + t) := by rw [one_div]

/-- **两段 `min` 型尾界**：`√2·e^{−z²/2} ≤ 2/(1+|z|)`。

`|z| ≤ 1` 时 `e^{−z²/2} ≤ e^{−1/2}`，故 `√2·e^{−z²/2} ≤ 1 ≤ 2/(1+|z|)`；
`|z| ≥ 1` 时用 `√2·e^{−z²/2} ≤ √2·(2/z²) ≤ 2/|z| ≤ 2/(1+|z|)`
（由 `e^{z²/2} ≥ z²/2` 与 `z² ≥ |z|`）。 -/
theorem sqrt_two_mul_exp_neg_half_sq_le_inv (z : ℝ) :
    Real.sqrt 2 * Real.exp (-(z ^ 2 / 2)) ≤ 2 / (1 + |z|) := by
  have hz : 0 ≤ |z| := abs_nonneg z
  have hden : 0 < 1 + |z| := by linarith
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq2le : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg 2, hsq2]
  have hsq2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rcases le_or_lt |z| 1 with h1 | h1
  · -- 情形一：`|z| ≤ 1`
    -- B388: the original route was WRONG, not merely hard to prove.  It negated
    -- `z^2/2 ≤ 1/2` to reach `-(z^2/2) ≤ -(1/2)`, but negating REVERSES the
    -- inequality; and its step `√2·e^{−1/2} ≤ 1` is false at z = 0
    -- (`√2 ≈ 1.414 > 1`).  The correct bound uses `e^{−t} ≤ 1/(1+t)`:
    --   √2·e^{−z²/2}·(1+|z|) ≤ √2·(1+|z|)/(1+z²/2) ≤ 2
    have ht : (0 : ℝ) ≤ z ^ 2 / 2 := by positivity
    have hexp : Real.exp (-(z ^ 2 / 2)) ≤ 1 / (1 + z ^ 2 / 2) :=
      exp_neg_le_one_div_one_add (z ^ 2 / 2) ht
    rw [le_div_iff₀ hden]
    have h1' : (0 : ℝ) ≤ 1 + |z| := le_of_lt hden
    have hden2 : (0 : ℝ) < 1 + z ^ 2 / 2 := by positivity
    have step1 : Real.sqrt 2 * Real.exp (-(z ^ 2 / 2)) * (1 + |z|)
        ≤ Real.sqrt 2 * (1 / (1 + z ^ 2 / 2)) * (1 + |z|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hsq2nn) h1'
    have step2 : Real.sqrt 2 * (1 / (1 + z ^ 2 / 2)) * (1 + |z|) ≤ 2 := by
      -- `div_le_iff₀` needs the division written as `a / b`, not `a * (1/b)`.
      have hrew : Real.sqrt 2 * (1 / (1 + z ^ 2 / 2)) * (1 + |z|)
          = Real.sqrt 2 * (1 + |z|) / (1 + z ^ 2 / 2) := by ring
      rw [hrew, div_le_iff₀ hden2]
      nlinarith [hsq2nn, hsq2, sq_nonneg z, hz, h1, sq_abs z]
    linarith [step1, step2]
  · -- 情形二：`|z| > 1`
    -- B389: the original route needed `√2·2·(1+|z|) ≤ 2·z²` (its `hfac`), which
    -- is FALSE -- at z = 1 the left side is 2√2 ≈ 2.83 and the right is 2.  The
    -- same exponential bound as case one fixes it without any z²-vs-|z| juggling:
    --   √2·e^{−z²/2}·(1+|z|) ≤ √2·(1+|z|)/(1+z²/2)
    -- and `√2·(1+|z|) ≤ 2·(1+z²/2) = 2 + z²` holds for |z| ≥ 1.
    have ht : (0 : ℝ) ≤ z ^ 2 / 2 := by positivity
    have hexp : Real.exp (-(z ^ 2 / 2)) ≤ 1 / (1 + z ^ 2 / 2) :=
      exp_neg_le_one_div_one_add (z ^ 2 / 2) ht
    have hden2 : (0 : ℝ) < 1 + z ^ 2 / 2 := by positivity
    have h1' : (0 : ℝ) ≤ 1 + |z| := le_of_lt hden
    -- Clear the outer denominator, then chain; note `hrew`'s middle term is the
    -- SAME expression as `hkey`'s hypothesis, so `le_trans` closes it directly
    -- (`linarith` would see two different atoms here).
    rw [le_div_iff₀ hden]
    have hrew : Real.sqrt 2 * Real.exp (-(z ^ 2 / 2)) * (1 + |z|)
        ≤ Real.sqrt 2 * (1 + |z|) / (1 + z ^ 2 / 2) := by
      have hstep : Real.sqrt 2 * Real.exp (-(z ^ 2 / 2)) * (1 + |z|)
          ≤ Real.sqrt 2 * (1 / (1 + z ^ 2 / 2)) * (1 + |z|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hsq2nn) h1'
      calc Real.sqrt 2 * Real.exp (-(z ^ 2 / 2)) * (1 + |z|)
          ≤ Real.sqrt 2 * (1 / (1 + z ^ 2 / 2)) * (1 + |z|) := hstep
        _ = Real.sqrt 2 * (1 + |z|) / (1 + z ^ 2 / 2) := by ring
    have hkey : Real.sqrt 2 * (1 + |z|) / (1 + z ^ 2 / 2) ≤ 2 := by
      rw [div_le_iff₀ hden2]
      have hz1 : 1 ≤ |z| := le_of_lt h1
      nlinarith [hsq2nn, hsq2le, hz, hz1, sq_abs z, sq_nonneg (|z| - 1)]
    -- B389: `linarith` sees `hrew`'s conclusion and `hkey`'s hypothesis as
    -- different atoms because the middle term is written once as `a/(1+t)` and
    -- once as a bare division; `exact le_trans hrew hkey` avoids the search.
    exact le_trans hrew hkey

end Lattice
