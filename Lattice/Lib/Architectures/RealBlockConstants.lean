import Mathlib
import Lattice.Lib.Architectures.RealBlockInstance
import Lattice.Lib.Attention.RealSoftmaxLipschitz
import Lattice.Lib.Optim.RealValueIteration
import Lattice.Lib.LinearAlgebra.RealBanach
/-!
# LATTICE: 组件常数代入块界 —— softmax 权重完整注意力的数字 Lipschitz 与端到端块闭式

VERIFICATION.md §5 展望「组件常数代入块界」的收官：
把 softmax 的输入-Lipschitz 常数（RealSoftmaxLipschitz.softmax_lipschitz_coord）
代入「权重随输入变化」的**完整注意力算子**，得到带完整数字常数的 attention
Lipschitz；再代入 transformer 块（RealBlockLipschitz.block_lipschitz_bound），
得到端到端数字闭式。

完整注意力算子：A(x) = Σᵢ softmax(Sx)ᵢ · (Vᵢ x)，softmax 权重 w(x) = softmax(Sx)
依赖输入 x（非固定权重）；S : E →L[ℝ] (Fin k → ℝ) 是**线性分数映射**
（如 S = Q·Kᵀ/√d，见 score_lin_lipschitz_qk 的算子范数实例）。

定理链（全部闭式常数，无 open 假设除诚实的数据域假设）：
  1. weight_l1_diff_bound：Σᵢ |softmax(sx)ᵢ − softmax(sy)ᵢ|
     ≤ k·(k+1)·e^{4M'}·‖sx−sy‖∞（softmax 坐标 Lipschitz 逐坐标求和，维度因子 k）；
  2. score_lin_lipschitz：线性分数映射 S 的 ∞-范数 Lipschitz：
     LinfNorm(Sx−Sy) ≤ ‖S‖·‖x−y‖（Pi 范数 = LinfNorm 桥 + le_opNorm）；
  3. score_lin_lipschitz_qk：实例 S = (1/√d)·(Kᵀ∘Q) ⟹ 界 ≤ (‖Kᵀ‖·‖Q‖/√d)·‖x−y‖；
  4. attention_lipschitz_weighted：抽象权重 w（非负、和为 1、L1-Lipschitz）
     ⟹ ‖A(x)−A(y)‖ ≤ M·(1 + B·Lw)·‖x−y‖（‖x‖ ≤ B，M = max‖Vᵢ‖）；
  5. attention_lipschitz_numeric：w = softmax∘S 实例化，Lw = k·(k+1)·e^{4·‖S‖·B}·‖S‖，
     La = M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)；
  6. transformer_block_numeric：Block = RMSNorm∘(id + Attn + FFN) 端到端
     Lf·(1 + La + Lg)：**Lf = √n/c**（紧常数，见下）、Lg = ‖W‖——纯数字常数闭式。
     **⚠ v14（Z1-5）常数收紧**：旧稿 Lf = 2√n/c（松弛 2 倍），现改为已证紧常数
     √n/c（`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`）。松弛版仍有效，
     见 `RealBlockInstance.transformer_block_closed_relaxed`。
     **⚠ v14（B53）定义域前提改为点对**：`hx : c ≤ ‖x‖`、`hy : c ≤ ‖y‖`
     （旧的 `∀ z` 与 `hc : 0 < c` 矛盾、使定理空洞）。

诚实假设（模型无关，均显式标注）：
  · 数据范数上界 B（‖z‖ ≤ B，用于分数上界 |S z ᵢ| ≤ ‖S‖·B 与 ‖Vᵢ x‖ ≤ M·B）；
  · value 投影界 M（max‖Vᵢ‖ ≤ M）；
  · 数据范数下界 c（RMSNorm 定义域 ‖z‖ ≥ c > 0）；
  · [NeZero k]（注意力指标非空，softmax 分母为正的前提）。

⚠ **定义域契约改为点对（B53 修复，v14）**：`transformer_block_numeric` 原假设
`hxdom : ∀ z, c ≤ ‖z‖` 与 `hc : 0 < c` **矛盾**（`z := 0` ⟹ `c ≤ 0`）
⟹ **前提不可满足、定理空洞**（CORRECTIONS B53）。现改为**点对假设**，
且设在 **RMSNorm 的实际输入（内层残差和）** 上：
`hx : c ≤ ‖x + SoftmaxAttnOp S V x + W x‖`、`hy : c ≤ ‖y + SoftmaxAttnOp S V y + W y‖`
——这是 `rmsNormE_sqrt_lipschitz` 本来需要的**可满足**契约
（见证：`S`/`V` 任取、`x = y = c • e₀` 且 `SoftmaxAttnOp`/`W` 取零映射时内层和 = `c • e₀`）。
数据上界 `hB` **保留全空间形式**。

⚠⚠ **更正（B357，v16）**：此处原文写「它在 `z = 0` 处给 `0 ≤ B`，**可满足**」——
**该判定是错的**。`z = 0` **只**给出**必要条件** `0 ≤ B`，而 `hB` 是**全空间全称量化**，
单点实例**不构成见证**（用单点充当全称命题的见证 = **伪见证**，false witness）。
内核级反证：取 `z = t • e₀` 令 `‖z‖ = |t|` 任意大，由 `hB` 可得 `∀ t : ℝ, |t| ≤ B`，
即 `B` 是全体实数的上界 ⟹ **`hB` 不可满足**（`[Nontrivial E]` 下直接推出 `False`）。
⭐ 这与本文件 `:44-46` 判 `hxdom` 空洞时用的是**同一条单点反驳逻辑** ——
⚠ **同一文件内判据曾自相矛盾**。`hB` 的**修正形式**（点对 / 沿链）见
`RealModelChain.lean` 中 `chainN_dom_bound` 的定义处与 P0-2 的迁移计划。

⚠ **v15 更正（B60）**：11:03 的一处修复把该点对前提设在了 **`x`** 上而非
**RMSNorm 的实际输入**上，使证明体的 `le_trans hx ?_` 需要假命题
`∀ u, ‖x‖ ≤ ‖u‖`（取 `u = 0` 反例）⟹ **填不满**（把"空洞"换成了"编译错误"）。
⇒ **教训（已登记 STYLE）**：**点对前提必须设在被引用者的实际输入上，
而不是调用者手里的那一个变量上。**

模型无关：任意范数空间 E（attention 定理）、任意线性分数 S、任意 value 投影 V、
任意线性 FFN W。
-/

noncomputable section

namespace Lattice

/-! ## 引理一：softmax 权重 L1 差界
Σᵢ |softmax(sx)ᵢ − softmax(sy)ᵢ| ≤ k·(k+1)·e^{4M'}·‖sx−sy‖∞
（sx、sy 坐标均在 [-M', M']；softmax 坐标 Lipschitz 逐坐标求和）。-/

lemma weight_l1_diff_bound {k : ℕ} [NeZero k] (M' : ℝ) (hM' : 0 ≤ M') (sx sy : Fin k → ℝ)
    (hsx : ∀ i : Fin k, -M' ≤ sx i ∧ sx i ≤ M')
    (hsy : ∀ i : Fin k, -M' ≤ sy i ∧ sy i ≤ M') :
    (∑ i : Fin k, |softmax sx i - softmax sy i|)
      ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (sx - sy) := by
  -- 逐坐标：softmax 坐标 Lipschitz（每坐标 ≤ (k+1)·e^{4M'}·Linf）
  have hper : ∀ i : Fin k, |softmax sx i - softmax sy i|
      ≤ ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (sx - sy) := by
    intro i
    simpa using (softmax_lipschitz_coord (n := k) M' sx sy hM' hsx hsy i)
  calc
    (∑ i : Fin k, |softmax sx i - softmax sy i|)
        ≤ ∑ i : Fin k, ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (sx - sy) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hper i
    _ = (k : ℝ) * (((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (sx - sy)) := by
          simp [Finset.sum_const]
    _ = (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (sx - sy) := by ring

/-! ## 引理二：线性分数映射的 ∞-范数 Lipschitz
LinfNorm(Sx − Sy) ≤ ‖S‖·‖x−y‖（LinfNorm = Pi 范数 桥 + 算子范数 le_opNorm）。-/

lemma score_lin_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (S : E →L[ℝ] (Fin k → ℝ)) :
    ∀ x y : E, LinfNorm (S x - S y) ≤ ‖S‖ * ‖x - y‖ := by
  intro x y
  calc
    LinfNorm (S x - S y) = ‖S x - S y‖ := linfNorm_eq_norm (S x - S y)
    _ = ‖S (x - y)‖ := by rw [← (S.map_sub x y)]
    _ ≤ ‖S‖ * ‖x - y‖ := S.le_opNorm (x - y)

/-! ## 引理三：QK/√d 分数实例（算子范数代数）
S = (1/√d)·(Kᵀ∘Q) ⟹ LinfNorm(Sx−Sy) ≤ (‖Kᵀ‖·‖Q‖/√d)·‖x−y‖
（comp_norm_bound 复合范数 + smul_norm_bound 缩放范数）。-/

lemma score_lin_lipschitz_qk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (Q : E →L[ℝ] E) (KS : E →L[ℝ] (Fin k → ℝ)) (d : ℝ) (hd : 0 < d) :
    ∀ x y : E,
      LinfNorm (((1 / Real.sqrt d) • (KS ∘L Q)) x - ((1 / Real.sqrt d) • (KS ∘L Q)) y)
        ≤ (‖KS‖ * ‖Q‖ / Real.sqrt d) * ‖x - y‖ := by
  intro x y
  -- ‖(1/√d)•(KS∘Q)‖ ≤ ‖KS‖·‖Q‖/√d（缩放范数 + 复合范数）
  have hnorm : ‖(1 / Real.sqrt d) • (KS ∘L Q)‖ ≤ ‖KS‖ * ‖Q‖ / Real.sqrt d := by
    have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
    have hsq1 : 0 ≤ 1 / Real.sqrt d := le_of_lt (one_div_pos.mpr hsq)
    calc
      ‖(1 / Real.sqrt d) • (KS ∘L Q)‖ = |1 / Real.sqrt d| * ‖KS ∘L Q‖ :=
        norm_smul (1 / Real.sqrt d) (KS ∘L Q)
      _ = (1 / Real.sqrt d) * ‖KS ∘L Q‖ := by rw [abs_of_nonneg hsq1]
      _ ≤ (1 / Real.sqrt d) * (‖KS‖ * ‖Q‖) := by
        exact mul_le_mul_of_nonneg_left (comp_norm_bound KS Q) hsq1
      _ = ‖KS‖ * ‖Q‖ / Real.sqrt d := by
        field_simp [ne_of_gt hsq]
  calc
    LinfNorm (((1 / Real.sqrt d) • (KS ∘L Q)) x - ((1 / Real.sqrt d) • (KS ∘L Q)) y)
        ≤ ‖(1 / Real.sqrt d) • (KS ∘L Q)‖ * ‖x - y‖ :=
          score_lin_lipschitz ((1 / Real.sqrt d) • (KS ∘L Q)) x y
    _ ≤ (‖KS‖ * ‖Q‖ / Real.sqrt d) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-! ## 引理四：完整注意力 Lipschitz（抽象权重）
权重 w(x)（非负、和为 1、L1-Lipschitz：Σᵢ|w x ᵢ − w y ᵢ| ≤ Lw·‖x−y‖）与 value
投影 V（max‖Vᵢ‖ ≤ M）、数据界 ‖x‖ ≤ B ⟹
‖A(x) − A(y)‖ ≤ M·(1 + B·Lw)·‖x−y‖（差分解：权重差项 + 权重固定凸组合项）。-/

theorem attention_lipschitz_weighted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} [NeZero k] (w : E → Fin k → ℝ) (V : Fin k → E →L[ℝ] E) (M Lw B : ℝ)
    (hw0 : ∀ x : E, ∀ i : Fin k, 0 ≤ w x i)
    (hsum : ∀ x : E, (∑ i : Fin k, w x i) = 1)
    (hwlip : ∀ x y : E, ‖x‖ ≤ B → ‖y‖ ≤ B →
      (∑ i : Fin k, |w x i - w y i|) ≤ Lw * ‖x - y‖)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (x y : E) (hBx : ‖x‖ ≤ B) (hBy : ‖y‖ ≤ B) :
    ‖(∑ i : Fin k, w x i • (V i x)) - (∑ i : Fin k, w y i • (V i y))‖
      ≤ M * (1 + B * Lw) * ‖x - y‖ := by
  -- M、B 非负（M 由 [NeZero k] 保证存在指标；B 由 ‖x‖ ≤ B 与范数非负）
  have hM0 : 0 ≤ M := by
    rcases (Fin.pos_iff_nonempty.mp (NeZero.pos k)) with ⟨i₀⟩
    linarith [hM i₀, norm_nonneg (V i₀)]
  have hB0 : 0 ≤ B := by
    linarith [hBx, norm_nonneg x]
  -- 差分解：A x − A y = Σ (w x ᵢ − w y ᵢ)•(Vᵢx) + Σ w y ᵢ•(Vᵢ(x−y))
  have hdiff : (∑ i : Fin k, w x i • (V i x)) - (∑ i : Fin k, w y i • (V i y))
      = (∑ i : Fin k, (w x i - w y i) • (V i x)) + (∑ i : Fin k, w y i • (V i (x - y))) := by
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sub_smul]
    rw [(V i).map_sub]
    rw [smul_sub]
    abel
  -- 第一项：权重差 × 输出范数 ≤ M·B·Lw·‖x−y‖
  have h1 : ‖∑ i : Fin k, (w x i - w y i) • (V i x)‖ ≤ M * B * Lw * ‖x - y‖ := by
    calc
      ‖∑ i : Fin k, (w x i - w y i) • (V i x)‖
          ≤ ∑ i : Fin k, ‖(w x i - w y i) • (V i x)‖ := norm_sum_le _ _
      _ = ∑ i : Fin k, (|w x i - w y i| * ‖V i x‖) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin k, (|w x i - w y i| * (M * ‖x‖)) := by
            apply Finset.sum_le_sum
            intro i hi
            have h : ‖V i x‖ ≤ M * ‖x‖ := by
              calc
                ‖V i x‖ ≤ ‖V i‖ * ‖x‖ := (V i).le_opNorm x
                _ ≤ M * ‖x‖ := mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ ≤ ∑ i : Fin k, (|w x i - w y i| * (M * B)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBx hM0) (abs_nonneg _)
      _ = (∑ i : Fin k, |w x i - w y i|) * (M * B) := by rw [← Finset.sum_mul]
      _ ≤ (Lw * ‖x - y‖) * (M * B) := by
            exact mul_le_mul_of_nonneg_right (hwlip x y hBx hBy) (mul_nonneg hM0 hB0)
      _ = M * B * Lw * ‖x - y‖ := by ring
  -- 第二项：权重固定（w y）的凸组合不放大 ≤ M·‖x−y‖
  have h2 : ‖∑ i : Fin k, w y i • (V i (x - y))‖ ≤ M * ‖x - y‖ := by
    have hlin : (∑ i : Fin k, w y i • (V i x)) - (∑ i : Fin k, w y i • (V i y))
        = ∑ i : Fin k, w y i • (V i (x - y)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(V i).map_sub]
      rw [smul_sub]
    have hmain := convComb_lipschitz_prob (w y) V M (hw0 y) (hsum y) hM x y
    rw [hlin] at hmain
    exact hmain
  -- 三角不等式组装
  calc
    ‖(∑ i : Fin k, w x i • (V i x)) - (∑ i : Fin k, w y i • (V i y))‖
        = ‖(∑ i : Fin k, (w x i - w y i) • (V i x)) + (∑ i : Fin k, w y i • (V i (x - y)))‖ := by rw [hdiff]
    _ ≤ ‖(∑ i : Fin k, (w x i - w y i) • (V i x))‖ + ‖(∑ i : Fin k, w y i • (V i (x - y)))‖ := norm_add_le _ _
    _ ≤ (M * B * Lw * ‖x - y‖) + M * ‖x - y‖ := add_le_add h1 h2
    _ = M * (1 + B * Lw) * ‖x - y‖ := by ring

/-! ## 定理一：完整注意力 Lipschitz（数字常数）
A(x) = Σᵢ softmax(Sx)ᵢ·(Vᵢx)（softmax 权重随输入），分数 S 线性（如 QK/√d），
数据域 ‖z‖ ≤ B（全体输入）⟹
‖A(x) − A(y)‖ ≤ La·‖x−y‖，La = M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)。
-/

theorem attention_lipschitz_numeric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} [NeZero k] (S : E →L[ℝ] (Fin k → ℝ))
    (V : Fin k → E →L[ℝ] E) (M B : ℝ)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M) :
    -- B366 (P0-2): was `(hB : ∀ z : E, ‖z‖ ≤ B)`, UNSATISFIABLE on any nontrivial
    -- space (B357 kernel-proved).  The bound is needed only at the two points the
    -- conclusion names, so it is stated pointwise inside the forall x y.
    ∀ x y : E, ‖x‖ ≤ B → ‖y‖ ≤ B →
      ‖(∑ i : Fin k, (softmax (S x)) i • (V i x)) - (∑ i : Fin k, (softmax (S y)) i • (V i y))‖
        ≤ M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖)) * ‖x - y‖ := by
  intro x y hBx hBy
  have hM0 : 0 ≤ M := by
    rcases (Fin.pos_iff_nonempty.mp (NeZero.pos k)) with ⟨i₀⟩
    linarith [hM i₀, norm_nonneg (V i₀)]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg x) hBx
  -- 分数上界 M' = ‖S‖·B（数据域 + 算子范数 ⟹ |S z ᵢ| ≤ ‖S‖·B）
  let M' : ℝ := ‖S‖ * B
  have hM' : 0 ≤ M' := by
    dsimp [M']
    exact mul_nonneg (norm_nonneg S) hB0
  -- B366: bound as a per-point parameter (template verified in B364/B365)
  have hscore : ∀ (z : E), ‖z‖ ≤ B → ∀ i : Fin k, |(S z) i| ≤ M' := by
    intro z hz i
    dsimp [M']
    calc
      |(S z) i| ≤ ‖S z‖ := by
            rw [← linfNorm_eq_norm (S z)]
            exact le_csSup (bddAbove_abs (S z)) (by exact ⟨i, rfl⟩)
      _ ≤ ‖S‖ * ‖z‖ := S.le_opNorm z
      _ ≤ ‖S‖ * B := mul_le_mul_of_nonneg_left hz (norm_nonneg S)
  -- softmax 权重 L1-Lipschitz：Lw = k·(k+1)·e^{4M'}·‖S‖（softmax 坐标 Lipschitz ∘ 分数 Lipschitz）
  have hwlip : ∀ (u v : E), ‖u‖ ≤ B → ‖v‖ ≤ B →
      (∑ i : Fin k, |softmax (S u) i - softmax (S v) i|)
      ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) * ‖u - v‖ := by
    intro u v hu hv
    have h1 := weight_l1_diff_bound (k := k) M' hM' (S u) (S v)
      (fun i => abs_le.mp (hscore u hu i)) (fun i => abs_le.mp (hscore v hv i))
    have h2 := score_lin_lipschitz S u v
    calc
      (∑ i : Fin k, |softmax (S u) i - softmax (S v) i|)
          ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (S u - S v)) := h1
      _ ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) * ‖u - v‖ := by
            have hcoef : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') := by positivity
            calc
              ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * LinfNorm (S u - S v))
                  = ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M')) * LinfNorm (S u - S v) := by ring
              _ ≤ ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M')) * (‖S‖ * ‖u - v‖) :=
                    mul_le_mul_of_nonneg_left h2 hcoef
              _ = ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) * ‖u - v‖ := by ring
  -- 抽象定理实例化（w = softmax∘S）
  have hA := attention_lipschitz_weighted (w := fun z i => softmax (S z) i) V M
    ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * M') * ‖S‖) B
    (by intro x i; exact softmax_nonneg (S x) i)
    (by intro x; exact softmax_sum_one (S x))
    hwlip hM x y hBx hBy
  simpa [M'] using hA

/-! ## 注意力算子（softmax 权重随输入） -/

def SoftmaxAttnOp {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (NeZero.pos k)
  ∑ i : Fin k, (softmax (S x)) i • (V i x)

/-! ## 定理二：transformer 块端到端数字闭式
Block = RMSNorm∘(id + Attn + FFN)（Attn = softmax 权重完整注意力），
常数 Lf·(1 + La + Lg)：**Lf = √n/c**（紧常数，见下）、
La = M·(1 + B·k·(k+1)·e^{4·‖S‖·B}·‖S‖)、
Lg = ‖W‖——块界 block_lipschitz_bound 组装（加法/残差/复合组合律）。

**⚠ 常数收紧（Z1-5，v14）**：旧稿 Lf = 2√n/c（松弛 2 倍），现改为已证的紧常数
`√n/c`（`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`）。`RMSNormOp` 与
`RealNormSharpConstant.rmsNormE` **定义相同**，故紧界可直接代入。 -/

/-- **`transformer_block_numeric`（结构线收官，定理二）**：数值 transformer 块
    `Block = RMSNorm∘(id + Attn + FFN)` 在**点对定义域假设**下的数字 Lipschitz 闭式。

    **定义域契约（B53 修复，v14）**：RMSNorm 只在 `‖z‖ ≥ c > 0` 上有 `√n/c` 界
    （`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz` 本来就是**点对**陈述），
    故这里用**点对假设**——**可满足**（见证：`e₀` 单位向量，`c • e₀` 范数为 `c`）。

    ⚠ **v15 更正（B60）**：11:03 的一处修复把点对前提设在了 **`x`** 上
    （`hx : c ≤ ‖x‖`）而非 **RMSNorm 的实际输入**上，导致证明体的
    `rmsNormE_sqrt_lipschitz u v c hc (le_trans hx ?_)` 中的 `?_` 需要
    `∀ u, ‖x‖ ≤ ‖u‖`——**这是假命题**（取 `u = 0`），故该处**填不满**、
    只是把「前提不可满足的空洞」换成了「编译错误」。
    现已把前提改到**内层残差和** `x + SoftmaxAttnOp S V x + W x` 上。
    ⇒ **教训（已登记 STYLE）**：**点对前提必须设在被引用者的实际输入上，
    而不是调用者手里的那一个变量上**。

    ⚠ **修复前**的假设是 `hxdom : ∀ z, c ≤ ‖z‖`，它与 `hc : 0 < c` **矛盾**
    （`z := 0` 给 `c ≤ 0`）⟹ 前提恒假、定理**空洞**（CORRECTIONS B53）。
    `hB : ∀ z, ‖z‖ ≤ B` 保留全空间形式。

    ⚠⚠ **更正（B357，v16）**：原文此处写「它在 `z = 0` 处给 `0 ≤ B`，**可满足**」——
    **该判定是错的**（与 `:51` 同一处错误）。`z = 0` 只给**必要条件**，不是全称命题的见证。
    内核级反证：`hB` 在 `[Nontrivial E]` 下**不可满足**（`z = t • e₀` ⟹ `∀ t, |t| ≤ B` ⟹ `False`）。
    要点 **`hB` 与上文 `hxdom` 是同一类缺陷**（不可满足前提），
    而本文件此前对二者用了**相反的判据** —— 这条不一致已登记。 -/
theorem transformer_block_numeric {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M B c : ℝ)
    (hc : 0 < c)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    -- B366 (P0-2): was `(hB : ∀ z, ‖z‖ ≤ B)`, UNSATISFIABLE on any nontrivial
    -- space (B357 kernel-proved: it forces `∀ t : ℝ, |t| ≤ B`), so every theorem
    -- carrying it was vacuous.  The proof consumes the bound only at x and y,
    -- so it is stated there -- after x and y are introduced.
    (x y : EuclideanSpace ℝ (Fin n))
    (hBx : ‖x‖ ≤ B) (hBy : ‖y‖ ≤ B)
    (hx : c ≤ ‖x + SoftmaxAttnOp S V x + W x‖)
    (hy : c ≤ ‖y + SoftmaxAttnOp S V y + W y‖) :
    ‖RMSNormOp (x + SoftmaxAttnOp S V x + W x)
      - RMSNormOp (y + SoftmaxAttnOp S V y + W y)‖
      ≤ (Real.sqrt n / c)
          * (1 + (M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖))) + ‖W‖)
          * ‖x - y‖ := by
  let La : ℝ := M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖))
  -- RMSNorm 的点对界：直接对**内层和**这两点用 rmsNormE_sqrt_lipschitz
  have hF : ‖RMSNormOp (x + SoftmaxAttnOp S V x + W x)
      - RMSNormOp (y + SoftmaxAttnOp S V y + W y)‖
      ≤ (Real.sqrt n / c)
        * ‖(x + SoftmaxAttnOp S V x + W x) - (y + SoftmaxAttnOp S V y + W y)‖ := by
    rw [RMSNormOp_eq_rmsNormE (x + SoftmaxAttnOp S V x + W x),
        RMSNormOp_eq_rmsNormE (y + SoftmaxAttnOp S V y + W y)]
    exact rmsNormE_sqrt_lipschitz _ _ c hc hx hy
  have hA : ∀ u v : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ B → ‖v‖ ≤ B →
      ‖SoftmaxAttnOp S V u - SoftmaxAttnOp S V v‖ ≤ La * ‖u - v‖ := by
    intro u v hu hv
    have h := attention_lipschitz_numeric (E := EuclideanSpace ℝ (Fin n)) S V M B hM u v hu hv
    simpa [SoftmaxAttnOp, La] using h
  have hG : ∀ x y : EuclideanSpace ℝ (Fin n), ‖W x - W y‖ ≤ ‖W‖ * ‖x - y‖ := by
    intro x y
    exact linear_map_lipschitz W x y
  have hLf : 0 ≤ Real.sqrt n / c := by positivity
  -- 内层和 (1 + La + ‖W‖)-Lipschitz（加法/残差组合律，逐点）
  have hid : ∀ x y : EuclideanSpace ℝ (Fin n), ‖x - y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
    intro x y; simp
  have hin : ‖(x + SoftmaxAttnOp S V x + W x) - (y + SoftmaxAttnOp S V y + W y)‖
      ≤ (1 + La + ‖W‖) * ‖x - y‖ := by
    -- B366: `lipschitz_add` requires UNCONDITIONAL `forall x y` hypotheses, which
    -- would need a global bound -- the unsatisfiable hB.  Since only this pair is
    -- needed, the triangle inequality is applied directly here instead.
    have h1 : ‖(x + SoftmaxAttnOp S V x) - (y + SoftmaxAttnOp S V y)‖
        ≤ (1 + La) * ‖x - y‖ := by
      calc
        ‖(x + SoftmaxAttnOp S V x) - (y + SoftmaxAttnOp S V y)‖
            = ‖(x - y) + (SoftmaxAttnOp S V x - SoftmaxAttnOp S V y)‖ := by abel
        _ ≤ ‖x - y‖ + ‖SoftmaxAttnOp S V x - SoftmaxAttnOp S V y‖ := norm_add_le _ _
        _ ≤ ‖x - y‖ + La * ‖x - y‖ := by
              exact add_le_add_left (hA x y hBx hBy) _
        _ = (1 + La) * ‖x - y‖ := by ring
    calc
      ‖(x + SoftmaxAttnOp S V x + W x) - (y + SoftmaxAttnOp S V y + W y)‖
          = ‖((x + SoftmaxAttnOp S V x) + W x) - ((y + SoftmaxAttnOp S V y) + W y)‖ := by
            abel
      _ = ‖((x + SoftmaxAttnOp S V x) - (y + SoftmaxAttnOp S V y)) + (W x - W y)‖ := by
            abel
      _ ≤ ‖(x + SoftmaxAttnOp S V x) - (y + SoftmaxAttnOp S V y)‖ + ‖W x - W y‖ :=
            norm_add_le _ _
      _ ≤ (1 + La) * ‖x - y‖ + ‖W‖ * ‖x - y‖ := by
            exact add_le_add h1 (linear_map_lipschitz W x y)
      _ = (1 + La + ‖W‖) * ‖x - y‖ := by ring
  calc
    ‖RMSNormOp (x + SoftmaxAttnOp S V x + W x)
        - RMSNormOp (y + SoftmaxAttnOp S V y + W y)‖
        ≤ (Real.sqrt n / c)
          * ‖(x + SoftmaxAttnOp S V x + W x) - (y + SoftmaxAttnOp S V y + W y)‖ := hF
    _ ≤ (Real.sqrt n / c) * ((1 + La + ‖W‖) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left hin hLf
    _ = (Real.sqrt n / c)
          * (1 + (M * (1 + B * ((k : ℝ) * ((k : ℝ) + 1) * Real.exp (4 * (‖S‖ * B)) * ‖S‖))) + ‖W‖)
          * ‖x - y‖ := by
          -- `La` 是 let 绑定的局部定义：`simp only` 不展开它，用 `dsimp only`（定义等价）
          dsimp only [La]
          ring

/-! ## 注：端到端收官
  单块闭式 L_block = (√n/c)·(1 + La + ‖W‖)（本定理，**紧常数** √n/c；
  松弛版 `2√n/c` 见 `RealBlockInstance.transformer_block_closed_relaxed`，
  由 `RealNormLipschitz.rmsNorm_lipschitz` 提供，仍是有效上界）
  ⟹ n 块链端到端误差 ≤ (L_block)ⁿ·‖Δx‖（chainN_identical_blocks_bound，
  RealBlockLipschitz 定理五）——「组件常数代入块界」（VERIFICATION §5 展望）完成：
  softmax 输入-Lipschitz（RealSoftmaxLipschitz）⟹ 完整注意力常数（本文件定理一）
  ⟹ 块端到端闭式（本文件定理二）；全部常数显式：维度因子 n/k、exp 上界 e^{4‖S‖B}、
  算子范数 ‖S‖/‖W‖、value 界 M、数据域 B、规范化 √n/c。唯一场景假设：数据范数
  上下界（B 有界域、c 非退化）。**注（B53 修复，v14；B60 更正，v15）**：本文件定理二
  的定义域前提是**点对**的、且设在 **RMSNorm 的实际输入（内层残差和）**上：
  `hx : c ≤ ‖x + SoftmaxAttnOp S V x + W x‖`（**不是**全空间 `∀ z, c ≤ ‖z‖`
  ——那与 `hc : 0 < c` 矛盾、使定理空洞；**也不是** `c ≤ ‖x‖`
  ——位置错，会使下游 `le_trans` 需要假命题 `∀ u, ‖x‖ ≤ ‖u‖`）。 -/
end Lattice
