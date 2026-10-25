import Lattice.Lib.Architectures.RealNormLipschitz
import Lattice.Lib.Architectures.RealRMSNormSharpness
import Lattice.Lib.Attention.RealAttentionLipschitz
import Lattice.Lib.Architectures.RealOperatorNorm
import Lattice.Lib.Architectures.RealBlockLipschitz
import Mathlib

/-!
# LATTICE: 端到端块闭式 —— transformer 块的完整 Lipschitz 组装

把全部组件 Lipschitz 常数组装成**完整 transformer 块的端到端闭式**：

    Block(x) = RMSNorm(x + Attn(x) + FFN(x))

    Lipschitz ≤ (√n/c)·(1 + M + ‖W‖)

组件常数（各文件已证）：
  · 规范化 Lf = **√n/c**（`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`，**紧常数**；
    旧稿曾用松弛版 2√n/c，来自 `RealNormLipschitz.rmsNorm_lipschitz`。
    注意 `RMSNormOp` 与 `RealNormSharpConstant.rmsNormE` **定义相同**，
    故紧界可直接代入）；
  · 注意力 La = M（RealAttentionLipschitz.convComb_lipschitz_prob，
    凸组合权重固定版；配合 softmax 输入-Lipschitz 得完整 La）；
  · FFN 线性 Lg = ‖W‖（RealOperatorNorm.linear_map_lipschitz）。

组装 = block_lipschitz_bound（加法/残差/复合的组合律）。

**⚠ 常数收紧登记（Z1-5，v14）**：本文件原用 Lf = 2√n/c（松弛 2 倍），
现改用**已证的紧常数 √n/c**。`2√n/c` 仍是有效上界（`RealNormLipschitz` 保留），
但**不是紧的**——`RealRMSNormSharpness.rmsNormE_constant_iff` 证明真正常数恰为 `√n/c`。
**注意**：本文件是 `transformer_block_closed` 的定义处；收紧后下游
（`RealBlockConstants.transformer_block_numeric` 及其 `simpa` 读出链）
**同步收紧**，见各文件标注。

完整模型端到端实例化：n 块链误差 ≤ (L_block)ⁿ（chainN_identical_blocks_bound），
L_block = 上式——「完整模型前向链」从骨架到闭式的收官。

**⚠ v14（B53）定义域前提（本文件）**：两条块定理的 RMSNorm 定义域前提是
**点对**的、且设在 **RMSNorm 的实际输入（内层残差和）** 上：
`hx : c ≤ ‖x + ConvCombOp w V x + W x‖`、`hy : c ≤ ‖y + ConvCombOp w V y + W y‖`。
- **可满足性见证**：`w` 任取行随机、`V := 0`、`W := 0`、`x = y = c • e₀`
  ⟹ 内层和 = `c • e₀`，`‖·‖ = c` 成立。
- **⚠ v15 更正（B60）**：11:03 的一处修复把该前提设在 **`x`** 上
  （`hx : c ≤ ‖x‖`），而 RMSNorm 作用在内层和上 ⟹ 证明体的
  `le_trans hx ?_` 需要假命题 `∀ u, ‖x‖ ≤ ‖u‖`（`u = 0` 即反例）⟹ **填不满**。
  ⇒ **教训**：**点对前提必须设在被引用者的实际输入上，而不是调用者手里的变量上。**
- 旧稿 `hxdom : ∀ z, c ≤ ‖z‖` 与 `hc : 0 < c` 矛盾（`z := 0` ⟹ `c ≤ 0`）
  ⟹ **前提不可满足、定理空洞**（CORRECTIONS B53）。

模型无关：任意注意力投影 V（max‖Vᵢ‖ ≤ M）、任意线性 FFN、
任意点对定义域（c = RMSNorm 输入范数下界，唯一场景假设）。
-/

noncomputable section

namespace Lattice

/-! ## RMSNorm 算子（块组件） -/

def RMSNormOp {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt n) • ((1 / ‖z‖) • z)

/-! ## 凸组合注意力算子（块组件） -/

def ConvCombOp {n k : ℕ} (w : Fin k → ℝ) (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin k, w i • (V i x)

/-- **`RMSNormOp` 与 `RealNormSharpConstant.rmsNormE` 定义相同**（都是
`√n • ((1/‖z‖) • z)`）——故 `RealRMSNormSharpness` 的紧界可直接代入本文件。 -/
lemma RMSNormOp_eq_rmsNormE {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) :
    RMSNormOp z = rmsNormE z := rfl

/-! ## 定理：完整 transformer 块端到端闭式
Block = RMSNorm ∘ (id + Attn + FFN) 是 (√n/c)·(1 + M + ‖W‖)-Lipschitz。
（Z1-5：Lf 由松弛版 2√n/c 收紧为**已证的紧常数** √n/c。）

**⚠ v14（B53）定义域前提改为点对**：RMSNorm 只在 `‖z‖ ≥ c > 0` 上有 `√n/c` 界
（`RealRMSNormSharpness.rmsNormE_sqrt_lipschitz` 本来就是点对陈述），故用
`hx : c ≤ ‖x + ConvCombOp w V x + W x‖`、`hy : c ≤ ‖y + ConvCombOp w V y + W y‖`。
**可满足**（见证：零注意力 + 零 FFN + `x = y = c • e₀`，内层和即 `c • e₀`）。
旧的 `hxdom : ∀ z, c ≤ ‖z‖` 与 `hc : 0 < c` 矛盾（`z := 0` ⟹ `c ≤ 0`）
⟹ 前提恒假、定理空洞（CORRECTIONS B53）。

⚠ **v15 更正（B60）**：11:03 的修复把前提设在了 **`x`** 上而非 **RMSNorm 的实际
输入**（内层和）上，使证明体的 `le_trans hx ?_` 需要假命题 `∀ u, ‖x‖ ≤ ‖u‖`
（取 `u = 0` 反例）⟹ **填不满**。现已改正到内层和。 -/

theorem transformer_block_closed {n k : ℕ} [NeZero n] (w : Fin k → ℝ)
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (M c : ℝ)
    (hc : 0 < c) (hw : ∀ i : Fin k, 0 ≤ w i) (hsum : (∑ i : Fin k, w i) = 1)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : c ≤ ‖x + ConvCombOp w V x + W x‖)
    (hy : c ≤ ‖y + ConvCombOp w V y + W y‖) :
    ‖RMSNormOp (x + ConvCombOp w V x + W x)
      - RMSNormOp (y + ConvCombOp w V y + W y)‖
      ≤ ((Real.sqrt n / c) * (1 + M + ‖W‖)) * ‖x - y‖ := by
  -- RMSNorm 的点对界：直接对**内层和**这两点用 rmsNormE_sqrt_lipschitz
  have hF : ‖RMSNormOp (x + ConvCombOp w V x + W x)
      - RMSNormOp (y + ConvCombOp w V y + W y)‖
      ≤ (Real.sqrt n / c)
        * ‖(x + ConvCombOp w V x + W x) - (y + ConvCombOp w V y + W y)‖ := by
    rw [RMSNormOp_eq_rmsNormE (x + ConvCombOp w V x + W x),
        RMSNormOp_eq_rmsNormE (y + ConvCombOp w V y + W y)]
    exact rmsNormE_sqrt_lipschitz _ _ c hc hx hy
  have hA : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖ConvCombOp w V x - ConvCombOp w V y‖ ≤ M * ‖x - y‖ := by
    intro x y
    exact convComb_lipschitz_prob w V M hw hsum hM x y
  have hG : ∀ x y : EuclideanSpace ℝ (Fin n), ‖W x - W y‖ ≤ ‖W‖ * ‖x - y‖ := by
    intro x y
    exact linear_map_lipschitz W x y
  have hLf : 0 ≤ Real.sqrt n / c := by positivity
  -- 内层和 (1 + M + ‖W‖)-Lipschitz（加法/残差组合律，逐点）
  have hid : ∀ x y : EuclideanSpace ℝ (Fin n), ‖x - y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
    intro x y; simp
  have hin : ‖(x + ConvCombOp w V x + W x) - (y + ConvCombOp w V y + W y)‖
      ≤ (1 + M + ‖W‖) * ‖x - y‖ := by
    have h1 := lipschitz_add (fun z : EuclideanSpace ℝ (Fin n) => z)
      (ConvCombOp w V) 1 M hid hA
    have h2 := lipschitz_add (fun z : EuclideanSpace ℝ (Fin n) => z + ConvCombOp w V z)
      (fun z : EuclideanSpace ℝ (Fin n) => W z) (1 + M) ‖W‖ h1 hG
    simpa [add_assoc] using h2 x y
  calc
    ‖RMSNormOp (x + ConvCombOp w V x + W x)
        - RMSNormOp (y + ConvCombOp w V y + W y)‖
        ≤ (Real.sqrt n / c)
          * ‖(x + ConvCombOp w V x + W x) - (y + ConvCombOp w V y + W y)‖ := hF
    _ ≤ (Real.sqrt n / c) * ((1 + M + ‖W‖) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left hin hLf
    _ = ((Real.sqrt n / c) * (1 + M + ‖W‖)) * ‖x - y‖ := by ring

/-- **松弛版对照（全部证明保留，不删）**：`2√n/c` 仍是有效上界。
本定理把紧版 `transformer_block_closed` 蕴含为 `2√n/c` 版，
便于下游按需回退到松弛常数。

**注**：本定理多一个显式假设 `hbr : 0 ≤ 1 + M + ‖W‖`
（比较两个常数时需要它；紧版 `transformer_block_closed` **不需要**该假设，
因为它只在 `hLf : 0 ≤ √n/c` 下组装）。本定理**保留 `[NeZero n]`** 与等价陈述
（`Fin k` 索引不参与，故不要求 `[NeZero k]`）。

**⚠ v14（B53）**：定义域前提与紧版同步改为**点对（内层残差和上）**
（旧 `hxdom : ∀ z` 与 `hc : 0 < c` 矛盾、使本定理同样空洞）。
⚠ **v15 更正（B60）**：与紧版同步，前提位置由 `x` 改正为 RMSNorm 的**实际输入**
（内层和）——设在 `x` 上会使 `?_` 要求假命题 `∀ u, ‖x‖ ≤ ‖u‖`。 -/
theorem transformer_block_closed_relaxed {n k : ℕ} [NeZero n] (w : Fin k → ℝ)
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (M c : ℝ)
    (hc : 0 < c) (hw : ∀ i : Fin k, 0 ≤ w i) (hsum : (∑ i : Fin k, w i) = 1)
    (hM : ∀ i : Fin k, ‖V i‖ ≤ M)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : c ≤ ‖x + ConvCombOp w V x + W x‖)
    (hy : c ≤ ‖y + ConvCombOp w V y + W y‖)
    (hbr : 0 ≤ 1 + M + ‖W‖) :
    ‖RMSNormOp (x + ConvCombOp w V x + W x)
      - RMSNormOp (y + ConvCombOp w V y + W y)‖
      ≤ ((Real.sqrt n * 2 / c) * (1 + M + ‖W‖)) * ‖x - y‖ := by
  have htight := transformer_block_closed w V W M c hc hw hsum hM x y hx hy
  have h1 : Real.sqrt n / c ≤ Real.sqrt n * 2 / c := by
    have hle : Real.sqrt n * 1 ≤ Real.sqrt n * 2 := by
      nlinarith [Real.sqrt_nonneg n]
    have h3 : Real.sqrt n * 1 / c ≤ Real.sqrt n * 2 / c :=
      div_le_div_of_nonneg_right hle (le_of_lt hc)
    simpa using h3
  calc
    ‖RMSNormOp (x + ConvCombOp w V x + W x)
      - RMSNormOp (y + ConvCombOp w V y + W y)‖
        ≤ ((Real.sqrt n / c) * (1 + M + ‖W‖)) * ‖x - y‖ := htight
    _ ≤ ((Real.sqrt n * 2 / c) * (1 + M + ‖W‖)) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hbr) (norm_nonneg _)

/-! ## 注：完整模型端到端实例化收官
  单块闭式 L_block = (√n/c)·(1 + M + ‖W‖)（本定理，**紧常数**；
  松弛版 (2√n/c)·(1 + M + ‖W‖) 见 `transformer_block_closed_relaxed`）⟹
  n 块链端到端误差 ≤ (L_block)ⁿ·‖Δx‖（chainN_identical_blocks_bound）
  ——「完整模型前向链」（RealChain）从骨架到闭式；
  全部组件常数（规范化/注意力/FFN）显式证明（RealRMSNormSharpness、
  RealAttentionLipschitz、RealOperatorNorm、RealSoftmaxLipschitz）。
  唯一场景假设：数据范数下界 c（有界域）。-/

end Lattice
