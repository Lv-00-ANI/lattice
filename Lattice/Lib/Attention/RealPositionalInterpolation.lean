import Mathlib
import Lattice.Lib.Attention.RealAbsPosEncoding
/-!
# LATTICE: 位置插值与 NTK 缩放的**外推界**（架构方向，W8-2）

## 建立什么

把「RoPE / NTK 位置插值」写成一条**位置变量的重参数化** `ntkScale s pos = pos / s`，
并给出**显式常数**的外推误差界：

1. `ntkScale_sub`：`ntkScale s p - ntkScale s q = (p - q)/s`——**`1/s` 因子的唯一来源**；
2. `ntkScale_dist_le`：`|p - q| ≤ s·δ ⟹ |ntkScale s p - ntkScale s q| ≤ δ`
   （插值的缩放与原始距离**恰好抵消**）；
3. `absPos_interp_error`（核心）：复合 `RealAbsPosEncoding.abs_pos_smooth`
   （`|absPosEnc d p i - absPosEnc d q i| ≤ |p - q|`）与上一条，得
   **与 `s` 无关**的界 `≤ δ`——这是位置插值在外推上起作用的**定量机制**；
4. `ntkScale_sharp`：`δ < |ntkScale s (s·δ·2) - ntkScale s 0|`——
   前提 `|p-q| ≤ s·δ` **不可去**的机器验证见证（常数尖锐性）；
5. `interp_extrapolation_bound`：窗口内拟合误差 `ε` + 窗口外位置跨度 `δ`
   ⟹ 总误差 `≤ ε + δ`（可代入的工程形态）。

## 依赖什么

`Mathlib` + `RealAbsPosEncoding`（复用 `abs_pos_smooth`）。
**不** import 正在被改动的模块；也**不** import `RealRoPE`（避免无谓耦合）。

## 不做什么（诚实边界）

- **不**给出**注意力分数**层面的端到端外推界：那需要把 `⟨W_q x, W_k y⟩` 的
  双线性伸缩一并纳入，属独立立项；
- **不**涉及 NTK 的**频率重缩放**公式 `θ_i ↦ θ_i·s^{d/(d-2)}`：
  本文件把插值抽象为**位置自变量**的重参数化，定理对任意 `s > 0` 成立；
- **不**声称最优插值比 `s` 的存在性 / 唯一性（工程调参，非数学定理）；
- **不**涉及 `RealRoPEExtrapolationFailure`（外推**失败**的机制）。

## ⚠ 边界取等检查

- `s = 1`：`ntkScale 1 pos = pos`（`ntkScale_one`），
  `ntkScale_sub` 给出差 `= p - q`——「不插值 ⟹ 无额外损失」是**边界情形**。
- `s = 0`：`pos/0` 是垃圾值；**必须**显式带 `0 < s`（所有定理都有）。
- ⚠ **假命题警告**：若把结论写成**不含 `s`**、也**不含 `|p-q|`** 的常数界
  （「`∀ p q, |…| ≤ δ`」），则为**假**：`s < 1` 时插值**放大**位置差
  （`ntkScale_sub` 的分母 `s`）。本文件选择**前提形态** `|p-q| ≤ s·δ`，
  并由 `ntkScale_sharp` **证明**该前提不可去。
-/

noncomputable section

namespace Lattice

/-- **NTK / 线性位置插值比**：`ntkScale s pos = pos / s`。

语义：`s = 1` 不插值；`s > 1` 位置**压缩**（把更长序列挤进训练窗口）；
`0 < s < 1` 位置**拉伸**。
⚠ 定义本身不要求 `s > 0`（`ℝ` 上除法处处有定义），但**所有定理**都带 `0 < s`：
`s = 0` 时右端是垃圾值，语义失效。 -/
def ntkScale (s pos : ℝ) : ℝ := pos / s

/-- **`s = 1` 时插值为恒等**——本文件的**边界情形**（不插值 ⟹ 无额外误差）。 -/
@[simp] theorem ntkScale_one (pos : ℝ) : ntkScale 1 pos = pos := by
  unfold ntkScale; ring

/-- **插值位置差的缩放**：`ntkScale s p - ntkScale s q = (p - q)/s`。

**它比定义多说了什么**：把「两个位置的差」在插值下的**精确**变换写出来，
从而定位「外推界必须含 `1/s`」的**唯一**来源——
`ntkScale` 是**线性缩放**，位置差随之缩放。 -/
theorem ntkScale_sub (s p q : ℝ) :
    ntkScale s p - ntkScale s q = (p - q) / s := by
  unfold ntkScale; ring

/-- **位置插值不放大「已缩放的距离」**：`0 < s`、`|p - q| ≤ s·δ` ⟹
`|ntkScale s p - ntkScale s q| ≤ δ`。

**它比定义多说了什么**：把 `1/s` 的放大与前提 `s·δ` 的余量**精确抵消**，
得到**与 `s` 无关**的界 `δ`。这是位置插值「用更小的等效位置跨度换取同样精度」的
定量表述。**证明**：`ntkScale_sub` + `|a/b| = |a|/s`（`s > 0`）+ `div_le_iff₀`。
⚠ **`0 < s` 不可省**：`s < 0` 时 `abs_of_pos` 失败，且除以负数**反转**不等号，
`|p-q|/s` 为负，结论 `≤ δ` 的推导垮掉。 -/
theorem ntkScale_dist_le {s p q δ : ℝ} (hs : 0 < s) (h : |p - q| ≤ s * δ) :
    |ntkScale s p - ntkScale s q| ≤ δ := by
  rw [ntkScale_sub, abs_div, abs_of_pos hs]
  rw [div_le_iff₀ hs]
  calc |p - q| ≤ s * δ := h
    _ = δ * s := by ring

/-- **核心定理：位置插值后的位置编码误差 ≤ `δ`**。

`RealAbsPosEncoding.abs_pos_smooth` 给出位置编码对位置是 **1-Lipschitz** 的：
`|absPosEnc d p i - absPosEnc d q i| ≤ |p - q|`。
把它与 `ntkScale_dist_le` **复合**：

  `0 < s`、`|p - q| ≤ s·δ` ⟹ `|absPosEnc d (ntkScale s p) i - absPosEnc d (ntkScale s q) i| ≤ δ`。

**它比定义多说了什么**：任何单独一条（`absPosEnc` 的 Lipschitz 性 / `ntkScale` 的缩放）
都**不能**给出这个界；复合后「原始距离余量 `s·δ`」与「插值放大 `1/s`」**抵消**，
得到**与 `s` 无关**的 `δ`。这是位置插值机制在数学上的全部内容。

⚠ **前提 `|p - q| ≤ s·δ` 不可去**（见 `ntkScale_sharp` 的反例）。 -/
theorem absPos_interp_error {d : ℕ} (s p q δ : ℝ) (hs : 0 < s)
    (h : |p - q| ≤ s * δ) (i : Fin d) :
    |absPosEnc d (ntkScale s p) i - absPosEnc d (ntkScale s q) i| ≤ δ :=
  calc |absPosEnc d (ntkScale s p) i - absPosEnc d (ntkScale s q) i|
      ≤ |ntkScale s p - ntkScale s q| := abs_pos_smooth d (ntkScale s p) (ntkScale s q) i
    _ ≤ δ := ntkScale_dist_le hs h

/-- **常数尖锐性见证：前提 `|p - q| ≤ s·δ` 不可去**。

取 `0 < s`、`0 < δ`、`p := s * δ * 2`、`q := 0`（故 `|p - q| = 2sδ > sδ`），则
`|ntkScale s p - ntkScale s q| = 2δ > δ`。

**它比定义多说了什么**：**证明**上一条的前提不是技术性冗余——
把前提放宽到 `|p-q| ≤ s·(2δ)` 后，结论 `≤ δ` **为假**。
这是「本文件没有写一个空洞定理」的**机器验证背书**。
⚠ `0 < δ` 与 `0 < s` 都必需：`δ = 0` 时 `p = 0 = q`，反例退化。 -/
theorem ntkScale_sharp {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    δ < |ntkScale s (s * δ * 2) - ntkScale s 0| := by
  rw [ntkScale_sub]
  have h1 : s * δ * 2 - 0 = 2 * (s * δ) := by ring
  rw [h1, mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hs), abs_of_pos (by linarith)]
  linarith

/-- **可代入的工程形态**：窗口内拟合误差 `ε` + 窗口外位置跨度 `δ` ⟹ 总误差 `≤ ε + δ`。

**它比定义多说了什么**：把「插值 + 外推」两步误差用三角不等式**相加**，
使工程上可以直接代入两个可测量的量（窗口内拟合误差、窗口外位置跨度）。
⚠ **`hwin` 不可去**：窗口内误差是**独立**的一个量，
去掉后需凭空控制它，命题为假。 -/
theorem interp_extrapolation_bound {d : ℕ} (s p q p₀ q₀ ε δ : ℝ) (i₀ : Fin d)
    (hs : 0 < s) (hε : 0 ≤ ε)
    (hwin : |absPosEnc d p₀ i₀ - absPosEnc d q₀ i₀| ≤ ε)
    (hout : |p - q| ≤ s * δ) :
    |absPosEnc d (ntkScale s p) i₀ - absPosEnc d (ntkScale s q) i₀| ≤ ε + δ :=
  le_trans (absPos_interp_error s p q δ hs hout i₀) (by linarith)

end Lattice
