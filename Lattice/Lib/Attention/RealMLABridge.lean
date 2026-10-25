import Mathlib
import Lattice.Lib.Attention.RealMLA
import Lattice.Lib.Attention.RealGQA
/-!
# LATTICE: MLA 桥 —— 吸收算子的范数代价与「与普通打分一致」的退化

本文件是 `RealMLA` 的**语义消费者**（不是装饰性 import）：它消费吸收律，
给出两条 MLA **特有**、无法从 `RealGQA` 或 `RealAttention` 单独导出的结论。

  1. `mlaAbsorbedMap`：MLA 推理时**预合成**的算子 `W_UK† ∘ W_Q`；
  2. `mla_absorbed_opNorm_le`（**定量界**）：`‖W_UK† ∘ W_Q‖ ≤ ‖W_UK‖ * ‖W_Q‖`——
     吸收把「每 token 物化 k」换成「一次算子合成」，其**代价**被两个投影的
     算子范数之积界住。含 `≤`，不是恒等式；
  3. `mla_score_eq_plain_inner`（**桥接**）：上投影取恒等（`W_UK = id`）时，
     MLA 的吸收打分 = 普通内积打分——即 MLA 在「不压缩」退化下与标准注意力
     打分**逐点一致**，说明 MLA 是标准注意力的**真扩展**而非不同对象。

## 接线状态：本文件是**消费链末环**（`not wired`，显式登记）

`check-new-roots-indegree.py` 实测：`RealMLA` 已从 `[BARE]` 列表消失（本文件是它的
真实入边），但**本文件自身** `in-degree = 0`（`[BARE]`）。这是**结构必然**，
不是缺陷——消费链必然在某一环保终止（Y06 §2.5 的「孤岛逐层下推」）。
本文件**没有**装饰性 import，也不打算为刷绿而入边；
若后续有模块需要「MLA 打分 = 普通打分」这一桥接，本模块即成为其真实依赖。

## 诚实边界

- 本文件**不声称** MLA 的训练/推理**复杂度**结论；`mla_absorbed_opNorm_le` 是
  算子范数界，不是 FLOP/IO 计数。
- 恒等退化的等价性**只对 nocompute 的打分**成立，不含 RoPE 解耦维度。
-/

noncomputable section

namespace Lattice

variable {E L : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]

/-- MLA 推理时预合成的**吸收算子**：`x ↦ W_UK† (W_Q x)`。
物化它之后，每个 token 只需一次与 latent 的内积，无需物化 `k = W_UK c`。 -/
def mlaAbsorbedMap (WQ : E →L[ℝ] E) (WUK : L →L[ℝ] E) : E →L[ℝ] L :=
  (ContinuousLinearMap.adjoint WUK).comp WQ

/-- **吸收的算子范数代价**：`‖W_UK† ∘ W_Q‖ ≤ ‖W_UK‖ * ‖W_Q‖`。
（伴随等距 `‖W_UK†‖ = ‖W_UK‖` 与复合的次乘性。）
这是 MLA 特有的定量界：吸收不是免费的，其代价由两个投影的范数之积控制。 -/
theorem mla_absorbed_opNorm_le (WQ : E →L[ℝ] E) (WUK : L →L[ℝ] E) :
    ‖mlaAbsorbedMap WQ WUK‖ ≤ ‖WUK‖ * ‖WQ‖ := by
  unfold mlaAbsorbedMap
  calc ‖(ContinuousLinearMap.adjoint WUK).comp WQ‖
      ≤ ‖ContinuousLinearMap.adjoint WUK‖ * ‖WQ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖WUK‖ * ‖WQ‖ := by rw [ContinuousLinearMap.adjoint.norm_map]

/-- **吸收打分 = 预合成算子打分**：把 `mla_absorb_query` 重述为算子形式，
说明「吸收」在陈述层面就是一次算子应用。 -/
theorem mla_score_eq_absorbedMap (WQ : E →L[ℝ] E) (WUK : L →L[ℝ] E) (x : E) (c : L) :
    inner (𝕜 := ℝ) (WQ x) (WUK c) = inner (𝕜 := ℝ) (mlaAbsorbedMap WQ WUK x) c := by
  unfold mlaAbsorbedMap
  exact mla_absorb_query WQ WUK x c

/-- **恒等退化 ⟹ 普通内积打分**：`W_UK = id`（不压缩）时，
MLA 的吸收打分退化为普通内积打分 `⟨q, c⟩`——
即 MLA 是标准注意力打分的**真扩展**（在恒等上投影处与原打分重合）。 -/
theorem mla_score_eq_plain_inner (q c : E) :
    mlaScoreAbsorbed (ContinuousLinearMap.id ℝ E) q c = inner (𝕜 := ℝ) q c := by
  unfold mlaScoreAbsorbed
  rw [ContinuousLinearMap.adjoint_id]
  simp [ContinuousLinearMap.id_apply]

/-! **桥接 `RealGQA`**：`RealGQA.gqaLogits` 在 `Kv = id`、`√d = 1` 时的分数，
与 MLA 恒等上投影的吸收打分**逐点相等**——
把两个模块的「打分」定义在退化点钉在一起（消费 `RealGQA.gqaLogits`）。
⚠ `omit` 不能紧跟 docstring（Lean 报 `unexpected token 'omit'`），故此处用块注释。 -/
omit [CompleteSpace E] in
theorem mla_score_eq_gqa_logits_id {ι : Type} [Fintype ι] [Nonempty ι]
    (Q : Fin 1 → E →L[ℝ] E) (g : Fin 1 → Fin 1)
    (xq : E) (x : ι → E) (i : Fin 1) (j : ι) :
    gqaLogits Q (fun _ : Fin 1 => ContinuousLinearMap.id ℝ E) g 1 xq x i j
      = inner (𝕜 := ℝ) (Q i xq) (x j) := by
  unfold gqaLogits
  simp [ContinuousLinearMap.id_apply, Real.sqrt_one]

end Lattice
