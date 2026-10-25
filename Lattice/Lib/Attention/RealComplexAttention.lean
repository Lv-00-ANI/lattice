import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Chain.RealComplex
import Lattice.Lib.Attention.RealComplexRoPE
/-!
# LATTICE: 复数注意力 —— ℂ 打分、softmax 概率分布与 RoPE 相位不变性

RealAttention（实注意力：`ProbDist`/`convComb`/`softmax` 与凸组合范数界）与
RealComplexRoPE（复数 RoPE：|⟨R_m q, R_n k⟩| = |⟨q,k⟩|）的**交汇模块**：

  1. **复数打分**：`complexScore q k = Re⟪q,k⟫`（实数值打分，相位相关）与
     `complexAbsScore q k = |⟪q,k⟫|`（打分模，相位不变）；
  2. **softmax 仍是行随机概率分布**：softmax 只依赖实数值打分，故 ℂ 打分
     （经 `Re` 或 `|·|` 实化）的 softmax 满足 `ProbDist`（非负 + 和为 1）——
     「ℂ 打分不改变注意力权重的概率语义」；
  3. **复数注意力输出界**：ℂ 打分的注意力输出仍是 value 的凸组合，
     `‖convComb (softmax (complexScore ∘ (q,k))) V‖ ≤ M`（RealAttention 凸组合界）；
  4. **核心——RoPE 相位不改变注意力的模决定性部分**：
     `complexAbsScore (R_m q) (R_n k) = complexAbsScore q k`（RealComplexRoPE
     `complex_rope_relative_abs`），故任意 key 族的 |打分| 向量在位置编码下不变，
     从而 softmax 权重不变（相位只移动内积的相位 e^{iθ(n−m)}，不改变模）；
  5. **ℂ 注意力在实数据上退化为 ℝ 版**：`complexScore (x:ℂ) (y:ℂ) = x*y`，
     故 softmax 权重与实数内积注意力一致。

诚实性：`Re⟪q,k⟫` 本身**不是** RoPE 不变量（相位移动会旋转实部），
故 RoPE 不变性只对 `|⟪q,k⟫|`（模）陈述——这是本文件明确区分的两个打分口径。
所有定理只引用 mathlib 4.14 现成引理与既有文件定理，无 sorry/axiom/admit。
模型无关：任意键数 ι、任意基频 θ、任意位置、任意复 value。
-/

noncomputable section

namespace Lattice

open scoped ComplexConjugate

/-! mathlib 4.14 中 ⟪x, y⟫ 是作用域内记法；本文件沿用 RealComplex/RealComplexRoPE
的显式本地记法（固定 𝕜 := ℂ）。 -/
local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-! ## 定义：复数打分（两个口径） -/

/-- 复数打分（实数值，相位相关）：`Re⟪q,k⟫`。
这是把 ℂ 内积实化后可直接送入 softmax 的实值打分。 -/
def complexScore (q k : ℂ) : ℝ := RCLike.re ⟪q, k⟫

/-- 复数打分的模（相位不变）：`|⟪q,k⟫|`。
RoPE 只改变内积相位，故这是位置编码下稳定的打分口径。 -/
def complexAbsScore (q k : ℂ) : ℝ := Complex.abs ⟪q, k⟫

/-! ## 第一节：softmax 只依赖实数值打分 ⟹ ℂ 打分 softmax 是概率分布 -/

/-- 任意实值打分的 softmax 是概率分布（非负 + 和为 1）：
softmax 的概率语义只依赖打分的**实数值**，与打分的来源（ℝ/ℂ）无关。 -/
theorem complex_softmax_pmf {ι : Type*} [Fintype ι] [Nonempty ι] (score : ι → ℝ) :
    ProbDist (softmax score) :=
  ⟨softmax_nonneg score, softmax_sum_one score⟩

/-- ℂ 打分（经 `complexScore` 实化）的 softmax 是概率分布。 -/
theorem complex_score_softmax_pmf {ι : Type*} [Fintype ι] [Nonempty ι]
    (q k : ι → ℂ) :
    ProbDist (softmax (fun i => complexScore (q i) (k i))) :=
  complex_softmax_pmf _

/-- ℂ 打分（经 `complexAbsScore` 取模实化）的 softmax 是概率分布。 -/
theorem complex_abs_score_softmax_pmf {ι : Type*} [Fintype ι] [Nonempty ι]
    (q k : ι → ℂ) :
    ProbDist (softmax (fun i => complexAbsScore (q i) (k i))) :=
  complex_softmax_pmf _

/-! ## 第二节：复数注意力输出界（凸组合界，values 在 ℂ 上） -/

/-- **复数注意力输出界**：ℂ 打分的注意力输出是复 value 的凸组合，
被最大 value 范数界住：`‖Σᵢ softmax(score)ᵢ • Vᵢ‖ ≤ M`。
（`ℂ` 作为 ℝ-赋范空间调用 RealAttention `attention_output_bound`。） -/
theorem complex_attention_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (q k : ι → ℂ) (V : ι → ℂ) (M : ℝ) (hV : ∀ i, ‖V i‖ ≤ M) :
    ‖convComb (softmax (fun i => complexScore (q i) (k i))) V‖ ≤ M :=
  attention_output_bound (fun i => complexScore (q i) (k i)) V M hV

/-- 复数注意力输出界（模打分口径）：同一凸组合界，打分用 `|⟪q,k⟫|`。 -/
theorem complex_abs_attention_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (q k : ι → ℂ) (V : ι → ℂ) (M : ℝ) (hV : ∀ i, ‖V i‖ ≤ M) :
    ‖convComb (softmax (fun i => complexAbsScore (q i) (k i))) V‖ ≤ M :=
  attention_output_bound (fun i => complexAbsScore (q i) (k i)) V M hV

/-- 复数注意力输出界（`convComb` 展开形式）：把 `convComb` 展开成 `∑ i, w i • V i`
（`w` 为 `complexScore` 打分的 `softmax` 权重）后，输出仍被 `M` 界住。
此处陈述为「输出范数 ≤ M」，右端是 `M` 本身而非乘积形式；本定理与
`complex_attention_bound` 同源（证明即对其的一行转发），差别只在结论写成展开后的
显式和，供下游直接按展开形式消费。 -/
theorem complex_attention_bound_expanded {ι : Type*} [Fintype ι] [Nonempty ι]
    (q k : ι → ℂ) (V : ι → ℂ) (M : ℝ) (hV : ∀ i, ‖V i‖ ≤ M) :
    ‖∑ i, (softmax (fun j => complexScore (q j) (k j)) i) • V i‖ ≤ M :=
  complex_attention_bound q k V M hV

/-! ## 第三节：核心——RoPE 相位不改变注意力的模决定性部分 -/

/-- **RoPE 下 |打分| 族不变**：query 在位置 m、第 i 个 key 在位置 `pos i`，
经复数 RoPE 旋转后 |打分| 向量与原 |打分| 向量逐项相等
（RealComplexRoPE `complex_rope_relative_abs`：相位因子 |e^{iθ(n−m)}| = 1）。 -/
theorem complex_rope_abs_score_family_invariant {ι : Type*}
    (θ m : ℝ) (pos : ι → ℝ) (q : ℂ) (k : ι → ℂ) :
    (fun i => complexAbsScore (complexRotate θ m q) (complexRotate θ (pos i) (k i)))
      = (fun i => complexAbsScore q (k i)) := by
  funext i
  exact complex_rope_relative_abs θ m (pos i) q (k i)

/-- **复数 RoPE 注意力不变性（核心）**：位置编码不改变注意力的模决定性部分——
`softmax` 作用于 |打分| 得到的注意力权重在 RoPE 前后完全一致。
（相位 e^{iθ(n−m)} 模 1，只影响 `Re⟪·,·⟫` 的方向，不影响 `|⟪·,·⟫|`。） -/
theorem complex_rope_attention_invariant {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ m : ℝ) (pos : ι → ℝ) (q : ℂ) (k : ι → ℂ) :
    softmax (fun i => complexAbsScore (complexRotate θ m q) (complexRotate θ (pos i) (k i)))
      = softmax (fun i => complexAbsScore q (k i)) := by
  rw [complex_rope_abs_score_family_invariant]

/-- RoPE 注意力的输出不变性（由权重不变 + value 不变推出凸组合不变）：
模打分口径下，RoPE 前/后的注意力输出相等。 -/
theorem complex_rope_attention_output_invariant {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ m : ℝ) (pos : ι → ℝ) (q : ℂ) (k : ι → ℂ) (V : ι → ℂ) :
    convComb (softmax (fun i =>
        complexAbsScore (complexRotate θ m q) (complexRotate θ (pos i) (k i)))) V
      = convComb (softmax (fun i => complexAbsScore q (k i))) V := by
  rw [complex_rope_attention_invariant]

/-- 相位口径的说明性定理：RoPE 后内积 = 原内积 × 相位因子 e^{iθ(n−m)}
（RealComplexRoPE `complex_rope_phase_shift`）——**实部会被相位旋转改变**，
这正是「RoPE 不变性只能对 |·| 陈述」的形式化理由。 -/
theorem complex_rope_score_phase_relation (θ m n : ℝ) (q k : ℂ) :
    ⟪complexRotate θ m q, complexRotate θ n k⟫ =
      ⟪q, k⟫ * Complex.exp (((θ * (n - m) : ℝ) : ℂ) * Complex.I) :=
  complex_rope_phase_shift θ m n q k

/-! ## 第四节：ℂ 注意力在实数据上退化为 ℝ 版 -/

/-- **实数据退化**：实数的 ℂ 内积实部 = 实数乘积，
故 ℂ 打分在实数据上等于 ℝ 打分 `x*y`（虚部为 0，无 ℂ 特有信息）。 -/
theorem complex_attention_eq_real (x y : ℝ) :
    complexScore (x : ℂ) (y : ℂ) = x * y := by
  unfold complexScore
  rw [RCLike.inner_apply]
  simp [Complex.conj_ofReal, Complex.ofReal_mul]

/-- 实数据退化（函数形式）：逐项实数据的 ℂ 打分族 = ℝ 打分组。 -/
theorem complex_attention_eq_real_family {ι : Type*} (x y : ι → ℝ) :
    (fun i => complexScore ((x i : ℝ) : ℂ) ((y i : ℝ) : ℂ)) = fun i => x i * y i := by
  funext i
  exact complex_attention_eq_real (x i) (y i)

/-- 实数据退化（权重形式）：ℂ 打分与 ℝ 内积打分的 softmax 权重完全相同。 -/
theorem complex_attention_eq_real_weights {ι : Type*} [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) :
    softmax (fun i => complexScore ((x i : ℝ) : ℂ) ((y i : ℝ) : ℂ))
      = softmax (fun i => x i * y i) := by
  rw [complex_attention_eq_real_family]

/-! 输出层退化注（诚实边界）：实数数据下 ℂ 打分与 ℝ 内积打分逐项相等
（`complex_attention_eq_real_family`），故 softmax 权重相同
（`complex_attention_eq_real_weights`）；把实 value 经 `(· : ℝ) → ℂ` 嵌入后，
ℂ 凸组合输出即该 ℝ 凸组合同构像——这一步是 ℂ 作为 ℝ-代数的 `map_sum`/`map_smul`
纯代数事实，不属于本模块的语义结论，故不在此单独陈述。-/

/-! ## 注：ℂ 注意力闭环
  ℂ 打分经实化（`Re` 或 `|·|`）后进入 softmax（第一节：概率分布），
  注意力输出由 RealAttention 凸组合界控制（第二节）；核心不变性
  `complex_rope_attention_invariant` 显示 RoPE 相位只改变内积方向、
  不改变 |打分|，故模口径下的注意力权重与输出位置编码不变（第三节）；
  实数据上全部退化为 ℝ 版（第四节）。Re 口径的 RoPE 非不变性由
  `complex_rope_score_phase_relation` 明确记录（诚实边界）。 -/

end Lattice
