import Mathlib
import Lattice.Lib.Attention.RealHardAttention
import Lattice.Lib.Architectures.RealSwiGLU
/-!
# LATTICE: MoE/top-k 路由链 —— 单调门控保序选择

稀疏路由调研（research/real-world/norm-topk-family.md 推荐目标 2）：
MoE（Mixtral/Switch/DeepSeek-V3）的门控路由——**单调门控不改选择**：

  1. argmax_of_monotone：单调门控 g（如 softmax/sigmoid）不改变 argmax
     （sⱼ ≤ sᵢ ⟹ g(sⱼ) ≤ g(sᵢ)）；
  2. sigmoid 保序：σ 单调（exp 单调 + 正分母倒数反序）——门控保序；
  3. MoE 专家选择：分数 argmax 与门控输出 argmax 一致（路由确定性）。

衔接：softmax 保序已在 RealHardAttention.softmax_monotone 证明；
top-k 选择集在单调门控下不变（保序选择），k=1 退化为 argmax（已证）。

模型无关：任意分数函数、任意单调门控。

⚠ **本文件不含负载均衡 / 容量 / 丢弃语义**（W24 判定「名不副实」的依据）。
本文件的 5 条定理**全部是保序/确定性命题**——它们在任何负载下都成立，
因此**不携带任何负载信息**。真正的 MoE 负载均衡语义见：
  · `RealMoELoadBalance.lean`（容量/丢弃的离散计数内核）；
  · `RealMoERouteCapacity.lean`（把路由选择集接上容量丢弃的桥）。
⟹ **不得**把本文件的保序命题当作「MoE 负载均衡已覆盖」的证据。
-/


noncomputable section

namespace Lattice

-- 注：RealHardAttention / RealSwiGLU 是模块名而非命名空间，open 无效，已删除。
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## 定理一：单调门控保 argmax
g 单调 ⟹ argmax(g∘s) = argmax(s)（门控不改最大分数的选择）。-/

omit [Fintype ι] [Nonempty ι] in
theorem argmax_of_monotone (s : ι → ℝ) (g : ℝ → ℝ) (hg : Monotone g) (i : ι)
    (hi : IsArgMax s i) : IsArgMax (fun j => g (s j)) i := by
  intro j
  exact hg (hi j)

/-! ## 定理二：sigmoid 保序（门控单调）
x ≤ y ⟹ σ(x) ≤ σ(y)（exp 单调 + 正分母倒数反序）。-/

theorem sigmoid_monotone (x y : ℝ) (h : x ≤ y) : sigmoid x ≤ sigmoid y := by
  unfold sigmoid
  -- x ≤ y → -y ≤ -x → exp(-y) ≤ exp(-x)
  have hne : Real.exp (-y) ≤ Real.exp (-x) := by
    exact Real.exp_le_exp.mpr (by linarith)
  -- 分母：1+e^-y ≤ 1+e^-x；正分母倒数反序
  have hd1 : 0 < 1 + Real.exp (-x) := by positivity
  have hd2 : 0 < 1 + Real.exp (-y) := by positivity
  have hden : 1 + Real.exp (-y) ≤ 1 + Real.exp (-x) := by linarith
  -- 1/(1+e^-x) ≤ 1/(1+e^-y)（分母反序）
  have hinv : (1 + Real.exp (-x))⁻¹ ≤ (1 + Real.exp (-y))⁻¹ :=
    (inv_le_inv₀ hd1 hd2).mpr hden
  -- 用除法形式
  calc
    1 / (1 + Real.exp (-x)) = (1 + Real.exp (-x))⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ (1 + Real.exp (-y))⁻¹ := hinv
    _ = 1 / (1 + Real.exp (-y)) := by rw [div_eq_mul_inv]; ring

/-! ## 定理三：sigmoid 门控保序选择
sⱼ ≤ sᵢ ⟹ σ(sⱼ) ≤ σ(sᵢ)（门控不改变分数次序）。-/

omit [Fintype ι] [Nonempty ι] in
theorem sigmoid_gate_preserves_order (s : ι → ℝ) (i j : ι) (h : s j ≤ s i) :
    sigmoid (s j) ≤ sigmoid (s i) :=
  sigmoid_monotone (s j) (s i) h

/-! ## 定理四：MoE 专家选择一致
分数 argmax ⟹ 门控输出 argmax（sigmoid 门控路由确定性）。-/

theorem moe_expert_selection (s : ι → ℝ) (i : ι) (hi : IsArgMax s i) :
    IsArgMax (fun j => sigmoid (s j)) i := by
  exact argmax_of_monotone s sigmoid (by
    intro a b h
    exact sigmoid_monotone a b h) i hi

/-! ## 定理五：softmax 保序门控（衔接 RealHardAttention）
softmax 是单调门控（保序），门控路由与分数次序一致。 -/

theorem softmax_gate_preserves_order (s : ι → ℝ) (i j : ι) (h : s j ≤ s i) :
    softmax s j ≤ softmax s i :=
  softmax_monotone s i j h

/-! ## 注：top-k 变体等价
全空间 softmax → top-k 选择 → 重归一，等价于 top-k logits 上直接 softmax
（选择集由保序门控决定，重归一不改变已选集的相对权重）。
k=1 退化 argmax 已证（RealHardAttention.argmax_unique）。 -/

end Lattice
