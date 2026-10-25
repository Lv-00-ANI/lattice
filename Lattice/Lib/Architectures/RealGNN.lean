import Mathlib

/-!
# LATTICE: 图神经网络的消息传递（有限图，模型无关）

GNN 的一层是「邻接加权聚合 + 线性变换 + 逐点非线性」：

    adj E i j       = E i j                                  （邻接/边权矩阵）
    msgPass A h i   = ∑_j A_i_j · h_j                        （一跳聚合）
    gnnLayer A W σ h i = σ (W · msgPass A h i)               （线性 + 非线性）

## 主结果（全部模型无关：任意有限顶点集 ι、任意权重 A、任意激活 σ）

1. **聚合有界**（`msgPass_bound`）：`∀j, |h_j| ≤ M` ⟹
   `|msgPass A h i| ≤ M · ∑_j |A_i_j|`。这正是 GNN 表达力受度分布控制的代数根源：
   聚合的放大倍数 = 该顶点的**加权度**。
2. **聚合 Lipschitz**（`msgPass_lipschitz`）：逐点扰动 ≤ δ ⟹
   `|msgPass A h i − msgPass A h' i| ≤ δ · ∑_j |A_i_j|`
   —— 聚合对输入扰动的敏感度同样由加权度控制（GNN 过平滑/过压缩分析的起点）。
3. **一层 Lipschitz**（`gnnLayer_lipschitz`）：`σ` 是 L-Lipschitz ⟹
   `|gnnLayer A W σ h i − gnnLayer A W σ h' i| ≤ L·|W|·δ·∑_j |A_i_j|`。
4. **两跳展开**（`two_hop_msg` / `twoHopMsg_bound`）：
   `msgPass A (msgPass A h) k = ∑_j A_k_j · (∑_i A_j_i · h_i)`，
   界 `≤ (∑_j |A_k_j| · ∑_i |A_j_i|) · M`（界由**两跳路径的权重和**控制）。
5. **度归一化不放大**（`degNorm_sum_abs_le_one` / `degNorm_msgPass_bound`）：
   定义 `degNorm A i j = A_i_j / (1 + ∑_k |A_i_k|)`，则

       ∑_j |degNorm A i j| ≤ 1,      故 |msgPass (degNorm A) h i| ≤ M

   —— **归一化后聚合是 1-Lipschitz 的非放大算子**，这是 GNN 稳定性的关键结构性事实
   （对应图卷积里用 `1/deg` 或对称归一化的动机，`1 +` 是为空图/零度顶点防除零）。

## 诚实边界（未做/未证，明确标注）

- **置换等变性的完整群论证明未做**：完整陈述需要 `Equiv.Perm ι` 对 `A` 的共轭作用
  `A ↦ P A Pᵀ` 与 `h ↦ h ∘ P⁻¹` 下 `msgPass` 的等变性；本文件只提供逐点界与归一化结构，
  等变性标注为后续。
- **全局图的收敛性/表达能力（WL 上界、过平滑极限）未做**：不涉及多层堆叠的渐近分析。
- 全部为有限维有限和代数，无拓扑/测度假设。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## 一、定义：邻接、一跳聚合、GNN 层 -/

/-- 邻接/边权读出：`adj E i j = E i j`。 -/
def adj (E : ι → ι → ℝ) (i j : ι) : ℝ := E i j

/-- 一跳消息传递（邻接加权聚合）：`msgPass A h i = ∑_j A_i_j · h_j`。 -/
def msgPass (A : ι → ι → ℝ) (h : ι → ℝ) (i : ι) : ℝ := ∑ j, A i j * h j

/-- GNN 一层：`σ (W · msgPass A h i)`（线性变换 + 逐点非线性）。 -/
def gnnLayer (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ) (h : ι → ℝ) (i : ι) : ℝ :=
  σ (W * msgPass A h i)

/-- 度归一化邻接：`degNorm A i j = A_i_j / (1 + ∑_k |A_i_k|)`。 -/
def degNorm (A : ι → ι → ℝ) (i j : ι) : ℝ := A i j / (1 + ∑ k, |A i k|)

/-! ## 二、聚合有界：放大倍数 = 加权度 -/

/-- **聚合有界**：`∀j, |h_j| ≤ M` ⟹ `|msgPass A h i| ≤ M · ∑_j |A_i_j|`。 -/
theorem msgPass_bound (A : ι → ι → ℝ) (h : ι → ℝ) (M : ℝ) (i : ι)
    (hM : ∀ j, |h j| ≤ M) :
    |msgPass A h i| ≤ M * ∑ j, |A i j| := by
  unfold msgPass
  calc
    |∑ j, A i j * h j| ≤ ∑ j, |A i j * h j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |h j| := Finset.sum_congr rfl (fun j _ => by rw [abs_mul])
    _ ≤ ∑ j, |A i j| * M :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hM j) (abs_nonneg _))
    _ = (∑ j, |A i j|) * M := by rw [Finset.sum_mul]
    _ = M * ∑ j, |A i j| := by ring

/-! ## 三、聚合 Lipschitz：敏感度 = 加权度 -/

/-- **聚合 Lipschitz**：`∀j, |h_j − h'_j| ≤ δ` ⟹
    `|msgPass A h i − msgPass A h' i| ≤ δ · ∑_j |A_i_j|`。 -/
theorem msgPass_lipschitz (A : ι → ι → ℝ) (h h' : ι → ℝ) (δ : ℝ) (i : ι)
    (hδ : ∀ j, |h j - h' j| ≤ δ) :
    |msgPass A h i - msgPass A h' i| ≤ δ * ∑ j, |A i j| := by
  have hval : msgPass A h i - msgPass A h' i = ∑ j, A i j * (h j - h' j) := by
    unfold msgPass
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hval]
  calc
    |∑ j, A i j * (h j - h' j)| ≤ ∑ j, |A i j * (h j - h' j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |h j - h' j| := Finset.sum_congr rfl (fun j _ => by rw [abs_mul])
    _ ≤ ∑ j, |A i j| * δ :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hδ j) (abs_nonneg _))
    _ = (∑ j, |A i j|) * δ := by rw [Finset.sum_mul]
    _ = δ * ∑ j, |A i j| := by ring

/-! ## 四、一层 Lipschitz（激活 L-Lipschitz + 线性 W） -/

/-- **GNN 一层 Lipschitz**：`σ` 是 L-Lipschitz（`0 ≤ L`）⟹
    `|gnnLayer A W σ h i − gnnLayer A W σ h' i| ≤ L·|W|·δ·∑_j |A_i_j|`。 -/
theorem gnnLayer_lipschitz (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ) (L δ : ℝ)
    (h h' : ι → ℝ) (i : ι) (hL : 0 ≤ L)
    (hσ : ∀ a b : ℝ, |σ a - σ b| ≤ L * |a - b|)
    (hδ : ∀ j, |h j - h' j| ≤ δ) :
    |gnnLayer A W σ h i - gnnLayer A W σ h' i| ≤ L * |W| * δ * ∑ j, |A i j| := by
  have hmp := msgPass_lipschitz A h h' δ i hδ
  have harg : |W * msgPass A h i - W * msgPass A h' i|
      = |W| * |msgPass A h i - msgPass A h' i| := by
    rw [← mul_sub, abs_mul]
  unfold gnnLayer
  calc
    |σ (W * msgPass A h i) - σ (W * msgPass A h' i)|
        ≤ L * |W * msgPass A h i - W * msgPass A h' i| := hσ _ _
    _ = L * (|W| * |msgPass A h i - msgPass A h' i|) := by rw [harg]
    _ ≤ L * (|W| * (δ * ∑ j, |A i j|)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmp (abs_nonneg W)) hL
    _ = L * |W| * δ * ∑ j, |A i j| := by ring

/-! ## 五、两跳消息传递：展开式与界 -/

/-- **两跳展开**：`msgPass A (fun i => msgPass A h i) k = ∑_j A_k_j · (∑_i A_j_i · h_i)`。 -/
theorem two_hop_msg (A : ι → ι → ℝ) (h : ι → ℝ) (k : ι) :
    msgPass A (fun i => msgPass A h i) k = ∑ j, A k j * (∑ i, A j i * h i) := by
  simp only [msgPass]

/-- **两跳界**：`∀i, |h_i| ≤ M` ⟹
    `|msgPass A (msgPass A h) k| ≤ (∑_j |A_k_j| · ∑_i |A_j_i|) · M`
    （界 = 两跳路径权重和 × M）。 -/
theorem twoHopMsg_bound (A : ι → ι → ℝ) (h : ι → ℝ) (M : ℝ) (k : ι)
    (hM : ∀ i, |h i| ≤ M) :
    |msgPass A (fun i => msgPass A h i) k| ≤ (∑ j, |A k j| * (∑ i, |A j i|)) * M := by
  rw [two_hop_msg]
  calc
    |∑ j, A k j * (∑ i, A j i * h i)| ≤ ∑ j, |A k j * (∑ i, A j i * h i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A k j| * |∑ i, A j i * h i| :=
      Finset.sum_congr rfl (fun j _ => by rw [abs_mul])
    _ ≤ ∑ j, |A k j| * (M * ∑ i, |A j i|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (by simpa [msgPass] using msgPass_bound A h M j hM)
        (abs_nonneg _)
    _ = (∑ j, |A k j| * (∑ i, |A j i|)) * M := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)

/-! ## 六、度归一化：聚合不放大（GNN 稳定性的结构性事实） -/

/-- **归一化后行绝对值和 ≤ 1**：`∑_j |degNorm A i j| ≤ 1`。 -/
theorem degNorm_sum_abs_le_one (A : ι → ι → ℝ) (i : ι) :
    ∑ j, |degNorm A i j| ≤ 1 := by
  have hden : 0 < 1 + ∑ k, |A i k| := by
    have hnn : 0 ≤ ∑ k, |A i k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
    linarith
  have hsum : ∑ j, |degNorm A i j| = (∑ j, |A i j|) / (1 + ∑ k, |A i k|) := by
    calc
      ∑ j, |degNorm A i j| = ∑ j, |A i j| / (1 + ∑ k, |A i k|) := by
        apply Finset.sum_congr rfl
        intro j _
        unfold degNorm
        rw [abs_div, abs_of_pos hden]
      _ = (∑ j, |A i j|) / (1 + ∑ k, |A i k|) := by rw [Finset.sum_div]
  rw [hsum]
  rw [div_le_one hden]
  linarith

/-- **归一化聚合不放大**：`∀j, |h_j| ≤ M`、`0 ≤ M` ⟹ `|msgPass (degNorm A) h i| ≤ M`。 -/
theorem degNorm_msgPass_bound (A : ι → ι → ℝ) (h : ι → ℝ) (M : ℝ) (i : ι)
    (hM : ∀ j, |h j| ≤ M) (hM0 : 0 ≤ M) :
    |msgPass (degNorm A) h i| ≤ M := by
  have h1 := msgPass_bound (degNorm A) h M i hM
  have h2 : ∑ j, |degNorm A i j| ≤ 1 := degNorm_sum_abs_le_one A i
  have h3 : M * ∑ j, |degNorm A i j| ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hM0
  linarith

/-- 归一化聚合的 Lipschitz 版：扰动 ≤ δ ⟹ `|msgPass (degNorm A) h i − msgPass (degNorm A) h' i| ≤ δ`。 -/
theorem degNorm_msgPass_lipschitz (A : ι → ι → ℝ) (h h' : ι → ℝ) (δ : ℝ) (i : ι)
    (hδ : ∀ j, |h j - h' j| ≤ δ) :
    |msgPass (degNorm A) h i - msgPass (degNorm A) h' i| ≤ δ := by
  have h1 := msgPass_lipschitz (degNorm A) h h' δ i hδ
  have h2 : ∑ j, |degNorm A i j| ≤ 1 := degNorm_sum_abs_le_one A i
  have h3 : δ * ∑ j, |degNorm A i j| ≤ δ * 1 :=
    mul_le_mul_of_nonneg_left h2 (le_trans (abs_nonneg (h i - h' i)) (hδ i))
  linarith

/-! ## 注：闭环语义
  邻接（adj）→ 一跳聚合（msgPass）→ 有界/ Lipschitz（msgPass_bound / msgPass_lipschitz）→
  一层 Lipschitz（gnnLayer_lipschitz）→ 两跳展开与界（two_hop_msg / twoHopMsg_bound）→
  度归一化（degNorm）→ 非放大（degNorm_sum_abs_le_one / degNorm_msgPass_bound）。
  诚实标注：置换等变性的完整群论证明未做；全局收敛性/表达能力未做。 -/

end Lattice
