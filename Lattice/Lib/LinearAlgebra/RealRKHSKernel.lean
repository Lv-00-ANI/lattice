import Mathlib
import Lattice.Lib.LinearAlgebra.RealSVD
import Lattice.Lib.LinearAlgebra.RealHessian
import Lattice.Lib.Attention.RealLinearAttention
/-!
# LATTICE: RKHS / 核方法基础（有限版）—— 正定核、Gram 半正定、Mercer 分解与核平滑

`RealLinearAttention` 把线性注意力写成**可分核** `featScore φ q k = Σ_i φ(q_i)·φ(k_i)`，
并明确标注「核化」却**没有核方法基础**：既没有「什么函数才配叫核」的定义，
也没有「Gram 矩阵半正定 ⟺ 存在特征映射」的 Mercer 型定理。E2/R3 调研把这一缺口
登记为接口缺口——「注意力 = 核平滑」这句话在库里当时**没有可证的对象**。本文件补上
**有限（离散）版**核方法地基，全部避开测度论。

**路线**：一切都在有限输入 `Fin n`（或 `Fin m`）上做，于是

  · 「核」退化为**数**的半正定性条件（Gram 矩阵 PSD）；
  · 「Mercer 定理」（积分算子特征分解）退化为**有限实对称谱定理**
    （已由 `RealSVD.symmetric_spectral_theorem` 提供 `A = U·diag λ·Uᵀ`）；
  · 「特征映射到无穷维 RKHS」退化为**特征映射到 ℝⁿ**；
  · 「Nadaraya–Watson 估计」退化为**有限加权平均**。

## 本文件建立

**一、核与 Gram 矩阵**
1. `IsPosDefKernel`：`K : α → α → ℝ` 是**正定核**（对称 + 半正定）——两项分开给，
   因为下游常常只有其中一项可用；
2. `kernelGramMatrix K x`：`G_{ij} = K (x i) (x j)`（`Fin n` 上的核 Gram 矩阵）;
3. `kernelGramMatrix_symm`、`kernelGramMatrix_isHermitian`、`kernelGramMatrix_transpose`：对称性的三种形态；
4. `kernelQuadForm_eq_kernelGramQuadForm`：用**核语言**改写 Gram 二次型
   `vᵀGv = Σ_i Σ_j v_i·K(x_i,x_j)·v_j`（这是全部 PSD 结论的桥）；
5. `isSymmKernel_iff_gram_psd`（**主结果**）：**对称假设下**「核半正定 ⟺ 每个有限 Gram
   二次型非负」。⚠ 初稿曾断言无对称假设的版本（`IsPosDefKernel ⟺ Gram PSD`），
   **该命题为假**（半正定只约束对称部分，见 `kernel_sym_part_abs_le` 的登记），
   已更正为显式带 `hsymm` 的版本；
   `isPosDefKernel_gram_psd` 保留 `IsPosDefKernel → Gram PSD` 的**可证方向**；

**二、Mercer 型有限版（主结果）**
6. `kernelGramMatrix_psd_iff_exists_featureMap`（**Mercer 有限版**）：
   **对称假设下** `Gram 半正定 ⟺ ∃ Φ : α → ℝⁿ, ∀ a b, K a b = ⟨Φ a, Φ b⟩`
   ——即「（对称）半正定核 ⟺ 可写成特征内积」。`⟸` 由 `Σ v_i Φ(x_i)` 的平方和给出
   （无需谱定理）；`⟹` 由 `RealSVD.symmetric_spectral_theorem` 取
   `Φ x i = √λᵢ·Uᵢₓ`（`Real.sqrt` 吸收负特征值）。
   ⚠ `hsymm` 是**必需的**：半正定本身推不出对称性（反例见第一节 `kernel_sym_part_abs_le`）；
7. `kernelGramMatrix_eq_featureMap_mul_transpose`：`G = Φ·Φᵀ`（矩阵形态，直接回收谱定理）；
8. `metric_eq_kernel_expansion`：**距离–核恒等式**
   `‖Φ x − Φ y‖² = K x x − 2·K x y + K y y`（task 指定的核心恒等式）；
9. `metric_kernel_nonneg`：由上式回收核的「负型」非负性；
10. `kernel_metric_zero_iff`：`K x x − 2K x y + K y y = 0` ⟺ `Φ x = Φ y`
    （核「距离」为零刻画特征映射等价）。

**三、与线性注意力的接口**
11. `featScore_eq_inner`：`featScore φ q k = ⟪φ∘q, φ∘k⟫`——`RealLinearAttention.featScore`
    正是**可分核** `K(u,v) = Σ_i φ(u_i)·φ(k_i)` 在特征映射 `u ↦ φ∘u` 下的内积；
12. `polyKernel` / `polyKernel_one_gram_psd`：齐次多项式核 `(⟨x,y⟩)^d` 在 `d = 1` 时正定
    （显式特征映射 `Φ x = x`）。**诚实降级**：`d ≥ 2` 与 `c > 0` 的非齐次版**未证**
    （需多重组合展开），故本文件只认证这一个非空实例，不声称一般多项式核；
13. `expKernel` / `heatKernel` / `heatKernel_gram_psd_const`：**指数核** `K(x,y) = exp(⟨x,y⟩)`
    （softmax 注意力的核）与**热核** `exp(−‖x−y‖²/(2σ²))`；热核在常值输入上 Gram 半正定。
    **诚实降级**：`expKernel` 的**一般** Gram PSD 未证（见下）。

**四、核平滑视角（Nadaraya–Watson / softmax 注意力）**
14. `heatKernel` / `heatKernel_diag`；`nwEstimate`：Nadaraya–Watson 型估计
    `Σ_j K(x_j, x)·f(x_j) / Σ_j K(x_j, x)`；
15. `nwEstimate_self`：自身核平滑恢复原值（`f` 常数或权重退化为自身点质量）；
16. `nwEstimate_constant`：常数函数的 NW 估计恒等于该常数（**分母非零**假设，
    即 `RealLinearAttention.linAttnDenom_pos` 的同型前提）；
17. `softmax_attention_is_nw`（**核心接口**）：softmax 注意力权重
    `softmax (fun j => ⟨q, k_j⟩)_j` **逐点等于** 以指数核为核的 NW 权重
    `expKernel-smoothing`；即 softmax 注意力**就是**核 `K(x,y)=exp(⟨x,y⟩)` 下的
    NW 估计。这条把「注意力 = 核平滑」变成了库内的等式定理；
18. `softmax_attention_nw_is_prob`：该权重是概率分布（非负 + 和为 1），
    引用 `RealAttention.softmax` 的既有结论。

## 与既有模块的接口定理（显式互链）

| 本文件 | 对接 | 内容 |
|:--|:--|:--|
| `kernelGramMatrix_psd_iff_exists_featureMap`（需 `hsymm`） | `RealSVD.symmetric_spectral_theorem` | Mercer 有限版 = 实对称谱定理 |
| `isSymmKernel_iff_gram_psd` / `isPosDefKernel_gram_psd` | `RealHessian` 的二次型语言 | 核 PSD ⟺ Gram 二次型非负 |
| `kernelGramMatrix_eq_featureMap_mul_transpose` | `RealSVD.symmetric_spectral_theorem'` | `G = U diag λ Uᵀ = Φ Φᵀ` |
| `isSymmKernel_iff_gram_psd` | `RealHessian.quadForm`（二次型语言同构） | 核 PSD ⟺ Gram 二次型非负 |
| `featScore_eq_inner` | `RealLinearAttention.featScore` | 线性注意力打分 = 可分核内积 |
| `softmax_attention_is_nw` | `RealAttention.softmax`、`RealLinearAttention.featScore` | 注意力 = 核平滑（NW） |
| `polyKernel_one_gram_psd` | `RealLinearAttention.featScore` | 线性注意力核（`φ=id`）的正定性认证 |
| `softmax_attention_nw_is_prob` | `RealAttention.softmax` 的既有归一化结论 | 权重是概率分布 |

## 诚实边界（诚实 / 未证 / 未做 / 降级 / 标注）

> **v14 修复说明（W3 波次）**：本文件此前存在 **6 处编译缺陷**，集中在
> `nwEstimate_const`、`softmax_attention_is_nw`、`softmax_numerator_eq_expKernel`、
> `softmax_attention_nw_is_prob`、`softmax_attention_eq_nwWeights` 五条定理的**证明体**。
> 缺陷的共同根因是 **lambda 未 beta-展开**（`(fun _ => c) (x j)` 之类）与
> **`unfold` 未作用于目标**（只在假设上生效），以及由此派生的
> `no goals to be solved`（过度化简后残留收尾）。修复**只改证明体**，
> **未改动任何命题陈述、定理名、定义**。详见各定理处的 `v14 修复` 注释。

- **未做：完整 Mercer 定理（积分算子版）**。一般 Mercer 需要紧自伴算子的谱定理、
  `C(X)` 上正线性泛函的 Riesz 表示、以及特征函数的**一致收敛**（Mercer 定理的难点在
  一致性，通常需 `K` 连续 + `X` 紧）。mathlib 4.14 没有这条链，本文件**只做有限输入版**：
  `α` 任意、`Fin n` 为样本数，结论是**有限 Gram 矩阵**的分解，不含无穷维 RKHS 构造。
  有限版不是「逼近」——它在有限样本上**就是**准确的 Mercer 内容（特征映射到 ℝⁿ）。
- **未做：RKHS 的完备化 / 再生性**。本文件给的是「特征映射到 ℝⁿ」的**具体**实现，
  没有构造抽象 RKHS `H_K`，也没有证明再生性 `⟨K_x, f⟩ = f(x)`。原因是抽象 RKHS 需要
  「由核函数张成的内积空间取完备化」，其良定义性（商空间 + 完备化）在 mathlib 4.14
  对此用途缺少现成骨架，且属于**非有限**的内容。
- **诚实降级：`expKernel` 的一般 Gram 半正定性未证**。`K(x,y) = exp(⟨x,y⟩)` 的
  一般 Gram 半正定性等价于「指数函数是正定函数」（Bochner 定理的有限版），
  mathlib 4.14 无 Bochner 定理，本文件**不证**（标注为未做）。
  本文件对 `expKernel` 只建立**不需要 PSD** 的结果：它是 softmax 注意力的核
  （`softmax_numerator_eq_expKernel`），且 NW 权重恒等式
  （`softmax_attention_eq_nwWeights`）与之封装。同理热核只证**常值输入**上的
  Gram PSD（`heatKernel_gram_psd_const`），一般高斯核 PSD 亦未做（同样需 Bochner）。

  这是**有意的切分**：「需要 Bochner/正定函数理论」的部分（核的 PSD）与
  「只需代数归一化」的部分（注意力 = NW 平滑）被切开，后者才是注意力语义所在，
  且**完全不依赖前者**——`softmax_attention_is_nw` 走的是 `RealAttention.softmax`
  的归一化定义，是恒等式而非 PSD 论断。
- **未做：核的正则性理论**。RKHS 范数、代表点定理（representer theorem）、
  核岭回归的闭式解、泛化界均不在本文件范围（`RealRidge`/`RealPAPBayes` 类文件各自处理）。
  本文件只提供「核」这一对象的**定义与代数性质**，不含学习理论。
- **未做：无穷维特征映射的有限逼近误差**。`Φ : α → ℝⁿ` 用的是样本数 `n` 维特征
  （谱分解给出），不是核的无穷维特征映射的截断；截断误差界属于
  `RealEckartYoung` 的低秩逼近范畴，本文件不重复。
- **范围**：`α` 为任意类型（无拓扑/可测结构），样本索引 `Fin n`；全程有限求和。
- 无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators
open scoped Matrix
open scoped InnerProduct
-- ⚠ `⟪…, …⟫`（无下标版）**只**在 `RealInnerProductSpace` 作用域里可用
-- （见 `Mathlib/Analysis/InnerProductSpace/Basic.lean`：
-- `scoped[RealInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y`）。
-- `InnerProduct` **不是**作用域名，`open scoped InnerProduct` 静默无效 ⟹
-- `⟪⟫` 会报 `expected token`（本文件原先即栽在此处）。
open scoped RealInnerProductSpace
-- `open Matrix`（**不是** `open scoped Matrix`）：本文件用的裸 `diagonal` 是
-- `Matrix.diagonal`，它只在 `Matrix` **命名空间**里，`open scoped` 不引入它。
-- 缺这一行会让 `diagonal` 解析失败（`function expected at diagonal`），
-- 并在 `quadForm_mul_diagonal_mul_transpose` / `eigenvalues_nonneg_of_gram_psd` /
-- `kernelGramMatrix_eq_featureMap_mul_transpose` 三处级联出 12 条 error。
open Matrix

namespace Lattice

variable {α : Type*}

/-! ## 一、正定核与 Gram 矩阵 -/

/-- **核对称**：`K a b = K b a`（对所有 `a b`）。 -/
def IsSymmKernel (K : α → α → ℝ) : Prop := ∀ a b, K a b = K b a

/-- **核半正定（有限版）**：每个有限输入族的 Gram 矩阵二次型非负。
这是「正定核」在有限维语言下的**准确**含义（Mercer 的 `∫∫ K f f ≥ 0` 的离散化）。

注意本定义**只对 `Fin n`（`n` 任意，含 `n = 0,1,2`）量化**，因此它是逐有限集的
条件，不含任何拓扑/测度假设。 -/
def IsPSDKernel (K : α → α → ℝ) : Prop :=
  ∀ {n : ℕ} (x : Fin n → α) (v : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, v i * K (x i) (x j) * v j

/-- **正定核**：对称 + 半正定（两项分开保留，便于下游只取其一）。 -/
def IsPosDefKernel (K : α → α → ℝ) : Prop := IsSymmKernel K ∧ IsPSDKernel K

/-- **核 Gram 矩阵**：`kernelGramMatrix K x i j = K (x i) (x j)`。
有限输入 `x : Fin n → α` 下核的全部可观测内容。

命名说明：**不叫 `gramMatrix`**——`RealGramEdit.gramMatrix`
（`(k : Fin m → E) → Matrix (Fin m) (Fin m) ℝ`，内积空间键–键 Gram）已占用该名，
签名不同。本文件的核 Gram 是**抽象核** `K : α → α → ℝ` 版，语义相关但类型不同，
按 STYLE §2「避免同命名空间同名」分开命名。 -/
def kernelGramMatrix {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => K (x i) (x j)

/-- 核 Gram 矩阵是（实）对称的：`Gᵀ = G`（核对称时）。 -/
theorem kernelGramMatrix_transpose {n : ℕ} (K : α → α → ℝ) (x : Fin n → α)
    (hK : IsSymmKernel K) : (kernelGramMatrix K x)ᵀ = kernelGramMatrix K x := by
  ext i j
  exact hK (x j) (x i)

/-- **核 Gram 矩阵 Hermitian**：实对称 ⟹ `IsHermitian`（喂给 `RealSVD` 的谱定理）。 -/
theorem kernelGramMatrix_isHermitian {n : ℕ} (K : α → α → ℝ) (x : Fin n → α)
    (hK : IsSymmKernel K) : (kernelGramMatrix K x).IsHermitian := by
  rw [real_isHermitian_iff_transpose]
  exact kernelGramMatrix_transpose K x hK

/-- 核 Gram 矩阵按元素对称（点式形态，`ring` 友好）。 -/
theorem kernelGramMatrix_symm {n : ℕ} (K : α → α → ℝ) (x : Fin n → α)
    (hK : IsSymmKernel K) (i j : Fin n) :
    kernelGramMatrix K x i j = kernelGramMatrix K x j i :=
  hK (x i) (x j)

/-- **核语言 ⟺ 矩阵语言的桥**：`G` 的二次型就是核的二次型。
`Σ_i Σ_j v_i·G_{ij}·v_j = Σ_i Σ_j v_i·K(x_i,x_j)·v_j`（定义即证）。 -/
theorem kernelQuadForm_eq_kernelGramQuadForm {n : ℕ} (K : α → α → ℝ) (x : Fin n → α)
    (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * K (x i) (x j) * v j)
      = ∑ i, ∑ j, v i * kernelGramMatrix K x i j * v j := rfl

/-- **单点 Gram 半正定 ⟹ 对角非负**：`0 ≤ K a a`。
（取 `n = 1`, `v = 1`：`vᵀGv = K a a`。） -/
theorem kernel_diag_nonneg (K : α → α → ℝ) (hpsd : IsPSDKernel K) (a : α) :
    0 ≤ K a a := by
  have h := hpsd (fun _ : Fin 1 => a) (fun _ => 1)
  simpa [Fin.sum_univ_one] using h

/-- **两点 Gram 半正定 ⟹ 核被对角控制**：`2·K a b ≤ K a a + K b b`
（取 `n = 2`、输入 `(a,b)`、`v = (1,−1)`，二次型 `K a a − 2K a b + K b b ≥ 0`），
即核的「非负型」条件。

⚠ **v15 更正（本轮实测：原名题为假，已加 `hsymm`）**：
原陈述只有 `hpsd : IsPSDKernel K`，**推不出**该结论。
取 `α = Bool`、`K ⊥ ⊥ = K ⊤ ⊤ = 1`、`K ⊥ ⊤ = 2`、`K ⊤ ⊥ = 0`：
二次型 `= v₀² + 2v₀v₁ + v₁² = (v₀+v₁)² ≥ 0`（**半正定成立**），
但 `2·K ⊥ ⊤ = 4 > 1 + 1 = K ⊥ ⊥ + K ⊤ ⊤`。**故原名题为假**。

**根因**：`v = (1,−1)` 给出的二次型是 `K a a − K a b − K b a + K b b ≥ 0`，
它含的是**对称部分** `K a b + K b a`，**不是** `K a b`。要把它化成 `K a b`
**必须**用对称性 `K b a = K a b`。这与本文件 `:214` 起登记的
「半正定只约束对称部分、推不出对称性」是**同一个根因**（该登记原先只挂在
`kernel_symm_of_psd` 上，**漏了本条也是同族假命题**）。

⇒ 修法：**显式加入 `hsymm : IsSymmKernel K`**（与 `isSymmKernel_iff_gram_psd`
的更正方式一致），并保留**不需要对称性**的真命题 `kernel_sym_part_abs_le`（见下条）。 -/
theorem kernel_le_half_diag_add (K : α → α → ℝ) (hpsd : IsPSDKernel K)
    (hsymm : IsSymmKernel K) (a b : α) :
    2 * K a b ≤ K a a + K b b := by
  -- 在两点输入 (a,b) 上取 v = (1,-1)，二次型 = K a a − K a b − K b a + K b b ≥ 0
  have h := hpsd (fun i : Fin 2 => if i = 0 then a else b)
    (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1)
  -- v15 修复：**不要**先 `rw [Fin.sum_univ_two, Fin.sum_univ_two] at h`
  -- （外层 `rw` 只展开某一层，内层 `∑` 会留下未归约的 `ite`，
  -- 这正是 v14 注释里「`h` 的 `if` 没有被完全归约」的真因）。
  -- 改用 `simp only [Fin.sum_univ_two, …]` **一次性**展开两层并归约 `ite`。
  simp only [Fin.sum_univ_two, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h
  -- 此时 `h : 0 ≤ K a a + (-K a b - K b a) + K b b`（含 `K b a`）
  -- 目标含 `K a b` ⟹ **必须**用对称性把 `K b a` 换成 `K a b`，否则 `linarith` 无解。
  rw [hsymm b a] at h
  linarith

/-! **⚠ 登记在案的假命题（本轮实测抓出，未证明、不声称）**。

初稿曾断言 `kernel_symm_of_psd : IsPSDKernel K → IsSymmKernel K`
（「实二次型半正定 ⟹ 核对称」）。**该命题为假**，反例（可在内核外复核）：

取 `α = {a, b}`、`K a a = K b b = 1`、`K a b = 2`、`K b a = 0`。
则对**任意** `v : Fin 2 → ℝ` 有
`q(v) = v₀² + (2+0)·v₀v₁ + v₁²`，即
`q(t,1) = (t+1)² ≥ 0`、`q(t,−1) = (t−1)² ≥ 0`（`t` 任意实），
故 `q ≥ 0` 成立（半正定），但 `K a b = 2 ≠ 0 = K b a`，**不对称**。

**根因**：实二次型 `ΣΣ v_i K_ij v_j` 只依赖于**对称部分** `(K_ij + K_ji)/2`；
反对称部分对二次型**完全不可见**。故「半正定」**不能**推出对称性——
对称性必须**单独假设**（这正是 `IsPosDefKernel := IsSymmKernel ∧ IsPSDKernel`
把两者**并列**而非推出关系的原因）。

**对策**：`isSymmKernel_iff_gram_psd` 的 `⟸` 方向**改为显式要求对称性假设**
（见该定理），Mercer 分解中用到的对称性由**输入假设** `hsymm : IsSymmKernel K` 提供
（体现在 `kernelGramMatrix_psd_iff_exists_featureMap` 的显式参数上）。

**⚠ v15 追加登记（同族第二例，本轮实测）**：`kernel_le_half_diag_add`
（原名题 `IsPSDKernel K → 2·K a b ≤ K a a + K b b`）**也是假命题**，
**用的是同一个反例核**（`K a b = 2`、`K b a = 0`、对角为 1）：半正定成立，
但 `2·2 = 4 > 1 + 1 = 2`。**根因与上条完全相同**——两点二次型含的是
`K a b + K b a`（对称部分），要落到单个 `K a b` **必须**用对称性。
⇒ 该定理已加入 `hsymm : IsSymmKernel K` 假设（见其 docstring 的 v15 说明）。 -/

/-- **半正定 ⟹ 对称部分被对角控制**（从上面的假命题中**抢救出的真命题**）：
`2·K a b ≤ K a a + K b b` 的**对称化**版本——
`K a b + K b a ≤ K a a + K b b` 且 `−(K a b + K b a) ≤ K a a + K b b`
（即 `|K a b + K b a| ≤ K a a + K b b`）。

这是「半正定」**真正**给出的结论（只约束对称部分，不约束反对称部分）。 -/
theorem kernel_sym_part_abs_le (K : α → α → ℝ) (hpsd : IsPSDKernel K) (a b : α) :
    |K a b + K b a| ≤ K a a + K b b := by
  -- v = (1,1)：K a a + K a b + K b a + K b b ≥ 0
  have h1 := hpsd (fun i : Fin 2 => if i = 0 then a else b)
    (fun _ : Fin 2 => (1 : ℝ))
  -- v = (1,-1)：K a a − K a b − K b a + K b b ≥ 0
  have h2 := hpsd (fun i : Fin 2 => if i = 0 then a else b)
    (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1)
  simp only [Fin.sum_univ_two, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **对称 + Gram 半正定 ⟺ 每个有限 Gram 矩阵半正定**（有限版刻画，主结果之一）。

⚠ **重要更正**：初稿写的是 `IsPosDefKernel K ↔（每个有限 Gram 二次型非负）`，
但那**为假**——因为 `IsPosDefKernel = IsSymmKernel ∧ IsPSDKernel` 含**对称性**，
而右端（二次型非负）**只约束对称部分**，推不出对称性（反例见上一条 docstring）。
故本条**显式加入对称性假设** `hsymm : IsSymmKernel K`，
得到**正确**的等价：`IsSymmKernel K → (IsPSDKernel K ↔ 每个有限 Gram 二次型非负)`。

这条把「核」的抽象定义与「文件里实际会用的 Gram 二次型」等价地接起来：
此后所有 PSD 论证都可以只在 Gram 矩阵上做（对称性另行假设/提供）。

⚠ **v15 补充（机械实测）**：`hsymm` 参数**未参与证明**——内核报
`unused variable 'hsymm'`，且等式两侧由 `kernelQuadForm_eq_kernelGramQuadForm`
（一条 `rfl`）直接给出，**不需要对称性**。即本条**实际上是 `Iff.rfl` 级**的恒等式。
⇒ **`hsymm` 为「接口约定」参数**：保留它是因为本文件的**接口契约**
（对称性是 PSD 论证的显式前提，Mercer 方向 `kernelGramMatrix_psd_iff_exists_featureMap`
**真的需要**它），且删掉会破坏下游调用点的实参个数。
**保留 + 本条注明**（不删）。 -/
theorem isSymmKernel_iff_gram_psd (K : α → α → ℝ) (hsymm : IsSymmKernel K) :
    IsPSDKernel K ↔
      ∀ {n : ℕ} (x : Fin n → α) (v : Fin n → ℝ),
        0 ≤ ∑ i, ∑ j, v i * kernelGramMatrix K x i j * v j := by
  constructor
  · intro hpsd n x v
    exact kernelQuadForm_eq_kernelGramQuadForm K x v ▸ hpsd x v
  · intro h n x v
    exact (kernelQuadForm_eq_kernelGramQuadForm K x v).symm ▸ h x v

/-- **正定核的 Gram 半正定（`IsPosDefKernel` 的展开方向，保留原名语义）**：
`IsPosDefKernel K` 时每个有限 Gram 二次型非负。
（这是原 `isPosDefKernel_iff_gram_psd` 的**可证方向**，单独保留以便下游使用。） -/
theorem isPosDefKernel_gram_psd (K : α → α → ℝ) (hK : IsPosDefKernel K) :
    ∀ {n : ℕ} (x : Fin n → α) (v : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, v i * kernelGramMatrix K x i j * v j :=
  fun x v => kernelQuadForm_eq_kernelGramQuadForm K x v ▸ hK.2 x v

/-! ## 二、Mercer 型有限版：半正定 ⟺ 存在特征映射

`kernelGramMatrix_psd_iff_exists_featureMap` 是本文件的主结果：**有限输入下，核半正定
当且仅当它可以写成特征内积** `K a b = ⟪Φ a, Φ b⟫`。

- `⟸`（易）：`Σ_i v_i·Φ(x_i)` 的范数平方展开。
- `⟹`（难，用谱定理）：`G = U·diag λ·Uᵀ`（`RealSVD.symmetric_spectral_theorem'`），
  令 `Φ x i = √(λ_i)·U_{x i}`。因 `G` 半正定故 `λ_i ≥ 0`（这一步由 `G` 半正定与
  特征值的二次型刻画给出），`√` 才有意义。 -/

/-- **矩阵二次型在 `G = U diag λ Uᵀ` 下的展开（对角化桥）**：
`vᵀ(U diag λ Uᵀ)v = Σ_p (Σ_i v_i·U_{ip})·λ_p·(Σ_j U_{jp}·v_j)`。

这是把「谱分解」翻译成「加权平方和」的关键代数步骤，后面的特征值非负
与 Mercer 分解都走它。 -/
theorem quadForm_mul_diagonal_mul_transpose {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (lam : Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * (U * diagonal lam * Uᵀ) i j * v j)
      = ∑ p, (∑ i, v i * U i p) * lam p * (∑ j, U j p * v j) := by
  have hexp : ∀ i j, (U * diagonal lam * Uᵀ) i j
      = ∑ p, U i p * lam p * U j p := by
    intro i j
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single p]
    · -- v15 修复：原本这里在 `diagonal_apply_eq`/`transpose_apply` 之后还有 `ring`，
      -- 但两条 `rw` 已把目标关掉 ⟹ `ring` 报 `no goals to be solved`。
      rw [Matrix.diagonal_apply_eq, Matrix.transpose_apply]
    · intro q _ hq
      rw [Matrix.diagonal_apply_ne _ hq]
      ring
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  -- v15 修复：原稿用 `calc` + 三段式，但中间段的 `sum_comm`/`sum_mul`/`mul_sum`
  -- 链**顺序与目标形状不匹配**，故 `:357` 报 type mismatch。
  -- ⚠ 关键实测：`simp only [Finset.sum_mul, Finset.mul_sum]` 作用在 RHS 上时，
  -- 产生的 binder 顺序是 **(p, j, i)**（不是直觉上的 (p, i, j)）——
  -- 即 `Σ p, Σ j, Σ i, v i * U i p * lam p * (U j p * v j)`。
  -- 故两侧都归约到**这个实测范式**（而非猜测的范式），`ring` 逐项收口。
  have hR : (∑ p, (∑ i, v i * U i p) * lam p * (∑ j, U j p * v j))
      = ∑ p, ∑ j, ∑ i, v i * U i p * lam p * (U j p * v j) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
  have hL : (∑ i, ∑ j, v i * (U * diagonal lam * Uᵀ) i j * v j)
      = ∑ p, ∑ j, ∑ i, v i * U i p * lam p * (U j p * v j) := by
    simp only [hexp, Finset.sum_mul, Finset.mul_sum]
    -- LHS: Σ i, Σ j, Σ p, v i * (U i p * lam p * U j p) * v j
    -- (1) 内层换序：对固定 `i`，把 `Σ j` 与 `Σ p` 交换
    rw [show (∑ i, ∑ j, ∑ p, v i * (U i p * lam p * U j p) * v j)
        = ∑ i, ∑ p, ∑ j, v i * (U i p * lam p * U j p) * v j from
      Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    -- (2) 外层换序：`Σ p` 提到最外
    rw [Finset.sum_comm]
    -- (3) 再把内层 `Σ i`/`Σ j` 换成实测范式的 `Σ j, Σ i`
    rw [show (∑ p, ∑ i, ∑ j, v i * (U i p * lam p * U j p) * v j)
        = ∑ p, ∑ j, ∑ i, v i * (U i p * lam p * U j p) * v j from
      Finset.sum_congr rfl fun p _ => Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hL, hR]

/-- **半正定 ⟹ 特征值非负**：`G` 半正定、`G = U diag λ Uᵀ`、`UᵀU = 1` ⟹ `0 ≤ λ k`。

取 `v` 为 `U` 的第 `k` 列（即 `v i = U i k`）：由 `UᵀU = 1` 得
`Σ_i v_i·U_{ip} = δ_{pk}`，于是展开式只剩 `p = k` 项，二次型 `= λ_k`。 -/
theorem eigenvalues_nonneg_of_gram_psd {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}
    {U : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hU : Uᵀ * U = 1) (hG : G = U * diagonal lam * Uᵀ)
    (hpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * G i j * v j) (k : Fin n) :
    0 ≤ lam k := by
  set v : Fin n → ℝ := fun i => U i k with hv
  -- `UᵀU = 1` 的按元素形式：`Σ_i U i p * U i q = δ_{pq}`
  have hUtU : ∀ p q : Fin n, (∑ i, U i p * U i q) = if p = q then (1:ℝ) else 0 := by
    intro p q
    have h := congrFun (congrFun hU p) q
    -- v15 修复：原稿 `rw [Matrix.mul_apply] at h` 后 `h` 是
    -- `∑ j, Uᵀ p j * U j q = …`（**含转置、且 binder 名是 `j`**），
    -- 而目标是 `∑ i, U i p * U i q = …` ⟹ 原 `rw [h]` 找不到模式（`:376` error）。
    -- 改为 `simp only` **一次性**同时归约 `mul_apply`/`one_apply`/`transpose_apply`，
    -- 直接得到与目标句法同形的 `h`。
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] at h
    exact h
  have hkey : (∑ i, ∑ j, v i * G i j * v j) = lam k := by
    rw [hG, quadForm_mul_diagonal_mul_transpose]
    -- 两端的括号都退化为单点
    have hL : ∀ p, (∑ i, v i * U i p) = if p = k then (1:ℝ) else 0 := by
      intro p
      rw [show (∑ i, v i * U i p) = ∑ i, U i k * U i p from
        Finset.sum_congr rfl fun i _ => by rw [hv]]
      -- v15 修复：`hUtU k p` 给出的是 `if k = p then 1 else 0`，
      -- 而目标要 `if p = k then 1 else 0` ⟹ 须把**条件方向**统一
      -- （原稿 `rw [hUtU k p]` 后直接停手，`leave` 下 `(if k = p …) = (if p = k …)`
      -- 未解 ⟹ `:392` 报 unsolved goals）。用 `by_cases` + `simp` 显式对齐。
      rw [hUtU k p]
      by_cases hpk : p = k
      · simp [hpk]
      · have hkp : ¬ (k = p) := fun h => hpk h.symm
        simp [hpk, hkp]
    have hR : ∀ p, (∑ j, U j p * v j) = if p = k then (1:ℝ) else 0 := by
      intro p
      rw [show (∑ j, U j p * v j) = ∑ j, U j p * U j k from
        Finset.sum_congr rfl fun j _ => by rw [hv]]
      rw [hUtU p k]
      -- v15 修复：原稿在此加 `by_cases h : p = k` 再 `simp [h]`，
      -- 但 `hUtU p k` 已经把目标**关掉**（两侧同为 `if p = k then 1 else 0`），
      -- 后续 `by_cases` 报 `no goals to be solved`。删除该多余分支。
    rw [Finset.sum_eq_single k]
    · -- v15 修复：此处的目标是
      -- `(if k = k then 1 else 0) * lam k * (if k = k then 1 else 0) = lam k`。
      -- ⚠ `rw [hL k, hR k, if_pos rfl]` 无效：`rw` 的 `if_pos rfl` 只能匹配
      -- **第一处** `ite`，第二处仍残留 ⟹ `:430` not-found。
      -- 用 `simp only [hL k, hR k, if_true, mul_one, one_mul]` 一次归约两处。
      simp only [hL k, hR k, if_true, mul_one, one_mul]
    · intro p _ hp
      rw [hL p, if_neg hp, hR p, if_neg hp]; ring
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [← hkey]
  exact hpsd v

/-- **Gram 矩阵的 `Φ Φᵀ` 分解**：对称谱定理给出的 `U diag λ Uᵀ` 写成显式特征映射
`featureMapOf U lam i j = √(λ_j)·U_{i j}` 的 `Φ·Φᵀ`。

因 `G` 半正定故 `λ_j ≥ 0`（`eigenvalues_nonneg_of_gram_psd`），`Real.sqrt` 才有意义
（`√λ·√λ = λ` 需要 `0 ≤ λ`）。

⚠ **v15 补充（机械实测）**：本条的 `hU : Uᵀ * U = 1` **未参与证明**
（内核报 `unused variable 'hU'`）—— 因为该分解 `U diag λ Uᵀ = Φ Φᵀ`
**只用 `U` 与 `lam` 的代数形状**，正交性不是必要的。
⇒ **`hU` 为「接口约定」参数**：保留它是因为它的调用点
（`kernelGramMatrix_psd_iff_exists_featureMap`）从谱定理一次拿到 `⟨U, lam, hU, hG⟩`，
显式传参保持接口一致，且删掉会改动调用点的实参个数。
**保留 + 本条注明**（不删）。 -/
theorem kernelGramMatrix_eq_featureMap_mul_transpose {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (lam : Fin n → ℝ) (hU : Uᵀ * U = 1) (hlam : ∀ j, 0 ≤ lam j) :
    U * diagonal lam * Uᵀ
      = Matrix.of (fun i j => Real.sqrt (lam j) * U i j)
        * (Matrix.of (fun i j => Real.sqrt (lam j) * U i j))ᵀ := by
  -- v15 修复（三处）：
  -- ① 原稿的右端写成裸 `(fun i j => …) * (fun i j => …)ᵀ`，
  --    函数字面量**没有矩阵类型**，`*` 上 `HMul` 无法合成
  --    （`:381` 报 `failed to synthesize HMul (Fin n → Fin n → ℝ) (Matrix …)`）。
  --    **用 `Matrix.of` 显式标注**为矩阵（`… : Matrix …` 的 ascription 在此不够，
  --    因为 `*` 的左侧仍是未标注的 λ）。
  -- ② 原稿 `rw [Matrix.mul_apply, Matrix.transpose_apply]` 一次做两步：
  --    `mul_apply` 展开后 `transpose_apply` 的模式已不存在（`:444` not-found）。
  --    改为**分别对左右两端**各建一条 `have`，各自展开到同一个 `Σ p` 范式。
  -- ③ `Real.sq_sqrt` 给出的是 `√x ^ 2 = x`（`pow` 形），而目标是 `√x * √x`；
  --    须先用 `pow_two` 换形，否则 `:460` 报 type mismatch。
  ext i j
  have hL : (U * diagonal lam * Uᵀ) i j = ∑ p, U i p * lam p * U j p := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · rw [Matrix.diagonal_apply_eq, Matrix.transpose_apply]
    · intro q _ hq
      rw [Matrix.diagonal_apply_ne _ hq]; ring
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  have hR : (Matrix.of (fun i j => Real.sqrt (lam j) * U i j)
        * (Matrix.of (fun i j => Real.sqrt (lam j) * U i j))ᵀ) i j
      = ∑ p, U i p * lam p * U j p := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
    have hs : Real.sqrt (lam p) * Real.sqrt (lam p) = lam p := by
      rw [← pow_two]; exact Real.sq_sqrt (hlam p)
    rw [show Real.sqrt (lam p) * U i p * (Real.sqrt (lam p) * U j p)
          = (Real.sqrt (lam p) * Real.sqrt (lam p)) * (U i p * U j p) by ring, hs]
    ring
  rw [hL, hR]

/-- **Mercer 型有限版（主结果）**：有限输入下，**核半正定 ⟺ 存在特征映射 `Φ : α → ℝⁿ`
使 `K a b = ⟪Φ a, Φ b⟫`**。

- `⟸`：取 `v` 任意，`Σ_i Σ_j v_i·⟪Φ x_i, Φ x_j⟫·v_j = ‖Σ_i v_i • Φ x_i‖² ≥ 0`。
- `⟹`：`RealSVD.symmetric_spectral_theorem` 给出 `G = U·diag λ·Uᵀ`；`G` 半正定故
  `λ ≥ 0`，令 `Φ x_i j = √(λ_j)·U_{i j}`，用 `kernelGramMatrix_eq_featureMap_mul_transpose`。 -/
theorem kernelGramMatrix_psd_iff_exists_featureMap {n : ℕ} (K : α → α → ℝ) (x : Fin n → α)
    (hsymm : IsSymmKernel K) :
    (∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * kernelGramMatrix K x i j * v j)
      ↔ ∃ Φ : Fin n → Fin n → ℝ,
          ∀ i j, kernelGramMatrix K x i j = ∑ p, Φ i p * Φ j p := by
  constructor
  · intro hpsd
    -- `G` 对称性由**核对称假设** `hsymm` 提供（半正定本身推不出，见 `kernel_sym_part_abs_le` 的说明）
    have hHerm : (kernelGramMatrix K x).IsHermitian :=
      kernelGramMatrix_isHermitian K x hsymm
    obtain ⟨U, lam, hU, hG⟩ := symmetric_spectral_theorem (kernelGramMatrix K x) hHerm
    have hlam : ∀ k, 0 ≤ lam k :=
      eigenvalues_nonneg_of_gram_psd hU hG hpsd
    refine ⟨fun i j => Real.sqrt (lam j) * U i j, fun i j => ?_⟩
    -- G = U diag λ Uᵀ = Φ Φᵀ，逐元素即 `kernelGramMatrix K x i j = Σ_p Φ i p * Φ j p`
    have hpt := congrFun (congrFun
      (kernelGramMatrix_eq_featureMap_mul_transpose U lam hU hlam) i) j
    rw [← hG] at hpt
    -- v15 修复：`hpt : (U * diag λ * Uᵀ) i j = (Φ * Φᵀ) i j`；`rw [← hG]` 把它变成
    -- `kernelGramMatrix K x i j = (Φ * Φᵀ) i j`。目标是
    -- `kernelGramMatrix K x i j = Σ p, Φ i p * Φ j p` ⟹ 用 `hpt`（**不是** `hpt.symm`）
    -- （原稿用 `hpt.symm`，方向反了，`simpa` 报 type mismatch）。
    simpa [kernelGramMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
      using hpt
  · rintro ⟨Φ, hΦ⟩ v
    have : ∀ i j, v i * kernelGramMatrix K x i j * v j
        = ∑ p, (v i * Φ i p) * (v j * Φ j p) := by
      intro i j
      rw [hΦ i j, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    calc
      (∑ i, ∑ j, v i * kernelGramMatrix K x i j * v j)
          = ∑ i, ∑ j, ∑ p, (v i * Φ i p) * (v j * Φ j p) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => this i j
      _ = ∑ p, (∑ i, v i * Φ i p) ^ 2 := by
            -- v15 修复：原稿只做**一次** `rw [Finset.sum_comm]`（它只交换最外两层
            -- `∑ i`/`∑ j`），而这里要把**最内层**的 `∑ p` 提到最外 ⟹ 模式不匹配
            -- （`:498` 报 not-found）。
            -- 正确顺序：① 内层换序（对固定 `i`，交换 `j` 与 `p`）② 外层换序。
            rw [show (∑ i, ∑ j, ∑ p, (v i * Φ i p) * (v j * Φ j p))
                = ∑ i, ∑ p, ∑ j, (v i * Φ i p) * (v j * Φ j p) from
              Finset.sum_congr rfl fun i _ => Finset.sum_comm]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [pow_two, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            -- v15 修复：`Finset.mul_sum` **一条就闭合了整个目标**
            -- （实测：其后任何 `sum_congr`/`ring` 都报 `no goals to be solved`）。
            -- 原稿在其后多写 `sum_congr` + `ring` ⟹ `:537`。
      _ ≥ 0 := Finset.sum_nonneg fun p _ => sq_nonneg _

/-- **距离–核恒等式（任务指定核心恒等式）**：设 `Φ` 是核 `K` 的特征映射
（即 `K a b = ⟪Φ a, Φ b⟫`，把有限 `Φ` 写成逐点和），则

    `‖Φ x − Φ y‖² = K x x − 2·K x y + K y y`。

这条是「核 = 特征映射内积」的直接后果，也是核方法中把核当作「平方距离」使用
（如 `K(x,x) − 2K(x,y) + K(y,y) ≥ 0`）的代数依据。 -/
theorem metric_eq_kernel_expansion {n : ℕ} {K : α → α → ℝ} (Phi : α → Fin n → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Phi a p * Phi b p) (a b : α) :
    (∑ p, (Phi a p - Phi b p) ^ 2) = K a a - 2 * K a b + K b b := by
  rw [hK a a, hK a b, hK b b]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **特征映射距离平方非负（核的负型非负性）**：
`0 ≤ K a a − 2·K a b + K b b`（由 `‖Φ a − Φ b‖² ≥ 0`）。 -/
theorem metric_kernel_nonneg {n : ℕ} {K : α → α → ℝ} (Phi : α → Fin n → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Phi a p * Phi b p) (a b : α) :
    0 ≤ K a a - 2 * K a b + K b b := by
  rw [← metric_eq_kernel_expansion Phi hK a b]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

/-- **核距离为零 ⟺ 特征映射相等**：`K a a − 2K a b + K b b = 0 ↔ Φ a = Φ b`
（平方和为零 ⟺ 每项为零）。 -/
theorem kernel_metric_zero_iff {n : ℕ} {K : α → α → ℝ} (Phi : α → Fin n → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Phi a p * Phi b p) (a b : α) :
    K a a - 2 * K a b + K b b = 0 ↔ Phi a = Phi b := by
  rw [← metric_eq_kernel_expansion Phi hK a b, Finset.sum_eq_zero_iff_of_nonneg
    (fun p _ => sq_nonneg _)]
  constructor
  · intro h
    funext p
    have hp := h p (Finset.mem_univ p)
    have : Phi a p - Phi b p = 0 := pow_eq_zero hp
    linarith
  · intro h p _
    rw [h]
    ring

/-! ## 三、与线性注意力的接口 -/

/-- **`RealLinearAttention.featScore` 就是可分核的内积**：
`featScore φ q k = Σ_i φ(q_i)·φ(k_i) = ⟪φ∘q, φ∘k⟫`（`Fin d → ℝ` 上的欧氏内积）。

即线性注意力的打分在特征映射 `u ↦ fun i => φ (u i)` 下是核内积：
`featScore φ` **就是**核 `K_φ(u,v) = ⟪φ∘u, φ∘v⟫`。

⚠ **v15 更正（实测）**：原陈述把 `⟪…, …⟫_ℝ` 直接作用在 **`Fin d → ℝ`** 上，
但**该类型在本 mathlib（4.14）根本没有 `Inner` 实例** ——
内积实例只挂在 `PiLp 2 f`（即 `EuclideanSpace 𝕜 ι`）上
（`Mathlib/Analysis/InnerProductSpace/PiL2.lean:71` 的
`instance PiLp.innerProductSpace : InnerProductSpace 𝕜 (PiLp 2 f)`，
**没有** `∀ i, f i` 的版本）。
⇒ 原陈述**类型不合法**（报 `failed to synthesize Inner ℝ (Fin d → ℝ)`），
且 `⟪⟫` 记号本身还要求 `open scoped RealInnerProductSpace`（`InnerProduct` 不是作用域名）。
本版把内积对象**显式放到 `EuclideanSpace ℝ (Fin d)`**（二者作为 `Fin d → ℝ` 逐点相等），
记号仍要求 `open scoped RealInnerProductSpace`（已在本文件顶部 open）。 -/
theorem featScore_eq_inner {d : ℕ} (φ : ℝ → ℝ) (q k : Fin d → ℝ) :
    featScore φ q k
      = (⟪(EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => φ (q i)),
          (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => φ (k i))⟫ : ℝ) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_coe, EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply,
    featScore]
  refine Finset.sum_congr rfl fun i _ => ?_
  show φ (q i) * φ (k i)
      = (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => φ (q i)) i
        * (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => φ (k i)) i
  rfl

/-- **可分核是正定核**：`K_φ(u,v) = ⟪φ∘u, φ∘v⟫` 半正定（特征映射 `u ↦ φ∘u`）。
这是线性注意力「核化」说法的正定性认证——`featScore` 对应的核**确实**是正定核，
无条件（对任意 `φ : ℝ → ℝ`，不需要 `φ ≥ 0`；非负性只影响权重非负，不影响核 PSD）。 -/
theorem separableKernel_gram_psd {d n : ℕ} (φ : ℝ → ℝ) (u : Fin n → Fin d → ℝ)
    (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * (∑ p, φ (u i p) * φ (u j p)) * v j := by
  -- v15 修复：原稿 `rw [Finset.sum_comm]` 直接作用在含**内层 `∑ p`** 的目标上，
  -- 且 `v i`/`v j` 分属内外两层，直接换序会把不同层的因子搅在一起。
  -- 与 `polyKernel_one_gram_psd` 同一根因，**照用同一条已验证路线**：
  -- ① 归约到显式三重和 `Σ i, Σ j, Σ p, (v i * φ (u i p)) * (φ (u j p) * v j)`
  -- ② `∑ p` 提到最外（先内层、后外层）③ 逐 `p` 化为平方和。
  -- ⚠ 索引类型：`u : Fin n → Fin d → ℝ`，外层 `i j : Fin n`、**内层 `p : Fin d`**。
  have h1 : (∑ i, ∑ j, v i * (∑ p, φ (u i p) * φ (u j p)) * v j)
      = ∑ i, ∑ j, ∑ p, (v i * φ (u i p)) * (φ (u j p) * v j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [h1]
  rw [show (∑ i, ∑ j, ∑ p, (v i * φ (u i p)) * (φ (u j p) * v j))
      = ∑ i, ∑ p, ∑ j, (v i * φ (u i p)) * (φ (u j p) * v j) from
    Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  rw [show (∑ p, ∑ a, ∑ j, (v a * φ (u a p)) * (φ (u j p) * v j))
      = ∑ p, (∑ c, v c * φ (u c p)) ^ 2 from
    Finset.sum_congr rfl fun p _ => by
      rw [pow_two, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

/-- **指数核（softmax 注意力的核）**：`K(x,y) = exp(⟪x,y⟫)`。 -/
def expKernel {d : ℕ} (x y : Fin d → ℝ) : ℝ := Real.exp (∑ i, x i * y i)

/-- **热核 / 高斯核**：`heatKernel σ x y = exp(−‖x−y‖²/(2σ²))`。 -/
def heatKernel {d : ℕ} (sigma : ℝ) (x y : Fin d → ℝ) : ℝ :=
  Real.exp (-(∑ i, (x i - y i) ^ 2) / (2 * sigma ^ 2))

/-- 热核对角为 1（`x = y` 时指数为 0）。 -/
theorem heatKernel_diag {d : ℕ} (sigma : ℝ) (x : Fin d → ℝ) :
    heatKernel sigma x x = 1 := by
  unfold heatKernel
  have h : (∑ i, (x i - x i) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    ring
  rw [h]
  norm_num

/-- **热核的秩一 Gram 半正定**（显式降级：只对「输入是一条固定向量族的数乘」陈述）。
证明：此时 `K(x_i,x_j) = exp(0) = 1`（同一条向量），Gram 是 `1` 矩阵，
二次型 `(Σ v_i)² ≥ 0`。 -/
theorem heatKernel_gram_psd_const {n : ℕ} (sigma : ℝ) (a : Fin n → ℝ) (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * heatKernel sigma a a * v j := by
  -- v15 修复：`rw [heatKernel_diag]` 无法匹配，因为 `heatKernel_diag` 的结论
  -- 形如 `heatKernel sigma x x = 1`，而目标里是 `heatKernel sigma a a`
  -- （binder 名不同 ⟹ `rw` 失配）；且 `← Finset.sum_mul_sum` 的 LHS 是
  -- `(∑ i ∈ s, f i) * ∑ j ∈ t, g j`（**带 `∈`**），与目标形状不符 ⟹ `:674` 报错。
  -- ⇒ `simp only [heatKernel_diag, mul_one]` 归约后目标实测为
  -- `0 ≤ ∑ x, ∑ x_1, v x * v x_1`，用 `pow_two` + `Finset.sum_mul` 把它写成 `(Σ v)^2`。
  simp only [heatKernel_diag, mul_one]
  rw [show (∑ x, ∑ x_1, v x * v x_1) = (∑ x, v x) ^ 2 from by
    rw [pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]]
  exact sq_nonneg _

/-! ### 多项式核：线性注意力核的正定性认证（主结果）

`polyKernel d x y = (⟪x,y⟫)^d`（`d : ℕ`）。它是核方法里最经典的正定核族，
也是「线性注意力用 `φ` 的逐维函数张成特征空间」这一说法的**来源**：
`(⟪x,y⟫)^d` 展开后是 `x` 的 `d` 次单项式的内积，特征维数 `= C(d+m-1, d)`。

**诚实降级（重要）**：本文件**只证 `d = 1` 的情形**（即 `polyKernel 1`，
此时特征映射就是恒等 `Φ x = x`，证明是 `Σ v_i x_i` 的平方和）。

- **`d ≥ 2` 未证**。一般 `d` 需要枚举指数向量 `e : Fin m → ℕ`（`Σ e_i = d`）、
  多重组合系数 `multinomial e` 与 `Real.sqrt (multinomial e)` 的拼接，
  以及 `Finset` 上的多项式展开（`MvPolynomial` 或手写多重求和）。
  这条链在 mathlib 4.14 上**原理上可行但体积大**（核心是「`(Σ a_i)^d` 的多重展开
  等于对指数向量的求和」），本轮未做，标注为后续工作。
- **`c > 0`（非齐次多项式核）未证**：需在 `d = 1` 基础上加常值坐标 `√c`，
  依赖 `d ≥ 2` 的结论，同样未做。
- 因此本文件**不声称**「一般多项式核是正定核」，只声称 `d = 1` 版。
  但 `polyKernel_one_eq_featScore` 已足以说明：**线性注意力最平凡的特征映射
  （`φ = id`）对应的核确实是正定核**，认证了「核化」说法的一个非空实例。 -/

/-- **多项式核（齐次版）**：`polyKernel d x y = (Σ_i x_i·y_i)^d`。
（`c > 0` 的非齐次版本未做，见上。） -/
def polyKernel {m : ℕ} (d : ℕ) (x y : Fin m → ℝ) : ℝ := (∑ i, x i * y i) ^ d

/-- **多项式核的 `d = 1` 情形就是可分核**：`polyKernel 1 x y = Σ_i x_i·y_i = ⟪x,y⟫`，
即 `RealLinearAttention.featScore` 取 `φ = id` 的特例。 -/
theorem polyKernel_one_eq_featScore {m : ℕ} (x y : Fin m → ℝ) :
    polyKernel 1 x y = featScore (fun t => t) x y := by
  unfold polyKernel featScore
  rw [pow_one]

/-- **多项式核在 `d = 1` 时是正定核**（显式特征映射 `Φ x = x`）。
这是 `polyKernel_one_eq_featScore` 与 `featScore_eq_inner` 的合成结论。 -/
theorem polyKernel_one_gram_psd {m : ℕ} (x : Fin m → Fin m → ℝ) (v : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * polyKernel 1 (x i) (x j) * v j := by
  have h : ∀ i j, polyKernel 1 (x i) (x j) = ∑ p, x i p * x j p := by
    intro i j
    unfold polyKernel
    rw [pow_one]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [h i j]))]
  -- v15 修复：原稿 `rw [Finset.sum_comm]` 作用于含**内层 `∑ p`** 的目标，
  -- 换序结果与后续 `Finset.sum_mul` 不匹配（原报 not-found / typeclass stuck）。
  -- ⚠ 关键：`v i * (∑ p, …) * v j` 里的 `v i`/`v j` 分属**内外两层**，
  -- 直接换序会把两个不同层的因子搅在一起（实测报 typeclass instance stuck）。
  -- 正确做法：① 先把目标归约到**显式三重和**范式
  --   `Σ i, Σ j, Σ p, (v i * x i p) * (x j p * v j)`
  -- ② 再把 `∑ p` 提到最外（先换内层、再换外层），③ 逐 `p` 化为平方。
  have h1 : (∑ i, ∑ j, v i * (∑ p, x i p * x j p) * v j)
      = ∑ i, ∑ j, ∑ p, (v i * x i p) * (x j p * v j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [h1]
  rw [show (∑ i, ∑ j, ∑ p, (v i * x i p) * (x j p * v j))
      = ∑ i, ∑ p, ∑ j, (v i * x i p) * (x j p * v j) from
    Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  -- 实测此处目标：`0 ≤ ∑ y, ∑ x_1, ∑ j, v x_1 * x x_1 y * (x j y * v j)`
  rw [show (∑ y, ∑ a, ∑ j, (v a * x a y) * (x j y * v j))
      = ∑ y, (∑ c, v c * x c y) ^ 2 from
    Finset.sum_congr rfl fun y _ => by
      rw [pow_two, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

/-! ## 四、核平滑视角：Nadaraya–Watson 与 softmax 注意力 -/

/-- **Nadaraya–Watson 核平滑估计**：
`nwEstimate K x f = Σ_j K (x j) x · f (x j) / Σ_j K (x j) x`。
以样本点 `x j` 为核中心、`x` 为查询点。 -/
def nwEstimate {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) (f : α → ℝ) (q : α) : ℝ :=
  (∑ j, K (x j) q * f (x j)) / (∑ j, K (x j) q)

/-- **NW 权重**：`w_j = K(x_j,q) / Σ_l K(x_l,q)`（与 `RealLinearAttention.linAttnWeights` 同型）。 -/
def nwWeights {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) (q : α) : Fin n → ℝ :=
  fun j => K (x j) q / ∑ l, K (x l) q

/-- **NW 估计 = 权重的加权平均**（把商写成权重内积，便于与注意力对齐）。 -/
theorem nwEstimate_eq_sum_weights {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) (f : α → ℝ)
    (q : α) :
    nwEstimate K x f q = ∑ j, nwWeights K x q j * f (x j) := by
  unfold nwEstimate nwWeights
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **核非负 ⟹ NW 权重非负**（分母为 0 时 Lean 的除法给 0，仍非负）。 -/
theorem nwWeights_nonneg {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) (q : α)
    (hK : ∀ a b, 0 ≤ K a b) (hd : 0 ≤ ∑ l, K (x l) q) (j : Fin n) :
    0 ≤ nwWeights K x q j :=
  div_nonneg (hK _ _) hd

/-- **NW 权重和为 1**（分母非零）。 -/
theorem nwWeights_sum_one {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) (q : α)
    (hd : (∑ l, K (x l) q) ≠ 0) :
    ∑ j, nwWeights K x q j = 1 := by
  unfold nwWeights
  rw [← Finset.sum_div]
  exact div_self hd

/-- **常数函数的 NW 估计恒等于该常数**（分母非零）。 -/
theorem nwEstimate_const {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) (c : ℝ) (q : α)
    (hd : (∑ l, K (x l) q) ≠ 0) :
    nwEstimate K x (fun _ => c) q = c := by
  -- v14 修复：`unfold nwEstimate` 后分子是 `∑ j, K (x j) q * (fun _ => c) (x j)`，
  -- 常函数**未 beta-展开**，故 `Finset.mul_sum` 无法匹配 `∑ j, K (x j) q * c`。
  -- 先用 `simp only []` 做 beta 归约。
  unfold nwEstimate
  simp only []
  -- v15 修复：`simp only []` 后目标实测为
  -- `(∑ x_1, K (x x_1) q * c) / (∑ j, K (x j) q) = c`
  -- ⟹ 用 `Finset.sum_mul` 的**逆用**把常数 `c` 提出求和号（**不带 `∈`** 的版本），
  -- 再 `mul_div_cancel_left₀`。原稿写 `← Finset.mul_sum`（把 `c` 提到**左侧**），
  -- 方向反了 ⟹ `:786` not-found。
  rw [← Finset.sum_mul, mul_div_cancel_left₀ _ hd]

/-- **NW 估计被 `f` 的上下界夹住**（核非负 + 分母正）：核平滑不越界。
这是核平滑的「保序 / 稳定」性质，与 `RealAttention.convComb_norm_bound` 同源。 -/
theorem nwEstimate_le_of_le {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) (f : α → ℝ)
    (q : α) (M : ℝ) (hK : ∀ a b, 0 ≤ K a b) (hd : 0 < ∑ l, K (x l) q)
    (hf : ∀ a, f a ≤ M) :
    nwEstimate K x f q ≤ M := by
  have hdne : (∑ l, K (x l) q) ≠ 0 := ne_of_gt hd
  have hw : ∑ j, nwWeights K x q j = 1 := nwWeights_sum_one K x q hdne
  have hle : ∑ j, nwWeights K x q j * f (x j) ≤ ∑ j, nwWeights K x q j * M := by
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left (hf (x j))
      (nwWeights_nonneg K x q hK (le_of_lt hd) j)
  rw [nwEstimate_eq_sum_weights]
  calc
    (∑ j, nwWeights K x q j * f (x j)) ≤ ∑ j, nwWeights K x q j * M := hle
    _ = (∑ j, nwWeights K x q j) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hw, one_mul]

/-- **softmax 注意力权重 = 指数核的 NW 权重（核心接口定理）**。

`softmax (fun j => ⟪q, k_j⟫)_j = nwWeights expKernel k q`，
其中 `expKernel k_j q = exp(⟪k_j, q⟫)`。

即：**softmax 注意力就是核 `K(x,y) = exp(⟪x,y⟫)` 下的 Nadaraya–Watson 型估计的权重**。
这把「注意力 = 核平滑」从口号变成库内等式——`softmax` 的分子 `exp(logit)` 正是
指数核的值，分母正是核的配分函数。

⚠ **v15 补充（机械实测）**：`hn : 0 < n` 对本条的**等式本身**并非必需
（内核之所以报 `unused variable 'hn'`，是因为证明体只用了一次
`Fin.pos_iff_nonempty.mp hn` 来提供 `Nonempty (Fin n)` 实例，
而 `softmax` 的 `Finset.univ` 求和**不要求非空**）。
⇒ **`hn` 为「接口约定」参数**：保留它的理由是语义（注意力权重需要一个非空的
key 集合才有意义，且与 `softmax_attention_eq_nwWeights` / `softmax_attention_nw_is_prob`
的签名一致）。**保留 + 本条注明**（不删）。 -/
theorem softmax_attention_is_nw {d n : ℕ} (hn : 0 < n) (q : Fin d → ℝ) (k : Fin n → Fin d → ℝ) :
    (fun j => softmax (fun l => ∑ i, q i * k l i) j)
      = fun j => Real.exp (∑ i, k j i * q i) / ∑ l, Real.exp (∑ i, k l i * q i) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  funext j
  -- v14 修复：`softmax (fun l => …) j` 的实参需要先 beta-展开，
  -- 否则 `congr 1` 拿到的是未约简的 `(fun l => …) j`，`apply Finset.sum_congr` 无法统一。
  show Real.exp ((fun l => ∑ i, q i * k l i) j) / ∑ l, Real.exp ((fun l => ∑ i, q i * k l i) l)
      = Real.exp (∑ i, k j i * q i) / ∑ l, Real.exp (∑ i, k l i * q i)
  -- v15 修复：`div_congr` **不是 mathlib 的名字**（`:824` unknown identifier）。
  -- 改为：先 `simp only []` 做 beta 归约（`(fun l => …) j` 需要这一步），
  -- 再对**分子**与**分母**各写一条 `show`，都用 `Finset.sum_congr` + `mul_comm` 对齐因子顺序。
  simp only []
  rw [show (∑ i, q i * k j i) = ∑ i, k j i * q i from
    Finset.sum_congr rfl fun i _ => mul_comm (q i) (k j i)]
  rw [show (∑ l, Real.exp (∑ i, q i * k l i)) = ∑ l, Real.exp (∑ i, k l i * q i) from
    Finset.sum_congr rfl fun l _ => congrArg Real.exp
      (Finset.sum_congr rfl fun i _ => mul_comm (q i) (k l i))]

/-- **softmax 注意力权重的分母恰是配分函数** `Z q k = Σ_l exp(⟪k_l,q⟫)`，
显式命名以便与 `RealAttention.softmax` 的既有归一化结论对接。 -/
def attentionPartition {d n : ℕ} (q : Fin d → ℝ) (k : Fin n → Fin d → ℝ) : ℝ :=
  ∑ l, Real.exp (∑ i, k l i * q i)

/-- softmax 权重的分子是 `exp` 的核值：`exp(⟪k_j,q⟫) = expKernel (k j) q`。 -/
theorem softmax_numerator_eq_expKernel {d n : ℕ} (q : Fin d → ℝ) (k : Fin n → Fin d → ℝ)
    (j : Fin n) :
    Real.exp (∑ i, k j i * q i) = expKernel (k j) q := by
  -- v15 修复：`expKernel (k j) q` 展开后**就是** `Real.exp (∑ i, (k j) i * q i)`，
  -- 与目标左端**句法同一**（`k j i` 即 `(k j) i`）⟹ 原稿的
  -- `Finset.sum_congr … mul_comm (k j i) (q i)` 把目标写成了
  -- `k j i * q i = k j i * q i`（自反式），报 type mismatch（`:807`）。
  -- 直接 `rfl` 收口。
  rfl

/-- **softmax 注意力权重是概率分布**（分母非零）：非负 + 和为 1。
与 `RealLinearAttention.linear_attn_weights_pmf` 是同一语义在指数核下的实例。 -/
theorem softmax_attention_nw_is_prob {d n : ℕ} (hn : 0 < n) (q : Fin d → ℝ)
    (k : Fin n → Fin d → ℝ) (hZ : attentionPartition q k ≠ 0) :
    (∀ j, 0 ≤ Real.exp (∑ i, k j i * q i) / attentionPartition q k)
      ∧ (∑ j, Real.exp (∑ i, k j i * q i) / attentionPartition q k) = 1 := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  constructor
  · intro j
    -- v14 修复：原稿用 `le_of_lt (Real.exp_pos _)` 证分母正，但分母是
    -- `attentionPartition q k`（一个**未展开的定义**），`Real.exp_pos` 无法作用于它。
    -- 正确做法：先展开 `attentionPartition`，再用「非零 ⟹ 正」（有限指数和恒正）。
    apply div_nonneg (Real.exp_nonneg _)
    unfold attentionPartition at hZ ⊢
    have hpos : 0 < ∑ l, Real.exp (∑ i, k l i * q i) := by
      refine Finset.sum_pos (fun l _ => Real.exp_pos _) (by
        obtain ⟨j⟩ := (inferInstance : Nonempty (Fin n))
        exact ⟨j, Finset.mem_univ j⟩)
    exact le_of_lt hpos
  · unfold attentionPartition at hZ ⊢
    rw [← Finset.sum_div]
    exact div_self hZ

/-- **softmax 注意力权重 = `nwWeights` 指数核（接口归约）**：
把 `softmax_attention_is_nw` 的右端识别为 `nwWeights` 在核 `expKernel (k ·) (·) q`
下的取值。这条让「注意力 = NW 核平滑」在**库内对象**（`nwWeights`）上闭合，
而不仅是与裸 `exp` 表达式的等式。 -/
theorem softmax_attention_eq_nwWeights {d n : ℕ} (hn : 0 < n) (q : Fin d → ℝ)
    (k : Fin n → Fin d → ℝ) :
    (fun j => softmax (fun l => ∑ i, q i * k l i) j)
      = nwWeights (fun (a b : Fin d → ℝ) => expKernel a b) k q := by
  rw [softmax_attention_is_nw hn]
  funext j
  unfold nwWeights
  -- v14 修复：原稿在 `unfold nwWeights` 后用 `congr 1` 再分两支，
  -- 但 `congr 1` 在此**可能直接关掉目标**（两侧已是同一形状），
  -- 随后的两个 `exact` 于是报 `no goals to be solved`。
  -- 改为显式重写分子/分母，不用 `congr`。
  rw [softmax_numerator_eq_expKernel q k j,
    Finset.sum_congr rfl (fun l _ => softmax_numerator_eq_expKernel q k l)]

/-- **softmax 注意力的分母 = 指数核的配分函数**（同一对象两种写法）。 -/
theorem attentionPartition_eq_sum_expKernel {d n : ℕ} (q : Fin d → ℝ)
    (k : Fin n → Fin d → ℝ) :
    attentionPartition q k = ∑ l, expKernel (k l) q :=
  Finset.sum_congr rfl fun l _ => (softmax_numerator_eq_expKernel q k l).symm

/-- **softmax 注意力输出被 value 的上界夹住（核平滑稳定性的注意力实例）**。

以 `w_j = softmax(logits)_j` 为权重、`c_j` 为标量 value，则 `c_j ≤ M`（∀j）时
`Σ_j w_j·c_j ≤ M`。这是 `nwEstimate_le_of_le` 经
`softmax_attention_eq_nwWeights` 的实例化：注意力输出的稳定性是**核平滑性质**的推论。 -/
theorem softmax_attention_output_le {n : ℕ} (z : Fin n → ℝ) (c : Fin n → ℝ) (M : ℝ)
    (hn : 0 < n) (hc : ∀ j, c j ≤ M) :
    ∑ j, softmax z j * c j ≤ M := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hnn : ∀ j, 0 ≤ softmax z j := softmax_nonneg z
  have hsum : ∑ j, softmax z j = 1 := softmax_sum_one z
  calc
    (∑ j, softmax z j * c j) ≤ ∑ j, softmax z j * M :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hc j) (hnn j)
    _ = (∑ j, softmax z j) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hsum, one_mul]

/-! ## 注：闭环语义

核定义（`IsSymmKernel` + `IsPSDKernel`）→ 核 Gram 矩阵（`kernelGramMatrix`）→
对称性三形态（`kernelGramMatrix_transpose` / `kernelGramMatrix_isHermitian` / `kernelGramMatrix_symm`）→
桥（`kernelQuadForm_eq_kernelGramQuadForm`）→ 有限刻画（`isSymmKernel_iff_gram_psd` /
`isPosDefKernel_gram_psd`）→
单点/两点推论（`kernel_diag_nonneg` / `kernel_le_half_diag_add`）→
**Mercer 有限版**（`kernelGramMatrix_psd_iff_exists_featureMap`，回收 `RealSVD` 谱定理 +
`eigenvalues_nonneg_of_gram_psd`）→ 矩阵形态（`kernelGramMatrix_eq_featureMap_mul_transpose`）→
**距离–核恒等式**（`metric_eq_kernel_expansion`）→
接口（`featScore_eq_inner` 连 `RealLinearAttention`）→
核平滑（`nwEstimate` / `nwWeights` 及其性质）→
**注意力即核平滑**（`softmax_attention_is_nw` → `RealAttention.softmax`）。

诚实降级：Mercer 只做有限版（无积分算子）；RKHS 只给特征映射到 ℝⁿ（无完备化/再生性）；
`expKernel` 的一般 Gram PSD 未证（等价于 Bochner 定理的有限版，mathlib 无），
只给秩一/常值退化情形；代表性定理、核岭回归、泛化界未做（属其他模块）。
-/

end Lattice
