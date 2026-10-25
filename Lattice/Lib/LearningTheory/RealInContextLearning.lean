import Mathlib
import Lattice.Lib.Optim.RealLeastSquares
import Lattice.Lib.Attention.RealLinearAttention
/-!
# LATTICE: 上下文学习（ICL）——单层线性自注意力 ⟹ 一步梯度下降

**来源（两条独立证明的交叉校验）**：

| 论文 | 定理 | 内容 |
|:--|:--|:--|
| Mahankali–Hashimoto–Ma, arXiv:**2307.03576** | **Theorem 1** | 全局最优 ⟹ 单层线性自注意力实现线性回归上的**一步 GD**，输出 `η·Σᵢ yᵢ xᵢᵀ xₙ₊₁` |
| Ahn–Cheng–Daneshmand–Sra, arXiv:**2306.00297** | **Theorem 1** | 同一现象，经由参数化 `(P₀, Q₀)` 的**独立**证明（非各向同性一般化为 `Σ⁻¹` 预条件） |

两文都断言：**预训练损失的全局极小点**所对应的单层线性自注意力，
在查询 token 上的输出**恰好等于**最小二乘目标上的一步（预条件）梯度下降。
本文件把**两文共同依赖的代数内核**形式化，并给出**两条独立路径**在同一 Lean 语句上的汇合。

## 精确假设（按原文，不加强也不削弱）

论文记号：上下文 `(x₁,y₁),…,(xₙ,yₙ)`（`xᵢ ∈ ℝᵈ`、`yᵢ ∈ ℝ`），查询 `xₙ₊₁`，
token `vᵢ = [xᵢ ; yᵢ]`（`i ≤ n`）与 `vₙ₊₁ = [xₙ₊₁ ; 0]`（**零权**）。原文构造取

  `W_K* = W_Q* = [[I_d, 0], [0, 0]]`，`W_V* = [[0,0],[0,η]]`，`h* = [0_d ; 1]`，

于是注意力输出为 `(h*)ᵀ Σᵢ (W_V* vᵢ)(vᵢᵀ (W_K*)ᵀ W_Q* vₙ₊₁) = η·Σᵢ yᵢ xᵢᵀ xₙ₊₁`（原文 Eq. 28）。

**本文件形式化的核心（原文 Eq. 28 ⇄ Eq. 29–30 的代数桥）**：

  `ᵀ(h*) · (Σᵢ vᵢ · (vᵢᵀ M v_q)) = η · Σᵢ yᵢ · (xᵢ · x_q)`  （`M = (W_K*)ᵀW_Q* = diag(I_d,0)`）
  `w₀ − η·∇L(w₀)`，在 `w₀ = 0` 时即 `η·Σᵢ yᵢ xᵢ`

两者给出**同一线性预测子** `η·Σᵢ yᵢ (xᵢ · x_q)`——这就是「权重里存的是算法」的精确陈述。

## 实现注记：矩阵类型 vs 向量函数类型（实测坑，务必遵守）

`attnState` 的 `M` 要求 **`Fin (d+1) → Fin (d+1) → ℝ`（指标 × 指标）**；
而 `projFeature` / `projLabel` 的类型是 **`(Fin (d+1) → ℝ) → Fin (d+1) → ℝ`（向量 → 坐标）**。
**二者不是同一个类型**，写成 `fun a b => projFeature a b` 会让 Lean 把指标当向量，
在下游 `k ⟨j,_⟩` 处爆出**成片** `function expected at`（首批验证实测 6 处）。

因此本文件为每个「函数式投影」配一个**矩阵式孪生定义**，并用一致性引理钉住：

| 函数式（向量 → 坐标） | 矩阵式（指标 × 指标） | 一致性引理 |
|:--|:--|:--|
| `projFeature`（留特征位） | `projMatrix = diag(I_d,0)` | `projMatrix_mulVec` |
| `projLabel`（留标签位） | `projLabelMatrix = diag(0,1)` | `projLabelMatrix_mulVec` |

**下游一律使用矩阵式**；函数式只用于陈述与化简。

## 诚实边界（本文件不证 / 不声称的）

- **不证全局最优性本身**：原文 Theorem 1 的前提是「`(W_K*,W_Q*,W_V*,h*)` 是预训练损失 `L` 的
  **全局极小点**」。这一步依赖对数据分布 `𝒯` 的期望损失计算与 Gaussian 假设；
  mathlib 4.14 定版 pin **无** `multivariateGaussian`（E2 报告 §3.4 实测），故需自建多维高斯。
  本文件**只形式化该定理的代数内核**（Eq. 28–30 的等式），
  **不**引入 `IsGlobalMinimizer` 之类的未定义黑箱谓词来假装前提已被证明。
  **这是诚实的范围限定**：本文件证的是「该构造 ⟹ 输出等于一步 GD」，
  **不**证「该构造确实是全局极小」（后者的陈述需要概率层，属于明确的未做项）。
- **不含 Thm 2 的概率部分**：`Σ⁻¹` 预条件的**代数形式**在 `icl_precond_one_step` 中给出，
  但「倾斜协方差使 `Σ⁻¹` 成为全局最优」这一**统计**断言未证（同上，需 Gaussian 期望）。
- **不含 Thm 3（非线性目标）**：需要 ReLU/函数族 `ℱ` 的逼近论，超出本文件范围，标注为**未做**。
- **不含 `η` 的期望之比**：原文 `η = E[ŵᵀXᵀy]/E[yᵀXXᵀy]` 是**期望之比**；
  本文件给出其一维二次型极小点的**代数刻画**（`etaQuadratic` 族），
  但**不**断言它等于原文那个期望之比（那需要把期望损失展开成该二次型，属未做项）。
- 未做：多层（`L` 层）推广、ReLU 特例、训练动力学（`2306.09927` Thm 4.1）。

**交叉校验的意义**：两条独立证明路线（2307.03576 的 `h*`–`W_V` 直接展开 vs
2306.00297 的 `P₀`/`Q₀` 状态分解）在 Lean 中被**归约到同一条 `Finset.sum` 代数恒等式**，
若任一路线的形式化有误，`icl_two_proofs_agree` 会失败——这是形式化驱动的交叉验证。

模型无关：任意有限 `d`、`n`；只 import Mathlib + 2 个只读 LATTICE 模块。
无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

variable {d n : ℕ}

/-! ## 1. 定义：token 嵌入、投影矩阵与线性自注意力（按 2307.03576 的记号）

token 为 `vᵢ = [xᵢ ; yᵢ] ∈ ℝ^{d+1}`：前 `d` 个坐标是特征，**最后**一个坐标是标签。
把 `v : Fin (d+1) → ℝ` 的最后一位（`Fin.last d`）用作标签槽位，与原文 `[x ; y]` 一致。

**为什么用 `Fin.castLE` 而非 `⟨j, h⟩`**：在 `if (j:ℕ) < d then v ⟨j,h⟩ else 0` 中，
Lean 会把 `⟨j,h⟩` 的期望类型推断为 `Fin (d+1)`（外层函数的值类型），
导致 `h : j < d` 与 `j < d+1` 不匹配（实测报 `application type mismatch`）。
显式写 `Fin.castLE (by omega) j` 是唯一稳妥的写法。 -/

/-- 上下文 token：`vᵢ = [xᵢ ; yᵢ]`（前 `d` 位特征，`Fin.last d` 位标签）。 -/
def iclToken (x : Fin d → ℝ) (y : ℝ) : Fin (d + 1) → ℝ :=
  fun j => if h : (j : ℕ) < d then x ⟨(j : ℕ), h⟩ else y

/-- 查询 token：`v_{n+1} = [x_{n+1} ; 0]`——**零权**（原文 `v_{n+1} = [x_{n+1} ; 0]`）。

**实现注记（实测坑）**：`Fin.castLE` 在此处不可用——`iclQuery` 的返回类型是 `Fin (d+1) → ℝ`，
而 `if (j:ℕ) < d` 分支里要构造的是**输入** `Fin d`，Lean 对 `Fin.castLE` 的 `d ≤ d+1`
会错误地期望 `d ≤ d`（报 `argument has type d ≤ d.succ but is expected to have type d ≤ d`）。
直接用本元素引 `⟨(j:ℕ), h⟩`（期望类型由 `xq : Fin d → ℝ` 决定）才是稳妥写法。 -/
def iclQuery (xq : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  fun j => if h : (j : ℕ) < d then xq ⟨(j : ℕ), h⟩ else 0

/-- **投影（函数形式）**：作用在 `v` 上即**只保留特征位、抹掉标签位**（`diag(I_d,0)` 的语义）。 -/
def projFeature (v : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun j => if (j : ℕ) < d then v (Fin.castLE (by omega) j) else 0

/-- **投影矩阵（矩阵形式）** `M = diag(I_d, 0)`（原文 `W_K* = W_Q* = [[I_d,0],[0,0]]`）。

**⚠️ 为什么必须与 `projFeature` 分开定义（实测类型错误的根因）**：
`projFeature` 的类型是 `(Fin (d+1) → ℝ) → Fin (d+1) → ℝ`——**第一个参数是向量**；
而 `attnState` 的 `M` 要求 `Fin (d+1) → Fin (d+1) → ℝ`——**两个参数都是指标**。
二者**不是同一个类型**。写成 `fun a b => projFeature a b` 会让 Lean 把指标 `a` 当向量，
在后续 `k ⟨j,_⟩` 处爆出成片的 `function expected at`（实测 6 处）。

正确定义见下：`projMatrix` 是 `projFeature` 的**矩阵表示**，
一致性由 `projMatrix_mulVec`（`M *ᵥ v = projFeature v`）钉住。 -/
def projMatrix : Fin (d + 1) → Fin (d + 1) → ℝ :=
  fun k l => if ((k : ℕ) < d ∧ k = l) then 1 else 0

/-- **`projMatrix` 作用即 `projFeature`**（矩阵表示与函数表示一致）。

这是 ICL 形式化的关键接口引理：原文的矩阵构造 `W_K*, W_Q*` 与「只留特征位」的
函数式描述通过它对号入座。 -/
lemma projMatrix_mulVec (v : Fin (d + 1) → ℝ) :
    (fun k => ∑ l, projMatrix k l * v l) = projFeature v := by
  funext k
  -- **F3 修法（实证，日志 `139:4`）**：`unfold projMatrix projFeature` **只把定义体塞进目标、
  -- 不做 β-归约**，`if` 留在 λ 内 ⟹ 一切 `if_pos`/`dif_pos` 都报
  -- `did not find instance of the pattern … dite (↑k < d) ?m ?m`。
  -- `simp only [projMatrix, projFeature]` **会**做 β-归约，把两侧的 λ 打开。
  -- 归约后两侧都是 `ite`（判别式是不依赖证明的 `Prop`），故一律用 `if_pos`/`if_neg`。
  simp only [projMatrix, projFeature]
  by_cases hk : (k : ℕ) < d
  · -- 特征位：RHS 取 `v (castLE k)`（其值就是 `v k`）；LHS 整行只有 `l = k` 存活。
    rw [if_pos hk, Finset.sum_eq_single k]
    · -- 目标：`(if ↑k < d ∧ k = k then 1 else 0) * v k = v (Fin.castLE … k)`。
      -- ⚠ 判别式是**合取** `↑k < d ∧ k = k`（因为 `projMatrix` 写成 `(↑k < d ∧ k = l)`），
      -- 故 `if_pos hk` 模式不匹配（日志 `did not find instance … if ↑k < d then ?m else ?m`）。
      -- 正解：`if_pos ⟨hk, rfl⟩` 一次给出整个合取。
      rw [if_pos ⟨hk, rfl⟩, one_mul]
      -- `v k = v (Fin.castLE … k)`：同一个 `Fin` 的两种写法。
      congr 1
    · intro l _ hl
      -- 判别式是 `↑k < d ∧ k = l`；`hl : l ≠ k` 反驳第二个分量。
      rw [if_neg (fun hc => hl hc.2.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro l _
    rw [if_neg (fun hc => hk hc.1), zero_mul]

/-- **线性自注意力状态**（2306.00297 的 `Q₀` 路线与 2307.03576 Eq. 28 的公共形式）：

  `attnState M v_q V = Σᵢ vᵢ · (vᵢᵀ M v_q)`

即「注意力输出 = Σᵢ (W_V vᵢ)·(vᵢᵀ M v_q)」的**未加读出向量**形式，`M = (W_K)ᵀW_Q`。 -/
def attnState {ι : Type*} [Fintype ι] (M : Fin (d + 1) → Fin (d + 1) → ℝ)
    (vq : Fin (d + 1) → ℝ) (V : ι → Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun j => ∑ i, V i j * (∑ k, V i k * (∑ l, M k l * vq l))

/-- **单层线性自注意力输出**（原文 Eq. 28 的左侧）：读出向量 `h` 作用在缩放后的状态上。

  `linearSelfAttention η h M v_q V = η · Σⱼ hⱼ · attnState M v_q V ⱼ`

原文取 `h* = [0_d ; 1]`、`W_V* = [[0,0],[0,η]]`，即「读出标签位并乘 `η`」。 -/
def linearSelfAttention {ι : Type*} [Fintype ι] (η : ℝ) (h : Fin (d + 1) → ℝ)
    (M : Fin (d + 1) → Fin (d + 1) → ℝ) (vq : Fin (d + 1) → ℝ)
    (V : ι → Fin (d + 1) → ℝ) : ℝ :=
  η * ∑ j, h j * attnState M vq V j

/-! ## 2. `projFeature` 的三个基本引理 -/

/-- 特征位：`projFeature` 在特征坐标上就是原向量。 -/
lemma projFeature_feature {v : Fin (d + 1) → ℝ} {i : Fin d} :
    projFeature v ⟨(i : ℕ), by omega⟩ = v ⟨(i : ℕ), by omega⟩ := by
  unfold projFeature
  simp only [i.isLt, dif_pos]
  congr 1

/-- 标签位：`projFeature` 抹掉标签槽位。 -/
lemma projFeature_last (v : Fin (d + 1) → ℝ) : projFeature v (Fin.last d) = 0 := by
  unfold projFeature
  have h : ¬ ((Fin.last d : Fin (d + 1)) : ℕ) < d := by simp
  simp [h]

/-- **特征内积**：`Σⱼ projFeature v ⱼ · projFeature vq ⱼ = Σ_{j<d} v_j · vq_j`。

`projFeature` 抹掉标签位，故求和只在特征位上——这是 Eq. 28 的**分数**侧。 -/
lemma sum_projFeature_mul (v vq : Fin (d + 1) → ℝ) :
    ∑ j, projFeature v j * projFeature vq j
      = ∑ i : Fin d, v ⟨(i : ℕ), by omega⟩ * vq ⟨(i : ℕ), by omega⟩ := by
  unfold projFeature
  rw [Fin.sum_univ_castSucc]
  have hlast : (if ((Fin.last d : Fin (d + 1)) : ℕ) < d
        then v (Fin.castLE (by omega) (Fin.last d)) else 0)
      * (if ((Fin.last d : Fin (d + 1)) : ℕ) < d
        then vq (Fin.castLE (by omega) (Fin.last d)) else 0) = 0 := by
    have h : ¬ ((Fin.last d : Fin (d + 1)) : ℕ) < d := by simp
    simp [h]
  rw [hlast, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hcast : ((j.castSucc : Fin (d + 1))) = ⟨(j : ℕ), by omega⟩ := Fin.ext rfl
  rw [hcast]
  simp only [j.isLt, dif_pos]
  congr 1

/-! ## 3. token 引理 -/

@[simp] lemma iclToken_last (x : Fin d → ℝ) (y : ℝ) : iclToken x y (Fin.last d) = y := by
  unfold iclToken
  rw [dif_neg (by simp)]

@[simp] lemma iclQuery_last (xq : Fin d → ℝ) : iclQuery xq (Fin.last d) = 0 := by
  unfold iclQuery
  have h : ¬ ((Fin.last d : Fin (d + 1)) : ℕ) < d := by simp
  rw [dif_neg h]

/-- `iclQuery` 的特征位就是 `xq`。 -/
lemma iclQuery_feature {xq : Fin d → ℝ} {i : Fin d} :
    iclQuery xq ⟨(i : ℕ), by omega⟩ = xq i := by
  unfold iclQuery
  rw [dif_pos i.isLt]

/-- `iclToken` 的特征位就是 `x`。 -/
lemma iclToken_feature {x : Fin d → ℝ} {y : ℝ} {i : Fin d} :
    iclToken x y ⟨(i : ℕ), by omega⟩ = x i := by
  unfold iclToken
  rw [dif_pos i.isLt]

/-! ## 4. 核心代数恒等式（原文 Eq. 28 的右侧）

标签槽位（`Fin.last d`）上的注意力读出 = `Σᵢ yᵢ (xᵢ · x_q)`。

关键机制：`projFeature` 抹掉标签位 ⟹ **分数**只用特征内积（`sum_projFeature_mul`）；
而 `attnState` 的**值**槽位在标签坐标上仍读得到 `V i (Fin.last d) = yᵢ`。 -/

/-- **注意力状态在标签位的展开**（Eq. 28 的中间式）：

  `attnState projMatrix v_q V (last) = Σᵢ Vᵢ(last) · (Σ_{j<d} Vᵢⱼ · v_qⱼ)`

即：投影矩阵使**分数**只用特征内积，而**值**读出标签位。

**证明策略（经一次类型修正）**：内层 `Σ_l projMatrix k l · vq l = projFeature vq k`
（由 `projMatrix_mulVec`，**注意 `M` 是矩阵类型、`projFeature` 是向量函数类型，不可混用**），
故内层与 `k` 无关、可整列提出；再用 `castSucc` 拆分：
特征位给出 `Σ_{j<d} Vᵢⱼ·vqⱼ`，标签位系数为 `projFeature vq (last) = 0`（`projFeature_last`）。 -/
lemma attnState_projFeature_last {ι : Type*} [Fintype ι]
    (vq : Fin (d + 1) → ℝ) (V : ι → Fin (d + 1) → ℝ) :
    attnState (d := d) projMatrix vq V (Fin.last d)
      = ∑ i, V i (Fin.last d)
          * (∑ j : Fin d, V i ⟨(j : ℕ), by omega⟩ * vq ⟨(j : ℕ), by omega⟩) := by
  -- 内层：`Σ_l projMatrix k l · vq l = projFeature vq k`（矩阵表示 = 函数表示）。
  have hinner : ∀ k : Fin (d + 1),
      (∑ l, projMatrix k l * vq l) = projFeature vq k := by
    intro k
    have := congrFun (projMatrix_mulVec (d := d) vq) k
    simpa using this
  -- 于是内层与 `k` 无关，可提出求和：`Σ_k V i k · projFeature vq k`。
  -- 再用 castSucc 拆分：特征位给出 `Σ_{j<d} V i j · vq j`，标签位系数为 `projFeature vq (last) = 0`。
  unfold attnState
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  calc ∑ k, V i k * (∑ l, projMatrix k l * vq l)
      = ∑ k, V i k * projFeature vq k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hinner k]
    _ = ∑ j : Fin d, V i ⟨(j : ℕ), by omega⟩ * vq ⟨(j : ℕ), by omega⟩ := by
          rw [Fin.sum_univ_castSucc]
          have hlast : V i (Fin.last d) * projFeature vq (Fin.last d) = 0 := by
            rw [projFeature_last, mul_zero]
          rw [hlast, add_zero]
          apply Finset.sum_congr rfl
          intro j _
          have hcast : ((j.castSucc : Fin (d + 1))) = ⟨(j : ℕ), by omega⟩ := Fin.ext rfl
          rw [hcast, projFeature_feature]

/-- 读出向量 `h* = [0_d ; 1]`（原文构造）：只读标签槽位。 -/
def iclReadout : Fin (d + 1) → ℝ := fun j => if (j : ℕ) < d then 0 else 1

/-- `h*` 提取标签位：`Σⱼ iclReadoutⱼ · vⱼ = v(last)`。 -/
lemma sum_iclReadout_mul (v : Fin (d + 1) → ℝ) :
    ∑ j, iclReadout j * v j = v (Fin.last d) := by
  unfold iclReadout
  rw [Fin.sum_univ_castSucc]
  have hlast : (if ((Fin.last d : Fin (d + 1)) : ℕ) < d then (0 : ℝ) else 1) = 1 := by
    have h : ¬ ((Fin.last d : Fin (d + 1)) : ℕ) < d := by simp
    simp [h]
  rw [hlast, one_mul]
  have hzero : ∑ i : Fin d,
      (if ((i.castSucc : Fin (d + 1)) : ℕ) < d then (0 : ℝ) else 1) * v i.castSucc = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hcast : ((j.castSucc : Fin (d + 1))) = ⟨(j : ℕ), by omega⟩ := Fin.ext rfl
    rw [hcast]
    simp [j.isLt]
  rw [hzero, zero_add]

/-- **★ 核心恒等式（原文 Eq. 28）**：

  `h* ⊤ (attnState projFeature (iclQuery xq) (fun i => iclToken (X i) (y i))) = Σᵢ yᵢ (xᵢ · x_q)`

即原文 `η Σᵢ yᵢ xᵢᵀ x_{n+1}` 中的 `Σᵢ yᵢ xᵢᵀ x_{n+1}` 部分。 -/
theorem icl_attention_readout_eq (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (xq : Fin d → ℝ) :
    ∑ j, iclReadout j * attnState (d := d) projMatrix
        (iclQuery xq) (fun i => iclToken (X i) (y i)) j
      = ∑ i, y i * (∑ j : Fin d, X i j * xq j) := by
  rw [sum_iclReadout_mul, attnState_projFeature_last]
  apply Finset.sum_congr rfl
  intro i _
  rw [iclToken_last]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [iclToken_feature, iclQuery_feature]

/-! ## 5. 定理一（2307.03576 Theorem 1 的代数内核）：注意力输出 = 一步 GD 的预测

最小二乘目标 `L(w) = ½ Σᵢ (wᵀxᵢ − yᵢ)²`（Eq. 29），`∇L(w) = Σᵢ (wᵀxᵢ − yᵢ)xᵢ`（Eq. 30）。
在 `w₀ = 0` 处，一步 GD 给 `w₁ = −η·∇L(0) = η·Σᵢ yᵢxᵢ`，
其线性预测为 `w₁ · x_q = η·Σᵢ yᵢ(xᵢ · x_q)`。 -/

/-- 最小二乘目标 `L(w) = ½ Σᵢ (wᵀxᵢ − yᵢ)²`（原文 Eq. 29）。 -/
def lstsqObjective (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin d → ℝ) : ℝ :=
  (1 / 2) * ∑ i, (∑ j, w j * X i j - y i) ^ 2

/-- 梯度 `∇L(w) = Σᵢ (wᵀxᵢ − yᵢ)·xᵢ`（原文 Eq. 30），以**分量形式**给出。 -/
def lstsqGrad (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin d → ℝ) : Fin d → ℝ :=
  fun j => ∑ i, (∑ k, w k * X i k - y i) * X i j

/-- **在 `w₀ = 0` 处 `−∇L(0) = Σᵢ yᵢ xᵢ`**（原文：初始化于 `w₀ = 0` 时一步 GD 即 `η Σᵢ yᵢxᵢ`）。 -/
lemma lstsqGrad_zero (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (j : Fin d) :
    lstsqGrad X y (fun _ => 0) j = -∑ i, y i * X i j := by
  unfold lstsqGrad
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : ∑ k, (fun _ : Fin d => (0 : ℝ)) k * X i k - y i = -y i := by simp
  rw [h]
  ring

/-- **一步梯度下降的预测子（原文 Eq. 30 的积分）**：
从 `w₀ = 0` 出发一步 GD 得 `w₁ = η·Σᵢ yᵢ xᵢ`，其线性预测为 `w₁ · x_q`。 -/
def gdOneStepPredict (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (xq : Fin d → ℝ)
    (η : ℝ) : ℝ :=
  ∑ j, (∑ i, η * y i * X i j) * xq j

/-- `gdOneStepPredict` 即 `η · Σᵢ yᵢ (xᵢ · x_q)`（重排求和）。 -/
lemma gdOneStepPredict_eq (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (xq : Fin d → ℝ) (η : ℝ) :
    gdOneStepPredict X y xq η = η * ∑ i, y i * (∑ j : Fin d, X i j * xq j) := by
  unfold gdOneStepPredict
  have hL : ∀ j : Fin d, (∑ i : Fin n, η * y i * X i j) * xq j
      = ∑ i : Fin n, η * y i * (X i j * xq j) := by
    intro j
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_congr rfl (fun j _ => hL j)]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **★★ 定理一（2307.03576 Theorem 1 的代数内核）**：

线性自注意力（`h* = [0_d;1]`、`M = diag(I_d,0)`、步长 `η`）在查询 token 上的输出
= 线性回归最小二乘目标上、从零初始化出发**一步梯度下降**后的预测子。

即原文 Eq. 28 `η Σᵢ yᵢ xᵢᵀx_{n+1}` = 一步 GD 预测。这是「权重里存的是算法」的精确代数陈述。 -/
theorem icl_one_step_gd (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (xq : Fin d → ℝ)
    (η : ℝ) :
    linearSelfAttention (d := d) η iclReadout projMatrix
        (iclQuery xq) (fun i => iclToken (X i) (y i))
      = gdOneStepPredict X y xq η := by
  -- **F3 修法（实证，日志 `388:6`）**：`unfold`/`simp only` 对
  -- `linearSelfAttention`/`gdOneStepPredict` 里的 λ **不做 β-归约**，
  -- 故 `rw [gdOneStepPredict_eq]` 报
  -- `did not find instance of the pattern … ?η * ∑ i, ?y i * ∑ j, ?X i j * ?xq j`。
  -- 正解：**先在结论里把两侧用 `show` 显式 β-归约成同一形状**，再用已证的
  -- `icl_attention_readout_eq`（它本身就是 `η * ∑ … = ∑ …` 的形状）改写。
  unfold linearSelfAttention
  rw [icl_attention_readout_eq]
  -- 此时目标：`η * ∑ i, y i * (∑ j, X i j * xq j) = gdOneStepPredict X y xq η`。
  -- 用 `gdOneStepPredict_eq` **反向**把 RHS 也化到同一形状。
  rw [gdOneStepPredict_eq]

/-! ## 6. 第二条独立证明路线（2306.00297 Theorem 1 的形式）

Ahn et al. 的参数化为 `P₀ = [[0,0],[0,1]]`、`Q₀ = −diag(β_i, 0)`（`β_i` 由 `Σ` 的谱给出），
并断言其为全局极小。其状态形式把**标签**经 `P₀` 提到分数位置。

**★ 本节的诚实更正（重要，来自机器验证）**：
把第二条路线写成 `η·Σᵢ Σⱼ Xᵢⱼ · qStateᵢ`（`qStateᵢ = yᵢ·(xᵢ·x_q)`）是**假命题**——
`Σᵢ Σⱼ Xᵢⱼ · yᵢ · innerᵢ = Σᵢ yᵢ innerᵢ · (Σⱼ Xᵢⱼ)` 一般**不等于** `Σᵢ yᵢ innerᵢ`。
（数值反例：`n=3, d=2` 时左式 `0.2731…`、右式 `−0.2477…`，见 `_tmp_n1_a3.py` 的验证记录。）

**正确的对偶构造**是**交换 `M` 与读出向量 `h` 的角色**：

| | 分数矩阵 `M` | 读出向量 `h` | 查询 token `v_q` |
|:--|:--|:--|:--|
| 路线 A（2307.03576） | `diag(I_d, 0)` | `[0_d ; 1]` | `[x_q ; 0]` |
| 路线 B（2306.00297） | `diag(0, 1)` | `[x_q ; 0]` | `[x_q ; 1]` |

路线 B 中 `vᵢᵀ M v_q = yᵢ · 1 = yᵢ`（`M = diag(0,1)` 只取标签位，`v_q` 标签位取 1），
而读出 `h = [x_q ; 0]` 给 `Σᵢ (x_q · xᵢ) · yᵢ = Σᵢ yᵢ (xᵢ · x_q)`——
与路线 A **同一个**结果，且**求和结构完全不同**（分数一次、读出一次 vs 分数一次、读出一次，
但作用在不同的槽位上）。这才是「两条独立证明」在该代数内核上的忠实对应。 -/

/-- **路线 B 的查询 token**：`v_q = [x_q ; 1]`（标签槽位取 **1**，与路线 A 的零权相反）。

这与 2306.00297 把 `P₀ = diag(0,1)` 作用在查询上以取出「标签系数 1」的做法对应。 -/
def iclQueryLabel (xq : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  fun j => if h : (j : ℕ) < d then xq ⟨(j : ℕ), h⟩ else 1

/-- **路线 B 的读出向量**：`h = [x_q ; 0]`（读出特征、按 `x_q` 加权）。

这正是 2306.00297 中 `Q₀` 把查询特征散射到全部坐标上的角色。 -/
def iclReadoutQuery (xq : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  fun j => if h : (j : ℕ) < d then xq ⟨(j : ℕ), h⟩ else 0

/-- **路线 B 的投影（函数形式）**：`diag(0, 1)`（2306.00297 的 `P₀`）——只保留**标签**位。 -/
def projLabel (v : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun j => if (j : ℕ) < d then 0 else v (Fin.last d)

/-- **路线 B 的投影矩阵（矩阵形式）** `M = diag(0, 1)`，`M k l = (k = l ∧ ¬ k < d) ? 1 : 0`。

与 `projMatrix` 同样的理由：`attnState` 的 `M` 需要**指标 × 指标**类型，
而 `projLabel : vector → coord` 是**向量 → 坐标**类型——
两者不是同一类型（写成 `fun a b => projLabel a b` 会重演 `function expected at` 成片报错）。 -/
def projLabelMatrix : Fin (d + 1) → Fin (d + 1) → ℝ :=
  fun k l => if (¬ (k : ℕ) < d ∧ k = l) then 1 else 0

/-- **`projLabelMatrix` 作用即 `projLabel`**（矩阵表示与函数表示一致）。

**⚠ 修法记录（F3，与 `projMatrix_mulVec` 同根因 + 本条独有的两处）**：
1. **`rw [if_pos (by tauto), dif_pos hk]` 必然失败**——`rw` 按**给定顺序**逐个尝试，
   `if_pos` 先被作用在**尚未 β-归约**的目标上，`if` 还埋在 `projLabel` 的 λ 里
   ⟹ 报 `did not find instance of the pattern … dite (↑k < d) ?m ?m`。
   正解：**先 `rw [dif_pos hk]` / `rw [dif_neg hk]` 打开 λ**，再处理矩阵那个 `if`。
2. **`by tauto` 在 `by_cases hk` 的两个分支里都是错的**（实测 4 条 error：`tauto failed to solve some goals`）：
   - 特征位分支要用的是 `hk : (k:ℕ) < d`，而 `tauto` 对**同时含 `hk` 与 `¬hk` 的上下文**无力
     （它不消解"原子与其否定并存"这类命题逻辑之外的目标）；
   - 标签位分支要证 `¬ (k:ℕ) < d ∧ k = l` 为**假**，得从 `hl : k ≠ l` 出发——
     这里必须显式交出 `¬ ((k:ℕ) < d ∧ k = l)` 的证明，`tauto` 给不出。
   正解：一律用 `simp [hk]` / `simp [hk, hl]` 这类**可判定**的收尾。 -/
lemma projLabelMatrix_mulVec (v : Fin (d + 1) → ℝ) :
    (fun k => ∑ l, projLabelMatrix k l * v l) = projLabel v := by
  funext k
  -- 同 `projMatrix_mulVec`：必须用 `simp only [defs]` 做 β-归约，`unfold` 会留下未归约的 λ。
  -- 归约后两侧都是 **`ite`**（非 `dite`），故用 `if_pos`/`if_neg`。
  simp only [projLabelMatrix, projLabel]
  by_cases hk : (k : ℕ) < d
  · -- 特征位：RHS 取 0；LHS 整行为 0。
    rw [if_pos hk]
    apply Finset.sum_eq_zero
    intro l _
    rw [if_neg (by simp [hk]), zero_mul]
  · -- 标签位：只有 `l = k` 存活，且 `projLabel` 在该位取 `v (last) = v k`。
    rw [if_neg hk]
    have hlast : k = Fin.last d := Fin.ext (by simp [Fin.val_last]; omega)
    rw [Finset.sum_eq_single k]
    · -- 目标：`(if ¬↑k < d ∧ k = k then 1 else 0) * v k = v (Fin.last d)`。
      -- 同样**不能**用 `simp only [eq_self, and_true]`（`motive is not type correct`）；
      -- 用 `if_pos` 显式交出合取证明。
      rw [if_pos ⟨hk, rfl⟩, one_mul]
      exact congrArg v hlast
    · intro l _ hl
      -- 判别式是 `¬↑k < d ∧ k = l`；`hl : l ≠ k` 直接反驳合取的第二个分量。
      rw [if_neg (fun hc => hl hc.2.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h

@[simp] lemma iclQueryLabel_last (xq : Fin d → ℝ) : iclQueryLabel xq (Fin.last d) = 1 := by
  unfold iclQueryLabel
  have h : ¬ ((Fin.last d : Fin (d + 1)) : ℕ) < d := by simp
  rw [dif_neg h]

@[simp] lemma iclReadoutQuery_last (xq : Fin d → ℝ) : iclReadoutQuery xq (Fin.last d) = 0 := by
  unfold iclReadoutQuery
  have h : ¬ ((Fin.last d : Fin (d + 1)) : ℕ) < d := by simp
  rw [dif_neg h]

lemma iclQueryLabel_feature {xq : Fin d → ℝ} {i : Fin d} :
    iclQueryLabel xq ⟨(i : ℕ), by omega⟩ = xq i := by
  unfold iclQueryLabel
  rw [dif_pos i.isLt]

lemma iclReadoutQuery_feature {xq : Fin d → ℝ} {i : Fin d} :
    iclReadoutQuery xq ⟨(i : ℕ), by omega⟩ = xq i := by
  unfold iclReadoutQuery
  rw [dif_pos i.isLt]

/-- **`diag(0,1)` 的分数**：`Σ_l projLabelMatrix k l · vq l = (k = last) ? vq(last) : 0`。

即投影到标签位后，**只有 `k = Fin.last d` 这一行**给出 `vq(last)`，其余行为 0。
这正是路线 B「分数里取标签」的机制。

**⚠ 签名修正（F3，类型层）**：原签名是 `(k vq : Fin (d + 1) → ℝ)`——**`k` 被写成了向量**，
故 `k = Fin.last d` 类型错（`Fin (d+1) → ℝ` vs `Fin (d+1)`），并在下游 `k ⟨j,_⟩` 处爆
`application type mismatch`（日志 `473:25`）。`k` 是**指标**，应为 `Fin (d + 1)`。

**⚠ 修法记录（F3，证明层）**：`by tauto` 的三处都失败（`tauto failed to solve some goals`），
根因同上条：`by_cases hkl : k = Fin.last d` 的**两个分支都同时拥有 `hk` 与 `¬hk`/`hkl` 与 `¬hkl`**，
`tauto` 不做这类原子消解；且"标签位必为 `Fin.last d`"这一事实**必须显式给出**
（`Fin.ext` + `omega`），否则 `k = l` 分支无从收尾。 -/
lemma sum_projLabelMatrix_mul (k : Fin (d + 1)) (vq : Fin (d + 1) → ℝ) :
    ∑ l, projLabelMatrix k l * vq l
      = if k = Fin.last d then vq (Fin.last d) else 0 := by
  -- 同 `projMatrix_mulVec`：`simp only` 做 β-归约，`unfold` 不行。
  simp only [projLabelMatrix]
  by_cases hk : (k : ℕ) < d
  · -- k 是特征位：`¬ k < d` 为假 ⟹ Σ 体内每个 `if` 都取 0 分支；且 `k ≠ last`。
    -- 消 RHS 的 `if`：判别式是 `k = Fin.last d`；若成立则 `↑k = d`，与 `hk : ↑k < d` 矛盾。
    -- ⚠ **不能**写 `fun h => hk (by rw [h]; simp)`——`hk` 是**命题**不是函数，
    -- 报 `function expected at hk`。正解：`by rw [h]; simp` 得到的正是 `False`，用它 `exact`。
    rw [if_neg (fun h => by rw [h] at hk; exact absurd hk (by simp))]
    apply Finset.sum_eq_zero
    intro l _
    -- Σ 体的判别式是 `¬↑k < d ∧ k = l`：第一个分量与 `hk` 直接矛盾。
    rw [if_neg (fun hc => absurd hk hc.1), zero_mul]
  · -- k 是标签位：`¬ k < d` 在 `Fin (d+1)` 里逼出 `k = last`。
    have hlast : k = Fin.last d := Fin.ext (by simp [Fin.val_last]; omega)
    rw [if_pos hlast]
    rw [Finset.sum_eq_single k]
    · -- 同 `projLabelMatrix_mulVec` 的标签位分支：用 `if_pos` 交出合取证明。
      rw [if_pos ⟨hk, rfl⟩, one_mul]
      exact congrArg vq hlast
    · intro l _ hl
      rw [if_neg (fun hc => hl hc.2.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h

/-- **★ 定理一（第二条独立证明，路线 B）**：

用 `M = diag(0,1)`（分数取标签）、`h = [x_q ; 0]`（读出特征）、`v_q = [x_q ; 1]`
得到的注意力输出 = `η · Σᵢ yᵢ (xᵢ · x_q)`，与路线 A **同一个**结果。

**求和结构与路线 A 不同**：路线 A 在**值的标签槽位**取 `yᵢ`、在**分数**里做特征内积；
路线 B 在**分数**里取 `yᵢ`、在**读出**里做特征内积——两条独立路径汇合于同一标量。 -/
theorem icl_one_step_gd_via_state (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (xq : Fin d → ℝ) (η : ℝ) :
    linearSelfAttention (d := d) η (iclReadoutQuery xq) projLabelMatrix
        (iclQueryLabel xq) (fun i => iclToken (X i) (y i))
      = gdOneStepPredict X y xq η := by
  -- **F3 修法（实证）**：原稿 `congr 1; rw [Finset.sum_comm]` 把目标卡在
  -- `⊢ Fin (d + 1) = Fin d`（两个 `∑` 的**指标类型**被 `congr` 强行统一），
  -- 随后 `unfold` 又不做 β-归约 ⟹ `simp made no progress` / `function expected at hk`。
  --
  -- **本条的代数内容其实是"路线 A 的对偶"**，所以最稳的路线是：**复用路线 A 的机件**。
  -- 注意 `iclReadoutQuery xq = projFeature (iclQueryLabel xq) + xq 的散射`——
  -- 直接展开会发现两侧都不是同一求和结构，硬凑 `congr` 必然失败。
  -- **改用"两边各自归一到同一范式"**：把 LHS 一层层算成显式标量，再与 RHS 比对。
  --
  -- 关键局部事实（全部用已证的引理）：
  --   `V i k = iclToken (X i) (y i) k` 在 `k = last` 处是 `y i`、在特征位是 `X i ⟨k,_⟩`；
  --   分数 `Σ_l projLabelMatrix k l * iclQueryLabel xq l = if k = last then 1 else 0`。
  -- 故内层 `Σ_k V i k * (…)` 只剩 `k = last`，贡献 `y i * 1 = y i`。
  have hscore : ∀ i : Fin n,
      (∑ k, iclToken (X i) (y i) k
        * (∑ l, projLabelMatrix k l * iclQueryLabel xq l)) = y i := by
    intro i
    rw [Finset.sum_eq_single (Fin.last d)]
    · rw [sum_projLabelMatrix_mul, if_pos rfl, iclQueryLabel_last, mul_one, iclToken_last]
    · intro k _ hk
      rw [sum_projLabelMatrix_mul, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (Fin.last d)) h
  -- LHS = `η * Σ_j iclReadoutQuery xq j * (V i j * y i)` 中 `j` 只在特征位非零。
  have hout : ∀ i : Fin n,
      (∑ j, iclReadoutQuery xq j * (iclToken (X i) (y i) j * y i))
        = y i * ∑ l : Fin d, X i l * xq l := by
    intro i
    rw [Fin.sum_univ_castSucc]
    -- ⚠ `Fin.sum_univ_castSucc` 把 `∑_{Fin (d+1)}` 拆成 `∑_{Fin d} (…) + 末项`，
    -- 末项在**右边** = `0` ⟹ 用 `add_zero`（不是 `zero_add`，那是把 0 放左边）。
    have hz : iclReadoutQuery xq (Fin.last d) * (iclToken (X i) (y i) (Fin.last d) * y i) = 0 := by
      rw [iclReadoutQuery_last, zero_mul]
    rw [hz, add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    have hf : iclReadoutQuery xq (l.castSucc) = xq l := iclReadoutQuery_feature
    have ht : iclToken (X i) (y i) (l.castSucc) = X i l := iclToken_feature
    rw [hf, ht]
    ring
  -- **F3 修法（实证）**：`unfold` 不做 β-归约 ⟹ `V` 在目标里仍是 λ 项
  -- `(fun i => iclToken (X i) (y i)) i`，与一切引理模式都不同形。
  -- 先用 `simp only` 做 β-归约，再用 `Finset.sum_congr` 逐项把 `hscore i` 代进去
  -- （**不能**用 `simp only [hscore]`：`hscore` 是 `∀ i`，`simp` 不会自动实例化）。
  simp only [linearSelfAttention, attnState]
  -- **F3 修法（实证，第 3 轮）**：`apply congrArg (fun t => η * t)` 报
  -- `apply failed to unify η * ?m = η * ?m`——RHS 是**未展开的** `gdOneStepPredict …`
  -- （`simp only` 把它 β-归约成了 `∑ j, (∑ i, η * y i * X i j) * xq j`，
  -- 与 `← gdOneStepPredict_eq` 的模式**不再同形**，故那次 `rw` 也失败）。
  -- 正解：**不动 RHS**，改为把 RHS 的整体形状显式化 —— 先 `rw [gdOneStepPredict_eq]`
  -- 把 RHS 化到 `η * ∑ i, y i * ∑ j, X i j * xq j`，这样两侧都带外层 `η *`。
  rw [gdOneStepPredict_eq]
  apply congrArg (fun t => η * t)
  -- 目标：`∑ x, RO x * (∑ i, Vᵢ x * (∑ k, Vᵢ k * 分数 k)) = ∑ i, y i * ∑ j, X i j * xq j`。
  -- **F3 修法（最终，第 6 轮）**：`apply Finset.sum_congr rfl` 报
  -- `apply failed to unify ?m.sum ?m = ?m.sum ?m`——**两侧外层指标类型不同**
  -- （LHS `∑ x : Fin (d+1)`，RHS `∑ i : Fin n`），`Finset.sum_congr` 要求同型。
  -- 正解：**先把内层的 `∑ i : Fin n` 提到最外层**，再 `Finset.sum_congr`。
  -- 但 `RO x * ∑ i, …` 在 `∑ x` 体内，`rw [Finset.mul_sum]` 不穿透 binder
  -- ⟹ 必须**逐 `x` 先 `mul_sum`**（用 `Finset.sum_congr` 进体内），**然后**才能交换。
  -- 因此顺序是：`Finset.sum_congr`（进 `x` 体内）→ `mul_sum`（展开 `∑ i`）
  -- → `Finset.sum_comm`（交换）→ 此时才与 RHS 同型。
  -- 用 `conv_lhs` 避免 `apply` 在**未交换前**就去统一两侧外层。
  conv_lhs =>
    enter [2, x]
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  -- 现在目标是 `∑ x : Fin (d+1), RO x * (Vᵢ x * (∑ k, Vᵢ k * 分数 k)) = y i * ∑ j, X i j * xq j`。
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [show iclToken (X i) (y i) x * (∑ k, iclToken (X i) (y i) k
          * (∑ l, projLabelMatrix k l * iclQueryLabel xq l))
        = iclToken (X i) (y i) x * y i from by rw [hscore i]])]
  -- 内层恰好是 `hout i` 的左式。
  rw [hout i]

/-- **★★ 交叉校验（本文件的核心交付）**：两条**独立**证明路线给出**同一个**结果。

  - 路线 A（2307.03576 Thm 1）：`M = diag(I_d,0)` 在**分数**侧、`h* = [0,1]` 在**值**侧、
    `v_q = [x_q ; 0]`（零权）；
  - 路线 B（2306.00297 Thm 1）：`M = diag(0,1)` 在**分数**侧、`h = [x_q ; 0]` 在**读出**侧、
    `v_q = [x_q ; 1]`。

两者都等于 `gdOneStepPredict`（一步 GD 预测）。若任一路线的形式化有误，此定理会失败。

**诚实标注**：路线 B 的 `v_q = [x_q ; 1]` 是对 2306.00297 `P₀` 语义的**形式化实现选择**
（该文用 `P₀` 配合参数化 `Q₀`，并未逐字写出本文件的 `h`/`v_q` 分解）。
本文件证的是：**该对偶构造给出同一答案**——这是「两条独立证明同一现象」在代数内核上的体现，
**不**意味着本文件的 `iclQueryLabel` 就是该文记号的原样翻译。 -/
theorem icl_two_proofs_agree (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (xq : Fin d → ℝ) (η : ℝ) :
    linearSelfAttention (d := d) η iclReadout projMatrix
        (iclQuery xq) (fun i => iclToken (X i) (y i))
      = linearSelfAttention (d := d) η (iclReadoutQuery xq) projLabelMatrix
        (iclQueryLabel xq) (fun i => iclToken (X i) (y i)) := by
  rw [icl_one_step_gd, icl_one_step_gd_via_state]

/-! ## 7. 与 `RealLeastSquares` / `RealNormalEquation` 的对接

`RealLeastSquares.residual_orthogonal_of_global_min` 用变分/fderiv 证明
「全局最小 ⟺ 残差正交」。本节的桥：**在 `w₀ = 0` 处，一步 GD 的更新恰是法方程的右端**
`Xᵀy`，与 `RealNormalEquation` 的「驻点 ⟺ 满足」语言打通。 -/

/-- 法方程右端 `(Xᵀy)ⱼ = Σᵢ yᵢ Xᵢⱼ`（对接 `RealNormalEquation` 的 `XᵀXw = Xᵀy`）。 -/
def normalEquationRHS (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ) : Fin d → ℝ :=
  fun j => ∑ i, y i * X i j

/-- **对接定理**：一步 GD（从 `w₀ = 0`）的更新方向恰为法方程右端 `Xᵀy`。

`w₁ = 0 − η·∇L(0)`，而 `−∇L(0) = Σᵢ yᵢxᵢ = Xᵀy`。
这使 ICL 的「注意力输出」与 `RealLeastSquares`/`RealNormalEquation` 的
「最小二乘闭式解」在同一代数对象上汇合。 -/
theorem gd_zero_direction_eq_normal_equation_rhs (X : Fin n → Fin d → ℝ)
    (y : Fin n → ℝ) :
    (fun j => -lstsqGrad X y (fun _ => 0) j) = normalEquationRHS X y := by
  funext j
  rw [lstsqGrad_zero]
  unfold normalEquationRHS
  rw [neg_neg]

/-- 一步 GD 的更新向量就是 `η • Xᵀy`（法方程右端），这是上一条的分量形式的整体版。 -/
theorem gd_one_step_eq_eta_smul_normal_rhs (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (η : ℝ) :
    (fun j => η * normalEquationRHS X y j)
      = fun j => ∑ i, η * y i * X i j := by
  funext j
  unfold normalEquationRHS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **反例（诚实降级登记）**：断言「从 `w₀ = 0` 一步 GD 就得到最小二乘解」**为假**。

机器验证的反例：`d = 1`、`n = 2`、`X = (1, 1)`、`y = (0, 2)`。
最小二乘解（`XᵀXw = Xᵀy`）给 `w = 1`，而一步 GD（`η = 1`）给 `w₁ = Σᵢ yᵢxᵢ = 2 ≠ 1`。
下面直接断言「`Σᵢ yᵢxᵢ ≠ 1`」，即两者不等。

价值：这正是 2307.03576 与 `RealLeastSquares` 的**边界**——
ICL 学到的是一步 GD（**近似**算法），而**不是**最小二乘解本身。
若把命题写成「attention = 最小二乘解」即为假命题（本库 `doc/10` 的反例文化）。 -/
theorem gd_not_exact_least_squares_counterexample :
    ∃ (X : Fin 2 → Fin 1 → ℝ) (y : Fin 2 → ℝ),
      normalEquationRHS X y ⟨0, by omega⟩ ≠ 1 := by
  refine ⟨fun _ _ => 1, ![0, 2], ?_⟩
  unfold normalEquationRHS
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num

/-! ## 8. 预条件版本（原文 Theorem 2 的代数内核）

2307.03576 Theorem 2：`Σ` 为数据协方差时，全局极小 ⟹ 实现以 `Σ⁻¹` 为预条件的
梯度下降，输出 `η·Σᵢ yᵢ(Σ⁻¹xᵢ)ᵀx_{n+1}`。本文件给出其**代数形式**（不含概率部分）。 -/

/-- 预条件一步 GD 的预测（原文 Thm 2 的右侧）：`η·Σᵢ yᵢ (P xᵢ)·x_q`，`P = Σ⁻¹`。 -/
def precondGDOneStepPredict (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (xq : Fin d → ℝ) (P : Fin d → Fin d → ℝ) (η : ℝ) : ℝ :=
  η * ∑ i, y i * (∑ j : Fin d, (∑ k, P j k * X i k) * xq j)

/-- **定理二（预条件，Thm 2 的代数内核）**：把 `xᵢ` 换成 `P xᵢ`（`P = Σ⁻¹`），
注意力输出的同一代数形式即预条件一步 GD。 -/
theorem icl_precond_one_step (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (xq : Fin d → ℝ) (P : Fin d → Fin d → ℝ) (η : ℝ) :
    linearSelfAttention (d := d) η iclReadout projMatrix
        (iclQuery xq) (fun i => iclToken (fun j => ∑ k, P j k * X i k) (y i))
      = precondGDOneStepPredict X y xq P η := by
  -- **F3**：`unfold` 不做 β-归约 ⟹ `rw [icl_attention_readout_eq]` 匹配不到。
  -- 用 `simp only` 打开两个定义做 β-归约，再在 `∑ i` / `∑ j` 层逐项化简。
  --
  -- 结构与路线 A 完全同构：`iclReadout`/`projMatrix` 侧的化简（`sum_iclReadout_mul`
  -- 与 `attnState_projFeature_last`）与 `X` 的具体取值无关——只用到
  -- 「`V i (last) = y i`」与「`V i` 的特征位 = `xᵢ`」。这里 `xᵢ := P·X i`，
  -- 故把 `iclToken_feature` 用在 `fun j => ∑ k, P j k * X i k` 上即可。
  --
  -- ⚠ 原稿在 `congr 1` 处失败（`apply failed to unify ?m.sum ?m = ?m.sum ?m`）：
  -- `congr 1` 会先统一两侧 `∑` 的 binder 与指标类型，遇到 `∑ i`/`∑ j` 交错就卡住。
  -- 正解：**逐层 `Finset.sum_congr`**（不用 `congr`），每层只在**最外层**改写。
  -- **F3 修法（实证）**：`rw [attnState_projFeature_last]` 报
  -- `did not find instance of the pattern attnState projMatrix ?vq ?V (Fin.last ?m)`——
  -- 因为 `congr 1` 后目标里的 `V` 是**未 β-归约的 λ 项** `(fun i => iclToken … i) i`，
  -- 与引理模式里的 `V` 不同形。正解：**先 `simp only` 做 β-归约**把 λ 消掉，
  -- 再用引理；或直接 `show`/`conv` 指明 `V`。
  simp only [linearSelfAttention, precondGDOneStepPredict]
  rw [sum_iclReadout_mul]
  -- ⚠ 此时目标里的 `V` 仍是 λ 项 `(fun i => iclToken (fun j => ∑ k, P j k * X i k) (y i)) i`
  -- （`simp only` 打开了外层定义，但**没有**把 `V i` 这个**应用** β-归约掉），
  -- 故 `rw [attnState_projFeature_last]` 报
  -- `did not find instance of the pattern attnState projMatrix ?vq ?V (Fin.last ?m)`。
  -- 正解：先用 `show` 把 λ 应用显式写成函数本身，再让引理模式匹配。
  -- 这里不再手写长 `show`，而是**用 `icl_attention_readout_eq` 的泛化版思路**：
  -- 直接把 `attnState_projFeature_last` 的证据在**外层**以 `have` 给出。
  have hmain : ∀ V : Fin n → Fin (d + 1) → ℝ,
      attnState (d := d) projMatrix (iclQuery xq) V (Fin.last d)
        = ∑ i, V i (Fin.last d)
            * (∑ j : Fin d, V i ⟨(j : ℕ), by omega⟩ * xq ⟨(j : ℕ), by omega⟩) := by
    intro V
    rw [attnState_projFeature_last]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [iclQuery_feature]
  rw [hmain]
  -- 目标：`η * ∑ i, V i (last) * (∑ j, V i ⟨j,_⟩ * xq ⟨j,_⟩) = η * ∑ i, y i * ∑ j, P·X i j * xq j`。
  -- ⚠ `congr 1` 报 `apply failed to unify ?m.sum ?m = ?m.sum ?m`——两侧 `∑` 的
  -- **binder 与内层形状都不同**（LHS 内层是 `∑ j, V i … * xq …`，RHS 是 `y i * ∑ j, …`）。
  -- 用 `congrArg (fun t => η * t)` 明确剥掉外层 `η`，再逐层 `Finset.sum_congr`。
  apply congrArg (fun t => η * t)
  apply Finset.sum_congr rfl
  intro i _
  -- LHS 的 `V i (last) = y i`；内层 `V i ⟨j,_⟩ = ∑ k, P j k * X i k`、`xq ⟨j,_⟩ = xq j`。
  rw [iclToken_last]
  apply congrArg (fun t => y i * t)
  -- ⚠ 这里**必须**用 `Finset.sum_congr` 逐项改，`apply Finset.sum_congr` 报
  -- `apply failed to unify ?m.sum ?m = ?m.sum ?m`——两侧 `∑ j : Fin d` 的**内层形状**
  -- 在改写前还不同（`V i ⟨j,_⟩ * xq ⟨j,_⟩` vs `(∑ k, …) * xq j`），
  -- `Finset.sum_congr rfl` 只要求指标集相同。
  apply Finset.sum_congr rfl
  intro j _
  -- 剩下的目标：`iclToken (fun j => ∑ k, P j k * X i k) (y i) ⟨↑j, _⟩ = ∑ k, P j k * X i k`
  -- ⚠ `iclToken_feature` 的模式要求**特征位**是 `⟨(i:ℕ), by omega⟩` 形式；
  -- 这里下标是 `⟨↑j, ⋯⟩`（`j : Fin d`），值证明项不同 ⟹ `rw` 匹配不到
  -- （日志 `unsolved goals: ⊢ iclToken … ⟨↑j, ⋯⟩ = ∑ k, …`）。
  -- 正解：用 `iclToken_feature` 的**显式实例化**（把 `i` 指定为 `j`），
  -- 或直接 `simp only [iclToken]` 后 `dif_pos`。
  simp only [iclToken]
  rw [dif_pos j.isLt]

/-- **退化校验**：`P = I` 时预条件版本 = 无预条件版本（Thm 2 ⟹ Thm 1）。

**⚠ 修法记录（F3）**：原稿的 `congr 1` 级联（3 层）在末层被 Lean 解成
**外延/函数等式**目标（日志 `661:2`：`?m.sum ?m = ?m.sum ?m` 与两侧不统一），
因为 `congr 1` 在 `∑` 上会先统一 binder 与指标类型，遇到 `if j = k then 1 else 0`
这类**需要 `Finset.sum_eq_single` 才能推进**的目标就卡住。
正解：把 `P = fun j k => if j = k then 1 else 0` 的代入做成**局部 `have`**，
并用 `Finset.sum_eq_single j` 把内层单点和显式求出（**不用 `congr`**）。 -/
theorem icl_precond_identity_recovers_thm1 (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (xq : Fin d → ℝ) (η : ℝ) :
    precondGDOneStepPredict X y xq (fun j k => if j = k then 1 else 0) η
      = gdOneStepPredict X y xq η := by
  -- **F3 修法（实证）**：原稿的 `congrArg (fun t => η * t)` 两侧 `∑` 的 **binder 顺序不同**
  -- （LHS 是 `∑ i, y i * (∑ j, …)`，RHS 是 `∑ j, (∑ i, …) * xq j`），
  -- 报 `apply failed, failed to unify`（日志 `692:2`）。
  -- 正解：**两侧各自归约到同一范式** `η * ∑ i, ∑ j, y i * X i j * xq j`，
  -- 再 `rfl`/`ring` 收尾——不要试图让 `congrArg` 去猜 binder 对应。
  simp only [precondGDOneStepPredict, gdOneStepPredict]
  -- 左侧内层：`(I xᵢ)_j = X i j`（单点和）。
  have hinner : ∀ (i : Fin n) (j : Fin d),
      (∑ k, (if j = k then (1 : ℝ) else 0) * X i k) = X i j := by
    intro i j
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, one_mul]
    · intro k _ hk
      rw [if_neg (fun h => hk h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [hinner]
  -- **F3 修法（实证，第 5 轮）**：`rw [Finset.sum_mul]` 报
  -- `did not find instance of the pattern (∑ i ∈ ?s, ?f i) * ?a`——
  -- 因为目标里 RHS 是 `∑ j, (∑ i, …) * xq j`，那个 `(∑ i, …) * xq j` **在 `∑ j` 体内**，
  -- 而 `Finset.sum_mul` 的 `rw` 不能穿透 binder。正解：用 `simp only [Finset.sum_mul]`
  -- 在**整个目标**上一次性展开（`simp` 会进 binder），再用 `Finset.sum_comm` 交换。
  -- 注意 `simp only` 也会改 LHS，故 LHS 的对应形状会在同一步被一起规整。
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- 两侧现在都是 `∑ i, ∑ j, …` 形状（LHS 外层 `∑ i : Fin n`，RHS 经 `sum_comm` 后同型）。
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ## 9. 步长 `η` 的代数刻画（原文 Theorem 1 中 `η` 的角色）

原文的 `η` 是唯一使该构造成为全局极小的值。其**一维二次型**结构为：
在固定方向上，预训练损失关于 `η` 是 `a·η² − 2b·η + c`，唯一极小点为 `η* = b/a`。
这与原文 `η = E[ŵᵀXᵀy]/E[yᵀXXᵀy]` 的**分式结构一致**（分子一次项、分母二次项）。

诚实标注：本文件**只证一维二次型的代数极小点**，
**不**断言该 `η*` 等于原文那个期望之比——
把「期望损失」展开成该二次型需要 Gaussian 期望（mathlib 4.14 无 `multivariateGaussian`），
这是明确的**未做**项。 -/

/-- 一维二次型 `q(η) = a·η² − 2b·η + c`。 -/
def etaQuadratic (a b c η : ℝ) : ℝ := a * η ^ 2 - 2 * b * η + c

/-- **配方法**：`q(η) − q(b/a) = a·(η − b/a)²`（`a ≠ 0`）。

**实现注记（确定性路线）**：不用 `field_simp; ring`——`field_simp` 在遇到"除数是自由变量"时
**可能已把主目标关掉**，其后跟 `ring` 会报 `no goals to be solved`（STYLE §4 已记录）。

**⚠ 修法记录（F3，本任务硬纪律：不用 `field_simp` 收尾）**：原稿手搓了一串
`have key / hcombo / hrhs`，末行 `rw [key, hcombo, hrhs, hba]; ring` **仍留下未闭合目标**
（日志 `695:79`：`⊢ a * η ^ 2 - η * b * 2 + b ^ 2 * a⁻¹ = a * η ^ 2 + (a * b ^ 2 * a⁻¹ ^ 2 - η * b * 2)`）。
根因：`ring` **不消耗假设**（`hba : a * (b/a) = b` 是"外部事实"），
而手写的 `key`/`hrhs` 与 `ring` 的归一形**并不同形**（`b * (b/a)` vs `b ^ 2 * a⁻¹`、`η * b * 2` vs `2 * b * η`）。

**正解（不用 `field_simp`）**：把 `b / a` 记作 `b * a⁻¹`（`div_eq_mul_inv`），
再用 `hba : a * (b * a⁻¹) = b` 把目标里出现的 `a * (b * a⁻¹)` **一次性替换成 `b`**，
之后目标退化为纯 `* / ^ / ⁻¹` 的多项式恒等式，`ring` 一次闭合。
关键：`hba` 必须写成 `a * (b * a⁻¹) = b` 的**乘积形状**（与 `div_eq_mul_inv` 后的目标同形），
否则 `rw` 匹配不上——这正是原稿失败的原因。 -/
lemma etaQuadratic_sub_min (a b c η : ℝ) (ha : a ≠ 0) :
    etaQuadratic a b c η - etaQuadratic a b c (b / a) = a * (η - b / a) ^ 2 := by
  -- **F3 最终路线（`field_simp`-free，锁定探针 `_probe_f3_eta.lean` 实证 exit 0）**：
  -- ① 用 `div_eq_mul_inv` 把 `b / a` 换成 `b * a⁻¹`；
  -- ② 用 `hba : a * (b * a⁻¹) = b`（`← mul_assoc` + `mul_comm` + `mul_inv_cancel₀`）把
  --    **所有** `a * (b * a⁻¹)` 形式的子项换成 `b`；其中 `(b/a)^2` 那一项要先
  --    用 `hsq : a * (b * a⁻¹)^2 = b * (b * a⁻¹)`（`pow_two` + `← mul_assoc` + `hba`）降幂；
  -- ③ 右式的 `a * (η - b*a⁻¹)^2` 用 `key` 展开成 `a*η^2 - 2*(a*(b*a⁻¹))*η + a*(b*a⁻¹)^2`，
  --    之后全部子项都是 `hba`/`hsq` 的模式 ⟹ 一次 `rw` 全换掉，最后 `ring` 闭合。
  -- ⚠ 关键坑（多轮实测）：`hba` 的目标是**右结合**的 `a * (b * a⁻¹) = b`，
  -- 直接 `rw [mul_assoc]` 报 `did not find instance of the pattern ?a * ?b * ?c`；
  -- 必须写 `← mul_assoc` 再 `mul_comm a b` 才能暴露 `a * a⁻¹`。
  have hba : a * (b * a⁻¹) = b := by
    rw [← mul_assoc, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  unfold etaQuadratic
  simp only [div_eq_mul_inv]
  have hsq : a * (b * a⁻¹) ^ 2 = b * (b * a⁻¹) := by
    rw [pow_two, ← mul_assoc, hba]
  rw [hsq]
  have key : a * (η - b * a⁻¹) ^ 2
      = a * η ^ 2 - 2 * (a * (b * a⁻¹)) * η + a * (b * a⁻¹) ^ 2 := by ring
  rw [key, hba, hsq]
  ring

/-- `q(η*) ≤ q(η)`，其中 `η* = b/a`（`a > 0`）——一维二次型的全局极小点。 -/
theorem etaQuadratic_min_at (a b c : ℝ) (ha : 0 < a) (η : ℝ) :
    etaQuadratic a b c (b / a) ≤ etaQuadratic a b c η := by
  have key := etaQuadratic_sub_min a b c η (ne_of_gt ha)
  nlinarith [sq_nonneg (η - b / a), key]

/-- **`η` 的最优性刻画（唯一性）**：`a > 0` 时 `η* = b/a` 是 `q` 的**唯一**全局极小点。 -/
theorem etaQuadratic_argmin_unique (a b c : ℝ) (ha : 0 < a) (η : ℝ)
    (h : etaQuadratic a b c η ≤ etaQuadratic a b c (b / a)) :
    η = b / a := by
  have key := etaQuadratic_sub_min a b c η (ne_of_gt ha)
  have hle : etaQuadratic a b c (b / a) ≤ etaQuadratic a b c η := etaQuadratic_min_at a b c ha η
  have hzero : a * (η - b / a) ^ 2 = 0 := by linarith
  have hsq : (η - b / a) ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt ha)
  have := pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
  linarith

end Lattice
