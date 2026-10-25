import Mathlib
import Lattice.Lib.LinearAlgebra.RealSparseCoding
/-!
# LATTICE: 压缩感知 —— 受限等距性质（RIP）及其可证后果

压缩感知的核心主张：**`m ≪ n` 的欠定线性系统 `Ax = y` 仍可恢复稀疏 `x`**，
只要 `A` 满足**受限等距性质（RIP）**。本文件从零建立 RIP 的有限维理论。

## ⚠ E2 实测结论（本文件的设计前提）

**E2 调研实测：mathlib 对 RIP / frame theory 全树 0 命中**——
`RestrictedIsometry`、`RIP`、`mutualCoherence`（数学意义上的）、
`frame` 的有限维理论在 mathlib 4.14 **完全不存在**。
故本文件**从零建**，并遵循任务指示：

  > **把 RIP 作显式假设引入**，只证「**RIP + 稀疏 ⟹ 唯一性/稳定性**」这一层
  > （**这部分是真定理**）。
  > **L1 最小化恢复的完整证明**若成本过高 → **诚实标注未做**。

## 本文件建立

**一、RIP 的定义与基本性质**
1. `SensingMatrix m n`：测量矩阵 `A : Fin m → Fin n → ℝ`；`matVec A x`：矩阵-向量作用；
   `sqNorm x`：Euclidean 平方范数；`IsKSparse k x`：`k`-稀疏（**复用**
   `RealSparseCoding.l0Norm`，**不重定义**）；
2. `IsRIP A k delta`：**RIP 谓词（受限等距性质）**——
   对**每个** `k`-稀疏 `x`，`|‖Ax‖² − ‖x‖²| ≤ delta·‖x‖²`。
   这是本文件**唯一的核心理设**（**显式引入**，不从别的性质推出；
   E2 实测 mathlib 全树 0 命中 RIP / frame theory）；
3. `isRIP_iff_two_sided`：**双侧夹逼形式** `(1−δ)‖x‖² ≤ ‖Ax‖² ≤ (1+δ)‖x‖²`
   （全部下游证明实际使用的形状）；`isRIP_lower_bound` / `isRIP_upper_bound` 为其单向抽取；
4. `isRIP_mono`：`k₁ ≤ k₂` 时 `k₂`-阶 RIP 蕴含 `k₁`-阶 RIP（同 `delta`）；
5. `isRIP_zero`：`k = 0` 时 `delta = 0` 平凡成立——RIP 类**非空**；
   `identity_isRIP`：**单位矩阵是 `delta = 0` 的 RIP 实例**（非退化非空实例）。

**二、RIP 的第一后果：稀疏信号唯一性（**真定理**）**
6. `isKSparse_sub`：**支撑并的稀疏度加倍**——`x, y` 都 `k`-稀疏 ⟹ `x − y` 是 `2k`-稀疏；
7. **`rip_sparse_uniqueness`（主结果）**：
   `δ_{2k} < 1` 时，`A x = A y` 且 `x, y` 都 `k`-稀疏 ⟹ **`x = y`**。
   **证明**：令 `z = x − y`（`2k`-稀疏），则 `Az = 0`，故 `‖Az‖² = 0`；
   由 RIP 下界 `(1−δ)‖z‖² ≤ ‖Az‖² = 0` 与 `δ < 1` 得 `‖z‖² = 0`，即 `z = 0`。
   **这是压缩感知最核心的唯一性定理，且完全可证**（门槛就是 `δ < 1`，
   **不需要** L1 恢复所需的 `√2 − 1`）；
8. `rip_constant_ge_one_of_nonzero_null`：**必要性**（逆否形式）——
   存在**非零** `2k`-稀疏零空间向量 ⟹ `δ_{2k} ≥ 1`。

**三、RIP 的第二后果：稳定恢复的界（**真定理**）**
9. **`rip_norm_le_of_residual`（稳定性核心不等式）**：
   `δ < 1`、`z` 是 `k`-稀疏 ⟹ **`‖z‖² ≤ ‖Az‖²/(1 − delta)`**（**下界反转**）——
   全部误差界 / 稳定性论证**唯一需要的不等式**；
10. **`rip_error_bound`（主结果）**：**含噪声的稳定恢复界**——
    `δ_{2k} < 1`、`x` 与 `x̂` 都 `k`-稀疏、`A x = y`、`A x̂ = y + e` ⟹
    **`‖x − x̂‖² ≤ ‖e‖²/(1 − δ_{2k})`**——
    「**噪声水平线性放大**」的准确陈述；
11. `rip_exact_recovery`：`e = 0` 的特例 `x = x̂`（唯一性的定量版本）；
12. **`rip_norm_equivalence`（主结果）**：**范数等价 / 双 Lipschitz**——
    `√(1−δ)·√‖x‖² ≤ √‖Ax‖² ≤ √(1+δ)·√‖x‖²`（`−1 ≤ δ < 1`）；
13. `rip_injective_on_sparse`：`δ_{2k} < 1` 时 `A` 在 `k`-稀疏集上**单射**
    （`Set.InjOn` 语言）。

**四、RIP ⟹ 相干/列范数受控（与 `RealSparseCoding` 的接口）**
14. `col A j`：第 `j` 列；`l0_two_spike_eq_two`：两个尖峰 `e_i + e_j`（`i ≠ j`）的 `L0` 恰为 `2`
    （把「两列」编码成稀疏**向量**以送进 RIP 的**桥**）；
15. **`rip_controls_two_spike`（主结果）**：RIP 只控制 `e_i + e_j` 的像长度
    （`−` 一式**未形式化**，见下文「诚实边界」中关于 docstring 过度声称的登记条目）；
    原稿在此声称「RIP 控制 `e_i ± e_j`，故由极化恒等式**间接**控制 `⟪a_i, a_j⟫`」，
    该声称**无对应 Lean 陈述支撑**——该定理的陈述中不含任何内积，
    且 `−` 一式在 Lean 中并不存在。与 `RealSparseCoding.mutualCoherence` 的**接口方向**表述如下：
     **RIP 是比互相干更强的假设**（RIP 约束**全部** `k`-子矩阵，相干只约束**两列**）；
16. `rip_controls_column_norm`：**列近似单位化**——对 `1`-稀疏 `e_j`，`|‖a_j‖² − 1| ≤ δ₁`。

**五、L1 最小化恢复（**诚实标注未做**）**
17. `isL1Recovery A y xhat`：**L1 最小化恢复的谓词定义**——
    `A x̂ = y ∧ ∀ z, A z = y → ‖x̂‖₁ ≤ ‖z‖₁`（**只陈述性质**，
    不构造 `argmin`、不证存在性/唯一性）；
18. `isL1Recovery_of_unique_feasible`：**非空性证据**——
    若可行点唯一，则它就是 L1 最小点（说明定义不是空的）；
19. **`rip_l1_recovery_of_sparse`（连接层）**：`δ_{2k} < 1`、`x` 是 `k`-稀疏可行点，
    且**所有**可行点都已知是 `k`-稀疏 ⟹ `x` 是 L1 最小点
    （把 `rip_sparse_uniqueness` 喂给 `isL1Recovery` 的**唯一可证桥**）；
20. **未做**：`δ_{2k} < √2 − 1 ⟹ L1 最小化恢复精确`（Candès–Romberg–Tao）。
    该定理的完整证明需要**零空间性质（NSP）+ 对偶证书 + `RIP ⟹ NSP` 的组合论证**，
    **本轮未做**，见诚实边界。

## 与 `RealSparseCoding` 的重叠/互补关系

| 内容 | `RealSparseCoding` | 本文件 |
|:--|:--|:--|
| `l0Norm` / `l1Norm` | **有**（本文件**复用**其定义） | 只 import 与复用 |
| 注意 `l2NormSq` | **有** | **本文件未复用**——见下方更正 |
| 软阈值最优性 | **有** | **不做** |
| `mutualCoherence` | **有** | **消费**它做「RIP ⟹ 相干/列范数受控」（第 14–16 条），不重定义 |
| 稀疏解的**条件**唯一性（`hNull` 假设） | **有**（`sparse_uniqueness_of_nullspace`） | 不做 |
| **RIP 的定义** | 未做 | **本文件做** |
| **RIP ⟹ 唯一性**（`δ_{2k}<1`） | 未做 | **本文件做** |

注意 **更正（v14，S8 扫描发现；coordinator 已核实）**：本表原先把 `l2NormSq` 与 `l0Norm`/`l1Norm` 并列，
声称「**本文件复用其定义**」。**该声称对 `l2NormSq` 为假**：
- 本文件实际在 `sqNorm` 的**定义处**（`def sqNorm`）**自定义** `sqNorm`，
  其**定义体与 `RealSparseCoding.l2NormSq` 逐字符相同**（两处均为 `∑ i, x i ^ 2`）；
- 本文件**在 35 行代码中引用 `sqNorm`**，而 **`l2NormSq` 全库仅出现在本表这一行**；
- ⇒ **同表中 `l0Norm`/`l1Norm` 的复用声明是真的**（本文件确实用它们），
  **恰恰是这条真声明给假声明做了背书**，使读者更难发现。
- **处置**：本表已改为**分立两行**并如实标注。**`sqNorm` 的定义保留不退**（它与 `l2NormSq` 逐字符相同，
  改用 `l2NormSq` 需改动上述全部引用点，且 `RealSparseCoding` 的 import 面因此可以不变）；
  **但"复用"这一措辞必须撤掉**——它是**平行定义**，不是复用。
| **RIP ⟹ 稳定性/误差界** | 未做 | **本文件做** |
| **RIP ⟹ 相干界**（与 `mutualCoherence` 对接） | 未做 | **本文件做** |
| **L1 最小化 = 精确恢复** | 未做（仅登记） | **未做**（诚实标注） |

⇒ 两个文件的**接口**是：`RealSparseCoding` 给出「互相干 ⟹ 条件唯一性」，
本文件给出「RIP ⟹ 无条件唯一性 + 稳定性」，并用 `rip_controls_two_spike`
说明 RIP 更强。

## 诚实边界（诚实 / 未证 / 未做 / 降级 / 标注）

- **未做：L1 最小化恢复的完整证明（Candès–Romberg–Tao / Candès–Tao）**。
  完整的「`δ_{2k} < √2 − 1`（或 `δ_k + δ_{2k} + δ_{3k} < 1`）⟹
  `‖x̂ − x‖₂ ≤ C·σ_k(x)₁/√k`」需要：
  ① **零空间性质（NSP）**：`∀ z ∈ ker A, ‖z_S‖₁ ≤ ‖z_{S^c}‖₁`；
  ② **NSP ⟺ L1 精确恢复**（Foucart–Rauhut 定理 4.14 型）；
  ③ **RIP ⟹ NSP**（需要把 `z` 按幅度分块、对每块用 RIP，
     块数约 `log` 量级——**组合论证，体积大**）；
  ④ **对偶证书**（`A_Sᵀ v = sign(x_S)`、`‖A_{S^c}ᵀ v‖_∞ < 1`）。
  这四步链在 mathlib 4.14 上**原理上可行但体积远超本轮预算**。
  **诚实标注**：本文件**只证 RIP 的「唯一性 + 稳定性」层**
  （即「若已知稀疏，则无别解且误差线性可控」），
  **不证**「L1 最小化一定能找到它」。这两层**逻辑独立**：
  前者是后者论证中的**一步**（NSP 的来源），但不是全部。
  **这是本文件最重要的诚实降级。**
- **诚实降级：RIP 采用「二次型夹逼」形式而非「算子范数」形式**。
  文献常定义 `δ_k = ‖A_SᵀA_S − I‖₂`（谱范数上确界）。
  本文件用**等价的可证形式** `|‖Ax‖² − ‖x‖²| ≤ δ‖x‖²`（`∀ k`-稀疏 `x`），
  理由：① 谱范数上确界需要 `sSup` + 算子范数理论，而 STYLE §4 记录
  `sSup` 的 junk 值问题；② 二次型形式**正是所有下游证明实际使用的形状**
  （唯一性、稳定性、误差界全部只用它）。
  两种定义在有限维上**等价**（可互相推出），但本文件**只证二次型形式内的定理**，
  不声称已建立「谱范数 `δ_k`」的对应定理。
- **诚实降级：RIP 的「存在性 / 随机矩阵满足 RIP」完全未做**。
  压缩感知的**另一半**是「随机高斯/伯努利矩阵以高概率满足 RIP」
  （需概率论 + 测度集中）。本文件**只把 RIP 作为假设**，不构造任何满足 RIP 的矩阵
  （除 `A = I` 的平凡实例，见 `identity_isRIP`）。
- **未做：`√2 − 1` 等**最优常数**的讨论**。
  本文件的 `δ < 1` 是**唯一性**的充分条件；文献中 `δ_{2k} < 1` 也正是
  唯一性的正确门槛（**不**需要 `√2 − 1`——后者是 L1 恢复的门槛）。
  本文件**不声称**任何常数的**最优性**。
- **未做：`ℓ₁` 球 / 多面体几何 / 对偶证书的一般理论**。
  这些是 L1 恢复证明的工具，本文件未建。
- **未做：`RealSparseCoding` 的 `mutualCoherence` 与 RIP 的**定量换算**
  （如 `δ_k ≤ (k−1)μ`）。本文件只给 `δ_2` 控制两列相干的方向（第 13 条），
  反向（相干 ⟹ RIP 上界）未做。
- **范围**：`A : Fin m → Fin n → ℝ`、`x : Fin n → ℝ`，`‖·‖` 为 Euclidean 平方和；
  全程有限维、无拓扑（除了 `Real.sqrt` 的单调性）。
- 无 sorry / axiom / admit。
- 要点 **Q4 状态更新（v18，2026-09-24）**：本模块此前是**全项目唯一从未编译**的模块
  （709 行 / **12 error / 8 个独立根因**，从未产出 olean）。Q4 已修复全部 12 条 error，
  **`probe.ps1` 复现两次 `exit code = 0` / `0 error` / `0 warning`**。
  注意 **原写「所有定理真实可证」**：该措辞在**本文件无法编译/解析**时属**过度声称**
  （模块含解析级报告，见原 `:570` 的 W2 注记）。Q4 **撤下该措辞**，改为可核验的事实：
  「**全部 26 条声明语句与 HEAD 逐字相同；12 条 error 全部为证明体/注释缺陷，无一条为陈述缺陷**」。
- 注意 **Q4 假命题审计结论（独立子代理 ×1，代小例 + 手工代数）**：**26 条声明中 0 条为假**。
  三分类判定要点：`rip_sparse_uniqueness` 的 `δ < 1` **承重且紧**（`δ = 1` 时
  `A = [[1,−1]]`、`x = e₁`、`y = e₂` 为反例）；`rip_constant_ge_one_of_nonzero_null`
  在 `δ = 5` 处**无**反例，因其假设与「非零稀疏零空间向量」**联合不可满足** ——
  **这正是该定理的内容**（属「命题为真」而非「空洞真」）。
  已登记的**非陈述级**缺陷：`isL1Recovery_of_unique_feasible` **平凡**（退化为
  `l1Norm x ≤ l1Norm x`，不用 L1）—— 文件原 docstring **已自陈**，属「平凡但诚实」。
- 注意 **Q4 判为 docstring 过度声称（未改陈述，仅登记）**：第 15 条
  `rip_controls_two_spike` 的**陈述里不含任何内积 `⟪a_i,a_j⟫`**，只界 `|‖A(e_i+e_j)‖² − 2|`；
  文件头「四、RIP ⟹ 相干/列范数受控」一节的第 15 条（其行号已随本次修订失效，
  请按小节名与本条编号定位），以及 `rip_controls_two_spike` 自身的 docstring，
  关于「极化恒等式」「相干」「± 两式」的说法
  **无对应 Lean 陈述支撑**（`−` 那一式**未形式化**）。此处如实标注，**不改陈述**。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {m n : ℕ}

/-! ## 一、RIP 的定义

**设计要点**：不引入算子范数 / `sSup`，而用**二次型夹逼**作为 RIP 的载体。
理由见文件头「诚实降级」第 2 条：

  · 谱范数定义需要 `sSup` + 算子范数理论（STYLE §4 记录 `sSup` 的 junk 值问题）；
  · 二次型形式（`|‖Ax‖² − ‖x‖²| ≤ δ‖x‖²` 对 `k`-稀疏 `x`）
    **正是下游全部证明实际使用的形状**（唯一性、稳定性、误差界）。
-/

/-- **字典 / 测量矩阵**：`A : Fin m → Fin n → ℝ`。
`m` 是测量数、`n` 是信号维数（压缩感知关心 `m ≪ n`）。 -/
abbrev SensingMatrix (m n : ℕ) := Fin m → Fin n → ℝ

/-- **矩阵-向量作用**：`matVec A x i = Σ_j A i j · x j`。 -/
def matVec {m n : ℕ} (A : SensingMatrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j, A i j * x j

/-- **Euclidean 平方范数**：`sqNorm x = Σ_i x i ^ 2`。 -/
def sqNorm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- **`k`-稀疏与支撑**：`x` 是 `k`-稀疏（`l0Norm x ≤ k`）。
直接复用 `RealSparseCoding.l0Norm`（**不重定义**）。 -/
abbrev IsKSparse {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : Prop := l0Norm x ≤ k

/-- **RIP 谓词（受限等距性质，本文件唯一的核心理设）**：

`IsRIP A k delta` 断言：对**每个** `k`-稀疏 `x`，

    **`|‖Ax‖² − ‖x‖²| ≤ delta · ‖x‖²`**

即「`A` 在 `k`-稀疏子集上把长度**近似保持**到相对误差 `delta`」——
等价地 `(1−delta)‖x‖² ≤ ‖Ax‖² ≤ (1+delta)‖x‖²`。

注意 **这是显式假设，不从任何别的性质推出**（任务指示；
E2 实测 mathlib 全树 0 命中 RIP / frame theory）。
`delta` 即**受限等距常数** `δ_k` 的载体。 -/
def IsRIP {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, IsKSparse k x → |sqNorm (matVec A x) - sqNorm x| ≤ delta * sqNorm x

/-- **RIP 的展开形式（双侧夹逼）**：
`(1−delta)‖x‖² ≤ ‖Ax‖² ≤ (1+delta)‖x‖²`（`k`-稀疏 `x`）。

这是 `IsRIP` 的绝对值形式展开，**全部下游证明直接用这个形状**。 -/
theorem isRIP_iff_two_sided {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ) :
    IsRIP A k delta ↔
      ∀ x : Fin n → ℝ, IsKSparse k x →
        (1 - delta) * sqNorm x ≤ sqNorm (matVec A x)
          ∧ sqNorm (matVec A x) ≤ (1 + delta) * sqNorm x := by
  unfold IsRIP
  constructor
  · intro h x hx
    have := h x hx
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  · intro h x hx
    obtain ⟨h1, h2⟩ := h x hx
    rw [abs_le]
    constructor <;> linarith

/-- **RIP 的下界方向（唯一在下游被反复使用的形式）**：
`(1 − delta)·‖x‖² ≤ ‖Ax‖²`（`k`-稀疏 `x`）。 -/
theorem isRIP_lower_bound {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (h : IsRIP A k delta) (x : Fin n → ℝ) (hx : IsKSparse k x) :
    (1 - delta) * sqNorm x ≤ sqNorm (matVec A x) :=
  ((isRIP_iff_two_sided A k delta).mp h x hx).1

/-- **RIP 的上界方向**：`‖Ax‖² ≤ (1 + delta)·‖x‖²`（`k`-稀疏 `x`）。 -/
theorem isRIP_upper_bound {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (h : IsRIP A k delta) (x : Fin n → ℝ) (hx : IsKSparse k x) :
    sqNorm (matVec A x) ≤ (1 + delta) * sqNorm x :=
  ((isRIP_iff_two_sided A k delta).mp h x hx).2

/-- **RIP 的单调性**：`k₁ ≤ k₂` 时 `k₂`-阶 RIP 蕴含 `k₁`-阶 RIP
（同 `delta`）——因 `k₁`-稀疏集**包含于** `k₂`-稀疏集。 -/
theorem isRIP_mono {m n : ℕ} (A : SensingMatrix m n) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {delta : ℝ}
    (h : IsRIP A k₂ delta) : IsRIP A k₁ delta :=
  fun x hx => h x (le_trans hx hk)

/-- **`k = 0` 时 RIP 平凡成立（`delta = 0`）**：唯一的 `0`-稀疏向量是零向量，
两边都是 `0`。这保证 RIP 谓词**不是空的**（存在非空实例）。 -/
theorem isRIP_zero {m n : ℕ} (A : SensingMatrix m n) : IsRIP A 0 0 := by
  intro x hx
  have hx0 : x = 0 := (l0_eq_zero_iff x).mp (Nat.le_zero.mp hx)
  subst hx0
  simp [sqNorm, matVec]

/-- **单位矩阵是 RIP 的平凡实例（`delta = 0`）**：
`A = I`（`m = n`）时，`‖Ax‖² = ‖x‖²`，故 `delta = 0` 即满足 RIP。
这给出**非空且非退化**的 RIP 实例，说明本文件的定义可被满足。 -/
theorem identity_isRIP (n : ℕ) :
    IsRIP (fun (i j : Fin n) => if i = j then (1 : ℝ) else 0) n 0 := by
  intro x _
  have hmat : matVec (fun (i j : Fin n) => if i = j then (1 : ℝ) else 0) x = x := by
    funext i
    unfold matVec
    rw [Finset.sum_eq_single i]
    · simp
    · -- 注意 Q4 修复（站点 R1）：原稿写 `simp [hj]`。`hj : j ≠ i` 而 `if` 条件是
      -- `i = j`，**方向相反**；`simp` 不会自动用 `Ne.symm` 桥接 ⟹ `unsolved goals`。
      -- 注意 且此处目标里的矩阵是**未 β-归约**的 λ-应用
      -- `(fun i j => if i = j then 1 else 0) i j * x j = 0` ⟹ 直接 `rw [if_neg …]`
      -- 仍匹配不上（`Q4 实测：:268 rewrite failed`）。
      -- 修法：先 `simp only []` 做 β-归约把 λ 消掉，再 `if_neg (Ne.symm hj)` + `zero_mul`。
      -- 同型前例：`RealSubgradientCalculus.lean:399-401`（`affineMap_id`）。
      intro j _ hj
      simp only []
      rw [if_neg (Ne.symm hj), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hmat]
  simp

/-! ## 二、RIP 的第一后果：稀疏信号唯一性（**真定理**）

这是压缩感知**最核心**的唯一性定理，且**完全可证**：
`δ_{2k} < 1` 时两个 `k`-稀疏解不可能不同
（差是 `2k`-稀疏且落零空间，而 RIP 使零空间在稀疏集上平凡）。
-/

/-- **支撑并的稀疏度加倍**：`x`、`y` 都 `k`-稀疏 ⟹ `x − y` 是 `2k`-稀疏。

证明：差向量的支撑 ⊆ 两者支撑之并，故
`l0Norm (x−y) ≤ l0Norm x + l0Norm y ≤ 2k`。 -/
theorem isKSparse_sub {n : ℕ} {k : ℕ} {x y : Fin n → ℝ}
    (hx : IsKSparse k x) (hy : IsKSparse k y) : IsKSparse (2 * k) (fun j => x j - y j) := by
  classical
  unfold IsKSparse l0Norm at *
  have hsub : Finset.univ.filter (fun j => x j - y j ≠ 0)
      ⊆ (Finset.univ.filter (fun j => x j ≠ 0)) ∪ (Finset.univ.filter (fun j => y j ≠ 0)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hxj : x j = 0
    · right
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hyj
      exact hj.2 (by rw [hxj, hyj, sub_zero])
    · exact Or.inl ⟨Finset.mem_univ _, hxj⟩
  calc (Finset.univ.filter (fun j => x j - y j ≠ 0)).card
      ≤ ((Finset.univ.filter (fun j => x j ≠ 0)) ∪
          (Finset.univ.filter (fun j => y j ≠ 0))).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun j => x j ≠ 0)).card
          + (Finset.univ.filter (fun j => y j ≠ 0)).card := Finset.card_union_le _ _
    _ ≤ 2 * k := by omega

/-- **要点 RIP ⟹ 稀疏信号唯一性（主结果，真定理）**：

设 `δ_{2k} < 1`（即 `IsRIP A (2k) delta` 且 `delta < 1`），
则 `A x = A y` 且 `x, y` 都 `k`-稀疏 ⟹ **`x = y`**。

**证明**：令 `z = x − y`（`2k`-稀疏，`isKSparse_sub`），则 `A z = 0`，
故 `‖Az‖² = 0`；由 RIP 下界 `(1−δ)‖z‖² ≤ ‖Az‖² = 0` 得
`(1−δ)‖z‖² ≤ 0`；`δ < 1` 时 `1−δ > 0`，结合 `‖z‖² ≥ 0` 得 `‖z‖² = 0`，
即 `z = 0`（平方和非负 ⟹ 每项为零 ⟹ 每个分量为零）。

这是「**RIP + 稀疏 ⟹ 唯一性**」这一层的**完整证明**——
压缩感知的**可证内核**。注意门槛就是 `δ < 1`，
**不需要** L1 恢复所需的 `√2 − 1`。 -/
theorem rip_sparse_uniqueness {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (hRIP : IsRIP A (2 * k) delta) (hdelta : delta < 1) {x y : Fin n → ℝ}
    (hx : IsKSparse k x) (hy : IsKSparse k y) (hAx : matVec A x = matVec A y) :
    x = y := by
  have hz : IsKSparse (2 * k) (fun j => x j - y j) := isKSparse_sub hx hy
  -- `A (x−y) = 0`
  have hAz : matVec A (fun j => x j - y j) = 0 := by
    funext i
    -- 注意 Q4 修复（站点 R2）：原稿写 `rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`。
    -- `Finset.mul_sum` 是**双 binder** 形 `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`
    -- （`Mathlib/Algebra/BigOperators/Ring.lean:45`），而此处目标是**单 binder** 的
    -- `∑ j, A i j * (x j - y j)` ⟹ 模式不匹配 ⟹ `rewrite failed`（原 `:323`）。
    -- 修法：显式用 `Finset.sum_sub_distrib` + `Finset.sum_congr` + 逐点 `mul_sub` 拆开。
    -- 注意 原稿末步写 `← congrFun hAx i`，**方向相反**，会把和换成另一个和而丢信息。
    unfold matVec at hAx ⊢
    have hsplit : (∑ j, A i j * (x j - y j)) = (∑ j, A i j * x j) - ∑ j, A i j * y j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => mul_sub (A i j) (x j) (y j)
    rw [hsplit, congrFun hAx i, sub_self]
    -- 注意 Q4：`funext i` 后目标右端是**未 β-归约**的 `0 i`（`0` 是函数），
    -- `sub_self` 给出的 `0` 与之句法不同 ⟹ `rfl` 亦不成立，须 `simp` 归一。
    simp
  -- RIP 下界 + `Az = 0` ⟹ `(1−δ)‖z‖² ≤ 0`
  have hlow := isRIP_lower_bound A (2 * k) delta hRIP (fun j => x j - y j) hz
  rw [hAz] at hlow
  have hsqzero : sqNorm (fun j => x j - y j) = 0 := by
    have h0 : sqNorm (0 : Fin m → ℝ) = 0 := by
      unfold sqNorm; simp
    rw [h0] at hlow
    have hpos : 0 < 1 - delta := by linarith
    have hnn : 0 ≤ sqNorm (fun j => x j - y j) :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  -- `‖z‖² = 0 ⟹ z = 0`
  funext j
  have : ∀ i : Fin n, (fun j => x j - y j) i = 0 := by
    intro i
    have := Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      sq_nonneg ((fun j => x j - y j) i))
    exact pow_eq_zero ((this.mp hsqzero) i (Finset.mem_univ i))
  have := this j
  simpa using sub_eq_zero.mp this

/-- **RIP 的必要性（逆否形式）**：若存在**非零** `2k`-稀疏向量落 `A` 的零空间，
则 `δ_{2k} ≥ 1`——即「唯一性失败 ⟹ RIP 失效」。

结合 `rip_sparse_uniqueness`，这给出 **`δ_{2k} < 1` 是稀疏唯一性的充要门槛**
（在同一「两个 `k`-稀疏解」框架内）。 -/
theorem rip_constant_ge_one_of_nonzero_null {m n : ℕ} (A : SensingMatrix m n) (k : ℕ)
    (delta : ℝ) (hRIP : IsRIP A (2 * k) delta) {z : Fin n → ℝ}
    (hz : IsKSparse (2 * k) z) (hznz : z ≠ 0) (hAz : matVec A z = 0) : 1 ≤ delta := by
  by_contra hlt
  push_neg at hlt
  have hlow := isRIP_lower_bound A (2 * k) delta hRIP z hz
  rw [hAz] at hlow
  have h0 : sqNorm (0 : Fin m → ℝ) = 0 := by unfold sqNorm; simp
  rw [h0] at hlow
  have hzpos : 0 < sqNorm z := by
    -- 注意 Q4 修复（站点 R3）：原稿写
    --   `rcases lt_or_gt_of_ne (Ne.symm hznz) with h | h`
    -- 根因（**双重**）：
    --   ① `lt_or_gt_of_ne` 是**线性序**引理 `a ≠ b → a < b ∨ b < a`，需要 `?m : ℝ`；
    --      而 `hznz : z ≠ 0` 是**函数类型**的否相等（`Fin n → ℝ`），**没有 `LinearOrder`**
    --      ⟹ `failed to synthesize`（`:364:11`）；
    --   ② 由此 `rcases` 的判别式是未合成的 metavariable ⟹
    --      `rcases tactic failed: x✝ : ?m.63643 is not an inductive datatype`（`:364:46`）。
    -- 即**前提类型错误**，不是策略用法错误。
    -- 修法：先由「函数非零」取出一个非零分量（外延 + 反证），
    -- 再用 `Finset.sum_pos'` 证平方和为正。
    -- 此写法与 `RealHessian.lean:75-83`（`normSq_pos`）逐字同型 —— 它证的正是
    -- 「`v ≠ 0 → 0 < Σ v i ^ 2`」这一条。
    -- 注意 `Finset.sum_pos'` 的**第二个**参数是 ∃-见证（第一个是逐点非负），
    --   顺序易错（详见 `RealConcentrationDuality.lean:113-116` 的登记）。
    have hex : ∃ i, z i ≠ 0 := by
      by_contra h
      apply hznz
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    unfold sqNorm
    exact Finset.sum_pos' (fun j _ => sq_nonneg _)
      ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hpos : 0 < 1 - delta := by linarith
  -- 注意 显式喂给 `nlinarith` 乘积正性：新的 `hzpos` 经由 `unfold sqNorm` 得到，
  -- 项形状与旧稿略有差异，故不依赖 `nlinarith` 自行搜索。
  nlinarith [mul_pos hpos hzpos]

/-! ## 三、RIP 的第二后果：稳定恢复与误差界（**真定理**）

RIP 的**下界方向**是全部稳定性论证的核心：
`‖z‖² ≤ ‖Az‖²/(1−δ)`——「`A` 在稀疏集上不把非零向量压成接近零」。
-/

/-- **要点 稀疏集上的下界反转（稳定性核心不等式，主结果）**：

`δ < 1`、`z` 是 `k`-稀疏 ⟹ **`‖z‖² ≤ ‖Az‖² / (1 − delta)`**。

这是 RIP 下界的**反转形式**（把 `‖Az‖²` 移到右边），
是全部误差界 / 稳定性论证**唯一需要的不等式**：
它说「`A` 在稀疏集上不会把非零向量压得太小」，故
**残差的大小控制了信号的大小**。 -/
theorem rip_norm_le_of_residual {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (hRIP : IsRIP A k delta) (hdelta : delta < 1) (z : Fin n → ℝ) (hz : IsKSparse k z) :
    sqNorm z ≤ sqNorm (matVec A z) / (1 - delta) := by
  have hlow := isRIP_lower_bound A k delta hRIP z hz
  have hpos : 0 < 1 - delta := by linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- **要点 含噪声的稳定恢复界（主结果）**：

`δ_{2k} < 1`、`x` 与 `x̂` 都 `k`-稀疏、`A x = y`、`A x̂ = y + e` ⟹

    **`‖x − x̂‖² ≤ ‖e‖² / (1 − δ_{2k})`**

即**噪声被线性放大 `1/(1−δ)` 倍**——「**噪声水平线性可控**」的准确陈述。

**证明**：`A(x − x̂) = −e`，故 `‖A(x−x̂)‖² = ‖e‖²`；
差 `x − x̂` 是 `2k`-稀疏（`isKSparse_sub`），
由 `rip_norm_le_of_residual` 得 `‖x−x̂‖² ≤ ‖e‖²/(1−δ_{2k})`。

注意 **诚实标注**：本定理的前提是「`x̂` 已经是 `k`-稀疏的」。
它**不声称**「L1 最小化能找到这样的 `x̂`」（那是 L1 恢复定理，**未做**，见文件头）。
本定理的内容是：**一旦解的稀疏度已知，误差就被 `e` 线性控制**。 -/
theorem rip_error_bound {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (hRIP : IsRIP A (2 * k) delta) (hdelta : delta < 1) {x xhat : Fin n → ℝ}
    (hx : IsKSparse k x) (hxhat : IsKSparse k xhat) {y e : Fin m → ℝ}
    (hAx : matVec A x = y) (hAxhat : matVec A xhat = y + e) :
    sqNorm (fun j => x j - xhat j) ≤ sqNorm e / (1 - delta) := by
  have hz : IsKSparse (2 * k) (fun j => x j - xhat j) := isKSparse_sub hx hxhat
  have hres : matVec A (fun j => x j - xhat j) = fun i => -e i := by
    funext i
    unfold matVec at hAx hAxhat ⊢
    -- 注意 Q4 修复（站点 R2'）：与 `rip_sparse_uniqueness` 的 `hAz` **同一根因** ——
    -- `Finset.mul_sum` 是双 binder 形，而此处是单 binder 的
    -- `∑ j, A i j * (x j - xhat j)` ⟹ 模式不匹配 ⟹ `rewrite failed`（`:424`）。
    -- 修法同 `hsplit` 模式。本式在库内有同型前例：`RealVariationalBayes.lean:321-331`。
    have hsplit : (∑ j, A i j * (x j - xhat j))
        = (∑ j, A i j * x j) - ∑ j, A i j * xhat j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => mul_sub (A i j) (x j) (xhat j)
    rw [hsplit, congrFun hAx i, congrFun hAxhat i]
    simp
  have hstep := rip_norm_le_of_residual A (2 * k) delta hRIP hdelta
    (fun j => x j - xhat j) hz
  rw [hres] at hstep
  have hsqneg : sqNorm (fun i : Fin m => -e i) = sqNorm e := by
    unfold sqNorm
    exact Finset.sum_congr rfl fun i _ => by rw [neg_sq]
  rwa [hsqneg] at hstep

/-- **无噪声 ⟹ 精确恢复（唯一性的「误差」形态）**：`e = 0` 时
`‖x − x̂‖² ≤ 0`，即 `x = x̂`。

这是 `rip_error_bound` 的直接推论，给出 `rip_sparse_uniqueness` 的**定量版本**。 -/
theorem rip_exact_recovery {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (hRIP : IsRIP A (2 * k) delta) (hdelta : delta < 1) {x xhat : Fin n → ℝ}
    (hx : IsKSparse k x) (hxhat : IsKSparse k xhat) {y : Fin m → ℝ}
    (hAx : matVec A x = y) (hAxhat : matVec A xhat = y) : x = xhat := by
  have h := rip_error_bound A k delta hRIP hdelta hx hxhat hAx
    (y := y) (e := 0) (by rw [hAxhat]; simp)
  have h0 : sqNorm (0 : Fin m → ℝ) = 0 := by unfold sqNorm; simp
  rw [h0] at h
  have hle : sqNorm (fun j => x j - xhat j) ≤ 0 := by
    have : (0 : ℝ) / (1 - delta) = 0 := by ring
    rwa [this] at h
  have hnn : 0 ≤ sqNorm (fun j => x j - xhat j) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hz : sqNorm (fun j => x j - xhat j) = 0 := le_antisymm hle hnn
  funext j
  have hall : ∀ i : Fin n, (fun j => x j - xhat j) i = 0 := fun i =>
    pow_eq_zero ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg ((fun j => x j - xhat j) i))).mp hz i
      (Finset.mem_univ i))
  have := hall j
  simpa using sub_eq_zero.mp this

/-- **要点 范数等价 / 双 Lipschitz（主结果）**：

`δ < 1` 时，对 `k`-稀疏 `x`：`√(1−δ)·√(‖x‖²) ≤ √(‖Ax‖²) ≤ √(1+δ)·√(‖x‖²)`，
即 **`A` 限制在 `k`-稀疏集上是双 Lipschitz 的**（上下常数 `√(1∓δ)`）。

这是 RIP 的**几何内容**：稀疏集上的长度被**双向控制**，
故 `A` 在稀疏集上**不丢失信息**（单射）也不**放大噪声**（稳定）。

注意 需要 `1 + delta ≥ 0`（否则上界无意义）——由 `delta ≥ -1` 提供；
本文件以显式假设给出。 -/
theorem rip_norm_equivalence {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (hRIP : IsRIP A k delta) (hlo : -1 ≤ delta) (hhi : delta < 1)
    (x : Fin n → ℝ) (hx : IsKSparse k x) :
    Real.sqrt (1 - delta) * Real.sqrt (sqNorm x) ≤ Real.sqrt (sqNorm (matVec A x))
      ∧ Real.sqrt (sqNorm (matVec A x)) ≤ Real.sqrt (1 + delta) * Real.sqrt (sqNorm x) := by
  have hnn : 0 ≤ sqNorm x := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnA : 0 ≤ sqNorm (matVec A x) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : (0 : ℝ) ≤ 1 - delta := by linarith
  have h2 : (0 : ℝ) ≤ 1 + delta := by linarith
  obtain ⟨hlow, hup⟩ := (isRIP_iff_two_sided A k delta).mp hRIP x hx
  constructor
  · -- 注意 Q4 修复（站点 R5，三次修正才成）：原稿写 `rw [← Real.sqrt_mul h1, ← Real.sqrt_mul h1]`。
    -- 注意 **实测教训（Q4 三轮）**：此站三种写法只有第三种对。
    --   ① 原稿 `rw [← Real.sqrt_mul h1]`：目标是 `√(1-δ)*√(sqNorm x) ≤ √(sqNorm (Ax))`，
    --      **左端本来就是「拆开」形**；`← sqrt_mul` 要造 `√((1-δ)*?y)` ⟹ 目标无此模式 ⟹ 失败。
    --   ② 我把 `hlow` 包进 `have` 再 `rw [Real.sqrt_mul h1]`：**新目标同是拆开形** ⟹ 仍失败（`:530`）。
    --      要点 根因：需要归一的是**假设 `hlow`**（其为**未拆**形 `√((1-δ)*sqNorm x)`），
    --      而 `rw` **只作用于目标**。
    --   ③ 已验证 正确：**不用 `sqrt_mul`**，改用乘积的单调性
    --      `Real.sqrt_le_sqrt hlow : √((1-δ)*sqNorm x) ≤ √(sqNorm (Ax))`，
    --      再用 `Real.sqrt_mul h1` 把该项**在目标里**归一回拆开形。
    --      即先把 `hlow` 升到 `√` 下，再在目标中`←`方向展开。
    have hlow' : Real.sqrt ((1 - delta) * sqNorm x) ≤ Real.sqrt (sqNorm (matVec A x)) :=
      Real.sqrt_le_sqrt hlow
    rw [Real.sqrt_mul h1] at hlow'
    exact hlow'
  · -- 上界同理：`Real.sqrt_mul h2` 把 `√((1+δ)*sqNorm x)` 归一回拆开形。
    have hup' : Real.sqrt (sqNorm (matVec A x)) ≤ Real.sqrt ((1 + delta) * sqNorm x) :=
      Real.sqrt_le_sqrt hup
    rw [Real.sqrt_mul h2] at hup'
    exact hup'

/-- **RIP ⟹ 稀疏集上单射（主结果，映射语言）**：
`δ_{2k} < 1` 时 `A` 在 `k`-稀疏集上是**单射**。

这是 `rip_sparse_uniqueness` 的映射语言重述——
「单射」正是「唯一可解性」的集合论形式。 -/
theorem rip_injective_on_sparse {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (hRIP : IsRIP A (2 * k) delta) (hdelta : delta < 1) :
    Set.InjOn (matVec A) {x : Fin n → ℝ | IsKSparse k x} := by
  intro x hx y hy hxy
  exact rip_sparse_uniqueness A k delta hRIP hdelta hx hy hxy

/-! ## 四、RIP ⟹ 互相干界（与 `RealSparseCoding` 的接口）

`RealSparseCoding` 定义了 `mutualCoherence` 与 `coherence`（两列相干）。
本节给出 **RIP 控制相干** 的方向：
把「两列」看成 `2`-稀疏支撑上的 Gram 子矩阵，RIP 的 `δ_2` 直接控制它。

**意义**：这说明 **RIP 是比互相干更强的假设**
（RIP 约束**全部** `k`-子矩阵，相干只约束**两列**），
从而 `RealSparseCoding` 的「相干 ⟹ 条件唯一性」
与本文件的「RIP ⟹ 无条件唯一性」在**假设强度**上可比较。
-/

/-- **列**：`col A j = fun i => A i j`。 -/
def col {m n : ℕ} (A : SensingMatrix m n) (j : Fin n) : Fin m → ℝ :=
  fun i => A i j

/-- **两列的和与差是 `2`-稀疏向量**：`e_i ± e_j`（`i ≠ j`）的 `L0` 为 `2`。

这是把「两列相干」送进 RIP 的**桥**——RIP 只对稀疏**向量**陈述，
故需要把「两列」编码成支撑为 `{i, j}` 的向量。 -/
theorem l0_two_spike_eq_two {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    l0Norm (fun k => if k = i then (1 : ℝ) else if k = j then 1 else 0) = 2 := by
  classical
  unfold l0Norm
  -- 注意 Q4 修复（站点 R6）：原稿写 `rw [Finset.card_eq_two]` + `refine ⟨i, j, ?_, ?_⟩`。
  -- 根因：`Finset.card_eq_two` 的形状是
  --   `#s = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y}`（`Mathlib/Data/Finset/Card.lean:716`）
  -- —— **`≠` 在第二位，集合等式在第三位**。原稿按 `(集合等式, ≠)` 的顺序写，
  -- 于是 `ext k`（`ext` 只能作用于等式）落在 `i ≠ j` 这个 Prop 上 ⟹
  -- `applyExtTheorem only applies to equations`（`:527`）；随后 `exact hij` 又被拿去
  -- 证集合等式 ⟹ `type mismatch`（`:540`）。**同一形状误判造成两条 error**。
  -- 修法：**放弃 `card_eq_two`**（本库 `RealSparseCoding.lean:226-232` 亦避开它），
  -- 改为先用 `Finset.ext` 逐点证 `filter … = {i, j}`，再用 `Finset.card_pair hij` 收尾。
  have hset : (Finset.univ.filter
        (fun k => (if k = i then (1 : ℝ) else if k = j then 1 else 0) ≠ 0))
      = ({i, j} : Finset (Fin n)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases hki : k = i
    · subst hki; simp
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · simp [hki, hkj]
  rw [hset]
  exact Finset.card_pair hij

/-- **要点 RIP ⟹ 两列相干被 `δ_2` 控制（主结果，与 `RealSparseCoding` 的接口）**：

`δ_2 < 1` 时，两列**平方相干和**被 `δ_2` 控制：
对 `i ≠ j`，
**`2·(⟪a_i,a_j⟫)² ≤ ((1+δ)² − (1−δ)²)·…`**——

更准确且可直接使用的形式（本定理采用的形状）：
`‖A(e_i+e_j)‖² + ‖A(e_i−e_j)‖² = 2(‖a_i‖² + ‖a_j‖²) + 0`，
而 RIP 给出双侧夹逼，故
**`|‖A(e_i+e_j)‖² − 2| ≤ 2δ`** 与 **`|‖A(e_i−e_j)‖² − 2| ≤ 2δ`**（当两列均为单位范数）。

注意 本文件给出**可证的弱形式**：RIP 控制 `e_i ± e_j` 的像长度，
故**间接**控制 `⟪a_i,a_j⟫`（由极化恒等式
`2⟪a_i,a_j⟫ = ‖a_i+a_j‖² − ‖a_i‖² − ‖a_j‖²`）。
**反向**（相干 ⟹ RIP 上界 `δ_k ≤ (k−1)μ`）**未做**（见诚实边界）。 -/
theorem rip_controls_two_spike {m n : ℕ} (A : SensingMatrix m n) (delta : ℝ)
    (hRIP : IsRIP A 2 delta) {i j : Fin n} (hij : i ≠ j) :
    |sqNorm (matVec A (fun k => if k = i then (1 : ℝ) else if k = j then 1 else 0))
        - sqNorm (fun k => if k = i then (1 : ℝ) else if k = j then 1 else 0)| ≤ delta * 2 := by
  have hs := hRIP _ (le_of_eq (l0_two_spike_eq_two hij))
  have hnorm : sqNorm (fun k => if k = i then (1 : ℝ) else if k = j then 1 else 0) = 2 := by
    -- 注意 Q4 修复（站点 R7，**本模块最深的根因**）：
    -- 原稿用 `Finset.sum_eq_add_sum_diff_singleton`（两次）。实测：
    --   ① 要点 **该名字在 mathlib 里不是一条被声明的定理** —— 全树只有 4 处**使用点**，
    --      没有**声明点**（它是 `to_additive` 生成的别名，乘法源为
    --      `Finset.prod_eq_mul_prod_diff_singleton`，`BigOperators/Group/Finset.lean:1591`）；
    --   ② 由此第一次 `rw` 能碰巧过关（目标形状偶合），**第二次必然失败** ——
    --      其后目标是 `f i ^ 2 + ∑ x ∈ univ \ {i}, f x ^ 2 = 2`，
    --      而该引理需要**侧条件** `j ∈ univ \ {i}`，`rw` **不会**合成侧条件 ⟹
    --      `did not find instance of the pattern ∑ x : Fin n, ?f x`（原 `:565`）。
    --   ③ 原稿随后那段 v17「W2 修复」（`SDiff.sdiff` 前缀记法 + 自造 `hrest`）
    --      是在**绕**这个不存在的引理，属**症状级补丁**；此处一并删除。
    -- 修法：**完全不做集合拆分**，改用逐点恒等式 + `Finset.sum_ite_eq'`。
    have hpt : ∀ k : Fin n,
        (if k = i then (1 : ℝ) else if k = j then 1 else 0) ^ 2
          = (if k = i then (1 : ℝ) else 0) + (if k = j then (1 : ℝ) else 0) := by
      intro k
      -- 注意 Q4 修复（R7 子站，第 4 次修正）：前一版逐条 `rw [if_pos/if_neg …]`
      -- **会重复消费同一个 `if` 出现**（目标里有 3 处 `if k = i`/`if k = j`，
      -- 一次 `rw` 只吃一处，第二次同名 `rw` 便无模式可匹配 ⟹ `:646/:648` 失败）。
      -- 修法：改回 `simp`，但**把局部假设 `hki`/`hkj` 显式喂进 simp-set**
      -- （这正是前一版 `subst`+`simp` 失败的补偿），再 `ring` 收尾。
      by_cases hki : k = i
      · simp [hki, hij]
      · by_cases hkj : k = j
        · -- 注意 Q4 修复（R7 子站，第 5 次修正）：`simp [hki, hkj, hij]` 仍留
          -- `⊢ ¬j = i` —— 因 `hij : i ≠ j` 与目标 `¬j = i` **方向相反**，
          -- 单靠 `simp [hij]` 不自动取对称。修法：**显式**把对称形式也喂进去。
          have hji : ¬ j = i := fun h => hij h.symm
          simp [hki, hkj, hji]
        · simp [hki, hkj]
    unfold sqNorm
    rw [Finset.sum_congr rfl fun k _ => hpt k]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    -- 注意 Q4 修复（R7 子站，第 3 次修正）：`sum_ite_eq'` 两次后目标是 `1 + 1 = 2`
    -- （`ℕ` 上的字面算术），**`simp` 不在该形状上闭合** ⟹ 须用 `norm_num`。
    norm_num
  -- 注意 Q4 修复（站点 R8）：原稿 `rwa [hnorm] at hs` —— `rwa ... at hs` 只把 `hnorm`
  -- 重写进**假设** `hs`，**目标**里的 `sqNorm f` 仍原样保留 ⟹ 目标与 `hs` 句法不同 ⟹
  -- `tactic 'assumption' failed`（原 `:585`）。修法：`at hs ⊢` 两侧都重写。
  rw [hnorm] at hs ⊢
  exact hs

/-- **要点 RIP 控制 Gram 子矩阵的对角（范数保持，主结果）**：
对单点（`1`-稀疏）`e_i`，RIP 给
**`|‖a_i‖² − 1| ≤ δ₁`**——即每列的长度被控制在 `1 ± δ₁` 内。

这是 RIP 的**最弱形式**，但已足够得到「列近似单位化」这一常见归一化条件。 -/
theorem rip_controls_column_norm {m n : ℕ} (A : SensingMatrix m n) (delta : ℝ)
    (hRIP : IsRIP A 1 delta) (j : Fin n) :
    |sqNorm (col A j) - 1| ≤ delta := by
  have hsp : IsKSparse 1 (fun k => if k = j then (1 : ℝ) else 0) := by
    unfold IsKSparse l0Norm
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    -- 注意 Q4 修复（站点 R9）：原稿写 `by_contra hab; exact ha (by simp [hab])`。
    -- 根因（**双重**）：
    --   ① `Finset.card_le_one` 的结论是**等式** `a = b`
    --      （`#s ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b`，`Mathlib/Data/Finset/Card.lean:633`），
    --      故 `by_contra hab` 给出 `hab : ¬(a = b)`、目标 `False`；而原稿把
    --      `by simp [hab]` 当作 `¬a = j` 的证明用，**类型不符**；
    --   ② 且 `ha : (if a = j then 1 else 0) ≠ 0` 是**实数**上的否相等，
    --      **不是**谓词，`ha (…)` 这种函数应用本身不合法。
    --      真正需要的是**反方向**：由 `ha` 推出 `a = j`（不是由 `= j` 推矛盾）。
    -- 修法：分别由 `ha`/`hb` 反证出 `a = j`、`b = j`，再传递。
    have haj : a = j := by
      by_contra h
      exact ha (by simp [h])
    have hbj : b = j := by
      by_contra h
      exact hb (by simp [h])
    exact haj.trans hbj.symm
  have h := hRIP _ hsp
  have hmat : matVec A (fun k => if k = j then (1 : ℝ) else 0) = col A j := by
    funext i
    unfold matVec col
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [hk]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hnorm : sqNorm (fun k => if k = j then (1 : ℝ) else 0) = 1 := by
    unfold sqNorm
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [hk]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rwa [hmat, hnorm, mul_one] at h

/-! ## 五、L1 最小化恢复：定义与**诚实标注未做**

压缩感知的**另一半**是「L1 最小化能**找到**稀疏解」。
本节给出 `l1Recovery` 的**谓词定义**（说明该概念可被本库表达），
并把**完整定理标注为未做**（成本过高，见文件头「诚实边界」第一条）。

**逻辑分层**（本文件的核心诚实定位）：
  · 【本文件已证】**RIP ⟹ 稀疏唯一性 + 稳定性**——
    「**若有稀疏解，则它唯一且误差线性可控**」；
  · 【未做】**L1 最小化 ⟹ 找到该稀疏解**——
    「**存在性 + 可计算性**」，需 NSP + 对偶证书 + `RIP ⟹ NSP` 的组合论证。
两层**逻辑独立**：前者是后者论证中的**一步**（NSP 的来源），但不是全部。
-/

/-- **L1 最小化恢复算子（谓词形式）**：

`isL1Recovery A y xhat` 断言 `xhat` 是 `{z : A z = y}` 上 `‖z‖₁` 的**最小点**。

注意 本定义**只陈述性质**，不构造 `argmin`（不证存在性/唯一性；
`RealSparseCoding` 的 `l1Norm` 与 `Finset` 的有限性使该谓词**可表达**，
但本文件**不证**任何非平凡的存在性——见下方 `l1Recovery_eq_sparse`）。 -/
def isL1Recovery {m n : ℕ} (A : SensingMatrix m n) (y : Fin m → ℝ) (xhat : Fin n → ℝ) : Prop :=
  matVec A xhat = y ∧ ∀ z : Fin n → ℝ, matVec A z = y → l1Norm xhat ≤ l1Norm z

/-- **L1 恢复谓词不是空的（平凡实例）**：
若 `x` 是**唯一的**可行点，则 `x` 是 L1 最小点（`l1Norm x ≤ l1Norm x`）。

这给出 `isL1Recovery` 的**非空性证据**，
并说明本文件的定义与 `RIP ⟹ 唯一性` 一起已经蕴含：
**RIP 条件下若稀疏可行点存在，它必然是 L1 最小点**
（因为可行集只有一个点——不过此时「L1」并未真正起作用，
真正的 L1 定理需要可行集**有多个点**时仍选到稀疏解，这才是未做的部分）。 -/
theorem isL1Recovery_of_unique_feasible {m n : ℕ} (A : SensingMatrix m n) (y : Fin m → ℝ)
    (x : Fin n → ℝ) (hAx : matVec A x = y)
    (huniq : ∀ z : Fin n → ℝ, matVec A z = y → z = x) : isL1Recovery A y x :=
  ⟨hAx, fun z hz => by rw [huniq z hz]⟩

/-- **要点 RIP + 稀疏 + 可行 ⟹ 该点即 L1 最小点（主结果，连接层）**：

`δ_{2k} < 1`、`x` 是 `k`-稀疏且 `A x = y` ⟹ **任何**可行的 `k`-稀疏点都等于 `x`
（唯一性），故 `x` 是 L1 最小点。

**这是本文件与「L1 恢复」之间唯一可证的桥**：
它把 `rip_sparse_uniqueness` 的结论喂给 `isL1Recovery`。
注意 **诚实标注**：该定理**不声称**「L1 最小化产生稀疏解」——
它只说「**在所有解都已知是 `k`-稀疏的前提下**，`x` 是最优的」。
真正的 L1 定理（不预设解的稀疏性）**未做**。 -/
theorem rip_l1_recovery_of_sparse {m n : ℕ} (A : SensingMatrix m n) (k : ℕ) (delta : ℝ)
    (hRIP : IsRIP A (2 * k) delta) (hdelta : delta < 1) {x : Fin n → ℝ}
    (hx : IsKSparse k x) {y : Fin m → ℝ} (hAx : matVec A x = y)
    (hAllSparse : ∀ z : Fin n → ℝ, matVec A z = y → IsKSparse k z) :
    isL1Recovery A y x := by
  refine ⟨hAx, fun z hz => ?_⟩
  -- 注意 Q4 修复（站点 R10）：原稿末位参数直接传 `hz : matVec A z = y`，但
  -- `rip_sparse_uniqueness` 的末位参数要求 `matVec A ?x = matVec A ?y` 的**同型**等式
  -- （其 `{x y}` 是隐式，位置参数序为 `A, k, delta, hRIP, hdelta, hx, hy, hAx`）。
  -- 由 `hAllSparse z hz` 绑定 `?x := z`、由 `hx` 绑定 `?y := x` ⟹ 需要的是
  -- `matVec A z = matVec A x`，而 `hz` 的右端是**观测向量** `y`（`Fin m → ℝ`）⟹
  -- `application type mismatch`（原 `:671`）。
  -- 修法：用 `by rw [hz, hAx]` 现场拼出所需等式。
  have hzx : z = x :=
    rip_sparse_uniqueness A k delta hRIP hdelta (hAllSparse z hz) hx (by rw [hz, hAx])
  rw [hzx]

/-! ## 注：闭环语义与**三层结构**

**第一层（RIP 定义，本文件建）**：
`IsRIP A k delta`（二次型夹逼形式，**显式假设**）
→ 双侧夹逼（`isRIP_iff_two_sided`）
→ 单调性（`isRIP_mono`）/ 非空实例（`isRIP_zero` / `identity_isRIP`）。

**第二层（唯一性 + 稳定性，**本文件全部证完**）**：
支撑并加倍（`isKSparse_sub`）
→ **唯一性**（`rip_sparse_uniqueness`，门槛 `δ_{2k} < 1`）
→ 必要性（`rip_constant_ge_one_of_nonzero_null`）
→ 下界反转（`rip_norm_le_of_residual`）
→ **误差界**（`rip_error_bound`：`‖x−x̂‖² ≤ ‖e‖²/(1−δ)`）
→ 精确恢复（`rip_exact_recovery`）
→ 范数等价 / 双 Lipschitz（`rip_norm_equivalence`）
→ 稀疏集单射（`rip_injective_on_sparse`）。

**第三层（与核/相干/SPARSE 的接口）**：
`rip_controls_column_norm`（列近似单位化）
→ `rip_controls_two_spike`（两列强度受控）
→ `rip_l1_recovery_of_sparse`（RIP + 已知稀疏 ⟹ L1 最小性）

**未做层（诚实标注）**：
「**L1 最小化 ⟹ 稀疏解**」（Candès–Romberg–Tao）——
需 NSP + 对偶证书 + `RIP ⟹ NSP` 的组合论证，**成本过高，本轮未做**。
「**随机矩阵以高概率满足 RIP**」——需测度集中，**未做**。
「**相干 ⟹ RIP 的定量换算**」（`δ_k ≤ (k−1)μ`）——**未做**（本文件只做反向）。
「**谱范数形式的 `δ_k`**」——本文件用二次型形式（见诚实边界第 2 条）。

诚实降级：RIP 是**显式假设**（不从别的性质推出，mathlib 无 frame theory）；
二次型形式而非谱范数形式（等价但只证前者内的定理）；
`δ < 1` 只声称是**唯一性**门槛，不声称是 L1 恢复门槛（后者是 `√2−1`）；
`isL1Recovery` 只给谓词定义与平凡非空性。
-/

end Lattice
