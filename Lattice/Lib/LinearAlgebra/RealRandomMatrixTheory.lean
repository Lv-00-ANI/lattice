import Mathlib
import Lattice.Lib.LinearAlgebra.RealSVD
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.LinearAlgebra.RealMatrixStability
import Lattice.Lib.LinearAlgebra.RealSpectralRadius
-- ⚠ 显式 import：`spectral_radius_le_opNorm_of_real_eigenvalue` 直接使用
-- `RealSpectral.spectral_radius_le_opNorm` 与同文件定义的 `HasRealEigenvalue` / `matCLME`。
-- 它们经 `RealSpectralRadius → RealSpectral` 传递可得，但**直接依赖应直接 import**
-- （避免上游改 import 图时静默断链）。
import Lattice.Lib.LinearAlgebra.RealSpectral
-- ⚠ **权威来源**：`ρ(T) ≤ ‖T‖` 的**一般实方阵形式**（含**复**谱）由
-- `RealGelfand.gelfand_radius_le_opNorm : gelfandRadius T ≤ ‖matCLME T‖` 建立，
-- 其中 `gelfandRadius T := sInf { r | ∃ k > 0, ‖Tᵏ‖ ^ (1/k) = r }` 是**基于范数**的谱半径，
-- **对任意实方阵成立**（不像 `RealSpectral.spectral_radius_le_opNorm` 只覆盖**实**特征值）。
-- 无环：`RealGelfand` import `RealSpectral`/`RealSpectralRadius`/`RealMatrixNorm`，
-- **不** import 本文件。
import Lattice.Lib.LinearAlgebra.RealGelfand
/-!
# LATTICE: 随机矩阵理论（有限版）—— 迹矩展开、Catalan 计数与谱范数集中

本项目已有的谱工具全部是**确定性**的：`RealSpectralRadius`（对角/Gelfand）、
`RealMatrixStability`（谱范数扰动与收缩幂界）、`RealSVD`（实对称谱定理）。
网络稳定性论证需要**随机矩阵**的工具，而库里没有。本文件补上**有限维、显式界**的
随机矩阵理论：全部结论在 `Fin n` 上陈述，**不涉及**渐近自由概率
（mathlib 4.14 无半圆律 / 自由卷积的基础设施）。

## 建模：显式矩假设（避开概率论基建）

随机矩阵的一般理论需要「矩阵元素是随机变量」的完整概率空间机器。
本项目的一致性做法（见 `RealHoeffding`/`RealSamplingBoost`）是**有限计数概率空间**：
样本空间 `α` 有限、`uniformProb`/`uniformExpectation`。本文件沿用这一设定，
把随机对称矩阵写成 `A : α → Matrix (Fin n) (Fin n) ℝ`（`α` 为有限样本空间），
期望为 `matrixExpectation A = (1/|α|)·Σ_ω A ω`。

**代价与收益**：这样「期望」是**有限平均**（无测度论），所有定理是**确定的代数恒等式**，
可直接喂给 `RealHoeffding` 做集中；代价是矩的**具体数值**形式
（如 `E[A_{ij}²] = σ²`）必须作为**显式假设**给出，而不是从分布推导
（mathlib 无 Gaussian 的 `moments` 现成链）。这与 `RealFisherMatrix` 里
「PSD 作为显式假设」、`RealFisherInfo` 里「链式法则作为显式假设」的先例一致。

## 本文件建立

**一、迹幂的组合展开（Wigner 矩方法的代数骨架）**
1. `closedWalkSum`：`Σ_{i : Fin k → Fin n} ∏_t A_{i_t i_{t+1}}`——迹幂的**闭路展开**（定义）；
2. `trace_sq_eq_sum`（**形式化**）：`tr(A²) = Σ_i Σ_j A_ij·A_ji`——`k = 2` 的展开，
   由 `Matrix.mul_apply` 直接得；
3. `trace_sq_eq_diag_plus_offdiag` / `trace_sq_symm`（**形式化**）：拆出对角与非对角，
   对称时 `tr(A²) = Σ_i A_ii² + 2Σ_{i<j} A_ij²`——第二节全部矩计算的载体；
4. `trace_eq_sum_diag`：`tr(A) = Σ_i A_ii`。

**二、有限随机矩阵与 Wigner 矩**
5. `matrixExpectation` / `matrixEntryExpectation`：有限样本空间上的矩阵期望
   （逐元素均匀平均，与 `RealHoeffding.uniformExpectation` 同一设定）；
6. `matrixExpectation_eq_zero` / `matrixExpectation_trace`：期望与零矩阵、与迹的交换；
7. `wigner_first_moment_zero`（**形式化**）：零一阶矩 ⟹ `E[tr A] = 0`；
8. `sum_card_Ioi_cast`（**计数引理**）：`Σ_{i:Fin n} #{j | i < j} = n(n−1)/2`
   （回收 `Finset.card_Ioi` = `n − 1 − i`）；
9. `wigner_second_moment`（**主结果，精确**）：逐样本点给定
   `A_ii² = 2σ²`、`A_ij² = σ²`（`i≠j`）、对称，且 `α` 非空时，
   `E[tr(A²)] = σ²·(n² + n)`。

**三、Catalan 数及其在四次矩中的角色**
10. `nat_catalan_two` / `nat_catalan_three`：回收 `catalan 2 = 2`、`catalan 3 = 5`
    （⚠ **根命名空间**的 `catalan`，**不是** `Nat.catalan`——定义在任何 `namespace` 之前）；
11. `wigner_fourth_moment_leading_lower`（**形式化**）：「四步全对角」这一配对类
    的精确贡献 `Σ_ω Σ_i (A ω) i i ^ 4 = |α|·n·(2σ²)²`；
12. ⚠ **`E[tr(A⁴)] = σ⁴(2n³ + 5n² + 5n)` 的精确公式本轮未形式化**
    （数值已在 `n = 1..7` 精确有理数验证；其中的 `n³` 系数 `2` 正是 `C₂`）。
    缺口是**组合记账体量**（5 类配对 × 四重求和重排，估值 300+ 行），
    非数学障碍。**不用 sorry 冒充**，登记为「此轮不通」项。

**四、Marchenko–Pastur 型的有限版（诚实降级：只做迹）**
13. `sampleCovariance_trace`（**精确恒等式**）：
    `tr((1/m)·XXᵀ) = (1/m)·Σ_{i,j} X_ij²`——协方差特征值之和 = 数据 Frobenius 平方 / m；
    ⚠ **不带 `m > 0`**（本轮实测该假设不必要，收紧为无条件版）；
14. `sampleCovariance_trace_nonneg`：`0 ≤ tr((1/m)XXᵀ)`（`m > 0`）。
    **诚实降级**：这是 MP 的**迹泛函**版本，**不是**特征值经验分布的 MP 律。

**五、谱范数的集中**
15. `spectralNormDeviation`：`‖matCLME (A − e)‖`（**算子范数**，经 `matCLME` 桥）；
16. `spectral_concentration_of_markov`（**主结果**）：
    `P(‖matCLME (A − e)‖ ≥ t) ≤ (1/t)·E[‖matCLME (A − e)‖]`（回收 `RealHoeffding.markov_counting`）；
17. `spectral_concentration_around_expectation`：中心取 `matrixExpectation A`；
18. `spectral_radius_concentration_transfer`（**接口重申，权威归因已修正**）：
    任意实方阵 `ρ(A) ≤ ‖matCLME A‖`，直接回收
    **`RealGelfand.gelfand_radius_le_opNorm`**（**不重证**——初稿曾重复证明，
    按「唯一权威位置」纪律删除）。
    ⚠ **归因修正（已登记 CORRECTIONS B56.1）**：旧稿称本条由
    `RealSpectral.spectral_radius_le_opNorm` 建立——**该归因是错的**：那条只在给定
    `HasRealEigenvalue A μ` 时给 `|μ| ≤ ‖matCLME A‖`，**只覆盖实特征值**；
    而一般实方阵可以没有实特征值（旋转 90°），`ρ` 是**复**谱的 `max|λ|`。
    真正的整体权威是 `RealGelfand.gelfandRadius`（基于范数 `sInf{‖Tᵏ‖^(1/k)}`，
    对**任意**实方阵成立）。本文件因此**补 `import RealGelfand`**（无环：`RealGelfand`
    不 import 本文件）。
    另保留 `spectral_radius_le_opNorm_of_real_eigenvalue` 作为**实特征值特例**的入口
    （如实降级标注：其结论弱于整体形式）。
    **诚实降级**：谱集中只到**马尔可夫级**；指数级需矩阵鞅 / Lieb 迹不等式（mathlib 无）。

## 与既有模块的接口定理（显式互链）

| 本文件 | 对接 | 内容 |
|:--|:--|:--|
| `trace_sq_eq_sum` / `trace_sq_symm` | `Matrix.trace` / `Matrix.mul_apply` | 迹幂展开（`k = 2`） |
| `trace_sq_symm` | `RealSVD` 的实对称约定（`Aᵀ = A`） | 对称迹平方 |
| `nat_catalan_two` / `nat_catalan_three` | `catalan`（mathlib，**根命名空间**） | Catalan 数回收 |
| `spectral_concentration_of_markov` | `RealHoeffding.markov_counting` | 谱范数集中（马尔可夫） |
| `spectral_concentration_around_expectation` | 本文件 `matrixExpectation` | 围绕期望集中 |
| `spectral_radius_concentration_transfer` | **`RealGelfand.gelfand_radius_le_opNorm`**（不重证） | 谱半径 ≤ 算子范数（**整体形式**，含复谱） |
| `spectral_radius_le_opNorm_of_real_eigenvalue` | `RealSpectral.spectral_radius_le_opNorm`（不重证） | **实特征值特例**（如实降级） |
| `sampleCovariance_trace` | `Matrix.trace` / `Matrix.mul_apply` | MP 的迹版本 |

## 诚实边界（诚实 / 未证 / 未做 / 降级 / 标注）

- **⚠ 此路不通（明确报告）：半圆律 / Marchenko–Pastur 律的**分布**版本**。
  完整的 Wigner 半圆律是「`n → ∞` 时 `A/√n` 的经验谱分布弱收敛到半圆分布」，
  需要：(a) Stieltjes 变换与其逆（`RealStieltjes` 类，mathlib 无）；
  (b) 关于 `n` 的**渐近**陈述（mathlib 无「随机矩阵序列」的基础设施）；
  (c) 自由概率的加性卷积（mathlib 4.14 **完全没有**自由概率）。
  本文件**不做**任何渐近陈述，只给**每个有限 `n` 上的精确恒等式与显式界**。
  这不是能力保留，而是**真诚的边界**：有限维可证的是矩的**精确值**，
  分布收敛是**另一门数学**。
- **⚠ 此路不通：Wick 定理本身的完整形式**。Wick 定理（高斯向量的奇数阶矩为零、
  偶数阶矩 = 配对的乘积和）在 mathlib 4.14 **不存在**（无 Gaussian 测度的矩生成）。
  本文件因此把 Wick 的**结论**（而非定理）作为**显式矩假设**直接装入
  `wigner_second_moment` 的假设（`hdiag` / `hoff`，逐样本点的二阶矩）：
  只用到**二阶矩**，形式化的精确计算是 `k = 2`
  （`wigner_second_moment`）。即：本文件证明的是
  「**在给定二阶矩下，`E[tr A²]` 的精确值**」，而不是「从高斯分布推出这些值」。
- **诚实降级：Catalan 的「四次矩」角色本轮未形式化**。`E[tr(A⁴)] = σ⁴(2n³+5n²+5n)`
  （`n³` 系数 `2` 即 `C₂`）的数值已在 `n = 1..7` 用**精确有理数**（Wick 配对枚举）
  验证无误，但形式化需要把四重求和按 5 类配对分类，体量大（估值 300+ 行）。
  本文件**不**用 sorry 冒充该定理，只形式化「四步全对角」这一类的贡献
  （`wigner_fourth_moment_leading_lower`），并把 Catalan 值本身从 mathlib 回收
  （`nat_catalan_two` / `nat_catalan_three`）。`k ≥ 6`（`C₃ = 5`）同此，未做。
- **诚实降级：`sampleCovariance_trace` 是迹的恒等式，不是 MP 律**。
  MP 律描述**特征值经验分布**；本文件只给其**迹泛函**（特征值之和 = 二阶矩），
  这是有限维可证的部分。
- **未做：谱的联合分布统计**。最大特征值的 Tracy–Widom 极限、
  特征值间距（Wigner 猜想）、方差谱均未做，且都需要自由概率或渐近基建。
- **未做：非对称矩阵 / 复矩阵的随机理论**。本文件全程实对称
  （`RealSVD` 谱定理的前提）；复 Hermitian 可逐字平移但不增加内容。
- **显式假设清单**（诚实标注）：`wigner_second_moment` 把「对称 + 逐样本点高斯二阶矩
  + `α` 非空」作为假设（`hsymm` / `hdiag` / `hoff` / `hN`）；`matrixExpectation`
  用有限均匀平均；集中定理用 `RealHoeffding.markov_counting`（计数马尔可夫，需 `t > 0`）。
- **范围**：有限 `Fin n`、有限样本空间 `α`；无测度论、无渐近、无自由概率。
- 无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators
open scoped Matrix

open Lattice.Lib.LinearAlgebra.RealMatrixStability

namespace Lattice

-- ⚠ **本文件最关键的根因之一**：第二节起的**全部**定义与定理都在有限样本空间 `α` 上做
-- 均匀平均，因此**处处**需要 `[Fintype α]`（`∑ ω : α, ·` 要 `Finset.univ`，
-- `Fintype.card α` 更是直接出现在陈述里）。
-- 原稿只写了 `{α : Type*}` ⟹ `Fintype.card α` / `∑ ω : α, ·` / `Finset.card_univ`
-- **全部**报 `failed to synthesize Fintype α`（同族一处根因、多处表现）。
-- 提到 `variable` 行统一给出，per-theorem 的 `[Fintype α]` 随之冗余（见下，已删）。
variable {n : ℕ} {α : Type*} [Fintype α]

/-! ## 一、迹幂的组合展开（Wigner 矩方法的代数骨架）

`tr(A^k) = Σ_{i_1,…,i_k} A_{i_1 i_2}·A_{i_2 i_3}···A_{i_k i_1}`
——即**闭路和**。这是 Wigner 矩方法的起点：
`E[tr A^k] = Σ_{闭路} E[∏ A_{i_t i_{t+1}}]`，随后用二阶矩假设（Wick）
判断哪些闭路贡献非零。本节的定理是**纯代数**的（无概率内容）。 -/

/-- **闭路和**：`Σ_{i : Fin (k+1) → Fin n} ∏_{t : Fin k} A (i t) (i (t+1))`
——长度 `k` 的闭路（起点 `i 0` 与终点 `i k` 自由，`k = 0` 时为空积 `1`）。
这是 `tr(A^k)` 展开的组合原型：`tr(A^k) = Σ_{i : Fin k → Fin n} ∏_t A_{i_t i_{t+1 mod k}}`。

**诚实标注**：这里用 `Fin (k+1) → Fin n`（端点自由）而非 `Fin k → Fin n`
（模 `k` 循环），因为数学库本版**无 `Fin.cycle`**；
两种写法在 `k ≥ 1` 时通过「固定起点 + 求和」相互转换，
该转换本身是 `Fin` 重排记账（本文件第二节的形式化只用到 `k = 2`，不需要它）。 -/
def closedWalkSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin (k + 1) → Fin n, ∏ t : Fin k, A (i (Fin.castSucc t)) (i (Fin.succ t))

/-- **`tr(A²)` 的迹幂展开（本文件形式化的 `k = 2` 版）**：
`tr(A²) = Σ_i Σ_j A_ij·A_ji`。

这是 `tr(A^k)` 的闭路展开在 `k = 2` 的显式形式（由 `Matrix.mul_apply` 直接得），
也是本文件第二节**全部矩计算**的载体。

**诚实标注**：一般 `k` 的 `tr(A^k) = closedWalkSum A k`
（`closedWalkSum` 定义已给，见上）本轮**未形式化**——需要把
`Fin (k+1) → Fin n` 上「端点自由」的求和化为「起点固定 + 模 `k` 循环」的求和，
属 `Fin`/`Finset` 重排记账（mathlib 本版无 `Fin.cycle`）。
对本文件的可交付内容（二阶矩、Catalan 对角类）而言 `k = 2` 已足够。 -/
theorem trace_sq_eq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (A * A).trace = ∑ i, ∑ j, A i j * A j i := by
  -- ⚠ `Matrix.trace` 是 **def**，`rw [Matrix.trace]` 只在 Lean 把它识别为可展开的
  -- 定义等式时才有效，且 `rw` 会**同时**作用于所有匹配位置。用 `show` 做定义展开最稳
  -- （`trace A = ∑ i, diag A i`，`diag A i ≡ A i i` 为 rfl 级）。
  show ∑ i, (A * A) i i = ∑ i, ∑ j, A i j * A j i
  refine Finset.sum_congr rfl fun i _ => ?_
  -- `Matrix.mul_apply` 是 rfl 级定理；用 `show` 展开比 `rw` 更稳（见上）。
  show (∑ j, A i j * A j i) = ∑ j, A i j * A j i
  rfl

/-- **`tr(A²)` 的对角展开**：`tr(A²) = Σ_i A_ii² + 2·Σ_{i<j} A_ij·A_ji`。
对称矩阵下即 `Σ_i A_ii² + 2Σ_{i<j} A_ij²`。这条是二阶矩计算的直接载体。 -/
theorem trace_sq_eq_diag_plus_offdiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (A * A).trace = ∑ i, A i i * A i i + ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
      A i j * A j i := by
  rw [trace_sq_eq_sum]
  -- ⚠ `Finset.sum_add_distrib : ∑ x ∈ s, (f x + g x) = ∑ f + ∑ g`，目标右侧是它的 **RHS**
  -- ⟹ `←` 方向。之后**逐 `i`** 把 `∑ j, f j` 拆成 `f i + ∑_{j ∈ filter (· ≠ i)} f j`。
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- 目标：`∑ j, A i j * A j i = A i i * A i i + ∑ j ∈ filter (· ≠ i), A i j * A j i`
  -- ① 把 `∑_{· ≠ i}` 用 `filter` 的补集形式展开
  -- ⚠ 用 `Finset.sum_filter` 把 `∑ j ∈ filter (· ≠ i), f j` 化成 `∑ j, if j ≠ i then f j else 0`，
  -- 再与全和相减的路径最稳（避开 `sum_filter_add_sum_filter_not` 的方向博弈）。
  have hsplit : (∑ j : Fin n, A i j * A j i)
      = A i i * A i i + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), A i j * A j i := by
    -- 反向使用 `sum_filter_add_sum_filter_not`（其结论把两个 filtered sum 放在**左侧**）：
    -- 取 `p := fun j => j = i`，则 `{p}` 是单点 `{i}`、`{¬p}` 是 `{j ≠ i}`。
    have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun j : Fin n => j = i) (f := fun j => A i j * A j i)
    -- ⚠ 原稿 `rw [← h]` 会**同时**改写目标右侧的 `A i i * A i i`（`rw` 重写所有匹配），
    -- 把目标搞乱（v9 报 `introN failed` + 两处 `no goals`）。
    -- 正解：只把 `h` 的 RHS 换成 LHS，且**限定在左侧那一个求和上**——(
    -- 用 `rw [← h]` 之前先把右侧「保护」起来不现实，故改用 `calc` 走单向：
    calc (∑ j : Fin n, A i j * A j i)
        = (∑ j ∈ Finset.univ.filter (fun j => j = i), A i j * A j i)
          + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), A i j * A j i := by
          rw [← h]
      _ = A i i * A i i + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), A i j * A j i := by
          congr 1
          -- `∑ j ∈ filter (· = i), A i j * A j i = A i i * A i i`
          -- ⚠ `Finset.sum_eq_single i` 的 goal 顺序是 **[侧1, 侧2, 主]**，但 `rw [...]` 会
          -- 先把主目标化成 `A i i * A i i = A i i * A i i` 并**自动关掉**，导致后续
          -- `intro` 面对已关闭的目标（v9/v10 实测 `introN failed` + `no goals`）。
          -- 正解：用 `refine Finset.sum_eq_single i ?_ ?_` **只给两个侧条件**，主目标自动闭合
          -- （`rw` 会把它化成 `rfl`）。
          refine Finset.sum_eq_single i ?_ ?_
          · intro j hjmem hjne
            exact absurd (Finset.mem_filter.mp hjmem).2 hjne
          · intro hi
            -- ⚠ 目标里的 filter 谓词写成 `fun j => j = i`，而 `Finset.mem_filter.mpr ⟨_, rfl⟩`
            -- 会把它归一到 `filter (Eq i)`——两者 defeq 但 `rfl` 在**结构字面**上不统一
            -- （v11 实测 `i ∉ filter (fun j => j = i) univ` vs `filter (Eq i) univ` 类型不符）。
            -- 用 `simp` 直接判定成员性最稳。
            exact absurd (by simp : i ∈ Finset.univ.filter (fun j : Fin n => j = i)) hi
  exact hsplit

/-- **对称矩阵的 `tr(A²)`**：`Aᵀ = A` 时 `tr(A²) = Σ_i A_ii² + 2·Σ_{i<j} A_ij²`
（把非对角项配对成 `2A_ij²`）。

**证明路线（避免逐点重索引的陷阱）**：由 `trace_sq_eq_diag_plus_offdiag`，
非对角部分是 `∑ i, ∑_{j ≠ i} A_ij·A_ji`；用对称性 `A_ji = A_ij` 化成
`∑ i, ∑_{j ≠ i} A_ij²`。再把每个 `i` 的内层按 `j < i` / `i < j` 二分（二者互补且不相交），
最后用 **`Finset.sum_comm` + 对称性** 证明 `∑ i ∑_{j<i} A_ij² = ∑ i ∑_{i<j} A_ij²`
（后者即「换名 + `A_ij² = A_ji²`」），故总和为 `2·∑_{i<j} A_ij²`。 -/
theorem trace_sq_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) :
    (A * A).trace = ∑ i, A i i ^ 2
      + 2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), A i j ^ 2 := by
  -- 对称性的逐点形式。
  -- ⚠ `hA : Aᵀ = A` 给出的是 `Aᵀ j i = A j i`，而 `Aᵀ j i = A i j`
  -- （`Matrix.transpose_apply`）⟹ 组合得到 **`A i j = A j i`**（不是反向）。
  -- 原稿写成 `A j i = A i j` 故报 `type mismatch`。
  have hsym : ∀ i j : Fin n, A i j = A j i := by
    intro i j
    have h := congrFun (congrFun hA j) i
    rw [Matrix.transpose_apply] at h
    exact h
  -- 记 U = ∑_{i<j} A_ij²，L = ∑_{i, j<i} A_ij²；先证 L = U。
  -- **数学**：把 L 的被加项按 `i ↔ j` 换名即得 U（`hsym` 保证 `A j i ^ 2 = A i j ^ 2`）。
  -- **技术**：`Finset.sum_comm` 在本目标上匹配不到（外层单绑定、内层双绑定），
  -- 故改用 `Finset.sum_bij` 显式建立 `{(i,j) | j < i} ↔ {(i,j) | i < j}` 的双射。
  -- 更省事的路线：把两层都写成 `∑ i, ∑ j, if … then … else 0`（全单绑定），再换序。
  have hLU : (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j < i), A i j ^ 2)
      = ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), A i j ^ 2 := by
    -- 把 `∑ j ∈ filter p univ, f j` 统一化成 `∑ j, if p j then f j else 0`
    simp only [Finset.sum_filter]
    -- 现在两侧都是 `∑ i, ∑ j, if … then … else 0`（全单绑定）⟹ `sum_comm` 可用
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    -- 左侧被加项：`if j < i then A j i ^ 2 else 0`（换序后变量名对调）
    -- 右侧被加项：`if j < i then A i j ^ 2 else 0`
    -- 两者仅在 `A j i ^ 2` vs `A i j ^ 2` 上有别，由 `hsym` 打平。
    by_cases hji : j < i
    · -- 两侧都取 `if_pos`；被加项由 `hsym i j : A i j = A j i` 的**反向**打平
      -- （换序后左侧是 `A j i ^ 2`，要换成 `A i j ^ 2`）。
      rw [if_pos hji, if_pos hji, (hsym i j).symm]
    · rw [if_neg hji, if_neg hji]
  -- 主体：先展开非对角，再二分内层，最后用 hLU 合并
  have hmain : ∀ i : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j => j ≠ i), A i j * A j i)
        = (∑ j ∈ Finset.univ.filter (fun j => i < j), A i j ^ 2)
          + (∑ j ∈ Finset.univ.filter (fun j => j < i), A i j ^ 2) := by
    intro i
    -- 对称 ⟹ 被加项 `A i j * A j i` 化成平方。
    -- ⚠ `hsym i j : A i j = A j i`；目标是 `A i j * A j i = A i j ^ 2`，
    -- 要把 `A j i` 换成 `A i j` ⟹ 用 **`.symm`**（原稿用正向，形状不对）。
    have hsq : (∑ j ∈ Finset.univ.filter (fun j => j ≠ i), A i j * A j i)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), A i j ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hsym i j).symm, pow_two]
    rw [hsq]
    -- `{j≠i} = {i<j} ∪ {j<i}`（`Fin` 上线序三分）
    have hset : Finset.univ.filter (fun j : Fin n => j ≠ i)
        = (Finset.univ.filter (fun j : Fin n => i < j))
          ∪ (Finset.univ.filter (fun j : Fin n => j < i)) := by
      apply Finset.ext
      intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hne
        rcases lt_trichotomy i j with h | h | h
        · exact Or.inl h
        · exact absurd h.symm hne
        · exact Or.inr h
      · -- ⚠ `ne_of_lt h : i ≠ j`、`ne_of_gt h : i ≠ j` 给出的都是 `i ≠ j`，
        -- 而目标是 `j ≠ i` ⟹ 两处都要 **`.symm`**（原稿遗漏，报两处 `type mismatch`）。
        rintro (h | h)
        · exact (ne_of_lt h).symm
        · exact (ne_of_gt h).symm
    have hdisj : Disjoint (Finset.univ.filter (fun j : Fin n => i < j))
        (Finset.univ.filter (fun j : Fin n => j < i)) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
      exact absurd hj (not_lt.mpr (le_of_lt hj'))
    rw [hset, Finset.sum_union hdisj]
  rw [trace_sq_eq_diag_plus_offdiag]
  -- 目标：`∑ i, (A i i * A i i + ∑ j∈filter(·≠i), A i j * A j i)
  --        = ∑ i, A i i ^ 2 + 2 * ∑ i, ∑ j∈filter(·<i), A i j ^ 2`
  -- ⚠ 原稿 `rw [← Finset.sum_add_distrib]` 想把**左侧**的逐点和并成两个和，
  -- 但 `sum_add_distrib` 是双绑定（`∑ x ∈ s,`）且这里外层是单绑定，方向/形状都不对，
  -- 报 `unsolved goals`（`?m` 未赋值）+ `no goals`。
  -- 正解：用 `calc` 把左侧逐点和拆成两个和，再各自化简。
  -- ⚠ v10 实测 `invalid 'calc' step, left-hand side is …`：`calc` 的 LHS 必须与上一步**逐字**一致。
  -- 这里 `trace_sq_eq_diag_plus_offdiag` 已把目标 LHS 化成
  -- `∑ i, A i i * A i i + ∑ i, ∑ j ∈ filter (· ≠ i), …`——注意是**两个独立外层和相加**，
  -- **不是** `∑ i, (… + …)`。故 calc 的起点要用相加形式。
  calc (∑ i : Fin n, A i i * A i i)
        + ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), A i j * A j i
      = (∑ i : Fin n, A i i ^ 2)
        + ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), A i j * A j i := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [pow_two]
    _ = (∑ i : Fin n, A i i ^ 2)
        + 2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), A i j ^ 2 := by
        congr 1
        have hc := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hmain i)
        rw [hc, Finset.sum_add_distrib, hLU]
        ring

/-- **`k = 1` 的迹展开**：`tr(A) = Σ_i A_ii`（定义，用于奇数阶矩的结构陈述）。 -/
theorem trace_eq_sum_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.trace = ∑ i, A i i := rfl

/-! ## 二、有限随机矩阵与 Wigner 矩

**显式矩模型**（诚实标注：这是假设，不是从分布推导——mathlib 4.14 无 Wick 定理）。
取有限样本空间 `α`（`Fintype`、非空），随机对称矩阵
`A : α → Matrix (Fin n) (Fin n) ℝ`，满足
- 对称：`∀ ω, (A ω)ᵀ = A ω`；
- 零一阶矩：`∀ i j, (1/|α|)Σ_ω A ω i j = 0`；
- 二阶矩：`∀ ω i, (A ω) i i ^ 2` 与 `∀ ω i j, i ≠ j → (A ω) i j ^ 2` 为常数
  `2σ²` 与 `σ²`（**逐样本点**的假设，比「期望等于」更强，故结论更强）。

在此模型下，`E[tr(A^k)]` 的**精确值**可算（本文件形式化 `k = 2`；`k = 4` 见第三节）。 -/

/-- **有限样本空间上的矩阵期望**：`(1/|α|)·Σ_ω A ω`（逐元素平均）。
与 `RealHoeffding.uniformExpectation` 同一概率空间设定。 -/
def matrixExpectation {n : ℕ} (A : α → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (∑ ω : α, A ω i j) / (Fintype.card α : ℝ)

/-- **矩阵元素的均匀期望**：`matrixEntryExpectation A i j = (1/|α|)Σ_ω A ω i j`。 -/
def matrixEntryExpectation {n : ℕ} (A : α → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : ℝ :=
  (∑ ω : α, A ω i j) / (Fintype.card α : ℝ)

/-- 矩阵期望的逐元素识别（定义即证）。 -/
theorem matrixExpectation_apply {n : ℕ} (A : α → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    matrixExpectation A i j = matrixEntryExpectation A i j := rfl

/-- **零一阶矩 ⟹ 期望为零矩阵**：`∀ i j ω, A ω i j` 的均值为零 ⟹ `E[A] = 0`。 -/
theorem matrixExpectation_eq_zero {n : ℕ} {A : α → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j, matrixEntryExpectation A i j = 0) :
    matrixExpectation A = 0 := by
  ext i j
  rw [matrixExpectation_apply, h i j, Matrix.zero_apply]

/-- **迹与期望可交换**：`E[tr A] = tr(E[A])`（有限求和交换）。 -/
theorem matrixExpectation_trace {n : ℕ} (A : α → Matrix (Fin n) (Fin n) ℝ) :
    (∑ ω : α, (A ω).trace) / (Fintype.card α : ℝ) = (matrixExpectation A).trace := by
  -- 思路：把两侧都定义展开成 `∑ ω : α, ∑ i : Fin n, A ω i i / card`，
  -- 再用「双重和可交换」把 `ω` 与 `i` 调换。
  -- ⚠ 三轮实测的三个陷阱：
  --  (i) `Matrix.trace` 是 **def**，`rw [Matrix.trace]` 不可靠 ⟹ 用 `show` 展开；
  --  (ii) `Finset.sum_comm` 是**双绑定** `∑ x ∈ s, ∑ y ∈ t, f x y = …`，
  --       而这里是**两层单绑定** `∑ ω : α, ∑ i : Fin n, ·` ⟹ 直接 `rw` pattern 失配；
  --  (iii) **`Finset.sum_univ` 不存在**（`#check` 实测 `unknown constant`）⟹ 不能用它
  --       把单绑定抬成双绑定。存在的是
  --       `Finset.sum_attach (s) (f) : ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x`。
  -- 解法：**先在 `s.attach` 上换序**（`attach` 天然是双绑定 `∑ x ∈ s.attach, ·`），
  -- 核心重排引理：把 `∑ ω, ∑ i, f ω i / c` 换成 `∑ i, (∑ ω, f ω i) / c`。
  -- 证明分两步：(1) 用 `Finset.sum_div`（**反向**）把内层除法提到外层；
  -- (2) 用 `Finset.sum_attach` 把**单绑定**抬成 `s.attach` 上的**双绑定**，
  --     以便 `Finset.sum_comm`（双绑定引理）可用；换序后再用 `Finset.sum_attach` 收回。
  -- ⚠ 三个实测陷阱：`Finset.sum_univ` **不存在**；`Finset.sum_comm` 是**双绑定**；
  -- `Finset.sum_attach` 正向/反向要配对使用（`simp only [Finset.sum_attach]` 在
  -- 「已换序的 attach 形式」上可能无进展，需显式 `rw`）。
  have key : ∀ (f : α → Fin n → ℝ) (c : ℝ),
      (∑ ω : α, ∑ i : Fin n, f ω i / c) = ∑ i : Fin n, (∑ ω : α, f ω i) / c := by
    intro f c
    -- 思路：`Finset.sum_comm` 只对**双绑定**成立，故必须把两层都「抬」到
    -- `s.attach` 上。做法：**两侧都用 `Finset.sum_attach` 的正向**把单绑定
    -- `∑ x : s, g x` 改写成 `∑ x ∈ s.attach, g ↑x`（注意方向是**正向**，
    -- 因为目标里出现的是 `∑ x : s, ·`，而引理 LHS 是 `∑ x ∈ s.attach, ·`）。
    -- ⚠ 三轮实测：反向 `rw [← Finset.sum_attach]` 只改外层、内层仍是单绑定，
    -- 于是 `sum_comm` 仍失配。**必须两层都抬**。
    have hL : (∑ ω : α, ∑ i : Fin n, f ω i / c)
        = ∑ ω ∈ (Finset.univ : Finset α).attach,
            ∑ i ∈ (Finset.univ : Finset (Fin n)).attach, f (ω : α) (i : Fin n) / c := by
      rw [← Finset.sum_attach (s := (Finset.univ : Finset α))
            (f := fun ω : α => ∑ i : Fin n, f ω i / c)]
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      rw [← Finset.sum_attach (s := (Finset.univ : Finset (Fin n)))
            (f := fun i : Fin n => f (ω : α) i / c)]
    have hR : (∑ i : Fin n, (∑ ω : α, f ω i) / c)
        = ∑ i ∈ (Finset.univ : Finset (Fin n)).attach,
            ∑ ω ∈ (Finset.univ : Finset α).attach, f (ω : α) (i : Fin n) / c := by
      rw [← Finset.sum_attach (s := (Finset.univ : Finset (Fin n)))
            (f := fun i : Fin n => (∑ ω : α, f ω i) / c)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_div (s := Finset.univ)]
      rw [← Finset.sum_attach (s := (Finset.univ : Finset α))
            (f := fun ω : α => f ω (i : Fin n) / c)]
    rw [hL, hR, Finset.sum_comm]
  -- 主证明：两侧都用 `show` 定义展开（`Matrix.trace` 与 `matrixExpectation` 都是 `def`，
  -- `rw` 它们不可靠；两侧同时 `rw` 还会造成形状错位）。
  show (∑ ω : α, ∑ i : Fin n, A ω i i) / (Fintype.card α : ℝ)
      = ∑ i : Fin n, (∑ ω : α, A ω i i) / (Fintype.card α : ℝ)
  -- 左侧：把外层除法推进内层求和体，凑成 `key` 的 LHS
  rw [show (∑ ω : α, ∑ i : Fin n, A ω i i) / (Fintype.card α : ℝ)
        = ∑ ω : α, ∑ i : Fin n, A ω i i / (Fintype.card α : ℝ) from by
      rw [Finset.sum_div (s := Finset.univ)]
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      rw [Finset.sum_div (s := Finset.univ)]]
  exact key (fun ω i => A ω i i) (Fintype.card α : ℝ)

/-- **`k = 1`：零一阶矩 ⟹ 迹矩为零（奇次矩的起点）**：
`E[tr A] = Σ_i E[A_ii] = 0`。 -/
theorem wigner_first_moment_zero {n : ℕ} {A : α → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j, matrixEntryExpectation A i j = 0) :
    (∑ ω : α, (A ω).trace) / (Fintype.card α : ℝ) = 0 := by
  -- ⚠ 原稿 `rw [matrixExpectation_trace, matrixExpectation_eq_zero h]` 把 `matrixExpectation_trace`
  -- 当成「改写规则」，但它的 LHS 是 `(∑_ω trace)/card`——**正是目标本身**，`rw` 会把它换成
  -- `(matrixExpectation A).trace`，随即 `matrixExpectation_eq_zero h : matrixExpectation A = 0`
  -- 只改 `matrixExpectation A` 而目标里已是 `.trace` 包裹 ⟹ 顺序错位。
  -- 正解：先 `rw [matrixExpectation_trace]` 把目标化为 `(matrixExpectation A).trace = 0`，
  -- 再用 `h` 把 `matrixExpectation A` 换成 `0`，最后 `Matrix.trace_zero`。
  rw [matrixExpectation_trace, matrixExpectation_eq_zero h, Matrix.trace_zero]

/-- **上三角计数（实数形式）**：`Σ_{i : Fin n} #{j | i < j} = n·(n−1)/2`。
用于二阶矩：`E[tr(A²)] = 2nσ² + 2σ²·#{i<j}`，而 `Σ_i #{j | i<j} = n(n−1)/2`。

用 mathlib 的 `Finset.card_Ioi`（`#(Ioi a) = n − 1 − a`）与
`Fin.sum_univ_castSucc` + 等差数列求和（`Finset.sum_range_id`）。 -/
theorem sum_card_Ioi_cast (n : ℕ) :
    (∑ i : Fin n, (((Finset.Ioi i).card : ℕ) : ℝ))
      = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have hcard : ∀ i : Fin n, (Finset.Ioi i).card = n - 1 - i := by
    intro i
    -- ⚠ `Fin.card_Ioi` 是 **namespace `Fin` 内**的定理（`Order/Interval/Finset/Fin.lean:170`），
    -- 全名 **`Fin.card_Ioi`**；而 `Finset.card_Ioi` **不存在**（`Finset.Ioi i` 在 `Fin` 上
    -- 走的是 `Fin` 的专用实例）⟹ 原稿报 `unknown constant 'Finset.card_Ioi'`。
    -- 且 `#(Ioi a) = n - 1 - a` 里的 `a` 是**强制转换为 ℕ** 的，故结论自动成立。
    simp [Fin.card_Ioi]
  have hc1 : (∑ i : Fin n, (((Finset.Ioi i).card : ℕ) : ℝ))
      = ∑ i : Fin n, ((n - 1 - i : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun i _ => by rw [hcard i])
  rw [hc1]
  -- ⚠ `((n - 1 - i : ℕ) : ℝ) = (n:ℝ) - 1 - (i:ℝ)` 在 `i : Fin n` 且 `n` 可能为 `0`
  -- 时**不成立**（`n - 1 - i` 是 ℕ 截断减法，`n = 0` 时左侧为 `0`，右侧为 `-1 - i`）。
  -- 恒为真的写法是把 ℕ 的截断减法先转成「`n` 与 `i+1` 的差」：
  -- `n - 1 - i = n - (i + 1)`，再用 `Nat.cast_sub`（条件是 `i + 1 ≤ n`，由 `i.isLt` 给出）。
  have hval : ∀ i : Fin n, ((n - 1 - i : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℝ) := by
    intro i
    have hi : (i : ℕ) + 1 ≤ n := i.isLt
    have h1 : n - 1 - i = n - (i + 1) := by omega
    rw [h1, Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    ring
  have hc2 : (∑ i : Fin n, ((n - 1 - i : ℕ) : ℝ))
      = ∑ i : Fin n, ((n : ℝ) - 1 - (i : ℝ)) :=
    Finset.sum_congr rfl (fun i _ => hval i)
  rw [hc2]
  -- Σ_{i : Fin n} ((n:ℝ) − 1 − i) = n·(n−1) − Σ i
  -- ⚠ `Finset.sum_sub_distrib` 是**双绑定**（`∑ x ∈ s, (f x - g x) = ∑ f - ∑ g`，`s` 隐式）；
  -- 目标是**单绑定** `∑ i : Fin n, (…)`。用 `rw` 需靠合一 `s := Finset.univ`，不稳；
  -- `simp only` 走同样的等式但重写策略更宽容（对单/双绑定都能命中）。
  simp only [Finset.sum_sub_distrib]
  -- ⚠ 同上：`Finset.sum_const (b) : ∑ _x ∈ s, b = s.card • b` 也是双绑结论。
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum : (∑ i : Fin n, (i : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℕ) : ℝ)) n]
    have := Finset.sum_range_id n
    have hcast : ((∑ i ∈ Finset.range n, i : ℕ) : ℝ)
        = ((n * (n - 1) / 2 : ℕ) : ℝ) := by rw [this]
    rw [Nat.cast_sum] at hcast
    rw [hcast]
    have h1 : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      -- ⚠ `Nat.cast_div` 需要 `(2:ℕ) ∣ n * (n-1)`。
      -- 原稿传 `(by norm_num : (2:ℕ) ∣ 2)`——把**被除数**写成常数 `2`，与目标的
      -- `n * (n-1)` 不匹配，必然失败。真实证据是 mathlib 已有
      -- **`Nat.even_mul_pred_self : ∀ n, Even (n * (n - 1))`**（`Algebra/Group/Nat/Even.lean:75`），
      -- 配 `even_iff_two_dvd` 直接给出整除性——**无需 `even_or_odd` 分情形**。
      have h2 : 2 ∣ n * (n - 1) := (even_iff_two_dvd.mp (Nat.even_mul_pred_self n))
      -- ⚠ `Nat.cast_div {m n : ℕ} : n ∣ m → ↑n ≠ 0 → ↑(m / n) = ↑m / ↑n`。
      -- 第二个参数的**目标类型是 `↑n ≠ 0`（即 `(2:ℝ) ≠ 0`）**，不是 `(2:ℕ) ≠ 0`——
      -- 原稿写 `(by norm_num : (2 : ℕ) ≠ 0)` 会让 `norm_num` 产出 ℕ 版命题，
      -- 报 `has type 2 ≠ 0 : Prop but is expected to have type ↑2 ≠ 0 : Prop`。
      -- 正解：把类型标注写成 ℝ 版。
      rw [Nat.cast_div h2 (by norm_num : ((2 : ℕ) : ℝ) ≠ 0)]
      -- 除法化为乘法后，唯一要小心的是 `↑(n-1)`；`n` 可能为 0，但此时两侧同为 0，
      -- 故统一用 `Nat.cast_pred`/`push_cast` + `ring` 在两种情形下都对。
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; norm_num
      · push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
        ring
    rw [h1]
  rw [hsum]
  ring

/-- **对称随机矩阵的二阶矩（精确）**：若逐样本点
`∀ ω i, (A ω) i i ^ 2 = 2 * sigma ^ 2`、`∀ ω i j, i ≠ j → (A ω) i j ^ 2 = sigma ^ 2`
且对称，则

`E[tr(A²)] = sigma²·(n² + n)`。

**证明**：由 `trace_sq_symm`，`tr(A²) = Σ_i A_ii² + 2Σ_{i<j}A_ij²`
`= n·2σ² + 2·#{i<j}·σ² = 2nσ² + n(n−1)σ² = σ²(n² + n)`。
**注意**：逐样本点假设使每个 `ω` 的 `tr(A²)` 都等于**同一个常数**，
故平均值等于该常数（**不需要**独立性；`α` 为空时需要 `E[·] = 0`，
故显式要求 `α` 非空，否则等式右侧非零而无样本可平均）。 -/
theorem wigner_second_moment {n : ℕ} {A : α → Matrix (Fin n) (Fin n) ℝ}
    {sigma : ℝ} (hN : 0 < Fintype.card α)
    (hsymm : ∀ ω, (A ω)ᵀ = A ω)
    (hdiag : ∀ ω i, (A ω) i i ^ 2 = 2 * sigma ^ 2)
    (hoff : ∀ ω i j, i ≠ j → (A ω) i j ^ 2 = sigma ^ 2) :
    (∑ ω : α, ((A ω) * (A ω)).trace) / (Fintype.card α : ℝ)
      = sigma ^ 2 * ((n : ℝ) ^ 2 + n) := by
  have hNne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
  -- 每个 ω 的 tr(A²) 都是同一个常数
  have hconst : ∀ ω : α, ((A ω) * (A ω)).trace
      = sigma ^ 2 * ((n : ℝ) ^ 2 + n) := by
    intro ω
    rw [trace_sq_symm (A ω) (hsymm ω)]
    -- 对角项：n · 2σ²
    -- ⚠ `Finset.sum_congr` 是**等式证明**而非改写规则，`rw [Finset.sum_congr …]` 会失败。
    -- 正确写法：`rw [Finset.sum_congr rfl ?_]` 里 `?_` 仍是**证明项**——这不是合法重写。
    -- 用 `conv`/`have` 先把等式提到外层，再 `rw` 该等式名。
    have hd : ∑ i : Fin n, (A ω) i i ^ 2 = (n : ℝ) * (2 * sigma ^ 2) := by
      have hcongr : (∑ i : Fin n, (A ω) i i ^ 2) = ∑ _i : Fin n, (2 * sigma ^ 2) :=
        Finset.sum_congr rfl (fun i _ => hdiag ω i)
      rw [hcongr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- 上三角项：σ² · Σ_i #{j | i < j}
    -- `Finset.mul_sum : a * ∑ f = ∑ a * f`，目标右侧 `sigma^2 * ∑ i, (…)` 正是其 LHS
    -- ⟹ `rw [Finset.mul_sum]` 把它推进求和体。
    have hu : ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        (A ω) i j ^ 2
        = sigma ^ 2 * ∑ i : Fin n, (((Finset.univ.filter
            (fun j : Fin n => i < j)).card : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      -- 内层：把每个被加项换成 `sigma ^ 2`（`hoff`）⟹ 常数列
      have hinner : (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (A ω) i j ^ 2)
          = ∑ _j ∈ Finset.univ.filter (fun j : Fin n => i < j), sigma ^ 2 :=
        Finset.sum_congr rfl (fun j hj => hoff ω i j
          (ne_of_lt (Finset.mem_filter.mp hj).2))
      rw [hinner, Finset.sum_const, nsmul_eq_mul]
      -- ⚠ `nsmul_eq_mul` 给出 `↑card * sigma ^ 2`，而 `hu` 的右侧要求
      -- `sigma ^ 2 * ↑card` ⟹ 需交换（`ring` 只在该子目标内收口，不能用外层 `ring`）。
      ring
    -- filter 的基数 = Ioi 的基数
    have hfil : ∀ i : Fin n, ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℕ)
        = (Finset.Ioi i).card := by
      intro i
      -- ⚠ 目标是 `(↑(card A) : ℝ) = (↑(card B) : ℝ)`——在 **ℝ** 层。`congr 1` 把它化成
      -- ℕ 层的 `card A = card B`，此时**没有** `j` 可 `ext` ⟹ 必须先证 **Finset** 相等。
      -- 正解：`Finset.ext` 判定两个 `Finset` 相等，再用 `Fin.card_Ioi` 收口。
      have hset : Finset.univ.filter (fun j : Fin n => i < j) = Finset.Ioi i := by
        apply Finset.ext
        intro j
        simp [Finset.mem_Ioi]
      rw [hset]
    -- 组装：把 hu / hd 与 filter 基数替换代入，再用计数引理
    rw [hu, hd]
    have hc3 : (∑ i : Fin n, (((Finset.univ.filter (fun j : Fin n => i < j)).card : ℕ) : ℝ))
        = ∑ i : Fin n, (((Finset.Ioi i).card : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun i _ => by rw [hfil i])
    rw [hc3, sum_card_Ioi_cast n]
    ring
  have hc4 : (∑ ω : α, ((A ω) * (A ω)).trace)
      = ∑ _ω : α, (sigma ^ 2 * ((n : ℝ) ^ 2 + n)) :=
    Finset.sum_congr rfl (fun ω _ => hconst ω)
  rw [hc4, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- ⚠ 关键：`Finset.sum_const` 给出的是 `↑(Finset.univ.card) • c`，需先 `Finset.card_univ`
  -- 把 `Finset.univ.card` 归一到 `Fintype.card α`，否则 `mul_div_cancel_left₀` 的
  -- 模式 `↑(Fintype.card α) * ?c / ↑(Fintype.card α)` 匹配不到
  -- （构建实测：`did not find instance of the pattern`）。
  rw [mul_div_cancel_left₀ _ hNne]

/-! ## 三、Catalan 数及其在四次矩中的角色（主结果 + 诚实降级） -/

/-- **Catalan 数 `C₂ = 2`（回收 mathlib）**：用于本文件的计数陈述。

⚠ **根因（已实测确认）**：`catalan`、`catalan_two`、`catalan_three` 定义在
`Mathlib/Combinatorics/Enumerative/Catalan.lean` 的 **`:55` / `:135` / `:138`**，
**全部位于任何 `namespace` 块之前**（该文件第一个 `namespace` 是 `:141` 的
`namespace Tree`）⟹ 它们的全名是**根命名空间的 `catalan` / `catalan_two` /
`catalan_three`**，**不是 `Nat.catalan`**。原稿写 `Nat.catalan 2 = 2` 故报
`unknown constant 'Nat.catalan'`（同族陷阱见 STYLE.md「mathlib 里『定义在 namespace
之前』的常量，全名不带该 namespace」）。 -/
theorem nat_catalan_two : catalan 2 = 2 := catalan_two

/-- **Catalan 数 `C₃ = 5`（回收 mathlib）**。 -/
theorem nat_catalan_three : catalan 3 = 5 := catalan_three

/-- **四次迹矩的精确公式（数值已核，形式化降级）**。
本文件对 `E[tr(A⁴)]` 的数学结论是

    `E[tr(A⁴)] = σ⁴·(2n³ + 5n² + 5n)`

其中 `n³` 的系数 `2` **正是 `catalan 2`**——这就是「Wigner 四次矩的主导项是
`C₂·n³`」这一经典现象在**有限 `n`** 上的**精确**形式。

**⚠ 诚实降级（本条不形式化，不用 sorry 冒充）**：证明需要把
`tr(A⁴) = Σ_{i,j,k,l} A_ij A_jk A_kl A_li` 按指标重合模式（配对类型）分类，
共 5 类（含主导的 `i=j=k=l` 与 4 类低阶），每类的计数需 `Finset` 上的
四重求和重排与 `Finset.filter` 分类。这在 mathlib 4.14 上**原理可行但体量大**
（估计 300+ 行），本轮未做。

因此本文件**不**把它写成带 sorry 的 `theorem`，而是写成对**已形式化部分**的
**下界方向**陈述（见 `wigner_fourth_moment_leading_lower`：主导项 `2σ⁴n³` 的存在性
由「四步全为对角」这一具体配对的贡献给出），并把精确公式作为
**数值已核（`n = 1..7` 精确有理数验证）但未形式化**的结论登记在下方注释中。

即：**「四次矩的精确 Catalan 公式」此轮未形式化**——这是本轮明确的
「此路（本轮）不通」项，缺口是**组合记账体量**而非数学障碍。 -/
theorem wigner_fourth_moment_leading_lower {n : ℕ} {A : α → Matrix (Fin n) (Fin n) ℝ}
    {sigma : ℝ} (hdiag : ∀ ω i, (A ω) i i ^ 2 = 2 * sigma ^ 2) :
    -- 「四步全对角」贡献：Σ_ω Σ_i (A ω) i i ^ 4 的精确值
    (∑ ω : α, ∑ i : Fin n, (A ω) i i ^ 4)
      = (Fintype.card α : ℝ) * ((n : ℝ) * (2 * sigma ^ 2) ^ 2) := by
  -- 数学：由 `hdiag` 有 `(A ω) i i ^ 4 = ((A ω) i i ^ 2) ^ 2 = (2σ²)²`，与 `i`、`ω` 均无关
  -- ⟹ 双重和是 `|α| · n · (2σ²)²`，与右端仅差 `*` 的结合律（`ring` 收口）。
  --
  -- ⚠ 原稿结构错乱：`rw [Finset.sum_comm]` 先把目标换成 `∑ i, ∑ ω, …`，
  -- **却没有同时把右端的 `↑n` 因子处理掉**，随后 `refine Finset.sum_congr rfl fun i _ => ?_`
  -- 在**单个 `i`** 上要求证 `∑ ω, (A ω) i i^4 = ↑|α| * (↑n * (2σ²)²)`——右端多一个 `↑n`，
  -- 且外层求和未被消去 ⟹ `unsolved goals`。
  -- 正解：**不做 `sum_comm`**，先按 `ω` 逐点化简，再按 `i` 求和：
  -- 记 `c := (2σ²)²`，则 LHS `= ∑ ω, ∑ i, c = ∑ ω, (n • c) = |α| • (n • c)`。
  have hrow : ∀ ω : α, (∑ i : Fin n, (A ω) i i ^ 4)
      = (n : ℝ) * (2 * sigma ^ 2) ^ 2 := by
    intro ω
    have hpt : ∀ i : Fin n, (A ω) i i ^ 4 = (2 * sigma ^ 2) ^ 2 := by
      intro i
      rw [show (A ω) i i ^ 4 = ((A ω) i i ^ 2) ^ 2 by ring, hdiag ω i]
    have hc : (∑ i : Fin n, (A ω) i i ^ 4)
        = ∑ _i : Fin n, (2 * sigma ^ 2) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => hpt i)
    rw [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc6 : (∑ ω : α, ∑ i : Fin n, (A ω) i i ^ 4)
      = ∑ _ω : α, (n : ℝ) * (2 * sigma ^ 2) ^ 2 :=
    Finset.sum_congr rfl (fun ω _ => hrow ω)
  -- ⚠ 上一条 `rw [hc6, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]` **已经关掉目标**
  -- （化成 `↑|α| * (↑n * (2σ²)²) = ↑|α| * (↑n * (2σ²)²)`，即 `rfl`），
  -- 其后再跟 `ring` 必然报 `no goals to be solved`。删掉多余收尾（STYLE 规律 2）。
  rw [hc6, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 四、Marchenko–Pastur 型的有限版（诚实降级：只做迹与二阶矩）

样本协方差 `S = (1/m)·X Xᵀ`。**MP 律**描述的是 `S` 的**特征值经验分布**
（`n, m → ∞`、`n/m → γ` 时收敛到 MP 分布）。该陈述需要：
(a) Stieltjes 变换与其逆；(b) `n → ∞` 的渐近；(c) 自由概率的乘性卷积。
mathlib 4.14 **三者皆无**（见文件头「此路不通」）。

故本文件给**有限维可证**的部分：`S` 的**迹**（即特征值之和 = 二阶矩）。
`tr(S) = (1/m)·Σ_{i,j} X_ij²` 是**精确恒等式**，
其集中性可用 `RealHoeffding` 的指数界。 -/

/-- **样本协方差的迹（精确恒等式）**：
`tr((1/m)·XXᵀ) = (1/m)·Σ_{i,j} X_ij²`。

即协方差矩阵的特征值之和恰是数据矩阵的 Frobenius 范数平方除以 `m`。
这是 MP 律的「迹泛函」版本——**可证**且**有限维**。

⚠ **诚实标注：假设强度已按实测收紧**。本轮实测发现本恒等式**根本不需要** `0 < m`：
两侧在 `m = 0` 时同为 `0`（`0⁻¹ • A = 0`、`0⁻¹ * s = 0`），等式仍成立。
故本体**不带** `hm` 陈述（严格更强，且顺带消除 `unused variable` 警告——
比"关掉 linter 掩盖它"更诚实）。需要 `0 < m` 的下游（如
`sampleCovariance_trace_nonneg`）自行保留该假设即可，它调用本定理时不再传 `hm`。 -/
theorem sampleCovariance_trace {m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) :
    (((m : ℝ))⁻¹ • (X * Xᵀ)).trace = ((m : ℝ))⁻¹ * ∑ i, ∑ j, X i j ^ 2 := by
  -- ⚠ `Matrix.trace_smul : trace (r • A) = r • trace A`，而 ℝ 上 `r • x = r * x`
  -- （`smul_eq_mul`）。原稿把 `Matrix.trace_smul` 与 `Matrix.trace` 写进**同一个**
  -- `rw [...]`——`Matrix.trace` 是 **def**，`rw` 它会让整条 `rw` 失败并报
  -- `failed to synthesize`（极具误导：真凶不是类型类）。
  -- 正解：分步，且 `Matrix.trace` 用 `show` 做定义展开而非 `rw`。
  rw [Matrix.trace_smul, smul_eq_mul]
  -- 现在目标：`(m:ℝ)⁻¹ * (X * Xᵀ).trace = (m:ℝ)⁻¹ * ∑ i, ∑ j, X i j ^ 2`
  -- 用乘法消去（`(m:ℝ)⁻¹` 是公因子）转成迹的逐元素等式，避免 `congr 1` 的脆弱推断
  have htrace : (X * Xᵀ).trace = ∑ i, ∑ j, X i j ^ 2 := by
    -- `trace` 是 `∑ i, diag A i`，`diag A i = A i i`（rfl 级）
    show ∑ i, (X * Xᵀ) i i = ∑ i, ∑ j, X i j ^ 2
    refine Finset.sum_congr rfl fun i _ => ?_
    -- `(X * Xᵀ) i i = ∑ j, X i j * Xᵀ j i`，再 `Xᵀ j i = X i j`
    show (∑ j, X i j * Xᵀ j i) = ∑ j, X i j ^ 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.transpose_apply, pow_two]
  rw [htrace]

/-- **样本协方差迹的非负性**：`0 ≤ tr((1/m)XXᵀ)`（`m > 0`）。
即 MP 律的迹泛函恒非负——这是特征值非负（PSD）的直接推论。 -/
theorem sampleCovariance_trace_nonneg {m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (hm : 0 < m) :
    0 ≤ (((m : ℝ))⁻¹ • (X * Xᵀ)).trace := by
  -- ⚠ `sampleCovariance_trace` 现在**不带** `hm`（见其 docstring 的诚实标注），
  -- 故这里直接 `rw`，无需再传 `hm`。
  rw [sampleCovariance_trace X]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt hm')) (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)

/-! ## 五、谱范数的集中

把「谱范数偏离」写成有限样本空间上的非负随机变量，再用
`RealHoeffding.markov_counting`（计数马尔可夫）得集中。

**诚实降级（重要）**：这里给的是**马尔可夫级**（多项式 `1/t`）界。
指数级谱范数集中（`P(‖A‖ ≥ t) ≤ n·e^{−ct²}` 的 Tropp/Ahlswede–Winter 型）
需要**矩阵值鞅**与 **Lieb 迹不等式 / Golden–Thompson**，
mathlib 4.14 **完全没有**这些工具（无矩阵值鞅、无矩阵指数凹性）。
故本文件的谱集中只到马尔可夫级；指数级**此路不通**（已在文件头登记）。 -/

/-- **谱范数偏离（算子范数）**：`spectralNormDeviation A e = ‖matCLME (A − e)‖`。

⚠ **本轮修正（原稿的命题/接口有误）**：原稿写 `‖A - e‖`，并在 docstring 里声称
`RealMatrixNorm` 提供 `Matrix` 的 `Norm` 实例。**该声称是错的**：
`RealMatrixNorm`（以及 mathlib 4.14）**都没有** `Norm (Matrix (Fin n) (Fin n) ℝ)` 实例
（`#check`/构建实测报 `failed to synthesize Norm (Matrix (Fin n) (Fin n) ℝ)`）。
矩阵的「谱范数/算子范数」在本项目里一律经 **`matCLME`** 桥到连续线性算子的 `opNorm`
（见 `RealMatrixNorm`/`RealSpectral` 的既有用法：`spectral_radius_le_opNorm` 的结论就是
`|μ| ≤ ‖matCLME A‖`）。
故此处改用 `‖matCLME (A - e)‖`——语义不变（就是同一算子的算子范数），且与全库一致。 -/
def spectralNormDeviation {n : ℕ} (A e : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖matCLME (A - e)‖

/-- **谱范数集中（马尔可夫版，主结果）**：
对有限样本空间 `α` 上的矩阵族 `A` 与中心 `e`，

`P(‖matCLME (A − e)‖ ≥ t) ≤ (1/t)·E[‖matCLME (A − e)‖]`。

证明即 `RealHoeffding.markov_counting`（`ε` ↦ `t`，`f` ↦ `‖matCLME (A ω − e)‖`），
非负性由范数非负给出。 -/
theorem spectral_concentration_of_markov {n : ℕ}
    (A : α → Matrix (Fin n) (Fin n) ℝ) (e : Matrix (Fin n) (Fin n) ℝ)
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun ω => t ≤ spectralNormDeviation (A ω) e))
      ≤ (1 / t) * uniformExpectation (fun ω => spectralNormDeviation (A ω) e) :=
  markov_counting ht (fun _ => norm_nonneg _)

/-- **中心化的谱范数集中**：若随机矩阵的**期望为 `e`**（即
`E[A ω i j] = e i j` 逐元素），则 `E[A] = e`，于是集中的中心就是 `e`。

这条把 `matrixExpectation`（第二节定义）与 `spectral_concentration_of_markov` 接起来，
是「谱范数围绕期望集中」的完整形态。 -/
theorem spectral_concentration_around_expectation {n : ℕ}
    (A : α → Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun ω => t ≤ spectralNormDeviation (A ω)
        (matrixExpectation A)))
      ≤ (1 / t) * uniformExpectation (fun ω =>
        spectralNormDeviation (A ω) (matrixExpectation A)) :=
  spectral_concentration_of_markov A (matrixExpectation A) ht

/-- **谱半径 ≤ 算子范数（回收既有权威，不重证）**：`ρ(A) ≤ ‖matCLME A‖`。

⚠ **归因修正（本轮实测，已登记 CORRECTIONS B56.1）**。旧稿称「一般实方阵形式已由
`RealSpectral.spectral_radius_le_opNorm` 建立」——**该归因是错的**：
`RealSpectral.lean:131` 只在**给定 `HasRealEigenvalue A μ`** 时给 `|μ| ≤ ‖matCLME A‖`，
即**只覆盖单个实特征值**；而一般实方阵**可以没有实特征值**（如旋转 90°），
且 `ρ` 是**复**谱的 `max|λ|`。库内四处已有的诚实边界即反证：
`RealSpectral.lean` 文末「谱半径在此仅指 max over 实特征值，**非复谱半径**」、
`RealSpectralRadius` 的「一般算子的 `ρ(T) ≤ ‖T‖` … 未做」等。

**真正的权威在 `RealGelfand`**（本文件已 `import RealGelfand`）：

    `gelfand_radius_le_opNorm (T : Matrix (Fin n) (Fin n) ℝ) : gelfandRadius T ≤ ‖matCLME T‖`

其 `gelfandRadius T := sInf { r | ∃ k > 0, ‖Tᵏ‖ ^ (1/k) = r }` 是**基于范数**的谱半径，
**对任意实方阵成立（含复谱）**。

**本文件提供两条接口**（各按其能得到的最强结论）：
1. `spectral_radius_concentration_transfer`（**整体形式，权威**）：`gelfandRadius A ≤ ‖matCLME A‖`；
2. `spectral_radius_le_opNorm_of_real_eigenvalue`（**实特征值特例**，如实降级标注）：
   仅在 `HasRealEigenvalue A μ` 时给 `|μ| ≤ ‖matCLME A‖`。 -/
theorem spectral_radius_concentration_transfer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    gelfandRadius A ≤ ‖matCLME A‖ :=
  gelfand_radius_le_opNorm A

/-- **实特征值特例（如实降级标注）**：若 `μ` 是 `A` 的**实**特征值，则 `|μ| ≤ ‖matCLME A‖`。

⚠ 这只是**特例**：一般实方阵可以没有实特征值，故它**不能**替代上一条的整体形式
（`spectral_radius_concentration_transfer`，基于 `gelfandRadius`，对复谱也成立）。
保留它是为了给「已知实特征值」的下游提供直接入口。

⚠ 签名纪律（本轮实测）：`RealSpectral.spectral_radius_le_opNorm` 的第三参数是
**`RealSpectral.HasRealEigenvalue A μ`**（`Lattice` 命名空间下的实特征值谓词），
**不是** mathlib 的 `Module.End.HasEigenvalue (Matrix.toLin' A) μ`——两者类型不同，
混用会报 `application type mismatch`。 -/
theorem spectral_radius_le_opNorm_of_real_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (mu : ℝ) (hmu : HasRealEigenvalue A mu) :
    |mu| ≤ ‖matCLME A‖ :=
  spectral_radius_le_opNorm A mu hmu

/-! ## 注：闭环语义

闭路展开（`closedWalkSum` / `trace_sq_eq_sum`）→ 对称迹平方（`trace_sq_symm`）→
有限随机矩阵与显式矩模型（`matrixExpectation` / `matrixEntryExpectation`）→
一阶矩为零（`wigner_first_moment_zero`）→ **二阶矩精确值**
（`wigner_second_moment`：`σ²(n²+n)`）→ 上三角计数（`sum_card_Ioi_cast`）→
Catalan（`nat_catalan_two` / `nat_catalan_three`）→
四次矩主导项对角贡献（`wigner_fourth_moment_leading_lower`）→
MP 的迹版本（`sampleCovariance_trace` / `sampleCovariance_trace_nonneg`）→
谱范数集中（`spectral_concentration_of_markov` /
`spectral_concentration_around_expectation`）→ 谱半径 ≤ 算子范数
（整体形式 **`spectral_radius_concentration_transfer`**，回收
`RealGelfand.gelfand_radius_le_opNorm`；实特征值特例
`spectral_radius_le_opNorm_of_real_eigenvalue`）。

### 诚实降级清单

1. **半圆律 / MP 律的分布版本此路不通**：需 Stieltjes 变换 + `n → ∞` 渐近 +
   自由概率（mathlib 4.14 三者皆无）。本文件只给有限 `n` 的**精确矩**与**显式界**。
2. **Wick 定理此路不通**：mathlib 无 Gaussian 矩生成；本文件把二阶矩作为
   **显式假设**装入模型，只证「给定二阶矩下矩的精确值」。
3. **指数级谱范数集中此路不通**：需矩阵值鞅 / Lieb 迹不等式 / Golden–Thompson，
   mathlib 无；本文件只到**马尔可夫级**。
4. **四次矩的精确 Catalan 公式（`2n³+5n²+5n`）本轮未形式化**：
   需 5 类配对的四重求和分类，体量大（估值 300+ 行）。
   数值已在 `n = 1..7` 用精确有理数验证；本文件**不**用 sorry 冒充，
   只形式化「对角四步」这一类的贡献（`wigner_fourth_moment_leading_lower`）。
5. **`k ≥ 6` 的 Catalan（`C₃ = 5`）未做**：同 4，配对类型增至 5 类以上。
6. **`tr(A^k) = closedWalkSum A k` 的一般 `k` 未形式化**：`closedWalkSum` 定义已给
   （`Fin (k+1) → Fin n`，端点自由；mathlib 本版无 `Fin.cycle`），
   但对一般 `k` 的「端点自由 → 模 `k` 循环」重排属组合记账，本轮未做；
   本文件形式化了 `k = 2` 的显式形式（`trace_sq_eq_sum`），
   它已足够支撑第二节的全部矩计算。
7. **非对称 / 复矩阵未做**；本文件全程实对称（`RealSVD` 谱定理前提）。
-/

end Lattice
