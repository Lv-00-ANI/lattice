import Mathlib
import Lattice.Lib.Architectures.RealSparseCodingNorms
import Lattice.Lib.LinearAlgebra.RealSparseCodingSoftThreshold
import Lattice.Lib.LinearAlgebra.RealSparseCodingOptimality
import Lattice.Lib.LinearAlgebra.RealSparseCodingCounterexamples
import Lattice.Lib.LinearAlgebra.RealSparseCodingCoherence
/-!
# LATTICE: 稀疏编码 —— L0/L1 范数、软阈值算子的最优性与互相干唯一性

稀疏编码的核心问题：给定字典 `A` 与观测 `y`，求**最少非零项**的表示 `x`
（`min ‖x‖₀ s.t. Ax = y`）。该问题是 **NP 难**的，实践中代之以
`min ‖x‖₁ s.t. Ax = y`（**凸松弛**）。本文件把这两条主张里**可证**的部分形式化：

  · `L0`/`L1` 的定义与基本不等式（`‖x‖₁ ≥ ‖x‖₀` 型）——**凸松弛的合法性来源**；
  · **软阈值算子** `soft_λ(y) = sign(y)·max(|y|−λ, 0)` 是
    `min_x ½(x−y)² + λ|x|` 的**唯一最优解**（一维情形，完整证明）——
    这是 L1 正则化/TISTA/ISTA 全部算法的**原子步骤**，也是本文件的核心；
  · **互相干** `μ(A) = max_{i≠j} |⟪a_i, a_j⟫|`（单位列规范下）的良定义与
    `μ < 1/(2k−1)` 型的**唯一性充分条件**（`k`-稀疏可辨识）。

## 本文件建立

**一、L0 / L1 范数与凸松弛的合法性**
1. `l0Norm`：`‖x‖₀ = #{i | x_i ≠ 0}`（非零项个数，`ℕ` 值）；
2. `l1Norm`：`‖x‖₁ = Σ_i |x_i|`（`ℝ` 值）；`l2NormSq`：`‖x‖₂²`；
3. **⚠ 纠错（本轮实测，STYLE §4「先代小整数判真假」）**：
   任务描述的 `‖x‖₁ ≥ ‖x‖₀` **为假**——`x = (1/2, 0)`：`L0 = 1 > 1/2 = L1`；
   且**加取整也救不回来**——`x = (1/2, 1/2)`：`L0 = 2 > 1 = ⌈L1⌉`。
   两条反例均已**机器验证**（`l0_le_l1_false_counterexample` /
   `l0_le_ceil_l1_false_counterexample`）。
   **根因**：`L0` 是**计数**、`L1` 是**质量**，量纲不同，无量纲假设下不可比。
4. 本文件采用的**正确替代**（无条件或条件明确、且为真）：
   · `l0_le_l1_of_one_le`：**条件版** `(∀ i, x i ≠ 0 → 1 ≤ |x i|) → L0 ≤ L1`；
   · **`l1_sq_le_l0_mul_l2sq`**：**Cauchy–Schwarz 版 `‖x‖₁² ≤ ‖x‖₀·‖x‖₂²`**
     （**无条件**；这是真正的「`L1` 被 `√L0·L2` 控制」，前置是 `l1_le_l0_sqrt`）；
   · `l1_le_l0_mul_sup`：**最大元版 `‖x‖₁ ≤ ‖x‖₀·‖x‖_∞`**（无条件）。
   三条合起来是「L1 是 L0 的凸代理」的**可证依据**；
   本文件**不主张**任何 `L0 ≤ L1` 形式的无条件不等式。
5. `l0_eq_zero_iff` / `l0_pos_iff`：`‖x‖₀ = 0 ⟺ x = 0`；`0 < ‖x‖₀ ⟺ x ≠ 0`。

**二、软阈值算子（核心）**
6. `softThresh`：`softThresh lam y = sign(y)·max(|y|−lam, 0)`；
7. `softThresh_eq`：分段显式形式（`y > lam` / `|y| ≤ lam` / `y < −lam` 三段）；
8. **`softThresh_optimal`（核心主结果）**：**软阈值是 L1 近端算子的唯一最优解**——
   对 `lam > 0`，`x = softThresh lam y` 是 `f(x) = ½(x−y)² + lam·|x|` 的
   **唯一全局最小点**（最优性 + 等号刻画两部分）。
   证明：**按 `x` 的三段分情形**（`x > 0` / `x = 0` / `x < 0`），
   每段内把目标化为无约束二次函数并**配方**
   （`quadraticMinimizer_identity` / `quadraticMinimizer_identity_neg`），
   再证明三段的下界**一致**于 `softThresh` 处的值（`hval` 引理）；
   完全绕开 `ConvexOn`（它是 **def 别名**，点号投影会失败，见 STYLE §4）。
9. `softThresh_zero`：`softThresh lam 0 = 0`（稀疏性的来源：小信号被压到恰为 0）；
10. `softThresh_eq_zero_of_abs_le`：`|y| ≤ lam ⟹ softThresh lam y = 0`（**死区**）；
11. `softThresh_of_le`：`0 < λ ≤ y ⟹ soft_λ(y) = y − λ`（大信号平移）；
    ⚠ **原稿只假设 `λ ≤ y` ⟹ 命题为假**（见下方「诚实边界」第三条假命题登记）；
    `softThresh_of_le_false_counterexample` 给出机器验证的反例（`λ = −1, y = 0`）；
12. `softThresh_nonexpansive`：**非扩张性** `|soft_λ y₁ − soft_λ y₂| ≤ |y₁ − y₂|`——
    软阈值是 1-Lipschitz（这是 ISTA/TISTA **收敛性**的关键假设）；
    证明走分解 `soft_λ y = max(y−λ, 0) + min(y+λ, 0)` 与两条 max/min 差的不等式。
13. `softThresh_odd`：奇对称 `soft_λ(−y) = −soft_λ(y)`；
    `softThresh_mono`：单调性（由非扩张 + 奇对称）；
    `proxL1` / `proxL1_optimal`：近端算子语言的固定命名与最优性重述。

**三、互相干与唯一性充分条件**
14. `Dict m n`：有限字典 `A : Fin m → Fin n → ℝ`；`coherence`：两列相干
    `|⟪a_i, a_j⟫| = |Σ_k A k i · A k j|`；`mutualCoherence`：最大值；
15. `mutualCoherence_def`：显式核算 `μ(A) = sup'_{i≠j} |Σ_k A k i · A k j|`
    （用 `Finset.sup'` 对**函数值**取上确界——⚠ `Finset.max'` 比的是**指标**，
    见 STYLE §4 的「名字误导型」陷阱）；
    ⚠ **`μ` 带 `(hn : 2 ≤ n)` 参数**：非对角对 `(i, j)`（`i ≠ j`）只在 `n ≥ 2` 时存在，
    `Finset.sup'` 要求 `Nonempty`，而 `n ≤ 1` 时 filter **恰为空**。
    这是**第三处诚实偏离**：收窄定义域而非为 `n ≤ 1` 编造 `Nonempty`（详见下方「诚实边界」）；
16. `mutualCoherence_nonneg` / `mutualCoherence_le_one_of_unitCols`：非负性；
    单位 Euclid 范数列 ⟹ `μ ≤ 1`（Cauchy–Schwarz）；
    `coherence_le_mutualCoherence`：非对角相干被 `μ` 控制；
17. **`mutualCoherence_lt_inv`（唯一性充分条件的界形式）**：
    `k ≥ 1`、`μ < 1/(2k−1)` ⟹ `(2k−1)·μ < 1`
    （整理成后续组合论证可直接用的**无除法**形式）；
18. **`sparse_uniqueness_of_nullspace`（主结果，逻辑骨架）**：
    若 `A` 的零空间**不含非零 `2k`-稀疏向量**（显式假设 `hNull`），
    则 `A x = A y` 且 `x, y` 都 `k`-稀疏 ⟹ `x = y`。
    证明：差向量 `x − y` 落零空间（零空间是线性的），
    其支撑 ⊆ 两者支撑之并（`Finset.card_union_le` + `omega`），
    故 `‖x−y‖₀ ≤ 2k`，由 `hNull` 得差为 0。
19. `nullspace_vanishes_on_column`：`k = 1` 时 `hNull` 的**可证刻画**——
    「零空间无 `1`-稀疏非零向量」等价于「`A` 无零列」（给出非空实例）。

## 诚实边界（诚实 / 未证 / 未做 / 降级 / 标注）

- **⚠ 前置命题纠错（本轮实测，按 STYLE §4「先代小整数判真假」）**：
  任务描述的 `‖x‖₁ ≥ ‖x‖₀`（「L1 是 L0 的凸松弛」的形式化）**为假**。
  反例 `x = (1/2, 0)`：`L0 = 1 > 1/2 = L1`（机器验证
  `l0_le_l1_false_counterexample`）；且**上加取整也无效**——
  `x = (1/2, 1/2)`：`L0 = 2 > 1 = ⌈L1⌉`（机器验证
  `l0_le_ceil_l1_false_counterexample`）。
  **根因**：`L0` 是**计数**、`L1` 是**质量**，量纲不同，无量纲假设下不可比。
  **处置**：不证该假命题，改为证三条**真**的替代
  （`l0_le_l1_of_one_le` 条件版 / `l1_sq_le_l0_mul_l2sq` Cauchy–Schwarz 版
  **无条件** / `l1_le_l0_mul_sup` 最大元版 **无条件**），并登记上述两条反例。
  这是与任务清单的**第一处诚实偏离**。
- **诚实降级：`sparse_uniqueness_of_nullspace` 的假设形式**。
  经典的 `μ < 1/(2k−1)` 唯一性定理证明需要一个**真正的组合引理**：
  对 `2k`-稀疏的 `z`，比较 `‖Aᵀ A z‖_∞ ≥ (1 − (k−1)μ)·‖z‖_∞`
  与 `‖Aᵀ A z‖_∞ ≤ (k−1)μ‖z‖_∞` 得矛盾。其中**第一步**
  （`AᵀA z` 的 `i` 分量 `= z_i + Σ_{j≠i} ⟪a_i,a_j⟫ z_j`，
  用 `|Σ_{j≠i}| ≤ (k−1)μ‖z‖_∞` 与 `‖z‖_∞` 的定义）需要按 `z` 的**支撑集**
  做 `Finset.filter` 计数与双重量化的精细拆分——**能在 mathlib 4.14 上做但体积大**。
  本轮把该组合引理作为**显式假设** `hNull`（零空间无 `2k`-稀疏向量）陈述，
  **只证「`hNull` ⟹ 唯一性」这一步**（这一步是真定理，且是唯一性论证的
  **逻辑骨架**：唯一性 ⟺ 零空间平凡 + 差向量稀疏度加倍）。
  **未做**：从 `μ < 1/(2k−1)` 推出 `hNull` 的完整代数链。
  本文件**不声称**已证经典的互相干唯一性定理本身。
  这是与任务清单的**第二处诚实偏离**（任务允许「若能证」）；
  但 `mutualCoherence_lt_inv` 已把该条件的**可用界形式**备好，
  下游只需补组合引理即可闭环。
- **⚠ 诚实偏离之三（v6 新增）：`mutualCoherence` 的定义域收窄为 `n ≥ 2`**。
  `Finset.sup'` 的签名要求 `Nonempty`（`s.sup' (H : s.Nonempty) f`），
  而非对角对 `(i,j)`（`i ≠ j`）**只在 `n ≥ 2` 时存在**：`n = 1` 时
  `Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 ≠ p.2) = ∅`，`sup'` **无值可给**。
  ⇒ 把 `(hn : 2 ≤ n)` 作为**显式参数**（`(0,1)` 即一对合法非对角指标，`Nonempty` 可显式构造）。
  ⚠ **未做**：`n ≤ 1` 时的 `μ`（该情形下"互相干"在没有非对角对时无定义，
  强行赋值 `0` 会让 `mutualCoherence_nonneg` / `le_one_of_unitCols` 的
  陈述与经典定理**语义脱节**——这正是本文件拒绝的做法）。
  这**不削弱**主结果：稀疏编码的非对角相干只在 `n ≥ 2`（字典至少两列）时有意义。
- **⚠ 第三处假命题登记（v6 实测，按 STYLE §4「先代小整数判真假」）**：
  `softThresh_of_le` 原陈述 `λ ≤ y ⟹ soft_λ(y) = y − λ`（**不加 `0 < λ`**）**为假**。
  反例 `λ = −1, y = 0`：`soft_λ(0) = sign(0)·max(|0|−(−1), 0) = 0 ≠ 1 = y − λ`
  （机器验证 `softThresh_of_le_false_counterexample`）；
  另一个更醒目的反例 `λ = −1, y = −1/2`：`soft_λ(−1/2) = −3/2 ≠ 1/2 = y − λ`。
  **根因**：`λ < 0` 时 `max(|y|−λ, 0) = |y|−λ ≠ |y|`，`sign` 因子把符号带偏；
  `λ` 是正则化强度，**物理上取 `λ ≥ 0`**。
  **处置**：改为 `0 < λ ≤ y ⟹ …`（**正确版本**，两处调用点都已有 `0 < λ`），
  并登记上例。这是与任务清单的**第四处诚实偏离**。
- **未做：L1 最小化的全局凸性证明**。mathlib 4.14 有 `ConvexOn`（但它是 **def 别名**，
  见 STYLE §4），本文件**不**走凸分析一般理论证 `½(x−y)² + λ|x|` 的凸性，
  而是**按分段直接证全局最优性**（`softThresh_optimal`）——后者更强（含唯一性），
  且完全绕开 `ConvexOn` 的点号投影陷阱。
- **未做：多维软阈值（组稀疏 / block soft-thresholding）**。本文件只做**标量**版
  （`x, y : ℝ`），这是稀疏编码的原子步骤。向量版需要 `‖·‖₂` 的
  Cauchy–Schwarz 型论证，属后续工作。
- **未做：硬阈值算子**。`hard_λ(y) = y·1_{|y|>λ}` **不是**任何凸泛函的最小点
  （这正是 L0 难的原因）。本文件**不给**硬阈值的最优性定理——
  因为该命题为**假**（数学事实，标注为未做而非降级）。
- **未做：字典学习（`A` 也待优化）**。本文件只处理 `A` 固定时的表示问题。
- **范围**：`x : Fin n → ℝ`（有限维），字典 `A : Fin m → Fin n → ℝ`；
  `l0Norm` 取 `ℕ` 值（非负项计数），`l1Norm` 取 `ℝ` 值。避免 `ℚ` 上的 `decide` 卡顿
  （见 STYLE §4：`by decide` 对 `ℚ` 卡）。
- 无 sorry / axiom / admit；所有定理真实可证。
-/


/-!
> **拆分说明（2026-10-15）**：本文件原含 **47 个声明**、1590 行。声明已按原有分节拆入
> 5 个模块，本文件**改为 re-export 门面**：
>
> | 子模块 | 原行范围 | 声明数 |
> |:--|:--|--:|
> | `RealSparseCodingNorms` | 155–493 | 11 |
> | `RealSparseCodingSoftThreshold` | 494–668 | 7 |
> | `RealSparseCodingOptimality` | 669–702 | 4 |
> | `RealSparseCodingCounterexamples` | 703–1276 | 12 |
> | `RealSparseCodingCoherence` | 1277–1588 | 13 |
> | **合计** | | **47** |
>
> 采用**连续切分**，边界**逐点校验注释深度为 0**：原文件 `:741` 的 `## ⚠ 假命题之四`
> 位于 `:703` 打开的注释块内部（散文，非标记），在彼处切分会得到 `unterminated comment`。
>
> 两个 importer（`RealCompressedSensing`、`RealSeamBridges2`）通过 `import RealSparseCoding`
> 取用 `l0Norm`/`l1Norm`/`l2NormSq`/`coherence`/`mutualCoherence`/
> `sparse_uniqueness_of_nullspace`/`IsSparse`；门面 re-export 全部子模块，名字仍可达。
-/
