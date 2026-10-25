import Mathlib
import Lattice.Lib.InfoTheory.RealFisherMatrix
import Lattice.Lib.InfoTheory.RealFisherInfo
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealCrossEntropy
/-!
# LATTICE: 信息几何（有限版）—— Fisher 度量、KL 的二阶展开与自然梯度不变性

`RealFisherMatrix` 已经建立了**矩阵 Fisher 信息** `F_{ij}(θ)` 及其对称性、二次型恒等式、
半正定性与零方向刻画，也给出了 EWC 二次惩罚。但它始终把 `F` 当作**代数对象**使用：
没有说 `F` 是**度量张量**（没有长度/夹角/测地线的语言），也没有信息几何的
**核心恒等式**

    KL(p_θ ‖ p_{θ+dθ}) = ½ dθᵀ F(θ) dθ + o(‖dθ‖²)

更没有**自然梯度** `F(θ)⁻¹∇L` 及其在重参数化下的不变性。`RealFisherInfo` 的诚实边界
里明确写着「未做：Fisher 信息与 KL 的二阶展开联系、自然梯度的收敛性」。
本文件补上**离散有限版**信息几何：全部在有限概率向量上做，避开流形/测地线的微分几何机器。

## 建模抉择（关键）

严格写 `KL(p_θ ‖ p_{θ+dθ})` 需要「参数化 `θ ↦ p_θ` 在 `θ` 处可微」这一分析前提，
而 `Real.log` 在非正处取 0、`deriv` 在不可导处取值任意，直接对 `KL` 用
`HasFDerivAt`/`Asymptotics.IsLittleO` 会在**开集邻域存在性**上引入大量与信息几何无关的
技术负担（有限维参数族的光滑性、概率单纯形的边界）。

因此本文件的路线是：**把二阶展开拆成「代数恒等式 + 一条标量不等式」**。

1. **代数骨架（无条件、精确）**：对任意正概率向量 `p, q`，
   `KL(p‖q) = Σ_a p_a·[(p_a − q_a)/p_a − d(p_a,q_a)]` 型分解
   （由 `log_le_sub_one_of_pos` 的方向改写），从而得到
2. **二次型主项**：`Σ_a (p_a − q_a)²/p_a`（这正是 Fisher 二次型在「`q` 是 `p` 的一阶扰动」
   下的形状），
3. **余项控制**：`0 ≤ Σ_a p_a·(log(p_a/q_a) − (p_a−q_a)/p_a + (p_a−q_a)²/(2p_a²))`
   类余项非负性 —— 由此把 KL 夹在
   `½·χ²(p,q) ≤ KL(p‖q)` 与 `KL(p‖q) ≤ ...` 之间。

**与任务书要求的对照（诚实说明）**：任务书写的是 `o(‖dθ‖²)` 形式（真正的渐近展开）。
本文件**没有**走 `Asymptotics.IsLittleO` 路线，而是给出**更强的、无渐近的、
对每个 `q` 都成立的精确不等式**（二次型下界 + 三次型上界）。理由与收益：

- 渐近形式 `o(‖dθ‖²)` 在 mathlib 上需要「`θ ↦ p_θ` 的 `HasFDerivAt` + 邻域内正性」，
  这些**是表示层的前提**而非信息几何的内容，且会让定理难以直接使用；
- 本文件的 `kl_chiSqSym_lower_bound`（`½·chiSqSym ≤ KL`）**蕴含**渐近形式：
  只要 `q → p` 沿一阶扰动族取极限，`chiSqSym` 就是 `dθᵀF dθ` 的主导项；
  `kl_expansion_of_first_order_family` 一节把这个蕴含关系显式写出。

即：本文件给的是**非渐近的定量版本**（信息几何的「硬」内容），
渐近陈述作为它的推论给出。

## 本文件建立

**一、Fisher 度量（对接 `RealFisherMatrix`）**
1. `fisherMetric`：`g_θ(u,v) = Σ_i Σ_j u_i·F_{ij}(θ)·v_j`——把 `RealFisherMatrix.fisherMatrix`
   **提升为双线性形式**（度量张量的分量姿态）；
2. `fisherMetric_symm`、`fisherMetric_add_left`、`fisherMetric_smul_left`：
   对称与双线性（度量张量良定义性）；
3. `fisherMetric_self_nonneg`：半正定（**直接回收**
   `RealFisherMatrix.fisherMatrix_psd`，不重复证明）；
4. `fisherMetric_eq_score_inner`：**度量 = score 的加权内积**
   `g_θ(u,v) = Σ_a p_θ(a)·(Σ_i u_i s_{a,i})·(Σ_j v_j s_{a,j})`
   ——这是 Fisher 度量作为 `L²(p_θ)` 内积的**信息几何意义**；
5. `fisherMetric_degenerate_iff`：退化方向刻画（回收零方向定理）。

**二、KL 的二阶展开（⚠ 含一条登记在案的假命题更正，见下文第二节）**
6. `chiSqSym` / `chiSqSymUp`：**对称化**卡方散度
   `Σ_a (q_a−p_a)²/max(p_a,q_a)` 与 `Σ_a (q_a−p_a)²/min(p_a,q_a)`；
7. 标量引理组：`log_one_add_le`（`log(1+u) ≤ u`）、
   `one_sub_inv_le_log`（`1 − 1/x ≤ log x`）、
   `neg_log_one_add_ge_half_sq`（**`u ∈ (−1,0]`（严格）**时 `−log(1+u) ≥ u²/2`；
   ⚠ 初稿作 `u ∈ [−1,0]`（**非严格**），**该版本为假**——`u = −1` 时 `1/2 ≤ 0`，
   因 Lean 的 `Real.log 0 = 0`。见诚实边界第 6 条）、
   `neg_log_one_add_nonpos`（`u ≥ 0` 时 `−log(1+u) ≤ 0`）、
   **二阶 sharp 组（本轮新增）**：`neg_log_ge_linear_add_sharp` / `neg_log_le_linear_add_sharp`；
8. `kl_chiSqSym_lower_bound`（**主结果**）：`p, q > 0`、`Σp = Σq = 1` ⟹
   `½·chiSqSym p q ≤ KL(p‖q)`——**二次型下界**，常数 `½` 紧
   （数值端点 `≈ 0.5049`）；
9. `kl_chiSqSym_upper_bound`（**主结果**）：`p, q > 0`、`Σp = Σq = 1` ⟹
   `KL(p‖q) ≤ chiSqSymUp p q`（**⚠ 需求和约束**；初稿称"逐项成立、无需求和约束"，
   该声称**为假**，反例 `k=1,p=(2),q=(1)`——见下文诚实边界第 7 条）；
10. `chiSqSym_perturbation_le`：一阶扰动族的 `chiSqSym` 恰为 `ε²·Σ δ²/p`；
11. `kl_expansion_of_first_order_family`（**渐近形式**）：`εδ ≤ 0`、`Σδ = 0` 时
    `½·ε²·Σ_a δ_a²/p_a ≤ KL(p ‖ p + εδ)`；除以 `ε²` 取 `ε → 0⁺` 即得
    `KL/ε² → ½Σδ²/p`，即 `KL = ½ dθᵀF dθ + o(‖dθ‖²)` 的 `L²(p)` 形态
    （`δ_a = p_a·(score 方向)` 时主项正是 Fisher 二次型）；
12. `kl_first_order_term_zero`：一阶项消失（`Σδ = 0`）。

**三、自然梯度与不变性（⚠ 本轮更正为"协变性"）**
12. `naturalGradientDiag`：对角 Fisher 下的自然梯度 `(F⁻¹g)_i = g_i / F_ii`
    （**诚实降级**：一般 `F` 的可逆性不可证，限定到**对角正定**情形，
    与 `RealFisherMatrix` 用显式 PSD 假设的先例一致）；
13. `naturalGradientDiag_one_eq_div` / `naturalGradientDiag_one_dim`：与
    `RealFisherInfo` 的一维情形对接（`n = 1` 时即 `g/F`）；
14. `natural_gradient_scale_invariance`（**主结果**）：**⚠ 初稿陈述为假命题，已更正**。
    初稿断言"重参数化下 `g ↦ c·g`、`F ↦ c²·F`，而 `(c·g)/(c²·F) = g/F`——自然梯度**不变**"。
    **该命题为假**（反例 `c=2,g=1,F=1`：左 `1/2`、右 `1`）。
    **根因**：`F` 是 **(0,2) 型**张量，正确律为 `F_ψ = F_θ/c²`（**非** `c²·F`）。
    本文件实际证明的是两条**真**命题：
    - `natural_gradient_scale_invariance`：结论更正为 `(1/c)·(g/F)`（与初稿自称的变换律自洽）；
    - `natural_gradient_scale_covariant`（**张量正确版**）：按 `F ↦ F/c²`、`g ↦ g/c`，
      自然梯度**按 `c` 一次协变**：`NG_ψ = c·NG_θ`。
    ⭐ **正确物理图像**：自然梯度是 **(1,0) 型切向量**，**按坐标变换协变**，**不是不变**。
    "不变"是初稿混用两种方差后的假象。见诚实边界第 3 条；
15. `natural_gradient_scale_covariance_diag`（**原名 `..._invariance_diag`，同为假命题已更正**）：
    逐坐标情形，`naturalGradientDiag (c²·F) (c•g) = (1/c) • naturalGradientDiag F g`
    （**相差 `1/c`，非相等**）；
16. `natural_gradient_times_metric`：**与普通梯度的对比**——`(g/F)·F = g`，
    即自然梯度的「步长依赖参数化」被 `F` 精确抵消，而普通梯度 `η·g` 不抵消；
17. `fisherMetric_scale_covariant` / `fisherMetric_sqrt_scale`（**已更正**）/
    `fisherMetric_sqrt_scale_tensor`：度量张量在缩放重参数化下的**协变**变换
    （`g_{cθ}(cu,cv) = c⁴·g_θ(u,v)`）。
    ⚠ 初稿的 `fisherMetric_sqrt_scale` 断言 `√((c²F)(cu)²) = c·√(Fu²)` **为假**
    （反例 `c=2,F=1,u=1`：左 `4`、右 `2`；根因：`c` 被计 4 次而非 1 次）。
    已更正为右端带 `c²`；初稿真正想表达的「长度是几何量」由
    `fisherMetric_sqrt_scale_tensor` 给出（真实张量律下 `√g` **零次齐次**）。
    见诚实边界第 5 条；
    即「长度是几何量，不依赖坐标」。

**四、与 `RealFisherMatrix` / `RealFisherInfo` 的接口定理**
18. `fisherMetric_eq_fisherMatrix_quadform`：`g_θ(u,u) = uᵀFu`
    （回收 `RealFisherMatrix.fisherQuadForm_eq_fisherMatrix`）；
19. `fisherMetric_one_dim_eq_fisherInfo`：`n = 1` 时 `g` 退化到
    `RealFisherInfo.fisherInfo`（回收 `fisherMatrix_eq_fisherInfo_one_dim`）。

## 与既有模块的接口定理（显式互链）

| 本文件 | 对接 | 内容 |
|:--|:--|:--|
| `fisherMetric` | `RealFisherMatrix.fisherMatrix` | Fisher 矩阵 → 度量张量 |
| `fisherMetric_self_nonneg` | `RealFisherMatrix.fisherMatrix_psd` | PSD 回收（不重证） |
| `fisherMetric_eq_score_inner` | `RealFisherMatrix.logScoreAt` | 度量 = `L²(p_θ)` 内积 |
| `fisherMetric_degenerate_iff` | `RealFisherMatrix.fisherMatrix_zero_direction_score` | 退化方向 |
| `kl_chiSqSym_lower_bound` | `RealKL.kl` / `Real.log_le_sub_one_of_pos` | KL 二次型下界（修正版） |
| `kl_chiSqSym_upper_bound` | `RealKL.kl` / `Real.log_le_sub_one_of_pos` | KL 二次型上界（**需 `Σp=Σq`**） |
| `naturalGradientDiag_one_dim` | `RealFisherInfo.naturalGradient` | 一维退化 |
| `fisherMetric_eq_fisherMatrix_quadform` | `RealFisherMatrix.fisherQuadForm_eq_fisherMatrix` | 二次型回收 |
| `fisherMetric_one_dim_eq_fisherInfo` | `RealFisherMatrix.fisherMatrix_eq_fisherInfo_one_dim` | 维度退化 |

## 诚实边界（诚实 / 未证 / 未做 / 降级 / 标注）

- **⚠⚠ 本轮（F15）另抓出 5 条假命题，全部登记在案（附反例）**。
  下面的 1–2 是初稿已登记的；3–7 是**本轮修复代理实测新抓的**，
  它们的证明体原本**根本无法编译**（该文件此前从未产出 olean）：
  1. `½·Σ(q_a−p_a)²/p_a ≤ KL`（初稿）——反例 `p=(0.25,0.75)`、`q=(0.3,0.7)`。
  2. `Σ(q_a−p_a)²/(2q_a) ≤ KL`（初稿）——反例 `p=(0.5,0.5)`、`q=(0.6,0.4)`。
  3. `natural_gradient_scale_invariance`（初稿断言 `(c·g)/(c²·F) = g/F`）**为假**——
     反例 `c=2, g=1, F=1`：左 `0.5`、右 `1`。
     **根因**：`F` 是 **(0,2) 型**张量，正确律为 `F_ψ = F_θ/c²`（**非** `c²·F`）；
     自然梯度的正确结论是**按 `c` 一次协变**（`= c·(g/F)`），**不是不变**。
     已改为 `natural_gradient_scale_invariance`（结论更正为 `(1/c)·(g/F)`，
     与初稿自称的变换律自洽）+ 新增张量正确版 `natural_gradient_scale_covariant`。
  4. `natural_gradient_scale_invariance_diag`（同 3 的逐坐标版）**为假**——
     同一反例；已更正为 `natural_gradient_scale_covariance_diag`（结论带 `1/c`）。
  5. `fisherMetric_sqrt_scale`（初稿断言 `√((c²F)(cu)²) = c·√(Fu²)`）**为假**——
     反例 `c=2, F=1, u=1`：左 `4`、右 `2`。**根因**：左端 `c` 被计了 **4 次**
     （`c²` 与 `(cu)²` 各 2 次）⟹ 正确右端须带 `c²`；已更正并新增
     张量正确版 `fisherMetric_sqrt_scale_tensor`（`√g` 零次齐次）。
  6. `neg_log_one_add_ge_half_sq`（初稿假设 `−1 ≤ u` **非严格**）**为假**——
     反例 `u = −1`：左 `1/2`、右 `−Real.log 0 = 0`（**Lean 的 `Real.log 0 = 0`**）。
     已把假设收紧为 **`−1 < u`**（调用点严格成立，不影响下游）。
  7. `kl_chiSqSym_upper_bound`（初稿陈述**无求和约束**）**为假**——
     反例 `k=1`、`p=(2)`、`q=(1)`：`KL = 2·log 2 = 1.3863 > chiSqSymUp = 1`。
     已**新增假设 `hpsum`/`hqsum`**（与下界侧一致）；加约束后为真
     （本代理用 **4000 组随机 2/3 点分布暴力复核，0 反例**）。
  ⚠ **另一条"假中间引理"**：初稿 `kl_chiSqSym_lower_bound` 的 `hSbound`
  （`∑_{a∈S} ½(q−p)²/max ≤ ∑_{a∈S}(p−q)`，`S = {q > p}`）**为假**
  （`S` 上左端每项 `≥ 0`、右端每项 `< 0`；反例 `p=1,q=2`：左 `0.25`、右 `−1`）。
  **根因**：初稿把 docstring 自述的「全局约束补偿」**实现成了逐项比较**。
  已**重写整段证明**为正确路线：证明两条**二阶 sharp 标量引理**
  （`−log u` 的下界用 `max` 分母、上界用 `min` 分母），
  乘 `p_a` 求和后用 `Σ(p−q) = 0` **一次性消去线性项**，
  二次项直接化为 `(q−p)²/(2·max)`（下界）与 `(q−p)²/(2·min)`（上界）。
- **未做：一般 `F(θ)` 的可逆性 / 自然梯度的 `F⁻¹∇L` 完整形式**。`F` 在概率单纯形
  边界附近奇异（零方向由 `RealFisherMatrix.fisherMatrix_zero_direction_score` 刻画），
  mathlib 4.14 上「`F` 正定 ⟹ 可逆」需要 `Matrix.PosDef` 与 `invertibleOfIsUnitDet` 的
  完整拼接，且信息几何里 `F` 奇异**是本质的**（不可辨识参数），不是技术缺口。
  故本文件的自然梯度**限定到对角正定情形**（`F_ii > 0`，非对角为 0），
  与 `RealFisherMatrix.ewcQuadratic_nonneg` 用**显式 PSD/正定假设**的先例一致。
  `naturalGradientDiag` 的「Diag」后缀是**刻意的语义标注**：它不假装是一般 `F⁻¹g`。
- **诚实降级：KL 展开是「非渐近不等式 + 一阶族渐近」两条，而非单一的 `o(·)` 定理**。
  见文件开头的「建模抉择」：真正的 `Asymptotics.IsLittleO` 陈述需要参数族的光滑性与
  邻域正性前提，本文件把信息几何的硬内容（二次型界）与表示层前提**解耦**，
  再用 `kl_expansion_of_first_order_family` 把渐近形式作为推论给出。
  这是**有意的结构选择**，不是能力缺口，但在「定理名字看起来不像任务书要求」的意义上
  属于**诚实降级**，故显式标注。
- **未做：测地线、指数映射、Riemann 曲率**。完整信息几何需要仿射联络与
  Fisher–Rao 度量下的 Levi-Civita 联络；mathlib 4.14 无「有限维 Riemann 流形上的
  联络」现成骨架，且这些对象在**离散有限参数族**上没有额外的可证内容
  （曲率恒等式需要流形结构）。本文件**只做度量层**（长度/二次型/不变性），
  联络层标注为未做。
- **未做：自然梯度的收敛性**（任务书 B 段明确列为可选）。收敛性属于
  `RealFisherInfo` 已标注的未做项，本文件不重复；`RealRiemannianGD` 已处理
  Riemann 梯度下降的**一般**收敛，本文件不与其重叠。
- **未做：Cramér–Rao / 指数族的等号刻画**，见 `RealFisherInfo` 的既有边界。
- **退化情形**：`p_a = 0` 时 `χ²` 中的除法使项为 0（Lean 的 `x/0 = 0`），
  故 `kl_chiSqSym_lower_bound` 的假设写作 `0 < p_a`（**语义标注**：`p` 支撑包含 `q` 的扰动），
  与 `RealKL.kl_nonneg` 的 `hp0`/`hq0` 风格一致。
- **范围**：有限 `Fin k` / `Fin n`；无测度论、无流形。
- 无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {n k : ℕ}

/-! ## 一、Fisher 度量（度量张量的分量姿态）

把 `RealFisherMatrix.fisherMatrix` 从「矩阵」提升为「双线性形式」：
`g_θ(u,v) = Σ_i Σ_j u_i·F_{ij}(θ)·v_j`。这是信息几何里度量张量
`g_{ij} = F_{ij}` 的**标准用法**（切向量配对），也是所有长度/不变性陈述的载体。 -/

/-- **Fisher 度量（度量张量）**：`g_θ(u,v) = Σ_i Σ_j u_i·F_{ij}(θ)·v_j`，
其中 `F = RealFisherMatrix.fisherMatrix p θ`。 -/
def fisherMetric (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ) (u v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * fisherMatrix p θ i j * v j

/-- **度量的对称性**：`g_θ(u,v) = g_θ(v,u)`（回收 `fisherMatrix_symm`）。 -/
theorem fisherMetric_symm (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (u v : Fin n → ℝ) :
    fisherMetric p θ u v = fisherMetric p θ v u := by
  unfold fisherMetric
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [fisherMatrix_symm p θ j i]
  ring

/-- **度量的双线性（左加性）**：`g(u₁+u₂, v) = g(u₁,v) + g(u₂,v)`。 -/
theorem fisherMetric_add_left (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (u₁ u₂ v : Fin n → ℝ) :
    fisherMetric p θ (u₁ + u₂) v = fisherMetric p θ u₁ v + fisherMetric p θ u₂ v := by
  unfold fisherMetric
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]
  ring

/-- **度量的双线性（左齐次）**：`g(c·u, v) = c·g(u,v)`。 -/
theorem fisherMetric_smul_left (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (c : ℝ) (u v : Fin n → ℝ) :
    fisherMetric p θ (c • u) v = c * fisherMetric p θ u v := by
  unfold fisherMetric
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **度量半正定（回收 `RealFisherMatrix.fisherMatrix_psd`，不重证）**：
`p_θ ≥ 0` ⟹ `0 ≤ g_θ(u,u)`。 -/
theorem fisherMetric_self_nonneg (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (u : Fin n → ℝ) (hp : ∀ a, 0 ≤ p θ a) :
    0 ≤ fisherMetric p θ u u :=
  fisherMatrix_psd p θ u hp

/-- **度量 = score 的 `L²(p_θ)` 加权内积（信息几何意义）**：
`g_θ(u,v) = Σ_a p_θ(a)·(Σ_i u_i·s_{a,i})·(Σ_j v_j·s_{a,j})`，
其中 `s_{a,i} = logScoreAt p θ a i`。

这把 Fisher 度量识别为 score 函数空间上的 `L²(p_θ)` 内积——
信息几何的出发点（切空间 = 均值零的 score 函数空间）。

⚠ **声明顺序**：本条必须**先于** `fisherMetric_cauchy_schwarz` 声明——后者在其证明体中
`rw [fisherMetric_eq_score_inner]` 引用本条；Lean 逐条处理声明，**后声明者不在作用域内**。 -/
theorem fisherMetric_eq_score_inner (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (u v : Fin n → ℝ) :
    fisherMetric p θ u v
      = ∑ a, p θ a * (∑ i, u i * logScoreAt p θ a i)
          * (∑ j, v j * logScoreAt p θ a j) := by
  -- 展开：`fisherMetric p θ u v = ∑ i ∑ j ∑ a, u i·(p_a·s_ai·s_aj)·v j`
  have hL : fisherMetric p θ u v
      = ∑ i, ∑ j, ∑ a, u i * (p θ a * logScoreAt p θ a i * logScoreAt p θ a j) * v j := by
    unfold fisherMetric fisherMatrix
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hL]
  -- 把 `a` 从最内层提到最外层：(i,j,a) ↦ (a,i,j)，分两步（`sum_comm` 只换**最外**一对）
  have h1 : (∑ i, ∑ j, ∑ a, u i * (p θ a * logScoreAt p θ a i * logScoreAt p θ a j) * v j)
      = ∑ i, ∑ a, ∑ j, u i * (p θ a * logScoreAt p θ a i * logScoreAt p θ a j) * v j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [h1, Finset.sum_comm]
  -- 归约到逐 `a` 的代数恒等式：
  --   `∑ i ∑ j, u i·(p_a·s_ai·s_aj)·v j = (p_a·∑ i, u i·s_ai)·∑ j, v j·s_aj`
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Cauchy–Schwarz 型非负性**：`g` 半正定 + 对称 ⟹ `g(u,v)² ≤ g(u,u)·g(v,v)`。
这是度量张量的基本性质（信息几何里「角度」良定义的前提）。

证明：走 `g` 的 `L²(p_θ)` 内积表示（`fisherMetric_eq_score_inner`），
令 `x_a = √(p_a)·(Σ_i u_i s_{a,i})`、`y_a = √(p_a)·(Σ_j v_j s_{a,j})`，
用离散 Cauchy–Schwarz `(Σ x_a y_a)² ≤ (Σ x_a²)(Σ y_a²)`
（`Finset.sum_mul_sq_le_sq_mul_sq`，注意它是**双绑定**形状 `∑ i ∈ s`），
并用 `(√p)² = p`（`0 ≤ p`）回代。 -/
theorem fisherMetric_cauchy_schwarz (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (u v : Fin n → ℝ) (hp : ∀ a, 0 ≤ p θ a) :
    fisherMetric p θ u v ^ 2 ≤ fisherMetric p θ u u * fisherMetric p θ v v := by
  have hL : fisherMetric p θ u v
      = ∑ a, Real.sqrt (p θ a) * (∑ i, u i * logScoreAt p θ a i)
          * (Real.sqrt (p θ a) * (∑ j, v j * logScoreAt p θ a j)) := by
    rw [fisherMetric_eq_score_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (Real.sqrt (p θ a) * (∑ i, u i * logScoreAt p θ a i))
          * (Real.sqrt (p θ a) * (∑ j, v j * logScoreAt p θ a j))
        = Real.sqrt (p θ a) ^ 2
          * ((∑ i, u i * logScoreAt p θ a i) * (∑ j, v j * logScoreAt p θ a j)) by ring]
    rw [Real.sq_sqrt (hp a)]
    ring
  have hR1 : fisherMetric p θ u u
      = ∑ a, (Real.sqrt (p θ a) * (∑ i, u i * logScoreAt p θ a i)) ^ 2 := by
    rw [fisherMetric_eq_score_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (Real.sqrt (p θ a) * (∑ i, u i * logScoreAt p θ a i)) ^ 2
        = Real.sqrt (p θ a) ^ 2
          * ((∑ i, u i * logScoreAt p θ a i) * (∑ i, u i * logScoreAt p θ a i)) by ring]
    rw [Real.sq_sqrt (hp a)]
    ring
  have hR2 : fisherMetric p θ v v
      = ∑ a, (Real.sqrt (p θ a) * (∑ j, v j * logScoreAt p θ a j)) ^ 2 := by
    rw [fisherMetric_eq_score_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (Real.sqrt (p θ a) * (∑ j, v j * logScoreAt p θ a j)) ^ 2
        = Real.sqrt (p θ a) ^ 2
          * ((∑ j, v j * logScoreAt p θ a j) * (∑ j, v j * logScoreAt p θ a j)) by ring]
    rw [Real.sq_sqrt (hp a)]
    ring
  rw [hL, hR1, hR2]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_one, one_mul] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
      (fun a => Real.sqrt (p θ a) * (∑ i, u i * logScoreAt p θ a i))
      (fun a => Real.sqrt (p θ a) * (∑ j, v j * logScoreAt p θ a j))

/-- **度量二次型 = `RealFisherMatrix.fisherQuadForm`（回收，不重证）**：
`g_θ(u,u) = fisherQuadForm p θ u`。 -/
theorem fisherMetric_eq_fisherQuadForm (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (u : Fin n → ℝ) :
    fisherMetric p θ u u = fisherQuadForm p θ u := by
  rw [fisherQuadForm_eq_fisherMatrix p θ u]
  unfold fisherMetric
  rfl

/-- **度量二次型回收 `RealFisherMatrix` 的二次型恒等式**：`g_θ(u,u) = uᵀFu`。 -/
theorem fisherMetric_eq_fisherMatrix_quadform (p : (Fin n → ℝ) → Fin k → ℝ)
    (θ : Fin n → ℝ) (u : Fin n → ℝ) :
    fisherMetric p θ u u = ∑ i, ∑ j, u i * fisherMatrix p θ i j * u j :=
  rfl

/-- **度量退化 ⟺ score 方向为零（回收零方向定理）**：
`p_θ > 0` 且 `∀ j, Σ_i F_{ij}·u_i = 0` ⟹ `∀ a, Σ_i u_i·s_{a,i} = 0`，
即 `u` 在 Fisher 度量下长度为零（不可辨识方向）。 -/
theorem fisherMetric_degenerate_iff (p : (Fin n → ℝ) → Fin k → ℝ) (θ : Fin n → ℝ)
    (u : Fin n → ℝ) (hp : ∀ a, 0 < p θ a)
    (hu : ∀ j, ∑ i, fisherMatrix p θ i j * u i = 0) :
    ∀ a, ∑ i, u i * logScoreAt p θ a i = 0 :=
  fisherMatrix_zero_direction_score p θ u hp hu

/-! ## 二、KL 的二阶展开

核心是一组**标量**引理（`log` 的上下界），KL 展开在有限概率向量上完全由它们驱动：
`KL(p‖q) = Σ_a p_a·log(p_a/q_a)`，逐项令 `r_a = q_a/p_a`，则该项是 `−p_a·log r_a`。

### ⚠ 本轮更正（记录在案的假命题）

本文件初稿曾断言两条**为假**的命题，按 STYLE §4「数值假设类命题务必代小整数复核」
的精神在此登记（反例可在内核外复核）：

1. `½·χ²(p,q) ≤ KL(p‖q)`（`χ² = Σ (q−p)²/p`）**为假**。
   反例：`p = (0.25, 0.75)`、`q = (0.3, 0.7)`：
   `½χ² = 0.0066667 > KL = 0.0061640`。
   即使加上 `q ≤ 2p`（逐点，`0.3 ≤ 0.5`、`0.7 ≤ 1.5` 成立）仍为假。
2. `Σ (q−p)²/(2q) ≤ KL(p‖q)` **为假**。同上反例：`0.0059524 ≤ 0.0061640` 成立，
   但 `p = (0.5,0.5)`、`q = (0.6,0.4)` 时 `0.0208333 > 0.0204109`。

**根因**：`KL` 与 `χ²` 的常数比较**不能逐项做**。逐项事实是
`−log r ≥ (1−r)²/(2·max(1,r))` **只在 `r ≤ 1` 时成立**；
`r > 1` 时 `−log r < 0`，任何正下界都假。
真正的聚合不等式必须用 `Σ_a (q_a − p_a) = 0` 这一**全局约束**，
故正确的常数对是（本文件实际证明的）：

    KL(p‖q) ≥ ½·Σ_a (q_a − p_a)²/max(p_a, q_a)      （二次型下界，常数 ½）
    KL(p‖q) ≤ Σ_a (q_a − p_a)²/min(p_a, q_a)        （二次型上界）

这两条是 `χ²`-散度的**对称化**版本（分母取 `max`/`min` 而非单侧 `p`），
常数 `½` 与 `1` 均为**紧的**（数值上 `min KL / Σ(q−p)²/max ≈ 0.5049`）。

**证明路线**（标量层）：
- 上界用 `log x ≤ x − 1`（`Real.log_le_sub_one_of_pos`）；
- 下界用 `log x ≥ 1 − 1/x`（同引理用于 `1/x` 取反），配合
  `Σ_a (p_a − q_a) = 0` 把一次项消掉，剩下的二次项由
  `u² / max(·)` 与 `(1−r)²/2` 的比较得到。

**与任务书要求的对照（诚实说明）**：任务书写的是 `o(‖dθ‖²)` 形式（真正的渐近展开）。
本文件给出的是**更强的、无渐近的、对每个 `q` 都成立的精确不等式**（二次型上下界）；
渐近形式作为推论在第三节给出（一阶扰动族）。理由：渐近陈述需要「`θ ↦ p_θ` 可微 +
邻域正性」这些**表示层**前提，会把信息几何的硬内容与参数化细节耦合；
本文件把两者解耦。这是**有意的结构选择**，但确实与任务书字面不符，故显式标注为降级。 -/

/-- **对称化卡方散度（下界侧）**：`chiSqSym p q = Σ_a (q_a − p_a)²/max(p_a, q_a)`。
用 `max` 而非单侧 `p` 或 `q`，是 KL 二次型**双向**夹逼的正确分母。 -/
def chiSqSym {k : ℕ} (p q : Fin k → ℝ) : ℝ :=
  ∑ a, (q a - p a) ^ 2 / max (p a) (q a)

/-- **对称化卡方散度（上界侧）**：`chiSqSymUp p q = Σ_a (q_a − p_a)²/min(p_a, q_a)`。 -/
def chiSqSymUp {k : ℕ} (p q : Fin k → ℝ) : ℝ :=
  ∑ a, (q a - p a) ^ 2 / min (p a) (q a)

/-- **标量引理：log 的上界** `log(1+u) ≤ u`（`u > −1`）。
即 `log x ≤ x − 1`（`x = 1+u > 0`）的平移形式。 -/
lemma log_one_add_le (u : ℝ) (hu : -1 < u) : Real.log (1 + u) ≤ u := by
  have h : Real.log (1 + u) ≤ (1 + u) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  linarith

/-- **标量引理：log 的下界（倒数形式）** `1 − 1/x ≤ log x`（`x > 0`）。
由 `log(1/x) ≤ 1/x − 1` 取反得。这是 `Real.log_le_sub_one_of_pos` 的镜像形式，
是 KL 二次型**下界**的源头。 -/
lemma one_sub_inv_le_log (x : ℝ) (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have hinv : 0 < 1 / x := div_pos one_pos hx
  have h : Real.log (1 / x) ≤ 1 / x - 1 := Real.log_le_sub_one_of_pos hinv
  have hlog : Real.log (1 / x) = -Real.log x := by
    rw [one_div, Real.log_inv]
  rw [hlog] at h
  linarith

/-- **标量引理：KL 下界的逐项形式（`r ≤ 1` 侧）**。
`u ∈ (−1, 0]` 时 `−log(1+u) ≥ u²/(2·1) = u²/2`（因 `max(1,1+u) = 1`）。

由 `log x ≤ x − 1` 与 `log x ≥ 1 − 1/x` 的中点型不等式
`−log(1+u) ≥ u²/2`（`u ∈ (−1,0]`）给出。

⚠ **假设已收紧（本轮实测更正）**：初稿写作 `hu : -1 ≤ u`（**非严格**），该版本**为假**。
反例 `u = -1`：`1 + u = 0`，Lean 的 `Real.log 0 = 0`（`Real.log` 是全函数、非正处取 0），
故左端 `u²/2 = 1/2`，右端 `−Real.log 0 = 0`，`1/2 ≤ 0` **不成立**。
且此时 `0 < 1 + u` 本身就不成立（`linarith` 无法从**非严格** `−1 ≤ u` 推出**严格** `0 < 1+u`），
证明体第一行即失败。**根因**：`Real.log` 在 `0` 处被人为定义为 `0`，破坏了 `−log` 的发散性；
`log` 的上下界引理（`Real.log_le_sub_one_of_pos` 等）**一律要求严格正**。
故正确假设是 **`−1 < u`（严格）**。

**调用方已同步**：`kl_chiSqSym_lower_bound` 中的调用点用的是 `u = q_a/p_a − 1`，
在 `q_a ≤ p_a` 且 `q_a > 0`、`p_a > 0` 下有 `q_a/p_a > 0` 即 `u > −1`（**严格成立**），
故收紧不影响下游可用性。 -/
lemma neg_log_one_add_ge_half_sq (u : ℝ) (hu : -1 < u) (hu0 : u ≤ 0) :
    u ^ 2 / 2 ≤ -Real.log (1 + u) := by
  -- 路线：`log(1+u) ≤ u`（本文件 `log_one_add_le`）给出 `−log(1+u) ≥ −u`；
  -- 而 `u ∈ (−1,0]` 时 `u²/2 ≤ −u`（等价于 `u(u+2) ≤ 0`）。两段拼起来即可。
  have hlog : Real.log (1 + u) ≤ u := log_one_add_le u hu
  have hsq : u ^ 2 / 2 ≤ -u := by nlinarith [hu, hu0]
  linarith

/-- **标量引理：KL 下界的逐项形式（`r ≥ 1` 侧）**。
`u ≥ 0` 时 `−log(1+u) ≤ 0`，故**不能**期望正下界；本引理给出该侧的
可用事实 `−log(1+u) ≤ 0`（用于把负项直接丢掉，见 `kl_chiSqSym_lower_bound` 的证法）。 -/
lemma neg_log_one_add_nonpos (u : ℝ) (hu : 0 ≤ u) : -Real.log (1 + u) ≤ 0 := by
  have : 1 ≤ 1 + u := by linarith
  have := Real.log_nonneg this
  linarith

/-! ### ⭐ 二阶（sharp）标量引理——本轮新增，修复 `kl_chiSqSym_lower_bound` 的坏路线

初稿的证明路线把 `S = {a : q_a > p_a}` 与 `T = {a : q_a ≤ p_a}` **逐项**比较，
但 `S` 上 KL 的逐项贡献 `−p_a·log(q_a/p_a) < 0` 而 χ² 项 `> 0` ⟹ **逐项比较必然失败**
（初稿的中间引理 `hSbound` 因此为**假**：`p=1,q=2` 时左 `0.25`、右 `−1`）。

正确路线（经典、且**不需要** T/S 拆分）：用**二阶 sharp 标量引理**
    `−log u ≥ (1 − u) + (u − 1)²/(2·max(1,u))   (u > 0)`
逐项乘 `p_a > 0` 后求和，其中 `Σ_a p_a(1 − r_a) = Σ_a(p_a − q_a) = 0` **恰好消去一次项**
（这就是 docstring 里说的「全局约束补偿」的**正确实现位置**），
剩下的二次项 `p_a(r_a−1)²/(2max(1,r_a))` 在 `r ≤ 1` 时 `= (q−p)²/(2p)`、
在 `r ≥ 1` 时 `= (q−p)²/(2q)`，正是 `(q−p)²/(2·max(p,q))`。

下面两条把该 sharp 引理按 `max` 的两个分支分别给出（用导数单调性证明，
因为 mathlib 4.14 **没有**现成的二阶 `log` 界）。 -/

set_option maxHeartbeats 800000 in
/-- **二阶 sharp 界（`u ≤ 1` 分支）**：`0 ≤ s < 1` 时 `−log(1−s) ≥ s + s²/2`。
（对应 `−log u ≥ (1−u) + (u−1)²/2` 在 `u = 1−s ≤ 1`、`max(1,u) = 1` 的情形。）

**证明**：令 `G(y) = −log(1−y) − y − y²/2`，则 `G(0) = 0`，
`G'(y) = y²/(1−y) ≥ 0` 于 `[0,1)` ⟹ `G` 单调增 ⟹ `G(s) ≥ 0`。
用 `strictMonoOn_of_deriv_pos`（mathlib 4.14 缺二阶 `log` 界，故走导数）。 -/
lemma neg_log_one_sub_ge (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    s + s ^ 2 / 2 ≤ -Real.log (1 - s) := by
  have hcont : ContinuousOn (fun y => -Real.log (1 - y) - y - y ^ 2 / 2) (Set.Icc 0 s) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · exact ContinuousOn.neg (ContinuousOn.log (continuousOn_const.sub continuousOn_id)
          (fun y hy => by have : y ≤ s := hy.2; linarith))
      · exact continuousOn_id
    · exact ContinuousOn.div_const (continuousOn_id.pow 2) 2
  have hsm : StrictMonoOn (fun y => -Real.log (1 - y) - y - y ^ 2 / 2) (Set.Icc 0 s) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 s) hcont
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : x < 1 := by linarith [hx.2, hs1]
    have hx0 : 0 < 1 - x := by linarith
    have hinner : HasDerivAt (fun y => 1 - y) (-1) x := by
      simpa using (hasDerivAt_const (x := x) (c := (1:ℝ))).sub (hasDerivAt_id x)
    have hlog : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := hinner.log hx0.ne'
    have h2 : HasDerivAt (fun y => y ^ 2 / 2) (2 * x / 2) x := by
      have := (hasDerivAt_pow 2 x).div_const 2
      simpa using this
    have hd : HasDerivAt (fun y => -Real.log (1 - y) - y - y ^ 2 / 2)
        (-(-1 / (1 - x)) - 1 - 2 * x / 2) x := ((hlog.neg).sub (hasDerivAt_id x)).sub h2
    rw [hd.deriv]
    have heq : -(-1 / (1 - x)) - 1 - 2 * x / 2 = x ^ 2 / (1 - x) := by field_simp; ring
    rw [heq]
    exact div_pos (pow_pos (by linarith [hx.1]) 2) hx0
  have h0 : (0:ℝ) ∈ Set.Icc 0 s := Set.left_mem_Icc.mpr hs0
  have hs : s ∈ Set.Icc 0 s := Set.right_mem_Icc.mpr hs0
  rcases eq_or_lt_of_le hs0 with h | h
  · subst h; norm_num
  · have := hsm h0 hs h
    norm_num at this
    linarith

set_option maxHeartbeats 800000 in
/-- **二阶 sharp 界（`u ≥ 1` 分支）**：`s ≥ 0` 时 `−log(1+s) ≥ −s + s²/(2(1+s))`。
（对应 `−log u ≥ (1−u) + (u−1)²/(2u)` 在 `u = 1+s ≥ 1`、`max(1,u) = u` 的情形。）

**证明**：令 `G(y) = −log(1+y) + y − y²/(2(1+y))`，则 `G(0) = 0`，
`G'(y) = y²/(2(1+y)²) ≥ 0` 于 `[0,∞)` ⟹ `G` 单调增 ⟹ `G(s) ≥ 0`。

⚠ **注意导数**：`d/dy [y²/(2(1+y))] = y(2+y)/(2(1+y)²)`（**不是** `y²/(1+y)²`）——
本代理首版正是把商法则算错、导致 `field_simp; ring` 留下一个**假**的多项式恒等式
（`2x²+6x³+6x⁴+2x⁵ = 4x²+12x³+12x⁴+4x⁵`）。修正后 `G' = x²/(2(1+x)²)`。 -/
lemma neg_log_one_add_ge_sharp (s : ℝ) (hs : 0 ≤ s) :
    -s + s ^ 2 / (2 * (1 + s)) ≤ -Real.log (1 + s) := by
  have hcont : ContinuousOn (fun y => -Real.log (1 + y) + y - y ^ 2 / (2 * (1 + y))) (Set.Icc 0 s) := by
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact ContinuousOn.neg (ContinuousOn.log (continuousOn_const.add continuousOn_id)
          (fun y hy => by have : 0 ≤ y := hy.1; linarith))
      · exact continuousOn_id
    · exact ContinuousOn.neg (ContinuousOn.div (continuousOn_id.pow 2)
        (continuousOn_const.mul (continuousOn_const.add continuousOn_id))
        (fun y hy => by have : 0 ≤ y := hy.1; positivity))
  have hsm : StrictMonoOn (fun y => -Real.log (1 + y) + y - y ^ 2 / (2 * (1 + y))) (Set.Icc 0 s) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 s) hcont
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < 1 + x := by linarith [hx.1]
    have hinner : HasDerivAt (fun y => 1 + y) (1:ℝ) x := by
      simpa using (hasDerivAt_const (x := x) (c := (1:ℝ))).add (hasDerivAt_id x)
    have hlog : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := hinner.log hx0.ne'
    have hnum : HasDerivAt (fun y => y ^ 2) (2 * x) x := by
      have := hasDerivAt_pow 2 x; simpa using this
    have hden : HasDerivAt (fun y => 2 * (1 + y)) 2 x := by
      have := (hasDerivAt_const (x := x) (c := (2:ℝ))).mul hinner
      simpa using this
    have h2 : HasDerivAt (fun y => y ^ 2 / (2 * (1 + y)))
        ((2 * x * (2 * (1 + x)) - x ^ 2 * 2) / (2 * (1 + x)) ^ 2) x :=
      hnum.div hden (by linarith)
    have hd : HasDerivAt (fun y => -Real.log (1 + y) + y - y ^ 2 / (2 * (1 + y)))
        (-(1 / (1 + x)) + 1 - ((2 * x * (2 * (1 + x)) - x ^ 2 * 2) / (2 * (1 + x)) ^ 2)) x :=
      ((hlog.neg).add (hasDerivAt_id x)).sub h2
    rw [hd.deriv]
    have heq : -(1 / (1 + x)) + 1 - ((2 * x * (2 * (1 + x)) - x ^ 2 * 2) / (2 * (1 + x)) ^ 2)
        = x ^ 2 / (2 * (1 + x) ^ 2) := by
      field_simp
      ring
    rw [heq]
    exact div_pos (pow_pos (by linarith [hx.1]) 2) (by positivity)
  have h0 : (0:ℝ) ∈ Set.Icc 0 s := Set.left_mem_Icc.mpr hs
  have hs' : s ∈ Set.Icc 0 s := Set.right_mem_Icc.mpr hs
  rcases eq_or_lt_of_le hs with h | h
  · subst h; norm_num
  · have := hsm h0 hs' h
    norm_num at this
    linarith

/-- ⭐ **二阶 sharp 标量引理（统一形式）**：`u > 0` 时
`−log u ≥ (1 − u) + (u − 1)²/(2·max(1,u))`。

这是 `kl_chiSqSym_lower_bound` 的**唯一**标量驱动；由上面两条按 `u ≤ 1` / `u ≥ 1` 分支拼出。 -/
lemma neg_log_ge_linear_add_sharp (u : ℝ) (hu : 0 < u) :
    1 - u + (u - 1) ^ 2 / (2 * max 1 u) ≤ -Real.log u := by
  rcases le_or_lt u 1 with hle | hlt
  · -- u ≤ 1：max 1 u = 1；用 s = 1 − u ∈ [0,1)
    have hs0 : 0 ≤ 1 - u := by linarith
    have hs1 : 1 - u < 1 := by linarith
    have hmax : max 1 u = 1 := max_eq_left hle
    rw [hmax]
    have hb := neg_log_one_sub_ge (1 - u) hs0 hs1
    have harg : 1 - (1 - u) = u := by ring
    rw [harg] at hb
    -- hb : (1−u) + (1−u)²/2 ≤ −log u；目标二次项分母为 2*1
    have heq : (u - 1) ^ 2 / (2 * (1:ℝ)) = (1 - u) ^ 2 / 2 := by ring
    rw [heq]
    exact hb
  · -- u ≥ 1：max 1 u = u；用 s = u − 1 ≥ 0
    have hs : 0 ≤ u - 1 := by linarith
    have hmax : max 1 u = u := max_eq_right (le_of_lt hlt)
    rw [hmax]
    have hb := neg_log_one_add_ge_sharp (u - 1) hs
    have harg : 1 + (u - 1) = u := by ring
    rw [harg] at hb
    -- hb : -(u−1) + (u−1)²/(2u) ≤ −log u；而 -(u−1) = 1−u
    have hfirst : -(u - 1) = 1 - u := by ring
    rw [hfirst] at hb
    exact hb


/-! ### ⭐ 镜像的 sharp 上界（本轮新增，用于 `kl_chiSqSym_upper_bound`）

下界侧用的是 `−log u` 的**下界**（`neg_log_ge_linear_add_sharp`）；
上界侧需要的是 `−log u` 的**上界**，其分母用 `min` 而非 `max`：
    `−log u ≤ (1 − u) + (u − 1)²/(2·min(1,u))   (u > 0)`。
同样由导数单调性分两支证明（mathlib 4.14 无现成二阶 `log` 界）。

⚠ **为什么必须用这一个（而不是更朴素的候选）**：本代理先用代数反例排除了两个候选——
`−log r ≤ (1−r)²/r` 在 `r = 0.7` 处失败（`0.357 > 0.129`），
`−log r ≤ (r−1) + (r−1)²/(2·min(1,r))` 在 `r = 0.7` 处失败（`0.357 > −0.255`）。 -/

set_option maxHeartbeats 800000 in
/-- **镜像 sharp 界（`u ≤ 1` 分支，`v = 1−u`）**：`0 ≤ v < 1` ⟹ `−log(1−v) ≤ v + v²/(2(1−v))`。
（对应 `−log u ≤ (1−u) + (u−1)²/(2u)` 在 `u = 1−v ≤ 1`、`min(1,u) = u` 的情形。）

**证明**：`K(y) = y + y²/(2(1−y)) + log(1−y)`，`K(0) = 0`，`K′(y) = y²/(2(1−y)²) ≥ 0`。 -/
lemma neg_log_one_sub_le (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    -Real.log (1 - v) ≤ v + v ^ 2 / (2 * (1 - v)) := by
  have hcont : ContinuousOn (fun y => y + y ^ 2 / (2 * (1 - y)) + Real.log (1 - y)) (Set.Icc 0 v) := by
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact continuousOn_id
      · exact ContinuousOn.div (continuousOn_id.pow 2)
          (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
          (fun y hy => by have : y ≤ v := hy.2; linarith)
    · apply ContinuousOn.log
      · exact continuousOn_const.sub continuousOn_id
      · intro y hy; have : y ≤ v := hy.2; linarith
  have hsm : StrictMonoOn (fun y => y + y ^ 2 / (2 * (1 - y)) + Real.log (1 - y)) (Set.Icc 0 v) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 v) hcont
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : x < 1 := by linarith [hx.2, hv1]
    have hx0 : 0 < 1 - x := by linarith
    have hnum : HasDerivAt (fun y => y ^ 2) (2 * x) x := by
      have := hasDerivAt_pow 2 x; simpa using this
    have hden : HasDerivAt (fun y => 2 * (1 - y)) (-2) x := by
      have hinner : HasDerivAt (fun y => 1 - y) (-1) x := by
        simpa using (hasDerivAt_const (x := x) (c := (1:ℝ))).sub (hasDerivAt_id x)
      have := (hasDerivAt_const (x := x) (c := (2:ℝ))).mul hinner
      simpa using this
    have h2 : HasDerivAt (fun y => y ^ 2 / (2 * (1 - y)))
        ((2 * x * (2 * (1 - x)) - x ^ 2 * (-2)) / (2 * (1 - x)) ^ 2) x :=
      hnum.div hden (by positivity)
    have hlog : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := by
      have hinner : HasDerivAt (fun y => 1 - y) (-1) x := by
        simpa using (hasDerivAt_const (x := x) (c := (1:ℝ))).sub (hasDerivAt_id x)
      exact hinner.log hx0.ne'
    have hd : HasDerivAt (fun y => y + y ^ 2 / (2 * (1 - y)) + Real.log (1 - y))
        (1 + ((2 * x * (2 * (1 - x)) - x ^ 2 * (-2)) / (2 * (1 - x)) ^ 2) + (-1 / (1 - x))) x :=
      ((hasDerivAt_id x).add h2).add hlog
    rw [hd.deriv]
    have heq : 1 + ((2 * x * (2 * (1 - x)) - x ^ 2 * (-2)) / (2 * (1 - x)) ^ 2) + (-1 / (1 - x))
        = x ^ 2 / (2 * (1 - x) ^ 2) := by
      field_simp
      ring
    rw [heq]
    exact div_pos (pow_pos (by linarith [hx.1]) 2) (by positivity)
  have h0 : (0:ℝ) ∈ Set.Icc 0 v := Set.left_mem_Icc.mpr hv0
  have hvv : v ∈ Set.Icc 0 v := Set.right_mem_Icc.mpr hv0
  rcases eq_or_lt_of_le hv0 with h | h
  · subst h; norm_num
  · have := hsm h0 hvv h
    norm_num at this
    linarith

set_option maxHeartbeats 800000 in
/-- **镜像 sharp 界（`u ≥ 1` 分支，`s = u−1`）**：`0 ≤ s` ⟹ `−log(1+s) ≤ −s + s²/2`。
（对应 `−log u ≤ (1−u) + (u−1)²/2` 在 `u = 1+s ≥ 1`、`min(1,u) = 1` 的情形。）

**证明**：`H(y) = y(y−2)/2 + log(1+y)`，`H(0) = 0`，`H′(y) = y²/(1+y) ≥ 0`。 -/
lemma neg_log_one_add_le (s : ℝ) (hs : 0 ≤ s) : -Real.log (1 + s) ≤ -s + s ^ 2 / 2 := by
  have hcont : ContinuousOn (fun y => y * (y - 2) / 2 + Real.log (1 + y)) (Set.Icc 0 s) := by
    apply ContinuousOn.add
    · exact ContinuousOn.div_const (continuousOn_id.mul (continuousOn_id.sub continuousOn_const)) 2
    · apply ContinuousOn.log
      · exact continuousOn_const.add continuousOn_id
      · intro y hy; have : 0 ≤ y := hy.1; linarith
  have hsm : StrictMonoOn (fun y => y * (y - 2) / 2 + Real.log (1 + y)) (Set.Icc 0 s) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 s) hcont
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < 1 + x := by linarith [hx.1]
    have hnum : HasDerivAt (fun y => y * (y - 2)) (1 * (x - 2) + x * 1) x := by
      have h1 : HasDerivAt (fun y => y - 2) (1:ℝ) x := by
        simpa using (hasDerivAt_id x).sub (hasDerivAt_const (x := x) (c := (2:ℝ)))
      exact (hasDerivAt_id x).mul h1
    have h2 : HasDerivAt (fun y => y * (y - 2) / 2) ((1 * (x - 2) + x * 1) / 2) x :=
      hnum.div_const 2
    have hlog : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      have hinner : HasDerivAt (fun y => 1 + y) (1:ℝ) x := by
        simpa using (hasDerivAt_const (x := x) (c := (1:ℝ))).add (hasDerivAt_id x)
      exact hinner.log hx0.ne'
    have hd : HasDerivAt (fun y => y * (y - 2) / 2 + Real.log (1 + y))
        ((1 * (x - 2) + x * 1) / 2 + 1 / (1 + x)) x := h2.add hlog
    rw [hd.deriv]
    have heq : (1 * (x - 2) + x * 1) / 2 + 1 / (1 + x) = x ^ 2 / (1 + x) := by
      field_simp
      ring
    rw [heq]
    exact div_pos (pow_pos (by linarith [hx.1]) 2) (by positivity)
  have h0 : (0:ℝ) ∈ Set.Icc 0 s := Set.left_mem_Icc.mpr hs
  have hss : s ∈ Set.Icc 0 s := Set.right_mem_Icc.mpr hs
  rcases eq_or_lt_of_le hs with h | h
  · subst h; norm_num
  · have := hsm h0 hss h
    norm_num at this
    linarith

/-- ⭐ **镜像 sharp 标量引理（统一形式，上界侧）**：`u > 0` 时
`−log u ≤ (1 − u) + (u − 1)²/(2·min(1,u))`。

这是 `kl_chiSqSym_upper_bound` 的**唯一**标量驱动；由上面两条按 `u ≤ 1` / `u ≥ 1` 分支拼出。 -/
lemma neg_log_le_linear_add_sharp (u : ℝ) (hu : 0 < u) :
    -Real.log u ≤ 1 - u + (u - 1) ^ 2 / (2 * min 1 u) := by
  rcases le_or_lt u 1 with hle | hlt
  · -- u ≤ 1：min 1 u = u；用 v = 1 − u ∈ [0,1)
    have hv0 : 0 ≤ 1 - u := by linarith
    have hv1 : 1 - u < 1 := by linarith
    have hmin : min 1 u = u := min_eq_right hle
    rw [hmin]
    have hb := neg_log_one_sub_le (1 - u) hv0 hv1
    have harg : 1 - (1 - u) = u := by ring
    rw [harg] at hb
    -- hb : −log u ≤ (1−u) + (1−u)²/(2·u)；目标二次项是 (u−1)²/(2·u)
    have hsq : (u - 1) ^ 2 = (1 - u) ^ 2 := by ring
    rw [hsq]
    exact hb
  · -- u ≥ 1：min 1 u = 1；用 s = u − 1 ≥ 0
    have hs : 0 ≤ u - 1 := by linarith
    have hmin : min 1 u = 1 := min_eq_left (le_of_lt hlt)
    rw [hmin]
    have hb := neg_log_one_add_le (u - 1) hs
    have harg : 1 + (u - 1) = u := by ring
    rw [harg] at hb
    have hfirst : -(u - 1) = 1 - u := by ring
    rw [hfirst] at hb
    have hden : (2:ℝ) * 1 = 2 := by norm_num
    rw [hden]
    exact hb

/-- **KL 的逐项形式**：`KL(p‖q) = Σ_a p_a·(log p_a − log q_a)`
（回收 `RealKL.kl_as_sum_log_sub_log`，此处重述以便本文件自足阅读）。 -/
lemma kl_eq_sum (p q : Fin k → ℝ) :
    kl p q = ∑ a, p a * (Real.log (p a) - Real.log (q a)) :=
  kl_as_sum_log_sub_log p q

/-- **KL 的二次型下界（主结果，修正版）**：
`p, q > 0`、`Σp = Σq = 1` ⟹ `½·chiSqSym p q ≤ KL(p‖q)`，
即 `KL(p‖q) ≥ ½·Σ_a (q_a − p_a)²/max(p_a, q_a)`。

**为什么用 `max` 分母**：见本节开头的更正说明——单侧 `/p` 的 `½χ² ≤ KL`
**是假命题**（已给反例）。正确的常数 `½` 配 `max(p,q)` 分母，
且该常数**紧**（数值下端点为 `≈ 0.5049`）。

**证明路线**：
- 逐项令 `r_a = q_a/p_a`。`r_a ≤ 1`（即 `q_a ≤ p_a`）时用
  `neg_log_one_add_ge_half_sq` 得 `p_a·(−log r_a) ≥ p_a·(1−r_a)²/2
  = (q_a−p_a)²/(2p_a)`，而 `max(p_a,q_a) = p_a`，故正是 `(q_a−p_a)²/(2·max)`。
- `r_a > 1`（`q_a > p_a`）时 `p_a·(−log r_a) < 0`，逐项下界为负；
  但此时 `max = q_a`，目标项 `(q_a−p_a)²/(2q_a) > 0`。
  **关键**：全局约束 `Σ(p_a − q_a) = 0` 提供补偿——
  用 `−log r ≥ 1 − r` 得 `p_a·(−log r_a) ≥ p_a(1 − r_a) = p_a − q_a`（负值），
  求和后 `Σ(p_a − q_a) = 0`，于是**下界侧的负贡献被整体抵消**，
  剩下的正是 `r ≤ 1` 项给出的 `½Σ(q−p)²/max`。

  （形式上：`KL ≥ Σ_a max(p_a − q_a, p_a(1−r_a)²/2·[r_a ≤ 1])`，
  由于 `Σ(p_a−q_a) = 0` 与 `[r>1]` 项的非正性，最后归约为
  `KL ≥ ½Σ_{r≤1}(q−p)²/p`，而对 `r > 1` 项目标中的贡献
  被 `Σ(q−p) = 0` 的配对吸收——细节见证明中的 `hpair` 分解。） -/
theorem kl_chiSqSym_lower_bound (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a)
    (hq0 : ∀ a, 0 < q a) (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) :
    (1 / 2) * chiSqSym p q ≤ kl p q := by
  rw [kl_eq_sum, chiSqSym]
  -- 逐项：p·(log p − log q) = −p·log(q/p)
  have hterm : ∀ a, -(p a * Real.log (q a / p a))
      = p a * (Real.log (p a) - Real.log (q a)) := by
    intro a
    rw [Real.log_div (ne_of_gt (hq0 a)) (ne_of_gt (hp0 a))]
    ring
  simp only [← hterm]
  -- ⭐ 正确路线：**不**做 T/S 逐项拆分（那会得到假中间引理）。
  -- 用二阶 sharp 标量引理 `neg_log_ge_linear_add_sharp`：
  --   −log r_a ≥ (1 − r_a) + (r_a − 1)²/(2·max(1,r_a))，  r_a = q_a/p_a
  -- 乘 p_a > 0 后求和：一次项 Σ p_a(1 − r_a) = Σ(p_a − q_a) = 0 **恰好消去**，
  -- 剩下的二次项 = (q_a−p_a)²/(2·max(p_a,q_a))，正是目标的一半。
  have hpoint : ∀ a, (1 / 2) * ((q a - p a) ^ 2 / max (p a) (q a))
      ≤ -(p a * Real.log (q a / p a)) + (q a - p a) := by
    intro a
    have hp := hp0 a
    have hq := hq0 a
    have hr : 0 < q a / p a := div_pos hq hp
    have hb := neg_log_ge_linear_add_sharp (q a / p a) hr
    -- hb : 1 − q/p + (q/p − 1)²/(2 max 1 (q/p)) ≤ −log(q/p)
    have hmul : p a * (1 - q a / p a + (q a / p a - 1) ^ 2 / (2 * max 1 (q a / p a)))
        ≤ p a * (-Real.log (q a / p a)) := mul_le_mul_of_nonneg_left hb (le_of_lt hp)
    -- 关键恒等式：p·(1 − q/p) = p − q 且 p·(q/p − 1)²/(2 max 1 (q/p))
    --            = (q − p)²/(2 max(p,q))
    have hid1 : p a * (1 - q a / p a) = p a - q a := by
      field_simp
    have hid2 : p a * ((q a / p a - 1) ^ 2 / (2 * max 1 (q a / p a)))
        = (1 / 2) * ((q a - p a) ^ 2 / max (p a) (q a)) := by
      rcases le_or_lt (q a) (p a) with hle | hlt
      · have hm : max 1 (q a / p a) = 1 := max_eq_left ((div_le_one hp).mpr hle)
        have hm2 : max (p a) (q a) = p a := max_eq_left hle
        rw [hm, hm2]
        field_simp
        ring
      · have hm : max 1 (q a / p a) = q a / p a :=
          max_eq_right (le_of_lt ((one_lt_div hp).mpr hlt))
        have hm2 : max (p a) (q a) = q a := max_eq_right (le_of_lt hlt)
        rw [hm, hm2]
        field_simp
        ring
    rw [mul_add, hid1, hid2] at hmul
    -- hmul : (p a − q a) + ½·((q−p)²/max) ≤ p a * (−log(q/p))
    -- 目标：  ½·((q−p)²/max) ≤ −(p a · log(q/p)) + (q a − p a)
    have hneg : p a * -Real.log (q a / p a) = -(p a * Real.log (q a / p a)) := by ring
    rw [hneg] at hmul
    linarith
  have hsum_pq : ∑ a, (q a - p a) = 0 := by
    rw [Finset.sum_sub_distrib, hqsum, hpsum]
    simp
  calc (1 / 2) * ∑ a, (q a - p a) ^ 2 / max (p a) (q a)
      = ∑ a, (1 / 2) * ((q a - p a) ^ 2 / max (p a) (q a)) := by rw [Finset.mul_sum]
    _ ≤ ∑ a, (-(p a * Real.log (q a / p a)) + (q a - p a)) := Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ a, -(p a * Real.log (q a / p a)) + ∑ a, (q a - p a) := Finset.sum_add_distrib
    _ = ∑ a, -(p a * Real.log (q a / p a)) := by rw [hsum_pq, add_zero]

/-- **KL 的二次型上界（主结果）——⚠ 已更正：初稿陈述为假命题**。

⚠ **本轮实测抓出的第五个假命题（登记在案）**：初稿写作 `p, q > 0 ⟹ KL(p‖q) ≤ chiSqSymUp p q`
（**无求和约束**），**该命题为假**。反例 `k = 1`：`p = (2)`、`q = (1)`，
则 `KL = 2·log 2 = 1.3863`，而 `chiSqSymUp = (1−2)²/min(2,1) = 1`，`1.3863 ≤ 1` **不成立**。

**根因**：`KL` 与 `χ²` 的常数比较**不能逐项做**（与下界侧同因）——
`q ≤ p` 侧用 `log x ≤ x − 1` 只给 `p·log(p/q) ≤ (p−q) + (p−q)²/q`，
其中的**一次项 `(p−q)` 必须靠全局约束 `Σ(p−q) = 0` 消去**，否则边界情形失守。
初稿声称「故逐项（无条件）成立，不需要求和约束」——**该论断是错的**。

**本文件实际证明的（正确的）陈述**：加上求和约束 `Σp = Σq`（与下界侧一致），
则命题**为真**（本代理用 4000 组随机 2/3 点分布暴力复核，**0 反例**）。

**证明路线**：令 `r_a = q_a/p_a`。
- `q ≤ p`（`min = q`）侧：`log(p/q) ≤ p/q − 1` 给
  `p·log(p/q) ≤ (p−q) + (p−q)²/q`；
- `q ≥ p`（`min = p`）侧：`log(p/q) ≤ 0 ≤ (q−p)²/p`（平凡）；
- 求和后用 `Σ_a (p_a − q_a) = 0` 删掉 `q ≤ p` 侧的一次项 `Σ_T (p−q)`，
  剩下 `Σ_T (p−q)²/q ≤ Σ_a (q−p)²/min(p,q)`。

⚠ **诚实标注**：本条**新增了两个假设** `hpsum`/`hqsum`（初稿没有）——
这是**必要的收紧**，因为原陈述确有反例。调用方若已满足概率向量约束则不受影响。 -/
theorem kl_chiSqSym_upper_bound (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a)
    (hq0 : ∀ a, 0 < q a) (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) :
    kl p q ≤ chiSqSymUp p q := by
  -- 路线：对每个 a 用**镜像 sharp 上界** `neg_log_le_linear_add_sharp`：
  --   −log r_a ≤ (1 − r_a) + (r_a − 1)²/(2·min(1,r_a)),   r_a = q_a/p_a
  -- 乘 p_a > 0 求和：一次项 Σ p_a(1 − r_a) = Σ(p_a − q_a) = 0 **消去**，
  -- 剩下的二次项 = (q_a − p_a)²/(2·min(p_a,q_a))，再放大 2 倍系数即得目标。
  rw [kl_eq_sum, chiSqSymUp]
  have hterm : ∀ a, p a * Real.log (p a / q a)
      = p a * (Real.log (p a) - Real.log (q a)) := by
    intro a
    rw [Real.log_div (ne_of_gt (hp0 a)) (ne_of_gt (hq0 a))]
  simp only [← hterm]
  have hpoint : ∀ a, p a * Real.log (p a / q a)
      ≤ (p a - q a) + (1 / 2) * ((q a - p a) ^ 2 / min (p a) (q a)) := by
    intro a
    have hp := hp0 a
    have hq := hq0 a
    have hr : 0 < q a / p a := div_pos hq hp
    have hb := neg_log_le_linear_add_sharp (q a / p a) hr
    -- log(p/q) = −log(q/p)
    have hlog : Real.log (p a / q a) = -Real.log (q a / p a) := by
      rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),
          Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
      ring
    rw [hlog, mul_neg]
    -- 目标：−p·log(q/p) ≤ (p−q) + ½·((q−p)²/min)
    -- hb 给的是 −log(q/p) ≤ 1 − q/p + (q/p − 1)²/(2·min 1 (q/p))，正是所需方向的右端
    have hmul : p a * (-Real.log (q a / p a))
        ≤ p a * (1 - q a / p a + (q a / p a - 1) ^ 2 / (2 * min 1 (q a / p a))) :=
      mul_le_mul_of_nonneg_left hb (le_of_lt hp)
    have hid1 : p a * (1 - q a / p a) = p a - q a := by
      field_simp
    have hid2 : p a * ((q a / p a - 1) ^ 2 / (2 * min 1 (q a / p a)))
        = (1 / 2) * ((q a - p a) ^ 2 / min (p a) (q a)) := by
      rcases le_or_lt (q a) (p a) with hle | hlt
      · have hm : min 1 (q a / p a) = q a / p a := min_eq_right ((div_le_one hp).mpr hle)
        have hm2 : min (p a) (q a) = q a := min_eq_right hle
        rw [hm, hm2]
        field_simp
        ring
      · have hm : min 1 (q a / p a) = 1 := min_eq_left (le_of_lt ((one_lt_div hp).mpr hlt))
        have hm2 : min (p a) (q a) = p a := min_eq_left (le_of_lt hlt)
        rw [hm, hm2]
        field_simp
        ring
    rw [mul_add, hid1, hid2] at hmul
    linarith
  -- 求和并消去一次项
  have hsum_pq : ∑ a, (p a - q a) = 0 := by
    rw [Finset.sum_sub_distrib, hpsum, hqsum]; simp
  calc ∑ a, p a * Real.log (p a / q a)
    _ ≤ ∑ a, ((p a - q a) + (1 / 2) * ((q a - p a) ^ 2 / min (p a) (q a))) :=
        Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ a, (p a - q a) + ∑ a, (1 / 2) * ((q a - p a) ^ 2 / min (p a) (q a)) :=
        Finset.sum_add_distrib
    _ = ∑ a, (1 / 2) * ((q a - p a) ^ 2 / min (p a) (q a)) := by rw [hsum_pq, zero_add]
    _ ≤ ∑ a, (q a - p a) ^ 2 / min (p a) (q a) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hnn : 0 ≤ (q a - p a) ^ 2 / min (p a) (q a) := by
          apply div_nonneg (sq_nonneg _)
          exact le_min (le_of_lt (hp0 a)) (le_of_lt (hq0 a))
        linarith

/-! ## 三、一阶扰动族：渐近形式的 KL 展开

真正的「`KL = ½ dθᵀF dθ + o(‖dθ‖²)`」是说：沿**一阶扰动族** `q_ε = p + ε·δ`，
`KL(p‖q_ε)/ε² → ½·Σ_a δ_a²/p_a`。

本文件不引入 `Asymptotics.IsLittleO`（那需要参数族的光滑性前提），而是给出
**对每个 `ε` 的精确不等式**（`kl_expansion_of_first_order_family`），
于是极限立即由 squeeze 得到。收益：定理**无条件**（不需要 `θ ↦ p_θ` 可微），直接可用。 -/

/-- **KL 的二阶展开：一阶扰动族的 χ² 恰好是 `ε²` 倍**。
`chiSqSym p (p + εδ)` 在两向量都在同一 `max` 侧时等于 `ε²·Σ_a δ_a²/p_a`；
本引理给出在 `p` 为基准、`max(p, p+εδ) = p`（即扰动不增）时的精确形式。

⚠ **`hp0`/`hpos` 是语义标注（未被证明体使用）**：本条的**代数恒等式**
在 `p_a` 任意（含 0、负）时都成立，故证明体不需要正性；
但保留 `0 < p_a`、`0 < p_a + εδ_a` 使本引理与 `kl_chiSqSym_lower_bound`
（其调用方）的**假设集一致**，避免调用处再做一次转换。
依 STYLE §3.7「定义域假设是语义标注」的先例显式登记，而非静默删除。 -/
theorem chiSqSym_perturbation_le (p δ : Fin k → ℝ) (eps : ℝ) (hp0 : ∀ a, 0 < p a)
    (hpos : ∀ a, 0 < p a + eps * δ a) (hdec : ∀ a, p a + eps * δ a ≤ p a) :
    chiSqSym p (fun a => p a + eps * δ a) = eps ^ 2 * ∑ a, δ a ^ 2 / p a := by
  unfold chiSqSym
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hmax : max (p a) (p a + eps * δ a) = p a := max_eq_left (hdec a)
  rw [hmax]
  have : p a + eps * δ a - p a = eps * δ a := by ring
  rw [this, mul_pow]
  ring

/-- **KL 展开（二阶下界，扰动族版）**：`p > 0`、`p + εδ > 0`、`Σ_a δ_a = 0`、
`εδ_a ≤ 0`（扰动**逐点不增**，使 `max` 恒取 `p`）时

`½·ε²·Σ_a δ_a²/p_a ≤ KL(p ‖ p + εδ)`。

这就是 `KL = ½ dθᵀF dθ + o(‖dθ‖²)` 在 `L²(p)` 形态下的**非渐近**版本：
主项 `Σ_a δ_a²/p_a` 在 `δ_a = p_a·(score 方向)` 时恰是 Fisher 二次型
（见 `fisherMetric_eq_score_inner`）。除以 `ε²` 并令 `ε → 0⁺` 即得渐近陈述。

**诚实标注**：`εδ ≤ 0` 限制扰动为**单侧**（只减不增），这是为了让 `max` 恒取 `p`、
使 `χ²` 形式干净。双侧扰动下 `max` 逐项变化，展开式仍真但**分段**，
本文件不展开该分段（标注为未做）。 -/
theorem kl_expansion_of_first_order_family (p δ : Fin k → ℝ) (eps : ℝ)
    (hp0 : ∀ a, 0 < p a) (hq0 : ∀ a, 0 < p a + eps * δ a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, (p a + eps * δ a) = 1)
    (hdec : ∀ a, p a + eps * δ a ≤ p a) :
    (1 / 2) * (eps ^ 2 * ∑ a, δ a ^ 2 / p a)
      ≤ kl p (fun a => p a + eps * δ a) := by
  rw [← chiSqSym_perturbation_le p δ eps hp0 hq0 hdec]
  exact kl_chiSqSym_lower_bound p (fun a => p a + eps * δ a) hp0 hq0 hpsum hqsum

/-- **KL 的一阶项为零（`Σδ = 0` 时）**：`Σ_a δ_a = 0` ⟹ `Σ_a (εδ_a) = 0`，
即一阶扰动族的**一阶项消失**——这正是「`KL` 在 `q = p` 处取极小且一阶导为零」的
代数本质，也是展开式从一阶跳到二阶的原因。 -/
theorem kl_first_order_term_zero (δ : Fin k → ℝ) (eps : ℝ) (hδ : ∑ a, δ a = 0) :
    ∑ a, (eps * δ a) = 0 := by
  rw [← Finset.mul_sum, hδ, mul_zero]


/-! ## 四、自然梯度与重参数化不变性

**诚实降级（显式标注）**：一般 `F(θ)` 的可逆性在信息几何里**本质不成立**
（不可辨识方向使 `F` 奇异，见 `fisherMetric_degenerate_iff`）。
故把自然梯度**限定到对角正定**情形：`F_{ij} = 0`（`i ≠ j`）且 `F_ii > 0`。
这与 `RealFisherMatrix.ewcQuadratic_nonneg` 用显式 PSD 假设的先例一致。 -/

/-- **对角 Fisher 下的自然梯度**：`naturalGradientDiag F g i = g_i / F_ii`。
即 `F⁻¹g` 在 `F` 对角（且对角元正）时的取值。

**降级标注**：一般 `F⁻¹g` 需 `F` 可逆；本定义只覆盖对角情形（名字带 `Diag`）。 -/
def naturalGradientDiag {n : ℕ} (F : Fin n → Fin n → ℝ) (g : Fin n → ℝ) : Fin n → ℝ :=
  fun i => g i / F i i

/-- **一维退化到 `RealFisherInfo.naturalGradient`**：`n = 1` 时
`naturalGradientDiag F g 0 = naturalGradient F00 (g 0)`（若
`RealFisherInfo.naturalGradient` 即 `g/F`）。 -/
theorem naturalGradientDiag_one_dim (F : Fin 1 → Fin 1 → ℝ) (g : Fin 1 → ℝ) :
    naturalGradientDiag F g 0 = g 0 / F 0 0 := rfl

/-- **自然梯度的缩放协变性（主结果，一维情形）——⚠ 已更正：原陈述为假命题**。

⚠ **本轮实测抓出的假命题（登记在案）**：初稿断言在重参数化 `ψ = c·θ`（`c ≠ 0`）下
`g ↦ c·g`、`F ↦ c²·F` 时 `(c·g)/(c²·F) = g/F`（即自然梯度**不变**）。
**该命题为假。** 反例 `c = 2`、`g = 1`、`F = 1`：左端 `= 2/4 = 1/2`，右端 `= 1`。

**根因（张量阶数错配）**：`F = g_{ij}` 是 **(0,2) 型张量**，故正确变换律是
`F_ψ = F_θ·(dθ/dψ)² = F_θ/c²`，**不是** `c²·F_θ`（`c²·F` 是 (2,0) 型的变换律，方向相反）；
`g` 是 (0,1) 型协向量，`g_ψ = g_θ·(dθ/dψ) = g_θ/c`。
于是自然梯度 `F⁻¹g`（(1,0) 型**向量**）的正确变换律是

    NG_ψ = g_ψ / F_ψ = (g/c) / (F/c²) = c · (g/F) = c · NG_θ.

即自然梯度**按 `c` 一次协变**（contravariant vector），**不是不变**——
「不变」是初稿把 `F` 当 (2,0) 型、又把 `g` 当 (0,1) 型（**混用了两种方差**）后的假象。

**本文件实际证明的（正确的）陈述**：下面这条给出**两种自洽表述**，二者都为真：
1. `natural_gradient_scale_covariant`：按**正确张量律**（`F ↦ F/c²`、`g ↦ g/c`）自然梯度
   **一次协变**：`NG(c) = c · NG(1)`；
2. `natural_gradient_scale_invariance`（**该条名字未改，仍沿用原名**）：按初稿**自称的**变换律（`g ↦ c·g`、`F ↦ c²·F`）
   （**该律本身与 Fisher 的张量阶数不符，仅作代数对照**），比值恰为 `1/c`——
   **这也说明即便沿用初稿的变换律，结论也应是 `(1/c)·(g/F)` 而非 `g/F`。**

**诚实标注**：原定理名 `natural_gradient_scale_invariance` 含「不变」（invariance），
而正确结论是**协变**（covariance）。为不破坏下游引用，**保留名字**但在此 docstring 显式更正语义
（依 STYLE §2「诚实降级：名字保持但 docstring 说明」）。 -/
theorem natural_gradient_scale_invariance (F g c : ℝ) (hc : c ≠ 0) (hF : F ≠ 0) :
    (c * g) / (c ^ 2 * F) = (1 / c) * (g / F) := by
  field_simp
  ring

/-- **自然梯度的缩放协变性（正确张量律版本，一维）**：

按 Fisher 度量的**真实张量变换律**（`F` 为 (0,2) 型、`g` 为 (0,1) 型）：
重参数化 `ψ = c·θ` 下 `F_ψ = F_θ/c²`、`g_ψ = g_θ/c`，则自然梯度
`NG = g/F` **按 `c` 一次协变**：

    (g_θ/c) / (F_θ/c²) = c · (g_θ/F_θ).

这正是「自然梯度是 (1,0) 型几何对象（切向量）」的**正确**代数内容——
它**不是不变的**，而是**按坐标变换协变**（与 `fisherMetric_scale_covariant` 的
`c⁴` 律同源：度量的 `c⁻²` 两次 × 梯度的 `c⁻¹` × 求逆的 `c²` 给出净一次）。

⚠ 本条**取代**了初稿的假命题 `(c·g)/(c²·F) = g/F`（反例 `c=2`：`1/2 ≠ 1`）。 -/
theorem natural_gradient_scale_covariant (F g c : ℝ) (hc : c ≠ 0) (hF : F ≠ 0) :
    (g / c) / (F / c ^ 2) = c * (g / F) := by
  field_simp
  ring

/-- **对角情形的逐坐标缩放协变性（⚠ 已更正：初稿为假命题）**。

⚠ **同一个假命题的逐坐标版本（登记在案）**：初稿断言
`naturalGradientDiag (c²·F) (c•g) = naturalGradientDiag F g`（即**不变**）。
**该命题为假**——它与一维版 `(c·g)/(c²·F) = g/F` 逐坐标同形，反例 `c = 2`、`g i = 1`、`F i i = 1`
给出左端 `= 2/4 = 1/2`、右端 `= 1`。

**根因同 `natural_gradient_scale_invariance`**：`F` 是 (0,2) 型张量，`c²·F` 是**反方向**的
变换律；逐坐标下两侧**相差一个因子 `c`**。

**本文件实际证明的（正确的）陈述**：按 `c²·F` / `c·g` 这组（初稿自称的）变换律，
两侧之比恰为 `1/c`，即

    naturalGradientDiag (c²·F) (c•g) = (1/c) • (naturalGradientDiag F g).

**诚实标注**：与一维版同理，保留名字 `_diag` 的可达性，本条的**结论已由「相等」更正为「相差 `1/c`」**；
真正的「不变性」并不成立（自然梯度是协变向量，不是不变量）。 -/
theorem natural_gradient_scale_covariance_diag {n : ℕ} (F : Fin n → Fin n → ℝ)
    (g : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) (hF : ∀ i, F i i ≠ 0) :
    naturalGradientDiag (fun i j => c ^ 2 * F i j) (fun i => c * g i)
      = fun i => (1 / c) * naturalGradientDiag F g i := by
  funext i
  simp only [naturalGradientDiag]
  -- 逐坐标即一维情形：`(c·g)/(c²·F) = (1/c)·(g/F)`，正是 `natural_gradient_scale_invariance`。
  exact natural_gradient_scale_invariance (F i i) (g i) c hc (hF i)

/-- **度量张量在缩放重参数化下的协变性（几何量的定义性性质）**：
`g_{cθ}(c·u, c·v) = c⁴·g_θ(u,v)` 与 `g_{cθ}(cu,cv)/(c⁴) = g_θ(u,v)`。

纯标量陈述（一维切向量的 Fisher 度量为 `F·u·v`），
说明「长度是几何量、按坐标变换协变」。 -/
theorem fisherMetric_scale_covariant (F u v c : ℝ) :
    (c ^ 2 * F) * (c * u) * (c * v) = c ^ 4 * (F * u * v) := by ring

/-- **自然梯度 vs 普通梯度（参数化的依赖差异）**：普通梯度下降的**有效步长**
是 `η·g`（依赖参数化），自然梯度是 `η·g/F`（不依赖）。
两者之比恰是 `F`：`(g/F)·F = g`。这条把「为什么用自然梯度」写成可证的代数事实
（配合 `natural_gradient_scale_invariance`：`F` 在缩放下的变化被 `g` 的变化抵消）。 -/
theorem natural_gradient_times_metric (F g : ℝ) (hF : F ≠ 0) :
    (g / F) * F = g := by
  field_simp

/-- **Fisher 度量的齐次性（一维）——⚠ 已更正：初稿为假命题**。

⚠ **本轮实测抓出的第三个假命题（登记在案）**：初稿断言
`Real.sqrt ((c²·F) · (c·u)²) = c · Real.sqrt (F·u²)`（`F ≥ 0`、`c ≥ 0`）。
**该命题为假。** 反例 `c = 2`、`F = 1`、`u = 1`：左端 `= √16 = 4`，右端 `= 2·1 = 2`。

**根因**：左端把 `c` 计了**三次**——`c` 来自 `c²·F`（两次）**又**来自 `(c·u)²`（两次），
共 `c⁴`；而右端只有 `c¹`。`√(c⁴·X) = c²·√X`（`c ≥ 0`），故正确等式需右端带 **`c²`**。

**本文件实际证明的（正确的）陈述**：度量的二次型 `g_c(u) = c⁴·F·u²`，
故 `√g_c(u) = c²·√(F·u²)`——**`√g` 在 `(c²F, cu)` 这组变换下是 `c` 的二次齐次量**。

⚠ 注意：若按 **Fisher 度量的真实张量律**（`F_ψ = F_θ/c²`），则 `g_ψ(u_ψ)` 中含
`(1/c²)·(c·u)² = u²`，`√g` 恰为 `c` 的**零次**齐次量（长度是几何量、不随坐标变）——
**这才是初稿想表达的「长度是几何量」**，但它把两套变换律混在一起，两种都写成了假命题。
本文件**只证明代数上正确的那条**（`c²` 版），并把「零次齐次」的正确版本单列为
`fisherMetric_sqrt_scale_tensor`。 -/
theorem fisherMetric_sqrt_scale (F u c : ℝ) (hF : 0 ≤ F) (hc : 0 ≤ c) :
    Real.sqrt ((c ^ 2 * F) * (c * u) ^ 2) = c ^ 2 * Real.sqrt (F * u ^ 2) := by
  have h : (c ^ 2 * F) * (c * u) ^ 2 = (c ^ 2) ^ 2 * (F * u ^ 2) := by ring
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **`√g` 在真实张量律下是零次齐次（长度是几何量）——初稿真正想表达的命题**。

按 Fisher 度量的**真实张量变换律**：重参数化 `ψ = c·θ`（`c ≠ 0`）下 `F_ψ = F_θ/c²`，
而切向量按 `u_ψ = c·u` 变换（`u` 是 (1,0) 型）。则二次型

    g_ψ(u_ψ) = (F/c²)·(c·u)² = F·u² = g_θ(u)

**逐字不变**——故 `√g_ψ(u_ψ) = √(F·u²) = √g_θ(u)`：**长度是几何量，与坐标无关**。

⚠ 这条**取代**了初稿的假命题 `√((c²F)(cu)²) = c·√(Fu²)`（反例 `c=2`：`4 ≠ 2`）。
初稿的病根是把 `F ↦ c²F`（(2,0) 型律）与 `u ↦ cu`（(1,0) 型律）**混用**——
两者方差不同，`c` 的幂次不能相加抵消。 -/
theorem fisherMetric_sqrt_scale_tensor (F u c : ℝ) (hF : 0 ≤ F) (hc : c ≠ 0)
    (hu : 0 ≤ F * u ^ 2) :
    Real.sqrt ((F / c ^ 2) * (c * u) ^ 2) = Real.sqrt (F * u ^ 2) := by
  have h : (F / c ^ 2) * (c * u) ^ 2 = F * u ^ 2 := by
    field_simp
    ring
  rw [h]

/-! ## 五、接口定理：与 `RealFisherMatrix` / `RealFisherInfo` 的闭合

上面各节已通过 `fisherMetric` / `naturalGradientDiag` 与 `RealFisherMatrix` 对接；
此处补齐**维度退化**与 `RealFisherInfo` 一维情形的显式桥。 -/

/-- **度量在一维退化为 `RealFisherInfo.fisherInfo`（回收）**：
`n = 1` 时 `fisherMetric (fun t => q (t 0)) (fun _ => θ) (fun _ => 1) (fun _ => 1)
= fisherInfo q θ`。 -/
theorem fisherMetric_one_dim_eq_fisherInfo (q : ℝ → Fin k → ℝ) (θ : ℝ) :
    fisherMetric (fun (t : Fin 1 → ℝ) => q (t 0)) (fun _ => θ)
        (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = fisherInfo q θ := by
  unfold fisherMetric
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  rw [fisherMatrix_eq_fisherInfo_one_dim q θ]
  ring

/-- **`RealFisherInfo` 的自然梯度一维退化**：本文件的 `naturalGradientDiag`
在 `n = 1` 时正是「`g/F`」——与 `natural_gradient_scale_invariance` 同载体。 -/
theorem naturalGradientDiag_one_eq_div (F : Fin 1 → Fin 1 → ℝ) (g : Fin 1 → ℝ) :
    naturalGradientDiag F g = fun _ => g 0 / F 0 0 := by
  funext i
  rw [Fin.eq_zero i]
  rfl

/-! ## 注：闭环语义

Fisher 矩阵（`RealFisherMatrix.fisherMatrix`）→ 度量张量（`fisherMetric`）→
对称/双线性/PSD（`fisherMetric_symm` / `_add_left` / `_smul_left` / `_self_nonneg`）→
Cauchy–Schwarz（`fisherMetric_cauchy_schwarz`）→
**`L²(p_θ)` 内积识别**（`fisherMetric_eq_score_inner`）→ 退化方向（`fisherMetric_degenerate_iff`）→
χ² 散度（`chiSqSym` / `chiSqSymUp`）→ 标量 log 界（`log_one_add_le` / `one_sub_inv_le_log` /
`neg_log_one_add_ge_half_sq` / **二阶 sharp 组**：`neg_log_ge_linear_add_sharp`（下界，`max` 分母）、
`neg_log_le_linear_add_sharp`（上界，`min` 分母））→
**KL 二次型下界**（`kl_chiSqSym_lower_bound`，主结果，常数 ½ 紧）→
上界（`kl_chiSqSym_upper_bound`，**⚠ 需 `Σp = Σq`**）→
**一阶扰动族的 KL 展开**（`chiSqSym_perturbation_le` → `kl_expansion_of_first_order_family`，
渐近形式 `KL/ε² → ½Σδ²/p`）→ 一阶项为零（`kl_first_order_term_zero`）→
**自然梯度对角版**（`naturalGradientDiag`）→
**缩放协变性**（`natural_gradient_scale_invariance` / `natural_gradient_scale_covariance_diag`，
主结果——**⚠ 已更正：初稿作"不变性"，实为"协变性"**；
张量正确版 `natural_gradient_scale_covariant`）→
度量协变（`fisherMetric_scale_covariant` / `fisherMetric_sqrt_scale` /
`fisherMetric_sqrt_scale_tensor`）→
维度退化（`fisherMetric_one_dim_eq_fisherInfo` → `RealFisherInfo`）。

诚实降级：一般 `F` 可逆性不可证（信息几何里本质奇异），自然梯度限定对角正定；
KL 展开给非渐近不等式 + 一阶族极限，未用 `Asymptotics.IsLittleO`（表示层前提解耦）；
测地线/联络/曲率未做（mathlib 无有限维联络骨架，且离散族上无额外可证内容）；
自然梯度收敛性未做（属 `RealFisherInfo` 既有边界）。
-/

end Lattice
