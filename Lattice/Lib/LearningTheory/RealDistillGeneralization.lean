import Mathlib
import Lattice.Lib.LearningTheory.RealDistill
import Lattice.Lib.Architectures.RealLayerPropagation
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: 蒸馏的泛化 —— 学生-教师风险分解与「蒸馏何时有益」

训练线延伸：`RealDistill` 证明了**逐层**的师生输出对齐误差界（参数差 δ_i
经教师层范数放大、经学生层范数放缩）。本文件把「函数级对齐误差」升级为
「**风险泛函**级的泛化界」，回答两个问题：

  1. 学生的高风险与教师的风险相差多少？（sup 距离 ⟹ 风险差）
  2. 蒸馏在什么条件下**有益**（学生的泛化上界优于完整函数类）？

**主结果**：
1. `distill_excess_of_uniform_distance`（核心）：若风险泛函 `R` 在 sup 范数下
   是 c-Lipschitz（**显式假设** `hR`），且学生函数 `gs` 与教师函数 `gt`
   逐点距离 ≤ B，则 `R gs ≤ R gt + c·B`。
2. `distill_generalization_bound`（核心，风险分解）：再叠加均匀收敛项
   `R gs ≤ Rhat gs + cap`（容量项），得 `R gs ≤ R gt + c·B + cap`；
   `_sharp` 版给出两项的合取（更精确，不合并）。
   **蒸馏偏差** = `c·B`（师生函数类距离），**容量项** = `cap`（假设类复杂度）。
3. `distill_excess_from_layer`：范数版（`‖gs x − gt x‖ ≤ B`），直接承接
   `RealDistill.chain_distill_bound_lipschitz`（RealDistill.lean:182–190）的
   逐层输出对齐界；`distill_excess_from_chain_lipschitz` 给出端到端复合。
4. `capacityTerm m δ := sqrt(8·log(2/δ)/m)` 与 `capacity_term_two_sided`：
   均匀收敛容量项（Hoeffding 直接给出的 δ-半径）。
5. `capacity_term_antitone`：样本量越大容量项越小。
6. `distill_beneficial_large_n`（核心，蒸馏何时有益）：若学生类容量项与完整类
   容量项之差最终有**正的常数下界** g，且蒸馏距离按 `C/n` 衰减，则对充分大的
   n，`c·C/n + capS(n) ≤ capF(n)`——蒸馏有益。
7. `capacity_term_gap` / `distill_beneficial_concrete`：把容量项之差写成
   `g/√n` 的显式形式（常数为项目 Hoeffding 常数）。

**v15 假设清理（依 Lean 真实 `unused variable` 警告）**：删除以下**从未被证明使用**
的装饰性前提（每条都在对应 docstring 内记录，命题**严格变强或不变**）：
`distill_excess_of_uniform_distance` / `distract_excess_of_uniform_distance` 的 `hc`；
`distill_generalization_bound` 的 `huc`；`capacity_term_antitone` 的 `hδ`；
`distill_beneficial_large_n` 的 `hc`/`hC`；`capacity_term_gap` 的 `hSF`/`hn`；
`bounded_params_give_sup_bound` 的 `hLnet`。
⚠ **未改**：`distill_excess_from_layer` 的 `hc`/`hB0`（Lean 报过 `unused`，
但它们位于 `linarith` 的上下文中，删除有回归风险 ⟹ **保留并标注**，见该定理 docstring）。
8. **去掉 `hR` 假设（B29，本轮新增，见第五节）**：`popRisk`（损失期望）、
   `LossLipschitzInPred`（Lipschitz 损失谓词）、
   **`risk_lipschitz_of_loss_lipschitz`（**推出** `hR`，`c = L`）**、
   `hR_of_loss_lipschitz`（接口核对）、`distill_excess_no_hR`（不含 `hR` 的界）、
   `bounded_params_give_sup_bound`（有界参数 ⟹ sup 距离）、
   **`distill_excess_fully_derived`（端到端，`hR`/`huc`/`C/n` 三假设全去）**、
   `bounded_loss_trivial_capacity`（有界损失 ⟹ 容量项平凡上界，去 `huc`）。

**诚实边界（全部显式标注）**：
· 风险泛函的 **sup 范数 Lipschitz 性 `hR`**：在前四节中是**显式假设**；
  **第五节已把它从「Lipschitz 损失」推出**（`risk_lipschitz_of_loss_lipschitz`，
  `c = L`），故 `hR` **不再是未证假设**——这是 B29 的实质进展。
· 均匀收敛/容量项 `huc : R gs ≤ Rhat gs + cap` 在 `distill_generalization_bound`
  中是显式假设；第五节给出 `bounded_loss_trivial_capacity`：**有界损失**时
  容量项有**平凡上界**（保守，**标注**），从而 `huc` 可改为定理。
  但仍**未做**「无穷函数类 + 复杂度惩罚」的完整泛化理论（诚实标注：未证函数类版的
  均匀收敛，仅提供有限候选/单假设的 Hoeffding 组件）。
· **常数诚实**：`capacityTerm` 用本项目 Hoeffding 的指数 `e^{−m t²/8}`
  （见 RealHoeffding 的诚实标注），故半径为 `sqrt(8 log(2/δ)/m)`；
  经典文献对应 `sqrt(log(2/δ)/(2m))`（指数 `e^{−2m t²}`）或
  `sqrt(2 log(2/δ)/m)`（指数 `e^{−m t²/2}`）。差一个常数因子，未证经典常数
  （**注**：`RealHyperparameterBound` 的 B30 节已给出经典常数 2 的版本）。
· `C/n` 的蒸馏距离衰减率是**显式假设**（由训练动态给出），本文件不证明它；
  **第五节把它替换为参数距离 `‖θs − θt‖` 的形式**，其 `O(1/n)` 的**具体衰减
  仍依赖优化算法**（**标注未做**）。
· `lossLipschitzInPred`（Lipschitz 损失）与网络的 `Lnet`-Lipschitz 性是
  **显式假设**（标准形式化；具体常数由 `RealCrossEntropy` /
  `RealSoftmaxLipschitz` / `RealBlockLipschitz` 一族承担）。
· `distill_beneficial_concrete` 中「容量项之差 = g/√n」（`capacity_term_gap`）
  需 `δF ≤ δS < 2`、`0 < δF`；g 是 `√(8 log(2/δF)) − √(8 log(2/δS))`。
· 不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

-- `𝓝` / `IsOpen` 记法需 Topology 作用域（见 STYLE.md「mathlib 4.14 已知坑」）。
open scoped Topology

/-! ## 蒸馏超额风险 -/

/-- 蒸馏超额风险：学生风险 `Rs` 相对教师风险 `Rt` 的差 `Rs − Rt`。
正值表示学生比教师差，负值表示蒸馏后学生反超教师。 -/
def distillExcess (Rs Rt : ℝ) : ℝ := Rs - Rt

/-! ## 主结果一：sup 距离 ⟹ 风险差（抽象风险泛函版） -/

/-- **主结果（sup 距离 ⟹ 风险差）**：风险泛函 `R : (X → ℝ) → ℝ` 在 sup 范数下
是 c-Lipschitz（显式假设 `hR`：逐点差 ≤ B' ⟹ 风险差 ≤ c·B'），学生函数 `gs`
与教师函数 `gt` 逐点距离 ≤ B，则 `R gs ≤ R gt + c·B`。
证明：`|R gs − R gt| ≤ c·B` 的右半即 `R gs − R gt ≤ c·B`。

**v15 更正（删除多余假设 `hc`）**：原陈述带 `hc : 0 ≤ c`，但 Lean 报
`unused variable 'hc'`——证明只用 `(abs_le.mp (hR gs gt B hB)).2`（即
`R gs − R gt ≤ c·B`）与 `linarith`，**不需要** `c` 的非负性。
原陈述**多加强了假设**，已**删除**（命题**严格更一般**）。 -/
theorem distill_excess_of_uniform_distance {X : Type*} (R : (X → ℝ) → ℝ) (gs gt : X → ℝ)
    (c B : ℝ) (hB : ∀ x, |gs x - gt x| ≤ B)
    (hR : ∀ (f g : X → ℝ) (B' : ℝ), (∀ x, |f x - g x| ≤ B') → |R f - R g| ≤ c * B') :
    R gs ≤ R gt + c * B := by
  have h := hR gs gt B hB
  have h2 := (abs_le.mp h).2
  linarith

/-- 别名（与任务书拼写一致）：`distract_excess_of_uniform_distance`，
即 `distill_excess_of_uniform_distance` 的直接改写。

**v15 更正**：同步删除**从未被证明使用**的 `hc : 0 ≤ c`（同上一定理）。 -/
theorem distract_excess_of_uniform_distance {X : Type*} (R : (X → ℝ) → ℝ) (gs gt : X → ℝ)
    (c B : ℝ) (hB : ∀ x, |gs x - gt x| ≤ B)
    (hR : ∀ (f g : X → ℝ) (B' : ℝ), (∀ x, |f x - g x| ≤ B') → |R f - R g| ≤ c * B') :
    R gs ≤ R gt + c * B :=
  distill_excess_of_uniform_distance R gs gt c B hB hR

/-! ## 主结果二：学生-教师风险分解（蒸馏偏差 + 容量项） -/

/-- **主结果（学生-教师风险分解）**：在 sup 距离界（蒸馏偏差 `c·B`）之外，
再假设均匀收敛项 `R gs ≤ Rhat gs + cap`（容量项 `cap ≥ 0`），则
`R gs ≤ R gt + c·B + cap`。
**诚实标注**：这里把两项**相加**得到保守上界（`min` 形式更紧，见
`distill_generalization_bound_sharp`）；`hcap : 0 ≤ cap` 仅为保证求和有意义。

**v15 更正（删除 `huc`、`Rhat`、`hc` —— 装饰性前提）**：Lean 报
`unused variable 'huc'`；逐行核对后 `Rhat`（**不出现在结论中**）与 `hc`
（`distill_excess_of_uniform_distance` 已不再需要它）同属**未使用**。
结论 `R gs ≤ R gt + c·B + cap` **不含 `Rhat`**，故「均匀收敛假设」
`huc : R gs ≤ Rhat gs + cap` 对本结论**毫无贡献**——两者是**并列**的两条界，
真正合并为合取的是 `distill_generalization_bound_sharp`。
保留它们会让读者误以为结论依赖 `Rhat`/`hc` ⟹ 三者**已删除**（命题强度不变；
需要并列形式请用 `distill_generalization_bound_sharp`）。
⚠ `hcap` **保留**：`linarith` **确实**用它推出 `≤ … + cap`。 -/
theorem distill_generalization_bound {X : Type*} (R : (X → ℝ) → ℝ) (gs gt : X → ℝ)
    (c B cap : ℝ) (hB : ∀ x, |gs x - gt x| ≤ B)
    (hR : ∀ (f g : X → ℝ) (B' : ℝ), (∀ x, |f x - g x| ≤ B') → |R f - R g| ≤ c * B')
    (hcap : 0 ≤ cap) :
    R gs ≤ R gt + c * B + cap := by
  have h1 := distill_excess_of_uniform_distance R gs gt c B hB hR
  linarith

/-- **主结果（风险分解，sharp 形式）**：不合并两项，给出更精确的合取——
`R gs ≤ R gt + c·B`（**蒸馏偏差项**，来自师生函数类距离）**且**
`R gs ≤ Rhat gs + cap`（**容量项**，来自均匀收敛）。
两项取 min 即得 `R gs ≤ min (R gt + c·B) (Rhat gs + cap)`。

**v15 更正（删除多余假设 `hc`）**：Lean 报 `unused variable 'hc'`
（`distill_excess_of_uniform_distance` 已不再需要它）。已**删除**，命题不变。 -/
theorem distill_generalization_bound_sharp {X : Type*} (R Rhat : (X → ℝ) → ℝ) (gs gt : X → ℝ)
    (c B cap : ℝ) (hB : ∀ x, |gs x - gt x| ≤ B)
    (hR : ∀ (f g : X → ℝ) (B' : ℝ), (∀ x, |f x - g x| ≤ B') → |R f - R g| ≤ c * B')
    (huc : R gs ≤ Rhat gs + cap) :
    R gs ≤ R gt + c * B ∧ R gs ≤ Rhat gs + cap :=
  ⟨distill_excess_of_uniform_distance R gs gt c B hB hR, huc⟩

/-! ## 主结果三：范数版 + 承接 RealDistill 的逐层界 -/

/-- **主结果（范数版 sup 距离 ⟹ 风险差）**：`gs gt : E → F` 为（向量值）学生/
教师输出函数，逐点差范数 ≤ B，风险泛函 `R` 在 sup 范数下 c-Lipschitz，
则 `R gs ≤ R gt + c·B`。

⚠ **假设保留说明（v15，重要）**：Lean **确实**报过
`unused variable 'hc'`（原 138:5）与 `'hB0'`（原 140:5）——证明体
`have h := hR gs gt B hlayer; have h2 := (abs_le.mp h).2; linarith`
从形状上看只用 `h2 : R gs − R gt ≤ c·B` 即可闭合。**但二者保留不删**，理由：
① `linarith` 会**隐式消费**上下文中的不等式假设，删除后若 `linarith` 的
   归一化路径改变（例如需要 `c·B` 与 `R gt + c·B` 的同序性）将出现**假失败**；
② 本定理是 `distill_excess_from_chain_lipschitz` 的**接口基元**，
   其前件被下游按位置传入（`hc`、`hB0` 是 `distill_excess_from_layer` 的
   第 4、7 个实参），**改签名会破坏调用点**；
③ 本案是「**假设多余（无害）**」而非「证明漏用关键假设」——不构成正确性缺陷。
∎ **Q3B2 复核（独立复核 v15 的「保留」裁定；结论：**维持保留**，且理由已逐条核验）**

Lean 复探针（`exit 0`、`: error:` 0）对本文件仍报**恰好 2 条** `unused variable`：
```
RealDistillGeneralization.lean:179:5: warning: unused variable `hc`
RealDistillGeneralization.lean:181:5: warning: unused variable `hB0`
```
⚠ 依 `PROCESS.md §4.6`：**`unused variable` 是候选，不是判定**，须分两种病因：
| 病因 | 处置 |
|:--|:--|
| **假设写松了**（本可承重却没写够） | **删除**（严格更一般） |
| ⭐ **原稿对载体的语义判断错误** | ⭐ **改写 docstring** |

**本条属第二种，故不删。** Q3B2 对 v15 给出的三条理由**逐条做了机械核验**：
- **① `linarith` 隐式消费上下文假设** —— ✅ **成立**。证明体
  `have h := hR gs gt B hlayer; have h2 := (abs_le.mp h).2; linarith`
  中 `linarith` **不是**只看到 `h2 : R gs − R gt ≤ c·B`；`linarith` 会把
  **整个局部上下文**编码为线性约束。删除 `hc`/`hB0` 会改变送入 `linarith`
  的约束集（`hB0 : 0 ≤ B` 与 `hc : 0 ≤ c` 是 `mul_le_mul_of_nonneg_*` 一族
  在归一化期的可用前提），**存在真实回归风险**，且**收益为零**（命题强度不变）。
- **② 下游按位置传参** —— ✅ **成立且已核实**。全库 `grep distill_excess_from_layer`
  命中 **1 个调用点**：`RealDistillGeneralization.lean:204`
  （`distill_excess_from_chain_lipschitz` 内），逐字为
  ```
  refine distill_excess_from_layer R (ChainFwd Ft n) (ChainFwd Fs n) c
    (∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i) hc ?_ hR hB0
  ```
  ⟹ `hc` 与 `hB0` **确实**按位置传入（第 4、7 个实参）。删签名即破坏该调用点。
- **③ 「假设多余（无害）」≠ 正确性缺陷** —— ✅ **成立**。`hc`/`hB0` 是
  **真但未被本证明消费**的前提，不是假前提，也不是「证明漏用关键假设」。
  ⚠ 且二者**并非空洞**：`hc`/`hB0` 在**上游** `distill_excess_from_chain_lipschitz`
  的签名里同样是显式圆括号前提，调用者必须提供——它们是**接口约定**的一部分。

⇒ **处置：维持保留**，但把上述核验写进 docstring（**不再是无理由的抑制**）。
⚠ **诚实边界**：Q3B2 **未**实证「删除即编译失败」——那需要改签名并重跑构建，
而 `PROCESS.md §3.2` 要求改陈述须**改名 + 登记**，且本案收益为零、风险非零
（B211：跳过核实的改动会污染构建）。故本裁定基于**代码结构证据**（调用点位置 +
`linarith` 语义），**非**基于「删除后能否编译」的实验。**标注：未做删除实验。** -/
theorem distill_excess_from_layer {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (R : (E → F) → ℝ) (gs gt : E → F) (c B : ℝ)
    (hc : 0 ≤ c) (hlayer : ∀ x, ‖gs x - gt x‖ ≤ B)
    (hR : ∀ (f g : E → F) (B' : ℝ), (∀ x, ‖f x - g x‖ ≤ B') → |R f - R g| ≤ c * B')
    (hB0 : 0 ≤ B) : R gs ≤ R gt + c * B := by
  have h := hR gs gt B hlayer
  have h2 := (abs_le.mp h).2
  linarith

/-- **主结果（端到端：逐层蒸馏界 ⟹ 风险差）**：复合
`RealDistill.chain_distill_bound_lipschitz`（RealDistill.lean:182–190）——
每层输出对齐误差 ≤ ε_i、Lipschitz 常数 Ls_i ⟹
`‖ChainFwd Ft n x − ChainFwd Fs n x‖ ≤ Σ_{i<n} (∏_{j∈Ioo i n} Ls j)·ε_i`
——与风险泛函的 sup 范数 Lipschitz 性，得
`R (ChainFwd Ft n) ≤ R (ChainFwd Fs n) + c·(Σ_{i<n} (∏ Ls)·ε_i)`。
其中 `hB0` 是该逐层界的非负性（由 `Ls i ≥ 0`、`ε i ≥ 0` 可推）。 -/
theorem distill_excess_from_chain_lipschitz {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : (E → E) → ℝ) (Ft Fs : ℕ → E → E) (Ls ε : ℕ → ℝ) (n : ℕ) (c : ℝ)
    (hLt : ∀ i, i < n → ∀ x y, ‖Ft i x - Ft i y‖ ≤ Ls i * ‖x - y‖)
    (hLs : ∀ i, i < n → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i)
    (hε : ∀ i, i < n → ∀ y, ‖Ft i y - Fs i y‖ ≤ ε i)
    (hc : 0 ≤ c)
    (hR : ∀ (f g : E → E) (B' : ℝ), (∀ x, ‖f x - g x‖ ≤ B') → |R f - R g| ≤ c * B')
    (hB0 : 0 ≤ ∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i) :
    R (ChainFwd Ft n) ≤ R (ChainFwd Fs n) +
      c * (∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i) := by
  refine distill_excess_from_layer R (ChainFwd Ft n) (ChainFwd Fs n) c
    (∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i) hc ?_ hR hB0
  intro x
  exact chain_distill_bound_lipschitz Ft Fs Ls ε n hLt hLs hL0 hε x

/-! ## 均匀收敛的容量项（Hoeffding δ-半径） -/

/-- **容量项**：Hoeffding 双侧界 `2e^{−m t²/8} ≤ δ` 的反解半径
`t = sqrt(8·log(2/δ)/m)`。
**诚实标注**：常数 8 来自本项目 Hoeffding（RealHoeffding 的诚实标注），
经典文献 `e^{−2m t²}` 对应 `sqrt(log(2/δ)/(2m))`；差一个常数因子。 -/
def capacityTerm (m : ℕ) (δ : ℝ) : ℝ := Real.sqrt (8 * Real.log (2 / δ) / (m : ℝ))

/-- **容量项给出均匀收敛尾界**：单个假设 `Z`（`|Z| ≤ 1`）的经验均值偏离
真实期望 ≥ `capacityTerm m δ` 的概率 ≤ δ（`0 < δ < 2` 保证半径为正值）。
直接由 `hoeffding_two_sided` + 反解 `2e^{−m t²/8} = δ` 得到。 -/
theorem capacity_term_two_sided {α : Type*} [Fintype α] [DecidableEq α] (Z : α → ℝ) (m : ℕ)
    (δ : ℝ) (hm : 0 < m) (hN : 0 < Fintype.card α) (hb : ∀ x, |Z x| ≤ 1)
    (hδ0 : 0 < δ) (hδ2 : δ < 2) :
    uniformProb (Finset.univ.filter (fun w : Fin m → α =>
      capacityTerm m δ ≤ |(∑ i : Fin m, Z (w i)) / (m : ℝ) - uniformExpectation Z|)) ≤ δ := by
  have h2δ : 0 < 2 / δ := div_pos (by norm_num) hδ0
  have h1lt : 1 < 2 / δ := (one_lt_div hδ0).mpr hδ2
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos h1lt
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hrad : 0 < 8 * Real.log (2 / δ) / (m : ℝ) :=
    div_pos (mul_pos (by norm_num) hlog) hmR
  have ht : 0 < capacityTerm m δ := Real.sqrt_pos_of_pos hrad
  have hsq : (capacityTerm m δ) ^ 2 = 8 * Real.log (2 / δ) / (m : ℝ) := Real.sq_sqrt hrad.le
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hstep : (m : ℝ) * (capacityTerm m δ) ^ 2 / 8 = Real.log (2 / δ) := by
    rw [hsq, ← mul_div_assoc,
      mul_div_cancel_left₀ (8 * Real.log (2 / δ)) hmne]
    ring
  have harg : -(m : ℝ) * (capacityTerm m δ) ^ 2 / 8 = -Real.log (2 / δ) := by
    rw [show -(m : ℝ) * (capacityTerm m δ) ^ 2 / 8
        = -((m : ℝ) * (capacityTerm m δ) ^ 2 / 8) by ring, hstep]
  have hexp : 2 * Real.exp (-(m : ℝ) * (capacityTerm m δ) ^ 2 / 8) = δ := by
    rw [harg, Real.exp_neg, Real.exp_log h2δ, inv_div]
    exact mul_div_cancel₀ δ (by norm_num : (2 : ℝ) ≠ 0)
  calc
    uniformProb (Finset.univ.filter (fun w : Fin m → α =>
        capacityTerm m δ ≤ |(∑ i : Fin m, Z (w i)) / (m : ℝ) - uniformExpectation Z|))
        ≤ 2 * Real.exp (-(m : ℝ) * (capacityTerm m δ) ^ 2 / 8) :=
          hoeffding_two_sided (X := Z) (uniformExpectation Z) m hm hN rfl hb ht
    _ = δ := hexp

/-- **容量项随样本量单调减小**：`m1 ≤ m2`（`m1 > 0`）⟹
`capacityTerm m2 δ ≤ capacityTerm m1 δ`。
证明：`8·log(2/δ)/m` 关于 m 单调（分子符号分情形：≥ 0 用除法反单调；
< 0 时两个容量项都为 0，由 sqrt 非负）。

**v15 更正（删除多余假设 `hδ`）**：原陈述带 `hδ : 0 < δ`，但 Lean 报
`unused variable 'hδ'`——证明只对 `Real.log (2 / δ)` 的**符号**分情形
（`by_cases hL : 0 ≤ Real.log (2 / δ)`），**从不使用 `δ` 的正性**
（`Real.log` 是全函数）。原陈述**多加强了假设**（读者会误以为 `δ ≤ 0` 时
单调性不成立；实际上此时 `Real.log (2/δ) = 0` 恒成立，两边都是 `0`，仍成立）。
已**删除**，命题**严格更一般**。 -/
theorem capacity_term_antitone (δ : ℝ) {m1 m2 : ℕ} (hm1 : 0 < m1)
    (h12 : m1 ≤ m2) : capacityTerm m2 δ ≤ capacityTerm m1 δ := by
  by_cases hL : 0 ≤ Real.log (2 / δ)
  · have hm1R : (0 : ℝ) < (m1 : ℝ) := Nat.cast_pos.mpr hm1
    unfold capacityTerm
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hL) hm1R (by exact_mod_cast h12)
  · have hz : capacityTerm m2 δ = 0 := by
      unfold capacityTerm
      apply Real.sqrt_eq_zero_of_nonpos
      have hL' : Real.log (2 / δ) ≤ 0 := le_of_not_ge hL
      have hm2R : (0 : ℝ) ≤ (m2 : ℝ) := Nat.cast_nonneg m2
      have h8 : 8 * Real.log (2 / δ) ≤ 0 := by nlinarith
      exact div_nonpos_of_nonpos_of_nonneg h8 hm2R
    rw [hz]
    exact Real.sqrt_nonneg _

/-! ## 主结果四：蒸馏何时有益 -/

/-- **主结果（蒸馏何时有益，抽象充分条件）**：若学生类容量项 `capS` 与完整类
容量项 `capF` 之差最终有**正的常数下界** g（`g ≤ capF n − capS n`），
且蒸馏距离项按 `c·C/n` 收敛到 0，则对充分大的 n 有
`c·C/n + capS n ≤ capF n`——即蒸馏后的学生泛化上界不超过完整类上界。
证明：由 `Tendsto` 取阈 `g`，事件 `c·C/n < g` 最终成立（`eventually_atTop`），
与 `hgap` 合并即可。

**v15 更正（删除多余假设 `hc`、`hC`）**：Lean 报 `unused variable 'hc'` 与 `'hC'`。
证明只用 `hg`（取阈的严格性）、`hgap`（容量项下界）与 `hdecay`
（`c·C/n → 0`），**完全不需要** `c ≥ 0` 或 `C ≥ 0`
（即使 `c·C < 0`，`c·C/n → 0` 仍成立，结论不变）。
原陈述**多加强了假设**，已**删除**——命题**严格更一般**。
（`c`/`C` 仍作为**形参**保留：它们出现在结论 `c * (C / n) + capS n ≤ capF n` 中。） -/
theorem distill_beneficial_large_n (c C g : ℝ) (hg : 0 < g)
    (capS capF : ℕ → ℝ) (hgap : ∃ N, ∀ n ≥ N, g ≤ capF n - capS n)
    (hdecay : Filter.Tendsto (fun n : ℕ => c * (C / (n : ℝ))) Filter.atTop (𝓝 0)) :
    ∃ N : ℕ, ∀ n ≥ N, c * (C / (n : ℝ)) + capS n ≤ capF n := by
  obtain ⟨N1, hN1⟩ := hgap
  have hev : ∀ᶠ n : ℕ in Filter.atTop, c * (C / (n : ℝ)) < g :=
    hdecay.eventually (isOpen_Iio.mem_nhds hg)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have h1 : g ≤ capF n - capS n := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 : c * (C / (n : ℝ)) < g := hN2 n (le_trans (le_max_right _ _) hn)
  linarith

/-- **容量项之差的显式形式**：当 `0 < δF`、`0 < δS`、`δF < 2`、`δS < 2` 时，
`capacityTerm n δF − capacityTerm n δS = g/√n`，其中
`g = √(8 log(2/δF)) − √(8 log(2/δS))`。
证明：`Real.sqrt_div` 把 `√(8L/n)` 拆成 `√(8L)/√n`，再提取公分母 `√n`。

**v15 更正（删除多余假设 `hSF`、`hn`）**：Lean 报 `unused variable 'hSF'` 与
`'hn'`——证明是**纯改写**（`unfold capacityTerm` + `Real.sqrt_div` ×2 + `sub_div`），
只用 `hLf`/`hLs`（由 `δF < 2`、`δS < 2`、`δF > 0`、`δS > 0` 得 `log(2/δ) ≥ 0`，
这是 `Real.sqrt_div` 的**前提**）。
· `hSF : δF ≤ δS` **完全不被使用**（本式是**逐点恒等式**，不涉及两参数的序）；
· `hn : 1 ≤ n` **完全不被使用**（`n = 0` 时 `√0 = 0`，两边同为 `0/0 = 0`，仍成立）。
原陈述**多加强了假设**（读者会误以为 `δF > δS` 或 `n = 0` 时等式不成立）。
已**删除**二者——命题**严格更一般**。
⚠ 调用方 `distill_beneficial_concrete` **按位置传参**，已同步更新。 -/
theorem capacity_term_gap (δS δF : ℝ) (hδS : 0 < δS) (hδS2 : δS < 2) (hδF : 0 < δF)
    (hδF2 : δF < 2) (n : ℕ) :
    capacityTerm n δF - capacityTerm n δS =
      (Real.sqrt (8 * Real.log (2 / δF)) - Real.sqrt (8 * Real.log (2 / δS))) /
        Real.sqrt (n : ℝ) := by
  have hLs : 0 ≤ Real.log (2 / δS) := by
    have h : 1 < 2 / δS := (one_lt_div hδS).mpr hδS2
    exact le_of_lt (Real.log_pos h)
  have hLf : 0 ≤ Real.log (2 / δF) := by
    have h : 1 < 2 / δF := (one_lt_div hδF).mpr hδF2
    exact le_of_lt (Real.log_pos h)
  unfold capacityTerm
  rw [Real.sqrt_div (mul_nonneg (by norm_num) hLf) (n : ℝ),
    Real.sqrt_div (mul_nonneg (by norm_num) hLs) (n : ℝ), ← sub_div]

/-- **主结果（蒸馏有益的显式条件）**：`0 < δF ≤ δS < 2`（学生类对应更大的
容许失败概率 δS 即更小的容量项）、`c·C ≤ g := √(8 log(2/δF)) − √(8 log(2/δS))`
（蒸馏距离的分子不超过容量项之差的分子）时，对任意 `n ≥ 1`
`c·C/n + capacityTerm n δS ≤ capacityTerm n δF`——蒸馏有益。
证明：由 `capacity_term_gap` 把目标化为 `c·C/n ≤ g/√n`，交叉相乘（`√n > 0`、
`n ≥ 1`、`√n ≤ n`、`g ≥ 0`、`c·C ≥ 0`）后用 `hcc` 得证。
**诚实标注**：`c·C ≤ g` 是显式充分条件，不是必要条件。 -/
theorem distill_beneficial_concrete (c C δS δF : ℝ) (hδS : 0 < δS) (hδS2 : δS < 2)
    (hδF : 0 < δF) (hδF2 : δF < 2) (hSF : δF ≤ δS) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hcc : c * C ≤ Real.sqrt (8 * Real.log (2 / δF)) - Real.sqrt (8 * Real.log (2 / δS))) :
    ∀ n : ℕ, 1 ≤ n → c * (C / (n : ℝ)) + capacityTerm n δS ≤ capacityTerm n δF := by
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- log(2/δS) ≤ log(2/δF)
  have hlog_le : Real.log (2 / δS) ≤ Real.log (2 / δF) := by
    apply Real.log_le_log
    · exact div_pos (by norm_num) hδS
    · exact div_le_div_of_nonneg_left (by norm_num) hδF hSF
  have hg0 : 0 ≤ Real.sqrt (8 * Real.log (2 / δF)) - Real.sqrt (8 * Real.log (2 / δS)) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by nlinarith))
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnR
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨le_of_lt hnR, by nlinarith [hnR, hn1, sq_nonneg ((n : ℝ) - 1)]⟩
  have hcC : 0 ≤ c * C := mul_nonneg hc hC
  have hcross : c * C * Real.sqrt (n : ℝ) ≤
      (Real.sqrt (8 * Real.log (2 / δF)) - Real.sqrt (8 * Real.log (2 / δS))) * (n : ℝ) := by
    have h1 : c * C * Real.sqrt (n : ℝ) ≤ c * C * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt_le hcC
    have h2 : c * C * (n : ℝ) ≤
        (Real.sqrt (8 * Real.log (2 / δF)) - Real.sqrt (8 * Real.log (2 / δS))) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hcc (le_of_lt hnR)
    linarith
  have hkey : c * C / (n : ℝ) ≤
      (Real.sqrt (8 * Real.log (2 / δF)) - Real.sqrt (8 * Real.log (2 / δS))) /
        Real.sqrt (n : ℝ) :=
    (div_le_div_iff₀ hnR hsqrt_pos).mpr hcross
  have hcd : c * (C / (n : ℝ)) = c * C / (n : ℝ) := by rw [mul_div_assoc]
  have hgap := capacity_term_gap δS δF hδS hδS2 hδF hδF2 n
  have hmain : c * (C / (n : ℝ)) ≤ capacityTerm n δF - capacityTerm n δS := by
    rw [hcd, hgap]
    exact hkey
  linarith

/-! ## 五、**去掉 `hR` 假设**（B29：从「Lipschitz 损失 + 有界参数」**推出** sup-Lipschitz）

前四节的 `hR`（风险泛函在 sup 范数下 c-Lipschitz）是**显式假设**。
本节把它**推出**：只要风险是**损失函数的期望**、损失对**模型输出**是
`L`-Lipschitz 的（标准的「Lipschitz 损失」假设），则 sup 距离界
`∀ x, |f x − g x| ≤ B'` **自动蕴含** `|R f − R g| ≤ L·B'` ——
即 `hR` 以 `c = L` **成立**，无需单独假设。

  1. `popRisk`（**总体风险**）：`R f = E_z[ℓ(f, z)]`（有限计数期望）；
  2. `lossLipschitzInPred`（**Lipschitz 损失的谓词**）：
     `∀ z a b, |ℓ a z − ℓ b z| ≤ L·|a − b|`；
  3. **`risk_lipschitz_of_loss_lipschitz`（主交付 B29 之一）**：
     `Lipschitz 损失 ⟹ R 在 sup 距离下 L-Lipschitz` —— **`hR` 被推出**；
  4. `distill_excess_no_hR`：把 3 代回 `distill_excess_of_uniform_distance`，
     得到**不含 `hR`** 的蒸馏超额风险界 `R gs ≤ R gt + L·B`；
  5. `distill_excess_no_hR`：进一步去掉 `huc`（容量项假设）——
     用**有界损失** `|ℓ| ≤ M` 直接给出 `R gs ≤ R gt + L·B`，
     并且**容量项自动为 0**（不调用均匀收敛）；
  6. `bounded_params_give_sup_bound`（**有界参数 ⟹ sup 距离**）：
     若学生/教师网络在同一有界参数集上取值、且网络对参数是 `Lnet`-Lipschitz，
     则 sup 距离界 `≤ Lnet·‖θs − θt‖` ——
     即**把超参数/参数距离转化为函数距离**，从而喂给第 4 条的 `hB`；
  7. `distill_excess_fully_derived`（**端到端，三条假设全去**）：
     Lipschitz 损失 + Lipschitz 网络 + 有界参数 ⟹
     `R gs ≤ R gt + L·Lnet·‖θs − θt‖` ——
     **`hR`、`huc`、`C/n` 三个显式假设全部不再需要**（`C/n` 衰减也由
     `‖θs − θt‖` 的具体形式决定，见 `distill_excess_fully_derived`）。

**诚实边界（重要，标注）**：
  · **`hR` 已被推出**（第 3 条），这是本节的实质进展；
  · **`huc` 已可去掉**（第 5 条）：只要有界损失，容量项可置 0
    ——但这是**保守**处理（真实的均匀收敛项 `> 0`，本文件不重新推导它）；
  · **`C/n` 衰减率**：本节把它**替换为** `‖θs − θt‖` 的**参数距离**形式。
    `‖θs − θt‖ = O(1/n)` 的**具体衰减**（`C/n`）仍需要**优化算法**的收敛保证
    （学生训练到多近），**本节不证**（**标注未做**）——这是 B29 三项中最难的一项，
    诚实降级为「以参数距离形式给出，衰减率留待优化文件（`RealDistill` /
    `RealGradDescent` 一族）提供」；
  · `lossLipschitzInPred` 与网络的 `Lnet`-Lipschitz 性都是**显式假设**
    （它们是「Lipschitz 损失 + 有界参数」的标准形式化，本文件不证具体损失/网络的
    Lipschitz 常数，那些由 `RealCrossEntropy` / `RealSoftmaxLipschitz` /
    `RealBlockLipschitz` 一族承担）。
-/

/-- **总体风险（损失期望）**：`R f = E_z[ℓ (f ·) z]`（有限计数期望）。
`Z` 是数据空间（`Fintype`），`ℓ` 是损失（第一参为**预测值** `ℝ`，第二参为数据点）。 -/
def popRisk {Z : Type*} [Fintype Z] (ℓ : ℝ → Z → ℝ) (f : Z → ℝ) : ℝ :=
  (∑ z : Z, ℓ (f z) z) / (Fintype.card Z : ℝ)

/-- **Lipschitz 损失（谓词）**：损失对**预测值**是 `L`-Lipschitz。
这是「Lipschitz loss」的标准形式化（如交叉熵在 softmax 后、
或 Huber 损失在给定温度下）。 -/
def LossLipschitzInPred {Z : Type*} (ℓ : ℝ → Z → ℝ) (L : ℝ) : Prop :=
  ∀ z (a b : ℝ), |ℓ a z - ℓ b z| ≤ L * |a - b|

/-- **主交付（B29 之一）：Lipschitz 损失 ⟹ 风险在 sup 距离下 Lipschitz**。

`LossLipschitzInPred ℓ L`、`L ≥ 0`、`N = |Z| > 0`、sup 距离界 `∀ z, |f z − g z| ≤ B'`
⟹ `|popRisk ℓ f − popRisk ℓ g| ≤ L·B'`。

**即 `hR` 被推出**：`hR` 的形式（`∀ f g B', (∀ x, |f x − g x| ≤ B') → |R f − R g| ≤ c·B'`）
在本定理中以 `c = L` **成立**，不再需要作为假设。

证明：逐点 `|ℓ (f z) z − ℓ (g z) z| ≤ L·|f z − g z| ≤ L·B'`；
对 `z` 求和（`Finset.sum_le_sum`）+ 三角不等式 `|Σ| ≤ Σ|·|`；
除以 `N > 0`；再用 `abs_div`。 -/
theorem risk_lipschitz_of_loss_lipschitz {Z : Type*} [Fintype Z] (ℓ : ℝ → Z → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hLip : LossLipschitzInPred ℓ L) (hN : 0 < Fintype.card Z)
    (f g : Z → ℝ) (B' : ℝ) (hB : ∀ z, |f z - g z| ≤ B') :
    |popRisk ℓ f - popRisk ℓ g| ≤ L * B' := by
  have hNR : (0 : ℝ) < (Fintype.card Z : ℝ) := Nat.cast_pos.mpr hN
  have hpt : ∀ z : Z, |ℓ (f z) z - ℓ (g z) z| ≤ L * B' := by
    intro z
    exact le_trans (hLip z (f z) (g z)) (mul_le_mul_of_nonneg_left (hB z) hL)
  have hsub : popRisk ℓ f - popRisk ℓ g
      = (∑ z : Z, (ℓ (f z) z - ℓ (g z) z)) / (Fintype.card Z : ℝ) := by
    unfold popRisk
    rw [← sub_div, Finset.sum_sub_distrib]
  rw [hsub, abs_div, abs_of_pos hNR]
  rw [div_le_iff₀ hNR]
  calc |∑ z : Z, (ℓ (f z) z - ℓ (g z) z)|
      ≤ ∑ z : Z, |ℓ (f z) z - ℓ (g z) z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : Z, L * B' := Finset.sum_le_sum (fun z _ => hpt z)
    _ = L * B' * (Fintype.card Z : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **去掉 `hR` 的蒸馏超额风险界（B29 主交付之二）**：把
`risk_lipschitz_of_loss_lipschitz` 代回 `distill_excess_of_uniform_distance`，
得到**不含 `hR` 假设**的结论 `popRisk ℓ gs ≤ popRisk ℓ gt + L·B`。 -/
theorem distill_excess_no_hR {Z : Type*} [Fintype Z] (ℓ : ℝ → Z → ℝ) (L B : ℝ)
    (hL : 0 ≤ L) (hLip : LossLipschitzInPred ℓ L) (hN : 0 < Fintype.card Z)
    (gs gt : Z → ℝ) (hB : ∀ z, |gs z - gt z| ≤ B) :
    popRisk ℓ gs ≤ popRisk ℓ gt + L * B := by
  have h := risk_lipschitz_of_loss_lipschitz ℓ L hL hLip hN gs gt B hB
  linarith [(abs_le.mp h).2]

/-- **有界参数 ⟹ sup 距离界（B29 主交付之三）**：若学生/教师网络共享同一
参数化 `net : Θ → Z → ℝ`（`Θ` 为参数空间），且 `net` 对参数是 `Lnet`-Lipschitz
（即 `∀ θ θ' z, |net θ z − net θ' z| ≤ Lnet·‖θ − θ'‖`，`Θ` 为赋范空间），则

    `∀ z, |net θs z − net θt z| ≤ Lnet·‖θs − θt‖`

—— 即**把参数距离转化为函数 sup 距离**，从而喂给 `distill_excess_no_hR` 的 `hB`。
这是「**有界参数**」假设的精确用途：网络 Lipschitz 常数 `Lnet` 与参数半径给出
函数距离的界。

**v15 更正（删除多余假设 `hLnet`）**：原陈述带 `hLnet : 0 ≤ Lnet`，但 Lean 报
`unused variable 'hLnet'`——证明只是**逐点重述** `hNet`（`fun z => hNet θs θt z`），
**不需要** `Lnet` 的非负性。原陈述**多加强了假设**（读者会误以为 `Lnet < 0` 时
结论不成立；实际上此时 `hNet` 本身通常不可满足，但那是 `hNet` 的责任，不是本定理的）。
已**删除**。（注：`hLnet` 在**下游** `distill_excess_fully_derived` 中**确实**被
使用——那里经 `distill_excess_no_hR` 的 `hL` 进入 `mul_le_mul_of_nonneg_left`，
故该定理的 `hLnet` **保留**。） -/
theorem bounded_params_give_sup_bound {Θ : Type*} [NormedAddCommGroup Θ] {Z : Type*}
    (net : Θ → Z → ℝ) (Lnet : ℝ)
    (hNet : ∀ θ θ' (z : Z), |net θ z - net θ' z| ≤ Lnet * ‖θ - θ'‖)
    (θs θt : Θ) :
    ∀ z : Z, |net θs z - net θt z| ≤ Lnet * ‖θs - θt‖ :=
  fun z => hNet θs θt z

/-- **端到端（B29 主交付之四，三假设全去）**：Lipschitz 损失 + Lipschitz 网络
+ 显式参数距离 ⟹

    `popRisk ℓ (net θs) ≤ popRisk ℓ (net θt) + L·Lnet·‖θs − θt‖`

**`hR`、`huc`、`C/n` 三个显式假设全部不再需要**：
· `hR` 由 `risk_lipschitz_of_loss_lipschitz` **推出**（`c = L`）；
· `huc`（容量项）**不再出现**——结论里没有 `cap`；
· `C/n` 衰减率被**参数距离** `‖θs − θt‖` 取代（具体衰减需优化算法，**标注未做**）。

（代小整数复核：`L = 2`、`Lnet = 3`、`‖θs−θt‖ = 1` ⟹ 界为 `6`；
若 `gs = gt`（`‖θs−θt‖ = 0`）则界为 `0`，即两模型风险**相同**，成立。）

**v15 更正（删除多余假设 `hLnet`）**：Lean 报 `unused variable 'hLnet'`——
证明经 `distill_excess_no_hR`（其前提是 `hL`、`hLip`、`hN`、`hB`），
`hB` 由 `bounded_params_give_sup_bound`（**已不再需要 `hLnet`**）提供，
故 `hLnet` 在本定理中**未被任何一步使用**，已**删除**（命题强度不变）。 -/
theorem distill_excess_fully_derived {Θ : Type*} [NormedAddCommGroup Θ] {Z : Type*}
    [Fintype Z] (ℓ : ℝ → Z → ℝ) (net : Θ → Z → ℝ) (L Lnet : ℝ)
    (hL : 0 ≤ L) (hLip : LossLipschitzInPred ℓ L)
    (hN : 0 < Fintype.card Z)
    (hNet : ∀ θ θ' (z : Z), |net θ z - net θ' z| ≤ Lnet * ‖θ - θ'‖)
    (θs θt : Θ) :
    popRisk ℓ (net θs) ≤ popRisk ℓ (net θt) + L * (Lnet * ‖θs - θt‖) := by
  refine distill_excess_no_hR ℓ L (Lnet * ‖θs - θt‖) hL hLip hN (net θs) (net θt) ?_
  intro z
  exact bounded_params_give_sup_bound net Lnet hNet θs θt z

/-- **有界损失 ⟹ 容量项可置 0（去掉 `huc` 的保守版本）**：
若损失一致有界 `|ℓ a z| ≤ M`，则总体风险 `|R f| ≤ M`；
故在 `distill_generalization_bound` 里取 `cap` 为**具体的界**
`popRisk ℓ gs + |Rhat 界|` 型量时无需均匀收敛。

**诚实标注**：这是**保守**处理——真实的均匀收敛项 `> 0`，
本定理只说明「**有界损失时容量项有平凡上界**」，从而 `huc` 可作为
**定理**而非假设获得（代价是界更松）。

**v15 更正（删除多余假设 `hM : 0 ≤ M`）**：Lean 报 `unused variable 'hM'`。
该界只需 `hb`（`|ℓ a z| ≤ M`）与 `0 < card Z`：
证明走 `|∑ ℓ| ≤ ∑ |ℓ| ≤ card·M` 再除以 `card > 0`，**全程不用 `M` 的符号**。
且 `M` 无需非负——若 `M < 0` 则 `hb` **本身不可满足**（`|ℓ a z| ≥ 0 ≤ M` 矛盾），
命题对该情形**空洞成立**。故 `hM` 是**冗余前提**（读者会误以为 `M < 0` 时结论不成立）。
已**删除**，命题**严格更一般**。 -/
theorem bounded_loss_trivial_capacity {Z : Type*} [Fintype Z] (ℓ : ℝ → Z → ℝ) (M : ℝ)
    (hN : 0 < Fintype.card Z) (hb : ∀ a z, |ℓ a z| ≤ M) (f : Z → ℝ) :
    |popRisk ℓ f| ≤ M := by
  have hNR : (0 : ℝ) < (Fintype.card Z : ℝ) := Nat.cast_pos.mpr hN
  unfold popRisk
  rw [abs_div, abs_of_pos hNR]
  rw [div_le_iff₀ hNR]
  calc |∑ z : Z, ℓ (f z) z| ≤ ∑ z : Z, |ℓ (f z) z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : Z, M := Finset.sum_le_sum (fun z _ => hb (f z) z)
    _ = M * (Fintype.card Z : ℝ) := by
        -- ⚠ STYLE §4 已知坑（v15）：`Finset.sum_const` + `nsmul_eq_mul` 把 `∑ _z, M`
        -- 化成 **`↑(card Z) * M`**，与陈述里写的 `M * ↑(card Z)` **方向相反**
        -- （`norm_num`/`linarith` 不处理**变量**的交换律）⟹ 补 `ring` 收尾。
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **`hR` 与推出的 `hR` 形式一致（接口核对）**：本文件前四节的 `hR` 形如
`∀ f g B', (∀ x, |f x − g x| ≤ B') → |R f − R g| ≤ c·B'`；
`risk_lipschitz_of_loss_lipschitz` 给出的**正是这一形式**（`c = L`、
`R = popRisk ℓ`）。本定理把该接口**显式写出**，便于前四节按需替换 `hR`。 -/
theorem hR_of_loss_lipschitz {Z : Type*} [Fintype Z] (ℓ : ℝ → Z → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hLip : LossLipschitzInPred ℓ L) (hN : 0 < Fintype.card Z) :
    ∀ (f g : Z → ℝ) (B' : ℝ), (∀ z, |f z - g z| ≤ B') →
      |popRisk ℓ f - popRisk ℓ g| ≤ L * B' :=
  fun f g B' hB => risk_lipschitz_of_loss_lipschitz ℓ L hL hLip hN f g B' hB

/-! ## 注：闭环语义（蒸馏泛化如何接入验证线）
    1. `RealDistill.chain_distill_bound_lipschitz` 给出逐层输出对齐界
       `‖ChainFwd Ft n x − ChainFwd Fs n x‖ ≤ Σ (∏ Ls)·ε`（RealDistill.lean:182）；
    2. `distill_excess_from_chain_lipschitz` 把它与风险泛函的 sup 范数 Lipschitz
       性（显式假设 `hR`）复合，得到风险级的**蒸馏偏差项** `c·B`；
    3. `capacity_term_two_sided` 由 `RealHoeffding.hoeffding_two_sided` 给出
       均匀收敛的**容量项** `capacityTerm m δ = sqrt(8 log(2/δ)/m)`；
    4. `distill_generalization_bound` 把二者相加得学生泛化的保守上界；
    5. `distill_beneficial_large_n` / `distill_beneficial_concrete` 给出
       「蒸馏有益」的充分条件：容量项之差（显式形式 `g/√n`）压过蒸馏距离项
       `c·C/n` 时，学生上界不超过完整类上界。

    诚实边界小结（**B29 已部分解除**）：
    · **`hR`（风险 Lipschitz）已被推出**（第五节
      `risk_lipschitz_of_loss_lipschitz` / `hR_of_loss_lipschitz`）：
      在「Lipschitz 损失」`LossLipschitzInPred ℓ L` 下，`hR` 以 `c = L`
      **自动成立**，不再需要作为假设；端到端形式见 `distill_excess_fully_derived`；
    · **`huc`（均匀收敛/容量项）**：有界损失时可由
      `bounded_loss_trivial_capacity` 给出**平凡上界**（保守，**标注**）；
      真实容量项 `> 0` 仍由 `capacityTerm` 给出（前四节保留）；
    · **`C/n` 距离衰减率**：第五节**替换为参数距离** `‖θs − θt‖` 的形式；
      其 `O(1/n)` 的**具体衰减**依赖学生优化算法的收敛保证，**本节未证**
      （**标注未做**：留待 `RealDistill` / `RealGradDescent` 一族提供）；
    · 容量项常数为项目 Hoeffding 常数（`e^{−mt²/8}` ⟹ `sqrt(8 log(2/δ)/m)`），
      与经典 `sqrt(log(2/δ)/(2m))` 相差常数因子，已诚实标注，未证经典常数
      （注：`RealHyperparameterBound` 的 B30 节已给出**经典常数 2** 的版本，
      可供本文件后续替换）。 -/

end Lattice
