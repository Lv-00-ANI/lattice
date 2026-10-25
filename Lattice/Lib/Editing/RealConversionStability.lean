import Mathlib
import Lattice.Lib.Compiler.RealNonlinearCompile
import Lattice.Lib.Editing.RealNonlinearExtract
import Lattice.Lib.Optim.RealSecondOrderNoModulus
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Editing.RealRoundtripBound
import Lattice.Lib.LinearAlgebra.RealSpectralRadius
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.Architectures.RealNormStability
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealDataProcessing
import Lattice.Lib.Optim.RealConversionStabilityConvergence
import Lattice.Lib.Quantization.RealConversionStabilityFloatBounds
import Lattice.Lib.Editing.RealConversionStabilityReversibility
import Lattice.Lib.Editing.RealConversionStabilityInformation
/-!
# LATTICE: 转换层的稳定性、可微性与浮点正确性 —— 把本轮数学资产回喂到符号⇄权重主线

> **拆分说明（2026-10-14）**：本文件原先含 **58 个声明**、约 1922 行。这 58 个声明已按主题
> 拆入 4 个子模块，本文件**改为纯 re-export 门面**，自身不再声明任何东西：
>
> | 子模块 | 声明数 |
> |:--|--:|
> | `RealConversionStabilityConvergence` | 23 |
> | `RealConversionStabilityFloatBounds` | 20 |
> | `RealConversionStabilityReversibility` | 9 |
> | `RealConversionStabilityInformation` | 6 |
> | **合计** | **58** |
>
> **为什么改**：首次拆分是「复制声明、保留原文件」，实测导致 58 个声明**各存在两份**
> （116 个），既使 `STATS.md` 的规模数字重复计数，也让两份副本可能各自漂移。
> 现在声明**只在子模块中定义一次**。保留本文件是为了让 `import RealConversionStability`
> 继续有效——所有 4 个子模块都在 `namespace Lattice` 内，限定名不变。

## 定位（本文件为何存在）

E1 审计的核心发现是：本轮新增的 100+ 模块（浮点/IEEE-754、SSM、GNN、因果、OT、
决策论、凸分析…）大多是**尚未与 `符号 ⇄ 权重` 转换主线建立引用关系**的数学资产；
主线当前的"保真度"论断（`RealRoundtripBound`、`RealNonlinearCompile`）只用到了
很初级的不等式（一次 Lipschitz 界、逐点等价）。

本文件把**已经验证过的分析工具**回喂到转换层，每条回喂都给出一个**新结论**
（不是"我 import 了 X"）。共四条：

  1. **可微性/光滑性回喂（第一节）**：`RealNonlinearCompile` / `RealNonlinearExtract`
     的收敛论述此前只有「逐点等价 + 初等 Lipschitz」。本节用
     `RealSecondOrderNoModulus.exists_modulus_of_posDef`（点式正定 ⟹ 显式模数）
     证明：**模数 ⟹ GD 映射是压缩 ⟹ 不动点唯一 + 几何收敛率 `c^n`**；
     给出**复合（多层）收敛率的乘性法则**；给出 `RealNonlinearExtract` 侧的
     闭包算子代数与**精确不动点刻画**；最后给出 `piecewiseCompile` 的
     **闭式 Lipschitz 常数**与**区间连续性二分法**。
  2. **浮点正确性回喂（第二节）**：把 `RealCompileFloatCorrectness` 的误差界
     `n·κ^(2n+1)·((1+eps)·mag + tiny)` **实例化到 doc/03 的 `lv_compile`**
     （约束集 → 单层网络）**与 `lv_extract`（提取）**上，
     并证明**编译-提取闭环**的误差仍是 `n·κ^expo·B` 形、给出**放大率**；
     把 `lv_verify` 的判定翻转阈值钉死；给出编译优化的**安全域**原理；
     最后给出「浮点零化判据失效」**可证的那一半**与**缺的桥**。
  3. **稳定性回喂（第三节）**：在**算子范数/谱半径界**下给出
     **Neumann 型闭式稳定性定理**：`‖T‖ < 1 ⟹ ∑_m ‖T^m‖ ≤ 1/(1−‖T‖)`
     （从而**重构算子可逆**），配合 `RealRoundtripBound` 的线性误差传播得到
     「提取方程组解的扰动 `≤ L·ε`」（`L` 由算子范数/谱半径界给出）；
     对角情形用 `RealSpectralRadius` 的 `ρ̂(d) = ‖diag d‖` 给出**可实例化**版本；
     并用 `RealNormStability` 证明**提取前的安全归一化不放大**。
     §3.2 还给出**退化分析**：`extractReal` 是恒等，故"把提取当线性算子"的
     直接读法**无信息**，稳定性分析的正确载体是**重构求解器**。
  4. **信息论回喂（第四节）**：DPI 链 `KL → tv → 每坐标误差` 给出
     **提取精确 ⟹ 权重逐分量精确**（这是熵单纯性的信息论证明）；
     给出 DPI 的**等号刻画**独立复算；并给出**「压缩不损失可行性」为假**的
     机器验证反例。

## 诚实边界（本文件不证 / 不声称的；统一关键词：诚实/未做/降级/标注）

- **第一节的"唯一不动点"是关于 `gdStep`（梯度下降映射）的**，不是关于
  `closureOperator` 的——后者有整整一族不动点（每个闭集都是），
  把它写成"不动点唯一"会是**假命题**（见 `extract_fixpoints_many`）。
- **不动点的存在性未证**：本节只给"**至多**一个"（`contraction_fixpoint_unique`）
  与"给定不动点时的收敛率"（`gd_error_le_geometric`）。完整压缩映射原理
  所需的完备性 + 迭代构造**未做**（本文件走 `RealConvergence` 的 ε-终止路线）。
- **二阶导的 Fréchet 对齐未做**：真正的 Hessian `fderiv ℝ (fderiv ℝ F x) x`
  与本节使用的抽象 `H` / `g` 之间的桥接，仍是 `RealTaylorMultivariate` 与
  `RealHessian` 已标注的缺口；本文件不重复该桥接，也不声称补齐。
- **第二节的浮点模型是 `RealFloatFormat` 的抽象 `RoundOp`**（相对误差界 + 幂等），
  **不建模 IEEE 逐位语义**（NaN/Inf/舍入模式/指数偏置）——这是既有模块的显式
  抽象降级，本文件继承之，不用 `RealIEEE754` 做更细的建模。
  另外：**`lv_compile` 把同一输入 `x` 喂给每条约束对应神经元的权重**
  （`compileNeuron` 的语义选择，与 `doc/03` 的 `lv_compile` / `lv_neuron_out` 一致）；
  原 Lean 定义 `compileToLayer` 的输入是列表，本文件用 `Fin k` 索引做了对齐，
  该对齐**显式写在类型里**而非隐含。
- **第二节的 `Expr` 与 `lv_compile` 不是同一个语法对象**：本文件用
  `Expr.var 0` 为每条编译约束的神经元权重做**同一数值的赋值**，从而把
  `compile_error_bound` 从「表达式语义」落到「编译函数语义」。
  这是**实例化**（instantiation），不是同一性（identity）——如实标注。
- **第三节的 `T`（置信度 / 交叉项矩阵）是"提取残差算子"的模型**：
  3.1 节如实指出，`RealRoundtripBound.extractReal` 在
  `RealNeuron → RealConstraint` 上**真的就是恒等**（只拷系数），
  故"把提取当线性算子"的直接读法是**退化的**（`T = 1`、`ρ = 1`，界无信息）。
  3.2 节因此把稳定性结论放在**重构 / 最小二乘求解器**上（`M = 1 − T`），
  这才是转换层真正会遇到的算子。
- **第三节的输出空间限于 `n ≥ 1`**：`gelfandRadius` / `diagRadius` 需要
  `Nonempty (Fin n)`；`n = 0` 的退化情形**降级排除**。
- **第四节「压缩不损失可行性」被证明为假**（`compression_not_feasible_preserving`）：
  这是**负面结论**，按 STYLE §5.6 如实登记为反例。
  - **⚠ ~~实测发现：`RealCompileFloatCorrectness.lean` 的 docstring 与它的真实声明集不符~~**
    **⭐ C-12 复核：本条指控【已失效】。**
    `RealCompileFloatCorrectness.lean` 的 **`:33-56`** 现在**自己列出**全部未落地项
    （「本轮**未能落地**的部分（诚实标注…）」，逐条点名 `MagPair` / `mul_error_bound` /
    `div_error_condition_factor` / `TranscendentalOp` 等，并明说「这些声明在文件中不存在，
    引用它们会构建失败」）。**下面这段描述因此不再是「不符」，而是「该文件已自我声明」。**
    ⭐ 保留本段是为了记录**该指控曾成立、后由对方文件自身修正**；
    行号亦已过期（原文的「该文件头部」现为 §未能落地）。
    ⚠ **不要**据此再次立项「docstring 与声明集不符」。
  该文件头部把下列 6 项列为"交付"：
  `compile_error_bound_pure`（项 7）、`compile_exact_of_zero_ops`、
  `mul_error_bound`（项 8）、`mul_mag_pair_bound`（项 9）、
  `foldOpt` / `deadOpt` / `cseOpt` / `opt_error_bound_invariant` /
  `expanded_opt_error_bound_invariant`（项 10）、`div_error_condition_factor`（项 11）、
  `TranscendentalOp` / `transcendental_error_bound`（项 12）。
  **这些声明在文件中一个都不存在**：该文件的真实声明集为
  `Expr` / `evalReal` / `evalFloat` / `numOps`(+5 条 rfl 引理) / `mag`(+5 条引理) /
  `abs_round_le` / `abs_round_le_growth` / `round_growth_contract` /
  `evalReal_abs_le_mag` / `evalFloat_abs_le_mag` / `hasMul` / `expo`(+5 条 rfl 引理) /
  `compile_error_bound`——**共 1 条核心定理**。
  另外 docstring 描述的 `mag` 在 `mul` 上是 `max(Ma,Ma')·max(Mb,Mb')`、
  指数是 `n_ops`，而**真实实现**是乘积形式 `mag A a * mag A b`、指数是 `expo e = 2·numOps e + 1`。
  本文件因此**不引用**这些不存在的名字，并在 §2.2 把"优化不使界变差"改为
  可证的**抽象安全域原理**（`lv_compile_optimization_invariant`）。
  **缺的桥**：`RealCompilerOpt`（有自己的表达式类型）与
  `RealCompileFloatCorrectness.Expr` 之间的**类型桥接模块**尚未建立。
  **边界更新**：本文件已在 `lv_compile_optimization_safe`（见其定义处的
  `ceOps`/`ceMag` 两条等式义务）处**绕开**该桥——该定理把"优化不使界变差"
  归约为两条**可验证的等式义务**，其 docstring 明写这**不依赖**上述桥。
  因此该桥对本文件的结论**不再承重**，仅作为将来与 `RealCompilerOpt`
  对接时的**独立待办**保留（其建立与否不影响本文件已证结论）。
- **第三节不 import `RealGelfand`（依赖顺序降级，非数学缺口）**：
  本轮 `RealGelfand.olean` 在共享构建队列中尚未产生（源码已存在），
  为让本模块**独立可构建**，第三节只用**已构建**的 `RealSpectralRadius`
  （对角情形 `‖diag d‖ = ρ̂(d)`）。非对角矩阵的 `ρ(T) ≤ ‖T‖`
  已由 `RealGelfand.gelfand_radius_le_opNorm_general` 提供，本文件不重复；
  第三节的 Neumann 界本身**只用 `‖T‖ < 1`**，与 `ρ` vs `‖·‖` 之争正交。
- **第三节「`ρ(T) < 1` ⟹ Neumann 收敛」的完整链条未做**：本文件用 `‖T‖ < 1`
  这个**充分条件**。从 `ρ(T) < 1` 推到 `‖Tⁿ‖ → 0` 需要 Gelfand 极限定理的
  **复语境适配**——`RealGelfand` 文件头已明确标注为**未做**，本文件继承该边界。
- 全程无 `sorry` / `axiom` / `admit`；所有定理真实可证。
-/
