import Mathlib

import Lattice.Lib.Compiler.RealLv00CompilerLanguage
import Lattice.Lib.Compiler.RealLv00CompilerIR
import Lattice.Lib.Compiler.RealLv00CompilerCodegen
import Lattice.Lib.Compiler.RealLv00CompilerReal
import Lattice.Lib.Compiler.RealLv00CompilerSpec
import Lattice.Lib.Compiler.RealLv00CompilerSat
import Lattice.Lib.Compiler.RealLv00CompilerHonesty
/-!
# LATTICE / Lv-00 采集（H3）：编译正确性 / IR / 代码生成

## 采集来源

| 项 | 值 |
|:--|:--|
| 仓库 | `https://github.com/level0000x/Lv-00`（public，`master`，末次推送 2026-09-08） |
| 子树 | **`lv-merged/`**（Lean 4 / `leanprover/lean4:v4.14.0`，与本项目一致） |
| 原模块 | `lvFormal/Theory/` 下：`CompilerCorrectness.lean`(750 行/17 定理)、`Compiler.lean`(188/9)、`CodegenCorrectness.lean`(209/9)、`Codegen.lean`(233/6)、`IR.lean`(187/4)、`lvLang.lean`(223/10)、`Cv00Lang.lean`(280/6)、`Cv00Memory.lean`(149/11)、`ProofCompilerTheory.lean`(152/10)、`MetaVerificationTheory.lean`(89/9)、`EndToEndCorrectness.lean`(72/7)、`NormalizationProperties.lean`(46/3) |
| 依赖 | mathlib `rev = 4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`（= v4.14.0），**与本项目同一 rev** |
| 命名空间 | 原 `lvFormal.Theory.*` → 本文件 `Lattice.Lv00.Compiler`（与 `Lattice.*` 不冲突） |
| 采集理由 | 编译正确性 / IR / 代码生成是**与项目目标（转换层 = Compiler 意义上的转换）最直接相关**的一组素材：它给出「源语言 → IR → C 子集」三级编译管道的**形式化骨架**，以及若干**可复用的归约引理**（变量依赖性、编译来源追踪、图可满足性拼合）。 |

## 三分类判别（逐条，见 §9 清单）

Lv-00 的形式化大量处于**规格声明阶段**（其文件头自述 *「多数为规格声明…以构造性示例和代数恒等式为主」*）。
本文件逐条判别并**只保留 (A)(B)**：

| 类 | 含义 | 本包条数（机器核实，见下） |
|:--|:--|--:|
| **(A) 真结果** | 证明体实质（结构归纳 / 非平凡改写 / 真实胶合论证） | **13 条定理** |
| **(B) 规格声明** | 证明平凡（`rfl` / 一句 `simp`），但**定义与命题形式有价值** | **9 条定理 + 15 条定义/结构/归纳类型** |
| **(C) 无价值** | 占位（`True` 型「定理」）、带 `sorry`、或与 mathlib / 本项目重复 | **丢弃 47+ 条（§9）** |
| **§7 诚实降级** | 本项目新增的**机器验证反例**（**非 Lv-00 原产**） | **10 条定理** |

上表的 A / B / §7 降级三档**并不穷尽**本文件的 `theorem`/`lemma`：另有 1 条辅助引理
`empty_graph_satisfiable`（§2，空图恒可满足）**不计入 A/B/C/§7 任何一档**——它证明平凡（构造退化
环境 + 空列表消解），因而不满足 (A) 的「证明体实质」，也不在 (B) 的 9 条定理清单内，故单列为
第 33 条。<u>因此上表是「33 = 13 + 9 + 10 + 1 辅助」的前三档，而非完整分类</u>。（§8 把该条列作
与本项目 `symbolToWeight_empty` 的重复项，是另一维度的判定，与本表的分类维度不同。）

**(B) 的 9 条定理**：`compile_empty`；`stmt_compiled_edge_correct_{point,constraint,prove,normalize}`（4 条）；
`compile_constraint_degenerately_satisfied`、`compile_bridge_sem`、`compile_preserves_satisfiability`（3 条，**标注为空洞**）；
`compile_preserves_satisfiability_hypothesis_unused`（「证伪钉」）。
**(B) 的 15 条定义**：`VarName`/`Coord`/`lvPoint`/`lvConstraintKind`/`lvConstraint`/`lvStmt`/`lvProgram`/`State`/`initialState`/`addPoint`/`addConstraint`/`setProve`/`setNormalize`/`eval_stmt`/`eval_program`/`no_errors`/`satisfiable`（语义层）
与 `IRExpr`/`IRConstraint`/`ir_sem`/`ptX`/`ptY`/`dist`/`dot`/`cross`/`ConstraintGraph`/`graph_satisfied`/`graph_satisfiable`（IR 层）
与 `compile_point`/`compile_points`/`compile_constraint`/`compile_stmt`/`compile_program_go`/`compile_program`（编译层）。
**文件自重**：本文件共 **33 条 `theorem`/`lemma`**（13 A + 9 B + 10 降级 D + 1 辅助
`empty_graph_satisfiable`）、**0 `sorry`**、**0 `axiom`**。

## 诚实警告（本文件最重要的一段）

Lv-00 `CompilerCorrectness.lean` 文件头声称：

> *「本模块证明 lvLang → IR 编译器保持语义正确性 … 编译器保持可满足性（通过编译桥接引理）」*

**核实结论：这个声称被严重高估。** 该「可满足性保持定理」（`compile_preserves_satisfiability`）
的证明**完全无视源程序**：它构造退化环境 `fun _ => (0,0)`，并在该环境下**无关于源约束地**
满足编译产物。理由有三，均可机器验证（见 §5 与 §7）：

1. `compile_bridge_sem` 的证明只依赖 `compile_constraint` 的**输出形状**加退化环境的恒真性——
   它对**任意** `lvConstraint` 都成立，因为退化环境把所有点压成同一个点，
   使共线 / 垂直 / 中点 / 直角 / 等长等**全部**恒真；
2. 定理的假设 `lvLang.satisfiable (eval_program initialState prog)` 展开后是 `State.errors = []`，
   即一个**纯语法**的良构性条件（无重复点名等），**不含任何几何内容**——它**根本没被用到**；
3. 因此该「可满足性保持」是**平凡真**的：它为**每一个**程序成立，与编译器的正确性无关。

真正的「编译保持语义」（同一环境下 源约束 ⟺ 编译产物）在 Lv-00 中**不成立**，
本文件 §7 给出**机器验证反例**。

**引用纪律**：本文件中标注 `(A)`/`(B)` 的条目是**如实采集**；
§5 的桥接引理**按原样保留但明确标注为规格（近乎空洞）**；§7 的降级条目是本项目新增的**反例**，
不属于 Lv-00 原产。

**纪律**：不 `import lvFormal.*`（仅 `import Mathlib`，因此**零命名冲突**）；
无 `sorry`/`axiom`/`admit`；不修改任何既有 `.lean`。
-/

/-!
> **拆分说明（2026-10-15）**：本文件原含 **89 个声明**、1395 行。声明已按原有分节
> （一～七）拆入 7 个模块，本文件**改为 re-export 门面**：
>
> | 子模块 | 原行范围 | 声明数 |
> |:--|:--|--:|
> | `RealLv00CompilerLanguage` | 76–186 | 17 |
> | `RealLv00CompilerIR` | 187–307 | 13 |
> | `RealLv00CompilerCodegen` | 308–369 | 6 |
> | `RealLv00CompilerReal` | 370–645 | 17 |
> | `RealLv00CompilerSpec` | 646–968 | 20 |
> | `RealLv00CompilerSat` | 969–1233 | 6 |
> | `RealLv00CompilerHonesty` | 1234–1307 | 10 |
> | **合计** | | **89** |
>
> 采用**连续切分**（每模块覆盖连续行区间并 import 紧邻前驱），实测本文件**零前向引用**，
> 故文件顺序即拓扑序，无需手写依赖表。
>
> 子模块已注册进 `lakefile.toml` 的 `roots`。
-/

/-! ## 八、与 mathlib / 本项目的重复清单

### 与 mathlib 重复（建议将来回收）

| Lv-00 定义 | mathlib 对应 | 说明 |
|:--|:--|:--|
| `dist (p q : ℝ × ℝ)` | `dist`（`PseudoMetricSpace`）、`EuclideanSpace ℝ (Fin 2)` | 本定义是 `Prod` 上的特化手写式，**重复建设** |
| `dot (p q : ℝ × ℝ)` | `inner`（`InnerProductSpace`） | 同上 |
| `graph_satisfied` / `graph_satisfiable` | `∀ c ∈ g, P c`（无专用名） | 薄包装，可保留 |
| `constraints_of_program` / `vars_of_program` | `List.flatMap`（已复用） | 无重复 |
| `cross` | `crossProduct`（3 维，`Mathlib.Analysis.InnerProductSpace.CrossProduct`） | 维度不同，**非重复** |

### 与本项目重复

| Lv-00 | 本项目 | 说明 |
|:--|:--|:--|
| `Compiler.compile_program`（逐约束映射） | `SymbolToWeightCorrectness.compileToLayer = cs.map convertVec` | **同一构型**（列表 map），但 Lv-00 **不保语义**，本项目**保语义** |
| `compile_program_append` | 无（本项目无拼接定理） | Lv-00 的**真**结果，可借鉴 |
| `ir_sem_depends_on_vars` | 无 | Lv-00 的**真**结果，可借鉴 |
| `empty_graph_satisfiable` | `symbolToWeight_empty` | 同为「空输入平凡成立」 |

### 命名冲突

本文件**只 import Mathlib**，故 `scripts/collision-pairs.txt` 的冲突面**完全规避**。

## 九、(C) 丢弃清单（47+ 条）

| 来源 | 丢弃内容 | 理由 |
|:--|:--|:--|
| `CodegenCorrectness.lean` | `codegen_sem_preserved`、`cgen_constraint_sem_preserved`、`cgen_graph_sem_preserved`、`eval_expr_matches`（**4 条，目标为 `True`**） | `:= by trivial`，内容空洞（机器核实：该文件 4 处 `: True := by`） |
| `CodegenCorrectness.lean` | `safe_stmt_never_aborts`、`cgen_graph_never_aborts` | 依赖 **`sorry`**（原文件第 173 行），**不可采集** |
| `ProofCompilerTheory.lean` | `proof_chain_validity`、`depth_consistency`、`export_format_semantics_preservation`、`coq_export_syntax_valid`、`lean4_export_syntax_valid`、`trace_event_ordering`、`trace_completeness`、`widget_layout_invariant`、`widget_registration_ordering`、`tactic_mapping_completeness`（**全部 10 条：目标为 `True` 8 条 + 证 `False` 2 条（`depth_consistency`、`lean4_export_syntax_valid`，结论是 `False` 而证明 `:= by trivial`）**） | 8 条**目标为 `True`**；另 2 条**结论退化为 `False`**（不计入 `True` 型）。结构定义（`ProofStepRecord` 等）属导出/UI 主题，非本包核心 |
| `MetaVerificationTheory.lean` | `meta_completeness` | 依赖 **`sorry`**（第 82 行） |
| `MetaVerificationTheory.lean` | `selfRefUnsat`、`godelNumber`、`metaVerifier`、`metaVerified` | 定义**退化为常量**（`:= False`、`:= 0`），无数学内容 |
| `EndToEndCorrectness.lean` | `safety_chain`、`ub_free_chain`、`evidence_chain`、`evidence_reliability_chain`、`full_pipeline_safety`、`zero_trust_pipeline`（**6 条，全部 `True`**） | `:= by trivial`，内容空洞（机器核实：6 处 `: True := by`） |
| `Cv00Memory.lean` | `exec_preserves_mem_if_no_call`、`points_to_env_correct_x`、`points_to_env_correct_y`、`points_to_env_defined_only`（**4 条 sorry**）、`satisfiable_bridge_to_cv00` | 依赖 **`sorry`**；且 `exec_stmt` 对 9 种语句中 **7 种直接返回 `.normal m env`**（无实际语义），`Cv00Memory` 整体不可用 |
| `Cv00Lang.lean` | 6 条定理（`eval_lit` 等） | **`(C)`**：`simp` 级字面量求值，属 H6 系统侧主题 |
| `Codegen.lean` | `cgen_graph_nonempty`、`cgen_add_const`、`cgen_var_preserves_name`、`cgen_dist_nonempty`、`cgen_collinear_nonempty`、`cgen_midpoint_nonempty`（**6 条**） | **`(C)`**：全是 `rfl`/`simp` 级「非空性」断言，无数学内容；且 `cgen_expr` **把 `IRExpr.const` 折叠为 `lit_float 0`**（数值信息丢失），其「正确性」声称不成立 |
| `NormalizationProperties.lean` | `normalization_idempotent`、`const_normalized`、`var_normalized` | **(A) 但属 H2 主题**（重写/规范化），本包不取；其 `normalize` 实质是恒等函数，主题归属 H2 |
| `FormulaSemantics.lean` | 5 条（公式语义） | 主题归属 H2（推理/语义），非编译管道核心 |
| `BootstrapCorrectness.lean` | 6 条 | 主题归属 H6（自举/系统侧） |
| 全局 | `CompilerTooling.lean` | **0 字节空文件** |

**合计丢弃**：`True` 型 18 条、`sorry` 依赖 7 条、`simp`/`rfl` 级无内容 6 条、常量退化定义 4 条、主题归属他包 11 条、空文件 1 个。

**逐行对账**：`True` 型 18 条 = `CodegenCorrectness` 4 + `ProofCompilerTheory` 8 + `EndToEndCorrectness` 6；
`sorry` 依赖 7 条 = `CodegenCorrectness` 2 + `MetaVerificationTheory` 1 + `Cv00Memory` 4；
`simp`/`rfl` 级无内容 6 条 = `Cv00Lang` 6；常量退化定义 4 条 = `MetaVerificationTheory` 4；
主题归属他包 11 条 = `NormalizationProperties` 3 + `FormulaSemantics` 5 + `BootstrapCorrectness` 6 …… 
（**待订正**：`NormalizationProperties` + `FormulaSemantics` + `BootstrapCorrectness` 实为 14 条，多于此处汇总的 11 条，
两者不自洽，尚未核实是哪一侧需要订正。）**另有 2 条未计入上述任何一档**：
`ProofCompilerTheory` 的 `depth_consistency` 与 `lean4_export_syntax_valid`，其结论为 `False`（证明 `:= by trivial`）——
既非 `True` 型，亦非 `sorry` / `simp` / `常量退化` / `主题归属他包`，故本汇总的档位划分**未覆盖该行全部 10 条**。

## 十、结论：与 `symbolToWeight_correct` 的关系

| 维度 | Lv-00 `compile_preserves_satisfiability` | 本项目 `symbolToWeight_correct` |
|:--|:--|:--|
| 陈述 | `satisfiable (eval prog) → graph_satisfiable (compile prog)` | `AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x` |
| 方向 | **单向** | **双向（⟺）** |
| 假设实质 | `errors = []`——**纯语法**，且**证明未使用** | `x : List Int` 为任意输入；**无额外假设** |
| 结论强度 | 存在**某个**环境满足（退化环境，与源无关） | 对**同一输入 `x`**，网络全零 ⟺ 全部约束满足 |
| 是否语义保持 | **否**（§7 D1 反例：数值载荷被丢弃） | **是**（`convertVec_preserves_semantics` 逐约束保语义） |
| 可复用性 | `compile_program_append`、`ir_sem_depends_on_vars`、`compile_append_satisfiable`、来源追踪 | `forall_mem_map_iff` 列表桥接 |

**结论（三条）**：

1. **两者不是同一命题**。Lv-00 的是「编译产物**可**满足」（∃ 环境，且是**与源无关**的退化环境）；
   本项目的是「编译产物在**给定输入**上**全零 ⟺ 源约束全满足**」。
   前者是**存在性且平凡**，后者是**逐点双向等价且非平凡**。
   ⇒ Lv-00 的这条**不能**充当本项目 `symbolToWeight_correct` 的素材或旁证。

2. **可借鉴的是「骨架」，不是「定理」**。本项目 `symbolToWeight_correct` 目前是
   `cs.map convertVec` 的**单层**形式，缺少：
   - **拼接律**（`compile (p1 ++ p2) = compile p1 ++ compile p2`）——Lv-00 `compile_program_append` 是**真结果**，可直接借形；
   - **变量不相交时的可组合性**——Lv-00 `compile_append_satisfiable` + `ir_sem_depends_on_vars`
     的「分片环境」论证是**真结果**，可为「多层/多模块网络编译」的模块化正确性提供**技术路线**；
   - **来源追踪**（编译产物必定来自源约束）——Lv-00 `compile_program_contains_compiled_constraints` 是**真结果**，
     对应「网络神经元必定来自某条约束」，是反向提取（`WeightToSymbolEquivalence`）的**对偶骨架**。

3. **Lv-00 的「可满足性保持」是一个反面教材**：它展示了
   *「用一个退化模型证明存在性」* 如何产生一条**看起来像编译器正确性、实则与编译器无关**的定理。
   本项目应引以为戒：任何「编译保持语义」定理**必须**是**同环境/同输入**的逐点等价，
   且必须**实际使用**源程序的语义（而非语法良构性）。
-/
