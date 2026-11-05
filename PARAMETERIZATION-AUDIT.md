# PARAMETERIZATION AUDIT —— 18 条「具体实例 vs 抽象角色」缺陷

> **唯一判据（贯穿全文）：**
>
> **这个对象是「具体实例」，还是「抽象角色」？**
>
> **如果是具体实例，那么这个具体选择就可能在某个方向上不够用。**
> **正确做法通常是**参数化**（用一个类型参数承载抽象角色），而不是换一个更具体的实例。**

**建立时间：第 135 轮之后**
**状态：18 条全部**已登记、未修**（除第 8 条已被 CIC 决定覆盖）**

---

## 0. 为什么这份清单存在

**第 134 轮完成了 C0（CIC 载体最小验证，V2 通过），第 135 轮完成了 C1 的前半（`Substitution`、`Reduction`）。**

**但同一类错误——**把某个抽象角色焊死在一个具体实例上**——在代码库中还有 18 处。**
**它们不是 bug：每一条单独看都能编译、能证明。它们是**表达力的天花板**：一旦某个方向需要更强的结构，选定的实例就不够用，而修改它要动整条链。**

**=> 这份文件把 18 条集中登记，好让后续每一轮能**按影响面**而不是按发现的偶然顺序来修。**

---

## 1. 一级：直接造成已知缺陷

### 1.1 `Weights` 选成了裸向量

| 项 | 内容 |
|:--|:--|
| **现状** | **`Weights` 是抽象参数；几何侧为 `ℕ → Pt n`** |
| **选成了什么** | **用「向量」承载「参数」这一抽象角色** |
| **后果** | **层、位置对应关系丢失，导致 `ChainSlot` 读不出 `MLayer`；T3 参数层只能做投影；导出规格无法定义** |
| **改法** | **`Weights A : A.Params → ℝ`，用 `Arch` 索引** |
| **影响面** | **T3、`ChainSlot`、`ModelArtifact`、G-1/G-3** |
| **难度** | **M–L** |

### 1.2 `State` 选成了 `K → Option ℕ`

| 项 | 内容 |
|:--|:--|
| **现状** | **`RState K := K → Option ℕ`（`Runtime/Model.lean:39`）** |
| **选成了什么** | **用「键值小整数」承载「运行时状态」** |
| **后果** | **无法承载 `Weights`、`Cert`、`Term`** |
| **改法** | **`State V := K → Option V`，`V` 可实例化为 `Weights`、`Cert` 或 `Eff`** |
| **影响面** | **T5–T8 全部** |
| **难度** | **M** |

### 1.3 `Effect` 选成了「单键覆写 + prev」

| 项 | 内容 |
|:--|:--|
| **现状** | **`{ key, value, prev }`（`Runtime/Model.lean:46`），`apply` 是单键覆写** |
| **选成了什么** | **用「一次写入」承载「任意状态变换」** |
| **后果** | **无法表达整层编译、不可逆、部分可逆** |
| **改法** | **`{ run : State → State, undo : State → State, mode : EffectMode }`；单键写入成为实例** |
| **影响面** | **T5、T7、T8** |
| **难度** | **M** |

### 1.4 `Term` 只有语法，未分 `Prop` / `Type` —— **已修（第 136 轮）**

| 项 | 内容 |
|:--|:--|
| **现状** | **~~`Core/CIC/Syntax.lean:83` 的 `Term` 有 `sort : Level → Term`~~** |
| **选成了什么** | **~~用「单一 term 宇宙」承载「规格 + 结构」~~** |
| **后果** | **~~`Spec`（命题）与 `Model`（结构）混在一起，T0 的「可类型性即可构造」失去区分~~** |
| **改法** | **✅ `inductive SortKind \| prop \| type`，`sort : SortKind → Level → Term`** |
| **影响面** | **C0、C1、C2** |
| **难度** | **M** |
| **状态** | **✅ 已完成。`Syntax.lean` 的 `Term.sort` 现在携带 `SortKind`；`Typing.typable_sort`、`subst`、`shift`、`encode` 全部同步。门禁的 `PROBES` 已更新为检查**旧**形状，并报告 `FIXED 4`。** |

**为什么这条必须最先定：`CARRIER-CIC.md` 的 T0 说「可满足性 = 可类型性」。若 `Spec` 与 `Model` 都是同一个 `Term`，那么「`t` 可类型化」对 `t` 是哪一个**什么也没说**——这条义务就会退化为同义反复。**
**=> `SortKind` 把两个角色在**语法层**分开，而不是靠约定。**

### 1.5 `Obligation.theoremName` 选成了 `String` —— **已部分修（第 137 轮）**

| 项 | 内容 |
|:--|:--|
| **现状** | **`theoremName : String`（`Plugins/Manifest.lean`），**现已并列 `proof : Option Prop`**** |
| **选成了什么** | **用「字符串」承载「定理引用」** |
| **后果** | **DAG 两条幽灵名（`denote_seq`/`denote_par` 实为 `dag_denote_seq`/`dag_denote_par`）；Norm 路径错配** |
| **改法** | **✅ `Obligation.proof : Option Prop` + `verifiedObligation` 构造器** |
| **影响面** | **`PluginProof`、`Manifest`、11 个插件** |
| **难度** | **S–M** |
| **状态** | **✅ 字段已加、构造器已加、DAG 三条已改为携带 `Prop`、两个幽灵名已修、`check_obligation_proofs.py` 已度量：**3 verified / 71 named**。** |

**为什么 `proof` 是**可选**的，以及这代价什么：**

**74 个 manifest 已经把定理名写成字符串。要让字段必填，要么一次性重写（无法保证正确），要么每个 manifest 填一个占位——**而占位就是原问题，只是下移了一层**。**

**⇒ 字段现在可选，`verifiedObligation` 是填它的构造器，门禁**度量**迁移而不是承诺迁移。**
**迁移目标：71 → 0。**

---

## 2. 二级：限制表达力，但暂无直接缺陷

### 2.1 `Arch` 选成了层列表

| 项 | 内容 |
|:--|:--|
| **现状** | **`Core/ModelArtifact.lean:98` 的 `Arch := { widths : List ℕ, acts : List Activation }`** |
| **选成了什么** | **用「线性层列表」承载「计算图」** |
| **后果** | **无法表达 DAG、残差、分支、共享权重；DAG 载体的 `dagPar = p ++ q` 退化是直接证据** |
| **改法** | **`Arch := { nodes : List Node, edges : List (Nat × Nat) }`；层列表是线性特例** |
| **影响面** | **DAG、Conv/Attention、五载体接 CIC** |
| **难度** | **M–L** |

### 2.2 `Behavior` 选成了函数

| 项 | 内容 |
|:--|:--|
| **现状** | **`Behavior` = `Input → Output`** |
| **选成了什么** | **用「确定性函数」承载「语义」** |
| **后果** | **无法表达概率、路由、约束满足、多步交互** |
| **改法** | **`Behavior` 改为关系或带效用的转移系统；函数是特例** |
| **影响面** | **`MODEL-WEIGHT.md §3`、T1/T2 的 `denote`** |
| **难度** | **M** |

### 2.3 `Spec` 选成了约束列表 —— **已被 CIC 决定覆盖**

| 项 | 内容 |
|:--|:--|
| **现状** | **`ExpressibleSpec n := { constraints : List (GeoConstraint n) }`** |
| **状态** | **`CARRIER-CIC.md` 已决定符号载体改为 CIC term，故本条**不需要单独修**——`List` 只是 `Encode/Geometry` 的一个实例** |
| **待确认** | **代码中不得再以 `List (GeoConstraint n)` 作为**主**形状** |

### 2.4 `ServiceKey` 选成了 `String`

| 项 | 内容 |
|:--|:--|
| **现状** | **`abbrev ServiceKey := String`（`Plugins/Manifest.lean:125`）** |
| **选成了什么** | **用「字符串」承载「能力键」** |
| **后果** | **版本化能力键在类型层不可表达；T6 的 provider 替换无法刻画** |
| **改法** | **`{ name : Name, version : Nat }` 或枚举** |
| **影响面** | **`PLUGIN-PROTOCOL.md`、T6** |
| **难度** | **S** |

### 2.5 `ResultEquiv` 选成了三支并列

| 项 | 内容 |
|:--|:--|
| **现状** | **`weights` / `behavior` / `approx ε` 三个构造子** |
| **选成了什么** | **用「并列三支」承载「等价关系族」** |
| **后果** | **没有强弱序，无法在 T7 里说「用哪一支」** |
| **改法** | **定义 `weights ≤ behavior ≤ approx` 的序，或参数化** |
| **影响面** | **`MODEL-WEIGHT.md §4`、T7** |
| **难度** | **S** |

---

## 3. 三级：结构问题（不是「对象选错」，而是「结构选错」）

### 3.1 `ProofComplete` 选成了扁平合取

| 项 | 内容 |
|:--|:--|
| **现状** | **23 项 `A ∧ B ∧ …`（`Lattice/Plugins.lean:480`）** |
| **选成了什么** | **用「扁平列表」承载「证明结构」** |
| **后果** | **无法表达依赖与核心/可选；`c6` 别名、T0 间接进入、`CPhaseAdditions` 这类「接线器」全是它造成的** |
| **改法** | **每个 obligation 声明 `requires`，闭合 = 依赖图拓扑闭合** |
| **影响面** | **`Plugins.lean`、`PROOF-OBLIGATIONS.md`** |
| **难度** | **M** |
| **与前序关系** | **H0 先清伪证明；结构改造在 H2 之后** |

### 3.2 插件是「目录」与「能力」只取其一

| 项 | 内容 |
|:--|:--|
| **现状** | **一个插件 = 一个目录 + `Manifest` + `Plugin` + `Proofs`；`Migrated` 只查路径前缀** |
| **选成了什么** | **用「目录结构」**单独**承载「能力归属」** |
| **后果** | **「迁移 = 移动文件」；wrapper 冒充 move；`Migrated` 无内容** |
| **改法** | **两者都需要**：**目录负责物理组织与编译单元；`Capability` 负责语义归属。`Migrated` 应同时检查：① 目录前缀（物理）② `Obligation.proof` 的命题确实由该目录内的定理提供（语义）** |
| **影响面** | **`Migration.lean`、`Plugins.lean`、11 个插件** |
| **难度** | **M–L** |

---

## 4. 四级：补充

### 4.1 `Layer` 选成了固定枚举

**`PluginLayer` 固定 8 个构造子（`card_eq_eight := rfl`）。**
**加层要改枚举 + `card_eq_eight`；`Plugins` 层甚至不在 `gate.py` 的 `LAYER_OF` 里。**

**改法：`Layer` 改为 `Name` 或带序的 `Nat`；或保留枚举但加「未登记层」检查。** **难度 S。**

### 4.2 `Repair` 的 `μ` 选成了 `ℕ`

**无法表达实数收敛率；`converges_within` 只能是步数界。**
**改法：`μ : α → ℝ≥0`，或用 `WellFoundedRelation`。** **影响 T4、`RepairConvergence`。难度 M。**

### 4.3 `SafeBranch` 选成了 `False` 分支

**4 个构造子被定义为 `False`。**
**后果：精确双条件实际只覆盖 8/12，却像是 12/12。**

**改法：显式声明 `exactConstructors` / `relaxedConstructors` / `unsupportedConstructors` 三集合，并证 `= 12`。** **影响 T2。难度 S。**

### 4.4 `Spec` 的存在性选成了 `Nonempty`

**`c1_solve_reads_spec := ∀ n, Nonempty (FamilySolver n)` —— 存在性不等于「读 spec」。**
**改法：改为「存在一个 `solve`，其输出依赖 `S.constraints`」的命题。** **影响 T0。难度 S。**

### 4.5 `Fiber` 的生命周期选成了 `Bool`

**`Step.failing : Bool` 无法表达 `inactive → activating → active → deactivating → unloaded → failed`。**
**改法：显式 `inductive FiberState`。** **影响 T5–T8。难度 S–M。**

### 4.6 `Card` 类断言选成了 `length := rfl`

**`pluginCensusSize := 8` 与 `proofRegistry.length = 8 := rfl` 是**自数**，不是内容相等。**
**改法：从 `proofRegistry` 推导，或证明两个独立定义的集合基数相等。** **难度 S。**

---

## 5. 按「改一个影响多少」排序

| 序 | 问题 | 影响面 | 难度 | 建议时机 |
|--:|:--|:--|:--|:--|
| **1** | **`Weights` 索引化** | **T3、ChainSlot、ModelArtifact、导出** | **M–L** | **现在（C0 之后、C2 之前）** |
| **2** | **`Term` 分 `Prop`/`Type`** | **C0/C1/C2 全部** | **M** | **现在（C0 内）** |
| **3** | **`Obligation` 内嵌命题** | **幽灵名根治、H2 的 `PluginProof`** | **S–M** | **H2 内** |
| **4** | **`State` 参数化 + `Effect` 泛化** | **T5–T8** | **M** | **C3 之前** |
| **5** | **`FiberState` 枚举** | **T5–T8** | **S–M** | **C3 内** |
| **6** | **`Arch` 改图** | **DAG、五载体接 CIC** | **M–L** | **F 阶段** |
| **7** | **`ProofComplete` 改依赖图** | **判据结构** | **M** | **H2 之后** |
| **8** | **插件目录 + 能力两者** | **`Migrated` 真实性** | **M–L** | **H2/H3** |
| **9** | **`Spec` 三集合** | **T2** | **S** | **H0 内** |
| **10** | **`Behavior` 改关系** | **T1/T2** | **M** | **C1 之后** |
| **11** | **`ServiceKey` 类型化** | **T6** | **S** | **C3 内** |
| **12** | **`Layer` 枚举** | **`gate.py`** | **S** | **H0 内** |
| **13** | **`Repair.μ` 改 `ℝ≥0`** | **T4** | **M** | **C2 内** |
| **14** | **`ResultEquiv` 加序** | **文档** | **S** | **随时** |
| **15** | **`Spec` 的存在性** | **T0** | **S** | **H0 内** |
| **16** | **`Spec` 列表** | **已被 CIC 覆盖** | **S** | **确认** |
| **17** | **`FiberState`** | **T5–T8** | **S–M** | **C3 内** |
| **18** | **`Card` 自数** | **判据** | **S** | **H0 内** |

---

## 6. 判据（已实现为门禁）

**这份清单的价值在于它可被**自动检查**，而不只是一份备忘。**

**`gov/check_parameterization.py` 做两件事：**

1. **验证 18 条**全部**在本文档中登记**（防止清单被悄悄删减）；
2. **对每一条**，检查代码中**是否仍未被参数化**——通过在该条登记的 `现状` 定义上搜索**硬编码实例**的特征（如 `Option ℕ`、`String`、`:= rfl` 的自数）。

**=> 清单是**活的**：修好一条，门禁会报告「已参数化，可从清单移除」。**

**未修时门禁报告计数，不阻止构建**（因为 18 条都是**已登记的技术债**，不是缺陷）。
**=> 与 `prop-def-baseline.txt` 同构：登记即透明，修好即递减。**

---

## 7. 一句话

> **载体已经修好（第 134 轮 CIC 决定）；同类问题还有 18 条。**
> **三条必须在 C0/C2 之前定：`Term` 的 `Prop`/`Type`、`Weights` 索引化、`Obligation` 内嵌命题。**
> **三条在 C3 之前：`State`/`Effect`/`FiberState`。**
> **两条在 H2 之后：`ProofComplete` 依赖图、插件目录+能力双轨。**
> **判断标准始终是同一句：它现在是「具体实例」还是「抽象角色」？**
