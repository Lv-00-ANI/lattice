# 使用说明（USAGE）

> 本文件面向**外部使用者**：想知道这个库能做什么、怎么接进来、什么做不到。
>
> **本文件里每一段 Lean 代码都在 `Lattice/Usage/Examples.lean` 里有一份可编译的对应实现。**
> 若那段文件编译失败，说明本说明是错的——这是本文件唯一的正确性保证，
> 也是它区别于普通文档的地方。

---

## 0. 一句话

`LATTICE` 是一条**端到端的表示链路**：

```
数据 ⇄ token ⇄ 符号模型 ⇄ 权重
```

正向把符号知识编译成权重；逆向把权重行为提取回符号；闭环是验证回路。
**正确性由 Lean 4 保证**，且**每个结构的意义来自它的义务字段**，不是注释。

---

## 1. 四个结构，各带一条义务

库的用法几乎都是「实现一个结构，然后免费得到它的定理」。四者形状一致：

| 结构 | 全名 | 义务字段 | 提供了什么定理 |
|:--|:--|:--|:--|
| `Compiler` | `Lattice.Lift.Compiler P W inputP inputW` | `sound` | `compileProgram_sound` |
| `Representation` | `Lattice.Lift.Representation P W` | `roundtrip` | `extract_compile`、`compile_injective` |
| `Ladder` | `Lattice.Lift.Ladder Data Tok Sym W` | `l2l3_sound` | `ladder_forward` |
| `Repair` | `Lattice.Core.Repair α` | `absorbs` / `decreases` / `atomic` | `progress`、`converges_within` |

**关键设计**：义务是**字段**，所以实现结构时**必须**提供；而一旦提供，
下游的定理**不需要再证**。这就是 `ROADMAP-v9 §1` 实测到的
「`compileProgram_sound` 等三条定理零引用内核声明」的原因。

---

## 2. 最小 `Compiler`

```lean
def boolCompiler : Compiler Bool Nat Unit Unit where
  encode  := id
  compile := fun b => if b then 1 else 0
  satP    := fun b _ => b = true
  satW    := fun n _ => n = 1
  sound   := by intro b _ hb; simp [hb]
```

四点注意：

1. **四个类型参数**：`P`（符号）、`W`（权重）、`inputP`（符号侧输入）、`inputW`（权重侧输入）。
   后两个是**类型参数**而非字段——这是为了让「所有后端」能被一次量化（见 `CompilerScheme`）。
2. `sound` 就是义务，没有默认值。
3. `encode` 可以不是恒等（`NonIdentical.projectCompiler` 是投影）。
4. 有了它，`boolCompiler.compileProgram_sound` 立刻可用。

---

## 3. 最小 `Representation`

```lean
def boolRep : Representation Bool Nat where
  inputP := Unit
  inputW := Unit
  encode := id
  decode := id
  compile := fun b => if b then 1 else 0
  extract := fun n => n = 1
  roundtrip := by intro b; cases b <;> rfl
```

> **若你的提取是有损的**，不要硬塞进 `Representation`——
> 用 `Lattice.Lift.LossyRepresentation.LossyRep`，它把往返放宽为「在某观察关系下等价」。
> `RoundingBackend.roundingLossy` 是具体实例（整数取整，误差 ≤ 1）。

---

## 4. 最小 `Ladder`（端到端）

```lean
def boolLadder : Ladder (List Bool) Bool Bool Bool where
  l0l1 := identityTokenizer Bool          -- Data = List Tok
  l1l2 := boolTok                          -- 自己写的 Tokenizer Bool Bool
  l2l3 := id
  satSym := fun s => s = true
  satW   := fun w => w = true
  l2l3_sound := by intro s hs; simpa using hs
```

⇒ `boolLadder.ladder_forward` 给出端到端的保语义。

> **真实实例**见 `Geo/LadderInstance.lean` 的 `linearLadder`：
> L1⇄L2 用 `encodeForm`/`decodePayload`（往返定理在 `Lift/L1L2Roundtrip.lean`），
> L2→L3 是线性形式 ↦ 残差平方。
>
> **诚实边界**：`linearLadder` 的 `W` 取的是**损失值**（`ℝ`），不是权重参数。

---

## 5. 最小 `Repair`（验证回路）

```lean
def natRepair : Repair ℕ where
  Sat  := fun n => n = 0
  fix  := fun n => n - 1
  μ    := fun n => n
  absorbs   := by intro n hn; simp [hn]
  decreases := by intro n hn; exact Nat.sub_one_lt (by omega)
  atomic    := by intro n hn; exact hn
```

⇒ 立即得到**收敛率**：

```lean
converges_within natRepair n :  natRepair.Sat (natRepair.iterate (natRepair.μ n) n)
```

**界的意义**：`μ n = n` 步之内必然满足，且**这个界是紧的**——
对 `RepairMultistep.countdown`，少于 `μ k` 步到不了（`no_uniform_bound`）。

> **`atomic` 现在是简短的**：用 `Lattice.Core.RepairAtomicity.mkWithAtomic`，
> 只需提供 `μ x = 0 ↔ Sat x`，证明形式由库给出。

---

## 6. 加一个新约束类型，要做四件事

以给 `GeoConstraint` 加 `Foo` 为例：

| 步 | 做什么 | 参考 |
|:--|:--|:--|
| 1 | 在 `GeoExpr` / `GeoConstraint` 加构造子 | `Geo/Expr.lean`、`Geo/Constraint.lean` |
| 2 | 给 `Holds` 加分支 | `Geo/Constraint.lean` |
| 3 | 给 `poly` 加分支（残差） | `Geo/Loss.lean` |
| 4 | 给 `poly` 的分支加 Lipschitz 常数 | `Geo/PolyAssemble.lean`，常数见 `PolyConstants` |

**做完这四步，自动得到**：`GeoSampledBound.geo_sampled_bound`（采样验证给出全域界）、
`Reinjection` 的再注入、以及 `Geo.Synthesis` 的合成框架。

> **不需要**：重证链路、重证收敛、重证损失为零。

**这三条承诺是可验证的**：`Lattice/Usage/Examples.lean` 第八节用它们的**完整签名**
各写了一个 `example`。若那三条定理改名、改签名或消失，那个文件就编译不过。

---

## 7. 可执行轨道：`Float` 常量与容差检查

**前面各节用的都是 `ℝ`——那是本库的证明轨道。**
`ℝ` 上的定义是 `noncomputable`，`#eval` 直接失败，所以外部训练流程无法直接调用它们。

第 87–88 轮为此建了一条**并行的可执行轨道**。**ℝ 轨道完全不动。**

| 轨道 | 常量类型 | 求值 | 用途 |
|:--|:--|:--|:--|
| **证明轨道** | `ℝ` | `noncomputable def evalPts` | 全部 8,000+ 条定理 |
| **可执行轨道** | `Float` | **`def evalC`（可计算）** | 接到外部流程 |

两族的形状完全一致（`coord` / `const` / `add` / `sub` / `mul`），
**`CExpr` 是 `GeoExpr` 的并行版本，不是它的替代。**

### 7.1 可执行的表达式

```lean
open Lattice.Geo.ComputableExpr

def demoExpr : CExpr 1 :=
  .add (.mul (.coord 0 0) (.coord 0 0)) (.const 2.0)
```

`evalC` 是 `def`：`#eval` 能直接运行它。

### 7.2 容差检查，以及它为什么必须带容差

`Float` 的相等**不可判定**——`NaN` 破坏自反性。所以「约束成立」不能直接判定，
可执行版本用容差：

```lean
open Lattice.Geo.ExecutableCheck

def demoTol : Tolerance where
  tol := 0.001
  pos := by native_decide
```

`Tolerance` 结构把 `0 < tol` **编进类型**：容差为正**是构造的前提，不是一条待证的命题**。

### 7.3 只证一个方向，这是刻意的

```lean
approxHoldsEqZero_sound : approxHoldsEqZero T e pts = true -> |evalC e pts| <= T.tol
```

**只有 `sound` 方向可证。** 反方向（「在容差内成立 ⟹ 判定为真」）**无法陈述**：
ℝ→`Float` 的舍入误差**依赖具体数值**，不存在一个常数容差使它成立。

⇒ **记分卡的「可执行边界」只算部分达标**，因为可执行轨道存在但只单向可靠。
详细论证见 `STATE-FINAL §3.6.2`。

### 7.4 三个必须知道的限制

| 限制 | 内容 |
|:--|:--|
| **`Float` 相等不可判定** | 12 个 `GeoConstraint` 构造子里 10 个要求相等，只能改用容差 |
| **只有 `sound` 可证** | 完备性方向是浮点固有性质，不是缺证明 |
| **`Float` 没有 `Preorder` 实例** | `<` 是 `compare = .lt`，**所有序引理不可用**；`tol ≠ 0` 这类命题不能用 `lt_irrefl` |

**第三点的实际后果**：`Tolerance.pos` 只能对具体字面量用 `native_decide` 证明，
不能用通用引理。**这正是它必须放在结构里的原因。**

---

## 8. 每个入口点证明什么

| 入口 | 定理 | 一句话 |
|:--|:--|:--|
| 编译保语义 | `Compiler.compileProgram_sound` | 编译后的程序接受原程序接受的一切 |
| 提取可逆 | `Representation.extract_compile` | 提取是编译的左逆 |
| 端到端 | `Ladder.ladder_forward` | 符号满足 ⟹ 末端 artifact 满足 |
| 收敛率 | `RepairConvergence.converges_within` | `μ x` 步之内满足，界紧 |
| 采样验证 | `GeoSampledBound.geo_sampled_bound` | 有限采样 + Lipschitz ⟹ 全域界 |
| 逼近精确 | `ApproxExact.epsSat_of_loss_le_sq` | 损失 ≤ ε² ⟹ 残差 ≤ ε |
| 再注入 | `Reinjection.reinject_loss_eq_zero` | 修正后再编译，惩罚为零 |
| 后端统一 | `CompilerScheme.scheme_covers_all` | 任何编译器都是一个后端 |

---

## 9. 什么**做不到**（去 `REFUTATION-CENSUS.md` 查全部 296 条）

| 做不到的事 | 定理 |
|:--|:--|
| 损失为零 ⟹ 约束精确成立 | `PenaltyEmbedding.sound_not_exact`（**否证**） |
| 用恒等算子做修复 | `Geo.Repair.no_identity_repair` |
| 分词单射 | `RealTokenization.tokenize_not_injective` |
| 取整编码单射 | `RoundingBackend.compileZ_not_injective` |
| `absorbs` 由另两条导出 | `ObligationIndependence.absorbs_not_derivable` |
| 三步保证收敛 | `Repair.down_no_progress` |
| 统一步数界 | `RepairMultistep.no_uniform_bound` |

**这些是项目定位「通用基础设施」的证据面**：一个基础设施的可信度，
很大程度上取决于它明确知道什么做不到。

---

## 10. 项目**不**做什么（定位边界）

| 不做 | 实测证据 |
|:--|:--|
| 实现推理引擎 | 标题含 `torch`/`cuda`/`tensor`/`autograd` 的文件：**0** |
| 实现模型架构 | 同上；`Lib/Architectures` 是数值基础设施（SVD/范数），不是模型定义 |
| 实现训练框架 | 同上 |
| 绑定厂商 | 文件名含厂商/模型：**0** |

---

## 11. 怎么验证你在看的这份说明是对的

```bash
# 1. 编译
cd lattice-new && lake build Lattice

# 2. 门禁（8 条不变量 + 反应性测试）
cd gov && python gate.py

# 3. 文档计数与树一致
python audit_counts.py

# 4. 本文件里的每个示例
lake build Lattice.Usage.Examples
```

**第 4 条是这份说明的自我保证**：`Lattice/Usage/Examples.lean` 的 8 节
（第 2–8 节）对应本文件的第 2–8 节，它编译不过就说明本文有错。

**这个自保证有明确的边界，必须说清**：

| 覆盖 | 不覆盖 |
|:--|:--|
| 第 2–8 节里出现的**每一个 Lean 代码块与每一条承诺** | 第 0、1、9、10 节（纯散文） |
| 定理的**签名**（改名、改参数、消失都会失败） | 散文里的**数字**（如"本节标题里那个条数"）：由 `check_doc_consistency.py` 管 |

**两条守卫分工明确**：`Lattice/Usage/Examples.lean` 守代码，`check_doc_consistency.py` 守数字。
本节第 9 节的否证总数**曾写错一个数**（写大了约三分之一），而当时没有任何守卫覆盖 `USAGE.md`——**那一处就是新守卫 `check_usage_claims.py` 的由来**。

**注意**：守卫的正则会抓取本文里所有"全部 N 条"形式的出现，所以**不要在正文里引用旧数字**，只描述它错了。

---

## 6. 新类型用法（2026-11-02）

### 6.1 构造

```text
Spec → Constraints → Solve → Params → ModelArtifact
```

只对 `ExpressibleSpec`；不是梯度训练。

### 6.2 导入

```text
RawModel → FormatAdapter.parse → ModelArtifact
```

格式解析属于工程；失败返回 `none`，不静默降级。

### 6.3 变换

```text
ModelArtifact → edit / merge / quantize / repair → ModelArtifact
```

- exact / approx ε / irreversible；
- irreversible 必须显式 commit；
- 证书绑定 provider 与 artifact。

### 6.4 导出

```text
ModelArtifact → FormatAdapter.export → RawModel
```

导出是 emission：不可逆，只能版本化/补偿。

### 6.5 新增插件

```text
Lattice/Plugins/<Layer>/<Name>/
  Manifest.lean
  Semantics.lean
  Soundness/
  Completeness/
  Laws/
  Exactness/
  Approximation/
  Recovery/
  Spatial/
  Confluence/
  Equivariance/
  Idempotence/
  Plugin.lean
```

详见 `PLUGIN-PROTOCOL.md` 与 `PLUGIN-PROOFS.md`。
