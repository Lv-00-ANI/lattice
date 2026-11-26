# MODEL / WEIGHT SEMANTICS

## 1. 范围

本文件只定义 Lean 内的抽象模型/权重对象与语义关系。
格式解析、文件 I/O、C、conformance 属于 `ENGINEERING.md`。

**目标确认（2026-11-23）**：本设计覆盖模型与权重的行为语义，不止参数搬运或格式往返。CIC 经 IR 连接到模型架构与权重，正向转换、逆向提取、验证、修复及再注入须分别说明语义保持或显式误差保证。任意精度目标须声明目标类、输入域、误差度量和可增长资源，不预设固定模型规模，也不因局部不可逆反例取消该目标。

本文件中的代码块是设计示意，不是完成声明。旧几何实例及过时路径的全库清理见 [设计目标对齐](DESIGN-ALIGNMENT.md) §4；几何不作为默认主线语义。

## 2. 抽象对象

```lean
structure ModelArtifact where
  arch    : Arch
  weights : Weights
```

- `Arch`：架构语法/语义；
- `Weights`：抽象权重，不是 `ByteArray`、不是 `Float`、不是文件；
- 没有 `format` 字段；
- 没有 `bytes` 字段。

**来源是 IR 的编译（IR 由 `parse` 从 CIC 得到）**：

```lean
def compile : IR → Weights
def archOf  : Term → Arch
-- 示意：假设 parse : Term → Option IR；解析失败显式保留。
def artifactOf (t : Term) : Option ModelArtifact := do
  let ir ← parse t
  pure { arch := archOf t, weights := compile ir }
```

几何侧的 `Pt n → Weights` 保留为一条 Domain 实例路径
（`Domains/Geometry`），不再是唯一来源。理由见 `CARRIER-REPLACEMENT.md`。

`RawModel` 只存在于工程侧：

```lean
structure RawModel where
  bytes  : ByteArray
  format : Format
```

## 3. 语义

```lean
def denote : ModelArtifact → Behavior
```

`Behavior` 可以是：

- `Input → Output`；
- 约束满足关系；
- 概率/路由语义。

具体选择由插件 `Semantics.lean` 定义。

## 4. 等价

```lean
inductive ResultEquiv : ModelArtifact → ModelArtifact → Prop
| weights  : A.weights = B.weights
| behavior : ∀ x, denote A x = denote B x
| approx   : ∀ x, |denote A x - denote B x| ≤ ε
```

- `bytes` 等价属于工程测试，不属于证明；
- `behavior` / `approx` 是“只看结果”的证明口径；
- `weights` 是最强口径，但不要求训练过程相同。

## 5. 构造

```lean
def construct : Typable Γ t A → Option ModelArtifact
```

- 构造的输入是 **term**，不是点配置；
- 「可构造」= 「可类型性」+ 「`compile` 有定义」，因此可判定；
- exact / canonical / approx；
- 无 `Typable` 见证时返回 `none`。

几何上的旧构造器（`ExpressibleSpec n → Pt n`）只以 family 强度存在：
`no_specSolver`（`Plugins/Targets/SolverBoundary.lean`）已证明它对任意 spec 不可能。

## 6. 变换

```lean
def transform : ModelArtifact → Transform → Option ModelArtifact
```

- exact：语义保持；
- approx：显式 ε；
- irreversible：必须显式 commit，不能假装可逆。

## 7. 禁止

- 在 Lean 证明中解析文件；
- 在 Lean 证明中调用 C；
- 用 `ByteArray` 冒充 `Weights`；
- 用格式 roundtrip 冒充语义等价。
