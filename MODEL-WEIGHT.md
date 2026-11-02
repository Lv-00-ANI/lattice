# MODEL / WEIGHT SEMANTICS

## 1. 范围

本文件只定义 Lean 内的抽象模型/权重对象与语义关系。
格式解析、文件 I/O、C、conformance 属于 `ENGINEERING.md`。

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
def construct : Spec → Option ModelArtifact
```

- 只对 `ExpressibleSpec`；
- exact / canonical / approx；
- 无符号规格时返回 `none`。

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
