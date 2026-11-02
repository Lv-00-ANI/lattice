# CONSTRUCTIVE TRAINING

## 1. 定义

构造性预训练 = 从符号规格构造模型，不经过梯度训练。

```text
Spec → Constraints → Solve → Params → ModelArtifact
```

这不是“把权重写成字面量”，而是“从规格解出权重”。

## 2. 只对 ExpressibleSpec

```lean
def ExpressibleSpec : Set Spec
```

条件：

- 架构可表达；
- 行为可约束；
- 权重可解；
- 欠定有 canonical 规则。

不属于 `ExpressibleSpec` 的模型：

- 无符号规格；
- 纯数据驱动、无约束；
- 私有权重格式；
- 不可复现随机过程。

这些只能 `import` / `transform`，不能声称从零构造。

## 3. 三种结果

```lean
theorem construct_sound :
  construct s = some A → A ⊨ s

theorem construct_complete :
  s ∈ ExpressibleSpec → ∃ A, construct s = some A

theorem construct_canonical :
  construct s = some A →
  ∀ B, B ⊨ s → canonical A ≤ canonical B

theorem construct_approx :
  construct s = some A →
  ∀ x, |denote A x - target x| ≤ ε
```

## 4. 与权重字面量

把 checkpoint 的权重写成字面量不是 construct。

`construct` 要求：

- 输入是 `Spec`；
- 通过 `Solve` 得到 `Params`；
- 有 `construct_sound` 或 `construct_approx`。

## 5. 与训练

不实现梯度循环；外部训练器只作为 `Delegate`，证书为 `Imported` / `Empirical`。

## 6. 与 Confluence

T7 保证：

> 动态加载/卸载/替换后的最终模型 = 从最终 `Spec` 重新 `construct`。

这把“从零构造”和“可扩展插件”接起来。
