# CONSTRUCTIVE TRAINING

## 1. 定义

构造性预训练 = 从符号规格构造模型，不经过梯度训练。

**新载体（CIC）下的流程：**

```text
Typable Γ t A → Term t → compile t → Weights → ModelArtifact
```

**几何实例（Domain）下的流程：**

```text
ExpressibleSpec → Family → solve → Pt n → Weights → ModelArtifact
```

这不是“把权重写成字面量”，而是“从规格解出权重”。
两者的区别见 `CARRIER-CIC.md`：几何版本只能以 family 强度存在
（`no_specSolver` 已证任意 spec 不可行），CIC 版本以可类型性为前提，可判定。

## 2. 只对可构造的规格

### 2.1 CIC 版本

```lean
def Typable : Context → Term → Type → Prop
```

条件：

- term 在给定 context 下可类型化；
- `compile : Term → Weights` 有定义；
- 欠定有 canonical 规则。

### 2.2 几何版本（Domain 实例）

```lean
def ExpressibleSpec : Set Spec
```

条件与旧版相同，但**只能 family 强度**：

- 架构可表达；
- 行为可约束；
- 权重可解；
- 欠定有 canonical 规则。

不属于可构造范围的模型：

- 无符号规格；
- 纯数据驱动、无约束；
- 私有权重格式；
- 不可复现随机过程。

这些只能 `import` / `transform`，不能声称从零构造。

## 3. 三种结果

### 3.1 CIC 版本

```lean
theorem construct_sound :
  Typable Γ t A → Models (compile t) A

theorem construct_complete :
  Typable Γ t A → ∃ W, compile t = W

theorem construct_canonical :
  compile t = W → ∀ W', Models W' A → canonical W ≤ canonical W'

theorem construct_approx :
  compile t = W → ∀ x, |denote W x - denote t x| ≤ steps t * ε
```

注意 `construct_approx` 的 `ε` 来自 **β 归约步数 `steps t`**，
是显式的、`steps t → 0` 时可退化为 exact（见 `PROOF-OBLIGATIONS.md` T2）。

### 3.2 几何版本（Domain 实例，旧形状）

```lean
theorem construct_sound :
  construct s = some A → A ⊨ s

theorem construct_complete :
  s ∈ ExpressibleSpec → ∃ A, construct s = some A
```

**注意：** 第二条在几何上对任意 spec **不成立**（`no_specSolver`），
因此几何版本只在 family 上陈述。

## 4. 与权重字面量

把 checkpoint 的权重写成字面量不是 construct。

`construct` 要求：

- 输入是 term（CIC）或 spec（几何 Domain）；
- 通过 `compile` 或 `solve` 得到 `Weights`；
- 有 `construct_sound` 或 `construct_approx`。

## 5. 与训练

不实现梯度循环；外部训练器只作为 `Delegate`，证书为 `Imported` / `Empirical`。

## 6. 与 Confluence

T7 保证：

> 动态加载/卸载/替换后的最终模型 = 从最终 `Spec` 重新 `construct`。

这把“从零构造”和“可扩展插件”接起来。
