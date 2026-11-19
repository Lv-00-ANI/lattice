# PRIMITIVE-MATRIX：已登记的 `Primitive` 与适配器需求

> **本文件由 `gov/gen_primitive_matrix.py` 生成，勿手改。**
> **它是「报数」，不是门禁**：`verify_all.py` 把它登记为 `reported`，不是 `ok`。

## 这份矩阵是什么，**不是**什么

它是**文本层**矩阵。Python 看不见 Lean 的类型，所以它读每个 `Primitive` 的
`Input := …` / `Output := …` **源码文本**再比较。两个后果，下面都写清：

1. **「文本相同」是「不需要适配器」的充分条件，不是必要条件。**
   `ℝ` 写两次是同一类型；但类型同义词、可归约的 `abbrev`、需要展开的定义会
   是**同一类型而文本不同**，矩阵会要求一个 §6 实际上并不需要的适配器。
2. **它完全不说明组合是否被证明过。** 它只说明类型允许什么。

**仍然值得生成**，因为它量的正是 §6 出错的那件事：
`compose` 的签名假定 `f.Output = g.Input`，而结构里没有任何东西强制它。

## 一、已登记的 `Primitive`

| # | 名称 | 位置 | `Input` | `Output` | 强度 | 覆盖 |
|--:|:--|:--|:--|:--|:--|:--|
| 1 | `compose` | `Lattice/Compose/Combinators.lean:101` | `I` | `O` | `f.strength.min g.strength` | `f.coverage.inter g.coverage` |
| 2 | `composeWith` | `Lattice/Compose/Combinators.lean:120` | `I` | `O` | `f.strength.min g.strength` | `f.coverage.inter g.coverage` |
| 3 | `identity` | `Lattice/Compose/Combinators.lean:190` | `α` | `α` | `.exact` | `none` |
| 4 | `descentStep` | `Lattice/Compose/ForwardChain.lean:70` | `ℝ` | `ℝ` | `.exact` | `some ({"constraint.eqZero"} : Finset String)` |
| 5 | `iterate` | `Lattice/Compose/Iterate.lean:304` | `I` | `I` | `p.strength` | `p.coverage` |
| 6 | `parallel` | `Lattice/Compose/More.lean:61` | `(I₁ × I₂)` | `(O₁ × O₂)` | `f.strength.min g.strength` | `f.coverage.inter g.coverage` |
| 7 | `choice` | `Lattice/Compose/More.lean:95` | `I` | `O` | `f.strength.min g.strength` | `f.coverage.union g.coverage` |
| 8 | `optional` | `Lattice/Compose/More.lean:145` | `I` | `I` | `p.strength` | `p.coverage` |
| 9 | `applySgd` | `Lattice/Compose/Steps.lean:65` | `ℝ` | `ℝ` | `.exact` | `none` |
| 10 | `applyMomentum` | `Lattice/Compose/Steps.lean:120` | `(ℝ × ℝ)` | `(ℝ × ℝ)` | `.exact` | `none` |
| 11 | `applyAdam` | `Lattice/Compose/Steps.lean:148` | `(ℝ × ℝ × ℝ)` | `(ℝ × ℝ × ℝ)` | `.exact` | `none` |

## 二、适配器矩阵

行 = 先跑的，列 = 后跑的。三态：

- **`—`**：文本相同，适配器可取 `id`；
- **`POLY`**：至少一侧是**裸类型变量**（如 `α`），调用方可**实例化**它，所以原则上不需要适配器；
- **`ADAPT`**：文本不同且没有可实例化的变量，**必须**提供适配器。

| 先 \\ 后 | `compose` | `composeWith` | `identity` | `descentStep` | `iterate` | `parallel` | `choice` | `optional` | `applySgd` | `applyMomentum` | `applyAdam` |
|:--|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| `compose` | ADAPT | ADAPT | POLY | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT |
| `composeWith` | ADAPT | ADAPT | POLY | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT |
| `identity` | POLY | POLY | — | POLY | POLY | POLY | POLY | POLY | POLY | POLY | POLY |
| `descentStep` | ADAPT | ADAPT | POLY | — | ADAPT | ADAPT | ADAPT | ADAPT | — | ADAPT | ADAPT |
| `iterate` | — | — | POLY | ADAPT | — | ADAPT | — | — | ADAPT | ADAPT | ADAPT |
| `parallel` | ADAPT | ADAPT | POLY | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT |
| `choice` | ADAPT | ADAPT | POLY | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT |
| `optional` | — | — | POLY | ADAPT | — | ADAPT | — | — | ADAPT | ADAPT | ADAPT |
| `applySgd` | ADAPT | ADAPT | POLY | — | ADAPT | ADAPT | ADAPT | ADAPT | — | ADAPT | ADAPT |
| `applyMomentum` | ADAPT | ADAPT | POLY | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | — | ADAPT |
| `applyAdam` | ADAPT | ADAPT | POLY | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | ADAPT | — |

## 三、读数

| 指标 | 值 |
|:--|--:|
| 已登记的 `Primitive` | 11 |
| 有序对总数 | 121 |
| **`—` 文本相同** | **17** |
| **`POLY` 可实例化** | **20** |
| **`ADAPT` 必须给适配器** | **84** |

**这三行就是 §6 那个签名的错误规模**：`ADAPT` 的比例越高，
原签名（`compose (f g : Primitive) (h : ∀ x y, f.post x y → g.pre y)`）
假定的 `f.Output = g.Input` 就越不成立——**而结构里没有任何东西强制它**。

**注意 `ADAPT` 里包含自组合**：`parallel` 的 `Input` 是 `f.Input × g.Input`、
`Output` 是 `f.Output × g.Output`，**文本永不相等**，所以 `parallel` 连与自身组合都要适配器。
这不是矩阵的缺陷，是 `parallel` 的定义决定的。

⚠ **不要把 `—` 读成「已证明可组合」**：它只说明类型文本一致，
`compose` 仍需要 `adapt : f.Output → g.Input`（此时可取 `id`）
**与兼容性证明 `h : ∀ x y, f.post x y → g.pre (adapt y)`**。
**后者是真正的工作量，本矩阵不测量它。**

### ⚠ 第 40 轮更正：这 121 格里 **96 格没有对象**

| 类 | 名字 | 数量 | 签名形状 |
|:--|:--|--:|:--|
| **值** | `identity`、`descentStep`、`applySgd`、`applyMomentum`、`applyAdam` | **5** | 返回 `Primitive I O`，**不接收 `Primitive` 参数** |
| **组合子** | `compose`、`composeWith`、`parallel`、`choice`、`optional`、`iterate` | **6** | **接收 `Primitive` 参数**，返回 `Primitive I O` |

**矩阵把组合子当作「输入 `I`、输出 `O` 的值」填进表里**——而那两个是**它结果的**类型。
`compose` 在成为值之前需要**两个 `Primitive` 参数**，所以「`compose` 后面接 `descentStep` 需要适配器」这句话**没有对象**。

**所以：121 格里有 121 − 25 = 96 格涉及组合子，它们是 `N/A（元数）`，不是 `ADAPT（义务）`。**
真正有对象的只有 **5 × 5 = 25 格**（值 对 值）。

**而适配器本身从不是类型层的障碍**（`AdapterMatrix.adapter_always_exists`）：只要目标类型有居民，`O → I` **总是**存在（常函数）。
所以「必须提供适配器」不是不可能性——它是**语义**问题：常函数适配器几乎肯定违反 `g.pre`，**而那正是 `h` 要挡住的**（见 `Compose/ComposeObligation.lean`）。

