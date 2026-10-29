# 超越线性：三层评估与四项待办

> **登记日期**：2026-10-29。**状态**：前向已超越；**精确表示仍仿射**；**非线性训练未开始**。
> **本文件的目的**：把这个判断、它的证据、以及达到目标的四项工作**放在一处**，
> 并且**纠正一个正在流传的过度断言**（见 §三）。

---

## 一、三层评估

| 层面 | 是否超越线性 | 证据 |
|:--|:--|:--|
| **前向表达式 / 程序语义** | ✅ **是** | `ProgramAST` 有 `affine / relu / scale`；`ActivationLadder` 带激活栈 + `∀x` 语义 + 非重言 `l2l3_sound`；`SoftmaxSubLayer` 具体 attention；softmax/attention Lipschitz 已闭合 |
| **精确的符号⇄权重表示** | ❌ **否，仍是仿射** | `weightSymbolRep` / `rectangularRep` 仿射；`ConstraintRepresentation` 的 L2⇄L3 实例是 `convertVec` 逐字段拷贝（`List Int` 系数 + 偏置）；`GeoLadder` 的 `W` 仍是损失 |
| **非线性训练 / 后训练** | ❌ **否** | `shiftLayer` 是 `W=0`、单层、单约束、`Fin 1`；`netLoss` 无一般反向；无 AD / data / SFT / DPO / RLHF |

**一句话**：**前向「能算非线性」已经做到；精确「把非线性权重反回符号」只能线性；「训练非线性模型」还没开始。**

---

## 二、四项待办（达到「真正超越线性」）

### P4-NL-1（最高优先）`SemanticRepresentation` 的 program 实例

**目标**：`LayerProgram` ↔ `List ℝ`（参数）挂上 `SemanticRepresentation`。

- `P` = 程序（`LayerProgram n` 或其语法层）；
- `W` = 参数（`List ℝ` / `LayerParams`）；
- `compile` = 合成/编码；`extract` = 反解析；
- `roundtrip` = **语法**往返（`decode ∘ encode = id`）；
- **`compile_preserves`** = `evalProgram` 语义保真。

**当前状态**：`ProgramAST` 只做了语法往返（`programRep`），**`SemanticRepresentation` 没有挂上去**。
**这是「真正超越线性」的第一步**，而且它**不需要先有非线性训练**。

**为什么可做**：`evalProgram` 与 `eval_append` 已经存在；语义律的形状与 `symbolToWeight_correct` 相同。

### P4-NL-2 非线性原语进入 `ProgramAST`

**目标**：把 softmax / layernorm / attention 做成 **`Instr` 的构造子**，而不是只在 `SubLayer` 里包装。

**约束**：**保持语法往返**（`ProgramAST` 的 `programRep` 不能因此破掉）。

**依赖**：P4-NL-1（先把结构挂上，再加构造子）。

### P4-NL-3 非线性训练

**目标**：`grad` / AD 对 `LayerProgram` 的参数；优化器接 `netLoss`；**不再 `W=0`**。

**当前状态**：`Momentum`/`Adam` 的 `sound` 是 `rfl` 级；无一般反向传播；无 data pipeline。

**依赖**：P4-NL-1；以及清单里的 `P2-01`/`P2-02`/`P2-03`。

### P4-NL-4 权重侧分类收口

**目标**：4 个标量构造子 + 6 个非线性构造子，**每个给三态之一**：

- **可表示**（并给出层）；
- **已证明不可能**（并给出定理）；
- **未做**（并说明为什么还没做）。

**另**：`GeoLadder` 的 `W` 要么改成权重，要么**明确降级为损失**并写清理由。

---

## 三、⚠ 纠正一个正在流传的过度断言

`Domains/Geometry/WeightSideLadder.lean` L214-215 说：

> **所以「12 个构造子里有几个能走到权重侧」的答案是 2 个**（`samePoint`、`midpoint`），
> 另外 4 个是「一个泛函」、6 个是「非线性零点集」。**这不是没做，是分类的结果。**

**「这不是没做」这半句错。** 实测 `Domains/Geometry/AffineClass.lean`：

| 构造子 | 已有的定理 | 那条定理到底否定了什么 |
|:--|:--|:--|
| `eqZero` | **`eqZero_representable`（肯定！）** | **它可表示**；`aff 1 (-c) x = 0 ↔ x = c` |
| `leZero` / `ltZero` / `gtZero` | `leZero_not_affine` 等 | **只否定了【等式】形式**；文件 L63 自己写「半空间表示当然可以」，且 `leZero_halfspace` 存在 |
| `sqDistEq` / `equalLength` | `sqDistEq_not_affine`、`equalLength_not_affine` | 否定**仿射等式**表示 |
| `perpendicular` / `rightAngle` / `collinear` / `parallel` | `bilinear_not_affine`（一条覆盖四个） | 否定**仿射等式**表示 |

**所以准确的三态是：**

| 状态 | 个数 | 是哪些 |
|:--|--:|:--|
| **真的建了仿射权重层** | **2** | `samePoint`、`midpoint` |
| **有肯定结果、但没建层**（「未做」，不是「不可能」） | **4** | `eqZero`（`eqZero_representable` 已证）、`leZero`/`ltZero`/`gtZero`（`leZero_halfspace` 已证半空间形式） |
| **有形式化否定（仅限等式形式）** | **6** | 2 个二次 + 4 个双线性 |

⇒ **「2 of 12」这个数字的问题是**：**它用「`n` 个坐标」这个形状要求，把 4 个标量构造子排除了——
那是形状选择，不是不可能性定理。** 而这 4 个里有 1 个（`eqZero`）**已经被证明可表示**。

**这不是要推翻那条分类**（分类本身有用），**是要把那句总结改成**：
**「2 个已建层；4 个有可表示证据但未建层；6 个在等式形式下已被否定，但『不存在任何非线性表示』未被证明。」**

---

## 四、为什么「精确非线性权重表示」不能靠继续补仿射

`AffineClass.no_affine_represents_of_two_roots` 已经证明：

> 只要约束在 1 维有**两个不同解**，就不存在非零斜率的仿射函数以其零集为解集。

而 `ReLU` 也非单射（`relu(-1) = relu(0) = 0`），所以「权重→符号」的**函数逆**不成立。

⇒ **正确路线不是「找更强的仿射表示」，而是「程序作为权重侧」**：

- `P` = 程序语法 / 约束规格；
- `W` = `LayerProgram` / 参数；
- `compile` = 合成；
- `extract` = 反解析；
- `roundtrip` = **语法**往返；
- **语义由 `SemanticRepresentation.compile_preserves` 单独给。**

**这正是 P4-NL-1。** `ProgramAST` 已经有语法往返，**缺的只是把语义结构挂上去。**

---

## 五、与既有清单的关系

| 本文件 | 既有条目 |
|:--|:--|
| P4-NL-1 | 推进 `P0-13`（端到端定理）与 `P1-24`（ProgramAST 接 Ladder/Representation） |
| P4-NL-2 | `P1-25`（具体 attention/layernorm）的延伸 |
| P4-NL-3 | `P2-01`/`P2-02`/`P2-03`（netLoss / AD / 优化器） |
| P4-NL-4 | `P1-14`（权重侧 4 标量 + 6 非线性三态）、`P1-13`（`GeoLadder` 的 `W`） |

**所以这四项不是新路线，而是既有清单里几个条目的收敛点**——
它们的共同前提是 **P4-NL-1**，而 P4-NL-1 **不需要**先完成训练或非线性原语。
