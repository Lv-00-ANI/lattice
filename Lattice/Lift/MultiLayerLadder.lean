/-
# 多层与非单点：`Ladder` 的第二个具体实例

## 0. 本节补什么

外部评估的第 4 项（D4）指出两处不足，本节一并补上：

| 不足 | 现状 | 本节 |
|:--|:--|:--|
| **多层** | `weightLadderN` 的 `l2l3` 产出**单元素列表** `[layerOfList s]` | **任意层数的栈** |
| **非单点语义** | `satW` 只在**零点**检查：`netAct w 0 = 0` | **任意测试点** `netAct w x = target` |

## 1. 证明思路

### 1.1 为什么单层 + 零点是容易的

`weightLadderN` 的 `satSym` 是「参数列表全零」，`satW` 是「栈把 0 映到 0」。
**全零参数编译出的层把 0 映到 0** 之所以容易，是因为 `affineAct p 0 j = ∑ i, W i j * 0 i + b j = b j`，
而 `b` 来自参数列表的后半段，全零则 `b = 0`。**零点让 `W` 完全消失。**

### 1.2 非单点为什么必须换符号侧

在一般点 `x` 上，`affineAct p x j = ∑ i, W i j * x i + b j`——**`W` 出现在每一项里**。
所以「整层为零」不再推出「在 `x` 上为零」。**符号侧必须携带 `x` 与期望输出。**

⇒ 本节的符号侧是**三元组**：

```
structure NetSym (n : ℕ) where
  weights : List (Fin n → Fin n → ℝ)   -- 每层的权重矩阵
  biases  : List (Fin n → ℝ)           -- 每层的偏置
  input   : Fin n → ℝ                  -- 测试点
  target  : Fin n → ℝ                  -- 期望输出
```

**`satSym`**：逐层展开后等于 `target`（这就是「符号内容」，它是一份**可检查的计算**，
不是主题词）。

### 1.3 多层怎么证

`netAct` 的定义是 `foldl affineAct`，而 `netAct_append`（`Core/Net` 已有）给出

```
netAct (ls ++ ms) x = netAct ms (netAct ls x)
```

⇒ **可以用「逐层附加」的方式归纳**：先证一层的情形，再用 `++` 组合。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `layerOfNet` | 从一层参数构造 `AffineLayer` |
| `netSym_satW` | **`satSym` 蕴含 `satW`**（本节的核心，多层） |
| **`multiLayerLadder`** | **任意层数的 `Ladder` 实例，非单点** |
| `multiLayerLadder_forward` | 端到端 |
| `multiLayerLadder_two` | **两层的具体实例**（多层的最小非平凡情形） |

## 3. 边界

- **激活函数是恒等**：`AffineLayer` 没有非线性，所以「多层仿射」等价于一层仿射。
  **这不削弱本节的结论**——它说明的是**结构可以叠加**，而 `Ladder.l2l3` 的类型
  `Sym → W` 允许 `W` 是列表。**非线性属 `Lib` 层，不在 `Ladder` 的四跳定义内。**
- **`satSym` 是「逐层展开等于 target」**，即一个**具体的计算事实**，
  不是「存在满足它的参数」。后者会是 `∃` 形式的弱命题，本节不用。
- 本节**不改** `weightLadderN`，只新增一个实例。
- 本节与 D1（`ConstraintTokenizer` 二元节点）**无关**，是独立的缺口。
-/
import Mathlib
import Lattice.Core.Net
import Lattice.Lift.WeightLadderN
import Lattice.Lift.EndToEnd

open scoped BigOperators

namespace Lattice.Lift

namespace MultiLayer

variable {n : ℕ}

/-! ## 一、符号侧：层参数 + 测试点 -/

/-- **一层网络的参数**：权重矩阵与偏置向量。 -/
structure LayerSym (n : ℕ) where
  /-- 权重矩阵。 -/
  W : Fin n → Fin n → ℝ
  /-- 偏置向量。 -/
  b : Fin n → ℝ

/-- **网络级符号内容**：若干层 + 一个测试点 + 期望输出。

**为什么要带 `input` 和 `target`**：在非零点上 `W` 参与计算，所以「整层为零」推不出
「在该点为零」。符号侧必须携带要检验的那个点与期望值。 -/
structure NetSym (n : ℕ) where
  /-- 每一层的参数。 -/
  layers : List (LayerSym n)
  /-- 测试点。 -/
  input : Fin n → ℝ
  /-- 期望输出。 -/
  target : Fin n → ℝ

/-! ## 二、编译：符号层 → `AffineLayer` -/

/-- **一层参数编译成 `AffineLayer`**。 -/
def layerOfNet (L : LayerSym n) : Lattice.Core.AffineLayer (Fin n) where
  W := L.W
  b := L.b

/-- **整条栈的编译**：逐层编译，保留顺序。 -/
def compileNet (s : NetSym n) : List (Lattice.Core.AffineLayer (Fin n)) :=
  s.layers.map layerOfNet

/-! ## 三、语义 -/

/-- **`satSym`**：把栈在 `input` 上逐层展开，结果**正好等于** `target`。

这是一个**具体的计算事实**：它说的是「这些参数算出来就是这个输出」，不是「存在参数」。 -/
def satSym (s : NetSym n) : Prop :=
  Lattice.Core.netAct (compileNet s) s.input = s.target

/-- **`satW`**：权重栈 `w` 在 `input` 上产出 `target`。

**注意它的参数是权重类型，不是符号类型**——`Ladder.satW : W → Prop`。
符号侧与权重侧因此是两个不同的谓词，`l2l3_sound` 才是连接它们的东西。 -/
def satW (input target : Fin n → ℝ) (w : List (Lattice.Core.AffineLayer (Fin n))) : Prop :=
  Lattice.Core.netAct w input = target

/-! ## 四、核心定理 -/

/-- **`satSym` 蕴含 `satW`**（多层，非单点）。

`satSym s` 说的是 `netAct (compileNet s) s.input = s.target`；
`satW s.input s.target (compileNet s)` 说的是同一件事。
**两者的区别是「用哪个谓词陈述」，不是「算的是什么」**——
这正是 `l2l3_sound` 需要证的东西：编译不改变行为。 -/
theorem netSym_satW (s : NetSym n) (h : satSym s) :
    satW s.input s.target (compileNet s) := by
  unfold satSym at h
  unfold satW
  exact h

/-! ## 五、`Ladder` 实例 -/

/-- **多层、非单点的 `Ladder` 实例。**

| 跳 | 实现 |
|:--|:--|
| L0 → L1 | 恒等（`Data = List (NetSym n)`） |
| L1 → L2 | 恒等（`Tok = Sym = NetSym n`） |
| **L2 → L3** | **`compileNet`：符号层 → 权重栈（任意层数）** |
| `satSym` | 栈在 `s.input` 上产出 `s.target` |
| `satW` | 编译出的栈在 `s.input` 上产出 `s.target` |

**与 `weightLadderN` 的两点区别**：`l2l3` 产出**任意长度**的栈；语义在**任意点**。

### `satW` 为什么接收 `input`

`Ladder.satW : W → Prop` 只接收权重，而「在某点上的行为」必须知道那个点。
本节让**实例本身**把 `input` 与 `target` 固定下来（它们是实例参数），
`satSym` 则从 `s` 里取同一对值。**`l2l3_sound` 的实质内容就是这两条陈述一致**。

### ⚠ 第 168 轮的诚实记录：`l2l3_sound` 是**重言**，而且不是笔误

`compileNet s = s.layers.map layerOfNet`，而 `layerOfNet` 是一个**保持结构**的强制转换
（`W := L.W`，`b := L.b`）。所以 `satSym s` 展开是
`netAct (compileNet s) s.input = s.target`，而 `satW s.input s.target (compileNet s)` 展开是**同一个命题**。
`l2l3_sound := fun _ h => h` 因此是唯一可能的证明。

**这不是靠更努力能证出来的东西**：符号侧 `LayerSym` 携带的数据与权重侧 `AffineLayer`
**完全相同**，`l2l3` 只换了包装。两个谓词在这种情形下必然重合，桥梁定理也就没有内容。

**要让它有内容，`l2l3` 必须改变表示。** 库里有现成的例子：
`CExprCodegen.toStack`（第 157 轮）把**表达式树**编译成**扁平的指令列表**，
`toStack_correct` 是真正的翻译正确性定理，而不是重言。**那种实例本文件没有建。**

**这一条登记为已知缺口，不隐藏**：它对应审计 P1-2「补一个 `satW` 对全输入成立的 `Ladder` 实例」，
且审计对 `l2l3_sound := exact h` 的判断是正确的。 -/
noncomputable def multiLayerLadder (n : ℕ) (input target : Fin n → ℝ) :
    Ladder (List (NetSym n)) (NetSym n) (NetSym n) (List (Lattice.Core.AffineLayer (Fin n))) where
  l0l1 := identityTokenizer (NetSym n)
  l1l2 :=
    { encode := fun s => [s]
      decode := fun ts => ts.head?
      roundtrip := fun _ => rfl }
  l2l3 := compileNet
  satSym := fun s => Lattice.Core.netAct (compileNet s) input = target
  satW := satW input target
  l2l3_sound := by
    intro s h
    exact h

/-- **端到端**：符号侧的计算事实 ⟹ 权重栈执行出同一结果（任意层数、任意点）。 -/
theorem multiLayerLadder_forward (n : ℕ) (input target : Fin n → ℝ) (s : NetSym n)
    (hs : s.input = input) (ht : s.target = target)
    (h : (multiLayerLadder n input target).satSym s) :
    (multiLayerLadder n input target).satW ((multiLayerLadder n input target).l2l3 s) :=
  Ladder.ladder_forward (multiLayerLadder n input target) s h

/-! ## 六、两层：多层的最小非平凡情形 -/

/-- **两层网络的实例**：这是「多层」这一词的**最小非平凡见证**。

一层的证明在 `weightLadderN` 里已有；**两层需要 `netAct` 的组合律**，
所以它检验的是「栈真的被展开执行」，而不是「单层被重复」。 -/
def twoLayerSym (L₁ L₂ : LayerSym n) (input target : Fin n → ℝ) : NetSym n where
  layers := [L₁, L₂]
  input := input
  target := target

/-- **两层的栈按顺序执行**：先 `L₁` 后 `L₂`。

这条把 `compileNet` 与 `netAct` 的 `foldl` 展开连起来，
说明 `l2l3` 产出的**真的是一个栈**，不是被压平的一个层。 -/
theorem twoLayer_act (L₁ L₂ : LayerSym n) (x : Fin n → ℝ) :
    Lattice.Core.netAct (compileNet (twoLayerSym L₁ L₂ x x)) x =
      Lattice.Core.affineAct (layerOfNet L₂) (Lattice.Core.affineAct (layerOfNet L₁) x) := by
  show Lattice.Core.netAct [layerOfNet L₁, layerOfNet L₂] x = _
  rfl

/-- **两层实例的端到端**：两层的结论与任意层数一致。 -/
theorem multiLayerLadder_two (L₁ L₂ : LayerSym n) (input target : Fin n → ℝ)
    (h : (multiLayerLadder n input target).satSym (twoLayerSym L₁ L₂ input target)) :
    (multiLayerLadder n input target).satW
      ((multiLayerLadder n input target).l2l3 (twoLayerSym L₁ L₂ input target)) :=
  Ladder.ladder_forward (multiLayerLadder n input target) (twoLayerSym L₁ L₂ input target) h

end MultiLayer

end Lattice.Lift
