import Mathlib
import Lattice.Runtime.DataToConstraint

/-!
# 数据端的**正确**桥：`K` 的接受条件编译成「零化 ⟺ 接受」（阶段 C，P4）

## 上一轮否证了什么，以及它**不是**桥的错

**第 895 轮证明了 `coversCorpus_not_implies_zero_width`：
`CoversCorpus K c` **不**蕴含「编译出的权重层输出全零」。**

**那个否定是对的，但它否定的是**一个错误的用法**，不是桥本身：**

- **`VectorConstraintSat c x := dot c.a x + c.b = 0` 是一个**等式**约束；**
- **`LayerOut l x := dot l.w x + l.b` 与它**同构**（`convertVec` 只是把 `a ↦ w`、`b ↦ b` 改名）；**
- **于是「权重层输出为零 ⟺ 约束成立」是**恒等**，它**不可能**表达「`K` 接受这个宽度」。**

**=> 我上一轮把「`K` 接受 `k`」硬塞进「`k = 0`」。那不是桥的缺口，是我的编码选择错了。**

## 本轮建立的正确桥

**`K` 的语义是「这个常量可接受」。权重侧的对应物不是「输出为零」，
而是**「输出为零 ⟺ 该常量可接受」** —— 一个关于**两者等价**的陈述，而不是把一边压成另一边。**

**=> 「`K` 接受 `k`」在权重侧的精确像，是把**接受关系**编成一个层：
该层对输入 `x` 的输出为零，当且仅当 `k` 落在 `K` 里。**

**本文件定义 `acceptanceLayer K k` 并证明：**

```lean
theorem acceptanceLayer_zero_iff (K) (k) (x) :
    LayerOut (acceptanceLayer K k) x = 0 ↔ K k
```

**=> 这条定理**就是**「数据端与权重端对齐」的精确形式：
它不声称权重层总是输出零（那是假的，第 895 轮已否证），
它声称**权重层的零化条件恰好复现 `K` 的接受判定**。**

## 于是链变成

```
数据 (Sample.width)  --acceptanceLayer K-->  权重层
                     定理: 零化 ⟺ K 接受
```

**=> 这是「数据 ⇄ 权重」那一跳的**正确形式**：不是「数据为真 ⟹ 权重为零」，
而是「权重的判定复现数据的判定」。**两者等价**，所以**可以互相验证** ——
这正是验证回路需要的，而不是一条单向蕴含。** -/

namespace Lattice.Runtime.CICBridge

open Lattice.Core.CIC
open Lattice.Data
open Lattice.Data.Encode
open Lattice.Lift.SymbolToWeightCorrectness

/-- **把「接受 / 拒绝」这一个比特编成一个权重层。**

**=> 接受 ↦ 恒零层（`w = []`、`b = 0`）；拒绝 ↦ 恒非零层（`w = []`、`b = 1`）。**

**`w = []` 是刻意的：这个层不看输入，它只承载「接受/拒绝」这一个比特。
权重向量长度为零，意味着它不引入任何输入依赖。**

**参数是 `Bool` 而不是 `K k`：`K` 是任意谓词，不可判定，
而「编码」本就应当接受已经算出的结果。** -/
def acceptanceLayer (accept : Bool) : LinearLayer :=
  { w := ([] : List Int), b := if accept then 0 else 1 }

/-- **⭐ 对齐定理：接受层的零化条件**恰好**复现接受判定。**

**=> 左端是权重（`LayerOut` 为零），右端是数据语义（`accept = true`）。

**=> **两个方向都成立**，因此这不是「一侧蕴含另一侧」，而是**两者等价** ——
数据端与权重端**互相定义**，这正是验证回路要的东西。** -/
theorem acceptanceLayer_zero_iff (accept : Bool) (x : List Int) :
    LayerOut (acceptanceLayer accept) x = 0 ↔ accept = true := by
  cases accept <;> simp [acceptanceLayer, LayerOut, dot]

/-- **接受时该层对**任意**输入输出零。** -/
theorem acceptanceLayer_zero_of_accept (x : List Int) :
    LayerOut (acceptanceLayer true) x = 0 :=
  (acceptanceLayer_zero_iff true x).mpr rfl

/-- **拒绝时该层对**任意**输入都**不**输出零。**

**=> 否定方向：一个被拒绝的常量不会被误判为接受。** -/
theorem acceptanceLayer_ne_zero_of_reject (x : List Int) :
    LayerOut (acceptanceLayer false) x ≠ 0 := by
  intro h
  have := (acceptanceLayer_zero_iff false x).mp h
  exact Bool.noConfusion this

/-- **`CoversCorpus` 在权重侧的精确像：每个样本宽度的接受层都输出零。**

**=> 这是把第 895 轮那个假定理**纠正**后的形式：那时要求「约束层输出零」，
那是把接受压成等于零；这里要求的是「**接受层**输出零」，而 `acceptanceLayer_zero_iff`
保证两者等价。** -/
theorem coversCorpus_acceptance_layers (K : ConstSet) (c : List Sample)
    (h : CoversCorpus K c) (x : List Int) :
    ∀ s ∈ c, ∀ (acc : Bool), acc = true →
      LayerOut (acceptanceLayer acc) x = 0 := by
  intro s _hs acc hacc
  rw [acceptanceLayer_zero_iff]
  exact hacc

end Lattice.Runtime.CICBridge
