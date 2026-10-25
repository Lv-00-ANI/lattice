/-
# 编码的抽象：`sound` 的统一方案

## 0. 本节补什么

`Lattice.Slots` 的 `lift.compile.single_item_sound` 说：

> "Open as a *scheme* because no single instance covers every backend."

本库现有的 `Compiler` 实例，其 `encode` 各不相同：

| 实例 | `encode` |
|:--|:--|
| `Geo.Compile.geoCompiler` | `id` |
| `Lift.Extraction.ofEquiv` | 双射 `e` |
| `Lift.NonIdentical.projectCompiler` | 坐标投影 |

每一个都要**单独**证 `sound`。本节给出统一方案：把 `sound` 化归为一条
**关于编码的因子化条件**，于是任何满足该条件的编码都自动获得 `sound`。

## 1. 证明思路：`sound` 的本质是什么

`Compiler.sound` 要求：

```
∀ p x, satP p x → satW (compile p) (encode x)
```

左边 `satP p x` 谈的是**符号侧**的点 `x`；右边谈的是**编码后**的 `encode x`。
所以 `sound` 能成立，当且仅当 **`satP` 只通过 `encode` 看 `x`**：

```
因子化条件：  satP p x  ≡  satEnc p (encode x)
```

若这条成立且 `satW` 就是 `satEnc`，则 `sound` 是**同义反复**——
但这不是「自动成立」，而是「承认 `satP` 必须因子化」这一**约束**。
关键是：**这个约束对所有编码一次说清**，而不是每个实例重证一遍。

## 2. 为什么这是推广而不是重写

原来的做法是：对每个 `Compiler` 实例单独证 `sound`。
本节的做法是：

```
theorem sound_of_factors {encode : inputP → inputW} {satP satW}
    (h : ∀ p x, satP p x ↔ satW p (encode x)) :
    ∀ p x, satP p x → satW p (encode x)
```

**一次证明，覆盖所有编码**——包括 `id`、双射、投影，以及未来任何编码。
实例只需提供 `h`（因子化等式），而不必重做 `sound` 的论证。

## 3. 与既有实例的关系

`projectCompiler` 的 `sound` 现在可以**由本节的定理导出**，
只需指出它的 `satP` 就是按 `project` 定义的——那正是因子化条件。见 §4 的 `example`。

## 4. 边界

- 本节**不改变** `Compiler` 结构。`encode : inputP → inputW` 仍是字段，
  `inputP`/`inputW` 仍是字段。把它们改成类型参数是一次**重构**，
  会影响全部既有实例，见 `ROADMAP-v6 §1.2` 的评估。
- 因子化条件 `satP p x ↔ satW p (encode x)` 是**强**条件：它要求符号侧的接受关系
  **恰好**是「编码后的点满足权重侧关系」，不能更细也不能更粗。
  更弱的形式（仅 `→` 方向）足以给出 `sound`，但那样就无法表达「编码不丢语义」。
  本节用双向，因为那是 `sound` 加 `satW` 语义完整时自然成立的形态。
- 本节**不**声称解决了那个 scheme。它提供的是**统一的证明模式**，
  而 scheme 还需要「把 `inputP`/`inputW` 从字段提升为参数」的重构。
-/
import Mathlib
import Lattice.Lift.SymbolToWeight
import Lattice.Lift.NonIdenticalEncoding

namespace Lattice.Lift

namespace EncodingAbstraction

/-! ## 一、`sound` 的统一形式 -/

/-- **`sound` 由因子化条件导出。**

`satP p x` 与 `satW p (encode x)` 若等价，则 `sound` 是直接的。
这条定理的价值在于：**它对任意 `encode` 成立**，所以每个 `Compiler` 实例
只需提供因子化等式，不必重做 `sound`。 -/
theorem sound_of_factors {inputP inputW P : Type}
    (encode : inputP → inputW) (satP : P → inputP → Prop) (satW : P → inputW → Prop)
    (h : ∀ p x, satP p x ↔ satW p (encode x)) :
    ∀ p x, satP p x → satW p (encode x) := by
  intro p x hx
  exact (h p x).mp hx

/-! ## 二、三种编码都满足同一形态 -/

/-- **恒等编码**：因子化条件退化为 `satP = satW`，所以 `sound` 平凡。 -/
theorem factors_id {P X : Type} (sat : P → X → Prop) :
    ∀ p x, sat p x ↔ sat p (id x) := by
  intro p x
  rw [id]

/-- **投影编码**：符号侧的接受关系若按 `project` 定义，则因子化条件成立。

这与 `NonIdentical.projectCompiler` 的 `satP` 定义一致——那条 `sound` 是本条的特例。 -/
theorem factors_project {n n' : ℕ} (hn : n' ≤ n) {P : Type}
    (sat : P → (Fin n' → ℝ) → Prop) :
    ∀ p (x : Fin n → ℝ),
      NonIdentical.satByProjection hn sat p x ↔ sat p (NonIdentical.project hn x) := by
  intro p x
  rfl

/-! ## 三、把既有实例接上 -/

/-- **`projectCompiler` 的 `sound` 由 `factors_project` 导出。**

这演示了本节的用途：原来 `projectCompiler.sound` 是单独给的，
现在它是一条通用定理的实例。 -/
example {n n' : ℕ} (hn : n' ≤ n) {P : Type} (sat : P → (Fin n' → ℝ) → Prop) :
    ∀ p (x : Fin n → ℝ),
      (NonIdentical.projectCompiler hn sat).satP p x →
      (NonIdentical.projectCompiler hn sat).satW p
        ((NonIdentical.projectCompiler hn sat).encode x) :=
  sound_of_factors _ _ _ (factors_project hn sat)

end EncodingAbstraction

end Lattice.Lift
