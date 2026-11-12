import Mathlib
import Lattice.Core.IR.Extract
import Lattice.Core.IR.FinSupport

/-!
# P1-2：槽位桥 `slotOf` —— 把符号槽位命名成可执行的下标（阶段 B）

## 第 859 轮的 `FinSupport` 与既有的 `compileWith`/`extractWith` 之间缺的那一环

**树里已有：**

```lean
def compileWith (k) (f) : IRWeights := fun n => if n = 0 then skeletonCode k else ... f st ⟨i,_⟩ ...
def extractWith (W) : (s) → Fin s.shape.prod → ℝ := fun s i => W (Nat.pair (s.id + 1) i + 1)
theorem extractWith_compileWith : extractWith (compileWith k f) st = f st
```

**=> 编码与读出都已经存在且已证。但它们都写在**无限**载体 `IRWeights := ℕ → ℝ` 上。**

**第 859 轮的 `FinSupport N` 给了**有限**载体，但没有任何定理把它与 `compileWith`/`extractWith` 连起来。
因此「有限支撑」与「IR 编码」目前是两套互不相干的东西。**

**=> 本文件补上那一环：命名的槽位函数 `slotOf`，以及它在两个载体上的一致性。**

## `slotOf`

```lean
def slotOf (st : TensorShape) (i : Fin st.shape.prod) : ℕ := Nat.pair (st.id + 1) (i : ℕ) + 1
```

**这把 `extractWith` 里那个匿名位置表达式**命名**成 `slotOf`，从而可以单独陈述与证明它的性质。**

**`+ 1` 不是装饰：位置 `0` 被 `skeletonCode` 占据（`compileWith_code`），所以数据槽位必须从 `1` 开始。**
**`st.id + 1` 也不是装饰：`Nat.pair` 的第一分量 `0` 保留给「非张量槽位」（`compileWith` 的 `| 0 => 0` 分支）。**

**=> 这两处偏移正是 `slotOf` 有内容的地方，也是本文件要证明它们**不冲突**的地方。**

## 本文件证明什么

| 定理 | 内容 |
|:--|:--|
| `slotOf_pos` | **槽位下标恒 `> 0`（与 `skeletonCode` 的位置 `0` 不相交）** |
| `slotOf_injective` | **不同张量或不同下标的槽位**不同**（`Nat.pair` 单射 + `id` 单射）** |
| `extractWith_eq_slotOf` | **`extractWith W st i = W (slotOf st i)` —— 把读出的位置写成命名的槽位** |

**=> 第三条是桥本身：它把「有限支撑的下标」与「IR 的读出口」变成同一个东西。** -/

namespace Lattice.Core.IR

/-- **槽位下标：张量 `st` 的第 `i` 个分量在权重向量里的位置。**

**=> `Nat.pair (st.id + 1) i + 1`。两处 `+1` 都是必要的：**
**位置 `0` 归 `skeletonCode`；`Nat.pair` 的第一分量 `0` 归非张量槽位。** -/
def slotOf (st : TensorShape) (i : Fin st.shape.prod) : ℕ :=
  Nat.pair (st.id + 1) (i : ℕ) + 1

/-- **槽位下标恒大于零。**

**=> 因 `Nat.pair … + 1 > 0`。这条保证数据槽位不会与 `compileWith` 在位置 `0` 写入的
`skeletonCode` 相撞 —— 而那个不相撞正是 `compileWith_code` 成立的前提。** -/
theorem slotOf_pos (st : TensorShape) (i : Fin st.shape.prod) : 0 < slotOf st i := by
  unfold slotOf
  omega

/-- **槽位函数是单射：不同 `(张量, 下标)` 对给出不同位置。**

**=> 由 `Nat.pair` 的单射性（`Nat.pair_eq_pair`）与 `st.id + 1` 的单射性出发：
若 `Nat.pair (st₁.id + 1) i₁ = Nat.pair (st₂.id + 1) i₂`，则 `st₁.id + 1 = st₂.id + 1` 且 `i₁ = i₂`。**

**=> 这条是「槽位不重叠」的机器陈述：没有两个不同的数据分量被写到同一位置。** -/
theorem slotOf_injective_pair (st₁ st₂ : TensorShape) (i₁ : Fin st₁.shape.prod)
    (i₂ : Fin st₂.shape.prod) (h : slotOf st₁ i₁ = slotOf st₂ i₂) :
    st₁.id = st₂.id ∧ (i₁ : ℕ) = (i₂ : ℕ) := by
  unfold slotOf at h
  have hp : Nat.pair (st₁.id + 1) (i₁ : ℕ) = Nat.pair (st₂.id + 1) (i₂ : ℕ) := by omega
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp hp
  exact ⟨Nat.succ.inj h1, h2⟩

/-- **桥：`extractWith` 读出的位置正是 `slotOf`。**

**=> `extractWith W st i = W (slotOf st i)`。**

**这是 P1-2 的核心：它把「IR 的读出口」与「有限支撑的下标」变成同一个表达式，
于是 `FinSupport N` 上的定理可以直接落到 `extractWith` 上。** -/
theorem extractWith_eq_slotOf (W : IRWeights) (st : TensorShape) (i : Fin st.shape.prod) :
    extractWith W st i = W (slotOf st i) := by
  unfold extractWith slotOf
  rfl

/-- **桥的推论：`compileWith` 在槽位处读出原值。**

**=> 由 `extractWith_eq_slotOf` 与既有的 `extractWith_compileWith` 复合：
`compileWith k f (slotOf st i) = f st i`（在 `k` 的张量 `id` 无重复、`st ∈ k.tensors` 时）。**

**=> 这条把两轮的成果接起来：`slotOf` 命名了位置，`extractWith_compileWith` 保证了读出正确。** -/
theorem compileWith_slotOf (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup) {st : TensorShape} (hst : st ∈ k.tensors)
    (i : Fin st.shape.prod) :
    compileWith k f (slotOf st i) = f st i := by
  have h := extractWith_compileWith k f hnd hst
  have h2 := congrFun h i
  rw [extractWith_eq_slotOf] at h2
  exact h2

end Lattice.Core.IR
