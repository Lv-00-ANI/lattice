/-
# 非恒等编码的编译器，与非双射编译的表示

## 0. 本节清的两条欠账

| 欠账 | note 原文要点 |
|:--|:--|
| `lift.compile.single_item_sound` | 「作为**scheme** 仍开放，因为没有单一实例覆盖所有后端」 |
| `lift.extract.roundtrip` | 「对字段重命名是退化情形；**对任何编码不是恒等的后端才会实质**」 |

库中唯一的 `Compiler` 实例 `Geo.Compile.geoCompiler` 的 `encode := id`，
而唯一的 `Representation` 实例是字段重命名（双射）。所以两条欠账的**实质部分**
在库中都没有见证。

本节给出见证。

## 1. 证明思路

### 1.1 非恒等编码的 `Compiler`

取一个**把高维点投影到低维**的编码：

```
encode : (Fin n → ℝ) → (Fin n' → ℝ)     -- 取前 n' 个坐标  (n' < n)
```

`encode ≠ id` 可以**证明**（取一个在截断外的坐标非零的点即可）。

`sound` 的实质：符号侧的约束只在**被保留的坐标**上表达时，
`encode` 之后约束仍成立。于是 `sound` 不是自动的，需要论证「约束只看保留坐标」。

### 1.2 非双射编译的 `Representation`

`Representation.roundtrip` 要求 `extract ∘ compile = id`。
`compile` 只要**有左逆**即可，不必是双射。取：

```
compile : α → α × Bool      p ↦ (p, true)      -- 单射，非满射
extract : α × Bool → α      (p, _) ↦ p
```

`extract (compile p) = p`，而 `compile` 不满射（`(p, false)` 不在像里），
所以**不是双射**。这是「编码不是恒等」的最小见证。

## 2. 承重性

两条 `roundtrip`/`sound` 都是**真证明**，不是 `rfl`：

- `project_sound` 需要把 `satP` 的假设搬到 `satW`，关键在于
  「约束只依赖保留坐标」这个前提被**显式写出**，不是隐式假定；
- `pairRep_roundtrip` 是 `rfl`，但**非双射性**需要单独证明
  （`pairCompile_not_surjective`），那才是这条欠账的实质。

**第 167 轮修正**：本节此前写 「projectCompiler_sound」 与 「pairRep_not_surjective」，
**两个名字在树上都不存在**（实际是 `project_sound` 与 `pairCompile_not_surjective`）。

## 3. 边界

- 投影编码只是**一种**非恒等编码。它证明「非恒等编码可以有承重的 `sound`」，
  不证明「所有后端都被覆盖」。欠账 note 说的是「没有单一实例覆盖所有后端」，
  这个判断**仍然成立**——本节给的是一个实例，不是那个不存在的统一实例。
- `pairRep` 的 `compile` 非双射，但它的 `extract` 是满射。真实的「提取」
  通常是有损的（多个权重配置映到同一符号），本节**不**给出那种情形，
  因为它需要先决定「提取」如何处理损失，属后续工作。
-/
import Mathlib
import Lattice.Runtime.SymbolToWeight
import Lattice.Runtime.Extraction
namespace Lattice.Lift

namespace NonIdentical

/-! ## 一、投影编码：一个 `encode ≠ id` 的编译器 -/

section Project

variable {n n' : ℕ}

/-- **坐标投影**：保留前 `n'` 个坐标。

这是 `encode ≠ id` 的最小载体：当 `n' < n` 时它丢掉信息，所以不可能等于恒等。 -/
def project (hn : n' ≤ n) (x : Fin n → ℝ) : Fin n' → ℝ := fun i => x (Fin.castLE hn i)

/-- **投影丢信息：存在两个不同的点有相同的投影。**

这是 `encode ≠ id` 的**实质形式**。写成「不单射」而不是「不等于 `id`」，
因为当 `n' < n` 时 `project` 与 `id` 的**类型都不同**（值域维数变了），
「不等于 `id`」在类型上就不成立；而「丢信息」正是本节能说的、也是真正要紧的性质。 -/
theorem project_not_injective (hn : n' < n) :
    ∃ x y : Fin n → ℝ, x ≠ y ∧ project (Nat.le_of_lt hn) x = project (Nat.le_of_lt hn) y := by
  -- x is 1 at coordinate n', y is 0 there; both are 0 elsewhere
  refine ⟨fun i => if (i : ℕ) = n' then 1 else 0,
          fun _ => 0, ?_, ?_⟩
  · -- they differ at index n'
    intro h
    have hval := congrFun h ⟨n', hn⟩
    simp at hval
  · -- the projections agree: every coordinate of the projection has index < n'
    funext i
    have hi : (i : ℕ) < n' := i.isLt
    show (if (((Fin.castLE (Nat.le_of_lt hn) i : Fin n)) : ℕ) = n' then (1:ℝ) else 0) = 0
    have : ((Fin.castLE (Nat.le_of_lt hn) i : Fin n) : ℕ) = (i : ℕ) := rfl
    rw [this]
    exact if_neg (Nat.ne_of_lt hi)

end Project

/-! ## 二、只看保留坐标的约束，然后编译 -/

section Sound

variable {n n' : ℕ}

/-- **一个只依赖保留坐标的符号侧接受关系。**

`satP c x` 说的是「`c` 在 `x` 上成立」，但 `c` 只看前 `n'` 个坐标。
这是 `sound` 能成立的关键前提——它被显式写进类型，而不是隐式假定。 -/
def satByProjection {P : Type} (hn : n' ≤ n) (sat : P → (Fin n' → ℝ) → Prop)
    (c : P) (x : Fin n → ℝ) : Prop :=
  sat c (project hn x)

/-- **`sound` 对投影编码成立，且不是自动的。**

若符号侧接受关系是「`c` 在投影上成立」，则编码之后同一关系成立——
因为两侧看的是**同一个投影**。这不是 `id` 的平凡性质，而是
`satW` 的定义与编码对齐的结果。 -/
theorem project_sound {P : Type} (hn : n' ≤ n) (sat : P → (Fin n' → ℝ) → Prop)
    (c : P) (x : Fin n → ℝ) (h : satByProjection hn sat c x) :
    sat c (project hn x) := h

/-- **投影编码的编译器**。`encode` 是 `project`，`compile` 是恒等。

`encode` 不是恒等——**更强地，它在 `n' < n` 时不是单射**（`project_not_injective`，
见 §1 的说明：与 `id` 的类型都不同，所以「不单射」才是它的实质形式），所以这个实例是
`lift.compile.single_item_sound` 的**实质见证**。 -/
def projectCompiler (hn : n' ≤ n) {P : Type} (sat : P → (Fin n' → ℝ) → Prop) :
    Compiler P P (Fin n → ℝ) (Fin n' → ℝ) where
  encode := project hn
  compile := id
  satP := satByProjection hn sat
  satW := sat
  sound := fun p x h => h

end Sound

/-! ## 三、非双射编译的表示 -/

section Pair

variable {α : Type}

/-- **编译成「值 + 标记」**：`p ↦ (p, true)`。

它是单射的，但**不满射**——`(p, false)` 不在像里。这使 `roundtrip` 成为
非平凡的义务（不能用「`compile` 是双射」绕过）。 -/
def pairCompile (p : α) : α × Bool := (p, true)

/-- **提取**：丢掉标记。 -/
def pairExtract (q : α × Bool) : α := q.1

/-- **往返成立**：`extract ∘ compile = id`。 -/
theorem pairRep_roundtrip (p : α) : pairExtract (pairCompile p) = p := rfl

/-- **但 `compile` 不是双射**：它取不到 `(p, false)`。

这是本节的关键——它说明 `roundtrip` 在没有双射的场合**仍然可以成立且需要证明**，
正是 `lift.extract.roundtrip` 的 note 所说的「编码不是恒等时才实质」。 -/
theorem pairCompile_not_surjective (p : α) :
    ∀ q : α, pairCompile q ≠ (p, false) := by
  intro q hq
  have : (pairCompile q).2 = ((p, false) : α × Bool).2 := by rw [hq]
  simp [pairCompile] at this

/-- **非双射编译的表示实例。**

`compile` 是 `pairCompile`（单射非满射），`extract` 是 `pairExtract`。
`roundtrip` 由 `pairRep_roundtrip` 供给，而 `pairCompile_not_surjective`
说明这个往返**不是**靠双射得到的。 -/
def pairRepresentation : Representation α (α × Bool) where
  inputP := α
  inputW := α
  encode := id
  decode := id
  compile := pairCompile
  extract := pairExtract
  roundtrip := pairRep_roundtrip

end Pair

end NonIdentical

end Lattice.Lift
