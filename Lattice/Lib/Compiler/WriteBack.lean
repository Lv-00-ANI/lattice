import Lattice.Lib.Compiler.Layout
import Lattice.Lib.Compiler.Samples
import Lattice.Core.RepairModule.Repair

/-!
# **P0-c：真实写回——修复作用于**权重载荷**，且可观察值确实改变**

## 规划要求什么

规划 §3.3 C.2 要求最终定理同时给出四件事：

| 项 | 本文件 |
|:--|:--|
| **改到的部分** | 第 0 段的斜率被改成目标值 `a`（`slopeFix_sat`） |
| **保留的部分** | 第 0 段的截距不变、其余所有段不变（`slopeFix` 的定义 + `slopeFix_preserves_rest`） |
| **到达方式** | **有限一步**（不是极限，也不是「ε 内」） |
| **失败分支** | 本实例**没有**失败分支：`slopeFix` 对任意族都有定义（`total by construction`） |

**⇒ C.3 还要求「把结论落实到实际写回的模型产物的求值上」**——这正是 `writeBack` 与
`write_back_verifies_and_changes` 做的事：修好的载荷被**重新编码成权重**，新产物的 `evalAt` 被
重新求值，并且那条定理同时说「约束已满足」与「可观察值确实变了」。

## 为什么选「斜率」这个约束

**因为它是**可判定的**、**单位置的**、且**行为可见的**：**
- 可判定：`(g 0).m = a` 是结构字段的等式；
- 单位置：只动第 0 段，故「保留的部分」可以精确陈述，而不是含糊地说「尽量少改」；
- 行为可见：`Segment.eval = m·x + c`，所以在**任意 x ≠ 0 且 `segmentIndex n x = 0`** 处，
  斜率变化必然改变求值——这就是「修复不是只改内部表示」的证明。

**⇒ 这不是一个「为了闭环形状而造」的玩具**：规划 §8.2 禁止的是把 `Repair` 抬升为双向 `Carrier`；
本文件不碰 `Carrier`，而是把 `Repair` **第一次装到权重载荷上**。
-/

namespace Lattice.Lib.Compiler.WriteBack

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler
open Lattice.Core

/-- **判据**：第 0 段的斜率等于目标值 `a`。 -/
def slopeSat (a : ℝ) (g : ℕ → Segment) : Prop := (g 0).m = a

/-- **修复**：把第 0 段的斜率置为 `a`，截距保留，其余段**逐段不变**。 -/
def slopeFix (a : ℝ) (g : ℕ → Segment) : ℕ → Segment :=
  fun k => if k = 0 then ⟨a, (g 0).c⟩ else g k

/-- **度量**：满足则 0，否则 1。**⇒ 取 `ℕ` 值，因为这是「一步到位」的修复：不存在需要数步的情形。** -/
noncomputable def slopeMeasure (a : ℝ) (g : ℕ → Segment) : ℕ :=
  if (g 0).m = a then 0 else 1

/-- **⭐⭐ 修复实例：`Repair (ℕ → Segment)`。**

**⇒ 三条义务都被证明，而不是假定：**
- `absorbs`：已满足者不改（因为它已经是 `⟨a, c⟩` 形状）；
- `decreases`：不满足者修一步后度量**严格下降**（`0 < 1`，因为修复后必满足）；
- `atomic`：度量为 `0` 者必满足。 -/
noncomputable def slopeRepair (a : ℝ) : Lattice.Core.Repair (ℕ → Segment) where
  Sat := slopeSat a
  fix := slopeFix a
  μ := slopeMeasure a
  absorbs := by
    intro g hg
    funext k
    by_cases hk : k = 0
    · subst hk
      show (if (0 : ℕ) = 0 then ⟨a, (g 0).c⟩ else g 0) = g 0
      rw [if_pos rfl]
      have h0 : g 0 = ⟨a, (g 0).c⟩ := by
        cases h : g 0 with
        | mk m c =>
            simp only [slopeSat] at hg
            simp only [h] at hg
            simp [hg]
      rw [h0]
    · show (if k = 0 then ⟨a, (g 0).c⟩ else g k) = g k
      rw [if_neg hk]
  decreases := by
    intro g hg
    -- **修复后必满足，故度量变成 0；未满足时度量是 1。**
    have hfix : slopeSat a (slopeFix a g) := by
      show (if (0 : ℕ) = 0 then ⟨a, (g 0).c⟩ else g 0).m = a
      rw [if_pos rfl]
    have h0 : slopeMeasure a (slopeFix a g) = 0 := by
      show (if (slopeFix a g 0).m = a then 0 else 1) = 0
      exact if_pos hfix
    have h1 : slopeMeasure a g = 1 := by
      show (if (g 0).m = a then 0 else 1) = 1
      exact if_neg hg
    rw [h0, h1]
    exact Nat.zero_lt_one
  atomic := by
    intro g hg
    show (g 0).m = a
    by_contra hne
    have : slopeMeasure a g = 1 := by
      show (if (g 0).m = a then 0 else 1) = 1
      exact if_neg hne
    rw [this] at hg
    exact absurd hg (by norm_num)

/-- **⭐ 修复后判据成立。** -/
theorem slopeFix_sat (a : ℝ) (g : ℕ → Segment) : slopeSat a (slopeFix a g) := by
  show (if (0 : ℕ) = 0 then ⟨a, (g 0).c⟩ else g 0).m = a
  rw [if_pos rfl]

/-- **⭐ 修复只动第 0 段：其余段逐段不变。** -/
theorem slopeFix_preserves_rest (a : ℝ) (g : ℕ → Segment) {k : ℕ} (hk : k ≠ 0) :
    slopeFix a g k = g k := by
  show (if k = 0 then ⟨a, (g 0).c⟩ else g k) = g k
  rw [if_neg hk]

/-- **⭐ 修复不改变第 0 段的截距。** -/
theorem slopeFix_keeps_intercept (a : ℝ) (g : ℕ → Segment) :
    (slopeFix a g 0).c = (g 0).c := by
  show (if (0 : ℕ) = 0 then ⟨a, (g 0).c⟩ else g 0).c = (g 0).c
  rw [if_pos rfl]

/-- **常分段族**：用来构造一个**具体**的违规产物。 -/
def constFamily (b c : ℝ) : ℕ → Segment := fun _ => ⟨b, c⟩

/-- **⭐⭐ 修复改变了一个**可观察量**（不是只改内部表示）。**

**⇒ 取一个**第 0 段内且 `x ≠ 0`** 的点（由调用者给出：`segmentIndex r.n x = 0` 与 `x ≠ 0`）。
则求值读到第 0 段，斜率从 `b` 变成 `a`，且 `m·x` 项非零，故求值**确实不同**。**

**⇒ 為什么不把 `x` 写死：因为「哪个 `x` 落在第 0 段」取决于 `r.n`；
把它作为前提交给调用者，比在定理里假设 `r.n = 1` 更强也更诚实。** -/
theorem repair_changes_observable (a b c : ℝ) (hba : b ≠ a) (n : ℕ) (x : ℝ)
    (hx0 : x ≠ 0) (hidx : segmentIndex n x = 0) :
    gridEval (slopeFix a (constFamily b c)) n x ≠ gridEval (constFamily b c) n x := by
  -- **先把两边求值**算出来**，再比较实数。
  -- **直接 `simp` 会把 `if` 的条件化约成 `True` 但不化约 `if` 本身，
  -- 于是目标形状与任何人写的 `show` 都不匹配——效果上是把证明推给了演绎器。**
  have hfix0 : slopeFix a (constFamily b c) 0 = (⟨a, c⟩ : Segment) := by
    show (if (0 : ℕ) = 0 then (⟨a, (constFamily b c 0).c⟩ : Segment) else constFamily b c 0)
        = (⟨a, c⟩ : Segment)
    rw [if_pos rfl]
    rfl
  have hconst0 : constFamily b c 0 = (⟨b, c⟩ : Segment) := rfl
  have e1 : gridEval (slopeFix a (constFamily b c)) n x = a * x + c := by
    unfold gridEval
    rw [hidx, hfix0]
    rfl
  have e2 : gridEval (constFamily b c) n x = b * x + c := by
    unfold gridEval
    rw [hidx, hconst0]
    rfl
  rw [e1, e2]
  intro h
  -- `a * x + c = b * x + c` ⇒ `(a - b) * x = 0` ⇒ `a = b` 或 `x = 0`
  have hx : (a - b) * x = 0 := by linarith
  rcases mul_eq_zero.mp hx with h1 | h2
  · have : a = b := by linarith
    exact hba this.symm
  · exact hx0 h2

/-! ## 写回：把修好的载荷重新编码成权重，并在新产物上重新验证 -/

/-- **写回**：把载荷 `g` 重新编码进权重，构成**新的**产物。 -/
noncomputable def writeBack (g : ℕ → Segment) (dom : Lattice.Lib.Compiler.SemDomain)
    (r : Lattice.Lib.Compiler.CompileRecipe) : Lattice.Lib.Compiler.EvaluatedArtifact :=
  Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments g dom r

/-- **写回后的求值**就是该载荷的网格求值（由产物契约的往返保证）。 -/
theorem writeBack_evalAt (g : ℕ → Segment) (dom : Lattice.Lib.Compiler.SemDomain)
    (r : Lattice.Lib.Compiler.CompileRecipe) (x : ℝ) :
    (writeBack g dom r).evalAt x = some (gridEval g r.n x) :=
  Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments g dom r x

/-- **⭐⭐⭐ P0-c 的收口：写回后**既满足约束、又可观察值改变**。**

**⇒ 两个合取项分别是规划 C.2 的「改到的部分」与 C.5 的「可观察变化」，
而且都落在**写回后的产物**上。** -/
theorem write_back_verifies_and_changes (a b c : ℝ) (hba : b ≠ a)
    (dom : Lattice.Lib.Compiler.SemDomain) (r : Lattice.Lib.Compiler.CompileRecipe)
    (x : ℝ) (hx0 : x ≠ 0) (hidx : segmentIndex r.n x = 0) :
    slopeSat a (slopeFix a (constFamily b c))
      ∧ (writeBack (slopeFix a (constFamily b c)) dom r).evalAt x
          ≠ (writeBack (constFamily b c) dom r).evalAt x := by
  refine ⟨slopeFix_sat a (constFamily b c), ?_⟩
  rw [writeBack_evalAt, writeBack_evalAt]
  exact fun h => repair_changes_observable a b c hba r.n x hx0 hidx (Option.some.inj h)

end Lattice.Lib.Compiler.WriteBack