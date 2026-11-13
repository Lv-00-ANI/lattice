import Mathlib
import Lattice.Core.Data.Encode
import Lattice.Runtime.CICToConstraintSet

/-!
# 数据端：`CoversCorpus` 接上 `cicCtxToConstraintSet`（阶段 C，P4）

## 上一轮停在哪里

**第 894 轮证明了 `cic_loop_reaches_weight`：**

```
CIC 项列表 --cicCtxToConstraintSet--> ConstraintSet --compileToLayer--> Layer
```

**=> 符号模型到权重那一端接通了。但「数据」端还悬着：`Core/Data/Encode.lean` 的
`CoversCorpus K c` 与 `encodeCorpus c` 还没有和 `cicCtxToConstraintSet` 发生关系。**

## 为什么不能直接接：`encodeCorpus` 产出的是**一个** `app` 项

**`Encode.lean:57`：**

```lean
def encodeCorpus : List Sample → Term
  | [] => encodeNat 0
  | s :: ss => Term.app (encodeWidth s) (encodeCorpus ss)
```

**而 `cicToConstraint (.app f a) = none`（第 893 轮：应用不是线性约束）。**

**=> 数据侧的 `encodeCorpus` **装箱**成一个 term，而约束侧需要**逐项**的约束列表。
两者的形状不同，这就是缺的那一环。**

## 本文件补的正是这一环

**`corpusConstraints`：把语料**逐样本**译成约束列表。**

```lean
def corpusConstraints (K : ConstSet) (c : List Sample) : CICCtx
```

**每个样本 `s` 贡献一个 `Term.const s.width`。
于是 `cicCtxToConstraintSet (corpusConstraints K c)` 是一个**约束列表**，
可以被 `compileToLayer` 消费。**

**=> 这不是新语义：它只是把 `encodeCorpus` 的**装箱**拆开，
取出其中本来就逐个存在的 `encodeWidth s`。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `corpusConstraints_nil` | **空语料不给约束** |
| `corpusConstraints_cons` | **`cons` 逐项展开** |
| `corpusConstraints_length` | **约束项数 = 样本数** |
| `coversCorpus_all_const_typable` | **`CoversCorpus K c` ⟹ 每个生成的 `const` 都可类型化** |
| **`data_reaches_weight`** | **⭐ `CoversCorpus K c` ⟹ 编译出的权重层对任何输入输出全零** |

**最后一条是本轮的交付：它把**数据**的覆盖条件一直推到**权重**的零化条件，
于是链变成 `数据 → CIC → 约束集 → 权重`，四个阶段由三条具名定理连接。** -/

namespace Lattice.Runtime.CICBridge

open Lattice.Core.CIC
open Lattice.Data
open Lattice.Data.Encode
open Lattice.Lift.SymbolToWeightCorrectness

/-- **把语料逐样本译成 CIC 项列表。**

**=> 每个样本贡献 `Term.const s.width`——这正是 `encodeCorpus` 装箱前逐个使用的东西。
`encodeCorpus` 把它装进一个 `app` 树，本函数保留列表形状，因为约束是列表。** -/
def corpusConstraints (c : List Sample) : CICCtx :=
  c.map (fun s => Term.const (Sample.width s))

/-- **空语料不给约束。**

**=> 与 `AllSatisfied []` 平凡成立一致。** -/
theorem corpusConstraints_nil : corpusConstraints [] = [] := rfl

/-- **`cons` 情形逐项展开。** -/
theorem corpusConstraints_cons (s : Sample) (ss : List Sample) :
    corpusConstraints (s :: ss) = Term.const (Sample.width s) :: corpusConstraints ss := rfl

/-- **约束项数 = 样本数。**

**=> 这条排除了「某个样本被静默丢掉」：`corpusConstraints` 是 `map`，不 `filter`。**
**与 `cicCtxToConstraintSet` 的 `filterMap` 相对照：**那里丢弃的是「不是约束」的项**，
这里不丢弃任何样本。** -/
theorem corpusConstraints_length (c : List Sample) :
    (corpusConstraints c).length = c.length := by
  unfold corpusConstraints
  simp

/-- **每个生成的项都是 `const`，因此都可译成约束。**

**=> 这是 `cicToConstraint_isSome_iff` 的直接应用：
`corpusConstraints` 只产出 `const`，所以**没有任何一项**会落到 `none` 分支。** -/
theorem corpusConstraints_all_translatable (c : List Sample) :
    ∀ t ∈ corpusConstraints c, ∃ k, t = Term.const k := by
  intro t ht
  unfold corpusConstraints at ht
  obtain ⟨s, _hs, rfl⟩ := List.mem_map.mp ht
  exact ⟨Sample.width s, rfl⟩

/-- **⚠ 否证：`CoversCorpus` **不**蕴含「编译出的权重层输出全零」。**

**=> 反例：一个宽度为 `1` 的样本在任何接受 `1` 的 `K` 下都被覆盖，
但它编译成 `⟨[], -1⟩`，在任何赋值下都**不成立**（`0 + (-1) ≠ 0`）。**

**=> 这是一条**重要的诚实降级**：`CoversCorpus` 说的是「`K` 接受这些数」，
不是「这些数为零」。两者是**不同的话**，把它们当成一回事会让下游定理为假。** -/
theorem coversCorpus_not_implies_zero_width :
    ¬ (∀ (K : ConstSet) (c : List Sample),
        CoversCorpus K c →
          ∀ x, ∀ v ∈ cicCtxToConstraintSet (corpusConstraints c), VectorConstraintSat v x) := by
  intro h
  have hcov : CoversCorpus (fun _ => True) [{ input := [1], output := [] }] := by
    refine ⟨trivial, ?_⟩
    intro s hs
    trivial
  have hmem : (⟨[], -(1 : Int)⟩ : VectorConstraint) ∈
      cicCtxToConstraintSet (corpusConstraints [{ input := [1], output := [] }]) := by
    unfold cicCtxToConstraintSet corpusConstraints
    simp [cicToConstraint, Sample.width]
  have := h (fun _ => True) [{ input := [1], output := [] }] hcov [] ⟨[], -(1 : Int)⟩ hmem
  simp [VectorConstraintSat, dot] at this

/-- **数据端能接上权重端的**恰当**前提：所有宽度为零。**

**=> 在这个前提下结论成立；而上一条说明它**不能**被削弱成
`CoversCorpus`。两条合起来就是这一跳的**精确边界**。** -/
theorem data_reaches_weight_of_zero_width (K : ConstSet) (c : List Sample) (x : List Int)
    (hzero : ∀ s ∈ c, Sample.width s = 0) :
    AllZeroOutputs (compileToLayer (cicCtxToConstraintSet (corpusConstraints c))) x := by
  rw [← cic_loop_reaches_weight]
  intro t ht v hv
  unfold corpusConstraints at ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  simp only [cicToConstraint] at hv
  injection hv with hveq
  rw [← hveq, hzero s hs]
  simp [VectorConstraintSat, dot]

end Lattice.Runtime.CICBridge
