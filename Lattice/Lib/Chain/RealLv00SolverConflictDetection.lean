import Mathlib

/-!
# 冲突检测的真实现：把上游的「恒返回空」桩换成有语义的计算（阶段 A，P0-5）

## 桩为什么是问题

**`RealLv00Solver.lean:512` 的 `ConflictDetector.detect` 恒返回空冲突集，于是
`conflict_empty_trail` 与 `conflict_resolve_fixed_point` 都是 `rfl` 级 —— 它们对**任何**实现都成立，
包括一个什么都不做的实现。**

**=> 这类定理不是错的，而是**空的**：它们没有排除任何情形，因此无法支撑任何关于求解器的结论。**

## 本文件做什么

**给出冲突检测的**真实语义**，并配一条**在桩下为假**的定理：**

```lean
detDetect_nonempty_of_conflict :
  detContradictoryAt trail v = true -> c ∈ clauses -> detMentions c v = true ->
    (detDetect clauses trail v).clauses ≠ []
```

**在桩下右侧恒等于 `[]`，此式**为假**。这就是「实现有语义」的机器证据。**

## 为什么单独开一个文件而不是改 `RealLv00Solver.lean`

**`RealLv00Solver.lean` 是上游 Lv-00 的忠实转写，其桩**带 `⚠` 标注**，属于「已登记的缺口」而非隐瞒。
改它会与 `Reference/Geometry/LvFormal/Theory/SolverInfrastructure.lean` 的独立副本产生不一致。**

**=> 正确做法是**并置**：保留上游转写（带其标注），另起一个文件给出真实现与其定理。
两者的差别本身就是证据 —— 桩下的定理是 `rfl`，真实现下的定理有内容。**

## 命名

**本文件的类型与函数一律带 `det` 前缀，因为它们与上游转写里的 `Clause`/`Trail`/`ConflictSet`
同名但**语义不同**（后者保留上游形状）。前缀避免 I3（定义唯一性）冲突。** -/

namespace Lattice.Lib.Chain.RealLv00SolverConflictDetection

/-- **子句**：一列带极性的变量。 -/
abbrev DetClause : Type := List (Nat × Bool)

/-- **赋值轨迹**：变量到取值的列表。 -/
abbrev DetTrail : Type := List (Nat × Bool)

/-- **冲突集**：出冲突的子句集合，以及它是否已被判为极小。

**=> `isMinimal` 不再恒为 `true`：真实现下它要由实际检查给出。** -/
structure DetConflictSet where
  /-- 参与冲突的子句。 -/
  clauses : List DetClause
  /-- 该集合是否已被判为极小。**恒 `true` 是桩的特征**；真实现必须计算它。 -/
  isMinimal : Bool

/-- **`trail` 在变量 `v` 上是否自相矛盾**：同时赋了真与假。 -/
def detContradictoryAt (trail : DetTrail) (v : Nat) : Bool :=
  trail.contains (v, true) && trail.contains (v, false)

/-- **子句是否提到变量 `v`。** -/
def detMentions (c : DetClause) (v : Nat) : Bool :=
  c.any (fun p => p.1 = v)

/-- **冲突检测的真实现：当 `trail` 在 `v` 上自相矛盾时，返回提到 `v` 的子句；否则返回空集。**

**=> 关键设计：以**候选冲突变量** `v` 为参数（由调用者从 `trail` 中挑出）。
这使定义保持可算且简单，而「检测会非空」成为**可证的**，而不是恒假。** -/
def detDetect (clauses : List DetClause) (trail : DetTrail) (v : Nat) : DetConflictSet :=
  if detContradictoryAt trail v then
    { clauses := clauses.filter (fun c => detMentions c v), isMinimal := false }
  else
    { clauses := [], isMinimal := false }

/-- **无矛盾的轨迹上检测为空。**

**=> 仍然成立，但理由变了：不是「实现恒空」，而是「`v` 不自相矛盾」。** -/
theorem detDetect_empty_of_no_conflict (clauses : List DetClause) (trail : DetTrail) (v : Nat)
    (h : detContradictoryAt trail v = false) : (detDetect clauses trail v).clauses = [] := by
  simp [detDetect, h]

/-- **真实现才有的内容：自相矛盾时，若某子句提到 `v`，则检测**非空**。**

**=> **这条在桩实现下为假**（右侧恒等于 `[]`）。它排除了「什么都不做」的实现，
因此是把桩换成真实现的**机器证据**。** -/
theorem detDetect_nonempty_of_conflict (clauses : List DetClause) (trail : DetTrail) (v : Nat)
    (hv : detContradictoryAt trail v = true) (c : DetClause) (hc : c ∈ clauses)
    (hm : detMentions c v = true) :
    (detDetect clauses trail v).clauses ≠ [] := by
  simp only [detDetect, hv, if_true]
  intro hnil
  have hmem : c ∈ clauses.filter (fun c => detMentions c v) := List.mem_filter.mpr ⟨hc, hm⟩
  rw [hnil] at hmem
  simp at hmem

/-- **极小性不再恒真：本实现给出 `false`（未检查），而桩给出 `true`。**

**=> 这条把「`isMinimal := true` 是桩特征」写成可检查的事实。** -/
theorem detDetect_isMinimal_eq_false (clauses : List DetClause) (trail : DetTrail) (v : Nat) :
    (detDetect clauses trail v).isMinimal = false := by
  unfold detDetect
  split <;> rfl

end Lattice.Lib.Chain.RealLv00SolverConflictDetection
