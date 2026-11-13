/-
# `Compose/Registry` —— 登记表与组合矩阵（**参数版**）

## 0. 参数化的代价在这里付

`Primitive` 现在是 `Primitive (I O : Type)`，所以**它不再是单一 `Type`**。
一个「混合的 primitive 列表」因此不能直接写成 `List Primitive`——
必须把类型对**存进行里**，也就是 `Sigma`：

```lean
structure MatrixRow where
  I : Type
  O : Type
  prim : Primitive I O
  ...
```

**这是类型系统要求我付的价，不是设计缺陷**：字段版能写 `List Primitive` 正是因为它
把类型藏在字段里，而**那正是 cast 的来源**。

## 1. 保证在类型里，不在定理里

登记表最容易制造的假定理是「登记的 primitive 都 sound」，证明体就是 `r.prim.sound`。
**审计判过这个形态**（`Core/Repair.stable`：「证明体就是一个字段投影，一字未改」）。

**所以保证放进类型**：

- `prim : Primitive I O` 是**字段**——**没有 `sound` 的 primitive 构造不出来**；
- `hstrength` / `hcoverage` 是**证明字段**——**一行不可能谎报强度或覆盖**。
  这是 §2.7「不允许把 `approx` 静默升级成 `exact`」在**数据层**的实现：
  守卫查已写下的代码，这里**连谎都写不出**。

## 2. 本节唯一的真定理

`foldStrength_le_of_mem`：登记表整体的强度 **≤** 任何一行的强度——
**组合不会比任一项更强**。它要对 `List` 归纳，**不是投影**。

## 3. 边界

- **`ofPrims` 要求 `Nodup` 证明**。第一版把它当义务，只能 `sorry`；**`sorry` 不被接受**，
  所以签名改成**要求**该证明：**造不出表胜于造出谎言**。
- **只给上界**，不说「整体恰是 `min`」（要 `min` 结合律与列表非空）。
- **登记表不声称完整**：`Registry.empty` 合法。
- **不检查名字是否描述了它做的事**——那要读语义。 -/
import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
namespace Lattice.Compose

/-! ## 一、矩阵的一行 -/

/-- **登记表的一行**。

`I`/`O` 是**参数化的代价**：`Primitive` 不再是单一 `Type`，所以类型对必须存进行里（等价于 `Sigma`）。 -/
structure MatrixRow where
  /-- 输入类型。 -/
  I : Type
  /-- 输出类型。 -/
  O : Type
  /-- 名字（用于矩阵展示）。 -/
  name : String
  /-- 被登记的 primitive。**它自带 `sound`，所以「没有证明的 primitive」进不来。** -/
  prim : Primitive I O
  /-- 强度。 -/
  strength : Strength
  /-- 覆盖。 -/
  coverage : Coverage
  /-- 强度必须与 primitive 的一致。 -/
  hstrength : strength = prim.strength
  /-- 覆盖必须与 primitive 的一致。 -/
  hcoverage : coverage = prim.coverage

/-- **一行的强度就是它 primitive 的强度。** -/
theorem MatrixRow.strength_eq (r : MatrixRow) : r.strength = r.prim.strength := r.hstrength

/-- **由 `Primitive` 直接造一行**：强度与覆盖自动取 primitive 的，**因此不可能写错**。 -/
def MatrixRow.ofPrim {I O : Type} (name : String) (p : Primitive I O) : MatrixRow where
  I := I
  O := O
  name := name
  prim := p
  strength := p.strength
  coverage := p.coverage
  hstrength := rfl
  hcoverage := rfl

/-! ## 二、登记表 -/

/-- **登记表**：若干行 + 名字不重复。 -/
structure Registry where
  rows : List MatrixRow
  nodup : (rows.map MatrixRow.name).Nodup

/-- **空表合法**。**本节不声称登记表完整**——「所有 primitive 都登记了」需要知道全集。 -/
def Registry.empty : Registry where
  rows := []
  nodup := List.nodup_nil

/-- **由 `(名字, primitive)` 列表构造登记表**，强度与覆盖自动取 primitive 的。

**`h` 是名字不重复的证明**——`Nodup` 不能从任意列表推出，所以它必须是**参数**。
（第一版把它当义务，只能 `sorry`；`sorry` 不被接受。）
这里每个元素是 `MatrixRow`（已带类型对），所以 `h` 可直接满足。 -/
def Registry.ofRows (rows : List MatrixRow) (h : (rows.map MatrixRow.name).Nodup) : Registry where
  rows := rows
  nodup := h

/-! ## 三、组合登记的强度下界（本节唯一的真定理） -/

/-- **逐行取 `min` 的强度**：登记表整体的强度。 -/
def Registry.foldStrength (rs : List MatrixRow) : Strength :=
  rs.foldr (fun r acc => r.strength.min acc) .exact

/-- **登记的任意一行的强度 ≥ 整体强度**——即**组合不会比任一项更强**。

这是 §2.7「组合时强度取最小」在登记表上的形式。它对列表归纳：
头元素由 `min_rank_le_left`，其余由 `min_rank_le_right` 加归纳假设。

**这条不是投影**：它需要 `List` 归纳与 `min` 的两条单调性。 -/
theorem foldStrength_le_of_mem :
    ∀ (rs : List MatrixRow) (r : MatrixRow), r ∈ rs →
      (Registry.foldStrength rs).rank ≤ r.strength.rank
  | [], r, hr => absurd hr (List.not_mem_nil r)
  | (s :: ss), r, hr => by
      show (s.strength.min (Registry.foldStrength ss)).rank ≤ r.strength.rank
      rcases List.mem_cons.mp hr with rfl | hmem
      · exact Strength.min_rank_le_left _ _
      · exact le_trans (Strength.min_rank_le_right _ _)
          (foldStrength_le_of_mem ss r hmem)

/-- **组合不会把 `approx` 升级成 `exact`**：若整体强度是 `exact`，则每一登记项**本身就是 `exact`**。

§2.7 那句禁令的正面形式：**「静默升级」在登记表上被排除。** -/
theorem exact_of_foldStrength_exact (rs : List MatrixRow)
    (h : Registry.foldStrength rs = .exact) (r : MatrixRow) (hr : r ∈ rs) :
    r.strength.rank = 4 := by
  have hle := foldStrength_le_of_mem rs r hr
  have h4 : Strength.exact.rank = 4 := rfl
  rw [h, h4] at hle
  have hb : r.strength.rank ≤ 4 := by
    cases r.strength <;> decide
  exact le_antisymm hb hle

end Lattice.Compose
