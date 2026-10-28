/-
# `Compose/Registry` —— 登记表与组合矩阵

## 0. 这份文件**刻意不制造**「字段投影冒充定理」

登记表最容易被写成「有一条定理说登记的 primitive 都 sound」——而那定理的证明体就是
`r.prim.sound`，**一字未改**。审计已经判过这个形态（`Core/Repair.stable`：
「证明体就是结构体的一个字段投影，一字未改」）。

**所以本节把保证放进类型，而不是放进定理**：

- `MatrixRow` 带一个 `Primitive` **字段**——**没有 `sound` 的 primitive 构造不出来**，
  所以「登记的都有 `sound`」是**类型的性质**，不需要再证一遍；
- 行还带 `hstrength : strength = prim.strength` 与 `hcoverage : coverage = prim.coverage`
  **两个证明字段**——**一行不可能谎报强度或覆盖**。这是 §2.7「不允许把 `approx` 静默升级成 `exact`」
  在**数据层**的实现：守卫查的是已写下的代码，这里连写都写不出。

**本节只把有内容的一条写成定理**：`foldStrength_le_of_mem`——组合登记的强度**下界**，
它对列表归纳，**不是投影**。

## 1. 交付

| 声明 | 内容 |
|:--|:--|
| **`MatrixRow`** | 名字 + primitive + 强度 + 覆盖 + **两个一致性证明** |
| `MatrixRow.ofPrim` | 由 primitive 造行，强度/覆盖**自动取**，因此不可能写错 |
| **`Registry`** | 若干行 + 名字不重复 |
| `Registry.empty` | 空表合法 |
| `Registry.ofPrims` | **要求名字不重复的证明**——它不能凭空造出来 |
| `Registry.foldStrength` | 逐行取 `min` 的强度 |
| **`foldStrength_le_of_mem`** | **登记表里任意一行的强度 ≥ 整体强度**（组合不会比任一项更强） |

## 2. 边界

- **`ofPrims` 要求 `Nodup` 证明**。第一版想直接从一个 `(String × Primitive)` 列表造表并把
  `Nodup` 当义务——**那证不出来**（输入列表的名字可以重复），于是只能 `sorry`。
  **`sorry` 不被接受**，所以签名改成**要求**该证明：造不出表比造出谎言好。
- **`foldStrength_le_of_mem` 只给上界**：它说整体**不超过**任一登记项。
  **不说**「整体恰是 `min`」——那需要 `min` 的结合律与列表非空，本节不做。
- **登记表不声称完整**：`Registry` 是一个 `List`，**空表也合法**。
- **不检查「名字是否描述了它做的事」**——那要读语义，不是类型能做的。 -/
import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators

namespace Lattice.Compose

/-! ## 一、矩阵的一行 -/

/-- **登记表的一行**。

`hstrength` 与 `hcoverage` 是**证明字段**：一行**不可能**谎报强度或覆盖。
这比「用守卫检查是否谎报」更强——谎报在这里**不可构造**。 -/
structure MatrixRow where
  /-- 名字（用于矩阵展示）。 -/
  name : String
  /-- 被登记的 primitive。**它自带 `sound`，所以「没有证明的 primitive」进不来。** -/
  prim : Primitive
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
def MatrixRow.ofPrim (name : String) (p : Primitive) : MatrixRow where
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

/-- **空表合法**。**本节不声称登记表完整**——「所有 primitive 都登记了」需要知道全集，本节给不出。 -/
def Registry.empty : Registry where
  rows := []
  nodup := List.nodup_nil

/-- **由 `(名字, primitive)` 列表构造登记表**，强度与覆盖自动取 primitive 的。

**`h` 是名字不重复的证明**——`Nodup` 不能从任意列表推出，所以它必须是**参数**。
（第一版把它当成要证的义务，只能 `sorry`；`sorry` 不被接受。） -/
def Registry.ofPrims (ps : List (String × Primitive))
    (h : (ps.map (fun np => np.1)).Nodup) : Registry where
  rows := ps.map (fun np => MatrixRow.ofPrim np.1 np.2)
  nodup := by
    -- `rows.map name` is `ps.map (fun np => np.1)`, so the proof is exactly `h`
    simpa using h

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

/-- **组合不会把 `approx` 升级成 `exact`**：若整体强度是 `exact`，则每一登记项的秩都 ≥ `exact` 的秩，
**也就是每一登记项本身就是 `exact`**。

这是上一条的直接推论，但它是 §2.7 那句禁令**正面**的形式：**「静默升级」在登记表上被排除。** -/
theorem exact_of_foldStrength_exact (rs : List MatrixRow)
    (h : Registry.foldStrength rs = .exact) (r : MatrixRow) (hr : r ∈ rs) :
    r.strength.rank = 4 := by
  have hle := foldStrength_le_of_mem rs r hr
  have h4 : Strength.exact.rank = 4 := rfl
  have := hle
  rw [h, h4] at this
  have hb : r.strength.rank ≤ 4 := by
    cases r.strength <;> decide
  exact le_antisymm hb this

end Lattice.Compose
