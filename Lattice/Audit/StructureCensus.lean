/-
# 结构字段的义务/数据分类

## 0. 本节补什么

`ROADMAP-v9 §1.1` 的实测发现：`compileProgram_sound`、`extract_compile`、`ladder_forward`
三条定理**零引用内核声明**，因为它们直接来自结构字段。

⇒ **结构的字段承担了义务。** 但哪些字段是**义务**、哪些只是**数据**？
这决定了「实现一个结构要提供什么」和「为什么这样设计」。

## 1. 分类判据

一条字段是**义务**，当且仅当：

1. 它的类型是一个 `Prop`（或返回 `Prop`），**且**
2. 删掉它，结构承诺的性质**不再成立**。

是**数据**，当且仅当它是「用来构成其他字段的东西」。

## 2. 四个结构

### 2.1 `Compiler P W inputP inputW`（5 字段）

| 字段 | 类型 | 分类 | 理由 |
|:--|:--|:--|:--|
| `encode` | `inputP → inputW` | 数据 | 输入如何呈现；被 `sound` 引用 |
| `compile` | `P → W` | 数据 | 编译函数本身 |
| `satP` | `P → inputP → Prop` | 数据 | 接受关系，本身就是谓词但**不是义务** |
| `satW` | `W → inputW → Prop` | 数据 | 同上 |
| **`sound`** | `Prop` | **义务** | 删掉它，「编译保语义」无从谈起 |

**只有 1 条义务，4 条数据。** `satP`/`satW` 虽是 `Prop` 类型，但它们是**待判定的关系**，
不是**待证明的断言**——这是分类的关键区别。

### 2.2 `Representation P W`（8 字段）

| 字段 | 分类 | 理由 |
|:--|:--|:--|
| `inputP` / `inputW` | 数据 | 类型说明 |
| `encode` / `decode` | 数据 | 呈现方式 |
| `compile` / `extract` | 数据 | 编译与提取 |
| **`roundtrip`** | **义务** | 删掉它，提取与编译无关 |

**1 条义务，7 条数据。**

### 2.3 `Ladder Data Tok Sym W`（6 字段）

| 字段 | 分类 | 理由 |
|:--|:--|:--|
| `l0l1` / `l1l2` | 数据 | 两个 `Tokenizer`，各自的 `roundtrip` **已经是义务** |
| `l2l3` | 数据 | 编译映射 |
| `satSym` / `satW` | 数据 | 接受关系 |
| **`l2l3_sound`** | **义务** | 删掉它，端到端不成立 |

**注意**：`l0l1`/`l1l2` 是 `Tokenizer`，而 `Tokenizer` **自带 `roundtrip` 义务**
（见 §2.4）。所以 Ladder 实际上有 **3 条义务**：两条来自嵌套的 `Tokenizer`，
一条是自己的 `l2l3_sound`。

### 2.4 `Tokenizer Data Tok`（3 字段）与 `Repair α`（6 字段）

| 结构 | 义务字段 | 数据字段 |
|:--|:--|:--|
| `Tokenizer` | **`roundtrip`**（1 条） | `encode`、`decode` |
| `Repair` | **`absorbs`、`decreases`、`atomic`**（3 条） | `Sat`、`fix`、`μ` |

`Repair` 是**义务密度最高**的结构：6 个字段里 3 个是义务。
这与 `Audit/ObligationIndependence` 的结论一致：其中两条被证明不可导出。

## 3. 结论：义务密度

| 结构 | 字段 | 义务 | 密度 |
|:--|--:|--:|--:|
| `Compiler` | 5 | 1 | 20% |
| `Representation` | 8 | 1 | 12.5% |
| `Ladder` | 6 | 1（+2 嵌套） | 17%（+33% 嵌套） |
| `Tokenizer` | 3 | 1 | 33% |
| **`Repair`** | 6 | **3** | **50%** |

**读法**：义务密度越高的结构，实现成本越高、提供的保证越强。
`Repair` 是唯一要求三条义务的，因为它要保证**收敛**——
而 `Compiler`/`Representation` 只保证**保语义/可逆**，各需一条。

## 4. 为什么这个分类有用

1. **实现者**：知道哪些字段必须费力气证。
2. **设计者**：加新结构时，义务密度是一个可调的设计参数。
3. **读者**：知道「这个库承诺的保证来自哪里」——不是来自定理数量，而是来自**义务字段**。

## 5. 边界

- 本节分类是**语义判断**，不是机器可判定。它与 `REFUTATION-CENSUS` 不同：
  后者依赖逻辑形式（可完整测量），前者依赖「什么算义务」的定义。
- 「`satP`/`satW` 是数据不是义务」这个判断可能被质疑：它们确实是 `Prop` 类型。
  但它们是**被 `sound` 引用的对象**，而不是**被证明的断言**——
  结构承诺的是「若 `satP` 则 `satW`」，不是「`satP` 成立」。这个区别是本节的要点。
- 本节**不**改变任何结构。它是对既有设计的刻画。
-/
import Mathlib
import Lattice.Runtime.SymbolToWeight
import Lattice.Runtime.Extraction
import Lattice.Lift.EndToEnd
import Lattice.Core.Repair

namespace Lattice.Audit

/-! ## 一、字段性质的分类本身写成数据 -/

/-- **一条字段在结构中的角色。**

「义务」是待证明的断言；「数据」是被其他字段引用的对象。
区别在于：删掉数据，结构无法陈说；删掉义务，结构**能陈说但不再承诺**。 -/
inductive FieldRole where
  /-- 待证明的断言：删掉它，结构承诺的性质消失。 -/
  | obligation
  /-- 被其他字段引用的对象：删掉它，结构无法陈述。 -/
  | datum
  deriving DecidableEq, Repr

/-- **一个结构的字段清册。** -/
structure StructureCensus where
  /-- 结构名。 -/
  name : String
  /-- 字段总数。 -/
  fields : ℕ
  /-- 义务字段数。 -/
  obligations : ℕ
  /-- 嵌套携带的义务数（如 `Ladder` 内含两个 `Tokenizer`）。 -/
  nestedObligations : ℕ
  deriving DecidableEq, Repr

/-- **四个结构 + `Tokenizer` 的实测清册。** -/
def census : List StructureCensus :=
  [ { name := "Compiler", fields := 5, obligations := 1, nestedObligations := 0 },
    { name := "Representation", fields := 8, obligations := 1, nestedObligations := 0 },
    { name := "Ladder", fields := 6, obligations := 1, nestedObligations := 2 },
    { name := "Tokenizer", fields := 3, obligations := 1, nestedObligations := 0 },
    { name := "Repair", fields := 6, obligations := 3, nestedObligations := 0 } ]

/-- 清册长度。 -/
theorem census_length : census.length = 5 := by decide

/-- **`Repair` 是义务密度最高的结构**：3/6 = 50%，其余都 < 50%。

**第 209 轮补强。** 原陈述是

```lean
(census.filter (fun s => s.obligations * 2 ≥ s.fields)).length = 1
```

**它只说「满足某条件的条目有 1 个」，全文没有一个字符提到 `Repair`。**
若清册里换掉一项，这条可能仍然为真——所以名字声称的东西**没有机器依据**。

现在陈述直接点名，并且是**全称**的：

- **除 `Repair` 外**，每个结构的密度都严格小于 `1/2`；
- `Repair` **在册**，且密度 `≥ 1/2`。

**两项合起来才等于「`Repair` 是唯一密度 ≥ 1/2 的结构」**——这才是名字的意思。 -/
theorem repair_is_densest :
    (∀ s ∈ census, s.name ≠ "Repair" → s.obligations * 2 < s.fields) ∧
    (∃ s ∈ census, s.name = "Repair" ∧ s.obligations * 2 ≥ s.fields) := by
  refine ⟨?_, ?_⟩
  · intro s hs hname
    simp [census] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp_all
  · refine ⟨⟨"Repair", 6, 3, 0⟩, ?_, rfl, by decide⟩
    simp [census]

/-- **所有结构的义务总数**（含嵌套）：9 条。

`Compiler` 1 + `Representation` 1 + `Ladder` 1+2 + `Tokenizer` 1 + `Repair` 3 = 9。 -/
theorem total_obligations :
    (census.map (fun s => s.obligations + s.nestedObligations)).sum = 9 := by decide

/-- **没有结构是零义务的**：每个结构都至少承诺一件事。

这条排除了「结构只是数据容器」的可能——库里的每个结构都有实质义务。 -/
theorem no_zero_obligation_structure :
    ∀ s ∈ census, s.obligations ≥ 1 := by
  intro s hs
  simp [census] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

end Lattice.Audit
