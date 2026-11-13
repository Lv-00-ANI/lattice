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

### 2.2 `Representation P W`（**7** 字段）

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
| `Representation` | **7** | 1 | 14.3% |
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
import Lattice.Runtime.EndToEnd
import Lattice.Plugins.Core.Repair.Repair
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
  /-- 结构名（显示用）。 -/
  name : String
  /-- **声明的全名**——第 30 轮加。表里的小名字符串**不足以唯一指向一个声明**（树里有多个
  `Compiler` 与 `Ladder`），所以每一行现在带着全名，`run_cmd` 才能对着环境核对它。 -/
  fullName : Lean.Name
  /-- 字段总数。 -/
  fields : ℕ
  /-- 义务字段数。 -/
  obligations : ℕ
  /-- 嵌套携带的义务数（如 `Ladder` 内含两个 `Tokenizer`）。 -/
  nestedObligations : ℕ
  deriving DecidableEq, Repr

/-- **四个结构 + `Tokenizer` 的清册（**人工维护**）。**

⚠⚠ **第 9 轮修正：这里的数字不是「实测」，而且没有任何机器核对。**

`decide` 只能核对**表内算术**（`census.length = 5`、`obligations ≥ 1`、密度的比较），
**它核对不了表里的数字是否与真实结构相符**。本轮就发现了一处错的：

| 行 | 原值 | 真实值 | 依据 |
|:--|--:|--:|:--|
| `Representation` | 8 | **7** | `Runtime/Extraction.lean:58` 的字段：`inputP`、`inputW`、`encode`、`decode`、`compile`、`extract`、`roundtrip` |

**8 不符合任何一种口径**（连把类型参数 `P W` 算进去也是 9）。已改为 7。

⚠ **这个缺陷的性质**：`decide` 定理（`census_length`、`no_zero_obligation_in_census_table`、
`repair_is_densest`）全部**照旧为真**——它们证明的是**表自己的性质**，不是表**关于库**的准确性。
**所以这张表可以在不触发任何门禁的情况下漂移**，而在漂移之后，
那几条 `decide` 定理会**以「已核对」的外表继续为真**。

⭐ **要真正锁住它**，需要让每行与结构本身绑定（例如用反射取字段数），
那在 Lean 里需要 `Lean` 的元编程而非 `decide`。

✅ **第 30 轮做到了。** 文件末尾的 `run_cmd` 在**构建期**从 `Lean` 环境取
`StructureInfo.fieldNames.size`，与表里的数字比较，不等就 `throwError`。**已经实测会失败**：

改了 `censusEnv` 里 `Repair` 的 6 为 7，构建给出
`census: Lattice.Core.Repair 实际有 6 个字段，表里写的是 7`，`exit 1`；改回去 `exit 0`。

**所以那张表不再按「人工录入、未经核对」读。** 上面那三条 `decide` 定理仍然只陈述表自身的性质
（这一点没有变，也不该被说成别的），它们旁边现在多了一个**关于库**的仪器。 -/
def census : List StructureCensus :=
  [ { name := "Compiler", fullName := ``Lattice.Lift.Compiler,
      fields := 5, obligations := 1, nestedObligations := 0 },
    { name := "Representation", fullName := ``Lattice.Lift.Representation,
      fields := 7, obligations := 1, nestedObligations := 0 },
    { name := "Ladder", fullName := ``Lattice.Lift.Ladder,
      fields := 6, obligations := 1, nestedObligations := 2 },
    { name := "Tokenizer", fullName := ``Lattice.Lift.Tokenizer,
      fields := 3, obligations := 1, nestedObligations := 0 },
    { name := "Repair", fullName := ``Lattice.Core.Repair,
      fields := 6, obligations := 3, nestedObligations := 0 } ]

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
  -- 第 30 轮：结构体多了 `fullName` 字段，所以不再用位置构造子（`⟨...⟩` 会少一个字段而报错），
  -- 改为**从表里取那一行**——这样这条定理也就不再假设表长什么样，只假设表里有一行叫 `Repair`。
  · obtain ⟨row, hrow_mem, hrow_name⟩ :
        ∃ s ∈ census, s.name = "Repair" := by
      simp [census]
    exact ⟨row, hrow_mem, hrow_name, by
      have hf : row.fields = 6 := by
        simp [census] at hrow_mem
        rcases hrow_mem with rfl | rfl | rfl | rfl | rfl <;> simp_all [census]
      have ho : row.obligations = 3 := by
        simp [census] at hrow_mem
        rcases hrow_mem with rfl | rfl | rfl | rfl | rfl <;> simp_all [census]
      omega⟩

/-- **所有结构的义务总数**（含嵌套）：9 条。

`Compiler` 1 + `Representation` 1 + `Ladder` 1+2 + `Tokenizer` 1 + `Repair` 3 = 9。 -/
theorem total_obligations :
    (census.map (fun s => s.obligations + s.nestedObligations)).sum = 9 := by decide

/-- **清册里的每个结构 `obligations ≥ 1`。**

⚠ **第 5 轮降级，两处。名字和 doc 都声称过强。**

1. **名字**原来是 `no_zero_obligation_structure`，读作「没有结构是零义务的」——
   而陈述只覆盖 `census` 的 **5 个条目**。改成现在这个名字后两者一致。

2. **doc** 原来接着写「**库里的每个结构都有实质义务**」。⚠ **那句话没有任何机器依据**：
   `obligations` 是**作者填的数字字段**，不是证明义务；而这 5 行**也不是库里的全部结构**。
   **从一张手填的五行表推全库，是无效推理。**

所以本条现在只声称：**这张表里没有 0**。它是一条**表一致性**检查，不是关于库的结论。 -/
theorem no_zero_obligation_in_census_table :
    ∀ s ∈ census, s.obligations ≥ 1 := by
  intro s hs
  simp [census] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide


/-! ## 让这张表**不再能漂移**（第 30 轮）

上面那段 docstring 说：「要真正锁住它，需要让每行与结构本身绑定（例如用反射取字段数），
那在 Lean 里需要 `Lean` 的元编程而非 `decide`。」**本节就是那一节。**

`run_cmd` 在**构建期**运行：它从 `Lean` 环境取每个结构的 `StructureInfo.fieldNames.size`，
与表里的数字比较，不等就 `throwError`——**构建失败**。所以表不再是「人工录入、未经核对」。

⚠ **为什么 `decide` 做不到**：`decide` 只能对**表自身的项**求值；结构体的字段数不是表中的项，
它在环境里。这不是「更强的 `decide`」，是**另一个仪器**。 -/

/-- **环境核对表**：`(全名, 表里的字段数)`。

与 `census` 的 `(fullName, fields)` 用 `census_env_agrees` 绑定，所以**两处必须同时改**：
改表不改这里，`decide` 失败；改这里不改表，`decide` 也失败。 -/
def censusEnv : List (Lean.Name × ℕ) :=
  [ (``Lattice.Lift.Compiler, 5),
    (``Lattice.Lift.Representation, 7),
    (``Lattice.Lift.Ladder, 6),
    (``Lattice.Lift.Tokenizer, 3),
    (``Lattice.Core.Repair, 6) ]

/-- **两处数字一致**：`censusEnv` 就是 `census` 的投影。 -/
theorem census_env_agrees :
    census.map (fun r => (r.fullName, r.fields)) = censusEnv := by decide

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (nm, expected) in censusEnv do
    match Lean.getStructureInfo? env nm with
    | none =>
      throwError "census: {nm} 在环境里不是一个结构体——表指向了不存在的东西"
    | some si =>
      unless si.fieldNames.size = expected do
        throwError "census: {nm} 实际有 {si.fieldNames.size} 个字段，表里写的是 {expected}"
      checked := checked + 1
  logInfo m!"census: {checked} 个结构体已对着 Lean 环境核对（字段数一致）"

end Lattice.Audit
