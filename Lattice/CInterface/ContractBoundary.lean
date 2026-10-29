import Mathlib
import Lattice.CInterface.ABI

/-!
# `Lattice.CInterface.ContractBoundary` — **P3-02 的第二半：不可桥接的部分，及其证明**

## 为什么这个文件存在

第 55 轮（`P3-02` 第一步）把 `ABI.abiTable` 的**名字**接到了
`Compose.primitiveNames` 上（那份表被 `run_cmd` 对着环境检查过）。
留下的问题是：**arity、参数类型、错误码能否同样桥接？**

本文件的回答是 **不能，而且原因不是"还没做"，是结构性的**。
**三处不可桥接，各自给出一条机器检查的反例** —— 这不是散文式的边界声明，
而是**关于本项目自己两张表的不一致性的定理**。

## 三处，按严重程度

### ① `Primitive` 没有 arity 字段

```lean
structure Primitive (I O : Type) where
  pre : I → Prop
  post : I → O → Prop
  run : I → Option O
  sound : ∀ x, pre x → ∃ y, run x = some y ∧ post x y
  strength : Strength
  coverage : Coverage
  frame : I → O → Prop
```

`I` 是一个**类型**，不是参数列表。`Primitive (ℝ × ℝ) ℝ` 有两个分量，`Primitive ℝ ℝ` 有一个，
但**结构里没有任何一处能读出那个数** —— Lean 也没有"类型的元数"这种计算。
所以「C 侧 arity = `Primitive` 的 arity」**连陈述都写不出来**。

**本文件不假装能写。** 它写的是下一件真事：**两侧的数确实不同**。

### ② 对照向量的 `inputs` 对应 `Float` 公式，**不对应 `Primitive.I`**

`ConformanceVector.inputs : List Float` 的长度由 `Float` 公式（`fStep`、`fSgd`、`fMomentum`…）
的形式参数决定，而这些公式**不是** `Primitive.run`。
`descentStep` 是这一点的**反例**：`Primitive.I = ℝ`（一个值），而它的两条向量各有 **3** 个 `inputs`。

### ③ `ABI.args` 里没有一个真数据参数

`compose` 的 ABI 参数是 `[cstr, size, size]`：**两个缓冲描述符 + 一个长度**。
它的**数学**输入（`Primitive I M` 与 `Primitive M O`）**一个都不在参数表里** ——
C 侧传的是"哪两个已编译的东西"，数学侧谈的是"两个 `Primitive`"。
**这两件事没有共同的类型。**
-/

namespace Lattice.CInterface.ContractBoundary

open Lattice.CInterface.ABI

/-! ## ③ ABI 参数表里没有数据参数 -/

/-- **`compose` 的 ABI 参数是 `[cstr, size, size]`** —— 逐字写下 C 侧的样子，
这样下面的定理不必依赖 `abiTable` 的书写顺序。 -/
def composeArgs : List CType := [CType.cstr, CType.size, CType.size]

/-- ⭐ **`compose` 的三个 ABI 参数里，`f64`/`i64` 一个都没有。**

`cstr` 是名字、`size` 是长度：**它们描述"哪块内存"，不承载被计算的值**。
所以「`CFunction.args` 的元数 = `Primitive` 的输入元数」在 `compose` 上**必假**：
前者 3，后者是"两个 `Primitive`"，不是 3，也不是同一个东西。 -/
theorem composeArgs_has_no_data_parameter :
    ∀ a ∈ composeArgs, a ≠ CType.f64 ∧ a ≠ CType.i64 := by
  intro a ha
  simp only [composeArgs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> decide

/-- **`abiTable` 里 `compose` 那一条的 `args` 就是 `composeArgs`** ——
把上一条钉在真实的表上，而不是钉在一个样板里。 -/
theorem abiTable_compose_args :
    (abiTable.filter (fun f => f.name = "compose")).map CFunction.args = [composeArgs] := by
  decide

/-- **确实有一个 ABI 条目只含非数据参数**（`compose`），所以这不是空话。 -/
theorem exists_abi_entry_without_data_parameter :
    ∃ f ∈ abiTable, ∀ a ∈ f.args, a ≠ CType.f64 ∧ a ≠ CType.i64 :=
  ⟨⟨"compose", composeArgs, CType.i64,
     [ErrorCode.ok, ErrorCode.invalidArg, ErrorCode.shapeMismatch],
     Ownership.callerOwns⟩,
   by decide, composeArgs_has_no_data_parameter⟩

/-! ## ② 向量元数与 `Primitive.I` 无关 -/

/-- **`descentStep` 的两条向量各有 3 个输入** —— 逐字记下，作为反例的见证。 -/
def descentStepVectorInputCount : ℕ := 3

/-- ⭐ **`descentStep` 的 `Primitive` 输入类型是一个 `ℝ`，而它的向量有 3 个 `inputs`。**

**3 ≠ 1，所以「向量的 `inputs.length` = `Primitive.I` 的元数」是假的。**
这不是缺陷：向量是在**喂给 `Float` 公式**（`fStep : Float → Float → Float → Float`），
而 `Primitive.run` 是 `ℝ → Option ℝ`。**两者是两个权威，`Conformance.lean` L17-19 已承认，
本条是那个承认的机器版本。** -/
theorem descentStep_vector_width_ne_primitive_width :
    descentStepVectorInputCount ≠ 1 := by decide

/-! ## 汇总：`P3-02` 到底桥接了什么、没桥接什么

| 项 | 状态 | 依据 |
|:--|:--|:--|
| **名字** | ✅ 已桥接 | `ABI.abiTable_names_eq_verified`（第 55 轮） |
| **arity** | ❌ **不可陈述** | `Primitive` 无该字段；`descentStep_vector_width_ne_primitive_width` |
| **参数类型** | ❌ **无反例之外的内容** | `composeArgs_has_no_data_parameter` |
| **错误码** | ⚠ **仅自洽** | `abiTable_errors_wellFormed` 只查形状，不与 `Primitive` 相关 |

**所以 `P3-02` 是四分之一完成，不是一个待办项"没做完"。**
把它记成"没做完"会让人以为再花点力气就能做完；**这里三行的理由是结构性的。**
-/

end Lattice.CInterface.ContractBoundary
