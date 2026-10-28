/-
# `CInterface/ABI` —— 11 个 primitive 的 C 侧契约（**规格，不是 C 代码**）

## 这一层是什么，不是什么

`DIRECTORY-DESIGN.md` §8.1 说得很清楚：`CInterface/` 是**Lean 侧的 C 契约**，不是 C 实现。
本文件因此**不调用任何 C**、**不假设任何 ABI 字节布局**，只把「每个 primitive 对应的 C 函数
长什么样」写成 Lean 数据，并**证明这张表自身是自洽的**。

⚠ **它证明不了的事**（必须说清，否则又是一条「有名字就算完成」）：

- **没有证明**「C 实现对得上 Lean 语义」——那需要真的写 C 并做 conformance 向量对照（§8.1 的 P6，另行排期）；
- **没有证明**所有权约定安全——`Ownership` 只是个标签；
- **没有证明**布局与 `Layout.lean` 一致——那在另一个文件里，且只能对**已存在的类型**说。

## 为什么这层可以真做，而 `Kernel` 不行

`Kernel/Types` 要 23 个**不存在**的类型（第 15 轮实测），所以不可执行。
本层只需要**已有的 11 个 `Primitive`**（`Compose/Primitive.lean`，第 232 轮参数化）+ 一张名字表。
**名字表与 `Compose` 的一致性有门禁**（`gov/check_cinterface_abi.py`），所以它不会漂。 -/
import Mathlib

namespace Lattice.CInterface.ABI

/-- C 标量类型。**只列 primitive 契约真正需要的那些**，不从 C 标准抄全集。 -/
inductive CType
  /-- `int64_t`：token、整数坐标、步数。 -/
  | i64
  /-- `double`：权重、损失、步长。 -/
  | f64
  /-- `const char*`：名字、错误信息。 -/
  | cstr
  /-- `size_t`：长度。 -/
  | size
  /-- `void`：无返回值。 -/
  | void
  deriving DecidableEq, Repr

/-- 错误码。**闭集**：`ok` 加上四类失败，不引入未列出的码。 -/
inductive ErrorCode
  /-- 成功。 -/
  | ok
  /-- 参数为空或长度不符。 -/
  | invalidArg
  /-- 形状/维度不匹配。 -/
  | shapeMismatch
  /-- 调用方缓冲不足。 -/
  | bufferTooSmall
  /-- 该 primitive 在此配置下不适用（对应 `Primitive` 的 `coverage` 为空）。 -/
  | notApplicable
  deriving DecidableEq, Repr

/-- 所有权约定。**标签，不是安全证明。** -/
inductive Ownership
  /-- 调用方分配、调用方释放。 -/
  | callerOwns
  /-- 被调方分配、调用方用配套的 `free` 释放。 -/
  | calleeAllocates
  /-- 只借用，不转移。 -/
  | borrowed
  deriving DecidableEq, Repr

/-- **一个 primitive 的 C 侧契约**。 -/
structure CFunction where
  /-- 符号名，必须与 `Compose` 里的 primitive 名一致。 -/
  name : String
  /-- 参数类型，按 C 的从左到右顺序。 -/
  args : List CType
  /-- 返回类型。 -/
  ret : CType
  /-- 该函数可能返回的错误码（`ok` 总在其中）。 -/
  errors : List ErrorCode
  /-- 输出缓冲的所有权。 -/
  ownership : Ownership
  deriving DecidableEq, Repr

/-- `ok` 总是可能的返回，所以每个契约的 `errors` 都必须含它。 -/
def CFunction.errorsWellFormed (f : CFunction) : Bool :=
  f.errors.contains ErrorCode.ok

/-- **11 个 primitive 的 ABI 表。** 名字与 `Compose` 的 primitive 一一对应，由
`gov/check_cinterface_abi.py` 核对。 -/
def abiTable : List CFunction :=
  [ { name := "compose", args := [CType.cstr, CType.size, CType.size], ret := CType.i64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg, ErrorCode.shapeMismatch],
      ownership := Ownership.callerOwns }
  , { name := "composeWith", args := [CType.cstr, CType.cstr, CType.size], ret := CType.i64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg, ErrorCode.notApplicable],
      ownership := Ownership.callerOwns }
  , { name := "identity", args := [CType.size], ret := CType.i64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg],
      ownership := Ownership.callerOwns }
  , { name := "descentStep", args := [CType.f64, CType.f64, CType.f64, CType.size], ret := CType.f64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg],
      ownership := Ownership.borrowed }
  , { name := "iterate", args := [CType.cstr, CType.size, CType.size, CType.size], ret := CType.i64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg, ErrorCode.notApplicable],
      ownership := Ownership.callerOwns }
  , { name := "parallel", args := [CType.cstr, CType.cstr, CType.size], ret := CType.i64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg],
      ownership := Ownership.callerOwns }
  , { name := "choice", args := [CType.cstr, CType.cstr, CType.i64, CType.size], ret := CType.i64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg, ErrorCode.notApplicable],
      ownership := Ownership.callerOwns }
  , { name := "optional", args := [CType.cstr, CType.i64, CType.size], ret := CType.i64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg],
      ownership := Ownership.callerOwns }
  , { name := "applySgd", args := [CType.f64, CType.f64, CType.size], ret := CType.f64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg],
      ownership := Ownership.callerOwns }
  , { name := "applyMomentum", args := [CType.f64, CType.f64, CType.f64, CType.size], ret := CType.f64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg],
      ownership := Ownership.callerOwns }
  , { name := "applyAdam", args := [CType.f64, CType.f64, CType.f64, CType.f64, CType.size],
      ret := CType.f64,
      errors := [ErrorCode.ok, ErrorCode.invalidArg],
      ownership := Ownership.callerOwns }
  ]

/-- **表有 11 项**——与 `Compose` 的 primitive 数一致。 -/
theorem abiTable_length : abiTable.length = 11 := by decide

/-- ⭐ **符号名互不相同。** 一个 ABI 里有重名符号是**真 bug**（链接期就会撞），
所以这条不是形式主义。 -/
theorem abiTable_names_nodup : (abiTable.map CFunction.name).Nodup := by decide

/-- ⭐ **每个契约的 `errors` 都含 `ok`**：否则「成功」在该函数上不可表示。 -/
theorem abiTable_errors_wellFormed : ∀ f ∈ abiTable, f.errorsWellFormed = true := by
  intro f hf
  simp only [abiTable, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **没有契约返回 `void`**：每个 primitive 都产出可检查的值，所以「无返回」是设计错误。 -/
theorem abiTable_returns_a_value : ∀ f ∈ abiTable, f.ret ≠ CType.void := by
  intro f hf
  simp only [abiTable, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **名字表**，供门禁与文档使用（`decide` 无法把 `String` 列成名字，故单列一条）。 -/
def primitiveNames : List String :=
  ["compose", "composeWith", "identity", "descentStep", "iterate", "parallel",
   "choice", "optional", "applySgd", "applyMomentum", "applyAdam"]

/-- **`primitiveNames` 就是 `abiTable` 的名字序列**——这条把两份清单钉在一起，
所以门禁只需要核对 `primitiveNames` 与 `Compose`。 -/
theorem primitiveNames_eq_abi : abiTable.map CFunction.name = primitiveNames := by decide

end Lattice.CInterface.ABI
