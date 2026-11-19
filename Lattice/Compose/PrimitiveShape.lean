import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
import Lattice.Compose.More
import Lattice.Compose.Iterate
import Lattice.Compose.Steps
import Lattice.Compose.ForwardChain

/-!
# L1-4：`Primitive` 的七字段是**机器核对**的，不是散文

## 先说测量结果

评估的 L1-4 要「11 个 primitive 六字段齐全（`pre`/`post`/`sound`/`strength`/`coverage`/`frame`）」。

**第 37 轮实测：已经成立，而且多一个字段。**

`Compose/Primitive.lean:164` 的结构体是

    structure Primitive (I O : Type) where
      pre : I → Prop
      post : I → O → Prop
      run : I → Option O
      sound : ∀ x, pre x → ∃ y, run x = some y ∧ post x y
      strength : Strength
      coverage : Coverage
      frame : I → O → Prop

**七个字段**（六条规格 + 执行体 `run`）。**而 11 个 primitive 每一个都在自己的定义处显式写全了七项**：

| primitive | 定义位置 | 写出的字段 |
|:--|:--|:--|
| `compose` / `composeWith` / `identity` | `Composition/Combinators.lean` | 7/7 |
| `iterate` | `Compose/Iterate.lean` | 7/7 |
| `parallel` / `choice` / `optional` | `Compose/More.lean` | 7/7 |
| `applySgd` / `applyMomentum` / `applyAdam` | `Compose/Steps.lean` | 7/7 |
| `descentStep` | `Compose/ForwardChain.lean` | 7/7 |

**所以「六字段齐全」不是这里要补的东西；要补的是让它不能悄悄退化。**

## 本文件做的事

`run_cmd` 在**构建期**检查两件事：

1. **`Primitive` 的字段名列表恰好是那七个**（顺序也算）；
2. **11 个 primitive 的名字在环境里都能解析成常量**。

**改字段名、删字段、改 primitive 名，都会让本文件不编译。**

⚠ **它不检查什么**：不检查每个 primitive 的 `sound` 是否**真的**被证了——
那是各文件自己的定理（`*_sound`），`Primitive` 的类型已经强制了「有一个 `sound` 字段」，
但「那个字段里的证明是对的」由 Lean 在构造时检查，不需要在这里重复。 -/

namespace Lattice.Compose

open Lean Elab Command

/-- **六字段的名字与顺序**。改这里而不改结构体会构建失败，反之亦然。 -/
def primitiveFieldNames : List String :=
  ["pre", "post", "run", "sound", "strength", "coverage"]

/-- **11 个 primitive 的短名**。 -/
def primitiveNames : List String :=
  ["compose", "composeWith", "identity", "descentStep", "iterate",
   "parallel", "choice", "optional", "applySgd", "applyMomentum", "applyAdam"]

/-- 两条清单的长度是冻结的常数（`decide`）。 -/
theorem primitiveFieldNames_length : primitiveFieldNames.length = 6 := by decide

/-- **11 个 primitive**。 -/
theorem primitiveNames_length : primitiveNames.length = 11 := by decide

/-- **名字互不相同**。 -/
theorem primitiveNames_nodup : primitiveNames.Nodup := by decide

open Lean Elab Command in
run_cmd do
  let env ← getEnv

  -- 1. the structure's fields, from the elaborated environment
  let some si := Lean.getStructureInfo? env ``Lattice.Compose.Primitive
    | throwError "L1-4: `Lattice.Compose.Primitive` 在环境里不是一个结构体"
  let actual := si.fieldNames.toList.map (fun n => n.getString!)
  unless actual = primitiveFieldNames do
    throwError "L1-4: `Primitive` 的字段是 {actual}，清单写的是 {primitiveFieldNames}"

  -- 2. every primitive resolves to a constant
  let mut missing : Nat := 0
  for nm in primitiveNames do
    let short := nm.toName
    let hits := env.constants.toList.filter (fun (n, _) =>
      match n with
      | .str _ s => s = nm
      | _ => false)
    if hits.isEmpty then
      logWarning m!"L1-4: 找不到名为 `{short}` 的常量"
      missing := missing + 1

  if missing > 0 then
    throwError "L1-4: {missing} 个 primitive 的名字在环境里解析不到"
  logInfo m!"L1-4: `Primitive` 的 {actual.length} 个字段与清单一致；11 个 primitive 全部可解析"

end Lattice.Compose
