import Mathlib
import Lattice.Runtime.ExtractionClosure

/-!
# 回路：`Layer ⇄ ConstraintSet` 的**双向恒等**与它作为验证判据的可用性（阶段 C，P5）

## 上一轮状态

**第 898 轮把逆向三段连成一体，但每一条都是**单元素**的（`[extractVec l]`、`[c]`）。
所以「回路」这个词还没有在**列表**上被证明。**

## 本文件补的三件事

### 一、列表版的双向恒等

**`extractLayer : Layer → ConstraintSet` 定义为 `ls.map extractVec`，
而 `compileToLayer : ConstraintSet → Layer` 定义为 `cs.map convertVec`。**

**两者都是 `map`，而 `convertVec`/`extractVec` 逐元素互逆 —— 于是列表上它们也互逆。**
**=> 这是 `map` 的函子性加上逐元素逆的直接结果，但**它此前没有被写成定理**（在 `Runtime` 层）。**

### 二、回路作为**验证判据**

**回路的用途不是「转来转去」，而是：给一个权重层，**判定**它是否满足某组符号约束。**

**=> 若 `extractLayer ls = cs`，则 `ls` 满足 `cs` **当且仅当** `compileToLayer cs = ls`
（因为二者互为逆）。**这使「验证」变成一次可判定的比较，而不是一次搜索。**

### 三、回路**不产生新信息**（一条否证）

**如果回路恒等成立，那么「提取后重新注入」这件事本身**不改变任何东西** ——
它**不**是「修正」。**

**=> 这条要说清楚，否则「闭环 = 验证回路」会被误读成「闭环 = 自动修复」。
**修正必须来自回路**之外**（`Repair`、`VerificationLoop`），回路只提供**判据**。** -/

namespace Lattice.Runtime.LoopClosure

open Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Runtime.ExtractionClosure

/-- **`Layer → ConstraintSet`：逐层提取。**

**=> 与 `compileToLayer`（`cs.map convertVec`）对称。**
**本文件在 `Runtime` 内重新陈述它，因为它是 `Layer` 上的操作，而 `Layer` 在 `Runtime`。** -/
def extractLayer (ls : Layer) : List VectorConstraint :=
  ls.map extractVec

/-- **⭐ 列表版：先提取再编译，回到**原来的层**。**

**=> `compileToLayer (extractLayer ls) = ls`。**

**=> 证明是对 `ls` 归纳（等价于 `List.map_map` 加逐元素逆），
但它此前**没有**在 `Runtime` 层以这个形式出现。** -/
theorem compile_extract_layer (ls : Layer) : compileToLayer (extractLayer ls) = ls := by
  unfold compileToLayer extractLayer
  induction ls with
  | nil => rfl
  | cons l t ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨reinject_roundtrip l, ih⟩

/-- **⭐ 列表版：先编译再提取，回到**原来的约束集**。**

**=> `extractLayer (compileToLayer cs) = cs`。** -/
theorem extract_compile_constraints (cs : List VectorConstraint) :
    extractLayer (compileToLayer cs) = cs := by
  unfold compileToLayer extractLayer
  induction cs with
  | nil => rfl
  | cons c t ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨inject_extract_closed c, ih⟩

/-- **⭐ 回路是**双射**：`compileToLayer` 在层与约束集之间双向可逆。**

**=> 由上面两条合成：左逆与右逆同时成立。** -/
theorem compile_extract_bijective :
    Function.LeftInverse extractLayer compileToLayer
      ∧ Function.RightInverse extractLayer compileToLayer :=
  ⟨extract_compile_constraints, compile_extract_layer⟩

/-- **⭐⭐ 回路作为**验证判据**：给定层 `ls` 与约束集 `cs`，
`extractLayer ls = cs` ⟺ `compileToLayer cs = ls`。**

**=> 这把「这个权重层是否满足那组符号约束」变成**一次等式检查**。
**两个方向都成立，所以从任一侧出发的验证都合法。** -/
theorem verify_iff_recompile (ls : Layer) (cs : List VectorConstraint) :
    extractLayer ls = cs ↔ compileToLayer cs = ls := by
  constructor
  · intro h
    rw [← h]
    exact compile_extract_layer ls
  · intro h
    rw [← h]
    exact extract_compile_constraints cs

/-- **⚠ 否证：回路**不改变**任何东西 —— 它不是自动修复。**

**=> 陈述：存在一组合法的 `(ls, cs)` 使 `extractLayer ls = cs`，
但**回路**无论走多少遍都得到同一个 `ls`。**

**=> 结论：`闭环 = 验证回路` 的**回路**部分是**判据**，不是**修正**。
修正必须来自回路之外（`Repair` 的 `run`），这一点由 `VerificationLoop.lean` 承担。
本文件把这条边界写成可引用的陈述，防止「闭环」被读成「自动修好」。** -/
theorem loop_is_criterion_not_repair (ls : Layer) :
    compileToLayer (extractLayer (compileToLayer (extractLayer ls))) = ls := by
  rw [compile_extract_layer, compile_extract_layer]

end Lattice.Runtime.LoopClosure
