import Mathlib
import Lattice.Lib.Chain.RealEndToEnd
import Lattice.Lib.Chain.RealEndToEndNontrivial

/-!
# P1-7：`L1Bridge` 的**同态性**（阶段 A）

## 规划中的第三项

**三个 e2e 文件（`RealE2EComposite`、`RealChainEntryOOV`、`RealEndToEndNontrivial`）都**逐 token 递归重算**
`L1Bridge`，因为库里没有一条「拼接」引理。**

**=> 本文件补上它：**

```lean
L1Bridge_append (ts₁ ts₂) : L1Bridge (ts₁ ++ ts₂) = L1Bridge ts₁ ++ L1Bridge ts₂
```

## 为什么这条应当成立，而且不难

**`L1Bridge` 的定义是：**

```lean
| [] => []
| t :: ts => SymToken.sym (charCode t) :: SymToken.sep :: L1Bridge ts
```

**它把每个 token 翻译成**固定长度的两块**（`sym` 加 `sep`），然后接上余下的递归结果 ——
这正是列表同态的形状。**拼接在两种顺序下都得到「逐 token 的两块依次排列」，因此相等。**

## 它的用途

**有了这条，任何形如 `L1Bridge (a ++ b)` 的表达式可以**拆开处理**，而不必重新展开定义。
三个 e2e 文件里逐 token 重算的模式可以改为一次 `rw [L1Bridge_append]`。** -/

namespace Lattice.Lib.Chain.RealEndToEnd

/-- **`L1Bridge` 保持列表拼接：它是一条列表同态。**

**=> 对 `ts₁` 归纳：`[]` 情形是 `L1Bridge [] = []`，`t :: ts` 情形由 `L1Bridge_cons` 两次改写后
用归纳假设。** -/
theorem L1Bridge_append (ts₁ ts₂ : List CharToken) :
    L1Bridge (ts₁ ++ ts₂) = L1Bridge ts₁ ++ L1Bridge ts₂ := by
  induction ts₁ with
  | nil => simp only [List.nil_append, L1Bridge]
  | cons t ts ih =>
      simp only [List.cons_append, L1Bridge_cons, ih, List.append_assoc]

/-- **同态的推论：长度可加。**

**=> 由 `L1Bridge_append` 与 `List.length_append` 立得；单独命名以便在守恒引理里直接引用。** -/
theorem L1Bridge_append_length (ts₁ ts₂ : List CharToken) :
    (L1Bridge (ts₁ ++ ts₂)).length = (L1Bridge ts₁).length + (L1Bridge ts₂).length := by
  rw [L1Bridge_append, List.length_append]

/-- **同态的推论：拼接后的段展开恰是两段展开的**拼接**。**

**=> 注意：`toSegs` 本身**不**是列表同态（它在段边界处会合并），
所以不能直接从 `L1Bridge_append` 滑过去。
但 `L1Bridge` 的像在每个 token 后都有 `sep`，所以段 **不会**跨边界合并 ——
用 `d41_toSegs_L1Bridge` 把两边都写成逐 token 单元素段，结论就是 `List.map_append`。** -/
theorem toSegs_L1Bridge_append (ts₁ ts₂ : List CharToken) :
    toSegs (L1Bridge (ts₁ ++ ts₂)) = toSegs (L1Bridge ts₁) ++ toSegs (L1Bridge ts₂) := by
  rw [d41_toSegs_L1Bridge, d41_toSegs_L1Bridge, d41_toSegs_L1Bridge, List.map_append]

end Lattice.Lib.Chain.RealEndToEnd
