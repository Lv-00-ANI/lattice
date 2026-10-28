/-
# S13：**float 精化**——C 用 double 时的误差界

## 0. 补的是什么

`SEMANTICS-MAINLINE` 的 **S13** 说：「若 C 用 double，给出误差界；否则**显式**信任边界」。

`Lib/Quantization/RealIEEE754/Basic.lean` 已经有**一步**的舍入界：

```lean
IEEERound.err_bound : |R.toFun x − x| ≤ F.eps · |x| + F.tiny
```

`Lift/StackError.lean` 已经有**多层累积**的界：

```lean
netAct_deviation_le_devB : |netAct ls x − netAct ls' x| ≤ devB ε B G ls
```

**两者各自完整，但从未接起来。** 本节接上：**每一步的舍入误差，经 `k` 层累积，给出端到端的界。**
这正是「做了一半」的典型形态——两半都在，中间的连接没有。

## 1. 设计：把「浮点计算的层」建成一个显式的对象

```lean
roundLayer R L := { W := fun i j => R.toFun (L.W i j), b := fun j => R.toFun (L.b j) }
```

于是「C 用 double 跑这个网络」就是「**把所有层换成 `roundLayer R`**」，
而端到端误差是两个网络输出的差——**正好是 `devB` 的适用形状**。

**没有引入新的误差模型**：`R.err_bound` 就是 `IEEERound` 结构的字段，
**它是假设，不是从位级模型推出来的**——这就是 S13 要求「显式写出信任边界」的那条边界。
本节把它写成**显式的结构字段**，而不是埋在一个引理里。

## 2. 交付

| 声明 | 内容 |
|:--|:--|
| **`roundLayer`** | 一层在浮点下计算的结果 |
| **`roundLayer_rel`** | **逐项误差 ≤ `eps·Mn + tiny`**（由 `ieee_error_bound_of_le`） |
| `forall₂_map_round` | 原层栈与浮点层栈逐层 `ε`-接近 |
| **`float_stack_refinement`** | **`\|netAct ls x − netAct (map (roundLayer R) ls) x\| ≤ devB ε B G ls`** |
| **`float_refinement_trust_boundary`** | **信任边界的显式陈述**（N：不给 `err_bound` 则无结论） |

## 3. 边界的实质

- **`IEEERound.err_bound` 是一个假设**：`|round x − x| ≤ eps·|x| + tiny`。
  **本节不证它**，也不声称它来自 IEEE 754 的位级语义——它是 `IEEERound` 结构的字段。
  **S13 的「显式信任边界」就是这一条**，本节让它可见而不是隐藏。
- **`Mn` 必须界住所有层项**：`eps·Mn + tiny` 里的 `Mn` 是**输入界**，不是相对误差。
  若某层项无界，本节的界不适用——**那时不是「误差大」，是「没有界」**。
- **不在正规范围时 `eps·|x|` 那一项失效**：`RealIEEE754` 的
  `ieee_subnormal_abs_bound` 说明次正规区只剩绝对底 `tiny`。
  **本节用 `err_bound`（含 `tiny`），所以对次正规区仍然成立**——代价是界更松（多一个 `tiny`）。
- 本节**不声称 C 程序正确**：它说的是「浮点层的误差被 `devB` 界住」。
  C 的可执行语义是 `StackCodegen` 那一侧，**两者还没有连接**（见 §4）。

## 4. 为什么这个文件在 `Lib/` 而不在 `Lift/`

它同时需要 `Lift.StackError`（层 2，`devB`）与 `Lib.Quantization.RealIEEE754.Basic`（层 3）。
**`Lift` 不能 import `Lib`**（门禁 I4），所以它只能在层 3 或更高——即 `Lib/`。
这与 `Geo.NetLoss` 从 `Lift` 移到 `Geo` 是同一个判据：**模块的层由它 import 的最高层决定。**
-/
import Mathlib
import Lattice.Runtime.StackError
import Lattice.Lib.Quantization.RealIEEE754.Basic

namespace Lattice.Lib.FloatStackRefinement

open Lattice Lattice.Core Lattice.Lift.StackError

variable {n : ℕ}

/-! ## 一、浮点下的层 -/

/-- **一层在浮点下计算**：逐项舍入。

「C 用 double 跑这个网络」在本模型里就是「把所有层换成 `roundLayer R`」。 -/
noncomputable def roundLayer (F : FloatFormat) (m : RoundMode) (R : IEEERound F m)
    (L : AffineLayer (Fin n)) : AffineLayer (Fin n) where
  W := fun i j => R.toFun (L.W i j)
  b := fun j => R.toFun (L.b j)

/-- **逐项误差 ≤ `eps·Mn + tiny`**：直接来自 `ieee_error_bound_of_le`。

**这是 `IEEERound.err_bound` 的推论，而 `err_bound` 是假设**——S13 的信任边界在这里被使用。 -/
theorem roundLayer_rel (F : FloatFormat) (m : RoundMode) (R : IEEERound F m)
    (L : AffineLayer (Fin n)) {Mn : ℝ}
    (hW : ∀ i j, |L.W i j| ≤ Mn) (hb : ∀ j, |L.b j| ≤ Mn) :
    (∀ i j, |(roundLayer F m R L).W i j - L.W i j| ≤ F.eps * Mn + F.tiny) ∧
      (∀ j, |(roundLayer F m R L).b j - L.b j| ≤ F.eps * Mn + F.tiny) :=
  ⟨fun i j => ieee_error_bound_of_le F m R (hW i j),
   fun j => ieee_error_bound_of_le F m R (hb j)⟩

/-- **原层栈与浮点层栈逐层 `ε`-接近**（`ε := eps·Mn + tiny`）。 -/
theorem forall₂_map_round (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) :
    ∀ (ls : List (AffineLayer (Fin n))) {Mn : ℝ},
      (∀ L ∈ ls, (∀ i j, |L.W i j| ≤ Mn) ∧ (∀ j, |L.b j| ≤ Mn)) →
      List.Forall₂ (fun L L' =>
        (∀ i j, |L.W i j - L'.W i j| ≤ F.eps * Mn + F.tiny) ∧
        (∀ j, |L.b j - L'.b j| ≤ F.eps * Mn + F.tiny))
        ls (ls.map (roundLayer F m R)) := by
  intro ls
  induction ls with
  | nil =>
      intro Mn _
      exact List.Forall₂.nil
  | cons L rest ih =>
      intro Mn h
      rw [List.map_cons]
      refine List.Forall₂.cons ?_ (ih (fun L' hL' => h L' (List.mem_cons_of_mem L hL')))
      obtain ⟨hW, hb⟩ := h L (List.mem_cons_self L rest)
      have hr := roundLayer_rel F m R L hW hb
      exact ⟨fun i j => by rw [abs_sub_comm]; exact hr.1 i j,
             fun j => by rw [abs_sub_comm]; exact hr.2 j⟩

/-! ## 二、端到端：`k` 层累积 -/

/-- **S13：浮点层的端到端误差界。**

把网络每层换成浮点版本后，输出偏差被 `devB (eps·Mn + tiny) B G ls` 界住——
**每层的舍入误差被后面所有层放大，再逐层相加。**

**信任边界**：`R : IEEERound F m` 的 `err_bound` 是**假设**。本节不证它，
也不声称它来自 IEEE 754 的位级语义。**这条边界现在是一个显式的类型参数，不是一个脚注。** -/
theorem float_stack_refinement (F : FloatFormat) (m : RoundMode) (R : IEEERound F m)
    (ls : List (AffineLayer (Fin n))) {Mn B G : ℝ}
    (hMn : ∀ L ∈ ls, (∀ i j, |L.W i j| ≤ Mn) ∧ (∀ j, |L.b j| ≤ Mn))
    (hε : 0 ≤ F.eps * Mn + F.tiny) (hB : 1 ≤ B) (hG : 1 ≤ G)
    (hGl : ∀ L ∈ ls, gain L ≤ G) (hGr : ∀ L ∈ ls.map (roundLayer F m R), gain L ≤ G)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∀ j, |netAct ls x j - netAct (ls.map (roundLayer F m R)) x j|
      ≤ devB (F.eps * Mn + F.tiny) B G ls :=
  netAct_deviation_le_devB hε ls (ls.map (roundLayer F m R))
    (forall₂_map_round F m R ls hMn) hG hGl hGr B x hx hB

/-! ## 三、信任边界：写在散文里，不写成定理

初稿在这里放过一条

```lean
theorem float_refinement_trust_boundary (R : IEEERound F m) (x : ℝ) :
    |R.toFun x - x| ≤ F.eps * |x| + F.tiny := R.err_bound x
```

**删掉了。** 那是 `IEEERound` 的一个**字段投影**——证明体就是 `R.err_bound x`，一字未改。
审计已经把这种形态判过一次（`Core/Repair.stable`：*"证明体就是 R.absorbs x h，
即 Repair 结构体的一个字段投影，一字未改"*）。**再写一条同款的，就是把发现的东西又做了一遍。**

信任边界不需要定理，它需要读者看见：

- `float_stack_refinement` 的界是 `devB (F.eps · Mn + F.tiny) B G ls`；
- 其中 `F.eps`、`F.tiny`、`Mn` **来自舍入模型**（`IEEERound.err_bound`，**假设**），
  其余 `B`、`G`、`devB` 的形状**来自网络结构**；
- **`IEEERound.err_bound` 本身在本库中不是定理而是结构字段**，所以「这个界成立」等价于
  「存在一个满足 `err_bound` 的舍入模型」——**这就是 S13 要求显式写出的那条信任边界。**

**把它写成定理会让它看起来被证了，而它没有。** -/

end Lattice.Lib.FloatStackRefinement
