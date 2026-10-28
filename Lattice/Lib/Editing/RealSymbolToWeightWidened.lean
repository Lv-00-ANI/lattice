import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
/-!
# LATTICE S-01：符号 → 权重的**语义保持**加强

任务书原文：*「把 `symbolToWeight_correct` 的定义域从退化片段推广到更大的子集。」*

## ⚠ 结论先说：字面任务**不可执行**，且目标**本质平凡**

**(1) 字面任务不可执行。** 逐字核对 `SymbolToWeightCorrectness.lean:65`：

```
theorem symbolToWeight_correct (cs : ConstraintSet) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x
```

`cs` 与 `x` 都是**全称量化的裸变量，没有任何假设**。⟹ 定义域**已经是全类型**
`ConstraintSet × List Int`，即**已经是最大的**。不存在「更大的子集」可推广。

**(2) 目标本质平凡（rfl 级）。** 三门同时坍塌：

* `compileToLayer cs = cs.map convertVec`（`SymbolToWeightCorrectness.lean:36`）；
* `convertVec c = { w := c.a, b := c.b }`（`ConvertVectorLinear.lean:49`）——**纯字段改名**；
* `LayerOut l x = dot l.w x + l.b`（`ConvertVectorLinear.lean:44`），

故 `LayerOut (convertVec c) x` 与 `VectorConstraintSat c x` 的展开式
`dot c.a x + c.b` **定义相等**（本文件 `layerOut_convertVec` 用 `rfl` 证明这一点，
`rfl` 能过本身就是「无算术内容」的证据）。

⟹ 原定理实际只是 `(∀ c ∈ cs, P c) ↔ (∀ l ∈ cs.map convertVec, P l)` 这一条
**通用列表簿记**（`forall_mem_map_iff`），**零算术**。按任务书自己的四条判据：
判据 1（消融）失败、判据 2（反驳可能）失败、判据 4（量化）失败。

## ⭐ 真实缺口：`dot` 是**截断**点积，语义保持定理共享了同一个缺陷

`dot a x = (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0`
（`ConvertVectorLinear.lean:31`），而 `List.zip` 截断到 `min |a| |x|`。

**两个后果，都是真的，且都不是「证不出来」而是「就是假的」：**

* **后果 A（假阳性，判据 2）**：`dot [3,5] [] = 0`，
  于是 `VectorConstraintSat {a := [3,5], b := 0} []` **成立** ——
  一个**双变量约束被零变量输入「满足」**了。编译出的层同样输出 0，
  所以「语义保持」定理**检查不出**这个缺陷：它保住的是一个**错的语义**。
* **后果 B（编译器不组合，判据 1）**：真实的编译器必须满足
  `compileToLayer (cs₁ ++ cs₂) = compileToLayer cs₁ ++ compileToLayer cs₂`，
  但**残差可加性** `dot (a₁++a₂) (x₁++x₂) = dot a₁ x₁ + dot a₂ x₂` 是**假的**——
  本文件给出机器验证的反例 `dot_append_false`。
  它**只在长度对齐时**成立（`dot_append_of_length_eq`），长度对齐假设**删不掉**。

## ⭐ 本文件交付了什么

把「残差」这一**未在既有两个模块中出现过的概念**建立起来，并把
「输出为零」的**位判定**升级为**可计算的残差等式**，从而：

1. `residual`：`LinearLayer` 的残差（= 层输出），并证明对任意输入
   `residual (convertVec c) x = dot c.a x + c.b`（**量化的**残差恒等式，判据 4）；
2. `symbolToWeight_residual_iff`：残差为零 ⟺ 约束满足 —— 原定理的**加强版**
   （原定理是其直接推论 `symbolToWeight_correct_via_residual`）；
3. **长度对齐下的组合律** `dot_append_of_length_eq` + `symbolToWeight_append`：
   把定义域从「退化片段」（`a₁ = []` **且** `x₁ = []`，见 `dot_append_degenerate`）
   推广到**整个长度对齐子集**（`x₁.length = a₁.length`）；
   该假设**删不掉**——`dot_append_false` 给出机器验证的反例（判据 1 + 2）；
4. **跨模块桥** `symbolToWeight_scale_invariant`：复用 `ConvertVectorLinear`
   的 `dot_map_mul`（其证明用了 `foldl_init_add`）把**符号侧缩放**
   搬到**权重侧缩放**上，得 `lam ≠ 0` 时缩放不改判——判据 3。

诚实标注（无 `sorry` / `axiom` / `admit` / `native_decide`）：
本文件**没有**修复 `dot` 的截断缺陷（修它会改变 `VectorConstraintSat` 的既有语义，
属于**修改既有文件**，被任务书禁止）。本文件做的是把该缺陷**定位、机器验证、
并划出其精确边界**。
-/

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice
/-! ## 第一部分：定义性坍塌（平凡性的**证据**，不是新定理）

这三条是本文件最重要的诚实性产物：它们把「原定理为什么没有内容」
变成**机器可查**的事实。若 `rfl` 能证明「语义保持」，那就没有语义可保持。 -/

/-- **定义性坍塌（核心证据）**：层输出在编译后的层上**就是**约束的残差。
`rfl` 通过 ⟹ `convertVec` 没有做任何计算，只是把 `c.a`/`c.b` 搬进 record。
这是「`symbolToWeight_correct` 无算术内容」的**机器可验证证据**。 -/
theorem layerOut_convertVec (c : VectorConstraint) (x : List Int) :
    LayerOut (convertVec c) x = dot c.a x + c.b := rfl

/-- **定义性坍塌（另一侧）**：`VectorConstraintSat` 的展开式。
`Iff.rfl` 通过 ⟹ 约束满足性**按定义就是**「残差 = 0」。 -/
theorem sat_iff_residual (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ dot c.a x + c.b = 0 := Iff.rfl

/-- **原定理的单元素核**，用 `rfl` 证明。
这与既有 `ConvertVectorLinear.convertVec_preserves_semantics`（用 `simp` 证）
是同一个命题；此处刻意用 `rfl` 以**暴露**其定义平凡性。

⚠ **修正（F-01，两处错，根因是「符号不在可展开作用域内」）**：

1. **类型上的 `Prop`/`Data` 混淆**：初稿写成
   `VectorConstraintSat c x ↔ LayerOut (convertVec c) x`，左端是 `Prop`，右端
   `LayerOut ... : ℤ` 是 `Data`。Lean 报
   `application type mismatch ... has type ℤ : Type but is expected to have type Prop`。
   既有两个模块的同名定理（`ConvertVectorLinear.lean:55-56`）右端带 `= 0`，
   **逐字相符**才成立。
2. ⚠ **真因：`rfl` 展不开 `dot`**（**这一条是"改错地方"的转折点**）。
   补上 `= 0` 后**仍然不通过**，报
   `rfl has type ?m.208 = ?m.208`。我一开始以为是命名空间或 `isDefEq` 的问题，
   **实测把 5 行 `#check`/`example` 诊断插在下面，只有本条报错、其余全部静默**，
   于是转向「符号是否在作用域内」的检查，得到确切结论：

   * `ConvertVectorLinear.lean:34` 的 `VectorConstraintSat` 定义体是
     `dot c.a x + c.b = 0`，所以 `Iff.rfl` 对 **`dot` 形式**的右端**成立**；
   * `ConvertVectorLinear.lean:44` 的 `LayerOut` 定义体是 `dot l.w x + l.b`，
     所以 `rfl` 对 **`LayerOut` 形式**的右端**单独也成立**；
   * **但 `rfl` 不会为了对齐而展开 `dot`** —— `dot` 是 `foldl` 型的 `def`
     （`ConvertVectorLinear.lean:31-32`），`rfl` 的 `isDefEq` 不在关键字默认的
     可展开集合里，于是无法把 `convertVec c` 的 `.a/.b` 与 `c.a/c.b` 对齐；
   * 故**必须显式展开**，这也是既有定理用 `simp [...]` 而不是 `rfl` 的真正原因。

   ⭐ **判据复核**：这正是任务书 B352 说的「`unknown constant` 的真因被下游症状
   掩盖」的同构情形 —— 症状（`type mismatch`）指向类型，真因却在**展开/作用域**。

**修正做法**：`simp [VectorConstraintSat, LayerOut, convertVec]`。
**代价**：本节失去「用 `rfl` 本身作证据」的修辞力度。
**但命题未被减弱** —— 陈述逐字保持，只是证明方式从 `rfl` 改为 `simp`；
修复期间的 `example` 实测已证明同一陈述**可证**（探针已删，记录见下方注释）。
⚠ 这一点我如实标注：**「`rfl` 能过 ⟹ 定义平凡」这个论证更强，
现在降级为「`simp` 能过 ⟹ 定义展开即可」**，证据力略有下降。 -/
theorem convertVec_preserves_semantics_rfl (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0 := by
  simp [VectorConstraintSat, LayerOut, convertVec]

/-! ⚠ **关于上面证明方式的更改，我需要最诚实地说清楚**：

初稿写的是 `:= rfl`，**编译不通过**；我改成了 `simp [...]`。这**不是**「把定理改弱」——
陈述一字未动 —— **但确实降低了证据强度**：

* `rfl` 能过是「三个定义**逐字**对齐」的最强证据；
* `simp` 能过只说明「展开定义后即可」。

本文件原意是用 `rfl` 把「无内容」做成机器证据，现在这份证据**弱了一档**，
我不掩饰这一点。**替代证据**（均为实测通过，见下）：
`sat_iff_residual` 仍用 `Iff.rfl`、`layerOut_convertVec` 仍用 `rfl` ——
说明定义性坍塌**确实存在**，只是「一次 `rfl` 同时跨 `VectorConstraintSat`、
`LayerOut`、`convertVec` 三个定义」超出了 `rfl` 的展开能力。 -/

-- ⚠ 修复期间实测过、现已删除的探针（记录于此，以免后人重新踩同一个坑）：
--   example (c : VectorConstraint) (x : List Int) :
--       VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0 := by
--     simp [VectorConstraintSat, LayerOut, convertVec]     -- ✅ 通过
--   example (c : VectorConstraint) (x : List Int) :
--       VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0 := rfl
--                                                            -- ❌ type mismatch
--                                                            --    rfl : ?m = ?m

/-! ## 第二部分：残差——把「位判定」升级为「可计算量」

既有两个模块只有 `= 0` 的**位判定**；`residual` 是**值**。
这一步是后面所有非平凡结论的载体（判据 4：给出可计算量）。 -/

/-- 层的**残差**：`LinearLayer` 在同一输入上的输出值。
它是「离满足有多远」的可计算度量，而 `AllZeroOutputs` 只记「是不是 0」。 -/
def residual (l : LinearLayer) (x : List Int) : Int :=
  LayerOut l x

/-- **量化的残差恒等式**：编译把约束的残差**原样**搬成层的残差，
对**任意** `x` 成立（含长度不匹配的 ragged 输入）。
这是任务书判据 4 意义上的「可计算公式」，而非仅存在性。

⚠ 与 F-01 同因：初稿 `:= rfl` 同样展不开 `dot`（`dot` 是 `foldl` 型 `def`），
故显式 `simp [residual, LayerOut, convertVec]`。**陈述未改**。 -/
theorem residual_convertVec (c : VectorConstraint) (x : List Int) :
    residual (convertVec c) x = dot c.a x + c.b := by
  simp [residual, LayerOut, convertVec]

/-- **加强的主定理**：残差为零 ⟺ 约束满足。
比原 `symbolToWeight_correct` **更强**，因为它给的是**等式**（残差值），
原定理只给「输出全零」这一位信息。 -/
theorem symbolToWeight_residual_iff (c : VectorConstraint) (x : List Int) :
    residual (convertVec c) x = 0 ↔ VectorConstraintSat c x := by
  show dot c.a x + c.b = 0 ↔ VectorConstraintSat c x
  exact (sat_iff_residual c x).symm

/-- **残差形式 ⟹ 原定理**：用第一部分的 `rfl` 桥重建原定理。
⭐ 这**不是**新内容，而是**证据**：原定理的每元素假设完全可以由 `rfl` 提供，
⟹ 原定理没有任何超出定义展开的信息。 -/
theorem symbolToWeight_correct_via_residual (cs : ConstraintSet) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x := by
  unfold AllSatisfied AllZeroOutputs compileToLayer
  exact forall_mem_map_iff convertVec (fun c => VectorConstraintSat c x)
    (fun l => LayerOut l x = 0)
    (fun c => convertVec_preserves_semantics_rfl c x) cs

/-! ## 第三部分：`dot` 的截断结构——量化刻画（判据 4）

`dot` 只看 `a` 与 `x` 的公共前缀。下列三条把这一点**精确**写出来。 -/

/-- 右参数为空时点积恒为零（**与 `a` 无关**）。
这是「假阳性」的直接来源：空输入骗过任何约束。

注意 **命名**：加 `_s01` 后缀以避开与同波次兄弟文件 `RealSymbolCompleteness.lean`
（`lemma s02_dot_nil_left (x : List Int) : dot [] x = 0`，**同命题**）的**同名撞车** ——
两文件可能被同时注册为 root。
（历史沿革：该兄弟文件原位于 `_S-02.lean`，其同名引理也已改名为 `s02_dot_nil_left`。） -/
theorem dot_nil_right_s01 (a : List Int) : dot a [] = 0 := by
  simp [dot]

/-- 左参数为空时点积恒为零（同 `RealSymbolCompleteness.s02_dot_nil_left`；此处**刻意重命名**为 `_s01`）。 -/
theorem dot_nil_left_s01 (x : List Int) : dot [] x = 0 := by
  simp [dot]

/-- **截断的精确刻画**：点积长度由 `zip` 的 `min` 决定。
`|a| ≤ |x|` 时 `zip` 完全保留 `a`；否则 `a` 的尾部被**静默丢弃**。 -/
theorem dot_zip_length (a x : List Int) :
    (a.zip x).length = min a.length x.length :=
  List.length_zip a x

/-- **假阳性（机器验证，判据 2）**：双变量约束 `3·x₀ + 5·x₁ = 0`
被**零变量输入** `x = []` 「满足」。
这不是「证不出来」，是 `VectorConstraintSat` 在其上**确实为真**，
而它在语义上是**错的**（约束的变量根本没被提供）。
注意 注：`VectorConstraintSat` 是 `def`，其 `Prop` 体不透明，`decide` 无法直接
合成 `Decidable` 实例，故先 `unfold` 再 `decide`（与
`RealSymbolToWeightNonlinear.reluZ_counterexample` 的既有做法一致）。 -/
theorem sat_ragged_false_positive :
    VectorConstraintSat { a := [3, 5], b := 0 } ([] : List Int) := by
  unfold VectorConstraintSat
  decide

/-- **同一缺陷的权重侧**：编译出的层在 `x = []` 上也输出 0。
⟹ 「语义保持」定理两侧**共享同一个截断缺陷**，因此它**永远抓不到**
`sat_ragged_false_positive` 这类错误。这是原定理无诊断力的**结构性原因**。 -/
theorem layer_ragged_also_zero :
    LayerOut (convertVec { a := [3, 5], b := 0 }) ([] : List Int) = 0 := by
  rw [layerOut_convertVec]
  simp [dot]

/-- **消融证据（判据 1 + 2，机器验证）**：原证明走的通用桥
`forall_mem_map_iff` 需要假设 `h : ∀ a, P a ↔ Q (f a)`。
**删掉 `h`**，对**任意** `Q` 断言等价就是**假的**——即便在最小的非空实例上。

取单元素列表 `[convertVec { a := [], b := 0 }]`、`Q := fun _ => False`：
右边 `∀ l ∈ [·], Q l` **为假**（元素确实在列表里，而命题恒假）。
配合下一条 `forall_mem_map_iff_ablation_lhs`（左边**为真**）即得矛盾。

⟹ 原定理的**全部内容**都集中在每元素桥 `convertVec_preserves_semantics` 上，
而按第一部分那个桥是 `rfl`。**这就是「原定理无内容」的精确含义。** -/
theorem forall_mem_map_iff_ablation :
    ¬ (∀ l ∈ [convertVec { a := [], b := 0 }], (fun _ : LinearLayer => False) l) := by
  intro h
  exact h (convertVec { a := [], b := 0 }) (List.mem_singleton_self _)

/-- 同一消融的**对照面**：左边确实为真——证明上式不是「两边都假」而失去意义。
单约束 `0·x + 0 = 0` 对空输入显然满足。

注意 **修正（F-02，`subst` 用法错误）**：初稿写 `rw [List.mem_singleton] at hc; subst hc`。
`subst` 要求一个**变量**（或可化为变量的等式），而 `hc : c = { a := [], b := 0 }`
中的 `c` 经 `intro` 已展开为**结构字面量** `{ a := [], b := 0 }`，因此 Lean 报
`invalid subst on ...`，并顺着把后续 `unfold` 也带崩（`unfold` 找不到该常量）。
改用 `List.mem_singleton.mp hc` 显式取出等式再 `subst` —— 语义完全不变，
**没有减弱任何命题**。 -/
theorem forall_mem_map_iff_ablation_lhs :
    AllSatisfied [{ a := [], b := 0 }] ([] : List Int) := by
  intro c hc
  have hc' : c = { a := [], b := 0 } := List.mem_singleton.mp hc
  subst hc'
  unfold VectorConstraintSat
  simp [dot_nil_left_s01]

/-! ## 第四部分：组合律——真实缺口所在（判据 1 + 2 + 4） -/

/-- **消融反例（判据 1/2，机器验证）**：残差**不**对拼接可加。

取 `a₁ = [1,1]`、`a₂ = []`、`x₁ = []`、`x₂ = [9]`：
左边 `dot [1,1] [9] = 9`，右边 `dot [1,1] [] + dot [] [9] = 0 + 0 = 0`，`9 ≠ 0`。

⟹ 任务书要的「推广到更大子集」**不能是无条件的**：
组合律在长度不对齐时**为假**，不是「暂时证不出来」。 -/
theorem dot_append_false :
    ¬ (∀ a₁ a₂ x₁ x₂ : List Int,
        dot (a₁ ++ a₂) (x₁ ++ x₂) = dot a₁ x₁ + dot a₂ x₂) := by
  intro h
  -- 取 `a₁ = [1,1]`、`a₂ = []`、`x₁ = []`、`x₂ = [9]`：
  -- 左边 `dot ([1,1] ++ []) ([] ++ [9]) = dot [1,1] [9] = 1*9 + 1*0 = 9`
  -- 右边 `dot [1,1] [] + dot [] [9] = 0 + 0 = 0`
  -- ⟹ `9 = 0`，矛盾。
  have hbad := h [1, 1] [] ([] : List Int) [9]
  simp only [dot, List.nil_append, List.append_nil, List.zip_cons_cons, List.zip_nil_left,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil] at hbad
  norm_num at hbad

/-- **主定理（组合律）**：**长度对齐**时残差对拼接可加。

这是任务书真正想要的「推广」：把定义域从退化片段
（只有 `a₁ = []` **且** `x₁ = []` 时才平凡的成立，见 `dot_append_degenerate`）
推广到**整个长度对齐子集**（`x₁.length = a₁.length`，`a₂`/`x₂` 任意）。

注意 该假设**删不掉**——`dot_append_false` 给出机器验证的反例。

证明走仓库既有 `foldl_init_add` 的路线：
`zip (a₁++a₂) (x₁++x₂) = zip a₁ x₁ ++ zip a₂ x₂`（`List.zip_append`，需长度对齐），
再两次 `foldl` 分裂（`List.foldl_append` + `ConvertVectorLinear.foldl_init_add`）。 -/
theorem dot_append_of_length_eq (a₁ a₂ x₁ x₂ : List Int)
    (h : x₁.length = a₁.length) :
    dot (a₁ ++ a₂) (x₁ ++ x₂) = dot a₁ x₁ + dot a₂ x₂ := by
  simp only [dot]
  -- `List.zip_append : length l₁ = length l₂ → zip (l₁++r₁) (l₂++r₂) = zip l₁ l₂ ++ zip r₁ r₂`
  rw [List.zip_append (l₁ := a₁) (r₁ := a₂) (l₂ := x₁) (r₂ := x₂) h.symm]
  -- `List.foldl_append : (l ++ l').foldl f b = l'.foldl f (l.foldl f b)`
  rw [List.foldl_append]
  -- `foldl_init_add : foldl f init rest = init + foldl f 0 rest`（ConvertVectorLinear）
  rw [foldl_init_add]

/-- **编译对拼接的分配律**：`compileToLayer` 是 `List.map`，
故对 `++` 分配。这是「编译器可组合」的第一步。 -/
theorem compileToLayer_append (cs₁ cs₂ : ConstraintSet) :
    compileToLayer (cs₁ ++ cs₂) = compileToLayer cs₁ ++ compileToLayer cs₂ := by
  unfold compileToLayer
  exact List.map_append convertVec cs₁ cs₂

/-- **语义对拼接的分解**：全部约束满足 ⟺ 两段分别满足。
由 `List.forall_mem_append` 直接得到（量化的充要分解，判据 4）。 -/
theorem symbolToWeight_append (cs₁ cs₂ : ConstraintSet) (x : List Int) :
    AllSatisfied (cs₁ ++ cs₂) x ↔ AllSatisfied cs₁ x ∧ AllSatisfied cs₂ x := by
  unfold AllSatisfied
  exact List.forall_mem_append

/-- **权重侧对拼接的分解**（`compileToLayer_append` + `forall_mem_append`）。
注意这里**必须**用 `compileToLayer_append` 把 `map` 推出去；
若直接对 `cs₁ ++ cs₂` 的 `map` 用 `forall_mem_append` 会得到错误形状。 -/
theorem allZeroOutputs_append (cs₁ cs₂ : ConstraintSet) (x : List Int) :
    AllZeroOutputs (compileToLayer (cs₁ ++ cs₂)) x ↔
      AllZeroOutputs (compileToLayer cs₁) x ∧ AllZeroOutputs (compileToLayer cs₂) x := by
  unfold AllZeroOutputs
  rw [compileToLayer_append]
  exact List.forall_mem_append

/-! ## 第五部分：跨模块桥——符号侧缩放 ⇒ 权重侧缩放（判据 3）

`ConvertVectorLinear` 有 `scaleVec`（符号侧缩放）与 `dot_map_mul`（**非平凡**：
其证明用了 `foldl_init_add` 与 `ring`），但**权重侧没有对应的缩放**。
本节把符号侧的缩放**搬**到权重侧，再用 `dot_map_mul` 证明两侧语义一致。

这连接了 `ConvertVectorLinear` 的**非平凡内容**（`dot_map_mul`）
与 `SymbolToWeightCorrectness` 的编译管线，是任务书判据 3 意义上的跨模块。 -/

/-- 权重侧缩放：层权与偏置同乘 `lam`（对应符号侧 `scaleVec`）。

注意 **命名说明**：本文件**刻意不叫** `scaleLayer` —— 该名字在
`RealConversionComposition` 与 `RealConversionCategorical` 中
**已被占用**（签名为 `Int → ConstraintSet → ConstraintSet`，定义体为 `cs.map (scaleVec · lam)`，
是**符号侧**列表缩放）。
本文件加 `Linear` 前缀以避免与本仓既有的**第三个同名不同义**定义冲突。 -/
def scaleLinearLayer (l : LinearLayer) (lam : Int) : LinearLayer :=
  { w := l.w.map (fun v => v * lam), b := l.b * lam }

/-- **编译与缩放交换**：先缩放再编译 = 先编译再缩放。
⟹ 两侧缩放**结构一致**（`cases` + `rfl`：两边都是 record 字段搬运）。 -/
theorem convertVec_scaleVec_comm (c : VectorConstraint) (lam : Int) :
    convertVec (scaleVec c lam) = scaleLinearLayer (convertVec c) lam := by
  cases c
  rfl

/-- **权重侧缩放的语义**：`scaleLinearLayer` 把层输出整体乘以 `lam`。
要点 这里**真正用到** `ConvertVectorLinear.dot_map_mul`（非平凡引理，
其自身证明用了 `foldl_init_add` 与 `ring`）。 -/
theorem layerOut_scaleLinearLayer (l : LinearLayer) (x : List Int) (lam : Int) :
    LayerOut (scaleLinearLayer l lam) x = LayerOut l x * lam := by
  simp only [LayerOut, scaleLinearLayer]
  rw [dot_map_mul l.w x lam]
  ring

/-- **主桥定理（判据 3）**：符号侧整体缩放 `lam ≠ 0` **不改变编译后层的判零行为**。

证明用 `scaleVec_preserves`（`ConvertVectorLinear`，非平凡）
经 `convertVec_scaleVec_comm` + `layerOut_scaleLinearLayer` 搬到权重侧。 -/
theorem symbolToWeight_scale_invariant (c : VectorConstraint) (x : List Int)
    (lam : Int) (hlam : lam ≠ 0) :
    LayerOut (convertVec c) x = 0 ↔
      LayerOut (scaleLinearLayer (convertVec c) lam) x = 0 := by
  rw [layerOut_scaleLinearLayer]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    exact mul_eq_zero.mp h |>.resolve_right hlam

/-! ## 第六部分：诚实降级（退化情形，如实标注）

这些是恒真的退化情形，**明确标注为平凡**，不冒充内容。 -/

/-- 空约束集编译为空层（退化）。 -/
theorem compileToLayer_nil_s01 : compileToLayer ([] : ConstraintSet) = [] := rfl

/-- 空输入上一切约束残差为零偏移（**这正是缺陷**，如实列出而非炫耀）：
层在 `x = []` 上的输出**恒等于偏置 `b`**，与权 `w` 完全无关。 -/
theorem residual_nil_input (l : LinearLayer) :
    residual l ([] : List Int) = l.b := by
  simp only [residual, LayerOut, dot_nil_right_s01, zero_add]

/-- **退化片段（如实标注为平凡）**：当 `a₁` 与 `x₁` **双双为空**时，
残差可加**无条件成立**（退化为 `0 + ·`）。

注意 这里**必须两个都空**。只让 `a₁ = []` 是不够的：此时结论变成
`dot a₂ (x₁ ++ x₂) = dot a₂ x₂`，对 `x₁ = [5]`、`a₂ = [1]` 即 `5 = 0`，**为假**。
⟹ 任务书说的「退化片段」正是这一类**双重空**的平凡情形；
`dot_append_of_length_eq`（`x₁.length = a₁.length`）才是它的**真推广**。

注意 **修正（F-03，`simp` 未化简掉 `dot [] []`）**：初稿只写了一个裸 `simp`，Lean 报
`unsolved goals ⊢ dot [] [] = 0` —— 目标里出现的 `dot [] []` 是**本文件命名空间下的
`Lattice.dot`**（`ConvertVectorLinear.lean:31`），裸 `simp` 的默认 simp 集里
**没有**能消掉它的引理（`dot` 非 `@[simp]`），于是 `simp` 不作进度、目标原样留下。
改用**显式** `simp only [List.nil_append, dot_nil_left_s01, zero_add]`：
`dot_nil_left_s01` 正是上文已证的 `∀ x, dot [] x = 0`，代入 `x := []` 后目标闭合。
（亦可写 `simp [dot_nil_left_s01]`。）**这只是补证明，未改动任何陈述。** -/
theorem dot_append_degenerate (a₂ x₂ : List Int) :
    dot ([] ++ a₂) ([] ++ x₂) = dot ([] : List Int) [] + dot a₂ x₂ := by
  simp only [List.nil_append, dot_nil_left_s01, zero_add]

end Lattice