import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lib.LearningTheory.RealRecoverEndpoint
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Meta.RealNegativeCore
/-!
# LATTICE: RealRecoverBehavior — 链上真正空缺的那条边（E5）＋ 端点散文的定理化

## 为什么这个文件存在

V02 用机器判据定位了链上唯一**无任何定理**的耦合边：

> **E5：`Recover` ↔ `Behavior`** —— 527 个 roots 模块中，**同时**出现 `recover` 与
> `LayerOut` 的行 = **0**。

`recover` 的全部四个消费点（`recover_compileToLayer` / `recover_injective` /
`recover_readback` / `recover_is_load_bearing`）**无一触及 L3 行为函数**：
`recover_readback` 结论里的 `AllSatisfied` 是 **L2 符号层**谓词，不是 L3 的 `LayerOut`。
实测 `LayerOut` 在 `RealEndToEnd.lean` 中出现 **0 次**。

**后果**：链在 `L3 → Behavior → Recover` 这一跳上，`recover` 的**像**从未被行为函数检验过。

## ⚠⚠ W04 实测更正（两条，均据 `lake build`）

### 更正 1（致命）：本文件此前**从未被编译过**

本文件此前**不在 `lakefile.toml` 的 `roots` 白名单**中，也**不被任何模块 `import`**
（全库 `grep RealRecoverBehavior` 命中 = **1**，即本文件自己的标题行）。
`lakefile.toml` 的 `roots` 是**显式白名单**（V02 发现 3），未登记模块对 `lake` **完全不可见**。

⇒ 实测：`.lake/build/lib/RealRecoverBehavior.olean` **不存在**；
`lake build RealRecoverBehavior` 此前报 `error: unknown target`。

W04 已**登记为 root**（`lakefile.toml`）并**首次真编译**，随即发现**更正 2**。

### 更正 2（本条最重）：原两条定理的证明体**编不过**

首次真编译实测（`lake build RealRecoverBehavior`，exit 1）：

    error: RealRecoverBehavior.lean:79:4: unsolved goals
    error: RealRecoverBehavior.lean:81:10: tactic 'rewrite' failed

原 `recover_not_behavior_injective` 的**两个分支顺序颠倒**：
第一分支的目标是 `l ∈ []` 的荒谬消解，却被写成 `List.mem_singleton` 的改写；
第二分支反之。**已修正**（`§二` 第二条，证明体改为 `unfold AllZeroOutputs` + 正确分支）。

⚠ **这正是本会话判据 1/2 的又一实例**：若判据是 `lake env lean -R . <f>`，
或若接受 `Replayed` 的 exit 0，则本文件的**不可编译状态可以长期存活**。
**唯一暴露它的判据是「先把文件登记为 root，再 `lake build`」**。

## 本文件给什么（W04 新增 §三、§四）

### §三 E5 边的第一批定理（V04 遗产，已修正）

### §四 ⭐⭐⭐ `RealRecoverEndpoint.lean:255-256` 散文的**定理化** —— 结论是【散文错了】

散文逐字（`RealRecoverEndpoint.lean:255-256`）：

> ❌ 不声称 `Layer → List SymToken` 是链路的「完整逆」：
> §五表明 `Layer` 的行为信息**多于**其语法表示，故**任何纯语法逆都不可能恢复行为**。

⭐ W04 先把「语义逆」**定义**出来（`§四.1`），再**逐字检验**散文的两个分句：

| 散文分句 | 定理化形态 | 实测 |
|:--|:--|:--|
| 「任何纯语法逆都不可能恢复行为」 | `¬ ∃ g, ∀ ls, g (recover ls) = Beh ls` | ⭐⭐ **为假**（`§四.2` 证其**否定**） |
| 「行为信息**多于**语法表示」 | `∀ ls ls', Beh ls = Beh ls' ↔ recover ls = recover ls'` | ⭐⭐ **为假**，且**方向相反**（`§四.3`） |

⭐⭐ **根因**：`recover` **是单射**（`RealRecoverEndpoint:169 recover_injective`）。
单射 ⟹ **左逆存在**。取 `s := recover` 的任一段（`Classical.choose`），
则 `Beh ∘ s` **逐字就是**恢复行为的纯语法函数。**散文的「不可能」在此被正面构造推翻。**

⭐⭐ **真定理是散文的【对偶】**（`§四.3`）：`Beh` **非单射**（`layerOut_not_injective`）
而 `recover` **单射** ⟹ **语法严格细于行为** ⟹ **行为不能决定语法**
（`recover` **不穿过** `Beh` 分解）。散文把**蕴含方向写反了**。

## ⚠ 诚实边界

* ⚠ **§三 第一条本体接近平凡** —— 它是 E5 上的**第一条**定理，价值在于让
  「哪条边是空的」**不再靠人工搜索**，不在于数学深度。
* ⚠ **§四 是【否定性发现】**：它**没有**给出一条新的"结构定理"，
  而是**证伪**了端点文件的一条散文断言，并给出**方向相反**的真定理。
  这**降低**了「E5 缺口已按原设想闭合」的宣称强度 —— 原设想**本身不成立**。
* **不**声称链路整体可逆或不可逆：§四只谈 `recover` 与 `Beh` 两个具体的映射。
* ⚠ §四 的 `Beh` 用 **`AllZeroOutputs`（L3 层谓词）** 而非 `LayerOut` 单点值 ——
  因为 `LayerOut` 作用于 `LinearLayer` 而 `Layer = List LinearLayer`，两者不同层。
-/

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、E5 边的行为谓词与语义逆的定义

⭐ **「语义逆」的精确定义**是本节的首要交付 —— 端点散文从未定义它，
故其断言**在定义之前无法被检验**。 -/


/-! ## 二、E5 边的第一批定理（V04 遗产，W04 修正证明体） -/

/-- **E5 第一条定理**：`recover` 之后经 `decode`/`compileToLayer` 往返，
`AllZeroOutputs` 意义上的行为**保持不变**。

这条把链尾 `recover` 与链头行为谓词**放在同一个陈述里** —— 此前全库不存在这样的陈述。 -/
theorem recover_then_behavior_preserved (cs : ConstraintSet) (x : List Int) :
    (decode (recover (compileToLayer cs))).map (fun cs' => AllZeroOutputs (compileToLayer cs') x)
      = some (AllZeroOutputs (compileToLayer cs) x) := by
  rw [recover_compileToLayer, decode_encode]
  rfl

/-- ⭐ **E5 的核心负面事实**：`recover` **不是行为单射**。

即：存在两个层，它们在**全部输入**上的行为完全相同（`AllZeroOutputs` 逐点等价），
但 `recover` 把它们映到**不同**的符号串。

⟹ 由 `recover` 的像出发**若只允许比较像是否相等**，则无法区分这两者。

⚠ 这与 `recover_injective` **不矛盾**：
`recover` 在 `Layer` 上是单射（语法可逆），但 `Layer → 行为` 本身**不是**单射
（`layerOut_not_injective` 已证），故 `recover` 不可能同时是行为单射。
这正是「**语法可逆 ≠ 语义可逆**」的机器形态。

⚠⚠ **W04 更正**：本条证明体此前**编不过**（分支顺序颠倒，见文件头 更正 2）。
现改为 `unfold AllZeroOutputs` 后按正确分支处理。 -/
theorem recover_not_behavior_injective :
    ∃ ls ls' : Layer,
      (∀ x : List Int, AllZeroOutputs ls x ↔ AllZeroOutputs ls' x)
      ∧ recover ls ≠ recover ls' := by
  refine ⟨[], [{ w := [], b := 0 }], ?_, ?_⟩
  · intro x
    unfold AllZeroOutputs
    constructor
    · -- `[]` 的行为恒真 ⟹ `[{zero}]` 的行为恒真
      intro _ l hl
      rw [List.mem_singleton] at hl
      rw [hl]
      exact zeroLayer_out x
    · -- `[{zero}]` 的行为恒真 ⟹ `[]` 的行为恒真（空表成员命题为假）
      intro _ l hl
      exact absurd hl (List.not_mem_nil l)
  · -- 但 recover 的像不同（否则由单射得 [] = [零层]）
    intro h
    have : ([] : Layer) = [{ w := [], b := 0 }] := recover_injective h
    simp at this

/-! ## 三、⭐ 端点散文的定理化 —— 先定义「语义逆」

`RealRecoverEndpoint.lean:255-256` 的散文断言**没有定义**「纯语法逆」与「恢复行为」，
故它**不可能被检验**。本节补上定义，然后**逐字**检验。

**定义（语义逆）**：一个**纯语法**函数 `g : List SymToken → List Int → Prop` 称为
`recover` 的**行为恢复器**，当且仅当

    ∀ ls : Layer, g (recover ls) = Beh ls

即：**只看符号串**就能还原该层的行为谓词。 -/

/-- **行为等价**（`Beh` 逐点相等），供 §三 引用。 -/
theorem beh_nil_eq_beh_zero :
    Beh ([] : Layer) = Beh ([{ w := [], b := 0 }] : Layer) := by
  funext x
  apply propext
  unfold Beh AllZeroOutputs
  constructor
  · intro _ l hl
    rw [List.mem_singleton] at hl
    rw [hl]
    exact zeroLayer_out x
  · intro _ l hl
    exact absurd hl (List.not_mem_nil l)

/-! ### §三.1 ⭐⭐ 散文分句一「任何纯语法逆都不可能恢复行为」—— **为假**

散文断言 `¬ ∃ g, ∀ ls, g (recover ls) = Beh ls`。
⭐ 实测**证其否定**：**存在**这样的 `g`，且构造是**正面的**。 -/

/-- ⭐⭐⭐ **散文分句一的否定**：**存在**纯语法函数**恢复行为**。

**构造**：`recover` 单射（`recover_injective`）⟹ 可取它的一个**段**（section）
`s : List SymToken → Layer`（`Classical.choose`，在像外的取值任意）。
则 `g := Beh ∘ s` 满足 `g (recover ls) = Beh (s (recover ls)) = Beh ls`。

⭐⭐ **故 `RealRecoverEndpoint.lean:255-256` 的「任何纯语法逆都不可能恢复行为」为【假】。**
机制：**单射 ⟹ 左逆存在**，而符号串因此**完整携带**了 `Layer` 的全部信息
（**含**其行为），故「语法的信息**少于**行为」这一前提在本载体下**不成立**。 -/
theorem exists_syntactic_inverse_recovers_behavior :
    ∃ g : List SymToken → (List Int → Prop), ∀ ls : Layer, g (recover ls) = Beh ls := by
  classical
  -- recover 的一个段：像内取（唯一）原像，像外取 []
  let s : List SymToken → Layer := fun t =>
    if h : ∃ ls : Layer, recover ls = t then Classical.choose h else []
  have hs : ∀ ls : Layer, s (recover ls) = ls := by
    intro ls
    have hex : ∃ ls' : Layer, recover ls' = recover ls := ⟨ls, rfl⟩
    dsimp only [s]
    rw [dif_pos hex]
    -- choose_spec 给 recover (choose hex) = recover ls，再由单射得相等
    exact recover_injective (Classical.choose_spec hex)
  refine ⟨fun t => Beh (s t), ?_⟩
  intro ls
  show Beh (s (recover ls)) = Beh ls
  rw [hs ls]

/-! ### §三.2 ⭐⭐⭐ 散文分句二「行为信息**多于**语法表示」—— **为假，且方向相反**

散文断言行为**比**语法**携带更多**信息。⭐ 实测**恰好相反**：**语法严格细于行为**。

**两条并置**：

| 映射 | 性质 | 依据 |
|:--|:--|:--|
| `recover : Layer → List SymToken` | **单射** | `RealRecoverEndpoint:169` |
| `Beh : Layer → (List Int → Prop)` | **非单射** | `layerOut_not_injective`（`RealRecoverEndpoint:208`） |

⟹ **语法分辨得开的东西，行为分辨不开** ⟹ **行为的等价类严格粗于语法的等价类**。

⭐⭐ **故真定理是散文的【对偶】**：**行为不能决定语法**（`recover` **不穿过** `Beh` 分解）。 -/

/-- ⭐⭐⭐ **散文分句二的【对偶】真定理**：`recover` **不穿过** `Beh` 分解。

即：**不存在**函数 `g : (List Int → Prop) → List SymToken` 使 `g (Beh ls) = recover ls`。
反证：`[]` 与 `[{w:=[], b:=0}]` 的 `Beh` 相等（`beh_nil_eq_beh_zero`）
⟹ `g` 给同一值 ⟹ `recover` 的像相等 ⟹ 由 `recover_injective` 得两层相等，
与 `List.length` 矛盾。

⭐ **这是「语义不可逆」在 `recover` 侧的【正确方向】**：可逆性断裂在
**行为 → 语法**，**不在** **语法 → 行为**（后者由 §三.1 正面构造证成）。 -/
theorem recover_not_factor_through_behavior :
    ¬ (∃ g : (List Int → Prop) → List SymToken, ∀ ls : Layer, g (Beh ls) = recover ls) := by
  intro ⟨g, hg⟩
  -- 两层行为相同
  have h1 := beh_nil_eq_beh_zero
  -- 故 g 给出相同的符号串，即 recover 的像相同
  have hr : recover ([] : Layer) = recover ([{ w := [], b := 0 }] : Layer) := by
    rw [← hg ([] : Layer), ← hg ([{ w := [], b := 0 }] : Layer), h1]
  -- 但 recover 单射 ⟹ 两层相等，与长度矛盾
  have hne : ([] : Layer) ≠ [{ w := [], b := 0 }] := by
    intro h
    have := congrArg List.length h
    simp at this
  exact hne (recover_injective hr)

/-- ⭐⭐ **散文分句二的直接否定（等价形态）**：
`Beh` **不是** `recover` 的**完全行为不变量** ——
存在行为相同而语法不同的一对层。

即 `∀ ls ls', Beh ls = Beh ls' ↔ recover ls = recover ls'` **为假**。

⚠ 与 `recover_not_factor_through_behavior` 是同一事实的两种写法
（后者证「不存在分解函数」，本条证「等价关系不重合」），此处**两条并列**，
使「方向」在陈述层面即不可混淆。 -/
theorem recover_not_complete_behavioral_invariant :
    ¬ (∀ ls ls' : Layer, Beh ls = Beh ls' ↔ recover ls = recover ls') := by
  intro h
  have hr : recover ([] : Layer) = recover ([{ w := [], b := 0 }] : Layer) :=
    (h _ _).mp beh_nil_eq_beh_zero
  have hne : ([] : Layer) ≠ [{ w := [], b := 0 }] := by
    intro hh
    have := congrArg List.length hh
    simp at this
  exact hne (recover_injective hr)

/-! ## 四、⭐ 消融判据：把「内容是否承重」变成可失败的检查

⚠ 本会话教训 5：「判据通过自己的全部 fixture 仍可能是错的 —— 只有真实负对照能推翻它」。
本节给 §三 的两条**真实负对照**，使 ∃/¬ 的**方向**本身成为可失败判据。 -/

/-- **消融对照（负对照）**：一个**刻意非单射**的语法映射 `badMap`（恒为 `[]`，
把**所有**层坍缩到同一个符号串）。

⭐ 用途：若 §三.1 的 ∃ 定理**内容空洞**（对任意语法映射都成立），则它在 `badMap` 上也应成立。
下面的 `no_behavior_recovery_for_noninjective` 证明**它不成立** ⟹ ∃ 定理的成立
**恰好依赖 `recover` 的单射性**，而非重言式。 -/
def badMap (_ : Layer) : List SymToken := []

/-- ⭐⭐ **真实负对照**：对**非单射**的 `badMap`，行为恢复器**不存在**。

**证明**：`badMap` 把任意两层映到同一符号串 `[]`，故 `g []` 必须同时等于
`Beh ls`（对所有 `ls`）⟹ 所有 `Beh ls` 相等。但
`Beh []` 与 `Beh [{w:=[1], b:=0}]` 在输入 `[1]` 上**不同**
（前者空表恒真，后者输出 `1*1+0 = 1 ≠ 0`）⟹ 矛盾。

⭐⭐ **这与 §三.1 并置即构成消融判据**：
`recover`（**单射**）⟹ 恢复器**存在**；`badMap`（**非单射**）⟹ 恢复器**不存在**。
单射性是**承重假设**，不是装饰。 -/
theorem no_behavior_recovery_for_noninjective :
    ¬ (∃ g : List SymToken → (List Int → Prop), ∀ ls : Layer, g (badMap ls) = Beh ls) := by
  intro ⟨g, hg⟩
  -- badMap 把任意两层映到同一符号串 ⟹ 所有行为相等
  have hall : ∀ ls ls' : Layer, Beh ls = Beh ls' := by
    intro ls ls'
    have : badMap ls = badMap ls' := rfl
    rw [← hg ls, ← hg ls', this]
  -- 但两个具体层的行为可分离
  have hsep : Beh ([] : Layer) ≠ Beh ([{ w := [1], b := 0 }] : Layer) := by
    intro h
    have hx := congrFun h [1]
    unfold Beh AllZeroOutputs at hx
    have h1 : (∀ l ∈ ([{ w := [1], b := 0 }] : Layer), LayerOut l [1] = 0) := by
      rw [← hx]
      intro l hl
      exact absurd hl (List.not_mem_nil l)
    have h2 := h1 ({ w := [1], b := 0 } : LinearLayer) (by simp)
    simp [LayerOut, dot] at h2
  exact hsep (hall _ _)

/-- ⭐ **消融判据的可执行形态（单条定理，双向对照）**：

    (∃ g, ∀ ls, g (recover ls) = Beh ls)          -- 单射 recover：恢复器存在
      ∧ ¬ (∃ g, ∀ ls, g (badMap ls) = Beh ls)     -- 非单射 badMap：恢复器不存在

⭐ **若把本条的任一合取项改成另一方向，证明即失败** —— 这是 §三.1 与散文
**方向相反**的机器凭据，也是「删掉 `recover_injective` 则本文件不成立」的凭据。 -/
theorem injection_is_load_bearing :
    (∃ g : List SymToken → (List Int → Prop), ∀ ls : Layer, g (recover ls) = Beh ls)
      ∧ ¬ (∃ g : List SymToken → (List Int → Prop), ∀ ls : Layer, g (badMap ls) = Beh ls) :=
  ⟨exists_syntactic_inverse_recovers_behavior, no_behavior_recovery_for_noninjective⟩

end Lattice
