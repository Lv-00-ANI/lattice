import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lift.RealTokenSymbolLink
-- 注意 `extractLayer` 有【三个】roots 模块各自声明（`RealCompileExtractClosed:100` /
-- `RealExtractCanonical:79` / `RealRflAudit:69`，三处定义体**逐字相同** `ls.map extractVec`）。
-- 同时 import 两个以上会产生**同名冲突**（正是 `SymToken` 改名登记所记的那类断裂，
-- `RealTokenSymbolLink:68-76`）。本文件**只 import 一个**，取最早声明处。
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: RealRecoverEndpoint —— 链路「Recover 段」的类型层补全（`Layer → List SymToken`）

## 定位（本文件补的是哪一处缺口）

链路 `L0 数据 ⇄ L1 token ⇄ L2 符号 ⇄ L3 权重` 的**逆向**此前在 `L3 → L2` 处终止：

* `extractVec : LinearLayer → VectorConstraint`（单对象，`WeightToSymbolEquivalence:55`）
* `extractLayer : Layer → ConstraintSet`（列表级适配子，`RealCompileExtractClosed:100`）

但**没有任何声明把 `Layer` 接到 token 层**。全库 `def recover` **0 命中**
（`PROCESS.md §10` 的「⇒ 下一步」第 2 条；`CORRECTIONS B400.5 P1-1`）。

本文件补上 `recover : Layer → List SymToken`，即 `L3 → L1` 这一跳的类型层载体。

## ⚠⚠ 本节最重要的话：`recover` 是**由既有部件复合**的，不是新数学

`CORRECTIONS B400.5 P1-1` 逐字称它「**1 行可构造**」。这是**真的**，且本文件据此**只做接线**：

    recover ls = encode (extractLayer ls)

即 `Layer --extractLayer--> ConstraintSet --encode--> List SymToken`。
**两个部件都已存在且已在 roots**，故本文件**不引入任何新定义性内容**。

⭐⭐ **本文件的核心交付 = 一个【与任务书预期相反】的机器验证结论。**

`B400.5 P1-1` 与 `PROCESS.md:498` 都要求「**必须同时给出非单射反例**」——
其**隐含前提**是「`L3 → L1` 这一跳**必然有损**」。

⭐⭐ **本文件证明该前提【不成立】**（§四 的 `recover_injective`，机器验证）：

    extractVec  : LinearLayer → VectorConstraint   是【双射】（`w↔a`, `b↔b`，纯字段重命名）
    encode      : ConstraintSet → List SymToken    是【单射】（既有 `encode_injective`）
    ⟹ recover = encode ∘ extractLayer              必然是【单射】

**结构性原因**：`Layer := List LinearLayer` 与 `ConstraintSet := List VectorConstraint`
**逐字段同构**（`LinearLayer` 恰有 `w`/`b`，`VectorConstraint` 恰有 `a`/`b`），
故 `Layer` 的信息量**不超过** `ConstraintSet` ⟹ **这条边上根本没有信息损失**。

⭐ **真正的不可逆性在【行为层】**（§五，`layerOut_not_injective`）：可验证 ——
`[]` 与 `[{w:=[], b:=0}]` 是**不同的** `Layer`，却**行为完全相同**。

⚠ **这【不是】「缺口已闭合」的好消息**，而是「**缺口的形式与预期不同**」的发现：
不可逆性**不在** `L3→L1` 语法边，而在 `Layer→行为`。
⇒ 建议按本结论更新 `B400.5 P1-1`（本文件 §6.3 已给出接口表）。

⚠ **同时如实登记**：作者**最初也按任务书预期**去构造非单射反例
（原设想用「空层 vs 含零层」），**逐层展开后发现该见证两个像并不相等**
（`[]` vs `[sym 0, sep]`）⟹ **原计划被自我否证**，按 `PROCESS.md §3.3` 五步保留原设想、改证其反面（§六）。

## 诚实边界（本文件不证 / 不声称的）

- **不证 `recover` 是左逆**：`extractLayer ∘ compileToLayer = id` 在**对象层**成立
  （纯字段重命名），但 `recover ∘ compileToLayer` 与 `encode` 的复合**不是** `Layer → Layer`
  的恒等，本文件**不声称**链路「可逆」。
- ⭐ **本文件证的是【不可逆在别处】**：`recover` **是单射**（§四），
  而不可逆性位于 `Layer → 行为`（§五）。
- **不涉及 L0**：无 `Char`/`String`/字节层。
- 不使用 sorry / axiom / admit。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、`recover` 的定义：两个既有部件的复合

`extractLayer`（`RealCompileExtractClosed:100`）与 `encode`
（`RealTokenSymbolLink:138`）都已在 roots，故 `recover` 是**纯接线**。 -/

/-- **Recover 段（L3 → L1）**：把一层权重还原为符号 token 序列。

⭐ **构造方式**：`extractLayer`（逐层提取回符号约束）后接 `encode`（符号 → token）。
**两个部件都是既有的**；本定义不含任何新的数学内容。

⚠ **诚实标注（`PROCESS.md §2.2` 的问题：「这条定理比它的【定义】多说了什么？」）**：
就 `recover` 的**定义**而言，它什么也没多说 —— 它只是把两个已有函数接起来。
**本文件的实质内容全在 §四/§五**：关于该复合的**单射性**（正面、但相对定义不算多），
以及**行为层不可逆**（否定，且是真正有信息量的那一半）。 -/
def recover (ls : Layer) : List SymToken :=
  encode (extractLayer ls)

/-! ## 二、单步正确性：`recover` 在编译像上确实还原出原 token

这是 `recover` 唯一**正面**的性质。它真实但**弱**：只在 `compileToLayer` 的像上成立。 -/

/-- **`recover` 在编译像上是 `encode ∘ id`**：对任意约束集 `cs`，
`recover (compileToLayer cs) = encode cs`。

⚠ **本条的有效范围【仅限编译像】**：`compileToLayer` 是单射（逐项 `convertVec`，
纯字段重命名），但 `recover` 的定义域是**整个 `Layer`**，
其中包含**不来自任何约束集**的层。§四 证明即便那样 `recover` 仍单射。 -/
theorem recover_compileToLayer (cs : ConstraintSet) :
    recover (compileToLayer cs) = encode cs := by
  unfold recover
  congr 1
  -- extractLayer (compileToLayer cs) = cs：两侧都是逐项字段重命名
  unfold extractLayer compileToLayer
  rw [List.map_map]
  -- 现在只需 `extractVec ∘ convertVec = id`
  have : (extractVec ∘ convertVec) = (id : VectorConstraint → VectorConstraint) := by
    funext c
    exact roundtrip_extractVec c
  rw [this, List.map_id]

/-! ## 三、`extractLayer` / `extractVec` 在当前载体下【无损】

`extractVec l = { a := l.w, b := l.b }` 只看 `l.w` 与 `l.b`，
而 `LinearLayer` **恰好只有这两个字段** ⟹ 它是**双射**（逆是 `convertVec`）。

⭐ **这正是「非单射反例」构造不出来的结构性原因** —— 见 §四。 -/

/-- **`extractVec` 在当前载体下是单射**（`LinearLayer` 恰有 `w`/`b` 两字段，
`extractVec` 是完整的字段重命名；其逆为 `convertVec`，见 `roundtrip_extractVec`）。 -/
theorem extractVec_injective : Function.Injective (extractVec : LinearLayer → VectorConstraint) := by
  intro l₁ l₂ h
  -- 两条记录相等 ⟹ 逐字段相等
  have hw : l₁.w = l₂.w := congrArg VectorConstraint.a h
  have hb : l₁.b = l₂.b := congrArg VectorConstraint.b h
  cases l₁
  cases l₂
  simp_all

/-! ## 四、⭐⭐ 核心发现：`recover` **不是**非单射 —— 任务书预期被否证

**任务书预期**（`B400.5 P1-1`、`PROCESS.md:498`）：`recover` 应有**非单射反例**。

### 4.1 原设想（已否证，如实保留）

原计划用**空层 `[]`** 与**含一个零层的层 `[{ w := [], b := 0 }]`** 作见证，理由是「零层不携带信息」。

**逐层展开后该设想【不成立】**：
1. `extractLayer [{ w := [], b := 0 }] = [{ a := [], b := 0 }]`；
2. `encode [{ a := [], b := 0 }] = [sym 0, sep]`（`encodeConstraint` 总以 `sep` 收尾）；
3. `recover [] = encode [] = []` ⟹ **两者像是 `[]` 与 `[sym 0, sep]`，并不相等**。

⚠ **故原见证是错的**，按 `PROCESS.md §3.3` 五步：**保留原设想 + 登记否证 + 改证其反面**。

### 4.2 为什么构造不出非单射反例（结构性论证）

| 部件 | 性质 | 依据 |
|:--|:--|:--|
| `extractVec : LinearLayer → VectorConstraint` | **双射** | `w↔a`, `b↔b` 纯字段重命名；逆为 `convertVec` |
| `extractLayer := List.map extractVec` | **单射** | 单射的 `map` 仍单射 |
| `encode : ConstraintSet → List SymToken` | **单射** | 既有 `RealTokenSymbolLink.encode_injective` |
| ⭐ **`recover = encode ∘ extractLayer`** | ⭐ **单射** | **单射的复合是单射** |

**根因**：`Layer := List LinearLayer` 与 `ConstraintSet := List VectorConstraint`
**逐字段同构** ⟹ `Layer` 的信息量**不超过** `ConstraintSet` ⟹ **这条边上没有信息损失**。 -/

/-- ⭐⭐ **`recover` 是单射** —— **与 `B400.5 P1-1` 的预期相反**。

由 `extractLayer`（`extractVec_injective` + `List.map`）单射、`encode` 单射
（`RealTokenSymbolLink.encode_injective`）、以及**单射复合仍单射**直接得到。

⚠ **这不是「缺口已闭合」的好消息**，而是「**缺口的形式与预期不同**」的发现：
不可逆性**不在** `L3→L1` 语法边，而在 `Layer→行为`（§五）。 -/
theorem recover_injective : Function.Injective (recover : Layer → List SymToken) := by
  intro ls₁ ls₂ h
  unfold recover at h
  -- encode 单射 ⟹ extractLayer ls₁ = extractLayer ls₂
  have h₁ : extractLayer ls₁ = extractLayer ls₂ := encode_injective h
  -- extractLayer = List.map extractVec，而 extractVec 单射 ⟹ 列表相等
  unfold extractLayer at h₁
  exact List.map_injective_iff.mpr (fun _ _ hc => extractVec_injective hc) h₁

/-! ## 五、⭐⭐ 真正的不可逆性在【行为层】：`Layer → (List Int → Int)` 非单射

§四 证明语法层 `recover` 无损。**但链路的用途是「行为」**，
而 `Layer` 到其行为的映射**必损**：

`LayerOut l x = dot l.w x + l.b`（`ConvertVectorLinear:141`）。

⭐ **零层**（`w = [], b = 0`）的输出恒为 `0`：
`dot [] x + 0 = 0`。故**任意多个**零层**行为相同**，而它们**是不同的 `Layer`**。

⇒ ⭐⭐ **这才是 `Layer` 侧真正的不可逆性。**
⚠ **它与 `B400.5 P1-1` 所担忧的「有损」【位置不同】**：
`P1-1` 把损失定位在 `L3→L1`（语法），本文件证明**损失在 `Layer→行为`**。
⇒ **两者不可互引**（本项目已登记过「三链不统一」的同类教训，见下）。 -/

/-- **零层存在且其输出恒为零**：`{ w := [], b := 0 }` 的行为是常函数 `0`。 -/
theorem zeroLayer_out (x : List Int) :
    LayerOut ({ w := [], b := 0 } : LinearLayer) x = 0 := by
  unfold LayerOut dot
  simp

/-- ⭐⭐ **`Layer` 到行为的映射非单射**（真正的不可逆性所在）。

**见证**：`[]`（空层）与 `[{ w := [], b := 0 }]`（含一个零层）是**不同**的 `Layer`，
但二者对**任何**输入 `x` 的**全部**神经元输出都为零
（空层：全称量词在空表上**空洞为真**；单零层：由 `zeroLayer_out`）。

⚠ **诚实标注（`PROCESS.md §2.2`）**：本条**不是** `recover` 的性质，
而是**它上层**（行为语义）的性质。登记它是为了**防止把两种不可逆性混为一谈**
—— 本项目已登记过「三链不统一到『商可逆』」的教训（`PROCESS.md §9`，依据 `B206/B209/B223`）。 -/
theorem layerOut_not_injective :
    ¬ Function.Injective (fun ls : Layer => fun x : List Int => ∀ l ∈ ls, LayerOut l x = 0) := by
  intro hinj
  -- 两个不同的层
  have hne : ([] : Layer) ≠ [{ w := [], b := 0 }] := by
    intro h
    have hlen := congrArg List.length h
    simp at hlen
  -- 但它们的行为函数相同
  have heq :
      (fun x : List Int => ∀ l ∈ ([] : Layer), LayerOut l x = 0)
        = (fun x : List Int => ∀ l ∈ [{ w := [], b := 0 }], LayerOut l x = 0) := by
    funext x
    apply propext
    constructor
    · intro _ l hl
      -- `l ∈ [{...}]` ⟹ `l = {w := [], b := 0}`
      have : l = ({ w := [], b := 0 } : LinearLayer) := by simpa using hl
      rw [this]
      exact zeroLayer_out x
    · intro h l hl
      -- `l ∈ []` 不可能：空表的成员命题为假，直接消解
      simp at hl
  exact hne (hinj heq)

/-- **`Beh` 的两层行为等价**（§五 的见证在谓词层的直接形态）：
`[]` 与 `[{w:=[], b:=0}]` 的逐点行为谓词**相等**。

⚠ 本条与 `RealRecoverBehavior.beh_nil_eq_beh_zero` 结论相同但**独立构造**
（本文件【不】import 该模块：两处都定 `Beh`，会**同名冲突**，
同 `extractLayer` 三处声明之情形 `RealRecoverEndpoint:6-10`）。 -/
theorem layerOut_beh_nil_eq_beh_zero :
    (fun x : List Int => ∀ l ∈ ([] : Layer), LayerOut l x = 0)
      = (fun x : List Int => ∀ l ∈ ([{ w := [], b := 0 }] : Layer), LayerOut l x = 0) := by
  funext x
  apply propext
  constructor
  · intro _ l hl
    have : l = ({ w := [], b := 0 } : LinearLayer) := by simpa using hl
    rw [this]
    exact zeroLayer_out x
  · intro _ l hl
    exact absurd hl (List.not_mem_nil l)

/-- **两个见证层【不同】**：`[]` 与 `[{w:=[], b:=0}]` 长度不同。 -/
theorem layerOut_nil_ne_zeroLayer : ([] : Layer) ≠ [{ w := [], b := 0 }] := by
  intro h
  have := congrArg List.length h
  simp at this

/-! ## 六、诚实边界与自我更正登记

### 6.1 ⭐ 本次自我更正（按 `PROCESS.md §3.3` 五步处置，不删除）

**原设想**（任务书与 `B400.5 P1-1` 均预期）：`recover` **非单射**，须给反例。

**逐层展开后的实测**：`recover = encode ∘ extractLayer`，
而 `extractVec` 在 `Layer` 上**单射**（§三）、`encode` **单射**（既有 `encode_injective`）
⟹ **复合单射**（§四 的 `recover_injective`）。

⇒ ⭐ **任务书的预期在当前载体下【不成立】**，已证其反面（`recover_injective`），
并**把真正的不可逆性定位到行为层**（§五，`layerOut_not_injective`）。

⚠ **这不降低交付价值**：`B400.5 P1-1` 的真实目的是**防止「1 行 recover + 无内容宣称」**。
本文件以**三类定理**（一条复合正确性 + 一条单射 + 一条行为层非单射）代替「1 行 + 反例」，
且**明确标注了不可逆性的真实位置**。**判据比原计划更强，不是更弱。**

### 6.2 本文件**不**声称的

- ❌ **不声称链路「可逆」**：恰好相反，§五证明行为层不可逆。
- ❌ **不声称 `recover` 是 `encode` 的左逆**：`recover` 的定义域是 `Layer`，
  `encode` 的定义域是 `ConstraintSet`，二者只通过 `compileToLayer` 的像相接（§二）。
- ❌ **不声称 `Layer → List SymToken` 是链路的「完整逆」**：
  ⚠⚠ **本条的【理由】在 B486 被推翻（两个分句都反了）—— 见下 §6.2.1。**

#### 6.2.1 ⭐⭐ 【B486 就地更正】原散文的两个分句**都反了**，真定理是它的**对偶**

**原散文（已作废，逐字保留）**：

> ❌ 不声称 `Layer → List SymToken` 是链路的「完整逆」：
> §五表明 `Layer` 的行为信息**多于**其语法表示，故任何纯语法逆都**不可能**恢复行为。

⭐ **"不声称"这一【态度】仍然成立；被推翻的是它给出的【理由】** —— 两个分句都反了：

| 原分句 | 定理化形态 | 实测 |
|:--|:--|:--|
| 「任何纯语法逆都**不可能**恢复行为」 | `¬ ∃ g : List SymToken → (List Int → Prop), ∀ ls, g (recover ls) = Beh ls` | ⭐⭐ **为假**（其否定可证：`∃` 成立） |
| 「行为信息**多于**语法表示」 | `∀ ls ls', recover ls = recover ls' → Beh ls = Beh ls'` | ⭐⭐ **为假，且【方向相反】**：真方向是 `Beh` 相等 **⇏** `recover` 相等 |

**根因**：§四 已证 `recover` 是**单射** ⟹ **左逆存在** ⟹ `recover` 的像
**完整携带** `Layer` 的全部信息（**含**行为）⟹ 「语法信息少于行为」不成立。

⭐⭐ **真定理是上述两个分句的【对偶】**，由本文件 §6.2.2 的三条定理机器钉死：

    recover 单射  ∧  Beh 非单射（§五）  ⟹  【语法严格细于行为】
    ⟹  行为不能决定语法：¬ ∃ g, ∀ ls, g (Beh ls) = recover ls

⚠ **原散文恰恰把蕴含方向写反了**：断裂在 **行为 → 语法**，**不在** 语法 → 行为。

⚠⚠ **本散文是 V02「E5 缺口」论证的根因陈述**（`V02-链尾六级的端到端耦合:171-176` 逐字引用了它）
⟹ 该报告的「E5 = `Behavior ↔ Recover` 耦合边不存在」**作为搜索事实仍成立**，
但其**根因解释**与《E5 缺口已按原设想闭合》类宣称**不成立**。
⚠ 机器凭据此前**不在本文件**，而在 `RealRecoverBehavior.lean`（W04 落地、B477 登记）。

#### 6.2.2 ⭐⭐ 就地钉死「语法严格细于行为」的三条定理（B486 新增）

§四/`RealRecoverBehavior` 已证 `recover` 单射、§五 已证 `Beh` 非单射。
**但「细于」此前从未被【当作陈述】写下来** —— 单射与非单射**各自**是对**单个映射自身**的陈述，
二者**不相加**即不出「严格细于」。下面三条把这一步补上（**独立构造**，不复用
`RealRecoverBehavior` 的 `badMap` 路线）。 -/

/-- **E5 行为谓词 `Beh`（本文件就地定义）**：把 `Layer` 映到它的**逐点行为谓词**
`Beh ls = fun x => AllZeroOutputs ls x`。

⚠ **本文件【不】import `RealRecoverBehavior`**（两处都定 `Beh` 会**同名冲突**，
同 `extractLayer` 三处声明之情形，见本文件 6-10 行）⟹ 就地重定义，
接口与 `RealRecoverBehavior.Beh` **逐字一致**。 -/
def Beh (ls : Layer) : List Int → Prop := fun x => AllZeroOutputs ls x

/-- **一般形态**：任一**单射**的 `f`，只要其定义域上存在**行为相同而自身不等**的一对元素
（即 `Beh` 非单射），则 `f` **不是** `Beh` 的完全（行为）不变量。

⭐ 本条是「细于」的**一般机制**：`f` 单射 ⟹ `f x = f y → x = y`；
而 `Beh x = Beh y` 而 `x ≠ y` ⟹ 反例。**无需 `f` 是 `recover`**（可复用于任意单射语法映射）。 -/
theorem injective_not_complete_behavioral_invariant
    {α : Type} (f : α → List SymToken) (B : α → (List Int → Prop))
    (hinj : Function.Injective f) (x y : α) (hBeh : B x = B y) (hne : x ≠ y) :
    ¬ (∀ a b : α, B a = B b → f a = f b) := by
  intro hc
  exact hne (hinj (hc x y hBeh))

/-- ⭐⭐ **真定理（对偶形态）**：**存在**一个**纯语法**函数 `f`，它在 `recover` 的像上
**逐字就是**一个**真左逆**（`∀ ls, f (recover ls) = ls`），
**却仍然不能**恢复行为（`f` 不是 `Beh` 的完全不变量）。

⭐ **这是对原散文【最强】的否定**：原分句一被反驳的方式不是「弱读法下有个 `g`」，
而是「**连真语法左逆都不够**」—— 语法层**不损失**任何信息，损失**全部**发生在
`Beh : Layer → 行为` 这一步（§五）。**"任何纯语法逆都不可能恢复行为"在此被正面构造推翻。** -/
theorem exists_leftinv_not_complete_behavioral_invariant :
    ∃ f : List SymToken → Layer,
      (∀ ls : Layer, f (recover ls) = ls) ∧
      ¬ (∀ ls ls' : Layer, Beh ls = Beh ls' → f (recover ls) = f (recover ls')) := by
  classical
  -- `recover` 单射（§四）⟹ 取它的一个段 `f`（像内取唯一原像，像外取 `[]`）
  let f : List SymToken → Layer := fun t =>
    if h : ∃ ls : Layer, recover ls = t then Classical.choose h else []
  have hf : ∀ ls : Layer, f (recover ls) = ls := by
    intro ls
    have hex : ∃ ls' : Layer, recover ls' = recover ls := ⟨ls, rfl⟩
    dsimp only [f]
    rw [dif_pos hex]
    exact recover_injective (Classical.choose_spec hex)
  refine ⟨f, hf, ?_⟩
  -- 反例：`[]` 与 `[{w:=[], b:=0}]` 行为相同（§五），但 `f` 是左逆 ⟹ 二者必须相等
  intro hc
  have h1 : f (recover ([] : Layer)) = f (recover ([{ w := [], b := 0 }] : Layer)) :=
    hc _ _ (layerOut_beh_nil_eq_beh_zero)
  rw [hf, hf] at h1
  exact layerOut_nil_ne_zeroLayer h1

/-- **独立形态（合取打包）**：`Beh` **非单射** 而 `recover` **单射** ⟹
**语法的等价类严格细于行为的等价类**。

⚠ 这是 §6.2.1 表中第二行的**直接机器凭据**，且**不复用** `RealRecoverBehavior.badMap`。 -/
theorem beh_coarser_than_recover :
    (¬ Function.Injective (Beh : Layer → (List Int → Prop)))
      ∧ Function.Injective (recover : Layer → List SymToken) :=
  ⟨layerOut_not_injective, recover_injective⟩

/-- **两条散文分句的字面对偶**（合取，供外部一键引用）：

    ¬ (∀ ls ls', Beh ls = Beh ls' ↔ recover ls = recover ls')   -- 分句二对偶
      ∧ ¬ (∃ g : (List Int → Prop) → List SymToken, ∀ ls, g (Beh ls) = recover ls)  -- 「行为→语法」不成立

⚠ 这里**没有**「不存在纯语法逆」那一半 —— 因为它是**假的**（见上 `exists_leftinv_…`）。 -/
theorem recover_endpoint_prose_duals :
    ¬ (∀ ls ls' : Layer, Beh ls = Beh ls' ↔ recover ls = recover ls')
      ∧ ¬ (∃ g : (List Int → Prop) → List SymToken, ∀ ls : Layer, g (Beh ls) = recover ls) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hr : recover ([] : Layer) = recover ([{ w := [], b := 0 }] : Layer) :=
      (h _ _).mp layerOut_beh_nil_eq_beh_zero
    exact layerOut_nil_ne_zeroLayer (recover_injective hr)
  · rintro ⟨g, hg⟩
    -- ⚠ `hg ls` 的左边是 `g (Beh ls)`，**不是** `g (recover ls)`；
    -- 故只能先用 `Beh` 相等把两个 `g` 项各自改写，不能直接 `rw` 掉 `hg`。
    have hbeh : Beh ([] : Layer) = Beh ([{ w := [], b := 0 }] : Layer) := by
      simpa only [Beh] using layerOut_beh_nil_eq_beh_zero
    have hr : recover ([] : Layer) = recover ([{ w := [], b := 0 }] : Layer) := by
      rw [← hg ([] : Layer), ← hg ([{ w := [], b := 0 }] : Layer), hbeh]
    exact layerOut_nil_ne_zeroLayer (recover_injective hr)

/-! ### 6.3 与既有登记的接口

| 既有登记 | 关系 |
|:--|:--|
| `CORRECTIONS B400.5 P1-1`（本文件直接回应） | ⚠ **其预期（非单射）被本文件否证**；建议按 §6.1 更新该条 |
| `RealCompileExtractClosed:204 closed_loop_adds_nothing` | 一致的**否定**方向：闭环不增内容 |
| `RealReversibilityBoundary:228 semantic_layer_not_injective` | ⭐ **同型**：本文件的 §五 是该结论在 `Layer` 侧的实例 |
| `PROCESS.md §2.2`（判「比定义多说了什么」） | §一 已逐字回答：**`recover` 的定义本身什么也没多说** |
-/

end Lattice
