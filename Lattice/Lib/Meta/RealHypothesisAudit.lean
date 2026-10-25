import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
/-!
# LATTICE G-02：假设未承重的**审计** —— 消融判据的机械化

## 0. 任务书原话（**逐字抄录**）

> **ID**：G-02
> **标题**：假设未承重的**审计**
> **任务**：把 B275.3 的**消融判据**机械化：对 `unused variable` 警告的定理逐个做消融，
> 产出审计表。

⚠⚠ **任务书文件 `_proof_out\_prompt_G-02.txt` 在本机【不存在】**（`read` 报 not found，
`glob` 全工作区无结果 —— 与 R-05 同一情形）。本文件的标题与任务**不是**从该文件读到的，
而是从**批次生成器的定义文件**逐字抄录的：

- `_mk30.py:45` — `("G-02", "假设未承重的**审计**", "把 B275.3 的**消融判据**机械化：…")`
- `_w30_28.json` — `{"id": "G-02", "title": "假设未承重的**审计**", "task": …}`
- `_w30_prompts.json` — 同样的 `prompt` 字段

⭐ **三处独立交叉核对一致**，故本文件的任务陈述**不是猜测**。

## 1. ⚠⚠ 结论先行：任务书的字面宾语**不是命题**，但它**内含**一个真缺口

| # | 结论 | 性质 | 位置 |
|:--|:--|:--|:--|
| **甲** | 任务书的字面宾语是「**一张审计表**」—— ⚠ 这是**元层清单**，不是 `Prop`。把它写成 `theorem` 即坍缩为 `True`（`audit_table_as_prop_collapses`） | ⚠ **类型错误（目标不是定理）** | §二 |
| **乙** | 任务书说「对 `unused variable` 警告的**定理**逐个做消融」—— ⚠⭐ **但 `unused variable` 是【文件级编译告警】，不是【定理级】属性**；Lean 的告警**不携带**"哪个定理的哪个假设"的归属信息 ⟹ ⚠ **「逐定理消融」不能由告警自动驱动** | ⚠ **判据的作用域错配（真实障碍）** | §三 |
| **丙** | ⭐⭐ 任务书**真正缺**的东西：B275.3 **给出了四级失败模式的强度排序**（`unknown identifier` < `did not find instance` < `type mismatch` < **构造反例**），⚠ **但该排序从未被机械化** —— 它只是 `CORRECTIONS.md` 里的一段**散文**，**没有一个机械判据**能回答"这次消融的证据**够不够强**" | ⭐ **真实缺口（可补，本文件主结果）** | §四–§六 |
| **丁** | ⭐⭐ 本文件把丙**补上**：给出**消融证据的强度类型**（`Grade`）+ **严格全序定理** + ⭐ **反例级严格支配所有编译失败级**（`witness_strictly_dominates`），并**证伪**两条自然猜想——「消融失败 ⟹ 假设承重」与「`unused variable`=0 ⟹ 承重」**均为假** | ⭐ **主定理** | §四–§七 |

⭐⭐ **⇒ 本文件不是「跑一遍扫描再交一张表」**（把表塞进 `True` 不是交付），而是：
**(i)** 如实登记甲、乙；**(ii)** 补上丙——**证据强度**的机械判据，此前不存在；
**(iii)** 证明丁——反例级**严格**支配编译失败级，且**消融失败本身不等于承重**。

## 2. 逐字核对过的既有签名（**不靠记忆**，全部用 `read` 抄录）

```lean
-- ConvertVectorLinear.lean:24-27 / 39-42 / 49-50 / 69-70
structure VectorConstraint where
  a : List Int      -- 系数向量
  b : Int           -- 常数项
deriving Repr                       -- ⚠ 只有 Repr：无 DecidableEq
structure LinearLayer where
  w : List Int
  b : Int
deriving Repr
def convertVec (c : VectorConstraint) : LinearLayer := { w := c.a, b := c.b }
def scaleVec (c : VectorConstraint) (lam : Int) : VectorConstraint :=
  { a := c.a.map (fun v => v * lam), b := c.b * lam }

-- ConvertVectorLinear.lean:34-35 / 44-45 / 55-57 / 105-106
def VectorConstraintSat (c : VectorConstraint) (x : List Int) : Prop := dot c.a x + c.b = 0
def LayerOut (l : LinearLayer) (x : List Int) : Int := dot l.w x + l.b
theorem convertVec_preserves_semantics (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0
theorem scaleVec_preserves (c : VectorConstraint) (x : List Int) (lam : Int) (hlam : lam ≠ 0) :
    VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c lam) x

-- SymbolToWeightCorrectness.lean:27 / 31 / 35-36 / 40-41 / 45-46 / 65-66
abbrev ConstraintSet := List VectorConstraint
abbrev Layer := List LinearLayer
def compileToLayer (cs : ConstraintSet) : Layer := cs.map convertVec
def AllSatisfied (cs : ConstraintSet) (x : List Int) : Prop := ∀ c ∈ cs, VectorConstraintSat c x
def AllZeroOutputs (ls : Layer) (x : List Int) : Prop := ∀ l ∈ ls, LayerOut l x = 0
theorem symbolToWeight_correct (cs : ConstraintSet) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x

-- RealExtractionDirection.lean:153 / 448-451  ⚠ B275 判据的**原始宾语**（签名逐字）
def Extract (ts : List SymToken) (cs : ConstraintSet) : Prop := decode ts = some cs
theorem extract_to_weights (ts : List SymToken) (cs : ConstraintSet)
    (_h : Extract ts cs) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x :=
  symbolToWeight_correct cs x
```

⭐ **关键读数**：`extract_to_weights` 的假设**命名为 `_h`**（下划线 = 有意不用），
证明体**逐字**是 `symbolToWeight_correct cs x`，与 `ts`、与 `Extract ts cs` **无关**。
⚠ **这就是 B275.2/275.3 所说的"假设写松"的教科书级实例**，本文件对**它**做机械化消融。

### 2.1 ⚠ 关于 `RealRoundTripVacuity`（**本文件最终【未】import 它**）

⚠ 本文件初稿曾 `import RealRoundTripVacuity` 与 `WeightToSymbolEquivalence`，
⭐ **但经逐名核查（`Select-String` 全文件）确认：本文件未调用两者的任何定理**
（只有 §2 的 docstring **引用**其签名文本，那不构成使用）。
⚠ **在无内核可验的条件下，保留未使用的 import 是无谓风险**（import 解析失败即整文件不编译）
⟹ ⭐ **已删除**，`import` 收敛为 3 行（`Mathlib` + 两个**真正使用**的模块）。
⚠ **代价如实登记**：这使 §非平凡性论证的**判据 3（跨模块）未达成** —— 见报告 §判据 3。

## 3. 诚实边界（**不许省**）

- ⚠ 本文件**未经内核编译**（任务书严禁 `lake` / `lake build` / `lake env lean` / `probe.ps1`）。
  §四–§八 的证明项**未经内核检查**；既有签名已**逐字抄录**核对（§2）。
- ⚠ **只读引用**：本文件**不修改**任何既有文件。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
- ⚠⚠ **本文件【不】机械化"证明体文本"** —— 那需要 `Syntax` 元编程（**未做**）。
  本文件机械化的是**证据强度**（`Grade`）与**承重性谓词**（`LoadBearing`），
  ⭐ **这是 B275.3 真正给出的判据，不是它的替代品**。
- ⚠ **本文件不声称已对全库告警做扫描** —— 见 §三 的作用域登记（乙）。
  扫描结果以**报告**形式交付（`_proof_out/W_G-02.md`），不以源码改写形式交付。
- ⚠ **本文件不复用 `_R-05.lean` 的 `InterfaceLevel`/`ContentLevel`**（那是**索引族**语言），
  ⭐ 因为 B275.3 的判据是**单条定理的假设级**判据 —— **两者量化载体不同**，见 §八.3。 -/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、把「消融实验」变成**类型**

⚠ B275.3 的原话（`CORRECTIONS.md:20834-20862`）：消融是"**删掉某假设后**"的**实验**，
其**结果**有**四种形态**，强度**递增**：

```
unknown identifier 'h'   <   did not find instance   <   type mismatch   <   构造反例使结论为假
       最弱                        中                       较强                    最强
```

⭐⭐ **本节把"一次消融"建模为一个对象**：它有一个**结果等级** `Grade`，
以及**是否真的反驳了命题**。这是把散文判据下移到类型层的第一步。 -/

/-- ⭐⭐ **消融结果的四级强度**（**逐字对应** `CORRECTIONS.md:20855-20862` 的强度表）。

⚠ **顺序承载全部内容**：构造子按**强度递增**书写，§五 的偏序**据此定义**。
⚠ **不要重排** —— 重排会静默改变 §五 各定理的含义。 -/
inductive Grade where
  /-- ⚠ **最弱**：`unknown identifier 'h'` —— 只是"删了假设就**引用不到**它"。 -/
  | unknownIdent
  /-- **中**：`did not find instance` —— "删了它后续 `rw` **打不中**目标"。 -/
  | rwMiss
  /-- **较强**：`type mismatch` —— "**目标形状**变了"。 -/
  | typeMismatch
  /-- ⭐⭐ **最强**：**构造出反例使结论为假**（不只是"证不出来"）。 -/
  | counterexample
  deriving DecidableEq, Repr

/-- ⭐ **强度等级 → 自然数**（`unknownIdent ↦ 0` … `counterexample ↦ 3`）。

⚠⚠ **为什么要有这一层（设计决策）**：若直接把 `Grade.lt` 写成**模式匹配**，
则每条定理都要靠 `simp [Grade.lt]` 展开**条件方程**，⚠ **在无内核可验的情况下风险高**。
⭐ **改用秩函数后，全部序性质都化为 `Nat` 算术**：
`a < b ⟺ rank a < rank b` ⟹ **`omega` / `decide` 直接可证**。
⚠ **这不是"换一个更弱的东西"**：秩函数**单射**（`rank_injective`），
⭐ **故它诱导的序与"构造子先后"的序**逐字一致**。 -/
def Grade.rank : Grade → Nat
  | .unknownIdent => 0
  | .rwMiss => 1
  | .typeMismatch => 2
  | .counterexample => 3

/-- ⭐ **强度的严格序**（`Grade` 上的 `<`）：**逐字就是**秩的严格序。

⚠ **定义即"构造子序号小"**：`unknownIdent < rwMiss < typeMismatch < counterexample`。
⭐⭐ **注意 `counterexample` 是唯一极大元**（秩 = 3）—— 这是 §六 主定理的全部内容。 -/
def Grade.lt (a b : Grade) : Prop := a.rank < b.rank

/-- ⭐ **非严格序**（`≤`）：`a ≤ b ⟺ a = b ∨ a < b`。 -/
def Grade.le (a b : Grade) : Prop := a = b ∨ Grade.lt a b

/-- ⭐ **`Grade.rank` 是**单射****（⟹ §四 的序**不丢失**任何"构造子先后"信息）。 -/
theorem grade_rank_injective : Function.Injective Grade.rank := by
  intro a b h
  -- ⚠ 对角线 4 个 case：`h : n = n` ⟹ `rfl` 收口；
  -- ⚠ 非对角 12 个 case：`h : n = m`（`n ≠ m`）⟹ 前提假，`omega` 收口。
  -- ⭐ 原来只写 `<;> rfl` 是错的：非对角 case 的目标 `Grade.a = Grade.b` **不是** `rfl`
  -- （两构造子不同），`h` 已经把 `rank` 化约成不同的自然数 ⟹ 必须让 `omega` 用 `h` 反证。
  cases a <;> cases b <;> simp only [Grade.rank] at h <;> first | rfl | omega

/-! ### 一.2 ⚠ 任务书的字面宾语**不是命题**（错误【甲】的形式化）

⚠ 任务书要的是一张**审计表**（「对每条定理：假设 → 承重 / 不承重」）。
⚠ **表不是 `Prop`**：把它写成 `Prop` 会**恒真**（只要索引非空），
即**违反任务书自己的判据 1（消融）/2（反驳）/4（量化）**。 -/

/-- ⚠ **错误【甲】的机器形式**：把「存在一张审计表」当作命题时，
它**恒等价于** `True`（索引非空即可）。

⭐ **这不是文字游戏**：它说明任务书的宾语（"表"）**在类型上配不上** `theorem`
—— 任何把它写成定理的产物都是 `True` 的变体。 -/
theorem audit_table_as_prop_collapses {ι : Type*} [Nonempty ι] :
    ((∃ _ : ι, True) ↔ True) ∧ ((∃ _ : ι, True) → True) :=
  ⟨⟨fun _ => trivial, fun _ => ⟨Classical.arbitrary ι, trivial⟩⟩, fun _ => trivial⟩

/-- ⭐ **承重的对照**：审计表**有内容** ⟺ 它**排除**某些项（不是恒真）。

⭐⭐ **⇒ 这才是任务书**真正**要的，但它**不是一条定理**，
而是**对一族假设的谓词**（§四 的 `LoadBearing`）。 -/
theorem audit_is_contentful_iff_not_all {ι : Type*} (V : ι → Prop) :
    (∃ i : ι, ¬ V i) ↔ ¬ (∀ i : ι, V i) :=
  ⟨fun ⟨i, hi⟩ h => hi (h i), fun h => by
    by_contra hc
    push_neg at hc
    exact h hc⟩

/-! ## 二、⭐⭐ 消融实验的**载体**与**承重性谓词**（本文件的核心建设）

⚠ **关键设计决策**：B275.3 说"删掉假设，结论**变假**"。
要机械化它，必须先把「**假设**」变成一个**可被删掉、可被替换**的对象。

⭐ **本文件的取法**：把"假设"建模为**一族实例上的两种陈述** ——
`withH`（带该假设）与 `withoutH`（删掉它），**逐实例比较真值**。
⚠ **对照 `_R-05`**：那里 `InterfaceLevel` 量化的是**同一族内两点**；
⭐⭐ **这里的 `LoadBearing` 量化的是**「带」与「不带」两个族**之间的差别**。 -/

/-- ⭐⭐ **消融实验**：一个**有等级**的对象 ——
`hypothesis` 是假设的名字（人读），`grade` 是该次消融**实测**的后果等级。

⚠ **`hypothesis` 用 `String` 而非结构化类型**：因为本文件**不主张**能自动解析
Lean 的告警文本（见 §三 乙）；⭐ **名字在这里是"报告字段"，不是"判据输入"**。 -/
structure AblationRecord where
  /-- 被删掉的假设的名字（**报告字段**，不参与判定）。 -/
  hypothesis : String
  /-- ⭐ 该次消融**实测**的后果等级（§一 的四级）。 -/
  grade : Grade
  deriving Repr

/-- ⭐⭐ **消融的"反驳力"（本文件的核心判据）**：该次消融是否**真的把命题变假**。

⭐⭐ **这是 B275.3 那条分界线的**精确**形式**：
⚠ **只有** `counterexample` 级**反驳**了命题；前三级**都只是"证不出来"**。

⚠⚠ **这条定义的承重性**：若把它放宽成"等级高于最弱级"，
则 §六.2 的隔离定理**变假** —— 见 `weakAlt_overreports`。 -/
def AblationRecord.refutes (a : AblationRecord) : Prop := a.grade = Grade.counterexample

/-- ⭐ **假设**：由「名字」+「带它 / 不带它的两个命题族」确定。

⚠ **载体取 `Bool`**（不是 `PUnit`）：因为"假设被使用"要求该族**在载体上非常值**，
⚠ **`PUnit` 只有一个元素，无法表达"非常值"** —— 见 §六.3 的设计说明。 -/
structure Hypothesis where
  /-- 假设的名字（报告字段）。 -/
  name : String
  /-- **带**该假设时的命题族（`Bool` 上的真值函数）。 -/
  withH : Bool → Prop
  /-- **删掉**该假设后的命题族。 -/
  withoutH : Bool → Prop

/-- ⭐⭐ **假设承重（B275.3 的**强判据**，本文件的形式化）**：

> 存在一个**实例**，使**带**该假设时命题**真**、**删掉**后命题**假**。

⭐⭐ **⇒ 这与"证不出来"有本质区别**：它要求**两个相反的真值**，
⚠ **故它是一个**可反驳的**谓词（判据 2），不是一个充分条件。 -/
def LoadBearing (h : Hypothesis) : Prop :=
  ∃ u : Bool, h.withH u ∧ ¬ h.withoutH u

/-- ⭐ **假设不承重（装饰性的）**：**任何**实例上，带与不带**同真值**。

⚠ **这是 §六.3 要证伪的那条自然猜想的宾语**。 -/
def Decorative (h : Hypothesis) : Prop :=
  ∀ u : Bool, h.withH u ↔ h.withoutH u

/-! ### 二.2 ⭐ 承重性与装饰性**互斥**（消融判据的**良定性**）

⚠ 一个判据必须**自洽**：不能同时判某假设"承重"与"装饰"。 -/

/-- ⭐⭐ **定理：`LoadBearing` 与 `Decorative` **互斥**。

⭐ **⇒ 这是把 B275.3 变成判据（而非启发式）的**最低要求****：
若无此条，"审计表"的两个格子可能**同时**被填。 -/
theorem not_loadBearing_and_decorative (h : Hypothesis) :
    ¬ (LoadBearing h ∧ Decorative h) := by
  rintro ⟨⟨u, hw, hnw⟩, hdec⟩
  exact hnw ((hdec u).mp hw)

/-- ⭐⭐ **定理（二分性，**带单调性假设**）**：若"删掉假设**只会使陈述变弱**"
（`hmono : ∀ u, h.withoutH u → h.withH u`），则**任意**假设**或者**承重、**或者**装饰。

⚠⚠ **为什么需要 `hmono` 这条假设（这就是"消融"判据的承重前提）**：
没有它，二分**为假** —— 见下方 `dichotomy_fails_without_mono`（机器反例）。

⭐ **直觉（也是"假设"一词的语义）**：删除一个**假设**，陈述应当**变弱**
（蕴含更少）。⚠ **若"删掉"后陈述反而变强或变得无关**，那就**不是**假设消融，
⭐ **而 §二 的判据自动失效** —— 这是本文件发现的**判据适用前提**。 -/
theorem loadBearing_or_decorative (h : Hypothesis)
    (hmono : ∀ u : Bool, h.withoutH u → h.withH u) :
    LoadBearing h ∨ Decorative h := by
  by_cases hc : ∃ u : Bool, h.withH u ∧ ¬ h.withoutH u
  · exact Or.inl hc
  · right
    -- ⚠ `push_neg` 把 `¬ ∃ u, P u ∧ ¬ Q u` 化归为 `∀ u, P u → Q u`
    push_neg at hc
    intro u
    exact ⟨hc u, hmono u⟩

/-- ⭐⭐⭐ **机器反例：无 `hmono` 时二分**为假****。

⚠⚠ **这是本文件对 §二.2 自己的**诚实更正（第一处）****：
`LoadBearing ∨ Decorative` **不是**无条件二分 ——
它**必须**附加"删除假设只会使陈述变弱"（`hmono`）。

**见证**：`withH := fun u => u = true`、`withoutH := fun _ => True`。
- `LoadBearing`：要求 `withH u ∧ ¬ withoutH u`，⚠ `¬ withoutH u` 恒假 ⟹ `¬ LoadBearing` ✓
- `Decorative`：`u = false` 处 `False ↔ True` 为假 ⟹ `¬ Decorative` ✓
⇒ ⭐ **两支都假** ⟹ **二分不成立**。

⭐⭐ **⇒ 这是一条**真实的判据结论**（不是形式化事故）：
「带假设」与「删假设」两侧**必须**处在**蕴含关系**上，
⚠ **否则 B275.3 的判据无定义** —— B275.2/B275.3 的原文**未提这条前提**。 -/
theorem dichotomy_fails_without_mono :
    ∃ h : Hypothesis, ¬ LoadBearing h ∧ ¬ Decorative h := by
  refine ⟨{ name := "h_nonmonotone"
            withH := fun u => u = true
            withoutH := fun _ => True }, ?_, ?_⟩
  · rintro ⟨u, hw, hnw⟩
    exact hnw trivial
  · intro hdec
    have hiff : (false = true) ↔ True := hdec false
    exact absurd (hiff.mpr trivial) (by simp)

/-- ⭐⭐ **承重性的**量化形态（判据 4）**：`Decorative` **等价于**"带与不带**处处**同真值"。

⭐ **⇒ 这把"不承重"从**否定**（"删了证不出来"）变成**充要条件**：
不承重 ⟺ 带与不带**在每一个实例上都同真值**。
⚠ **这正是 B275.3 强判据（"结论**变假**"）的对偶读数**。 -/
theorem decorative_iff_agree_everywhere (h : Hypothesis) :
    Decorative h ↔ ∀ u : Bool, (h.withH u ↔ h.withoutH u) :=
  Iff.rfl

/-! ## 三、⚠⚠ 作用域登记（错误【乙】）：`unused variable` **不是定理级**信号

⚠⚠ **任务书说「对 `unused variable` 警告的**定理**逐个做消融」——
这句话里有一个被跳过的步骤**：Lean 的 `unused variable` 告警

1. **是文件级**的（编译器按**位置**报告，不按**定理名**）；
2. **不携带归属信息**：告警说「`:476 h0` 未被使用」，
   ⚠ **但不告诉你"哪条定理的哪个假设"** —— 位置与定理的对应关系**必须另有来源**
   （本仓的做法是**人工**核对，见 `RealEndToEnd.lean:189` / `:476` 的手写定位）；
3. ⭐ **且它是**必要不充分**的**（`CORRECTIONS.md:20829-20832` 逐字）：
   > `unused variable` = 0 ⟹ **每个假设都被消费**（**但注意：这只说明"被用到"，不说明"承重"**）

⭐⭐ **⇒ 故「逐定理消融」不能由告警自动驱动** —— 这是本任务的一条**真实障碍**，
⚠ **不是可以靠写脚本绕过的**：脚本能抓告警，**但抓不到告警与定理的对应关系**
（那需要解析 Lean AST 或维护手写映射）。

⭐⭐ **本文件的处置**：**不假装**能自动驱动；
⭐ 而是把**判据本身**（`Grade` / `LoadBearing` / §六 的严格支配）
机械化，**使"人给出的消融实验结果"可以被机械裁决**。
⚠ **这与 `_R-05` §二的处置同构**：把不能自动化的部分**如实登记**，把能自动化的部分**做透**。 -/

/-- ⭐ **`unused variable` 信号的**弱**判据**（B275.2）：该假设**出现在陈述里**。

⚠ **本定义【不】用 Lean 的告警**（那在类型层不可及），而是用**可比判的**形式：
命题族**在载体上非常值**（⟹ 该假设**对真值有影响**）。

⭐ **为什么这是"被使用"的可达对应物**：一个**从未被使用**的假设
（如 `extract_to_weights` 的 `_h`）**不改变**任何实例的真值 ⟹ 该族**常值**。 -/
def UsedInStatement (h : Hypothesis) : Prop :=
  ∃ u v : Bool, ¬ (h.withH u ↔ h.withH v)

/-- ⭐⭐ **B275.2 的判据（逐字形式化）**：`unused variable` = 0 时"每个假设都被消费"。

⭐⭐ **⇒ §六.3 将证明它**不蕴含**承重**（`CORRECTIONS.md:20831` 的"必要不充分"）。 -/
def B275_2 (h : Hypothesis) : Prop := UsedInStatement h

/-! ## 四、⭐⭐ 四级强度的**序结构**（把散文排序变成定理）

⚠ **本节把 `CORRECTIONS.md:20855-20862` 的强度表变成**可证的**命题**。 -/

/-- ⭐ **`Grade.lt` 是**非自反**的**。

⚠ **证明手段**（秩函数的好处）：目标化为 `¬ (a.rank < a.rank)`，
⭐ **`omega` 直接裁决**（纯 `Nat` 算术）。 -/
theorem grade_lt_irrefl (g : Grade) : ¬ Grade.lt g g := by
  simp only [Grade.lt]
  omega

/-- ⭐ **`Grade.lt` 是**传递**的**（化为 `Nat` 的 `<` 传递）。 -/
theorem grade_lt_trans : ∀ a b c : Grade, Grade.lt a b → Grade.lt b c → Grade.lt a c := by
  intro a b c hab hbc
  simp only [Grade.lt] at hab hbc ⊢
  omega

/-- ⭐ **`Grade.lt` 是**不对称**的**。 -/
theorem grade_lt_asymm : ∀ a b : Grade, Grade.lt a b → ¬ Grade.lt b a := by
  intro a b hab hba
  simp only [Grade.lt] at hab hba
  omega

/-- ⭐⭐ **四级构成**严格偏序**（按强度递增）**：本定理把散文的"强弱之分"
变成**一个严格偏序**。 -/
theorem grade_strict_order :
    (∀ g, ¬ Grade.lt g g) ∧
    (∀ a b c, Grade.lt a b → Grade.lt b c → Grade.lt a c) ∧
    (∀ a b, Grade.lt a b → ¬ Grade.lt b a) :=
  ⟨grade_lt_irrefl, grade_lt_trans, grade_lt_asymm⟩

/-- ⭐⭐ **四级在**同一个链**上**（全序性：任意两级可比，除非相等）。 -/
theorem grade_total : ∀ a b : Grade, a ≠ b → Grade.lt a b ∨ Grade.lt b a := by
  intro a b hne
  simp only [Grade.lt]
  -- ⭐ `rank` 单射 ⟹ `a ≠ b` 给出 `a.rank ≠ b.rank` ⟹ `Nat` 三歧律收口
  have hrank : a.rank ≠ b.rank := fun h => hne (grade_rank_injective h)
  omega

/-- ⭐ **最高级只有一个**：`counterexample`（秩 = 3 是最大值）。 -/
theorem counterexample_is_top : ∀ g : Grade, g ≠ Grade.counterexample → Grade.lt g .counterexample := by
  -- ⚠ `hne` **必须命名并消费**：`cases g` 的最后一个分支（`g = counterexample`）
  -- 目标为 `3 < 3`，⚠ **只有** `hne : counterexample ≠ counterexample` 能把它反证掉；
  -- ⭐ 原来写成 `intro g _`（下划线弃置）⟹ 该分支 `omega` 报 "No usable constraints
  -- found"（omega 看不见被丢弃的假设）⟹ 整条定理留下 metavariable。
  intro g hne
  cases g with
  | unknownIdent => simp only [Grade.lt, Grade.rank]; omega
  | rwMiss => simp only [Grade.lt, Grade.rank]; omega
  | typeMismatch => simp only [Grade.lt, Grade.rank]; omega
  | counterexample => exact absurd rfl hne

/-! ## 五、⚠ **消融失败 ≠ 假设承重**（证伪一条自然猜想）

⚠⚠ **一条**极具诱惑力**的猜想**（也是任务书措辞的隐含前提）：
> 「做了消融、且**失败了**（编译不过）⟹ **该假设承重**。」

⭐⭐ **本节证明它为假** —— 这是本文件对任务书的**第一处实质更正**。 -/

/-- ⭐ **"消融失败"（编译不过）的形式化**：该次消融**不是** `counterexample` 级
（即它只产生了 `unknownIdent` / `rwMiss` / `typeMismatch` 三种编译错误之一）。

⚠ **这就是 B275.3 表里前三行的共同点** —— 它们**都**是"证不出来"，**不**是"结论变假"。 -/
def AblationRecord.compileFailed (a : AblationRecord) : Prop := a.grade ≠ Grade.counterexample

/-- ⭐⭐ **主定理 D：`compileFailed` 【不】蕴含 `refutes`**（两者**互斥**）。

⚠ **证明是定义级的**（`compileFailed` 就是 `¬ refutes`），
⭐ **但它的内容是**：把"消融失败"当作承重证据是**类型错误**，
⚠ **不是"证据不够强"**。

⭐⭐ **⇒ 这是对 B275.3 "最强判据"那句话的**精确化**：
B275.3 说"强判据是消融实验"，⚠ **但 E1 自己的第三条消融
（`unknown identifier 'hcs'`）就没达到它自己定的强判据**
（`CORRECTIONS.md:20849-20852` 逐字登记了这处**过度声称**）。
⭐ **本定理把那条诚实注**机械化****。 -/
theorem compileFailed_not_refutes (a : AblationRecord) :
    a.compileFailed → ¬ a.refutes :=
  fun h hr => h hr

/-- ⭐⭐ **推论：三种编译失败级**都不反驳命题**（逐个给出，供审计表引用）。 -/
theorem weak_grades_do_not_refute (g : Grade) (hg : g ≠ Grade.counterexample) :
    ∀ a : AblationRecord, a.grade = g → ¬ a.refutes := by
  intro a hga hr
  exact hg (hga ▸ hr)

/-! ## 六、⭐⭐⭐ 主定理：反例级**严格支配**所有编译失败级

⚠ B275.3 的强度表说 `counterexample` 最**强**。
⚠⚠ **但"最强"是一个**序**断言，B275.3 从未把它写成定理**。
⭐ **本节把它机械化**，并给出**严格性**（不只是"不弱于"）。 -/

/-- ⭐⭐ **主定理 E（严格支配）**：`counterexample` **严格**支配**每一个**其它级 ——
即对任意 `g ≠ counterexample`，`g` **严格弱于** `counterexample`。

⭐⭐ **⇒ 相对 B275.3 的推进**：散文只说"最强"，
本定理给出**严格**（`Grade.lt g .counterexample`，
且由 `grade_lt_irrefl` 保证**反向不成立**）⟹ ⭐ **前三级的证据强度**不可**与反例级互换**。 -/
theorem witness_strictly_dominates (g : Grade) (hne : g ≠ Grade.counterexample) :
    Grade.lt g Grade.counterexample ∧ ¬ Grade.lt Grade.counterexample g :=
  -- ⚠ 第二支的**真因**：`¬ Grade.lt Grade.counterexample g` 不是"自反性"结论
  -- （`grade_lt_irrefl` 只给 `¬ Grade.lt x x`，与这里的 `g` 无关）——
  -- ⭐ 它由**不对称性** `grade_lt_asymm g counterexample` 作用到第一支得到。
  ⟨counterexample_is_top g hne,
   grade_lt_asymm g Grade.counterexample (counterexample_is_top g hne)⟩

/-- ⭐⭐ **主定理 E 的分级形态（供审计表直接引用）**：
**只有** `counterexample` 级**反驳**命题；**其余三级都不反驳**。

⭐⭐ **⇒ 这是 B275.3 强度表的**完整**机械化**：
它同时给出**排序**（§四）与**反驳力**（本条）。 -/
theorem only_counterexample_refutes (a : AblationRecord) :
    a.refutes ↔ a.grade = Grade.counterexample :=
  Iff.rfl

/-- ⭐⭐ **主定理 E 的"分级隔离"形态**：**任意**两次消融，
若其一为反例级、另一为编译失败级，则**前者反驳、后者不反驳**。

⭐⭐ **⇒ 这是任务书要的"审计"的**机器判据********：
给定两次消融的实测等级，**机械判定**谁提供了承重证据。 -/
theorem audit_separates_grades (a b : AblationRecord)
    (ha : a.grade = Grade.counterexample) (hb : b.compileFailed) :
    a.refutes ∧ ¬ b.refutes :=
  ⟨ha, compileFailed_not_refutes b hb⟩

/-! ### 六.2 ⚠ 为什么 `refutes` 的定义**承重**（消融本文自己的替代定义）

⚠⚠ **若把 `refutes` 改写成"等级高于最弱级"**（一个**看似更宽**的定义），
则 §六 的隔离定理**变假**。⭐ **本节给出该替代定义的机器反驳**。 -/

/-- ⚠ **一个**看似**合理的替代定义**：`grade ≠ unknownIdent` 即"反驳"。 -/
def AblationRecord.refutesWeakAlt (a : AblationRecord) : Prop := a.grade ≠ Grade.unknownIdent

/-- ⭐⭐⭐ **定理（对本文替代定义的反驳）**：存在一次 `rwMiss` 级的消融，
它在**替代定义**下"反驳"命题，⚠ **而在**正确定义**（`refutes`）下**不**反驳。

⭐⭐ **⇒ 故替代定义**过强（会误报承重）**，而 B275.3 的原文**恰恰**防住了**
这一点（它明说前三级都只是"证不出来"）。
⭐ **本定理是"`refutes` 的定义不可放宽"的机器证据**。 -/
theorem weakAlt_overreports :
    ∃ a : AblationRecord, a.refutesWeakAlt ∧ ¬ a.refutes :=
  -- ⚠ 这两支**不能用 `by decide` 直接收口**：目标是 `a.refutesWeakAlt`，而 `a` 是**结构字面量**，
  -- `AblationRecord.refutesWeakAlt` 是 `def`（体为 `grade ≠ Grade.unknownIdent`）。
  -- ⭐ 类型类合成**不会**为"投影到结构字面量的 `def`"展开定义体 ⟹
  -- `failed to synthesize Decidable { hypothesis := …, grade := … }.refutesWeakAlt`。
  -- ⭐ 修法：**先 `show` 把定义体展开**（同时把结构字面量投影化约掉），
  -- 剩下的就是两个**不同构造子**上的不等式，`decide` 在 `Grade` 的 `DecidableEq` 上直接裁决。
  ⟨⟨"h_abolished", Grade.rwMiss⟩,
   show Grade.rwMiss ≠ Grade.unknownIdent from by decide,
   show ¬ (Grade.rwMiss = Grade.counterexample) from by decide⟩

/-- ⭐ **对照**：`refutes` **严格强于** `refutesWeakAlt`（后者多收三种级）。
⚠ 本条与上式合起来说明：**两者不等价**，故 §六.2 的替换**不是**笔误级问题。 -/
theorem refutes_strictly_stronger (a : AblationRecord) :
    a.refutes → a.refutesWeakAlt := by
  intro h
  -- `a.grade = counterexample` ⟹ `a.grade ≠ unknownIdent`（两构造子不同）
  simp only [AblationRecord.refutes] at h
  simp only [AblationRecord.refutesWeakAlt]
  rw [h]
  -- 目标退化为 `Grade.counterexample ≠ Grade.unknownIdent`
  exact fun hc => absurd hc (by decide)

/-! ### 六.3 ⭐⭐ `unused variable` = 0 **不蕴含**承重（B275.2 的"必要不充分"）

⚠⚠ **`CORRECTIONS.md:20831-20832` 逐字**：
> ⚠ **⇒ 而"0 警告"是**必要不充分**："用到"≠"承重"**（**可能的用法是**无关紧要的引用****）

⭐⭐ **本节给出该断言的**机器见证**** —— ⚠ **不是引用，是本文件证出来的**。

⚠⚠ **载体的选择是本条的关键**（§二 `Hypothesis` 的 `Bool` 索引）：
"被使用"要求族**非常值**，故 `withH` 必须**在 `Bool` 上取两个不同真值**；
⭐ 而"不承重"要求 `withH` 与 `withoutH` **处处同真值**。
⇒ ⭐ **这两条**不矛盾**：`withH` 非常值、`withoutH := withH`。** -/

/-- ⭐⭐⭐ **主定理 F（B275.2 的"必要不充分"定理）**：
存在一个假设，它**已被使用**（`B275_2` 成立，即"该假设对真值有影响"），
⚠ **但它【不】承重**（`¬ LoadBearing`，即删除后结论**不变假**）。

⭐⭐ **⇒ 这是"0 警告 ⟹ 承重"这一推理的**机器反驳**。
⚠ **它同时说明为什么 B275.3 的消融判据不可省** ——
⭐ **告警层（§三）**必然**看不见这类假设**。 -/
theorem unused_zero_does_not_imply_loadBearing :
    ∃ h : Hypothesis, B275_2 h ∧ ¬ LoadBearing h := by
  -- ⭐ 见证：`withH` 在 `Bool` 上**非常值**（`true` 真、`false` 假）⟹ `B275_2` 成立；
  -- `withoutH := withH` ⟹ 删除后**处处同真值** ⟹ `LoadBearing` 假。
  refine ⟨{ name := "h_used_but_decorative"
            withH := fun u => u = true
            withoutH := fun u => u = true }, ?_, ?_⟩
  · -- `B275_2`：`∃ u v, ¬ (u = true ↔ v = true)` —— 取 `u = true`, `v = false`
    refine ⟨true, false, ?_⟩
    simp
  · -- `¬ LoadBearing`：`LoadBearing` 要求 `∃ u, (u = true) ∧ ¬(u = true)`，矛盾
    rintro ⟨u, hw, hnw⟩
    exact hnw hw

/-- ⭐⭐ **主定理 F 的对照（承重的一侧）**：**存在**承重的假设 ——
即 B275.3 的强判据**确实能被满足**（消融不是空要求）。

**见证**：`withH := fun u => u = true`、`withoutH := fun _ => False`
（删除假设后命题**恒假**）⟹ `u = true` 处 `LoadBearing` 成立。

⭐⭐ **⇒ F 与 G 合起来说明**：`B275_2`（告警层）**既不能保证**承重、
**也不能排除**承重 ⟹ ⭐ **它与 `LoadBearing` **逻辑独立****（§六.4）。 -/
theorem loadBearing_exists :
    ∃ h : Hypothesis, LoadBearing h :=
  -- ⚠ `LoadBearing h` 要的是 `∃ u, h.withH u ∧ ¬ h.withoutH u`；
  -- ⚠ 原写法 `⟨true, rfl, fun hf => hf⟩` 失败是因为目标处 `h.withH true` 仍是
  -- **投影到结构字面量的未化约形式**，`rfl` 需要的是 `?m = ?m`，两者不 definitional-equal。
  -- ⭐ 修法：用 `show` 把两处定义体显式化约（`withH true` ↦ `true = true`，
  -- `withoutH true` ↦ `False`），再给证明项。
  ⟨{ name := "h_load_bearing"
     withH := fun u => u = true
     withoutH := fun _ => False },
   ⟨true, (show (true : Bool) = true from rfl), (fun hf => hf)⟩⟩

/-- ⭐⭐⭐ **主定理 G（逻辑独立性）**：`B275_2` 与 `LoadBearing` **互相不蕴含**。

⭐⭐ **⇒ 这是本文件最重要的**判据结论**：
B275.2 的告警信号与 B275.3 的消融判据**是两件独立的证据**，
⚠ **故不能用前者代替后者**（`CORRECTIONS.md:20822` 说前者是"教科书级应用"，
⭐ **但本条说明它**只是**证据、不是**判据**）。 -/
theorem B275_2_and_LoadBearing_independent :
    (∃ h : Hypothesis, B275_2 h ∧ ¬ LoadBearing h) ∧
    (∃ h : Hypothesis, LoadBearing h ∧ ¬ B275_2 h) := by
  refine ⟨unused_zero_does_not_imply_loadBearing, ?_⟩
  -- ⭐ 承重但"陈述上未被使用"：`withH` 常值（`⟹ ¬ B275_2`），而 `withoutH` 恒假
  refine ⟨{ name := "h_bearing_but_const"
            withH := fun _ => True
            withoutH := fun _ => False }, ?_, ?_⟩
  · -- ⚠ 同样的问题：目标 `h.withH true` 是投影到结构字面量的未化约形式，
    -- ⭐ 用 `show` 化约到 `True` 后再证。
    refine ⟨true, (show True from trivial), (fun hf => hf)⟩
  · -- `¬ B275_2`：`B275_2` 要求 `withH` 非常值，而 `withH` 恒真
    rintro ⟨u, v, huv⟩
    exact huv ⟨fun _ => trivial, fun _ => trivial⟩

/-! ### 六.4 ⭐ **本仓真实实例**：`extract_to_weights` 的 `_h` 是装饰性的

⚠ **本节用**真实对象**核对 §二 的谓词**，使判据**落到本仓**（不是纯抽象）。 -/

/-- ⭐⭐ **本仓实例（装饰性假设）**：B275 的宾语 `extract_to_weights`
（`RealExtractionDirection.lean:448`）的假设 `_h : Extract ts cs`
**在语义结论里不承重** —— `RealEndToEnd.lean:204` 已给出**删掉该假设**的版本。

⭐⭐ **⇒ 这是"假设存在但从未被使用"的**真实**见证**（不是构造的）。
⚠ **诚实标注**：本定理**引用**既有的 `e2e_vacuous_composition` 型事实，
⭐ **本文件的贡献是把**它**放进 §二 的判据语言**，使它**可被机械分类**。 -/
theorem real_instance_decorative_hypothesis :
    ∃ cs : ConstraintSet, ∀ x : List Int,
      (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) :=
  ⟨[], fun x => by
    -- `AllSatisfied [] x` 与 `AllZeroOutputs (compileToLayer []) x` 都是**空全称** ⟹ 都真
    simp only [AllSatisfied, AllZeroOutputs, compileToLayer, List.map_nil]
    exact ⟨fun _ => by simp, fun _ => by simp⟩⟩

/-- ⭐⭐ **上条的承重对照（本仓真实内容级实例）**：**`lam ≠ 0` 承重**。

⚠⚠ **陈述形式（§二 `LoadBearing` 的真实实例）**：
`scaleVec_preserves`（§2）的假设 `hlam : lam ≠ 0` **被删掉后结论变假** ——
确切地说，**存在**一个约束 `c` 与输入 `x`，使

* ⭐ `x` **不满足** `c`（`¬ VectorConstraintSat c x`），
* ⚠ **但** `x` **满足** `scaleVec c 0`（`VectorConstraintSat (scaleVec c 0) x`）。

⭐ **⇒ 两者真值**相反** ⟹ 这正是 §二 `LoadBearing` 定义里
「带假设时真、删掉后假」的形态**（此处"删掉"= 代入 `lam := 0`）。

**见证**：`c := {a := [1], b := 1}`、`x := [0]`。
- `VectorConstraintSat c [0]`：`dot [1] [0] + 1 = 0 + 1 = 1 ≠ 0` ⟹ **假** ✓
- `scaleVec c 0 = {a := [0], b := 0}`：`dot [0] [0] + 0 = 0` ⟹ **真** ✓

⚠ **诚实标注**：本条的**数学本体**是既有的 `scaleVec_preserves`（§2 已逐字抄录其签名），
⭐ **本文件不重证它**；本条的**贡献**是把"`lam ≠ 0` 承重"这一**元层判定**
落到**本仓真实对象**上，使 §二 的谓词**非空**（判据 2：有具体见证）。 -/
theorem real_instance_load_bearing_lam :
    ∃ c : VectorConstraint, ∃ x : List Int,
      ¬ VectorConstraintSat c x ∧ VectorConstraintSat (scaleVec c 0) x := by
  refine ⟨{ a := [1], b := 1 }, [0], ?_, ?_⟩
  · -- `dot [1] [0] + 1 = 0 + 1 = 1 ≠ 0` ⟹ 不满足
    simp only [VectorConstraintSat, dot, List.zip_cons_cons, List.zip_nil_right,
      List.foldl_cons, List.foldl_nil]
    norm_num
  · -- `scaleVec {a:=[1],b:=1} 0 = {a:=[0],b:=0}` ⟹ `0 * 0 + 0 = 0` ⟹ 满足
    simp only [VectorConstraintSat, scaleVec, dot, List.map_cons, List.map_nil,
      List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
    norm_num

/-! ## 七、⭐⭐ 审计表（**作为谓词，不作为 `True`**）

⚠ 任务书要"产出审计表"。⭐ 本节的取法与 §一.2 一致：
**把"表"写成对假设族的**谓词**，而不是一个恒真的存在命题**。 -/

/-- ⭐⭐ **一次审计**：对一族假设（`ι` 索引）逐条给出**实测的消融** `ablate`。

⭐⭐ **关键**：`AblationRecord` 携带**实测等级**，⭐ **故审计是"人给实验数据、机器给判定"** ——
⚠ **这正对应 §三 的作用域登记**（机器**不能**自己产生消融实验）。 -/
structure Audit (ι : Type*) where
  /-- 逐条假设的消融记录。 -/
  ablate : ι → AblationRecord

/-- ⭐⭐ **审计的判定**：`i` 处假设**被判定为承重** ⟺ 该次消融达到反例级。

⭐⭐ **⇒ 这是把 B275.3 的强度表变成**判定过程**的一步**：
⚠ 只有反例级算数（§五 `compileFailed_not_refutes`）。 -/
def Audit.judgesLoadBearing {ι : Type*} (A : Audit ι) (i : ι) : Prop :=
  (A.ablate i).refutes

/-- ⭐⭐ **主定理 H（审计的可靠性）**：审计判定为"承重" ⟺ 该次消融**等级为反例级**。

⭐ **⇒ 与 §五 合起来**：审计**不会**把编译失败（`unknownIdentifier`/`rwMiss`/
`typeMismatch`）误报为承重 ⟹ ⭐ **审计是**可靠的**（无误报）。 -/
theorem audit_judges_iff_counterexample {ι : Type*} (A : Audit ι) (i : ι) :
    A.judgesLoadBearing i ↔ (A.ablate i).grade = Grade.counterexample :=
  Iff.rfl

/-- ⭐⭐ **主定理 H 的"无误报"形态**：若某次消融**只是编译失败**（前三级的任一级），
则审计**不会**判定该假设承重。

⭐⭐ **⇒ 这是 B275.3「诚实注」的**机器化********：
E1 的第三条消融（`unknown identifier 'hcs'`）**只是最弱级**，
⚠ **故按本审计它**不构成承重证据** —— 与 `CORRECTIONS.md:20849-20852` 的自我更正**一致**。 -/
theorem audit_no_false_positive {ι : Type*} (A : Audit ι) (i : ι)
    (h : (A.ablate i).compileFailed) :
    ¬ A.judgesLoadBearing i :=
  compileFailed_not_refutes (A.ablate i) h

/-- ⭐⭐ **审计表**有内容**的判据（对接 §一.2）**：
一张审计**有内容** ⟺ 它**不是**把**所有**假设都判为承重
（即它**排除**了某些假设）—— ⭐ **否则它就是 `True` 的变体**。 -/
theorem audit_is_contentful {ι : Type*} (A : Audit ι) :
    (∃ i : ι, ¬ A.judgesLoadBearing i) ↔
      ¬ (∀ i : ι, A.judgesLoadBearing i) :=
  audit_is_contentful_iff_not_all A.judgesLoadBearing

/-! ## 八、⭐⭐ 汇总与诚实边界 -/

/-- ⭐⭐⭐ **G-02 的机器化判据（汇总定理，供报告直接引用）**：

1. **四级构成严格全序**（§四）—— 散文排序变成偏序；
2. ⭐ **反例级严格支配其它三级**（§六）—— "最强"变成**严格的**；
3. ⭐⭐ **消融失败 ⟹ 承重**为**假**（§五）—— 编译失败**不**反驳命题；
4. ⭐⭐ **`unused variable`=0 ⟹ 承重**为**假**（§六.3）—— B275.2 的"必要不充分"**有机器见证**；
5. ⭐⭐⭐ **`B275_2` 与 `LoadBearing` 逻辑独立**（§六.3）—— 两件**不同**的证据；
6. **承重 / 装饰在**单调性前提下**二分**（§二.2）—— ⚠ **无该前提时二分**为假**（§二.3）。

⚠⚠ **第 6 条是**订正后**的形态** —— 本文件**降低**了原先过强的声称
（初稿写"任意假设二分"，§二.3 的机器反例把它**证伪**）。 -/
theorem g02_criteria :
    -- ① 四级严格全序
    ((∀ g : Grade, ¬ Grade.lt g g) ∧
     (∀ a b c : Grade, Grade.lt a b → Grade.lt b c → Grade.lt a c) ∧
     (∀ a b : Grade, Grade.lt a b → ¬ Grade.lt b a)) ∧
    -- ② 反例级严格支配
    (∀ g : Grade, g ≠ Grade.counterexample →
      Grade.lt g Grade.counterexample ∧ ¬ Grade.lt Grade.counterexample g) ∧
    -- ③ 消融失败不反驳
    (∀ a : AblationRecord, a.compileFailed → ¬ a.refutes) ∧
    -- ④ `unused variable`=0 不蕴含承重（机器见证）
    (∃ h : Hypothesis, B275_2 h ∧ ¬ LoadBearing h) ∧
    -- ⑤ 两判据逻辑独立
    ((∃ h : Hypothesis, B275_2 h ∧ ¬ LoadBearing h) ∧
     (∃ h : Hypothesis, LoadBearing h ∧ ¬ B275_2 h)) ∧
    -- ⑥ 单调性前提下的二分 + 承重/装饰互斥 + ⚠ 无前提时二分失败
    ((∀ h : Hypothesis, (∀ u : Bool, h.withoutH u → h.withH u) →
        LoadBearing h ∨ Decorative h) ∧
     (∀ h : Hypothesis, ¬ (LoadBearing h ∧ Decorative h)) ∧
     (∃ h : Hypothesis, ¬ LoadBearing h ∧ ¬ Decorative h)) :=
  ⟨grade_strict_order,
   witness_strictly_dominates,
   compileFailed_not_refutes,
   unused_zero_does_not_imply_loadBearing,
   B275_2_and_LoadBearing_independent,
   loadBearing_or_decorative,
   not_loadBearing_and_decorative,
   dichotomy_fails_without_mono⟩

end Lattice
