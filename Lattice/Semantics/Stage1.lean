/-
# 语义信息主线 · 阶段 1：语义域、词表、几何与继承

## 0. 这一节补什么

`SEMANTICS-MAINLINE.md` 把「语义信息」拆成三个可形式化的命题（§2.1–2.4），
并给出目标骨架（§3）。**此前库里一个声明都没有**——`SemanticDomain`、`Vocab`、
`Geometry`、`Inherits` 全部不存在。

本节把 §3 的骨架**落成 Lean**，并在 `ConstraintSet` 上给出**第一个实例**
（阶段 1 第 1–3 条）。

## 1. 三个设计决策，每个都有理由

### 1.1 `Meaning` 取「配置上的谓词」，不取字符串

```lean
Meaning := (ℕ → Pt n) → Prop
```

**为什么不取 `String`**：字符串的相等无法给出有内容的定理（`"x" = "x"` 是重言）。
取谓词之后，`equiv` 可以是**外延等价**，而那正是「两个约束集意思相同」的准确定义——
`HoldsSet` 逐配置相同。

### 1.2 `equiv` 必须是**结构字段**，不能是 `Prop` 假设

`SEMANTICS-MAINLINE.md` §3 说得很直接：`sound`/`commutes` 是**字段**，必须由实例填充。
`equiv` 同样——它是语义域的一部分，不是外部加的条件。

**但 `equiv` 必须自带 `refl`**：没有自反性的「等价」不能用在编辑的 `reversible`/`idempotent`
里。初稿漏了这一点，`refl` 是后加的。

### 1.3 `Inherits` 的两个字段：`sound` 与 `complete`，**强度不同**

| 字段 | 内容 | 可证性 |
|:--|:--|:--|
| `sound` | `label (embed w x) = behavior w x` | **常常可证**：它是「几何的标注对准模型的行为」 |
| `complete` | `∀ m, ∃ w x, label (embed w x) = m` | **常常不可证**：它要求几何**覆盖整个语义域** |

**`complete` 不能当成和 `sound` 一样的东西。** 阶段 1 里 `Meaning` 是谓词，
而「每个谓词都被某个载体标注」通常为假——所以本节把 `complete` **限制到一个显式子域 `D`**
（`Semantics-MAINLINE.md` §6 的 S2 就是这个意思：`complete_on D`）。

## 2. 交付

| 声明 | 内容 | 对应 §6 义务 |
|:--|:--|:--|
| `SemanticDomain` | `Meaning` + `equiv` + `refl` | S0 |
| `constraintDomain` | **`ConstraintSet` 上的语义域** | S0 实例 |
| `holdsSetMeaning` | 约束集作为 `Meaning` | — |
| `holdsSet_meaning_equiv` | 两个约束集 `equiv` ⟺ 逐配置同真 | S1 的基础 |
| `Vocab` | `Token` + `denote` | S1 |
| `Vocabulary` | **约束词表的实例**：token 就是约束 | S1 实例 |
| `Geometry` | `Carrier` + `label` | S3 |
| `constraintGeometry` | **约束几何的实例** | S3 实例 |
| `Inherits` | `embed` + `sound` + `completeOn` | S4/S5 |
| `inherits_sound` | `label ∘ embed = behavior` 的展开 | S3 |
| `complete_on` | **相对 `D` 的完备性** | S2 |

## 3. 边界（四条）

- **阶段 1 只做约束几何。** 程序语义（阶段 2）与隐空间（阶段 3）不在本节。
- **`complete` 是相对 `D` 的**，不是全局的。全局完备性对谓词语义域一般**为假**
  （存在谓词不是任何约束集）。**把它写成 `completeOn D` 是把它变成可证的形状，不是弱化。**
- **`Vocab.denote` 是约定，不是从权重学出来的**——`SEMANTICS-MAINLINE.md` §2.1 明说。
  本节不声称「模型按这个指称使用 token」；那是行为语义，属阶段 2。
- **本节不含 `Model`/`Annotation`/`Edit`/`MergeRecord`**（S6–S11）。
  它们是下一节的内容，**不在本文件里假装有**。
-/
import Mathlib
import Lattice.Domains.Constraints.ConstraintSet
import Lattice.Domains.Constraints.Constraint

namespace Lattice.Semantics.Stage1

open Lattice.Geo Lattice.Geo.ConstraintSet

/-! ## 一、语义域 -/

/-- **语义域**：先选定一个可形式化的 `D`。

`Meaning` 是「意思」的类型，`equiv` 是「意思相同」的口径。
**`refl` 是字段而不是定理**：没有自反性的等价不能用在编辑的 `reversible`/`idempotent` 里，
所以它必须由语义域的提供者负责。 -/
structure SemanticDomain where
  /-- 「意思」的类型。 -/
  Meaning : Type
  /-- 「两个意思相同」。 -/
  equiv : Meaning → Meaning → Prop
  /-- 该口径自反。 -/
  refl : ∀ m, equiv m m

namespace SemanticDomain

/-- `equiv` 的传递性**不是**自动的（`refl` 只给自反），所以单独要求。 -/
def Transitive (D : SemanticDomain) : Prop :=
  ∀ a b c, D.equiv a b → D.equiv b c → D.equiv a c

/-- `equiv` 的对称性。 -/
def Symmetric (D : SemanticDomain) : Prop :=
  ∀ a b, D.equiv a b → D.equiv b a

end SemanticDomain

/-- **阶段 1 的语义域：固定维数上的约束集**。

`Meaning := (ℕ → Pt n) → Prop`——一个意思就是「哪些配置被接受」。
`equiv` 是**外延等价**：逐配置同真。

**这就是「两个约束集意思相同」的准确定义**，而且它让 `HoldsSet` 天然尊重这个口径
（`holdsSet_meaning_equiv` 是 `Iff.rfl`，因为口径就是按 `HoldsSet` 的形状选的）。 -/
def constraintDomain (n : ℕ) : SemanticDomain where
  Meaning := (ℕ → Pt n) → Prop
  equiv := fun P Q => ∀ pts, P pts ↔ Q pts
  refl := fun _ _ => Iff.rfl

/-- `constraintDomain` 的 `equiv` **是对称的**（外延等价天然对称）。 -/
theorem constraintDomain_symmetric (n : ℕ) : (constraintDomain n).Symmetric :=
  fun _ _ h pts => (h pts).symm

/-- `constraintDomain` 的 `equiv` **是传递的**。 -/
theorem constraintDomain_transitive (n : ℕ) : (constraintDomain n).Transitive :=
  fun _ _ _ hab hbc pts => (hab pts).trans (hbc pts)

/-- **约束集作为一个 `Meaning`**。 -/
def holdsSetMeaning {n : ℕ} (cs : List (GeoConstraint n)) : (constraintDomain n).Meaning :=
  fun pts => HoldsSet cs pts

/-- **两个约束集等价，当且仅当它们逐配置同真。**

这是 `Iff.rfl`——**因为口径就是照着 `HoldsSet` 的形状选的**。
**这不是重言，这是设计**：外延语义的定义就是「在哪真」。
如果口径取别的（例如语法相等），这条就不成立，那才是问题。 -/
theorem holdsSet_meaning_equiv {n : ℕ} (cs ds : List (GeoConstraint n)) :
    (constraintDomain n).equiv (holdsSetMeaning cs) (holdsSetMeaning ds) ↔
      ∀ pts, HoldsSet cs pts ↔ HoldsSet ds pts :=
  Iff.rfl

/-- **约束集的等价被拼接保持**：若 `cs ≡ cs'`，则 `cs ++ ds ≡ cs' ++ ds`。 -/
theorem holdsSet_equiv_append_left {n : ℕ} (cs cs' ds : List (GeoConstraint n))
    (h : (constraintDomain n).equiv (holdsSetMeaning cs) (holdsSetMeaning cs')) :
    (constraintDomain n).equiv (holdsSetMeaning (cs ++ ds)) (holdsSetMeaning (cs' ++ ds)) := by
  intro pts
  unfold holdsSetMeaning
  rw [holdsSet_append, holdsSet_append]
  exact and_congr_left' (h pts)

/-! ## 二、词表 -/

/-- **词表**：token 到语义的**约定**。

`denote` 不是从权重学出来的——它是人定的符号接口（`SEMANTICS-MAINLINE.md` §2.1）。
**本节不声称模型按这个指称使用 token**；那是行为语义，需要另证。 -/
structure Vocab (D : SemanticDomain) where
  /-- 词表里的 token 类型。 -/
  Token : Type
  /-- `token ↦ 它的意思`。 -/
  denote : Token → D.Meaning

/-- **阶段 1 的约束词表**：token 就是约束本身，`denote` 把它映射到「哪些配置满足它」。

**这是一个诚实的实例，不是最有用的那个**：真实词表的 token 是字符串，
`denote` 是人标的。但在约束几何这个域里，「token = 约束」让
`denote` 有无内容的定义，从而后面的继承定理可以真的证。 -/
def constraintVocab (n : ℕ) : Vocab (constraintDomain n) where
  Token := GeoConstraint n
  denote := fun c pts => GeoConstraint.Holds c pts

/-- **`vocab_denote_sound`（S1 的阶段 1 形式）**：词表指称与 `Holds` 一致。

对约束词表，这是 `Iff.rfl`；**意义在于它给出 S1 在该域上的确切形式**，
而不是一句「指称与行为一致」的散文。 -/
theorem constraintVocab_denote_sound {n : ℕ} (c : (constraintVocab n).Token)
    (pts : ℕ → Pt n) :
    (constraintVocab n).denote c pts ↔ GeoConstraint.Holds c pts :=
  Iff.rfl

/-! ## 三、几何与继承 -/

/-- **几何**：载体 + 标注。

`label` 把载体上的点映射到语义。**载体是什么由实例决定**：
阶段 1 里它是配置空间，阶段 3 里它会是隐空间。 -/
structure Geometry (D : SemanticDomain) where
  /-- 几何的载体。 -/
  Carrier : Type
  /-- `载体上的点 ↦ 它的意思`。 -/
  label : Carrier → D.Meaning

/-- **阶段 1 的约束几何**：载体是**约束集**，标注是该约束集的含义。

初稿把载体取成配置（`ℕ → Pt n`），于是 `label : 配置 → 意思` 只能是
`fun pts => fun cs => HoldsSet cs pts`——**`pts` 出现的位置与 `Meaning` 的形状不符**，
类型检查拒绝。

**取载体为约束集才是对的**：把载体当成配置是想要「几何点标注了什么」，
但 `Meaning` 是「哪些配置被接受」，所以载体侧的对象必须是**接受者**而不是被接受者。
**这不是为了通过类型检查而改，是把「几何点是什么」想清楚了。** -/
def constraintGeometry (n : ℕ) : Geometry (constraintDomain n) where
  Carrier := List (GeoConstraint n)
  label := holdsSetMeaning

/-- **继承**：几何标注与模型行为一致。

- `sound`：**几何的标注对准模型的行为**——这是继承的实质；
- `completeOn D`：几何在子域 `D` 上**覆盖**语义。

**两者强度不同**：`sound` 常常可证，`complete` 对谓词语义域一般**为假**
（不是每个谓词都是某个约束集的含义）。所以 `complete` 带一个显式 `D`。 -/
structure Inherits (D : SemanticDomain) (G : Geometry D) (M : Type) where
  /-- 权重侧的载体。 -/
  Weights : Type
  /-- 从权重到几何载体的嵌入。 -/
  embed : Weights → G.Carrier
  /-- 模型行为：权重 + token 序列 → 意思。 -/
  behavior : Weights → List M → D.Meaning
  /-- **继承的实质**：几何的标注等于模型的行为。 -/
  sound : ∀ (w : Weights) (toks : List M), G.label (embed w) = behavior w toks
  /-- **完备性的子域**：几何在这些意思上覆盖。 -/
  Domain : D.Meaning → Prop
  /-- 对 `Domain` 里的每个意思，都有载体点标注它。 -/
  completeOn : ∀ m, Domain m → ∃ x : G.Carrier, G.label x = m

/-- **`geometry_inherits`（S3）**：`sound` 字段的展开形式。

`label ∘ embed = behavior`，逐点写出。**这是继承的定义被使用时的样子**，
不是一条需要另证的东西——**S3 的内容在 `Inherits` 结构的 `sound` 字段里，
而填充那个字段才是每个实例要做的事**。 -/
theorem inherits_sound {D : SemanticDomain} {G : Geometry D} {M : Type}
    (I : Inherits D G M) (w : I.Weights) (toks : List M) :
    G.label (I.embed w) = I.behavior w toks :=
  I.sound w toks

/-- **`complete_on D`（S2）**：完备性只在声明的子域上成立。 -/
theorem complete_on {D : SemanticDomain} {G : Geometry D} {M : Type}
    (I : Inherits D G M) (m : D.Meaning) (hm : I.Domain m) :
    ∃ x : G.Carrier, G.label x = m :=
  I.completeOn m hm

/-- **继承的 `sound` 让「几何标注」与「模型行为」不可区分**：
若两个权重在几何里嵌入到同一点，它们的行为相同。 -/
theorem inherits_behavior_ext {D : SemanticDomain} {G : Geometry D} {M : Type}
    (I : Inherits D G M) (w₁ w₂ : I.Weights)
    (h : I.embed w₁ = I.embed w₂) (toks : List M) :
    I.behavior w₁ toks = I.behavior w₂ toks := by
  rw [← I.sound w₁ toks, ← I.sound w₂ toks, h]

end Lattice.Semantics.Stage1
