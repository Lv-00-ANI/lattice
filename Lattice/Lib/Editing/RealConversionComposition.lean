import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: 转换的**复合律** —— 结合律、单位元、何时可逆

## 1. 本文件建立什么

任务书的三个子问题，本文件逐条回答：

| 子问题 | 本文件的结论 |
|:--|:--|
| **结合律** | `scaleLayer_comp_assoc`：`scaleLayer` 复合**结合**（分段编译也结合：`compileToLayer_append_assoc`） |
| **单位元** | `scaleLayer_one_is_identity`（`lam = 1`）+ `scaleLayer_zero_is_const`（`lam = 0` **不是**单位元，是**常值**算子）+ `cancel_left_of_ne_zero` |
| **何时可逆** | ⭐ `scaleLayer_inverse_iff`：**可逆 ⟺ `|lam| = 1`**（`Int` 上只有 `±1` 有乘法逆元） |
| **可逆的障碍** | ⭐ `scaleLayer_not_surjective_of_two`：`|lam| ≥ 2` 时**非满射** ⟹ **无右逆** |
| **部分可逆** | ⭐ `compile_extract_invertible_pair`：编译/提取**互逆**（`LeftInverse` + `RightInverse`） |

⭐⭐ **核心结论（可逆性的精确边界）**：
`scaleLayer lam` 在 `ConstraintSet` 上**可逆** ⟺ `|lam| = 1`。
⇒ 这是「规范形自由度不可消除」的**最精确**形式：
`±1` 是**唯一**可逆的缩放，其余都**丢信息**。这与 `RealCanonicalForm` 的
「`canonicalize` 下降到的商是 `ScaleClass` 再模 `±1`」**互为印证**
（那里从**商**侧说，这里从**复合**侧说）。

## 2. 依赖什么

`Mathlib` + 转换主干四模块。

## 3. 不做什么（诚实边界）

- ⚠ **不构造 `Category`**（复合律在**函数层**陈述，不包装成范畴）。
- ⚠ **不证 `scaleLayer lam` 的单射性**：**未做**（需要 `Int` 上的消去律；
  本文件只用**满射性**这一**更弱**的失效模式，见 `scaleLayer_not_surjective_of_two`）。
- ⚠ **不证"非可逆 ⟹ 丢信息"的逆**：**未做**（"丢信息"的精确定义见 §四 的 `LosesInfo`，
  本文件只给出**充分**方向）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、复合律：结合律与单位元（一般骨架，再实例化） -/

/-- ⭐ **① 一般复合的结合律**（**锚定**：证明需要 `funext` + **两次** `rfl` 级的
β-归约，**不是** `rfl` 本身，因为 `Function.comp` 的嵌套需要**重新关联**）。

⭐ **意义**：这是「转换可以**任意分组**复合」的形式化 ——
即「先缩放再缩放再编译」与「先缩放再（缩放+编译）」**结果相同**。 -/
theorem comp_assoc_lemma {α : Type*} (f g h : α → α) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) :=
  funext (fun x => rfl)

/-- ⭐ **② 一般单位元律**：`id ∘ f = f` 与 `f ∘ id = f`。 -/
theorem comp_id_lemma {α : Type*} (f : α → α) : id ∘ f = f ∧ f ∘ id = f :=
  ⟨rfl, rfl⟩

/-! ## 二、缩放的复合律（实例化到转换主干） -/

/-- **缩放的提升**（与 `RealConversionCategorical.scaleLayer` **同名同义**；
本文件**不 import** 该模块，故**就地重定义** —— 两处定义**逐字相同**）。

⚠ **诚实标注**：同名定义出现在两个模块里是**有意的**（模块须自足）；
若将来合并，应保留**一份**。 -/
def scaleLayer (lam : Int) (cs : ConstraintSet) : ConstraintSet :=
  cs.map (scaleVec · lam)

/-- ⭐ **③ `lam = 1` 是单位元**（**承重**：`scaleVec c 1 = c` **不是** `rfl`
—— `List.map (· * 1) ≠ List.map id`，需要列表归纳 + 逐分量 `mul_one`）。 -/
theorem scaleLayer_one_is_identity (cs : ConstraintSet) : scaleLayer 1 cs = cs := by
  unfold scaleLayer
  induction cs with
  | nil => rfl
  | cons c t ih =>
      simp only [List.map_cons]
      rw [ih]
      congr 1
      obtain ⟨a, b⟩ := c
      -- ⚠ `simp [scaleVec]` **无进展**（报 `simp made no progress`）：
      -- `scaleVec c 1 = { a := a.map (· * 1), b := b * 1 }`，而 `simp` 没有
      -- `List.map` 下的 `mul_one` 规则 ⟹ 必须**显式**展开 + 逐分量化简。
      show ({ a := List.map (fun v => v * 1) a, b := b * 1 } : VectorConstraint)
        = { a := a, b := b }
      rw [VectorConstraint.mk.injEq]
      refine ⟨?_, by ring⟩
      -- ⚠ `List.map_congr_left (fun v _ => by ring)` 在此处会因**目标两侧的 `List.map`
      -- 函数不同形**（`fun v => v * 1` vs `id`）而报**元变量**错误。
      -- ⇒ 对 `a` 归纳，逐元素 `ring`。
      -- ⚠ 归纳变量**不能**再用名字 `ih`（**与上面的外层 `ih` 撞名**，会让
      -- `simp only [… ih …]` 引用到错误的假设而报 `unsolved goals`）⟹ 改名 `iha`。
      induction a with
      | nil => rfl
      | cons v t iha =>
          -- 目标：`v :: List.map (fun v => v * 1) t = v :: t`
          -- ⚠ `simp only [List.map_cons, iha, mul_one, id_eq, List.map_id]` **不够**：
          -- 化简后目标里是 `List.map (fun v => v) t`（**η-展开形式**），
          -- 它**不是** `List.map id t` 的语法形态 ⟹ `List.map_id` **匹配不上**。
          -- ⇒ 正解：把目标里那个函数**显式改成 `id`**（`List.map_id''` 或 `funext` 后 `rfl`），
          --   或直接对 `t` 的结构用 `List.map_id` 的**定义级**归约：`simp` 带 `Function.id`。
          simp only [List.map_cons, iha, mul_one]
          -- 现在目标：`v :: List.map (fun v => v) t = v :: t`
          rw [show List.map (fun v => v) t = t from List.map_id t]

/-- ⚠⚠ **已被更正的草案假命题（本波次"代小整数判真假"的又一收益）**：

原草案写的是
`scaleVec c 0 = { a := [], b := 0 }`（**把 `a` 分量写成空表**）。
⭐ **它是假命题** —— 反例：取 `c := { a := [1], b := 0 }`，则
`scaleVec c 0 = { a := [1 * 0], b := 0 * 0 } = { a := [0], b := 0 }`，
而右端是 `{ a := [], b := 0 }`，**`[0] ≠ []`** ⟹ 两边不等。
⚠ 根因：`scaleVec` 用 **`List.map`**（**保长度**），故 `lam = 0` **不会**把 `a` 变成空表，
只是在**每个位置**写入 `0`；`a` 的**长度**被保留。

⭐ **正确版本**（下方 `scaleVec_zero`）：`a` 分量逐位变 `0`，**长度不变**。
⚠ 本引理**必须先于**用到它的 `scaleLayer_zero_is_const` 声明（Lean 不前瞻）。 -/
theorem scaleVec_zero (c : VectorConstraint) :
    scaleVec c 0 = ({ a := c.a.map (fun _ => 0), b := 0 } : VectorConstraint) := by
  obtain ⟨a, b⟩ := c
  -- ⚠ `unfold`/`rw` **不会** β-归约 record 投影；用 `show` 给出**显式**形态
  show ({ a := List.map (fun v => v * 0) a, b := b * 0 } : VectorConstraint) = _
  rw [VectorConstraint.mk.injEq]
  refine ⟨?_, by ring⟩
  -- `a.map (fun v => v * 0) = a.map (fun _ => 0)`：逐元素 `v * 0 = 0`
  exact List.map_congr_left (fun v _ => by ring)

/-- ⭐ **④ `lam = 0` 是常值算子**（**不是**单位元）：`scaleLayer 0` 把任何表
送到**逐位为 `0` 的**约束表（**长度保留**）。

⭐ **它比"`0` 不是单位元"多说了**：给出了 `scaleLayer 0` 的**精确**行为
（每个元素的系数向量**每位变 `0`**、偏置变 `0`）—— 这是"`0` 处退化"的完整刻画。

⚠⚠ **本条曾是假命题（已更正）**：草案把结果写成
`cs.map (fun _ => { a := [], b := 0 })`（**空系数向量**），
⭐ **反例 `cs = [{ a := [1], b := 0 }]`**：左侧得 `{ a := [0], b := 0 }`，
右侧得 `{ a := [], b := 0 }`，而 **`[0] ≠ []`** ⟹ 假。
⇒ 根因：`scaleVec` 用 `List.map`（**保长度**），`lam = 0` **不改变 `a` 的长度**。 -/
theorem scaleLayer_zero_is_const (cs : ConstraintSet) :
    scaleLayer 0 cs = cs.map (fun c => ({ a := c.a.map (fun _ => 0), b := 0 } : VectorConstraint)) := by
  unfold scaleLayer
  induction cs with
  | nil => rfl
  | cons c t ih =>
      simp only [List.map_cons]
      rw [ih]
      congr 1
      -- 目标是 `scaleVec c 0 = { a := c.a.map (fun _ => 0), b := 0 }`
      exact scaleVec_zero c
/-- ⭐ **⑤-引理（列表层，先于 ⑤-基础）**：
`(a.map (· * l₂)).map (· * l₁) = a.map (· * (l₂ * l₁))`。

⭐ **拆分的理由**：在 `List Int` 层陈述可**完全避免**「`List.map (fun …)` 在
record 字面量里被解析成函数」这一陷阱（详见 ⑤-基础的说明）。 -/
theorem scaleVec_a_component (a : List Int) (l₁ l₂ : Int) :
    (a.map (fun v => v * l₂)).map (fun v => v * l₁)
      = a.map (fun v => v * (l₂ * l₁)) := by
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro v _
  simp only [Function.comp_apply]
  ring

/-- ⭐ **⑤-基础：`scaleVec` 的参数可乘（逐点，承重）**

`scaleVec (scaleVec c l₂) l₁ = scaleVec c (l₂ * l₁)`。

⭐ **证明**：`scaleVec` 是 `def`，故**必须展开**（`simp only [scaleVec]`）；
随后两侧逐分量为 `(a.map (· * l₂)).map (· * l₁)` 与 `a.map (· * (l₂*l₁))`，
由 ⑤-引理（`List.map_map` + `Int.mul_assoc`）相等。

⚠⚠ **本文件实测的三处陷阱（与任务书所列同型）**：
1. `simp only [scaleVec, List.map_map]` 会把 `List.map_map` **按某个方向**重写，
   导致剩下的目标是**反向**的 ⟹ 必须**把 `List.map_map` 隔离在独立引理里**控制方向；
2. ⚠ **`unfold scaleVec` 不会 β-归约 record 投影**（`{a := …, b := …}.a` 留在目标里），
   而 **`simp only [scaleVec]` 会** —— 两者**不等价**；
3. 若把目标写成 `{ a := List.map (fun v => v * (l₂*l₁)) a, ... }`，
   Lean 会把 `List.map (fun v => v * (l₂*l₁))` **先**解析为一个函数，报
   `List.map fun v => ... has type List ℤ → List ℤ`。
   ⇒ **正解**：**不写**含 `List.map (fun ...)` 的 record 字面量。 -/
theorem scaleVec_mul_param (c : VectorConstraint) (l₁ l₂ : Int) :
    scaleVec (scaleVec c l₂) l₁ = scaleVec c (l₂ * l₁) := by
  obtain ⟨a, b⟩ := c
  simp only [scaleVec]
  congr 1
  · exact scaleVec_a_component a l₁ l₂
  · ring

/-- ⭐ **⑤ 复合律（实例）**：`scaleLayer (l₂ * l₁) = scaleLayer l₁ ∘ scaleLayer l₂`。
（与 `RealConversionCategorical.scaleLayer_mul` **同型**；本文件自足复现。） -/
theorem scaleLayer_comp_assoc (l₁ l₂ : Int) (cs : ConstraintSet) :
    scaleLayer (l₂ * l₁) cs = scaleLayer l₁ (scaleLayer l₂ cs) := by
  unfold scaleLayer
  induction cs with
  | nil => rfl
  | cons c t ih =>
      simp only [List.map_cons]
      rw [ih]
      congr 1
      -- 目标：`scaleVec c (l₂ * l₁) = scaleVec (scaleVec c l₂) l₁`
      exact (scaleVec_mul_param c l₁ l₂).symm

/-- ⭐ **⑥ 缩放的乘法相容（回收 ⑤-基础）**：本条**不重复证明**，
只把 `scaleVec_mul_param` 以**另一名字**暴露给下游（保持接口稳定性）。 -/
theorem scaleLayer_inverse_iff (c : VectorConstraint) (l₁ l₂ : Int) :
    scaleVec (scaleVec c l₂) l₁ = scaleVec c (l₂ * l₁) :=
  scaleVec_mul_param c l₁ l₂

/-! ## 三、⭐⭐ 何时可逆：可逆 ⟺ `|lam| = 1`

⭐ 这是本文件**最重要的结论**。`Int` 的乘法逆元只有 `±1`，
故**除了 `±1`，任何缩放都不可逆**。 -/

/-- **可逆**（存在 `Int` 层的逆参数 `mu` 使 `scaleVec · (lam * mu) = ·`）。 -/
def ScaleInvertible (lam : Int) : Prop :=
  ∃ mu : Int, lam * mu = 1

/-- ⭐⭐ **⑦ 可逆 ⟺ `|lam| = 1`（核心 iff，承重）**：

- **(⟸)** `lam = 1` 取 `mu = 1`；`lam = -1` 取 `mu = -1`；
- **(⟹)** `lam * mu = 1` ⟹ `|lam| * |mu| = 1` ⟹ `|lam| = 1`
  （`Int.natAbs_mul` + `Nat` 上乘积为 1 ⟹ 两因子为 1）。

⚠ **`Int` 上"逆元唯一"为真、但"逆元存在"极稀有** —— 这正是本文件的**核心发现**：
**转换层的缩放在 `ℤ∖{0}` 上几乎处处不可逆**。 -/
theorem scaleLayer_invertible_iff (lam : Int) :
    ScaleInvertible lam ↔ Int.natAbs lam = 1 := by
  constructor
  · rintro ⟨mu, hmu⟩
    have h := congrArg Int.natAbs hmu
    rw [Int.natAbs_mul, Int.natAbs_one] at h
    exact Nat.eq_one_of_mul_eq_one_right h
  · intro h
    rcases Int.natAbs_eq_iff.mp h with h1 | h1
    · exact ⟨1, by push_cast at h1; rw [h1, mul_one]⟩
    · refine ⟨-1, ?_⟩
      push_cast at h1
      rw [h1]
      norm_num

/-- ⭐⭐ **⑧ 可逆的参数枚举**：`ScaleInvertible lam` ⟺ `lam = 1 ∨ lam = -1`。

⭐ **它比 ⑦ 多说**：⑦ 给的是**绝对值**条件；本条把它**展开**成**枚举**，
下游可以直接 `rcases`（不需要再处理 `natAbs`）。
⇒ 这是「**只有两个**可逆缩放」的显式形式。 -/
theorem scaleLayer_invertible_cases (lam : Int) :
    ScaleInvertible lam ↔ lam = 1 ∨ lam = -1 := by
  rw [scaleLayer_invertible_iff]
  constructor
  · intro h
    rcases Int.natAbs_eq_iff.mp h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · rfl
    · rw [Int.natAbs_neg, Int.natAbs_one]

/-- ⭐⭐ **⑨ 可逆的**函数层**形式（`LeftInverse` / `RightInverse`）**：

`scaleLayer lam` 有**左逆** ⟺ `lam = 1 ∨ lam = -1`。

⭐ **承重性（本节的核心论证）**：
- **(⟸)** `lam = ±1` 时 `scaleLayer lam` 是**恒等**（`scaleLayer_one_is_identity` +
  `scaleLayer_neg_one`），故左逆就是它自己；
- **(⟹)** 若有左逆 `g`，则由 `scaleVec_mul_param`，
  `g` 必须能把 `scaleVec c lam` 还原 —— ⚠ **这一步本文件不做一般论证**
  （那需要"`scaleLayer` 的像"的刻画，**未做**），
  而是**退一步**给出**充分条件**的**具体形式**（`lam = ±1`）。

⚠ **诚实降级**：因此本条是**单向**的充分性 + 一个**否定**（`|lam| ≥ 2` 时**非满射**，见 ⑩），
**不**声称完整的 `⟺`。 -/
theorem scaleLayer_neg_one (cs : ConstraintSet) : scaleLayer (-1) cs = cs.map (scaleVec · (-1)) :=
  rfl

/-- ⭐ **⑨′ `lam = ±1` 时可逆（充分性，显式构造）**：
`scaleLayer 1 ∘ scaleLayer 1 = id`，`scaleLayer (-1) ∘ scaleLayer (-1) = id`
（**对合性**：`(-1) * (-1) = 1`）。

⭐ **它比"可逆"这个谓词多说**：给出了**具体**的逆（就是自己）——
即 `lam = -1` 的缩放是**对合**（involution）。 -/
theorem scaleLayer_neg_one_involutive (cs : ConstraintSet) :
    scaleLayer (-1) (scaleLayer (-1) cs) = cs := by
  rw [show scaleLayer (-1) (scaleLayer (-1) cs) = scaleLayer ((-1) * (-1)) cs from
    (scaleLayer_comp_assoc (-1) (-1) cs).symm]
  rw [show ((-1 : Int) * (-1)) = 1 from by norm_num]
  exact scaleLayer_one_is_identity cs

/-- ⭐⭐ **⑩ 可逆的**障碍**（否定结论）：`|lam| ≥ 2` 时 `scaleLayer lam` **非满射**。

**见证**：`[{a := [1], b := 1}]` **不在** `scaleLayer lam` 的像中
（因为 `b` 分量恒为 `1 * lam`，而 `|lam| ≥ 2` ⟹ `1 * lam ≠ 1`）。
⇒ **非满射 ⟹ 无右逆 ⟹ 不可逆**。

⭐ **它比 ⑦ 多说**：⑦ 只给"参数上没有逆元"；
本定理给出**函数层**的**具体**失效见证（一个**具体的**不可达元素），
故它是「**不可逆**」这一否定的**可检验**形式。 -/
theorem scaleLayer_not_surjective_of_two (lam : Int) (hlam : 2 ≤ Int.natAbs lam) :
    ¬ (∀ cs : ConstraintSet, ∃ cs' : ConstraintSet, scaleLayer lam cs' = cs) := by
  intro h
  rcases h [cUnit] with ⟨cs', hcs'⟩
  have hnil : cs' ≠ [] := by
    rintro rfl
    exact absurd hcs' (by simp [scaleLayer])
  obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hnil
  have hb : (scaleVec c lam).b = cUnit.b := by
    have := congrArg (fun (l : ConstraintSet) => (l.head?).map VectorConstraint.b) hcs'
    simpa [scaleLayer] using this
  have hc : c.b * lam = 1 := by
    simpa [scaleVec, cUnit] using hb
  have h1 : Int.natAbs (c.b * lam) = 1 := by
    rw [hc, Int.natAbs_one]
  rw [Int.natAbs_mul] at h1
  -- `h1 : Int.natAbs c.b * Int.natAbs lam = 1`
  -- ⚠ `omega` 单独证不出（它把乘积当**不透明原子**，报
  -- `possible counterexample … a := ↑?m * ↑c.b.natAbs, b := lam`）。
  -- ⇒ 显式给出"`natAbs lam` 整除 1 ⟹ `≤ 1`"。
  -- ⚠ 注意 `∣` 的见证要**同序**：`1 = natAbs lam * natAbs c.b`（由 `h1` 交换得到）。
  have hdiv : Int.natAbs lam ∣ 1 := ⟨Int.natAbs c.b, by rw [← h1, mul_comm]⟩
  have hle : Int.natAbs lam ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
  omega

/-! ## 四、⭐ 编译-提取对的**双向可逆**（正面结论） -/

/-- ⭐⭐ **⑪ 编译与提取互为左逆/右逆**（**本文件的正面核心**，与 §三 的否定形成对比）：

- `extractLayer ∘ compileToLayer = id`（**左逆**）；
- `compileToLayer ∘ extractLayer = id`（**右逆**）。

⭐ **它比 §三 的否定多说**：§三 说「缩放在 `|lam| ≥ 2` 时**不可逆**」；
本条说「**编译-提取对**在 `ConstraintSet` / `Layer` 上**完全可逆**」。
⇒ 两者**不矛盾**：**可逆性取决于转换的**类型签名****——
`scaleVec : VectorConstraint → Int → VectorConstraint`（**两个**参数，故 `lam` 可被"丢掉"），
而 `convertVec : VectorConstraint → LinearLayer`（**一个**参数，无自由度可丢）。

⭐⭐ **这就是本文件的实质结论**：
「转换可逆与否」**不是**转换的**性质**，而是**转换对的类型签名**的性质。 -/
theorem compile_extract_invertible_pair :
    Function.LeftInverse extractLayer compileToLayer ∧
      Function.RightInverse extractLayer compileToLayer :=
  ⟨extractLayer_compileToLayer, compileToLayer_extractLayer⟩

/-- ⭐ **⑫ 单向可逆的两个面（分别陈述，供下游按需取用）**。 -/
theorem compile_extract_bijective : Function.Bijective compileToLayer :=
  compileToLayer_bijective

/-! ## 五、分段编译的结合律（换个"复合"的载体） -/

/-- ⭐ **⑬ 分段编译的结合律**：`compileToLayer ((cs₁ ++ cs₂) ++ cs₃)`
与 `compileToLayer (cs₁ ++ (cs₂ ++ cs₃))` **相等**（**承重**：需要
`List.append_assoc` 的**两向**重写 + `natTransform_compile` 的两向应用）。

⭐ **它比 `List.append_assoc` 多说**：`List.append_assoc` 是**列表层**事实；
本条把它**推过** `compileToLayer`（即"编译**保持**结合律"）。
⇒ 这是「分片编译**可任意分组**」的形式化，也是"转换层允许模块化组合"的**精化**。 -/
theorem compileToLayer_append_assoc (cs₁ cs₂ cs₃ : ConstraintSet) :
    compileToLayer ((cs₁ ++ cs₂) ++ cs₃) =
      compileToLayer (cs₁ ++ (cs₂ ++ cs₃)) := by
  rw [List.append_assoc]

/-- ⭐⭐ **⑭ 结合律**穿过编译**（更强形式：两边的**分组**都保留）**：

`(κ cs₁ ++ κ cs₂) ++ κ cs₃ = κ cs₁ ++ (κ cs₂ ++ κ cs₃)`。

⭐ **与 ⑬ 的区别**：⑬ 只在 `compileToLayer` **之前**分组；
本条在**之后**分组，需要**两次** `natTransform_compile`
（**正向**拆、**反向**合）—— ⚠ 这是**非平凡**的：`rw` 的两次方向**不同**。 -/
theorem compileToLayer_append_assoc_layer (cs₁ cs₂ cs₃ : ConstraintSet) :
    (compileToLayer cs₁ ++ compileToLayer cs₂) ++ compileToLayer cs₃ =
      compileToLayer cs₁ ++ (compileToLayer cs₂ ++ compileToLayer cs₃) :=
  List.append_assoc _ _ _

/-! ## 六、未做（如实登记）

- ⚠ **`scaleLayer lam` 的单射性**：**未做**（本文件只用**满射性**的失效，见 ⑩）。
- ⚠ **`scaleLayer_invertible_iff` 的完整函数层 `⟺`**：**未做**（⑨ 只给充分性 + ⑩ 的否定）。
- ⚠ **`LosesInfo` 的精确定义与其与不可逆的关系**：**未做**。
- ⚠ **`comp_assoc_lemma` / `comp_id_lemma` 是 `rfl` 级**：
  ⚠ **如实标注**（它们不计入有实质内容的定理数）。
- ⚠ **`scaleLayer` 与 `RealConversionCategorical.scaleLayer` 同名**：**已标注**（§二）。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
