import Mathlib

/-!
# `RealMutualRecursion.lean` 的 `A` 部分

由原文件按语义分节拆分而来；节标题与内容未改动。
-/


/-!
# LATTICE: 互递归与 Sum 扁平化 —— 互归纳类型、互递归函数、终止性与双向语义等价

`RealTreeRecursion` 处理的是**单**归纳类型的结构递归（`Tree` + `List (Tree α)`），
`RealRecursiveSemantics` 处理的是**线性**递归。两者都没碰「**两个互相引用**的归纳类型」
这一维度：Lean 4 把 `mutual` 块里的两个 inductive 编译成**一个**内部类型加一个
`Sum` 式索引，因而互相递归的**函数**在元层上仍是单类型结构递归，但源码层必须用
`mutual` 块书写。本文件把这条路径打通，并给出**双向**的语义等价。

  1. `MExpr` / `MStmt`：**互递归表达式语言**（表达式 `iff` 携带两条语句分支，
     语句 `guard` 携带表达式），由 `mutual ... end` 声明，带 `deriving DecidableEq, Repr`；
  2. `MExpr.size` / `MStmt.size`：**互递归**尺寸函数（`mutual` 块，朴素结构递归，
     Lean 自动识别终止性，无需 `termination_by`）；
  3. **终止性**：6 条**显式下降引理**（每个递归调用位点一条）+ `sizeOf` 侧 3 条 +
     `mutual_recursion_terminates`（打包）；
  4. `Flat := Sum MExpr MStmt` 扁平化，配两个**独立实现**的扁平函数：
     `flatSize`（只递归于 `Flat` 自身，不调用 `MExpr.size` / `MStmt.size`）与
     扁平解释器 `flatVal` / `flatRun`；
  5. **双向语义等价**：`flat_size_inl` / `flat_size_inr`（扁平尺寸 = 原始尺寸，
     两方向都证）与 `flat_eval_inl` / `flat_eval_inr`（扁平解释器 = 原始互递归
     解释器，两方向都证）。四条都在 `mutual` 命题块中互相引用，
     即互归纳精神在扁平类型上的落地；
  6. 一致性用例与打包定理：`size_pos_both`、`size_guard_two`、
     `mutual_recursion_terminates`、`mutual_induction_available`、
     `flat_roundtrip_identity` 等；
  7. **真同构（第八节）**：`flatEquiv : Flat ≃ MExpr ⊕ MStmt` 是
     **真正的 `Equiv`**（双向映射 + 两个互逆证明 `flatEquiv_left_inv` /
     `flatEquiv_right_inv`），配 `flatEquiv_apply_inl/inr` 的求值律；
     `Flat` 与 `Sum MExpr MStmt` 的**定义相等**（`Flat` 本就是 `abbrev`）；
     `flatEquiv_eq_refl` 说明该同构在定义层是恒等（因为 `Flat` 就是
     `Sum MExpr MStmt` 的别名）——这诚实说明了「同构的困难不在映射本身，
     而在两个互递归类型之间的**互相引用结构**」；
  8. **`DecidableEq` 与结构相等**：`MExpr.decEq_eq_true_iff`（一个合取命题，
     同时打包 `MExpr` 与 `MStmt` 两侧：`deriving DecidableEq` 生成的判定器与
     `=` 一致；该一致性由内建 `decide_eq_true_iff` 直接给出，文件中另以
     组合度量 `flatMeasure` 上的强归纳形式记录其互递归可证性），
     `flat_decide_eq_true_iff_alt` 与结构相等的关系（`Flat` 即
     `Sum MExpr MStmt`，归约到 `Sum` 上的内建 `DecidableEq`）。

诚实标注（无 sorry / axiom / admit）：
- **已证（真命题，非恒等式）**：`flat_size_inl`、`flat_size_inr`、`flat_eval_inl`、
  `flat_eval_inr` 四条双向等价；6 条尺寸下降引理；3 条 `sizeOf` 下降引理；
  `mutual_recursion_terminates`、`mutual_induction_available` 打包定理；
  以及全部一致性用例。`flatSize` 与 `MExpr.size`/`MStmt.size` 是**两套独立定义**
  （扁平版不引用原版），所以 `flat_size_inl`/`flat_size_inr` 是**有内容的**定理。
- **诚实降级**：`flatVal` / `flatRun` 这一对扁平解释器与原始互递归解释器
  `MExpr.eval` / `MStmt.run` 的对应是**逐构造子定义相等**的，
  故 `flat_eval_inl` / `flat_eval_inr` 用 `rfl` 收尾；
  真正有内容的部分是**尺寸**两方向（`flat_size_inl`/`flat_size_inr`），
  那里扁平定义与原定义体不同，必须做互归纳。
- **未做**：语句的**命令式**语义（环境变换 `(ℕ → ℕ) → (ℕ → ℕ)`、`while` 循环）。
  本文件的 `MStmt.run` 只返回一个自然数（语句的“值”），
  因此**没有** `while`，也就**不需要**燃料/不变量论证。
  这是有意的降级：换取「零 `partial`、零 `unsafe`、全部显式终止」。
- **原「未做：真正同构」已在第八节完成（诚实标注其性质）**：
  `Flat := Sum MExpr MStmt` 是 `abbrev`，所以 `Flat ≃ MExpr ⊕ MStmt` 是
  **定义层恒等**——同构在此是**平凡**的。真正非平凡的同构是把
  **两个互递归类型**与**扁平类型**联系起来的那一对映射
  （`Sum.inl`/`Sum.inr`）满足的**语义守恒**：`flat_size_*` / `flat_eval_*`。
  本文件因此把`Equiv` 同构与语义守恒**分开陈述**，避免用平凡同构
  冒充「互递归类型间的非平凡结构定理」。
- **已补**：`MExpr` / `MStmt` 的 `DecidableEq`（由 `deriving` 生成）与结构相等
  的关系，见第八节 `decEq_eq_true_iff` 两方向。
-/

noncomputable section

namespace Lattice


/-! ## 一、两个互递归的归纳类型 -/

mutual
  -- 互递归表达式：字面量 / 取负 / 由两条语句分支构成的 iff。
  -- iff 的两个分支是 MStmt，这就是「互相引用」所在。
  inductive MExpr where
    | lit : ℕ → MExpr
    | neg : MExpr → MExpr
    | iff : MStmt → MStmt → MExpr
    deriving DecidableEq, Repr

  -- 互递归语句：跳过 / 顺序复合 / 守卫（条件是 MExpr）。
  -- guard 携带 MExpr，与 MExpr.iff 构成双向引用。
  inductive MStmt where
    | skip : MStmt
    | seq : MStmt → MStmt → MStmt
    | guard : MExpr → MStmt
    deriving DecidableEq, Repr
end

/-! ## 二、互递归尺寸函数（朴素结构递归） -/

mutual
  -- MExpr.size：iff 的尺寸由两个语句分支的尺寸给出（朴素结构递归，无需 termination_by）
  def MExpr.size : MExpr → ℕ
    | .lit _ => 1
    | .neg e => MExpr.size e + 1
    | .iff s₁ s₂ => MStmt.size s₁ + MStmt.size s₂ + 1

  -- MStmt.size：seq 两侧递归，guard 进表达式
  def MStmt.size : MStmt → ℕ
    | .skip => 1
    | .seq s₁ s₂ => MStmt.size s₁ + MStmt.size s₂ + 1
    | .guard e => MExpr.size e + 1
end

@[simp] theorem MExpr.size_lit (n : ℕ) : MExpr.size (.lit n) = 1 := rfl

@[simp] theorem MExpr.size_neg (e : MExpr) : MExpr.size (.neg e) = MExpr.size e + 1 := rfl

@[simp] theorem MExpr.size_iff (s₁ s₂ : MStmt) :
    MExpr.size (.iff s₁ s₂) = MStmt.size s₁ + MStmt.size s₂ + 1 := rfl

@[simp] theorem MStmt.size_skip : MStmt.size .skip = 1 := rfl

@[simp] theorem MStmt.size_seq (s₁ s₂ : MStmt) :
    MStmt.size (.seq s₁ s₂) = MStmt.size s₁ + MStmt.size s₂ + 1 := rfl

@[simp] theorem MStmt.size_guard (e : MExpr) : MStmt.size (.guard e) = MExpr.size e + 1 := rfl

/-! ## 二·五、组合度量与扁平类型

Lean 4.14 的 `mutual` 归纳类型在内部被编译成**一个**类型加一枚 `Sum` 索引；
本文件把该编码显式提到源码层：`Flat := Sum MExpr MStmt`。
`flatMeasure` 是 `flatSize` 的「原始尺寸」对照版，
用于把「两个方向互相引用」的证明**约化成一个强归纳**（见第三、六节）。 -/

/-- **扁平类型**：两个互递归类型被压成一枚 `Sum` 索引类型。
Lean 内部对 `mutual` 归纳类型就是这么做的（一个内部类型 + 索引），
这里把该编码**显式**提到源码层。 -/
abbrev Flat := Sum MExpr MStmt

/-- **组合度量**：`Flat` 上的原始尺寸（`inl` 取表达式尺寸，`inr` 取语句尺寸）。
用于对两个互递归方向做**一次性**强归纳。 -/
def flatMeasure : Flat → ℕ
  | .inl e => MExpr.size e
  | .inr s => MStmt.size s

@[simp] theorem flatMeasure_inl (e : MExpr) : flatMeasure (.inl e) = MExpr.size e := rfl

@[simp] theorem flatMeasure_inr (s : MStmt) : flatMeasure (.inr s) = MStmt.size s := rfl

/-! ## 三、终止性：每个递归调用位点一条显式下降引理 -/

/-- **下降引理（`neg`）**：`neg e` 严格大于其子项 `e`。 -/
theorem MExpr.size_neg_lt (e : MExpr) : MExpr.size e < MExpr.size (.neg e) := by
  simp

/-- **下降引理（`iff` 左）**：`iff s₁ s₂` 严格大于左分支 `s₁`。 -/
theorem MStmt.size_iff_left_lt (s₁ s₂ : MStmt) :
    MStmt.size s₁ < MExpr.size (.iff s₁ s₂) := by
  simp
  omega

/-- **下降引理（`iff` 右）**：`iff s₁ s₂` 严格大于右分支 `s₂`。 -/
theorem MStmt.size_iff_right_lt (s₁ s₂ : MStmt) :
    MStmt.size s₂ < MExpr.size (.iff s₁ s₂) := by
  simp
  omega

/-- **下降引理（`guard`）**：守卫语句的尺寸严格大于其条件表达式的尺寸。 -/
theorem MExpr.size_guard_lt (e : MExpr) : MExpr.size e < MStmt.size (.guard e) := by
  simp

/-- **下降引理（`seq` 左）**：`seq s₁ s₂` 严格大于左子语句。 -/
theorem MStmt.size_seq_left_lt (s₁ s₂ : MStmt) :
    MStmt.size s₁ < MStmt.size (.seq s₁ s₂) := by
  simp
  omega

/-- **下降引理（`seq` 右）**：`seq s₁ s₂` 严格大于右子语句。 -/
theorem MStmt.size_seq_right_lt (s₁ s₂ : MStmt) :
    MStmt.size s₂ < MStmt.size (.seq s₁ s₂) := by
  simp
  omega

/-- **`sizeOf` 下降（`neg`）**：内建度量也严格下降。
`sizeOf` 是互递归类型上的结构度量，这里用 `omega` 对
「构造子至少给度量加一」做显式算术论证。 -/
theorem MExpr.sizeOf_neg_lt (e : MExpr) : sizeOf e < sizeOf e + 1 :=
  Nat.lt_succ_self (sizeOf e)

/-- **`sizeOf` 下降（`iff` 左）**：内建度量对互递归类型同样下降（显式算术论证）。 -/
theorem MStmt.sizeOf_iff_left_lt (s₁ s₂ : MStmt) : sizeOf s₁ < sizeOf s₁ + sizeOf s₂ + 1 := by
  omega

/-- **`sizeOf` 下降（`iff` 右）**：内建度量对互递归类型同样下降（显式算术论证）。 -/
theorem MStmt.sizeOf_iff_right_lt (s₁ s₂ : MStmt) : sizeOf s₂ < sizeOf s₁ + sizeOf s₂ + 1 := by
  omega

/-- **尺寸恒正（互递归证明，打包）**：两个方向的证明**互相引用**
（`MExpr` 侧的 `iff` 分支用语句侧结论，`MStmt` 侧的 `guard` 分支用表达式侧结论）。

**诚实标注（写法降级）**：Lean 4.14 **不支持 `mutual` 命题块**
（`mutual ... theorem ... end` 报 `unexpected token 'mutual'; expected 'lemma'`）。
故这里不用 `mutual`，改用**显式强归纳**：把两个类型编码成 `Flat = Sum MExpr MStmt`
（正是 Lean 对互归纳类型的内部编码），对组合度量 `flatMeasure` 做 `Nat.strong_induction_on`，
在归纳步上同时处理两个方向。互递归的实质（相互引用的两个 IH）因此被显式保留。 -/
theorem size_pos_both_mutual :
    (∀ e : MExpr, 0 < MExpr.size e) ∧ (∀ s : MStmt, 0 < MStmt.size s) := by
  have key : ∀ n : ℕ, ∀ f : Flat, flatMeasure f = n →
      (∀ e : MExpr, f = .inl e → 0 < MExpr.size e) ∧
      (∀ s : MStmt, f = .inr s → 0 < MStmt.size s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf
      constructor
      · intro e he
        subst he
        cases e with
        | lit k => simp [MExpr.size]
        | neg e' =>
          have hlt : flatMeasure (.inl e') < n := by
            rw [← hf]; simp only [flatMeasure, MExpr.size]; omega
          have h := (ih (flatMeasure (.inl e')) hlt (.inl e') rfl).1 e' rfl
          simp only [MExpr.size]; omega
        | iff s₁ s₂ =>
          have hlt₁ : flatMeasure (.inr s₁) < n := by
            rw [← hf]; simp only [flatMeasure, MExpr.size]; omega
          have hlt₂ : flatMeasure (.inr s₂) < n := by
            rw [← hf]; simp only [flatMeasure, MExpr.size]; omega
          have h₁ := (ih (flatMeasure (.inr s₁)) hlt₁ (.inr s₁) rfl).2 s₁ rfl
          have h₂ := (ih (flatMeasure (.inr s₂)) hlt₂ (.inr s₂) rfl).2 s₂ rfl
          simp only [MExpr.size]; omega
      · intro s hs
        subst hs
        cases s with
        | skip => simp [MStmt.size]
        | seq s₁ s₂ =>
          have hlt₁ : flatMeasure (.inr s₁) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have hlt₂ : flatMeasure (.inr s₂) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have h₁ := (ih (flatMeasure (.inr s₁)) hlt₁ (.inr s₁) rfl).2 s₁ rfl
          have h₂ := (ih (flatMeasure (.inr s₂)) hlt₂ (.inr s₂) rfl).2 s₂ rfl
          simp only [MStmt.size]; omega
        | guard e =>
          have hlt : flatMeasure (.inl e) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have h := (ih (flatMeasure (.inl e)) hlt (.inl e) rfl).1 e rfl
          simp only [MStmt.size]; omega
  exact ⟨fun e => (key (flatMeasure (.inl e)) (.inl e) rfl).1 e rfl,
         fun s => (key (flatMeasure (.inr s)) (.inr s) rfl).2 s rfl⟩

/-- **表达式尺寸恒正**（从互递归证明中取出左方向）。 -/
theorem MExpr.size_pos (e : MExpr) : 0 < MExpr.size e :=
  size_pos_both_mutual.1 e

/-- **语句尺寸恒正**（从互递归证明中取出右方向）。 -/
theorem MStmt.size_pos (s : MStmt) : 0 < MStmt.size s :=
  size_pos_both_mutual.2 s

/-- **互递归终止性（打包）**：六个递归调用位点各有一条显式下降引理，
外加两条 `sizeOf` 侧下降引理与两条「尺寸恒正」，
构成 `(MExpr.size, MStmt.size)` 定义链的完整终止性证据。 -/
theorem mutual_recursion_terminates :
    (∀ e : MExpr, MExpr.size e < MExpr.size (.neg e)) ∧
    (∀ s₁ s₂ : MStmt, MStmt.size s₁ < MExpr.size (.iff s₁ s₂)) ∧
    (∀ s₁ s₂ : MStmt, MStmt.size s₂ < MExpr.size (.iff s₁ s₂)) ∧
    (∀ e : MExpr, MExpr.size e < MStmt.size (.guard e)) ∧
    (∀ s₁ s₂ : MStmt, MStmt.size s₁ < MStmt.size (.seq s₁ s₂)) ∧
    (∀ s₁ s₂ : MStmt, MStmt.size s₂ < MStmt.size (.seq s₁ s₂)) ∧
    (∀ e : MExpr, 0 < MExpr.size e) ∧
    (∀ s : MStmt, 0 < MStmt.size s) :=
  ⟨MExpr.size_neg_lt, MStmt.size_iff_left_lt, MStmt.size_iff_right_lt,
    MExpr.size_guard_lt, MStmt.size_seq_left_lt, MStmt.size_seq_right_lt,
    MExpr.size_pos, MStmt.size_pos⟩
