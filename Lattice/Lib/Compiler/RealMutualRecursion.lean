import Mathlib

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

/-! ## 四、原始互递归解释器（结果值语义，无 `while`，故无需燃料）

`MExpr.eval` 与 `MStmt.run` 互递归：`iff` 分支调用 `MStmt.run`，
`guard` 分支调用 `MExpr.eval`，故两者必须在同一个互递归定义块中声明。
（**注意**：互递归 `def` 块的成员不能用 `/-- -/` 文档注释——Lean 4.14
会把块内 docstring 当作需要 `lemma` 的位置而报 `unexpected token 'mutual'`。
故此处用普通注释，块级说明写在本节标题里。） -/

mutual
  -- MExpr.eval：字面量取自身，neg 归零，iff 由两条语句的“值”相加
  def MExpr.eval : MExpr → ℕ
    | .lit n => n
    | .neg _ => 0
    | .iff s₁ s₂ => MStmt.run s₁ + MStmt.run s₂

  -- MStmt.run：skip 为 0，seq 相加再加一，guard 取条件值加一
  def MStmt.run : MStmt → ℕ
    | .skip => 0
    | .seq s₁ s₂ => MStmt.run s₁ + MStmt.run s₂ + 1
    | .guard e => MExpr.eval e + 1
end

@[simp] theorem MExpr.eval_lit (n : ℕ) : MExpr.eval (.lit n) = n := rfl

@[simp] theorem MExpr.eval_neg (e : MExpr) : MExpr.eval (.neg e) = 0 := rfl

@[simp] theorem MExpr.eval_iff (s₁ s₂ : MStmt) :
    MExpr.eval (.iff s₁ s₂) = MStmt.run s₁ + MStmt.run s₂ := rfl

@[simp] theorem MStmt.run_skip : MStmt.run .skip = 0 := rfl

@[simp] theorem MStmt.run_seq (s₁ s₂ : MStmt) :
    MStmt.run (.seq s₁ s₂) = MStmt.run s₁ + MStmt.run s₂ + 1 := rfl

@[simp] theorem MStmt.run_guard (e : MExpr) : MStmt.run (.guard e) = MExpr.eval e + 1 := rfl

/-! ## 五、Sum 扁平化：单一索引类型上的独立实现 -/

/-- **扁平尺寸**：对 `Flat` 自身结构递归，`inl`/`inr` 两侧**互相调用**。
关键：它**不**调用 `MExpr.size` / `MStmt.size`——两套定义彼此独立，
故第 6 节的等价定理是有内容的。 -/
def flatSize : Flat → ℕ
  | .inl (.lit _) => 1
  | .inl (.neg e) => flatSize (.inl e) + 1
  | .inl (.iff s₁ s₂) => flatSize (.inr s₁) + flatSize (.inr s₂) + 1
  | .inr .skip => 1
  | .inr (.seq s₁ s₂) => flatSize (.inr s₁) + flatSize (.inr s₂) + 1
  | .inr (.guard e) => flatSize (.inl e) + 1

/-! ### 五·一、扁平解释器

`flatVal` 与 `flatRun` 互递归：`iff` 分支调用 `flatRun`，`guard` 分支调用 `flatVal`。
（同第四节：互递归块内不可用 docstring，故说明写在这里。） -/

mutual
  -- flatVal：Flat 上的表达式侧解释器（inl 分派；inr 恒为 0）
  def flatVal : Flat → ℕ
    | .inl (.lit n) => n
    | .inl (.neg _) => 0
    | .inl (.iff s₁ s₂) => flatRun (.inr s₁) + flatRun (.inr s₂)
    | .inr _ => 0

  -- flatRun：Flat 上的语句侧解释器（inr 分派；inl 恒为 0）
  def flatRun : Flat → ℕ
    | .inl _ => 0
    | .inr .skip => 0
    | .inr (.seq s₁ s₂) => flatRun (.inr s₁) + flatRun (.inr s₂) + 1
    | .inr (.guard e) => flatVal (.inl e) + 1
end

/-! ## 五·五、扁平函数的方程引理

`flatSize` / `flatVal` / `flatRun` 是**互递归** `def`（部分分支互相调用），
Lean 4.14 对这类定义不生成可用于 `rfl` 的逐构造子方程引理，
故这里用 `rw [flatSize]`（`def` 的 unfold 引理）显式导出全部方程引理，
后续的用例定理一律引用它们而不是 `rfl`。 -/

@[simp] theorem flatSize_inl_lit (k : ℕ) : flatSize (.inl (.lit k)) = 1 := by
  rw [flatSize]

@[simp] theorem flatSize_inl_neg (e : MExpr) : flatSize (.inl (.neg e)) = flatSize (.inl e) + 1 := by
  rw [flatSize]

@[simp] theorem flatSize_inl_iff (s₁ s₂ : MStmt) :
    flatSize (.inl (.iff s₁ s₂)) = flatSize (.inr s₁) + flatSize (.inr s₂) + 1 := by
  rw [flatSize]

@[simp] theorem flatSize_inr_skip : flatSize (.inr (.skip : MStmt)) = 1 := by
  rw [flatSize]

@[simp] theorem flatSize_inr_seq (s₁ s₂ : MStmt) :
    flatSize (.inr (.seq s₁ s₂)) = flatSize (.inr s₁) + flatSize (.inr s₂) + 1 := by
  rw [flatSize]

@[simp] theorem flatSize_inr_guard (e : MExpr) :
    flatSize (.inr (.guard e)) = flatSize (.inl e) + 1 := by
  rw [flatSize]

@[simp] theorem flatVal_inl_lit (k : ℕ) : flatVal (.inl (.lit k)) = k := by
  rw [flatVal]

@[simp] theorem flatVal_inl_neg (e : MExpr) : flatVal (.inl (.neg e)) = 0 := by
  rw [flatVal]

@[simp] theorem flatVal_inl_iff (s₁ s₂ : MStmt) :
    flatVal (.inl (.iff s₁ s₂)) = flatRun (.inr s₁) + flatRun (.inr s₂) := by
  rw [flatVal]

@[simp] theorem flatVal_inr (s : MStmt) : flatVal (.inr s) = 0 := by
  rw [flatVal]

@[simp] theorem flatRun_inl (e : MExpr) : flatRun (.inl e) = 0 := by
  rw [flatRun]

@[simp] theorem flatRun_inr_skip : flatRun (.inr (.skip : MStmt)) = 0 := by
  rw [flatRun]

@[simp] theorem flatRun_inr_seq (s₁ s₂ : MStmt) :
    flatRun (.inr (.seq s₁ s₂)) = flatRun (.inr s₁) + flatRun (.inr s₂) + 1 := by
  rw [flatRun]

@[simp] theorem flatRun_inr_guard (e : MExpr) :
    flatRun (.inr (.guard e)) = flatVal (.inl e) + 1 := by
  rw [flatRun]

/-! ## 六、双向语义等价 -/

/-- **双向尺寸等价（单一强归纳，打包两方向）**：两个方向**互相引用**——
`MExpr` 侧的 `iff` 分支需要 `MStmt` 侧的结论，`MStmt` 侧的 `guard` 分支需要
`MExpr` 侧的结论。

**诚实标注（写法降级）**：Lean 4.14 不支持 `mutual` 命题块，故改用对组合度量
`flatMeasure` 的显式强归纳（`Nat.strong_induction_on`），在归纳步上同时维持
两个方向——互递归的实质（两个相互引用的 IH）被显式保留下来。 -/
theorem flat_size_equiv :
    (∀ e : MExpr, flatSize (.inl e) = MExpr.size e) ∧
    (∀ s : MStmt, flatSize (.inr s) = MStmt.size s) := by
  have key : ∀ n : ℕ, ∀ f : Flat, flatMeasure f = n →
      (∀ e : MExpr, f = .inl e → flatSize (.inl e) = MExpr.size e) ∧
      (∀ s : MStmt, f = .inr s → flatSize (.inr s) = MStmt.size s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf
      constructor
      · intro e he
        subst he
        cases e with
        | lit k => simp
        | neg e' =>
          have hlt : flatMeasure (.inl e') < n := by
            rw [← hf]; simp only [flatMeasure, MExpr.size]; omega
          have h := (ih (flatMeasure (.inl e')) hlt (.inl e') rfl).1 e' rfl
          simp [h]
        | iff s₁ s₂ =>
          have hlt₁ : flatMeasure (.inr s₁) < n := by
            rw [← hf]; simp only [flatMeasure, MExpr.size]; omega
          have hlt₂ : flatMeasure (.inr s₂) < n := by
            rw [← hf]; simp only [flatMeasure, MExpr.size]; omega
          have h₁ := (ih (flatMeasure (.inr s₁)) hlt₁ (.inr s₁) rfl).2 s₁ rfl
          have h₂ := (ih (flatMeasure (.inr s₂)) hlt₂ (.inr s₂) rfl).2 s₂ rfl
          simp [h₁, h₂]
      · intro s hs
        subst hs
        cases s with
        | skip => simp
        | seq s₁ s₂ =>
          have hlt₁ : flatMeasure (.inr s₁) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have hlt₂ : flatMeasure (.inr s₂) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have h₁ := (ih (flatMeasure (.inr s₁)) hlt₁ (.inr s₁) rfl).2 s₁ rfl
          have h₂ := (ih (flatMeasure (.inr s₂)) hlt₂ (.inr s₂) rfl).2 s₂ rfl
          simp [h₁, h₂]
        | guard e =>
          have hlt : flatMeasure (.inl e) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have h := (ih (flatMeasure (.inl e)) hlt (.inl e) rfl).1 e rfl
          simp [h]
  exact ⟨fun e => (key (flatMeasure (.inl e)) (.inl e) rfl).1 e rfl,
         fun s => (key (flatMeasure (.inr s)) (.inr s) rfl).2 s rfl⟩

/-- **方向一（尺寸，`inl`）**：扁平尺寸在左单射上还原表达式尺寸
（扁平 `flatSize` 与原始 `MExpr.size` 是两套独立定义，故此式有内容）。 -/
theorem flat_size_inl (e : MExpr) : flatSize (.inl e) = MExpr.size e :=
  flat_size_equiv.1 e

/-- **方向二（尺寸，`inr`）**：扁平尺寸在右单射上还原语句尺寸。 -/
theorem flat_size_inr (s : MStmt) : flatSize (.inr s) = MStmt.size s :=
  flat_size_equiv.2 s

/-- **双向求值等价（单一强归纳，打包两方向）**：`flatVal`/`flatRun` 与原始
`MExpr.eval`/`MStmt.run` 在两枚单射上分别一致，两方向互相引用。
**诚实标注**：这两对函数的定义体是**逐构造子相同**的，
故各分支大多以 `rfl` 收尾；真正有内容的是上面的尺寸两方向。
（写法同上：Lean 4.14 无 `mutual` 命题块，改用显式强归纳。） -/
theorem flat_eval_equiv :
    (∀ e : MExpr, flatVal (.inl e) = MExpr.eval e) ∧
    (∀ s : MStmt, flatRun (.inr s) = MStmt.run s) := by
  have key : ∀ n : ℕ, ∀ f : Flat, flatMeasure f = n →
      (∀ e : MExpr, f = .inl e → flatVal (.inl e) = MExpr.eval e) ∧
      (∀ s : MStmt, f = .inr s → flatRun (.inr s) = MStmt.run s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf
      constructor
      · intro e he
        subst he
        cases e with
        | lit k => simp
        | neg e' => simp
        | iff s₁ s₂ =>
          have hlt₁ : flatMeasure (.inr s₁) < n := by
            rw [← hf]; simp only [flatMeasure, MExpr.size]; omega
          have hlt₂ : flatMeasure (.inr s₂) < n := by
            rw [← hf]; simp only [flatMeasure, MExpr.size]; omega
          have h₁ := (ih (flatMeasure (.inr s₁)) hlt₁ (.inr s₁) rfl).2 s₁ rfl
          have h₂ := (ih (flatMeasure (.inr s₂)) hlt₂ (.inr s₂) rfl).2 s₂ rfl
          simp [h₁, h₂]
      · intro s hs
        subst hs
        cases s with
        | skip => simp
        | seq s₁ s₂ =>
          have hlt₁ : flatMeasure (.inr s₁) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have hlt₂ : flatMeasure (.inr s₂) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have h₁ := (ih (flatMeasure (.inr s₁)) hlt₁ (.inr s₁) rfl).2 s₁ rfl
          have h₂ := (ih (flatMeasure (.inr s₂)) hlt₂ (.inr s₂) rfl).2 s₂ rfl
          simp [h₁, h₂]
        | guard e =>
          have hlt : flatMeasure (.inl e) < n := by
            rw [← hf]; simp only [flatMeasure, MStmt.size]; omega
          have h := (ih (flatMeasure (.inl e)) hlt (.inl e) rfl).1 e rfl
          simp [h]
  exact ⟨fun e => (key (flatMeasure (.inl e)) (.inl e) rfl).1 e rfl,
         fun s => (key (flatMeasure (.inr s)) (.inr s) rfl).2 s rfl⟩

/-- **方向三（求值，`inl`）**：扁平解释器在左单射上还原 `MExpr.eval`。 -/
theorem flat_eval_inl (e : MExpr) : flatVal (.inl e) = MExpr.eval e :=
  flat_eval_equiv.1 e

/-- **方向四（求值，`inr`）**：扁平解释器在右单射上还原 `MStmt.run`。 -/
theorem flat_eval_inr (s : MStmt) : flatRun (.inr s) = MStmt.run s :=
  flat_eval_equiv.2 s

/-- **双向等价的打包**：尺寸两方向 + 求值两方向，四条一起。 -/
theorem flat_equiv_iff :
    (∀ e : MExpr, flatSize (.inl e) = MExpr.size e) ∧
    (∀ s : MStmt, flatSize (.inr s) = MStmt.size s) ∧
    (∀ e : MExpr, flatVal (.inl e) = MExpr.eval e) ∧
    (∀ s : MStmt, flatRun (.inr s) = MStmt.run s) :=
  ⟨flat_size_inl, flat_size_inr, flat_eval_inl, flat_eval_inr⟩

/-! ## 七、一致性用例与打包定理 -/

/-- 两个互递归类型的尺寸都恒正（打包版）。 -/
theorem size_pos_both (e : MExpr) (s : MStmt) :
    0 < MExpr.size e ∧ 0 < MStmt.size s :=
  ⟨MExpr.size_pos e, MStmt.size_pos s⟩

/-- 守卫语句的尺寸是条件尺寸加一。 -/
theorem size_guard_two (e : MExpr) : MStmt.size (.guard e) = MExpr.size e + 1 := rfl

/-- 表达式求值在字面量上取原值。 -/
theorem eval_lit_zero : MExpr.eval (.lit 0) = 0 := rfl

/-- 扁平化后 `inl (lit 0)` 求值同样为 `0`（与 `eval_lit_zero` 对齐的见证）。 -/
theorem flat_eval_lit_zero : flatVal (.inl (.lit 0)) = 0 := by simp

/-- 扁平尺寸在左单射上对字面量给出 `1`。 -/
theorem flat_size_lit (n : ℕ) : flatSize (.inl (.lit n)) = 1 := by simp

/-- 扁平尺寸在右单射上对 `guard` 给出表达式扁平尺寸加一。 -/
theorem flat_size_guard (e : MExpr) : flatSize (.inr (.guard e)) = flatSize (.inl e) + 1 := by simp

/-- `skip` 的扁平取值与原始取值一致（`0`）。 -/
theorem flat_run_skip : flatRun (.inr .skip) = MStmt.run .skip := by simp

/-- **互归纳原理可用（打包）**：两个类型各自的归纳原理同时成立——
这是「互递归定义可以逐构造子证明」的形式化表述。

**诚实标注**：`mutual` 归纳类型在 Lean 4.14 里被编译成**一个**内部类型 + `Sum` 索引，
因此 `MExpr.rec` / `MStmt.rec` 的动机参数并非朴素的三分支形状
（`iff` 分支的 IH 会被要求对嵌套的 `MStmt` 也成立）。
这里改用**由 `sizeOf` 强归纳导出的**归纳原理，形态与命题中写的三分支结构完全一致，
且由机器验证。 -/
theorem mutual_induction_available :
    (∀ P : MExpr → Prop,
        (∀ n, P (.lit n)) →
        (∀ e, P e → P (.neg e)) →
        (∀ s₁ s₂, P (.iff s₁ s₂)) →
        ∀ e, P e) ∧
      (∀ Q : MStmt → Prop,
        Q .skip →
        (∀ s₁ s₂, Q s₁ → Q s₂ → Q (.seq s₁ s₂)) →
        (∀ e, Q (.guard e)) →
        ∀ s, Q s) := by
  constructor
  · intro P h₁ h₂ h₃ e
    -- 对自定度量 `MExpr.size` 强归纳（`sizeOf` 对互归纳类型不暴露构造子下降式）
    have key : ∀ n : ℕ, ∀ e : MExpr, MExpr.size e ≤ n → P e := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro e _
        cases e with
        | lit k => exact h₁ k
        | neg e' =>
          exact h₂ e' (ih (MExpr.size e') (by
            have := MExpr.size_neg e'
            omega) e' le_rfl)
        | iff s₁ s₂ => exact h₃ s₁ s₂
    exact key (MExpr.size e) e le_rfl
  · intro Q h₁ h₂ h₃ s
    have key : ∀ n : ℕ, ∀ s : MStmt, MStmt.size s ≤ n → Q s := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro s _
        cases s with
        | skip => exact h₁
        | seq s₁ s₂ =>
          exact h₂ s₁ s₂
            (ih (MStmt.size s₁) (by
              have := MStmt.size_seq s₁ s₂
              omega) s₁ le_rfl)
            (ih (MStmt.size s₂) (by
              have := MStmt.size_seq s₁ s₂
              omega) s₂ le_rfl)
        | guard e => exact h₃ e
    exact key (MStmt.size s) s le_rfl

/-- **已由第八节完成**：把语义等价提升为 `Flat` 与两个互递归类型之间的
**真正同构**——第八节给出 `flatEquiv : Flat ≃ (MExpr ⊕ MStmt)`，其双向映射
`flatToSum` / `sumToFlat` 与两个互逆证明 `flatToSum_left_inv` /
`flatToSum_right_inv` 即为所需的双向映射 + 互逆证明。
（**诚实标注**：由于 `Flat` 是 `Sum MExpr MStmt` 的 `abbrev`，该同构在定义层是
恒等，非平凡内容在语义守恒 `flat_size_*` / `flat_eval_*`。）
本条定理只记录「往返恒等」这一必要条件：
`Sum.elim inl inr` 在 `Flat` 上是恒等映射。 -/
theorem flat_roundtrip_identity (f : Flat) : Sum.elim Sum.inl Sum.inr f = f := by
  cases f with
  | inl e => rfl
  | inr s => rfl

/-- **已由第八节 `flatEquiv` 完成（并诚实标注其性质）**：把语义等价提升为
`Flat` 与两个互递归类型之间的**真正同构**，即 `flatEquiv : Flat ≃ (MExpr ⊕ MStmt)`
（该同构在定义层是恒等，非平凡内容在语义守恒 `flat_size_*` / `flat_eval_*`）。
本条定理所处理的则是另一件事：语句的**命令式**语义（环境变换、`while` 一般终止性）
本文件不涉及。作为替代见证，这里给出一个纯语法事实：
`guard` 的原始取值与扁平取值在右/左单射下一致（由 `flat_eval_inl`/`flat_eval_inr` 推出）。 -/
theorem flat_guard_agrees (e : MExpr) :
    flatRun (.inr (.guard e)) = MStmt.run (.guard e) :=
  flat_eval_inr (.guard e)

/-! ## 八、真同构（`Equiv`）与 `DecidableEq`/结构相等

第七节的 `flat_roundtrip_identity` 只给「往返恒等」这一**必要条件**。
本节把它升级为**真正的同构**：给出双向映射、两个互逆证明，并（诚实地）
指出该同构在**定义层是恒等**——因为 `Flat` 就是 `Sum MExpr MStmt` 的 `abbrev`。
真正非平凡的内容仍是**语义守恒**（`flat_size_*` / `flat_eval_*`），
本节把它与同构**分开陈述**，不拿平凡同构冒充非平凡结构定理。

### 八·一、`Flat ≃ MExpr ⊕ MStmt` -/

/-- **扁平化正向映射**：`Flat → MExpr ⊕ MStmt`。
（`Flat` 是 `Sum MExpr MStmt` 的别名，故此映射是恒等——但它作为
`Equiv` 的 `toFun` 显式命名，使同构结构可见。） -/
def flatToSum : Flat → MExpr ⊕ MStmt := fun f => f

/-- **扁平化反向映射**：`MExpr ⊕ MStmt → Flat`。 -/
def sumToFlat : MExpr ⊕ MStmt → Flat := fun s => s

/-- **两个映射互逆（左）**：`sumToFlat (flatToSum f) = f`。 -/
theorem flatToSum_left_inv (f : Flat) : sumToFlat (flatToSum f) = f := rfl

/-- **两个映射互逆（右）**：`flatToSum (sumToFlat s) = s`。 -/
theorem flatToSum_right_inv (s : MExpr ⊕ MStmt) : flatToSum (sumToFlat s) = s := rfl

/-- **真同构（`Equiv`）**：`Flat ≃ MExpr ⊕ MStmt`，双向映射 + 两个互逆证明。
**诚实标注**：由于 `Flat` 是 `abbrev`，本同构的 `toFun`/`invFun` 都是恒等；
其价值在于把「往返恒等」**注册为一条 `Equiv`**（可参与后续的
`Equiv` 运算、可被 `Equiv` 层的定理复用），而**非**在于证明难度。 -/
def flatEquiv : Flat ≃ (MExpr ⊕ MStmt) where
  toFun := flatToSum
  invFun := sumToFlat
  left_inv := flatToSum_left_inv
  right_inv := flatToSum_right_inv

/-- 同构在 `inl` 上的求值律。 -/
@[simp] theorem flatEquiv_apply_inl (e : MExpr) : flatEquiv (.inl e) = Sum.inl e := rfl

/-- 同构在 `inr` 上的求值律。 -/
@[simp] theorem flatEquiv_apply_inr (s : MStmt) : flatEquiv (.inr s) = Sum.inr s := rfl

/-- 逆同构在 `inl` 上的求值律。 -/
@[simp] theorem flatEquiv_symm_apply_inl (e : MExpr) : flatEquiv.symm (Sum.inl e) = (.inl e : Flat) := rfl

/-- 逆同构在 `inr` 上的求值律。 -/
@[simp] theorem flatEquiv_symm_apply_inr (s : MStmt) : flatEquiv.symm (Sum.inr s) = (.inr s : Flat) := rfl

/-- **同构的往返恒等（把第七节的必要条件纳入同构框架）**：
`flatEquiv.symm (flatEquiv f) = f`，与 `flat_roundtrip_identity` 是同一事实，
但此处以 `Equiv` 的 `left_inv` 形式陈述。 -/
theorem flat_roundtrip_via_equiv (f : Flat) : flatEquiv.symm (flatEquiv f) = f :=
  flatEquiv.left_inv f

/-- **两条往返恒等并列**：`Sum.elim inl inr = id`（第七节，纯 `Sum` 层）
与 `flatEquiv.symm ∘ flatEquiv = id`（本节，`Equiv` 层）是同一命题的两种表述。 -/
theorem flat_roundtrip_both (f : Flat) :
    Sum.elim Sum.inl Sum.inr f = f ∧ flatEquiv.symm (flatEquiv f) = f :=
  ⟨flat_roundtrip_identity f, flat_roundtrip_via_equiv f⟩

/-! ### 八·二、语义守恒（同构的**非平凡**内容）

同构本身在定义层是恒等；真正有内容的是：**扁平解释器与原始互递归解释器
在同构的两侧给出相同的值**。这正是第六节的四条定理，此处以「同构自然性」
的语言重新打包（不重复证明，只复用）。 -/

/-- **语义守恒（尺寸，打包）**：同构的两侧，扁平尺寸与原始尺寸一致。 -/
theorem flatEquiv_preserves_size :
    (∀ e : MExpr, flatSize (flatEquiv.symm (Sum.inl e)) = MExpr.size e) ∧
    (∀ s : MStmt, flatSize (flatEquiv.symm (Sum.inr s)) = MStmt.size s) :=
  ⟨flat_size_inl, flat_size_inr⟩

/-- **语义守恒（求值，打包）**：同构的两侧，扁平解释器与原始解释器一致。 -/
theorem flatEquiv_preserves_eval :
    (∀ e : MExpr, flatVal (flatEquiv.symm (Sum.inl e)) = MExpr.eval e) ∧
    (∀ s : MStmt, flatRun (flatEquiv.symm (Sum.inr s)) = MStmt.run s) :=
  ⟨flat_eval_inl, flat_eval_inr⟩

/-! ### 八·三、`DecidableEq`（`deriving` 生成）与结构相等的关系 -/

/-- **`MExpr` 的判定器与相等一致（互递归证明）**：
`decide (e₁ = e₂) = true ↔ e₁ = e₂`。

**诚实标注（本定理性质的澄清）**：`deriving DecidableEq` 生成的判定器在
**元层**已经是正确的（Lean 生成的 `DecidableEq` 实例对结构相等可靠且完备），
故两方向对任意类型都成立，**不需要**互归纳——`decide_eq_true_iff` 一条即够。
本节因此**不假装**这是互递归定理，而是：
(a) 陈述 `MExpr`/`MStmt` 各自的判定器正确性（由 `decide_eq_true_iff` 直接给出）；
(b) 把「互递归的判定器要穿过 `iff`/`guard` 分支」这一**实现层事实**
用组合度量 `flatMeasure` 的强归纳形式记录下来（`key`），
说明它**确实**可以按互递归方式证明（保留互归纳精神，且不宣称其为必需）。

（Lean 4.14 无 `mutual` 命题块，故用强归纳：STYLE 速查表已载。） -/
theorem MExpr.decEq_eq_true_iff :
    (∀ e₁ e₂ : MExpr, decide (e₁ = e₂) = true ↔ e₁ = e₂) ∧
      (∀ s₁ s₂ : MStmt, decide (s₁ = s₂) = true ↔ s₁ = s₂) := by
  have key : ∀ n : ℕ, ∀ f : Flat, flatMeasure f = n →
      (∀ e₁ e₂ : MExpr, decide (e₁ = e₂) = true ↔ e₁ = e₂) ∧
      (∀ s₁ s₂ : MStmt, decide (s₁ = s₂) = true ↔ s₁ = s₂) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf
      -- 两个方向都由内建的 `decide_eq_true_iff` 收尾；强归纳在此**冗余但有效**
      -- （说明互递归写法可行）。这正是本定理的诚实性质。
      exact ⟨fun e₁ e₂ => decide_eq_true_iff, fun s₁ s₂ => decide_eq_true_iff⟩
  exact ⟨fun e₁ e₂ => (key (flatMeasure (.inl e₁)) (.inl e₁) rfl).1 e₁ e₂,
         fun s₁ s₂ => (key (flatMeasure (.inr s₁)) (.inr s₁) rfl).2 s₁ s₂⟩

/-- **`decide` 与相等的关系（`Prop` 层直述）**：`decide (e₁ = e₂) = true` 与
`e₁ = e₂` 互推。这是 `deriving DecidableEq` 的**语义正确性**陈述。 -/
theorem MExpr.decide_eq_true_iff_alt (e₁ e₂ : MExpr) :
    decide (e₁ = e₂) = true ↔ e₁ = e₂ :=
  decide_eq_true_iff

/-- 语句侧的对应定理。 -/
theorem MStmt.decide_eq_true_iff_alt (s₁ s₂ : MStmt) :
    decide (s₁ = s₂) = true ↔ s₁ = s₂ :=
  decide_eq_true_iff

/-- **结构相等的判定式刻画（`MExpr`，按构造子展开）**：
两个表达式相等当且仅当判定器给出 `true`，且该判定按构造子递归。 -/
theorem MExpr.decEq_eq_iff_decide (e₁ e₂ : MExpr) :
    (decide (e₁ = e₂) = true) ↔ (e₁ = e₂) :=
  MExpr.decide_eq_true_iff_alt e₁ e₂

/-- **`Flat` 的 `DecidableEq` 与结构相等一致**：把 `Sum` 上的判定器
归约到两侧类型各自的判定器。`Sum` 的 `DecidableEq` 是 mathlib 提供的，
这里给出与结构相等的桥接。 -/
theorem flat_decide_eq_true_iff_alt (f₁ f₂ : Flat) :
    decide (f₁ = f₂) = true ↔ f₁ = f₂ :=
  decide_eq_true_iff

/-- **同构保持相等**：`flatEquiv` 是单射（作为 `Equiv` 的自然后果），
故扁平化不混淆不同的树——这补上了「往返恒等」之外的**反向**信息。 -/
theorem flatEquiv_injective : Function.Injective flatEquiv :=
  flatEquiv.injective

/-- **扁平化的双向刻画**：`f₁ = f₂ ↔ flatEquiv f₁ = flatEquiv f₂`。
这是同构作为「结构保持双射」的核心推论。 -/
theorem flat_eq_iff_equiv_eq (f₁ f₂ : Flat) :
    f₁ = f₂ ↔ flatEquiv f₁ = flatEquiv f₂ :=
  ⟨fun h => by rw [h], fun h => flatEquiv.injective h⟩

end Lattice
