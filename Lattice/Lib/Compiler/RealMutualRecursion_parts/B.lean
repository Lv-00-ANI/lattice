import Mathlib
import Lattice.Lib.Compiler.RealMutualRecursion_parts.A

/-!
# `RealMutualRecursion.lean` 的 `B` 部分

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
