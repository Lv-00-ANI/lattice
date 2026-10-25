

import Lattice.Lib.Compiler.RealMutualRecursion_parts.A
import Lattice.Lib.Compiler.RealMutualRecursion_parts.B
import Lattice.Lib.Compiler.RealMutualRecursion_parts.C


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
