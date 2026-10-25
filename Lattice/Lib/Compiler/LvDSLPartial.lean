/-
LvDSL 部分函数性质（Lv-00 formal，v1.1 R1）
=========================================

本模块是 _harvest/lv00/lv-merged/lvFormal/Theory/LvDSL.lean 的**可跟踪落点**。

## 为什么需要这个文件（立项理由）

原始 LvDSL.lean 位于 lattice/_harvest/，该目录被 .gitignore 的 /_* 规则忽略，
且不在 lattice/lean/lakefile.toml 的 roots 列表中，全库 **0 个模块 import 它**
（该现状截至本注释订正时仍成立）。因此对它的任何改动都**不构成交付**。

## 落地结果（该立项已闭环）

本模块已把其中已验证的证明体重建到 lattice/lean/ 下，并**已注册进**
lattice/lean/lakefile.toml 的 roots 列表（见该文件 roots 数组中的 "LvDSLPartial"
一项），故构建范围与 #print axioms 审计范围这一目标已经达成：
其三条定理现有 #print axioms 证据（见文件末尾的 #print axioms 命令）。
注意：其本身仍**未被任何其他模块 import**，
全库对它的引用目前仅为 lakefile 的 roots 条目与本文档记载。

## 已验证结论（走锁编译 exit 0 + axioms 干净）

三条定理均为**定义展开**（rfl / Nat.zero_le），证明体不含 sorry、
不含 sorryAx：#print axioms 仅列出 [propext, Classical.choice, Quot.sound]。

## 诚实边界（重要）

原文件中另外 12 条 sorry **不能**通过「去掉 partial」解锁：

1. partial def 无法简单改名为 def —— Lean 报 fail to show termination
   （lv_type_check 在类型参数上模式匹配、lv_free_vars 走高阶 List.bind、
   lv_subst 走 List.map 部分应用，三者的结构递归推断全部失败）。
2. 保留 partial 时，unfold 也**无法**展开 partial 定义
   （实测 tactic 'unfold' failed to unfold ... lv_type_check）。
3. 故凡语句中提及 lv_type_check / lv_subst / lv_free_vars 的引理，
   在两种路线下都不可证，除非先为这些函数补出 termination_by/decreasing_by
   或改写为结构递归版本（属于**函数改写**，不是去化）。

本模块只承载**确实成立**的三条，不冒充已解锁 15 条。
-/

import Mathlib

noncomputable section

namespace lvFormal.Theory.LvDSLPartial

/-! ## 最小复现所需的数据类型（与 LvDSL.lean 同构） -/

/-- 约束声明 -/
structure LvConstraint where
  name : String

/-- 语句 -/
inductive LvStmt where
  | constraintDecl : String → LvConstraint → String → LvStmt
  | prove : String → LvStmt
  | other : String → LvStmt

/-- 完整程序 -/
structure LvProgram where
  name : String
  stmts : List LvStmt

/-- 从 Lv 程序中提取所有约束声明列表（对应 LvDSL.getConstraints） -/
def getConstraints (p : LvProgram) : List LvConstraint :=
  p.stmts.filterMap fun stmt =>
    match stmt with
    | .constraintDecl _ c _ => some c
    | _ => none

/-- 从 Lv 程序中提取 Prove 语句（对应 LvDSL.findProveStmt） -/
def findProveStmt (p : LvProgram) : Option LvStmt :=
  p.stmts.find? fun stmt =>
    match stmt with
    | .prove _ => true
    | _ => false

/-! ## 已验证定理 -/

/-- 空程序不含任何约束。证明体 = 定义展开（filterMap 作用于 []）。 -/
lemma empty_program_no_constraints : getConstraints (⟨"", []⟩ : LvProgram) = [] := by rfl

/-- 空程序没有 Prove 语句。证明体 = 定义展开（find? 作用于 []）。 -/
lemma empty_program_no_prove : findProveStmt (⟨"", []⟩ : LvProgram) = none := by rfl

/-- 约束列表长度非负。证明体 = Nat.zero_le（不涉及任何定义展开）。 -/
lemma getConstraints_length_nonneg (p : LvProgram) : 0 ≤ (getConstraints p).length := by
  exact Nat.zero_le _

end lvFormal.Theory.LvDSLPartial

#print axioms lvFormal.Theory.LvDSLPartial.empty_program_no_constraints
#print axioms lvFormal.Theory.LvDSLPartial.empty_program_no_prove
#print axioms lvFormal.Theory.LvDSLPartial.getConstraints_length_nonneg
