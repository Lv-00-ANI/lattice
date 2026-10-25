import Mathlib
import Lattice.Lib.Compiler.RealLv00CompilerSpec
/-! # RealLv00CompilerSat

拆分自 `RealLv00Compiler.lean`（第 969–1233 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Compiler` 仍有效。

本模块重新声明了原文件的模块级设置：`noncomputable section`（原 :72）与
`namespace Lattice.Lv00.Compiler`（原 :74）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Compiler

/-! ## 六、(A) 图可满足性的拼合 —— 本包唯一「像编译器正确性」的真结果

原 `CompilerCorrectness.lean` §「变量集不相交性」。这一节是真结果：
它证明了**两个变量不相交的程序，其编译结果的可满足性可以拼合**——
这是「模块化编译」的正确性骨架（依赖 `ir_sem_depends_on_vars` 与来源追踪）。 -/

/-- **(A) 程序引用的变量集**。 -/
def vars_of_program (prog : lvProgram) : List String :=
  let point_names := prog.flatMap (fun st => match st with | .point p => [p.name] | _ => [])
  let constraint_args := prog.flatMap (fun st => match st with | .constraint c => c.args | _ => [])
  point_names ++ constraint_args

/-- **(A) 两程序变量集不相交**。 -/
def variables_disjoint (p1 p2 : lvProgram) : Prop :=
  (∀ v, v ∈ vars_of_program p1 → v ∉ vars_of_program p2) ∧
  (∀ v, v ∈ vars_of_program p2 → v ∉ vars_of_program p1)

/-- **(A) 编译产物的变量都来自源约束的 args**：12 个 kind × arity 穷举，非平凡。

证明策略：按 `compile_constraint [] c` 的**结果形状**分派。
每个命中分支中 `ir` 的形状由 `h` 唯一确定（`injection` + `subst`），于是 `ir_vars ir`
显式可算，`v ∈ ir_vars ir` 直接给出 `v ∈ c.args`（`args` 的形状也被同一分支固定）。

**注意 修法记录（F3）**：原实现用 `first | (cases h; simp_all [ir_vars, ir_expr_vars]) | (simp [compile_constraint] at h)`，
与 `compile_constraint_degenerately_satisfied` **同一根因**（`cases h` 对局部假设 `ir` 朝错误方向消去 +
`first` 静默接受"成功但不闭合"分支），报 12 条 `unsolved goals`。
现改为 `injection h with h'` + `subst h'` 后 `simp only [ir_vars, ir_expr_vars]` **显式闭合**。 -/
theorem compiled_ir_vars_subset_args (c : lvConstraint) (ir : IRConstraint)
    (h : compile_constraint [] c = some ir) (v : String) (hv : v ∈ ir_vars ir) :
    v ∈ c.args := by
  -- 同 F3 教训：收尾**写进每个 arm 内部**（尾部 `<;>` 不作用于前面 arm 的目标）。
  obtain ⟨_, kind, args⟩ := c
  cases kind with
  | collinear =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil =>
            · simp only [compile_constraint] at h
              injection h with h'
              subst h'
              simp_all [ir_vars, ir_expr_vars]
          | cons _ _ => simp [compile_constraint] at h
  | parallel =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                simp_all [ir_vars, ir_expr_vars]
            | cons _ _ => simp [compile_constraint] at h
  | perpendicular =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                simp_all [ir_vars, ir_expr_vars]
            | cons _ _ => simp [compile_constraint] at h
  | distance =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil =>
          · simp only [compile_constraint] at h
            injection h with h'
            subst h'
            simp_all [ir_vars, ir_expr_vars]
        | cons _ _ => simp [compile_constraint] at h
  | angle =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                simp_all [ir_vars, ir_expr_vars]
            | cons _ _ => simp [compile_constraint] at h
  | midpoint =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil =>
            · simp only [compile_constraint] at h
              injection h with h'
              subst h'
              simp_all [ir_vars, ir_expr_vars]
          | cons _ _ => simp [compile_constraint] at h
  | rightAngle =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil =>
            · simp only [compile_constraint] at h
              injection h with h'
              subst h'
              simp_all [ir_vars, ir_expr_vars]
          | cons _ _ => simp [compile_constraint] at h
  | equalLength =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                simp_all [ir_vars, ir_expr_vars]
            | cons _ _ => simp [compile_constraint] at h
  | equalAngle =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil => simp [compile_constraint] at h
            | cons a5 r5 => cases r5 with
              | nil => simp [compile_constraint] at h
              | cons a6 r6 => cases r6 with
                | nil =>
                  · simp only [compile_constraint] at h
                    injection h with h'
                    subst h'
                    simp_all [ir_vars, ir_expr_vars]
                | cons _ _ => simp [compile_constraint] at h
  | radius =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil =>
          · simp only [compile_constraint] at h
            injection h with h'
            subst h'
            simp_all [ir_vars, ir_expr_vars]
        | cons _ _ => simp [compile_constraint] at h
  | tangent =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                simp_all [ir_vars, ir_expr_vars]
            | cons _ _ => simp [compile_constraint] at h
  | ratioDivision =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil =>
            · simp only [compile_constraint] at h
              injection h with h'
              subst h'
              simp_all [ir_vars, ir_expr_vars]
          | cons _ _ => simp [compile_constraint] at h
/-- **(A) 约束参数都在程序的变量集中**。 -/
theorem constraint_args_mem_vars (p : lvProgram) (c : lvConstraint)
    (hc : c ∈ constraints_of_program p) (v : String) (hv : v ∈ c.args) :
    v ∈ vars_of_program p := by
  unfold vars_of_program
  rw [List.mem_append]; right
  unfold constraints_of_program at hc
  rcases List.mem_flatMap.mp hc with ⟨st, hst, hmem⟩
  cases st with
  | constraint c' =>
      have hceq : c = c' := by simpa using hmem
      subst c'
      exact List.mem_flatMap.mpr ⟨.constraint c, hst, hv⟩
  | point _ => simp at hmem
  | prove => simp at hmem
  | normalize => simp at hmem

/-- **(A) 编译产生的 IR 约束只引用源程序中对应的变量**。 -/
theorem compile_program_vars_subset (p : lvProgram) (ir : IRConstraint)
    (h : ir ∈ compile_program p) (v : String) (hv : v ∈ ir_vars ir) :
    v ∈ vars_of_program p := by
  rcases compile_program_contains_compiled_constraints p ir h with ⟨c, hc, hcc⟩
  exact constraint_args_mem_vars p c hc v (compiled_ir_vars_subset_args c ir hcc v hv)

/-- **(A) 变量不相交时编译结果可拼合**：
这是本包**唯一的「模块化编译正确性」真结果**——
`compile p1` 与 `compile p2` 各自可满足 ⟹ `compile (p1 ++ p2)` 可满足。
证明用 `compile_program_append` + `ir_sem_depends_on_vars` 构造「分片环境」。 -/
theorem compile_append_satisfiable (p1 p2 : lvProgram) (h_disjoint : variables_disjoint p1 p2)
    (h1 : graph_satisfiable (compile_program p1))
    (h2 : graph_satisfiable (compile_program p2)) :
    graph_satisfiable (compile_program (p1 ++ p2)) := by
  rw [compile_program_append]
  rcases h1 with ⟨env1, hsat1⟩
  rcases h2 with ⟨env2, hsat2⟩
  let env : String → ℝ × ℝ := fun v => if v ∈ vars_of_program p1 then env1 v else env2 v
  refine ⟨env, ?_⟩
  intro ir hir
  rw [List.mem_append] at hir
  rcases hir with hir | hir
  · have hsame : ∀ v, v ∈ ir_vars ir → env v = env1 v := by
      intro v hv
      have hv1 := compile_program_vars_subset p1 ir hir v hv
      simp [env, hv1]
    exact (ir_sem_depends_on_vars ir env env1 hsame).mpr (hsat1 ir hir)
  · have hsame : ∀ v, v ∈ ir_vars ir → env v = env2 v := by
      intro v hv
      have hv2 := compile_program_vars_subset p2 ir hir v hv
      have hvne : v ∉ vars_of_program p1 := h_disjoint.2 v hv2
      simp [env, hvne]
    exact (ir_sem_depends_on_vars ir env env2 hsame).mpr (hsat2 ir hir)


end Lattice.Lv00.Compiler
