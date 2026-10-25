import Mathlib
import Lattice.Lib.Compiler.RealLv00CompilerCodegen
/-! # RealLv00CompilerReal

拆分自 `RealLv00Compiler.lean`（第 370–645 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Compiler` 仍有效。

本模块重新声明了原文件的模块级设置：`noncomputable section`（原 :72）与
`namespace Lattice.Lv00.Compiler`（原 :74）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Compiler

/-! ## 四、(A) 真结果 —— 证明体实质的条目

本节是真结果：结构归纳、变量依赖性、来源追踪、图可满足性胶合。
它们是本采集包**最可复用**的部分。 -/

/-- **(B)** 空程序编译为空图。原为 `theorem compile_empty … := rfl`，平凡。
保留作为接口锚点。 -/
theorem compile_empty : compile_program ([] : lvProgram) = ([] : CompilerConstraintGraph) := rfl

/-- **(A) 编译结果与点列表参数无关**。
原文 `compile_constraint_ps_irrelevant`（`funext` + `rfl`）。
**这条定理本身就是 §7 降级 D5 的证据**：源程序的点信息**完全没有进入编译产物**，
所以「编译」实质上是**逐语句的无状态重写**，而非真正的 lowering。 -/
theorem compile_constraint_ps_irrelevant (ps1 ps2 : List lvPoint) :
    compile_constraint ps1 = compile_constraint ps2 := by
  funext c; rfl

/-- **(A) 语句编译与点列表无关**（对 `compile_constraint_ps_irrelevant` 的分派）。 -/
theorem compile_stmt_ps_irrelevant (ps1 ps2 : List lvPoint) (st : lvStmt) :
    compile_stmt st ps1 = compile_stmt st ps2 := by
  unfold compile_stmt
  cases st with
  | point p => rfl
  | constraint c => rw [compile_constraint_ps_irrelevant ps1 ps2]
  | prove => rfl
  | normalize => rfl

/-- **(A) 程序编译与初始点列表无关**：结构归纳，非平凡。 -/
theorem compile_program_go_ps_irrelevant (ps1 ps2 : List lvPoint) (prog : lvProgram) :
    compile_program_go ps1 prog = compile_program_go ps2 prog := by
  induction prog generalizing ps1 ps2 with
  | nil => rfl
  | cons st sts ih =>
      cases st with
      | point p =>
          show compile_stmt (.point p) ps1 ++ compile_program_go (p :: ps1) sts =
               compile_stmt (.point p) ps2 ++ compile_program_go (p :: ps2) sts
          rw [compile_stmt_ps_irrelevant ps1 ps2, ih (p :: ps1) (p :: ps2)]
      | constraint c =>
          show compile_stmt (.constraint c) ps1 ++ compile_program_go ps1 sts =
               compile_stmt (.constraint c) ps2 ++ compile_program_go ps2 sts
          rw [compile_stmt_ps_irrelevant ps1 ps2, ih ps1 ps2]
      | prove =>
          show compile_stmt .prove ps1 ++ compile_program_go ps1 sts =
               compile_stmt .prove ps2 ++ compile_program_go ps2 sts
          rw [compile_stmt_ps_irrelevant ps1 ps2, ih ps1 ps2]
      | normalize =>
          show compile_stmt .normalize ps1 ++ compile_program_go ps1 sts =
               compile_stmt .normalize ps2 ++ compile_program_go ps2 sts
          rw [compile_stmt_ps_irrelevant ps1 ps2, ih ps1 ps2]

/-- **(A) `compile_program_go` 对拼接的分配律**（带初始点列表参数）。 -/
theorem compile_program_go_append (ps : List lvPoint) (p1 p2 : lvProgram) :
    compile_program_go ps (p1 ++ p2) =
      compile_program_go ps p1 ++ compile_program_go ps p2 := by
  induction p1 generalizing ps with
  | nil => simp [compile_program_go]
  | cons st rest ih =>
      cases st with
      | point p =>
          show compile_stmt (.point p) ps ++ compile_program_go (p :: ps) (rest ++ p2) =
               (compile_stmt (.point p) ps ++ compile_program_go (p :: ps) rest) ++
                 compile_program_go ps p2
          rw [ih (p :: ps), compile_program_go_ps_irrelevant (p :: ps) ps p2]
          simp [List.append_assoc]
      | constraint c =>
          show compile_stmt (.constraint c) ps ++ compile_program_go ps (rest ++ p2) =
               (compile_stmt (.constraint c) ps ++ compile_program_go ps rest) ++
                 compile_program_go ps p2
          rw [ih ps]
          simp [List.append_assoc]
      | prove =>
          show compile_stmt .prove ps ++ compile_program_go ps (rest ++ p2) =
               (compile_stmt .prove ps ++ compile_program_go ps rest) ++ compile_program_go ps p2
          rw [ih ps]
          simp [List.append_assoc]
      | normalize =>
          show compile_stmt .normalize ps ++ compile_program_go ps (rest ++ p2) =
               (compile_stmt .normalize ps ++ compile_program_go ps rest) ++
                 compile_program_go ps p2
          rw [ih ps]
          simp [List.append_assoc]
/-- **(A) 程序拼接的编译分配律**：`compile (p1 ++ p2) = compile p1 ++ compile p2`。 -/
theorem compile_program_append (p1 p2 : lvProgram) :
    compile_program (p1 ++ p2) = compile_program p1 ++ compile_program p2 := by
  unfold compile_program
  exact compile_program_go_append [] p1 p2

/-- **(A) IR 表达式变量集**。 -/
def ir_expr_vars : IRExpr → List String
  | .var v => [v]
  | .const _ => []
  | .add e1 e2 => ir_expr_vars e1 ++ ir_expr_vars e2
  | .sub e1 e2 => ir_expr_vars e1 ++ ir_expr_vars e2
  | .mul e1 e2 => ir_expr_vars e1 ++ ir_expr_vars e2
  | .div e1 e2 => ir_expr_vars e1 ++ ir_expr_vars e2
  | .sqrt e => ir_expr_vars e

/-- **(A) IR 约束变量集**。 -/
def ir_vars : IRConstraint → List String
  | .distance a b d => [a, b] ++ ir_expr_vars d
  | .collinear a b c => [a, b, c]
  | .perpendicular a b c d => [a, b, c, d]
  | .parallel a b c d => [a, b, c, d]
  | .angle a b c d theta => [a, b, c, d] ++ ir_expr_vars theta
  | .midpoint m a b => [m, a, b]
  | .rightAngle a b c => [a, b, c]
  | .equalLength a b c d => [a, b, c, d]
  | .equalAngle a b c d e f => [a, b, c, d, e, f]
  | .radius c a r => [c, a] ++ ir_expr_vars r
  | .tangent ctr pt la lb => [ctr, pt, la, lb]
  | .ratioDivision p a b r => [p, a, b] ++ ir_expr_vars r
  | .eq_expr e1 e2 => ir_expr_vars e1 ++ ir_expr_vars e2
  | .lt_expr e1 e2 => ir_expr_vars e1 ++ ir_expr_vars e2
  | .gt_expr e1 e2 => ir_expr_vars e1 ++ ir_expr_vars e2

/-- **(A) 表达式求值只依赖其变量集**：结构归纳，非平凡。原 `eval_expr_depends_on_vars`。 -/
theorem eval_expr_depends_on_vars (e : IRExpr) (env1 env2 : String → ℝ × ℝ)
    (h : ∀ v, v ∈ ir_expr_vars e → env1 v = env2 v) :
    eval_expr env1 e = eval_expr env2 e := by
  induction e with
  | var v => rw [eval_expr, h v (by simp [ir_expr_vars]), eval_expr]
  | const c => simp [eval_expr]
  | add e1 e2 ih1 ih2 =>
      have h1 := ih1 (fun v hv => h v (by simp [ir_expr_vars, hv]))
      have h2 := ih2 (fun v hv => h v (by simp [ir_expr_vars, hv]))
      simp [eval_expr, h1, h2]
  | sub e1 e2 ih1 ih2 =>
      have h1 := ih1 (fun v hv => h v (by simp [ir_expr_vars, hv]))
      have h2 := ih2 (fun v hv => h v (by simp [ir_expr_vars, hv]))
      simp [eval_expr, h1, h2]
  | mul e1 e2 ih1 ih2 =>
      have h1 := ih1 (fun v hv => h v (by simp [ir_expr_vars, hv]))
      have h2 := ih2 (fun v hv => h v (by simp [ir_expr_vars, hv]))
      simp [eval_expr, h1, h2]
  | div e1 e2 ih1 ih2 =>
      have h1 := ih1 (fun v hv => h v (by simp [ir_expr_vars, hv]))
      have h2 := ih2 (fun v hv => h v (by simp [ir_expr_vars, hv]))
      simp [eval_expr, h1, h2]
  | sqrt e ih =>
      have h1 := ih (fun v hv => h v (by simp [ir_expr_vars, hv]))
      simp [eval_expr, h1]

/-- **(A) `ir_sem` 只依赖 `ir_vars` 中列出的变量**：15 个构造子逐 case，
每个 case 用 `eval_expr_depends_on_vars`。原 `ir_sem_depends_on_vars`，是真结果。 -/
theorem ir_sem_depends_on_vars (ir : IRConstraint) (env1 env2 : String → ℝ × ℝ)
    (h : ∀ v, v ∈ ir_vars ir → env1 v = env2 v) : ir_sem env1 ir ↔ ir_sem env2 ir := by
  induction ir with
  | distance a b d =>
      have ha := h a (by simp [ir_vars]); have hb := h b (by simp [ir_vars])
      have hd := eval_expr_depends_on_vars d _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      simp [ir_sem, ha, hb, hd]
  | collinear a b c =>
      have ha := h a (by simp [ir_vars]); have hb := h b (by simp [ir_vars])
      have hc := h c (by simp [ir_vars])
      simp [ir_sem, ha, hb, hc]
  | perpendicular a b c d =>
      have ha := h a (by simp [ir_vars]); have hb := h b (by simp [ir_vars])
      have hc := h c (by simp [ir_vars]); have hd := h d (by simp [ir_vars])
      simp [ir_sem, ha, hb, hc, hd]
  | parallel a b c d =>
      have ha := h a (by simp [ir_vars]); have hb := h b (by simp [ir_vars])
      have hc := h c (by simp [ir_vars]); have hd := h d (by simp [ir_vars])
      simp [ir_sem, ha, hb, hc, hd]
  | angle a b c d theta =>
      have ha := h a (by simp [ir_vars]); have hb := h b (by simp [ir_vars])
      have hc := h c (by simp [ir_vars]); have hd := h d (by simp [ir_vars])
      have ht := eval_expr_depends_on_vars theta _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      simp [ir_sem, ha, hb, hc, hd, ht]
  | eq_expr e1 e2 =>
      have h1 := eval_expr_depends_on_vars e1 _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      have h2 := eval_expr_depends_on_vars e2 _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      simp [ir_sem, h1, h2]
  | lt_expr e1 e2 =>
      have h1 := eval_expr_depends_on_vars e1 _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      have h2 := eval_expr_depends_on_vars e2 _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      simp [ir_sem, h1, h2]
  | gt_expr e1 e2 =>
      have h1 := eval_expr_depends_on_vars e1 _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      have h2 := eval_expr_depends_on_vars e2 _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      simp [ir_sem, h1, h2]
  | radius c a r =>
      have hc := h c (by simp [ir_vars]); have ha := h a (by simp [ir_vars])
      have hr := eval_expr_depends_on_vars r _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      simp [ir_sem, hc, ha, hr]
  | tangent ctr pt la lb =>
      have h1 := h ctr (by simp [ir_vars]); have h2 := h pt (by simp [ir_vars])
      have h3 := h la (by simp [ir_vars]); have h4 := h lb (by simp [ir_vars])
      simp [ir_sem, h1, h2, h3, h4]
  | midpoint m a b =>
      have hm := h m (by simp [ir_vars]); have ha := h a (by simp [ir_vars])
      have hb := h b (by simp [ir_vars])
      simp [ir_sem, hm, ha, hb]
  | rightAngle a b c =>
      have ha := h a (by simp [ir_vars]); have hb := h b (by simp [ir_vars])
      have hc := h c (by simp [ir_vars])
      simp [ir_sem, ha, hb, hc]
  | equalLength a b c d =>
      have ha := h a (by simp [ir_vars]); have hb := h b (by simp [ir_vars])
      have hc := h c (by simp [ir_vars]); have hd := h d (by simp [ir_vars])
      simp [ir_sem, ha, hb, hc, hd]
  | equalAngle a b c d e f =>
      have ha := h a (by simp [ir_vars]); have hb := h b (by simp [ir_vars])
      have hc := h c (by simp [ir_vars]); have hd := h d (by simp [ir_vars])
      have he := h e (by simp [ir_vars]); have hf := h f (by simp [ir_vars])
      simp [ir_sem, ha, hb, hc, hd, he, hf]
  | ratioDivision p a b r =>
      have hp := h p (by simp [ir_vars]); have ha := h a (by simp [ir_vars])
      have hb := h b (by simp [ir_vars])
      have hr := eval_expr_depends_on_vars r _ _ (fun v hv => h v (by simp [ir_vars, hv]))
      simp [ir_sem, hp, ha, hb, hr]

/-- **(A) 程序约束集提取**。 -/
def constraints_of_program (prog : lvProgram) : List lvConstraint :=
  prog.flatMap (fun st => match st with | .constraint c => [c] | _ => [])

/-- **(A) 辅助**：`constraints_of_program` 对 `cons` 的展开（逐语句 case）。 -/
theorem constraints_of_program_cons_point (p : lvPoint) (sts : lvProgram) :
    constraints_of_program (.point p :: sts) = constraints_of_program sts := by
  simp [constraints_of_program]

theorem constraints_of_program_cons_constraint (c : lvConstraint) (sts : lvProgram) :
    constraints_of_program (.constraint c :: sts) = c :: constraints_of_program sts := by
  simp [constraints_of_program]

theorem constraints_of_program_cons_prove (sts : lvProgram) :
    constraints_of_program (.prove :: sts) = constraints_of_program sts := by
  simp [constraints_of_program]

theorem constraints_of_program_cons_normalize (sts : lvProgram) :
    constraints_of_program (.normalize :: sts) = constraints_of_program sts := by
  simp [constraints_of_program]

/-- **(A) 编译产物的来源追踪**：`compile_program_go` 的每个输出都来自源程序某条约束的编译。
结构归纳（4 个语句 case），是真结果。 -/
theorem compile_program_go_contains (pts : List lvPoint) (prog : lvProgram) :
    ∀ ir ∈ compile_program_go pts prog,
      ∃ c ∈ constraints_of_program prog, compile_constraint [] c = some ir := by
  induction prog generalizing pts with
  | nil => intro ir hir; simp [compile_program_go] at hir
  | cons st sts ih =>
      intro ir hir
      cases st with
      | point p =>
          simp only [compile_program_go, compile_stmt, List.nil_append] at hir
          rcases ih (p :: pts) ir hir with ⟨c, hc, hcc⟩
          exact ⟨c, by rw [constraints_of_program_cons_point]; exact hc, hcc⟩
      | constraint c =>
          simp only [compile_program_go, compile_stmt, List.mem_append] at hir
          rcases hir with hir | hir
          · -- ir came from compiling c itself
            cases hc0 : compile_constraint pts c with
            | none => simp [hc0] at hir
            | some ir' =>
                have hir' : ir = ir' := by simpa [hc0] using hir
                subst hir'
                exact ⟨c, by rw [constraints_of_program_cons_constraint]; exact List.mem_cons_self c _, by
                  rw [congrFun (compile_constraint_ps_irrelevant [] pts) c]; exact hc0⟩
          · -- ir came from the tail
            rcases ih pts ir hir with ⟨c', hc', hcc'⟩
            exact ⟨c', by rw [constraints_of_program_cons_constraint]; exact List.mem_cons_of_mem _ hc', hcc'⟩
      | prove =>
          simp only [compile_program_go, compile_stmt, List.nil_append] at hir
          rcases ih pts ir hir with ⟨c, hc, hcc⟩
          exact ⟨c, by rw [constraints_of_program_cons_prove]; exact hc, hcc⟩
      | normalize =>
          simp only [compile_program_go, compile_stmt, List.nil_append] at hir
          rcases ih pts ir hir with ⟨c, hc, hcc⟩
          exact ⟨c, by rw [constraints_of_program_cons_normalize]; exact hc, hcc⟩

/-- **(A) 编译后的 IR 约束都来自源程序约束的编译**。 -/
theorem compile_program_contains_compiled_constraints (prog : lvProgram) :
    ∀ ir ∈ compile_program prog, ∃ c ∈ constraints_of_program prog,
      compile_constraint [] c = some ir :=
  compile_program_go_contains [] prog


end Lattice.Lv00.Compiler
