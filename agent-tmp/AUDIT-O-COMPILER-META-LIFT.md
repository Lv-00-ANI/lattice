# LATTICE 只读审计 · 子代理 O
## Lib/Compiler + Lib/Meta + Lib/Lift

- 基线：HEAD = `66fd8ec41105ac051da11a1c57f5d583b75122d1`
- 范围：`Lattice/Lib/Compiler/`(48) + `Lattice/Lib/Meta/`(8) + `Lattice/Lib/Lift/`(11) = **67 文件**
- 纪律：**纯只读**。未写任何源文件、未构建、未跑 gate/脚本、未提交。
  （本报告落在 `agent-tmp/`，不在 `Lattice/` 源码树内。）
- 全范围 `sorry` / `axiom` / `admit` 实测 **0 处**（正则全扫 67 文件）。

---

## 〇、对账先行：声明数与给定基线

| 目录 | 文件数 | 给定 theorem | **实测 theorem** | 给定总 | **实测总** |
|:--|--:|--:|--:|--:|--:|
| Compiler | 48 ✓ | 651 | **635** | 651 | **651**（thm 635 + lemma 16） |
| Meta | 8 ✓ | — | 109 | 119 | **120**（thm 109 + lemma 11） |
| Lift | 11 ✓ | — | 88 | 92 | **92**（thm 88 + lemma 4） |
| **合计** | **67 ✓** | | **832** | 862 | **863** |

**结论：文件数与 Compiler 总数、Lift 总数完全吻合。两处需订正：**

1. **Compiler "651 定理" 其实是宽口径**：651 = 635 `theorem` + **16 `lemma`**。
   若按字段字面「651 theorem」读，**多算 16 条**（多出 100% 来自 lemma 混入）。
2. **Meta 实测 120，给定 119，差 +1**。已逐名核对无重复计数，判定为**给定基线漏记 1 条**。

实测 863 条中 **832 条 `theorem` + 31 条 `lemma`**，全部计入下文逐条判定。

---

## 一、全量索引（逐文件，67 文件 / 863 条）

判定码：**S** 实质数学内容 · **G** 类定义桥接/形式化骨架 · **C** 纯对账/别名/复述 ·
**A** 证伪钉/反例（本身为真） · **K** 翻译包装（把既有定理换名/特化） · **P** 第5章定性（保语义/RH）
· **W** 纯空洞降级（结论退化） · **N** 0 定理的说明性文件 · **D** 声明与事实不符
· **X** 删除/否定边界（被删命题的否证） · **T** 玩具（成立但语言为玩具、不可连真实对象）

### Compiler（48 文件 / 651）

| 文件 | 条数 | 判定分布 |
|:--|--:|:--|
| `Combinators.lean` | 7 | S×4 (`andC_eq_zero_iff`,`orC_eq_zero_iff`,`and_comm_preserves`,`or_comm_preserves`) + G×3 (`dist_preserves`,`and_assoc_preserves`,`or_assoc_preserves`) |
| `CombinatorsXorNot.lean` | 17 | S×12 / A×2 (`xorC_offdomain_counterexample`,`notC_offdomain_counterexample`) / X×2 (`no_xorC_universal_without_domain`,`notC_ne_xorC_one_counterexample`) / T×1 (`xorC_value_table_on_bool`) |
| `Disjunction.lean` | 3 | S×3（含 lemma `prod_eq_zero_iff_exists`） |
| `Inequality.lean` | 5 | S×4 / X×1 (`sq_pos_of_ne`) |
| `LvDSLPartial.lean` | 3 (all lemma) | W×3（`empty_program_no_constraints`/`no_prove` 皆 `= by rfl`；`length_nonneg` 是 `Nat.zero_le`） |
| `ModConstraint.lean` | 13 | S×12（含 5 条整除 lemma）/ X×1 (`congruent_mod_neg_one`) |
| `RealAbstractInterpretation.lean` | 38 | S×30 / G×4 (`galoisMem_intro`,`galoisMem_pointwise`,`alpha_monotone`,`gamma_monotone`) / A×5 / X×2 (`lv00RoundDownHere_fails_lower_bound`,`roundDownSharp_identity_not_sound`) —— 见 §六.2 两处「结论弱于 docstring」 |
| `RealBetaConfluence.lean` | 28 | S×20 / A×4 (`par_T_not_step_T`,`omega_no_normal_form`,`lift_betaSubst_fails`,`no_lift_betaSubst_law`) / G×4 (`parStar_refl/single/trans/head`) |
| `RealBetaReduction.lean` | 26 | S×20 / A×4 (`diamond_fails`,`step_T_U`,`step_T_V`,`step_redV`) / G×2 (`star_refl`,`star_single`) |
| `RealBigStepSmallStep.lean` | 18 | S×16 / G×2 (`star_from_skip`,`skip_no_step`) |
| `RealBoolCompleteness.lean` | 19 | S×17 / G×2 (`impl_expressible`,`eval_congr`) |
| `RealCombinators.lean` | 24 | S×20 / G×2 / A×2 (`real_xorC_offdomain_counterexample`,`real_notC_ne_real_xorC_one_counterexample`) |
| `RealCompileFloatCorrectness.lean` | 23 | S×18 / T×5（`numOps_*`×5，`= rfl`）—— **主定理 `compile_error_bound` 见 §五.1** |
| `RealCompilerCorrectness.lean` | 7 | S×4 (`run_append`,`compile_correct`,`compile_correct_empty`,`literalFold_eval`) / X×2 (`compile_not_injective`,`compile_not_optimal`) / G×1 (`compile_not_identity`) |
| `RealCompilerOpt.lean` | 18 | S×16 / G×2 (`mem_deadElim`,`mem_cse`) |
| `RealConcurrentSemantics.lean` | 11 | S×9 / G×2 (`run_append`,`interleaving_length`) |
| `RealConstraintSat.lean` | 13 | S×11 / G×2 (`qSat_unfold`,`qSatisfiableOn_iff` 皆 `Iff.rfl`) |
| `RealContinuationEquivalence.lean` | 5 | S×4 / G×1 (`obsEq_iff_eval_eq`) |
| `RealEffectOrdering.lean` | 14 | S×12 / G×1 (`commute_refl` = `rfl`) / **D×1** (`commute_of_commute_fn`，见 §六.3) |
| `RealFirstOrderLogic.lean` | 32 | S×28 / A×2 (`finite_domain_compactness_fails`,`no_finite_model_for_all`) / G×2 |
| `RealGlobalConfluence.lean` | 10 | S×8 / G×2 (`star_single`,`star_trans`) |
| `RealLambdaCalculus.lean` | 20 | S×20 |
| `RealLv00Compiler.lean` | **0** | **N**（131 行纯 docstring 门面，re-export 7 子模块） |
| `RealLv00CompilerCodegen.lean` | **0** | **N**（见 §四，**Codegen = 0 定理**） |
| `RealLv00CompilerHonesty.lean` | 10 | A×7（D1/D1'/D2'/D2''/D4/D5/D6）/ W×2（`D3_angle_compiles_to_tautology`,`D3_angle_placeholder_always_true` 皆 `rfl`）/ K×1 |
| `RealLv00CompilerIR.lean` | 1 | G×1 (`empty_graph_satisfiable`) |
| `RealLv00CompilerLanguage.lean` | **0** | **N**（纯语法/语义定义，见 §四） |
| `RealLv00CompilerReal.lean` | 14 | S×7 / **A×4**（`compile_constraint_ps_irrelevant` 等：把「点信息从未进入编译」做成定理）/ G×4 (`constraints_of_program_cons_*` 全 `simp`) / W×1 (`compile_empty` = `rfl`) |
| `RealLv00CompilerSat.lean` | 4 | S×3 / G×1 (`compiled_ir_vars_subset_args`，12×arity 穷举但纯 `simp_all`) |
| `RealLv00CompilerSpec.lean` | 19 | **W×14**（`degenerate_*`×11 + `compile_constraint_degenerately_satisfied` + `compile_bridge_sem` + `compile_preserves_satisfiability`）/ G×4（`stmt_compiled_edge_correct_*`，**3 条是 `rfl`**）/ **A×1**（`compile_preserves_satisfiability_hypothesis_unused` — 全包最有价值的诚实钉） |
| `RealMutualRecursion.lean` | **0** | **N**（38 行门面） |
| `RealMutualRecursion_parts\A.lean` | 13 | S×13（互递归尺寸下降 + 终止打包） |
| `RealMutualRecursion_parts\B.lean` | **0** | **N**（149 行，仅 import + 复制的 docstring） |
| `RealMutualRecursion_parts\C.lean` | 30 | S×22 / G×4 (`flat_size_lit`,`eval_lit_zero`,`flat_run_skip`,`flat_guard_agrees`) / C×4（`flatEquiv_*` 系列，见 §六.4） |
| `RealNonlinearCompile.lean` | 13 | S×10 / A×1 (`linearization_global_fails`) / G×2 (`*_solution_set`) |
| `RealRecursiveSemantics.lean` | 13 | S×12 / G×1 (`recFwd_succ` = `rfl`) |
| `RealRefinementCalculus.lean` | 17 | S×12 / G×3 (`refines_iff`,`refines_refl`=`rfl`,`refines_mono`) / A×1 (`lv00_style_fidelity_is_trivial`) / P×1 (`fidelity_spec_step`) |
| `RealRegisterAllocation.lean` | 8 | S×5 / G×1 (`triangle_three_colorable`，显式 `⟨id, …⟩`) / T×2（见 §六.5：`loop_lower_bound`/`spill_required` 的载体是抽象图） |
| `RealSatComplete.lean` | 12 | S×9 / G×3 (`search_sound`,`search_complete`,`search_terminates` — 三者都是 `iff` 的直接方向，`search_terminates` 仅 `cases … <;> simp`） |
| `RealSemanticsPreservation.lean` | 13 | S×11 / G×1 (`sim_id`) / A×1 (`forward_not_backward`) |
| `RealTreeDecidable.lean` | 19 | S×17 / G×2 (`decEq_self`,`decEq_dite`) |
| `RealTreeRecursion.lean` | 23 | S×23 |
| `RealTypeSoundness.lean` | 9 | S×9（`progress`/`preservation` 完整无退化） |
| `RealTypeSoundnessSTLC.lean` | 17 | S×15 / A×2 (`stuckTm_is_stuck`,`progress_needs_closed`) / G×2 (`value_not_var`,`value_not_app`) |
| `RealTypeSystemExt.lean` | 12 | S×12 |
| `RealWhileTotalCorrectness.lean` | 14 | S×14 |
| `RealWP.lean` | 15 | S×9 / G×6（`exec_ite_*`, `wp_assign`,`wp_composition`,`wp_and` 皆 `Iff.rfl`/`rfl`） |
| `RealWPWhile.lean` | 20 | S×18 / G×2 (`whileApprox_zero`=`Iff.rfl`,`whileApprox_succ_eq_whileF`=`rfl`) |

**Compiler 汇总**：S≈**393** · G≈**75** · A/X≈**47** · W≈**19** · N=**5 文件** · D=**1** · C=4 · T=8 · K=1 · P=1

### Meta（8 文件 / 120）

| 文件 | 条数 | 判定分布 |
|:--|--:|:--|
| `RealCounterexamples.lean` | 28 | S×20 / K×6（`cex_ce_not_joint_convex` 等 wrapper）/ A×2（`cex_ce_zero_iff_eq_false`,`cex_silu_not_global_lipschitz_false`） |
| `RealDotLengthCondition.lean` | 12 | S×7 / **T×4**（`dot_truncates_a`/`dot_empty_left_ignores_x`/`dot_truncates_x`/`dot_same_length_ok` 皆 `by decide` 具体值）/ C×1（自承「本文件即 `dot` 重复声明的第 6 处」） |
| `RealDotRepresentationAudit.lean` | 10 | S×4 / **C×4**（`dot_eq_dotL`/`dotL_eq_dot` **皆 `rfl`**；`dot_representation_agreement`/`_bridge` 是同一事实的合取壳）/ G×2 |
| `RealHypothesisAudit.lean` | 33 | S×20 / **K×6**（见 §六.6：文件前 4 条是 `ConvertVectorLinear`/`SymbolToWeightCorrectness` 名的转述）/ A×7 |
| `RealNegativeCore.lean` | **0** | **N**（82 行 `example` 契约钉 + `#print axioms`，**0 theorem**） |
| `RealRflAudit.lean` | 24 | S×14 / C×6 / A×4 / G×2 —— **本身即自指审计**，见 §六.7 |
| `RealScalarVerdict.lean` | 2 | K×2（`affine_edit_output_bound_scalar`/`edit_verify_tolerance_scalar_affine` 是 `RealScalarField` 的 𝕜 参数化版） |
| `RealSymbolCompletenessVerdict.lean` | 11 | S×8 / A×2（`d32_s02_characterization_is_false`,`d32_row_zero_does_not_imply_all_zero`）/ K×1 |

**Meta 汇总**：S≈**75** · K≈**9** · C≈**11** · A≈**13** · T=4 · N=1 文件 · G=4

### Lift（11 文件 / 92）

| 文件 | 条数 | 判定分布 |
|:--|--:|:--|
| `RealBranch.lean` | 5 | S×2 / T×3（`branch_then_when_positive`/`branch_else_when_nonpos` 是 `if_pos`/`if_neg`；`branch_output_bound` 同形） |
| `RealContractAxioms.lean` | **0** | **N** —— 但**非同寻常**，见 §七 |
| `RealNonlinearFidelity.lean` | **0** | **N**（67 行 docstring 门面） |
| `RealNonlinearFidelity_parts\A.lean` | 21 | S×19 / G×2 |
| `RealNonlinearFidelity_parts\B.lean` | 27 | S×25 / A×2（`neg_zeroFixing_*` 系列） |
| `RealNonlinearFidelity_parts\C.lean` | 19 | S×17 / G×2 |
| `RealParamLoss.lean` | 7 | S×5 / A×2（`paramLoss_forall_p_false` 关键消融）/ G×1 |
| `RealTrainVerify.lean` | 1 | S×1（`train_verify_protocol`，真组合定理） |
| `RealWeightedConstraints.lean` | 3 | S×3 |
| `RealWeightedConstraintsN.lean` | 2 | S×2 |
| `VerifyLoopConvergence.lean` | 7 | S×5 / G×2（`odd_gt_zero` 是辅助；`repairEven_preserves` 仅 `simp [h]`） |

**Lift 汇总**：S≈**79** · G≈**7** · A≈**4** · T≈**3** · **N=2 文件**

---

## 二、重点核对逐项结论

### §2.1 三套编译器是否互不相连？—— **是，且比「三套」更严重：实际是四套半，零交集**

逐个给文件与定理（`grep '^import Lattice'` 全量核实）：

| 编译器 | 源语言 | 目标语言 | 主定理（file:line） | import 闭包内的其他编译器 |
|:--|:--|:--|:--|:--|
| **A. IntExpr → 栈机** | `IntExpr`（`lit/add/sub/mul/neg`） | `Instr`（`push/add/sub/mul/neg`）+ `run : List Instr → List ℤ → Option (List ℤ)` | **`compile_correct`** `RealCompilerCorrectness.lean:214` | **无**（`:46` 文件头自述「仅 import Mathlib，不 import 任何 LATTICE 模块」） |
| **B. Lv00 几何 → IR** | `lvProgram`（12 种几何约束） | `IRConstraint` ×15 + `ir_sem` | **无编译正确性定理**；只有退化版 `compile_preserves_satisfiability` `RealLv00CompilerSpec.lean:322` | **无** |
| **C. Float 误差界** | `FloatExpr`（`lit/var/add/neg/mul`） | **无目标语言**：`evalFloat` 直接对 `FloatExpr` 递归 | `compile_error_bound` `RealCompileFloatCorrectness.lean:471` | 仅 `RealCompilerOpt`（见 D），**不 import A/B** |
| **D. 约束程序 → 神经元** | `RealConstraint`(`a*x+b=0`) / `ConstExpr` | `RealNeuron` / `RealLayer` | `opt_preserves_semantics` `RealCompilerOpt.lean:188`，`listLoss_compile_iff` `:235` | **唯一触到 Runtime 的一套**，但 `convertReal` = 字段拷贝 |
| **E. 符号约束 → 权重** | `ConstraintSet` | `Layer` | `symbolToWeight_correct`（`Runtime/SymbolToWeightCorrectness.lean`，**不在本域**） | 由 `Inequality`/`Disjunction`/`Combinators` 三文件以 **Int 玩具版**平行复现（`convert_preserves_semantics` 的 Int 版） |

**互不相连的机器证据（4 条）**：
1. `RealCompilerCorrectness.lean:1-2` 只 `import Mathlib` —— A 与 B/C/D/E **零 import 关系**。
2. `RealCompileFloatCorrectness.lean:1-3` 的 import 闭包 = `{Mathlib, RealFloatFormat, RealCompilerOpt}` —— 与 A、B **无交集**。
3. `RealLv00Compiler*` 全 7 子模块的 import 闭包 = `{Mathlib}` 内部 —— 与 A/C/D **无交集**。
4. 全库 `RealCompilerCorrectness` 的 importer 为 **0**（只有 `Compiler.lean:14` 的聚合 import）；`RealLv00Compiler` 的定理被引用 **0** 次（`RealRefinementCalculus.lean:8,323` 仅在 docstring 里**文字提及**）。

⇒ **没有任何一条定理同时提及两个编译器的类型**。四套编译器在 Lean 里是**四个不相交宇宙**。

**F. 另外还有两处「编译器」但无定理**：`RealTypeSoundness` 的 `TypedExpr`（有 `Step`，**无 `compile`**）、`RealTypeSoundnessSTLC` 的 `Tm`（有 `Step`，**无 `compile`**）。`grep 'def compile'` 在两者中 **0 命中** —— 即它们**不是编译器**，只是类型系统。

### §2.2 Codegen 是否 0 定理？—— **是**
`RealLv00CompilerCodegen.lean`：70 行 / **0 theorem / 0 lemma**。内容仅 6 个 `def`（`compile_point` `:19`、`compile_points` `:25`、`compile_constraint` `:38`、`compile_stmt` `:58`、`compile_program_go` `:67`、`compile_program` `:76`）。

**信息丢失（4 处，均有源码自认 + 我的独立核对）**：
1. **数值载荷被硬编码为 0**：`:44` `distance → (.const 0)`、`:51` `radius → (.const 0)`、`:55` `ratioDivision → (.const 0)`。
2. **`angle` 编译为恒真占位**：`:45` `→ (.eq_expr (.const 0) (.const 0))`，源码自述「等价于不施加额外 IR 约束」。
3. **点环境完全不进入编译**：`:38` 首参 `_ps` 未使用；`compile_points` `:25` 在管道中**从未被调用**（`:24` 自注）。
4. **约束名丢失**：`:38` 只按 `kind` + `args` 分派，`c.name` 被丢弃。

**并且：这份 codegen 没有「正确性定理」，因为它的正确性确实是假的** —— 被 `RealLv00CompilerHonesty.lean:25` 的 `D1_compile_loses_distance_value` **机器否证**。这是本域最诚实的一处：**Codegen 0 定理 = 因为它不可证**。

### §2.3 `compile_correct` 是否只覆盖 IntExpr？—— **是，且只覆盖四则运算的五构造子**
`RealCompilerCorrectness.lean:214`：
```
theorem compile_correct (e : IntExpr) : ∀ ρ : List ℤ, run (compile e) ρ = some (evalInt e :: ρ)
```
`IntExpr` 定义在 `:88-99`，仅 `lit | add | sub | mul | neg` 五构造子。**不含**：变量、`let`、条件、循环、函数、内存、浮点。

⚠ **附带矛盾（D 类）**：`:32` 的 docstring 列出 `compile (ite c a b) = compile c ++ [brz (compile a) (compile b)]`，但 **`IntExpr` 无 `ite` 构造子、`Instr` 无 `brz` 构造子**（`:88-99`/`:113-124`）。**docstring 描述了一个不存在的分支**。

### §2.4 抽象解释与 codegen 是否有组合定理？—— **完全没有**
- `RealAbstractInterpretation.lean` 的 import 闭包 = `{RealKleeneFixedPoint, RealIEEE754}` → **不含任何 codegen 模块**。
- 反向：`RealCompilerOpt` / `RealLv00Compiler*` / `RealCompilerCorrectness` / `RealCompileFloatCorrectness` 的 import 列表里 **均无 `RealAbstractInterpretation`**。
- 因此 `bestAbstract`/`SoundAbstract`/`clampSharp_sound`/`roundDownSharp_sound` 与任何编译器之间 **零定理**。
- 唯一「像组合」的是 §六.2 的 `transfer_of_sound_abstraction`（`RealAbstractInterpretation.lean:325`），但它把组合条件 `K (αS {x}) ≤ αS {x}` 作为**显式假设**（`:320-322` 自注：推不出来），且 `F` 是**任意** `Concrete → Concrete`，**不是**任何本仓编译器。

### §2.5 `Lift` 11 模块是否只是壳（0 定理）？—— **不是。这条前提不成立，必须驳回**
- Lift 实测 **92 条定理**（匹配给定基线），仅 **2 个文件 0 定理**（`RealContractAxioms`、`RealNonlinearFidelity` 门面）。
- 且有实质内容：`RealParamLoss.lean`（MPO-1 参数化损失，7 条含关键消融 `paramLoss_forall_p_false:145`）、`RealNonlinearFidelity_parts/*`（67 条零集判据）、`RealTrainVerify.lean:43`（训练-验证闭环）、`VerifyLoopConvergence.lean:81`（修复回路收敛）。
- ⚠ 但**「Lift」这个名字与内容不符**：Lift 本应指「提升/桥接」，实际里面 11 个主题（分支、契约公理探针、非线性保真、参数化损失、训练-验证、加权驻点×2、修复收敛）**互不 import 成链**，全部是 `Compile*.lean` 聚合文件的并列叶子。**名实不符（目录级 D）**。

### §2.6 `RealTypeSoundness` vs `RealTypeSoundnessSTLC` 是否重名 `preservation`/`progress`？—— **重名，但不是命名冲突**
| 名称 | 位置 1 | 位置 2 |
|:--|:--|:--|
| `progress` | `RealTypeSoundness.lean:132`（ns `Lattice.Lib.Compiler.RealTypeSoundness`） | `RealTypeSoundnessSTLC.lean:531`（ns `Lattice.STLC`） |
| `preservation` | `RealTypeSoundness.lean:168`（同上） | `RealTypeSoundnessSTLC.lean:541`（`Lattice.STLC`） |

⇒ **两套不同的命名空间**（`:44` 与 `:65-66`），**无 `environment already contains` 冲突**，可同时 import（`Compiler.lean:40-41` 实际就同时 import）。
**它们是两个不同定理**：IR 版是 5 构造子无变量无绑定；STLC 版是 de Bruijn + λ + 应用（`:99-111`）。
⚠ **但配对的「同名同形」是假象风险**：两者的结论**不同构**（IR 版 `HasType e T`，STLC 版多一个 `Γ`），且 STLC 版 `progress` 要求**闭项** `HasType [] t A`，IR 版**无闭性要求**。**下游按名盲引会拿到错误的那条。**

### §2.7 `RealCompilerCorrectness` vs `RealConcurrentSemantics` 是否重名 `run_append`？—— **重名，不同命名空间**
- `RealCompilerCorrectness.lean:156`（ns `Lattice.Lib.Compiler.RealCompilerCorrectness`）：`run_append (is js : List Instr) (σ τ : List ℤ) (h : run is σ = some τ) : run (is ++ js) σ = run js τ`
- `RealConcurrentSemantics.lean:44`（ns `Lattice`）：`run_append (l₁ l₂ : List (X → X)) (x : X) : run (l₁ ++ l₂) x = run l₁ (run l₂ x)`

⇒ 命题**同型但不同义**（栈机 `Option` 版 vs `foldr` 函数复合版），**无编译冲突**。
⚠ **真实风险**：`RealConcurrentSemantics` 在 `namespace Lattice` 根命名空间，其 `run_append` 与 `run`/`run_nil`/`run_cons`/`IncStep` 等 9 个顶层名**裸暴露**，是本域最容易被别处 `open Lattice` 时撞上的文件。

### §2.8 `RealBetaReduction` vs `RealGlobalConfluence` 是否重名 `star_single`/`star_trans`？—— **重名，不同命名空间**
| 名称 | `RealBetaReduction.lean`（ns `…RealBetaReduction`） | `RealGlobalConfluence.lean`（ns `Lattice`） |
|:--|:--|:--|
| `star_single` | `:62`（`BetaStar` 专用） | `:72`（任意 `r` 的泛型版） |
| `star_trans` | `:66`（`BetaStar` 专用） | `:77`（任意 `r` 泛型版） |

⇒ **`RealGlobalConfluence` 的版本是 `RealBetaReduction` 版本的泛型化**（`r : α → α → Prop` 特化到 `RedStep` 即得）。这是**真正的重复**（一个可删），不是简单命名空间隔离。
⚠ 更严重的是：`RealGlobalConfluence.lean:4-8` 的 docstring 说「`RealConcurrentSemantics` 只做到…留下全局合流缺口。本文件补齐该缺口」，但**`RealGlobalConfluence` 并不 import `RealConcurrentSemantics`**，且其 `newman` 只对**抽象关系**陈述 —— **对 β-归约仍是条件性**（`:22-23`、`:26-29` 自认 `diamond_fails` 使局部合流为假、终止性未证）。**「补齐缺口」这个措辞与文件实际能力不符（D）。**

### §2.9 `Meta` 目录是否只是复述别处定理（审计自指）？—— **部分自指，但不是全部复述；自指最严重的是 `RealRflAudit`**
**属实（复述/转述）的部分 —— 13 条**：
- `RealHypothesisAudit.lean:41-75` 逐字抄录 `ConvertVectorLinear` / `SymbolToWeightCorrectness` 的签名，然后**以本文件内同名声明**（`convertVec_preserves_semantics`、`scaleVec_preserves`、`symbolToWeight_correct`、`extract_to_weights`）重放（6 条 K）。
- `RealRflAudit.lean:377-379` `instanceA_rfl_level` 的证明体逐字是 `exact extractVec_convertVec_rfl c`（**`:375-376` 自己承认「本条自己也是接口级」**）。
- `RealDotRepresentationAudit.lean:75` `dot_eq_dotL` / `:78` `dotL_eq_dot` 的证明体是 `rfl`，`:159` 主定理只是三条 `rfl`/桥接的合取壳。
- `RealNegativeCore.lean` 全文件 0 定理，只有 `example` 复述 7 条既有否定定理的陈述形状。
- `RealCounterexamples.lean` 6 条 wrapper（`cex_ce_not_joint_convex` 等）。

**不属实的部分（有独立内容）—— 约 75 条 S**：`RealHypothesisAudit` 的 20 条（`Grade` 强度全序 + `witness_strictly_dominates`）、`RealRflAudit` 的 14 条（层级二分定理）、`RealDotLengthCondition` 的 7 条（`zip_append_tail_eq:119` 是真题）、`RealSymbolCompletenessVerdict` 的 8 条（推翻 S-02:475）、`RealCounterexamples` 的 20 条。

⇒ **判定：Meta 是「审计 + 少量新数学」的混合体，不是纯复述。但存在一个结构性隐患：审计文件在 Lean 里无法检查自己被审计的对象**（`RealRflAudit.lean:104-106`、`RealHypothesisAudit.lean:93-94` 自认「未经内核编译 / 未做 `Syntax` 元编程」）。见 §六.7。

### §2.10 `RealContractAxioms` / `RealNonlinearFidelity` 是否纯 import 壳？—— **一半属实**
- `RealNonlinearFidelity.lean`：**是**。129 行中 127 行是 docstring，实际内容仅 3 行 `import`（`:3-5`）+ 1 行 `namespace`。**0 定理**，真内容在 `_parts/{A,B,C}`（67 条）。**判定 N（门面）。**
- `RealContractAxioms.lean`：**表面是壳，实际是本域最关键的元证据载体**。200 行、**0 定理**、16 行 `import`、**约 95 条 `#print axioms`**。它不是「复述定理」，而是**把「0 axiom」从声明变成可复现检查**（`:4-18` 自述，对齐 mathlib 官方判据）。
  ⚠ 并且它的 **`:36-64` 节是全仓最硬的一条架构事实**：记录了 `ConvertLinear + VerifyLoopConvergence → EvenSat`、`ConvertLinear + ComboN → EvenSat, EvenOut`、`Combinators + RealCombinators → andC, orC, dist_preserves, …` 的**不可同时 import 的模块对**。
  ✅ 我的独立核实：`VerifyLoopConvergence.lean:31-36` 明确记录「`EvenSat` 与 `ComboN.lean:19`、`ConvertLinear.lean:99` 逐字相同，构成**三路命名冲突**」，与 `RealContractAxioms.lean:42-45` **完全一致**。**这是一条真实、可交叉验证的架构缺陷。**

---

## 三、玩具判定（三条正面回答）

### §3.1 编译器是否在真实语言上？还是玩具 `IntExpr`？
**两者的准确表述是：既有真语言形式化，也有玩具，但「真语言」那边没有编译正确性定理。**

- **玩具（不可连真实对象）**：`IntExpr`（`RealCompilerCorrectness.lean:88`，5 构造子，无变量无内存无控制流）；`FloatExpr`（`RealCompileFloatCorrectness.lean:101`，5 构造子，**且根本没有 `compile` 函数**）；`lvProgram`（12 种几何约束，**但编译丢弃全部数值**）。
- **有真语言骨架但被裁掉**：`Cmd`（`RealBigStepSmallStep.lean:85-95`，含 `while'` 但 `while' true c` **立刻停机、不执行 c** —— `:95` 自认）；`TypedExpr`/`Tm`（有 `Step` 无 `compile`）；`Stmt`/`StmtT`（`RealWP.lean:54` / `RealWhileTotalCorrectness.lean:46`，**`RealWP` 的 `Stmt` 刻意不含 `while`**）。
- **唯一「真语言 + 真编译器 + 真语义」三点齐全的**是 `RealCompilerOpt.lean` 的约束程序编译器 —— 但它是 `convertReal` = `{w := c.a, b := c.b}`（`Runtime/RealLinear.lean:44`），**结构拷贝**；`compileNeurons` = `p.map convertReal`（`:201`）。**这是「编译器」概念的最弱使用**（map 一个字段拷贝）。

⇒ **结论：`IntExpr` 是玩具。本域不存在「真实语言上的编译正确性定理」。**

### §3.2 类型 soundness 是否真的连到运行时？
**完全没有。**
- `RealTypeSoundness.type_soundness`（`:216`）的结论是 `Value e ∨ ∃ e', Step e e'` ∧ `∀ e'', Step e e'' → HasType e'' T` —— 全部在 `TypedExpr` 内部，`Step` 是**归纳定义的语法关系**（`:88-95`），**没有求值到 `ℤ/ℝ/Bool` 的语义函数**。
- `RealTypeSoundnessSTLC.soundness`（`:578`）同理：`Relation.ReflTransGen Step t t'`，`Step` 归纳定义（`:211-220`），**无 `eval : Tm → ℕ`**。
- **无任何运行时连接**：`grep 'evalInt\|evalBool\|Float'` 在两文件的**定理陈述**中 0 命中；`RealTypeSoundnessSTLC` 的 `substTop`（`:206`）只被 `Step.beta` 用，**不在任何可执行解释器里**。
- `RealTypeSystemExt`（`preservation_ext:?`）同样只在 `ExprExt` 内部。

⇒ **「类型健全性」在此是纯语法的类型保持，与 Runtime 零连接。** 且 `TypedExpr`/`Tm`/`ExprExt` 与 `IntExpr`/`FloatExpr`/`IRConstraint` **无转换函数** —— 类型层与编译层之间**零桥**。

### §3.3 Codegen 是否有可执行语义？
**部分有，且质量两极分化。**
- **有可执行语义**：`RealCompilerCorrectness.Instr.run`（`:128`，`Option` 栈机，可归约）；`RealSatComplete.dpllSearch`（`:41`，Bool 回溯搜索，**已证 `dpllSearch_iff` 可靠且完备**）；`RealConstraintSat.qSatAllB`（`:162`，Bool 判定器）；`RealWP.exec`（`:61`，全函数大步语义）；`RealWhileTotalCorrectness.execF`（`:55`，燃料语义）。
- **无可执行语义**：`RealLv00CompilerCodegen.compile_*`（`List IRConstraint`，**`ir_sem` 是 `Prop`，不可求值**）；`RealCompileFloatCorrectness`（**无 `compile`**，`evalFloat` 只在 `ℝ` 上算，**不产生浮点字面量**）。
- ⚠ `RealCompilerCorrectness` 的栈机 **`run` 与 `compile` 都不可执行于 `Int` 之外**（`push : ℤ → Instr`，`:115`），**与任何真实目标机无关**；且 `RealCompilerCorrectness.lean:53-58` 自认「不含跳转/变量/函数/内存」。

---

## 四、0 定理文件（5 个 Compiler + 1 Meta + 2 Lift = 8 个）

| 文件 | 行 | 性质 | 判定 |
|:--|--:|:--|:--|
| `Compiler\RealLv00Compiler.lean` | 131 | 纯 docstring 门面，re-export 7 子模块；含**本仓最完整的诚实警告段**（`:51-76`） | N，且**有价值**（A 类信息） |
| `Compiler\RealLv00CompilerLanguage.lean` | 117 | 纯语法/语义定义（`lvLang` 移植） | N |
| `Compiler\RealLv00CompilerCodegen.lean` | 70 | **Codegen 本体，0 定理** | **N + 关键缺口**（§2.2） |
| `Compiler\RealMutualRecursion.lean` | 38 | 3 行 import 门面 | N |
| `Compiler\RealMutualRecursion_parts\B.lean` | 149 | **只有 import + 复制的 docstring，0 声明** | **N，纯冗余**（拆分产物） |
| `Meta\RealNegativeCore.lean` | 82 | 7 条 `example` 契约钉 + 8 条 `#print axioms` | N，**有用**（契约回归） |
| `Lift\RealContractAxioms.lean` | 200 | ~95 条 `#print axioms` | N，**本域最有价值元证据** |
| `Lift\RealNonlinearFidelity.lean` | 67 | 3 行 import 门面 | N |

⚠ 注意：`RealRflAudit.lean:98` 与 `RealHypothesisAudit.lean:93` **自认「本文件未经内核编译」** —— 这是**审计文件自身的构建状态不可验证**（见 §九 未验证项 U3）。

---

## 五、`rfl` 重言 / 循环论证专列

### §5.1 ⭐ 最重要的单条发现：Float 编译器核心定理的 `mul` 分支是**不可实例化的假设** `hMul`

- `RealCompileFloatCorrectness.lean:450` `abbrev hMul : Prop := ∀ F r ρ A …, |evalFloat F r ρ (.mul a b) − evalReal ρ (.mul a b)| ≤ numOps(.mul a b) · (κ^(expo) · ((1+eps)·mag A (.mul a b) + tiny))`
- `:471` `compile_error_bound (hM : hMul) …` —— **`:683` 的 `.mul` 分支证明体就是 `exact hM F r ρ A hA hvar hlit hcontract a b`**。
- **`hMul` 是 `compile_error_bound` 在 `mul` 处的目标的逐字复制**（`:443-444` 自认「形状与 `compile_error_bound` 在 `mul` 处的目标完全一致」）。

**⇒ 这是一个循环把目标当假设**：`compile_error_bound` 对含 `mul` 的表达式，其强度**不超过** `hMul`。
**全库零实例化**：`grep -r hMul` 在 `RealCompileFloatCorrectness.lean` 之外 **0 命中**（另 190 条命中全是无关的局部 `have hmul`）。**即 `hMul` 从未被任何人证出或使用。**

**而且它是可证的 —— 隔壁已证**：`Lattice/Lib/Quantization/RealConversionStabilityFloatBounds.lean:360` 的 `ce_compile_error_bound` 是**同一误差界的完整证明**，`mul` 分支**已闭合**（`:349-350` 自述「本定理的 `mul` 分支已完整证明，无需任何未证假设」），且用**更紧**的指数 `ceOps e`（而非 `2·n_ops+1`）。该文件自己的 `:343` 也点明 `RealCompileFloatCorrectness` 「不可构建」。
（该文件 13 条定理，实测确切存在；`ceOps`/`ceMag`/`CPExpr` 是 `RealCompileFloatCorrectness` 的**平行独立实现**。）

⇒ **判定：`RealCompileFloatCorrectness` 是一个「原地被隔壁超越的平行实现」，其主定理依赖一个从未被证、但隔壁已证的假设。** 这是**本域最该修的 1 条**。

### §5.2 `rfl` / `Iff.rfl` 重言（全范围 31 条，按危害排序）
**无害（接口锚点，docstring 已自认）**：
`compile_empty`(`RealLv00CompilerReal.lean:23`)、`stmt_compiled_edge_correct_point/prove/normalize`(`RealLv00CompilerSpec.lean:23/33/37` = `rfl`)、`D3_angle_*`(`RealLv00CompilerHonesty.lean:54/59`)、`mod_preserves`(`ModConstraint.lean:41` = `Iff.rfl`——**「编译保语义」就是定义同构**)、`point_le_iff_contains`(`RealAbstractInterpretation.lean:408` = `Iff.rfl`，自认「序选对了的机器证据」)、`qSat_unfold`/`qSatisfiableOn_iff`(`RealConstraintSat.lean:144/157`)、`wp_assign`/`wp_composition`/`wp_and`(`RealWP.lean:90/118/127`)、`whileApprox_zero`/`whileApprox_succ_eq_whileF`(`RealWPWhile.lean:66/104`)、`refines_refl`(`RealRefinementCalculus.lean:85`)、`commute_refl`(`RealEffectOrdering.lean:92`)、`numOps_*`×5(`RealCompileFloatCorrectness.lean:139-143`)、`recFwd_succ`(`RealRecursiveSemantics.lean:55`)、`decEq_*`、`dot_eq_dotL`/`dotL_eq_dot`(`RealDotRepresentationAudit.lean:75/78`)、`ablation_eq_contentLevel`(`RealRflAudit.lean:353`)、`flatEquiv_eq_refl`。

**有危害（伪装成数学内容，而 docstring 未自认 rfl）**：
- `LvDSLPartial.lean:83` `empty_program_no_constraints`、`:86` `no_prove`（**`= by rfl`**），`:89` `getConstraints_length_nonneg`（`Nat.zero_le`）—— 而该文件 docstring `:24-25` 称「三条均为**定义展开**」并附 axioms 证据，**读起来像有内容的三条定理**。
- `RealLv00CompilerSpec.lean` 的 `compile_bridge_sem`(`:311`)：证明体 3 行，但**结论在退化环境下对任意源约束成立**（`D2_bridge_independent_of_source` `RealLv00CompilerHonesty.lean:42` 机器证明）——**「桥接」二字是虚的**。
- `RealMutualRecursion_parts\C.lean` 的 `flatEquiv_*` 系列（4 条）：`Flat := Sum MExpr MStmt` 是 `abbrev`，故 `flatEquiv` 是**定义层恒等**。`RealMutualRecursion.lean:62-68` **已诚实自认**「同构在此是平凡的」。**判定 C。**

### §5.3 循环论证 / 自指（3 处）
1. **§5.1 的 `hMul`**（目标当假设）—— 最严重。
2. **`RealRflAudit`**：文件主体用「命题族层级」判定「某条定理是否接口级」，而**它自己 16 条里的 5 条被自己判为接口级**（`:472-473` 自认），且 `:478-479` 自认「不主张已为全库每条定理加标注」。**这是诚实的自指，但自指本身使「审计」的覆盖范围不可闭合。**
3. **`RealDotLengthCondition`**：`:59-60` 自认「本文件的 `dot` 是**本地重声明**…这本身即 §5 登记的『`dot` 被 5 处重复声明』的实例」—— 即**审计重复的文件自己制造了重复**。`:233` 又自认「只登记不合并」。**判定 C（自承）。**

---

## 六、重名 / 平行实现 / 与声明不符

### §6.1 重名清单（已核实为命名空间隔离，无编译冲突）
| 名 | 位置 A | 位置 B | 关系 |
|:--|:--|:--|:--|
| `progress` | `RealTypeSoundness.lean:132` | `RealTypeSoundnessSTLC.lean:531` | 不同命名空间，不同命题 |
| `preservation` | `RealTypeSoundness.lean:168` | `RealTypeSoundnessSTLC.lean:541` | 不同命名空间，不同命题 |
| `run_append` | `RealCompilerCorrectness.lean:156` | `RealConcurrentSemantics.lean:44` | 同型不同义 |
| `star_single` | `RealBetaReduction.lean:62` | `RealGlobalConfluence.lean:72` | **后者是前者的泛型化（真重复，可删一条）** |
| `star_trans` | `RealBetaReduction.lean:66` | `RealGlobalConfluence.lean:77` | 同上 |
| `convertVec_preserves_semantics` / `scaleVec_preserves` / `symbolToWeight_correct` / `extract_to_weights` | `Runtime\ConvertVectorLinear.lean` / `SymbolToWeightCorrectness.lean` | **`Meta\RealHypothesisAudit.lean:41-75` 同名重放** | **真重复（6 条）** |
| `convertVec_preserves_semantics` / `roundtrip_extractVec` / `extractVec_convertVec_rfl` / `extractLayer_compileToLayer` / `roundTripAddsNothing_of_factorsThrough` | 各原文件 | **`Meta\RealRflAudit.lean:60-85` 抄录** | **真重复（5 段签名的转述）** |
| `dot` / `dotL` / `dotQ` | `ConvertVectorLinear.lean:35` / `RealDotLengthCondition.lean:71` / `RealRoundtripRat.lean:98` | — | **3 份同义实现**；另有 `RealLv00Compiler.dot`(ℝ×ℝ) 等 6 个异型同名 |

👉 **`RealContractAxioms.lean:42-45` 记录的 `EvenSat`/`EvenOut` 三路冲突已独立核实**（`VerifyLoopConvergence.lean:31-36` 一致）。这是**本域唯一一条有交叉证据的架构级缺陷**。

### §6.2 `RealAbstractInterpretation` 两处「结论弱于 docstring」
- `:516-518` `clampSharp` 的 docstring 称「**丢弃原区间的界**…裁剪是最粗但可靠」，但 `clampSharp_sound:524` 的证明体 `intro a c _` —— **`a` 与 `c` 的包含关系 `c ∈ γ a` 被 `_` 丢弃**，定理对**任意** `c : ℝ` 成立（即 `clampTo_mem` 的重述）。`clampSharp_endpoint_bounds:547` 更弱（端点展开）。**判定 S + G，但 `:516` 的「抽象」措辞过强。**
- `:529-546` **诚实自认**「初稿试图证 `M ≤ (fSharp a).hi`，两条不等式方向相同无法传递 ⇒ 只交付端点展开」。**这是本域写得最好的诚实段之一。**

### §6.3 `RealEffectOrdering.commute_of_commute_fn` —— 唯一一条被自认为「假设未使用」的定理
`RealEffectOrdering.lean:163`：`(h : ∀ a b, Commute (ρ a) (ρ b))` 在证明中**完全未被使用**（`:185` `simp only` + `:191` `mul_comm` 就够了）。文件 `:144-162` **诚实登记**了根因：`Effect = State → State` 的 `*` 是**逐点乘法**（`Pi.mul_apply`）而非函数复合，`List.prod` 走的是逐点乘法，故 `Commute`（用 `∘`）与目标无关。
⇒ **判定 D（承认）+ 有价值的根因登记**。这不是掩盖，而是**「原稿对载体的语义判断错误」的机器化记录**。**同类问题在 `RealContractAxioms.lean:56` 有呼应（`Function` 的 `Monoid` 实例混淆）。**

### §6.4 `RealMutualRecursion_parts\C.lean` 的 4 条 `flatEquiv_*`：**真重复 + 平凡**
`Flat := Sum MExpr MStmt`（`abbrev`），`flatEquiv_apply_inl/inr`、`flatEquiv_left_inv`、`flatEquiv_right_inv` —— 全部在 `Sum` 上的**定义层恒等**。文件 `RealMutualRecursion.lean:62-68` 自认。**判定 C。**

### §6.5 `RealRegisterAllocation` 的 2 条「领域化」实为改名
- `loop_lower_bound`（`:194`）：证明体 `= clique_lower_bound s hclique h` —— **`hloop` 参数从未使用**（`:196` `(hloop : ∀ v ∈ s, inLoop v)`，而 `:200` 直接丢弃）。文件 `:190-193` 声称「`hloop` 是真实的前提，去掉它下界**不成立**」 —— **这是假的：`loop_lower_bound` 的证明根本不需要 `hloop`，且定理对任意 `hloop` 成立。** **判定 T + D（docstring 与证明体矛盾）。**
- `spill_required`（`:209`）：`= absurd (chromatic_ge_clique …)` —— 是**逆否的直接改写**（`:206` 自认）。**判定 T。**
- 真正有内容的是 `colorable_iff_coloring`（`:93`，双向桥到 mathlib `Coloring`）、`clique_lower_bound`（`:124`，鸽笼）、`complete_graph_chromatic_eq`（`:234`，双向）。**判定 S。**

### §6.6 `Meta\RealHypothesisAudit` 的 6 条转述
`:41-75` 逐字抄录 4 个结构的签名，并在本文件内**以同名声明重放**（`convertVec_preserves_semantics` 等 4 条）+ `symbolToWeight_correct` + `extract_to_weights`。**它们在 `Lattice` 命名空间内与 `Runtime` 的原件同名** —— **若二者同时 import 会冲突**。文件 `:102-103` 自认「不复用 `_R-05.lean` 的 `InterfaceLevel`」，但**未登记这 6 条重放本身的冲突风险**。**判定 K + 潜在 D。**

### §6.7 `Meta` 的「审计自指」结构性缺陷（本域最该注意的元问题）
- `RealRflAudit.lean:104-106`：「`InterfaceLevel` 是**证明体级判据的类型级对应物**，**不是**"证明体文本是 `rfl`"的字面形式化（那需要 `Syntax` 元编程，**未做**）。扫描计数来自 Python 正则，**非** `verify.ps1` 输出，**未经复核**。」
- `RealHypothesisAudit.lean:93-101`：「本文件**未经内核编译**…**不**机械化"证明体文本"…本文件**不声称**已对全库告警做扫描。」
- `RealDotLengthCondition.lean:8`：「本文件全部跨文件行号锚点…**会随对应文件改动而漂移，引用前须复核**。」

⇒ **三个审计文件共 3 处自认「审计手段本身不可验证」**（未经内核 / 正则 / 行号漂移）。这是**审计目录的元级 D**：**它们审计别人，但自身的可靠性不在 Lean 的管辖范围内。**

---

## 七、`RealContractAxioms` 的独立价值（不能当壳处理）

虽然 **0 定理**，但它是**本域唯一把「0 axiom」变成机器可复现检查的载体**：
- `:14-15` 引用 mathlib 官方判据 `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`。
- 覆盖 C2–C21 共 **19 组**契约不变量（`:90-199`），约 **95 条 `#print axioms`**。
- `:36-64` **登记了 3 组不可同时 import 的模块对**，且 `:47-54` 记录了**实测报错原文**（`environment already contains 'Lattice.EvenSat' from ConvertLinear`）。
- ⚠ **但它是 info-only**（`:22-27` 自认「`#print axioms` 写 info 消息，不改 artifact」）⇒ **它本身不失败、也不 gate**；真正的失败判定在 `scripts/check-axioms.ps1`（**不在本域，我未运行**）。

⇒ **判定 N + A（元证据）。建议保留，并登记为「唯一 axiom 门禁的 Lean 侧入口」。**

---

## 八、本域最该做的 10 条（按预期收益排序）

1. **【最高】用已证版替换 `hMul`**：把 `RealCompileFloatCorrectness.lean:450-471` 的 `compile_error_bound` 删除或改为套用 `Quantization\RealConversionStabilityFloatBounds.lean:360` 的 `ce_compile_error_bound`（乘法已闭合、指数更紧）。**若不做，Float 编译器"正确性"在本域是空的**（§5.1）。同时删掉 `RealCompileFloatCorrectness.lean:32-56` 中已失效的「未落地」清单与 `:65-76` 的历史沿革段（**它们描述的是被隔壁超越的旧状态**）。

2. **建立 IntExpr ↔ 栈机 ↔ 约束程序 的桥（哪怕只有一条）**：本域四套编译器**零交集**（§2.1）。最小可行：为 `RealCompilerCorrectness.Instr` 定义 `toRealNeuron`，证 **1 条** `run_corresponds_to_ProgramSat`。**一条桥胜过 651 条孤岛。**

3. **补 `compile_correct` 覆盖到有变量的语言**：现 `IntExpr`（`:88`）无变量，`compile_correct`（`:214`）本域最强定理也只覆盖 5 构造子。最小扩展：加 `var : ℕ → IntExpr` + `Instr.load`，重证 `run_append` 架构。**注意先修 `:32` 的 `ite/brz` docstring 虚假分支（D）。**

4. **Lv00 Codegen 三条路选一**：①（推荐）如实降级为**不可证**并只保留 `D1_compile_loses_distance_value`（`RealLv00CompilerHonesty.lean:25`）作为**永久反例**，删掉 `compile_constraint` 的 `.const 0` 硬编码；②补全数值载荷为一个独立的 `lvConstraintPayload` 结构再重做；③删除 `RealLv00CompilerCodegen.lean`。**当前「有 codegen、0 定理、且被自己证伪」是最坏状态（§2.2）。**

5. **修 `RealRegisterAllocation.loop_lower_bound`（`:194`）的 docstring 谎言**：`hloop` 未被使用且非必要（§6.5）。二选一：删 `hloop` 参数，或把 `inLoop` 真正接进一个「临时变量可否复用」的模型。**当前 docstring 断言「去掉它下界不成立」是假的。**

6. **处理 `EvenSat`/`EvenOut` 三路命名冲突**：`RealContractAxioms.lean:42-45` + `VerifyLoopConvergence.lean:31-36` 已双重登记。收敛到 `ComboN.EvenSat` 单一权威（`VerifyLoopConvergence` 已做了一半，`ConvertLinear.lean:99` 与 `ComboN.lean:19` 仍需统一）。**这是本域唯一有交叉证据的架构缺陷。**

7. **删 `star_single`/`star_trans` 之一的重复**（`RealBetaReduction.lean:62/66` vs `RealGlobalConfluence.lean:72/77`），并把 `RealGlobalConfluence` 泛型版改名引用。同时**修正 `:4-8` 的「补齐缺口」措辞**（§2.8）。

8. **`Meta` 去重 13 条转述**：`RealHypothesisAudit.lean:41-75` 的 6 条同名重放 + `RealRflAudit.lean:60-85` 的 5 段抄录。改为 `open` 引用或 `example`（**避免在 `Lattice` 命名空间制造第二份同名声明**）。至少登记为已知风险（§6.6）。

9. **把审计工具本身纳入内核**：`RealRflAudit`/`RealHypothesisAudit` 自认「未经内核编译 / 用 Python 正则 / 行号漂移」（§6.7）。最小可行：给 `RealRflAudit` 补一个**只覆盖本域**的 `#print axioms` 清单（像 `RealContractAxioms` 那样 info-only），至少消除「未编译」这一项。

10. **登记 `Lift` 的名实不符**：`Lift/` 下 11 个主题（分支/契约探针/非线性保真/参数化损失/训练验证/加权驻点×2/修复收敛）**互不 import**，且**没有一个与 Compiler 域的编译器相连**。要么改名（如 `Rewriting`/`Misc`），要么把 `RealParamLoss`（唯一有「提升」语义的：符号参数 → 可训练参数）真正接进 `RealCompilerOpt`。

---

## 九、覆盖文件清单与声明数 / 未验证项

### §9.1 覆盖（67/67 文件，100%）
**Compiler 48**（`Combinators` 7, `CombinatorsXorNot` 17, `Disjunction` 3, `Inequality` 5, `LvDSLPartial` 3, `ModConstraint` 13, `RealAbstractInterpretation` 38, `RealBetaConfluence` 28, `RealBetaReduction` 26, `RealBigStepSmallStep` 18, `RealBoolCompleteness` 19, `RealCombinators` 24, `RealCompileFloatCorrectness` 23, `RealCompilerCorrectness` 7, `RealCompilerOpt` 18, `RealConcurrentSemantics` 11, `RealConstraintSat` 13, `RealContinuationEquivalence` 5, `RealEffectOrdering` 14, `RealFirstOrderLogic` 32, `RealGlobalConfluence` 10, `RealLambdaCalculus` 20, `RealLv00Compiler` 0, `RealLv00CompilerCodegen` 0, `RealLv00CompilerHonesty` 10, `RealLv00CompilerIR` 1, `RealLv00CompilerLanguage` 0, `RealLv00CompilerReal` 14, `RealLv00CompilerSat` 4, `RealLv00CompilerSpec` 19, `RealMutualRecursion` 0, `RealMutualRecursion_parts/A` 13, `/B` 0, `/C` 30, `RealNonlinearCompile` 13, `RealRecursiveSemantics` 13, `RealRefinementCalculus` 17, `RealRegisterAllocation` 8, `RealSatComplete` 12, `RealSemanticsPreservation` 13, `RealTreeDecidable` 19, `RealTreeRecursion` 23, `RealTypeSoundness` 9, `RealTypeSoundnessSTLC` 17, `RealTypeSystemExt` 12, `RealWhileTotalCorrectness` 14, `RealWP` 15, `RealWPWhile` 20) = **651**

**Meta 8**（`RealCounterexamples` 28, `RealDotLengthCondition` 12, `RealDotRepresentationAudit` 10, `RealHypothesisAudit` 33, `RealNegativeCore` 0, `RealRflAudit` 24, `RealScalarVerdict` 2, `RealSymbolCompletenessVerdict` 11）= **120**

**Lift 11**（`RealBranch` 5, `RealContractAxioms` 0, `RealNonlinearFidelity` 0, `RealNonlinearFidelity_parts/A` 21, `/B` 27, `/C` 19, `RealParamLoss` 7, `RealTrainVerify` 1, `RealWeightedConstraints` 3, `RealWeightedConstraintsN` 2, `VerifyLoopConvergence` 7）= **92**

**行数**：Compiler **9686 行**（`Measure-Object -Line`）；三目录合计 **15149 行**（`Get-Content` 计数，含空行）。

### §9.2 未验证项（我**没有**验证的，明确列出）
| # | 未验证项 | 原因 |
|:--|:--|:--|
| U1 | **所有文件是否真的构建通过** | 纪律禁止 `lake build` / `lake env lean` |
| U2 | **`#print axioms` 是否真 ⊆ 三件套** | 需要跑 Lean；`RealContractAxioms` 的 ~95 条查询我**只读未执行** |
| U3 | **`RealRflAudit` / `RealHypothesisAudit` 是否可编译** | 两文件**自认未经内核编译**（`:98` / `:93`），我无法证伪也无法确认 |
| U4 | **`hMul` 是否真的可证** | 我只能证明「隔壁 `ce_compile_error_bound` 已证同型命题」；**两者语言类型不同**（`FloatExpr` vs `CPExpr`），严格说这是**同构类比的强证据，非同一命题的证明** |
| U5 | **`Meta` 119 vs 120 的权威口径** | 我的实测稳健（多法交叉），但无法判定是「给定基线漏记」还是「我的口径宽 1」 |
| U6 | **`RealContractAxioms.lean:42-45` 的 3 组冲突是否仍活跃** | 我核实了 `VerifyLoopConvergence` 的记载一致，但**未实际尝试同时 import** 验证报错 |
| U7 | **`RealSemanticsPreservation.forward_not_backward` 的反例是否满足全部假设** | 只读源码，未跑内核复核 |
| U8 | **`RealConversionStabilityFloatBounds.ce_compile_error_bound` 的 13 条是否真无 sorry** | 我只在该文件做过 `hMul` 关键字扫描，**未做全文件 `sorry` 扫描**（它不在本域） |
| U9 | **`RealAbstractInterpretation` 的 `Fintype`/`CompleteLattice` 假设是否被实例化** | 该文件 `:45-50` 自认「不动点迁移只在有限格上给出；未做无限格」——我未核实是否有任何下游实例 |
| U10 | **`Meta` 审计报告的 Python 扫描计数** | `RealRflAudit.lean:106` 自认「来自 `_r05_scan2.py`，**非** verify.ps1 输出，**未经复核**」；我未重跑 |

---

## 十、对账（最终）

### §10.1 与给定基线的对账
| 项 | 给定 | 实测 | 差额 | 处置 |
|:--|--:|--:|:--|:--|
| Compiler 文件数 | 48 | **48** | 0 | ✓ |
| Compiler 声明总数 | 651 | **651** | 0 | ✓ |
| Compiler `theorem` 条数 | 「651 定理」 | **635** | **−16** | **口径订正：651 含 16 条 `lemma`** |
| Meta 文件数 | 8 | **8** | 0 | ✓ |
| Meta 声明总数 | 119 | **120** | **+1** | **给定基线漏记 1 条** |
| Lift 文件数 | 11 | **11** | 0 | ✓ |
| Lift 声明总数 | 92 | **92** | 0 | ✓ |
| **合计声明** | 862 | **863** | **+1** | |

### §10.2 与仓库自身文档的对账（**4 处已证伪 / 待订正**）
1. **`RealLv00Compiler.lean:31-33`** 称「(A) 真结果 **13 条**、(B) 9 条、§7 降级 10 条、(C) 丢弃 47+」，`:48-49` 称「本文件共 **33 条** theorem/lemma」。**实测 Lv00 七子模块合计 52 条**（IR 1 + Real 14 + Spec 19 + Sat 4 + Honesty 10 + Language 0 + Codegen 0），**≠ 33**。`:39-40` 的「33 = 13+9+10+1」分类**已失效**（拆分后未重算）。
2. **`RealLv00Compiler.lean:148-152`** 自认「**待订正**：主题归属他包 11 条实为 14 条，两者不自洽」。**仍未订正**。
3. **`RealCompileFloatCorrectness.lean:32-56`** 的「本轮**未能落地**」清单（`MagPair`/`mul_error_bound`/`E3`/`E2`）与 `:65-76` 的历史沿革 —— **停留在旧状态**，未反映「隔壁已证」这一事实。
4. **`RealGlobalConfluence.lean:4-8`** 称「`RealConcurrentSemantics` 只做到…本文件补齐该缺口」—— 但**两文件无 import 关系**，且对 β-归约仍是条件性（`:22-29` 自认）。**措辞需下调。**

### §10.3 与我自己的方法论对账（自我订正，2 处）
1. **本报告最初的口径错误（已修）**：我第一轮用「只匹配行首 `theorem`」统计得 Compiler 720 / Meta 120 / Lift 92，与给定 651/119/92 不符。**根因是我把 docstring 中以 `theorem` 开头的行也计入了**。改用「排除注释行首」后得 **651 / 120 / 92**，**Compiler 与 Lift 完全吻合**，仅 Meta 差 +1。⇒ **任何后续审计都应声明口径（是否含 lemma、是否排注释），否则数字必然打架。**
2. **「Lift 只是壳」这条前提被证伪**：我最初按题面预期去找 0 定理证据，实测 92 条中 **79 条实质**，**必须驳回该前提**而非迎合它。同理「Meta 只是复述」也**只部分成立**（约 75 条有独立内容）。

### §10.4 一页纸结论
- **文件数、Compiler 总数、Lift 总数三项对账通过**；Meta +1 待订正；「651 定理」实为「635 定理 + 16 引理」。
- **四套编译器零交集**是本域第一位的结构问题：651 条定理里，**没有任何一条同时提到两个编译器的类型**。
- **Float 编译器的主定理靠一个从未被证、邻居已证的假设 `hMul`**，是本域最该修的单条。
- **Lv00 Codegen 0 定理是因它确实不可证**（被自己的 D1 反例证伪），这是全仓最诚实的一处设计，但状态是「有代码、无定理、自我证伪」。
- **类型健全性（3 个文件 38 条）与 Runtime 零连接**，且与任何 `compile` 零连接 —— 它们是类型演算，不是编译器的一部分。
- **审计目录（Meta）存在元级缺陷**：3 处自认「手段本身不可验证」（未经内核 / Python 正则 / 行号漂移）。
- **全范围 0 `sorry` / 0 `axiom`** —— 这条底线是干净的。
