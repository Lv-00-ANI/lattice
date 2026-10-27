# -*- coding: utf-8 -*-
"""Generate verdicts_010.jsonl from batch_010.jsonl + reviewer decisions."""
import json, io, sys

SRC = r"C:\Users\xingg\Desktop\agent\lattice-new\agent-tmp\review\batch_010.jsonl"
OUT = r"C:\Users\xingg\Desktop\agent\lattice-new\agent-tmp\review\verdicts_010.jsonl"

# (file, line, name, verdict, A, B, C, D, E, F, note)
D = []

def K(file, line, name, note):
    D.append((file, line, name, "keep", "", "", "", "", "", "", note))

A = "Lib/Chain/RealNumericChainOrder_parts/A.lean"
B = "Lib/Chain/RealNumericChainOrder_parts/B.lean"
C = "Lib/Compiler/"

K("Lib/Chain/RealN2AxiomDischargeJia.lean", 1207, "affineGeometry_false_but_repairable",
  "有限数据上的真命题：¬valid、extra 下 closed、extra 长度 = 4 三条都是可判定的具体事实；文件头已声明『只改谓词、不改数据』的严格更弱边界，没有冒充与原公理等价。无强度/覆盖问题。")
K("Lib/Chain/RealN2AxiomDischargeJia.lean", 1236, "all_twelve_discharged",
  "12 个包逐一给出 ¬PackageDependenciesValid，12/12 覆盖，是对上游 12 条假公理的真清算，不是空洞。名字 all_twelve_discharged 是历史遗留，doc 已明确『12 条上游公理全被证伪』，不构成过度声称。")
K(A, 107, "natToReal_strictMono", "ℕ→ℝ 严格单调查真命题（Nat.cast_strictMono 的库内接口），用途仅是链序向前方向，无需更强。")
K(A, 133, "natToReal_refl_lt", "反射方向真命题，与 strictMono 配对才能给出完整刻画；用途正当。")
K(A, 145, "natToReal_lt_iff", "由 107/133 组合的真 iff，无冗余前提；C.lean 的序刻画恰好需要双向。")
K(A, 149, "ratToReal_lt_iff", "ℚ 版同理，真 iff，陈述与用途匹配。")
K(A, 153, "natToInt_lt_iff", "ℕ→ℤ 版同理，真。")
K(B, 62, "rat_exists_between_zero_one", "显式反例（q = 1/2），真；用途是区分『离散/稠密』，一个 witness 已足够。")
K(B, 74, "real_dense_between", "x/2 构造，真；0 < x 是必要前提（x ≤ 0 时命题为假），不可删。")
K(B, 140, "natToReal_add", "保加法真命题（Nat.cast_add）。doc 说『由链交换律复合』与证明实际路径不符，但陈述本身正确且够用。")
K("Lib/Chain/RealScalarField.lean", 43, "edit_preserves_constraint_scalar",
  "算子范数残差界，真；doc 标题是『编辑后近似保持』，陈述就是界，没有被当成精确保持引用（RealComplex 按界使用）。")
K("Lib/Chain/RealScalarField.lean", 55, "edit_verify_tolerance_scalar", "43 的 ε 传递推论，真；hε 正是容差判定用途所需。")
K("Lib/Chain/RealZMod.lean", 34, "zmod_zero_iff_dvd", "Mathlib 同名引理的库内接口（含 p = 0 情形），陈述正确，作为库 API 保留合理。")
K(C + "Combinators.lean", 62, "orC_eq_zero_iff", "orC = a*b 的零因子刻画，真；带编码信息（非定义恒等）。")
K(C + "Combinators.lean", 68, "and_comm_preserves", "零集交换律，真；虽由 andC = a²+b² 的对称性也可直接得，但作为门语义接口有效。")
K(C + "Combinators.lean", 76, "or_comm_preserves", "零集交换律，真。")
K(C + "Combinators.lean", 83, "dist_preserves", "零集分配律，真（对应 AND/OR 门语义分配）。")
K(C + "Combinators.lean", 91, "and_assoc_preserves", "零集结合律，真。")
K(C + "Combinators.lean", 98, "or_assoc_preserves", "零集结合律，真。")
K(C + "CombinatorsXorNot.lean", 229, "xorC_offdomain_counterexample",
  "机器验证的域外反例 (0,2)：第一条 xorC 0 2 ≠ 0，第二条恰好是『恰一为零』为真，合起来正是全域版的反例；doc 还诚实标注了『只否定这一族编码，非任意函数』的边界。")
K(C + "Disjunction.lean", 30, "disj_embedding", "乘法零化 ↔ 析取，真；两侧均由 convert_preserves_semantics 支撑，非空洞。")
K(C + "Disjunction.lean", 82, "disjN_preserves", "列表版析取（乘积为零 ↔ 存在满足者），真；mem_map 两侧都处理了。")
K(C + "Inequality.lean", 34, "le_preserves", "x ≤ a ↔ x−a ≤ 0，真；编码不是同一命题，需要真实算术步。")
K(C + "Inequality.lean", 41, "le_and_ge_iff_eq", "Int 反对称，真；虽是 Mathlib 已有的基本事实，但被 25 直接用作一步。")
K(C + "Inequality.lean", 50, "le_ge_iff_sq_zero", "夹逼 ↔ 平方零化，真；两个方向都做了（含 int_sq_eq_zero_iff 的反向）。")
K(C + "Inequality.lean", 64, "bound_embedding_chain", "由 23/25 组合，真。")
K(C + "ModConstraint.lean", 72, "congruent_refl", "自反性真（m ∣ 0，含 m = 0）。")
K(C + "ModConstraint.lean", 80, "congruent_symm", "对称性真（dvd_neg）。")
K(C + "ModConstraint.lean", 89, "congruent_trans", "传递性真（dvd_add + ring 重写）。")
K(C + "ModConstraint.lean", 100, "congruent_add", "加法同余真。")
K(C + "ModConstraint.lean", 111, "congruent_mod_zero", "m = 0 退化 ↔ 严格相等，真且非平凡（0 ∣ k ⇒ k = 0）。")
K(C + "ModConstraint.lean", 130, "congruent_mod_one", "模 1 恒真，真；作为退化边界有信息。")
K(C + "ModConstraint.lean", 135, "congruent_mod_neg_one", "模 −1 恒真，真。")
K(C + "RealAbstractInterpretation.lean", 564, "roundDownN_le", "⌊xN⌋/N ≤ x，真；用 Int.floor_le 避开 toNat，负数正确。")
K(C + "RealAbstractInterpretation.lean", 572, "roundDownN_mono", "下取整单调，真（floor_mono + div_le_div_of_nonneg_right）。")
K(C + "RealBetaReduction.lean", 59, "star_refl", "ReflTransGen.refl 的接口，真。")
K(C + "RealBetaReduction.lean", 62, "star_single", "单步 → 多步，真。")
K(C + "RealBetaReduction.lean", 66, "star_trans", "多步传递性，真。")
K(C + "RealBetaReduction.lean", 106, "step_app_inv", "app 一步归约反转，三分支（根 β / app_l / app_r）穷尽，真；承重引理。")
K(C + "RealBetaReduction.lean", 116, "step_lam_inv", "lam 一步反转，真。")
K(C + "RealBetaReduction.lean", 129, "betaSubst_self", "替换自应用，真；用于 T/U/V 菱形分析。")
K(C + "RealBetaReduction.lean", 189, "step_Iz", "I z 唯一结果，真（三分支由 not_step_* 消解）。")
K(C + "RealBetaReduction.lean", 207, "not_step_redB", "redB = x x 无一步归约，真。")
K(C + "RealBetaReduction.lean", 228, "step_T_U", "T 根 β 一步到 U，真。")
K(C + "RealBetaReduction.lean", 235, "step_T_V", "T 参数内 β 一步到 V，真。")
K(C + "RealBetaReduction.lean", 241, "diamond_fails", "一步菱形反例：U、V 无共同一步归约，真；这是合流证明必须跨过的一步。")
K(C + "RealCombinators.lean", 38, "real_andC_eq_zero_iff", "ℝ 版 AND 零化，真（nlinarith 两个方向都做了）。")
K(C + "RealCombinators.lean", 57, "real_orC_eq_zero_iff", "ℝ 版 OR 零化 = mul_eq_zero，真。")
K(C + "RealCompilerCorrectness.lean", 156, "run_append",
  "run 的可拼接性，对 is 与 σ 联合归纳（generalizing τ/js），真；compile_correct 正是由它得出，属承重结果。")
K(C + "RealCompilerOpt.lean", 235, "listLoss_compile_iff", "列表损失零化 ↔ ProgramSat，真；两个方向都用 convertReal_preserves。")
K(C + "RealConcurrentSemantics.lean", 44, "run_append", "foldr 语义下的拼接律，真（run_cons + 归纳）。")
K(C + "RealConstraintSat.lean", 166, "qSatAllB_iff", "布尔检查器正确性，真（List.all_eq_true + decide_eq_true 双向）。")
K(C + "RealGlobalConfluence.lean", 72, "star_single", "泛型 ReflTransGen.single 接口，真。")
K(C + "RealGlobalConfluence.lean", 77, "star_trans", "泛型多步传递性，真。")
K(C + "RealLambdaCalculus.lean", 192, "subst_lift", "替换-提升相容律，真。")
K(C + "RealLambdaCalculus.lean", 202, "subst_subst", "替换复合律，真（对 t 归纳并在 lam 分支调用 subst_lift）。")
K(C + "RealLv00CompilerReal.lean", 161, "ir_sem_depends_on_vars",
  "15 个构造子逐一归纳（已核对 IRConstraint 恰好 15 个，ir_vars 覆盖全部字段），真；doc 的 15/15 与实际一致。")
K(C + "RealLv00CompilerSpec.lean", 332, "compile_preserves_satisfiability_hypothesis_unused",
  "对任意 prog 无条件证明 graph_satisfiable (compile_program prog)，这是有内容的证伪钉：它机器化地说明该实现的『编译正确性』是空真，正是诚实性文件的正当用途，不是过度声称。")
K(C + "RealMutualRecursion_parts/A.lean", 118, "MExpr.size_neg", "size 方程 rfl，真（方程编译器生成的标准 simp 引理，非重言）。")
K(C + "RealMutualRecursion_parts/A.lean", 125, "MStmt.size_seq", "size 方程 rfl，真。")
K(C + "RealMutualRecursion_parts/A.lean", 256, "MExpr.size_pos", "尺寸恒正，真（互递归归纳的投影），终止性所需。")
K(C + "RealMutualRecursion_parts/A.lean", 260, "MStmt.size_pos", "尺寸恒正，真。")
K(C + "RealNonlinearCompile.lean", 173, "piecewise_compile", "分段编译保语义，真（if_pos/if_neg 双向，两个分支各自取值）。")
K(C + "RealSemanticsPreservation.lean", 87, "sim_comp", "模拟对复合封闭，真；『多趟编译正确性可组合』的形式陈述成立。")
K(C + "RealSemanticsPreservation.lean", 97, "sim_mono", "模拟沿目标关系放宽，真。")
K(C + "RealTreeRecursion.lean", 143, "size_lt_of_mem", "c ∈ ts ⇒ size c < 1 + sizeList ts，真；终止性引理。")
K(C + "RealWP.lean", 75, "exec_ite_zero", "b = 0 走 else 分支，真（exec 定义即 if）。")
K(C + "RealWP.lean", 79, "exec_ite_nonzero", "b ≠ 0 走 then 分支，真。")
K(C + "RealWhileTotalCorrectness.lean", 79, "execF_mono", "燃料单调，真（对 k 归纳 + 5 个构造子逐一处理）。")
K(C + "RealWhileTotalCorrectness.lean", 180, "triple_while", "while 全正确性规则（保持 + 退出 + 变式强归纳），真且承重；用途（RealWPWhile）与强度匹配。")
K(C + "RealWhileTotalCorrectness.lean", 226, "wpT_while_fixpoint", "wp 不动点方程，真（两个方向都用 execF 展开并做燃料记账）。")
K(C + "RealWhileTotalCorrectness.lean", 263, "wpT_while_least", "最小不动点（对燃料归纳），真。")
K(C + "RealWhileTotalCorrectness.lean", 361, "embed_denotes_iff", "embed 的停机语义与原 exec 一致，真（embed_sound/embed_complete 两侧）。")
K("Lib/Concentration/RealAzuma.lean", 61, "hoeffding_lemma_scaled",
  "Hoeffding 引理的尺度化（X/c 归约到 |Y| ≤ 1），真；hN 为 uniformExpectation 非空所需，前提不多余。")

# ---------------- non-keep ----------------
D.append((C + "ModConstraint.lean", 41, "mod_preserves", "delete",
  "要支撑 RealContractAxioms 的『模约束编译保语义』，目标语义必须是独立定义的；现在目标谓词的定义就是源谓词，因此再怎么加强陈述也还是恒等，需要的是换目标语义而不是加强。",
  "应有 `mod_preserves_emod : (x : ZMod m) = (a : ZMod m) ↔ (x - a) % m = 0`（或 Int.emod 版），并对 m = 0 补 `ZMod 0 = ℤ` 的桥；这样目标才是真正的『整除判定』计算。",
  "无前提（本就无条件），无冗余前件可删。",
  "不涉及精确/误差降级：问题是恒等而非过强。",
  "覆盖所有 m（含 0），但覆盖的是定义展开，不是语义保持。",
  "Iff.rfl：Congruent x a m := m ∣ x − a，ModOut x a := x − a，Divisible out m := m ∣ out，展开后左右是同一命题，零信息。",
  "定义展开冒充『编译保语义』：三处定义拼起来就是恒等，下游 RealContractAxioms 拿它消解公理会是循环论证。建议删除或降级为 rfl 记号引理，另补 ZMod/emod 独立目标语义版。"))

D.append((C + "RealCompileFloatCorrectness.lean", 471, "compile_error_bound", "register",
  "对 users（RealConversionStabilityFloatBounds）而言，含乘法的表达式拿不到界：hMul 必须由调用者提供，而 hMul 正是 mul 分支本身的目标。对无乘法子语言则确实无条件成立。",
  "应有 `mul_error_bound`：用 |evalFloat a| ≤ mag A a、|evalReal a| ≤ mag A a 与乘法舍入界直接证 mul 节点，从而 compile_error_bound 不再需要 hMul；可再加 `no_mul_error_bound` 作为无条件子类版本。",
  "hcontract 可删：由 F.eps_nonneg、F.tiny_nonneg 与 m ≥ 1 可得 tiny ≤ tiny·m，即 (1+eps)m + tiny ≤ (1+eps+tiny)m，它不该作为公开前提；hA/hvar/hlit 是关于环境的真假设，保留。",
  "已是误差界形式，无需降级；问题在条件化（hMul）而非精确性。",
  "5 个构造子中 lit/var/add/neg 四个是真证，mul 由 hMul 假设；doc 与文件头对此完全一致，不构成隐式过度声称。",
  "非重言：是有内容的归纳证明，只是把最难的分支条件化了。",
  "register：hMul 等于把 mul 分支的目标原样作为前提（自指式降级），且 hcontract 可从 eps/tiny 非负内部推出。登记 PROOF-DEBT：补 mul_error_bound 并删去 hMul/hcontract；在此之前任何把本条当『全语言浮点正确性』的引用都过强。"))

D.append((C + "RealLv00CompilerSpec.lean", 119, "compile_constraint_degenerately_satisfied", "register",
  "对『编译保持源约束语义』这一用途，陈述只讲退化环境 (fun _ => (0,0))，对任意非退化输入无信息；要支撑该用途需要任意 env 的可靠性/完备性。",
  "应有 `compile_constraint_sound : (∃ ir, compile_constraint pts c = some ir ∧ ir_sem env ir) → constraint_sem env c` 与相应的完备性方向；以及说明退化模型为何恒真的 `ir_sem_degenerate`。",
  "h 是必要的命中前提，无冗余前件。",
  "不需要降级（本就不是精确声称）；问题是它把『退化模型存在』包装成编译正确性。",
  "12 条 IR 形状 × arity 确实穷举（含 tangent/ratioDivision 的存在量词形状），但环境固定为退化：覆盖的是编译输出形状，不是语义。",
  "非重言（需要 12 条形状引理），但语义上空：任意编译产物在 (0,0) 下恒真。",
  "register：doc 已诚实标 (B/空洞)，但下游 RealLv00CompilerSat 仍可能把它当编译正确性引用。登记 PROOF-DEBT：补任意 env 的 sound/complete，退化版降为示例。"))

D.append((C + "RealLv00CompilerSpec.lean", 311, "compile_bridge_sem", "register",
  "同 119 条：对任意 pts 都不变（经 ps_irrelevant），但环境仍是退化，对源程序语义无约束，无法支撑编译语义桥接的用途。",
  "同 119 条所需的 sound/complete 桥接定理；本条只应作为 ps_irrelevant 的展示。",
  "h 必要，无冗余。",
  "无需降级；过度声称在名字『bridge_sem』（听起来像语义桥）而非陈述。",
  "pts 任意（经 ps_irrelevant），环境退化——覆盖的是退化模型。",
  "由 119 条直接得到，无独立信息。",
  "register：与 119 条同一债务。名字 compile_bridge_sem 容易让下游误以为完成了编译语义桥接，实际只是退化模型特化；登记 PROOF-DEBT 并考虑改名。"))

D.append((C + "RealNonlinearCompile.lean", 228, "linearization_global_fails", "strengthen",
  "陈述只断言存在 f 与恒零 L，未断言 L 是 f 的线性化/近似（无 ApproxOn、无任何编译函数出现），因此不构成对『线性化编译保全局语义』的反例；必须把近似关系写进陈述才能支撑 users（RealCompileExtractClosed）。",
  "应改为 `∃ f L ε, 0 < ε ∧ (∀ t, |f t − L t| ≤ ε) ∧ (∀ t, L t = 0) ∧ ∃ t, f t ≠ 0`（取 f = 1/(1+t²)、L ≡ 0、ε = 1），或给出 `¬ ∀ f L, (∀ t, |f t − L t| ≤ ε) → (∀ t, L t = 0 → f t = 0)` 在 ε > 0 时的反例。",
  "无可删前件（无前件）。",
  "正是应降级的方向：把『全局不成立』写成『ε > 0 时全局精确零点不可得』的 ε 形式，而不是恒零函数的平凡反例；nonlinear_soundness_local 的 ε 正定理已在文件中，两句才对得上。",
  "存在量词，覆盖无意义。",
  "近乎平凡：任何非零 f 配 L ≡ 0 都满足（f ≡ 1 即可），不携带任何『线性化』信息。",
  "strengthen：反例缺少连接假设 L 为 f 的（全局/有界）ε-近似，现在只证明了『存在非零函数』。改成带 ApproxOn 的反例后，才能与文件头宣称的『全局版不可得、只能局部/ε』一致。"))

D.append((C + "RealWhileTotalCorrectness.lean", 215, "triple_iff_wpT", "register",
  "无强度需求：陈述是定义等价，任何用途都可用 change/rfl 替代，不需要更强。",
  "无缺失（真内容在 triple_while、wpT_while_fixpoint、wpT_while_least）。",
  "无前提。",
  "不适用。",
  "不适用（对任意 P/S/Q 定义成立）。",
  "Iff.rfl：Triple 的定义体就是 ∀ σ, P σ → wpT S Q σ（wpT 定义为 ∃ s, Denotes S σ s ∧ Q s），本条是定义展开，零信息。",
  "register：定义展开冒充定理。建议标为 @[simp] 展开引理或直接内联到 RealWPWhile；不要把它当作『Hoare 三元组与 wp 等价』的独立证据（真正的证据是 180/226/263）。"))

# ---------------- emit ----------------
batch = []
with io.open(SRC, encoding="utf-8") as f:
    for ln in f:
        ln = ln.strip()
        if ln:
            batch.append(json.loads(ln))

keys = [(d[0], d[1]) for d in D]
assert len(keys) == len(set(keys)), "duplicate key"
index = {(d[0], d[1]): d for d in D}

out = []
for o in batch:
    k = (o["file"], o["line"])
    assert k in index, "missing verdict for %s:%s %s" % (o["file"], o["line"], o["name"])
    d = index[k]
    assert d[2] == o["name"], "name mismatch at %s:%s: %s vs %s" % (k[0], k[1], d[2], o["name"])
    out.append({
        "file": o["file"], "line": o["line"], "name": o["name"], "verdict": d[3],
        "A_strength": d[4], "B_missing": d[5], "C_hypotheses": d[6],
        "D_downgrade": d[7], "E_coverage": d[8], "F_content": d[9], "note": d[10],
    })
assert len(out) == len(D), "count mismatch: %d vs %d" % (len(out), len(D))

with io.open(OUT, "w", encoding="utf-8", newline="\n") as f:
    for r in out:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")

from collections import Counter
c = Counter(r["verdict"] for r in out)
print("written", OUT, "n=", len(out), dict(c))
print("nonkeep", sum(1 for r in out if r["verdict"] != "keep"))
