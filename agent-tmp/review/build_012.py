# -*- coding: utf-8 -*-
import json, io, os

BATCH = r"C:\Users\xingg\Desktop\agent\lattice-new\agent-tmp\review\batch_012.jsonl"
OUT = r"C:\Users\xingg\Desktop\agent\lattice-new\agent-tmp\review\verdicts_012.jsonl"

# i -> (expected name, verdict, extra dict)
# extra may contain A_strength..F_content and note; missing keys filled by defaults.
V = {}

def add(i, name, verdict, note, **kw):
    V[i] = (name, verdict, note, kw)

# ---------------- keep ----------------
add(1, "natTransform_compile", "keep",
    "分片编译与整体编译一致；证明显式用 List.map_append（刻意不用 simp），真且够用（用户只需 map 对 ++ 的分配律），非重言。")
add(2, "galois_preimage_comp", "keep",
    "两次 gc.le_iff_le 复合成反序伴随 l₂∘l₁ ⊣ u₁∘u₂，真实非平凡，参数顺序正确。")
add(3, "roundTrip_eq_self", "keep",
    "roundTrip 定义下的往返恒等（由既有 extractLayer_compileToLayer 给出）；作为接口事实在 18 处真实使用，不是 a=a。",
    F_content="非 a=a：roundTrip 定义下的往返恒等")
add(4, "edit_output_bound", "keep",
    "即 (W'-W).le_opNorm 的展开形式，是残差估计所需的精确算子范数界；有实际内容。")
add(5, "applyEdit_writes_fact", "keep",
    "写入性质的精确等式；hk 不可删（k₀ = 0 时除零）；RealEditOrder:195 真实使用。")
add(6, "dot_nil_right", "keep",
    "dot 在第二参数为空时为零（zip 截断）；本文件 :281 真实使用；与 _s01/s02 重复但已显式登记。",
    F_content="非重言（zip 截断），与 _s01/s02 重复但已登记")
add(9, "editLayerList_outputs_eq_iff", "keep",
    "充要条件两向都真；ls = [] 边界与 DeltaCompatible 前提都是必需的（同文件另有双向为假的反例）。")
add(10, "editLayer_zero_delta", "keep",
    "长度对齐下的零增量恒等；需归纳，且反例（dw = [] 的截断）已由邻近定理钉死。")
add(11, "editLayer_nil_dw_not_identity", "keep",
    "机器验证的反例：dw = [] 不是恒等编辑；≠ 型命题有真实内容。")
add(12, "editConstraint_preserves_delta", "keep",
    "符号侧与权重侧共用同一 δ；真实跨模块主结论，长度前提不可删；RealEndToEndNontrivial:473 真实使用。")
add(13, "editSemantics_layer_zero_iff", "keep",
    "层输出为零 ⟺ CLM 形为零的接口等价（由既有 layerOut_zero_iff_clm 转写）；内容真实，但唯一引用是 #print axioms，属审计引用而非数学消费者。",
    A_strength="够用；但唯一引用是 #print axioms，属审计引用")
add(14, "edit_two_step", "keep",
    "三角不等式的精确实例，是两条序列界的地基；真实。")
add(15, "edit_seq_bound", "keep",
    "归纳得 n·δ 界；RealOrphanWiring:357 真实使用。")
add(16, "edit_seq_nonuniform", "keep",
    "非一致步长的 Σ δᵢ 界，比 uniform 版更紧；RealOrphanWiring:193 真实使用。")
add(17, "roundtrip_convertVec_rfl", "keep",
    "结构 eta（cases 后 rfl），是 extractVec/convertVec 往返的权威接口，被 13 处使用；定义相等但非 a=a。",
    F_content="定义相等（cases 后 rfl），非 a=a；作为权威改写接口使用")
add(18, "canonical_eq_none_of_not_contentOk", "keep",
    "canonical 的 dif_neg 分支；真实接口事实（无代表时返回 none），供主反例非退化。")
add(19, "layerContentOk_layerAB", "keep",
    "具体实例的内容非零；显式证以保证主反例不退化为 none = none。")
add(20, "layerContentOk_layerBA", "keep",
    "同上，顺序对调的实例；反例的另一半，必需。")
add(21, "R02_layer_canonical_not_unique_perm", "keep",
    "真否定命题：约束集合相同（集合意义）而 canonical 不同；证明不依赖语义约定，且两侧都非 none（由 19/20 保证）。")
add(22, "leftInverse_iff_injective", "keep",
    "一般集合层判据，双向都真；[Nonempty α] 必需（余域外取值需要选择），不可删。")
add(23, "relu_neg_eq_relu_zero", "keep",
    "具体数值反例，真实。")
add(24, "relu_not_injOn_nonpos", "keep",
    "由 23 得到的区域不可逆性；真实。")
add(25, "tanh_strictMonoOn_Ici_zero", "keep",
    "真解析定理（sinh 差恒等式 + div_lt_div_iff₀），非平凡。")
add(26, "geluGate_nonneg", "keep",
    "0 ≤ geluGate 0 的精确实例，正是 strictMonoOn_mul_of 需要的 hgate0；名字较宽但 doc 与陈述一致（只声称 x=0 处）。",
    E_coverage="doc 与陈述都只声称 x=0 处，名字比陈述宽")
add(27, "geluGate_pos_of_pos", "keep",
    "由 tanh 正性 + linarith 得；真实，且是门控三前提之一。")
add(28, "geluGate_monoOn", "keep",
    "真单调性（tanh 严格单调 + 线性组合）。")
add(29, "geluTanh_strictMonoOn", "keep",
    "由 strictMonoOn_mul_of 组合，无条件；真实。")
add(30, "geluTanh_injOn", "keep",
    "strictMonoOn ⟹ InjOn 的直接推论，无条件版；真实。")
add(31, "extractVec_injective", "keep",
    "真单射（cases + mk.injEq），是 R-03 的反驳；RealExtractSurjectivity 另有同命题的 extractVec_injective_layer（自包含重复，不影响正确性）。",
    F_content="非重言（单射性）；与同文件的 extractVec_injective_layer 重复")
add(32, "extractVec_range_eq_univ", "keep",
    "满射的等式形式，真（由 extractVec_exists_preimage）；doc 已如实标注其平凡性，属诚实的对照件。",
    A_strength="够用（doc 明确只作消融对照）", F_content="真但平凡（满射）")
add(34, "extractLayer_surjective", "keep",
    "列表级存在性，真（compileToLayer_extractLayer）；doc 如实标注平凡，不作过度声称。",
    F_content="真但平凡（存在性）")
add(35, "convertVec_extractVec_rfl", "keep",
    "定义 eta（cases rfl），convertVec 右逆的权威接口；RealCanonicalCompileComm:154 另有同名声明（重复），但陈述真实且被多处使用。",
    F_content="定义 eta（cases rfl），非 a=a")
add(37, "extractVec_respects_semEq", "keep",
    "SemEqL → 逐点 LayerOut → 两次 convertVec_preserves_semantics；semConv_injective 的承重一步，真实。")
add(38, "semConv_injective", "keep",
    "用 Quotient.exact/sound 完成下降单射；真实非平凡，与 doc 的读法 B 一致。")
add(39, "extract_idempotent", "keep",
    "闭包算子幂等（FCA 事实回收），真实且用于装配 ClosureOperator。")
add(40, "closureOperator_extensive", "keep",
    "扩张性，真，用于装配 ClosureOperator。")
add(41, "closureOperator_monotone", "keep",
    "单调性（intent/extent 两次反变），真，用于装配。")
add(42, "canonicalize_respects_scaleClassPlus", "keep",
    "下降所需的精确律；hg/hg' 不可删（canonicalize_section_pos 需要），真实。")
add(43, "relu_not_injective", "keep",
    "真（−1 ≠ 0 同像）；注意其 in_degree 指向 Core/Net，而该文件 :76 是自己同名的局部定理，引用疑似同名碰撞。",
    A_strength="够用；in_degree 指向 Core/Net 的同名局部定理，疑似碰撞")
add(44, "roundTripAddsNothing_of_factorsThrough", "keep",
    "一般充分条件（纤维稳定 + P 分解），真实非平凡；RealRflAudit:271 真实使用。")
add(46, "roundtrip_error_bound", "keep",
    "误差界精确（≤ ε₁X + ε₂），hypotheses 不可删；真实。")
add(47, "extract_lipschitz_one", "keep",
    "等距的直接推论（≤ 版），真实；目前只有注释级引用，无证明消费者。",
    A_strength="够用；但只有注释级引用")
add(48, "s02_dot_nil", "keep",
    "真（zip 截断），本文件内被大量真实使用；与 dot_nil_right/_s01 重复，属已知登记项。")
add(49, "s02_dot_cons_cons", "keep",
    "真展开律（需 foldl_init_add 提出累加器）；真实使用。")
add(50, "s02_dot_two_cons", "keep",
    "真展开律；三处使用。")
add(51, "s02_dot_two_eq_form", "keep",
    "对任意 a 的三情形统一等式，真；doc 诚实标注尾部非空时为假并只用空尾部，覆盖与陈述一致。")
add(52, "s02_single_constraint_incomplete", "keep",
    "真否定命题（¬∃ 单约束实现），三步矛盾法完整，是核心反例。")
add(54, "reluZ_counterexample", "keep",
    "机器验证反例（非线性层零输出 ≠ 约束满足）；真实。")
add(55, "zeroFixing_of_strictMono", "keep",
    "充分条件，真；RealNonlinearFidelity A.lean:267 真实使用。")
add(56, "sat_iff_residual", "keep",
    "定义展开（Iff.rfl），内容即定义；作为改写引理被 RealCrossUniverseConsumer:185/194 真实使用，不是占位。",
    F_content="定义展开（Iff.rfl），内容即定义；作为改写引理真实使用")
add(57, "dot_nil_right_s01", "keep",
    "真（zip 截断），本文件 :401 真实使用；与 s02/dot_nil_right 重复，已登记。")
add(58, "sat_ragged_false_positive", "keep",
    "机器验证的假阳性（空输入骗过双变量约束）；真实反例，被 ConvertVectorLinear 作为缺陷基准引用。")
add(60, "constraint_entailment_closure", "keep",
    "intent∘extent 的定义展开（rfl），作为「后承 = 内涵闭包」的接口被 RealFCAElementApplication:170 真实使用。",
    F_content="定义展开（rfl），内容即定义；作为接口改写引理使用")
add(61, "not_andC_zero_iff", "keep",
    "真（De Morgan 式），双向都用 real_andC_eq_zero_iff。")
add(62, "ce_eq_zero_iff_support", "keep",
    "真充要刻画（逐项非负 + 和为零）；与 doc 一致。")
add(63, "softmax_ce_directional_deriv", "keep",
    "真方向导数（链式 + 商法则）；RealContrastive:209 真实使用。")
add(64, "channelPush_pos", "keep",
    "真（有限个正项之和）；多处使用。")
add(65, "dp_eq_of_ratio_constant", "keep",
    "DPI 等号后向方向，真；hypotheses（正性、归一、行随机）不可删。")
add(66, "logsum_le", "keep",
    "真 log-sum 不等式（Gibbs），证明完整。")
add(67, "tv_data_processing", "keep",
    "真 TV 数据处理不等式；对 q 无额外假设（更一般）；RealConversionStabilityInformation:139 真实使用。")
add(68, "elbo_le_log_marginal", "keep",
    "真（ELBO ≤ log Z，由 KL 非负）；多处使用。")
add(69, "em_posterior_optimal", "keep",
    "真（最优性 + 取等刻画），两合取项都由既有定理闭合。")
add(70, "elbo_eq_sum_log_p_add_entropy", "keep",
    "真代数恒等式。")
add(71, "entropy_concave", "keep",
    "真凹性（KL 非负 + 混合恒等式）；hypotheses 必需。")
add(72, "kl_pos_of_ne", "keep",
    "真严格正性（非负 + 取等条件）。")
add(73, "entropy_concavity_strict", "keep",
    "真严格凹性；端点假设正确。")
add(74, "entropy_concavity_eq_iff", "keep",
    "真取等刻画；三个析取项覆盖 lam=0/1 与 p=q 边界。")
add(75, "kl_as_fdiv", "keep",
    "真实例（f-散度取 t log t）；RealFenchel:142 真实使用。")
add(76, "fisherMatrix_symm", "keep",
    "真对称性（乘积交换）。")
add(77, "fisherQuadForm_eq_fisherMatrix", "keep",
    "真二次型恒等式（三重和交换），非平凡。")
add(78, "fisherMatrix_psd", "keep",
    "真 PSD（逐项非负 + 二次型恒等式）；hp 必需。")
add(79, "fisherMatrix_zero_direction_score", "keep",
    "真（零方向 ⟹ score 为零），用平方和逐项为零的论证。")
add(80, "fisherMatrix_eq_fisherInfo_one_dim", "keep",
    "真一维退化兼容性（n=1 时 logScoreAt = score）。")

# ---------------- strengthen ----------------
add(8, "EditLayer_delta_not_unique", "strengthen",
    "建议加强为「存在相容增量但不还原 W」的形式；现状是两条互不相关的平凡事实之合取（把 EditLayer 换成 True 结论照样成立），作为判据 1 的接口层读数名不副实，且唯一引用只是 RealChainAxioms3 的 #print axioms。",
    A_strength="不足：结论 deltaOf Δ₁ x ≠ deltaOf Δ₂ x 与 EditLayer 合取项完全无关（Δ₁=⟨[1],0⟩、Δ₂=⟨[0],0⟩ 在任意 W 下都给出 1 ≠ 0）；因此它没有机器验证 doc 声称的「EditLayer_consequence 的 ∃ Δ 不能换成 ∀ Δ」。",
    B_missing="缺更强的陈述：∃ W Δ, DeltaCompatible W Δ ∧ editLayerList W Δ ≠ W（存在与 W 相容却不还原 W 的增量），或等价地 ∃ W, EditLayer W W ∧ ¬ ∀ Δ, DeltaCompatible W Δ → W = editLayerList W Δ。",
    C_hypotheses="无前件可删（原本就没有假设）。",
    D_downgrade="不适用。",
    E_coverage="doc 声称反驳 ∀ 量化，陈述只到「两个 δ 取值不同」，覆盖不足。",
    F_content="有内容但几乎不依赖 EditLayer：把 EditLayer 换成 True 结论照样成立，不能承重。")

# ---------------- delete ----------------
add(33, "extractVec_range_ne_proper", "delete",
    "纯改写前一条定理（等价于 ¬(s ⊂ s)），doc 自认「本条不新」；in_degree 的 1 是 RealSeamBridges2 的注释引用，没有证明消费者。删除不影响任何结论，保留只会继续充当「有名字 = 有结果」的计数单位。",
    A_strength="不适用（无实质内容）。",
    B_missing="不需要补；若要对照直接用 extractVec_range_eq_univ。",
    C_hypotheses="无。",
    D_downgrade="不适用。",
    E_coverage="doc 自认本条不新，与陈述一致——但这正说明它没有覆盖面。",
    F_content="重言式改写：由 range = univ 得 ¬(univ ⊂ univ)，证明只有 rw 与 lt_irrefl，零信息。")
add(36, "renderSurjective_holds", "delete",
    "doc 自己写「空洞真」并承认不含抽取能力的信息；in_degree 的 1 是 RealClosureReversibility 的注释引用。建议删除，只保留 ExtractionComplete 的反例作为真结论。",
    A_strength="不适用（命题无信息）。",
    B_missing="要补的是有内容的完备性判据；本命题方向不对（文件已证 ExtractionComplete 为假，那才是真结论）。",
    C_hypotheses="无。",
    D_downgrade="不适用。",
    E_coverage="doc 说它覆盖任意约束集，但见证恒为 encode cs——覆盖全场而零信息。",
    F_content="空洞真：任何有 section 的全函数都满足，与「抽取能恢复什么」无关。")

# ---------------- register ----------------
add(7, "dot_append_of_length_eq", "register",
    "与 Lib/Editing/RealSymbolToWeightWidened.lean:304 同名同义重复；两文件互不 import，文件内也没有证明使用（in_degree=1 是同名声明碰撞而非语义引用）。doc 把它当「承重件」，实际是死件 + 双副本：登记 PROOF-DEBT，建议收敛为一份并接上消费者。",
    A_strength="陈述本身够用；但 doc 称其为 T6′ 与 T1 的承重件，而全库没有任何证明级消费者（本文件里该名只出现在 doc 中）。",
    B_missing="缺单一权威副本（应收敛到 ConvertVectorLinear 一类基座）与至少一个真实消费者；否则不能算承重件。",
    C_hypotheses="h（长度对齐）不可删：邻近文件已给出 a=[1]、b=[]、x=[]、y=[7] 的反例。",
    D_downgrade="不适用。",
    E_coverage="覆盖完整（长度对齐子集），doc 未越界。",
    F_content="非重言：真组合律，证明用 List.zip_append + List.foldl_append + foldl_init_add。")
add(45, "rt2_leftInverse", "register",
    "零新增内容的纯别名，仅作为「实例 2」的标签在 RealRoundTripVacuity:354/363 使用；不影响正确性，登记 PROOF-DEBT（合并或直接引用），不值得现在动。",
    A_strength="陈述就是既有 roundtrip_extractVec 的 LeftInverse 形式，用途也只需要这个别名。",
    B_missing="无需新定理；应直接复用 roundtrip_extractVec，或把两者合并。",
    C_hypotheses="无。",
    D_downgrade="不适用。",
    E_coverage="覆盖完整但无新增内容。",
    F_content="别名：证明体就是 roundtrip_extractVec，与既有定理逐字同义。")
add(53, "s02_twoAxisLayer_needs_two", "register",
    "定理本身真且三个合取项都被用到，但 doc 把它读成一般计数结论（n 个神经元 ⟹ n 条约束），实际只有 2 轴实例；且无证明级消费者（唯一引用是 Meta 文件的注释）。登记覆盖债。",
    A_strength="对「这个 2 轴例子恰好需要 2 条」够；对 doc 末句的一般结论（n 个神经元 ⟹ n 条约束）不够。",
    B_missing="缺一般计数定理：实现 ls 的最少约束条数 = (extractLayer ls).length，或 ∀ ls, ¬∃ c, Realizes c ls → ...；也缺把它接上文件里 Realizes 充要条件的那一步。",
    C_hypotheses="无假设。",
    D_downgrade="不适用。",
    E_coverage="只覆盖 s02_twoAxisLayer 这一个实例；doc 的 n 条推广未形式化。",
    F_content="非重言：三个合取项都有内容（否定 + 存在 + 长度计算）。")
add(59, "dot_append_of_length_eq", "register",
    "与 Lib/Editing/RealEditInvariantCatalog.lean:221 同名同义重复（两文件互不 import）；本文件内该名只出现在 doc 里，in_degree=1 是同名声明碰撞。doc 称「主定理」，实际无消费者，登记重复/死件债。",
    A_strength="陈述本身够用（长度对齐下的组合律）；但 doc 称其为主定理/真推广，全库无证明级消费者。",
    B_missing="缺单一权威副本与真实消费者；与 RealEditInvariantCatalog:221 内容逐字同义，应合并到基座模块。",
    C_hypotheses="h（长度对齐）不可删（dot_append_false 反例）。",
    D_downgrade="不适用。",
    E_coverage="覆盖完整（长度对齐子集），doc 未越界。",
    F_content="非重言：真组合律，证明用 List.zip_append 与 foldl 分裂。")

DEF = {
    "keep": dict(A_strength="够用（无需更强）", B_missing="", C_hypotheses="无可删前件",
                 D_downgrade="不适用", E_coverage="与 doc 一致", F_content="非重言"),
}

with io.open(BATCH, encoding="utf-8") as f:
    batch = [json.loads(l) for l in f if l.strip()]

assert len(batch) == 80, len(batch)
assert set(V) == set(range(1, 81)), (len(V), sorted(set(range(1,81)) - set(V)))

rows = []
for idx, rec in enumerate(batch, 1):
    name, verdict, note, kw = V[idx]
    assert rec["name"] == name, (idx, rec["name"], name)
    base = dict(DEF.get(verdict, {}))
    base.update(kw)
    row = {
        "file": rec["file"],
        "line": rec["line"],
        "name": rec["name"],
        "verdict": verdict,
        "A_strength": base.get("A_strength", ""),
        "B_missing": base.get("B_missing", ""),
        "C_hypotheses": base.get("C_hypotheses", ""),
        "D_downgrade": base.get("D_downgrade", ""),
        "E_coverage": base.get("E_coverage", ""),
        "F_content": base.get("F_content", ""),
        "note": note,
    }
    rows.append(row)

with io.open(OUT, "w", encoding="utf-8", newline="\n") as f:
    for r in rows:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")

from collections import Counter
c = Counter(r["verdict"] for r in rows)
print("wrote", OUT)
print("entries", len(rows), dict(c))
