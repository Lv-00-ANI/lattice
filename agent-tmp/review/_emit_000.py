import json

BASE = r"C:\Users\xingg\Desktop\agent\lattice-new\agent-tmp\review"
rows = [json.loads(l) for l in open(BASE + r"\batch_000.jsonl", encoding="utf-8") if l.strip()]

# key = 1-based index in the batch ---- fields: verdict, A, B, C, D, E, F, note
V = {}

def keep(i, note):
    V[i] = dict(verdict="keep", A="", B="", C="", D="", E="", F="", note=note)

def full(i, verdict, A, B, C, D, E, F, note):
    V[i] = dict(verdict=verdict, A=A, B=B, C=C, D=D, E=E, F=F, note=note)

# ---------------- 1..10 ----------------
keep(1, "Tree 是本地嵌套归纳类型（inductive Tree，node : α → List (Tree α)），本定理是真正的结构归纳原理：motive 对所有子树成立的强归纳，经 size_node + size_lt_of_mem 递减闭合。无前件可删（h 承重）。⚠ 解析出的 in_degree=183 不可信——`induction` 与全库同名语法/构造重名；真实引用方只有 Compiler/RealTreeDecidable 与 RealMutualRecursion。")
keep(2, "LvVersion 版本序（三分量字典序）的传递性，真证明（字段展开后 omega 收口，omega 在纯 ℕ 线性算术上是决策过程，无误报可能）。前件 hab/hbc 不可省。⚠ in_degree=136 是重名污染的典型：Geo/Lipschitz.lean 用的是 Nat.le_trans，与 LvVersion 无关。")
full(3, "delete",
     "不适用——这条不是定理。",
     "应补的是被漏解析的真实声明：Geo/FlattenAgreement.lean:53 `flatEquiv_val_eq_seqSlot`（本批未收录）。",
     "无。",
     "不适用。",
     "doc/陈述为散文片段，无覆盖可言。",
     "非陈述：`stmt` = \"theorem rather than a definitional equality. -/\"，取自 docstring 第 52 行。",
     "解析伪条目：Geo/FlattenAgreement.lean:52 是 `flatEquiv_val_eq_seqSlot` 文档注释里的散文（\"...makes the agreement a theorem rather than a definitional equality\"），不是声明；真正的声明在 :53。in_degree=62 与 users 全部是散文中 `theorem` 一词的假匹配，应从统计中剔除，并把 :53 补进来。")
keep(4, "反对称性真实：obtain 三字段后 omega 收口，前件不可省（缺反向后不成立）。与 le_refl/le_trans/le_total 一起构成 LvVersion 的全序，用途（版本比较）与陈述相符。")
full(5, "delete",
     "不适用——这条不是定理。",
     "应补的是被漏解析的真实声明：Slots.lean:297 `weightSemanticsChosen : Slot`（Slot 记录，不是定理）。",
     "无。",
     "不适用。",
     "无。",
     "非陈述：`stmt` 是 Slots 文档注释的散文段落。",
     "解析伪条目：Slots.lean:284-296 是 `weightSemanticsChosen : Slot` 的 docstring，第 287 行 \"theorem stated against that class now applies to networks\" 被误当作陈述。in_degree=37 为假匹配（该文件里 `theorem` 一词出现在注释中）。")
keep(6, "自反性真实（三项析取右支 + Nat.le_refl），无前件，结论即所需。")
keep(7, "`extractVec (convertVec c) = c` 是 record 字段顺序复制的事实（cases <;> rfl），但它是 Lift/Editing 全部闭环定理的承重基座，强度恰好等于需要（无前件可加，也没有更强的形式）。")
keep(8, "Preservation 真实且强于需要：doc 说\"任意步数\"，证明确实给出 `iterate n x = x` 后传递；只用 absorbs，与 doc 的“needs only absorbs”一致。")
keep(9, "缩放不改变解集，`lam ≠ 0` 不可删（lam=0 时右侧退化为 0=0，命题为假）。证明经 dot_map_mul 线性引理 + mul_eq_zero.resolve_right，非平凡；用于构造语义非单射见证，强度够。")
keep(10, "长度对齐下的精确往返（`hn : 0 < n` 不可省：n=0 时 hlen 变为 s.length=0；系数半部走 Nat.div_add_mod，偏置半部走 Nat.add_sub_cancel'），是 WeightLadder 逆映射的核心承重定理。")

# ---------------- 11..20 ----------------
keep(11, "三层链条完整：contraction_pow_bound（幂界）→ geom_contraction_eventually（几何衰减）→ ε-终止；hc0/hc1/hnonneg 均不能由其余前件推出（e ≡ 0, c = -1 是反例），故无可删前件。用途（优化迭代收敛）与强度相符。")
full(12, "strengthen",
     "强度不足：用途是 L1→L2 的语义保持，但陈述建立在被截断的 `VectorConstraintSat` 上（`dot` = List.zip，静默截断到较短表）。`∀ x : List Int` 包含 |x| ≠ |a| 的 ragged 输入，那里满足性为真而语义上应为假——本仓 RealSymbolToWeightWidened.sat_ragged_false_positive 已经机器证明这一点，并指出本定理「两侧共享同一截断缺陷，因此永远抓不到它」。",
     "应存在：`convertVec_preserves_semantics_len (hx : x.length = c.a.length) : VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0`；或直接以同文件的 `VecConstraint.sat_iff_list_sat`（下标化载体、长度自动）为权威桥，另加 `WellFormed c x`（c.a.length = x.length）上的 AllSatisfied 版本。",
     "无前件可删（缺的是加长度/良构前提，属保真加强，不是删假设）。",
     "不适用：问题不是精确→误差，而是语义载体过宽。",
     "声称 ∀x 全称覆盖，实际只有同长输入才有语义意义；ragged 输入上陈述为真却是假阳性。",
     "非重言（连接两个不同定义），但只需 simp：convertVec 是字段拷贝、LayerOut 是 dot 展开，等于定义展开级内容。",
     "同一根因也落在 #13 上。建议把长度对齐版提升为权威语义桥，List 版降级为 legacy 并在 doc 中写明「不含 ragged 输入」。")
full(13, "strengthen",
     "强度不足：名字声称 symbol→weight 的正确性，实际内容是「∀-map 分配（forall_mem_map_iff）+ 逐元素 rfl 级桥」，而且它认证的满足语义带有截断假阳性。本仓 RealSymbolToWeightWidened 已逐条给出消融：删掉逐元素桥则命题为假 ⟹ 「原定理的全部内容都集中在这个 rfl 桥上」；并给出 layer_ragged_also_zero 说明两侧共享缺陷、定理无诊断力。",
     "应存在：`symbolToWeight_correct_wf (hwf : ∀ c ∈ cs, c.a.length = x.length) : AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x`；以及一个良构谓词 `WellFormed cs x` 与其单调性引理（编译保持良构）。",
     "无前件可删。",
     "不适用。",
     "doc 为空，但名字（…_correct）覆盖过宽：对 ragged x 该「正确性」不成立（cs 被空输入满足）。",
     "逐元素桥为定义展开；主定理内容只是 map 上的 forall 分配，属薄胶水。",
     "与 #12 同一根因，修 #12 即修此条；在此之前下游（RealChainAxioms、RealEndToEnd 等）不应把 L1⇄L2 语义保持当作已闭合结论引用。")

# ---------------- 14..23 ----------------
keep(14, "softmax 归一性真实（Finset.sum_div + field_simp，需要 [Nonempty ι]，由文件 section 变量给出，故陈述未隐藏假命题）。用途（注意力输出的概率权重）与强度相符。")
keep(15, "指数 Markov 尾界真实：滤波集包含（exp 单调）→ 概率单调 → markov_counting，链条完整。hlam 可弱化为 0 ≤ lam（lam=0 时等号成立），但那是可选优化，不是缺陷。")
keep(16, "Repair.progress 真实：对 μ 的强归纳，motive 量化当前点，结论经 iterate_succ 搬运；承重前件是 Repair 结构的 absorbs/decreases/atomic（atomic 的不可导性已在 Slots 登记），本定理没有把它们偷偷用成结论。")
keep(17, "分母正（Finset.sum_pos + univ_nonempty），真实且是 softmax 各定理的基座；[Nonempty ι] 由 section 给出。")
keep(18, "全序性真实（Nat.lt_trichotomy 三分 + 平铺三项析取归类）。doc 记载的两个陷阱（Lv-00 原证明四个 Or 的右支；定理名遮蔽 Nat.le_total）都是真实风险记录，不是掩盖。")
keep(19, "类型进度真实：对 HasType 归纳，逐构造子用 canonical_forms_int/real + 相容规则，无 sorry 无可疑前件。对象语言是极小 IR（只有字面量/add/cmp，无变量/无 λ），doc 未夸大，故不算半成品。⚠ in_degree=9 被 Core/Repair.progress 同名污染。")
keep(20, "STLC 进度真实：app 分支靠 canonical_abs 闭合（左子项为值时类型迫使它是 λ），app_fun 规则的存在被 doc 正确说明为封闭该分支所需。")
keep(21, "语法级左逆，真（列表归纳 + roundtrip_extractVec）。doc 诚实标注「两侧只是 record 字段重命名，见 §7」，因此作为语法恒等引用是准确的；不应被当作语义结论。")
full(22, "register",
     "陈述与用途（L0⇄L1 往返义务的 API 名）相称，但内容为结构字段投影：`T.roundtrip d`。",
     "缺真实分词器的往返实例：如 `wordPiece_roundtrip`、`bpe_roundtrip`（非 identity 的 Tokenizer  inhabitant），以及 `decode_encode_on_image`（decode∘encode 之外的充分性）。",
     "无前件可删。",
     "不适用。",
     "覆盖名义 1/1（唯一实例 identityTokenizer，其 roundtrip 为 rfl），实质有内容的实例 0/1。",
     "只复述假设：证明即 `T.roundtrip d`。",
     "doc 本身是诚实的（\"named lemma so that downstream can cite it by name\"），故不删；但必须登记：L0⇄L1 这一跳是 assume 的，唯一见证是 identity（rfl）。下游 RealChainAxioms2 / RealEndToEnd 不得据此称「分词无损已证」。")
keep(23, "集级往返真实且是 L1⇄L2 的真内容：encode_cons_eq + toSegs_map_sym_append_sep + mkConstraint_append_singleton 三步互逆引理，按列表归纳闭合；结论包含顺序与每个 (a,b)，与 doc 一致。")

# ---------------- 24..33 ----------------
keep(24, "分词永不失败真实且非平凡：foldBlanks 不增长度 ⟹ 燃料 s.length+1 充分 ⟹ tokAux_ne_none；再对 tokAux 结果分情形消去 none。结论与 doc 完全对应。")
keep(25, "凸组合范数界真实：norm_sum_le → |w_i| = w_i（hw0）→ 逐项乘 M → 提因子（hsum）；hw0/hsum/hV 三者均不可省。")
keep(26, "单步保持真实：对 Step 归纳，求值规则由字面量定型给出，相容规则用归纳假设；与 #19 配对即该 IR 的类型可靠性。")
keep(27, "STLC 保持真实，beta 分支承重于 subst_preserves_typing；doc 关于 revert ht / generalizing A 的说明准确（HasType 的环境与类型都是索引）。")
keep(28, "语法级右逆，真（列表归纳 + 结构 eta）。与 #21 合起来给出 compileToLayer 的双射（#42）。doc 同样诚实标注字段重命名。")
keep(29, "FCA 外延反单调真实（4 行，intro/apply 直接闭合），是闭包算子（#62）的必要组件。")
keep(30, "FCA 内涵反单调真实。")
keep(31, "外延-内涵广泛性 `O' ⊆ extent (intent O')` 真实（4 行），与 #29/#30 一起给出 extent∘intent 的闭包性质。")
keep(32, "KL 的对数比展开真实：先 kl_as_sum_log_sub_log，再用 Real.log_div（hp0/hq0 保证分子分母非零）。")
keep(33, "KL 非负真实，由 ce_ge_entropy 收口；正性与两条归一化前件都是必要的（否则 log 与不等式都不成立）。")

# ---------------- 34..43 ----------------
keep(34, "由往返字段导出编码单射：单射性并不在字段里，是真实的逻辑内容（Option.some.inj）。作为 T 的通用引理成立，前件不可省。注意其可信度继承 #22 的 caveat（roundtrip 是假设）。")
keep(35, "ReLU 零点判据真实：max x 0 = 0 ↔ x ≤ 0，两个方向都逐条证；用途（ReLU 层稀疏性/激活判定）与该形式匹配。")
keep(36, "符号编码单射，真（两次 decode_encode + Option.some.injEq），对下游「符号信息无损」是可用的精确表述。")
keep(37, "真实：translate_ne_self 给出「对象不同」，holds_translate_iff_of_translatable 给出「可平移约束逐点同值」。⚠ 名字声称 semantic_not_injective，陈述本身只给不变性 + 差异两个合取项，¬Injective 是两行推论、未单列；名字略强于陈述，但陈述没有说谎（且下游可两行导出），故不按错误计。")
keep(38, "sigmoid 严格落在 (0,1)：两个方向分别用 div_pos 与 div_lt_one，真实；∀x 覆盖完整。")
keep(39, "softmax 非负真实（exp 正 + 分母正），需要 Nonempty（section 给出），覆盖 ∀i 完整。")
keep(40, "具体见证成立且三项分别真：语法不同（[1]≠[2]）、层不同（经 compileToLayer_injective）、语义相同（scaleVec_preserves，lam=2）。doc 诚实标注「不是发现，已登记」，属准确引用。")
keep(41, "双侧 Hoeffding 真实：A ⊆ B ∪ C 分情形 → 概率单调 → 次可加 → 两侧单边界；指数 -n t²/8 是有效（较松）的常数，未夸大。hn/hN/hmean/hb 不可省。")
keep(42, "双射真实（extractLayer 同时是左逆与右逆），doc 自陈「成立正因两侧只是 record 字段重命名」，属如实标注，不构成过度声称。")
keep(43, "权重层语义非单射的机器见证：convertVec r03C 与 convertVec (scaleVec r03C 2) 层不同、作为函数逐点相等；两个方向分别靠 convertVec_injective 与 convertVec_preserves_semantics + scaleVec_preserves，是真合成。")

# ---------------- 44..53 ----------------
keep(44, "Int 上 foldl 初值可提（线性累加），真：归纳 + ring 收口；是 dot 线性引理（scaleVec_preserves）的支撑。")
keep(45, "语义非单射的独立见证（arity 入类型后仍在 arity 1 上给出 unitForm/scaledForm），真：unit_ne_scaled 比较系数（不是常数，doc 说明了为何），scaled_semEq_unit 由 semEq_scale 给出。")
keep(46, "平方距离非负真实（sqNorm_nonneg），无前件，用途（约束非退化前提）与强度相符。")
keep(47, "rho 非负真实：空索引 split 情形分别处理（空集走 le_rfl，非空走 sup' 取值 + abs_nonneg），非平凡无漏洞。")
full(48, "register",
     "形式与用途（Geo 层统一用 fix^[n] 记号）相称，但无独立内容。",
     "不需要新定理；需要的是消除双入口——`Repair.iterate` 与 `fix^[n]` 定义等价，应只保留一个（在 Core 内直接给 `fix` 版，或让 Geo 层直接用 iterate）。",
     "无前件可删。",
     "不适用。",
     "覆盖完整（与 progress 同命题），但覆盖的是同一件事。",
     "定义等价：`iterate n x := Nat.iterate R.fix n x`，而 `R.fix^[n] x` 就是 `Nat.iterate R.fix n x`，证明一行 `R.progress x`。",
     "与 Core.Repair.progress 定义等价，属 API 别名；保留会增加「又一条收敛定理」的账面，建议合并（register 而非 delete，因为改名涉及 4-5 处调用点）。")
full(49, "delete",
     "不适用（重复）。",
     "无需新增：Lattice.Geo.sqDist_nonneg 已存在，本文件经 Geo/Constraint → Geo/Dist 已能引用。",
     "无。",
     "不适用。",
     "覆盖与 Dist:65 完全相同。",
     "逐字重复（同陈述、同 4 行证明），位于 `Lattice.Geo.RepairCoverage` 命名空间下。",
     "与 Geo/Dist.lean:65 的 `Lattice.Geo.sqDist_nonneg` 重复；本文件 imports Lattice.Geo.Constraint（其 imports Lattice.Geo.Dist），原名已在作用域内。删除副本改引用原名，避免第二个权威。")
keep(50, "matCLME 作用等于 matvecE（LinearMap.mkContinuous_apply + rfl），是真实的定义等式；下游谱/稀疏性引理需要它把抽象算子范数落到矩阵向量乘上。")
keep(51, "算子范数 ≤ Frobenius 范数，真（mkContinuous_norm_le + frobenius_bound + frobeniusNorm_nonneg），是压缩与谱估计的标准界，强度与用途相符。")
keep(52, "连续线性映射 Lipschitz，真：map_sub + le_opNorm。是最常用的一行引理，无前件可删。")
keep(53, "RoPE 相对位置不变性真实：旋转可复合（rotate_compose）+ 旋转保内积（rotate_preserves_dot），得出 rdot(rot mθ q, rot nθ k) = rdot(q, rot((n-m)θ) k)，符号正确、无遗漏。")

# ---------------- 54..63 ----------------
keep(54, "链尾局部编辑的乘积界，真实：把 Fs (k+j) 平移进 chainN_error_bound，hk/hL/hL0 均必要（hL0 供乘积非负放大）。结论即所需（局部性界），无过强声称。")
keep(55, "Bool↔Prop 桥，simp 关闭，内容薄但真实且是 parted 文件（A/B/C/D）的唯一胶水；定义展开级正是它该有的强度。")
keep(56, "同 #55，`extra` 参数保留时闭包谓词退化到上游谓词，桥接真实。")
full(57, "register",
     "与 #55 内容相同（同名、同陈述、同 simp 证明），只是命名空间不同。",
     "缺的是合并，不是新定理：Closure 版（:74）与 Jia 版（:757）各自依赖自己那份 `AxiomPackageInstance`（Jia:76 自建，Closure 用 import RealLv00AxiomDischargeInstances）。",
     "无前件可删。",
     "不适用。",
     "各自命名空间内覆盖完整，但全库出现两个权威（两份 package 结构 + 两份谓词 + 两份桥）。",
     "定义展开级（simp），无独立数学内容。",
     "登记为「复制-分叉模块」债务：Jia 文件是 Closure 的 fork（同名字段、同名谓词、同名定理），两条桥与两份结构必须一起收敛；现在改任一侧都会静默失配。")
full(58, "register",
     "与 #56 内容相同（含 extra 的闭包谓词桥），命名空间不同。",
     "同 #57：合并两份 `AxiomPackageInstance`/谓词，或让 Jia 直接复用 Closure。",
     "无前件可删。",
     "不适用。",
     "各自命名空间内完整，全库重复。",
     "定义展开级（simp [.. DependenciesClosed, LegalNames]）。",
     "同 #57 的 fork 债务（含 extra 版本）。")
keep(59, "类型可靠性（永不卡死）真实：multistep_preservation 把类型搬到任意多步后的项上，再跑 progress；正是两半定理交替使用，doc 描述准确。")
keep(60, "Hoeffding 引理真实：凸性弦线（convexOn_exp）给出逐点界，求和用 hzero 归零，常数 e^{λ²/2} 与 |X|≤1 匹配。hN/hzero/hb 均不可省。")
keep(61, "‖k₀‖² ≠ 0 由范数零判据 + pow_ne_zero，真实；是 ROME/编辑串扰里分母安全的前提，虽然短但承重。")
keep(62, "extent∘intent 幂等真实：两个方向分别由 extent_antitone + subset_intent_extent / intent_antitone + subset_extent_intent 给出，是闭包算子的核心一环。")
keep(63, "intent∘extent 幂等真实（内部算子侧），与 #62 对称、两方向都用反单调 + 广泛性，证明无缺口。")

# ---------------- 64..73 ----------------
keep(64, "KL=0 ⟺ p=q 真实：先化到 support 形式（kl_zero_iff_support），再用 hp0 排除 p a=0 的分支、归一化保证和为零。前件（正性 + 归一）不可省，非平凡。")
keep(65, "作为 `Lattice.Lib.Penalty` 层的重导出，真（主体在 Lift/PenaltyAnalysis:89）；用途是分层命名空间，可接受。⚠ 同一陈述在两处（#70），应择一为权威、另一处只 import。")
keep(66, "n 层量化误差闭式界，真实：三角不等式逐层放大 + 闭式求和相等（le_of_eq of quantErrBound_closed）。doc 关于「后层放大、前层放缩输入」的解释与求和式一致，属恰当陈述（本就是界，不存在精确声称）。")
keep(67, "Int 上 a²=0 ⟺ a=0，真（pow_two + Int.mul_eq_zero）；短但真实，是约束嵌入（平方惩罚）的基座。")
full(68, "delete",
     "不适用：doc 声称 end-to-end soundness（三跳），陈述只触及最后一跳；命题本身没有可加强的余地。",
     "真正的端到端已存在：同文件 :167 `ladder_compose_soundness`（l0l1.encode → l1l2.decode → l2l3），以及 :187 `ladder_compose_roundtrip`。本定理无需补充，应退役。",
     "无前件可删（hsat 是唯一的真前提）。",
     "不适用。",
     "doc 声称覆盖三级阶梯，证明只用 `L.l2l3_sound s hsat` 一节；l0l1/l1l2 完全未参与。",
     "只投影结构字段：证明体 = `L.l2l3_sound s hsat`；doc 的「does not collapse into a restatement of l2l3_sound」为假——它就是该字段。",
     "教科书式的「有名字、当完成」：名字与 doc 借了端到端的重量，内容是一条字段投影（对比同文件 :181 的自陈「two field projections rather than an argument」）。删除后调用方直接引 `L.l2l3_sound`，端到端引 `ladder_compose_soundness`。")
full(69, "delete",
     "不适用——这条不是定理。",
     "应补的是被漏解析的真实声明：Lift/Extraction.lean:148 `scaledForm`、:154 `unit_ne_scaled`、:163 `scaled_semEq_unit`。",
     "无。",
     "不适用。",
     "无。",
     "非陈述：`stmt` = \"lemma applies definitionally rather than needing a structure extensionality step...\"（docstring 散文）。",
     "解析伪条目：Lift/Extraction.lean:145-147 是 `scaledForm` 的 docstring，第 146 行散文以 \"lemma applies definitionally...\" 开头被误判为声明。in_degree=5 为假匹配。")
keep(70, "非零导数处平方惩罚精确性，真：sq_localMin_dichotomy 两分支，一支给出 f x = 0，另一支与 hne 矛盾；hne 不可省（f 为仿射非零斜率时 f² 在 f=0 处才取极小）。与 sound_not_exact 反例互补，doc 准确。")
keep(71, "全局最小 ⇒ 局部最小，一行（Filter.Eventually.of_forall）但真实，且 doc 明说对任意拓扑空间 + 预序成立，避免了 ℝ 特化重复；用途（惩罚嵌入的极小点构造）与该强度匹配。")
keep(72, "实数约束 ⟺ 单神经元输出为零，真实（定义展开），是 RealLV/编译器一侧的语义基座。")
keep(73, "ReLU 非负（le_max_right），真；短但被 5 处用于激活界，属恰当的最小引理。")

# ---------------- 74..80 ----------------
keep(74, "定量收敛（μ x 步内必达），真实：归纳得「前 n 步皆失败 ⟹ μ 至少降 n」，取 n=μ x 后由 atomic 得矛盾。比 progress 强且是它的定量形式，doc 与证明一致。")
keep(75, "GeoExpr.add 的 Lipschitz 常数相加，真：值差可加 + abs_add + linarith；K₁+K₂ 正是所需常数，无过强声称。")
keep(76, "ReLU 的软掩码实例真实：分解 relu = s(x)·x（relu_mask_decomposition）+ 0 ≤ s ≤ 1；SoftMasked 是三合取谓词，非重言。")
keep(77, "GELU(tanh) 的软掩码实例真实：分解由 ring 收口，掩码界由 gelu_soft_mask_bounds 给出。")
keep(78, "SiLU 的软掩码实例真实：分解为 ring，界用 sigmoid_bounds 的严格不等式（故给出 0 < s < 1，比需要的 0 ≤ s ≤ 1 更强）。")
keep(79, "泛函版 Lipschitz 相加（范数三角不等式 + abel 重排），真；与 #75（GeoExpr 版）不同层，不构成重复。")
keep(80, "Frobenius 范数平方 = 逐项平方和，真（Real.sq_sqrt + 非负性）；是 opNorm_le_frobenius 与 Eckart-Young 一侧的基座。")

assert len(V) == len(rows) == 80, (len(V), len(rows))

out = []
for i, r in enumerate(rows, 1):
    v = V[i]
    out.append({
        "file": r["file"],
        "line": r["line"],
        "name": r["name"],
        "verdict": v["verdict"],
        "A_strength": v["A"],
        "B_missing": v["B"],
        "C_hypotheses": v["C"],
        "D_downgrade": v["D"],
        "E_coverage": v["E"],
        "F_content": v["F"],
        "note": v["note"],
    })

dst = BASE + r"\verdicts_000.jsonl"
with open(dst, "w", encoding="utf-8") as f:
    for o in out:
        f.write(json.dumps(o, ensure_ascii=False) + "\n")

from collections import Counter
c = Counter(o["verdict"] for o in out)
print("written", dst, "lines", len(out))
print(dict(c), "non-keep", sum(1 for o in out if o["verdict"] != "keep"))
