# -*- coding: utf-8 -*-
"""Emit verdicts_013.jsonl from batch_013.jsonl + hand-written judgments."""
import json, os

D = os.path.dirname(os.path.abspath(__file__))
rows = [json.loads(l) for l in open(os.path.join(D, "batch_013.jsonl"), encoding="utf-8") if l.strip()]

# (name, verdict, A, B, C, D, E, F, note)  -- order == batch order
V = []

def add(name, verdict, A="", B="", C="", Dd="", E="", F="", note=""):
    V.append(dict(name=name, verdict=verdict, A=A, B=B, C=C, D=Dd, E=E, F=F, note=note))

add("neg_log_one_add_ge_half_sq", "keep",
    note="真实标量不等式：hlog : log(1+u) ≤ u 加 hsq : u²/2 ≤ −u（由 −1<u、u≤0 nlinarith）合成。前件 −1<u 正是 Real.log 定义域边界而非可证条件（u=−1 时 1+u=0、log 0=0 结论即假），doc 如实记录了由非严格改严格的更正与下游调用点 u=q_a/p_a−1>−1 的成立性。非重言。")

add("mixDist_pos", "keep",
    note="λ=0 支走 h2，λ>0 支用 mul_pos 与 (1−λ)q≥0；两个前件是 q1/q2 逐点严格正，不可弱化（只给非负时只能得非负）。真实引理，非重言。")

add("ce_not_joint_convex", "keep",
    note="方向正确：CE(p0,p0)=CE(p1,p1)=0，而 CE(mix,mix)=H(1/2,1/2)=log2>0，故「LHS ≥ CE」失败，正是联合凸性不等式被否定。单个 k=2、λ=1/2 见证足以否证全称命题，覆盖充分；证明真正用到 CE 的展开与 log2>0。")

add("gibbsPartition_pos", "keep",
    note="指数和在有指标集时严格正；Nonempty (Fin k) 不可去（k=0 时为空和=0），也不是可从前件推出的。真实基元。")

add("gibbsDist_pos", "keep",
    note="exp/Z，由 Real.exp_pos 与 gibbsPartition_pos 相除；前件承重且不可删。真实。")

add("gibbsDist_sum", "keep",
    note="Σ exp / Z = 1 用 Finset.sum_div 与 div_self（hZ≠0 由配分函数正给出）；Nonempty 承重，否则除零。真实行随机性。")

add("crossEntropy_gibbs", "keep",
    note="核心恒等式，证明逐步 log_div/log_exp 展开后按 hsum 合并常数项：hsum 唯一出现在 −(Σ r)log Z 处，承重且无冗余前件。结论对 RealRegularizedMDP 的指数族刻画够用（「最大熵 = 矩约束」的配套不等式在下一条已在档）。非重言。")

add("prodDist_pos", "keep",
    note="prodDist 定义为两边缘之积，mul_pos 即得；两前件分别对应行/列边缘严格正，缺一不可。doc 为空但陈述自明，是 KL 链式法则需要的真实小引理。")

add("productPlan_isPlan", "keep",
    note="乘积计划三条件逐条给出：逐点非负、行边缘（← mul_sum 与 hq1）、列边缘（← sum_mul 与 hp1）；四个前件都承重。真实可行性基元，供 exists_optimal_plan 取非空见证。")

add("exists_optimal_plan", "keep",
    note="紧集上连续函数取极小点：可行性由 productPlan_isPlan 保证，连续性由 transportCost 的有限和展开给出，结论对任意可行 π' 成立而不越权声称唯一性。真实（依赖 isCompact_setOf_isTransportPlan）。")

add("kp_lipschitz_bound", "keep",
    note="IsOneLipschitz 给 |f a − f b| ≤ |a−b|，le_abs_self 取单侧；只陈述需要的那一侧是合适的（另一侧同文件另有反向引理）。真实。")

add("unique_bayes_admissible", "keep",
    note="huniq 是「严格 Bayes 最优」的正确形式（∀δ', 风险更小 → False），hpos 供 θ₀ 项严格性（mul_lt_mul_of_pos_left）与其余项非负（sum_lt_sum 的配套），结论 Admissible 由反证得到。瑕疵仅为 ProbVec 前件 _hp 未使用（可删、无害），不影响正确性与适用面。")

add("pZobs_eq_sum_sum_obs", "keep",
    note="由「Σx obsXZ = pZobs」（:269 已证）与 obsXZ 的定义展开（rfl）得到，属定义性展开；信息量偏低但它是后门调整推导的直接入口，doc 也如实写明「展开形式」。非重言。")

add("backdoor_adjustment", "keep",
    note="主定理：先用 doY_eq_sum_pZobs_ycond 把截断语义写成 Σ_z pZobs·ycond，再逐点用 pZobs_mul_ycond_eq_condYZ 换成观测条件概率；hpos（∀x z, 0<obsXZ）是重叠/正性假设，用于条件概率良定义。结论是精确等式而非误差界，doc 与证明一致。")

add("constrainedDenom_nonneg", "keep",
    note="分母是 exp 的掩码和，if 两支分别非负/零，sum_nonneg 闭合；确实无需任何假设，doc 的「无假设」名副其实。")

add("constrainedDenom_pos", "keep",
    note="hne 给出一个 exp>0 的被加项，sum_pos' 用它对整和取正；hne 不可去（全 false 时分母=0，见 empty_allowed_row_sum_ne_one）。真实。")

add("constrainedSoftmax_pos_of_allowed", "keep",
    note="ht 供 if_pos，hne 供分母正，div_pos 闭合；结论「允许则严格正」即「未误杀」，前件都承重。真实。")

add("constrainedSoftmax_support_iff_allowed", "keep",
    note="双向完整：→ 用逆否（eq_zero_of_not_allowed），← 用 pos_of_allowed；这是真正的充要条件，排除了「掩码恒零」的退化读法。前件 hne 承重。")

add("constrained_via_maskedSoftmax", "keep",
    note="两侧定义在哑提升下逐字相同，unfold 后 rfl；作为一维/二维定义的唯一桥梁本身是必要的 API（被本文件 20、22 直接消费），doc 也如实标注为「唯一合法桥」。")

add("constrained_sum_one_via_realMaskFamily", "register",
    A="结论与文件内已证的 constrainedSoftmax_sum_one（见 :229 之后 #print axioms 列表）同型同义，强度上无问题。",
    B="无需新增定理；若要保留「复用确认」这一意图，正确形状是 `alias` 或 `@[simp]` 转发并注明 derived-from，而不是并列一条定理。",
    C="无前件可删：hne 承重（全 false 时和=0）。",
    Dd="不涉及精确/误差界问题。",
    E="覆盖任意 n/allowed/s，未退化。",
    F="证明体是「改成二维、用 maskedSoftmax_sum_one」的另一条证明路径，数学内容与已有定理三重复，无新事实。",
    note="本文件已有 constrainedSoftmax_sum_one；本条是同一命题的第二次证明，以并列定理身份进入 API 会让「本文件定理数」虚高，且两条日后可能漂移。保留「复用确认」的意图可以理解，但应按 alias 登记而非计入定理数。verdict=register。")

add("empty_allowed_row_sum_ne_one", "keep",
    note="负对照：allowed 恒 false、s 恒 0 使分母 0、每分量 0，故 Σp=0≠1；证明用 hzero/sum_const 两步而 not decide，逻辑清楚。这是「非空前件不可去」的机器见证，对下游义务有意义，非重言。")

add("posMask_row_is_dummy", "keep",
    note="把两行都改写到 constrainedSoftmax（经 19）即得同一值；证明虽短，但结论是「行指标不携带信息」的机器事实，用于否决「直接复用二维 mask」的方案，doc 与用途一致。")

add("mask_actually_changes_distribution", "keep",
    note="显式数值见证：掩码后 p₀=1，未掩码为 1/2，不等；这是「反空洞性」的关键负对照（否则全部掩码定理可能恒真），非占位。")

add("nonempty_allowed_row_sum_eq_one_witness", "keep",
    note="allowed=(true,false)、s=0 时非空且 Σp=1，存在性见证直接实例化定理三；作用是证明定理三不空泛。虽为特例，非重言（确实调用了 sum_one）。")

add("not_allowed_contribution_zero", "keep",
    note="由 eq_zero_of_not_allowed 得 p=0 再 zero_mul；一行推论，但把「不可行 token 在加权和中项消失」固化成可复用形状，doc 对「非重述」的定位准确。")

add("mass_concentrated_on_allowed", "keep",
    note="把全和拆成 filter / filter-not（sum_filter_add_sum_filter_not），非允许部分逐项为 0（sum_eq_zero），余下 filter 部分=1；这是实质的支撑质量定理而非 sum_one 的重述。")

add("allowed_is_convex_weights", "register",
    A="结论只是两条已有定理的合取，强度够用（但它不是新事实）。",
    B="真正缺的是「凸组合」的实质内容：需要 Σ_t p_t ·(exp(s_t)/Z) 型的加权平均恒等式（p 是 exp 在单纯形上的归一），而不是两条已知事实的 ∧。若要这个假设包，叫 `ConstrainedSoftmaxIsProb` 更诚实。",
    C="hne 承重（非空才可能和为 1）；无冗余前件。",
    Dd="不涉及精确/误差界问题。",
    E="覆盖任意 n/allowed/s，前提可满足（见 24）。",
    F="证明体就是 ⟨constrainedSoftmax_nonneg, constrainedSoftmax_sum_one⟩：纯打包，无新数学内容。",
    note="合取包不是数学内容，调用点写 `⟨nonneg, sum_one⟩` 等价。doc 自称「可复用的假设包」，但以定理身份计数会虚高。verdict=register：删除或标为 convenience alias。")

add("support_from_decoded_constraints", "register",
    A="结论与 constrained_agrees_with_constraint_set 同型同义（同参数同结论），强度上无问题。",
    B="真正缺的是消费者侧的实质推论：例如「DecodesTo 成功 ⇒ 存在非空 allowed 见证」或「观测相等 ⇒ 干预相等」这类把 hts 变成可用信息的定理；本条并未多做。",
    C="hne/hts 全部原样转手给被调定理，无自己的前件可删。",
    Dd="不涉及精确/误差界问题。",
    E="覆盖任意 n/cs/tok/ts，未退化。",
    F="证明体是单个既有定理的完整应用（参数逐个传入），陈述与其结论同型：verbatim alias，零新内容。",
    note="与 constrained_agrees_with_constraint_set 同义同型，属别名转发。若下游只要短名字，建议 `alias` 或 @[simp] 转发并注明来源，不应作为并列定理计数。verdict=register。")

add("feasibility_is_caller_obligation", "keep",
    note="¬(允许集空 ∧ Σp=1) 的全称否定：空 ⇒ 每项 0 ⇒ 和 0 ≠ 1。与 21 不同（21 是具体反例，本条是全称义务），doc 对该区别的说明准确；结论可直接成为下游的接口义务。")

add("infonce_le_log_card_of_max", "keep",
    note="hmax ⇒ 分母 ≤ n·exp(s_i/τ) ⇒ softmax_i ≥ 1/n ⇒ infoNCE ≤ log n；hτ 承重，n>0 的 cast 也补了。这类界是 RealInfoNCELowerBound 需要的真实前置。")

add("infonce_le_log_one_add_of_gap", "keep",
    note="在 erase i 后逐项用 hgap 放大到 exp(s_i/τ)·exp(−Δ/τ)，再取对数，得到 log(1+(n−1)e^{−Δ/τ})；hτ、hgap 承重。瑕疵：`_hΔ : 0<Δ` 未使用（Δ≤0 时是否仍真未验证，故不轻言可删），不影响本条可用性。")

add("admissible_iff_not_dominated", "register",
    A="结论就是 Admissible 定义的改写，无需更强。",
    B="下游真缺的是可用形式：「非可容许 ⇒ ∃δ' 逐点不差且某点严格更好」（∃ 而非 ¬∀），本条给不出。",
    C="无前件可删（L、δ 任意）。",
    Dd="不涉及精确/误差界问题。",
    E="覆盖任意 L/δ，未退化。",
    F="证明体为 `Iff.rfl`：Admissible 定义即 ¬Dominated，故本条是 a=a 级的定义重述，信息量为零。",
    note="doc 自陈是定义改写、为下游保留两种语言。作为命名桥可以存在，但它是 0 信息量条目，若计入定理数就是虚高。verdict=register：改为 `abbrev`/@[simp] 转发，或在 doc 标注 alias。")

add("chain_distill_bound_lipschitz", "register",
    A="结论与 RealQuantizedError.quantized_chain_error_lipschitz 相同（仅 Ft/Fs 角色互换），强度无问题。",
    B="真正缺的是把逐层常数 Ls 从网络结构（权重范数）**导出**的桥：当前 Ls 是自由参数，doc 也用「取 max」人工补上；这条桥才是 RealDistillGeneralization 端到端界的承重环节。",
    C="hL0 承重（∏ 非负）；hLt/hLs 按角色原样传给被调定理，无冗余（但也没有自己的前件）。",
    Dd="不涉及精确/误差界问题（本身是界）。",
    E="覆盖任意 n/E，n=0 时为空和=0，未退化。",
    F="证明体 `exact quantized_chain_error_lipschitz Fs Ft Ls ε n hLs hLt hL0 hε x`：纯实例化＋改名，无新数学内容。",
    note="名为「块级蒸馏入口」，实为既有 Lipschitz 复合误差定理的角色互换实例。保留一个蒸馏词汇的名字可以接受，但应显式标注 derived-from，并补 B 中那条「由结构导出 Ls」的桥；否则下游会把自由参数 Ls 当成已验证的层常数。verdict=register。")

add("distill_excess_from_layer", "strengthen",
    A="Lean 实测报 179:5 `unused variable hc`、181:5 `unused variable hB0`，证明体只用 h2 : R gs − R gt ≤ c·B（来自 hR 与 hlayer），hc、hB0 不参与任何推导。二者既不可由其余前件推出，又被写进签名，删掉后定理严格更一般且证明不变。doc 的保留理由①「linarith 会隐式消费、删了会假失败」不成立：linarith 只在线性组合里搜索，删去未使用的假设不会使原本可证的线性目标不可证；②「改签名破坏调用点」是同文件/下游可同步的工程成本；③自己也承认是「假设多余」。",
    B="需要的是删前件后的新签名 `distill_excess_from_layer (R gs gt c B) (hlayer) (hR) : R gs ≤ R gt + c*B`；若为兼容保留旧名，让旧名做 alias 转发。",
    C="hc、hB0 可删（不是「可证」而是压根不用；删除使结论更强）。hlayer、hR 承重，不可动。",
    Dd="不涉及精确→误差界的降级（这条本身是界）。",
    E="覆盖任意 E/F/R，未退化（n 无关）。",
    F="非重言：真正用了 hR 的 Lipschitz 性与 hlayer 的逐点界。",
    note="本条不是「漏用关键假设」而是「接口带死前件 + doc 用一大段理由为死前件辩护」。按 PROCESS.md §4.6 第一类病因（假设写多/写松）应删前件：删 hc、hB0，同步 distill_excess_from_chain_lipschitz 的调用，并删掉 doc 里那段「linarith 隐式消费」的辩护。verdict=strengthen（删前件后严格更强）。")

add("pacBayes_risk_bound_of_exponent", "keep",
    note="纯线性重排：rw [le_div_iff₀ hlam] 后用 h 闭合，hlam>0 承重（lam=0 时结论无意义）。结论与指数形式等价，doc 表述准确；不对 δ/n 作无谓假设也不影响正确性。")

add("extractVec_injective_recover", "keep",
    note="LinearLayer 恰有 w/b 两字段，extractVec 是字段重命名；用 congrArg 抽出两个分量后 cases 闭合，单射性真实（不是 rfl 也不是空洞）。")

add("zeroLayer_out", "keep",
    note="空权重层 LayerOut = b = 0，unfold LayerOut/dot 后 simp；是下一条「Layer→行为非单射」的见证基础，真实计算。")

add("no_function_recovers_do", "keep",
    note="最强的不可识别性：对**任意** F（含不可计算）都失败。证明只用 obs_C_eq_obs_D 与 do_C_ne_do_D，逻辑闭合；coverage「任意 F」名副其实，doc 与陈述一致。")

add("top1_output_is_hard", "strengthen",
    A="陈述把求和限制在单元素集 {i} 上，`_hrest`（其余权重为 0）完全未使用，于是结论退化为 w i • v i = v i，与「top-1 硬路由」无关：真正该证的是全和 Σ_{j} w j • v j = v i（用 hw 与 hrest），这才是下游 RealDynamicRoute 需要的事实。当前形状即使其余权重任意也成立，名字 overclaim。",
    B="缺：全求和版 `top1_output_is_hard : (∑ j, w j • v j) = v i`（hw + hrest 承重）；以及「选择集 {i} 由 argmax/阈值产生」的配套（现在 {i} 是外部给定，硬路由的「硬」没有被证明来自选择机制）。",
    C="hw 承重；hrest 目前是死前件，改成全和后成为承重前件（这正是它存在的理由）。",
    Dd="不涉及精确/误差界问题。",
    E="单点集上的覆盖是空洞的：∀ j ∈ {i} 只有 j=i，故「单元素选择」这一前提未被真正检验。",
    F="非重言，但实质只是「单点和 + one_smul」的恒等式，信息量低于名字承诺。",
    note="把 `∑ j in ({i} : Finset ι)` 改成 `∑ j, w j • v j` 并让 _hrest 承重；否则这条定理对「硬路由」什么都没说，却以 top1_output_is_hard 之名被下游引用。verdict=strengthen。")

add("zeroFixingZ_of_strictMono", "keep",
    note="整数版判据 1：直接回收 zeroFixing_of_strictMono（h0 + StrictMono ⇒ ZeroFixing），doc 标明只读引用。结论真实，前件都承重（反例：平移的 strictMono 但不 zero-fixing）。")

add("zeroFixing_false_of_witness", "keep",
    note="有非零零点 ⇒ ¬ZeroFixing，证明是 (h y).mp 的一步，doc 明确它只覆盖「有非零零点」而不覆盖「零集为空」，边界诚实；对 B/C 文件是统一否定入口。")

add("zeroFixing_of_bounded_no_witness", "keep",
    note="把 ZeroFixing 拆成盒内（decide 穷举，经 zeroFixing_box_only）+ 盒外覆盖论证 hout；h0 供逆方向 y=0 → act y=0。这不是决策过程而是归约，doc 也如实这么写——作为可执行内核的接口是真实的，未冒充「对任意 act 可判定」。")

add("decidable_zeroFixing_siluZ", "delete",
    A="无强度问题可言：结论对任何恒等映射都成立，与 silu 的性质无关，无法支撑「silu 零集 = {0}」这一意图。",
    B="真正该存在的是对真实激活的陈述：`∀ y, y * sigmoid y = 0 ↔ y = 0`（ℝ 版），doc 应指向它而不是恒等代用。",
    C="无前件（也无任何假设）。",
    Dd="不涉及精确→误差界：这条不是「弱化」，是「换了对象」。",
    E="doc 声称「判定 0（零集 = {0}）」计入激活覆盖表，但载体 act_siluZ 在 B.lean:158 定义为恒等（`def act_siluZ (n : ℤ) : ℤ := n`），不是 SiLU 的整数版——覆盖名不副实。",
    F="ZeroFixing act_siluZ 展开为 ∀ y, (y = 0 ↔ y = 0)；证明体两方向分别就是 `hy` 与 `hy ▸ rfl`，是重言。",
    note="act_siluZ := fun n => n（B.lean:158），故本条是 y=0↔y=0 的重言。它被 C.lean 当「判定 0（零集={0}）」计入覆盖表，会让「12/12 激活全部已判定」的计数虚高——这正是「有名字、0 sorry 就当完成」的典型。建议删除或改成真实激活 x·σ(x) 的整数/实数版；C.lean 的引用改指向真实激活的证据（新证 x·σ(x)=0 ↔ x=0，或同类的 ℝ 版 zeroFixingR_* 条目）。verdict=delete。")

add("decidable_zeroFixing_geluZ", "delete",
    A="同样无法支撑「GELU 零集 = {0}」：结论对任何恒等映射成立，强度不足以对上 GELU 的语义。",
    B="真正该存在的是 `∀ y, y * geluGateFid y = 0 ↔ y = 0`（ℝ 版已在同文件 :467 的 zeroFixingR_geluTanhR 由 gate 恒正证出），本条应指向它。",
    C="无前件。",
    Dd="不涉及精确→误差界：这是替换对象而非弱化。",
    E="doc 称「判定 1（零集 = {0}）」，但载体 act_geluZ 在 B.lean:162 也是恒等（`:= n`），因此该行在激活覆盖表中的位置是虚的。",
    F="ZeroFixing act_geluZ 展开为 ∀ y, (y = 0 ↔ y = 0)，证明体两方向都是 hy / hy ▸ rfl：重言。",
    note="act_geluZ := fun n => n（B.lean:162），与上一条同为恒等占位上的重言。紧随其后的盒式内核实例（把 zeroFixing_of_bounded_no_witness 用在盒 n=3 上）才是有内容的演示，应保留那一支；本条建议删除或改陈述为真实 GELU。verdict=delete。")

add("decidable_zeroFixing_leakyReluZ", "keep",
    note="act_leakyReluZ（负斜率 1、正斜率 2）分四象限用 omega 证 StrictMono，再走判据 1（h0 : act 0 = 0）。doc 记录的两个 STYLE 陷阱与证明形状一致（先取条件再 unfold、对 x/y 符号分四种情形），说明证明是真承重的。")

add("neg_zeroFixing_softplusZ", "keep",
    note="act_softplusZ = n+1，见证 −1：act(−1)=0 且 −1≠0，经 zeroFixing_false_of_witness 闭合；doc 说明与实数 softplus（处处正、零集空）的差异，边界诚实。真实否定。")

add("neg_zeroFixing_hswishZ", "keep",
    note="act_hswishZ = n+1，见证 −1 同上；doc 交代了与真实 hardSigmoid 零点（−3）的平移关系。真实否定。")

add("neg_zeroFixing_mreluZ", "keep",
    note="act_mreluZ = n+1，见证 −1；doc 关于 ℂ 上 modReLU 零集的背景说明不影响本条（结论只需一个见证）。真实否定。")

add("neg_zeroFixing_reluZ", "register",
    A="结论与 B11 的 reluZ_not_zeroFixing 相同（¬ZeroFixing reluZ），强度无问题。",
    B="缺的是本条 doc 提到的「否定 2」：reluZ 在负半轴把 y 与 y+1 都送到 0 因而非单射——那才是它声称的「几何根源」，本条自己没有给出。",
    C="无前件。",
    Dd="不涉及精确/误差界问题。",
    E="只覆盖 reluZ 一个激活，未越权。",
    F="证明体只有 `reluZ_not_zeroFixing` 一个名字：纯别名，零新内容。",
    note="为了 neg_zeroFixing_* 统一命名而转发可以理解，但作为独立定理它只是 B11 已有结论的改名。verdict=register：改为 alias/@[simp] 转发并在 doc 标 derived-from，不计入定理数。")

add("zeroFixingR_geluTanhR", "keep",
    note="act_geluTanhR = y·gate y，用 gate 恒正（geluGateFid_pos）与 mul_eq_zero 得双向 y·gate y=0 ↔ y=0；证明不依赖单调性，是零集判据的独立证据。真实。")

add("abs_tanh_lt_one", "keep",
    note="严格版 |tanh x|<1：cosh²−sinh²=1 与 cosh>0 得 |sinh|<cosh，再经 tanh=sinh/cosh 与 div_lt_one。比项目内已有的 ≤1 / −1<tanh 两条强（严格、双向），证明用 sqrt 桥绕开 abs 模式匹配；mathlib 本版本无同名引理。真实内容。")

add("even_loop_converges", "keep",
    note="按 x%2 分两支：偶则 n=0，奇则 n=1 用 repairEven_odd_to_even；结论 ∃n EvenSat，实际给出 ≤1 步收敛，强于仅「收敛」。真实。")

add("iterateRepairEven_add", "keep",
    note="对 m 归纳的迭代合成律，succ 支用 iterateRepairEven 的递归展开与 ih；这是循环加速/终止论证的标准配套，非重言。")

add("zero_slope_not_exact", "keep",
    note="a=0,b≠0 时所有点都是局部极小但无可行点，故「局部极小 ⇒ 可行」为假；用 zero_slope_all_localMin 在 x=0 取反例精确否定了「坡度假设可去」，与 sq_penalty_exact 的 ha≠0 一一对应。真实的不可去性证明。")

add("exists_decrease", "keep",
    note="hA 满射给出 d 使 A d = r，取 x − 1•d，用 lossM_step 把损失写成 (1−s)²‖r‖² 的 s=1 处（=0），严格下降；hsq/hsq2 用 hd 改写，hpos 由 hr 的某分量非零得。前件都承重，真实。")

add("sq_penalty_exact_matrix", "keep",
    note="由 localMin_iff_feasible 与满射性直接得到，证明只有一行但引用的是实质引理；doc 明确只对满射 A 成立、并指出 m>n 时约束可能不可行——子类边界诚实标注，不是把子类当一般情形。")

add("exists_decrease", "keep",
    note="2 维逐坐标：把 resid2 的第 j 个分量归零、另一分量不变，再用 sq_pos_of_ne_zero + nlinarith 得严格下降；fin_cases 两支都处理，ha、hr 承重。真实。")

add("sqNorm_nonneg", "keep",
    note="平方和逐项非负（sum_nonneg + sq_nonneg）；一行但为标准前置（下游需要 0 ≤ sqNorm），真实，非占位。")

add("linearFix_residual", "keep",
    note="linearFix 用 if 分支；h 支直接得 residual=0，¬h 支 field_simp+ring 闭合，ha≠0 使除法合法。真实（修复步残余归零）。")

add("bellman_contracting", "keep",
    note="用 bellman_contraction_norm 得 LipschitzWith γ，再转 ContractingWith ⟨γ,hγ0⟩；hγ1 进结构、hPnonneg/hPsum 用于收缩估计（随机矩阵的行和为 1），前件都承重。真实。")

add("gelfand_opNorm_one_le", "keep",
    note="matCLME 1 = id（ext + simp/one_apply），再 norm_id_le；n=0 时也成立，故只给 ≤1，doc 明确把它与 0<n 的 =1 版分开。真实（doc 里的 R3 更正是文档卫生问题，不影响数学）。")

add("gelfand_opNorm_one_of_pos", "keep",
    note="hn>0 时用 ⟨0,hn⟩ 造 Nontrivial 实例（取单位向量与 0 相异），再套 norm_id；hn 承重（n=0 时 Nontrivial 不成立），doc 诚实。真实。")

add("gelfand_radius_le_opNorm", "keep",
    note="由 gelfand_radius_le_pow_root 取 k=1（rpow 1/1 化简）得 ρ(T) ≤ ‖T‖。这是 Gelfand 的平凡半边，doc 也这么说；结论对任意实方阵成立，真实。")

add("gelfand_radius_lt_one_of_opNorm_lt_one", "keep",
    note="‖T‖<1 ⇒ ρ(T)<1，lt_of_le_of_lt 复合上一条；是 Neumann 级数收敛的直接前置，真实。")

add("gelfand_radius_le_opNorm_general", "register",
    A="结论与 :224 的 gelfand_radius_le_opNorm 逐字相同（同陈述同类型），强度无问题。",
    B="无新数学内容可补：非对角情形已由 :224 覆盖；若要按「非对角谱半径」检索，用命名约定/标签即可，不需要并列定理。",
    C="无前件。",
    Dd="不涉及精确/误差界问题。",
    E="覆盖任意 n/T，未退化。",
    F="证明体就是 `gelfand_radius_le_opNorm T`：同陈述、同证明的具名重复，零新信息。",
    note="doc 自陈「具名重申」。它与 :224 是同一命题的两条记录，#print axioms / 定理计数都会重复，且未来改一条会忘另一条。verdict=register：合并（删本条，在 :224 的 doc 里加检索关键词）。")

add("normSq_nonneg", "keep",
    note="normSq 是平方和，sum_nonneg+sq_nonneg；一行标准前置，被 RealSDE 需要，真实非占位。")

add("two_dim_posdef_iff", "keep",
    note="正向取 v=(1,0) 与 v=(−b,a)（a>0 保证非零）得 a>0 与 a(ad−b²)>0；反向用配方恒等式 q = a(v₀+(b/a)v₁)² + ((ad−b²)/a)v₁² 与 nlinarith 排除两项同时为 0。真正的充要条件，两个方向都完整。")

add("second_order_necessary_multidim", "keep",
    note="路径 t↦x+t·v 把 IsLocalMin 经 Tendsto.eventually 传成 0 处的一维局部极小，再逐方向套一维 second_order_necessary 得 quadForm H v ≥ 0。前件是 C² 型正则性假设（其中 hcont 可由 hdiff 导出，属无害冗余、不缩小适用面），H/x/v 均任意。真实必要条件。")

add("second_order_sufficient_multidim", "keep",
    note="由 hH（H 有一致正模数 μ>0）与 hTaylor（全局二次下界）经 quadratic_lower_bound_of_posdef 得 ∀y≠x, F x<F y。doc 把「Taylor 型下界」明写为假设——本条定位是「二次下界 ⇒ 严格极小」，不是经典 C² 充分条件的全景证明，doc 也没有把它说成后者，故不算过度声称。")

add("infinite_sum_bound", "keep",
    note="summable_of_sum_range_le + Real.tsum_le_of_sum_range_le 两条 mathlib 事实组合，同时给出可和性与极限界；ha（非负）与 hC（一致截断界）都承重。真实。")

add("inner_self_norm_sq_scalar", "keep",
    note="inner_self_eq_norm_sq 的对称形式（‖x‖² = re⟪x,x⟫），一行转发；mathlib 已有反向，本条是该文件给 RealComplex 的 API 方向。真实但零推导（doc 为空，可补一句以免被当成新结果）。")

add("isometry_scalar_compose", "keep",
    note="两次用内积保持性，calc 两步；结论「等距复合仍保内积」真实（非 rfl，需两次改写）。")

add("op_apply_le", "keep",
    note="T.le_opNorm 的直接转发，doc 自陈是「算子范数的定义性不等式」；作为该文件算子范数 API 的基元被 op_norm_pow_apply_le 等使用，真实但零推导（如要更严格可标为 re-export）。")

add("op_norm_pow_apply_le", "keep",
    note="‖T^n x‖ ≤ ‖T^n‖‖x‖（le_opNorm）≤ ‖T‖^n‖x‖（op_norm_pow_le 与 mul_le_mul_of_nonneg_right）；深度放大上界，真实组合。")

add("op_norm_pow_apply_le_of_le", "keep",
    note="由 h 与幂单调（pow_le_pow_left₀）给出 c^n 界；`_hc : 0≤c` 虽未使用且可由 0≤‖T‖≤c 导出（冗余但自动满足，不缩小适用面）。真实。")

add("frob_add_le", "keep",
    note="用 |⟨A,B⟩| ≤ ‖A‖‖B‖（frobSq_inner_sq_le）与 (‖A‖+‖B‖)² 的展开比较，经 sq_le_sq 去根；hexp 的逐行展开与 nlinarith 都承重。真实三角不等式。")

add("iterateStep_succ", "keep",
    note="迭代式的定义展开（rfl）并标 @[simp]；是 iterateStep_norm_le 归纳的直接入口，虽为 rfl 但属必要的 API（不是对已有定理的重复）。")

add("iterateStep_norm_le", "keep",
    note="对 n 归纳：norm_add_le + op_apply_le，把 Σ_{k<n}‖T‖^k‖b‖ 推到 n+1（sum_range_succ' + ring）；真实扰动累积界。")

add("prod_one_add_le_exp", "keep",
    note="逐项 1+ε ≤ exp ε（add_one_le_exp）再 prod_le_prod 与 exp_sum；heps 承重（否则 1+ε 可能为负，乘积比较失效）。真实。")

add("one_add_lower_bound", "keep",
    note="由 abs_norm_sub_norm_le 取一侧得 ‖h‖−‖Wh‖ ≤ ‖h+Wh‖，配合 ‖Wh‖ ≤ Lw‖h‖ 得 (1−Lw)‖h‖ ≤ ‖h+Wh‖；doc 明确此条不需要 Lw<1（Lw<1 只在单射定理承重），对 hW 的用法诚实。真实。")

assert len(V) == len(rows), (len(V), len(rows))
out = []
for r, v in zip(rows, V):
    assert r["name"] == v["name"], (r["name"], v["name"])
    out.append({
        "file": r["file"], "line": r["line"], "name": r["name"],
        "verdict": v["verdict"],
        "A_strength": v["A"], "B_missing": v["B"], "C_hypotheses": v["C"],
        "D_downgrade": v["D"], "E_coverage": v["E"], "F_content": v["F"],
        "note": v["note"],
    })

with open(os.path.join(D, "verdicts_013.jsonl"), "w", encoding="utf-8", newline="\n") as f:
    for o in out:
        f.write(json.dumps(o, ensure_ascii=False) + "\n")

print("wrote", len(out))
from collections import Counter
print(Counter(o["verdict"] for o in out))
print("non-keep:", [ (o["name"], o["verdict"]) for o in out if o["verdict"] != "keep" ])
