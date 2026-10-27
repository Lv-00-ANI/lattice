# -*- coding: utf-8 -*-
"""Generate verdicts_014.jsonl from reviewed batch_014.jsonl (keyed by line)."""
import json, io, sys

BASE = r"C:\Users\xingg\Desktop\agent\lattice-new\agent-tmp\review"
SRC = BASE + r"\batch_014.jsonl"
OUT = BASE + r"\verdicts_014.jsonl"

K = dict(A="强度够（对唯一用户足够）", B="无需补", C="无可删", D="不适用（结论即精确等式/不等式）",
         E="doc 与陈述一致", F="非重言，有实质内容")

# line -> list of verdict records, consumed in authoring order
# (some line numbers occur in two different files, e.g. 28, 53, 71, 79, 86, 96, 196)
V = {}

def add(line, verdict, note, A=None, B=None, C=None, D=None, E=None, F=None):
    V.setdefault(line, []).append(dict(verdict=verdict, note=note,
        A_strength=A or K["A"], B_missing=B or K["B"], C_hypotheses=C or K["C"],
        D_downgrade=D or K["D"], E_coverage=E or K["E"], F_content=F or K["F"]))

# ---- RealOperatorInvertibility / RKHS / SVD -----------------------------------
add(141, "keep",
    "反例见证：结论 `¬Injective (h ↦ h + (-1)*h)` 由 0、1 同像即得，证明最小但命题是真否定式——正是 `Lw < 1` 不可删的机器证据；无冗余前件，用途（RealHreachClosed）只要这条否定式。")

add(177, "keep",
    "逐元素展开 + 核对称即得 `(Gᵀ)ᵢⱼ = Gⱼᵢ = Gᵢⱼ`；`hK` 是唯一前件且必需（去掉后转置对称不成立），形态正是 RealGaussianProcess 喂谱定理所需。")

add(203, "keep",
    "`0 ≤ K a a` 由 `hpsd` 在 `Fin 1`、`v = 1` 处取值即得，是真命题；`hpsd` 不可删（无它则无任何约束）。附带说明：本条 doc 字段把 :208 起的 v15 登记串了进来，源文件 :201-202 的 docstring 是正确的，属提取串行、非库缺陷。")

add(226, "keep",
    "`hsymm` 必需：doc 与 :242-266 的反例（K a b = 2、K b a = 0、对角 1）证明半正定推不出 `2K a b ≤ K a a + K b b`；不需要对称性的对照版 `kernel_sym_part_abs_le` 已在 :275，doc 承诺兑现，配套无缺口。")

add(564, "keep",
    "核展开的直接代数后果（`hK` 是唯一前件且必需）；把 `‖Φx−Φy‖²` 与核表达式逐项对齐，强度恰好够 RealReproducingKernelTheory 使用。")

add(574, "keep",
    "由 5（`metric_eq_kernel_expansion`）与平方和 ≥ 0 立得，是真非负性（负型）定理；注意它不依赖对称性，故不落入 `kernel_symm_of_psd` 同族假命题。")

add(582, "keep",
    "`= 0 ↔ Φ a = Φ b` 的 iff 两侧都证到（平方和为零 ⟺ 每项为零），`hK` 必需；`Finset.sum_eq_zero_iff_of_nonneg` 的正确用法，未偷减方向。")

add(53, "keep",
    "ℝ 上 `star` 恒等，故 `Aᴴ = Aᵀ` 是对任意 m,n 成立的实质等式；Concentration/RealEYM 靠它把 Hermitian 语言换到对称语言，桥不可省。")

add(114, "keep",
    "存在形式实谱定理：`U` 取 `hA.eigenvectorUnitary`，`UᵀU = 1` 来自 :104 附近的转置引理；对方法矩阵 `UᵀU=1` 已足以称正交，doc 未过度声称。`hA` 必需。")

add(128, "keep",
    "迹的循环性 + 谱分解，等式精确（`trace (diag λ) = Σλ` 逐项）；`hA` 必需，EckartYoung 只用这一条。")

add(212, "keep",
    "Frobenius 平方 = 特征值平方和，等式精确；证明显式用 `Aᵀ = A`（实对称）与 `trace_mul_self_conj_of_decomp`，前件无冗余。")

# ---- SparseCoding --------------------------------------------------------------
add(439, "delete",
    "本条目不是声明：:439 位于 `softThresh_le_of_is_min` 的 docstring 代码块内（:432 是 `/-!` 起、:471 是 `-/` 收），grep 全库只在注释里命中 `theorem eq_softThresh_of_is_min`；真声明在 :472（改名后的 `softThresh_le_of_is_min`）。即提取器把注释里的旧代码块当成了定理，是幻影条目（下游 RealSparseCodingCoherence:267 也只是在注释里提到该名）。应从批次中剔除，并对提取器加「跳过 /- -/ 区」的过滤。",
    A="条目无真实陈述（幻影），无可判强度", B="—", C="—", D="—", E="—",
    F="零信息量：载体是注释文本而非声明")

add(472, "delete",
    "与同文件 :428 的 `softThresh_is_min` **陈述逐字相同**、证明体就是调用它（`softThresh_is_min lam y hlam x`），是本轮改名留下的**别名**；且名字仍带 `of_is_min` 而陈述已无 `is_min` 前件，仍会误导读者。其 `users` 指向 RealSparseCodingCoherence.lean:267，那只是注释里提到旧名的一句话——全库没有任何证明真正引用 `softThresh_le_of_is_min`。应删别名（下游改引 `softThresh_is_min`），或做真正的改名而不是新增名字。",
    A="强度无问题（= 全局最优性）", B="无需补",
    C="已无前件可删（hlam 必需）", D="不适用",
    E="doc 自己承认「结论与 x 是否最小点无关」，与名字不符", F="零边际信息：同一陈述的第二个名字")

add(64, "keep",
    "分段等式在 `0 ≤ lam` 下为真，而该前件**不可删**：doc 与 :64 起的说明给出 lam=-5、y=-1 的反例（231 组穷举：λ<0 时 15 组违例）。这是本批对 C 维度最诚实的一条，`if` 链的 `<` 分支也已覆盖边界。")

add(136, "keep",
    "死区引理为真：`|y| ≤ lam` 迫使 `|y| − lam ≤ 0`，`max` 取右端得 0；`h` 是结论的实质条件（无它不成立），既不可删也不可弱化。")

add(189, "keep",
    "`0 < lam` + `lam ≤ y` 才能走 `sign y = 1` 分支并让 `max` 取左端；doc 明示省略 `0 < lam` 即假（同文件的反例定理），前件必需、未被夸大。")

# ---- Sparsity / quantization chains --------------------------------------------
add(61, "keep",
    "`A − A' = B` 逐点成立（`by_cases` 覆盖 S 内外两类点），是剪枝/误差解耦的定义级事实；下游 RealStructuredPruning 的线性性引用依赖它。")

add(67, "keep",
    "只是 17 的相反数形式（承接 `matCLME` 的线性性），等式精确、无前件；有独立用途（下游按 `A' − A` 书写）。")

add(227, "keep",
    "`matCLME (−A) = −matCLME A`（逐点 `matvecE_neg` + 连续线性映射外延），是真线性性引理，无前件。")

add(254, "keep",
    "把 `quantized_chain_error_closed` 实例化到剪枝算子；δᵢ 的乘积型误差界与下游逐层界同形，确为误差界（doc 未声称精确），用途匹配。")

# ---- Spectral ----------------------------------------------------------------
add(76, "keep",
    "Gershgorin：取模最大的坐标（先证该坐标非零），把 `Σ Aᵢⱼxⱼ = μxᵢ` 拆出对角项后取绝对值；`∃ i` 的覆盖与 doc 一致，是完整证明而非占位。")

add(73, "keep",
    "`ρ̂ ≥ 0` 由 `abs_le_diagRadius` 取任一分量即得；`[Nonempty (Fin n)]` 是文件级变量的诚实限制（doc :41-42 已登记「降级为非空对角阵」），不属偷减范围。")

add(207, "keep",
    "`‖matCLME (diag d)‖ = ρ̂(d)` 是双侧不等式夹出的等式（`opNorm_diagonal_le` + `le_opNorm_diagonal`），精确，`Nonempty` 限制同上。")

add(214, "keep",
    "由 23 + `Matrix.diagonal_pow` + `diagRadius_pow` 得；doc 声称「对一切 k 含 0」与 `∀ k : ℕ` 一致，k=0 时两侧均为 1 已被覆盖。")

# ---- Chains / meta -----------------------------------------------------------
add(29, "keep",
    "`deriv ((a y − b)²) x = 2a(a x − b)`：`HasDerivAt.pow` 组合后整理系数，等式精确；用于 RealPMixN 的平方损失驻点计算，无前件。")

add(86, "keep",
    "L-Lipschitz 复合 n 次的乘积界 `Lⁿ‖x−y‖`；`hL` 不可删（负 L 下幂不单调），形状正是 RealOrphanWiring 需要的。")

add(96, "keep",
    "编辑局部性：只把尾段放大 `L^(n−k)`，`hk : k < n` 用于避免空段；`Finset.prod_const` 化幂正确，界未被夸大。")

add(159, "keep",
    "三份 dot 同值的三元合取，三条分量各由独立引理给出（`:…` 分别是 `dot_eq_dotL`、`dotQ_eq_dot_cast`、`dot_eq_dotProduct`）——任一份被单方面改动即编译失败，是真实回归护栏而非重言。")

add(28, "keep",
    "三角不等式 + `edit_output_bound_scalar`，界 `‖W'−W‖‖x‖ + ‖b'−b‖` 精确（系数 1 处最优级），前件无。")

add(41, "keep",
    "把 28 用在零集点上（`h : W x + b = 0`），得 ε₁X+ε₂ 的判定界；ε₁/ε₂/X 都是判定用途所需，未多余。")

# ---- Optim: early stopping / FedAvg -----------------------------------------
add(72, "keep",
    "两侧间隙 ≤ γ 且验证不降 ⟹ 训练步长 ≤ 2γ；`hk : 1 ≤ k` 由 `IsStopPoint` 定义（:49 `s < t + k`）在 `omega` 中实际用到，非冗余前件。")

add(208, "strengthen",
    "C 维度：`_hG0 : 0 ≤ G` 从未参与证明，且由 `hG`（取 t = 0 得 `|g (x 0)| ≤ G`）即可推出 —— 应删掉该前件，陈述变成 `hη hζ0 hG hd hstep` 五前件。其余前件都被用到，单步界形状与下游 FedAvg 一致，不需要再加强。",
    C="删 `_hG0`（可由 `hG` 推出且证明未用）")

# ---- GD ---------------------------------------------------------------------
add(86, "keep",
    "平方收缩：`GD_contraction_step` 后接 `sq_le_sq'`，常数 `c²` 保留；`hc0` 必需（决定开方方向），前件无冗余。")

add(133, "keep",
    "n 次迭代的 `c²` 连乘由 32 逐点归纳，`GDIterate_comm_update` 对齐 update 形式；`hc0`、`hspec` 必需。附带说明：`hspec` 里的 `∀ _x : E` 是空绑定（体不依赖 x），等价于不带绑定的形式，只影响可读性、不影响强度。")

# ---- List/Fin bridge --------------------------------------------------------
add(28, "keep",
    "`foldl` 对起始值可加（zip 上），归纳并用 `ring` 收尾；是无语义陷阱的组合恒等式，RealChainAxioms3 用它做载体迁移。")

add(59, "keep",
    "List dot 转 Fin 求和，归纳覆盖 nil（含 `length_cons`/`sum_univ_succ`）与 cons 两类；是 `toVec`/`dotProduct` 桥的前置件。")

add(113, "keep",
    "反例见证：`[1]` 与 `[1,0]` 在 `toVec 2` 下同像，两个 `by decide` 均可判；doc「无长度条件时不单射」与陈述一致，正是 `toVec_injective` 需要长度前提的证据。")

# ---- Nesterov / Newton -------------------------------------------------------
add(96, "keep",
    "光滑性给出的下降引理，右端系数 `−η(1−Lη/2)` 精确；`hSM` 必需，η 任意（未加不必要的步长前提）。")

add(107, "keep",
    "由 37 + `η ≤ 1/L` 得目标不增；`hL/hη/hηL` 都进入 `nlinarith`（`L·η ≤ 1`、`1−Lη/2 ≥ 0`），前件无冗余。")

add(56, "keep",
    "`deriv (a/2 y² − b y) = a y − b`，`HasDerivAt` 组合后取值；正确且是 Newton 步的前置件。")

add(71, "keep",
    "二阶导 = a，先用 39 把一阶导写成函数再求导（避免对 `deriv` 直接展开）；正确。")

add(84, "keep",
    "`NewtonStep (deriv q) (deriv deriv q) x = b/a`，`ha : a ≠ 0` 为 `field_simp` 所需、不可删；对二次型是最优点，结论精确。")

# ---- Policy gradient / projection -------------------------------------------
add(34, "keep",
    "对数导数恒等式（score function）：`hpos` 给 `Real.hasDerivAt_log`，`hd` 给复合可导，等式精确；FisherInfo 的桥就靠这一条。")

add(71, "keep",
    "`x ∈ K ⟹ P_K x = x` 由 `orthogonalProjection_eq_self_iff` 直接给出，是投影梯度所需的固定点视角；陈述与 doc 一致。")

# ---- Proximal ----------------------------------------------------------------
add(100, "keep",
    "从 `prox_exists_unique` 取 `.exists`：结论是存在性（无选择形式），对 RealProximal 的定义性用途足够；去掉唯一性后独立可引，不算重言。")

add(48, "keep",
    "`‖a‖² = a²`（ℝ）的 simp 规范化，是 `prox_linear`/Moreau 等重写的前提；作为 simp 规则有实际用途。")

add(108, "keep",
    "ε-δ 式论证把极小性转成变分不等式（`t → 0` 取极限的显式化）；`hconv`、`hη` 必需，是本批真正的实质工作之一。")

add(143, "keep",
    "两条 VI 相减 + 约去 `|p−q|`（分 `= 0` 分支），非扩张性证明完整；`hconv` 必需（无凸性时 VI 桥不成立），`hη > 0` 不可删。")

add(196, "keep",
    "全局最小点是自身 prox（不动点视角），`hmin` 必需；`η > 0` 用于 `1/(2η) > 0`，结论精确。")

add(213, "keep",
    "线性目标的显式 prox `x − ηc`，配平方恒等式到 `(y − x + ηc)²` 精确；`hη` 必需。")

# ---- Riemannian --------------------------------------------------------------
add(158, "keep",
    "`‖x‖ = 1 ∧ gradStep ≠ 0 ⟹ sphereGD x ∈ sphere 0 1`；`hne` 不可删（归一化在 0 处无定义），doc 与陈述一致。")

add(239, "keep",
    "retraction 误差 `‖x⁺ − x‖ ≤ η‖g‖`：`⟨x,g⟩ = 0` 与 `η ≥ 0` 都进入 `norm_sub_sq_real` 展开，s 的显式界支撑了该不等式；这是 B21 的正结果，不是降级声称。")

# ---- SGD / stochastic --------------------------------------------------------
add(403, "keep",
    "二阶递推 `|α+μ| + μ < 1` 下的收敛（∀ε>0 ∃n），用 `W n = |p₁| + γ|p₂|` 作 Lyapunov 得 `c < 1`；该条件正是此类递推的临界线，未过强。")

add(68, "keep",
    "期望的齐次性（`Finset.mul_sum` + 逐项 ring），是方差恒等式与收缩界的基础件；无前件。")

add(131, "keep",
    "单步期望收缩：无偏（`hsub` 经 `Expect`）+ 二阶矩界 `hG`，右端 `η²G²` 精确；`hpsum = 1` 用于拆 `E[‖·‖²]`，必需。")

add(152, "keep",
    "方差恒等式 `E[(g − Eg)²] = E[g²] − (Eg)²`，靠 `hpsum = 1` 消常数项，等式精确；是下游 VarianceReduction 的直接依赖。")

add(170, "keep",
    "把 `η²E[g²]` 换成 `η²((Eg)² + Var)`，噪声项分解正确；`hvar` 由 55 提供，形状与下游对得上。")

add(202, "strengthen",
    "C 维度：`_hη : 0 ≤ η` 未出现在任何证明步（望远镜求和与 `ExpDist` 非负都不需要 η ≥ 0）——应删。`hp0`（`ExpDist` 非负）、`hstep` 都用到；界本身正确、无需加强。",
    C="删 `_hη`（证明未用）")

add(255, "keep",
    "由 57 除以 `2η`，`hη : 0 < η` 必需（除法与 `le_div_iff₀`）；平均界精确，`nlinarith` 收尾无漏洞。")

# ---- Saddle point ------------------------------------------------------------
add(82, "keep",
    "严格局部极大 ⟹ 局部极大：`isStrictLocalMax_iff_neg` 转成 `-f` 的严格极小，再 `toIsLocalMin.neg`；标准蕴含，无前件。")

add(161, "keep",
    "正性盒子引理由负性版取 `−g` 得到，`hδ/hg/hpos` 都用到，`η ≤ δ` 参数保留（未偷丢），是 KKT 二阶条件的对偶件。")

# ---- Seam bridges ------------------------------------------------------------
add(75, "keep",
    "跨模块识别 `bmean = mean`：两处批均值定义体逐字相同故 `rfl`；作为耦合护栏有效（任一方的定义体被改动即断）。同名副本另見 RealSeamBridges2:365，见该条的登记。")

add(78, "keep",
    "同上：`bmean = batchMean` 的 `rfl` 识别，是 BN ↔ 一致性文件的唯一耦合断言；本文件版本为规范位置。")

add(354, "register",
    "与 RealSeamBridges.lean:78 **同名、同陈述、同为 `rfl`** 的第二份声明（本文件未 import 前者，故不能复用而只能复写）。但两者都被 Lib/Optim.lean:51-52 汇聚导入，`Lattice.bmean_eq_batchMean` 在同一环境里因此有两份声明——下游一旦按名引用即报歧义，是一枚潜在炸弹。另外本条 `users` 填的是 RealSeamBridges.lean，即被复写的那份文件的所在处：两份副本互为对方的「用户」，in_degree = 1 是重复自造的，不是独立使用。建议让 RealSeamBridges2 import RealSeamBridges（或把桥收进单一 SeamBridge 模块），而不是复写。登记 PROOF-DEBT。",
    A="强度无问题", B="无需新定理：应改为单一来源（import 前者）+ 删除本副本",
    C="无可删", D="不适用",
    E="doc 自称「the substantive content is the identification across modules」，但同一识别已存在",
    F="与 :78 逐字重复，零边际信息")

add(365, "register",
    "与 RealSeamBridges.lean:75 **同名、同陈述、同为 `rfl`** 的第二份 `bmean_eq_mean`；同样被 Lib/Optim.lean:51-52 汇聚导入，构成同名双声明，且 `users` 指向的正是被复写的 RealSeamBridges.lean（两份副本互为「用户」，in_degree 非独立使用）。建议删除本副本并 import RealSeamBridges（或改名）。登记 PROOF-DEBT。",
    A="强度无问题", B="无需新定理：单一来源即可",
    C="无可删", D="不适用",
    E="doc 与陈述一致，但重复",
    F="与 :75 逐字重复，零边际信息")

# ---- Strong convexity --------------------------------------------------------
add(90, "keep",
    "`(μ/2)(x−x*)² ≤ f x − f x*`，由 `StrongConvex` 在 (x*, x) 取值并用 `hg0` 消去梯度项；`hg0` 在此**确实在用**，前件不可删。")

add(98, "keep",
    "`f x − f x* ≤ (L/2)(x−x*)²`，同法由 `Smooth` 得到；与 66 构成差距的双侧夹，是 `RealRateLower` 所需。")

add(130, "strengthen",
    "C 维度：`_hg0 : g xstar = 0` 被前缀标成未用，且证明里确实没有出现 —— 配平方 `(μ/2)((x*−x) + g x/μ)² ≥ 0` 完全不需要 `g x* = 0`。应删该前件（`StrongConvex`+`hμ` 已足够）。这也解释了为何调用点传什么都能过。",
    C="删 `_hg0`（证明未用；配平方论证不依赖 g x* = 0）")

add(168, "strengthen",
    "C 维度：`_hμL : μ ≤ L` 未参与证明（只用 `hdesc`、`hgrad`、`hkey`），即使 μ > L、右端系数为负，不等式仍由同一代数步骤成立 —— 应删。对照：下游 `gd_linear_rate`（:196）自己需要的 `μ ≤ L` 是它另外传的，故删此处前件不影响调用点。",
    C="删 `_hμL`（证明未用；μ > L 时不等式仍真）")

add(196, "keep",
    "由 69 归纳得 `(1−μ/L)ⁿ`；`hμL` 在此**确实必需**（要 `1 − μ/L ≥ 0` 才能把归纳步乘过去，:203-207 显式用了），与 69 里未用形成对照。")

# ---- Value iteration / Banach -----------------------------------------------
add(53, "keep",
    "`LinfNorm (|V|) = LinfNorm V`（`abs_abs` 双向 + 集合外延），Bellman 收缩的前置重写件；`n` 任意（空维时两侧同为 0）。")

add(79, "keep",
    "Bellman 算子的 γ-压缩（L∞）：`hPnonneg` + `hPsum`（行和为 1）是标准前提且都进入 `abs_mul`/`le_csSup` 链；n = 0 用 `by_cases Nonempty (Fin n)` 显式处理空 sup，未留洞。")

# ---- Penalty re-export -------------------------------------------------------
add(79, "register",
    "`Lattice.hasFDerivAt_sq` 与 `Lattice.Lift.hasFDerivAt_sq`（Lift/PenaltyAnalysis.lean:45）**陈述逐字相同**，证明体只调用后者——本条不引入任何新数学，是缩短命名空间的再导出。另注意：本条 `users` 指向 Lift/PenaltyAnalysis.lean，而该文件正是被转发的**下层原件**，不可能反向依赖本文件，这条引用是命名比对产物而非真实使用。建议改为 `export`/别名，或直接引用原定理。登记 PROOF-DEBT（低优先）。",
    A="强度无问题（与原定理同一陈述）", B="无需新定理",
    C="无可删", D="不适用",
    E="doc 与陈述一致，但无独立覆盖",
    F="零新增信息：同一陈述的第二个名字（与 Lift:45 重复）")

# ---- Float format ------------------------------------------------------------
add(122, "keep",
    "`r.err_bound (a+b)` 的实例：内容由 `RoundOp` 的假设全权供给，作为下游逐元素误差链的具名入口有效（不需要它也能写 `r.err_bound (a+b)`，但不构成错误或过度声称）。")

add(127, "keep",
    "`r.err_bound (a*b)` 的实例，同 74；结论与 doc 一致，是 MixedPrecisionRounding 的具名入口。")

add(149, "keep",
    "舍入传递性：`round x − y` 拆成 `(round x − x) + (x − y)` 后三角不等式，界 `eps|x| + tiny + η` 正确；`h` 必需。")

add(163, "keep",
    "Lipschitz 放大误差 = 条件数 × 单位舍入，`hκ ≥ 0` 必需（否则乘不等号反向）；doc 的「误差放大 = 条件数 × eps」与陈述严格一致。")

add(173, "strengthen",
    "C 维度：`_hx : 0 < |x|` 未参与证明（证明只用 `R.err_bound` 与 `InNormalRange`），可删——但 doc 把它写成条件之一（「且 `0 < |x|` 时」），删前件须同时改 doc。D 维度无问题：常数 2 已如实标注（要常数 1 需最近偶数语义），这是正确的 ε-界而非降级。",
    C="删 `_hx`（证明未用）；同时改 doc 去掉「且 0 < |x|」")

add(241, "keep",
    "`B.toFloatFormat.eps = B.eps` 是 `toFloatFormat` 定义里 `eps := B.eps` 的展开（`rfl`）；虽为定义展开，但它是唯一把两套浮点参数耦合起来的断言（改 def 即断），有护栏价值，Consistency 文件依赖它。")

add(245, "keep",
    "`tiny` 的同款定义展开（`rfl`），同上：两套参数耦合的唯一断言，改 `toFloatFormat` 即断。")

# ---- assemble -----------------------------------------------------------------
rows = []
with io.open(SRC, encoding="utf-8") as f:
    for ln in f:
        ln = ln.strip()
        if not ln:
            continue
        o = json.loads(ln)
        rows.append(o)

missing = [o["line"] for o in rows if o["line"] not in V]
extra = [k for k in V if k not in {o["line"] for o in rows}]
if missing or extra:
    print("MISSING:", missing)
    print("EXTRA:", extra)
    sys.exit(1)

ptr = {}
for o in rows:
    n = len(V[o["line"]])
    i = ptr.get(o["line"], 0)
    if i >= n:
        print("COUNT MISMATCH at line", o["line"], o["name"], "have", n)
        sys.exit(1)
    ptr[o["line"]] = i + 1

counts = {k: 0 for k in ("keep", "strengthen", "downgrade", "delete", "register")}
ptr = {}
with io.open(OUT, "w", encoding="utf-8", newline="\n") as f:
    for o in rows:
        i = ptr.get(o["line"], 0)
        ptr[o["line"]] = i + 1
        v = V[o["line"]][i]
        rec = {
            "file": o["file"], "line": o["line"], "name": o["name"],
            "verdict": v["verdict"],
            "A_strength": v["A_strength"], "B_missing": v["B_missing"],
            "C_hypotheses": v["C_hypotheses"], "D_downgrade": v["D_downgrade"],
            "E_coverage": v["E_coverage"], "F_content": v["F_content"],
            "note": v["note"],
        }
        counts[v["verdict"]] += 1
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")

print("rows:", len(rows), "counts:", counts, "out:", OUT)
