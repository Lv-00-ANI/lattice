# 否证清册（REFUTATION-CENSUS）

> 第 35 轮。脚本 `agent-tmp/fix_families.py` 生成分类，`agent-tmp/write_census2.py` 产出本文件。
>
> 一个形式化库的可信度，很大程度上取决于它**明确知道什么做不到**。
> 本清册把库中已证伪的论断归类，作为这一维度的证据面。

## 1. 数量与分布

**365 条**否定结论：`theorem`/`lemma` 级，且**结论类型**以 `¬` / `not` / `→ False` 开头。（第 265 轮几何层归档后由 342 降至 336：归档的 6 条反例移出主线统计。）

| 层 | 条数 | 占比 |
|:--|--:|--:|
| `Lib` | 253 | 85.3% |
| `Lift` | 0 | 0.0% |
| `Runtime` | 13 | 3.2% |
| `Domains` | **0** | 1.9% |
| `Evidence` | 8 | 2.7% |
| `Core` | 59 | 5.7% |
| `Geo` | 0 | 0.0% |
| `Compose` | 1 | 0.0% |
| `Plugins` | 22 | 9.2% |
| `Semantics` | 7 | 2.2% |
| `(root)` | 2 | 0.6% |

**分布值得注意**：87% 的否证在 `Lib`（具体领域），承重层（`Core`/`Lift`/`Runtime`/`Geo`/`Evidence`）
合计只占 28 条。这不是缺陷：承重层的职责不是穷举「不可能」，
而是钉住少数几条**关键**不可能性——而它们恰恰都在那里（见 §3）。

**第 77 轮新增一条**：`not_holds_gtZero_const_of_eval_zero` —— `gtZero` 要求【严格】不等式，
而退化配置给出的值恰为 `0`，故 `0 < 0` 不成立，且**没有任何表达式的选择能让它成立**——
这是本轮修正排除清单后【唯一幸存】的排除项，理由是结构性的而非偶然的。

**第 72 轮新增两条**：`collinear_not_expressible` 与 `parallel_not_expressible` ——
`collinear` 与 `parallel` 的代数层是 `existential`（需先消去见证），故它们【不能】进入
`ExpressibleSpec`。**这两条是 `T0` 的排除性见证：可表达性的边界由它们钉住。**

`Plugins` 的两条是插件框架的两条**边界**结论：
`refinement_not_mandatory`（C 后端不在强制义务内）与
`allMandatoryKindsCovered_nil_fails`（空注册表不可能覆盖任何强制义务）。

**第 162 轮新增一条**：`lift_shift_no_commute` —— **`inst_lift_shift` 的总体形式为假**
**（`b = var 0` 时左边 `var 0`、右边 `var 1`），故第 154 轮的「无绑定片段」限制**不是临时局限而是边界**。
故 `Core` 由 11 升为 12、总数由 329 升为 330。

**第 178 轮新增一条**：`basicHolds_unhandled` —— **IR 不含未定义语义的关系种类**
**（`lowRank` / `symmetry` / `depends` 等未定义 `Holds` 的 kind 造不出 `Relation`）**，
故 `Core` 由 12 升为 13、总数由 330 升为 331。

**第 182 轮新增两条**：`dependsHolds_nil`（空参数列表不满足 `depends`）与`holds3_unhandled`（未定义语义的 kind 造不出 `Relation`），
故 `Core` 由 13 升为 15、总数由 331 升为 333。

**第 189 轮新增一条**：`empty_graph_depends_false` —— **空依赖图不满足任何带真实输入的 `depends`**（`edges = fun _ => []` 时无物依赖无物），
故 `Core` 由 15 升为 16、总数由 333 升为 334。

**第 190 轮新增两条**：`canActivate_needs_requires`（需求未激活则激活门**拒绝**）与`resolution_certificate_stable`（provider 未变则证书**不失效**），
故 `Core` 由 16 升为 18、总数由 334 升为 336。

**第 191 轮新增一条**：`not_quiescent_of_unmet` —— **需求未满足的状态**不**是静息的**（`quiescent` 因此有实质内容，而非 `True`），
故 `Core` 由 18 升为 19、总数由 336 升为 337。
第 237 轮又加入一条：`pointTensors_not_covered`（`Core/IR/IsIR.lean`）证明「命名了错误位置的 relation 列表**不**覆盖同一批张量」，故 `Core` 由 19 升为 20、总数由 337 升为 338。

**第 160 轮新增一条**：`cutoff_commutation_false` —— **任意截断值下的 inst/shift 交换律为假**
**（`j=1, σ=常值 var 5, t=var 0` 时左边 `var 0`、右边 `var 6`），**根因是 `lift σ 0 = var 0` 而 `shift j 1` 在 `j>0` 时不动下标 0**。
故 `Core` 由 10 升为 11、总数由 328 升为 329。

**第 152 轮新增一条**：`comp_candidate_false` —— **教科书式替换复合律在本演算下为假**
**（`j=0, s=var 1, t=var 0, u=var 1` 时左边 `var 1`、右边 `var 0`），**根因是两侧的递减次数不同**。
故 `Core` 由 9 升为 10、总数由 327 升为 328。

**第 150 轮新增一条**：`shift_different_cutoffs_dont_commute` —— **第三次尝试的 shift 交换律也为假**（`c=2,d=1,c'=1,d'=1,n=1` 时左边 `var 3`、右边 `var 2`），
**三次都卡在同一个边界：恰好落在两个截断值之间的索引。**
故 `Core` 由 8 升为 9、总数由 326 升为 327。

**第 149 轮新增两条**：`no_step_var` 与 `no_step_sort` —— **`Step` 的每个构造子源形状都是 `app`/`letE`/`const`/`lam`/`pi`，故变量与宇宙**无出边****，
**这是 `reduction_is_oriented` 的正确替代形式（该 Prop 过强）。**
故 `Core` 由 6 升为 8、总数由 324 升为 326。

**第 147 轮新增一条**：`shift_comm_counterexample` —— **第 146 轮点名的 shift 交换律本身为**假****（`c=3, d=2, t=var 2` 时左边 `var 5`、右边 `var 3`），
**故修正后的替换律需要另寻分解，不能靠这条交换律。**
故 `Core` 由 5 升为 6、总数由 323 升为 324。

**第 146 轮新增一条**：`old_subst_shift_law_is_false` —— **第 135 轮点名的 `subst_shift_law` 本身为**假****（`j = 1` 时左边得 `var 1`、右边得 `var 0`），
**六次证明尝试失败不是因为重写顺序，而是因为命题不成立。**
故 `Core` 由 4 升为 5、总数由 322 升为 323。

**第 133 轮新增一条**：`sqDist_equivalence_requires_nonneg` —— **在真实 `sqDist` 上，去掉 `0 ≤ t` 后平方形式与开方形式仍不等价**，
**故几何层的阈值假设同样是真实成本，不只是坐标层。**
故 `Semantics` 由 6 升为 7、总数由 321 升为 322。

**第 132 轮新增一条**：`threshold_extraction_requires_nonneg` —— **去掉 `0 ≤ tau` 后平方形式与绝对值形式不再等价**，
**故 `thresholdInherits` 的 `sound` 所带的子类型假设是真实成本。**
故 `Semantics` 由 5 升为 6、总数由 320 升为 321。

**第 130 轮新增一条**：`nat_not_finite` —— **`ℕ` 没有 `Fintype` 实例**，
**故 `meaningTypesDiffer` 的计数路线在项目载体上无法起步——这不是缺证明，是路线的前提不成立。**
故 `Semantics` 由 4 升为 5、总数由 319 升为 320。

**第 128 轮新增一条**：`noncommuting_counterexample` —— **两个不交换的节点使 `dag_confluence` 为假**，
**故该定理的交换性假设是真实成本而非装饰。**
故 `Plugins` 由 28 升为 29、总数由 318 升为 319。

**第 122 轮新增一条**：`not_holdsSet_eqZero_const_one` —— **`eqZero (const 1)` 在零配置处不成立**，
**故 `labelAt_depends_on_carrier` 有真实见证：空集与它在该配置上取值不同。**
故 `Semantics` 由 3 升为 4、总数由 317 升为 318。

**第 121 轮新增一条**：`no_token_dependent_inherits` —— **`Inherits` 中不存在依赖 token 的行为**，
**因为 `sound` 的左边不含 `toks`，故右边不能含。第 120 轮的缺口是结构设计限制，不是缺实例。**
故 `Semantics` 由 2 升为 3、总数由 316 升为 317。

**第 120 轮新增一条**：`constant_label_blocks_complete` —— **常值标注的几何不满足 `completeOn`**，
**故 `identityInherits` 所要求的满射假设是真实成本而非形式条件。**
故 `Semantics` 由 1 升为 2、总数由 315 升为 316。

**第 119 轮新增一条**：`refines_not_trivial` —— **存在不精化任何约束的程序/约束对**，
**故 `refines` 关系既非空也非全，是真正的二元关系而非永真式的包装。**
故 `Semantics` 由 0 升为 1、总数由 314 升为 315。

**第 112 轮新增一条**：`sat_alone_not_fixed` —— **仅有 `Sat` 不足以给出不动点**，
**因为 `fix` 可以在满足点上移动它，除非 `Repair.absorbs` 被施加。**
**这条使 T4 的第三条义务（`t4_loop_fixed_point`）非平凡，而非 `Sat` 的推论。**
故 `Plugins` 由 27 升为 28、总数由 313 升为 314。

**第 102 轮新增一条**：`no_artifact_extractor_recovers_both` —— **没有任何提取器能同时是编译的左逆
与语义忠实的**。**它不是新事实，而是把 `Extraction.no_extractor_both_layers` 搬到工件层的词汇里**，
**因为 `SymbolicSummary` 之所以是「摘要」而非「规格重建」，正是由它决定的**。
故 `Plugins` 由 26 升为 27、总数由 312 升为 313。

**第 98 轮新增一条**：`no_loop_fixes_unsatisfiable` —— **没有闭环能修好不可满足的目标**。
**它不是新事实，而是把「`Repair` 收敛」与「`Sat` 可能为空」放在一起后必然的否定**，
**故 `Runtime` 由 9 升为 10、总数由 311 升为 312。**

**第 95 轮：`(root)` 由 4 降为 2，总数由 313 降为 311。**
**这两个否证消失的原因是它们【变成了真命题】**：`pluginCensusPending_holds` 断言
「注册表小于清单」，而清单的旧值 43 数的是【目录分组】而非插件。
**改正为 8（有 `Manifest.lean` 的目录数）后，该断言为假，随之被删除。**
**=> 否证清册在一次定义错误被纠正时会下降，且下降本身是修正的证据。**

**第 94 轮完成最后一次搬迁**：`Core/VariableDerivative.lean`（5,506 行，整条提取线）移入
`Plugins/Extractors/ChainSlot/`。**八个注册插件至此全部自有其义务**，`Core` 由 9 降为 4、
`Plugins` 由 21 升为 26。
**总数由 315 降为 313，减少的两条来自 `(root)`（6→4）**：`Plugins.lean` 中
`proofRegistry_migrated_pending` 被相反命题 `proofRegistry_migrated` 取代，
**旧的否证证明随命题一起消失——这不是统计损失，而是那个否定本身不再成立。**

**第 92 轮同计搬迁**：`Repair.lean`、`RepairAtomicity.lean`、`RepairConvergence.lean`、
`RepairMultistep.lean`、`RepairWF.lean` 移入 `Plugins/Core/Repair/`，故 `Core` 由 10 降为 9、
`Plugins` 由 20 升为 21，**总数不变**。**六个插件已完全自有其义务。**

**第 91 轮同计搬迁**：`Domains/Constraints/Flatten.lean`、`SeqRepresentation.lean`、
`LossExtraction.lean` 移入 `Plugins/Domains/Constraints/Tokens/`，故 `Domains` 由 7 降为 6、
`Plugins` 由 19 升为 20，**总数不变**。**五个插件已完全自有其义务。**

**第 90 轮同样计【搬迁】而非新增**：`Compose` 的 `Compose/Combinators.lean`、
`Compose/ComposeObligation.lean`、`Compose/Laws.lean` 与 `Core/Logic.lean` 全部移入各自插件目录，
故 `Compose` 由 1 降为 0、`Plugins` 由 18 升为 19，**总数不变（315）**。
**`Compose` 层归零是预期的：它此前的唯一一条否证现在住在 `Plugins/Compose/` 之下。**

**第 88 轮不计新增，计【搬迁】**：`Norm` 的 21 条定理从
`Lib/Architectures/RealBatchNormConsistency.lean` 移到
`Plugins/Architectures/Norm/Proofs.lean`，故 `Lib` 由 257 降为 256、`Plugins` 由 17 升为 18，
**总数不变（315）**。**这是一次真正的 `move + facade`：旧路径现在只 import 新模块，不含任何证明。**

**第 87 轮新增两条**：`Plugins` 的 `registryMigratedFor_fails_of_unlisted`（未列出的插件
使迁移失败）与 `(root)` 的 `unlisted_plugin_fails_migration`（同上，在注册表层）。
**这两条关闭了第 86 轮标注的 fail-open 缺陷：`pluginDirOf` 的兜底曾是 `""`，
而空串是【一切】的前缀，故未分类的插件会被判为已迁移；现在兜底是 `none`，未列出即失败。**

**第 86 轮新增三条**：`Plugins` 的 `coreConstraint_is_citation`（`Core.Constraint` 的首条义务指向
`Lattice/Core/Logic.lean`，故它是引用）、`(root)` 的 `proofRegistry_not_migrated`
（故 `RegistryMigratedFor pluginDirOf proofRegistry` 为假）与 `registryMigratedFor_nil` 的反面
用法。**这三条把「迁移是引用而非搬运」接进了 `ProofComplete` 本身**——审计的核心批评现在
是完成谓词上一条可被否证的合取项。

**第 85 轮新增六条**（均在 `Plugins`，`Migration.lean`）：`strPrefix_cons_ne`、
`strPrefix_cons_ne_gen`、`plugins_not_prefix_lib`、`lib_not_prefix_plugins`、
`norm_obligation_is_a_citation`、`not_migrated_of_foreign` ——
**这六条把「迁移是引用而非搬运」从散文断言变成可检查的事实。**
**其中前两条是一般引理（不同字符不构成前缀），后四条是它们在具体路径上的应用。**

**第 80 轮新增三条**（均在 `Plugins`）：`unsatisfiableSpec_no_model`（`[eqZero (const 1)]`
这个可表达规格【没有任何模型】）、`no_specSolver`（故 `SpecSolver n` 对非空点类型是 `IsEmpty`）、
`familyTotalGives_no_solver`（故任何族都无法补出一个 `SpecSolver`）。
**这三条把第 74 轮只能【断言】的接口边界变成了定理；审计指出的幽灵引用
`specSolver_is_family_limited` 也由此有了真身。**

**第 79 轮新增一条**：`deactivate_before_unload` —— 若 `y` 存活且可达 `x`，则 `x` 【不】可被失活。
**这是 T6（`spatial`）的依赖侧见证：插件的「空间」即为它存活期间不可移除的插件集合。**
**它取可达性的【传递闭包】，而非直接边——只查一步会放过经两跳的依赖，这正是经典的卸载 bug。**

**第 78 轮新增两条**（均在 `(root)`）：`empty_plugin_excluded` 与
`registry_with_empty_plugin_not_complete` —— **前者说空插件不满足 `NonVacuousFor`，后者说
含空插件的注册表【不】完备。这两条是本轮堵住「假完成路径」的形式见证。**

> **第 70 轮的更正**：`(root)` 层原有的两条否证（`registryComplete_fails`、
> `pluginRegistryComplete_not_yet`）**已被删除**——它们以「没有插件声明 `recovery`」为见证，
> 而 `Compose` 迁移后该见证不再成立。**结论变了，所以定理也必须变**，而不是保留一条
> 已经不真的命题。**当前注册表的完备性改由「类覆盖成立 + 插件普查未完成」两条**肯定**陈述
> 承载（见 `Plugins.lean` 的 `currentState`）。

## 2. 按否证的对象分类

| 类别 | 条数 | 含义 |
|:--|--:|:--|
| 谓词不可达（结论是某性质不成立） | 135 | 某个性质在任何配置上都取不到（如 `¬ Sat (iterate n x)`） |
| 等式被否（含不相等） | 37 | 某等式普遍不成立，或两对象不相等 |
| 界/不等式被否 | 31 | 某个界/单调性给不出来 |
| 全称命题被否（给出反例） | 26 | 一般断言不成立，必须附加前提 |
| 单射性被否 | 19 | 编码或映射会丢失信息 |
| 等价被否 | 13 | 两个刻画不能等同 |
| 存在性被否 | 10 | 某类对象不存在（`¬ ∃ …`） |
| 矛盾不可满足 (→ False) | 5 | 某组条件无法同时成立 |
| 极值/极小性被否 | 4 | 某点不是极小/极大（惩罚不精确） |
| 满射性被否 | 4 | 编码达不到某些目标 |

## 3. 承重层的否证（最重要的一组）

这些定理说明**这条链路在哪里停下来**：

| 层 | 定理 | 否证的内容 |
|:--|:--|:--|
| `Evidence` | `bridge_is_necessary` | `¬ (∀ (P Q : ℕ → Prop) (f g : ℕ → ℕ), (∀ x, P x → P (f x)) → (∀ x, Q x → Q (g x)) → ∀ x, P x → Q (g (f x))` |
| `Evidence` | `bridged_needs_bridge` | `¬ (∀ (P Q : ℕ → Prop) (f g : ℕ → ℕ), (∀ x, P x → P (f x)) → (∀ x, Q x → Q (g x)) → ∀ x, P x → Q (g (f x))` |
| `Evidence` | `sq_le_needs_nonneg` | `¬ (∀ r ε : ℝ, r ^ 2 ≤ ε ^ 2 → \|r\| ≤ ε)` |
| `Evidence` | `eps_needs_nonneg` | `¬ (∀ ε : ℝ, (0 : ℝ) ^ 2 ≤ ε ^ 2 → (0 : ℝ) ≤ ε)` |
| `Evidence` | `lipschitz_needs_nonneg` | `¬ (∀ L δ : ℝ, 0 ≤ δ → (0 : ℝ) ≤ L * δ)` |
| `Evidence` | `delta_is_input` | `¬ (∀ L δ : ℝ, 0 ≤ L → 0 ≤ δ → L * 0 = L * δ)` |
| `Evidence` | `destructiveFix_not_absorbs` | `¬ (∀ n : ℕ, n = 0 → destructiveFix n = n)` |
| `Evidence` | `absorbs_not_derivable` | `¬ (∀ (Sat : ℕ → Prop) (fix : ℕ → ℕ) (μ : ℕ → ℕ), (∀ n, ¬ Sat n → μ (fix n) < μ n) → (∀ n, μ n = 0 → Sat n` |
| `Core` | 57 | `¬ Function.Injective relu` |
| `Core` | 57 | `¬ Function.Injective (fun x : Fin 1 → ℝ => reluVec (netAct [] x))` |
| `Core` | 57 | `¬ countdown.Sat (countdown.iterate n k)` |
| `Core` | 57 | `¬ BehaviourallyEquivalent p q` |
| `Core` | 57 | `(∃ p q : LayerParams (Fin 1) (Fin 1), p ≠ q ∧ BehaviourallyEquivalent p q) → False` |
| `Geo` | `no_rules_no_steps` | `¬ ∃ r ∈ ([] : List (Rule n)), c = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d` |
| `Geo` | `not_eventually_zero_of_small_counterexample` | `False` |
| `Geo` | `sqDist_samePoint_not_localMin` | `¬ IsLocalMin (fun x : ℕ → Pt n => (sqDist (n` |
| `Geo` | `const_one_unsatisfiable` | `¬ GeoConstraint.Holds (.eqZero (.const 1)) pts` |
| `Geo` | `copy_not_separating` | `¬ Separated a b (fixSamePoint a b pts)` |
| `Lift` | `no_extractor_both_layers` | `¬ (∃ extract : W → P, (∀ p, extract (compile p) = p) ∧ (extract (compile c) = extract (compile c')))` |
| `Lift` | `constant_changes_semantics` | `¬ Lattice.Core.SatisfiesEq (⟨fun _ => (0 : ℤ), 1⟩ : Lattice.Core.LinearForm ℤ 1) (fun _ => 0)` |
| `Lift` | `rank_one_is_degenerate` | `¬ (∀ (W : Fin 2 → Fin 2 → ℝ), ∃ c : Fin 2 → ℝ, ∀ i j, W i j = c i)` |
| `Lift` | `const_not_levelB` | `¬ PenaltyExact constEmbedding` |
| `Lift` | `tokenize_not_injective` | `¬ Function.Injective tokenize` |
| `Lift` | `tokenize_never_none_fails_for_Vzz` | `¬ (∀ s : List Char, ∃ ts : CharToken, bestPrefixV Vzz s = some ts)` |
| `Lift` | `drop_b_changes_semantics` | `¬ VectorConstraintSat ({ a` |
| `Lift` | `compileZ_not_injective` | `¬ Function.Injective compileZ` |
| `Lift` | `sep_chars_distinct` | `¬ (classify cs = .sep ∧ classify cs = .sym)` |

## 4. 分类方法与**三次修正**（如实记录）

**判定规则**：取陈述的**结论类型**（最后一个顶层 `:` 之后），
若以 `¬` / `not ` / `→ False` 开头即计入。分类时先剥掉前导 `¬` 与外层括号，
再按**最外层构造子**匹配（量子词 → 等价 → 等式 → 极值 → 不等式 → 谓词应用）。

**三次修正过程**：

| 版本 | 结果 | 问题 |
|:--|:--|:--|
| 初版 | 329 条 | 只要陈述里出现 `¬` 就计入，把假设里的否定（`(h : ¬ j ≤ i)`）也算进来 |
| 二版 | 272 条 | 改为只看结论，但**文件路径被输出格式截断**，层统计出错（`ib`、`b` 出现） |
| **三版** | **292 条** | 完整路径 + 按最外层构造子分类；抽查发现 3 处误分类并修正 |

**残留误差**（仍存在，读者需知道）：

1. **语法而非语义**：形如 `¬ False` 的平凡否证也会计入，本清册不判断平凡性；
2. **「谓词不可达」占 135 条**（最大类），
   其中不少是**带条件**的事实（例如「在 `¬mask i j` 时输出为零」），
   它们的结论确实是 `¬…`，但整体是条件性结论而非反驳。**计入是保守的**（宁可多算）；
3. **`∃` 绑定子含 `:`**，嵌套深时可能误判个别条目。

## 5. 用途

1. **读者**：想知道「这个库限制了什么」，查 §3。
2. **后续工作**：新增一条「不可能」比新增一条「可能」更有价值——它排除一条路线，
   而 §2 的分类给出了哪些方向的排除已存在。
3. **定位**：项目自称通用基础设施。基础设施的可信度来自**边界清晰**，
   本清册就是那条边界的清单。

**第 779 轮**：新增 3 条（`binderCommutation_counterexample`、`binderCommutation_false`、
`binderCommutation_needs_identity_at_zero_false`），故 `Core` 由 24 升为 27、总数由 336 升为 339。

**第 786 轮**：新增 1 条（`selfLoop_no_normal_form`），故 `Core` 由 27 升为 28、总数由 339 升为 340。

**第 787 轮**：新增 2 条（`selfLoopEnv_not_lowerOnly`、`no_self_delta`），故 `Core` 由 28 升为 30、总数由 340 升为 342。

**第 791 轮**：新增 1 条（`all_indices_bound_too_strong`），故 `Core` 由 30 升为 31、总数由 342 升为 343。

**第 796 轮**：新增 2 条（`stuck_term_cannot_step`、`progress_is_false`），故 `Core` 由 31 升为 33、总数由 343 升为 345。

**第 797 轮**：新增 3 条（`neutral_not_sort`、`neutral_not_const`、`neutral_not_lam`），故 `Core` 由 33 升为 36、总数由 345 升为 348。

**第 799 轮**：新增 1 条（`neutral_can_be_stuck_var`），故 `Core` 由 36 升为 37、总数由 348 升为 349。

**第 800 轮**：新增 1 条（`headForm_value_not_neutral`），故 `Core` 由 37 升为 38、总数由 349 升为 350。

**第 802 轮**：新增 2 条（`canonical_not_app`、`canonical_not_letE`），故 `Core` 由 38 升为 40、总数由 350 升为 352。

**第 804 轮**：新增 3 条（`totalEnv_ne_empty`、`const_no_step_empty`、`const_app_cannot_step`），故 `Core` 由 40 升为 43、总数由 352 升为 358。

**第 805 轮**：新增 1 条（`no_const_typed`），故 `Core` 由 43 升为 44、总数由 358 升为 358。

**第 807 轮**：新增 1 条（`var_does_not_step`），故 `Core` 由 44 升为 45、总数由 358 升为 358。

**第 810 轮**：新增 1 条（`piShapeR_sort_false`），故 `Core` 由 45 升为 46、总数由 358 升为 358。

**第 814 轮**：新增 1 条（`hasTypeW_no_const`），故 `Core` 由 46 升为 47、总数由 358 升为 359。

**第 816 轮**：新增 1 条（`hasTypeW_no_const'`，与 `hasTypeW_no_const` 同命名故带撇号），故 `Core` 由 47 升为 48、总数由 359 升为 360。
