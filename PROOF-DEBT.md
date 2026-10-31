# PROOF-DEBT：证明强度的诚实登记

> **本文件由 `gov/gen_proof_debt.py` 生成，勿手改。**

## 为什么有这个文件

项目此前的完成标准是「有名字、是定理、0 `sorry`」。**Lean 只检查定理是真的，从不检查它有多强**，
于是一条 `:= h` 的复述、一条 `a = a` 的重言、一条只覆盖 4/12 的定理，
可以和真正完整的定理一样被 `import`、被引用、被写进「已闭合」。

**这不是猜测，是审阅出来的。** 第一层（被下游引用的 1,360 条定理）由子代理逐条按六个维度判定，
结论在下面。六维度是：

| 维度 | 问题 |
|:--|:--|
| A 强度 | 陈述是否需要更强才能支撑它的**用途**？ |
| B 配套 | 按用途看还缺哪些定理？ |
| C 前件 | 哪些假设本身可证、从而能删掉？ |
| D 降级 | 精确做不到时，能否把声称降级成误差界（精确 → ε）？ |
| E 覆盖 | doc 声称的范围是否真的覆盖？ |
| F 信息量 | 是否重言 / 只复述假设 / 纯占位？ |

## 严重度：不是「好不好修」，是「误导得多厉害」

| 判定 | 含义 | 为什么这个顺序 |
|:--|:--|:--|
| **delete** | 陈述无信息量（`a = a`、`:= h`、`True`） | **什么都没说**，却占着一个名字，最坏 |
| **strengthen** | 说的比该说的弱 | 说了真话但不够，下游按名字以为够 |
| **downgrade** | 声称过强，实际只到子类/误差界 | 说了过头的话 |
| **register** | 有债但当前不值得修 | 已知、已记录 |

同一严重度内按**入度**（多少别处文件引用）降序：**被二十个文件依赖的弱定理才是会传染的那个。**

## 统计（本层）

| 判定 | 条数 |
|:--|--:|
| `delete` | 44 |
| `strengthen` | 24 |
| `downgrade` | 0 |
| `register` | 97 |
| `keep` | 1217 |
| **合计审阅** | **1409** |

**这张表是「第一审判了多少条」，不是「还剩多少条没做」。**

第 208 轮试过加一列「已处理 / 剩余」，**又删掉了**：账本里的一行可以覆盖 8 条判定（`delete × 8` 就是一行），也可能一条判定被推翻成另一类——
**于是「剩余」会用行数算出假数字**（它会显示 `delete` 还剩 44，而那 44 条早已判完：
8 条删除、34 条被对抗性复核推翻、3 条改写）。**错的统计比没有统计更糟。**

真正做了什么，看下面的「已处理」一节与「对抗性复核」一节——**那两节逐条列出，不做汇总。**

## 覆盖范围：这份账本审了谁、没审谁

**这张表的数字由 `gov/check_coverage_claim.py` 计算，并由同一个脚本作为门禁核对。**
生成器与门禁**共用同一个测量函数**，所以它们不可能互相漂。

定义（三条都要满足才算「被引用」）：

1. **只数定理与引理**——`def`/`structure` 没有可审的证明；
2. **只数代码**——剥掉注释与 docstring，散文里提到一个名字不算引用；
3. **引用方必须真的 `import` 定义所在模块**——另一个命名空间里的同名声明不算。

| 总体 | 条数 | 已审 | 覆盖 |
|:--|--:|--:|--:|
| 定理 + 引理 | 8816 | 1238 | 14.5% |
| **入度 ≥ 1（承重集）** | **924** | **924** | **100%** |
| **入度 = 0** | **7892** | **354** | **4.5%** |

**两个方向都要读；只读一个是误导。**

- **承重集 100% 覆盖**：896 条被下游真正消费的定理全部审过（第 66 轮补审最后 12 条）。
  ⚠ **第 27 轮修正**：此前这里写的是「**100% 覆盖**」，而它上面的表格写的是 78.2%——
  **同一页三个数字**（表格 78.2%、正文 100%、更正段说集合算错、正确值是 839）。
  三个都来自**手写或过期的入度**，没有一个来自能复算的仪器。**现在只有一个数字，来自一个函数。**
- **零入度只有 4.5%**：7892 条入度为 0 的定理里审了 354 条。**这才是「样本」真正指的东西。**

### 承重集里**尚未审阅**的 7 条（逐条列出，不做汇总）

**这是本轮唯一还没做到的百分之几。** 它们入度 ≥ 1、被下游引用、但还没有判定：

- `affine_zeroSet_subsingleton`
- `exp_sub_one_le`
- `idxW_lt`
- `layerWords_length`
- `softmax_le_one`
- `softmax_lipschitz`
- `sq_eq_two_roots`

**为什么列出来而不是抹平**：把这 7 条补审之后，承重集才能真的说 100%。
在此之前它说 **99.2%**，并且**说得出缺的是哪些**——这比一个漂亮的整数有用。

### 零入度未审**不等于**已审，也不等于无害

**入度为 0 只说明「没有其他定理引用它」，不说明「它说了真话」。**
一条名义完成的定理可以零引用——本账本已删的 `hasQuadraticLowerBound_iff_self`（`a = a`）
与 `syntacticFunctor_id` 都是这一类。**它们误导不了下游，但它们在库里，读者会读到。**

### 零入度的抽样协议（第 27 轮写下）

**7668 条零入度定理不逐条语义审阅，这是显式取舍，不是遗漏。**

**抽样的依据**：过去的审阅按「旧的有缺陷的入度」选第一层，因此其中约三百多条
实际入度为 0——**它们不是为「零入度」抽的样，而是为「高价值」抽的样，事后发现落在零入度里。**
所以这个 354 条样本**不是随机抽样**，**偏向「曾经看起来重要」的那一侧**，
这对零入度集合是**有偏**的（偏向复杂的、被写进 docstring 的、跨文件重名的）。

**边界，写成可核对的断言**：

1. **不声称零入度集合已审**——覆盖率就是上表那个数字；
2. **不声称它不需要审**——`a = a` 这类重言正是零引用也能存在的；
3. **不按「误导下游」给零入度排序**：它们不误导下游，**它们误导读者**——
   而读者的检索路径不可形式化，所以**这里没有可证的优先级**，只有一条明说的取舍。

**若要全审**：正确做法是另开批次文件（`agent-tmp/review/batch_*.jsonl` 现有格式已支持），
**不是把现状说成已审**。

### 判定指向的声明**已不存在**的 12 条（第 29 轮登记）

**这些判定不是错的，而是没有对象了**：它们判的那条定理在活树里已经不存在——
`check_proof_debt_orphans.py` 只核对**文件**是否可解析，从不核对**名字**是否还在，
所以它们此前和活判定长得一模一样。`check_verdict_freshness.py` 现在每次重算并拦住新增。

| 原文件 | 定理 | 实测理由 |
|:--|:--|:--|
| `Evidence/ChainTransitivity.lean` | `preserves_one` | name is declared nowhere in the live tree (renamed or deleted) |
| `Evidence/CompositionClass.lean` | `bridged_needs_bridge` | name is declared nowhere in the live tree (renamed or deleted) |
| `Evidence/CompositionClass.lean` | `evidence_kinds_differ` | name is declared nowhere in the live tree (renamed or deleted) |
| `Evidence/CompositionClass.lean` | `sequential_evidence_trivial` | name is declared nowhere in the live tree (renamed or deleted) |
| `Evidence/Hypotheses.lean` | `no_redundant_hypotheses` | name is declared nowhere in the live tree (renamed or deleted) |
| `Evidence/MultiComposition.lean` | `chain_nil_identity` | name is declared nowhere in the live tree (renamed or deleted) |
| `Evidence/PredicateWitnesses.lean` | `isRedundant_true` | name is declared nowhere in the live tree (renamed or deleted) |
| `Evidence/StructureCensus.lean` | `no_zero_obligation_structure` | name is declared nowhere in the live tree (renamed or deleted) |
| `Lib/Editing/RealCanonicalCompileComm.lean` | `comm_via_extract` | name is declared nowhere in the live tree (renamed or deleted) |
| `Lib/Editing/RealExtractSurjectivity.lean` | `extractVec_range_ne_proper` | name is declared nowhere in the live tree (renamed or deleted) |
| `Runtime/ConstraintToLoss.lean` | `compile_changes_type` | name is declared nowhere in the live tree (renamed or deleted) |
| `Runtime/RatRepresentation.lean` | `compile_changes_type` | name is declared nowhere in the live tree (renamed or deleted) |

**为什么仍然列在这里而不是删掉**：它们记录的是「有人看过这一条、并给了判定」这一事实；
把记录删掉会让账本看起来更干净，**而它并不会更干净**。


> **范围（一条必须说清的更正）**：本文件覆盖 **1,360 条**已审定理。
> 它们最初是按**旧的、有缺陷的** `in_degree` 选出来的「第一层」。
> 审阅人指出该指标把 docstring 提及与不同命名空间的同名声明算成引用，
> 修正后（只计代码、且要求引用方真的 `import` 该模块）入度 ≥ 1 的定理只剩 **839** 条，
> 最高入度从 183 降到 18。
>
> 所以：**这 1,360 条是「高价值样本」，不是精确的「承重集合」**——其中约 521 条实际入度为 0，
> 而真正的承重集合里可能有尚未审阅的条目。
> **六维度的判定本身不受影响**（它们不依赖入度），受影响的只有排序与层边界。
> 下一轮按修正后的入度重跑第一层，并补齐剩余 7,587 条。

## 零、**C 契约的四条边界**（第 103 轮登记）

**这几条不是「没做完的证明」，是「在当前结构下不可陈述的对应」。**
**决策与理由见 `CONTRACT-DECISION.md`；本节只登记。**

| # | 边界 | 内容 | 状态 |
|:--|:--|:--|:--|
| **B-1** | **ABI 对应** | `CFunction` 表与 `Primitive` 之间的 arity／类型对应 | **未验证假设** |
| **B-2** | **C 实现等价** | C 侧行为与 Lean 侧 `Primitive` 语义相等 | **未验证假设** |
| **B-3** | **`WordEncoder`** | 定义在 `CInterface/LayoutBytes.lean`，**无实例** | **未实现** |
| **B-4** | **条目数** | ABI **11** vs SEMANTICS **12** | **不一致，已证不可桥接** |

**为什么 B-1 不可验证（四条已证的负结果，都在 `CInterface/ContractBoundary.lean`）：**

1. **`Primitive` 没有 arity 字段**——`I` 是类型，不是参数表，**所以「C 侧 arity = `Primitive` arity」连陈述都写不出来。**
   **这是根**。
2. **对照向量不对应 `Primitive.I`**——`descentStep` 的 `I` 是 `ℝ`，而它的向量有 3 个 `Float`
   （`descentStep_vector_width_ne_primitive_width`）；
3. **ABI 参数里没有数据参数**——`compose` 的 `args = [cstr, size, size]`，两个 `Primitive` 不在任何参数位上
   （`composeArgs_has_no_data_parameter`、`abiTable_compose_args`）；
4. **类型级不兼容**——11 个里 10 个的 `f64` 槽位数不足，7 个连一个 `Float` 槽都没有
   （`seven_primitives_float_inputs_have_no_f64_slot`、`three_primitives_have_too_few_f64_slots`）。

⚠ **第 1 条不是「补一条证明」能解决的**：它要求给 `Primitive` 加参数表——
**而那是架构级改动（7 个直接实例 + 6 个组合子 + 它们各自的所有 `where` 块），
且【仍然】不解决第 2 条。所以本层选择「不透明 + 登记」，理由在 `CONTRACT-DECISION.md` 第四节。**

**⇒ 这几条使 `e2e_sound` 的终点只能到 Lean 侧的 `Primitive`，到不了 C。**
**这不是缺口，是边界；而边界的诚实性依赖于它被写下来。**

---

## 一、`delete`：陈述无信息量

| 位置 | 定理 | 入度 | 判定依据 |
|:--|:--|--:|:--|
| `Lib/Editing/RealCompileExtractClosed.lean:206` | `closed_loop_adds_nothing` | 2 | F: 重言 (P↔Q)↔(P↔Q),信息量为零 |
| `Lib/Editing/RealOperatorSplit.lean:51` | `t1_decompose` | 2 | 重言：加法逆元恒等式（`add_sub_cancel`）。 |
| `Lib/Architectures/RealNormalEquation.lean:115` | `fderiv_eq_zero_iff_all` | 1 | 纯重言：fderiv f x = 0 ↔ ∀v, fderiv f x v = 0 是 CLM 外延 + map_zero，零信息；另有 _scalar 版重复（RealNormalEquationScalar:162） |
| `Lib/Attention/RealTemporalLayer.lean:224` | `split_immediately_confers_concept` | 1 | 证明体就是 h（P→P）；命题 = extent 的成员定义，属「只复述假设」。 |
| `Lib/Attention/RealTemporalLayer.lean:284` | `up_gaze_element_or_concept` | 1 | by_cases hasUpper 后两分支 exact Or.inr/inl，即 em；非穷尽性证明。 |
| `Lib/Attention/RealTemporalLayer.lean:338` | `suspend_dissolves_identity` | 1 | rfl：suspend := withGaze none，IsElement := gaze = none ⟹ 命题 = (none = none)。 |
| `Lib/Compiler/ModConstraint.lean:41` | `mod_preserves` | 1 | Iff.rfl：Congruent x a m := m ∣ x − a，ModOut x a := x − a，Divisible out m := m ∣ out，展开后左右是同一命题，零信息。 |
| `Lib/Concentration/RealMeasureTheoryBase.lean:194` | `prob_isFinite` | 1 | 只复述类型类：proof = `inferInstance`，结论由环境实例直接得到，零信息。 |
| `Lib/Lift/RealNonlinearFidelity_parts/B.lean:180` | `decidable_zeroFixing_siluZ` | 1 | ZeroFixing act_siluZ 展开为 ∀ y, (y = 0 ↔ y = 0)；证明体两方向分别就是 `hy` 与 `hy ▸ rfl`，是重言。 |
| `Lib/Lift/RealNonlinearFidelity_parts/B.lean:185` | `decidable_zeroFixing_geluZ` | 1 | ZeroFixing act_geluZ 展开为 ∀ y, (y = 0 ↔ y = 0)，证明体两方向都是 hy / hy ▸ rfl：重言。 |
| `Core/Repair.lean:117` | `stable` | 0 | 证明体就是 R.absorbs x h，即 Repair 结构体的一个字段投影，一字未改；等于把构造 Repair 时承诺的假设原样复述成「定理」。 |
| `Core/RepairAtomicity.lean:73` | `atomic_of_zero_iff` | 0 | 证明是 fun x hx => (h x).mp hx：结论就是前提的一个方向，重言。 |
| `Domains/Constraints/FlattenAgreement.lean:52` | `rather` | 0 | 非陈述：`stmt` = "theorem rather than a definitional equality. -/"，取自 docstring 第 52 行。 |
| `Domains/Geometry/RepairCoverage.lean:84` | `sqDist_nonneg` | 0 | 逐字重复（同陈述、同 4 行证明），位于 `Lattice.Geo.RepairCoverage` 命名空间下。 |
| `Evidence/ChainTransitivity.lean:111` | `preserves_one` | 0 | 证明 `hf x hx`：陈述是假设的直接实例化（`P x → P (f x)` 前件即 `hf`），零信息量。 |
| `Evidence/ChainTransitivity.lean:153` | `loop_preserves` | 0 | 证明 `preserves_iterate R.Sat R.fix (fun y hy => by rw [R.absorbs y hy]; exact hy) n x hx`：内容与 `Core/Repair.preserves:106` 逐字相同，零新增信息。 |
| `Evidence/CompositionAlgebra.lean:191` | `verdict_monoid_instance_agrees` | 0 | `⟨fun _ _ => rfl, rfl⟩`：两个等式都是定义性相等（实例取 `mul := (· ++ ·)`、`one := emptyVerdict`），恒真、不可能失败，零信息量。 |
| `Evidence/CompositionClass.lean:117` | `evidence_kinds_differ` | 0 | `⟨rfl, rfl⟩`：两个合取项都是定义性自等（`Evidence .sequential P Q` 归约到 `True`，`Evidence .bridged P Q` 归约到 `∀ x, P x → Q x`），零信息量。 |
| `Evidence/CompositionClass.lean:124` | `sequential_evidence_trivial` | 0 | 陈述定义展开后就是 `True`，证明 `trivial`：纯占位，零信息量（本批最纯的一条）。 |
| `Evidence/CompositionClass.lean:130` | `bridged_needs_bridge` | 0 | 证明是 `BridgedComposition.bridge_is_necessary`：一字不改地引用另一条定理，零新增信息。 |
| `Evidence/MultiComposition.lean:123` | `chain_single` | 0 | 归约后是 `h x hx`：只应用了一次假设，零信息量。 |
| `Evidence/MultiComposition.lean:128` | `chain_nil_identity` | 0 | `compose_chain (Chain.nil P) x hx` 归约后就是 `hx`：只复述假设。 |
| `Evidence/ObligationIndependence.lean:95` | `destructiveFix_atomic` | 0 | `fun _ hn => hn`：`n = 0 → n = 0` 是重言，且与同文件 :144 `ascendingFix_atomic` 的陈述逐字相同（两条一模一样的定理名）。 |
| `Evidence/ObligationIndependence.lean:144` | `ascendingFix_atomic` | 0 | `fun _ hn => hn`：重言；且与 :95 `destructiveFix_atomic` 的陈述逐字相同——同一文件里两条同名实不同名的重言。 |
| `Evidence/PredicateWitnesses.lean:69` | `isRedundant_true` | 0 | `rfl`：陈述是 `true = true`，重言（a=a），零信息量。 |
| `Lib/Architectures/RealOperatorNorm.lean:54` | `add_norm_bound` | 0 | 与 norm_add_le 逐字同义，零信息 |
| `Lib/Attention/RealTemporalLayer.lean:275` | `element_iff_no_upper` | 0 | Iff.rfl：isElementUnderUpGaze := ¬ hasUpper，命题即 P↔P。 |
| `Lib/Concentration/RealHoeffdingInequality.lean:333` | `condexp_hoeffding` | 0 | 重言：stmt 是假设的逐字复制，proof 体为 `hcond`（exact h）。 |
| `Lib/Editing/RealCanonicalCompileComm.lean:154` | `convertVec_extractVec_rfl` | 0 | 定义恒等：`cases l with \| mk w b => rfl`，展开即 `l = l`。 |
| `Lib/Editing/RealCanonicalCompileComm.lean:200` | `comm_via_extract` | 0 | 重言：`cases c with \| mk a b => rfl`，即 `canonicalize c = canonicalize c`。 |
| `Lib/Editing/RealCanonicalCompileComm.lean:344` | `canonicalize_absorbs_scale_pos` | 0 | 别名：与同库既有定理同陈述，proof 为单次应用（`canonicalize_section_pos c hg lam hlam`）。 |
| `Lib/Editing/RealConstraintEdit.lean:166` | `dot_replicate_zero_any` | 0 | 副本：同一命题在库内已有一份且被真实使用（LayerComposition:59），本副本零增量信息。 |
| `Lib/Editing/RealExtractSurjectivity.lean:127` | `extractVec_range_ne_proper` | 0 | 重言式改写：由 range = univ 得 ¬(univ ⊂ univ)，证明只有 rw 与 lt_irrefl，零信息。 |
| `Lib/Editing/RealExtractionDirection.lean:303` | `renderSurjective_holds` | 0 | 空洞真：任何有 section 的全函数都满足，与「抽取能恢复什么」无关。 |
| `Lib/LinearAlgebra/RealSparseCodingCounterexamples.lean:439` | `eq_softThresh_of_is_min` | 0 | 零信息量：载体是注释文本而非声明 |
| `Lib/LinearAlgebra/RealSparseCodingCounterexamples.lean:472` | `softThresh_le_of_is_min` | 0 | 零边际信息：同一陈述的第二个名字 |
| `Runtime/ConstraintToLoss.lean:101` | `compile_changes_type` | 0 | 与同文件 :85 `compile_is_loss` 逐字同一陈述，证明 rfl——零新增信息。 |
| `Runtime/EndToEnd.lean:132` | `ladder_forward` | 0 | 只投影结构字段：证明体 = `L.l2l3_sound s hsat`；doc 的「does not collapse into a restatement of l2l3_sound」为假——它就是该字段。 |
| `Runtime/Extraction.lean:146` | `applies` | 0 | 非陈述：`stmt` = "lemma applies definitionally rather than needing a structure extensionality step..."（docstring 散文）。 |
| `Runtime/RatRepresentation.lean:121` | `compile_changes_type` | 0 | 与同文件 :113 `compile_apply` 逐字同一陈述，证明 rfl。 |
| `Runtime/VerifyLoopProgress.lean:104` | `repair_preserves` | 0 | `simpa [repair] using h` 展开后是 `ConstraintSat c x → ConstraintSat c x`（`fun h => h`）——只复述假设。 |
| `Runtime/WeightToSymbolEquivalence.lean:44` | `roundtrip_behavior` | 0 | 第一项展开 `extract`/`ConstraintSat`/`NeuronOut`（`ConvertLinear:52/62/67`）后两边是同一个表达式，`simpa using h` 即 `fun h => h`；第二项是 `convert_preserves_semantics`（`ConvertLinear:73`）的 `.mpr`。零新增信息。 |
| `Runtime/WeightToSymbolEquivalence.lean:72` | `extract_is_valid` | 0 | 展开后是 `∀ x, l.w * x + l.b = 0 ↔ l.w * x + l.b = 0`，证明 `rfl`——即 `P ↔ P`，零信息量。 |
| `Slots.lean:287` | `stated` | 0 | 非陈述：`stmt` 是 Slots 文档注释的散文段落。 |

## 二、`strengthen`：说的比该说的弱

| 位置 | 定理 | 入度 | 判定依据 |
|:--|:--|--:|:--|
| `Lib/Architectures/RealReLULayer.lean:80` | `ReLUSum_iff_all_constraints` | 1 | doc 声称给出「全部约束满足」的批量判定，但陈述里 as/bs 与 ls、x 没有任何结构联系，撑不起该用途 |
| `Lib/Chain/RealChainEntryOOV.lean:249` | `e2e_path_exists_str` | 1 | 陈述太弱：只要求 ∃ts 使 tokenizeStr s = some ts，没把 ts 与 Text.encode s 的关系写进结论；encode 被改成常函数 [] 时它仍为真（文件自身 :268 的 V01 实测）。撑不起文件头 Z04-G2 宣称的「入口桥闭合」。 |
| `Lib/Compiler/RealNonlinearCompile.lean:228` | `linearization_global_fails` | 1 | 陈述只断言存在 f 与恒零 L，未断言 L 是 f 的线性化/近似（无 ApproxOn、无任何编译函数出现），因此不构成对『线性化编译保全局语义』的反例；必须把近似关系写进陈述才能支撑 users（RealCompileExtractClosed）。 |
| `Lib/Editing/RealEditSemantics.lean:172` | `EditLayer_delta_not_unique` | 1 | 不足：结论 deltaOf Δ₁ x ≠ deltaOf Δ₂ x 与 EditLayer 合取项完全无关（Δ₁=⟨[1],0⟩、Δ₂=⟨[0],0⟩ 在任意 W 下都给出 1 ≠ 0）；因此它没有机器验证 doc 声称的「EditLayer_consequence 的 ∃ Δ 不能换成 ∀ Δ」。 |
| `Lib/Optim/RealSGDStochastic.lean:202` | `sgd_expected_gap_sum_seq` | 1 | 强度够（对唯一用户足够） |
| `Lib/Optim/RealStrongConvex.lean:130` | `strong_convex_gap_le_grad_sq` | 1 | 强度够（对唯一用户足够） |
| `Lib/Optim/RealStrongConvex.lean:168` | `strong_convex_contraction` | 1 | 强度够（对唯一用户足够） |
| `Domains/Geometry/FormDeriv.lean:142` | `derivExpr_ofLinearForm_ne_zero` | 0 | 强度不足:只在一个基点 w = 0 陈述 HasNonzeroDeriv;用处是支撑 Unconditional 的无条件版本,而那里 x = 0 是特殊点(evalPts = c.b),结论退化为常数项为零。 |
| `Domains/Geometry/LoopPerp.lean:47` | `fixPerp_absorbs` | 0 | 结论可以更强:目前把保守性限制在非退化参考段上,而证明并不需要这个限制。 |
| `Evidence/ChainTransitivity.lean:140` | `iterate_from_fold` | 0 | 强度不足：doc 说「两种形状等价：`foldl` 版本不更强，也不更弱」，但本条只把 `replicate n f` 的 fold 单向送到 `P`——既没给等式也没给反方向，「等价」无从谈起。 |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/A.lean:95` | `modalLogic_false_but_repairable` | 0 | 三合取仍真，但第三项 `extra.length = 5` 是超集大小：1 个已在模板表内（second_order_logic），实际缺口 4。若用途是「补名修复的缺口/成本」，强度不足。 |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/C.lean:85` | `probabilityTheory_false_but_repairable` | 0 | 三合取仍真，但第三项 `extra.length = 4` 是超集大小：2 个已在模板表内（axiom_of_choice, computational_complexity_theory），实际缺口 2。若用途是「补名修复的缺口/成本」，强度不足。 |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/C.lean:119` | `informationTheory_false_but_repairable` | 0 | 三合取仍真，但第三项 `extra.length = 12` 是超集大小：11 个已在模板表内（adversary_model, channel_model, channel_model_specification, channel_models, cryptographic_protocol, distortion_measure, network_topology, program_termination, received_signal, source_distr… |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/D.lean:87` | `projectiveGeometry_false_but_repairable` | 0 | 三合取仍真，但第三项 `extra.length = 11` 是超集大小：10 个已在模板表内（alternative_division_ring, bruck_ryser_chowla_theorem, combinatorial_design_theory, computational_search, coordinate_field_construction, desargues_theorem_failure, finite_field_theory, non_… |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/D.lean:120` | `orderTheory_false_but_repairable` | 0 | 三合取仍真，但第三项 `extra.length = 9` 是超集大小：5 个已在模板表内（convex_geometry, dilworth_theorem, partial_order, realizer, topological_sort），实际缺口 4。若用途是「补名修复的缺口/成本」，强度不足。 |
| `Lib/Editing/RealExtractionDirection.lean:449` | `extract_to_weights` | 0 | 不足。doc 声称「L1 → L2 → L3 语义串联（从 token 流直达权重层）」，但陈述里 `ts` 只出现在死前提 `_h : Extract ts cs` 中，结论完全不依赖 `ts`。 |
| `Lib/Optim/RealFedAvg.lean:208` | `fedAvg_rate` | 0 | 强度够（对唯一用户足够） |
| `Lib/Quantization/RealIEEE754/Basic.lean:173` | `ieee_relative_error_bound` | 0 | 强度够（对唯一用户足够） |
| `Runtime/ConvertVectorLinear.lean:154` | `convertVec_preserves_semantics` | 0 | 强度不足：用途是 L1→L2 的语义保持，但陈述建立在被截断的 `VectorConstraintSat` 上（`dot` = List.zip，静默截断到较短表）。`∀ x : List Int` 包含 \|x\| ≠ \|a\| 的 ragged 输入，那里满足性为真而语义上应为假——本仓 RealSymbolToWeightWidened.sat_ragged_false_positive 已经机器证明这一点，并指出本定理「两侧共享同一截断缺陷，因此永远抓不到它」。 |
| `Runtime/EndToEndApproximation.lean:155` | `loss_le_sq_of_resid_le` | 0 | 用途（Geo/ApproxEmbedding、Geo/PartialReinjection）要的是「残差界 ⟹ 惩罚/EpsSat 界」；现状给 loss ≤ ε²，但按 loss = resid² ≥ 0 能给的更强是 `EpsSat E p (ε^2) x`。 |
| `Runtime/GeoSampledBound.lean:72` | `residual_le_of_zero_on_dense_of_d` | 0 | 结论强度足够：`\|r x\| ≤ L*δ` 已是该假设下的精确形式（无 slack、无额外常数）。问题在前件一侧：多了一条没被用到的假设，使调用点平白多背一个义务。 |
| `Runtime/RealTokenSymbolLink.lean:306` | `decode_drops_trailing_partial` | 0 | A: 需要更强:把单点见证换成一般命题,否则 doc 的一般结论无机器依据 |
| `Runtime/StackCodegen.lean:194` | `compileProg_correct` | 0 | 结论已是最强：`runProg (compileProg e) [seed] = some (evalStack cfg e :: [seed])`，连 `seed` 被原样保留都证了。要动的是**前件**，不是结论。 |
| `Runtime/SymbolToWeightCorrectness.lean:65` | `symbolToWeight_correct` | 0 | 强度不足：名字声称 symbol→weight 的正确性，实际内容是「∀-map 分配（forall_mem_map_iff）+ 逐元素 rfl 级桥」，而且它认证的满足语义带有截断假阳性。本仓 RealSymbolToWeightWidened 已逐条给出消融：删掉逐元素桥则命题为假 ⟹ 「原定理的全部内容都集中在这个 rfl 桥上」；并给出 layer_ragged_also_zero 说明两侧共享缺陷、定理无诊断力。 |

## 三、`downgrade`：声称过强

（无）

## 四、`register`：已登记的债

| 位置 | 定理 | 入度 | 判定依据 |
|:--|:--|--:|:--|
| `Lib/Architectures/RealBlockConstants.lean:324` | `transformer_block_numeric` | 2 | 登记理由：定理本体可交付，但 doc 与 stmt 已不同步，且 doc 的「不可满足」结论对本条不成立。修法：把 B53/B60/B357 的历史段移入 CORRECTIONS，只保留与本陈述匹配的契约说明，再计入成果。 |
| `Lib/Attention/RealAttention.lean:69` | `sqrt_d_scale_bound` | 2 | 登记理由：装饰性前件 hd（唯一用处是一个未再使用的 hd'）。删掉它对调用方是净收益，属清理级。 |
| `Lib/Attention/RealSoftmaxLipschitz.lean:124` | `softmax_lipschitz_coord` | 2 | 登记理由：仅 hM 冗余（可从 hx 推出）。属清理级问题，不阻塞 BlockConstants 的常数使用。 |
| `Lib/Attention/RealTemporalLayer.lean:335` | `suspend_preserves_base` | 2 | 登记理由：rfl 级定义事实被当作法则级成果引用，且同文件已有一条逐字重复的定理。建议：要么删掉（下游写 rfl），要么保留但改 doc 为「定义即得」，并把法则 5 的承载放到真正的语义定理上。 |
| `Lib/Architectures/RealBlockConstants.lean:79` | `weight_l1_diff_bound` | 1 | 数学正确、常数可用；唯一问题是前件 hM' 可证可删，属清理项，登记。 |
| `Lib/Architectures/RealGatingGeneral.lean:40` | `softMasked_is_gated` | 1 | 纯投影/命名别名；因它是唯一的「激活类 ⊆ 门控类」入口，不宜直接删，登记为接口债务。 |
| `Lib/Architectures/RealLayerScale.lean:79` | `layerscale_lipschitz` | 1 | 结论与常数都正确，唯一缺陷是冗余前件 _hL，一行可删；登记清理。 |
| `Lib/Architectures/RealNormStability.lean:115` | `safe_normalize_lipschitz_on` | 1 | 常数推导正确；唯一问题是前件 _hR 冗余，登记清理。 |
| `Lib/Attention/RealTemporalLayer.lean:342` | `suspend_not_decomposition` | 1 | 同文件重复命名（:335/:342），下游 Ext:319 引用 :342。登记为重复命名债；删它会牵动 Ext 的「不是拆解」叙述，故先登记不删。 |
| `Lib/Attention/RealTemporalLayer.lean:354` | `suspend_idempotent` | 1 | 登记理由：零信息 rfl 被命名为法则级结论，下游可能据此论证「撤回不丢失结构」。建议降为定义别名注释，或改述 withGaze 的代数律。 |
| `Lib/Chain/Geometry.lean:54` | `collinear_preserves` | 1 | 被 Lift/RealContractAxioms:132 当作 C11 契约锚点。零信息量却承担「保语义」名义——正是本库的点名病症。登记 PROOF-DEBT：要么补编译层等式，要么把契约措辞降级。 |
| `Lib/Chain/RealGeometry.lean:44` | `collinearR_preserves` | 1 | 与 47 同型，被 RealContractAxioms:180 当作 C11' 契约锚点。登记同一条 PROOF-DEBT（与 47 合并处理）。 |
| `Lib/Chain/RealLv00AxiomDischargeClosure.lean:91` | `dependenciesClosed_mono` | 1 | 登记理由：同名同义的定理在 Lattice.Lv00.AxiomDischarge / AxiomPackages / AxiomDischargeJia 三个命名空间各有一份，且各自定义了自己的 AxiomPackageInstance / PackageDependenciesClosed；三处签名已漂移（`∀ n, n ∈ extra → …` vs `∀ n ∈ extra, …`）。这是「同一语义多处实现」的典型，登记待收敛。 |
| `Lib/Compiler/RealWhileTotalCorrectness.lean:215` | `triple_iff_wpT` | 1 | register：定义展开冒充定理。建议标为 @[simp] 展开引理或直接内联到 RealWPWhile；不要把它当作『Hoare 三元组与 wp 等价』的独立证据（真正的证据是 180/226/263）。 |
| `Lib/Editing/RealConversionCategorical.lean:150` | `compile_galoisConnection_galois` | 1 | 定理真且被真实使用（RealConversionCategoryNew.lean:298、333 作为 `GaloisConnection.toGaloisInsertion / toGaloisCoinsertion` 的输入），但 doc 的『须满射 / 等价于满射』是错误归因，正是本库『叙述强度 > 陈述强度』的老毛病。建议改 doc 为『像-原像对任意函数成伴随，故不携带编译信息』，并以 `GaloisInsertion`（真需要满射）为主交付；因不影响证明，登… |
| `Lib/Editing/RealEditSemantics.lean:1014` | `b194_counterexamples_intact_holds` | 1 | register（不是 delete，也不是 keep）。它不是「有名字 0 sorry 就算完成」的受害者——doc 明说自己是锚点；但它正是**该被排除在成果计数之外**的那一类：删掉这个名字不损失任何数学，保留它只为编译器回归。同族先例：`Audit/CompositionAlgebra.verdict_monoid`（纯合取打包）判 register。建议登记 PROOF-DEBT：「B194 锚点为回归设施，非数学结果」，并在 `RealChainAxioms… |
| `Lib/LearningTheory/RealConstrainedDecoding.lean:229` | `constrained_sum_one_via_realMaskFamily` | 1 | 本文件已有 constrainedSoftmax_sum_one；本条是同一命题的第二次证明，以并列定理身份进入 API 会让「本文件定理数」虚高，且两条日后可能漂移。保留「复用确认」的意图可以理解，但应按 alias 登记而非计入定理数。verdict=register。 |
| `Lib/LearningTheory/RealConstrainedDecodingVerify.lean:85` | `allowed_is_convex_weights` | 1 | 合取包不是数学内容，调用点写 `⟨nonneg, sum_one⟩` 等价。doc 自称「可复用的假设包」，但以定理身份计数会虚高。verdict=register：删除或标为 convenience alias。 |
| `Lib/LearningTheory/RealConstrainedDecodingVerify.lean:101` | `support_from_decoded_constraints` | 1 | 与 constrained_agrees_with_constraint_set 同义同型，属别名转发。若下游只要短名字，建议 `alias` 或 @[simp] 转发并注明来源，不应作为并列定理计数。verdict=register。 |
| `Lib/Lift/RealNonlinearFidelity_parts/B.lean:263` | `neg_zeroFixing_reluZ` | 1 | 为了 neg_zeroFixing_* 统一命名而转发可以理解，但作为独立定理它只是 B11 已有结论的改名。verdict=register：改为 alias/@[simp] 转发并在 doc 标 derived-from，不计入定理数。 |
| `Lib/Quantization/RealMixedPrecision.lean:104` | `fp16_underflow_dominated` | 1 | 定理为真，但证明机制与 doc 脱节：`_hu` 完全没进证明，结论对任意 x 都成立（只要 `eps·\|x\| ≤ tiny`），doc 却把它叙述成『下溢区』特有的界。登记 PROOF-DEBT：(i) 删 `_hu`，改名为通用绝对底界 `eps·\|x\| ≤ tiny → \|round x − x\| ≤ 2·tiny`，下游 `RealMixedPrecisionRounding:365` 同步改签名；(ii) 若要保留『下溢区』叙事，需补真正消费 `0… |
| `Lib/Quantization/RealMixedPrecision.lean:241` | `mixed_layer_error` | 1 | 清理级（C）：`_hX` 是死假设（n>0 时由 `hx` 推出，n=0 时结论平凡）。删掉后下游 `RealMixedPrecisionRounding:381` 同步即可。结论与证明一致，无误。 |
| `Core/RepairAtomicity.lean:89` | `atomic_of_binary` | 0 | 登记 PROOF-DEBT：这是「把假设写成定理」的样本。要么改成上面的真引理（从「非满足处测度非零」推出 atomic），要么删掉并把 Slots 的 note 降级为「atomic 仍是逐算子假设」。 |
| `Domains/Constraints/ConstraintSet.lean:128` | `holdsSet_mem` | 0 | `Semantics/Annotations.lean:118` 自己写着「`Domains/Constraints/ConstraintSet.holdsSet_mem` 是**同一条定理**，只差参数顺序」。**这是第四类重复（同陈述、不同证明），任何语法仪器都测不到**——声明式比较会因为参数重排而给出不同签名。**登记而非删除**：两条都已在用，删除会让 `Annotations` 的调用点断裂，而合并需要同时改两处签名。 |
| `Domains/Geometry/GeoSampledBound.lean:57` | `geo_sampled_bound` | 0 | 登记理由：真定理，但「验证回路最终形式」的标题超出陈述。修法有二：补有限采样版本（首选），或把 docstring 改成「若零点集在 rho 下 δ-稠密则误差 ≤ Lδ」并与文件头 §3 对齐。 |
| `Domains/Geometry/PartialReinjection.lean:88` | `loss_le_sq_of_resid_le` | 0 | 登记理由仅为前件冗余（C）。属清理级问题，不阻塞用途；建议顺手删 hε。 |
| `Domains/Geometry/RepairBridge.lean:74` | `converges` | 0 | 与 Core.Repair.progress 定义等价，属 API 别名；保留会增加「又一条收敛定理」的账面，建议合并（register 而非 delete，因为改名涉及 4-5 处调用点）。 |
| `Evidence/ChainTransitivity.lean:116` | `preserves_three` | 0 | 登记：要么把 doc 改成「三段显式形式（`preserves_two` 再套一次）」，要么补 `preserves_foldl P [f,g,h] _ x hx` 的对照等式。当前它属于「有名字、有 0 sorry、doc 里有结论」但结论未被陈述承载的典型，恰好是本库要治的那类。 |
| `Evidence/CompositionAlgebra.lean:182` | `verdict_monoid` | 0 | 登记：`verdict_monoid` 与 :174 的实例提供同一事实（实例更强），建议删除或在 doc 首句注明「仅为逐条核对索引，非独立成果」，否则审计计数会把 monoid 结构算两遍。 |
| `Evidence/CompositionAlgebra.lean:196` | `bridgedCount_hom` | 0 | 登记：要么注册 `MonoidHom`（成本极低，两条现成），要么把 doc 降为「`bridgedCount` 保持单位与乘法（两条独立定理）」。「同态」在本库是会被当成结构事实引用的词，不宜只落在合取上。 |
| `Evidence/Counterexamples.lean:85` | `lipschitz_needs_nonneg` | 0 | 登记（不是删）：反例本身正确，`lipschitz_needs_nonneg` 这个名字也诚实；问题是它被 `Audit/Hypotheses:133` 当作 `0 ≤ L` 的承重证据引用，而它并未触及 `residual_le_of_zero_on_dense` 的推导。要么补上真正的那一步（乘法单调性的前提必要性），要么把 Hypotheses 那行的证据换成散文并注明「未机器核对」。同文件 :60/:70 两条是真反例（`r² ≤ ε²` 与 `EpsSat` … |
| `Evidence/DecreasesRole.lean:144` | `decreases_role` | 0 | 登记：删掉第二合取项（它就是 `hstep`），只留 `decreases_of_one_step`；若想强调「一步收敛 + 原子 ⟹ decreases 且已收敛」，应把它写成 `Repair` 结构上的实例（`hstep` 换成一个真实的收敛字段并证明），而不是把假设重列一遍。 |
| `Evidence/Hypotheses.lean:167` | `every_judgement_carries_a_reason` | 0 | 登记：doc 的「类型保证」不成立（`loadBearing`/`structurallyRequired` 带 `String` 是真的，但「没有第三构造子出现」只能查表）。改 doc，或把 `redundant` 从数据里去掉、改成单独的待办清单，这样这条才真的变成类型事实。 |
| `Evidence/StructureCensus.lean:150` | `total_obligations` | 0 | 登记：与 :141/:144/:156 同一处理——这组 `decide` 是清单纪律，不是「义务总数」的定理。若要当审计结果，doc 必须写清「入表 5 个结构」，否则读者会把它当成全库统计（而 `Representation` 那行已有字段数错误，说明表并未随代码维护）。 |
| `Evidence/VerdictLattice.lean:211` | `lattice_holds_per_segment_not_per_sequence` | 0 | 登记：作为文件结论的汇总条可以留，但应标注它是索引（`:149` 与 `:177` 的合取），不要与 `kind_is_bounded_lattice` 并列计为两条成果；doc 的「两条定理」改成三条。 |
| `Lib/Architectures/RealOperatorNorm.lean:47` | `comp_norm_bound` | 0 | Re-export 债务：不影响正确性但虚增定理数；与同文件 add_norm_bound（建议删）一并治理。 |
| `Lib/Attention/RealTemporalLayer.lean:243` | `split_exposes_parts_to_upward_gaze` | 0 | 同文件同陈述两个名字（:203 / :243），下游按 :243 引用。登记为重复命名债，合并时改调用点；不直接删是因为 Ext 的叙述依赖此名。 |
| `Lib/Chain/RealChainAxioms3.lean:148` | `b194_anchor_consumer` | 0 | doc 自认「不证明任何新数学——它把锚点取用一次」，作用只是编译期依赖锚点（防整节被删），且拦不住两处同删。作为「定理」零内容；登记 PROOF-DEBT，建议与 _holds 合并或换成真正的消费证明。 |
| `Lib/Chain/RealLv00AxiomDischargeClosure.lean:104` | `dependenciesClosed_of_subset` | 0 | 登记理由同 :91：与 RealLv00AxiomPackages:240 及 RealN2AxiomDischargeJia:786 是平行实现的三份副本之一，应统一或补桥。 |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:88` | `computabilityTheory_templateNames_length` | 0 | 【实测，锚点为假】`in_degree` 指向 `RealN2AxiomDischargeJia.lean` 的同名副本，但该文件不 import 本文件，只自行重声明同名定理（`Lattice...Jia` 命名空间），数一致（55）但仍是两份数据源。12 个包里 6 个分叉（modal 27/28、graph 70/71、probability 87/89、information 106/117、projective 38/48、order 32/37）；本条不在分… |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:129` | `modalLogic_templateNames_length` | 0 | 【实测，锚点为假 + 数值分叉】`in_degree` 指向 Jia 同名副本（不 import 本文件，只自行重声明）；本文件 28、Jia 27（本文件多 1 个 EXEC-Y1 外名）。def 上方的 docstring 仍写「上游 27 条」，与定理值 28 及 Jia 的 27 三者不一致。登记：doc 改为「27 上游 + 1 注入」，并补分解/对齐断言或删除一侧副本。 |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:174` | `zfcSetTheory_templateNames_length` | 0 | 【实测，锚点为假】`in_degree` 指向 `RealN2AxiomDischargeJia.lean` 的同名副本，但该文件不 import 本文件，只自行重声明同名定理（`Lattice...Jia` 命名空间），数一致（29）但仍是两份数据源。12 个包里 6 个分叉（modal 27/28、graph 70/71、probability 87/89、information 106/117、projective 38/48、order 32/37）；本条不在分… |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:240` | `graphTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数值分叉】`in_degree` 指向 Jia 同名副本（不 import 本文件，只自行重声明）；本文件 71、Jia 70（本文件多 1 个 EXEC-Y1 外名）。def 上方的 docstring 仍写「上游 70 条」，与定理值 71 及 Jia 的 70 三者不一致。登记：doc 改为「70 上游 + 1 注入」，并补分解/对齐断言或删除一侧副本。 |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:292` | `measureTheory_templateNames_length` | 0 | 【实测，锚点为假】`in_degree` 指向 `RealN2AxiomDischargeJia.lean` 的同名副本，但该文件不 import 本文件，只自行重声明同名定理（`Lattice...Jia` 命名空间），数一致（66）但仍是两份数据源。12 个包里 6 个分叉（modal 27/28、graph 70/71、probability 87/89、information 106/117、projective 38/48、order 32/37）；本条不在分… |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:333` | `functionalAnalysis_templateNames_length` | 0 | 【实测，锚点为假】`in_degree` 指向 `RealN2AxiomDischargeJia.lean` 的同名副本，但该文件不 import 本文件，只自行重声明同名定理（`Lattice...Jia` 命名空间），数一致（37）但仍是两份数据源。12 个包里 6 个分叉（modal 27/28、graph 70/71、probability 87/89、information 106/117、projective 38/48、order 32/37）；本条不在分… |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:392` | `probabilityTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数值分叉】`in_degree` 指向 Jia 同名副本（不 import 本文件，只自行重声明）；本文件 89、Jia 87（本文件多 2 个 EXEC-Y1 外名）。def 上方的 docstring 仍写「上游 87 条」，与定理值 89 及 Jia 的 87 三者不一致。登记：doc 改为「87 上游 + 2 注入」，并补分解/对齐断言或删除一侧副本。 |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:465` | `informationTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数值分叉】`in_degree` 指向 Jia 同名副本（不 import 本文件，只自行重声明）；本文件 117、Jia 106（本文件多 11 个 EXEC-Y1 外名）。def 上方的 docstring 仍写「上游 106 条」，与定理值 117 及 Jia 的 106 三者不一致。登记：doc 改为「106 上游 + 11 注入」，并补分解/对齐断言或删除一侧副本。 |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:521` | `linearAlgebra_templateNames_length` | 0 | 【实测，锚点为假】`in_degree` 指向 `RealN2AxiomDischargeJia.lean` 的同名副本，但该文件不 import 本文件，只自行重声明同名定理（`Lattice...Jia` 命名空间），数一致（90）但仍是两份数据源。12 个包里 6 个分叉（modal 27/28、graph 70/71、probability 87/89、information 106/117、projective 38/48、order 32/37）；本条不在分… |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:574` | `projectiveGeometry_templateNames_length` | 0 | 【实测，锚点为假 + 数值分叉】`in_degree` 指向 Jia 同名副本（不 import 本文件，只自行重声明）；本文件 48、Jia 38（本文件多 10 个 EXEC-Y1 外名）。def 上方的 docstring 仍写「上游 38 条」，与定理值 48 及 Jia 的 38 三者不一致。登记：doc 改为「38 上游 + 10 注入」，并补分解/对齐断言或删除一侧副本。 |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:622` | `orderTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数值分叉】`in_degree` 指向 Jia 同名副本（不 import 本文件，只自行重声明）；本文件 37、Jia 32（本文件多 5 个 EXEC-Y1 外名）。def 上方的 docstring 仍写「上游 32 条」，与定理值 37 及 Jia 的 32 三者不一致。登记：doc 改为「32 上游 + 5 注入」，并补分解/对齐断言或删除一侧副本。 |
| `Lib/Chain/RealLv00AxiomDischargeInstances.lean:667` | `affineGeometry_templateNames_length` | 0 | 【实测，锚点为假】`in_degree` 指向 `RealN2AxiomDischargeJia.lean` 的同名副本，但该文件不 import 本文件，只自行重声明同名定理（`Lattice...Jia` 命名空间），数一致（56）但仍是两份数据源。12 个包里 6 个分叉（modal 27/28、graph 70/71、probability 87/89、information 106/117、projective 38/48、order 32/37）；本条不在分… |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/A.lean:76` | `modalLogic_extra_length` | 0 | 【实测】本侧（Instances/PerPackage）的 `modalLogicTemplateNames` 已由 EXEC-Y1 追加外名，`modalLogicExtra` 没同步清理，1/5 个 extra 名已在模板表内；实际缺口 = classical_propositional_logic, modal_logic, modal_satisfiability_K, modal_satisfiability_S4（4 名）。`in_degree` 指向 Ji… |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/B.lean:65` | `graphTheory_extra_length` | 0 | 【实测】本侧（Instances/PerPackage）的 graphTheory 模板表已含 `three_colorability`（71），故 `graphTheoryExtra` 是 100% 冗余；Jia 侧（70 模板）里 extra 才等于缺失集，那里 keep 是对的。本条是「数据已补、extra 未清」的残迹；登记，不要当成「graph_theory 需要额外名才闭合」的证据。 |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/B.lean:91` | `graphTheory_orig_true` | 0 | 【实测，锚点即分叉】本批最危险的一条：同一 `graphTheoryPackage` 名在 `Lattice...AxiomDischargeJia`（70 模板）被 `not_graphTheory_orig` 证为假，在 `Lattice...AxiomDischarge`（71 模板）被本条证为真；两条都 0 sorry。`in_degree=1` 指向的正是那个旧副本，等于把分叉当引用。登记：按数据版本重命名/合并，并在`all_twelve_discharge… |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/C.lean:66` | `probabilityTheory_extra_length` | 0 | 【实测】本侧（Instances/PerPackage）的 `probabilityTheoryTemplateNames` 已由 EXEC-Y1 追加外名，`probabilityTheoryExtra` 没同步清理，2/4 个 extra 名已在模板表内；实际缺口 = measure_theory, zfc_set_theory（2 名）。`in_degree` 指向 Jia 副本，那里无 padding、extra 恰为缺失集，所以那条能 keep；本条不能照搬。… |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/C.lean:100` | `informationTheory_extra_length` | 0 | 【实测】本侧（Instances/PerPackage）的 `informationTheoryTemplateNames` 已由 EXEC-Y1 追加外名，`informationTheoryExtra` 没同步清理，11/12 个 extra 名已在模板表内；实际缺口 = universal_turing_machine（1 名）。`in_degree` 指向 Jia 副本，那里无 padding、extra 恰为缺失集，所以那条能 keep；本条不能照搬。登记数据… |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/D.lean:68` | `projectiveGeometry_extra_length` | 0 | 【实测】本侧（Instances/PerPackage）的 `projectiveGeometryTemplateNames` 已由 EXEC-Y1 追加外名，`projectiveGeometryExtra` 没同步清理，10/11 个 extra 名已在模板表内；实际缺口 = field_theory（1 名）。`in_degree` 指向 Jia 副本，那里无 padding、extra 恰为缺失集，所以那条能 keep；本条不能照搬。登记数据/文档债：重算 ex… |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/D.lean:101` | `orderTheory_extra_length` | 0 | 【实测】本侧（Instances/PerPackage）的 `orderTheoryTemplateNames` 已由 EXEC-Y1 追加外名，`orderTheoryExtra` 没同步清理，5/9 个 extra 名已在模板表内；实际缺口 = graph_isomorphism, group_theory, poset_dimension, zfc_set_theory（4 名）。`in_degree` 指向 Jia 副本，那里无 padding、extra 恰为… |
| `Lib/Chain/RealLv00AxiomDischargeSummary.lean:33` | `all_twelve_discharged` | 0 | 【实测，双向分叉】本条是 post-EXEC-Y1 版（graph 真），Jia:1236 是 pre-EXEC-Y1 版（graph 假）；同名、相反陈述、都 0 sorry，且各自 `#print axioms` 都干净。`in_degree` 指向 Jia 副本。登记：删一侧或按数据版本改名；在合并前，任何「12/12 discharged」的引用都必须写明是哪一版。 |
| `Lib/Chain/RealLv00Solver.lean:707` | `lcm_assoc` | 0 | 【实测，锚点为假】`RealDvdLatticeStratification.lean` 只 `import Mathlib`，其中 `lcm_assoc` 仅出现在注释（:107），且该文件用 `Nat.dvd_antisymm` **自己重证**了 `nat_sup_assoc`（:109–126），还错误宣称「mathlib 的 `Nat` 上无现成 `lcm_assoc`」——本条正是 `Nat.lcm_assoc` 的逐字包装。⇒ in_degree=1 是注… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:181` | `computabilityTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件与副本同为 55（数一致，但仍是两份数据源）。12 个包里 6 个分叉（modalLogic 27/28、graphTheory 70/71、probabi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:219` | `modalLogic_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件 27 / 副本 28（副本另有 padding 名，见其 `EXEC-Y1-EXTERNAL-30` 注释）。12 个包里 6 个分叉（modalLogi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:264` | `zfcSetTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件与副本同为 29（数一致，但仍是两份数据源）。12 个包里 6 个分叉（modalLogic 27/28、graphTheory 70/71、probabi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:327` | `graphTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件 70 / 副本 71（副本另有 padding 名，见其 `EXEC-Y1-EXTERNAL-30` 注释）。12 个包里 6 个分叉（modalLogi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:379` | `measureTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件与副本同为 66（数一致，但仍是两份数据源）。12 个包里 6 个分叉（modalLogic 27/28、graphTheory 70/71、probabi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:420` | `functionalAnalysis_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件与副本同为 37（数一致，但仍是两份数据源）。12 个包里 6 个分叉（modalLogic 27/28、graphTheory 70/71、probabi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:475` | `probabilityTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件 87 / 副本 89（副本另有 padding 名，见其 `EXEC-Y1-EXTERNAL-30` 注释）。12 个包里 6 个分叉（modalLogi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:535` | `informationTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件 106 / 副本 117（副本另有 padding 名，见其 `EXEC-Y1-EXTERNAL-30` 注释）。12 个包里 6 个分叉（modalLo… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:591` | `linearAlgebra_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件与副本同为 90（数一致，但仍是两份数据源）。12 个包里 6 个分叉（modalLogic 27/28、graphTheory 70/71、probabi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:632` | `projectiveGeometry_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件 38 / 副本 48（副本另有 padding 名，见其 `EXEC-Y1-EXTERNAL-30` 注释）。12 个包里 6 个分叉（modalLogi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:673` | `orderTheory_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件 32 / 副本 37（副本另有 padding 名，见其 `EXEC-Y1-EXTERNAL-30` 注释）。12 个包里 6 个分叉（modalLogi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:718` | `affineGeometry_templateNames_length` | 0 | 【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：本文件与副本同为 56（数一致，但仍是两份数据源）。12 个包里 6 个分叉（modalLogic 27/28、graphTheory 70/71、probabi… |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:757` | `packageDependenciesValidB_iff` | 0 | 登记为「复制-分叉模块」债务：Jia 文件是 Closure 的 fork（同名字段、同名谓词、同名定理），两条桥与两份结构必须一起收敛；现在改任一侧都会静默失配。 |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:762` | `packageDependenciesClosedB_iff` | 0 | 同 #57 的 fork 债务（含 extra 版本）。 |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:773` | `dependenciesClosed_mono` | 0 | 登记理由：这是同一语义的第三套独立实现（自带结构定义 + 自带谓词），三处结论无法在 Lean 内互相引用/校验，是本库「平行重写」的典型。登记待收敛，不作为新成果。 |
| `Lib/Chain/RealN2AxiomDischargeJia.lean:786` | `dependenciesClosed_of_subset` | 0 | 登记理由同 :773：三份平行实现之一（自带结构、无 import），建议收敛到规范实现或补等价桥后再作为成果引用。 |
| `Lib/Compiler/RealCompileFloatCorrectness.lean:471` | `compile_error_bound` | 0 | register：hMul 等于把 mul 分支的目标原样作为前提（自指式降级），且 hcontract 可从 eps/tiny 非负内部推出。登记 PROOF-DEBT：补 mul_error_bound 并删去 hMul/hcontract；在此之前任何把本条当『全语言浮点正确性』的引用都过强。 |
| `Lib/Compiler/RealLv00CompilerSpec.lean:119` | `compile_constraint_degenerately_satisfied` | 0 | register：doc 已诚实标 (B/空洞)，但下游 RealLv00CompilerSat 仍可能把它当编译正确性引用。登记 PROOF-DEBT：补任意 env 的 sound/complete，退化版降为示例。 |
| `Lib/Compiler/RealLv00CompilerSpec.lean:311` | `compile_bridge_sem` | 0 | register：与 119 条同一债务。名字 compile_bridge_sem 容易让下游误以为完成了编译语义桥接，实际只是退化模型特化；登记 PROOF-DEBT 并考虑改名。 |
| `Lib/Editing/RealCanonicalForm.lean:642` | `canonicalize_injective_on_quotient_boundary` | 0 | 数学上没问题（本库少见的真否定结论），问题只在名字与 doc 首句『性质③（商上单射）』同陈述（全称否定）不一致。建议改名 `canonicalize_not_constant_on_scaleClass`；改名会波及 RealExtractDecidability.lean:557 的文档引用，故登记而非现在改。 |
| `Lib/Editing/RealEditInvariantCatalog.lean:185` | `dot_append_sub` | 0 | 库内同陈述两处具名（本文件 :185 与 RealConstraintEdit:236）。doc 已登记为已知重复，风险是将来一处改动另一处漂移、下游按命名空间挑到哪条不确定。建议登记 PROOF-DEBT：删本副本改直接引用；现在不值得为它改动引理链。 |
| `Lib/Editing/RealEditInvariantCatalog.lean:221` | `dot_append_of_length_eq` | 0 | 与 Lib/Editing/RealSymbolToWeightWidened.lean:304 同名同义重复；两文件互不 import，文件内也没有证明使用（in_degree=1 是同名声明碰撞而非语义引用）。doc 把它当「承重件」，实际是死件 + 双副本：登记 PROOF-DEBT，建议收敛为一份并接上消费者。 |
| `Lib/Editing/RealExtractNonInjective.lean:137` | `convertVec_injective` | 0 | 同一声明在库内至少三份（另见 RealEditToSymbol:122、RealReversibilityBoundary:85）。doc 已诚实标注为「本文件内导出」，但正是这种自包含再导出在积累漂移面。建议登记 PROOF-DEBT：统一引用一处；当前不影响正确性。 |
| `Lib/Editing/RealExtractSurjectivity.lean:369` | `extractVec_convertVec_rfl` | 0 | 与 RealCanonicalCompileComm:148 的同名定理（那里是真 `rfl`）构成两处同义声明，均由 Meta/RealRflAudit 消费。作为审计证据可以留，但应在 Meta 层只引一处。登记 PROOF-DEBT，现值不值得改。 |
| `Lib/Editing/RealExtractionDirection.lean:162` | `extract_sound` | 0 | 读的是 L162-165 与 `Lib/Chain/RealEndToEnd.lean:252` 的调用点。**`Extract ts cs` 的定义就是`some ((toSegs ts).map mkConstraint) = some cs`**，所以这条定理是**定义的投影**——它诚实（`extract_sound` 这个名字说的正是这件事），但它不新增数学。登记而非删除：`RealEndToEnd` 的端到端合取需要它作为一个具名条款。 |
| `Lib/Editing/RealRoundTripVacuity.lean:347` | `rt2_leftInverse` | 0 | 零新增内容的纯别名，仅作为「实例 2」的标签在 RealRoundTripVacuity:354/363 使用；不影响正确性，登记 PROOF-DEBT（合并或直接引用），不值得现在动。 |
| `Lib/Editing/RealSymbolCompleteness.lean:428` | `s02_twoAxisLayer_needs_two` | 0 | 定理本身真且三个合取项都被用到，但 doc 把它读成一般计数结论（n 个神经元 ⟹ n 条约束），实际只有 2 轴实例；且无证明级消费者（唯一引用是 Meta 文件的注释）。登记覆盖债。 |
| `Lib/Editing/RealSymbolToWeightWidened.lean:304` | `dot_append_of_length_eq` | 0 | 与 Lib/Editing/RealEditInvariantCatalog.lean:221 同名同义重复（两文件互不 import）；本文件内该名只出现在 doc 里，in_degree=1 是同名声明碰撞。doc 称「主定理」，实际无消费者，登记重复/死件债。 |
| `Lib/LearningTheory/RealDecisionTheory.lean:88` | `admissible_iff_not_dominated` | 0 | doc 自陈是定义改写、为下游保留两种语言。作为命名桥可以存在，但它是 0 信息量条目，若计入定理数就是虚高。verdict=register：改为 `abbrev`/@[simp] 转发，或在 doc 标注 alias。 |
| `Lib/Linear/PenaltyPerturb.lean:274` | `localMin_of_feasible` | 0 | 全仓唯一无引用者:本文件内没有使用,grep 全仓只有定义行(274)。in_degree=3 完全由另外三个同名定理(Penalty:87、PenaltyMatrix:230、PenaltyPerturbN:187)造成,不是用途。内容又是 PenaltyPerturbN 一般 n 版在 n=2 的特例——本文件 doc 自己说 localMin_iff_feasible 已从一般版导出。建议登记死代码/重复:或删掉,或改写成从 n 版经 loss2=lossN / … |
| `Lib/LinearAlgebra/RealGelfand.lean:390` | `gelfand_radius_le_opNorm_general` | 0 | doc 自陈「具名重申」。它与 :224 是同一命题的两条记录，#print axioms / 定理计数都会重复，且未来改一条会忘另一条。verdict=register：合并（删本条，在 :224 的 doc 里加检索关键词）。 |
| `Lib/Optim/RealSeamBridges2.lean:354` | `bmean_eq_batchMean` | 0 | 与 RealSeamBridges.lean:78 **同名、同陈述、同为 `rfl`** 的第二份声明（本文件未 import 前者，故不能复用而只能复写）。但两者都被 Lib/Optim.lean:51-52 汇聚导入，`Lattice.bmean_eq_batchMean` 在同一环境里因此有两份声明——下游一旦按名引用即报歧义，是一枚潜在炸弹。另外本条 `users` 填的是 RealSeamBridges.lean，即被复写的那份文件的所在处：两份副本互为对方… |
| `Lib/Optim/RealSeamBridges2.lean:365` | `bmean_eq_mean` | 0 | 与 RealSeamBridges.lean:75 **同名、同陈述、同为 `rfl`** 的第二份 `bmean_eq_mean`；同样被 Lib/Optim.lean:51-52 汇聚导入，构成同名双声明，且 `users` 指向的正是被复写的 RealSeamBridges.lean（两份副本互为「用户」，in_degree 非独立使用）。建议删除本副本并 import RealSeamBridges（或改名）。登记 PROOF-DEBT。 |
| `Lib/Penalty/PolyExact.lean:79` | `hasFDerivAt_sq` | 0 | `Lattice.hasFDerivAt_sq` 与 `Lattice.Lift.hasFDerivAt_sq`（Lift/PenaltyAnalysis.lean:45）**陈述逐字相同**，证明体只调用后者——本条不引入任何新数学，是缩短命名空间的再导出。另注意：本条 `users` 指向 Lift/PenaltyAnalysis.lean，而该文件正是被转发的**下层原件**，不可能反向依赖本文件，这条引用是命名比对产物而非真实使用。建议改为 `export`/别… |
| `Lib/Quantization/RealIEEE754/Overflow.lean:101` | `clampTo_eq_self` | 0 | 清理级（C）：`_hM` 是死假设，且由 `hx : \|x\| ≤ M` 可推出。删掉后签名变 `(hx : \|x\| ≤ M)`，证明不变；下游 `RealMixedPrecisionRounding:298` 可少传 `(by norm_num)`。若为与 `clampTo_abs_le` 的 API 对齐而保留，应在 doc 里说明这是形状统一而非数学必需。 |
| `Lib/Quantization/RealStructuredPruning.lean:323` | `head_pruning_bound` | 0 | 同名不同义 + 无真实消费者：`Lib/Attention/RealHeadPruningOptimal.lean:141` 有自己的 `head_pruning_bound`（加权输出误差 ≤ M·prunedMass），该文件并不 import 本文件（其 :50 自陈『未与本文件的最优性对接』）⇒ batch 的 in_degree=1 是同名假匹配；全仓对这条声明没有任何引用，只有 `Quantization.lean` 对本文件的聚合 import。定理本身是… |
| `Runtime/EndToEnd.lean:60` | `decode_encode` | 0 | doc 本身是诚实的（"named lemma so that downstream can cite it by name"），故不删；但必须登记：L0⇄L1 这一跳是 assume 的，唯一见证是 identity（rfl）。下游 RealChainAxioms2 / RealEndToEnd 不得据此称「分词无损已证」。 |

## 已处理（修好的条目**保留**在这里，不删）

**为什么保留**：一个只会增长的债单没人信；而修好的条目悄悄消失更糟——
读者分不清「修好了」与「把发现删掉了」。

| 位置 | 定理 | 做了什么 |
|:--|:--|:--|
| `Lift/ConvertVectorLinear.lean` | `convertVec_preserves_semantics` | strengthen → 分两部分处理。(1) docstring 补上两条警告：它是定义展开（`convertVec` 只拷贝系数与偏置）、且两侧共享 `dot` 的 `List.zip` 截断，对元数错误零诊断力。(2) 新增否定定理 `convertVec_preserves_semantics_blind_to_arity`：`{a:=[3,5],b:=0}` 配 `x:=[]` 时两侧同时成立，故该等价永远抓不到这类错误。**P 侧（把 `dot` 接到真正的线性型）没做**——我试了加元数前提，Lean 报 `unused variable h`，说明「加前提」在这里是假的加强；真加强需要一条 `zip`/`foldl` 的桥，未做且已在文件里写明。 |
| `Lift/SymbolToWeightCorrectness.lean` | `symbolToWeight_correct` | strengthen → 同上的第二层。docstring 写明它的强度**完全继承**自 `convertVec_preserves_semantics`：结构上它经 `forall_mem_map_iff` 逐点提升（真定理，非重言），但内容不超出被提升的那条。新增 `symbolToWeight_correct_blind_to_arity` 把盲区变成同一层的否定定理。 |
| `(8 处，见本条)` | `delete × 8` | 对抗性复核确认无信息量且无依赖，已删除并逐一通过全库构建：`ChainTransitivity.preserves_one`（陈述就是 binder 的类型）、`CompositionClass.sequential_evidence_trivial`（陈述是常值 True，被同文件 `evidence_kinds_differ` 更强覆盖）、`CompositionClass.bridged_needs_bridge`（与 `BridgedComposition.bridge_is_necessary` 逐字相同）、`MultiComposition.chain_nil_identity`（展开即 `hx`）、`RealCanonicalCompileComm.comm_via_extract`（条件恒真）、`RealExtractSurjectivity.extractVec_range_ne_proper`（与紧邻上一条逻辑等价）、`ConstraintToLoss.compile_changes_type` 与 `RatRepresentation.compile_changes_type`（各与同文件前 8–16 行的另一份逐字同陈述同 `rfl` 证明，删的是后一份副本）。 |
| `Lift/WeightToSymbolEquivalence.lean` | `roundtrip_behavior` | 删掉了合取的第一项，那一项是 `h → h`（`NeuronOut l x = 0` 与 `ConstraintSat (extract l) x` 按定义相同，`simpa using h` 就是 `id`）。名字保留，因为 `Lib/Lift/RealContractAxioms.lean` 有 `#print axioms roundtrip_behavior`——改断言会断构建。并给本模块三条定理加上诚实 docstring：它们的往返恒等**是定义展开**（`rfl` / `simp [ConstraintSat, NeuronOut, convert]`），**没有建立任何对应关系**。 |
| `Lib/Chain/RealTaylorMultivariate.lean` | `second_order_taylor` | 判定从 `rewrite` **改为 `register`**：`∃ R, a = b + R` 与 `True` 同义（证明体把 `R` 取成 `a − b`），**当前假设下写不出更强的陈述**。要让它有内容必须把余项界 `\|R\| ≤ (C/2)‖v‖²` 并进结论，那需要 `n` 维 Taylor 余项定理（本文件正是用 `hg2`/`hC` 回避了它）。已把这段写进源码 docstring，明确「结论空洞，全部内容在假设里」，并指出 `second_order_taylor_unconditional` 的价值在于弱化假设（`hg2` → `ContDiffAt ℝ 2 f x`）而非让结论有内容。 |
| `Evidence/VerdictLattice.lean` | `kind_is_bounded_lattice` | 强化：名字说「有界格」，而原合取里**没有反对称性、没有下确界的泛性质**——所以它证的是「带上下界的并半格」。补上两项。**注意**：这两条的**定理早就存在**（`kindLe_antisymm`、`kindInf_le_left`/`kindInf_le_right`/`kindLe_inf`），只是**没被并进这个合取**——缺陷不在证明，在**陈述漏了它自己名字要求的项**。 |
| `Geo/LoopPerp.lean` | `fixPerp_absorbs` | 强化：**删掉了前提** `(∑ j, (pts e j − pts c j)²) ≠ 0`。它**从未被用到**——证明体走 `rw [hzero, zero_div, zero_mul, sub_zero]`，而 `zero_div` 对**任何**除数成立（`0/0 = 0` 是 Lean 的总函数约定）。删掉后定理**更强**：它现在对退化参考段（`e = c`）也成立。两处调用点（`LoopPerp` 内两处、`Geo/ConjRepair.lean` 一处）同步更新。**这是「说的比该说的弱」的正确修法：不是加结论，是减前提。** |
| `Evidence/StructureCensus.lean` | `repair_is_densest` | 强化：名字说「`Repair` 是义务密度最高的结构」，而原陈述是 `(census.filter (fun s => s.obligations * 2 ≥ s.fields)).length = 1`——**全文没有一个字符提到 `Repair`**，换掉清册里一项它可能仍为真。现在陈述**直接点名且全称**：除 `Repair` 外每个结构密度严格 < 1/2，且 `Repair` 在册且密度 ≥ 1/2。两项合起来才等于「唯一」。 |
| `Lib/LearningTheory/RealTopK.lean` | `top1_output_is_hard` | 强化：原陈述在**单元素集** `{i}` 上求和，所以 `_hrest`（其余权重为 0）**必然用不到**；结论退化成 `w i • v i = v i`，即 `1 • v i = v i`，**与「硬路由」无关**。现在求和范围是 `Finset.univ`，`hrest` 成为**必需**：和之所以塌缩成一项，正是因为其余权重为零。**这才是硬路由的定义。** |
| `Lib/Attention/RealDynamicRoute.lean` | `routeOutput_hard` | 强化：**与 `top1_output_is_hard` 同一个缺陷的下游副本**——路由集取 `{i}`，`hrest` 无从使用，结论退化。现在路由集是 `Finset.univ`。**同款缺陷成对存在**——与 `stackDepth`/`depth`、`CExprCodegen`/`StackCodegen` 是同一种形态，本轮一次收两个。 |
| `Lib/LearningTheory/RealConstrainedDecoding.lean` | `constrained_agrees_with_constraint_set` | 判定从 `strengthen` **改为 `downgrade`**：原陈述带前提 `(_hts : DecodesTo ts cs)`，而 `allowedByConstraints cs tok` **是 `cs` 与 `tok` 的函数、不含 `ts`**，所以 `_hts` 从未被用到——这条定理对**任何掩码**成立，`cs`、`ts` 都是装饰。**它没有建立「符号约束决定采样支撑」。**那个连接是 `allowedByConstraints` 的**定义**携带的，而「`cs` 非空」这一半由**调用方**以 `hne` 提供，**`DecodesTo` 给不出来**（非空性是 `tok` 的性质）。同一错误在消费方 `RealConstrainedDecodingVerify.support_from_decoded_constraints` 重复：其文档声称「使下游模块只需给出『解码成功』这一事实」，**而下游还必须自己给 `hne`**。两处陈述已收窄，前提已删。 |
| `Lib/InfoTheory/RealCrossEntropy.lean` | `ce_onehot_eq_neg_log` | 强化：删掉了前提 `(_hq : 0 < q y)`。本文件的 docstring **早就写着**它是「log 定义域标注（mathlib 的 log 是全函数，证明并不需要）」——**承认了却留着，就是「说得比该说的弱」**。3 个调用点已同步（`RealKL` 两处、`RealContrastive` 一处）。 |
| `Lib/Optim/RealStrongConvex.lean` | `strong_convex_iterate_contraction` | 删前提 `(_hμL : μ ≤ L)`，**并更正了一条错误的「诚实边界」注解**。原注称该前提「被下划线标记为未使用，但**保留它是正确的**」。**那句话是错的**：证明里 `h1` 只用共强制性，`h2` 是纯代数恒等式（`field_simp` + `ring`），**没有任何一步需要 `μ ≤ L`**。删掉后**命题仍为真**，只是 `μ > L` 时系数 `((L−μ)/(L+μ))²` 不再 `≤ 1`。`_of_sc` 保留 `μ ≤ L` 是**为了「收缩」这个解读**，不是为了命题的真假——**两种理由必须分开写，把「为了解读」说成「为了真假」正是原注的错误。** |
| `Lib/LearningTheory/RealDistillGeneralization.lean` | `distill_excess_from_layer` | 删除了前提 `hc : 0 ≤ c` 与 `hB0 : 0 ≤ B`（以及上游 `distill_excess_from_chain_lipschitz` 的同名两条）。本文件此前写的是「Lean 报过 unused，但它们位于 `linarith` 上下文中，**删除有回归风险** ⟹ 保留并标注」，并在另一处明写「**未做删除实验**」。**第 225 轮补做了这个实验**：全库构建通过，两个定理严格变强。**「存在回归风险」是顾虑，不是证据**——同一节上面那 9 条同样是 `linarith` 上下文里的装饰性前提，同样被删成功了。 |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_sound` | 判定从 `strengthen` **改为 `register`**：它的两个前提`h0 : tokenize s = some ts`、`h1 : Extract (L1Bridge ts) cs` 在**证明体**里不被用（证明就是 `symbolToWeight_correct cs x`），**但它们在陈述的类型里承重**：没有 `h1`，`cs` 就没有来源，定理会对**任意**约束集成立——那是另一个定理（`symbolToWeight_correct`），不是这一个。**所以它们不可删，也不可变承重**（`symbolToWeight_correct` 确实不需要它们）。真正的问题在**命名**：叫 `e2e_sound` 而内容只到 L2⇄L3。本文件的 docstring 已经把这件事写成一张表（「`Extract` 对语义**内容**不承重，但对结论的**可陈述性**承重」），**所以这是已登记的命名债，不是待强化的陈述**。 |
| `Domains/Geometry/Engine.lean` | `derivation_sound` | 强化了：新增「按步数索引的可导性」`DerivableIn` 与它的声称性 `derivableIn_sound`、`derivable_sound`。原定理的前提形状是 `∀ d ∈ r.prems, EntailsGeo G d`——**前提只能来自 `G`**，所以推导里更早的结论**不能当作后来的前提**：`steps` 只是一张清单，条目互不相干。**新定义的规则支取的是`DerivableIn rules G k d`**，所以链式可表达；并且新增**`derivable_two_step`** 作为链式的具体见证（旧陈述表达不了），以及 **`derivable_of_flat`** 证明新定义**包含**旧陈述。三次失败都是 Lean 的正确拒绝：嵌套归纳类型 `Exists`、`induction` 不支持互归纳、互归纳的终止性。最终形态是**在 `ℕ` 上的结构递归**，没有嵌套、没有互归纳、终止性平凡。 |
| `Domains/Geometry/Synthesis.lean` | `synthesize_from_initialisation` | 强化：原陈述的 `h : ∀ c ∈ G, ∃ a b, c = .samePoint a b` **在证明里没被用到**，`G` 也**不在结论里**，结论只讲一个与 `G` 无关的 `samePoint a b`——**所以它名不副实**：它没说「初始化的约束集 ⟹ 合成样本满足该约束集」。强化后的前提是 `hG : G = List.replicate G.length (.samePoint a b)`（**一致性**），结论覆盖 `G` 的**每一条**，且 `hG` 在证明中承重（逐条用 `mem_replicate_eq`）。新增 `mem_replicate_eq`（自证，不依赖 mathlib 的名字）。两次失败：`obtain ⟨a', b', rfl⟩` 之后 `subst` 会消掉参数 `a`/`b` 本身；改 `rw [hcab, ha, hb]` 后依赖类型上的多重 `rw` 不收敛。最终用一个**不依赖逐条改写**的入口。 |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_loss_compound` | 强化：原来的四个合取项**全是既存定理的打包**（`tokenize_collision`、`semantic_not_injective`、`decode_encode`、`encode_injective`），**没有任何一条断言两处损失之间的关系**——而定理名说「不可互相归约」。新增**两条新定理**作为第五、六个合取项：**(7) 下沉** `l0_loss_survives_pipeline`（`∃ s ≠ t, pipeline s = pipeline t`，其中 `pipeline` 是**新定义**的整条链）——L0 的损失**不可被任何下游环节修复**；**(8) 上浮** `l2_loss_visible_at_L1`（②的见证对在 `encode` 下**仍然不同**）——②的损失**不是** L0 损失。**两者合起来才排除「端到端就是某一环的损失」**：若只是 L0 的，则 (7) 成立而 (8) 不成立；若只是 L2⇄L3 的，则反之。四处修正：插入点落在文档块内；`Lattice.Core.VectorCoord` 是我猜的类型（不存在），改为不注解让 Lean 推断；`(n := n)` 多余；`semantic_not_injective` 的返回是三元合取，需逐层析构。 |
| `Evidence/BridgedComposition.lean` | `compose_three_with_bridges` | 降级已完成。两处：(1) doc 原写「这是非相邻组合的一般形式：**段数不限**」——那句话**没有定理支撑**（定理字面上只有 `P Q R` 三个性质、`f g h` 三个映射），已改为「**三段** + 逐段桥」并写明 **N 段未证、不再声称**；(2) 上方表格列的是 `compose_list_with_bridges`——**那个名字在文件里不存在**，已改为真实的 `compose_three_with_bridges`。对现有用途（两段对照、桥数 2）三段已够。 |
| `Evidence/Hypotheses.lean` | `no_redundant_hypotheses` | 降级已完成：**名字**才是过度声称的地方。它读作「审计没有发现冗余前提」（关于**整个定理库**），而定理只说 `chainAudit` 里没有 `.redundant` 条目。已改名为 **`no_redundant_entries_in_audit_table`**（入度 0，无依赖者），doc 也写清「证的是本表，不是库」。 |
| `Evidence/StructureCensus.lean` | `no_zero_obligation_structure` | 降级已完成，**两处**。(1) 名字读作「没有结构是零义务的」，而陈述只覆盖 `census` 的 **5 个条目**；已改名为 **`no_zero_obligation_in_census_table`**。(2) doc 原接着写「**库里的每个结构都有实质义务**」——**那句话没有机器依据**：`obligations` 是作者填的数字字段，不是证明义务，而这 5 行也不是库里的全部结构；**从一张手填的五行表推全库是无效推理**。已删掉该句，改为「这是一条**表一致性**检查，不是关于库的结论」。 |
| `Runtime/ApproxExact.lean` | `epsSat_of_loss_le_sq` | 处理完成：**它原本是一条别名**。结论 `\|E.resid p x\| ≤ ε` 与 `abs_resid_le_of_loss_le_sq` **逐字相同**，而名字说「`EpsSat` 的连接」——`EpsSat` **根本没出现**。现在结论是 **`EpsSat E.toPenaltyEmbedding p (ε ^ 2) x`**，**并且 `0 ≤ ε` 不再需要**（右端是 `ε ^ 2`，自动非负）——**谓词形式比残差形式更强**。三处计划外修正：`Audit/Counterexamples.lean` 的表行与 docstring 改指 `abs_resid_le_of_loss_le_sq`（反例 `r = 0, ε = -1` 对谓词形式**不适用**）；`Audit/Hypotheses.lean` 的「`0 ≤ ε` 承重」条目同样改指残差形式。四次脚本失败后的**结构性修正**：CJK 文本不再嵌入 Python 字符串，改为**片段写成文件 + ASCII 锚点拼接**。 |
| `Lib/Optim/RealSGDStochastic.lean` | `sgd_rate_bound` | 处理完成（**doc 修正**，不是证明修正）：原 doc 的假设清单只列 `D > 0`、`G > 0`、`T > 0`，**漏掉了真正承重的 `hstep`**。现在清单补齐并给出每条的作用。**并且写清了为什么 `hstep` 不是可补的缺口**：接口里有 `Subgradient f (x t) (Expect p (g t))`，而 `x : ℕ → Ω → ℝ` 是**随机过程**，两者**类型上就对不齐**（`PROOF-DEBT` 里那条 `B_missing` 写的 `Subgradient f (x t) (…)` 本身就是病式）；逐路径要求 `Subgradient f (x t ω) (g t ω)` 等于说**每个采样都是真次梯度**，噪声就没了。**标准证明靠条件期望 `E[g_t \| x_t] = ∇f(x_t)`，而本形式化只有 `Expect p Y = ∑ ω, p ω · Y ω`，没有 σ-代数与滤流。**能推出的是**确定性 `x` 的单步**，即 `sgd_expectation_contraction`。 |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_vacuous_composition` | 处理完成（**补上正面对照**）：原条目只报了**反例**（结论可以不带 `ts`），而 `B_missing` 要的是一条**真正用上 L1⇄L2 一跳**的语义结论。新增 **`e2e_contribution_of_L1L2`**（三段）：① `(toSegs ts).map mkConstraint = cs`（`ts` 的**段结构**恰好给出 `cs`）；② `∀ cs', Extract ts cs' → cs' = cs`（`ts` 的**读法唯一**）；③ `cs` 决定权重行为。另单独成条 **`extract_functional`**：`Extract` 是**部分函数**。**关键认识：「去掉 `ts` 结论不变」与「`ts` 无所贡献」不是同一件事**——`ts` 的全部贡献**已经在 `cs` 里用尽**，那是信息单向流动 `ts → cs → 权重` 的貌似。一处修正：`Option.some.injEq` 的方向需 `.symm`。 |
| `Evidence/StructureCensus.lean` | `census_length` | 处理完成：本轮发现清册里有一行**数字是错的**——`Representation` 写 `fields := 8`，而 `Runtime/Extraction.lean:58` 的结构只有 **7** 个字段（`inputP`/`inputW`/`encode`/`decode`/`compile`/`extract`/`roundtrip`），**8 不符合任何一种口径**（连把类型参数算进去也是 9）。已改为 7（清册行、§2.2 标题、汇总表三处，密度 12.5% → 14.3%）。**关键：三条 `decide` 定理照旧为真**——它们核对的是**表内算术**，不是**表与库的一致性**。已在 `census` 的 doc 里写明这一点，并列出本轮找到的错行。真正锁住它需要**反射取字段数**（Lean 元编程），不是 `decide`；在那之前这些数字只能按「人工录入」读。 |
| `Semantics/Annotations.lean` | `holdsSet_member` | 处理完成：它与 `Domains/Constraints/ConstraintSet.holdsSet_mem` **同一条定理**，只差参数顺序，而两份**都各自做了归纳**。已改为**一行转发**（`holdsSet_mem hmem pts h`），保留本地名字是因为 `edit_frame_holds`使用这个参数顺序。**判定里「唯一跨文件引用 `Semantics/Merge.lean:142`」已经不成立**——那一行现在是 `merge_parts`，而 `Merge.lean` 既没 import 本文件也没 open 本 namespace。 |
| `Runtime/CompilerScheme.lean` | `scheme_covers_all` | 处理完成（**doc / 状态修正**）：`Slots.lean` 的 `lift.compile.single_item_sound` 把它当作`.discharged` 的凭证，而它是 `⟨rfl, rfl, rfl⟩`——**字段自等**。已把 note 改为「**CLOSED — STRUCTURALLY ONLY**」，并写明**本条证的是「一个方案适用于所有后端」的结构事实，不证任何语义声称性**，并指出真正的声称性证明在 `Geo/Compile.geoCompiler.sound`（`unfold loss; rw [hx]; ring`）。 |
| `Runtime/CompilerScheme.lean` | `backend_sound` | 同上同一处修正：`every_backend_sound` 是 `Compiler.sound` 的**字段投影**，它给出 `sound` 是因为 `sound` 是结构的**假设**，sound 并非白得。note 现已写明这一点，并且指向一个真实的逐实例证明。 |
| `Evidence/Hypotheses.lean` | `chainAudit_length` | 处理完成（**doc 修正**）：三处写「**七**条」（§1 标题、§二 标题、本定理 doc），而 `chainAudit` 实际是 **10 行**。清单从 7 扩到 10 时 doc 没跟上。**关键：`decide` 只核对表内算术，所以三处「七」与一条 `= 10` 可以同时为「绿」。**已把三处改为 10，并在三处各写一句说明这个机械局限。 |
| `Lib/Chain/RealModelFamilyChainWiring.lean` | `convertVec_bias_eq_convertRealVec_bias` | 处理完成（**doc 降级**）：原 doc 说「本命题同时需要两侧的四个定义 ⟹ **这就是边的承重点**」，而证明是 **`rfl`**，只钉了**偏置字段**。**那句话会让读者以为语义抬升已证。**doc 已改为「只证字段相等」，并写出**真正该证的交换方块**（`RealLayerOut (convertRealVec c) (toRealVec x) = toRealVec (LayerOut (convertVec c) x)`）——**那条没有证、也没有写**。本条保留（它把可达边接成真实 import 依赖）。 |
| `Lib/Editing/RealCompileExtractClosed.lean` | `compile_extract_end_to_end` | 处理完成（**doc 降级**）：标题原本是「**★ 端到端闭环定理（target form）★**」。**实际证的是**：`extractLayer_compileToLayer`（**`rfl`**）把左式换成 `AllSatisfied cs`，再由 `symbolToWeight_correct` 收尾——**证明体是 `rw` 一行 + 一次实例化，零往返内容**。为什么闭环在这里是免费的：那一跳的 `extract` 是**字段重命名**，所以 `extract ∘ compile = id` 是定义级的。真正的端到端需要**一条信息有损的编译路径**——**没有，也不声称。**保留本条仍有用：它把两个此前从不互相引用的文件接成一条定理。 |
| `Lib/Quantization/RealMixedPrecision.lean` | `accumulation_error_bound` | 处理完成（**删未用前提**）：签名里的 `(_hM : 0 ≤ M)` **在证明中从未被引用**（`_` 前缀就是证据），而且**它是可导出的**：`hmag 0 (Nat.zero_le n)` 给出 `\|accSum ad 0 x\| ≤ M`，而 `accSum ad 0 x = 0`，所以 `0 ≤ M`。**删掉它使本条更强**。下游 `ieee_accumulation_error_bound` 的 `hM` **只用来传给本条**，因此一并去掉（它也因此更强，且它**没有调用者**，所以改元数不破任何东西）。**门禁表现**：`check_underscore_hypotheses` 报 **STALE** 并指名要删哪一行，基线从 127 降到 126（new 0 / stale 0）——**那是双向基线正常工作的样子**。 |
| `Lib/LearningTheory/RealDistill.lean` | `chain_distill_bound_lipschitz` | 处理完成（**桥补上了**）：`Ls : ℕ → ℝ` 原本是**自由函数**，doc 自己写着「诚实假设：若不同取 max」。实测发现**零件已经在树里**：`Runtime/StackError.affineAct_lipschitz`（**逐分量**）与 `layerMag_nonneg`。缺的是两步：**(1)** 逐分量 → sup 范数；**(2)** 师生取 max。新增 **`affineAct_lipschitz_norm`**与 **`chain_distill_affine`**（`Ls i := max (layerMag (Wt i)) (layerMag (Ws i))`）。⚠ **四次失败后才找到原因**：`pi_norm_le_iff_of_nonneg` 的正确用法是 `rw […]` 然后 `intro`，而**不是** `\|>.mpr`——`rw` 能从目标推断隐含的 `f`，项级 `mpr` 不能。★ **可迁移的教训：卡在一条 mathlib 引理上时，去读它的调用点，而不是猜它的参数形状。**边界：只做仿射层；**不声称 `layerMag` 是最优算子范数**；非线性层未接上。 |

## 对抗性复核：第一审判错的 **34 / 45**

把 45 条 `delete` 判定交给第二批子代理，任务设定为**论证第一审判错了**。结果：

| 结论 | 条数 |
|:--|--:|
| **推翻**（keep） | **34** |
| 确认可删（delete-safe） | 8 |
| 应改写而非删除（rewrite） | 3 |

**76% 的误判率**，原因高度集中：

1. **删除会让构建断裂。** 多条「空定理」被同文件后面的定理当作 `atomic` 义务的实参
   （`ObligationIndependence:95`/`:144` 就是 `absorbs_not_derivable`/`decreases_not_derivable` 的实参），
   还有的被 `#print axioms` 审计行点名——而 `#print axioms` 对不存在的名字是**硬错误**。
   第一审只看了 `proof` 与同名重复，没看后文调用点。
2. **「重复」常常是删错了对象。** `softThresh_le_of_is_min` 是已授权改名后的成果，
   真正重复的是同文件 `:428`，且 `:598` 用的是后者。
3. **「证明便宜」被误当成「陈述为空」。** `add_norm_bound` 是三角不等式，便宜但不是重言。
4. **4 条根本不是声明**，是 docstring 散文被旧提取器误抽（`stated`、`rather`、`applies`、
   `eq_softThresh_of_is_min`）。提取器已修，**这些是陈旧数据而非新 bug**。

**所以本文件把「一次判定」当线索，不当结论。** 任何 `delete` 必须经过
（a）对抗性复核 与（b）全库构建通过，两步都过才落地。

## 第二把尺子也是错的：点号记法

对抗性复核发现 `in_degree` 漏掉**点号记法**：token 正则把 `.` 算进标识符，
于是 `L.ladder_forward` 扫成单个 token，`ladder_forward` 永远匹配不到。
实测 `ladder_forward` 有 **15 处调用、13 个文件**，`in_degree` 报 **1**。

修正后（标识符按 `.` 切开）入度 ≥ 1 的定理从 839 升到 **873**，排名重排：
`roundtrip_extractVec` 升到首位（18）。

**这是本轮第二次「尺子错了，不是库错了」**——第一次是 docstring 被当成声明。
两次都由审阅人发现，两次都无法由守卫自身发现。

## 后续

1. **按修正后的入度重跑第一层**（839 条），再补齐其余 7,587 条。
   批次已按修正后的入度重新生成（`agent-tmp/review/batch_000..105.jsonl`）。
2. **工具修正（已修，第 208 轮）**：审阅人报告的两处**本仓库工具自身**的缺陷已修复——
   - 提取器现在只在**剥除全部注释**的文本里找声明，并从保留 docstring 的文本按偏移取回作者自述；
     幻影声明消失（`theorem` 7,576→7,575，`structure` 158→157）；
   - `in_degree` 只统计**代码**中的出现，且要求引用方真的 `import` 定义所在模块；
     `induction` 183→1、`le_trans` 136→0。
   **这是本轮最重要的收获之一：审阅人发现的不是库里的问题，而是丈量库的尺子的问题。**
3. **`delete` 类是唯一可以立刻处理的**：它们没有信息量，删掉不损失任何东西，
   而保留会让 8,000+ 的定理数虚高。
