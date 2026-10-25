# 可逆性审计表（REVERSIBILITY）

> **集群**：C2 ｜ **日期**：2026-09-21 ｜ **纪律**：全程只读既有文件，仅新增 `RealReversibilityBoundary.lean`；不 git、不改既有文件。
> **证据基础**：逐文件精读 `lean/` 中全部「转换 / 提取 / 往返」相关模块（22 个目标模块 + 其依赖），
> 并在 `scripts/lake-lock.ps1` 锁下做内核验证。
> **口径**：本表把"可逆"拆成**参数层**与**语义层**两个不同命题——这是本审计的核心方法论。
> 项目此前对"可逆"的叙述混淆了二者，导致 `doc/02`「完整且可逆的链路」成为**过度声称**。

---

## 0. 方法论：可逆性的两层判据（本表全部结论的基础）

设符号对象集 `X`（约束）、权重对象集 `W`（神经元/层）、语义函数
`sem_X : X → (输入 → Prop)`、`sem_W : W → (输入 → Prop)`，编译 `compile : X → W`。

| 层 | 命题 | 数学判据 | 有定理？ |
|:--|:--|:--|:--|
| **参数层可逆** | `extract ∘ compile = id` | `compile` **单射** | ✅ 有（`roundtrip_extract` / `roundtrip_extractVec` / `extract_compile_identity`） |
| **语义层可逆** | `∃ extract, sem_X (extract w) = sem_W w` | `compile` 在**商掉语义等价类**后单射 | ❌ **无**，且**已被机器验证为假**（见 §3） |

**关键区分**：`compile` 在参数层是单射（不同约束 ↦ 不同神经元），
但**语义层不是单射**——`∃ c ≠ c', sem(c) = sem(c')`，且二者都可由 `compile` 到达。
于是「函数 ↦ 权重」这件事**本质上是多对一**：
同一个函数有无穷多权重实现（doc/01 难点 2 的原话）。

> **这是本审计对项目叙事的一处实质性更正**：
> `doc/02` 的「完整且可逆的链路」在**参数层**成立且已机器验证，
> 在**语义层**已被机器验证为**假**。E1 审计说的"全局可逆已被机器验证为假"
> 指的正是**语义层**；此前库内**没有**任何一条定理把这个区分写出来
> （`RealCompileExtractClosed` 的空缺是同一问题的另一面）。
> 本文件补齐的就是这条**边界定理**。

---

## 1. 主表：逐层判定

**类别**：**(a)** 真正可逆 ｜ **(b)** 等价类意义下可逆 ｜ **(c)** 语义等价但语法不等 ｜ **(d)** 已机器验证不可逆 ｜ **(e)** 未知/未证

| # | 层级 / 模块 | 变换 | 定理 / 反例 | 类别 | 原因 | 规范形（若有） |
|:--:|:--|:--|:--|:--:|:--|:--|
| 1 | `ConvertLinear` (Int 标量) | `convert : LinearConstraint → LinearNeuron`，`a ↦ w, b ↦ b` | `convert_preserves_semantics`、`convert_preserves_solution_set`、**新增** `convert_injective` | **(a)** | 字段逐分量拷贝；结构构造子单射 ⟹ 双向都有定理 | 自身（无需商） |
| 2 | `ConvertVectorLinear` (Int 向量) | `convertVec : VectorConstraint → LinearLayer` | `convertVec_preserves_semantics`、`convertVec_preserves_solution_set`、**新增** `convertVec_injective` | **(a)** | 同上（`List Int` 逐字段拷贝） | 自身 |
| 3 | `RealLinear` (ℝ 标量) | `convertReal : RealConstraint → RealNeuron` | `convertReal_preserves`、**新增** `convertReal_injective` | **(a)** | 同上 | 自身 |
| 4 | `RealLinear` (ℝ 向量) | `convertRealVec : RealVectorConstraint ι → RealLinearLayer ι` | `convertRealVec_preserves` | **(a)** | 字段拷贝（同 #3 的 `Fintype ι` 版） | 自身 |
| 5 | `SymbolToWeightCorrectness` | `compileToLayer = List.map convertVec` | `symbolToWeight_correct`（`AllSatisfied ↔ AllZeroOutputs`）、`symbolToWeight_verify`、`symbolToWeight_empty` | **(a)** | 列表映射上的 `forall_mem_map_iff` 逐元素提升；语义保持**双向** | 自身 |
| 6 | `WeightToSymbolEquivalence` | `extract` / `extractVec` | `roundtrip_extract`、`roundtrip_extractVec`、`roundtrip_behavior`、`extract_is_valid` | **(a)** | **参数层往返恒等**（`cases c <;> rfl`）；这是库内最强可逆结论，但**只覆盖参数层** | 自身 |
| 7 | `RealRoundtripBound` | `extractReal` / `roundtripNeuron` | `extract_compile_identity`、`roundtripNeuron_self`、`roundtrip_error_bound_exact`、`extract_stability_isometry` | **(a)** | ℝ 版参数层恒等；`extract_stability_isometry` 证明提取是**等距**（Lipschitz 常数恰为 1，无信息放大） | 自身 |
| 8 | `RealRoundtripBound`（扰动版） | 量化/剪枝后往返 | `roundtrip_error_bound`、`roundtrip_under_quantization`、`roundtrip_under_pruning`、`extract_stability` | **(c)** | **行为一致而非结构相同**：往返本身精确，误差全部来自外部扰动 δ；结论是**界**（`≤ δX + δ`）而非等式 | 无（误差带 `[−δX−δ, δX+δ]`） |
| 9 | `ConvertVectorLinear.scaleVec` | `scaleVec c lam`（`a ↦ a·λ`, `b ↦ b·λ`, λ≠0） | `scaleVec_preserves`、`dot_map_mul`、`foldl_init_add` | **(b) + (d)** | **本审计的枢纽**：缩放保持语义**但改变参数** ⟹ `compile` 在语义层**非单射** ⟹ 「函数↦权重」不可逆。新增反例 `scaleVec_ne_self_two`、`convertVec_scale_ne`、`reversibility_boundary` | **权重向量方向归一化**（如 `w/‖w‖`）或**首非零分量归一**；即 doc/01 所说的"规范符号形式" |
| 10 | `RealLinear.real_scale_preserves` / `realVec_scale_preserves` | ℝ 版缩放 | `real_scale_preserves`、`realVec_scale_preserves`、`realDot_scale` | **(b) + (d)** | 与 #9 同构；ℝ 上 λ 连续取值 ⟹ **不可数无穷多**实现（Int 版是可数无穷） | 同上；ℝ 版可加 `b = 0`（齐次化）或 `‖(a,b)‖ = 1` |
| 11 | `ConstraintEmbeddingSoundness` | `loss c x = (NeuronOut (convert c) x)²` | `embedding_soundness`、`embedding_no_false_solutions`、`embedding_no_missing_solutions` | **(c)** | 损失是语义的**函数**而非语义本身：`loss = 0 ⟺ sat`（双向），但 `loss` 不是单射（`loss c x = loss c' x'` 常态）。**嵌入可逆性 = 零集的同构，不是值的同构** | 零集 `loss⁻¹(0) = sat`（正是一个规范形） |
| 12 | `TotalLoss` / `RealTotalLoss` | `totalLoss = Σ out_i²` | `totalLoss_eq_zero_iff_allSatisfied`、`realTotalLoss_soundness`、`realTotalLoss_pos_of_unsatisfied` | **(c)** | 同上：#11 的列表/ℝ 版。**合取语义**保持，但和式本身丢序/丢符号（`Σ` 不是单射） | 零集；严格正性 `> 0` 给出"不满足"的可判定信号 |
| 13 | `RealNonlinearCompile`（sign 编码） | `signCompile a b x = sign (a x + b)` | `signCompile_preserves`、`signCompile_solution_set`、`prodZero_compile` | **(d)** | `Real.sign` 把 `(0,∞) ↦ 1`、`(-∞,0) ↦ -1` ⟹ 编码**强非单射**。零化 ⟺ 等式**成立**（这条方向对），但**编码值不可反演** | 零集 `{x \| sign(...) = 0}`；**规范形 = 零集本身** |
| 14 | `RealNonlinearCompile`（relu 编码） | `reluCompile a b x = relu (a x + b)` | `reluCompile_preserves`（`a x + b ≤ 0 ⟺ relu = 0`）、**新增** `relu_not_injective`、`relu_zero_not_implies_eq` | **(d)** | `relu` 在 `(-∞,0]` 上恒为 0 ⟹ 零化**不再**推回唯一原值。**这是「输出零 ⟹ 约束满足」为假的根源** | 零集 `{x \| a x + b ≤ 0}`——但这是**不等式**的零集，与等式的零集**不同构** ⟹ 语义类本身改变了 |
| 15 | `RealSymbolToWeightNonlinear` | 带激活的层 `act (LayerOut l x)` | `symbolToWeight_nonlinear_correct`（**带 `ZeroFixing` 假设**）、`zeroFixing_of_strictMono`；反例 `reluZ_not_zeroFixing`、`reluZ_counterexample`、`reluZ_not_strictMono` | **(d)** | **已机器验证**：一般非线性下无条件版**为假**（`reluZ_counterexample`：约束 `x+1=0` 在 `x=-5` 上输出 0 但约束不满足）。正确版本**必须**带零集条件 `ZeroFixing` | 条件 `ZeroFixing act`（= 零集恰为 `{0}`）；严格单调 + `act 0 = 0` 是其充分条件 |
| 16 | `RealNonlinearCompile.nlCompile`（复合） | `(sign, relu)` 逐分量 | `nonlinear_compile_preserves`、`nlCompile_batch` | **(d)** | 复合编码继承 #13/#14 的非单射；只在**零集层面**保语义 | 零集 `(0,0)` |
| 17 | `RealNonlinearCompile.piecewiseCompile` | 分段线性按断点选支 | `piecewise_compile`、`piecewise_compile_solution_set` | **(c)** | 输出**精确双向**保语义，但 `piecewiseCompile` 丢掉"断点 `c`"与"两条分支系数"中的自由度（分段函数表示不唯一） | 规范形需约定分段边界归属（本文件已约定 `x ≤ c` 归左段） |
| 18 | `RealNonlinearCompile`（线性化） | 仿射 `L` 近似非线性 `f` | `nonlinear_soundness_local`、`nonlinear_soundness_local_exact`；**反例** `linearization_global_fails` | **(d)** | **已机器验证**：全局版不可得（`∃ f L, (∀t, L t = 0) ∧ ∃t, f t ≠ 0`，取 `f = t², L ≡ 0, t = 1`）。**诚实降级**为有界域 `\|t\| ≤ R` 上的 ε 带 | 无（只有 ε 带 `\|f t\| ≤ ε`） |
| 19 | `RealNonlinearExtract`（FCA 闭包） | `closureOperator R = extent ∘ intent` | `extract_idempotent`、`closureOperator_extensive`、`closureOperator_monotone`、`extract_preserves_fixpoint` | **(b)** | **等价类意义下可逆的典范**：提取把任何 `Ol` 压到它的闭包 `Ol**`；**在闭包不动点上可逆**（幂等 + 扩张 + 单调），在闭包外**丢信息** | **闭包 `Ol**`**（FCA 概念 = 双向闭包不动点，`formal_concept_iff_closure`） |
| 20 | `RealFCA` | `extent` / `intent` / Galois | `galois_connection`、`closure_idempotent`、`intent_closure_idempotent`、`extent_intent_extent`、`concept_meet_is_concept`、`concept_join_is_concept`、`subconcept_trans` | **(b)** | Galois 伴随给出**双向唯一对应**（在闭包上）；概念格是 meet/join 闭合的格。**但闭包外的原像不唯一** ⟹ 全局非单射 | **形式概念**（`IsFormalConcept`，= 闭包不动点） |
| 21 | `RealFCAInstance` | 满足关系实例化为 `RealConstraintSat` | `single_solution_constraint_concept`、`constraint_entailment_closure`、`entailment_closure_idempotent` | **(b)** | 提取到闭包即稳定；闭包 = **逻辑后承**。⚠️ 但 `constraint_entailment_closure` 的证明体是 **`rfl`**（`RealFCAInstance.lean:40-41` 自标"原 `closure_idempotent` 引用与目标不匹配，已改为 rfl，语义不变"）——**实质内容弱于名字** | 蕴含闭包（后承闭包） |
| 22 | `RealExtractInvertibility` | 可逆的充要条件 | `leftInverse_iff_injective`、`invertibleOn_iff_injOn`、`strictMonoOn_injOn` | **(a)** | **判据本身是完整双向等价**（可逆 ⟺ 单射 ⟺ 区域单射）；这是本审计全部否定结论所依赖的**元定理** | 无（判据，非规范形） |
| 23 | `RealExtractInvertibility`（ReLU） | `relu x = max x 0` | `relu_injOn_nonneg`（`[0,∞)` 可逆）；**反例** `relu_neg_eq_relu_zero`、`relu_not_injOn_nonpos` | **(d)** | **已机器验证反例**：`relu (-1) = relu 0`。`relu` 在 `(-∞,0]` 上不可逆；**全实轴不可逆**（**新增** `relu_global_not_invertible`） | **正半轴 `[0,∞)`**（该区间上 `relu` 是恒等） |
| 24 | `RealExtractInvertibility`（GELU-tanh） | `geluTanh x = x·gate x` | `geluTanh_strictMonoOn`、`geluTanh_injOn`（**无条件定理**）；反例见 docstring：全实轴非单射 | **(b)** | **区域 (b)**：`[0,∞)` 上严格单调 ⟹ 单射 ⟹ 可逆；**全实轴 (d)**：非单射。⚠️ docstring `:41` 引用 `geluTanh_not_injective`，**该定理名在本库不存在**（见 §5 清单） | **`[0,∞)` 区域**（区域规范形） |
| 25 | `RealExtractInvertibility`（sigmoid / exp） | `sigmoid`、`Real.exp` | `sigmoid_injective`、`sigmoid_invertible`、`exp_invertible` | **(a)** | 全局单射 ⟹ 全局可逆（罕见的**真全局可逆**实例，但都不属于转换层的编码） | 自身 |
| 26 | `RealNonlinearExtract`（分段线性） | `piecewiseLin c f g` | `piecewiseLin_left_invertible`、`piecewiseLin_right_invertible`、`relu_extract_on_positive`、`relu_extract_recovery` | **(b)** | **区域可逆**：给定各段逆 `fi`/`gi`（**假设**），逐段恢复输入。⚠️ 逆函数**存在性**由用户假设提供（`:26-27` 自标），非本库定理 | **逐段区域**（每段一个逆） |
| 27 | `Combinators`（ℤ） | `andC a b = a²+b²`、`orC a b = a·b` | `andC_eq_zero_iff`、`orC_eq_zero_iff`、`and/or_comm/_assoc_preserves`、`dist_preserves` | **(c)** | **语义（零集）同态，但值域非同态**：`andC a b = andC b a` 恒成立（值相等），而 `a²+b²` 不是单射（`(1,0)` 与 `(-1,0)` 同像）。保的是**零化判定**，不是代数结构 | 零集；交换/结合/分配律**在零集判定上**保持 |
| 28 | `RealCombinators`（ℝ） | 同 #27，ℝ 版 | `andC_eq_zero_iff`、`orC_eq_zero_iff`、`and/or_*_preserves`、`andC_pos_of_ne`、`orC_pos_of_both_ne` | **(c)** | 与 #27 同构；ℝ 额外给**严格正性**（任一非零 ⟹ `andC > 0`），把"不满足"变成可观测的正信号 | 零集 + 严格正性 |
| 29 | `ComboN` | `sumEven xs = Σ (x%2)` | `sumEven_eq_zero_iff`、`comboN_preserves`、`comboN_verify`、`comboN_empty`、`comboN_single` | **(c)** | N 元**合取** ⟺ 输出和为零。和为**非单射**（丢序），但零化判定**双向等价** | 零集（和 = 0） |
| 30 | `Disjunction` | `prodOuts = ∏ out_i` | `disj_embedding`、`prod_eq_zero_iff_exists`、`disjN_preserves` | **(c)** | N 元**析取** ⟺ 输出乘积为零（ℤ 零因子）。乘积**非单射**，零化判定**双向等价** | 零集（乘积 = 0） |
| 31 | `ModConstraint` | `Congruent x a m = m ∣ x-a`；`ModOut x a = x-a` | `mod_preserves`（**`Iff.rfl`**）、`congruent_refl/_symm/_trans/_add`、`congruent_mod_zero`、`congruent_mod_one/_neg_one` | **(b)** | **同余是等价关系**：`Congruent` 天然定义在**商 `ℤ/mℤ`** 上 ⟹ 提取只能到**同余类**，`a ↦ a mod m` 就是规范形。⚠️ `mod_preserves` 证明体是 `Iff.rfl`（定义同构，零数学内容） | **`x mod m`**（同余类代表元）；`m = 0` 退化为严格相等 |
| 32 | `Geometry` | `Collinear a b c = cross(b-a, c-a) = 0` | `collinear_preserves`（**`rfl`**）、`cross_translate`、`collinear_translate`、`cross_cyclic`、`collinear_cyclic`、`collinear_swap`、`collinear_degenerate` | **(b) + (d)** | **(b)**：共线在**平移**（`collinear_translate`）与**轮换/交换**（`collinear_cyclic`/`collinear_swap`）下不变 ⟹ 规范形是**平移+置换轨道**。**(d)**：编码**非单射**（`cross` 丢信息；`collinear_degenerate` 给出退化见证 `b = a` 时一律共线） | **平移 + 三点置换的轨道**（几何规范形式） |
| 33 | `Inequality` | `LeOut x a = x - a` | `le_preserves`、`le_and_ge_iff_eq`、`le_ge_iff_sq_zero`、`bound_embedding_chain`、`sq_pos_of_ne` | **(c)** | 单边不等式 `≤ 0` 判定**双向**保持；但 `LeOut` 值**非单射**（丢 `(x,a)` 的具体值，只留差）。夹逼 ⟺ 等式 ⟺ 平方零化是**三层语义等价链** | 差 `x - a ≤ 0` 的零集；非严格时 `sq_pos_of_ne` 给严格正信号 |
| 34 | `LayerComposition` | `layerFwd` / `layerSeq` 多层前向 | `layerFwd_allzero`、`constraint_satisfaction_propagates`、`layerSeq_three`、`layerSeq_three`、`dot_replicate_zero_any` | **(c)** | **单向传播**：约束满足 ⟹ 下一层收到零向量 ⟹ 输出退化为偏置。**反向不成立**（偏置层不可反推上层输入）⟹ 严格单向，非可逆 | 无（只证正向传播） |
| 35 | `RealWeightSharing` | `sharedChain F n` | `sharedChain_eq_iterate`、`shared_chain_error_bound`、`shared_vs_independent(_strict/_eq_iff)`、`shared_parameter_count(_le)`、`shared_grad_*` | **(b)** | **跨层参数共享是投影而非双射**：`F ↦ (F,…,F)` 把不同层函数映到同一共享链；共享链 ↔ `iterate F n`，**唯一反演 = 取任意一层**（等价类 = 同一个 `F`） | **单层 `F`**（共享链的规范代表元） |
| 36 | `RealSubspaceConstraint` | `subspaceConstraint` / `simplexConstraint` / `sphereConstraint` | `subspace_proj_mem`、`subspace_proj_idempotent`、`subspace_inf`、`simplex_convex`、`simplex_normalize_feasible/_fixed`、`sphere_normalize_projects/_fixed` | **(b)** | **投影算子幂等 ⟹ 不动点集 = 规范形集**：`subspace_proj_idempotent`、`simplex_normalize_fixed`、`sphere_normalize_fixed` **三条都是"可行点 = 不动点"**（Extensive + Idempotent ⟹ 闭包算子）⟹ **在约束集上可逆，集外多对一** | **约束集本身**（`S` / 单纯形 / 半径 `r` 球面）；⚠️ 单纯形的**欧氏投影**未做（只有归一化），球面是径向投影 |
| 37 | `RealWeightedConstraints` / `N` | 加权损失 `L = Σ wᵢ‖Aᵢx−bᵢ‖²` | `weighted2_fderiv`、`weighted2_stationarity_iff`、`weighted2_stationarity_of_components`、`weightedN_fderiv`、`weightedN_stationarity_of_components` | **(c)** | **驻点 ≠ 约束满足**：定理三是**单向**（各约束满足 ⟹ 加权驻点），**逆命题未证**（且一般**为假**：`w` 可为 0，或加权残差相消）。这是**语义充分而非充要** ⟹ 既非 (a) 也非 (d)，标 (c) 并注明**逆向未证** | 无；⚠️ `w = 0` 时该约束被**完全忽略**（规范形需 `w > 0` 约定） |
| 38 | `RealRoPEExtrapolationFailure` | `rotateR θ` | **反例** `rotateR_zero_eq_two_pi`、`rotateR_not_injective`、`exists_ne_same_rotateR`、`extrapolation_failure_witness`、`period_multiple_witness` | **(d)** | **已机器验证不可逆**：`rotateR 0 = rotateR (2π)` 而 `0 ≠ 2π` ⟹ 位置编码**丢失模 `2π` 信息**，外推失败。**独立于** #9 缩放问题 | **模 `2π` 的角（`θ mod 2π`）**；训练长度 `< 2π/θ` 时超出部分**完全丢失** |
| 39 | `RealLayerNormComplete` | `normalize` | **反例** `normalize_not_injective`；`normalize_translation_invariant`、`normalize_idempotent` | **(b) + (d)** | **已机器验证不可逆**：常数向量 `1` 与 `0` 同像 ⟹ 非单射。(b) 面：平移 (逐点) + 正缩放不变 ⟹ 规范形存在；(d) 面：`0` 的像（`0` 向量）**不是**任何原像的规范代表 | **单位球面 ∩ 零均值超平面**（`centerSq = 1` ⟹ `normalize x = x`）；**但该球面本身不可再区分径向** ⟹ 严格说规范形只在**方向**上成立 |
| 40 | `RealCompileFloatCorrectness`（浮点链路） | 编译 + 舍入 `RoundOp` | `compile_error_bound`、`magPair_sound`、`opt_error_bound_invariant` | **(c)** | **行为等价而非结构相同**：结论是**误差界**（`MagPair` 幅度对归纳），非等式往返。浮点编译的"可逆"只能是**带 ε 的可逆** | 误差带（幅度对 `MagPair`） |
| 41 | `RealSparsity` → `RealRoundtripBound` | 剪枝/量化 | `prune_magnitude_bound`、`deltaFromPruning`、`roundtrip_under_pruning` | **(c)** | 同 #8/#40：界而非等式 | 误差带 `δ = √s·θ` |
| 42 | `RealCompileExtractClosed` | 编译-提取**端到端闭环** | 审计开始时**文件不存在**（roots 已注册）；**审计期间由 C1 集群落地**：`extractLayer_compileToLayer`、`compileToLayer_extractLayer`、`compileToLayer_bijective`、`compile_extract_end_to_end`、`closed_loop_adds_nothing`、`activated_loop_breaks`、`activated_extract_cannot_repair` | **(a) 对象层 + (d) 语义层** | ✅ **已消解**。该文件的 `compileToLayer_bijective` 证明的是**对象层双射**（`ConstraintSet ≅ Layer`）；**与本表 §3.3 的语义层非单射不矛盾**——两个**不同**约束映到两个**不同**层，但两层的**函数相同**。⚠️ `activated_loop_breaks` 进一步说明：**加了激活后闭环被破坏**（与第 14/15 行一致） | 对象层：自身（双射）；语义层：**无** |
| 43 | `RealNonlinearFidelity` / `RealContractAxioms` / `RealConversionStability` / `RealTokenSymbolLink` / `RealGelfandMathlib` / `RealOverSmoothingSharp` | — | 审计开始时**文件均不存在**（roots 已注册） | **(e) → 已消解** | ⚠️ 审计开始时 `lake build lattice` 会因缺失源文件**整体立即失败**（STYLE.md:124）。**审计收尾复核：7/7 均已由其他集群补齐**。教训：**roots 与文件存在性必须作为构建前置断言**，否则"全绿"结论不可信 | 待定（不在本审计范围） |

---

## 2. 类别统计

| 类别 | 条目编号 | 计数 |
|:--|:--|:--:|
| **(a) 真正可逆** | 1, 2, 3, 4, 5, 6, 7, 22, 25, 42（对象层） | **10** |
| **(b) 等价类意义下可逆** | 9*, 10*, 19, 20, 21, 24, 26, 31, 32*, 35, 36, 39* | **12** |
| **(c) 语义等价但语法不等** | 8, 11, 12, 17, 27, 28, 29, 30, 33, 34, 37, 40, 41 | **13** |
| **(d) 已机器验证不可逆** | 9*, 10*, 13, 14, 15, 16, 18, 23, 32*, 38, 39*, 42（语义层） | **12** |
| **(e) 未知/未证** | ~~42~~（已由 C1 落地）、~~43~~（已由其他集群补齐） | **0** |

（带 `*` 的条目**同时**属于 (b) 与 (d)——这正是本审计的核心发现：
**"等价类意义下可逆"与"严格意义下不可逆"是同一件事的两面**，
标注 (b) 时**必须同时**标注 (d)，否则就是 doc/01 难点 2 所警告的那种"口号式可逆"。）

> ⚠️ **注意**：上表 (a) 的 10 项**全部是参数层（对象层）结论**。
> 语义层**没有任何一项**属于 (a)——这是本次审计最重要的量化结论。

> 📌 **(e) 归零说明**：审计开始时 (e) 有 2 项（第 42、43 行），
> 均为"roots 已注册但文件不存在"。审计期间由 C1 集群与其他集群补齐，
> 本审计**收尾时复核确认**（7/7 文件存在，`RealCompileExtractClosed` 含
> `compileToLayer_bijective` 等实质定理）。故 (e) 现为 **0**，
> 但**这不改变**语义层不可逆的结论——恰恰相反，
> C1 的对象层双射**凸显**了"对象层可逆 ∧ 语义层不可逆"的分裂。

---

## 3. (d) 反例补齐清单（新增于 `RealReversibilityBoundary.lean`）

> **锁下构建结果（权威）**：`scripts/lake-lock.ps1 -Priority 600 RealReversibilityBoundary`
> —— `✔ [5702/5702] Built RealReversibilityBoundary` / `Build completed successfully.` /
> `[lake-lock] lake exit code: 0`。日志中 **`error:` 行数 = 0**，
> 且**无任何 warning 提及本文件**。全部 14 条声明内核验证通过。

| 反例定理（新增） | 证明的内容 | 类型 | 对应上表行 |
|:--|:--|:--|:--:|
| `not_injective_of_witness` | 元引理：`x ≠ y ∧ f x = f y ⟹ ¬Injective f`（全部否定结论的统一骨架） | 构造性 | — |
| `convert_injective` | **(a) 侧**：`convert` 在参数层是单射 | 正向定理 | 1 |
| `convertVec_injective` | **(a) 侧**：`convertVec` 是单射 | 正向定理 | 2 |
| `convertReal_injective` | **(a) 侧**：`convertReal` 是单射 | 正向定理 | 3 |
| `scaleVec_ne_self_two` | **缩放等价类的最小显式见证**：`scaleVec revC 2 ≠ revC`（`b: 2 ≠ 1`） | `congrArg` 投影见证 | 9 |
| `scaleVec_two_semantically_equal` | 两者的**语义逐点等价**（复用 `scaleVec_preserves`） | 复用既有定理 | 9 |
| `convertVec_scale_ne` | **编译结果参数层不等**：`convertVec (scaleVec revC 2) ≠ convertVec revC` | 构造性 | 9 |
| `relu_not_injective` | **激活层反例**：`relu` 全局非单射（`-1` 与 `0` 同像） | 构造性 | 14, 23 |
| `relu_zero_not_implies_eq` | **零化不等价反例**：`∃ x, relu (x+1) = 0 ∧ x+1 ≠ 0`（`x = -5`） | `decide` 级见证 | 14, 15 |
| `relu_global_not_invertible` | **存在性形式**：`∃ x y, x ≠ y ∧ relu x = relu y` | 构造性 | 23 |
| `relu_zero_fiber_not_singleton` | **纤维形式**：`∃ x ∈ relu⁻¹({0}), x ≠ 0`（`x = -1`）——「提取到唯一原值」失败的直接原因 | 构造性 | 23 |
| `reversibility_boundary`（**核心**） | **边界定理**：`convertVec` 单射 **∧** `∃ c ≠ c', sem(c) = sem(c')` —— 参数层可逆 与 语义层不可逆**同时**成立 | 合取 | 9, 10 |
| `no_extractor_preserves_both`（**核心**） | **不可能性定理**：不存在既满足参数层往返 `extract ∘ convertVec = id`、又把语义相同的权重映到相同符号的提取器 ⟹ **严格意义不可逆** | 否定式 | 9, 10 |
| `semantic_layer_not_injective` | **语义层非单射的显式形式**：`∃ w ≠ w'`，二者表示同一函数，且**都**是某个符号约束的编译结果 | 构造性 | 9, 10 |

### 3.1 `reversibility_boundary` 的精确陈述与意义

```lean
theorem reversibility_boundary :
    Function.Injective (convertVec : VectorConstraint → LinearLayer) ∧
    (∃ c c' : VectorConstraint, c ≠ c' ∧
      ∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat c' x)
```

- **第一个合取支**（`convertVec_injective`）：「符号 → 权重」在**参数层**不丢信息
  —— 这是 `roundtrip_extractVec` / `extract_compile_identity` 之所以成立的原因。
- **第二个合取支**：存在**两个不同**的符号约束 `revC = {a := [1], b := 1}` 与
  `scaleVec revC 2 = {a := [2], b := 2}`，它们**逐点语义相同**
  （`∀ x, sat c x ↔ sat c' x`），但 `convertVec` 给出的权重**不同**。

**推论（严格意义不可逆，已机器验证）**：设 `sem_W : LinearLayer → (List Int → Prop)` 为
`x ↦ LayerOut l x = 0`。由 `convertVec_preserves_semantics`，
`sem_W (convertVec c) = sem_X c`。于是 `sem_W (convertVec c) = sem_W (convertVec c')`
而 `convertVec c ≠ convertVec c'`。

⚠️ **注意：上面这段"推论"曾只是文字论证，本审计已把它升级为内核定理**
`no_extractor_preserves_both`：

```lean
theorem no_extractor_preserves_both :
    ¬ ∃ extract : LinearLayer → VectorConstraint,
        (∀ c, extract (convertVec c) = c) ∧                    -- ① 参数层往返
        (extract (convertVec revC) = extract (convertVec (scaleVec revC 2)))  -- ② 语义同一
```

由 ①，`extract (convertVec revC) = revC` 且
`extract (convertVec (scaleVec revC 2)) = scaleVec revC 2`，代入 ② 得
`revC = scaleVec revC 2`，与 `scaleVec_ne_self_two` 矛盾。
即 **① 与 ② 不可兼得** ⟹ 「参数层可逆」与「语义层可逆」是**互斥**的，
严格意义的可逆**不存在**。

> 这正是 doc/01 难点 2 的**机器验证形式**：
> 「同一函数有无数权重实现（排列/缩放等价、冗余神经元）⟹ 反编译须选规范符号形式」。
> **规范形式 = 缩放轨道的代表元**，例如
> `w ↦ (w, b) / ‖(w, b)‖`（ℝ 版，要求 `(w,b) ≠ 0`），或
> `w ↦ (w, b) / |首非零分量|`（ℤ 版，避免除法）。
> 选取规范形后，「函数 ↦ 权重」在**商集**上是单射 ⟹ **(b)** 意义上的可逆成立。
> **规范形不是"锦上添花"，而是 (b) 成立的必要条件**。

### 3.2 为什么 (b) 与 (d) 必须同时标注

`scaleVec_preserves`（既有定理）说的是"缩放不改变语义"。
单看这一条，容易被读成"缩放自由度无害，可逆性不受影响"——
这是**误读**。正确的读法是：

- 缩放自由度**无害** ⟹ **(b)**：语义在**商掉**该自由度后良定义；
- 缩放自由度**存在** ⟹ **(d)**：`compile` 在**原空间**上非单射 ⟹ **严格不可逆**。

两条是**同一条定理**的两个推论。本审计新增 `reversibility_boundary`
与 `no_extractor_preserves_both`
就是把这条**逻辑关系**写进内核，使"可逆"不再是一句口号。

### 3.3 语义层非单射的显式形式

`reversibility_boundary` 与 `no_extractor_preserves_both` 分别从
**符号侧**（两个不同约束语义相同）与**提取器侧**（不存在兼顾两层的提取器）
刻画了不可逆。第三条定理从**权重侧**给出最贴近工程叙述的形式：

```lean
theorem semantic_layer_not_injective :
    ∃ w w' : LinearLayer, w ≠ w' ∧
      (∀ x : List Int, LayerOut w x = 0 ↔ LayerOut w' x = 0) ∧   -- 行为完全一致
      (∃ c, w = convertVec c) ∧ (∃ c, w' = convertVec c)          -- 都是编译产物
```

即：**存在两个不同权重，行为完全一致，且都可由编译得到**。
这正是 doc/01 难点 2 那句「同一函数有**无数**权重实现」的**存在性内核证明**
—— 两个已是内核级事实；"无数"由缩放的自由性（`λ` 遍历 `ℤ∖{0}`，即可数无穷；
ℝ 版 `λ ∈ ℝ∖{0}`，即不可数无穷）在 **同一见证族** 上给出，
本文件未把"无穷"本身形式化（见 §6.9）。

---

## 4. 规范形总表（把 (b) 从口头承诺变成可执行约定）

| 等价自由度 | 出处（定理） | 规范形 | 状态 |
|:--|:--|:--|:--|
| 系数整体缩放 `λ ≠ 0`（ℤ/ℝ，标量/向量） | `scaleVec_preserves`、`real_scale_preserves`、`realVec_scale_preserves` | `‖(a,b)‖ = 1`（ℝ）／`gcd(a) = 1 且首非零元 > 0`（ℤ） | **自由度已证**；**规范形选取未形式化**（本审计建议） |
| 点集闭包（FCA） | `closure_idempotent`、`intent_closure_idempotent`、`formal_concept_iff_closure` | 闭包 `Ol**` / 形式概念 | ✅ **已形式化**（`IsFormalConcept`） |
| 几何平移 + 置换 | `collinear_translate`、`collinear_cyclic`、`collinear_swap` | 平移 + 三点置换的轨道 | **自由度已证**；轨道代表元未形式化 |
| 同余类 | `congruent_refl/_symm/_trans` | `x mod m` | **等价关系已证**；`mod_preserves` 证明体是 `rfl`（**内容弱**） |
| 跨层参数共享 | `sharedChain_eq_iterate` | 单层 `F` | ✅ **已形式化**（`iterate F n` 反演 = 取一层） |
| 投影/闭包算子 | `subspace_proj_idempotent`、`simplex_normalize_fixed`、`sphere_normalize_fixed` | 约束集本身 | ✅ **已形式化**（"可行点 = 不动点"） |
| 归一化的平移 + 缩放 | `normalize_translation_invariant`、`normalize_not_injective` | 零均值超平面 ∩ 单位球面 | **不变量已证**；**规范形不存在**（球面上仍不可区分 ⟹ 严格说无规范形） |
| 位置编码的角周期 | `rotateR_not_injective` | `θ mod 2π` | **反例已证**；规范形未形式化 |
| 正半轴区域 | `relu_injOn_nonneg`、`geluTanh_injOn` | `[0,∞)` | ✅ **已形式化**（区域约束） |
| 加权损失权重 | `weightedN_stationarity_of_components` | 无（`w > 0` 仅是建议） | ⚠️ **未形式化**，且逆向命题**未证** |

---

## 5. 诚实降级清单（本审计发现的问题，**不修改既有文件**，仅登记）

| # | 位置 | 问题 | 性质 | 建议 |
|:--:|:--|:--|:--|:--|
| D-1 | `doc/02-符号训练框架-完整链路架构.md` | 定位"**完整且可逆**的链路"。**语义层可逆已被机器验证为假**（§3.1）。参数层可逆属实 | **文档过度声称**（违反 STYLE §5.4 诚实铁律） | 改为"**参数层完整可逆；语义层可逆仅在同构之上成立，一般情形为等价类意义**" |
| D-2 | `lean/RealExtractInvertibility.lean:41` | docstring 引用 `geluTanh_not_injective` 作"机器验证反例"，**该定理名在本库不存在**（glob 无匹配） | **幽灵定理名**（同 E1 附录 A-3 的 `RealWLRefinement` 问题） | 补定理（用 `geluTanh_zero` + `geluTanh_neg_of_neg` 构造 `0` 的单侧见证）或删引用 |
| D-3 | `lean/RealExtractInvertibility.lean` 全文 | **声称**"`geluTanh` 在全实轴上不是单射（机器验证反例）"，但**实际未给出**该反例的定理——只给了 `geluTanh_neg_of_neg`（负半轴取负值），而 `x < 0 ⟹ geluTanh x < 0` 与单射性**无矛盾**，**不足以证非单射** | **声称与正文脱节**（结论**为真但未证**，见右） | 结论可真，且**已数值定位**：`geluTanh` 在 `x ≈ −0.6392` 处取极小值 `≈ −0.13923`，故在 `(−∞, 0)` 上**先降后升** ⟹ 非单射。数值核验给出显式碰撞对 `geluTanh (−1.1981) = geluTanh (−0.2724) = −0.1`。**正式的机器验证需要极小点处的导数变号论证**（本审计未构造，见 §6.7） |
| D-4 | `lakefile.toml` roots | 审计开始时，**7 个已注册模块文件不存在**：`RealCompileExtractClosed`、`RealNonlinearFidelity`、`RealContractAxioms`、`RealConversionStability`、`RealTokenSymbolLink`、`RealGelfandMathlib`、`RealOverSmoothingSharp` | **基础设施缺陷**：`lake build lattice` **整体立即失败**（STYLE.md:124 已记录）⟹ 任何全量验证都被阻塞。**审计期间已由其他集群补齐**（现均存在，7/7） | ✅ **已消解**（本审计收尾时复核确认）；教训：**roots 与文件的存在性必须作为构建前置断言**，否则任何"全绿"结论都不可信 |
| D-5 | `lean/RealFCAInstance.lean:40-41` | `constraint_entailment_closure` 的证明体是 `rfl`（自标"原 `closure_idempotent` 引用与目标不匹配，已改为 rfl，语义不变"） | **同义反复**：定理名暗示实质内容，实为定义展开（E1 附录 A-8 已记录） | 若要保持内容，需把 `RealConstraintSat` 的蕴含结构与 `RealImplication` 真正接起来 |
| D-6 | `lean/RealFCA.lean:23` | 声称"概念格是**完备格**"，但只证 meet（`:181`）/join（`:227`）**二元**闭合，**未证** `iInf`/`iSup` 完整闭合 | **文档过度声称**（E1 附录 A-4 已记录） | 补 `iInf`/`iSup` 闭合，或降级措辞为"二元 meet/join 闭合格" |
| D-7 | `lean/RealWeightedConstraints*.lean` | 定理三是**单向**（约束满足 ⟹ 加权驻点），**逆命题未证**；且 `w = 0` 时约束被完全忽略，此时**驻点推不出任何约束满足** | **单向命题被当作刻画使用** | 注明单向性；或补 `w > 0` 下的部分逆命题 |
| D-8 | 本审计 | **(d) 反例只在"缩放/平移/周期/零化"四个自由度上机器验证**；**冗余神经元（排列等价）**这一 doc/01 明确列出的自由度，**库内既无定理也无反例**——本文件亦未补（见 §6） | **未做**（诚实标注） | 需先定义"神经元列表的置换作用"，再证"语义不变 + 参数变" |

---

## 6. 未做 / 边界（诚实标注）

1. **冗余神经元（排列等价）未形式化**。doc/01 难点 2 明确列出"排列/缩放等价、**冗余神经元**"三类自由度。
   本审计对**缩放**给出了完整的机器验证（`reversibility_boundary`），对**平移**（`collinear_translate`）、
   **周期**（`rotateR_not_injective`）、**零化**（`relu_not_injective`）给出了既有反例的回收，
   但**排列自由度**（同一函数由不同拓扑/神经元顺序实现的网络表示）在库内**没有任何形式化对象**
   （没有"网络 = 带索引的神经元列表 + 置换作用"的定义）⟹ **本文件不声称覆盖**。
   补齐它需要先引入 `Equiv.Perm` 作用于层结构并证明 `LayerOut` 在置换下不变。
2. **规范形的形式化选取未做**。本文件证的是**规范形存在的必要性**（因非单射），
   **没有**构造 `canonicalize : LinearLayer → LinearLayer` 并证明
   `sem_W (canonicalize l) = sem_W l ∧ canonicalize (canonicalize l) = canonicalize l ∧
   (sem_W l = sem_W l' ⟹ canonicalize l = canonicalize l')`。
   这是把 (b) 从"存在性"升级为"构造性"的下一步。
3. **`RealRoundtripBound` 的误差界未做紧性分析**。`roundtrip_error_bound` 给的是 `≤ ε₁X + ε₂`，
   本审计**未验证**该界是否可达（sharp）。
4. **浮点链路（`RealCompileFloatCorrectness`）只做定性分类**（(c) 行为等价），
   **未逐条枚举**该文件数百个定理的往返性质。
5. **本审计不改任何既有文件**（纪律 8）。上述 D-1…D-8 全部**只登记，不修改**。
6. **`RealInfConvAttain.lean` 等空壳文件**与可逆性无关，未纳入本表。
7. **`geluTanh` 全局非单射的机器验证未做**（D-3）。结论已由数值方法定位
   （极小点 `x ≈ −0.6392`，`geluTanh` 在 `(−∞,0)` 上先降后升；碰撞对
   `−1.1981` 与 `−0.2724` 同像于 `−0.1`），但本文件**没有**把下列任一条写进内核：
   ① `∃ x y, x ≠ y ∧ geluTanh x = geluTanh y`（需中值定理 + 极小点存在性）；
   ② `¬ StrictMonoOn geluTanh (Set.Iic 0)`（需在负半轴找到下降段）。
   可行的机器验证路线：由 `RealActDerivatives.geluTanh_hasDerivAt:165` 取
   `x = −1`、`y = 0`，导出 `geluTanh` 在 `[−1,0]` 上严格递增（导数 `gate + x·gate'` 正）；
   但该单调性只在 `[−1,0]` 上成立，**不足以**给出全局碰撞——真正的碰撞点之一是
   `−1.1981 ∉ [−1,0]`。故需更强的导数分析（在 `−1.1981` 处导数已为负）。
   本审计**如实标注此为上界困难**，不声称已证。
8. **「(a) 真正可逆」的 9 项全部是参数层结论**。本审计**未**在语义层找到任何 (a) 项，
   除 `sigmoid` / `Real.exp`（第 25 行）这类**并非转换层编码**的纯函数实例。
9. **「无数权重实现」中的"无数"未形式化**。`semantic_layer_not_injective` 证的是
   **存在两个**（`∃ w w'`）这样的权重；从"两个"到"无穷多个"需要一个额外的
   构造（对每个 `λ ∈ ℤ∖{0}` 给出 `convertVec (scaleVec revC λ)` 并证两两不同）。
   该构造是**平凡的**（`b` 字段 `λ ↦ λ` 单射），但本文件**未写出**
   —— 因为 doc/01 的原始措辞是"无数"，而内核里已证的是"至少两个"。
   若要把"无数"也写进内核，建议下一轮补
   `infinitely_many_weight_implementations : Set.Infinite {w | ∃ c, w = convertVec c ∧ sem_W w = sem_W (convertVec revC)}`。

---

## 7. 一句话结论

> **`doc/02` 的「完整且可逆」在参数层为真、在语义层为假。**
> 机器验证的边界是 `reversibility_boundary`：
> `convertVec` 单射 **∧** `∃ c ≠ c', sem(c) = sem(c')`；
> 并被 `no_extractor_preserves_both` 强化为**不可能性**：
> **不存在**同时满足参数层往返与语义层同一的提取器。
> 因此"反编译"只能在**商掉缩放/平移/周期/归一化等自由度之后**、即
> **(b) 等价类意义下**可逆；严格意义的可逆在 (d) 的 11 个环节上
> 已被内核证伪。规范形的**存在必要性**已证（且是 (b) 成立的必要条件），
> **构造**尚待形式化。

---
---


---

> **注意 · 附录已分离（B581，2026-10-08）**：本文件原含一个附录
> 「集群 C1 补充 —— 端到端闭环定理的落地与其精确边界」（原 `:303-440`）。
> 该附录已独立为 `28-REVERSIBILITY-C1.md`，理由是它属**另一集群的产出**（原文件因此有 2 个 H1）。
> **本文件的 29 份外部引用中，0 份指向该附录**，故分离无断链风险。
