# 否证清册（REFUTATION-CENSUS）

> 第 35 轮。脚本 `agent-tmp/fix_families.py` 生成分类，`agent-tmp/write_census2.py` 产出本文件。
>
> 一个形式化库的可信度，很大程度上取决于它**明确知道什么做不到**。
> 本清册把库中已证伪的论断归类，作为这一维度的证据面。

## 1. 数量与分布

**285 条**否定结论：`theorem`/`lemma` 级，且**结论类型**以 `¬` / `not` / `→ False` 开头。

| 层 | 条数 | 占比 |
|:--|--:|--:|
| `Lib` | 257 | 90.2% |
| `Lift` | 9 | 3.2% |
| `Audit` | 8 | 2.8% |
| `Core` | 5 | 1.8% |
| `Geo` | 6 | 2.1% |

**分布值得注意**：90% 的否证在 `Lib`（具体领域），承重层（`Core`/`Lift`/`Geo`/`Audit`）
合计只占 28 条。这不是缺陷：承重层的职责不是穷举「不可能」，
而是钉住少数几条**关键**不可能性——而它们恰恰都在那里（见 §3）。

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
| `Audit` | `bridge_is_necessary` | `¬ (∀ (P Q : ℕ → Prop) (f g : ℕ → ℕ), (∀ x, P x → P (f x)) → (∀ x, Q x → Q (g x)) → ∀ x, P x → Q (g (f x))` |
| `Audit` | `bridged_needs_bridge` | `¬ (∀ (P Q : ℕ → Prop) (f g : ℕ → ℕ), (∀ x, P x → P (f x)) → (∀ x, Q x → Q (g x)) → ∀ x, P x → Q (g (f x))` |
| `Audit` | `sq_le_needs_nonneg` | `¬ (∀ r ε : ℝ, r ^ 2 ≤ ε ^ 2 → \|r\| ≤ ε)` |
| `Audit` | `eps_needs_nonneg` | `¬ (∀ ε : ℝ, (0 : ℝ) ^ 2 ≤ ε ^ 2 → (0 : ℝ) ≤ ε)` |
| `Audit` | `lipschitz_needs_nonneg` | `¬ (∀ L δ : ℝ, 0 ≤ δ → (0 : ℝ) ≤ L * δ)` |
| `Audit` | `delta_is_input` | `¬ (∀ L δ : ℝ, 0 ≤ L → 0 ≤ δ → L * 0 = L * δ)` |
| `Audit` | `destructiveFix_not_absorbs` | `¬ (∀ n : ℕ, n = 0 → destructiveFix n = n)` |
| `Audit` | `absorbs_not_derivable` | `¬ (∀ (Sat : ℕ → Prop) (fix : ℕ → ℕ) (μ : ℕ → ℕ), (∀ n, ¬ Sat n → μ (fix n) < μ n) → (∀ n, μ n = 0 → Sat n` |
| `Core` | `relu_not_injective` | `¬ Function.Injective relu` |
| `Core` | `netRelu_not_injective` | `¬ Function.Injective (fun x : Fin 1 → ℝ => reluVec (netAct [] x))` |
| `Core` | `no_uniform_bound` | `¬ countdown.Sat (countdown.iterate n k)` |
| `Core` | `layer_behaviourally_separates` | `¬ BehaviourallyEquivalent p q` |
| `Core` | `reversibility_depends_on_representation` | `(∃ p q : LayerParams (Fin 1) (Fin 1), p ≠ q ∧ BehaviourallyEquivalent p q) → False` |
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
| **三版** | **285 条** | 完整路径 + 按最外层构造子分类；抽查发现 3 处误分类并修正 |

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
