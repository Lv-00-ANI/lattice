# 语义信息：基础 Primitive 与证明义务（SEMANTICS-MAINLINE）

> **状态**：Lean 侧设计/证明路线，不是完成声明。
> **范围**：语义域、词表编辑、语义编辑、基础 `Primitive`、证明义务。
> **C 全部推迟**：C ABI、序列化、conformance、C runtime 不在本文范围。
> **不提供打包能力**：没有 `VocabEdit`、`SemanticEdit`、`Import`、`PostTrain` 这类入口；只提供基础 `Primitive`，组合由用户完成。

---

## 0. 一句话

**语义信息 = 在某个语义域 `D` 上，模型行为、符号指称、几何标注之间可证明的对应关系。**

库只提供语义相关的**基础调用**：

- 词表-句法编辑：`Primitives/Vocab/*`
- 语义编辑：`Primitives/Semantics/*`
- 语义定律：`Kernel/Semantics/*`

用户自己组合，不存在固定的“语义使用链”。

---

## 1. 范围与不变量

1. **词表-句法编辑与语义编辑分开**；前者可配权重变换，后者没有纯权重变换。
2. **不提供打包能力**；每个操作是独立 `Primitive`。
3. **数据类型与操作分开**：`VocabEdit`、`WeightTransform`、`VocabCompat`、`Annotation`、`SemanticDelta` 是数据/证书；操作在 `Primitives/*`。
4. **没有固定流程**；`extract → align → merge → compile → post-train → edit` 只是示例组合，不是库规定。
5. **每个 `Primitive` 有 `pre/post/sound/strength/coverage/frame`**。
6. **Primitive 之间不互相 import**；只依赖 `Kernel`/`Runtime`/`Domains`。
7. **C 推迟**；当前只做 Lean 语义与证明。

---

## 2. 语义定义

### 2.1 语义域、词表、几何、继承

目标结构（当前实现见 `Lattice/Semantics/Stage1.lean`）：

```lean
structure SemanticDomain where
  Meaning : Type
  equiv   : Meaning → Meaning → Prop

structure Vocab (D : SemanticDomain) where
  Token : Type
  denote : Token → D.Meaning

structure Geometry (D : SemanticDomain) where
  Carrier : Type
  label   : Carrier → D.Meaning

structure Inherits (D) (G : Geometry D) (M : Type) where
  embed  : M → G.Carrier
  sound  : ∀ m x, G.label (embed m x) = behavior m x
  complete : ∀ y : D.Meaning, ∃ m x, G.label (embed m x) = y
```

**关键**：

- `Vocab.denote` 是约定，不是从权重学出来的；
- `Geometry.label` 是标注，不是自动从激活里“读”出来的；
- `Inherits.sound` 是**字段**，必须由实例提供；没有实例就没有继承。

当前实现：

- `SemanticDomain`、`constraintDomain`、`holdsSetMeaning`；
- `Vocab`、`constraintVocab`、`constraintVocab_denote_sound`；
- `Geometry`、`constraintGeometry`；
- `Inherits`、`inherits_sound`、`complete_on`。

### 2.2 两种“完整”

| 完整 | 陈述 | 性质 |
|:--|:--|:--|
| 行为完整 | 给定 `W` 与 `Vocab`，`behavior` 被唯一决定 | 同义反复，没有信息量 |
| 符号完整 | `∀ m ∈ D, ∃ W, behavior W = m` | 非平凡；只对受限语义域 `D` 可能成立 |

本文只承诺**相对 `D` 的符号完整**；不声称“所有 LLM 的语义”。

### 2.3 三种几何

| 几何 | 语义 | 能否证明 |
|:--|:--|:--|
| 约束几何：`{ x | constraints }` | 约束集本身 | 能；`Holds` 就是 `label` |
| 程序几何：AST / 计算图 | 程序指称 | 能；`eval` 定理 |
| 隐空间几何：激活流形/度量 | 解释函数 `label` | 只能条件性；不能证 `label` 本身 |

本文默认前两种；隐空间几何是研究假设。

### 2.4 标注是数据，不是编辑

`Annotation` 只是数据：

```lean
structure Annotation where
  target : Region
  meaning : Meaning
  provenance : Provenance
  priority : Priority
```

**标注不等于编辑。** 语义编辑由四个基础 Primitive 组成：

- `applyDelta`：只改记录/结构；
- `semanticCheck`：检查行为是否实现 meaning；
- `frameCheck`：检查目标外不变；
- `undo`：回滚。

不存在打包的 `Edit` 结构把四件事塞在一起。

---

## 3. 词表-Primitive（句法编辑）

### 3.1 数据与证书

以下都是**类型**，不是打包能力：

```lean
structure VocabEdit (V V' : Vocab D) where
  map  : V.Token → V'.Token
  kind : EditKind   -- perm | rename | add | delete | merge | split

structure WeightTransform (M M' : Model D) where
  apply : M → M'

structure VocabCompat (σ : VocabEdit V V') (T : WeightTransform M M') where
  commutes : ∀ m tokens,
    behavior (T.apply m) (tokens.map σ.map) = behavior m tokens
  exact : Prop      -- 精确；否则 ≈ε
```

实际调用拆在 `Primitives/Vocab/*`。

### 3.2 基础调用

| Primitive | Input | Output | 精确性 |
|:--|:--|:--|:--|
| `vocabCheck` | `Vocab` | `Certificate` | 良构 |
| `tokenMap` | `Vocab × Vocab` | `TokenMap` | 构造映射 |
| `applyTokenMap` | `Model × TokenMap` | `Model` | 取决于 map kind |
| `embeddingPermute` | `Embedding × Equiv` | `Embedding` | 精确 |
| `headPermute` | `OutputHead × Equiv` | `OutputHead` | 精确 |
| `embeddingAdd` | `Embedding × List (Token × Vector)` | `Embedding` | 精确（未使用 token） |
| `embeddingDelete` | `Embedding × List Token` | `Embedding` | 精确（未使用 token） |
| `embeddingMerge` | `Embedding × Token × Token` | `Embedding` | 一般有损 |
| `embeddingSplit` | `Embedding × Token × Token` | `Embedding` | 一般有损 |
| `headMerge` | `OutputHead × Token × Token` | `OutputHead` | 一般有损 |
| `headSplit` | `OutputHead × Token × Token` | `OutputHead` | 一般有损 |
| `vocabCompat` | `Model × TokenMap` | `Certificate` | 行为保持（精确/ε） |
| `vocabError` | `Model × TokenMap` | `ℝ` | merge/split 误差 |

### 3.3 精确性分类

| 编辑 | 权重侧 | 精确性 |
|:--|:--|:--|
| 置换/重命名 | embedding 行、输出头列同步置换 | **精确** |
| 增加未使用 token | 追加行/列 | **精确** |
| 删除未使用 token | 删除行/列 | **精确** |
| 合并 token | embedding/head 合并 | **一般有损**；仅当两者一致时精确 |
| 拆分 token | 复制/分区 embedding/head | **一般有损**；仅当初始分片一致时精确 |
| 改 `denote` | 没有权重变换能保持行为 | **不是词表编辑**；见 §4 |

**当前实现**：`Lattice/Semantics/VocabEdit.lean`。定理 S14–S19 见 §5。

---

## 4. 语义-Primitive（语义编辑）

### 4.1 基础调用

| Primitive | Input | Output | 说明 |
|:--|:--|:--|:--|
| `label` | `Model × Region` | `Meaning` | 读取标注 |
| `inheritsCheck` | `Geometry × Model` | `Certificate` | `label ∘ embed = behavior` |
| `denoteCheck` | `Vocab × Token × Meaning` | `Certificate` | token 含义一致 |
| `annotate` | `Model × Meaning` | `Annotation` | 创建标注 |
| `applyDelta` | `Model × SemanticDelta` | `Model` | **只改记录/结构** |
| `semanticCheck` | `Model × Meaning` | `Certificate` | 行为是否实现 meaning |
| `frameCheck` | `Model × SemanticDelta` | `Certificate` | 目标外不变 |
| `undo` | `Model × EditRecord` | `Model` | 回滚 |
| `meaningUnion` | `List Meaning` | `Meaning` | 合取/并集 |
| `semanticDiff` | `Model × Model` | `List SemanticDelta` | 差异 |
| `conflictDetect` | `ConstraintSet` | `List Conflict` | 冲突 |
| `conflictResolve` | `List Conflict × Priority` | `MergeRecord` | 裁决 |

### 4.2 `SemanticDelta`

```lean
inductive SemanticDelta where
  | addConstraint    : Constraint → SemanticDelta
  | removeConstraint : Constraint → SemanticDelta
  | replaceConstraint: Constraint → Constraint → SemanticDelta
  | redefineDenote   : Token → Meaning → SemanticDelta
  | relabel          : Region → Meaning → SemanticDelta
  | annotate         : Meaning → SemanticDelta
```

### 4.3 `applyDelta` 的诚实契约

```lean
pre  (m, δ) := δ.wellFormed ∧ compatible m δ
post (m, δ) m' :=
  m'.record = m.record ++ [δ]
  ∧ frame m m' δ
  -- 不保证 behavior m' 实现 δ.meaning
```

**`applyDelta` 不保证语义已实现**；实现由用户组合 Train/Repair 完成，再用 `semanticCheck` 验证。

### 4.4 `redefineDenote` 没有纯权重变换

- 改 `denote` 不是 embedding/head 的置换或合并；
- 没有 `WeightTransform` 能保持行为；
- 必须走：

```lean
m1 := applyDelta (m, SemanticDelta.redefineDenote tok newMeaning)?;
m2 := iterate 100 (trainStep loss) m1?;        -- 用户组合 Train
-- 或 iterate 10 (repairApply op) m1?          -- 用户组合 Repair
ok := semanticCheck (m2, newMeaning)?;
fr := frameCheck (m1, delta)?;
```

库不提供 `semanticEdit` 打包流程。

**当前实现**：`Lattice/Semantics/Annotations.lean`、`Lattice/Semantics/Merge.lean`；S4–S8 见 §5。

---

## 5. 证明义务 S1–S20

| ID | 义务 | 状态 | 落点 |
|:--|:--|:--|:--|
| S0 | `SemanticDomain` / `Meaning` | 已闭合 | `Semantics/Stage1.lean` |
| S1 | `vocab_denote_sound`（阶段 1 形式） | 已闭合 | `Stage1.lean` `constraintVocab_denote_sound` |
| S2 | `complete_on D` | 已闭合（相对 `D`） | `Stage1.lean` `complete_on` |
| S3 | `geometry_inherits` / `inherits_sound` | 已闭合 | `Stage1.lean` |
| S4 | `annotation_realizes` | 已闭合 | `Annotations.lean` |
| S5 | `edit_frame` | 已闭合 | `Annotations.lean` |
| S6 | `edit_reversible` | 已闭合 | `Annotations.lean` |
| S7 | `edit_idempotent` / `conflict_free` | 部分：idempotence 有；冲突自由在 S8 | `Annotations.lean`、`Merge.lean` |
| S8 | `merge_sound` / 冲突可检测 | 已闭合（多专家可组合） | `Merge.lean` |
| S9 | `compile_sound` | **未做** | 待 `Primitives/Compile` |
| S10 | `post_train_preserves` | **未做** | 待 `Primitives/Train` |
| S11 | `program_representation_roundtrip` | 已闭合 | `Lift/ProgramAST.lean` |
| S12 | `transformer_eval` | 已闭合 | `Lib/Architectures/RealTransformerEval.lean` |
| S13 | `float_refinement` | 已闭合（Lean 侧） | `Lib/FloatStackRefinement.lean` |
| S14 | `vocab_edit_permutation_exact` | 已闭合 | `VocabEdit.lean` |
| S15 | `vocab_edit_add_unused_exact` | 已闭合 | `VocabEdit.lean` |
| S16 | `merge_error_bound` + `merge_not_exact` | 已闭合 | `VocabEdit.lean` |
| S17 | `split_error_bound` | 已闭合 | `VocabEdit.lean` |
| S18 | `vocab_compat_permutation` | 已闭合 | `VocabEdit.lean` |
| S19 | `vocab_edit_reversible` | 已闭合 | `VocabEdit.lean` |
| S20 | `vocab_align_merge_sound` | **被阻塞** | 见 §5.1 |

### 5.1 S20 为什么被阻塞

S20 说“多专家对齐后 `MergeSound` 保持”。但 `MergeSound`（`Semantics/Merge.lean`）里**没有词表类型 `V`**：它只谈 `GeoConstraint` 与配置 `pts`。

所以只有两种可能：

1. **空**：`MergeSound` 不提 `V`，自然对词表编辑不变——那是重言；
2. **需要桥**：把
   `VocabModel.behavior : V → V → ℝ`（标量 logit）
   与
   `GeoConstraint.Holds : (ℕ → Pt n) → Prop`（配置谓词）
   连起来。

这条桥在库里不存在；它正是“符号 ⇄ 权重”那一跳。S20 的前置是：

| 缺什么 | 在哪 |
|:--|:--|
| 模型级 `behavior` 与约束级 `Holds` 的对应 | 需要 `Inherits` 在模型层实例化 |
| `Embedding`/`OutputHead` 到配置空间的解码 | `VocabEdit.lean` 只有 logit |
| 对应要能承载 `HoldsSet` | `HoldsSet` 目前只在 `GeoConstraint` 上 |

已做的替代：`Merge.lean` 的 `merge_sound_cons` / `merge_sound_append_experts` / `merge_sound_add_global`，以及否定侧 `merge_sound_not_composable`。

---

## 6. 示例组合（不是库流程）

### 6.1 词表置换

```lean
m  := importWeights?          -- 用户组合 base primitives
σ  := tokenMap (v1, v2)?;
m1 := applyTokenMap (m, σ)?;
c  := vocabCompat (m1, σ)?;
```

### 6.2 词表 merge（有损）

```lean
σ  := tokenMapMerge (v, t1, t2)?;
m1 := applyTokenMap (m, σ)?;
e  := vocabError (m1, σ)?;
c  := vocabCompat (m1, σ)?;   -- 只到 ε
```

### 6.3 语义 redefinition

```lean
d  := SemanticDelta.redefineDenote tok newMeaning;
m1 := applyDelta (m, d)?;
m2 := iterate 100 (trainStep loss) m1?;   -- 或 Repair
ok := semanticCheck (m2, newMeaning)?;
fr := frameCheck (m1, d)?;
m3 := undo (m2, record)?;
```

### 6.4 导入 vs 构造（两个入口，不是两步）

```lean
-- 入口 A：导入已有权重
m := bindVocab (weightsCheck w?, v)?;

-- 入口 B：从规格构造
p := synthesize (specCheck s?)?;
m := programAssemble (p, v)?;
```

**没有规定必须 Import 再 Extract 再 …；用户任意组合。**

---

## 7. 当前实现与目标目录

| 当前 | 目标 |
|:--|:--|
| `Semantics/Stage1.lean` | `Kernel/Semantics/*` |
| `Semantics/VocabEdit.lean` | `Primitives/Vocab/*` |
| `Semantics/Annotations.lean` | `Primitives/Semantics/*` |
| `Semantics/Merge.lean` | `Primitives/Merge/*` + `Primitives/Semantics/Conflict*` |
| `Lift/ProgramAST.lean` | `Runtime/Program.lean`（S11） |
| `Lib/Architectures/RealTransformerEval.lean` | `Domains/Transformer/Eval.lean`（S12） |
| `Lib/FloatStackRefinement.lean` | `Runtime/Float.lean`（S13） |

迁移时保留旧路径别名；不改声明名。

---

## 8. 非目标与非声称

- **不提供打包的语义能力**：没有 `VocabEdit`、`SemanticEdit`、`Edit` 入口。
- **不规定固定流程**：`extract → align → merge → compile → post-train → edit` 只是示例。
- **不声称** 任意词表编辑精确：置换/未用增删精确；merge/split 有损；改 `denote` 不是权重变换。
- **不声称** 隐空间几何自动继承语义。
- **不声称** 标注即编辑：标注是数据，编辑由 `applyDelta + semanticCheck + frameCheck + undo` 组成。
- **不声称** 所有 LLM 的语义完整；只对显式 `D` 声称。
- **不做 C**：C 全部推迟到 Lean 完成后。

---

## 9. 与目录设计的关系

- `Kernel/Semantics`：类型与定律（S0–S3、S11–S13 的语义基础）。
- `Primitives/Vocab`：S14–S19 的实际操作。
- `Primitives/Semantics`：S4–S8、S20 的实际操作与检查。
- `Compose`：只提供 `compose / parallel / choice / optional / iterate`；语义编辑的组合由用户写。
- 不存在 `Lattice/Semantics` 这样的打包能力目录；`Semantics` 只是 `Kernel/Semantics` + `Primitives/{Vocab,Semantics}`。

---

## 10. 执行顺序（Lean-only）

1. **P0**：`Kernel/Semantics` 类型；`Primitives/Vocab` 的 `tokenMap/applyTokenMap/vocabCompat` 骨架；`Primitives/Semantics` 的 `annotate/applyDelta/semanticCheck/frameCheck/undo` 骨架。不注册没有 `sound` 的 Primitive。
2. **P1**：S14–S19 拆到 `Primitives/Vocab`；S4–S8 拆到 `Primitives/Semantics`；S0–S3 留 `Kernel/Semantics`；补 S9/S10。
3. **P2**：S11–S13 接进 `Runtime`/`Domains`；S20 的桥放 `Kernel/Semantics`，不要塞进 `Primitives/Merge`。
4. **P3**：旧路径别名、`PROOF-DEBT` 路径映射、`Compose/Matrix` 覆盖语义组合。
5. **P4**：`THEOREM-INDEX` 语义部分；全量构建与检查。
6. **C**：不做，等 Lean 完成。

---

## 11. 一句话总结

**语义信息是“在显式语义域上，行为、符号、几何三者可证明的对应”，不是“权重里藏着可读出的意义”。**
**词表-句法编辑可配权重变换；语义编辑没有纯权重变换，必须由用户组合 `applyDelta + Train/Repair + semanticCheck + frameCheck + undo`。**
**库只提供 `Primitives/Vocab` 与 `Primitives/Semantics` 的基础调用；不存在打包的 `VocabEdit` / `SemanticEdit`，也没有固定的语义使用链。**
