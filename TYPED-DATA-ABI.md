# 类型化数据 ABI —— 已登记，暂缓执行

> **状态**：**登记，未实施。**
> **触发条件**：用户 2026-10-29 指示「然后你继续数学工作，等不知道干什么了再做这个，这个落文件就行」。
> **本文件的作用**：把这项工作的**范围、依据、代价、为什么现在不做**写清楚，使它不会因为被推迟而丢失，
> 也不会因为被口头传述而失真。

---

## 一、要做什么

把 C 契约从**名字表**升级成**类型化数据 ABI**：

1. **重写 `CFunction.args`**：每个 primitive 的参数表带**真实数据类型**——
   `f64` 数组（带长度）、`i64` 句柄、`shape`/`stride`，而不是现在的 `[cstr, size, size]`。
2. **`Conformance` 的 22 条向量改成真实 ABI 调用**：输入/输出**缓冲区**，
   而不是现在的 `List Float` + `Float` 公式。
3. **然后**才谈得上「arity/类型桥」与「C 实现与 Lean 语义一致」。

## 二、为什么现在做不了（三条已证的阻碍）

这不是"没时间"，是**当前结构下三条已经证明的阻碍**：

### ① `Primitive` 没有 arity 字段

`Lattice/Compose/Primitive.lean` L26：

```lean
structure Primitive (I O : Type) where
  pre : I → Prop
  post : I → O → Prop
  run : I → Option O
  sound : ∀ x, pre x → ∃ y, run x = some y ∧ post x y
  strength : Strength
  coverage : Coverage
  frame : I → O → Prop
```

`I` 是**类型**，不是参数表。**「C 侧 arity = `Primitive` 的 arity」连陈述都写不出来。**
见 `Lattice/CInterface/ContractBoundary.lean` ①。

### ② 对照向量不对应 `Primitive.I`（有反例）

`descentStep` 是 `(c : ℝ) (pts : ℕ → Pt 1) : Primitive ℝ ℝ` —— **`I` 是单个 `ℝ`**，
而它的两条向量各有 **3** 个 `Float` 输入（喂 `fStep : Float → Float → Float → Float`）。
**3 ≠ 1**，见 `descentStep_vector_width_ne_primitive_width`。

### ③ ABI 参数里没有数据参数（有反例）

`compose` 的 ABI 参数是 `[cstr, size, size]`——**两个缓冲描述符 + 一个长度**，
它的数学输入（两个 `Primitive`）**不在任何参数位上**。
见 `composeArgs_has_no_data_parameter` 与 `abiTable_compose_args`。

### ④ 类型级不兼容（第 56 轮，最强的一条）

`inputs : List Float` 只能落到 `CType.f64` 参数位。实测 `f64` 槽位数与向量输入数：

| primitive | `f64` 槽 | 向量输入 | |
|:--|--:|--:|:--|
| `compose` / `composeWith` / `identity` / `iterate` / `parallel` / `choice` / `optional` | **0** | 1–2 | ❌ 无槽 |
| `applySgd` | 2 | 3 | ❌ 不足 |
| `applyMomentum` | 3 | 5 | ❌ 不足 |
| `applyAdam` | 4 | 5 | ❌ 不足 |
| `descentStep` | 3 | 3 | ⚠ 恰好（**巧合**，其第 4 个参数是 `size`） |

**11 个里 10 个不兼容；7 个连一个 `Float` 槽都没有。**
见 `seven_primitives_float_inputs_have_no_f64_slot` 与 `three_primitives_have_too_few_f64_slots`。

⇒ **「把向量改成真实 ABI 调用」不是改写法，是重新设计两侧的表示。**
**而 `Primitive` 侧无 arity 概念这件事，重写 `CFunction.args` 也解决不了** ——
它解决的是 ③④，**解决不了 ①**。

## 三、代价（用户给出的估计，本文件照录并补注）

| 项 | 用户估计 | 补注 |
|:--|:--|:--|
| `ABI` 的 11 条 | **全部重写** | `abiTable`、`CType`（要加数组/句柄/stride 构造子）、`CFunction` 字段 |
| `Conformance` 的 22 条向量 | **全部重写** | 从 `List Float`+`Float` 公式改成缓冲区；`fStep`/`fSgd`/… 那 11 个 `Float` 模型要么保留为**第二套**、要么删除 |
| `ContractBoundary` 的 ③ | **全部重写** | `composeArgs_has_no_data_parameter`、`abiTable_compose_args`、`exists_abi_entry_without_data_parameter`、`seven_primitives_*`、`three_primitives_*` |
| （本文件补） | — | **`check_cinterface_abi.py`** 的 `abiTable` 名字抽取正则；**`Conformance.lean` 的 7 条定理**（`conformance_length` = 22 等） |

**总规模粗略估计**：**1–2 周**（Lean 侧），**不含 C 实现**。

## 四、为什么值得做（不是可有可无）

- **C 侧要真正实现数学，就必须有数据参数**。现在的 ABI 只传「哪块内存 + 多长」，
  **C 拿不到任何 `f64` 数据**，所以「C 实现与 Lean 语义一致」这句话**无从验证**。
- **它把 `P3-05`（conformance arity/type 对齐）从"规格决定"变成"可执行任务"**：
  现在的问题是「这些向量是 ABI 调用向量还是公式向量」——**类型化数据 ABI 直接回答它**。
- **它与第 59–60 轮的成果叠加**：`Representation ConstraintSet Layer` 已经把 L2⇄L3 的往返与语义接上，
  **下一步自然是让那套语义能被 C 侧执行**。

## 五、执行顺序（真要做的时候）

1. **先定 `CType`**：加 `f64Array`（带长度）、`i64Handle`、`shape`/`stride` 三个构造子，
   **并证明 `CType` 的规模与既有 11 条不变式不变**；
2. **重写 `abiTable`**，**每改一条就跑一次 `check_cinterface_abi`**（它会立刻抓到名字漂移）；
3. **`ContractBoundary` 的 ③ 全部删掉重写**——它们断言的是**旧** ABI 的事实，
   新 ABI 下那些反例**不再成立**（这正是它们该被删的理由：**它们记录的是一个已消失的状态**）；
4. **`Conformance` 重写**，**保留 22 条的数量**（`conformance_length = 22` 是既有门禁），
   **但把 `inputs`/`expected` 改成缓冲区描述**；
5. **补一条新定理**：`∀ v ∈ conformance, fieldTypes v ⊆ argsTypes (abiTable)`
   —— **这才是「arity/类型桥」的真身**，而它的可证性**依赖**上面四步。

## 六、不做的时候，这些边界仍然**可查**

**本文件登记的一切，当前都已经被机器检查**：

- ①、③：`Lattice/CInterface/ContractBoundary.lean` 的 5 条定理；
- ④：`seven_primitives_float_inputs_have_no_f64_slot`、`three_primitives_have_too_few_f64_slots`；
- 名字桥：`ABI.abiTable_names_eq_verified`（第 55 轮，接 `Compose.primitiveNames`，后者对**环境**检查过）。

⇒ **推迟不会让这些边界变成"未记录"。** 它们**已经被证明**，只是**尚未被消除**。
