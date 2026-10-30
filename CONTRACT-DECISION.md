# CONTRACT-DECISION.md — C 契约路线的**决定**

> **一句话决定：C 桥的 ABI 对应在当前 `Primitive` 结构下【不可陈述】，所以它不是「未做」，是「做不了」。
> 要让它是定理，必须先给 `Primitive` 加参数表；不给，就只能把它标为未验证假设。**

---

## 一、现状（第 103 轮实测）

| 项 | 实测 |
|:--|:--|
| `CInterface/` 自 `44436a4` 起 diff | **0** |
| C 代码 | **0 行** |
| `CFunction.args` 的类型 | **`List CType`——已经带类型** |
| `Primitive` 的实例 | **7 个直接 `where` 块** + 6 个组合子 |
| `WordEncoder` | 定义在 `CInterface/LayoutBytes.lean`，**无实例** |
| ABI 条目 / SEMANTICS 条目 | **11 / 12** |

**⚠ 第一条要纠正的直觉**：`args` 不是「没有类型」，**它是 `List CType`，而 `CType` 是 `f64`/`size` 这类枚举。**
**所以「typed-data ABI」不是「加类型」，是「加【结构】」**——缓冲描述符、长度、以及它们的**依赖关系**
（`size` 必须等于某个缓冲的长度）。

---

## 二、四条已证的阻碍，以及哪一条是根

`TYPED-DATA-ABI.md` §二 列了四条，**它们不是并列的**：

| # | 阻碍 | 已证于 | 能否靠改 `args` 解决 |
|:--|:--|:--|:--|
| ① | **`Primitive` 没有 arity 字段**（`I` 是类型，不是参数表） | `ContractBoundary` ① | ❌ **不能** |
| ② | 对照向量不对应 `Primitive.I`（`descentStep` 是 `ℝ`，向量有 3 个 `Float`） | `descentStep_vector_width_ne_primitive_width` | ❌ |
| ③ | ABI 参数里没有数据参数（`compose` 的 `args = [cstr, size, size]`） | `composeArgs_has_no_data_parameter` | ✅ |
| ④ | 类型级不兼容（10/11 个原语的 `f64` 槽不足） | `seven_primitives_float_inputs_have_no_f64_slot`、`three_primitives_have_too_few_f64_slots` | ✅ |

**⇒ ①是根，②是①的下游，③④是表层。** **而 `TYPED-DATA-ABI.md` §二 末尾已经写明了这一点：**

> 「而 `Primitive` 侧无 arity 概念这件事，重写 `CFunction.args` 也解决不了 —— 它解决的是 ③④，**解决不了 ①**。」

**本文件把这个判断升格为决定，并给出两条路。**

---

## 三、两条路

### 路 A：给 `Primitive` 加参数表

```lean
structure Primitive (I O : Type) where
  ...（现有七个字段不变）
  /-- **C 侧的参数形状**：arity 与逐位类型。 -/
  arity : ℕ
  paramTypes : Fin arity → CType
```

**收益**：**「ABI 的 `args` 与 `Primitive` 的参数表一致」变成一条【可陈述、可证明】的命题**——
`args = (List.ofFn p.paramTypes) ++ [CType.size]` 之类。**那是 ③④ 的统一解，也是让 C 桥进入证明链的唯一入口。**

**代价（实测）**：
- **7 个直接实例**（`identity`、`descentStep`、`descentStepCol`、`applySgd`、`applyMomentum`、`applyAdam`、`blocked`）
  各加两行；
- **6 个组合子**（`compose`、`composeWith`、`parallel`、`choice`、`optional`、`iterate`）**要算 arity 的传递规则**
  （`compose` 的 arity 是两个子原语的 arity 之和？**不一定**——`compose` 的 C 签名只传缓冲，不传子原语的参数）。
- ⚠ **最贵的一条**：**加了字段之后，`Primitive` 的每个 `def`/`theorem` 里凡是【构造】`Primitive` 的地方都要填**，
  **而 `Laws.lean` / `AssocLaws.lean` / `Iterate.lean` 里的组合子会全部受影响。** **这是架构级改动。**

### 路 B：C 侧不透明，ABI 对应**记为假设**

**不改 `Primitive`，`CInterface/` 只声明 ABI 表与错误码，不声明它与 `Primitive` 的对应。**
**「C 实现在语义上等于 Lean 侧 `Primitive`」这条写成一条 `opaque`/`axiom` 级别的**声明**，
**或者干脆不写，只在文档里标为「未验证」。**

**收益**：**零改动、零风险，且符合项目定位（「不实现引擎、模型和训练框架」）**——**它把 C 侧彻底推给实现者。**
**代价**：**C 桥永远在证明链外。** **`e2e_sound` 的终点只能到 Lean 侧的 `Primitive`，到不了 C。**

---

## 四、决定

> **选 B（C 侧不透明），并把「ABI 对应未验证」作为一条【登记的边界】写进 `PROOF-DEBT.md`，而不是留白。**

**理由三条，按权重排：**

1. **路 A 是架构级改动，而它的收益只到「ABI 对应可陈述」**——**不解决②之前**，
   **即使 `args` 与 `paramTypes` 对上了，`Primitive.I` 与「对照向量的 3 个 `Float`」之间的对应仍然不存在。**
   **所以路 A 需要与②一起做，而那意味着也改 `Primitive.I` 的表示**——**即重新设计 `Primitive` 的输入类型。**
   **那是重写 `Compose` 层，不是加字段。**
2. **项目定位明确不实现引擎**：C 侧是「引擎」一侧。**把它的正确性作为假设外置，比在 Lean 里建模它更符合定位。**
3. **当前 0 行 C 代码**：**在没有实现者的情况下先做路 A，是在为不存在的消费者付费。**

**⇒ 所以本文件【不】执行路 A，【也】【不】留下空白：它把这件事登记为一条已知边界。**

---

## 五、登记的内容（要写进 `PROOF-DEBT.md`）

| 边界 | 内容 | 状态 |
|:--|:--|:--|
| **B-1** | **`CFunction` 表与 `Primitive` 之间的 ABI 对应未验证** | **未验证假设** |
| **B-2** | C 实现的语义等价性未验证 | **未验证假设** |
| **B-3** | `WordEncoder` 无实例 | **未实现** |
| **B-4** | ABI 11 条 vs SEMANTICS 12 条 | **数量不一致，已证不可桥接** |

**而「它为什么不可验证」的四条证明保留在 `ContractBoundary.lean` 里**——
**那是【负结果】，而负结果是这条边界的证据，不是缺陷。**

---

## 六、什么时候应该改选路 A

**触发条件（任一条成立）：**

1. **真的开始写 C 代码**——那时 ABI 对应从「没人消费」变成「有人消费」，**投资才有回报**；
2. **`Primitive.I` 被重新设计**（例如为了 `P2-02` 的参数空间）——**那时 arity 可以顺带加，边际成本下降**；
3. **出现一个需要「Lean 侧证明 ⇒ C 侧行为」的外部消费者**（例如编译器验证）。

**在此之前，路 B 是唯一诚实的选项**，**而它的诚实性依赖于把边界【写下来】——这正是第五节要做的。**
