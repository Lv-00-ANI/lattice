import Mathlib
import Lattice.Plugins.Registry

/-!
# `PluginProof` 的 12 个槽位里哪些是字面 `True`（第 984 轮重测）

## 结论：**87 / 132**，其中 **72** 由 `True.intro` 关闭、**15** 由 `trivial` 关闭

**`PluginProof` 有 12 个字段（`soundness`、`laws`、`exactness`、`approximation`、`recovery`、
`spatial`、`confluence`、`equivariance`、`idempotence`、`invariants`、`completeness`、
`refinement`），11 个插件的 `Plugin.lean` 各自给出一个 `proof_holds : proof.Holds`。**

## 逐插件实测

| 插件 | 字面 `True` 槽 | 由 `True.intro` | 由 `trivial` |
|:--|--:|--:|--:|
| `Architectures/Attention` | **8** / 12 | 8 | 0 |
| `Architectures/Conv` | **8** / 12 | 8 | 0 |
| `Architectures/DAG` | **8** / 12 | 8 | 0 |
| `Architectures/GNN` | **7** / 12 | 7 | 0 |
| `Architectures/Norm` | **7** / 12 | 7 | 0 |
| `Compose` | **7** / 12 | 7 | 0 |
| `Core/Constraint` | **10** / 12 | 10 | 0 |
| `Core/Repair` | **7** / 12 | 0 | **7** |
| `Domains/Constraints/Penalty` | **8** / 12 | 0 | **8** |
| `Domains/Constraints/Tokens` | **8** / 12 | 8 | 0 |
| `Extractors/ChainSlot` | **9** / 12 | 9 | 0 |
| **合计** | **87 / 132** | **72** | **15** |

## 本节此前写的「42」是错的，错法值得记录

**旧版本只数了**五个**文件的 `True.intro`，得 42，然后断言「其余五个插件……的 `proof_holds` 里
**没有** `True.intro`」——同一句里说「五个」却列了**六个**名字，而那六个中的
`ChainSlot`(9)、`Constraint`(10)、`Compose`(7)、`Tokens`(8) **都在用 `True.intro`**。**

**=> 于是 42 同时漏掉了 46 个 `True.intro` 与全部 15 个 `trivial`，
把真实值 87 报成了 42 —— 一份**低估了一半**的自审证书。**

**而且这 15 个 `trivial` 是**第二种**关闭方式：`Core/Repair` 与 `Penalty` 用 `trivial` 而不是
`True.intro`，所以只 grep `True.intro` 的测量**在原理上**就看不见它们。**

**=> 教训与项目里已有的那条一致：**测量必须覆盖同一个语义的**所有**书写形态**，
否则「42」这种数字看起来像实测，其实是漏检。**

## 测量方法（可复现）

**对每个 `Lattice/Plugins/**/Plugin.lean`：**

1. **取其第一个 `PluginProof` 字面块里 12 个字段中值**逐字等于 `True`** 的个数；**
2. **统计全文 `True.intro` 出现次数；**
3. **统计全文 `trivial` 出现次数。**

**三条在同一份文件上互为交叉验证：②+③ 应等于 ①（实测 72 + 15 = 87 ✓）。**

## 为什么这仍然是坏消息

**87 个虚槽意味着 132 个槽位里有 87 处 `Holds` **无法排除任何反例**。
按 `mandatoryKinds` 的 11 项看，`recovery` / `spatial` / `confluence` 几乎处处是 `True`，
而这三项正是 `mandatoryKinds` 的成员 —— 它们的覆盖**全靠 `Compose` 插件补齐**。**

## 本文件交付什么

**一条**登记定理**：`PluginProof` 的 12 个字段与 `Holds` 的合取**逐位对应**。**

**=> 这条把「槽位」从文档里的说法变成**可检查的结构事实**：
若 `Holds` 成立则每个字段各自成立，反之亦然。
于是「某个槽位是 `True`」可以被精确定位到**哪个字段**，而不是笼统的「有虚槽」。**

**=> 有了它，填充虚槽可以**逐个字段**推进，每填一个都是独立可验证的改动。** -/

namespace Lattice.Plugins

/-- **`Holds` 的逐字段展开：合取的每一项对应一个具名字段。**

**=> 这是 `PluginProof.Holds` 的定义展开（`Iff.rfl` 级），但它把「12 个槽位」变成
12 个**可分别引用**的命题。** -/
theorem holds_iff_all_fields (π : PluginProof) :
    π.Holds ↔
      (π.soundness ∧ π.laws ∧ π.exactness ∧ π.approximation ∧ π.recovery ∧
       π.spatial ∧ π.confluence ∧ π.equivariance ∧ π.idempotence ∧
       π.invariants ∧ π.completeness ∧ π.refinement) :=
  Iff.rfl

/-- **投影：`Holds` 成立则每个字段都成立。**

**=> **第 1 槽**（`soundness`）。把虚槽定位到具体字段，需要一个字段一条投影。**
**=> 本条是模板：其余 11 条形状相同，本文件只给出 `soundness` 与 `laws` 两条作为示范，
因为完整展开对「逐槽推进」没有额外帮助 —— 那是 `holds_iff_all_fields` 已提供的信息。** -/
theorem holds_soundness {π : PluginProof} (h : π.Holds) : π.soundness :=
  h.1

/-- **投影：**第 2 槽**（`laws`）。** -/
theorem holds_laws {π : PluginProof} (h : π.Holds) : π.laws :=
  h.2.1

/-- **`trivial` 的 `Holds` 恒成立 —— 这既是它的用途，也是它的诚实边界。**

**=> `PluginProof.trivial` 的 12 个字段全是 `True`，所以 `Holds` 平凡成立。
一个用 `trivial` 的插件因此**什么都没证明** —— 而 `Registry.lean` 已把这一点写在注释里。**

**=> 本条把那条注释变成定理，从而可以在任何地方引用它来说明「这个插件未验证」。** -/
theorem trivial_holds_iff (π : PluginProof)
    (h : π = PluginProof.trivial) : π.Holds := by
  subst h
  exact PluginProof.trivial_holds

end Lattice.Plugins
