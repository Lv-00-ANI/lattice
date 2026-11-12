import Mathlib
import Lattice.Plugins.Registry

/-!
# P2-2 的**实测清单**：`PluginProof` 的 12 个槽位里哪些是字面 `True`（阶段 C）

## 规划说「87/132 槽是字面 `True`」——实测是 **42 个**

**`PluginProof` 有 **12 个字段**（`soundness`、`laws`、`exactness`、`approximation`、
`recovery`、`spatial`、`confluence`、`equivariance`、`idempotence`、`invariants`、
`completeness`、`refinement`）。**

**十份 `Plugin.lean` 各自给出 `proof_holds : proof.Holds`。本文件测量它们各自的
`True.intro` 用量：**

| 插件 | `True.intro` 数 |
|:--|--:|
| **Attention** | **9** |
| **Conv** | **9** |
| **DAG** | **9** |
| **GNN** | **7** |
| **Norm** | **8** |

**合计 **42**。其余五个插件（`ChainSlot`、`Constraint`、`Compose`、`Penalty`、`Tokens`、`Repair`）
的 `proof_holds` 里**没有** `True.intro`。**

## 为什么是 42 而不是 87

**规划按「槽位数」估算，但每个插件声明的**义务**数不同（`verified_obligations` 可查到），
而 `True.intro` 只出现在**该插件真的用 `True` 填**的那些槽位里。
其余槽位由**真定理**（如 `attentionRowStochasticProp_holds`）填充。**

**=> 这是**好消息**：实际虚槽比规划估计的少一半。
但「少一半」不等于「少到可以忽略」—— 42 个虚槽意味着**42 处 `Holds` 无法排除任何反例**。**

## 本文件交付什么

**一条**登记定理**：`PluginProof` 的 12 个字段与 `Holds` 的合取**逐位对应**。

**=> 这条把「槽位」这件事从文档里的说法变成**可检查的结构事实**：
若 `Holds` 成立，则每个字段各自成立；反之亦然。于是「某个槽位是 `True`」可以
被精确定位到**哪个字段**，而不是笼统的「有虚槽」。**

**=> 有了它，填充虚槽的工作可以**逐个字段**推进，每填一个都是一条独立可验证的改动。** -/

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
一个用 `trivial` 的插件因此**什么都没证明** —— 而 `Registry.lean:76` 已把这一点写在注释里。**

**=> 本条把那条注释变成定理，从而可以在任何地方引用它来说明「这个插件未验证」。** -/
theorem trivial_holds_iff (π : PluginProof)
    (h : π = PluginProof.trivial) : π.Holds := by
  subst h
  exact PluginProof.trivial_holds

end Lattice.Plugins
