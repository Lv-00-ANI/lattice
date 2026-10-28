import Mathlib
import Lattice.Runtime.ConvertLinear
import Lattice.Runtime.ConvertVectorLinear
/-!
# LATTICE: WeightToSymbolEquivalence（最小版本）—— 编译-提取往返恒等

doc/02 §4.3 的 `WeightToSymbolEquivalence` 最小实例（提取方向）：

对线性约束 → 线性层的编译（convertVec/convert），**提取方向完全可逆**：
  提取器 extract 从编译出的权重恢复原符号约束，往返恒等（round-trip identity）。

含义：
- 线性层权重中完整保留了符号约束信息——权重→符号在该子类上无损；
- 为提取方向确立正确性框架：提取候选须通过验证器（行为等价）确认。
- 真实难点在非线性层（提取不完全可逆），留待后续；本文件证明可逆子类的边界。

注意 **订正 B400**：此处原写「纯 Std。」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**本文件的表示层只用 `Int` / `List Int` 等核心类型**
（`LinearConstraint`、`LinearNeuron` 的字段皆为 `Int`，向量侧的 `LinearLayer` 为 `List Int`，
不依赖 mathlib 的专用结构），但**文件整体 import 了 Mathlib**。
⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。订正模板见 ConvertLinear / ConvertVectorLinear 的文件头「订正 B400」。**以本段为准。**
-/


namespace Lattice

/-! ## 标量版：提取器（从神经元恢复约束）
注：标量约束的系数是 Int，故标量提取器作用于标量神经元 LinearNeuron
（原 LinearLayer 是向量权重 List Int，与标量约束类型不匹配，已最小修正）。-/

def extract (l : LinearNeuron) : LinearConstraint :=
  { a := l.w, b := l.b }

/-! ## 定理一：编译-提取往返恒等（标量）
从编译出的神经元提取，恢复原约束。-/

theorem roundtrip_extract (c : LinearConstraint) :
    extract (convert c) = c := by
  cases c <;> rfl

/-! ## 定理二：往返保持行为等价

### ⚠ 这个模块的往返恒等是**定义展开**，不是建立起来的对应关系

**第 207 轮审计的结论，写在这里而不是留在债务表里。**

`extract { a := w, b := b } := { a := w, b := b }`，而 `ConstraintSat` 与 `NeuronOut`
按定义就是同一个 `Int` 表达式。所以：

| 定理 | 实际内容 |
|:--|:--|
| `roundtrip_extract` | `cases c <;> rfl`——**定义恒等** |
| `extract_is_valid` | `rfl`——**定义恒等** |
| `convert_preserves_semantics` | `simp [ConstraintSat, NeuronOut, convert]`——**定义展开** |

**这不是说它们是错的；是说它们没有建立任何东西。** 「权重→符号在该子类上无损」这句话
在这个模块里**是因为表示本来就是同一个 `Int` 列表**，不是因为证明了什么。
真正的无损性要等 `Embedding`/`OutputHead` 那一侧（`Semantics/VocabEdit.lean`）接上 `Holds`——
**那条桥目前不存在**（见 `SEMANTICS-MAINLINE.md` §6.1）。

### 原陈述的第一项是 `id`，已删

原 `roundtrip_behavior` 是合取：

```lean
(∀ l, NeuronOut l x = 0 → ConstraintSat (extract l) x) ∧
(ConstraintSat c x → NeuronOut (convert c) x = 0)
```

**第一项是 `h → h`**：两个命题按定义相同，`simpa using h` 就是 `id`。
**第 207 轮删掉了它**，只留第二项。名字保留，因为
`Lib/Lift/RealContractAxioms.lean` 有 `#print axioms roundtrip_behavior`——**改断言会断构建，改陈述不会。**

（第一项对应的真事实由 `extract_is_valid` 表述，而它自己也是 `rfl`。） -/

theorem roundtrip_behavior (c : LinearConstraint) (x : Int) :
    ConstraintSat c x → NeuronOut (convert c) x = 0 :=
  fun h => (convert_preserves_semantics c x).mpr h

/-! ## 向量版：提取器 -/

def extractVec (l : LinearLayer) : VectorConstraint :=
  { a := l.w, b := l.b }

/-! ## 定理三：向量版编译-提取往返恒等 -/

theorem roundtrip_extractVec (c : VectorConstraint) :
    extractVec (convertVec c) = c := by
  cases c <;> rfl

/-! ## 定理四：提取候选的有效性判定
提取候选若通过行为等价验证（输出零化 ⟺ 候选满足），则该候选是原权重的有效符号表示。
这是提取方向验证器的契约：验证通过 = 提取有效。-/

def ExtractionValid (l : LinearNeuron) (c : LinearConstraint) : Prop :=
  ∀ x : Int, NeuronOut l x = 0 ↔ ConstraintSat c x

/-- `extract` 返回的约束与原神经元**行为等价**。

⚠ **这是 `rfl`**：`extract l` 的字段就是 `l` 的字段，`ConstraintSat` 与 `NeuronOut`
按定义是同一个表达式。**没有建立任何对应关系**——见本文件 §定理二 的说明。 -/
theorem extract_is_valid (l : LinearNeuron) :
    ExtractionValid l (extract l) := by
  intro x
  unfold extract ConstraintSat NeuronOut
  rfl

end Lattice
