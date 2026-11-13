import Mathlib
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Runtime.SymbolToWeightCorrectness

/-!
# 逆向：从权重提取符号，并证明提取结果**可再注入**（阶段 C，P5）

## LATTICE 闭环的另一半

**正向（第 892-897 轮已打通）：数据 → CIC → ConstraintSet → 权重。**

**逆向：权重 → 符号 → **验证** → 再注入。**

**=> 本轮把逆向这一侧的三段写成具名定理，并证明它**回到正向的起点**。**
**这是「闭环」这个词唯一有内容的读法：逆向的产物必须能被正向重新消费。**

## 已有的部件

| 部件 | 位置 | 内容 |
|:--|:--|:--|
| **`extractVec`** | **`Runtime/WeightToSymbolEquivalence.lean`** | **权重层 → 约束（符号）** |
| **`roundtrip_extractVec`** | **同上** | **`extractVec (convertVec c) = c`** |
| **`ExtractionValidVec`** | **`Lib/Editing/RealCompileExtractClosed.lean`** | **「该候选对该层行为有效」** |
| **`verification_loop_closes_holds`** | **`Runtime/VerificationLoop.lean`** | **修复回路闭合** |

**=> 缺的是把它们**连成一条**：提取出的符号，能被 `compileToLayer` 重新编译回**行为等价**的权重。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `extract_sound` | **提取结果对原层**行为有效**（`ExtractionValidVec l (extractVec l)`）** |
| `reinject_roundtrip` | **⭐ 提取后重新编译**回到**原层：`convertVec (extractVec l) = l`** |
| `extract_reinject_loop` | **⭐⭐ 闭环：`extractVec` 后 `compileToLayer` 给出**同一个**层** |
| `inject_then_verify` | **正向后逆向再验证：注入的约束经验证后仍然有效** |

**=> `reinject_roundtrip` 是核心：它说明逆向**没有损失**——提取出的符号重新编译后
与原权重**逐字段相同**（`convertVec`/`extractVec` 是记录重命名，互为逆）。**

**而 `inject_then_verify` 是闭环的**语义**陈述：正向注入的约束 `c`，编译成层
`convertVec c`，再提取回来还是 `c`，因此 `ExtractionValidVec` 成立 —— **验证回路走了一圈回到原点且无所失**。**

## 诚实的边界

**`convertVec`/`extractVec` 是记录字段重命名。** **这意味着本文件的闭环是**结构性的**，
不是**语义性的**：它证明的是「符号与权重在这条表示上无损互转」，
**不是**「任意权重都能被还原成有意义的符号」。**

**后者是**真**的困难（第 895 轮已经遇到过它的一个形态）。** **本文件不声称它。** -/

namespace Lattice.Runtime.ExtractionClosure

open Lattice.Lift.SymbolToWeightCorrectness

/-- **`ExtractionValidVec l c`：候选 `c` 对层 `l` **行为有效**。**

**=> `∀ x, LayerOut l x = 0 ↔ VectorConstraintSat c x`。**

**本文件在 `Runtime` 内重新声明它（同名同义），因为它是**`LayerOut` 的性质**，
而 `LayerOut` 在 `Runtime`。`Lib` 侧另有一份同义定义 —— 那是第 897 轮之前就存在的分层现象，
本文件不改动它，只保证 `Runtime` 自己不需要向上导入。** -/
def ExtractionValidVec (l : LinearLayer) (c : VectorConstraint) : Prop :=
  ∀ x : List Int, LayerOut l x = 0 ↔ VectorConstraintSat c x

/-- **提取出的候选对原层行为有效。**

**=> 展开 `extractVec` 与 `VectorConstraintSat`/`LayerOut` 后 `rfl`：
提取就是把权重读成约束，两者是同一次计算。** -/
theorem extractVec_is_valid (l : LinearLayer) : ExtractionValidVec l (extractVec l) := by
  intro x
  show LayerOut l x = 0 ↔ VectorConstraintSat (extractVec l) x
  unfold extractVec VectorConstraintSat LayerOut
  rfl

/-- **提取出的候选对原层**行为有效**。**

**=> `extractVec l` 就是把 `l` 的权重读成约束，因此它对 `l` 的行为当然有效。
这不是「深刻」的定理，但它是**再注入**的前提：一个无效的候选不能被注回。
** -/
theorem extract_sound (l : LinearLayer) : ExtractionValidVec l (extractVec l) :=
  extractVec_is_valid l

/-- **⭐ 提取后重新编译**回到**原层。**

**=> `convertVec (extractVec l) = l`：两个方向都是记录字段重命名，因此互为逆。**

**=> 这条说明逆向**没有损失**：权重 → 符号 → 权重 是恒等。** -/
theorem reinject_roundtrip (l : LinearLayer) : convertVec (extractVec l) = l := by
  cases l with
  | mk w b => rfl

/-- **⭐⭐ 闭环：对单个层，提取后重新编译给出**同一个**层。**

**=> `compileToLayer [c] = [convertVec c]`，于是 `compileToLayer [extractVec l] = [l]`。**

**=> 这是「权重 → 符号 → 权重」在**层列表**上的形式，也就是再注入的完整陈述。** -/
theorem extract_reinject_loop (l : LinearLayer) :
    compileToLayer [extractVec l] = [l] := by
  unfold compileToLayer
  simp [reinject_roundtrip]

/-- **⭐⭐ 闭环的语义形式：正向后逆向再验证。**

**=> 对任意约束 `c`：注入 `c` 得到 `convertVec c`，从中提取回 `c`，该候选对 `convertVec c` **行为有效**。**

**=> 这就是「验证回路走了一圈」的精确陈述：注入 → 编译 → 提取 → 验证，终点是 `c` 对注入后的层有效。**
**它与 `extract_sound` 的区别是：这里起于**符号**、经**权重**、回到**符号的验证**。** -/
theorem inject_then_verify (c : VectorConstraint) :
    ExtractionValidVec (convertVec c) c := by
  have := extractVec_is_valid (convertVec c)
  rwa [roundtrip_extractVec] at this

/-- **闭环的两侧合起来：注入后再提取，得到**同一个**约束。**

**=> 这是 `roundtrip_extractVec` 的独立命名，使「符号 → 权重 → 符号」与
上一条「符号 → 权重 → 符号的验证」在本命名空间下**成对可引用**。** -/
theorem inject_extract_closed (c : VectorConstraint) : extractVec (convertVec c) = c :=
  roundtrip_extractVec c

end Lattice.Runtime.ExtractionClosure
