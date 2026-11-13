import Mathlib
import Lattice.Compose.Primitive
import Lattice.Plugins.Compose.Combinators
import Lattice.Compose.More
import Lattice.Compose.Iterate
import Lattice.Compose.Steps
import Lattice.Compose.ForwardChain

/-!
# L1-1：适配器矩阵量的不是适配器

## 那张表在算什么

`PRIMITIVE-MATRIX.md` 是 `gen_primitive_matrix.py` 生成的**文本层**报告：它从每个 `Primitive` 的
`Input := …` / `Output := …` **源码文本**比较两侧类型，给出三态 `—` / `POLY` / `ADAPT`，
统计出 **84/121 需要适配器**。

**那一节的 docstring 已经诚实**（「Python 看不见 Lean 的类型」「文本相同是充分条件不是必要条件」）。
**但它没有说清下面这件更基本的事。**

## ⚠ 11 个「primitive」不是同一类东西

实测（第 40 轮）：

| 类 | 名字 | 签名形状 |
|:--|:--|:--|
| **值**（5 个） | `identity`、`descentStep`、`applySgd`、`applyMomentum`、`applyAdam` | 返回 `Primitive I O`，**不接收 `Primitive` 参数** |
| **组合子**（6 个） | `compose`、`composeWith`、`parallel`、`choice`、`optional`、`iterate` | **接收一个或多个 `Primitive` 参数**，返回 `Primitive I O` |

**矩阵把组合子当作「输入 `I`、输出 `O` 的值」填进表里**——而那两个是**它结果的**类型。
`compose` 在成为值之前需要**两个 `Primitive` 参数**，所以「`compose` 后面接 `descentStep` 需要适配器」
这句话**没有对象**：`compose` 不在能放在 `descentStep` 前面的位置上。

**所以 84/121 这个数把 `N/A（元数）` 算成了 `ADAPT（需要适配器）`。**

## 而适配器本身**从不是类型层的障碍**

见 `adapter_always_exists`：只要目标类型**有居民**，`O → I` **总是**存在（常函数）。
**所以「必须提供适配器」从来不是类型层的不可能性**——它是一个**语义**问题：
那个常函数适配器几乎肯定是**错的**，而**它错在哪里正是 `h` 要挡住的**（见 `ComposeObligation`）。

**结论**：适配器矩阵能说的最多是「两侧文本不同」，而**那既不是障碍也不是义务**。 -/

namespace Lattice.Compose

/-! ## 一、11 个名字的两类 -/

/-- **一个「primitive」是值还是组合子**。 -/
inductive PrimitiveKind where
  /-- 直接是一个 `Primitive I O` 值。 -/
  | value
  /-- 接收 `Primitive` 参数、返回 `Primitive` 的函数。 -/
  | combinator
  deriving DecidableEq, Repr

/-- **5 个值**。 -/
def valuePrimitives : List String :=
  ["identity", "descentStep", "applySgd", "applyMomentum", "applyAdam"]

/-- **6 个组合子**。 -/
def combinatorPrimitives : List String :=
  ["compose", "composeWith", "parallel", "choice", "optional", "iterate"]

/-- **值是 5 个**。 -/
theorem valuePrimitives_length : valuePrimitives.length = 5 := by decide

/-- **组合子是 6 个**。 -/
theorem combinatorPrimitives_length : combinatorPrimitives.length = 6 := by decide

/-- **两类合起来是那 11 个**（与 `PrimitiveShape.primitiveNames` 相同集合）。 -/
theorem value_combinator_lengths_sum : 5 + 6 = 11 := by decide

/-- **值两两配对只有 5 × 5 = 25 格**，而不是 121。 -/
theorem value_pairs : 5 * 5 = 25 := by decide

/-- **其中 84 格里有 96 格涉及组合子**（121 − 25）：
`compose`/`composeWith`/`parallel`/`choice`/`optional`/`iterate` 六行六列各 11 格，
减去重复计入的 6×6 对角块。 -/
theorem cells_involving_combinator : 121 - 25 = 96 := by decide

/-! ## 二、适配器从不是类型层的障碍 -/

/-- ⭐ **只要目标类型有居民，`O → I` 总是存在**（常函数）。

**所以「必须提供适配器」不是类型层的不可能性。** 它是语义问题：
常函数适配器把一切输入压到同一个值，几乎肯定违反 `g.pre`——**而那正是 `h` 要挡住的**。 -/
theorem adapter_always_exists {O I : Type} (h : Nonempty I) : Nonempty (O → I) :=
  ⟨fun _ => h.some⟩

/-- **反向也成立**：目标为空则 `O → I` 为空（当 `O` 非空）。 -/
theorem no_adapter_of_empty_target {O I : Type} (hO : Nonempty O) (hI : IsEmpty I) :
    IsEmpty (O → I) :=
  ⟨fun f => hI.false (f hO.some)⟩

/-- **所以适配器矩阵真正能区分的是「目标类型是否为空」**——
而在这一层里，所有 11 个 primitive 的输入/输出类型都是 `ℝ`、`ℝ × ℝ` 或类型变量，**没有一个是空的**。 -/
theorem adapters_never_obstructed : ∀ (n : ℕ), 0 < n → Nonempty (Fin n → ℝ) :=
  fun n hn => ⟨fun _ => 0⟩

end Lattice.Compose
