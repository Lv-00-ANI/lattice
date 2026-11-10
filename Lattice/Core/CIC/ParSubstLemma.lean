import Mathlib
import Lattice.Core.CIC.TakahashiDev

/-!
# `shift` 与 `ParRedU`：两个闭合成份已证，绑定层是缺口（阶段 5）

## 本轮的六次尝试

**三角形性质需要「替换与 `ParRedU` 交换」。本轮试图搭它的第 1 层（`ParRedU` 在 `shift` 下合同），
六次尝试都停在**同一条**一般化上：绑定构造子的 cutoff 必须加一，而构造子不变量不接受它。**

**每次失败都在**更小**的陈述上成功，所以本文件只保留确定成立的两个部分，
并把缺口写清楚，而不是继续在大陈述上试。**

## 两个闭合成份

| 定理 | 内容 |
|:--|:--|
| `shift_zero_is_refl` | **零步在位移下仍是零步** |
| `shift_app_pair` | **位移分别作用到应用的两侧** |

**=> **原子情形**与**二元构造子**都没有障碍。缺口只在需要 cutoff 加一的绑定构造子
（`lam` 的体、`letE` 的体）。**

## 缺口为什么是真缺口

**`shift c d (lam A b) = lam (shift c d A) (shift (c+1) d b)`：体的 cutoff 是 `c+1` 而不是 `c`。**

**要证「`b ⟹ b'` 蕴含 `shift c d b ⟹ shift c d b'`」，需要把归纳假设用在 `c+1` 处。
`induction generalizing c d` **应该**提供这一点，但本层的 `ParRedU` **同时**在 `lam` 的类型位置上
固定标注（第 819 轮），两条一般化要求相互纠缠 —— 六次尝试都没解开。**

**=> 这是本阶段**第六个**由「类型标注的处理方式」引起的缺口
（前五个见第 810/814/816/819/822 轮）。它指向同一个结构性事实：
**`Term` 携带类型标注，而每个归约关系都必须决定「标注动不动」，
每个决定的组合都需要各自的引理。** -/

namespace Lattice.Core.CIC

/-- **零步在位移下仍是零步。**

**=> 位移不改变「不动」这件事。这条平凡，但它确立了原子情形无碍。** -/
theorem shift_zero_is_refl (E : DefEnv) (c d : ℕ) (t : Term) :
    ParRedU E (shift c d t) (shift c d t) :=
  ParRedU.zero _

/-- **位移分别作用到应用的两侧。**

**=> 若两侧各自在位移后仍平行归约，则应用整体也是。这条说明**二元构造子**没有障碍。** -/
theorem shift_app_pair (E : DefEnv) (c d : ℕ) {f f' a a' : Term}
    (hf : ParRedU E (shift c d f) (shift c d f'))
    (ha : ParRedU E (shift c d a) (shift c d a')) :
    ParRedU E (shift c d (.app f a)) (shift c d (.app f' a')) :=
  ParRedU.app hf ha

end Lattice.Core.CIC
