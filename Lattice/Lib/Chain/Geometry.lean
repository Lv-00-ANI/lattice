import Mathlib


/-!
# LATTICE: 几何约束 —— 共线性的代数判定与不变性

连接 Lv-00 的核心几何约束（Point/Constraint 语义的最小代数形式）：
三点共线 collinear(a,b,c) 用叉积判定 cross(b-a, c-a) = 0。

内容：
  1. 共线约束 → 叉积神经元（输出 = cross(b-a,c-a)），激活 = 0 —— 编译保语义；
  2. 平移不变性：整体平移三点，共线不变（几何规范形式）；
  3. 轮换不变性：三点顺序轮换，共线不变。

**注意** **订正 B400**：此处原写「纯 Std」并称「ring 为 Lean core 内置策略」，
而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾；且 `ring` 并非 Lean core 内置，
而是 **Mathlib 提供的策略**（本文件的三处 `ring` 与一处 `simp` 均来自 Mathlib）。
真实情况是：**本文件的几何表示层只用到 `Int` 等核心类型**
（`Point2`、`psub`、`padd`、`cross`、`Collinear` 皆为 `Int` 上的初等构造，
不依赖 mathlib 的专用结构），但**文件整体 import 了 Mathlib**，
证明亦依赖 Mathlib 的 `ring`/`simp`。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/

namespace Lattice

/-! ## 平面点（整数坐标） -/

structure Point2 where
  x : Int
  y : Int
deriving Repr

def psub (a b : Point2) : Point2 := { x := a.x - b.x, y := a.y - b.y }
def padd (a b : Point2) : Point2 := { x := a.x + b.x, y := a.y + b.y }

/-! ## 叉积（2D 行列式） -/

def cross (u v : Point2) : Int := u.x * v.y - u.y * v.x

/-! ## 共线约束（符号侧语义） -/

def Collinear (a b c : Point2) : Prop :=
  cross (psub b a) (psub c a) = 0

/-! ## 叉积神经元（权重侧输出：同一叉积值） -/

def CollinearOut (a b c : Point2) : Int :=
  cross (psub b a) (psub c a)

/-! ## 定理一：共线约束编译为叉积神经元保语义
共线 ⟺ 叉积输出为零（定义同构；约束信息完整保留在权重输出中）。-/

theorem collinear_preserves (a b c : Point2) :
    Collinear a b c ↔ CollinearOut a b c = 0 := by
  rfl

/-! ## 引理：平移消除
cross((b+d)-(a+d), (c+d)-(a+d)) = cross(b-a, c-a)-/

lemma cross_translate (a b c d : Point2) :
    cross (psub (padd b d) (padd a d)) (psub (padd c d) (padd a d)) =
    cross (psub b a) (psub c a) := by
  unfold cross psub padd
  ring

/-! ## 定理二：平移不变性
整体平移不改变共线关系（几何规范形式：平移是冗余自由度）。-/

theorem collinear_translate (a b c d : Point2) :
    Collinear (padd a d) (padd b d) (padd c d) ↔ Collinear a b c := by
  unfold Collinear
  rw [cross_translate]

/-! ## 引理：轮换下叉积保持
cross(c-b, a-b) = cross(b-a, c-a)（轮换重排下叉积不变） -/

lemma cross_cyclic (a b c : Point2) :
    cross (psub c b) (psub a b) = cross (psub b a) (psub c a) := by
  unfold cross psub
  ring

/-! ## 定理三：轮换不变性
三点轮换顺序，共线关系不变。 -/

theorem collinear_cyclic (a b c : Point2) :
    Collinear b c a ↔ Collinear a b c := by
  unfold Collinear
  rw [cross_cyclic]

/-! ## 定理四：共线对称性（交换后两点）
collinear(a,b,c) ⟺ collinear(a,c,b)（前两点交换，叉积取反但零判定不变）。-/

theorem collinear_swap (a b c : Point2) :
    Collinear a c b ↔ Collinear a b c := by
  unfold Collinear
  -- cross(c-a, b-a) = -cross(b-a, c-a)，零判定不变
  have hxy : cross (psub c a) (psub b a) = -cross (psub b a) (psub c a) := by
    unfold cross psub
    ring
  rw [hxy]
  exact neg_eq_zero

/-! ## 退化情形：两点重合必共线
b = a 时三点（a, a, c）共线（叉积为零向量）。-/

theorem collinear_degenerate (a c : Point2) : Collinear a a c := by
  unfold Collinear cross psub
  simp

end Lattice
