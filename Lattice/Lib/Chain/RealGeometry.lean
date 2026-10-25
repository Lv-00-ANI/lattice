import Mathlib

/-!
# LATTICE: ℝ 几何 —— 共线、正交、距离（连续域）

ℝ 平面几何约束的代数判定（对应 Lv-00 几何 Point/Constraint 的连续域版）：
  1. 共线：ℝ 叉积 = 0（+ 平移/轮换/交换不变性）；
  2. 正交：ℝ 内积 = 0（对称性 + 缩放不变性）——离散/整型约束之外的新维度；
  3. 距离平方 = 0 ⟺ 点重合（欧几里得语义）。

  注意：**订正 B400**：此处原写「纯 Std 没有的新维度」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
  真实情况是：**本文件的表示层只用到 Std 层的核心类型**（`Point2R` 的字段皆为 `ℝ`，
  `radd`/`rsub`/`rscale`/`rcross`/`rdot`/`distSqR` 只在这些核心类型上做算术，未使用 mathlib 的专用结构），
  但**文件整体 import 了 Mathlib**。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。

Mathlib 的 ring/nlinarith 处理全部代数恒等式（`ring`/`nlinarith` 由 **Mathlib 提供**，
并非 Lean core 内置）——这正是本文件必须 `import Mathlib` 的原因。
-/

namespace Lattice

/-! ## ℝ 平面点 -/

structure Point2R where
  x : ℝ
  y : ℝ

def radd (a b : Point2R) : Point2R := { x := a.x + b.x, y := a.y + b.y }
def rsub (a b : Point2R) : Point2R := { x := a.x - b.x, y := a.y - b.y }
def rscale (t : ℝ) (a : Point2R) : Point2R := { x := t * a.x, y := t * a.y }

/-! ## 叉积（ℝ 2D 行列式）与点积 -/

def rcross (u v : Point2R) : ℝ := u.x * v.y - u.y * v.x
def rdot (u v : Point2R) : ℝ := u.x * v.x + u.y * v.y

/-! ## 共线（符号侧）与输出（权重侧） -/

def CollinearR (a b c : Point2R) : Prop := rcross (rsub b a) (rsub c a) = 0
def CollinearROut (a b c : Point2R) : ℝ := rcross (rsub b a) (rsub c a)

/-! ## 定理一：ℝ 共线保语义 -/

theorem collinearR_preserves (a b c : Point2R) :
    CollinearR a b c ↔ CollinearROut a b c = 0 := by
  rfl

/-! ## 引理：平移消除 -/

lemma rcross_translate (a b c d : Point2R) :
    rcross (rsub (radd b d) (radd a d)) (rsub (radd c d) (radd a d)) =
    rcross (rsub b a) (rsub c a) := by
  unfold rcross rsub radd
  ring

/-! ## 定理二：ℝ 共线平移不变性 -/

theorem collinearR_translate (a b c d : Point2R) :
    CollinearR (radd a d) (radd b d) (radd c d) ↔ CollinearR a b c := by
  unfold CollinearR
  rw [rcross_translate]

/-! ## 定理三：ℝ 共线轮换不变性 -/

theorem collinearR_cyclic (a b c : Point2R) :
    CollinearR b c a ↔ CollinearR a b c := by
  unfold CollinearR rcross rsub
  dsimp
  constructor
  · intro h
    calc
      (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)
          = (c.x - b.x) * (a.y - b.y) - (c.y - b.y) * (a.x - b.x) := by ring
      _ = 0 := h
  · intro h
    calc
      (c.x - b.x) * (a.y - b.y) - (c.y - b.y) * (a.x - b.x)
          = (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x) := by ring
      _ = 0 := h

/-! ## 定理四：ℝ 共线缩放不变性（整体缩放 λ ≠ 0） -/

theorem collinearR_scale (a b c : Point2R) (t : ℝ) (ht : t ≠ 0) :
    CollinearR (rscale t a) (rscale t b) (rscale t c) ↔ CollinearR a b c := by
  unfold CollinearR rscale rcross rsub
  dsimp
  -- (t(b-a)).cross (t(c-a)) = t² · (b-a).cross (c-a)；t² ≠ 0
  have hsq : t * t ≠ 0 := by
    intro hs
    exact ht (mul_self_eq_zero.mp hs)
  constructor
  · intro h
    -- t²·cross = 0 → cross = 0
    have hmul : (t * t) * ((b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)) = 0 := by
      nlinarith
    exact (mul_eq_zero.mp hmul).resolve_left hsq
  · intro h
    calc
      (t * b.x - t * a.x) * (t * c.y - t * a.y) - (t * b.y - t * a.y) * (t * c.x - t * a.x)
          = (t * t) * ((b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)) := by ring
      _ = 0 := by
        rw [h]
        ring

/-! ## 正交（垂直）：内积 = 0 -/

def OrthogonalR (u v : Point2R) : Prop := rdot u v = 0

/-! ## 定理五：正交对称性 -/

theorem orthogonalR_symm (u v : Point2R) : OrthogonalR u v ↔ OrthogonalR v u := by
  unfold OrthogonalR rdot
  constructor
  · intro h
    calc
      v.x * u.x + v.y * u.y = u.x * v.x + u.y * v.y := by ring
      _ = 0 := h
  · intro h
    calc
      u.x * v.x + u.y * v.y = v.x * u.x + v.y * u.y := by ring
      _ = 0 := h

/-! ## 定理六：正交缩放不变性
缩放 u（λ ≠ 0）不改变与 v 的正交关系。 -/

theorem orthogonalR_scale (u v : Point2R) (t : ℝ) (ht : t ≠ 0) :
    OrthogonalR u v ↔ OrthogonalR (rscale t u) v := by
  unfold OrthogonalR rscale rdot
  constructor
  · intro h
    -- (t·u.x)·v.x + (t·u.y)·v.y = t·(u.x·v.x + u.y·v.y) = t·0 = 0
    calc
      (t * u.x) * v.x + (t * u.y) * v.y = t * (u.x * v.x + u.y * v.y) := by ring
      _ = t * 0 := by rw [h]
      _ = 0 := by ring
  · intro h
    have htuv : t * (u.x * v.x + u.y * v.y) = 0 := by
      calc
        t * (u.x * v.x + u.y * v.y) = (t * u.x) * v.x + (t * u.y) * v.y := by ring
        _ = 0 := h
    exact (mul_eq_zero.mp htuv).resolve_left ht

/-! ## 距离平方：|b - a|² = 0 ⟺ 点重合 -/

def distSqR (a b : Point2R) : ℝ := (b.x - a.x) ^ 2 + (b.y - a.y) ^ 2

/-! ## 定理七：距离平方零化 ⟺ 两点重合 -/

theorem distSqR_eq_zero_iff (a b : Point2R) : distSqR a b = 0 ↔ a = b := by
  constructor
  · intro h
    unfold distSqR at h
    have hx : b.x - a.x = 0 := by
      nlinarith [sq_nonneg (b.x - a.x), sq_nonneg (b.y - a.y)]
    have hy : b.y - a.y = 0 := by
      nlinarith [sq_nonneg (b.x - a.x), sq_nonneg (b.y - a.y)]
    -- 由分量相等得点相等
    cases a
    cases b
    rw [Point2R.mk.injEq]
    constructor <;> linarith
  · intro h
    cases h
    simp [distSqR]

/-! ## 定理八：距离平方平移不变性
整体平移两点，距离不变（欧几里得规范形式）。 -/

theorem distSqR_translate (a b d : Point2R) :
    distSqR (radd a d) (radd b d) = distSqR a b := by
  unfold distSqR radd
  ring

end Lattice
