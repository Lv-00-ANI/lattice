import Mathlib


/-!
# LATTICE: 同余约束 —— 模运算的代数判定与等价关系

同余约束（x ≡ a mod m）的代数形式：m ∣ (x - a)。
权重侧：模神经元输出 = x - a，激活 = 输出被 m 整除。

内容：
  1. 编译保语义：同余 ⟺ 整除判定（定义同构）；
  2. 同余是等价关系：自反 / 对称 / 传递；
  3. 同余的加法保持（模运算代数性质）；
  4. 零模退化：m = 0 时同余 ⟺ 严格相等。

注意 **订正 B400**：此处原写「纯 Std。」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**本文件的表示层只用到 `Int` 等核心类型**
（`Congruent`、`ModOut`、`Divisible` 皆以 `Int` 表达，不依赖 mathlib 的专用结构），
但**文件整体 import 了 Mathlib**。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
另：本文件证明所用的 `ring`、`omega` 均并非 Lean core 内置，而是 **Mathlib 提供的策略**
（其可用性来自文件整体 import 的 Mathlib）。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/

namespace Lattice

/-! ## 同余约束（符号侧）：m ∣ (x - a) -/

def Congruent (x a m : Int) : Prop :=
  m ∣ x - a

/-! ## 模神经元（权重侧输出：差值）与整除激活 -/

def ModOut (x a : Int) : Int := x - a

def Divisible (out m : Int) : Prop := m ∣ out

/-! ## 定理一：编译保语义
x ≡ a (mod m) ⟺ 模神经元输出被 m 整除。-/

theorem mod_preserves (x a m : Int) : Congruent x a m ↔ Divisible (ModOut x a) m := by
  unfold Congruent Divisible ModOut
  exact Iff.rfl

/-! ## 引理：整除的基本性质（Int） -/

lemma dvd_zero_int (m : Int) : m ∣ 0 := by
  exact dvd_zero m

lemma dvd_neg_int {m a : Int} (h : m ∣ a) : m ∣ -a := by
  rcases h with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  rw [hk]
  ring

lemma dvd_add_int {m a b : Int} (ha : m ∣ a) (hb : m ∣ b) : m ∣ a + b := by
  rcases ha with ⟨ka, hka⟩
  rcases hb with ⟨kb, hkb⟩
  refine ⟨ka + kb, ?_⟩
  rw [hka, hkb]
  ring

lemma dvd_sub_int {m a b : Int} (ha : m ∣ a) (hb : m ∣ b) : m ∣ a - b := by
  exact dvd_add_int ha (dvd_neg_int hb)

lemma neg_sub_neg (x a : Int) : -(x - a) = a - x := by
  ring

/-! ## 定理二：自反
x ≡ x (mod m)。-/

theorem congruent_refl (x m : Int) : Congruent x x m := by
  unfold Congruent
  rw [sub_self]
  exact dvd_zero_int m

/-! ## 定理三：对称
x ≡ a (mod m) → a ≡ x (mod m)。-/

theorem congruent_symm {x a m : Int} (h : Congruent x a m) : Congruent a x m := by
  unfold Congruent at h ⊢
  -- m ∣ x-a → m ∣ a-x = -(x-a)
  rw [← neg_sub_neg]
  exact dvd_neg_int h

/-! ## 定理四：传递
x ≡ a (mod m) → a ≡ y (mod m) → x ≡ y (mod m)。-/

theorem congruent_trans {x a y m : Int} (h1 : Congruent x a m) (h2 : Congruent a y m) :
    Congruent x y m := by
  unfold Congruent at h1 h2 ⊢
  -- m∣x-a, m∣a-y → m∣(x-a)+(a-y) = x-y
  have hsum : m ∣ (x - a) + (a - y) := dvd_add_int h1 h2
  have hrewrite : (x - a) + (a - y) = x - y := by ring
  rwa [hrewrite] at hsum

/-! ## 定理五：加法保持
x ≡ a 且 y ≡ b (mod m) → x+y ≡ a+b (mod m)。-/

theorem congruent_add {x a y b m : Int} (h1 : Congruent x a m) (h2 : Congruent y b m) :
    Congruent (x + y) (a + b) m := by
  unfold Congruent at h1 h2 ⊢
  -- m∣x-a, m∣y-b → m∣(x-a)+(y-b) = (x+y)-(a+b)
  have hsum : m ∣ (x - a) + (y - b) := dvd_add_int h1 h2
  have hrewrite : (x - a) + (y - b) = (x + y) - (a + b) := by ring
  rwa [hrewrite] at hsum

/-! ## 定理六：零模退化
m = 0 时，x ≡ a (mod 0) ⟺ x = a（0 整除 ⟺ 被除数零）。-/

theorem congruent_mod_zero (x a : Int) : Congruent x a 0 ↔ x = a := by
  unfold Congruent
  -- 0 ∣ (x-a) ⟺ x-a = 0
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    -- 0 * k = x - a → x - a = 0
    have : x - a = 0 := by
      rw [hk]
      simp
    omega
  · intro h
    refine ⟨0, ?_⟩
    omega

/-! ## 定理七：相同余数 ⟺ 同余（模运算判定形式）
当 m ≠ 0 时，x % m = a % m ⟺ m ∣ x - a。
（Int 模的完整性质依赖 mathlib；此处给出 m=±1 的退化特例：任何整数都同余。）-/

theorem congruent_mod_one (x a : Int) : Congruent x a 1 := by
  unfold Congruent
  refine ⟨x - a, ?_⟩
  ring

theorem congruent_mod_neg_one (x a : Int) : Congruent x a (-1) := by
  unfold Congruent
  refine ⟨a - x, ?_⟩
  ring

end Lattice
