import Mathlib

/-!
# LATTICE: ℝ 组合子 —— AND/OR 嵌入的连续域健全性

  注意 **订正 B400**：此处原写「对应纯 Std Combinators.lean 的 ℝ 版」，
  而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾；且被对照的 `Combinators.lean`
  自身第 1 行同样是 `import Mathlib`，其文件头亦已就此作出同名订正。
  真实情况是：**本文件的表示层构造基于 Std 类型** —— 两个组合子
  `real_andC`/`real_orC` 都只是 `ℝ → ℝ → ℝ` 的普通 `def`（平方和、乘积），
  零化引理 `… = 0 ↔ …` 的**陈述**不依赖 mathlib 的专用结构；
  但**本文件是 ℝ 版，其 `ℝ` 类型本身来自 Mathlib**，证明手段
  （`nlinarith`、`linarith`、`norm_num`、`sq_nonneg`、`sq_eq_zero_iff`、`mul_eq_zero`）
  亦由 Mathlib 提供，且**文件整体 import 了 Mathlib**。
  ⇒ 原措辞把「表示层的选型」误写成了「依赖的选型」。
  订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**

对应的 ℝ 版组合子（原句仅指本文件与 `Combinators.lean` 的版本对应关系）：
  AND 组合子  real_andC a b := a² + b²   （=0 ⟺ a=0 ∧ b=0）
  OR  组合子  real_orC  a b := a · b     （=0 ⟺ a=0 ∨ b=0）

内容：
  1. 零化引理（sq_nonneg + nlinarith / mul_eq_zero）；
  2. 交换/分配/结合律保持（符号逻辑代数在网络侧成立）；
  3. ℝ 特有：real_andC 严格正性——任一输入非零 ⟹ 组合损失 > 0（训练失败信号）。
-/

namespace Lattice

/-! ## 嵌入组合子 -/

def real_andC (a b : ℝ) : ℝ := a ^ 2 + b ^ 2

def real_orC (a b : ℝ) : ℝ := a * b

/-! ## 引理一：AND 零化 ⟺ 两项为零 -/

lemma real_andC_eq_zero_iff (a b : ℝ) : real_andC a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    unfold real_andC at h
    have ha : a = 0 := by
      have ha2 : a ^ 2 = 0 := by
        nlinarith [sq_nonneg a, sq_nonneg b]
      exact sq_eq_zero_iff.mp ha2
    have hb : b = 0 := by
      have hb2 : b ^ 2 = 0 := by
        nlinarith [sq_nonneg a, sq_nonneg b]
      exact sq_eq_zero_iff.mp hb2
    exact ⟨ha, hb⟩
  · intro h
    rcases h with ⟨ha, hb⟩
    simp [real_andC, ha, hb]

/-! ## 引理二：OR 零化 ⟺ 任一项为零 -/

lemma real_orC_eq_zero_iff (a b : ℝ) : real_orC a b = 0 ↔ a = 0 ∨ b = 0 := by
  unfold real_orC
  exact mul_eq_zero

/-! ## 交换律保持 -/

theorem real_and_comm_preserves (a b : ℝ) : real_andC a b = 0 ↔ real_andC b a = 0 := by
  rw [real_andC_eq_zero_iff, real_andC_eq_zero_iff]
  tauto

theorem real_or_comm_preserves (a b : ℝ) : real_orC a b = 0 ↔ real_orC b a = 0 := by
  rw [real_orC_eq_zero_iff, real_orC_eq_zero_iff]
  tauto

/-! ## 分配律保持（符号逻辑分配律在网络侧成立） -/

theorem real_dist_preserves (a b c : ℝ) :
    real_andC a (real_orC b c) = 0 ↔ real_orC (real_andC a b) (real_andC a c) = 0 := by
  rw [real_andC_eq_zero_iff, real_orC_eq_zero_iff, real_orC_eq_zero_iff, real_andC_eq_zero_iff, real_andC_eq_zero_iff]
  tauto

/-! ## 结合律保持 -/

theorem real_and_assoc_preserves (a b c : ℝ) :
    real_andC (real_andC a b) c = 0 ↔ real_andC a (real_andC b c) = 0 := by
  rw [real_andC_eq_zero_iff, real_andC_eq_zero_iff, real_andC_eq_zero_iff, real_andC_eq_zero_iff]
  tauto

theorem real_or_assoc_preserves (a b c : ℝ) :
    real_orC (real_orC a b) c = 0 ↔ real_orC a (real_orC b c) = 0 := by
  rw [real_orC_eq_zero_iff, real_orC_eq_zero_iff, real_orC_eq_zero_iff, real_orC_eq_zero_iff]
  tauto

/-! ## 定理：AND 组合损失严格正
任一输入非零 ⟹ real_andC > 0（ℝ 特有：训练失败信号严格为正）。-/

theorem andC_pos_of_ne (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : 0 < real_andC a b := by
  unfold real_andC
  rcases h with h | h
  · have hsq : 0 < a ^ 2 := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg b]
  · have hsq : 0 < b ^ 2 := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg a]

/-! ## 推论：OR 组合损失的等价可观测性
real_orC = 0 是"存在未零化项"的可判定信号：非零当且仅当两项都非零。 -/

theorem orC_pos_of_both_ne (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 0 < real_orC a b ∨ real_orC a b < 0 := by
  unfold real_orC
  by_cases hab : a * b = 0
  · exfalso
    rcases (mul_eq_zero.mp hab) with ha0 | hb0
    · exact ha ha0
    · exact hb hb0
  · rcases lt_or_gt_of_ne hab with hlt | hgt
    · right; exact hlt
    · left; exact hgt

/-! ## ¬（NOT）与 ⊕（XOR）组合子 —— 二值化域上的零化范式

注意 **对应 Std 版 `CombinatorsXorNot.lean` 的 ℝ 版**（P1-2 / P1-3 验收标准 ③「ℝ 版同步」）。

注意 **为什么这两者不能照抄 `real_andC` / `real_orC` 的范式**：
既有组合子全部依赖「**非负性**」（`a² + b²`）或「**零因子性**」（`a · b`），
而 XOR 的满足集 `({0}×ℝ*) ∪ (ℝ*×{0})` 在这两条性质下**都无法表达**
（该集合**不闭**：(0, 1/n) 在其内而极限点 (0,0) 在其外）。

要点 **处置**：在**二值化域 `{0,1}`** 上给出编码并证明零化 `↔`，
**定义域限制显式写在定理右端**。注意 **全域版本为假**
（见 `real_xorC_offdomain_counterexample`）。 -/

/-! ### ¬ 组合子（ℝ 版） -/

/-- **NOT 组合子（ℝ 版）**：`real_notC a := (1 - a)²`。取值 `real_notC 0 = 1`、`real_notC 1 = 0`。 -/
def real_notC (a : ℝ) : ℝ := (1 - a) ^ 2

/-- 要点 **NOT 零化 ⟺ 语义（ℝ 版，定义域限制显式在右端）**。 -/
theorem real_notC_eq_zero_iff_on_domain (a : ℝ) :
    real_notC a = 0 ↔ (a = 0 ∨ a = 1) ∧ a ≠ 0 := by
  have hkey : real_notC a = 0 ↔ a = 1 := by
    constructor
    · intro h
      have h1 : (1 - a) ^ 2 = 0 := by simpa [real_notC] using h
      have h2 : 1 - a = 0 := sq_eq_zero_iff.mp h1
      linarith
    · intro h
      subst h
      norm_num [real_notC]
  rw [hkey]
  constructor
  · intro h; subst h; exact ⟨Or.inr rfl, by norm_num⟩
  · rintro ⟨hdom, hne⟩
    rcases hdom with h0 | h1
    · exact absurd h0 hne
    · exact h1

/-- **NOT 零化（假设形态，ℝ 版）**：定义域限制作为假设传入。 -/
theorem real_notC_eq_zero_iff (a : ℝ) (ha : a = 0 ∨ a = 1) :
    real_notC a = 0 ↔ a = 1 := by
  rcases ha with rfl | rfl
  · constructor
    · intro h; norm_num [real_notC] at h
    · intro h; norm_num at h
  · constructor
    · intro _; rfl
    · intro _; norm_num [real_notC]

/-- 注意 **反例（机器验证）**：`real_notC` 的零化**不能**去掉定义域限制。 -/
theorem real_notC_offdomain_counterexample : real_notC 2 ≠ 0 ∧ (2 : ℝ) ≠ 0 := by
  constructor <;> norm_num [real_notC]

/-! ### ⊕ 组合子（ℝ 版，路线 A：两个 AND 的 OR） -/

/-- **XOR 组合子（ℝ 版）**：`real_xorC a b := real_orC (real_andC a (real_notC b)) (real_andC (real_notC a) b)`
—— 即 `(a ∧ ¬b) ∨ (¬a ∧ b)`，与任务书路线 A 逐字一致。 -/
def real_xorC (a b : ℝ) : ℝ :=
  real_orC (real_andC a (real_notC b)) (real_andC (real_notC a) b)

/-- 要点 **主定理：XOR 零化 ⟺ 语义（ℝ 版，定义域限制显式写在右端）**。

注意 右端 `(a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ ¬ (a ≠ 0 ↔ b ≠ 0)`：
前两项是**不可省略的定义域限制**，第三项是 XOR 语义（恰好一个为零）。 -/
theorem real_xorC_eq_zero_iff_on_domain (a b : ℝ) :
    real_xorC a b = 0 ↔
      (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ ¬ (a ≠ 0 ↔ b ≠ 0) := by
  constructor
  · intro h
    have hz : real_andC a (real_notC b) = 0 ∨ real_andC (real_notC a) b = 0 := by
      have hmul : real_andC a (real_notC b) * real_andC (real_notC a) b = 0 := by
        simpa [real_xorC, real_orC] using h
      exact mul_eq_zero.mp hmul
    rcases hz with h1 | h2
    · obtain ⟨ha0, hnb⟩ := (real_andC_eq_zero_iff a (real_notC b)).mp h1
      have hb1 : b = 1 := by
        have : (1 - b) ^ 2 = 0 := by simpa [real_notC] using hnb
        have : 1 - b = 0 := sq_eq_zero_iff.mp this
        linarith
      refine ⟨Or.inl ha0, Or.inr hb1, ?_⟩
      simp [ha0, hb1]
    · obtain ⟨hna, hb0⟩ := (real_andC_eq_zero_iff (real_notC a) b).mp h2
      have ha1 : a = 1 := by
        have : (1 - a) ^ 2 = 0 := by simpa [real_notC] using hna
        have : 1 - a = 0 := sq_eq_zero_iff.mp this
        linarith
      refine ⟨Or.inr ha1, Or.inl hb0, ?_⟩
      simp [ha1, hb0]
  · rintro ⟨ha, hb, hxor⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exfalso; exact hxor (by simp)
    · norm_num [real_xorC, real_orC, real_andC, real_notC]
    · norm_num [real_xorC, real_orC, real_andC, real_notC]
    · exfalso; exact hxor (by simp)

/-- **主定理（假设形态，ℝ 版）**：定义域限制作为假设参数传入。 -/
theorem real_xorC_eq_zero_iff (a b : ℝ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    real_xorC a b = 0 ↔ ¬ (a ≠ 0 ↔ b ≠ 0) := by
  have h := real_xorC_eq_zero_iff_on_domain a b
  exact ⟨fun hz => (h.mp hz).2.2, fun hx => h.mpr ⟨ha, hb, hx⟩⟩

/-- 要点 **XOR 零化的 AND/OR 分解（ℝ 版）**：路线 A 的语义内容。 -/
theorem real_xorC_zero_iff_and_or_decomposition (a b : ℝ) :
    real_xorC a b = 0 ↔ real_andC a (real_notC b) = 0 ∨ real_andC (real_notC a) b = 0 := by
  unfold real_xorC real_orC
  exact mul_eq_zero

/-- 要点 **`real_xorC` 的零点集刻画（全域，ℝ 版）**：恰好 `{(0,1), (1,0)}`。

注意 它**不是**「恰好一个为零」（后者是 `({0}×ℝ*) ∪ (ℝ*×{0})`，
含 `(0,2)` 等点，而 `real_xorC 0 2 = 5 ≠ 0`）。 -/
theorem real_xorC_eq_zero_iff_pair (a b : ℝ) :
    real_xorC a b = 0 ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have hz : real_andC a (real_notC b) = 0 ∨ real_andC (real_notC a) b = 0 :=
      (real_xorC_zero_iff_and_or_decomposition a b).mp h
    rcases hz with h1 | h2
    · obtain ⟨ha0, hnb⟩ := (real_andC_eq_zero_iff a (real_notC b)).mp h1
      have hb1 : b = 1 := by
        have : (1 - b) ^ 2 = 0 := by simpa [real_notC] using hnb
        have : 1 - b = 0 := sq_eq_zero_iff.mp this
        linarith
      exact Or.inl ⟨ha0, hb1⟩
    · obtain ⟨hna, hb0⟩ := (real_andC_eq_zero_iff (real_notC a) b).mp h2
      have ha1 : a = 1 := by
        have : (1 - a) ^ 2 = 0 := by simpa [real_notC] using hna
        have : 1 - a = 0 := sq_eq_zero_iff.mp this
        linarith
      exact Or.inr ⟨ha1, hb0⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num [real_xorC, real_orC, real_andC, real_notC]

/-- 注意 **反例（机器验证，ℝ 版）**：`real_xorC 0 2 = 5 ≠ 0`，
但「恰好一个为零」为**真**。⇒ 注意 **全域零化 `↔` 为假**，定义域限制不可省。

要点 与 Std 版 `xorC_offdomain_counterexample` 同形（**右端显式括号**，
避免 `∧`/`↔` 优先级歧义 —— 这是 Std 版初稿踩过的坑）。 -/
theorem real_xorC_offdomain_counterexample :
    real_xorC 0 2 ≠ 0 ∧ ¬ ((0 : ℝ) ≠ 0 ↔ (2 : ℝ) ≠ 0) := by
  constructor
  · norm_num [real_xorC, real_orC, real_andC, real_notC]
  · norm_num

/-- 要点 **NOT 是 XOR 的特例（ℝ 版）**：在 `{0,1}` 上 `real_notC a = real_xorC a 0`。
（P1-3 验收标准 ③「XOR 与 NOT 是否同源」的 ℝ 版见证。）

注意 **本条曾写成 `real_notC a = real_xorC a 1`（【假命题】）** —— 与 Std 版同一处 bug。
要点 **根因**：`real_xorC` 的**零集**编码 XOR，而其**取值**是 **XNOR**
（`real_xorC 0 0 = 1`）。⇒ 注意 **不可用取值相等陈述同源**，须用零化等价。 -/
theorem real_notC_eq_real_xorC_zero (a : ℝ) (ha : a = 0 ∨ a = 1) :
    real_notC a = real_xorC a 0 := by
  rcases ha with h | h
  · subst h; norm_num [real_xorC, real_orC, real_andC, real_notC]
  · subst h; norm_num [real_xorC, real_orC, real_andC, real_notC]

/-- 注意 **反例（机器验证，ℝ 版）**：`real_notC a = real_xorC a 1` **为假**（两点上都反）。 -/
theorem real_notC_ne_real_xorC_one_counterexample :
    real_notC 0 ≠ real_xorC 0 1 ∧ real_notC 1 ≠ real_xorC 1 1 := by
  constructor <;> norm_num [real_xorC, real_orC, real_andC, real_notC]

/-- 要点 **同源的【零化形态】表述（ℝ 版）**（避开取值陷阱的正确陈述）。 -/
theorem real_notC_zero_iff_real_xorC_zero_zero (a : ℝ) (ha : a = 0 ∨ a = 1) :
    real_notC a = 0 ↔ real_xorC a 0 = 0 := by
  rw [real_notC_eq_zero_iff a ha]
  rcases ha with h | h
  · subst h; constructor <;> intro h <;> norm_num [real_xorC, real_orC, real_andC, real_notC] at h
  · subst h; constructor <;> intro _ <;> norm_num [real_xorC, real_orC, real_andC, real_notC]

/-- 注意 **零集 vs 取值：`real_xorC` 的取值表**（`{0,1}²` 上逐点，防复活）。 -/
theorem real_xorC_value_table_on_bool :
    real_xorC 0 0 = 1 ∧ real_xorC 0 1 = 0 ∧ real_xorC 1 0 = 0 ∧ real_xorC 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [real_xorC, real_orC, real_andC, real_notC]

/-- 注意 **而零化表恰好是 XOR**（与上条逐点相反）—— 陷阱的完整见证。 -/
theorem real_xorC_zero_table_on_bool :
    real_xorC 0 0 ≠ 0 ∧ real_xorC 0 1 = 0 ∧ real_xorC 1 0 = 0 ∧ real_xorC 1 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [real_xorC, real_orC, real_andC, real_notC]

/-- 要点 **`real_notC` 与既有 De Morgan 定理的衔接**（把 P1-3 的「缺命名形态」
与 `RealImplication.lean:64` 的「已有内容」接上，**并说明为何两者不冲突**）。

注意 **本条不是 `real_notC_eq_zero_iff` 的别名**（那会是 B222.2 的空洞重述）——
它给出的是**结构对照**：既有 `not_andC_zero_iff` 把「`real_andC a b = 0` 的否定」
翻译成 `a ≠ 0 ∨ b ≠ 0`（**这是一个 Prop 层重写，不产生组合子值**），
而本文件的 `real_notC` **产生一个值**（`real_notC 0 = 1`）。

⇒ 两者分工：**De Morgan 路线管「非零判定」**（`¬(x = 0)`，不可零化），
**`real_notC` 管「二值化域上的取反」**（`x ↦ 1 - x`）。
下面的 `↔` 把这两件事的**衔接点**写出来：`real_notC a = 0` 恰好是
「`a` 在二值化域上取真值」，而 `a ≠ 0` 是「`a` 非零」——**在 `{0,1}` 上二者一致**
（`a = 1 ⟺ a ≠ 0`，由定义域限制承重）。 -/
theorem real_notC_zero_iff_ne_zero_on_domain (a : ℝ) (ha : a = 0 ∨ a = 1) :
    real_notC a = 0 ↔ a ≠ 0 := by
  rw [real_notC_eq_zero_iff a ha]
  rcases ha with rfl | rfl
  · constructor <;> intro h <;> norm_num at h
  · constructor <;> intro _ <;> norm_num

/-- 要点 **`real_notC a = 0` 与 `a = 0` 的互斥性**（二值化域上「取反」的语义核）。

注意 与 `real_notC_zero_iff_ne_zero_on_domain` 不同：那条给 `⟺ a ≠ 0`，
本条给出**更强的结构性事实** —— `real_notC a = 0` 与 `a = 0` **不可能同时成立**
（即 NOT 在二值化域上是真正的取反，不是恒等/常值）。
要点 **这正是 P1-3 判定「内容真缺」的依据**：
既有 De Morgan 定理**不产生值**，故不可能给出本条。 -/
theorem real_notC_zero_and_self_zero_exclusive (a : ℝ) (ha : a = 0 ∨ a = 1) :
    ¬ (real_notC a = 0 ∧ a = 0) := by
  rintro ⟨h1, h2⟩
  -- h1 : real_notC a = 0  ⟹  a = 1（在域内）；h2 : a = 0 ⟹ 1 = 0，矛盾
  rw [real_notC_eq_zero_iff a ha] at h1
  rw [h1] at h2
  norm_num at h2

end Lattice
