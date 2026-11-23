import Mathlib

/-!
# **部分截面：符号嵌入权重，而提取可以失败**

## 为什么需要这个抽象

目标说真正的难点只有「符号 ⇄ 权重」这一跳。这一跳在树里有两个**方向**的定理：

- 正向（符号 → 权重）：`compileSkel : IRSkeleton → IRWeights`，**全函数**；
- 逆向（权重 → 符号）：`extract : IRWeights → Option IRSkeleton`，**部分函数**。

（`extract_compile : extract (compileSkel k) = some k` 在 `Core/IR/Extract.lean`；
`compile_extract_layer : compileToLayer (extractLayer ls) = ls` 在 `Runtime/LoopClosure.lean`。）

**两个方向不是同一种东西，而 `Option` 不是瑕疵。** 权重携带的信息比骨架多
（`compileSkel` 只在位置 0 写 `skeletonCode k`，其余位置写 `0`），所以提取在**像之外**可以失败。
把它说成「提取恰好定义在像上」是**陈述错了**——它在某些像外输入上也会返回值。
准确的说法是：**像 ⊆ 提取有定义的地方**，且**在像上提取给出的见证就是原像**。

## 本文件提供什么

`PartialSection Sym W` = 一个全映射 `compile` 加一个部分映射 `extract`，满足
`extract ∘ compile = some` 且 `compile` 单射。这正是「符号嵌入权重」的代数内容：
**`compile` 是一个分裂单态射**（在 `Option` 的 Kleisli 意义下），而不是同构。

**⇒ 它比单独引用那两条定理更强的地方在于：它把「这一跳是嵌入而非同构」变成**类型**，
于是「哪些结论只依赖嵌入性」有了答案——本文件的五条引理就是那个答案。**
-/

namespace Lattice.Core

/-- **部分截面**：符号嵌入权重，提取是它的部分右逆。

**字段含义：**
- `compile`：全映射（符号 → 权重）。**必须全——编译不会失败。**
- `extract`：部分映射（权重 → `Option` 符号）。**必须部分——权重比符号多携带信息。**
- `retract`：`extract (compile s) = some s`。**提取在像上恒成功。**
- `compile_injective`：`compile` 单射。**不同符号编译出不同权重，这一跳不丢信息。**

**⇒ 四条合起来就是「`compile` 是分裂单态射」。`Option` 出现在 `extract` 的返回类型里，
是「提取在像外可能失败」这一事实的**类型级**记录，不是补丁。** -/
structure PartialSection (Sym W : Type) where
  /-- The total map: symbols compile into weights. -/
  compile : Sym → W
  /-- The partial map: extraction may fail, which is why it returns `Option`. -/
  extract : W → Option Sym
  /-- **Extraction succeeds on the image.** -/
  retract : ∀ s : Sym, extract (compile s) = some s
  /-- **Compilation is injective**, so the embedding loses no information. -/
  compile_injective : Function.Injective compile

namespace PartialSection

variable {Sym W : Type}

/-- **提取在像上恒成功**（`retract` 的直读）。 -/
theorem retract_some (P : PartialSection Sym W) (s : Sym) : P.extract (P.compile s) = some s :=
  P.retract s

/-- **像上的提取有定义**：存在一个 `s` 使 `extract` 返回 `some s`。

**⇒ 这是「部分」与「全」的差别的可用形式：在像上，`Option` 从不落到 `none`。** -/
theorem isSome_retract (P : PartialSection Sym W) (s : Sym) :
    (P.extract (P.compile s)).isSome := by
  rw [P.retract s]
  rfl

/-- **反向的截面性**：若 `w = compile s`，则提取 `w` 恰好得到 `s`。

**⇒ 与 `retract` 互为反向陈述；它给出「已知原像时提取的结果可预测」。** -/
theorem extract_eq_some_of_compile_eq (P : PartialSection Sym W) {s : Sym} {w : W}
    (h : P.compile s = w) : P.extract w = some s := by
  rw [← h]
  exact P.retract s

/-- **在像上，提取给出的见证就是原像。**

**⇒ 这是本抽象最有用的推论，也是它强于「两条定理并列」的地方：
调用者拿到一个提取结果 `some s` 和一个「该权重是编译出来的」事实 `w ∈ range compile`，
就能断言 `compile s = w`——不必再比较权重向量。**

**⇒ 证明只用到 `retract`：把 `w ∈ range` 展开成 `w = compile s'`，则 `some s' = some s`，故 `s' = s`。** -/
theorem compile_eq_of_mem_range (P : PartialSection Sym W) {w : W} {s : Sym}
    (hext : P.extract w = some s) (hmem : w ∈ Set.range P.compile) : P.compile s = w := by
  obtain ⟨s', rfl⟩ := hmem
  rw [P.retract s'] at hext
  have hss : s' = s := Option.some.inj hext
  rw [hss]

end PartialSection


/-! ## 二、同构的情形：`Option` 何时**消失**

**目标里有两跳同形状的「符号 ⇄ 权重」：**

- **权重那一跳**（`IRSkeleton ⇄ IRWeights`）：正向全、逆向**部分**，故是 `PartialSection`；
- **层那一跳**（`ConstraintSet ⇄ Layer`）：**两个方向的往返都有**，故是**同构**。

**⇒ 如果这两件事各自成篇，读者就得自己发现它们的差别是「权重侧是否携带额外信息」。**
**⇒ 本节的 `BiSection` 与 `isIso_iff_image_total` 把那个差别变成一条**定理**：
**`Option` 消失 ⟺ 每一个权重都是某个符号编译出来的。** -/

/-- **同构版本**：两个方向都是全函数，且互为逆。 -/
structure BiSection (Sym W : Type) where
  /-- Total map: symbols compile into weights. -/
  compile : Sym → W
  /-- **TOTAL** inverse: extraction cannot fail here. -/
  extract : W → Sym
  /-- `extract ∘ compile = id`. -/
  left : ∀ s : Sym, extract (compile s) = s
  /-- `compile ∘ extract = id`. -/
  right : ∀ w : W, compile (extract w) = w

namespace BiSection

variable {Sym W : Type}

/-- **同构给出一个全的 `PartialSection`**：`extract` 包装成 `some`。 -/
def toPartialSection (B : BiSection Sym W) : PartialSection Sym W where
  compile := B.compile
  extract := fun w => some (B.extract w)
  retract := fun s => by show some (B.extract (B.compile s)) = some s; rw [B.left s]
  compile_injective := by
    intro a b h
    have h' : B.extract (B.compile a) = B.extract (B.compile b) := by rw [h]
    rw [B.left a, B.left b] at h'
    exact h'

/-- **同构的 `extract` 从不失败。** -/
theorem extract_isSome (B : BiSection Sym W) (w : W) :
    (B.toPartialSection.extract w).isSome := by
  show (some (B.extract w)).isSome
  rfl

end BiSection

namespace PartialSection

variable {Sym W : Type}

/-- **`Option` 消失的判据：部分截面是同构 ⟺ 每个权重都在像中。**

**⇒ 两个方向都有内容：**
- **（→）若存在同构 `B` 且 `P.extract = some ∘ B.extract`，则 `w = P.compile (B.extract w)`，
  故 `w` 在像中——这不是形式游戏，它说明「同构」等价于「权重侧没有额外信息」。**
- **（←）若每个权重都在像中，则可用 `compile_eq_of_mem_range` 造出全的逆：
  `B.extract w` 取使 `P.extract w = some ·` 成立的那个见证（存在性由像 + `retract` 给出）。**

**⇒ 于是「为什么权重那一跳要 `Option`、而层那一跳不要」有了唯一答案：
因为 `IRWeights` 携带的信息比 `IRSkeleton` 多（`extract_injective` 不成立），而 `Layer` 与
`ConstraintSet` 互相编码、不多不少。** -/
theorem isIso_iff_image_total (P : PartialSection Sym W) :
    (∀ w : W, w ∈ Set.range P.compile) ↔
      ∃ B : BiSection Sym W, B.compile = P.compile ∧ ∀ w : W, P.extract w = some (B.extract w) := by
  classical
  constructor
  · intro hmem
    -- **每个权重都在像中，故 `P.extract w` 对每个 `w` 都成功；取其见证作为全的逆。**
    have htot : ∀ w : W, ∃ s : Sym, P.extract w = some s := by
      intro w
      obtain ⟨s, rfl⟩ := hmem w
      exact ⟨s, P.retract s⟩
    let inv : W → Sym := fun w => Classical.choose (htot w)
    have hinv : ∀ w : W, P.extract w = some (inv w) := fun w => Classical.choose_spec (htot w)
    refine ⟨{ compile := P.compile, extract := inv, left := ?_, right := ?_ }, rfl, hinv⟩
    · intro s
      have h1 : P.extract (P.compile s) = some (inv (P.compile s)) := hinv _
      rw [P.retract s] at h1
      exact (Option.some.inj h1).symm
    · intro w
      exact P.compile_eq_of_mem_range (hinv w) (hmem w)
  · rintro ⟨B, hB, hc⟩ w
    refine ⟨B.extract w, ?_⟩
    have hw : B.compile (B.extract w) = w := B.right w
    rw [hB] at hw
    exact hw

end PartialSection

end Lattice.Core