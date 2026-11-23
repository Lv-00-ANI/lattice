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


/-! ## 三、**单射本身就给出**一个规范的部分截面

**这一节回答的是「`PartialSection` 是不是一个凭空的抽象」。不是：**

**⇒ 任何单射 `f : Sym → W` 都**规范地**给出一个部分截面**（`of_injective`）：在像上取前像，在像外返回 `none`。**
**⇒ 于是 `Option` 的 `none` 分支不再是「留白」，而是一条**定理**：
`none` 恰好落在**像的补集**上（`of_injective_extract_none_iff`）。**

**⇒ 而这与 `Lib/Compiler/HopVerdict.lean` 的 `hop_verdict` 第 1 项正好构成对照：**
那一项说「单射 ⟺ 存在**全**的 `extract`」——它成立**只因为**那里假定了一个默认元素
（`[Inhabited S]`），于是像外可以填默认值。
**⇒ 没有默认值时，同一个构造只能返回 `Option`。** **这就是本项目选择 `Option` 的全部理由：
它是「没有默认值可用」的诚实版本，而不是把默认值伪装成答案。** -/

namespace PartialSection

variable {Sym W : Type}

/-- **由单射**规范地**得到一个部分截面。**

**`extract w` 的定义：若 `w` 有前像则给它的（唯一）前像，否则 `none`。**
**⇒ 「唯一」来自 `hf`，这正是单射性在这里的作用。** -/
noncomputable def of_injective (f : Sym → W) (hf : Function.Injective f) :
    PartialSection Sym W where
  compile := f
  extract := fun w => by
    classical
    exact if h : ∃ s : Sym, f s = w then some h.choose else none
  retract := by
    classical
    intro s
    have hex : ∃ s' : Sym, f s' = f s := ⟨s, rfl⟩
    simp only [dif_pos hex]
    exact congrArg some (hf hex.choose_spec)
  compile_injective := hf

/-- **`none` 的准确含义：它恰好落在像的补集上。**

**⇒ 这是本轮问题的答案。`Option` 的失败分支不是「未定义行为」，
而是**与像的补集相等**这一条定理；因此调用者只要知道「这个权重是编译出来的」，
就知道 `none` 不会出现（`isSome_retract`）。** -/
theorem of_injective_extract_none_iff (f : Sym → W) (hf : Function.Injective f) (w : W) :
    (of_injective f hf).extract w = none ↔ w ∉ Set.range f := by
  classical
  constructor
  · intro hn hmem
    obtain ⟨s, rfl⟩ := hmem
    have hs : (of_injective f hf).extract (f s) = some s := (of_injective f hf).retract s
    rw [hn] at hs
    exact Option.noConfusion hs
  · intro hout
    show (if h : ∃ s : Sym, f s = w then some h.choose else none) = none
    rw [dif_neg]
    rintro ⟨s, hs⟩
    exact hout ⟨s, hs⟩


/-- **`Option` 永不失败 ⟺ 映射满射。**

**⇒ 这是本节与 `BiSection` 的接口，也是「默认值」这件事的准确条件：
只有当每个权重都是某个符号编译出来的时候，才不需要默认值，`Option` 才恒为 `some`。**

**⇒ 与 `hop_verdict` 第 1 项对照读：那一项在 `[Inhabited Sym]` 下把部分 `extract` 变成全 `extract`，
代价是在**像外**填一个默认符号——那个符号**不是**提取出来的。本定理说明：
若不想付这个代价，就必须要求满射；而 `IRSkeleton → IRWeights` 并**不满射**
（`extract_not_injective` 的另一面：位置 1 的值与提取无关）。** -/
theorem of_injective_surjective_iff_never_none (f : Sym → W) (hf : Function.Injective f) :
    Function.Surjective f ↔ ∀ w : W, (of_injective f hf).extract w ≠ none := by
  constructor
  · intro hsur w hn
    have hmem : w ∈ Set.range f := hsur w
    have hnot : w ∉ Set.range f := (of_injective_extract_none_iff f hf w).mp hn
    exact hnot hmem
  · intro hnever w
    by_contra hnot
    exact hnever w ((of_injective_extract_none_iff f hf w).mpr hnot)

end PartialSection

end Lattice.Core