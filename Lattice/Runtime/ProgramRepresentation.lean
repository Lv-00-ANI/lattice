import Mathlib
import Lattice.Runtime.PartialRepresentation
import Lattice.Runtime.ProgramAST

/-!
# `Lattice.Runtime.ProgramRepresentation` — **把 `ProgramAST` 那条「被否决的路线」走通**

## 被否决的是什么，为什么当时否决是对的

`Runtime/ProgramAST.lean` L244 有一节标题：

> **为什么不建 `Representation`：一条被否决的路线**

里面的理由**完全成立**：

- `Representation.roundtrip : ∀ p, extract (compile p) = p` 要求 `extract` 是**全局逆**，
  返回类型是 `LayerProgram n`，**不是 `Option`**；
- 而解码在遇到**非法流**时**必然失败**——**`Representation` 里没有 `Option` 的位置**。

⇒ **在只有 `Representation` 的时候，这条路是死的。** 那个判断正确。

## 但第 60 轮补上了那个位置

`Lattice.Lift.PartialRepresentation` 的往返律是

```lean
roundtrip : ∀ p w, compile p = some w → extract w = some p
```

**两侧都带 `Option`。** 于是「解码可能失败」**不再是一个障碍**——
它只是 `extract` 返回 `none` 的那些输入。

**L244 的否决因此只对 `Representation` 成立，对整个表示层不成立。**
本文件把那条路线走通，而**不改动 `ProgramAST.lean` 的任何定义**。

## 语义用 `Option` 值，所以 `Y := Option (Fin n → ℝ)`

程序语义是 `evalProgram x p : Fin n → ℝ`——**一个函数，不是命题**。
而权重侧 `List ℝ` 的语义是「它解码成哪个程序，再求值」，**那件事可能失败**。

所以：

- `denoteP p x := some (evalProgram x p)`；
- `denoteW ws x := (decodeProgram hn ws).map (fun q => evalProgram x q)`。

**⇒ `compile_preserves` 就是 `ProgramAST.evalProgram_encodeProgram`**——不是"由它推出"，是**它就是**。

## 本文件给什么

1. `SemanticPartialRepresentation P W X Y` —— **偏表示 + 值语义**（`Y` 是一般的值类型，
   `Y := Prop` 就退化成 `SemanticRepresentation` 的形状）；
2. ⭐ `programPartial : PartialRepresentation (LayerProgram n) (List ℝ)` —— **被否决的那条路线**；
3. ⭐ `programSemantic : SemanticPartialRepresentation (LayerProgram n) (List ℝ)
   (Fin n → ℝ) (Option (Fin n → ℝ))` —— **语义挂上去了**。

## ⚠ 本文件**不**做的

- **不改 `ProgramAST.lean`**：`encodeProgram`/`decodeProgram`/`evalProgram` 一个字都没动。
- **不声称 `Representation` 也能承载它**：那条被否决的路线**对 `Representation` 仍然关闭**，
  本文件用的是 `PartialRepresentation`。
- **不涉及训练**：这里只有「程序 → 参数 → 反解析 → 求值」，没有梯度、没有损失。
-/

namespace Lattice.Lift

/-! ## 带值语义的偏表示 -/

/-- ⭐ **带语义的偏表示**：`denoteP`/`denoteW` 取一般的值类型 `Y`，不是只取 `Prop`。

**为什么一般化 `Y`**：`ConstraintSet` 的语义是命题（"这个点满不满足"），
而程序的语义是**函数**（`evalProgram x p : Fin n → ℝ`）。
**用 `Prop` 会把后者挡住**，所以 `Y` 是参数；取 `Y := Prop` 就回到 `SemanticRepresentation` 的形状。

`compile_preserves` 说的是：**一旦编译成功，两侧的语义值相等**——
**它不承诺编译一定成功**（那是 `compile : P → Option W` 的事）。 -/
structure SemanticPartialRepresentation (P W : Type) (X : Type) (Y : Type)
    extends PartialRepresentation P W where
  /-- 符号侧语义：给定输入点，得到语义值。 -/
  denoteP : P → X → Y
  /-- 权重侧语义：给定输入点，得到语义值。 -/
  denoteW : W → X → Y
  /-- ⭐ **编译保语义**：编译成功时两侧语义值相等。 -/
  compile_preserves : ∀ p w, compile p = some w → ∀ x, denoteP p x = denoteW w x

/-! ⚠ **本结构刻意不附带「辅助定理」。**

第一稿写了两条，都删了：

    theorem denote_of_extract ... := R.compile_preserves p w hw x      -- 字段的重述
    theorem no_claim_on_failure ... : True := trivial                  -- 证明 `True`

**第一条是别名**（`compile_preserves` 本身就是它）；**第二条什么都没说**——
「编译失败时无语义义务」这句话**只能靠读 `compile_preserves` 的前提来理解，不能被"证明"**，
写一条 `True` 的定理会让人以为有一条内容。 -/

end Lattice.Lift

/-! ## 实例：`LayerProgram n` ⇄ `List ℝ` -/

namespace Lattice.Lift

namespace ProgramAST

open Lattice.Lift (PartialRepresentation SemanticPartialRepresentation)

/-- ⭐⭐ **`LayerProgram n` 到 `List ℝ` 的偏表示** —— **`ProgramAST` L244 那条「被否决的路线」**。

- `compile p := some (encodeProgram hn p)` —— **编码是全的**；
- `extract ws := decodeProgram hn ws` —— **解码可能失败**（非法流给 `none`）；
- `roundtrip`：**`decodeProgram_encodeProgram`**。

**L244 说「`Representation` 没有 `Option` 的位置」，那句话对 `Representation` 是对的；
`PartialRepresentation` 就是那个位置。** -/
noncomputable def programPartial {n : ℕ} (hn : 0 < n) :
    PartialRepresentation (LayerProgram n) (List ℝ) where
  compile := fun p => some (encodeProgram hn p)
  extract := fun ws => decodeProgram hn ws
  roundtrip := by
    intro p w hw
    simp only [Option.some.injEq] at hw
    subst hw
    exact decodeProgram_encodeProgram hn p

/-- ⭐⭐ **程序的语义化偏表示**：程序 ⇄ 参数，语义是「求值」。

`denoteP p x := some (evalProgram x p)`；
`denoteW ws x := (decodeProgram hn ws).map (fun q => evalProgram x q)`。

**`compile_preserves` 就是 `evalProgram_encodeProgram`**——
「编码后再解码再求值，等于直接求值」，而那条定理在 `ProgramAST` 里已经证过。
**本文件没有重新证它，只是把它放到结构里的正确位置。** -/
noncomputable def programSemantic {n : ℕ} (hn : 0 < n) :
    SemanticPartialRepresentation (LayerProgram n) (List ℝ)
      (Fin n → ℝ) (Option (Fin n → ℝ)) where
  toPartialRepresentation := programPartial hn
  denoteP := fun p x => some (evalProgram x p)
  denoteW := fun ws x => (decodeProgram hn ws).map (fun q => evalProgram x q)
  compile_preserves := by
    intro p w hw x
    simp only [programPartial, Option.some.injEq] at hw
    subst hw
    show some (evalProgram x p)
      = Option.map (fun q => evalProgram x q) (decodeProgram hn (encodeProgram hn p))
    exact (evalProgram_encodeProgram hn p x).symm


end ProgramAST

end Lattice.Lift
