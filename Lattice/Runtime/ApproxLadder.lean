/-
# `ApproxLadder`：带**有界** token 往返的阶梯

## 0. 为什么需要它

`Ladder.l1l2 : Tokenizer Sym Tok` 要求**等式** `decode (encode s) = some s`。
第 144–153 轮为 `EqConstraint` 造出了这样的 tokenizer，**所以精确阶梯是真的。**

**但目标的逆向方向不可能总是精确的**：`Extraction.no_extractor_both_layers` 证明
**不存在同时对参数层与语义层忠实的提取器**。真实系统因此跑在**有界**提取上，
而 `ApproxRepresentation` 就是这个陈述。

## 1. 它接上了一条孤岛

**第 159 轮的结构扫描发现**：`Lift/ApproxExtraction.lean` 与 `Lift/RatRepresentation.lean`
**只被聚合文件 `Lift.lean` import**，而 `ApproxRepresentation` 只在**这两个文件**里出现。
**整条「有界提取」线是正确的、证明过的、从任何地方都不可达。**

**本节给它一个使用者**：`ApproxLadder` 的 `l1l2` 是一个 `ApproxRepresentation`，
于是端到端定理**把误差界带进结论**，而不是假设掉。

## 2. 为什么端到端陈述必须与精确版不同

`Ladder` 里 `ladder_forward` 的结论是 `satW (l2l3 s)`，**对往返一字不提**，
因为 `Tokenizer.roundtrip` 是**等式**——没有可陈述的东西。

**有界往返则不然**：token 往返最多损失 `ε`。所以结论是一个合取——
**正向保真 ∧ 往返界**。**去掉任一半，定理就比实际情况弱。**

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| **`approx_ladder_forward`** | **`satW (l2l3 s) ∧ dist (extract (compile s)) s ≤ ε`** |
| `approx_ladder_eps_nonneg` | `0 ≤ ε` |
| `approx_ladder_bound_mono` | 界对 `s` 一致 |

## 4. 实例

`roundingLadder`：`Sym = W = Data 元素 = ℤ`，token 跳是舍入后端（`ε = 1`）。
**这让有界线可被实例化，而不只是一个抽象框架。**

## 5. 边界

- **`l2l3_sound` 与精确版完全相同**：正向义务不受近似影响，**这正是两侧可以共存的原因**。
- **本节不声称「近似阶梯能替代精确阶梯」**：它声称两者都能被陈述，且精确性是 `ε = 0` 的特例
  （`ApproxExtraction.ofRepresentation` 已证）。
- `approx_ladder_bound_mono` 的陈述**目前是重言式**（结论与 `bounded` 相同）：
  它记录的意图是「界是唯一随实例变化的部分」。**真正的单调性需要 `ε' ≤ ε` 的实例构造，未做。**
- **本节只把有界线从「谁都不 import」推进到「被 `ApproxLadder` import」——`ApproxLadder` 自己
  仍然只被聚合文件 import。** 严格地说：**有界提取现在离目标近了一层，但还没有被目标链路使用。**
  真正的接线是给 `geoLadder` 一个近似版本，或让某个 `Ladder` 实例的 `l1l2` 用 `ApproxRepresentation`。
  **这一条是本节之后最诚实的剩余项。**
-/
import Mathlib
import Lattice.Runtime.EndToEnd
import Lattice.Runtime.ApproxExtraction
import Lattice.Runtime.RoundingBackend

open Lattice.Lift.ApproxExtraction

namespace Lattice.Lift

variable {Data Tok Sym W : Type}

/-- **The ladder with a bounded token round-trip.**

Identical to `Ladder` except that `l1l2` is an `ApproxRepresentation`, so the L1<->L2 rung carries an
error bound ε instead of an equation. -/
structure ApproxLadder (Data Tok Sym W : Type) where
  /-- L0 -> L1. -/
  l0l1 : Tokenizer Data Tok
  /-- **L1 <-> L2, with an error bound.** -/
  l1l2 : ApproxRepresentation Sym Tok
  /-- L2 -> L3. -/
  l2l3 : Sym → W
  /-- What it means for a symbolic form to accept a point. -/
  satSym : Sym → Prop
  /-- What it means for a weight artifact to accept a point. -/
  satW : W → Prop
  /-- **L2 -> L3 obligation**, unchanged from `Ladder`. -/
  l2l3_sound : ∀ s : Sym, satSym s → satW (l2l3 s)

namespace ApproxLadder

variable (L : ApproxLadder Data Tok Sym W)

/-- **End-to-end, with the bound kept.**

Two conjuncts, and each comes from a different premise:

* `satW (L.l2l3 s)` from `l2l3_sound` -- forward fidelity, the same obligation as the exact ladder;
* `L.l1l2.dist (L.l1l2.extract (L.l1l2.compile s)) s ≤ L.l1l2.ε` from `ApproxRepresentation.bounded`
  -- what the bounded rung contributes.

They hold at the SAME `s`, and that is the point: the forward direction does not get to ignore the
approximation the inverse direction has to live with. -/
theorem approx_ladder_forward (s : Sym) (h : L.satSym s) :
    L.satW (L.l2l3 s) ∧
      L.l1l2.dist (L.l1l2.extract (L.l1l2.compile s)) s ≤ L.l1l2.ε :=
  ⟨L.l2l3_sound s h, L.l1l2.bounded s⟩

/-- **The bound is nonnegative**, so a caller can read it as an error budget. -/
theorem approx_ladder_eps_nonneg : 0 ≤ L.l1l2.ε :=
  L.l1l2.hε

/-- **Monotonicity in the bound: a looser budget is still an upper bound.**

第 199 轮之前这条的结论是 ≤ L.l1l2.ε 而假设是 ε' ≤ L.l1l2.ε——**假设与结论无关**，
证明只是 L.l1l2.bounded s，所以「单调」是假的：把一个更紧的 ε' 传进来，
结论仍然报原来那个界。

**方向本来就该反过来**：单调性说的是「界可以放宽」。ε ≤ ε' 时同一个误差
仍然 ≤ ε'，这才是 le_trans。现在的证明用了假设，**不再是重言**。

反过来（收紧）不是单调性，是**重新测量**——那需要更紧的 ounded，
不是从旧的界推出来的。 -/
theorem approx_ladder_bound_mono {ε' : ℝ} (hε' : L.l1l2.ε ≤ ε')
    (s : Sym) :
    L.l1l2.dist (L.l1l2.extract (L.l1l2.compile s)) s ≤ ε' :=
  le_trans (L.l1l2.bounded s) hε'

end ApproxLadder

/-! ## An instance: the rounding backend

`Lift/RoundingBackend` proves `roundingIsApprox : ApproxRepresentation ℤ ℤ` with `ε = 1`. Putting it
in an `ApproxLadder` makes the bounded line reachable: the instance below exists, and any theorem
about `ApproxLadder` applies to it. -/

/-- **The rounding ladder**: `Sym = W = Data element = ℤ`, and the token rung is the rounding
backend, so going sym → token → sym can move a value by at most 1. -/
noncomputable def roundingLadder : ApproxLadder (List ℤ) ℤ ℤ ℤ where
  l0l1 := identityTokenizer ℤ
  l1l2 := ApproxExtraction.roundingIsApprox
  l2l3 := id
  satSym := fun k => k = 0
  satW := fun k => k = 0
  l2l3_sound := by
    intro s h
    exact h

/-- **The rounding ladder's end-to-end statement, as a concrete corollary.** -/
theorem roundingLadder_forward (k : ℤ) (h : k = 0) :
    (roundingLadder.satW (roundingLadder.l2l3 k) ∧
      roundingLadder.l1l2.dist
        (roundingLadder.l1l2.extract (roundingLadder.l1l2.compile k)) k ≤
        roundingLadder.l1l2.ε) :=
  roundingLadder.approx_ladder_forward k h

/-- **Its ε is 1**, so the corollary's bound is a real number, not a symbol. -/
theorem roundingLadder_eps : roundingLadder.l1l2.ε = 1 := rfl

end Lattice.Lift
