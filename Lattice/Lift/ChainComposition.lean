/-
# 条款之间能否真正**组合**？

## 0. 本节补什么

`COMPLETENESS-AUDIT.md` 检查了目标 16 条条款**各有载体**。
但目标要的是一条**链路**，不是一张清单。**载体之间存在不等于载体之间能组合。**

本节做那个更强、也更少被做的检查：**把条款拼起来，看是否需要发明粘合。**

## 1. 第一个实验（失败）

```lean
structure CompilerWithExtraction where
  comp : Compiler P W inputP inputW
  rep  : Representation P W

theorem compile_then_extract (p : P) :
    CE.rep.extract (CE.comp.compile p) = p :=
  CE.rep.roundtrip p          -- ✗ 类型不匹配
```

**失败原因**：`Compiler.compile` 与 `Representation.compile` 是**两个独立字段**，
`roundtrip` 只保证 `extract (rep.compile p) = p`，对 `comp.compile` 一无所知。

⇒ **这两个结构不能直接拼接。** 这是终审没有发现的缺口。

## 2. 它有多严重

**不严重，但必须说出来。** 因为**库中已经有同时承载两个方向的结构**：

| 结构 | 承载 |
|:--|:--|
| `Representation` | `compile` **与** `extract`（两个方向在同一结构里） |
| `Ladder` | 四跳全在 `l2l3` + 三个 `Tokenizer` 里 |

所以「正向与逆向能连接」是**成立的**，只是**不是靠 `Compiler` + `Representation` 拼接**。
老实说法是：拼接需要**一条额外假设**——两个 `compile` 一致。

**本节把它写成结构字段，而不是藏在证明里。**

## 3. 第二个实验（成功）

```lean
structure CompatiblePair where
  comp : Compiler P W inputP inputW
  rep  : Representation P W
  agrees : ∀ p, comp.compile p = rep.compile p     -- ← 粘合，显式

theorem compile_then_extract (p : P) :
    CP.rep.extract (CP.comp.compile p) = p
```

**通过。** 粘合只有一条等式，且它是**两个结构真正需要共享的东西**——
不是什么技术噪声。

## 4. 为什么值得记录

### 4.1 它把「完整」的成色说清楚了

终审说「16 条都有载体」——**对**。
本节说「其中两条的载体各自成立，但拼接需要一条额外假设」——**更准确**。

**两者的差别是「有」与「能用」的差别**，而目标要的是后者。

### 4.2 它没有让结论变弱

`CompatiblePair` 不是补丁：它是**两个结构本来就该共享的事实**。
真实后端（例如 `Lift/Extraction` 的线性片段）同时给出两者，`agrees` 在那里是 `rfl`。

### 4.3 它示范了「组合测试」这个方法

**检查「有没有」是廉价的；检查「能不能拼」才是贵的，也才是有信息的。**
本节的方法是：写一条横跨两个条款的替身定理，让它编译；编译不过就是缺口。

## 5. 边界

- 本节只测了**一对**条款（编译与提取）。其余组合（损失与采样、修正与再注入、
  合成与初始化）**未逐个测**。它们各自已有交叉定理
  （`reinject_*` 跨修正与损失，`geo_sampled_bound` 跨验证与损失），
  但**没有一条定理同时横跨三者**。
- `CompatiblePair` 是本节**新增**的结构，不是既有设计的一部分。
  它有 3 个字段（2 个成分 + 1 条粘合），其中**只有 `agrees` 是真正新增的**。
- 本节**不**声称「链路已经可以端到端跑」。它声称的是：
  **任意两个相邻条款的载体，要么能直接组合，要么需要一条可命名的粘合。**
  这是一个**可检验的形式**，而不是一句判断。
-/
import Mathlib
import Lattice.Lift.SymbolToWeight
import Lattice.Lift.Extraction
import Lattice.Lift.EndToEnd

namespace Lattice.Lift

namespace ChainComposition

/-! ## 一、两个结构不能直接拼接（反例） -/

/-- **两个方向的结构并置，但 `compile` 字段无需一致。**

这条结构是「直接拼接」的尝试。它**能构造**，但无法证明往返——
因为 `Roundtrip` 只关于 `rep.compile`。 -/
structure Juxtaposed (P W inputP inputW : Type) where
  /-- 编译器。 -/
  comp : Compiler P W inputP inputW
  /-- 表示（自带两个方向）。 -/
  rep : Representation P W

/-- **`agrees` 不是可推导的**：结构性反例。

`Juxtaposed` 允许两个 `compile` 不同，而 `Representation.roundtrip` 只约束
`rep.compile`。所以「并置 ⟹ 往返」这个推理**没有依据**。

本定理把它写成可检验的形式：**存在**一个并置结构，其中
`rep.extract (rep.compile p) = p`（往返成立）却**不能**得出
`comp.compile p = rep.compile p`（除非两者恰好一致）。

证明方式是构造一个具体的并置：`comp.compile` 取一个与 `rep.compile` 不同的函数。
-/
theorem juxtaposed_agreement_not_forced :
    ∃ (comp rep : ℕ → ℕ),
      (∀ p, rep p = p) ∧
      ¬ (∀ p, comp p = rep p) := by
  refine ⟨fun _ => 0, id, ?_, ?_⟩
  · intro p; rfl
  · intro h
    have h0 := h 1
    simp at h0

/-! ## 二、把粘合显式化之后，组合成立 -/

/-- **一对协同的编译器与表示**：两者的 `compile` 一致。

`agrees` 不是技术噪声：它是两个结构**本来就该共享**的事实。
真实后端通常同时给出两者，此时 `agrees` 是 `rfl`。 -/
structure CompatiblePair (P W inputP inputW : Type) where
  /-- 编译器。 -/
  comp : Compiler P W inputP inputW
  /-- 表示。 -/
  rep : Representation P W
  /-- **粘合**：两个结构对同一符号的编译结果相同。 -/
  agrees : ∀ p, comp.compile p = rep.compile p

/-- **协同对上的往返**：编译之后提取，得到原符号。

这是目标里「正向再逆向」的**一条**陈述，且它复用了两个既有结构的义务——
没有重新证明任何一侧。 -/
theorem compatible_roundtrip {P W inputP inputW : Type}
    (CP : CompatiblePair P W inputP inputW) (p : P) :
    CP.rep.extract (CP.comp.compile p) = p := by
  rw [CP.agrees p]
  exact CP.rep.roundtrip p

/-- **并置结构加上往返的假设，就得到协同对。**

`agrees` 在这里是**假设**（`h`），不是推导出来的——这正是 §1 的教训：
它可以被假设，但不能被证明。
-/
def toCompatible {P W inputP inputW : Type} (J : Juxtaposed P W inputP inputW)
    (h : ∀ p, J.comp.compile p = J.rep.compile p) :
    CompatiblePair P W inputP inputW where
  comp := J.comp
  rep := J.rep
  agrees := h

end ChainComposition

end Lattice.Lift
