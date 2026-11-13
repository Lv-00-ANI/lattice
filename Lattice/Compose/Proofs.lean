/-
# The `Compose` plugin's proofs -- MOVED from `Lattice/Compose/Laws.lean`

**`Compose`'s combinator laws: the unit, associativity and commutation lemmas that the plugin's
obligation list names.**

**Same discipline as the two previous migrations: the DECLARATIONS do not change at all --
same names, same statements, same proofs, same namespace -- so no downstream file needs
editing for the move itself.**

The old path is now a facade that imports this file and contains no proof.
-/

/-
# `Compose/Laws` —— 组合子之间的交互律

## 0. 为什么要有这个文件

`Combinators`/`More`/`Iterate` 各自证了自己那条组合子的定律（`sound`、强度、覆盖、`run` 展开）。
**但那些都是「单个组合子的性质」，不是「组合子之间的关系」。**

没有后者，「组合代数」就只是一堆能用的函数——**而 §5 说 `Compose` 提供的是组合子，
它就必须说明这些组合子怎么互相作用**，否则用户无法把简单组合子的已证结论推给复杂组合。

## 1. 本轮的承重定理：`compose` 对 `choice` 分配

**内容**：

```
compose (choice f g sel) h   ≡   choice (compose f h) (compose g h) sel     （在 run 上）
```

**为什么它成立**：`Option.bind` 对 `if` 分配：

```
(if c then a else b).bind k  =  if c then a.bind k else b.bind k
```

左边是「先选一支再串 `h`」，右边是「两支各自串好 `h` 再选」。**两者在执行上相同。**

**这条为什么重要**：它让「选之后串」可以改写成「串之后选」——
后者每一支都是 `compose`，**因此每一支的已证性质（`compose_sound`、强度 `min`、覆盖 `inter`）
可以分别使用**。没有这条，用户面对 `compose (choice …) h` 只能整块重证。

**范围**：只在 `run` 上成立。`post` 与 `pre` 的形状不同（`choice` 的 `pre` 按派发分情况），
所以结构相等**不成立**也不该声称（见 §3）。

## 2. 其余定律

| 定理 | 内容 |
|:--|:--|
| `parallel_run` | `parallel` 的 `run` 展开 |
| **`parallel_comm_run`** | **交换两路输入 ⟹ 输出取反序** |
| `parallel_identity_run` | 两个恒等并行 = 恒等 |
| **`choice_self_run`** | 选自己两次 = 只跑一次 |
| `optional_true_run` / `optional_false_run` | 判定永真 = 直接跑；永假 = 恒等 |
| **`compose_identity_right`** | **右单位**：`compose f (identity O)` 与 `f` 同 `run` |
| **`compose_choice_distrib_run`** | **§1 的分配律** |

## 3. 边界

- **全部是 `run` 层定律。** 不证结构相等：`Primitive` 带 `sound` 证明项，
  两个 primitive 的 `sound` 不会定义相等（需要证明无关性）。
- **`parallel` 的结合律不证**：`parallel (parallel f g) h` 与 `parallel f (parallel g h)` 的输出
  是 `((y,z),w)` 与 `(y,(z,w))`，**差一次重结合**。要证得引入 `Prod` 结合映射，
  那会让定律变成「差一个显式重结合」而不是「相等」——**写成后者会是一句空话**。
- **`choice` 与 `parallel` 的交换律不证**：它们的输入形状不同（一个是 `I`，一个是 `I₁ × I₂`），
  没有共同的类型去陈述交换。**这不是没做，是没有这条定律。** -/
import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
import Lattice.Compose.More

namespace Lattice.Compose

/-! ## 一、`parallel` 的定律 -/

/-- **`parallel` 的 `run` 展开式。** -/
theorem parallel_run {I₁ O₁ I₂ O₂ : Type} (f : Primitive I₁ O₁) (g : Primitive I₂ O₂)
    (a : I₁) (b : I₂) :
    (parallel f g).run (a, b)
      = (f.run a).bind (fun y => (g.run b).map (fun z => (y, z))) := rfl

/-- **交换两路输入，输出取反序。**

**两路互不依赖**，所以顺序可以换。证明靠对两个 `Option` 分别分情况：
`f.run a` 与 `g.run b` 各有成功/失败两种，四种情形都由 `simp` 收掉。 -/
theorem parallel_comm_run {I₁ O₁ I₂ O₂ : Type} (f : Primitive I₁ O₁) (g : Primitive I₂ O₂)
    (a : I₁) (b : I₂) :
    (parallel f g).run (a, b) = ((parallel g f).run (b, a)).map Prod.swap := by
  simp only [parallel_run, Option.bind_eq_bind, Option.map_eq_map]
  cases h1 : f.run a <;> cases h2 : g.run b <;> simp [h1, h2]

/-- **两个恒等并行 = 恒等**（在 `run` 上）。 -/
theorem parallel_identity_run (I O : Type) (a : I) (b : O) :
    (parallel (identity I) (identity O)).run (a, b) = some (a, b) := by
  simp [parallel_run, identity]

/-! ## 二、`choice` 与 `optional` 的定律 -/

/-- **选自己两次 = 只跑一次。** -/
theorem choice_self_run {I O : Type} (f : Primitive I O) (sel : I → Bool) (x : I) :
    (choice f f sel).run x = f.run x := by
  cases h : sel x <;> simp [choice, h]

/-- **判定永真 ⟹ 直接跑 `p`。** -/
theorem optional_true_run {I : Type} (p : Primitive I I) (x : I) :
    (optional p (fun _ => true)).run x = p.run x := by
  simp [optional]

/-- **判定永假 ⟹ 恒等。** -/
theorem optional_false_run {I : Type} (p : Primitive I I) (x : I) :
    (optional p (fun _ => false)).run x = some x := by
  simp [optional]

/-! ## 三、`compose` 的单位律与分配律 -/

/-- **右单位**：`compose f (identity O)` 与 `f` 的 `run` 相同。

（左单位在 `Combinators.lean` 的 `identity_compose_run`。） -/
theorem compose_identity_right {I O : Type} (f : Primitive I O)
    (h : ∀ x y, f.post x y → (identity O).pre y) (x : I) :
    (compose f (identity O) h).run x = f.run x := by
  show (f.run x).bind (fun y => some y) = f.run x
  rw [Option.bind_some]

/-- **`Option.bind` 对 `if` 分配**——§1 那条承重定理的**唯一实质步骤**。

`(if c then a else b).bind k = if c then a.bind k else b.bind k`。
`Bool` 只有两个值，所以两次 `cases` 就够。 -/
theorem bind_ite (c : Bool) (a b : Option α) (k : α → Option β) :
    (if c then a else b).bind k = if c then a.bind k else b.bind k := by
  cases c <;> simp

/-- **`compose` 对 `choice` 分配**（§1 的承重定理，`run` 层）。

**左边**：先选一支，再串 `h`。
**右边**：两支各自串好 `h`，再选。

**相等的理由**就是 `bind_ite`：`run` 的 `if` 与 `bind` 可以交换次序。
**这条让「选了之后的已证性质」可以分给每一支使用。** -/
theorem compose_choice_distrib_run {I M O : Type} (f g : Primitive I M) (h : Primitive M O)
    (sel : I → Bool)
    (hc : ∀ x z, (choice f g sel).post x z → h.pre z)
    (h₁ : ∀ x y, f.post x y → h.pre y)
    (h₂ : ∀ x y, g.post x y → h.pre y) (x : I) :
    (compose (choice f g sel) h hc).run x
      = (choice (compose f h h₁) (compose g h h₂) sel).run x := by
  show ((choice f g sel).run x).bind h.run
      = (if sel x then (f.run x).bind h.run else (g.run x).bind h.run)
  show ((if sel x then f.run x else g.run x)).bind h.run = _
  rw [bind_ite]

end Lattice.Compose
