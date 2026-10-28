/-
# `Compose/Combinators` —— 串联与恒等（**参数版**）

## 0. 参数化消掉的是 **cast**，不是**兼容性义务**

字段版里 `compose` 有两个附加参数：`adapt : f.Output → g.Input` 与
`h : ∀ x y, f.post x y → g.pre (adapt y)`。

**它们承担的是两件不同的事**：

| 参数 | 它解决什么 | 参数化后还在吗 |
|:--|:--|:--|
| `adapt : f.Output → g.Input` | **类型不匹配**（`f.Output` 与 `g.Input` 是两个独立字段） | **不在了**——中间类型 `M` 由推断配出 |
| `h : ∀ x y, f.post x y → g.pre …` | **语义义务**：`f` 的后置必须蕴含 `g` 的前置 | **还在** |

**这是必须分清的一件事**：第 228 轮的实测报错是类型错误（`g.pre y` 的 `y` 类型不对），
但那只是**表象**；即使类型对上，`g.pre y` 也**不会**从 `f.post x y` 推出。
`sound` 需要 `g.pre y` 才能调用 `g.sound`，**所以 `h` 无论如何都得由调用方给。**

**本节按这个分清的结果写**：`compose` 无适配器、保留 `h`；`composeWith` 两者都有。

**参数化的真实收益有两处，都不是 `compose` 的 `h`**：
1. `compose` 不再需要 `adapt`；
2. **`identity_compose_run` 不再需要任何兼容性假设**（见 §2）——字段版需要它，因为 `id` 的
   `α` 无法与 `f.Input` 对上。

## 1. 交付

| 声明 | 内容 |
|:--|:--|
| **`compose`** | `Primitive I M` → `Primitive M O` →（`h`）→ `Primitive I O` |
| **`composeWith`** | 同上但带 `adapt : A → B`（§7 第 5 条的情形） |
| `compose_sound` / `composeWith_sound` | 串联保持正确性 |
| `compose_run` / `composeWith_run` | `run` 的展开式 |
| `compose_run_assoc` | `run` 的结合律（`Option.bind_assoc`） |
| `compose_strength` / `compose_coverage` | 强度取最小 / 覆盖取交 |
| **`identity`** | `Primitive α α`，`exact`，覆盖不限制 |
| `identity_compose_run` | **左单位**——**不需要任何兼容性假设** |

## 2. 左单位**仍需要 `h`** —— 参数化只省掉 `adapt`

**第一版写错了**：它说参数版下左单位的 `h` 可以「由 `trivial` 给出」。**不成立**。
`compose` 的 `h` 要求 `∀ x y, (identity I).post x y → f.pre y`，而 `(identity I).post x y` 是 `y = x`，
于是 `h` 要产出 `f.pre y`——**而 `f.pre` 是任意的，`y = x` 推不出它。** 实测报错：

```
type mismatch: trivial has type True
 but is expected to have type f.pre x✝¹
```

**准确的收益是「少一个参数」，不是「不用证明」**：

| 版本 | 调用形态 | 缺什么 |
|:--|:--|:--|
| 字段版 | `compose (identity α) f id h` | `α` 要对上 `f.Input`（靠 `id` 的类型推断）**且**给 `h` |
| **参数版** | `compose (identity I) f h` | **只给 `h`** |

`α` 与 `f.Input` 的配对由推断完成，**适配器 `id` 不需要写出来了**——这是参数化在这里的**全部**收益。
`h` 是语义义务，与类型无关，**两种版本都要给**。

## 3. 边界

- **不证结构相等**：`Primitive` 带 `sound` 证明项，所以
  `compose (compose f g) h = compose f (compose g h)` **不可证**（需要证明无关性）。
  `run` 层**可证**，而 `run` 才是使用者调用的东西。
- **`identity` 的覆盖是 `none`**：含义是「不限制」。 -/
import Mathlib
import Lattice.Compose.Primitive

namespace Lattice.Compose

/-! ## 一、串联（中间类型相同，无适配器） -/

/-- **串联**：`f` 的输出类型就是 `g` 的输入类型。

**没有适配器**——中间类型 `M` 由类型推断配出。
**`h` 仍在**：`f` 的后置必须蕴含 `g` 的前置，**这是语义义务，不是类型产物**（见 §0）。 -/
def compose {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ x y, f.post x y → g.pre y) : Primitive I O where
  pre := f.pre
  post := fun x z => ∃ y, f.post x y ∧ g.post y z
  run := fun x => (f.run x).bind g.run
  sound := by
    intro x hx
    obtain ⟨y, hfy, hfpost⟩ := f.sound x hx
    have hgpre : g.pre y := h x y hfpost
    obtain ⟨z, hgz, hgpost⟩ := g.sound y hgpre
    exact ⟨z, by simp only [Option.bind, hfy, hgz], y, hfpost, hgpost⟩
  strength := f.strength.min g.strength
  coverage := f.coverage.inter g.coverage
  frame := fun x z => ∃ y, f.frame x y ∧ g.frame y z

/-! ## 二、串联（中间类型不同，带适配器） -/

/-- **带适配器的串联**：§7 第 5 条「缺边用显式适配器」的情形。

`adapt : A → B` 把 `f` 的输出送成 `g` 的输入类型。 -/
def composeWith {I A B O : Type} (adapt : A → B) (f : Primitive I A) (g : Primitive B O)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) : Primitive I O where
  pre := f.pre
  post := fun x z => ∃ y, f.post x y ∧ g.post (adapt y) z
  run := fun x => (f.run x).bind (fun y => g.run (adapt y))
  sound := by
    intro x hx
    obtain ⟨y, hfy, hfpost⟩ := f.sound x hx
    have hgpre : g.pre (adapt y) := h x y hfpost
    obtain ⟨z, hgz, hgpost⟩ := g.sound (adapt y) hgpre
    exact ⟨z, by simp only [Option.bind, hfy, hgz], y, hfpost, hgpost⟩
  strength := f.strength.min g.strength
  coverage := f.coverage.inter g.coverage
  frame := fun x z => ∃ y, f.frame x y ∧ g.frame (adapt y) z

/-! ## 三、定律 -/

/-- **串联保持正确性。** -/
theorem compose_sound {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ x y, f.post x y → g.pre y) (x : I) (hx : f.pre x) :
    ∃ z, (compose f g h).run x = some z ∧ (compose f g h).post x z :=
  (compose f g h).sound x hx

/-- **带适配器的串联保持正确性。** -/
theorem composeWith_sound {I A B O : Type} (adapt : A → B)
    (f : Primitive I A) (g : Primitive B O)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) (x : I) (hx : f.pre x) :
    ∃ z, (composeWith adapt f g h).run x = some z ∧ (composeWith adapt f g h).post x z :=
  (composeWith adapt f g h).sound x hx

/-- **`run` 的展开式**（无适配器）。 -/
theorem compose_run {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ x y, f.post x y → g.pre y) (x : I) :
    (compose f g h).run x = (f.run x).bind g.run := rfl

/-- **`run` 的展开式**（带适配器）。 -/
theorem composeWith_run {I A B O : Type} (adapt : A → B)
    (f : Primitive I A) (g : Primitive B O)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) (x : I) :
    (composeWith adapt f g h).run x = (f.run x).bind (fun y => g.run (adapt y)) := rfl

/-- **串联的强度取最小**：组合不会让承诺变强。 -/
theorem compose_strength {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ x y, f.post x y → g.pre y) :
    (compose f g h).strength = f.strength.min g.strength := rfl

/-- **串联的覆盖取交集**：组合不会让覆盖变大。 -/
theorem compose_coverage {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ x y, f.post x y → g.pre y) :
    (compose f g h).coverage = f.coverage.inter g.coverage := rfl

/-- **`run` 的结合律**：`(f 然后 g) 然后 k` 与 `f 然后 (g 然后 k)` 的执行相同。

`Option.bind_assoc` 的直接推论。**只在 `run` 层成立**——结构层需要证明无关性，见 §3。

**右边写成显式三层 `bind`**：写成两个 `compose` 的相等要为右边再造兼容性证明，
而那些证明**不进入 `run`**。显式 `bind` 才是这条定律的**内容**。 -/
theorem compose_run_assoc {I A B C : Type}
    (f : Primitive I A) (g : Primitive A B) (k : Primitive B C)
    (h₁ : ∀ x y, f.post x y → g.pre y)
    (h₂ : ∀ y z, g.post y z → k.pre z)
    (h₃ : ∀ x z, (compose f g h₁).post x z → k.pre z) (x : I) :
    (compose (compose f g h₁) k h₃).run x
      = (f.run x).bind (fun y => (g.run y).bind (fun z => k.run z)) := by
  show ((f.run x).bind g.run).bind k.run
      = (f.run x).bind (fun y => (g.run y).bind (fun z => k.run z))
  exact Option.bind_assoc (f.run x) g.run k.run

/-! ## 四、恒等 -/

/-- **恒等 primitive**：`exact` 强度，覆盖不限制（`none`）。 -/
def identity (α : Type) : Primitive α α where
  pre := fun _ => True
  post := fun x y => y = x
  run := fun x => some x
  sound := fun x _ => ⟨x, rfl, rfl⟩
  strength := .exact
  coverage := none
  frame := fun _ _ => True

/-- **左单位**：`compose (identity I) f` 的 `run` 就是 `f` 的 `run`。

**`h` 仍是参数**——见 §2：`f.pre` 是任意的，`y = x` 推不出 `f.pre y`，
所以兼容性义务不能凭空消掉。参数化省掉的是 `adapt`（`α` 与 `f.Input` 的配对），**不是 `h`**。 -/
theorem identity_compose_run {I O : Type} (f : Primitive I O)
    (h : ∀ x y, (identity I).post x y → f.pre y) (x : I) :
    (compose (identity I) f h).run x = f.run x := by
  show (some x).bind f.run = f.run x
  rfl

end Lattice.Compose
