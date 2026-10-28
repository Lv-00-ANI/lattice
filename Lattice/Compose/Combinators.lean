/-
# `Compose/Combinators` —— 组合子与它们的定律（P0）

## 0. ⚠ 先说一处**设计文档的签名错误**，本节修正了它

`DIRECTORY-DESIGN.md` §6 写的是

```lean
def compose (f g : Primitive) (h : ∀ x y, f.post x y → g.pre y) : Primitive
```

**这个签名不可类型化。** `f : Primitive` 的 `Output` 与 `g : Primitive` 的 `Input` 是**两个独立的
`Type` 字段**，结构里没有任何东西强制它们相等，所以 `g.pre y` 里的 `y : f.Output` 通不过类型检查。

实测报错（本文件第一版）：

```
error: application type mismatch
  g.pre y
argument y has type f.Output : Type
but is expected to have type g.Input : Type
```

§7 第 1 条说「所有 `Input/Output` 都是 `Kernel` 类型」——**那不等于同一个类型**。
§7 第 5 条自己说了「缺边用显式适配器」，所以正确的签名必须**显式带适配器**：

```lean
def compose (f g : Primitive) (adapt : f.Output → g.Input)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) : Primitive
```

**适配器不是可选的语法糖，是这条组合能成立的前提**——这是 §7 第 5 条在类型上的必然结果。
本节按修正后的签名实现。

## 1. 交付

| 声明 | 内容 |
|:--|:--|
| **`compose`** | **串联，需要适配器 + `post → pre` 的证明** |
| **`compose_sound`** | 两个 sound 的 primitive 串起来仍 sound |
| `compose_run_assoc` | `run` 的结合律（`Option` 单子的 `bind_assoc`） |
| `identity` | 恒等 primitive（`exact` / `univ`） |
| `identity_compose_run` | **左单位**：`compose identity f` 的 `run` 与 `f` 相同 |
| `compose_strength` / `compose_coverage` | 强度取最小 / 覆盖取交集 |

## 2. 为什么只证 `run` 层的结合律

`Primitive` 带 `sound` 字段——**一个证明项**。两个 `Primitive` 的 `sound` 不会定义相等，
所以 `compose (compose f g) h = compose f (compose g h)` **不可证**（需要证明无关性）。
但 **`run` 的结合律可证**，而 `run` 才是使用者调用的东西。
**把不可证的东西写成「定理」是名义完成**，所以本节只证 `run` 层并说明理由。

## 3. 边界

- **只做 `compose` 与 `identity`**。`parallel`/`choice`/`optional`/`iterate` 的 `Input`/`Output`
  是积/和类型，`sound` 写法各异，**P1 再做**。
- **`identity` 的覆盖是 `Finset.univ`**：含义是「不限制」，不是「覆盖了全部字符串」。
- **不注册任何 primitive**，不写 `Registry`。 -/
import Mathlib
import Lattice.Compose.Primitive

namespace Lattice.Compose

/-! ## 一、串联（带适配器） -/

/-- **串联**：先跑 `f`，用 `adapt` 把结果送进 `g`，再跑 `g`。

**`adapt` 是必需的**：`f.Output` 与 `g.Input` 是不同的类型（见 §0）。
**`h` 是兼容性证明**——`f` 的后置必须蕴含 `g` 在**适配后**的前置。
**这就是「库不打包能力」在类型上的实现**：想串两步，中间接口由调用方给出并证明。 -/
def compose (f g : Primitive) (adapt : f.Output → g.Input)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) : Primitive where
  Input := f.Input
  Output := g.Output
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

/-- **串联保持正确性。** -/
theorem compose_sound (f g : Primitive) (adapt : f.Output → g.Input)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) (x : f.Input) (hx : f.pre x) :
    ∃ z, (compose f g adapt h).run x = some z ∧ (compose f g adapt h).post x z :=
  (compose f g adapt h).sound x hx

/-- **串联的强度取最小**：组合不会让承诺变强。 -/
theorem compose_strength (f g : Primitive) (adapt : f.Output → g.Input)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) :
    (compose f g adapt h).strength = f.strength.min g.strength := rfl

/-- **串联的覆盖取交集**：组合不会让覆盖变大。 -/
theorem compose_coverage (f g : Primitive) (adapt : f.Output → g.Input)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) :
    (compose f g adapt h).coverage = f.coverage.inter g.coverage := rfl

/-- **`run` 的展开式**：串联的执行就是两次 `bind`。

这条是后面所有 `run` 层定律的地基——它把「组合的语义」变成一条可改写的事实。 -/
theorem compose_run (f g : Primitive) (a : f.Output → g.Input)
    (h : ∀ x y, f.post x y → g.pre (a y)) (x : f.Input) :
    (compose f g a h).run x = (f.run x).bind (fun y => g.run (a y)) := rfl

/-- **`run` 的结合律**：`(f 然后 g) 然后 k` 的执行等于 `f 然后 (g 然后 k)`。

`Option.bind_assoc` 的直接推论。**只在 `run` 层成立**——结构层需要证明无关性（`sound` 是证明项），
见 §2。

**注意它没有把右边写成 `compose f (compose g k …)`**：那需要为右边的复合再造一个适配器与兼容性证明，
而那些证明**不进入 `run`**。写成显式的三层 `bind` 才是这条定律的**内容**，
写成两个 `compose` 的相等只是把它藏进适配器里。 -/
theorem compose_run_assoc (f g k : Primitive)
    (a₁ : f.Output → g.Input) (a₂ : g.Output → k.Input)
    (h₁ : ∀ x y, f.post x y → g.pre (a₁ y))
    (h₂ : ∀ y z, g.post y z → k.pre (a₂ z)) (x : f.Input) :
    (compose (compose f g a₁ h₁) k a₂
        (by
          intro x z hz
          obtain ⟨y, _, hgz⟩ := hz
          exact h₂ (a₁ y) z hgz)).run x
      = (f.run x).bind (fun y => (g.run (a₁ y)).bind (fun z => k.run (a₂ z))) := by
  -- Unfold `run` twice and then use `Option.bind_assoc`.
  -- NOT via `simp only [compose_run]`: `simp` renames the bound variables, and the goal then shows
  -- `fun y => ... fun y => ...` while the right-hand side uses `y` and `z`. The rewriting is the same;
  -- the *display* differs, and that is what made the first attempt look unsolvable.
  show ((f.run x).bind (fun y => g.run (a₁ y))).bind (fun z => k.run (a₂ z))
      = (f.run x).bind (fun y => (g.run (a₁ y)).bind (fun z => k.run (a₂ z)))
  exact Option.bind_assoc (f.run x) (fun y => g.run (a₁ y)) (fun z => k.run (a₂ z))

/-! ## 二、恒等 -/

/-- **恒等 primitive**：`exact` 强度，不限制覆盖（`none`）。 -/
def identity (α : Type) : Primitive where
  Input := α
  Output := α
  pre := fun _ => True
  post := fun x y => y = x
  run := fun x => some x
  sound := fun x _ => ⟨x, rfl, rfl⟩
  strength := .exact
  coverage := none
  frame := fun _ _ => True

/-- **左单位**：`compose identity f` 的 `run` 就是 `f` 的 `run`。

**`α` 必须是 `f.Input`**：`compose` 的适配器类型是 `(identity α).Output → f.Input`，即 `α → f.Input`。
只有取 `α := f.Input` 时 `id` 才类型正确。**第一版把 `α` 留成任意类型，`id` 通不过类型检查**——
「恒等接在前面」这件事本身就要求两边的载体相同。

**兼容性证明由调用方给出**（`h`）：`identity` 的后置是 `y = x`，把它变成 `f.pre (id y)`
需要知道 `f.pre` 在 `x` 上成立。**这是 §2.2「组合是用户的事」在最小处的一次体现**：
连「恒等接在前面」这一步，接口也要有人担保。 -/
theorem identity_compose_run (f : Primitive)
    (h : ∀ x y, (identity f.Input).post x y → f.pre (id y)) (x : f.Input) :
    (compose (identity f.Input) f id h).run x = f.run x := by
  -- Option.bind (some x) g is g x by definition, and id x is x by definition.
  rfl

end Lattice.Compose
