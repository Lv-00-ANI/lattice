/-
# `Compose/More` —— `parallel` / `choice` / `optional`（**参数版**）

## 0. `choice` 现在写得出来了 —— 这是第 232 轮裁决的直接兑现

第 228 轮记下的阻塞是：`choice` 的 `Output` 只能取一支，另一支的输出要经 `hio` 搬运，
而 `hio.symm ▸ (hio ▸ z)` **不是** `rfl` 相等（`hio` 是变量，两次 `Eq.rec` 卡住），
于是 `choice` **写不出来**。

**参数版下根本没有 `hio`**：两个 primitive 都是 `Primitive I O`，同一个 `I` 同一个 `O`。
`run` 是 `if sel x then f.run x else g.run x`，**两支的输出类型相同，无需任何搬运。**

## 1. `choice` 的 `pre` 必须按派发分情况

若把 `pre` 写成 `f.pre`，则走 `g` 那一支时 `g.sound` 拿不到 `g.pre`。**所以 `pre` 与 `post` 同形**：

```lean
pre  := fun x   => (sel x = true → f.pre x)  ∧ (sel x = false → g.pre x)
post := fun x z => (sel x = true → f.post x z) ∧ (sel x = false → g.post x z)
```

**从 `pre` 的对应分支就能拿到对应一侧的前置**——这正是第 228 轮缺的那块
（那时 `pre` 只有一个，不可能同时等于两边的）。

## 2. 交付

| 声明 | 内容 |
|:--|:--|
| **`parallel`** | `Primitive (I₁ × I₂) (O₁ × O₂)` |
| `parallel_sound` / `parallel_strength` / `parallel_coverage` | 定律 |
| **`choice`** | **两个 `Primitive I O` + `sel : I → Bool`，无 cast** |
| `choice_sound` / `choice_strength` / `choice_coverage` | 定律（强度 `min`、覆盖**并**） |
| **`optional`** | `Primitive I I` + `dec : I → Bool`：条件跳过 |
| `optional_sound` / `optional_strength` | 定律 |

## 3. 强度与覆盖

- `parallel`：强度 **min**（两者都成功才叫成功），覆盖 **交**。
- `choice`：强度 **min**，覆盖 **并**——**这是唯一一处取并**，理由：`choice` 把两支的覆盖面加起来，
  而 `compose`/`parallel` 要求**都**适用。
- `optional`：强度 **不变**（它不新增承诺），覆盖 **不变**。

## 4. 边界

- **不做 `iterate`**：需要终止测度与循环不变式，§6 只给一行。
  **没有测度的「循环」在 Lean 里不终止**，写成一行实现必然是错的。
- **`choice` 的派发由调用方给 `Bool`**，不是「在 f 与 g 之间自由选择」——
  后者要选择策略，那是 `Compose` 之上的东西。
- **`optional` 要求 `Primitive I I`**（自映射）：跳过时要返回一个 `O`，而手上只有 `I`。
  这是参数化把「`optional` 只对自映射有意义」**写进类型**的地方。 -/
import Mathlib
import Lattice.Compose.Primitive

namespace Lattice.Compose

/-! ## 一、并行 -/

/-- **并行**：两个 primitive 各跑一次，输入与输出都成对。

强度取 `min`（**两个都成功才叫成功**），覆盖取交（两个都适用的情形才适用）。 -/
def parallel {I₁ O₁ I₂ O₂ : Type} (f : Primitive I₁ O₁) (g : Primitive I₂ O₂) :
    Primitive (I₁ × I₂) (O₁ × O₂) where
  pre := fun p => f.pre p.1 ∧ g.pre p.2
  post := fun p q => f.post p.1 q.1 ∧ g.post p.2 q.2
  run := fun p => (f.run p.1).bind (fun y => (g.run p.2).map (fun z => (y, z)))
  sound := by
    intro p hp
    obtain ⟨y, hy, hpy⟩ := f.sound p.1 hp.1
    obtain ⟨z, hz, hpz⟩ := g.sound p.2 hp.2
    exact ⟨(y, z), by simp only [Option.bind, hy, hz, Option.map], hpy, hpz⟩
  strength := f.strength.min g.strength
  coverage := f.coverage.inter g.coverage

/-- **并行保持正确性。** -/
theorem parallel_sound {I₁ O₁ I₂ O₂ : Type} (f : Primitive I₁ O₁) (g : Primitive I₂ O₂)
    (p : I₁ × I₂) (hp : f.pre p.1 ∧ g.pre p.2) :
    ∃ q, (parallel f g).run p = some q ∧ (parallel f g).post p q :=
  (parallel f g).sound p hp

/-- **并行的强度取最小。** -/
theorem parallel_strength {I₁ O₁ I₂ O₂ : Type} (f : Primitive I₁ O₁) (g : Primitive I₂ O₂) :
    (parallel f g).strength = f.strength.min g.strength := rfl

/-- **并行的覆盖取交。** -/
theorem parallel_coverage {I₁ O₁ I₂ O₂ : Type} (f : Primitive I₁ O₁) (g : Primitive I₂ O₂) :
    (parallel f g).coverage = f.coverage.inter g.coverage := rfl

/-! ## 二、二选一 -/

/-- **二选一**：`sel x = true` 走 `f`，否则走 `g`。

**两支都是 `Primitive I O`**——同一个输入、同一个输出，所以**没有任何 cast**（见 §0）。

**`pre` 按派发分情况**（见 §1）：否则走 `g` 那一支时 `g.sound` 拿不到 `g.pre`。 -/
def choice {I O : Type} (f g : Primitive I O) (sel : I → Bool) : Primitive I O where
  pre := fun x => (sel x = true → f.pre x) ∧ (sel x = false → g.pre x)
  post := fun x z => (sel x = true → f.post x z) ∧ (sel x = false → g.post x z)
  run := fun x => if sel x then f.run x else g.run x
  sound := by
    intro x hx
    by_cases hs : sel x = true
    · have hpre : f.pre x := hx.1 hs
      obtain ⟨y, hy, hpy⟩ := f.sound x hpre
      refine ⟨y, ?_, ?_, ?_⟩
      · simp only [hs, if_pos]; exact hy
      · intro _; exact hpy
      · intro hf; rw [hf] at hs; exact absurd hs (by simp)
    · have hfalse : sel x = false := by
        cases hv : sel x
        · rfl
        · exact absurd hv hs
      have hpre : g.pre x := hx.2 hfalse
      obtain ⟨z, hz, hpz⟩ := g.sound x hpre
      refine ⟨z, ?_, ?_, ?_⟩
      · simp only [hfalse, Bool.false_eq_true, if_false]; exact hz
      · intro ht; rw [ht] at hfalse; exact absurd hfalse (by simp)
      · intro _; exact hpz
  strength := f.strength.min g.strength
  coverage := f.coverage.union g.coverage

/-- **二选一保持正确性。** -/
theorem choice_sound {I O : Type} (f g : Primitive I O) (sel : I → Bool) (x : I)
    (hx : (choice f g sel).pre x) :
    ∃ z, (choice f g sel).run x = some z ∧ (choice f g sel).post x z :=
  (choice f g sel).sound x hx

/-- **二选一的强度取最小。** -/
theorem choice_strength {I O : Type} (f g : Primitive I O) (sel : I → Bool) :
    (choice f g sel).strength = f.strength.min g.strength := rfl

/-- **二选一的覆盖取并**——**组合子里唯一取并的地方**。

理由：`choice` 把两支的覆盖面**加起来**；而 `compose` 与 `parallel` 要求两者**都**适用，所以取交。
把 `choice` 也写成取交会**低估**它的覆盖，把 `compose` 写成取并会**高估**——
后者正是 §2.7 禁止的「把 `approx` 静默升级成 `exact`」的覆盖版本。 -/
theorem choice_coverage {I O : Type} (f g : Primitive I O) (sel : I → Bool) :
    (choice f g sel).coverage = f.coverage.union g.coverage := rfl

/-! ## 三、条件跳过 -/

/-- **条件跳过**：`dec x = true` 时跑 `p`，否则原样返回。

**`p` 必须是 `Primitive I I`**（自映射）——跳过时要返回一个 `O`，而手上只有 `I`。
这是参数化把「`optional` 只对自映射有意义」**写进类型**的地方：字段版只能靠等式约束。 -/
def optional {I : Type} (p : Primitive I I) (dec : I → Bool) : Primitive I I where
  pre := fun x => (dec x = true → p.pre x) ∧ (dec x = false → True)
  post := fun x z => (dec x = true → p.post x z) ∧ (dec x = false → z = x)
  run := fun x => if dec x then p.run x else some x
  sound := by
    intro x hx
    by_cases hd : dec x = true
    · have hpre : p.pre x := hx.1 hd
      obtain ⟨y, hy, hpy⟩ := p.sound x hpre
      refine ⟨y, ?_, ?_, ?_⟩
      · simp only [hd, if_pos]; exact hy
      · intro _; exact hpy
      · intro hf; rw [hf] at hd; exact absurd hd (by simp)
    · have hfalse : dec x = false := by
        cases hv : dec x
        · rfl
        · exact absurd hv hd
      refine ⟨x, ?_, ?_, ?_⟩
      · simp only [hfalse, Bool.false_eq_true, if_false]
      · intro ht; rw [ht] at hfalse; exact absurd hfalse (by simp)
      · intro _; rfl
  strength := p.strength
  coverage := p.coverage

/-- **条件跳过保持正确性。** -/
theorem optional_sound {I : Type} (p : Primitive I I) (dec : I → Bool) (x : I)
    (hx : (optional p dec).pre x) :
    ∃ z, (optional p dec).run x = some z ∧ (optional p dec).post x z :=
  (optional p dec).sound x hx

/-- **条件跳过的强度不变**：它不新增承诺。 -/
theorem optional_strength {I : Type} (p : Primitive I I) (dec : I → Bool) :
    (optional p dec).strength = p.strength := rfl

end Lattice.Compose
