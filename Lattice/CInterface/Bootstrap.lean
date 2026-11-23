import Mathlib

/-!
# **自举的装载规格：重复装载**观察保持**，而不是内部状态全等**

## 规划 §6.1 要求什么

规划把自举拆成三个独立交付物，并指出一处**规格写错**的证据要保留：

| 交付物 | 本文件 |
|:--|:--|
| **抽象装载正确** | `insertManifest` / `loadAll` 的定义与性质 |
| **重复装载观察保持** | `loadAll_reify_idempotent`：**观察**不变（不是内部状态全等） |
| **实际执行对应** | **不在本文件**：它需要 CIC 内核的 C 实现（`PLUGIN-SYSTEM.md §9` Q4/Q7 指明装载器的消费者在那边） |

**⇒ 文档记录的原始规格是错的：**`loadAll (loadAll ms) = loadAll ms`——若
`loadAll : List Manifest → LoaderState`，则 `loadAll (loadAll ms)` 的第二个参数类型不符。
修法是补 `reify : LoaderState → List Manifest` 并把第二轮输入改成 `reify (loadAll s)`。
**本文件按该修法实现，并把原来的类型错误作为**证据**留在文档，而不是悄悄改写。**

## 三个建模判断（都不是形式选择）

**判断一：必须有 `LoaderState`。** 「重复装载」只有在**状态**里才能定义：装载一个已在状态中的清单，
行为必须与装载新的不同。若 `loadAll` 只是 `List → List`，则「重复」无从表述——这正是原规格写错的根源。

**判断二：重复判定用**名字**，不用结构相等。** 同名不同版在真实装载器里会被视为同一个条目，
故 `insertManifest` 用 `x.name = m.name` 判定。**⇒ 这使「已在表中」与「同名已在表中」是两个不同的条件，
本文件把两者分开陈述，而不是用一个含糊的「重复」。**

**判断三：观察只含 `loaded`，不含 `rounds`。** 规划要求「定义『同一观察』包含哪些状态；
不是全部内部状态相等」。把 `rounds` 放进结构、排除在观察之外，是为了让这个差别**可见**。
-/

namespace Lattice.CInterface.Bootstrap

/-- **装载清单**：一个名字加一个版本号。

**⇒ `version` 是**载荷**，不参与重复判定（见判断二）。** -/
structure LoaderManifest where
  /-- The identity of the manifest. -/
  name : String
  /-- The payload version; deliberately NOT used for the duplicate test. -/
  version : ℕ
  deriving DecidableEq, Repr

/-- **装载器状态**：已装载清单表 + 轮次计数。 -/
structure LoaderState where
  /-- Manifests already loaded. -/
  loaded : List LoaderManifest
  /-- Internal counter; NOT part of the observation. -/
  rounds : ℕ

/-- **观察**：只取已装载清单表。**⇒ 这是「同一观察」的定义。** -/
def observeLoaded (s : LoaderState) : List LoaderManifest := s.loaded

/-- **装载一个清单**：若**同名**清单已在表中则**不动**，否则前插并递增轮次。 -/
def insertManifest (m : LoaderManifest) (s : LoaderState) : LoaderState :=
  if s.loaded.any (fun x => decide (x.name = m.name)) then s
  else { loaded := m :: s.loaded, rounds := s.rounds + 1 }

/-- **装载一批**：逐个前插（`foldl`），故后装载的清单在最前。 -/
def loadAll (s : LoaderState) (ms : List LoaderManifest) : LoaderState :=
  ms.foldl (fun acc m => insertManifest m acc) s

/-- **反向索引**：把状态还原成清单表。

**⇒ 这就是原规格缺失的那个函数；有了它，`loadAll` 才能接受一个**状态**而不是一个清单表。** -/
def reifyLoader (s : LoaderState) : List LoaderManifest := s.loaded

/-! ## 一、装载的局部性质 -/

/-- **已在表中的清单不会被重复装载**（状态**完全**不变，含 `rounds`）。 -/
theorem insertManifest_noop_of_mem {m : LoaderManifest} {s : LoaderState}
    (hm : m ∈ s.loaded) : insertManifest m s = s := by
  have hex : s.loaded.any (fun x => decide (x.name = m.name)) = true :=
    List.any_eq_true.mpr ⟨m, hm, by simp⟩
  unfold insertManifest
  rw [hex]
  simp

/-- **同名清单不在表中 ⟹ 装载会前插。**

**⇒ 前提比「`m` 不在表中」更强：判定看名字，故必须对**表中每个元素**都断言名字不同。
**把这一点写清楚，正是为了不把两种「重复」混为一谈。** -/
theorem insertManifest_new_changes {m : LoaderManifest} {s : LoaderState}
    (h : ∀ x ∈ s.loaded, x.name ≠ m.name) :
    observeLoaded (insertManifest m s) = m :: s.loaded := by
  have hany : s.loaded.any (fun x => decide (x.name = m.name)) = false := by
    apply List.any_eq_false.mpr
    intro x hx
    simpa using h x hx
  unfold insertManifest observeLoaded
  rw [hany]
  simp

/-! ## 二、重复装载**观察保持** -/

/-- **⭐⭐ 若一批清单都已在状态中，则装载它们不改变观察。**

**⇒ 对 `ms` 归纳，逐个用 `insertManifest_noop_of_mem`。这是「重复装载保持观察」的一般形式，
不预设这批清单来自 `reifyLoader`。** -/
theorem loadAll_preserves_observe_of_forall_mem (s : LoaderState) (ms : List LoaderManifest)
    (h : ∀ m ∈ ms, m ∈ s.loaded) : observeLoaded (loadAll s ms) = observeLoaded s := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
      have hm : m ∈ s.loaded := h m (List.mem_cons_self ..)
      have h' : ∀ m' ∈ rest, m' ∈ s.loaded :=
        fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
      have hstep : insertManifest m s = s := insertManifest_noop_of_mem hm
      show observeLoaded (loadAll (insertManifest m s) rest) = observeLoaded s
      rw [hstep]
      exact ih h'

/-- **⭐⭐⭐ 重复装载**观察保持**（自举规格，按文档修法）。**

**⇒ `observeLoaded (loadAll s (reifyLoader s)) = observeLoaded s`：
把状态自己的清单表再装一遍，**观察不变**。**

**⇒ 这是原规格的正确形式。结论只能是**观察**相等，不是**状态**相等；
`rounds` 的差别见 `load_changes_observe_of_new` 之后的说明。** -/
theorem loadAll_reify_idempotent (s : LoaderState) :
    observeLoaded (loadAll s (reifyLoader s)) = observeLoaded s :=
  loadAll_preserves_observe_of_forall_mem s (reifyLoader s) (fun _ hm => hm)

/-- **⭐ 保持不是空性质：装载一个**新**清单确实改变观察。**

**⇒ 与 `loadAll_reify_idempotent` 合起来，说明「保持」只在重复时成立，
对新增装载则**不**成立——两者共同界定了这个规格。** -/
theorem load_changes_observe_of_new (m : LoaderManifest) :
    observeLoaded (loadAll { loaded := [], rounds := 0 } [m])
      ≠ observeLoaded ({ loaded := [], rounds := 0 } : LoaderState) := by
  have hnew : ∀ x ∈ ([] : List LoaderManifest), x.name ≠ m.name := by
    intro x hx
    exact absurd hx (List.not_mem_nil x)
  have h1 : observeLoaded (loadAll { loaded := [], rounds := 0 } [m]) = [m] := by
    show observeLoaded (insertManifest m { loaded := [], rounds := 0 }) = [m]
    rw [insertManifest_new_changes (s := { loaded := [], rounds := 0 }) hnew]
  rw [h1]
  -- **`observeLoaded` 需显式展开，否则 `simp` 看不到 `[]`。**
  simp [observeLoaded]

end Lattice.CInterface.Bootstrap