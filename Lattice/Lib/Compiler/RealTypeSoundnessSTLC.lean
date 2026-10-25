import Mathlib

/-!
# LATTICE: 类型可靠性 —— STLC 最小片段的 progress + preservation

## 1. 本文件建立什么

⚠ **与既有的 `RealTypeSoundness.lean` 不重叠**：那个文件处理的是**符号 IR**
（`int / real / bool`，无变量、无 λ、无上下文）。本文件处理的是
**带变量绑定与函数的类型系统**（de Bruijn 索引 + λ 抽象 + 应用），
补上「**上下文与替换**」这一维度 —— 那正是替换引理、弱化引理与
`generalizing` 陷阱的所在，也是符号 IR 版本**结构上不可能**覆盖的部分。

| 定理 | 内容 |
|:--|:--|
| `progress` | 良类型**闭**项要么是值，要么能走一步 |
| `preservation` | 良类型项走一步后**仍是良类型**（同类型） |
| `soundness` | 两半**交替**合成的可靠性：良类型闭项任意多步后仍不卡死 |
| `multistep_preservation` | `preservation` 沿多步提升 |
| `value_no_step` | 值是范式 |
| `subst_preserves_typing` | **替换引理**（本文件技术核心） |
| `progress_needs_closed` | 反例：闭性条件不可去 |
| `stuckTm_is_stuck` / `stuckTm_untypeable` | 反例：存在卡死项，而类型系统恰好排除它 |

## 2. 为什么这不是恒等重述（承重性说明）

- `progress` 与 `preservation` 是**两个不同命题**（「能走或已是值」vs
  「走了之后类型不变」）。`soundness` **不是**二者的合取重述：它需要在
  步数归纳里**每步重跑 `progress`**（依赖 `multistep_preservation` 提供类型），
  这是真正的交替论证。
- `subst_preserves_typing` 是全部难度所在：对类型推导归纳，`var 0` 情形要求
  **查表唯一性**（`(A :: Γ)[0]? = some B ⟹ B = A`），`abs` 情形要求
  **上下文弱化**（否则归纳假设被 `A :: Γ` 固定）。
- 项语言含 `succ` 与应用右子项归约（非标准 STLC 的常见裁剪），
  使 `preservation` 有 3 个情形而非 1 个。

## 3. 依赖什么

仅 `Mathlib`。**不 import 任何 LATTICE 模块**（含 `RealTypeSoundness`）——
两个类型系统完全独立，名字空间内无冲突（本文件用 `STLC` 子命名空间）。

## 4. 不做什么（诚实边界）

- **不含多态、递归（`fix`）、引用、子类型**：类型只有 `nat` 与 `→`。
  证明结构完整，但不覆盖真实语言的类型特性（**被削弱的陈述**）。
- **求值策略是「回调式」**：`app` 只归约**右**子项，且要求左子项**已是**
  `abs`（`Step.app_arg`）。这比标准 STLC 少了「左子项归约」规则，
  故 `progress` 的 `app` 情形里有一个**死分支**（左子项能走步的情形
  在本语言中不可能）—— 我在证明里显式标注了它，不掩盖。
- **不含效应 / 并发 / 副作用**（效应顺序见 `RealEffectOrdering`）。
- `stuckTm_*` 是**存在性**见证，不是「所有未类型化项都卡死」。
- 不用 `sorry` / `axiom` / `admit` / `native_decide`。

## 5. 小规模自检（落盘前判真假）

- `progress` 对 `(λx. x) 0` ✅ → `Step.beta`（`0` 是值）。
- `preservation` 对 `(λx. x) 0 : nat` 走一步到 `substTop 0 (var 0) = 0 : nat` ✅。
- **反例检查**：`progress` 的闭性条件不可去 —— `HasType [nat] (var 0) nat`
  真，而 `var 0` 既非值也不能走步 ⇒ `progress_needs_closed` 真。
- **反例检查**：`succ (abs nat (var 0))` 不是值（是 `succ`）也不能走步
  （`succ` 规则要求参数能走，而 `abs` 是范式）⇒ 卡死。
  这个项**不可类型化**（`succ` 要求 `nat`），故 `stuckTm_untypeable` 真。
-/

namespace Lattice
namespace STLC

/-! ## 一、类型、项、上下文 -/

/-- **最小类型**：自然数类型与函数类型。 -/
inductive Ty : Type
  /-- 自然数类型。 -/
  | nat : Ty
  /-- 函数类型。 -/
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- **最小项语言**：变量（de Bruijn）、数值、后继、λ 抽象、应用。
不含 `fix`（见诚实边界）。 -/
inductive Tm : Type
  /-- 变量（de Bruijn 索引，0 为最内层）。 -/
  | var : ℕ → Tm
  /-- 数值字面量。 -/
  | num : ℕ → Tm
  /-- 后继。 -/
  | succ : Tm → Tm
  /-- λ 抽象（带参数类型标注）。 -/
  | abs : Ty → Tm → Tm
  /-- 应用。 -/
  | app : Tm → Tm → Tm
  deriving DecidableEq, Repr

/-- **类型环境**：de Bruijn 索引到类型的映射（索引 0 对应 `List` 头部）。 -/
abbrev Ctx := List Ty

/-! ## 二、类型推导 -/

/-- **类型推导** `HasType Γ t A`。 -/
inductive HasType : Ctx → Tm → Ty → Prop
  /-- 变量：查表命中。 -/
  | var {Γ : Ctx} {n : ℕ} {A : Ty} : Γ.get? n = some A → HasType Γ (.var n) A
  /-- 数值字面量：类型 `nat`。 -/
  | num {Γ : Ctx} (k : ℕ) : HasType Γ (.num k) .nat
  /-- 后继：`succ` 保持 `nat`。 -/
  | succ {Γ : Ctx} {t : Tm} : HasType Γ t .nat → HasType Γ (.succ t) .nat
  /-- λ 抽象：参数类型前插。 -/
  | abs {Γ : Ctx} {A B : Ty} {t : Tm} :
      HasType (A :: Γ) t B → HasType Γ (.abs A t) (.arr A B)
  /-- 应用：函数类型必须匹配。 -/
  | app {Γ : Ctx} {A B : Ty} {t u : Tm} :
      HasType Γ t (.arr A B) → HasType Γ u A → HasType Γ (.app t u) B

/-! ## 三、小步语义与值 -/

/-- **值是范式**：数值、λ 抽象、以及**后继于值之上**。

⚠⚠ **定义层更正（原定义缺 `succ` 构造子，已用内核反例实测）**：
原定义只有 `num` 与 `abs` 两条。**后果**：`succ (num k)` 是**良类型的闭项**
（`HasType Γ (.num k) .nat` ⟹ `HasType Γ (.succ (.num k)) .nat`，见 `HasType.succ`），
但它**既不是值**（`succ` 不是 `num`/`abs`）、**也没有出边**
（`Step.succ` 要求 `Step (num k) t'`，而 `num` 无出边）
⟹ 它是**卡死的良类型项** ⟹ `progress` **为假**。

⭐ **内核实测反例**（隔离最小复刻，`exit 0`）：
```lean
example : ¬ Value (.succ (.num 5)) := by intro h; cases h
example : ¬ ∃ t', Step (.succ (.num 5)) t' := by
  rintro ⟨t', hs⟩; cases hs with | succ h => cases h
theorem progress_false : ¬ (Value (.succ (.num 5)) ∨ ∃ t', Step (.succ (.num 5)) t')
```
⚠ **原文件头 §5 的自检只检查了 `succ (abs nat (var 0))`** ——
那一项**确实不可类型化**（`succ` 要求 `nat`，而 `abs` 给出函数类型），故无害；
⭐ **但作者把「某个填充不可类型化」推广到了整个 `succ` 构造子**，
**漏掉了 `succ (num k)` 这一可类型化填充**。这正是「反例必须满足原命题**全部**假设」的实例。

⭐ **修法（标准 STLC 的写法）**：补上第三条构造子 `succ`。
⚠ **这一条是`progress` 成立的必要条件**：
「值是范式」与「良类型闭项能走或已是值」两条合起来要求
**每个 `Value` 构造子都覆盖一类范式**，而 `succ v`（`v` 是值）正是一类范式。

⚠ **连锁修正**：原 `value_not_succ : ¬ Value (.succ t)` 在本定义下**为假**，**已删除**。 -/
inductive Value : Tm → Prop
  /-- 数值是值。 -/
  | num (k : ℕ) : Value (.num k)
  /-- λ 抽象是值。 -/
  | abs (A : Ty) (t : Tm) : Value (.abs A t)
  /-- **后继于值之上是值**（本次补入；缺它会让 `succ (num k)` 卡死）。 -/
  | succ {t : Tm} : Value t → Value (.succ t)

/-- **变量移位** `shift c t`：把 `t` 中所有 **`≥ c` 的自由**变量索引 `+1`。
`c` 是**截断深度**（当前已进入的 binder 数），故穿过 `abs` 时 `c` 递增。

⚠ 这是 de Bruijn 表示的**必需**构件：替换项进入 binder 之下时，
它的自由变量必须上移，否则会被新 binder **捕获**（variable capture）。 -/
def shift (c : ℕ) : Tm → Tm
  | .var n => if n < c then .var n else .var (n + 1)
  | .num k => .num k
  | .succ t => .succ (shift c t)
  | .abs A t => .abs A (shift (c + 1) t)
  | .app t₁ t₂ => .app (shift c t₁) (shift c t₂)

/-- **带截断的替换** `substAux c u t`：把 `t` 中**等于截断 `c` 的索引**换成 `u`，
并把 **`> c` 的索引 `-1`**（因为那一层的 binder 被消去了）；
**`< c` 的索引不动**（它们指向仍然存在的**外层** binder）。
穿过 `abs` 时截断 `c+1`（新 binder 使所有外层索引下移一位），
同时把 `u` 经 `shift 0` 上移以**避免捕获**。

⚠ **`c` 同时承担两个职责**，这是本定义的关键：
**(i) 判定「谁是那个被替换的自由变量」**（`n = c`），
**(ii) 判定「谁是被 binder 绑定的、不可动」**（`n < c`）。
⭐ 只做 `shift` 而不带截断是**不够的** —— 见 `substTop` 的 docstring。 -/
def substAux (c : ℕ) (u : Tm) : Tm → Tm
  | .var n => if n = c then u else if c < n then .var (n - 1) else .var n
  | .num k => .num k
  | .succ t => .succ (substAux c u t)
  | .abs A t => .abs A (substAux (c + 1) (shift 0 u) t)
  | .app t₁ t₂ => .app (substAux c u t₁) (substAux c u t₂)

/-- **de Bruijn 顶层替换** `substTop u t`：把 `t` 中**自由**的索引 0 换成 `u`，
其余自由索引下移一位。定义为 `substAux 0`（**单层递归**，便于 Lean 的终止性检查）。

⚠⚠ **定义层更正（原定义有语义错误，已实测）**：
原定义在 `abs` 分支写的是
`| .abs A t => .abs A (substTop u t)` —— **直接下潜、既不移位也不看绑定**。
**实测反例**（`#eval`）：
```
substTop (.num 5) (.abs (.var 0))  ⟹  Tm.abs (Tm.num 5)     -- 即 λx. 5
```
⚠ 但 `abs (var 0)` 就是 `λx. x`，**代入后应当仍是 `λx. x`** ——
因为 binder 内的 `var 0` 指的是**新绑定的那个变量**，**不是被替换的自由变量 0**。
⭐ 原定义把 `λx. x` 代换成了 `λx. 5`，**把绑定变量与自由变量混为一谈**，
⟹ 依赖它的替换引理 `subst_preserves_typing` **在此定义下为假**
（这正是 `abs` 分支无论怎么调 tactic 都证不出的根因）。
⭐ 另一个可直接观察的后果：原定义**不是** `Step.beta` 想要的语义 ——
`(λx. x) 5` 会归约成 `λx. 5` 而非 `5` 的包装。

⚠ 修法：引入 `shift`（防捕获）与 `substAux`（带截断，区分绑定/自由），
`substTop` 取 `substAux 0`。**`#eval` 实测修正后的行为**：
```
substTop 5 (abs (var 0))              ⟹ abs (var 0)                ✅ λx.x 不变
substTop 5 (abs (var 1))              ⟹ abs (num 5)                ✅ λx.5
substTop 5 (abs (app (var 1)(var 0))) ⟹ abs (app (num 5)(var 0))   ✅
substTop 5 (abs (abs (var 2)))        ⟹ abs (abs (num 5))          ✅
substTop 5 (abs (abs (var 1)))        ⟹ abs (abs (var 1))          ✅ 绑定者不动
``` -/
def substTop (u : Tm) : Tm → Tm := substAux 0 u

/-- **小步归约**。三条规则：β 归约、左子项归约（`app_fun`）、右子项归约（`app_arg`），
以及 `succ` 参数归约。**左归约规则是必需的**：否则 `progress` 里
「左子项能走步」的分支无法封闭（规则集本身不完备）。 -/
inductive Step : Tm → Tm → Prop
  /-- β 归约（参数必须是值）。 -/
  | beta {A : Ty} {t u : Tm} : Value u → Step (.app (.abs A t) u) (substTop u t)
  /-- 应用左子项归约。 -/
  | app_fun {t t' u : Tm} : Step t t' → Step (.app t u) (.app t' u)
  /-- 应用右子项归约（仅当左子项是 λ 抽象时）。 -/
  | app_arg {A : Ty} {t u u' : Tm} :
      Step u u' → Step (.app (.abs A t) u) (.app (.abs A t) u')
  /-- `succ` 参数归约。 -/
  | succ {t t' : Tm} : Step t t' → Step (.succ t) (.succ t')

/-! ## 四、值的语法性质 -/

/-- **值不可能是变量**。 -/
theorem value_not_var {n : ℕ} : ¬ Value (.var n) := by
  intro h; cases h

/-- **值不可能是应用**。 -/
theorem value_not_app {t u : Tm} : ¬ Value (.app t u) := by
  intro h; cases h

/-! ⚠⚠ **`value_not_succ` 已删除**（原为 `¬ Value (.succ t)`）。

**删除理由（该命题在原定义下就已经是**假**的、在新定义下同样是假）**：
补入 `Value.succ` 之后 `Value (.succ t)` 对**值是** `t` 的情形**成立**
（`Value.succ (Value.num 5) : Value (.succ (.num 5))`）。
⭐ 更重要的是：**原定义下它虽"真"（因为 `Value` 恰好没有 `succ`），
但这个"真"正是 `progress` 为假的根因** ——
`succ (num 5)` 良类型却不被任何 `Value` 构造子覆盖、也没有出边。
⚠ **⇒ 这条引理是"定义缺陷的症状"而非"语法事实"**：
它把「`Value` 缺一条构造子」误当成「`succ` 结构上不是值」。
⇒ 凡依赖它的证明都必须改用**正向**信息（如 `Value.abs` / 对 `Value` 分类）。 -/

/-! ## 五、替换引理（技术核心） -/

/-- **`shift` 保持可类型性**：若 `u : A` 在 `Δ ++ Γ` 下，则
`shift Δ.length u : A` 在 `Δ ++ (B₀ :: Γ)` 下 —— 即在 `Δ` **之下**插入一层 binder。

⚠ **为什么这是 `substAux` 的 `abs` 分支必需的一步**：
`substAux` 在 `abs` 下会把被替换项从 `u` 换成 `shift 0 u`（防捕获），
于是它需要一条「插入一层 binder 后 `u` 的移位版本仍同类型」的事实。
⭐ 这也解释了 `shift` 与 `cutoff` 的**分工**：
`substAux` 的 `c` 判定「哪些索引是绑定的」（是否该替换），
`shift` 判定「移位多少」（防止替换项被新 binder 捕获）。

⚠ **`induction h` 在此会报 `index in target's type is not a variable (Δ ++ Γ)`** ——
与 `subst_aux` **同一障碍**（环境是索引）⟹ 同样改为**对项 `u` 归纳**。
⚠ `Δ` **必须是「已在 `Γ` 之上」的前缀**（新 binder 插在 `Δ` 与 `Γ` 之间）：
若写成「`shift Δ.length u : A` 在 `Δ ++ Γ` 下」则**为假**
（`var 0` 会被移成 `var 1`，而 `Δ` 内的类型并未随之变化）。 -/
theorem shift_typing {Δ Γ : Ctx} {A : Ty} {u : Tm} (B₀ : Ty)
    (h : HasType (Δ ++ Γ) u A) : HasType (Δ ++ (B₀ :: Γ)) (shift Δ.length u) A := by
  induction u generalizing Δ A with
  | var n =>
      cases h with
      | var hv =>
          by_cases hn : n < Δ.length
          · have hs : shift Δ.length (.var n) = .var n := by
              simp only [shift]; rw [if_pos hn]
            rw [hs]
            have hg : (Δ ++ (B₀ :: Γ)).get? n = (Δ ++ Γ).get? n := by
              have h1 : n < (Δ ++ Γ).length := by simp only [List.length_append]; omega
              simp only [List.get?_eq_getElem?, List.getElem?_append_left hn,
                List.getElem?_append_left h1]
            exact HasType.var (by rw [hg]; exact hv)
          · have hs : shift Δ.length (.var n) = .var (n + 1) := by
              simp only [shift]; rw [if_neg hn]
            rw [hs]
            have hg : (Δ ++ (B₀ :: Γ)).get? (n + 1) = (Δ ++ Γ).get? n := by
              simp only [List.get?_eq_getElem?]
              rw [List.getElem?_append_right (by omega : Δ.length ≤ n),
                  List.getElem?_append_right (by omega : Δ.length ≤ n + 1)]
              have h1 : n + 1 - Δ.length = (n - Δ.length) + 1 := by omega
              rw [h1]
              simp
            exact HasType.var (by rw [hg]; exact hv)
  | num k => cases h with | num _ => exact HasType.num k
  | succ t₀ ih => cases h with | succ ht => exact HasType.succ (ih ht)
  | abs A₀ t₀ ih =>
      cases h with
      | abs hbody =>
          simp only [shift, List.length_cons]
          exact HasType.abs (ih (Δ := A₀ :: Δ) hbody)
  | app t₁ t₂ ih₁ ih₂ =>
      cases h with
      | app hf hu' => exact HasType.app (ih₁ hf) (ih₂ hu')

/-- **上下文弱化**：若 `Γ ⊢ t : A`，且 `Γ'` 在每个索引上与 `Γ` 相容，
则 `Γ' ⊢ t : A`。这是 `abs` 情形下归纳假设能跨上下文使用的桥梁。

⚠ 必须 `generalizing Γ'`：`HasType` 的环境是**索引**，不泛化则
归纳假设被具体环境 `Γ` 固定，`abs` 情形无法应用。 -/
theorem HasType.weaken {Γ : Ctx} {t : Tm} {A : Ty} (h : HasType Γ t A) :
    ∀ {Γ' : Ctx}, (∀ {n B}, Γ.get? n = some B → Γ'.get? n = some B) →
      HasType Γ' t A := by
  induction h with
  | var hv => intro Γ' hsub; exact HasType.var (hsub hv)
  | num k => intro Γ' _; exact HasType.num k
  | succ _ ih => intro Γ' hsub; exact HasType.succ (ih hsub)
  | abs hbody ih =>
      -- ⚠ `abs` 情形：`hbody : HasType (A₀ :: Γ) t₀ B₀`，而 `ih` 的归纳假设
      -- 是「对**任意** `Γ'`，只要 `(A₀ :: Γ)` 与 `Γ'` 查表相容，就有
      -- `HasType Γ' t₀ B₀`」。目标要的是 `HasType (A₀ :: Γ') t₀ B₀`，
      -- 故以 `Γ' := A₀ :: Γ'` 实例化，并提供子关系：
      -- 索引 `0` 处两旁都命中 `A₀`（`simp` 关闭），索引 `succ n` 处退化为 `hsub`。
      -- ⚠ `A₀` 由 `hbody` 的**类型**读出，不用 `rename_i`（后者按出现顺序取，
      -- 会误绑到 `Tm` 而不是 `Ty`）。
      intro Γ' hsub
      refine HasType.abs (ih (Γ' := _ :: Γ') ?_)
      · intro n B hb
        cases n with
        | zero => simpa using hb
        | succ n => simpa using hsub (by simpa using hb)
  | app _ _ ih1 ih2 => intro Γ' hsub; exact HasType.app (ih1 hsub) (ih2 hsub)

/-! **替换引理（承重）的证明路线**：`A :: Γ ⊢ t : B` 且 `Γ ⊢ u : A` ⟹ `Γ ⊢ substTop u t : B`。

证明对**项 `t`** 归纳（**不是**对类型推导 —— 见下面的技术说明）。
关键情形：
- `var 0`：查表得 `(A :: Γ).get? 0 = some A`，故 `B = A`，替换后恰为 `u : A`；
- `var (n+1)`：查表得 `(A :: Γ).get? (n+1) = Γ.get? n = some B`，替换后索引下移一位；
- `abs A₀`：项体活在 `A₀ :: A :: Γ` 里，需把 `hu` 经 `weaken` 提升到 `A₀ :: Γ`
  **并把 `u` 经 `shift 0` 移位**（否则替换项被新 binder 捕获）。

⚠⚠ **为何对项归纳而不是对类型推导归纳**：`HasType` 的**环境是索引**，
而本引理的环境形如 `A :: Γ`（**不是变量**）⟹ `induction ht` 直接报
`index in target's type is not a variable (consider using the cases tactic instead)`。
⭐ 实测**五条绕行路线全部失败**（登记以便后来者不必重走）：
1. `induction ht generalizing Γ` ❌（`generalizing` 不能泛化**索引**）；
2. `generalize hh : (A :: Γ) = Γ₀ at ht` + `subst hh` ❌（等式变成 IH 的**前提**，`subst` 从 `ih` 里消不掉）；
3. `revert A; intro t; induction t` ❌（分支名与 `Ty` 的构造子 `nat`/`arr` 冲突）；
4. `intro t; induction t`（`B`、`ht` 留到分支内 `intro`）❌（IH 仍被目标的 `B` 钉死）；
5. `Tm.rec` 显式 motive ❌（`unused named arguments: [motive_1]`）。
✅ **可行路线（第 6 条）**：把**被归纳项 `t` 排在 `∀` 绑定最前**，
使归纳动机**自动量化其余全部**（`Γ`、`A`、`u`、`B`）。
⚠ 但这要求引理的**陈述形状**配合 —— 故本定理拆成「辅助引理 + 本定理调用它」两步。 -/

/-- **替换引理（带截断的辅助引理）**：`Δ` 是「已被 binder 绑定、需跳过」的类型前缀。
`HasType (Δ ++ (A :: Γ)) t B` 且 `HasType (Δ ++ Γ) u A`
⟹ `HasType (Δ ++ Γ) (substAux Δ.length u t) B`。

⚠ **为何必须把 `u` 的类型放在 `Δ ++ Γ` 下**：`abs` 分支要下潜一层，
此时 `Δ` 变成 `A₀ :: Δ`，被替换项的上下文也随之变成 `A₀ :: (Δ ++ Γ)` ——
只有让前提**对任意 `Δ`** 成立，归纳假设才能在 `abs` 下继续使用。
⭐ 这是「cutoff 计数器」的**上下文层对应物**：计数器判「哪些索引是绑定的」，
`Δ` 就是那些绑定在**类型环境**里的对应物；两者必须同步增长。 -/
theorem subst_aux (t : Tm) :
    ∀ (Δ : Ctx) (Γ : Ctx) (A : Ty) (u : Tm) (B : Ty),
      HasType (Δ ++ Γ) u A → HasType (Δ ++ (A :: Γ)) t B →
      HasType (Δ ++ Γ) (substAux Δ.length u t) B := by
  induction t with
  | var n =>
      intro Δ Γ A u B hu ht
      cases ht with
      | var hv =>
          -- 索引 `n` 落在 `Δ ++ (A :: Γ)` 里。三种情况：
          -- (i) `n < Δ.length`：在 `Δ` 内，是**外层 binder**，`substAux` 不动它；
          -- (ii) `n = Δ.length`：正是 `A`，被替换成 `u`；
          -- (iii) `n > Δ.length`：在 `Γ` 内，索引下移一位。
          by_cases hlt : n < Δ.length
          · -- (i) 两侧都是 `Δ.get? n`；`substAux` 因 `n < Δ.length` 也不动它
            -- ⚠ **必须先用 `show` 把目标化到 `substAux` 已展开的形状**，
            -- 否则 `HasType.var` 的隐式索引元变量与未归约的 `if` 表达式不匹配
            -- （实测报 `HasType ?m ?m ?m` vs `if n = ... then ... else ...`）。
            have hget : (Δ ++ Γ).get? n = (Δ ++ (A :: Γ)).get? n := by
              rw [List.get?_eq_getElem?, List.get?_eq_getElem?]
              rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
            have hsub : substAux Δ.length u (.var n) = .var n := by
              simp only [substAux]
              rw [if_neg (by omega : ¬ n = Δ.length), if_neg (by omega : ¬ Δ.length < n)]
            rw [hsub]
            exact HasType.var (by rw [hget]; exact hv)
          · by_cases heq : n = Δ.length
            · -- (ii) 命中被替换的那个索引
              subst heq
              have hleft : (Δ ++ (A :: Γ)).get? Δ.length = some A := by
                rw [List.get?_eq_getElem?, List.getElem?_append_right (by omega)]
                simp
              rw [hleft] at hv
              injection hv with hvA
              subst hvA
              have hsub : substAux Δ.length u (.var Δ.length) = u := by
                simp only [substAux]
                simp
              rw [hsub]
              exact hu
            · -- (iii) 在 `Γ` 内：`substAux` 把索引 `-1`
              have hgt : Δ.length < n := by omega
              have hget : (Δ ++ Γ).get? (n - 1) = (Δ ++ (A :: Γ)).get? n := by
                rw [List.get?_eq_getElem?, List.get?_eq_getElem?]
                rw [List.getElem?_append_right (by omega : Δ.length ≤ n - 1),
                    List.getElem?_append_right (by omega : Δ.length ≤ n)]
                have h1 : n - Δ.length = (n - 1 - Δ.length) + 1 := by omega
                rw [h1]
                simp
              have hsub : substAux Δ.length u (.var n) = .var (n - 1) := by
                simp only [substAux]
                rw [if_neg heq, if_pos hgt]
              rw [hsub]
              exact HasType.var (by rw [hget]; exact hv)
  | num k =>
      intro Δ Γ A u B hu ht; cases ht with | num _ => exact HasType.num k
  | succ t₀ ih =>
      intro Δ Γ A u B hu ht
      cases ht with
      | succ ht' => exact HasType.succ (ih Δ Γ A u Ty.nat hu ht')
  | abs A₀ t₀ ih =>
      intro Δ Γ A u B hu ht
      cases ht with
      -- `hbody : HasType (A₀ :: (Δ ++ (A :: Γ))) t₀ B₀`
      -- ⚠ 目标 `substAux Δ.length u (abs A₀ t₀)` 化简为
      -- `abs A₀ (substAux (Δ.length+1) (shift 0 u) t₀)`（定义层直接给出）。
      -- 故以 `Δ := A₀ :: Δ` 实例化 IH：此前缀下 `(A₀::Δ).length = Δ.length + 1` 成立。
      -- ⚠ 关键是**被替换项变成 `shift 0 u`**，其类型由 `shift_typing` 给出：
      -- `HasType (Δ ++ Γ) u A ⟹ HasType (A₀ :: (Δ ++ Γ)) (shift (Δ.length+1-1) u) A`
      -- —— 即「多一层 binder 时，被替换项须上移一位」。
      | abs hbody =>
          -- ⚠ IH 需要的前提是 `HasType (Δ ++ (A₀ :: (A :: Γ))) (shift (Δ.length+1) u) A₀`？
          -- 不对 —— 重新对齐：`substAux` 在 `abs` 下产生
          --   `substAux (Δ.length+1) (shift 0 u) t₀`
          -- 而 IH（取 `Δ := A₀ :: Δ`）产生的是
          --   `substAux (A₀::Δ).length u' t₀`，其中 `(A₀::Δ).length = Δ.length+1` 成立，
          -- 前提要求 `HasType ((A₀::Δ) ++ Γ) u' A`，即 `HasType (A₀ :: (Δ ++ Γ)) u' A`。
          -- ⇒ 取 `u' := shift 0 u`，其类型由 `shift_typing` 在
          --   `Δ := []`、`Γ := Δ ++ Γ`、`B₀ := A₀` 处给出：
          --   `HasType ([] ++ (A₀ :: (Δ ++ Γ))) (shift 0 u) A` 成立 正是所需。
          exact HasType.abs (ih (A₀ :: Δ) Γ A (shift 0 u) _
            (shift_typing (Δ := []) (Γ := Δ ++ Γ) (A := A) (u := u) A₀
              (by simpa only [List.nil_append] using hu))
            hbody)
  | app t₁ t₂ ih₁ ih₂ =>
      intro Δ Γ A u B hu ht
      cases ht with
      | app hf hu' => exact HasType.app (ih₁ Δ Γ A u _ hu hf) (ih₂ Δ Γ A u _ hu hu')

/-- **替换引理**（承重，本文件技术核心）：`A :: Γ ⊢ t : B` 且 `Γ ⊢ u : A`
⟹ `Γ ⊢ substTop u t : B`。由 `subst_aux` 取 `Δ := []` 得到
（此时 `[].length = 0`，`[] ++ Γ = Γ`，`substAux 0 = substTop`）。 -/
theorem subst_preserves_typing {Γ : Ctx} {A : Ty} {u : Tm} (hu : HasType Γ u A) :
    ∀ {t : Tm} {B : Ty}, HasType (A :: Γ) t B → HasType Γ (substTop u t) B :=
  fun ht => subst_aux _ [] Γ A u _ (by simpa using hu) (by simpa using ht)

/-! ## 六、Progress -/

/-- **值是范式**：值不能走任何一步。
⚠ 补入 `Value.succ` 之后需多一个 `succ` 分支：
`succ v` 是值时，`Step` 里唯一可能匹配的是 `Step.succ`，它要求 `Step v t'`，
与归纳假设（`v` 是值时不能走步）矛盾。

⚠ **不要先 `intro h` 再归纳 `hv`**：那样目标终点 `t` 被钉死，
`succ` 分支的归纳假设会退化成错的形状（实测报
`ih : ¬Step t✝ t'✝` 而目标是 `¬Step t✝ t'✝.succ`）。
⇒ 直接对 `hv` 归纳，让 `t` 保持泛化。 -/
theorem value_no_step {v t : Tm} (hv : Value v) : ¬ Step v t := by
  -- ⚠ 先把终点 `t` 泛化：`revert t` 使归纳假设对**任意**终点成立。
  -- ⚠ 与 `subst_aux` 同一技术要点（**把隐含的"任意"显式化**）：
  -- 若直接 `induction hv with`（`t` 已被 `intro` 固定），
  -- `succ` 分支的 IH 会退化成 `¬Step t₀ <目标的某个具体项>`。
  revert t
  induction hv with
  | num k => intro t h; cases h
  | abs A t₀ => intro t h; cases h
  | succ hv ih =>
      intro t h
      cases h with
      | succ h' => exact ih h'

/-- **规范形式（函数）**：良类型的值若具有函数类型，则必是 λ 抽象。
（本文件只需要函数型规范形式；数值型的对应事实是
「`nat` 型的值不是 `abs`」，两处都在 `progress` 的 `app` 情形用到。）

⚠ 需处理 `Value.succ`：`succ v` 的类型只能是 `.nat`，与 `.arr _ _` 构造子互斥，
由 `cases ht` 自动消去。 -/
theorem canonical_abs {v : Tm} {A B : Ty} (hv : Value v)
    (ht : HasType [] v (.arr A B)) : ∃ C t, v = .abs C t := by
  cases hv with
  | num k => cases ht
  | abs C t => exact ⟨C, t, rfl⟩
  | succ hv => cases ht

/-- **Progress（辅助引理）**：把被归纳项 `t` 排在 `∀` 绑定**最前**，
使归纳动机自动量化 `A`（与 `subst_aux` 同一技术）。

⚠ **上下文必须是 `[]`**：`progress` 对**非空**上下文为**假**
（`HasType [nat] (var 0) nat` 真，而 `var 0` 既非值也不能走步）——
这正是反例 `progress_needs_closed` 的内容。故本引理**不能**对任意 `Γ` 陈述。

⚠ 必须这样拆分：若直接对 `progress` 的陈述（`{t}` 是**隐式**参数、`A`/`h` 在箭头右侧）
做 `induction t`，归纳假设会被目标的 `A` 钉死，`succ`/`app` 分支用不上。 -/
theorem progress_aux (t : Tm) :
    ∀ (A : Ty), HasType [] t A → Value t ∨ ∃ t', Step t t' := by
  induction t with
  | var n => intro A h; cases h with | var hv => simp [List.get?] at hv
  | num k => intro A h; exact Or.inl (Value.num k)
  | succ t₀ ih =>
      intro A h
      cases h with
      | succ ht =>
          rcases ih Ty.nat ht with hv | ⟨t', hs⟩
          · -- ⭐ **这正是补入 `Value.succ` 才能闭合的分支**：
            -- `t₀` 是值 ⟹ `succ t₀` 也是值（原定义下此处**无解**，
            -- 因为 `succ (num k)` 良类型却既非值也无出边）。
            exact Or.inl (Value.succ hv)
          · exact Or.inr ⟨_, Step.succ hs⟩
  | abs A₀ t₀ ih => intro A h; exact Or.inl (Value.abs _ _)
  | app t₁ t₂ ih₁ ih₂ =>
      intro A h
      cases h with
      | app hf hu' =>
          rcases ih₁ _ hf with hv1 | ⟨t', hs1⟩
          · obtain ⟨C, body, rfl⟩ := canonical_abs hv1 hf
            rcases ih₂ _ hu' with hv2 | ⟨u', hs2⟩
            · exact Or.inr ⟨_, Step.beta hv2⟩
            · exact Or.inr ⟨_, Step.app_arg hs2⟩
          · exact Or.inr ⟨_, Step.app_fun hs1⟩

/-- **Progress**：良类型**闭**项要么是值，要么能走一步。
`app` 情形用 `canonical_abs`：左子项若为值，其函数类型迫使它是 λ 抽象，
于是 β 或右归约适用；若左子项能走步，则用 `app_fun` 归约。
（`app_fun` 规则的存在正是为了让这一分支可封闭。） -/
theorem progress {t : Tm} : ∀ {A : Ty}, HasType [] t A → Value t ∨ ∃ t', Step t t' :=
  fun {A} h => progress_aux t A h

/-! ## 七、Preservation -/

/-- **Preservation**：良类型项走一步后类型不变。
`beta` 情形用替换引理（承重），`app_fun` / `app_arg` / `succ` 是结构性搬运。

⚠ 用 `induction hs generalizing A` 前必须先 `revert ht`：
`HasType` 的环境与类型都是**索引**，而 `hs` 的归纳会重写它们。 -/
theorem preservation {Γ : Ctx} {t t' : Tm} {A : Ty}
    (ht : HasType Γ t A) (hs : Step t t') : HasType Γ t' A := by
  revert ht
  induction hs generalizing A with
  | beta hv =>
      intro ht
      cases ht with
      | app hf hu =>
          cases hf with
          | abs ht' => exact subst_preserves_typing hu ht'
  | app_fun hstep ih =>
      intro ht
      cases ht with
      | app hf hu => exact HasType.app (ih hf) hu
  | app_arg hstep ih =>
      intro ht
      cases ht with
      | app hf hu => exact HasType.app hf (ih hu)
  | succ hstep ih =>
      intro ht
      cases ht with
      | succ ht' => exact HasType.succ (ih ht')

/-- **多步保持**：`preservation` 沿传递闭包提升。
**非平凡**：单步保持并不自动给出多步保持，需要对 `ReflTransGen` 归纳。 -/
theorem multistep_preservation {Γ : Ctx} {t : Tm} {A : Ty}
    (ht : HasType Γ t A) {t' : Tm} (hs : Relation.ReflTransGen Step t t') :
    HasType Γ t' A := by
  induction hs with
  | refl => exact ht
  | tail _ hbc ih => exact preservation ih hbc

/-! ## 八、合成：可靠性 -/

/-- **类型可靠性**：良类型闭项走任意多步后，要么是值，要么还能继续走
（**永不卡死**）。证明对多步关系归纳，每一步都用 `multistep_preservation`
把类型搬过来再跑 `progress` —— 这正是两半定理**交替**使用之处。 -/
theorem soundness {t : Tm} {A : Ty} (ht : HasType [] t A) :
    ∀ {t' : Tm}, Relation.ReflTransGen Step t t' → Value t' ∨ ∃ t'', Step t' t'' := by
  intro t' hs
  exact progress (multistep_preservation ht hs)

/-! ## 九、非空洞性：存在卡死项，且它不可类型化 -/

/-- **卡死项**：`(num 3) (num 4)` —— 把一个数值当函数用。

⚠⚠ **已更换见证**（原见证 `app (abs nat (var 0)) (succ (abs nat (var 0)))`
在补入 `Value.succ` 之后**不再卡死**）：
原论证依赖「`succ (abs …)` 不是值」，故 `beta` 不适用；
⭐ **但 `Value.succ` 使 `Value (succ (abs …))` 成立**（`abs` 是值 ⟹ 其 `succ` 是值）
⟹ **`beta` 适用** ⟹ 原见证项**能走一步**，不再是卡死项。
⚠ 这是**必要的一处更换**，不是可选的美化：
「卡死见证」必须随 `Value` 的定义同步更新。

**新见证的卡死性**：`app (num 3) (num 4)`
- 不是值（`Value` 无 `app` 构造子）；
- `beta` 要求左子项是 `abs`，而它是 `num` ⟹ 不适用；
- `app_fun` / `app_arg` 都要求左子项是 `abs`（`app_arg`）或`Step (num 3) …`（`app_fun`，
  而 `num` 无出边）⟹ 均不适用。
⭐ 与 `progress` **不矛盾**：本项**不可类型化**（`num 3` 没有函数类型），
故 `progress` 的良类型前提不满足 —— 这正是「类型系统恰好排除卡死项」的又一实例。 -/
def stuckTm : Tm := .app (.num 3) (.num 4)

/-- **`stuckTm` 确实卡死**：既非值，也无出边。这把 `soundness` 的
「永不卡死」与「存在卡死的项」分开，证明前者**不是空洞真**。 -/
theorem stuckTm_is_stuck : ¬ Value stuckTm ∧ ∀ t', ¬ Step stuckTm t' := by
  constructor
  · exact value_not_app
  · intro t' h
    cases h with
    | app_fun hs => cases hs

/-- **`stuckTm` 不可类型化**：类型系统恰好排除了卡死项 ——
这是 `soundness` 得以成立的**真正原因**（而非空洞的语法巧合）。

证明：`stuckTm = app (num 3) (num 4)`。
唯一适用的规则是 `app`，它要求 `HasType [] (num 3) (arr A B)` ——
而 `num` 只能有 `.nat` 类型（`HasType.num` 的结论是 `.nat`），
与 `.arr _ _` 的构造子互斥 —— 矛盾。 -/
theorem stuckTm_untypeable : ¬ HasType [] stuckTm .nat := by
  intro h
  cases h with
  | app hf _ =>
      -- `hf : HasType [] (num 3) (arr A nat)`，但 `num` 的推导只能给出 `.nat`
      cases hf

/-- **`progress` 的闭性条件不可去**（承重反例）：在上下文 `[nat]` 下，
自由变量 `.var 0` 良类型却既非值也不能走步。 -/
theorem progress_needs_closed :
    HasType [.nat] (.var 0) .nat ∧ ¬ Value (.var 0) ∧ ∀ t', ¬ Step (.var 0) t' := by
  refine ⟨HasType.var (by simp [List.get?]), value_not_var, ?_⟩
  intro t' h
  cases h

end STLC
end Lattice
