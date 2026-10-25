import Mathlib

/-!
# LATTICE: 带绑定的 λ-演算 —— de Bruijn 语法、提升与并行替换

`RealTypeSystemExt` 刻意裁剪了 λ/应用（其替换只允许「被替换项是值」以避免变量捕获与
索引移位）。本文件补上该基础设施：用 **de Bruijn 索引**表示带绑定项的 λ-演算，
并给出完整的 `lift`/`subst` 相容律。

  1. `Term`：`var ℕ | lam Term | app Term Term`（de Bruijn，无命名变量、无 α-等价问题）；
  2. `upRen`/`ren`：变量重命名与「进入绑定子时的提升」；`ren_id`、`ren_ren`；
  3. `lift`：`lift n t = ren (fun m => m + n) t`（把自由变量整体上移 `n`）；
     `lift_zero`、`lift_zero_id`、`lift_lift`；
  4. `up`/`subst`：并行替换 `σ : ℕ → Term`；`up σ` 在进入绑定子时给出
     「新绑定变量取 var 0，原有替换项整体上移 1」；
  5. **基本相容律**：`ren_subst`、`subst_ren`、`subst_id`、
     **`subst_lift`**（`subst (up σ) (lift 1 t) = lift 1 (subst σ t)`）、
     **`subst_subst`**（`subst σ (subst τ t) = subst (fun n => subst σ (τ n)) t`）；
  6. 自由变量与闭项：`ClosedAt c t`（所有变量 < `c`，即深度 `c` 上下文内的闭项）、
     `Closed`；`RenamingIdBelow`、`closed_ren`、`closed_lift`，
     以及 `IsIdBelow`、`up_isIdBelow`、`closed_subst_eq`。

诚实标注（无 sorry / axiom / admit）：
- 表示法是 **de Bruijn 索引**（不是命名变量），因此替换天然避免捕获；
  「提升」是索引移动而非数学内容，`lift 0 = id` 即「移动 0 步等于恒等」。
- 本文件只建立**语法与替换基础设施**；β-归约与合流见 `RealBetaReduction`，
  Newman 引理见 `RealGlobalConfluence`。本文件不声称任何合流/终止性结论。
- `ClosedAt`/`Closed` 是**语法闭性**（无自由 de Bruijn 索引），不是「值是闭项」的语义主张。
-/

noncomputable section

namespace Lattice

/-! ## 一、项与重命名 -/

/-- de Bruijn 表示的 λ-项：变量索引、抽象、应用。 -/
inductive Term where
  | var (n : ℕ) : Term
  | lam (t : Term) : Term
  | app (t₁ t₂ : Term) : Term
deriving DecidableEq, Repr

/-- 重命名函数在进入绑定子（`lam`）时的提升：`var 0` 保持为新的绑定变量，
其余索引整体加一。 -/
def upRen (ρ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ρ n + 1

/-- 变量重命名 `ren ρ t`：把项中每个自由变量索引 `n` 换成 `ρ n`
（进入绑定子时对 `ρ` 施加 `upRen`）。 -/
def ren (ρ : ℕ → ℕ) : Term → Term
  | .var n => .var (ρ n)
  | .lam t => .lam (ren (upRen ρ) t)
  | .app a b => .app (ren ρ a) (ren ρ b)

/-- 重命名恒等函数保持不变。 -/
theorem upRen_id : upRen id = id := by
  funext n
  cases n with
  | zero => rfl
  | succ m => simp [upRen]

/-- 重命名提升与函数复合相容。 -/
theorem upRen_comp (ρ ρ' : ℕ → ℕ) : upRen (ρ ∘ ρ') = upRen ρ ∘ upRen ρ' := by
  funext n
  cases n with
  | zero => rfl
  | succ m => simp [upRen, Function.comp]

/-- 恒等重命名不改变项。 -/
theorem ren_id (t : Term) : ren id t = t := by
  induction t with
  | var n => rfl
  | lam t ih => simp only [ren, upRen_id, ih]
  | app a b iha ihb => simp only [ren, iha, ihb]

/-- 重命名的复合律：`ren ρ (ren ρ' t) = ren (ρ ∘ ρ') t`。 -/
theorem ren_ren (t : Term) (ρ ρ' : ℕ → ℕ) :
    ren ρ (ren ρ' t) = ren (ρ ∘ ρ') t := by
  induction t generalizing ρ ρ' with
  | var n => rfl
  | lam t ih =>
      simp only [ren]
      rw [ih (upRen ρ) (upRen ρ'), upRen_comp]
  | app a b iha ihb => simp only [ren, iha ρ ρ', ihb ρ ρ']

/-! ## 二、提升 -/

/-- 提升：把项中所有自由变量索引整体增加 `n`。 -/
def lift (n : ℕ) (t : Term) : Term := ren (fun m => m + n) t

/-- 提升 0 步等于恒等。 -/
theorem lift_zero (t : Term) : lift 0 t = t := by
  unfold lift
  have h : (fun m : ℕ => m + 0) = id := by funext m; rfl
  rw [h, ren_id]

/-- `lift 0 = id`（函数等式形式）。 -/
theorem lift_zero_id : lift 0 = id := by
  funext t
  exact lift_zero t

/-- 提升的复合律：`lift n (lift m t) = lift (n + m) t`。 -/
theorem lift_lift (t : Term) (n m : ℕ) : lift n (lift m t) = lift (n + m) t := by
  unfold lift
  rw [ren_ren]
  apply congrArg (fun ρ => ren ρ t)
  funext k
  simp only [Function.comp_apply]
  omega

/-! ## 三、并行替换 -/

/-- 进入绑定子时的替换提升：新绑定变量 `var 0` 保持自身，
原有替换项整体上移 1（避免捕获）。 -/
def up (σ : ℕ → Term) : ℕ → Term
  | 0 => .var 0
  | n + 1 => lift 1 (σ n)

/-- 并行替换 `subst σ t`：把项中第 `n` 个自由变量换成 `σ n`。 -/
def subst (σ : ℕ → Term) : Term → Term
  | .var n => σ n
  | .lam t => .lam (subst (up σ) t)
  | .app a b => .app (subst σ a) (subst σ b)

/-- `up` 对逐点相等的替换保持逐点相等。 -/
theorem up_ext {σ τ : ℕ → Term} (h : ∀ n, σ n = τ n) : ∀ n, up σ n = up τ n := by
  intro n
  cases n with
  | zero => rfl
  | succ m => simp only [up]; rw [h m]

/-- 替换对逐点相等的替换函数保持相等（外延性）。 -/
theorem subst_ext (t : Term) {σ τ : ℕ → Term} (h : ∀ n, σ n = τ n) :
    subst σ t = subst τ t := by
  induction t generalizing σ τ with
  | var n => exact h n
  | lam t ih => simp only [subst]; rw [ih (up_ext h)]
  | app a b iha ihb => simp only [subst, iha h, ihb h]

/-- 重命名与替换可交换：`ren ρ (subst σ t) = subst (fun n => ren ρ (σ n)) t`。 -/
theorem ren_subst (t : Term) (ρ : ℕ → ℕ) (σ : ℕ → Term) :
    ren ρ (subst σ t) = subst (fun n => ren ρ (σ n)) t := by
  induction t generalizing ρ σ with
  | var n => rfl
  | lam t ih =>
      simp only [subst, ren]
      rw [ih (upRen ρ) (up σ)]
      congr 1
      apply subst_ext
      intro n
      cases n with
      | zero => rfl
      | succ m =>
          simp only [up, lift]
          rw [ren_ren, ren_ren]
          congr 1
  | app a b iha ihb => simp only [subst, ren, iha ρ σ, ihb ρ σ]

/-- 替换与重命名可交换：`subst σ (ren ρ t) = subst (fun n => σ (ρ n)) t`。 -/
theorem subst_ren (t : Term) (σ : ℕ → Term) (ρ : ℕ → ℕ) :
    subst σ (ren ρ t) = subst (fun n => σ (ρ n)) t := by
  induction t generalizing σ ρ with
  | var n => rfl
  | lam t ih =>
      simp only [subst, ren]
      rw [ih (up σ) (upRen ρ)]
      congr 1
      apply subst_ext
      intro n
      cases n with
      | zero => rfl
      | succ m => simp only [up, upRen]
  | app a b iha ihb => simp only [subst, ren, iha σ ρ, ihb σ ρ]

/-- `up` 保持替换恒等函数：`up var = var`。 -/
theorem up_var : up (Term.var) = Term.var := by
  funext n
  cases n with
  | zero => rfl
  | succ m => simp [up, lift, ren]

/-- 用变量替换恒等：`subst var t = t`。 -/
theorem subst_id (t : Term) : subst Term.var t = t := by
  induction t with
  | var n => rfl
  | lam t ih => simp only [subst]; rw [up_var, ih]
  | app a b iha ihb => simp only [subst, iha, ihb]

/-- **替换与提升的相容律**：`subst (up σ) (lift 1 t) = lift 1 (subst σ t)`。 -/
theorem subst_lift (t : Term) (σ : ℕ → Term) :
    subst (up σ) (lift 1 t) = lift 1 (subst σ t) := by
  unfold lift
  rw [subst_ren, ren_subst]
  apply subst_ext
  intro n
  simp only [Function.comp_apply, up, lift]

/-- **替换的复合律（替换引理）**：
`subst σ (subst τ t) = subst (fun n => subst σ (τ n)) t`。 -/
theorem subst_subst (t : Term) (σ τ : ℕ → Term) :
    subst σ (subst τ t) = subst (fun n => subst σ (τ n)) t := by
  induction t generalizing σ τ with
  | var n => rfl
  | lam t ih =>
      simp only [subst]
      rw [ih (up σ) (up τ)]
      congr 1
      apply subst_ext
      intro n
      cases n with
      | zero => rfl
      | succ m =>
          simp only [up]
          rw [subst_lift]
  | app a b iha ihb => simp only [subst, iha σ τ, ihb σ τ]

/-! ## 四、自由变量与闭项 -/

/-- `ClosedAt c t`：项 `t` 的所有自由 de Bruijn 索引都 `< c`
（即 `t` 在深度 `c` 的上下文里是闭的）。 -/
def ClosedAt (c : ℕ) : Term → Prop
  | .var n => n < c
  | .lam t => ClosedAt (c + 1) t
  | .app a b => ClosedAt c a ∧ ClosedAt c b

/-- `Closed t`：项 `t` 无自由变量（深度 0 上下文里的闭项）。 -/
def Closed (t : Term) : Prop := ClosedAt 0 t

/-- `RenamingIdBelow c ρ`：重命名 `ρ` 在索引 `< c` 上是恒等。 -/
def RenamingIdBelow (c : ℕ) (ρ : ℕ → ℕ) : Prop := ∀ m, m < c → ρ m = m

/-- `upRen` 保持「在 `< c` 上恒等」。 -/
theorem upRen_idBelow {c : ℕ} {ρ : ℕ → ℕ} (h : RenamingIdBelow c ρ) :
    RenamingIdBelow (c + 1) (upRen ρ) := by
  intro m hm
  cases m with
  | zero => rfl
  | succ k =>
      simp only [upRen]
      rw [h k (by omega)]

/-- **闭项在恒等重命名下不变**。 -/
theorem closed_ren (t : Term) (c : ℕ) (ρ : ℕ → ℕ) (h : RenamingIdBelow c ρ)
    (hc : ClosedAt c t) : ren ρ t = t := by
  induction t generalizing c ρ with
  | var n => simp only [ren]; rw [h n hc]
  | lam t ih =>
      simp only [ren]
      rw [ih (c + 1) (upRen ρ) (upRen_idBelow h) (show ClosedAt (c + 1) t from hc)]
  | app a b iha ihb =>
      simp only [ren]
      rw [iha c ρ h hc.1, ihb c ρ h hc.2]

/-- **闭项在提升下不变**：`Closed t ⟹ lift n t = t`。 -/
theorem closed_lift (t : Term) (n : ℕ) (h : Closed t) : lift n t = t := by
  have hr : RenamingIdBelow 0 (fun m => m + n) := by intro m hm; omega
  exact closed_ren t 0 (fun m => m + n) hr h

/-- `IsIdBelow c σ`：替换 `σ` 在索引 `< c` 上就是变量本身。 -/
def IsIdBelow (c : ℕ) (σ : ℕ → Term) : Prop := ∀ n, n < c → σ n = .var n

/-- `up` 保持「在 `< c` 上是变量本身」。 -/
theorem up_isIdBelow {c : ℕ} {σ : ℕ → Term} (h : IsIdBelow c σ) :
    IsIdBelow (c + 1) (up σ) := by
  intro n hn
  cases n with
  | zero => rfl
  | succ m =>
      simp only [up]
      rw [h m (by omega)]
      simp [lift, ren]

/-- **闭项在「恒等替换」下不变**：若替换在 `< c` 上是变量本身且 `ClosedAt c t`，
则 `subst σ t = t`。 -/
theorem closed_subst_eq (t : Term) (c : ℕ) (σ : ℕ → Term) (h : IsIdBelow c σ)
    (hc : ClosedAt c t) : subst σ t = t := by
  induction t generalizing c σ with
  | var n => exact h n hc
  | lam t ih =>
      simp only [subst]
      rw [ih (c + 1) (up σ) (up_isIdBelow h) (show ClosedAt (c + 1) t from hc)]
  | app a b iha ihb =>
      simp only [subst]
      rw [iha c σ h hc.1, ihb c σ h hc.2]

end Lattice
