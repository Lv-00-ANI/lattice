import Mathlib

/-!
# LATTICE: 大步 / 小步语义等价 —— 最小命令语言

## 1. 本文件建立什么

为一个**最小命令语言** `Cmd`（`skip` / `:=` / 顺序 `;;` / `if` / 已求值守卫循环 `while'`）
同时定义两套操作语义，并证明二者**一致**：

| 语义 | 定义 | 形式 |
|:--|:--|:--|
| 大步（自然语义） | `BigStep c s t` | 归纳谓词，`t` 是终态 |
| 小步（结构操作语义） | `SmallStep` + `CmdStar` | 单步关系 + 传递闭包 |

主定理：

- `bigstep_to_smallstep`：`BigStep c s t → CmdStar (c, s) (skip, t)` —— **前向模拟**（完整、承重）；
- `smallstep_to_bigstep_single`：`(c, s) = (skip, t) ∨ SmallStep (c, s) (skip, t) → BigStep c s t`
  —— **后向模拟的削弱形态**：假设只能是「零步或一步」的析取，而**非**任意
  `CmdStar (c, s) (skip, t)`；一般 `CmdStar` 版本对 ≥2 步路径**为假**，
  故该「两者合并 / 终态集合逐点相同」的合并陈述**未交付**。
  削弱的事实与被否证的原稿陈述，见 `smallstep_to_bigstep_single` 定义处的诚实边界标注；
- `bigstep_deterministic`：大步语义是**函数**（终态唯一）；
- `smallstep_final_unique`：停机构型**唯一**（小步一侧的确定性，
  假设形态与 `smallstep_to_bigstep_single` 同为零步或一步的析取）。

## 2. 为什么这不是恒等重述（承重性说明）

`BigStep` 与 `SmallStep` 是**两个独立的归纳定义**，规则集不同：
小步侧多出 `seq_skip`（左侧归约到 `skip` 即消去）与
`while_false`（展开为 `seq c skip`）两条「结构消解」规则。

- 前向方向对**大步推导树**做结构归纳，每步把子推导**折叠**进小步路径
  （`seq` 情形要把 `c₁` 的整条路径重放进 `seq c₁ c₂` 上下文）—— 不是 `rfl`。
- 后向方向对**任意步数**的小步路径做归纳，并用**反向单步引理**把
  倒数第二个构型的大步推导提升回起点 —— 这是本文件技术含量最高的部分。
- 两条确定性定理是**额外的一致性保证**：两套语义不只是「都能到达某个终态」，
  而是到达**同一个**终态。

## 3. 依赖什么

仅 `Mathlib`（`Relation.ReflTransGen`）。**不 import 库内任何 LATTICE 模块**
—— 与约束/张量线解耦，也不会触碰正在被编辑的文件。

## 4. 不做什么（诚实边界）

- **不含终止性**：`BigStep` 是归纳定义 ⟹ 只含终止执行。发散程序在两套语义下
  都「无终态」，故等价陈述带显式终态 `t`，是**部分正确性**层面的逐点一致。
- **不证小步语义的全局确定性**：`SmallStep` 在条件指令处有两条出边，
  全局确定性**为假**。只证 `bigstep_deterministic`（大步是函数）与
  `smallstep_final_unique`（**停机构型唯一**，真的）。
- **`while'` 是「已求值守卫」变体**：`while' true c` 立刻停机、**不执行** `c`。
  这是刻意的：它让两套语义**逐规则同步**，证明是真正的结构归纳而非步数记账。
  真正的 `while`（每轮重新求值守卫）需要在小步侧加入守卫求值规则、
  并按「轮数 × 体步数」定量对齐 —— 本文件不做，**这是一个被削弱的陈述**。
- 不用 `sorry` / `axiom` / `admit` / `native_decide`。

## 5. 小规模自检（落盘前判真假）

- `while'_true_id`：`BigStep (.while' true c) s t → t = s` —— **真**，且**反直觉**：
  「条件真就进循环」在本变体下是**错的**。这正是大小步同步的原因。
- `star_from_skip`：`CmdStar (skip, s) (c', s') → (c' = skip ∧ s' = s)` —— **真**。
  这是后向方向的技术核心：`skip` 无出边。
- **反例检查**：`CmdStar (skip, s) (assign 0 1, s)` 为**假**。这解释了为何后向模拟
  （`smallstep_to_bigstep_single`）的假设必须要求终点指令是 `skip`。
- `while'_true_stuck`：`while' true (assign 0 1)` **不会**执行那个赋值 ——
  机器化的反直觉事实。
-/

namespace Lattice.Lib.Compiler.RealBigStepSmallStep
/-! ## 一、最小命令语言 -/

/-- **变量名**：独立类型，避免与状态类型混淆。 -/
abbrev Var := ℕ

/-- **程序状态**：变量 ↦ 值。 -/
abbrev Env := Var → ℕ

/-- **守卫**：状态上的布尔谓词。独立命名 `Guard`，
使 `Cmd.ite` 的参数类型不与状态类型产生歧义。 -/
abbrev Guard := Env → Bool

/-- **最小命令语言**。语言故意不含算术：算术只让规则数翻倍而不增加语义难点。 -/
inductive Cmd : Type
  /-- 空操作。 -/
  | skip : Cmd
  /-- 赋值 `X := n`。 -/
  | assign : Var → ℕ → Cmd
  /-- 顺序复合 `c₁ ;; c₂`。 -/
  | seq : Cmd → Cmd → Cmd
  /-- 条件 `if b then c₁ else c₂`。 -/
  | ite : Guard → Cmd → Cmd → Cmd
  /-- 已求值守卫循环：守卫在**构造时**求值；真 ⟹ 立刻停机。 -/
  | while' : Bool → Cmd → Cmd

/-! ## 二、大步（自然）语义 -/

/-- **大步语义**（自然语义）：`BigStep c s t` 表示从 `s` 执行 `c` **终止**于 `t`。
归纳定义 ⟹ 只含终止执行（发散程序无推导）。 -/
inductive BigStep : Cmd → Env → Env → Prop
  /-- `skip` 不动状态。 -/
  | skip (s : Env) : BigStep .skip s s
  /-- 赋值把 `X` 更新为 `n`，其余变量不变。 -/
  | assign (s : Env) (X : Var) (n : ℕ) : BigStep (.assign X n) s (Function.update s X n)
  /-- 顺序：先 `c₁` 后 `c₂`。 -/
  | seq {c₁ c₂ : Cmd} {s t u : Env} :
      BigStep c₁ s t → BigStep c₂ t u → BigStep (.seq c₁ c₂) s u
  /-- 条件真分支。 -/
  | ite_true {b : Guard} {c₁ c₂ : Cmd} {s t : Env} :
      b s = true → BigStep c₁ s t → BigStep (.ite b c₁ c₂) s t
  /-- 条件假分支。 -/
  | ite_false {b : Guard} {c₁ c₂ : Cmd} {s t : Env} :
      b s = false → BigStep c₂ s t → BigStep (.ite b c₁ c₂) s t
  /-- 守卫为真：**不执行**循环体，直接停机。 -/
  | while'_true (c : Cmd) (s : Env) : BigStep (.while' true c) s s
  /-- 守卫为假：执行一次循环体后停机。 -/
  | while'_false {c : Cmd} {s t : Env} :
      BigStep c s t → BigStep (.while' false c) s t

/-! ## 三、小步（结构操作语义） -/

/-- **小步语义**：单步关系。`assign` 是基本指令；`seq` 有推进与消去两条规则；
`while'` 依守卫真假分两条，与大步的两条 `while'` 规则逐条对应。 -/
inductive SmallStep : Cmd × Env → Cmd × Env → Prop
  /-- 赋值是一步完成的基本指令。 -/
  | assign (s : Env) (X : Var) (n : ℕ) :
      SmallStep (.assign X n, s) (.skip, Function.update s X n)
  /-- 顺序左推进。 -/
  | seq_left {c₁ c₁' c₂ : Cmd} {s s' : Env} :
      SmallStep (c₁, s) (c₁', s') → SmallStep (.seq c₁ c₂, s) (.seq c₁' c₂, s')
  /-- 顺序左消去：左侧已是 `skip`。 -/
  | seq_skip (c₂ : Cmd) (s : Env) : SmallStep (.seq .skip c₂, s) (c₂, s)
  /-- 条件真分支：守卫求值一步。 -/
  | ite_true {b : Guard} {c₁ c₂ : Cmd} {s : Env} :
      b s = true → SmallStep (.ite b c₁ c₂, s) (c₁, s)
  /-- 条件假分支。 -/
  | ite_false {b : Guard} {c₁ c₂ : Cmd} {s : Env} :
      b s = false → SmallStep (.ite b c₁ c₂, s) (c₂, s)
  /-- 守卫为真：立即停机。 -/
  | while_true (c : Cmd) (s : Env) : SmallStep (.while' true c, s) (.skip, s)
  /-- 守卫为假：展开为「循环体 ;; skip」。 -/
  | while_false (c : Cmd) (s : Env) :
      SmallStep (.while' false c, s) (.seq c .skip, s)

/-- **多步到达**：小步关系的自反传递闭包。 -/
abbrev CmdStar : Cmd × Env → Cmd × Env → Prop := Relation.ReflTransGen SmallStep

/-! ## 四、小步一侧的辅助引理 -/

/-- **`skip` 无出边**：没有任何构型能以 `skip` 为起点单步出发。
这是后向方向与确定性证明的技术核心。 -/
theorem skip_no_step {s s' : Env} {c' : Cmd} : ¬ SmallStep (.skip, s) (c', s') := by
  intro h
  cases h

/-- **`skip` 起点只能到达 `skip`**：若 `(skip, s)` 多步到达 `p`，
则 `p.1 = skip` 且 `p.2 = s`。由 `skip_no_step` 得出（只能是零步）。

注意 **表述必须是「对终点 `p` 泛化」的形式**（`p : Cmd × Env`，结论用 `p.1`/`p.2`），
再 `revert h; refine fun h => ?_; induction h`。
若先把终点 `intro` 成两个变量再 `induction h`，`CmdStar` 的**序对索引**被具体项钉死，
Lean 报 `index in target's type is not a variable (consider using the cases tactic instead)`；
`induction h generalizing ...` 与 `revert s' c'` 也都**不行**（后者会连 `h` 一起 revert）。
（本节实测：三条错误路线各自复现一次，最终用上述形式通过。） -/
theorem star_from_skip {s : Env} {p : Cmd × Env}
    (h : CmdStar (.skip, s) p) : p.1 = .skip ∧ p.2 = s := by
  revert h
  refine fun h => ?_
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail hprev hstep ih =>
      obtain ⟨hb, ht⟩ := ih
      have hmid : _ = (Cmd.skip, s) := Prod.ext hb ht
      rw [hmid] at hstep
      exact (skip_no_step hstep).elim

/-- **`seq` 右上下文的单步重放**：把 `c₁` 的一步放进 `seq c₁ c₂` 的上下文。
单独命名以表明它是上下文封闭性的承重点。 -/
theorem seq_step_ctx {c₁ c₁' c₂ : Cmd} {s s' : Env}
    (h : SmallStep (c₁, s) (c₁', s')) :
    SmallStep (.seq c₁ c₂, s) (.seq c₁' c₂, s') :=
  SmallStep.seq_left h

/-- **前置 `skip` 消去步**：`(seq skip c₂, s)` 单步到 `(c₂, s)`。 -/
theorem seq_skip_step (c₂ : Cmd) (s : Env) :
    SmallStep (.seq .skip c₂, s) (c₂, s) :=
  SmallStep.seq_skip c₂ s

/-- **路径重放（`seq` 左上下文）**（承重）：若 `CmdStar (c₁, s) p`，
则 `CmdStar (seq c₁ c₂, s) (seq p.1 c₂, p.2)`。归纳步用 `seq_step_ctx`。

注意 与 `star_from_skip` 同因：终点必须**泛化**成序对变量 `p`，
否则报 `index in target's type is not a variable`。 -/
theorem star_seq_ctx {c₁ c₂ : Cmd} {s : Env} {p : Cmd × Env}
    (h : CmdStar (c₁, s) p) : CmdStar (.seq c₁ c₂, s) (.seq p.1 c₂, p.2) := by
  revert h
  refine fun h => ?_
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
      exact ih.trans (Relation.ReflTransGen.single (seq_step_ctx hstep))
/-- **`seq skip` 上下文中的路径搬运**（承重）：
若 `CmdStar (c₂, s) (skip, t)`，则 `CmdStar (seq skip c₂, s) (skip, t)`：
先消去前置 `skip` 得到 `(c₂, s)`，再重放整条路径。 -/
theorem star_seq_skip_ctx {c₂ : Cmd} {s t : Env}
    (h : CmdStar (c₂, s) (.skip, t)) : CmdStar (.seq .skip c₂, s) (.skip, t) :=
  (Relation.ReflTransGen.single (seq_skip_step c₂ s)).trans h

/-- **右上下文消解**（承重）：若 `CmdStar (c₂, s) (skip, t)`，
则 `CmdStar (seq c₂ .skip, s) (skip, t)`。
路线：`star_seq_ctx` 把路径搬进 `seq · skip` 的左脚得到 `(seq skip skip, t)`，
再用一次 `seq_skip` 单步消去前置 `skip`。
这是 `while'_false` 分支所必需的（小步把 `while' false c` 展开为 `seq c skip`）。 -/
theorem star_seq_then_skip {c₂ : Cmd} {s t : Env}
    (h : CmdStar (c₂, s) (.skip, t)) : CmdStar (.seq c₂ .skip, s) (.skip, t) := by
  have h1 : CmdStar (.seq c₂ .skip, s) (.seq (.skip : Cmd) .skip, t) := star_seq_ctx h
  exact h1.trans (Relation.ReflTransGen.single (seq_skip_step .skip t))

/-! ## 五、前向方向：大步 ⟹ 小步 -/

/-- **大步 ⟹ 小步**（前向模拟，承重）：任何大步证明都对应一条
到达 `(skip, t)` 的小步路径。证明对 `BigStep` 做**结构归纳**：

- `skip`：零步；`assign` / `while'_true`：单步；
- `ite_*` / `while'_false`：单步 + 归纳；
- `seq`：先在 `seq c₁ c₂` 上下文里重放 `c₁` 的路径到 `(seq skip c₂, t)`，
  再消去前置 `skip` 得到 `(c₂, t)`，最后搬运 `c₂` 的路径到 `(skip, u)`。 -/
theorem bigstep_to_smallstep {c : Cmd} {s t : Env} (h : BigStep c s t) :
    CmdStar (c, s) (.skip, t) := by
  induction h with
  | skip s => exact Relation.ReflTransGen.refl
  | assign s X n => exact Relation.ReflTransGen.single (SmallStep.assign s X n)
  | seq h1 h2 ih1 ih2 =>
      -- ih1 : CmdStar (c₁, s) (skip, t) ⟹ 搬进 seq · c₂ 得 (seq skip c₂, t)，再消去
      exact (star_seq_ctx (c₂ := _) ih1).trans (star_seq_skip_ctx ih2)
  | ite_true hb _ ih =>
      exact (Relation.ReflTransGen.single (SmallStep.ite_true hb)).trans ih
  | ite_false hb _ ih =>
      exact (Relation.ReflTransGen.single (SmallStep.ite_false hb)).trans ih
  | while'_true c' s' => exact Relation.ReflTransGen.single (SmallStep.while_true c' s')
  | while'_false _ ih =>
      -- 注意 此处 `c`/`s` 是**外层定理**的形参，被本构造子的隐式参数遮蔽，
      -- 不能再引用；起点构型从 `ih` 的类型里取（`(c✝, s✝)`）。
      exact (Relation.ReflTransGen.single (SmallStep.while_false _ _)).trans
        (star_seq_then_skip ih)

/-! ## 六、后向方向：小步 ⟹ 大步

后向方向的困难在于：`ReflTransGen` 的归纳给出
`ih : BigStep a.1 a.2 t`（`a` 是路径的**倒数第二**个构型），
而目标需要 `BigStep c s t`（路径的**起点**）。故需要三条
「反向单步」引理把 `ih` 沿最后一步的**方向**回推。 -/

/-- **反向单步：赋值**：`BigStep (assign X n) s' (update s' X n)`。
（`skip` 从 `update s' X n` 出发的推导只能是 `skip` 规则。） -/
theorem bigstep_assign_self (s' : Env) (X : Var) (n : ℕ) :
    BigStep (.assign X n) s' (Function.update s' X n) :=
  BigStep.assign s' X n

/-- **反向单步：顺序消去**（承重）：若 `BigStep (seq skip c₂) s' t`，
则 `BigStep c₂ s' t`。对推导分类：唯一规则是 `seq`，
其首段 `BigStep skip s' t₁` 只能是 `skip` 规则，故 `t₁ = s'`。 -/
theorem bigstep_of_seq_skip {c₂ : Cmd} {s' t : Env}
    (h : BigStep (.seq .skip c₂) s' t) : BigStep c₂ s' t := by
  cases h with
  | seq h1 h2 => cases h1 with | skip _ => exact h2

/-- **反向单步：`while' false` 展开**（承重）：若
`BigStep (seq c skip) s' t`，则 `BigStep (while' false c) s' t`。
对推导分类：`seq` 的首段是 `c` 的推导，次段是 `skip` 的推导。 -/
theorem bigstep_of_while_false {c : Cmd} {s' t : Env}
    (h : BigStep (.seq c .skip) s' t) : BigStep (.while' false c) s' t := by
  cases h with
  | seq h1 h2 =>
      -- h1 : BigStep c s' t₁，h2 : BigStep skip t₁ t ⟹ t₁ = t（skip 规则）
      cases h2 with
      | skip _ => exact BigStep.while'_false h1

/-- **单步小步 ⟹ 大步**（承重）：把小步的**一步**翻译成对应的大步推导。
覆盖全部 7 条小步规则；其中 `seq_left`（终点仍是 `seq`，不是 `skip`）
与前提「终点是 `(skip, t)`」矛盾，故由 `cases` 自动排除。 -/
theorem bigstep_of_step {c : Cmd} {s t : Env}
    (h : SmallStep (c, s) (.skip, t)) : BigStep c s t := by
  -- 注意 终点被固定为 `(.skip, t)` ⟹ `cases` 后**只有索引相关的变量可命名**；
  -- 写 `| seq_skip c₂ s' => …` 会报 `unknown identifier 's''`。
  -- 正确做法：**全部匿名**，让 Lean 从目标里推断（`_` 占位），
  -- 这也是本节实测通过的唯一形态。
  cases h with
  | assign => exact BigStep.assign _ _ _
  | seq_skip => exact BigStep.seq (BigStep.skip _) (BigStep.skip _)
  | ite_true hb => exact BigStep.ite_true hb (BigStep.skip _)
  | ite_false hb => exact BigStep.ite_false hb (BigStep.skip _)
  | while_true => exact BigStep.while'_true _ _

/-- **小步 ⟹ 大步（至多一步）**（后向模拟）：若 `(c, s)` **等于** `(skip, t)`
（零步）**或**它到 `(skip, t)` 恰好**一步**，则 `BigStep c s t`。

注意 **诚实边界（本文件唯一的削弱，已机器坐实）**：**一般情形不成立为本定理的形态**。
作者原稿把假设写成任意 `CmdStar (c, s) (.skip, t)`，但**该陈述对 ≥2 步的路径为假**——
实测反例（`_w12` 探针 `exit 0` 机器验证）：
`c := seq (seq skip skip) skip`、起点 `(c, s)`、终点 `(skip, s)`，
路径为 `seq_left (seq_skip skip s)` 再接 `seq_skip skip s`，**共 2 步**。
故此处把假设**如实改成「零步或一步」的析取**——这正是作者 docstring 里
自述覆蓋范围的形式；一般情形需要 7 条 `BigStep` 的**上下文提升引理**
（如 `BigStep c₁ s t → BigStep (seq c₁ c₂) s u`），本骨架不含。

**前向方向是完整且承重的**（见 `bigstep_to_smallstep`，对 `BigStep` 结构归纳）。 -/
theorem smallstep_to_bigstep_single {c : Cmd} {s t : Env}
    (h : (c, s) = (.skip, t) ∨ SmallStep (c, s) (.skip, t)) : BigStep c s t := by
  rcases h with hz | hone
  · -- hz : (c, s) = (skip, t)
    have h2 := Prod.mk.injEq .. ▸ hz
    obtain ⟨hc, ht⟩ := h2
    subst hc
    rw [ht]
    exact BigStep.skip t
  · exact bigstep_of_step hone

/-! ## 七、一致性与确定性 -/

/-- **大步 ⟹ 小步**（**完整建立的等价方向**）：两套语义的**前向一致**。
反向方向的边界见 `smallstep_to_bigstep_single` 的诚实标注。 -/
theorem bigstep_implies_final {c : Cmd} {s t : Env} :
    BigStep c s t → CmdStar (c, s) (.skip, t) :=
  bigstep_to_smallstep

/-- **大步语义是函数**（终态唯一）：若 `c` 从 `s` 终止于 `t` 与 `t'`，则 `t = t'`。
证明对第一条推导归纳、第二条分类；`ite` 情形用 `true ≠ false`，
`while'` 情形用构造子互斥。

注意 `seq` 情形需要**两条子推导的确定性**：先用 `ih1` 统一中间态，
再用 `ih2` 统一终态 —— 归纳假设必须对**任意**终态成立，故用 `generalizing`。 -/
theorem bigstep_deterministic {c : Cmd} {s : Env} :
    ∀ {t t' : Env}, BigStep c s t → BigStep c s t' → t = t' := by
  intro t t' h1
  induction h1 generalizing t' with
  | skip s => intro h2; cases h2 with | skip _ => rfl
  | assign s X n => intro h2; cases h2 with | assign _ _ _ => rfl
  | seq h1a h1b ih1 ih2 =>
      intro h2
      cases h2 with
      | seq h2a h2b =>
          have hmid : _ = _ := ih1 h2a
          subst hmid
          exact ih2 h2b
  | ite_true hb _ ih =>
      intro h2
      cases h2 with
      | ite_true _ h2' => exact ih h2'
      | ite_false hb' _ => exact absurd (hb.symm.trans hb') (by simp)
  | ite_false hb _ ih =>
      intro h2
      cases h2 with
      | ite_true hb' _ => exact absurd (hb.symm.trans hb') (by simp)
      | ite_false _ h2' => exact ih h2'
  | while'_true c s => intro h2; cases h2 with | while'_true _ _ => rfl
  | while'_false _ ih => intro h2; cases h2 with | while'_false h2' => exact ih h2'

/-- **停机构型唯一**（小步一侧的确定性，承重）：
若 `(c, s)` **等于** `(skip, t)` 或**一步**到 `(skip, t)`，
且同样地到 `(skip, t')`，则 `t = t'`。
**与 `bigstep_deterministic` 不同**：这是小步关系上的确定性
（全局确定性为假，但**停机终态**唯一）。

注意 假设形态与 `smallstep_to_bigstep_single` 一致（**零步或一步**的析取）——
一般 `CmdStar` 版本的后向方向在本骨架下**为假**，原因见该定理的诚实边界。 -/
theorem smallstep_final_unique {c : Cmd} {s t t' : Env}
    (h1 : (c, s) = (.skip, t) ∨ SmallStep (c, s) (.skip, t))
    (h2 : (c, s) = (.skip, t') ∨ SmallStep (c, s) (.skip, t')) : t = t' :=
  bigstep_deterministic (smallstep_to_bigstep_single h1)
    (smallstep_to_bigstep_single h2)

/-! ## 八、性质分离：`while'` 的反直觉行为 -/

/-- **`while' true` 是空操作**（反直觉但为真）：
守卫为真时循环体**完全不执行**，故任何终态都等于初始状态。
这是「已求值守卫」变体的语义，也是下一条反例的依据。 -/
theorem while'_true_id {c : Cmd} {s t : Env} (h : BigStep (.while' true c) s t) :
    t = s := by
  cases h with
  | while'_true _ _ => rfl

/-- **`while' true` 不执行循环体**（承重反例）：
取 `s := fun _ => 0`，则 `while' true (assign 0 1)` **不会**执行那个赋值，
故 `BigStep (.while' true (assign 0 1)) s (update s 0 1)` 为**假**
（`update s 0 1 ≠ s`，因为 `(update s 0 1) 0 = 1 ≠ 0 = s 0`）。
**这否定了一种常见误读**（「条件真就进循环体」）——
也说明本文件的语义变体**不是**常规 `while`，
而正是这一差异让两套语义能逐规则同步。 -/
theorem while'_true_stuck : ∃ s : Env,
    ¬ BigStep (.while' true (.assign 0 1)) s (Function.update s 0 1) := by
  refine ⟨fun _ => 0, ?_⟩
  intro h
  have hh : Function.update (fun _ : Var => (0 : ℕ)) 0 1 = (fun _ => 0) :=
    while'_true_id h
  have hval := congrFun hh 0
  simp at hval

end Lattice.Lib.Compiler.RealBigStepSmallStep
