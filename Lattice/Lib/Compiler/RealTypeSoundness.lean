import Mathlib

/-!
# LATTICE: 符号 IR 的类型系统健全性（progress + preservation）

约束程序（`RealConstraintSat.satisfiable` 的存在语义、`RealCompilerOpt.Program`
的约束列表）在编译到「权重」之前，先要有一层**符号 IR 的类型系统**：
本文件把符号表达式的最小类型系统形式化，并证明其**健全性**
（well-typed programs don't go wrong）：

  1. `Ty`：类型 `.int | .real | .bool`（整数 / 实数 / 布尔）；
  2. `TypedExpr`：语法（字面量 `litInt` / `litReal` / `litBool`，以及 `add` 与 `cmp`）。
     刻意保持极小（5 个构造子）以保证 progress / preservation **完整可证**；
  3. `HasType : TypedExpr → Ty → Prop`：归纳式定型 ——
     `litInt : int`、`litReal : real`、`litBool : bool`、`add : int→int→int` 与
     `add : real→real→real`、`cmp : int→int→bool`；
  4. `Value : TypedExpr → Prop`：字面量是值；
  5. `Step : TypedExpr → TypedExpr → Prop`：小步语义 —— `add` 的整数/实数求值规则、
     `cmp` 的整数比较规则，以及三个求值上下文（`add` 左右、`cmp` 左）的相容规则；
  6. **`progress`**：良类型表达式要么是值、要么能走一步（无卡死）；
  7. **`preservation`**：`HasType e T ∧ Step e e' ⟹ HasType e' T`（保持定型）；
     以及多步版 `preservation_multistep`；
  8. `canonical_forms_int` / `canonical_forms_real` / `canonical_forms_bool`：
     规范形式引理（良类型的值是字面量）；
  9. **`type_soundness`**：progress + preservation 的合取推论 ——
     良类型项永不卡死，且任意步保持定型；
  10. 退化接口 `type_preservation_add`（加法专用保持）与
      `no_stuck_well_typed_literals`（良类型字面量不卡死）作为命名入口。

诚实标注（无 sorry / axiom / admit）：
- **完整版 progress / preservation 已证**，未做退化；上述 10 中的退化接口是对
  主定理的命名特化，不是替代品。
- 语言刻意极小：`add` 只对同型（`int` 或 `real`）成立、`cmp` 只比较整数、
  无变量 / 无 λ / 无赋值的（非）类型与副作用 —— 这是为「完整可证」而做的
  **规模裁剪**，不是类型系统能力的声称。
- `cmpInt` 用 `decide (m = n)` 生成 `litBool`：ℤ 上的等式判定完全可归约，
  故规则是**可计算**的（对比：ℚ 的 `decide` 会卡在 `Rat.normalize`，
  这正是本文件把「可执行判定」放在 ℤ 上的原因）。
- 模型无关：不依赖任何既有 LATTICE 文件，仅 `import Mathlib`。
-/

noncomputable section

namespace Lattice.Lib.Compiler.RealTypeSoundness
/-! ## 一、类型与语法 -/

/-- 符号 IR 的类型：整数 / 实数 / 布尔。 -/
inductive Ty where
  | int : Ty
  | real : Ty
  | bool : Ty

/-- 符号 IR 的表达式（极小语法）：
字面量 `litInt` / `litReal` / `litBool`，二元 `add`（同型加法）与
`cmp`（整数相等比较，产出布尔）。 -/
inductive TypedExpr where
  | litInt (n : ℤ) : TypedExpr
  | litReal (r : ℝ) : TypedExpr
  | litBool (b : Bool) : TypedExpr
  | add (e₁ e₂ : TypedExpr) : TypedExpr
  | cmp (e₁ e₂ : TypedExpr) : TypedExpr

/-! ## 二、定型关系（归纳式） -/

/-- `HasType e T`：表达式 `e` 有类型 `T`。
`add` 在两个操作数同型时保持该型；`cmp` 比较两个整数并产出布尔。 -/
inductive HasType : TypedExpr → Ty → Prop where
  | litInt (n : ℤ) : HasType (.litInt n) .int
  | litReal (r : ℝ) : HasType (.litReal r) .real
  | litBool (b : Bool) : HasType (.litBool b) .bool
  | addInt {e₁ e₂ : TypedExpr} : HasType e₁ .int → HasType e₂ .int → HasType (.add e₁ e₂) .int
  | addReal {e₁ e₂ : TypedExpr} : HasType e₁ .real → HasType e₂ .real → HasType (.add e₁ e₂) .real
  | cmp {e₁ e₂ : TypedExpr} : HasType e₁ .int → HasType e₂ .int → HasType (.cmp e₁ e₂) .bool

/-- `Value e`：`e` 是值（当前语言中就是三个字面量）。 -/
inductive Value : TypedExpr → Prop where
  | litInt (n : ℤ) : Value (.litInt n)
  | litReal (r : ℝ) : Value (.litReal r)
  | litBool (b : Bool) : Value (.litBool b)

/-! ## 三、小步语义 -/

/-- `Step e e'`：`e` 走一步到 `e'`。
求值规则：整数加法、实数加法、整数比较（`decide (m = n)`，ℤ 上可归约）；
相容规则：`add` 左/右与 `cmp` 左的操作数求值
（`cmp` 右项只在左项为字面量后求值，故右项相容规则列在右项本身
——这里用左右两条相容规则覆盖，见 `cmpR`）。 -/
inductive Step : TypedExpr → TypedExpr → Prop where
  | addInt (m n : ℤ) : Step (.add (.litInt m) (.litInt n)) (.litInt (m + n))
  | addReal (r s : ℝ) : Step (.add (.litReal r) (.litReal s)) (.litReal (r + s))
  | cmpInt (m n : ℤ) : Step (.cmp (.litInt m) (.litInt n)) (.litBool (decide (m = n)))
  | addL {e₁ e₁' e₂ : TypedExpr} : Step e₁ e₁' → Step (.add e₁ e₂) (.add e₁' e₂)
  | addR {e₁ e₂ e₂' : TypedExpr} : Step e₂ e₂' → Step (.add e₁ e₂) (.add e₁ e₂')
  | cmpL {e₁ e₁' e₂ : TypedExpr} : Step e₁ e₁' → Step (.cmp e₁ e₂) (.cmp e₁' e₂)
  | cmpR {e₁ e₂ e₂' : TypedExpr} : Step e₂ e₂' → Step (.cmp e₁ e₂) (.cmp e₁ e₂')

/-- 多步语义（自反传递闭包，自包含定义以免依赖外部 API）。 -/
inductive MultiStep : TypedExpr → TypedExpr → Prop where
  | refl {e : TypedExpr} : MultiStep e e
  | step {e e' e'' : TypedExpr} : Step e e' → MultiStep e' e'' → MultiStep e e''

/-! ## 四、规范形式引理 -/

/-- **规范形式（整数）**：良类型的值是整数表达式。 -/
theorem canonical_forms_int {e : TypedExpr} (hv : Value e) (ht : HasType e .int) :
    ∃ n : ℤ, e = .litInt n := by
  cases hv with
  | litInt n => exact ⟨n, rfl⟩
  | litReal r => cases ht
  | litBool b => cases ht

/-- **规范形式（实数）**：良类型的值是实数表达式。 -/
theorem canonical_forms_real {e : TypedExpr} (hv : Value e) (ht : HasType e .real) :
    ∃ r : ℝ, e = .litReal r := by
  cases hv with
  | litInt n => cases ht
  | litReal r => exact ⟨r, rfl⟩
  | litBool b => cases ht

/-- **规范形式（布尔）**：良类型的值是布尔表达式。 -/
theorem canonical_forms_bool {e : TypedExpr} (hv : Value e) (ht : HasType e .bool) :
    ∃ b : Bool, e = .litBool b := by
  cases hv with
  | litInt n => cases ht
  | litReal r => cases ht
  | litBool b => exact ⟨b, rfl⟩

/-! ## 五、进度（progress）：良类型项不卡死 -/

/-- **进度**：若 `e` 有类型 `T`，则 `e` 要么是值，要么能走一步（`∃ e', Step e e'`）。
证明：对定型推导归纳，逐构造子用规范形式引理 + 相容规则。 -/
theorem progress {e : TypedExpr} {T : Ty} (ht : HasType e T) :
    Value e ∨ ∃ e', Step e e' := by
  induction ht with
  | litInt n => exact Or.inl (Value.litInt n)
  | litReal r => exact Or.inl (Value.litReal r)
  | litBool b => exact Or.inl (Value.litBool b)
  | addInt h1 h2 ih1 ih2 =>
      rcases ih1 with hv1 | ⟨e1', hs1⟩
      · obtain ⟨m, rfl⟩ := canonical_forms_int hv1 h1
        rcases ih2 with hv2 | ⟨e2', hs2⟩
        · obtain ⟨n, rfl⟩ := canonical_forms_int hv2 h2
          exact Or.inr ⟨_, Step.addInt m n⟩
        · exact Or.inr ⟨_, Step.addR hs2⟩
      · exact Or.inr ⟨_, Step.addL hs1⟩
  | addReal h1 h2 ih1 ih2 =>
      rcases ih1 with hv1 | ⟨e1', hs1⟩
      · obtain ⟨r, rfl⟩ := canonical_forms_real hv1 h1
        rcases ih2 with hv2 | ⟨e2', hs2⟩
        · obtain ⟨s, rfl⟩ := canonical_forms_real hv2 h2
          exact Or.inr ⟨_, Step.addReal r s⟩
        · exact Or.inr ⟨_, Step.addR hs2⟩
      · exact Or.inr ⟨_, Step.addL hs1⟩
  | cmp h1 h2 ih1 ih2 =>
      rcases ih1 with hv1 | ⟨e1', hs1⟩
      · obtain ⟨m, rfl⟩ := canonical_forms_int hv1 h1
        rcases ih2 with hv2 | ⟨e2', hs2⟩
        · obtain ⟨n, rfl⟩ := canonical_forms_int hv2 h2
          exact Or.inr ⟨_, Step.cmpInt m n⟩
        · exact Or.inr ⟨_, Step.cmpR hs2⟩
      · exact Or.inr ⟨_, Step.cmpL hs1⟩

/-! ## 六、保持（preservation）：步进保持定型 -/

/-- **保持**：`Step e e'` 且 `e` 有类型 `T` ⟹ `e'` 也有类型 `T`。
证明：对单步推导归纳；求值规则由结果字面量的定型给出，
相容规则由归纳假设在子项上保持定型。 -/
theorem preservation {e e' : TypedExpr} (hs : Step e e') :
    ∀ {T : Ty}, HasType e T → HasType e' T := by
  induction hs with
  | addInt m n =>
      intro T ht
      cases ht with
      | addInt _ _ => exact HasType.litInt (m + n)
      | addReal h1 _ => cases h1
  | addReal r s =>
      intro T ht
      cases ht with
      | addInt h1 _ => cases h1
      | addReal _ _ => exact HasType.litReal (r + s)
  | cmpInt m n =>
      intro T ht
      cases ht with
      | cmp _ _ => exact HasType.litBool (decide (m = n))
  | addL hs1 ih =>
      intro T ht
      cases ht with
      | addInt h1 h2 => exact HasType.addInt (ih h1) h2
      | addReal h1 h2 => exact HasType.addReal (ih h1) h2
  | addR hs2 ih =>
      intro T ht
      cases ht with
      | addInt h1 h2 => exact HasType.addInt h1 (ih h2)
      | addReal h1 h2 => exact HasType.addReal h1 (ih h2)
  | cmpL hs1 ih =>
      intro T ht
      cases ht with
      | cmp h1 h2 => exact HasType.cmp (ih h1) h2
  | cmpR hs2 ih =>
      intro T ht
      cases ht with
      | cmp h1 h2 => exact HasType.cmp h1 (ih h2)

/-- **保持（多步版）**：任意有限步序列保持定型。 -/
theorem preservation_multistep {e e' : TypedExpr} (h : MultiStep e e') :
    ∀ {T : Ty}, HasType e T → HasType e' T := by
  induction h with
  | refl => intro T ht; exact ht
  | step hs _ ih => intro T ht; exact ih (preservation hs ht)

/-! ## 七、健全性（soundness）与命名特化 -/

/-- **类型健全性**：progress 与 preservation 的合取推论 ——
良类型项要么已是值、要么能继续走一步，并且走出的任何一步都保持同一类型。
即「well-typed programs don't go wrong」在本语言中的完整表述。 -/
theorem type_soundness {e : TypedExpr} {T : Ty} (ht : HasType e T) :
    (Value e ∨ ∃ e', Step e e') ∧ (∀ e'' : TypedExpr, Step e e'' → HasType e'' T) :=
  ⟨progress ht, fun _ hs => preservation hs ht⟩

/-- **加法专用保持**（命名特化）：两个整数操作数之和的表达式走一步后仍是整数型。 -/
theorem type_preservation_add {e₁ e₂ e' : TypedExpr} (h1 : HasType e₁ .int) (h2 : HasType e₂ .int)
    (hs : Step (.add e₁ e₂) e') : HasType e' .int :=
  preservation hs (HasType.addInt h1 h2)

/-- **良类型字面量不卡死**（命名特化）：值没有出边（`Step` 的源形如 `add`/`cmp`，
字面量不是源）。 -/
theorem no_stuck_well_typed_literals {e : TypedExpr} {T : Ty} (ht : HasType e T) (hv : Value e) :
    ¬ ∃ e', Step e e' := by
  rintro ⟨e', hs⟩
  cases hv with
  | litInt n => cases hs
  | litReal r => cases hs
  | litBool b => cases hs

end Lattice.Lib.Compiler.RealTypeSoundness