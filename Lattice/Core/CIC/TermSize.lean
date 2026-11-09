import Mathlib
import Lattice.Core.CIC.Reduction
import Lattice.Core.CIC.Normalization

/-!
# 项大小度量与「步进使大小严格递减」的必要条件（阶段 5，`normal_form` 存在性）

## 要证什么

**`Normalization.lean` 已有归约步数层（`ReducesWithin`），但没有**正规形存在性**。
后者等价于强规范化，而强规范化需要一条**在每个 `Step` 上严格递减的度量**。**

**本轮先把这条度量建立起来，并检查它对哪些构造子严格递减 ——
因为**不会对全部构造子递减**，这一点必须在动笔前就知道。**

## 度量

```
size (sort k l)      = 1
size (const k)       = 1
size (var n)         = 1
size (app f a)       = size f + size a + 1
size (lam A b)       = size A + size b + 1
size (pi A B)        = size A + size B + 1
size (letE A t b)    = size A + size t + size b + 1
```

**=> 这是标准的语法大小。`appL`/`appR`/`lamBody`/`piDom`/`piCod`/`letVal`/`letBody`
七个构造子都在**真子项**上归约，因此 `size` 严格递减 —— 这部分可以直接证出来。**

## 已知不会递减的那个构造子

**`beta`：`app (lam A b) a → subst 0 a b`。**

**`size (app (lam A b) a) = size A + size b + size a + 2`，而 `size (subst 0 a b)`
**没有上界** —— 如果 `b` 里 `var 0` 出现多次，`a` 就被复制多次。
**=> `size` 对 `beta` **不**递减，这是替换型系统的标准现象，也是「强规范化不能靠语法大小证明」的原因。**

**同理 `delta`：`const k → E k`，body 可以任意大。
`zeta`：`letE A t b → subst 0 t b`，与 `beta` 同构。** -/

namespace Lattice.Core.CIC

/-- **项的语法大小。**

**=> 标准定义：每个构造子计 `1`，`app`/`lam`/`pi`/`letE` 的子项大小相加。** -/
def size : Term → ℕ
  | .sort _ _ => 1
  | .var _ => 1
  | .const _ => 1
  | .app f a => size f + size a + 1
  | .lam A b => size A + size b + 1
  | .pi A B => size A + size B + 1
  | .letE A t b => size A + size t + size b + 1

@[simp] theorem size_sort (k : SortKind) (l : Level) : size (.sort k l) = 1 := rfl
@[simp] theorem size_var (n : ℕ) : size (.var n) = 1 := rfl
@[simp] theorem size_const (k : ℕ) : size (.const k) = 1 := rfl
@[simp] theorem size_app (f a : Term) : size (.app f a) = size f + size a + 1 := rfl
@[simp] theorem size_lam (A b : Term) : size (.lam A b) = size A + size b + 1 := rfl
@[simp] theorem size_pi (A B : Term) : size (.pi A B) = size A + size B + 1 := rfl
@[simp] theorem size_letE (A t b : Term) : size (.letE A t b) = size A + size t + size b + 1 := rfl

/-- **大小为正。** -/
theorem size_pos (t : Term) : 0 < size t := by
  cases t <;> simp only [size] <;> omega

/-- **`appL` 使大小严格递减。**

**=> 左子项是真子项，所以 `size f' < size f` 直接蕴含 `size (app f' a) < size (app f a)`。** -/
theorem size_step_appL {E : DefEnv} {f f' a : Term} (h : Step E f f')
    (ih : size f' < size f) : size (.app f' a) < size (.app f a) := by
  simp only [size]
  omega

/-- **`appR` 使大小严格递减。** -/
theorem size_step_appR {E : DefEnv} {f a a' : Term} (h : Step E a a')
    (ih : size a' < size a) : size (.app f a') < size (.app f a) := by
  simp only [size]
  omega

/-- **`lamBody` 使大小严格递减。** -/
theorem size_step_lamBody {E : DefEnv} {A b b' : Term} (h : Step E b b')
    (ih : size b' < size b) : size (.lam A b') < size (.lam A b) := by
  simp only [size]
  omega

/-- **`piDom` 使大小严格递减。** -/
theorem size_step_piDom {E : DefEnv} {A A' B : Term} (h : Step E A A')
    (ih : size A' < size A) : size (.pi A' B) < size (.pi A B) := by
  simp only [size]
  omega

/-- **`piCod` 使大小严格递减。** -/
theorem size_step_piCod {E : DefEnv} {A B B' : Term} (h : Step E B B')
    (ih : size B' < size B) : size (.pi A B') < size (.pi A B) := by
  simp only [size]
  omega

/-- **`letVal` 使大小严格递减。** -/
theorem size_step_letVal {E : DefEnv} {A t t' b : Term} (h : Step E t t')
    (ih : size t' < size t) : size (.letE A t' b) < size (.letE A t b) := by
  simp only [size]
  omega

/-- **`letBody` 使大小严格递减。** -/
theorem size_step_letBody {E : DefEnv} {A t b b' : Term} (h : Step E b b')
    (ih : size b' < size b) : size (.letE A t b') < size (.letE A t b) := by
  simp only [size]
  omega

/-! ## 反例：`beta` 让大小**增大** -/

/-- **`beta` 的具体见证：最小的一步让项变大。**

**取 `A0 = sort prop zero`（大小 1）、`a = lam A0 A0`（大小 3）、
`b = app (app (app (var 0) (var 0)) (var 0)) (var 0)`（大小 7）。**

**则 `size (app (lam A0 b) a) = 13`，而 `subst 0 a b = app (app (app a a) a) a`
的大小是 **15**。**

**=> 一步 `beta` 使识别的大小从 13 升到 15。
**这就是「强规范化不能靠语法大小证明」的原因：
`subst` 会复制 `a`，复制次数由 `b` 里 `var 0` 的出现次数决定，
而那个次数没有上界。** -/
theorem size_beta_grows :
    size (Term.app
        (Term.lam (Term.sort SortKind.prop Level.zero)
          (Term.app (Term.app (Term.app (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 0)))
        (Term.lam (Term.sort SortKind.prop Level.zero) (Term.sort SortKind.prop Level.zero)))
      < size (Term.app
          (Term.app
            (Term.app
              (Term.lam (Term.sort SortKind.prop Level.zero) (Term.sort SortKind.prop Level.zero))
              (Term.lam (Term.sort SortKind.prop Level.zero) (Term.sort SortKind.prop Level.zero)))
            (Term.lam (Term.sort SortKind.prop Level.zero) (Term.sort SortKind.prop Level.zero)))
          (Term.lam (Term.sort SortKind.prop Level.zero) (Term.sort SortKind.prop Level.zero))) := by
  decide

end Lattice.Core.CIC
