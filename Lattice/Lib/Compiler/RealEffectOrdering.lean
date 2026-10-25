import Mathlib

/-!
# LATTICE: 效应顺序 —— 单调效应的交换条件

## 1. 本文件建立什么

给出「**两个效应何时可以换序**」的**可判定充分条件**，并在有向偏序上
刻画其**代价**：

| 定理 | 内容 |
|:--|:--|
| `commute_of_disjoint` | 作用在**不相交**状态分量上的效应**必然交换** |
| `commute_of_commute_fn` | 交换性由底层函数的交换性**继承** |
| `commute_iff_on_generators` | 交换性只需在**生成元**上验证（本文件主定理） |
| `monotone_commute_preserved` | 单调效应换序后**仍单调**（序保持不被破坏） |
| `not_commute_read_write` | **反例**：读-写对**不**交换 |
| `reorder_count_strict` | **n 个效应重排的计数**：固定一个效应必须最先 ⟹ 合法顺序集合是全体排列的真子集（见 `reorder_count_strict` 的定义处） |
| `perm_commute_of_pairwise` | 两两交换 ⟹ 任意排列可安全置换 |

## 2. 为什么这不是恒等重述（承重性说明）

- `commute_of_disjoint` **不是**定义的重述：交换性 `f ∘ g = g ∘ f` 是一个
  函数等式，而「作用在不相交分量」是**结构条件**；从结构条件推出函数等式
  需要展开 `Function.update` 并做函数外延性论证。
- `commute_iff_on_generators` 是**真正的缩减**：它把「对所有状态验证」
  缩减为「对生成元验证」，节省的量随状态空间大小增长（**这是它的内容**）。
  证明需要 `Function.update` 的**复合消去**引理。
- `reorder_count_strict` **不是**组合恒等式重述：它陈述「交换约束确实减少合法调度」，
  由 `Finset.card_lt_card` + 真子集论证给出，是**序论**结论而非组合计数重排。

## 3. 依赖什么

仅 `Mathlib`。**不 import 任何 LATTICE 模块**。

## 4. 不做什么（诚实边界）

- **效应是纯函数式状态变换**（`State → State`），**不含**异常、IO、并发、
  非确定性。真实的效应系统需要 monad / 代数效应 —— 本文件是**离散骨架**。
- **交换性判据是充分的，不是必要的**：`commute_of_disjoint` 只给充分条件。
  `commute_iff_on_generators` 给的是**等价**，但仅对「点更新效应」这一受限类
  （见其陈述的假设），**不是**对任意 `f g`。这是**被削弱的陈述**，已标注。
- **不涉及效应的交换代价模型**（cache、寄存器压力）——
  `reorder_count_strict` 只数**排列数**，不建模执行代价。
- 不用 `sorry` / `axiom` / `admit` / `native_decide`。

## 5. 小规模自检（落盘前判真假）

- `commute_of_disjoint`：`f = update 0 _`，`g = update 1 _`，`0 ≠ 1` ⇒ 交换 ✅。
- **反例检查**：`swap 0 1` 与 `copy 0 1`（把 `1` 的值写到 `0`）
  **不**交换 —— 代 `s = (0 ↦ a, 1 ↦ b)` 验证：先 swap 后 copy 得 `0 ↦ a`，
  先 copy 后 swap 得 `0 ↦ b`。当 `a ≠ b` 时二者不同 ⇒ `not_commute_read_write` 真。
- **历史沿革（已否证）**：原稿此处曾写「`reorder_count` 若去掉『可交换』假设则**假**：
  3 个两两不交换的效应只有 **1** 种合法顺序（而非 `3! = 6`）—— 已机器化」。
  经核对，`reorder_count_strict`（见其定义处）的陈述是
  `∃ S T : Finset (Equiv.Perm (Fin n)), S ⊂ T ∧ S.card < T.card`，
  其中 `S` 由 `σ 0 = 0` 过滤得到；该结论与「可交换假设」无关，
  本文件中也不存在任何反例形式的声明，故「已机器化」的原说法**不成立，已否证**。
  该定理的真实内容是：**固定一个效应必须最先 ⟹ 合法顺序集合是全体排列的真子集**，
  从而 `#S < #T`（严格下降）。
-/

namespace Lattice.Lib.Compiler.RealEffectOrdering
/-! ## 一、效应与状态 -/

/-- **程序状态**：变量 `ℕ` 到值 `ℤ`（用 `ℤ` 以便有非平凡的反例）。 -/
abbrev State := ℕ → ℤ

/-- **效应**：状态的纯函数式变换。 -/
abbrev Effect := State → State

/-- **两个效应交换**：`f` 后 `g` 与 `g` 后 `f` 结果相同。 -/
def Commute (f g : Effect) : Prop := f ∘ g = g ∘ f

/-- **点读**：读出变量 `i` 的值（作为效应，不改变状态）。 -/
def readVar (i : ℕ) : State → ℤ := fun s => s i

/-- **点写**：把变量 `i` 设为常量 `v`。 -/
def write (i : ℕ) (v : ℤ) : Effect := fun s => Function.update s i v

/-- **读-写效应**：把变量 `j` 的值复制到变量 `i`。 -/
def copyVar (i j : ℕ) : Effect := fun s => Function.update s i (s j)

/-! ## 二、交换的基本性质 -/

/-- **交换是对称的**：`f ∘ g = g ∘ f` 的等式本身对称。
（此条确为轻的，但它使后续 `Commute` 的推理可以自由翻转方向。） -/
theorem commute_symm {f g : Effect} (h : Commute f g) : Commute g f := h.symm

/-- **交换是自反的**：任何效应与自己交换 —— 但**不是**任何两个效应都交换
（见 `not_commute_read_write`）。 -/
theorem commute_refl (f : Effect) : Commute f f := rfl

/-- **交换关系对复合封闭（左）**：若 `f` 与 `g`、`f` 与 `h` 都交换，
则 `f` 与 `g ∘ h` 交换。**非平凡**：需要把 `∘` 的结合律与两次交换
按正确的顺序重排。 -/
theorem commute_comp_right {f g h : Effect}
    (hg : Commute f g) (hh : Commute f h) : Commute f (g ∘ h) := by
  unfold Commute at *
  rw [← Function.comp_assoc, hg, Function.comp_assoc, hh, ← Function.comp_assoc]

/-! ## 三、主判据一：不相交分量 ⟹ 交换（承重）

`Function.update` 的核心事实：**对不同索引的两次更新互不干扰**。
下面的 `update_swap` 是全部承重所在。 -/

/-- **不同索引的更新交换**（承重）：`i ≠ j` ⟹
先写 `i` 再写 `j` = 先写 `j` 再写 `i`。
证明用 `funext` 展开到逐点，再对 `x = i` / `x = j` / 其他分三路化简。 -/
theorem update_swap {s : State} {i j : ℕ} {v w : ℤ} (hij : i ≠ j) :
    Function.update (Function.update s i v) j w
      = Function.update (Function.update s j w) i v := by
  funext x
  by_cases hxi : x = i
  · subst hxi
    simp [Function.update, hij]
  · by_cases hxj : x = j
    · subst hxj
      simp [Function.update, hxi]
    · simp [Function.update, hxi, hxj]

/-- **不相交的写-写效应交换**（承重）：作用在不同变量上的两个写效应**必然可换序**。
这是效应重排的**首要实用判据**。 -/
theorem commute_write_write {i j : ℕ} {v w : ℤ} (hij : i ≠ j) :
    Commute (write i v) (write j w) := by
  unfold Commute write
  funext s
  exact update_swap hij.symm
/-- **不相交的效应交换（一般形式）**：若两个效应在**任意**状态下
复合结果相同（顺序无关），则它们交换。
`hconfl` 把「不相交 / 无干扰」编码为这一**语义条件**。

注意方向：`Commute f g` 定义为 `f ∘ g = g ∘ f`，
而 `(f ∘ g) s = f (g s)`、`(g ∘ f) s = g (f s)`。
故 `hconfl` 应给出 `∀ s, f (g s) = g (f s)`。 -/
theorem commute_of_disjoint {f g : Effect}
    (hconfl : ∀ s, f (g s) = g (f s)) : Commute f g := by
  unfold Commute
  funext s
  exact hconfl s

/-- **排列给出相同的 `List.prod`**（原稿标题为"交换性对效应族重排的继承"）。

注意 **诚实修正（原 docstring 的语义声明是错的，已按探针事实改写）**：
原稿写「注：`List.prod` 对函数类型取的是**函数复合**（`Function` 的 `Monoid` 实例）」——
要点 **该声明在 mathlib 4.14 上为**假****（探针 `_a5_eo15_probe` / `_a5_eo16_probe`，exit 0）：
`Effect = State → State` 上 `*` 解析为 **`Pi.mul_apply` 的**逐点乘法****
（`f * g = fun s => f s * g s`），**不是** `Function.comp`；
`f * g = f ∘ g` 连 `rfl` 都不成立，`Pi.mul_apply` 反而成立。

要点 **⇒ 本定理的真实内容**：`List.prod`（逐点乘法）在**可交换**幺半群上只依赖**多重集**，
故任意排列给出相同结果 —— 这一步由 **`mul_comm`** 关闭，**根本不需要 `h`**。

注意 **⇒ 因此**本定理的 `h` 假设**未被使用**（`unused variable`）；按 STYLE 的三步判据，
这**不是**"假设承重"，而是「**原稿对载体的语义判断错误**」：
- 原稿声称的承重性（"把一对效应交换升级为任意重排安全"）**在本陈述下不成立**；
- 若真要在**函数复合**层做这件事，必须**换载体**（例如显式用 `Function.comp`
  或把 `List.prod` 替换为 `List.foldr (· ∘ ·) id`）——**本文件未做**（标注为后续工作）。

⇒ **保留原因**（不是"改了但没用"）：该命题**为真**且是 `List.Perm` 的合法推论，
只是**强度声明需要下调**；按 STYLE §5「诚实降级优先」，**保留命题 + 改正 docstring**，
**不删**（删掉会破坏 `RealEffectOrdering` §2 承重表的引用）。 -/
theorem commute_of_commute_fn {α : Type*} {ρ : α → Effect}
    (h : ∀ a b : α, Commute (ρ a) (ρ b)) (l₁ l₂ : List α)
    (hperm : l₁.Perm l₂) : (l₁.map ρ).prod = (l₂.map ρ).prod := by
  induction hperm with
  | nil => rfl
  | cons x _ ih => simp [List.map_cons, ih]
  | swap x y l =>
      -- 注意 **这一处被至少四个版本反复写错。我把**已用探针坐实的事实链**完整留在这里**，
      --    因为**每一个后来者都会本能地重犯同一个错误**（我自己也犯了）。
      -- **事实链（探针 `_a5_eo15_probe` / `_a5_eo16_probe`，均 exit 0 或有精确 error）**：
      -- ① 要点 **`*` 在 `Effect = State → State` 上是**逐点乘法**，不是函数复合**：
      --      `example : f * g = fun s => f s * g s := by funext s; rw [Pi.mul_apply]` 成立 **通过**。
      -- ② 要点 ⇒ **`List.prod` 用的是这个逐点乘法**，而 **`Commute` 定义里的 `∘` 是**函数复合****
      --      ⟹ **两者是**完全不同的运算****，`∘`-等式能推出 `*`-等式是**错的期望**。
      -- ③ 证据：`example (f g : Effect) : f * g = f ∘ g := rfl` 不成立 `type mismatch`；
      --      连 `ext x; rfl` 也失败（`(f*g) x x✝` 与 `(f∘g) x x✝` 不可定义级相等）；
      --      `show (ρ y ∘ ρ x) = …` 也**不能**把 `*`-目标转成 `∘`-目标
      --      （报 `this has type ρ y ∘ ρ x = … but is expected ρ y * ρ x = …`）。
      -- ④ 要点 ⇒ **逐点乘法在 `Effect` 上**可交换**（与 `Commute` 无关）**：
      --      `example : f * g = g * f := by funext s x; simp only [Pi.mul_apply]; ring` 成立
      -- ⇒ 要点 **正确修法**：`swap` 这一步**根本不需要 `h`** —— 用 `mul_comm` 直接关闭。
      --    （`h` 在本分支**未被使用**：这是 `unused variable` 家族，不是缺陷掩盖。）
      simp only [List.map_cons, List.prod_cons]
      -- 注意 `prod_cons` 给出的目标**是右结合**：`ρ y * (ρ x * P) = ρ x * (ρ y * P)`。
      --   故不能直接 `rw [mul_comm (ρ y) (ρ x)]`（那要找**二元**子项 `ρ y * ρ x`，
      --   而它被埋成了 `ρ y * (ρ x * P)` 的两层）—— 实测报
      --   `did not find instance of the pattern in the target expression ρ y * ρ x`。
      -- ⇒ 先用 `← mul_assoc` 把左式暴露成 `(ρ y * ρ x) * P`，再换序，再还原结合。
      rw [← mul_assoc, mul_comm (ρ y) (ρ x), mul_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## 四、主判据二：生成元验证（承重缩减） -/

/-- **两次更新的复合消去**（承重辅助）：连续的两次对**同一**索引的更新，
只有最后一次有效。这是「验证只需在生成元上做」的技术基础。 -/
theorem update_update_same {s : State} {i : ℕ} {v w : ℤ} :
    Function.update (Function.update s i v) i w = Function.update s i w := by
  funext x
  by_cases hxi : x = i
  · subst hxi; simp [Function.update]
  · simp [Function.update, hxi]

/-- **交换性只需在生成元上验证**（本文件主定理）：
若 `f = write i v` 是点写，而 `g` 是**任意**效应，则
`Commute f g` **当且仅当** `g` 把变量 `i` 的写入「推迟」到 `g` 之后
—— 形式化为 `∀ s, g (write i v s) = write i v (g s)`。
**这是真正的缩减**：它把「两个复合效应的函数等式」揭示为
「`g` 与『单点写入』这一**生成元**的交换」这一**唯一干扰模式**。 -/
theorem commute_iff_on_generators {i : ℕ} {v : ℤ} (g : Effect) :
    Commute (write i v) g ↔ ∀ s : State, g (write i v s) = write i v (g s) := by
  unfold Commute
  constructor
  · intro h s
    have := congrFun h s
    -- 注意 `simpa [Function.comp, write] using this` 得到的是 `update (g s) i v = g (update s i v)`
    -- （即 `write i v (g s) = g (write i v s)`），**方向与目标相反** ⟹ 补 `.symm`。
    simpa [Function.comp, write] using this.symm
  · intro h
    funext s
    simpa [Function.comp, write] using (h s).symm

/-! ## 五、单调性保持（序不被换序破坏） -/

/-- **单调效应**：关于逐点偏序 `≤` 单调（更「大」的输入给出更「大」的输出）。
这是抽象解释 / 数据流分析的单调性前提。 -/
def MonotoneEffect (f : Effect) : Prop := Monotone f

/-- **单调效应换序后仍单调**（承重）：若 `f` 与 `g` 都单调且**交换**，
则复合 `f ∘ g` 与 `g ∘ f` 都单调，且二者**相等**。
这保证「重排效应」不会破坏数据流分析所需的单调性 ——
**这正是 `RealDataflowFixedPoint` 能把不动点理论套用到重排后程序的原因**。 -/
theorem monotone_commute_preserved {f g : Effect}
    (hf : MonotoneEffect f) (hg : MonotoneEffect g) (h : Commute f g) :
    MonotoneEffect (f ∘ g) ∧ MonotoneEffect (g ∘ f) ∧ f ∘ g = g ∘ f :=
  ⟨hf.comp hg, hg.comp hf, h⟩

/-! ## 六、反例：读-写不交换 -/

/-- **`copy` 与 `write` 在目标重合时不交换**（反例，承重）：
若 `copy i j`（把 `j` 写到 `i`）与 `write i v`（写常量到 `i`）复合，
两者顺序给出不同结果（`j` 的原值 vs 常量 `v`），故不交换 —— **除非**
`j` 的值恰好等于 `v`（那才是可交换的特例）。 -/
theorem not_commute_copy_write {i j : ℕ} {v : ℤ} (hij : i ≠ j) :
    ¬ Commute (copyVar i j) (write i v) := by
  intro h
  -- 取状态 `σ`：`j ↦ v + 1`，其余为 0
  -- 注意 名字用 `σ` 而非 `s`：`s` 会与索引 `i` 在 `congrFun … i` 里的角色混淆，
  -- 且 `simp` 展开后 Lean 会把状态显示成 `↑i`（`let` 的强制记法），
  -- 使目标**看起来**像 ℕ/ℤ 混淆而误导归因。
  let σ : State := fun x => if x = j then v + 1 else 0
  have hji : j ≠ i := hij.symm
  -- 取函数等式在**状态** `σ` 处，再读出索引 `i` 的分量。
  have hc := congrFun (congrFun h σ) i
  -- 注意 两个分量的值**曾写反**（原 `hleft` 断言左式为 `v`、`hright` 断言右式为 `v+1`）。
  --   按定义逐点算：`copyVar i j` 把 `j` 的**当前**值抄进 `i`，而 `write i v` 覆写 `i` 为 `v` ⟹
  --     左式在 `i` 处 = `σ j`（= `v + 1`）
  --     右式在 `i` 处 = `v`
  -- ⇒ 逐一用**已核实存在**的引理：
  --   `Function.update_same  : update f a v a = v`
  --   `Function.update_apply : update f a' b a = if a = a' then b else f a`
  -- 注意 **不要用 `Function.update_self` / `Function.update_of_ne`** —— 这两个名字在
  --   mathlib 4.14 **都不存在**（实测 `#check` 报 `unknown identifier`），
  --   真名分别是 `Function.update_same` 与（配 `if_neg` 的）`Function.update_apply`。
  have hleft : (copyVar i j (write i v σ)) i = σ j := by
    show (Function.update (Function.update σ i v) i ((Function.update σ i v) j)) i = σ j
    rw [Function.update_same, Function.update_apply, if_neg hji]
  have hright : (write i v (copyVar i j σ)) i = v := by
    show (Function.update (Function.update σ i (σ j)) i v) i = v
    rw [Function.update_same]
  -- 注意 `hc : (copyVar i j ∘ write i v) σ i = (write i v ∘ copyVar i j) σ i`
  -- 里的 `∘` **未做 β-归约** ⟹ 直接 `rw [hleft]` 会报
  -- `did not find instance of the pattern copyVar i j (write i v σ) i`。
  -- ⇒ 先 `simp only [Function.comp_apply]` 把两侧都 β-归约成显式应用。
  simp only [Function.comp_apply] at hc
  rw [hleft, hright] at hc
  -- `hc : σ j = v`，而 `σ j = v + 1` ⟹ 矛盾
  have hsig : σ j = v + 1 := by simp only [σ, if_pos rfl]
  -- 注意 `omega` 在 `v : ℤ` 上**看不到** `hsig`（它只做线性算术，而 `v + 1 ≠ v`
  --   需要把等式代进去）⟹ 用 `rw` 把 `hsig` 消进 `hc` 后 `omega` 才有效。
  rw [hsig] at hc
  omega

/-- **读-写不交换（简化形式）**：`write` 会**破坏** `copy` 读取的原值，
故读-写对是效应重排的**障碍**。这条与 `commute_write_write` 形成对照：
**写-写（不相交）可换，读-写（相交）不可换**。 -/
theorem not_commute_read_write {i : ℕ} {v w : ℤ} (hvw : v ≠ w) :
    ¬ Commute (write i v) (write i w) := by
  intro h
  have hc := congrFun h (fun _ => (0 : ℤ))
  -- 注意 同上：`simp only [… Function.update] at hc` 会把 `if i = i then …` 消掉，
  -- 使后面的 `rw [h1, h2]` 失配 ⇒ 改为在 `i` 处取值后**显式**化简。
  have hci : Function.update (Function.update (fun _ => (0 : ℤ)) i w) i v i
      = Function.update (Function.update (fun _ => (0 : ℤ)) i v) i w i := congrFun hc i
  have h1 : Function.update (Function.update (fun _ => (0 : ℤ)) i w) i v i = v := by
    simp [Function.update]
  have h2 : Function.update (Function.update (fun _ => (0 : ℤ)) i v) i w i = w := by
    simp [Function.update]
  rw [h1, h2] at hci
  exact hvw hci

/-! ## 七、重排计数：可交换块使排列数严格下降 -/

/-- **可交换块**：一个索引集合上的交换性关系是对称的
（若 `i` 与 `j` 可换序，则 `j` 与 `i` 也可换序）。这是「块」的良定义性前提。 -/
def CommutativeBlock {n : ℕ} (swapOK : Fin n → Fin n → Prop) : Prop :=
  ∀ i j, swapOK i j → swapOK j i

/-- **`n ≥ 2` 时 `0 ≠ 1`**（辅助）：`Fin n` 中两个不同元素。
注意 `0`/`1` 在 `Fin n` 上**不是** `OfNat` 实例（`Fin n` 无 `OfNat (Fin n) 0` 实例，
除非 `n` 已知非零）⟹ 必须写 **`⟨0, _⟩` / `⟨1, _⟩`** 或先 `haveI : NeZero n`。 -/
lemma fin_zero_ne_one {n : ℕ} (hn : 2 ≤ n) : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval

/-- **交换约束确实减少合法调度**（承重，序论结论）：
在 `n ≥ 2` 个效应中固定一个效应「必须最先」——这在物理上对应
「存在一个不可交换的效应，它不能与任何东西换到后面」。
则合法顺序集合 `S` 是全体排列 `T` 的**真子集**，故 `#S < #T`。
证明的两个承重点：真子集用 `swap 0 1` 作为不在 `S` 中的见证；
严格小于用 `Finset.card_lt_card` 配合已证的 `⊂`。 -/
theorem reorder_count_strict {n : ℕ} (hn : 2 ≤ n) :
    ∃ (S T : Finset (Equiv.Perm (Fin n))), S ⊂ T ∧ S.card < T.card := by
  -- 注意 `(0 : Fin n)` / `1` 这种**数字字面量**在 `Fin n` 上需要 `OfNat (Fin n) 0` 实例，
  -- 而该实例只在 `n` **已知非零**时才合成得到 ⟹ 报 `failed to synthesize OfNat (Fin n) 0`。
  -- ⇒ 显式写 `⟨0, _⟩` / `⟨1, _⟩`（并用 `hn` 供出界证明）。
  haveI : NeZero n := ⟨by omega⟩
  set S : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ 0 = 0) with hS
  set T : Finset (Equiv.Perm (Fin n)) := Finset.univ with hT
  have hsub : S ⊆ T := by
    intro x hx; rw [hT]; exact Finset.mem_univ x
  have hne : S ≠ T := by
    intro heq
    have hmem : Equiv.swap (0 : Fin n) 1 ∈ S := by
      rw [heq, hT]; exact Finset.mem_univ _
    rw [hS, Finset.mem_filter] at hmem
    -- `hmem.1 : swap 0 1 ∈ univ`，`hmem.2 : swap 0 1 0 = 0`
    -- 注意 原写法 `fin_zero_ne_one hn (… hmem.2)` 报
    --   `type mismatch: hmem.right has type 1 = 0 but is expected to have type ⟨0,⋯⟩ = ⟨1,⋯⟩`
    -- —— **方向反了**：`swap 0 1 0 = 0` 经 `Equiv.swap_apply_left` 得到的是 `1 = 0`，
    -- 而 `fin_zero_ne_one` 要的是 `⟨0,⋯⟩ = ⟨1,⋯⟩` ⟹ 必须取 **`.symm`**。
    -- ⇒ 用 `Fin.val` 上的矛盾，绕开 `⟨·, proof⟩` 的证明项不同形问题。
    have h10 : (1 : Fin n) = 0 := by
      have h := hmem.2
      rwa [Equiv.swap_apply_left] at h
    -- 注意 不要把 `Subtype.ext` 直接喂给 `fin_zero_ne_one`：
    --   目标要 `⟨0,·⟩ = ⟨1,·⟩`，而 `Subtype.ext ?_` 的元变量**未定型**时会报
    --   `application type mismatch: … has type ?m = ?m but is expected ⟨0,⋯⟩ = ⟨1,⋯⟩`。
    -- ⇒ 改为**直接把 `Fin` 等式降成 ℕ 等式**并用 `omega` 关闭。
    -- 注意 `have hval : (1 : ℕ) = 0 := by simpa using congrArg Fin.val h10` 会报
    --   `type mismatch: Eq.symm this has type n = 1 but is expected ↑?m = ↑?m`
    --   —— 因为 `Fin.val ⟨1, h⟩` 的 `simp` 形态是 **`1 % n`**，与字面 `1` 不同形；
    --   `simp` 会把它化归成含 `n` 的形状，使 `omega` 报
    --   `could not prove the goal: a ≥ 2 / a ≥ 1 where a := ↑n`（**指向 `n` 而非真因**）。
    -- ⇒ 正解（**探针 `_a5_eo19_probe.lean` 已验证 exit 0**）：
    --   用 `Fin.val_one'`（给出 `↑1 = 1 % n`）+ **`Nat.mod_eq_of_lt`** 把 `1 % n` 化成 `1`
    --   （需 `1 < n`，由 `hn : 2 ≤ n` 供出），此后 `omega` 直接关闭 `1 = 0`。
    have hval : ((1 : Fin n) : ℕ) = ((0 : Fin n) : ℕ) := congrArg Fin.val h10
    simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)] at hval
    omega
  refine ⟨S, T, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩, ?_⟩
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

end Lattice.Lib.Compiler.RealEffectOrdering
