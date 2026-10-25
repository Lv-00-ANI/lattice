import Mathlib


/-!
# LATTICE: 向量约束 → 线性层权重矩阵（保语义证明）

从 ConvertLinear.lean（标量线性约束）推广到向量：
符号侧一个向量约束（系数向量 a + 常数 b）转换为权重侧一个线性层
（权重向量 w + 偏置 b'），转换保持语义。

对应 doc/02 §4.3：朝 `SymbolToWeightCorrectness` 推进的一步。
向量用 List Int 表达，点积用 foldl。

⚠ **订正 B400**：此处原写「纯 Std（无 mathlib）」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**向量的表示与点积确实只用 `List Int` + `foldl`**（不依赖 mathlib 的向量/矩阵类型），
但**文件整体 import 了 Mathlib**。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。**以本段为准。**

另证明**权重缩放不变性**（scale_preserves）：
约束系数整体缩放 lam ≠ 0 不改变满足语义——这是 doc/01 中
「同一函数有无数权重实现（缩放等价）」规范形式选择难点的最小证明：
缩放自由度不影响约束语义，验证器可忽略它。
-/

namespace Lattice

/-! ## 符号侧：向量线性约束及其满足语义 -/

structure VectorConstraint where
  a : List Int      -- 系数向量
  b : Int           -- 常数项
deriving Repr

/-! 点积（List 版）：Σ a[i]*x[i] -/

def dot (a x : List Int) : Int :=
  (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0

def VectorConstraintSat (c : VectorConstraint) (x : List Int) : Prop :=
  dot c.a x + c.b = 0

/-! ## ⭐⭐ 下标化载体（EXEC-R1 的**最小侵入**修补）

`dot` 用 `List.zip`，而 `zip` **静默截断到较短表** ⟹ `VectorConstraintSat` 把
`[3,5] = 0` 这类双变量约束在**零变量输入** `x = []` 上报告为**满足**
（`RealSymbolToWeightWidened.sat_ragged_false_positive`，机器验证）。

⭐⭐ **本节的修补不走「加长度前提」也不走「改 `dot`」**，理由是二者都会改动
**1 个承重常量**（`dot` / `VectorConstraintSat`）并连带**109 个 in-degree 使用点**
的语义（详见 `_quarantine/CONSOLIDATED-DEFECTS.md` §4.4 的量化论证）。

本节的载体**把长度编码进类型**：`VecConstraint n` 的系数是 `Fin n → Int`，
于是「变量个数」`n` 是**位置**而不是**副作用**：截断**无法发生**
（`Finset.univ` 就是全部 `n` 个下标），而「输入长度不足」在类型层**不可表达**。

⚠ **诚实边界**：本节**不改动**上面任何既有声明；`VectorConstraint`（`List Int`）与其
截断语义**原样保留**（下游 109 个使用点因此**逐字不动**）。
本节是**并列新增**，不是**替换**。 -/

/-- **下标化向量约束**：`n` 个变量，系数 `a : Fin n → Int`，常数项 `b : Int`。

⚠ 与 `VectorConstraint` 的差别**只有载体**（`Fin n → Int` vs `List Int`）——
这使得「约束有几个变量」成为**类型的一部分**。 -/
structure VecConstraint (n : Nat) where
  a : Fin n → Int      -- 系数向量（下标化，长度由类型承载）
  b : Int              -- 常数项

/-- **下标化点积**：`∑ᵢ aᵢ·xᵢ`。⭐ **无截断** —— `Finset.univ` 恰好遍历 `Fin n` 的全部元素。

⚠ 与 `dot` 的关系由 `vecDot_eq_dot_lists` 给出：对**任意**长度 ≥ 1 的列表
（`l.get 0` 需非空），把 `l` 与系数列表**逐下标对齐**后取 `Fin l.length` 的前缀，
两者相等。 -/
def vecDot {n : Nat} (a : Fin n → Int) (x : Fin n → Int) : Int :=
  ∑ i : Fin n, a i * x i

/-- ⭐ **下标化满足语义（无截断版）**：约束满足 ⟺ 残差为零。

⚠ **与 `VectorConstraintSat` 的关系**：后者在长度不足时**静默截断**并可能返回真；
本谓词**不存在**长度不足的情形（`x` 是 `Fin n → Int`），故
`vecSat` **没有** `sat_ragged_false_positive` 这类假阳性 —— 这不是「补了长度条件」，
而是**该故障模式在此载体上不可表达**。 -/
def vecSat {n : Nat} (c : VecConstraint n) (x : Fin n → Int) : Prop :=
  vecDot c.a x + c.b = 0

/-- **把列表按给定长度补零抬到 `Fin n → Int`**（与 `RealListFinBridge.toVec` 同构造，
此处就地重证以保持本文件**零新增 import**）。 -/
def toFinVec (n : Nat) (x : List Int) : Fin n → Int := fun i => x.getD i.1 0

/-- **列表点积 = 下标化点积**（对齐到**左参数**的长度）：

    `dot a x = vecDot (toFinVec a.length a) (toFinVec a.length x)`。

⭐ 这条把「`List` 截断点积」与「`Fin` 无截断点积」**钉在同一个等式上**；
它对本仓 `dot` 的**任何**输入都成立（**无需**长度条件，因为右端已按 `a.length` 对齐）。
⚠ 证明**不**依赖 `RealListFinBridge`（本文件保持 `import Mathlib` 不变）。 -/
theorem vecDot_toFinVec_eq_dot (a x : List Int) :
    vecDot (toFinVec a.length a) (toFinVec a.length x) = dot a x := by
  induction a generalizing x with
  | nil => simp [vecDot, toFinVec, dot]
  | cons y ys ih =>
      cases x with
      | nil => simp [vecDot, toFinVec, dot]
      | cons z zs =>
          show (∑ i : Fin (ys.length + 1),
                  toFinVec (ys.length + 1) (y :: ys) i
                    * toFinVec (ys.length + 1) (z :: zs) i)
                = dot (y :: ys) (z :: zs)
          rw [Fin.sum_univ_succ]
          simp only [toFinVec, List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero,
                     Fin.val_succ, List.zip_cons_cons, List.foldl_cons, List.foldl_nil]
          have hih : (∑ x : Fin ys.length, ys.getD (↑x) 0 * zs.getD (↑x) 0) = dot ys zs := by
            simpa only [vecDot, toFinVec] using ih zs
          rw [hih]
          -- ⭐ `dot` 的 `foldl` 把累加器放在最前，而 `Fin.sum` 展开后是「头 + 尾和」。
          -- 需证「累加器平移」：`foldl f c l = c + foldl f 0 l`。
          -- ⭐ 归纳步必须把 IH 用于【两个】累加器值 `c+u` 与 `0+u`，否则 `simp` 展开
          --    `foldl` 后累加器变成 `0+u`，IH（只对 `0` 说事）就接不上。
          have hshift : ∀ (l : List (ℤ × ℤ)) (c : ℤ),
              List.foldl (fun acc uv => acc + uv.1 * uv.2) c l
                = c + List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 l := by
            intro l
            induction l with
            | nil => intro c; simp
            | cons uv rest ih2 =>
                intro c
                simp only [List.foldl_cons, List.foldl_nil]
                rw [ih2 (c + uv.1 * uv.2)]
                rw [ih2 (0 + uv.1 * uv.2)]
                ring
          simp only [dot, List.zip_cons_cons, List.foldl_cons, List.foldl_nil]
          -- ⭐ 目标左边是 `y*z + foldl f 0 L`，正是 `hshift L (y*z)` 的【右边】
          --    ⟹ 反向改写，再用 `zero_add` 消去右边的 `0 +`。
          rw [← hshift (ys.zip zs) (y * z)]
          simp only [zero_add]
/-! ## 权重侧：线性层（权重向量 + 偏置，输出为加权和） -/

structure LinearLayer where
  w : List Int      -- 权重向量
  b : Int           -- 偏置
deriving Repr

def LayerOut (l : LinearLayer) (x : List Int) : Int :=
  dot l.w x + l.b

/-! ## 转换：约束系数直接拷贝为层权重 -/

def convertVec (c : VectorConstraint) : LinearLayer :=
  { w := c.a, b := c.b }

/-! ## 定理一：转换保语义
约束满足 ⟺ 线性层输出为零。-/

theorem convertVec_preserves_semantics (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0 := by
  simp [VectorConstraintSat, LayerOut, convertVec, dot]

/-! ## 定理二：转换不改变解集 -/

theorem convertVec_preserves_solution_set (c : VectorConstraint) :
    {x : List Int | VectorConstraintSat c x} =
    {x : List Int | LayerOut (convertVec c) x = 0} := by
  ext x
  exact convertVec_preserves_semantics c x

/-! ## 缩放：把约束整体乘以 lam（对应权重初始化自由度） -/

def scaleVec (c : VectorConstraint) (lam : Int) : VectorConstraint :=
  { a := c.a.map (fun v => v * lam), b := c.b * lam }

/-! 引理：foldl 的初值可以提到外面（对线性累加函数） -/

lemma foldl_init_add (rest : List (Int × Int)) :
    ∀ (init : Int),
      List.foldl (fun acc uv => acc + uv.1 * uv.2) init rest =
        init + List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 rest := by
  induction rest with
  | nil => intro init; simp
  | cons p ps ih =>
      intro init
      simp [List.foldl] at ih ⊢
      rw [ih (init + p.1 * p.2), ih (p.1 * p.2)]
      ring

/-! 引理：点积对左参数逐项缩放保持线性：dot (a·lam) x = (dot a x) · lam -/

lemma dot_map_mul (a x : List Int) (lam : Int) :
    dot (a.map (fun v => v * lam)) x = (dot a x) * lam := by
  induction a generalizing x with
  | nil => simp [dot]
  | cons h t ih =>
      cases x with
      | nil => simp [dot]
      | cons y ys =>
          simp [dot] at ih ⊢
          rw [foldl_init_add ((List.map (fun v => v * lam) t).zip ys) (h * lam * y)]
          rw [ih ys]
          rw [foldl_init_add (t.zip ys) (h * y)]
          ring

/-! ## 定理三：权重缩放不改变约束语义
约束系数整体缩放 lam ≠ 0，满足集不变（0 缩放还是 0，非零缩放不引入新解）。-/

theorem scaleVec_preserves (c : VectorConstraint) (x : List Int) (lam : Int) (hlam : lam ≠ 0) :
    VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c lam) x := by
  unfold VectorConstraintSat scaleVec
  change dot c.a x + c.b = 0 ↔ dot (c.a.map (fun v => v * lam)) x + c.b * lam = 0
  rw [dot_map_mul c.a x lam]
  constructor
  · intro h
    have hmul : (dot c.a x) * lam + c.b * lam = 0 := by
      calc
        (dot c.a x) * lam + c.b * lam = (dot c.a x + c.b) * lam := by ring
        _ = 0 * lam := by rw [h]
        _ = 0 := by simp
    exact hmul
  · intro h
    -- 从 (dot c.a x)·lam + c.b·lam = 0 且 lam ≠ 0 推 dot c.a x + c.b = 0
    have hd : (dot c.a x + c.b) * lam = 0 := by
      calc
        (dot c.a x + c.b) * lam = (dot c.a x) * lam + c.b * lam := by ring
        _ = 0 := h
    -- (dot c.a x + c.b) * lam = 0 且 lam ≠ 0 ⟹ dot c.a x + c.b = 0（整数消去）
    exact mul_eq_zero.mp hd |>.resolve_right hlam

/-! ## ⭐⭐ 下标化载体的满足语义：与截断语义的**精确**关系（EXEC-R1）

本节把 §「下标化载体」的 `vecSat` 与本文件既有 `VectorConstraintSat` **钉在一起**，
给出三件事：

1. `VecConstraint.sat_iff` —— 下标化满足 ⟺ 残差为零（`Iff.rfl` 级，供下游重写）；
2. ⭐ `VecConstraint.sat_of_list_sat` —— **截断语义的满足蕴含下标化语义的满足**，
   当系数向量**恰好**长 `n`（即 `List` 侧无尾系数被吞）：
   这是「下标化载体严格更细」的**单向**证据；
3. ⭐⭐ `VecConstraint.list_sat_of_sat_of_length` —— **反向蕴含在长度对齐下成立**，
   配合上一条给出**双向**等价（`VecConstraint.sat_iff_list_sat`）。

⭐ **关键**：第 3 条的假设 `x.length = n` 在**下标化侧是自动的**（`x : Fin n → Int`），
而在 `List` 侧必须**显式写出来** —— 这正是「把长度编码进类型」的收益。 -/

namespace VecConstraint

variable {n : Nat}

/-- **下标化满足语义的展开**：与 `vecDot` + `vecSat` 的定义逐字一致。 -/
theorem sat_iff (c : VecConstraint n) (x : Fin n → Int) :
    vecSat c x ↔ vecDot c.a x + c.b = 0 := Iff.rfl


/-- ⭐ **截断语义 ⟹ 下标化语义**（系数向量恰长 `n`、输入恰长 `n`）。

⚠ **这条不是「加长度前提」** —— 前提 `x.length = n` 在下标化侧**由类型给出**，
此处只是把 `List` 输入与 `Fin n → Int` 输入**对齐**。 -/
theorem sat_of_list_sat {a : List Int} (ha : a.length = n) {b : Int} {x : List Int}
    (hx : x.length = n)
    (h : VectorConstraintSat ({ a := a, b := b } : VectorConstraint) x) :
    vecSat ({ a := toFinVec n a, b := b } : VecConstraint n) (toFinVec n x) := by
  subst ha
  unfold VectorConstraintSat at h
  unfold vecSat
  rw [vecDot_toFinVec_eq_dot a x]
  exact h

/-- ⭐⭐ **下标化语义 ⟹ 截断语义**（同样在长度对齐下）。

⭐ 与上一条合起来即**双向等价**；证明只用 `vecDot_toFinVec_eq_dot`。 -/
theorem list_sat_of_sat_of_length {a : List Int} (ha : a.length = n) {b : Int} {x : List Int}
    (hx : x.length = n)
    (h : vecSat ({ a := toFinVec n a, b := b } : VecConstraint n) (toFinVec n x)) :
    VectorConstraintSat ({ a := a, b := b } : VectorConstraint) x := by
  subst ha
  unfold vecSat at h
  unfold VectorConstraintSat
  rw [vecDot_toFinVec_eq_dot a x] at h
  exact h

/-- ⭐⭐ **双向等价（长度对齐下的完整性）**：
`List` 侧（截断）与下标化侧（无截断）的满足语义**逐字一致**。

⚠ **诚实标注**：本条**不是**「截断无害」的证据 —— 它只在 `x.length = n` **时**成立；
`x` 更短时左端可为真而右端**不可表达**，这正是缺陷所在（见
`RealSymbolToWeightWidened.sat_ragged_false_positive`）。 -/
theorem sat_iff_list_sat {a : List Int} (ha : a.length = n) {b : Int} {x : List Int}
    (hx : x.length = n) :
    vecSat ({ a := toFinVec n a, b := b } : VecConstraint n) (toFinVec n x) ↔
      VectorConstraintSat ({ a := a, b := b } : VectorConstraint) x :=
  ⟨list_sat_of_sat_of_length ha hx, sat_of_list_sat ha hx⟩

end VecConstraint

end Lattice
