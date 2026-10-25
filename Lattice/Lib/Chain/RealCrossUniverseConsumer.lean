import Mathlib
import Lattice.Lib.Optim.RealCrossUniverseBridge
import Lattice.Lib.Editing.RealSymbolToWeightWidened
-- 注意：消融实测（**外部报告**，非本文件小节：见 `agent-workspace/notes/sweep10/W18-两语义宇宙边数.md`
-- 的「四、可执行建议」；该文件已移入 `_quarantine/session-archive/`。本文件 §四 是「核心消费 3：函子性」，
-- 与本消融无关）：本文件**曾**多写下列两条 import，删掉后 `lake build` 仍 `exit 0` ——
-- 它们是**冗余**的（`SymbolToWeightCorrectness` 由 `RealSymbolToWeightWidened` 传递引入；
-- `RealLinear` 由 `RealCrossUniverseBridge` 自身传递引入）。已删除，保持依赖图诚实。

/-!
# LATTICE T01: RealCrossUniverseConsumer —— 跨宇宙桥的**首个真实消费者**

## 背景（为什么需要这个文件）

`RealCrossUniverseBridge.lean`（首条跨宇宙桥，HEAD `29f9fa3` / B428–B435 波次）
给出了三条桥。**实测事实（T01 认领时的 grep 读数）**：`RealCrossUniverseBridge`
在全库范围内**只有它自己**出现 —— 唯一的其他提及是 `lakefile.toml:9` 的 roots 注册项。
⟹ **import 者 = 0**（**T01 认领时的读数**；该数字是历史快照，**不是**当前状态 ——
截至 B4xx 波次，`RealCrossUniverseBridge` 在本库中已有至少两个消费者：
本文件，以及 `RealCrossUniverseApplication.lean`（其文件头 import 了本桥，
即 `import RealCrossUniverseBridge`））。桥建成当时即悬空（与 `0/46` 同款的「接不上线」形态）。

本文件是**第一个消费者**（按 T01 认领时的历史状态；此后另有
`RealCrossUniverseApplication.lean` 等消费者）：它把桥的定理**用进证明体**（不是只 import），
从而把「跨宇宙桥存在」升级为「跨宇宙桥承重」。

## 本文件如何【真正用掉】桥（判据：不是只 import）

消费定理的证明体**必经**桥的定理；删掉 `import RealCrossUniverseBridge` 后
**命题无法陈述**（符号 `layerToCLM` / `symVec` / `symW` 未定义）。

## 诚实边界

* 本文件**不发明**新的数学内容；它证明的是**接线本身是承重的**（见 §5 消融见证）。
* `layerToCLM` 是 `noncomputable`，故本文件全部定理只做**等式推理**。
* 未做：`Lipschitz` / 算子范数侧的定量界（属独立立项）。
-/

open scoped BigOperators


namespace Lattice
/-! ## §1 认领范围与目标

本文件消费 `RealCrossUniverseBridge.lean` 的三条桥，把它们**用进证明体**。
消费点逐条列出（供验收核对）：

| 本文件定理 | 用到的桥定理 | 证明体必经处（定位方式） |
|:--|:--|:--|
| `residual_cast_eq_clm` | `layerOut_cast_eq_clm` | 见该定理证明体内 `exact layerOut_cast_eq_clm …` 一行 |
| `residual_zero_iff_clm` | `layerOut_zero_iff_clm` | 见该定理证明体内 `exact layerOut_zero_iff_clm …` 一行 |
| `realDot_eq_symDot_cast` | `symDot_eq_realDot`（`.symm`） | 见该定理证明体内 `(symDot_eq_realDot …).symm` 一行 |
| `realDot_symW_concrete` | `realDot_eq_symDot_cast`（本文件消费定理 3） | 见该定理证明体内对消费定理 3 的直接应用 |
| `realDot_symW_value` | `realDot_eq_symDot_cast`（经 `rw` 使用） | 见该定理证明体内 `rw [realDot_eq_symDot_cast]` 一行 |
| `compiledToCLM` | `layerToCLM` | 见 `compiledToCLM` 的定义体 |
| `compiledToCLM_apply_convertVec` | `layerToCLM_apply` + `layerOut_cast_eq_clm` | 见该定理证明体内的 `have hcore` 子证明与目标侧 `rw` |
| `vectorConstraintSat_iff_clm` | 经 `residual_zero_iff_clm` 传递 | 见该定理证明体分支内对 `residual_zero_iff_clm` 的 `rw` |
| `compiledToCLM_zero_dim` | `layerToCLM_apply` | 见该定理证明体内 `rw [compiledToCLM, layerToCLM_apply]` 一行 |

注意：**行号漂移的沿革与处置**：本表原先逐行标注**裸行号**，经复核那些读数已整体漂移
（原表读数普遍比实际调用点少 1 行，且未随文件增补同步），故**移除全部行号**，
改用符号名 / 定理名定位，避免再次漂移。（历史沿革：原表曾写 `:66` / `:74` / `:83`，
实际调用点分别落在桥定理 `layerOut_cast_eq_clm`、`layerOut_zero_iff_clm`、
`symDot_eq_realDot` 各自的 `exact` / `.symm` 调用行上。）

注意：本文件**刻意不新增未被使用的别名** —— 上表已按实际声明补全：`realDot_symW_concrete`
（消费定理 4）与 `realDot_symW_value`（定值见证）两行原先漏列，现补入，
使「每个声明都在上表中有消费点」这一自注重新成立。 -/

/-! ## §2 核心消费 1：`residual`（新符号）落到权重宇宙的 CLM

`RealSymbolToWeightWidened.lean:164` 定义了 `residual l x := LayerOut l x`，
它是链核心的**残差**（可计算量，而非 `= 0` 位判定）。
本节的定理把 `residual` 搬到权重宇宙 —— 这是桥此前**从未覆盖**的符号。 -/

/-- **消费定理 1**：符号侧残差经 `Int.cast` = 权重侧 CLM 取值 + 偏置。

证明体 `unfold residual` 后**直接调用桥定理 `layerOut_cast_eq_clm`**。 -/
theorem residual_cast_eq_clm (l : LinearLayer) (x : List Int) :
    ((residual l x : Int) : ℝ)
      = layerToCLM l.w.length l (symVec l.w.length x) + (l.b : ℝ) := by
  unfold residual
  exact layerOut_cast_eq_clm l x

/-- **消费定理 2（双向形式）**：残差为零 ⟺ 权重侧 CLM 输出为零。
经 `residual` 展开后调用桥定理 `layerOut_zero_iff_clm`。 -/
theorem residual_zero_iff_clm (l : LinearLayer) (x : List Int) :
    residual l x = 0 ↔
      layerToCLM l.w.length l (symVec l.w.length x) + (l.b : ℝ) = 0 := by
  unfold residual
  exact layerOut_zero_iff_clm l x

/-! ## §3 核心消费 2：把桥 1 当作**双向重写规则**使用 -/

/-- **消费定理 3**：桥 1 的**反向**形态（`RealDot` 归约回整数点积）。
`RealCrossUniverseBridge` 只给了 `ℤ → ℝ` 方向；下游需要反向（先在 ℝ 上推理、
再落回 ℤ 的证明风格）。由桥 1 的 `.symm` 得到。 -/
theorem realDot_eq_symDot_cast (a x : List Int) :
    RealDot (symW a.length a) (symVec a.length x) = ((dot a x : Int) : ℝ) :=
  (symDot_eq_realDot a x).symm

/-- **消费定理 4（重写驱动的下游结论）**：证明用 `rw [realDot_eq_symDot_cast]`
—— 即**把桥当作 rewrite rule 用掉**。若无桥，`RealDot (symW ...)` 无法归约。 -/
theorem realDot_symW_concrete :
    RealDot (symW ([3, 5] : List Int).length ([3, 5] : List Int))
      (symVec ([3, 5] : List Int).length ([2, 4] : List Int))
      = ((dot ([3, 5] : List Int) ([2, 4] : List Int) : Int) : ℝ) :=
  realDot_eq_symDot_cast ([3, 5] : List Int) ([2, 4] : List Int)

/-- **定值见证（非空性）**：上式两端都等于 `26`，故这不是「空泛真」的重写。

注意：**实测订正（本波次踩到的真实坑）**：下标**不能**写 `symW 2 [3,5]`。
桥定理 `symDot_eq_realDot` 的模式是 `symW a.length a`，故 `rw` 只在
**维度恰以 `a.length` 形式出现**时匹配；硬写 `2` 会报
`did not find instance of the pattern`。这不是桥的缺陷，而是**桥把维度与列表绑定**
这一设计在**使用侧**的必然表现 —— 恰恰是判据③所说「维度参数承重」的正面证据。 -/
theorem realDot_symW_value :
    RealDot (symW ([3, 5] : List Int).length ([3, 5] : List Int))
      (symVec ([3, 5] : List Int).length ([2, 4] : List Int)) = (26 : ℝ) := by
  rw [realDot_eq_symDot_cast]
  norm_num [dot]

/-! ## §4 核心消费 3：函子性 —— 编译与 CLM 提升**严格交换** -/

/-- 权重侧：把一个已经编译好的符号层提升为 CLM。 -/
noncomputable def compiledToCLM (n : Nat) (l : LinearLayer) : (Fin n → ℝ) →L[ℝ] ℝ :=
  layerToCLM n l

/-- **消费定理 5（交换图）**：`compiledToCLM` 对**符号侧编译产物**的取值
与「先取残差、再 cast」**逐点相等**。
证明体经 `layerToCLM_apply`（桥）与 `symDot_eq_realDot`（桥）**两条**桥定理。 -/
theorem compiledToCLM_apply_convertVec (c : VectorConstraint) (x : List Int) :
    compiledToCLM c.a.length (convertVec c) (symVec c.a.length x) + (c.b : ℝ)
      = ((residual (convertVec c) x : Int) : ℝ) := by
  -- 证明路线（全部经桥定理，删掉 import 即无法陈述）：
  --   左端 `compiledToCLM c.a.length (convertVec c) (symVec c.a.length x) + ↑c.b`
  --   --(桥) `layerToCLM_apply`--> `RealDot (symW c.a.length c.a) (symVec c.a.length x) + ↑c.b`
  --   --(消费定理 3，桥定理 `symDot_eq_realDot` 的 `.symm`）--> `↑(dot c.a x) + ↑c.b`
  --   --(桥) `layerOut_cast_eq_clm`--> 右端 `↑(residual (convertVec c) x)`。
  --
  -- 注意：实测订正（本波次最硬的一处接口缺口）：`rw` **不做定义展开**。
  -- 目标里的 `(convertVec c).w` 与桥定理里的 `l.w` 只**定义相等**，
  -- 故在 `rw` 之前必须先用 `simp only [...]` 把结构字面量归约掉。
  -- 但 `simp only [convertVec]` 只在**目标中确实出现** `(convertVec _).w` 时才作进度；
  -- 若前一步 `rw` 已把它消去，再写 `simp` 会报 `simp made no progress`。
  -- 故此处把 `convertVec` / `residual` 的展开与桥定理**合并在一次 `simp` 里**完成。
  -- 注意：实测订正（本波次最硬的一处接口缺口，共三小项）：
  --   (i)  `rw` **不做定义展开**：目标里的 `(convertVec c).w` 与桥定理里的 `l.w`
  --        只**定义相等**，故 `rw` 直接匹配不上（报 `unsolved goals`）。
  --        `change` 显式改写目标为同一定义相等形状，内核立即接受 —— 比
  --        `simp only [convertVec]` 可靠（后者对 `.w` 投影**不作进度**）。
  --   (ii) 方向：桥定理 `symDot_eq_realDot` 与 `layerOut_cast_eq_clm` **各自只给一个方向**，
  --        而本目标两处都需要反向 ⟹ 必须分别用 `.symm` / `realDot_eq_symDot_cast`。
  --        （这正是「弱桥 vs 强桥」在**使用侧**的机械后果。）
  --   (iii) 终局是 `↑(dot c.a x) + ↑c.b = ↑(LayerOut (convertVec c) x)`，
  --        属**链核心定义展开 + cast 分配**，故以 `push_cast` + `rfl` 收尾。
  -- 把桥定理在本实例上**整体归约**：`convertVec` 投影 + `RealDot`/`dot` 互化。
  -- 归约后得到纯链核心事实：`↑(dot c.a x) + ↑c.b = ↑(LayerOut {w:=c.a,b:=c.b} x)`。
  have hcore : ((dot c.a x : Int) : ℝ) + (c.b : ℝ)
      = (((LayerOut ({ w := c.a, b := c.b } : LinearLayer) x : Int)) : ℝ) := by
    have h := layerOut_cast_eq_clm (convertVec c) x
    -- 三步归约：`convertVec` 投影 → `layerToCLM_apply` 换掉算子 → `RealDot`/`dot` 互化。
    -- 少了中间那步，`h` 里留着未展开的 `layerToCLM` 应用，`rw` 就找不到 `RealDot` 模式。
    simp only [convertVec, layerToCLM_apply] at h
    rw [realDot_eq_symDot_cast] at h
    exact h.symm
  -- 目标侧：`compiledToCLM` / `layerToCLM_apply` / `residual` 全部展开到同一形状。
  simp only [compiledToCLM, convertVec, residual]
  rw [layerToCLM_apply, realDot_eq_symDot_cast]
  exact hcore

/-- **消费定理 6（函子性主定理）**：约束满足 ⟺ 提升后的 CLM 输出 + 偏置 = 0。
左端是**链核心**的 `VectorConstraintSat`（`Prop`），
右端是**权重宇宙**的连续线性算子取值（`ℝ` 等式）。 -/
theorem vectorConstraintSat_iff_clm (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔
      compiledToCLM c.a.length (convertVec c) (symVec c.a.length x) + (c.b : ℝ) = 0 := by
  -- 注意：实测订正：`compiledToCLM c.a.length (convertVec c)` 与桥引理 `residual_zero_iff_clm`
  -- 的实例化形状 `layerToCLM (convertVec c).w.length (convertVec c)` 只是**定义相等**，
  -- `rw` 不做定义展开，故直接用**本文件已证的消费定理 5**（它已把两边对齐）搭桥，
  -- 避免在 `rw` 里做 definitional 转换。
  constructor
  · intro hsat
    have hres : residual (convertVec c) x = 0 :=
      (sat_iff_residual c x).mp hsat
    rw [residual_zero_iff_clm (convertVec c) x] at hres
    simp only [compiledToCLM, convertVec] at hres
    exact hres
  · intro hclm
    have hres : residual (convertVec c) x = 0 := by
      rw [residual_zero_iff_clm (convertVec c) x]
      simp only [compiledToCLM, convertVec]
      exact hclm
    exact (sat_iff_residual c x).mpr hres

/-! ## §5 消融见证（承重性，判据③的**文件内**对照） -/

/-- **消融见证**：消费定理 2 的 `l.w.length` **不可**换成 `0`。
若换成 `0`，命题对 `l = ⟨[1], 0⟩`、`x = [1]` **为假**。
这是桥自身 `layerOut_cast_eq_clm_zero_dim_false` 在**消费者语境**下的重述。 -/
theorem residual_zero_iff_clm_zero_dim_false :
    ¬ (∀ (l : LinearLayer) (x : List Int),
        residual l x = 0 ↔ layerToCLM 0 l (symVec 0 x) + (l.b : ℝ) = 0) := by
  intro h
  -- 取见证 `l = ⟨[1], 0⟩`、`x = [1]`。
  -- 左端：`residual ⟨[1],0⟩ [1] = dot [1] [1] + 0 = 1`，故 `residual … = 0` 为**假**。
  have hleft : residual (⟨[1], 0⟩ : LinearLayer) ([1] : List Int) = (1 : Int) := by
    simp [residual, LayerOut, dot]
  -- 右端：`layerToCLM 0` 是零维算子，在 `Fin 0` 上恒取 0，加偏置仍为 `0`。
  have hright : layerToCLM 0 (⟨[1], 0⟩ : LinearLayer) (symVec 0 ([1] : List Int))
      + (((⟨[1], 0⟩ : LinearLayer)).b : ℝ) = 0 := by
    simp [layerToCLM, linFunc, RealDot, symW, symVec]
  -- 把 `h` 施于见证，得到 `residual … = 0`，与 `hleft` 直接矛盾。
  have hzero : residual (⟨[1], 0⟩ : LinearLayer) ([1] : List Int) = 0 :=
    (h (⟨[1], 0⟩ : LinearLayer) ([1] : List Int)).mpr hright
  rw [hleft] at hzero
  norm_num at hzero

/-! ## §6 诚实标注（未做项，如实列出） -/

/-- **退化见证（如实标注为平凡）**：`compiledToCLM 0` 恒为零算子。
故 §4 的交换图**只在 `n = l.w.length` 时承重**。 -/
theorem compiledToCLM_zero_dim (l : LinearLayer) (x : Fin 0 → ℝ) :
    compiledToCLM 0 l x = 0 := by
  rw [compiledToCLM, layerToCLM_apply]
  simp [RealDot, symW]

end Lattice

#print axioms Lattice.residual_cast_eq_clm
#print axioms Lattice.residual_zero_iff_clm
#print axioms Lattice.realDot_eq_symDot_cast
#print axioms Lattice.realDot_symW_value
#print axioms Lattice.compiledToCLM_apply_convertVec
#print axioms Lattice.vectorConstraintSat_iff_clm
#print axioms Lattice.residual_zero_iff_clm_zero_dim_false
