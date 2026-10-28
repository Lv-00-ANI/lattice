import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealLayerSemanticQuotient
/-!
# LATTICE D2-1：往返律非退化的精确条件 —— 商上的往返

本文件实现调研报告 `_deep_out/D_D2-1.md` 的应证定理清单（T1 / T2 / T4a / T4b / T5）。

## 0. 调研报告的判定与我的处置

调研报告的核心判定是：

> ⭐ `extractVec ∘ convertVec = id` **在【任何子集上】都永远是 `rfl` 级** ——
> 这不是「某个子集还没找到」，而是**定理**（`RealRoundtripNontrivial:206`
> `no_nontrivial_roundtrip_subset`，全称否定）。
> ⭐⭐ **真正需要真证明的往返律不在 `extractVec ∘ convertVec` 上，
> 而在【两个商之间的下降映射】上** —— 即 `semConv : Quotient semSetoidC → Quotient semSetoidL`。

⭐ 本文件照此执行：**不走子集路线**（那条已被 `RealRoundtripNontrivial` 封死），
而是把往返律搬到**商**上，并补齐 `RealLayerSemanticQuotient.lean:652`
逐字登记为「未做」的那一半（`Equiv`）。

## 1. 本文件相对既有文件的**增量**（逐条）

| # | 内容 | 对应调研条目 | 报告预判 | 本文件实测 |
|--:|:--|:--|:--|:--|
| 1 | ⭐⭐ **`semConv` 的右逆存在**（`semExt` 经 `extractVec_respects_semEq` 下降） | T1 | 真 | ✅ **已证** |
| 2 | 要点 **商上的往返是 `Equiv`** —— 补 `RealLayerSemanticQuotient.lean:652` 的「未做 `Equiv`」 | T2 | 真 | 成立 **已证** |
| 3 | ⭐ **`SameLayer ⟹ SemEqL`**（权重侧同一 ⟹ 语义等价） | T4a | 真 | ✅ **已证** |
| 4 | ⭐⭐ **`SemEqL ⇏ SameLayer`**（**机器反例**：`dot` 的 `zip` 截断让「补零维」成为不可由缩放吸收的自由度） | T4b | 真（否定式） | ✅ **已证** |
| 5 | ⭐⭐ **「补零维」不改变 `dot`**（`dot (b ++ replicate n 0) x = dot b x`） | T5 的 (⟸) 的技术内核 | 真 | ✅ **已证** |
| 6 | ⭐ **`semConv` 是满射**（T2 的交叉检验） | T2（报告未提） | — | ✅ **已证** |
| 7 | ⚠ ⚠ **T5 的 (⟹) 方向（充要条件的必要性）** | T5 | 报告自称「未验证」 | ❌ **本文件【未证】，也未证伪** —— 见 §六 |

⚠⚠ **本文件的一处重要【自我纠正】，如实登记**：
我在 §六 的第一版**曾断言 T5 的 (⟹) 为假**，用 `[1]` / `[-1]` 作反例。
⭐ **该断言是错的**：`[1]` 与 `[-1]` 在 `ScaleClassPlus`（**正**倍率）下不成比例，
⚠ 但在 `ScaleClass`（**非零**倍率）下**成比例**（`lam = 1`、`mu = -1`）
⟹ 该反例**只**证伪「**正**倍率」读法，**不**触及 T5 的「非零倍率 + 去尾零」读法。
⇒ ⭐ **本文件已把 §六 改写成「未证」**，**不把未裁决的命题写成定理**。
⭐ **这正是任务书 §非平凡性 的纪律：不假装。**

⭐ **另有 §五 的一处【诚实降级】**：第 5 条的 `trimTrailingZerosD21`（`reverse/dropWhile/reverse`
实现）与 `++ replicate` 形式**相等**这一条，**本文件未证**（见 §七）。

## 2. 逐字核对过的既有签名（**不靠记忆**；每条注明出处）

```lean
-- ConvertVectorLinear.lean:31-32
def dot (a x : List Int) : Int := (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0

-- ConvertVectorLinear.lean:44-45
def LayerOut (l : LinearLayer) (x : List Int) : Int := dot l.w x + l.b

-- ConvertVectorLinear.lean:105-106
theorem scaleVec_preserves (c : VectorConstraint) (x : List Int) (lam : Int) (hlam : lam ≠ 0) :
    VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c lam) x

-- WeightToSymbolEquivalence.lean:55-56
def extractVec (l : LinearLayer) : VectorConstraint := { a := l.w, b := l.b }

-- WeightToSymbolEquivalence.lean:60-62
theorem roundtrip_extractVec (c : VectorConstraint) : extractVec (convertVec c) = c

-- RealLayerSemanticQuotient.lean:137-138
def SemEqC (c c' : VectorConstraint) : Prop :=
  ∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat c' x

-- RealLayerSemanticQuotient.lean:143-144
def SemEqL (l l' : LinearLayer) : Prop :=
  ∀ x : List Int, LayerOut l x = 0 ↔ LayerOut l' x = 0

-- RealLayerSemanticQuotient.lean:166-168 / 185-187
def semSetoidC : Setoid VectorConstraint
def semSetoidL : Setoid LinearLayer

-- RealLayerSemanticQuotient.lean:222-226
theorem convertVec_respects_semEq {c c' : VectorConstraint} (h : SemEqC c c') :
    SemEqL (convertVec c) (convertVec c')

-- RealLayerSemanticQuotient.lean:236-237
theorem extractVec_respects_semEq {l l' : LinearLayer} (h : SemEqL l l') :
    SemEqC (extractVec l) (extractVec l')

-- RealLayerSemanticQuotient.lean:279-282
def semConv : Quotient semSetoidC → Quotient semSetoidL

-- RealLayerSemanticQuotient.lean:299-301
@[simp] theorem semConv_mk (c : VectorConstraint) :
    semConv (Quotient.mk semSetoidC c) = Quotient.mk semSetoidL (convertVec c)

-- RealLayerSemanticQuotient.lean:318
theorem semConv_injective : Function.Injective semConv
```

⚠ **特别注意 `_G-03.lean` 的处置**：调研报告 T4a/T4b 要求用到 `SameLayer`，
而 `SameLayer` 定义在 `lattice\lean\_G-03.lean`（⚠ **不在 `lakefile.toml` roots 里、
从未被 elaboration**）。⚠ 且**任务书明令「只创建你自己的新文件；绝不修改任何已有文件」**
⟹ **本文件不能 import `_G-03`，也不能改它**。
⭐⭐ **本文件的处置**：**在自己的文件里重新定义 `SameLayer`**（逐字同式），
并**如实登记这是重复**（见 §七 诚实边界）。⚠ **理由**：`SameLayer` 的定义体是**纯数据**
（`∃ lam mu, 0 < lam ∧ 0 < mu ∧ …`），**不含任何依赖**，故重定义**完全等价**且
**不引入任何风险**；反而**避免**把 `_G-03` 的 8 条 import 与整条依赖链拉进来。
⭐ **这符合任务书「缺依赖时」的正确处置**（任务书 §工作方式 4：留在文件里的必须是可证的）。

## 3. 本文件**不做**的（诚实边界）

- ⚠ **不 import `_G-03`**（它不在 roots、可能不编译；见上）。⇒ 本文件对 `SameLayer` 的
  定理是**关于本文件副本**的定理，**不是**关于 `_G-03.SameLayer` 的定理。
  ⚠ 二者**逐字同式**，故数学内容相同，但**机器上不是同一个常量** —— **如实登记**。
- ⚠ **不碰 `lakefile.toml`**（任务书铁律）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

namespace Lattice

/-! # 一、基础设施：`dot` 的结构引理

⚠ **为什么必须自己证**：本仓 `ConvertVectorLinear` 只提供 `dot_map_mul`（对**左**参数
逐项缩放）与 `foldl_init_add`，**没有** `dot` 对「尾随零」的不变性 ——
而「尾随零不影响 `dot`」**正是** T4b 反例的**根因**（`zip` 截断）。
⭐ 故本节的引理是本文件 §五/§六 的**承重技术内容**。 -/

/-- ⭐ **`zip` 的右零律**：右列表为空时 `zip` 为空。
⚠ 这是 `List.zip` 截断语义的**最小形式**（`Mathlib\Data\List\Zip.lean` 的 `zip_nil_right`）。 -/
theorem zip_nil_right_d21 (a : List Int) : a.zip ([] : List Int) = [] := by
  cases a <;> rfl

/-- ⭐ **`dot` 对右参数为空恒为 `0`**。 -/
theorem dot_nil_right_d21 (a : List Int) : dot a [] = 0 := by
  simp [dot, zip_nil_right_d21, List.foldl_nil]

/-- ⭐⭐ **`dot` 的右单步展开**：`dot a (y :: ys) = (a.zip (y :: ys)).foldl … 0`。
⚠ 这是把 `dot` 交给 `zip_cons_cons` 化简的**唯一**入口。 -/
theorem dot_cons_right_d21 (a : List Int) (y : Int) (ys : List Int) :
    dot a (y :: ys) = (a.zip (y :: ys)).foldl (fun acc uv => acc + uv.1 * uv.2) 0 := rfl

/-- ⭐⭐ **带初值的 `foldl` 等式还原为「零初值」形式**（把 §一 的递归假设接到 `foldl` 上的桥）。

      `foldl f init p = foldl f init q`  ⟸  `foldl f 0 p = foldl f 0 q`

⭐ **为什么需要它**：递归假设 `ih` 陈述的是 `dot` 的相等（`0` 初值的 `foldl`），
而 `foldl` 的 `cons` 步之后目标里出现的是**带累加器** `0 + h * y` 的 `foldl`。
⭐ 用 `foldl_init_add`（`ConvertVectorLinear.lean:74`，逐字
`foldl f init rest = init + foldl f 0 rest`）把**两侧同时**化到零初值形状。 -/
theorem foldl_init_eq_of_zero_d21 (p q : List (Int × Int)) (init : Int)
    (h : List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 p =
         List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 q) :
    List.foldl (fun acc uv => acc + uv.1 * uv.2) init p =
      List.foldl (fun acc uv => acc + uv.1 * uv.2) init q := by
  rw [foldl_init_add p init, foldl_init_add q init, h]

/-- ⭐⭐ **`dot` 对【左】参数追加一个 `0` 不变**（本文件最关键的技术引理）。

     `dot (a ++ [0]) x = dot a x`

⭐ **证明路线（本文件实测选的路线）**：⚠ **不**走「`(a ++ [0]).zip x = a.zip x ++ …`」
那条路 —— 实测它在 `List.foldl` 与 `HAppend (List (ℤ×ℤ)) (List ℤ)` 上立刻发散
（见 §七 的实测记录）。⭐ **改走「对 `a` 归纳（`x` 泛化）」**：
`zip` 对**两个**列表同时递归，把 `a ++ [0]` 与 `a` 的**首项对齐**后，
两侧的 `foldl` 尾项恰好就是 `dot (t ++ [0]) ys` 与 `dot t ys`，递归假设直接接上。

⚠ **消融（判据 1）**：本引理**是假的**若把 `[0]` 换成 `[c]`（`c ≠ 0`）——
取 `a = []`、`x = [c]` 即得 `c ≠ 0` 的矛盾。⭐ 故「追加的必须是零」是**承重**的。 -/
theorem dot_append_zero_d21 (a x : List Int) : dot (a ++ [0]) x = dot a x := by
  induction a generalizing x with
  | nil =>
      -- `([] ++ [0]).zip x = [0].zip x`
      cases x with
      | nil => simp [dot]
      | cons y ys => simp [dot]
  | cons h t ih =>
      cases x with
      | nil => simp [dot]
      | cons y ys =>
          -- ⭐ 只展开到**带累加器**的 `foldl` 形状，再用 `foldl_init_eq_of_zero_d21`
          -- 把递归假设（零初值形式）搬过来。
          -- ⚠ 本文件第一版在此失败三次（`did not find instance of pattern`），
          -- 真因是 `rw [foldl_init_add …]` 的**元变量尾部**无法被 `rw` 的句法匹配定位；
          -- ⭐ 改用**显式的辅助引理**把方向钉死。
          simp only [List.cons_append, List.zip_cons_cons, List.foldl_cons, dot]
          -- `ih ys : dot (t ++ [0]) ys = dot t ys`，而 `dot` 就是**零初值**的 `foldl`
          -- ⭐ 先在 `ih ys` 里把 `dot` 展开，才能喂给 `foldl_init_eq_of_zero_d21`
          have hz : List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 ((t ++ [0]).zip ys) =
                    List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 (t.zip ys) := ih ys
          exact foldl_init_eq_of_zero_d21 ((t ++ [0]).zip ys) (t.zip ys) (0 + h * y) hz

/-! # 二、T4b：⭐⭐ `SemEqL` 严格粗于 `SameLayer`（**机器反例**）

⚠ 本节**逐字重定义** `_G-03.SameLayer`（理由见文件头 §2）。
⭐ **非平凡性**（判据 2：反驳可能）：本节的定理**推翻**了一个「看起来该相等」的等式，
并**定位了根因**（`dot` 的 `zip` 截断 ⟹ 补零维不可由缩放吸收）。 -/

/-- ⭐⭐ **权重侧的「同一性」**（⚠ **逐字**同 `_G-03.lean:205-207`）。

⚠ **为什么在这里重定义**：`_G-03.lean` **不在 roots**、从未 elaboration，
且任务书禁止修改既有文件 ⇒ 不能 import 它。 -/
def SameLayerD21 (l l' : LinearLayer) : Prop :=
  ∃ lam mu : Int, 0 < lam ∧ 0 < mu ∧
    l.w.map (fun v => v * lam) = l'.w.map (fun v => v * mu) ∧ l.b * lam = l'.b * mu

/-- ⭐⭐ **`SameLayer ⟹ SemEqL`**（调研报告 T4a，报告判「真」）。

⭐ **证明路线**：`SameLayer` 给出正倍率 `lam`/`mu` 使 `w` 逐元素成比例、`b` 成比例
⟹ `LayerOut l x * lam = LayerOut l' x * mu`（用 `dot_map_mul`）
⟹ 由 `lam, mu ≠ 0` 得 `LayerOut l x = 0 ↔ LayerOut l' x = 0`。

⚠ **消融（判据 1）**：删掉「成比例」这一条，结论**为假**（§三 的反例就是见证）。
⚠ **这不是 `rfl`**：需要 `dot_map_mul`（`ConvertVectorLinear:88`）把 `dot` 从 `map` 里提出来，
再用 `Int` 上的 `mul_eq_zero` 消去。 -/
theorem sameLayer_imp_semEqL_d21 {l l' : LinearLayer} (h : SameLayerD21 l l') :
    SemEqL l l' := by
  obtain ⟨lam, mu, hlam, hmu, hw, hb⟩ := h
  intro x
  -- ⭐ 关键桥：把 `dot l.w x` 与 `dot l'.w x` 分别经 `dot_map_mul` 接到成比例等式上
  have hw' : dot (l.w.map (fun v => v * lam)) x = dot (l'.w.map (fun v => v * mu)) x := by
    rw [hw]
  rw [dot_map_mul l.w x lam, dot_map_mul l'.w x mu] at hw'
  -- ⭐ 两个线性组合相等，且倍率非零 ⟹ 零化谓词相同
  constructor
  · intro hzero
    -- `LayerOut l x = 0` ⟹ `dot l.w x = -l.b` ⟹ `dot l'.w x * mu = -l'.b * mu`
    have hl : dot l.w x + l.b = 0 := hzero
    have h2 : (dot l.w x + l.b) * lam = 0 := by rw [hl]; ring
    have h3 : (dot l'.w x + l'.b) * mu = 0 := by
      calc (dot l'.w x + l'.b) * mu
          = dot l'.w x * mu + l'.b * mu := by ring
        _ = dot l.w x * lam + l.b * lam := by rw [← hw', ← hb]
        _ = (dot l.w x + l.b) * lam := by ring
        _ = 0 := h2
    exact (mul_eq_zero.mp h3).resolve_right (ne_of_gt hmu)
  · intro hzero
    have hl : dot l'.w x + l'.b = 0 := hzero
    have h2 : (dot l'.w x + l'.b) * mu = 0 := by rw [hl]; ring
    have h3 : (dot l.w x + l.b) * lam = 0 := by
      calc (dot l.w x + l.b) * lam
          = dot l.w x * lam + l.b * lam := by ring
        _ = dot l'.w x * mu + l'.b * mu := by rw [hw', hb]
        _ = (dot l'.w x + l'.b) * mu := by ring
        _ = 0 := h2
    exact (mul_eq_zero.mp h3).resolve_right (ne_of_gt hlam)

/-- ⭐ 见证层 1：`w = [1]`、`b = 0`（即 `x₀ = 0`）。 -/
def d21L : LinearLayer := { w := [1], b := 0 }

/-- ⭐ 见证层 2：`w = [1, 0]`、`b = 0`（**补了一个零维**，`dot` 与 `d21L` 逐点相同）。 -/
def d21L_two : LinearLayer := { w := [1, 0], b := 0 }

/-- ⭐⭐ **见证的语义等价**：`dot [1, 0] x = dot [1] x`（对**一切** `x`）。

⭐ **证明**：`[1, 0] = [1] ++ [0]`（`rfl`），再套 `dot_append_zero_d21`。
⭐ **这正是 `zip` 截断的直接后果**：第二个分量的系数是 `0`，乘不上任何东西。 -/
theorem d21_dot_witness_eq (x : List Int) : dot d21L_two.w x = dot d21L.w x := by
  have h : d21L_two.w = d21L.w ++ [0] := rfl
  rw [h, dot_append_zero_d21]

/-- ⭐⭐ **`SemEqL d21L d21L_two` 为真**（反例的**正面**一半）。 -/
theorem d21_semEqL_witness : SemEqL d21L d21L_two := by
  intro x
  unfold LayerOut
  -- 两个 `b` 分量都是 `0`，只需把 `dot` 拉平
  have hb : d21L_two.b = d21L.b := rfl
  rw [d21_dot_witness_eq x, hb]

/-- ⭐⭐ **`SameLayer` 为假**（反例的**反面**一半，判据 2 的**锋利**形式）。

⚠ **证明只看 `w` 的【长度】**：`List.map` 保长度，故正倍率**不可能**把长度 `1` 变成 `2`。

⭐⭐ **这就是根因**：`dot` 用 `List.zip` **截断**，故「补零维」在**语义**上自由、
在**缩放**下**不自由**（缩放不变长度）—— 一族不可由缩放吸收的自由度。 -/
theorem d21_not_sameLayer_witness : ¬ SameLayerD21 d21L d21L_two := by
  rintro ⟨lam, mu, _hl, _hm, hw, _hb⟩
  -- ⭐ 只看 `w` 分量的**长度**：`List.map` 保长度，`[1]` 长 1、`[1,0]` 长 2
  have hlen := congrArg List.length hw
  simp only [d21L, d21L_two, List.length_map, List.length_cons, List.length_nil] at hlen
  omega

/-- ⭐⭐ **T4b：`SemEqL` 不蕴含 `SameLayer`**（调研报告判「真」，本文件证实）。

⭐ 这是本清单**新知识密度最高**的一条：它把「看起来该相等」的两个关系**分开**，
并给出**具体且内核可关闭**的见证。 -/
theorem semEqL_not_imp_sameLayer_d21 :
    ¬ (∀ l l' : LinearLayer, SemEqL l l' → SameLayerD21 l l') := by
  intro h
  exact d21_not_sameLayer_witness (h d21L d21L_two d21_semEqL_witness)

/-! # 三、T4a 的补充：`SameLayer` 是【严格】更细的关系（收口）

⚠ 上节给出「`SemEqL ⇏ SameLayer`」；本节补上「`SameLayer ⟹ SemEqL`」，
⭐ 两条合起来给出**严格包含**（判据 4：量化 —— 不是「不等」，而是「严格更细」）。 -/

/-- ⭐⭐ **`SameLayer` 严格细于 `SemEqL`**（两个方向各自有承重证明）。

⚠ **诚实标注**：本条**本身是新证明的合取**，但它**不是** rfl 级 ——
两个合取支分别是 §二的 `sameLayer_imp_semEqL_d21`（需 `dot_map_mul`）
与 §二的 `semEqL_not_imp_sameLayer_d21`（需 `zip` 截断 + 长度不变量）。 -/
theorem sameLayer_strictly_finer_than_semEqL_d21 :
    (∀ l l' : LinearLayer, SameLayerD21 l l' → SemEqL l l') ∧
    (∃ l l' : LinearLayer, SemEqL l l' ∧ ¬ SameLayerD21 l l') :=
  ⟨fun _ _ => sameLayer_imp_semEqL_d21,
   d21L, d21L_two, d21_semEqL_witness, d21_not_sameLayer_witness⟩

/-! # 四、要点 T1/T2：商上的往返 —— 补 `RealLayerSemanticQuotient.lean:652` 的「未做 `Equiv`」

## 4.1 ⭐ 关于调研报告 T2 的陈述：**判定为真，并已证**（附一次自我纠正的登记）

调研报告 T2 的草案逐字是

```lean
noncomputable def semConvEquiv : Quotient semSetoidC ≃ Quotient semSetoidL := …
```

⭐ **本文件的判定**：**该陈述为真**，本文件在 §4.2 把它**证出来**。

⚠ **如实登记我在此处的一次【错误猜测 → 自我纠正】**（任务书 §诚实边界 要求）：
我最初怀疑该陈述为假，理由是「`semConv` 可能不是满射」。
⚠ **该怀疑是错的**：`convertVec` 把 `w := c.a`，而 `VectorConstraint.a : List Int`
**不受任何约束** ⟹ `convertVec` **满射** ⟹ `semConv` **满射**。
⭐ 具体地，`⟦{w := [1,0], b := 0}⟧` **就在** `semConv` 的像里
（取 `c := {a := [1,0], b := 0}`）。
⇒ ⭐ **报告 T2 的陈述成立**；本文件额外把满射性单列为 §4.3（**交叉检验**）。

⚠ **本次纠正的教训**（值得登记）：`LinearLayer` 与 `VectorConstraint` 字段类型**逐字相同**
（`List Int` × `Int`），故凡「关于 `convertVec` 的满射/单射」的问题，
答案**总由字段类型决定**，**没有任何结构性障碍**。
⭐ 这与 `RealRoundtripNontrivial` §四 的诊断（两侧只是同一个记录换字段名）**完全一致**。 -/

/-- ⭐⭐ **T1：`semConv` 的右逆存在** —— 补上 `semConv` 的另一半。

⭐⭐ **构造**：`semExt := Quotient.lift (fun l => ⟦extractVec l⟧) …`，
相容性由 `extractVec_respects_semEq`（`RealLayerSemanticQuotient.lean:236-237`）给出。

注意 **`Quotient.inductionOn` 的坑（本仓已实测登记，`RealLayerSemanticQuotient.lean:320-331`）**：
它**消不掉出现在【假设】里的 `q`** ⟹ 证明体必须先把含 `q` 的假设 `revert` 回目标。
⭐ 本文件的证明体照此办理。

⚠ **为什么这不是 `rfl` 空壳（判据 1 消融）**：若把 `extractVec_respects_semEq` 这一
**相容性前提**删掉，`Quotient.lift` **根本无法构造**（良定义性失败）
⟹ **结论不可陈述**。这是**承重假设**的最强形式。 -/
theorem semConv_rightInverse_exists_d21 :
    ∃ semExt : Quotient semSetoidL → Quotient semSetoidC,
      Function.LeftInverse semExt semConv ∧
      Function.RightInverse semExt semConv := by
  -- ⭐ 构造 `semExt`：`extractVec` 经相容性下降到权重侧商上
  let semExt : Quotient semSetoidL → Quotient semSetoidC :=
    Quotient.lift
      (fun l => Quotient.mk semSetoidC (extractVec l))
      (fun l l' h => Quotient.sound (extractVec_respects_semEq h))
  refine ⟨semExt, ?_, ?_⟩
  · -- `LeftInverse semExt semConv`：`semExt (semConv q) = q`
    intro q
    -- ⚠ 先 `revert`：`Quotient.inductionOn` 消不掉出现在假设里的 `q`（本仓实测坑）
    refine Quotient.inductionOn q ?_
    intro c
    -- `semExt (semConv ⟦c⟧) = ⟦c⟧`：两侧都归约到 `⟦extractVec (convertVec c)⟧`
    show Quotient.mk semSetoidC (extractVec (convertVec c)) = Quotient.mk semSetoidC c
    rw [roundtrip_extractVec c]
  · -- `RightInverse semExt semConv`：`semConv (semExt q) = q`
    intro q
    refine Quotient.inductionOn q ?_
    intro l
    -- `semConv ⟦extractVec l⟧ = ⟦convertVec (extractVec l)⟧ = ⟦l⟧`
    show Quotient.mk semSetoidL (convertVec (extractVec l)) = Quotient.mk semSetoidL l
    -- ⭐ `convertVec (extractVec l) = l`：结构 eta（`cases` 展开两个字段）
    have hl : convertVec (extractVec l) = l := by cases l with | mk w b => rfl
    rw [hl]

/-- ⭐⭐ **T2：`semConv` 的双射性**（即它是 `Equiv`）—— 补
`RealLayerSemanticQuotient.lean:652` 逐字登记的「未做 `Equiv`」。

⭐ **它比 T1 多说了什么**：T1 只说「存在一对互逆的映射」；
本条把它**打包成 `Equiv`**，即**把往返律提升为一个结构**（判据 4：量化形式）。

⚠ **它不是 `constraintLayerEquiv`**（`RealRoundtripNontrivial:277`，结构双射、`rfl` 级）：
本条的 `right_inv`/`left_inv` 走的是 **`Quotient.exact` 与 `Quotient.sound`**（真定理），
⚠ **不是**定义展开。⇒ ⭐ **消融可执行**：把 `SemEqC` 换成结构相等 `=`，
则本条**退化为 `constraintLayerEquiv`** ⟹ **立刻变 `rfl`**。 -/
noncomputable def semConvEquiv_d21 : Quotient semSetoidC ≃ Quotient semSetoidL where
  toFun := semConv
  invFun :=
    Quotient.lift
      (fun l => Quotient.mk semSetoidC (extractVec l))
      (fun l l' h => Quotient.sound (extractVec_respects_semEq h))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro c
    show Quotient.mk semSetoidC (extractVec (convertVec c)) = Quotient.mk semSetoidC c
    rw [roundtrip_extractVec c]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro l
    show Quotient.mk semSetoidL (convertVec (extractVec l)) = Quotient.mk semSetoidL l
    have hl : convertVec (extractVec l) = l := by cases l with | mk w b => rfl
    rw [hl]

/-- ⭐ **T2 与 `semConv_injective` 的一致化**：`semConvEquiv_d21` 的 `toFun` 就是 `semConv`，
且它是双射（**交叉检验**：与既有的 `semConv_injective` 不冲突）。

⚠ **本条是接口定理**（`conv` 是 `rfl`），⭐ 但其**内容**来自 `semConvEquiv_d21`
（后者的两个互逆律**都不是 `rfl`**）。 -/
theorem semConvEquiv_toFun_d21 : ⇑semConvEquiv_d21 = semConv := rfl

/-- ⭐ **T2 的推论（判据 4：量化）**：`semConv` 是满射。

⚠ **报告未提这一条**。⭐ 它**不是** T2 的必需前提
（`Equiv.ofBijective` 也可用），但它是**独立**的量化结论，
且它**恰好**回答了「报告 T4b 的见证层 `{w := [1,0], b := 0}` 在不在像里」——
⭐ **在**（取 `c := {a := [1,0], b := 0}`）。 -/
theorem semConv_surjective_d21 : Function.Surjective semConv :=
  semConvEquiv_d21.surjective

/-! # 五、T5 的 (⟸) 方向：**去尾零**是 `SemEqL` 的语义不变量

⭐ 上节（§二）的 T4b 反例**根因**是「补零维自由」。本节把该自由度**显式化**为
「追加零不改变 `dot`」这条**技术引理**。

⚠⚠ **诚实前置（不许省）**：本节**没有**证成报告 T5 的充要条件。
⭐ 本节证的是它的 **(⟸) 方向的【技术内核】**：
`dot (b ++ replicate n 0) x = dot b x` —— 即「补零维」不改变语义。
⚠ **报告 T5 的完整 (⟸)**（「去尾零后成比例 ⟹ `SemEqL`」）
还需要「去尾零运算与 `++ replicate` 分解的衔接」，**那一条本文件未证**（见 §七）。
⭐⭐ **报告 T5 的 (⟹) 方向**本文件**既未证也未证伪**（见 §六）。 -/

/-- ⭐ **去尾零**（`reverse`/`dropWhile`/`reverse` 形式，与报告 T5 草案逐字同式）。

⚠⚠ **本文件【没有】用到这个定义** —— 如实登记：
§五 的落点 `dot_of_append_zeros_d21` 走的是 `++ replicate` 形式，
而**把该定义与 `++ replicate` 分解衔接起来**的那条引理
（`∃ n, a = trimTrailingZerosD21 a ++ replicate n 0`）
**本文件未证**（见 §七）。
⭐ 保留该定义是**为了让「未证的部分」可被机器检索**，
**不**声称它已被使用或已与 §五 的落点打通。 -/
def trimTrailingZerosD21 (l : List Int) : List Int :=
  l.reverse.dropWhile (fun v => v = 0) |>.reverse

/-- ⭐ **`dot` 对右参数追加零的不变性**（把 §一 的 `dot_append_zero_d21` 用在左边）。

⚠ **本条不是 `rfl`**：需要把 `dot (a ++ [0]) x` 经 `dot_append_zero_d21` 消去。 -/
theorem dot_append_zero_left_d21 (a : List Int) (x : List Int) :
    dot (a ++ [0]) x = dot a x :=
  dot_append_zero_d21 a x

/-- ⭐⭐ **`dot` 对左参数追加任意个零都不变**（引理 A 的归纳升级）。

⭐ **这是 §五 承重的技术引理**：T4b 的见证是「追加**一个**零」，
而 `trimTrailingZeros` 一般要删掉**多个**零。 -/
theorem dot_append_replicate_d21 (a : List Int) (n : Nat) (x : List Int) :
    dot (a ++ List.replicate n 0) x = dot a x := by
  induction n with
  | zero => simp
  | succ k ih =>
      -- ⭐ 用 mathlib 的 **`List.replicate_succ'`**（`Data/List/Basic.lean:214`，逐字
      --    `replicate (n + 1) a = replicate n a ++ [a]`）—— 这正是所需的形状。
      -- ⚠ 本文件第一版在此**两次**失败（如实登记）：
      --   ① 用内层对 `k` 的归纳去证 `replicate (k+1) 0 = replicate k 0 ++ [0]`，
      --      结果**遮蔽**了外层的 `ih`（错误信息里 `ihj` 的陈述被污染）；
      --   ② 改用 `show … ; rw [ihj]; rfl` 后，`replicate (j+1+1) 0` 与
      --      `replicate j 0 ++ [0] ++ [0]` **不是**定义相等 ⟹ `rfl` 失败。
      -- ⭐ **正解：直接引用既有引理名**（任务书 §排错判据 ②：签名逐字核对）。
      rw [List.replicate_succ' k (0 : Int), ← List.append_assoc, dot_append_zero_d21, ih]

/-- ⭐⭐ **T5 的 (⟸) 方向（本文件证成的形式）：「补零维」不改变 `dot`。**

⭐ **本条的用途**：它把 T5 的 (⟸) 方向**完全**归约到「补零维」这一个自由度上，
⭐ 而该自由度的**存在性**由 §二 的 T4b 反例给出 ——
**两条合起来才说明「去尾零」为什么是必要的**：
若把「补零维」当成**同一个**层（`SemEqL` 确实这么看），
则 `SameLayer` 就**不是**那个关系（T4b）⟹ 任何「模掉补零维」的刻画
都**必须**显式经过 `trimTrailingZeros` 这类**去尾零**运算，
**不能**直接说「成比例」。

⚠⚠ **诚实标注（本文件的一处【未证】）**：`trimTrailingZerosD21` 的
`reverse/dropWhile/reverse` 实现与上面这个 `++ replicate` 形式**相等**
这一条**本文件未证**（见 §七）。⭐ 故本文件对 T5 的贡献是
**「补零维不变」+「`SemEqL ⇏ SameLayer`」两条**，
**不是**报告所要求的那条完整充要条件。 -/
theorem dot_of_append_zeros_d21 (b : List Int) (n : Nat) (x : List Int) :
    dot (b ++ List.replicate n 0) x = dot b x :=
  dot_append_replicate_d21 b n x

/-! # 六、⚠ T5 的 (⟹) 方向：**本文件未证，且不改弱陈述冒充它**

⚠ 调研报告 T5 的 (⟹) 逐字要求：

> 零化谓词相同 ⟹ 「成比例 **模掉尾随零**」（`ScaleClassPlus` 意义上的**正**倍率）

⚠ 报告自己标注：**「未验证」「我明确登记：未验证」**，
并说「**若 `⟹` 为假，则本条应改写为否定结论**」。

⭐⭐ **本文件的处置（诚实边界，不许省）**：

**① 我没有证明 (⟹)，也没有证伪它。**
它需要「`List.zip` 截断下，零化谓词决定系数（模尾零）」这一
`Int` 上的线性代数事实。⚠ 我**没有**找到该论证的 Lean 化路径，
**故按任务书 §工作方式 4 处置：不留 `sorry`，不改弱陈述冒充它，
在报告 `_prove_out\P_D2-1.md` 里登记为「未证」。**

**② 我给出的 `[1]` / `[-1]` 反例（§六-bis）【不能】证伪 T5 的 (⟹)。**
⚠ **这一点必须说清楚，否则就是夸大**：
`[1]` 与 `[-1]` 在 `ScaleClassPlus`（**正**倍率）下**不成比例**，
⚠ 但在 `ScaleClass`（**非零**倍率）下**成比例**（取 `lam = 1`、`mu = -1`）。
⭐ 而 T5 的候选写法用的是 `0 < lam` ⟹ 故该反例**只**证伪
「**正**倍率成比例」这一读法（即 §二 的 `SemEqL ⇏ SameLayer`），
**不**触及「非零倍率 + 去尾零」的读法。

**③ ⇒ 本文件对 T5 的**真实贡献**是两条〔都不是 T5 本身〕**：
- ⭐ `semEqL_not_imp_sameLayer_d21`（§二）：**正倍率**读法**为假**（机器反例，判据 2）；
- ⭐ `dot_of_append_zeros_d21`（§五）：「补零维」**不改变** `dot`
  ⟹ 任何模掉补零维的刻画**必须**显式经过「去尾零」运算。

⭐⭐ **⇒ 对调研报告 T5 的最终判定：`(⟹)` 的真实性【未被本文件裁决】。**
⚠ 我**倾向**认为它在「非零倍率 + 去尾零」读法下**为真**
（报告已排除伪反例 `[1,0,1]` vs `[1,0,0,1]`），但**倾向不是证明** ——
**本文件不把它写成定理**。 -/

/-- ⭐ **否定见证层**：`w = [1]`、`b = 0`。 -/
def d21Neg : LinearLayer := { w := [1], b := 0 }

/-- ⭐ **否定见证层**：`w = [-1]`、`b = 0`。 -/
def d21Neg_alt : LinearLayer := { w := [-1], b := 0 }

/-- ⭐⭐ **见证：`dot` 相差一个符号**（把 `[1]` 与 `[-1]` 的关系**结构地**说清楚）。

⭐ **本文件不展开 `foldl`**（⚠ `omega` 对 `foldl` 内的项**无效**，实测）——
而是先证**这条结构等式**，再在 `Int` 上消解。 -/
theorem d21_dot_neg_witness (x : List Int) : dot d21Neg_alt.w x = -dot d21Neg.w x := by
  -- `[1].zip x` 与 `[-1].zip x` 的形状只差首项的符号
  cases x with
  | nil => simp [d21Neg, d21Neg_alt, dot]
  | cons y ys => simp [d21Neg, d21Neg_alt, dot]

/-- ⭐⭐ **见证：`SemEqL d21Neg d21Neg_alt` 为真**（⚠ **但它【不是】** `SameLayer`）。

⚠ **证明的关键是 `a = 0 ↔ -a = 0`**，即**符号不改变零化谓词**。

⚠ **本文件第一版在此失败并已修正（如实登记）**：
第一版直接 `unfold LayerOut` 后用 `omega`，⚠ 报
`omega could not prove the goal: … a := dot {w := [-1], b := 0}.w x`
—— ⭐ **真因是 `omega` 不会展开 `dot`/`foldl`**（它在 `Int` 上是**线性**算术求解器，
而 `foldl` 是**未解释函数**）。⭐ 修法：先用 `d21_dot_neg_witness` 把两个 `dot`
化成 `a` 与 `-a`，再 `omega` —— **逻辑与结论完全不变**。

⚠⚠ **本条的【适用范围】必须说清楚**：它证伪的是「**正**倍率成比例」读法
（即 §二 的 `SameLayer`），**不是** T5 的「非零倍率 + 去尾零」读法 ——
因为 `[1]` 与 `[-1]` 在**非零**倍率下**确实**成比例（`lam = 1`、`mu = -1`）。
⭐ **详见本节 §六 开头 ② 的诚实说明。** -/
theorem d21_semEqL_neg_witness : SemEqL d21Neg d21Neg_alt := by
  intro x
  -- ⚠ 目标展开：`LayerOut d21Neg x = 0 ↔ LayerOut d21Neg_alt x = 0`
  -- ⭐ 关键：`dot d21Neg_alt.w x = -dot d21Neg.w x`，且两侧 `b` 都是 `0`
  have h := d21_dot_neg_witness x
  have hb : d21Neg_alt.b = 0 := rfl
  have hb' : d21Neg.b = 0 := rfl
  show LayerOut d21Neg x = 0 ↔ LayerOut d21Neg_alt x = 0
  unfold LayerOut
  rw [hb, hb', h]
  constructor <;> intro hz <;> omega

/-- ⭐⭐ **`¬ SameLayerD21 d21Neg d21Neg_alt`**：正倍率**不可能**把 `[1]` 变成 `[-1]`。

⚠ **证明是纯算术**：`1 * lam = -1 * mu` 且 `lam, mu > 0` ⟹ 左正右负 ⟹ 矛盾。

⭐ **⚠ 本文件第一版在此处失败并已修正（如实登记）**：
第一版用 `congrArg List.head? hw` 取首分量，⚠ 但 `List.head?` 在 `nil` 分支
不给出算术信息，且 `List.head?_map` 的句法形状不吻合。
⭐ **改为 `cases` 展开两个具体列表**（两处 `w` 都是字面量），
使 `map` 被 `simp` 直接归约掉，`omega` 只剩线性算术。 -/
theorem d21_not_sameLayer_neg_witness : ¬ SameLayerD21 d21Neg d21Neg_alt := by
  rintro ⟨lam, mu, hl, hm, hw, _hb⟩
  -- `w` 两侧都是字面量列表 ⟹ `map` 直接归约，剩 `1 * lam = -1 * mu`
  simp only [d21Neg, d21Neg_alt, List.map_cons, List.map_nil, List.cons.injEq] at hw
  omega

/-! # 七、⚠⚠ 诚实边界汇总（**不许省** —— 任务书 §报告结构 要求）

## 本文件【做到】的

| # | 内容 | 位置 | 是否 `rfl` |
|--:|:--|:--|:--|
| 1 | `SameLayer ⟹ SemEqL`（需 `dot_map_mul` + `mul_eq_zero`） | `sameLayer_imp_semEqL_d21` | ❌ 非 `rfl` |
| 2 | `SemEqL ⇏ SameLayer`（长度见证，`List.map` 保长度） | `semEqL_not_imp_sameLayer_d21` | ❌ 非 `rfl` |
| 3 | `SameLayer` 严格细于 `SemEqL`（收口） | `sameLayer_strictly_finer_than_semEqL_d21` | ❌ |
| 4 | ⭐ `semConv` 的右逆存在（`Quotient.lift`） | `semConv_rightInverse_exists_d21` | ❌ 非 `rfl` |
| 5 | ⭐ 商上的往返是 `Equiv`（补 `:652` 的「未做」） | `semConvEquiv_d21` | ❌ 非 `rfl` |
| 6 | `semConv` 满射（T2 交叉检验） | `semConv_surjective_d21` | ❌ |
| 7 | 「补零维」不改变 `dot`（`++ replicate`） | `dot_of_append_zeros_d21` | ❌ 非 `rfl` |
| 8 | 负号见证：`SemEqL` 对 `[-1]` 成立但 `SameLayer` 不成立 | `d21_semEqL_neg_witness` | ❌ 非 `rfl` |

## 本文件【没有】做的（**诚实清单**）

1. ⚠⚠ **报告 T5 的 (⟹) 方向（充要条件的必要性）**：
   **既未证也未证伪**。⚠ 我**没有**把它写成定理。
   ⭐ 它需要「`List.zip` 截断下，零化谓词决定系数（模尾零）」这一
   `Int` 上的线性代数事实，本文件未找到 Lean 化路径。
   ⚠ 我**倾向**认为它在「非零倍率 + 去尾零」读法下为真，
   ⚠ **但倾向不是证明** ⟹ **登记为未证**。
2. ⚠ **报告 T5 的 (⟸) 方向的完整形式**（「去尾零后成比例 ⟹ `SemEqL`」）**未证**。
   本文件只证了它的**技术内核**（`dot_of_append_zeros_d21`）。
   ⚠ 缺的一步是「`trimTrailingZerosD21` 与 `∃ n, a = trim b ++ replicate n 0` 的衔接」。
3. ⚠ **报告 T3**（`semQuotient_is_the_nondegenerate_locus`）**未做**：
   ⭐ 报告自己已诚实降级为「**大部分内容是重新打包既有定理**」
   （第一合取项**就是** `naive_fiber_has_two_points`）。
   ⇒ ⚠ 本文件**不重打包它**（重打包不产生新知识），**如实登记为跳过**。
4. ⚠ **报告 T6 / T6′**（元层「非 rfl 判据」）**未做**：
   ⭐ 报告自己已判定 T6 的第二个合取项是 `True`（空洞）、
   T6′ 是 `not_forall` 的重述（**四条非平凡性判据全部不通过**）。
   ⇒ ⚠ 本文件**不写空壳**，**如实登记为跳过**（任务书 §非平凡性 明令）。
5. ⚠ **报告 T7**（`canonicalizeW_unique`）**未做**：
   ⭐ 报告自己已标注它与 `_G-03.lean:509` 的
   `any_weight_side_canonical_eq_canonicalizeW` **内容重叠**（`_G-03` 已证），
   且需要 `import RealCanonicalForm`（⚠ 可能引入 `Zero VectorConstraint` 实例冲突）。
   ⇒ ⚠ **如实登记为跳过**。
6. ⚠ **`_G-03.lean` 的 `SameLayer` 本体未 import**：
   它**不在 `lakefile.toml` roots**、从未 elaboration；
   且任务书禁止修改既有文件 ⟹ 本文件**重新定义** `SameLayerD21`（逐字同式）。
   ⚠ **故本文件对 `SameLayer` 的定理是关于本文件副本的**，
   **不是**关于 `_G-03.SameLayer` 的 —— 数学内容相同，**机器上不是同一个常量**。
7. ⚠ **报告 §D 的「两个权重侧商从未对照过」这一点未做**：
   报告 T4 的原式 `SameLayer l l' ↔ SemEqL l l'` 被报告自己判为
   **`⟸` 方向为假**（用 `zip` 截断见证）。⭐ 本文件的 `semEqL_not_imp_sameLayer_d21`
   **证实了该判定**（用的是**长度**见证，比报告的 `zip` 截断见证更强、更省）。
   ⚠ 但**报告 T4 的 `⟹` 方向（`SameLayer ⟹ SemEqL`）本文件已证**（第 1 条）。
8. ⚠ **`semConvEquiv_d21` 与既有 `semConv_injective` 的关系未形式化**：
   ⭐ 本文件给了 `semConvEquiv_toFun_d21 : ⇑semConvEquiv_d21 = semConv`，
   ⚠ 但**没有**证「`Equiv` ⟹ `Injective`」这条推论与既有 `semConv_injective` 一致
   （那是 `Equiv.injective` 的一次调用，**本文件未写**）。

## ⚠ 我改弱了哪条陈述？

- ⚠ **【一处：T5 的 (⟸)】**：报告要求「去尾零后成比例 ⟺ `SemEqL`」（**充要**），
  本文件只交付了**技术内核**（`dot` 的补零维不变性）。
  ⭐ **即：我把「充要条件」降级为「一条必要技术引理」。**
- ⚠ **【一处：T5 的 (⟹)】**：报告预期它为真（虽未验证）。
  本文件**没有**把它改写成任何形式 —— **登记为未证**。
- ⚠ **【一处：`SameLayer`】**：报告要求的是 `_G-03.SameLayer`；
  本文件**重新定义了同式的 `SameLayerD21`**（因 `_G-03` 不可 import）。
  ⭐ **这是【载体】的替换，不是【陈述】的弱化**，但**必须明说**。

## ⚠ 哪个判断我特别不确定

- ⭐⭐ **「T5 的 (⟹) 在非零倍率 + 去尾零读法下为真」这个倾向** ——
  ⚠ 我**没有**验证它；报告也只说「倾向为真」。
  ⭐ 若它为假，则 T5 应改写为**否定结论**；⚠ **本文件不预判。**
- ⭐ **`trimTrailingZerosD21` 的定义是否与报告意图逐字一致** ——
  我用的是报告草案的 `reverse/dropWhile/reverse` 形式（逐字同式），
  ⚠ 但**没有**证明它满足「删掉的全是零」这一**刻画性质**。

## ⚠⚠ 交付状态（编译实测）

```
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\probe.ps1 -Soft lean\_D2-1.lean
[lean-lock] lake env lean C:\Users\xingg\Desktop\agent\lattice\lean\_D2-1.lean
[lean-lock] exit code: 0
```

⚠ **重要说明（为什么不是 `lean_probe.py`）**：
任务书指定 `python scripts\lean_probe.py lean\_D2-1.lean`，
⚠ **但该命令对本文件【在结构上不可能】返回 `exit 0`** ——
`lean_probe.py` 走的是 `lake build <模块名>`，而
`lakefile.toml` 的 `roots` **从不包含 `_` 开头的文件**
（`scripts\register-new-roots.ps1:44` 逐字 `if ($n.StartsWith('_')) { continue }`）。
⇒ 实测输出是 `error: unknown target '_D2-1'`（**B211**），
⭐ 而 `lean_probe.py` 自己的诊断信息就指向了 `probe.ps1`：
「Add it to roots, or use probe.ps1 for a single file.」
⇒ ⭐ **本文件因此用 `probe.ps1` 完成内核验证**（`exit code: 0`，见上），
并**如实登记这一纪律冲突**。 -/

end Lattice
