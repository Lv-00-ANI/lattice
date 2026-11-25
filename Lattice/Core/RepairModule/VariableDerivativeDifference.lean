import Mathlib
import Lattice.Core.VariableNet
import Lattice.Core.VariableActLayer
import Lattice.Core.AnalysisHelper
import Lattice.Core.RepairModule.VariableDerivativeDegree

/-!
# `VariableDerivativeDifference`

**4/4：`deg p = 0` 的数学边界与差分算子。**

**⇒ 自 4,197–5,521 行。**
-/

namespace Lattice.Core


/-! ## ⚠⚠ 第 36 轮：`deg p = 0` 是一个【真正的**数学边界，不是战术问题

## 压顶定理需要的

**`chainNatPoly_totalDegree`（第 33 轮）的前提是 `1 ≤ p.totalDegree`。
而网络输入是标量 `x`，载体写作 `MvPolynomial.C x`——**它的次数是 0**。
⇒ 直接套用被前提挡住。** -/

/-! ## 我试的补救：`deg p = 0` 的情形单独证

**目标：`deg(stepNat (off, p)) = 1`（当 `deg p = 0`）。

**我用的仍是 `totalDegree_add_eq_left_of_totalDegree_lt`，而它要求
`deg(X (off+1)) < deg(X off · p)`，即 `1 < 1 + 0`。**

**⚠ 那是【假**的。`deg p = 0` 时 `deg(X off · p) = 1`，与 `deg(X (off+1)) = 1` 【相等**，
于是那条引理的前提不成立，`rw` 把目标变成了 `False`。**

**⇒ 这不是名字或顺序的问题：`deg p = 0` 时两层次数【并列**，
`totalDegree_add_le` 只给 `≤ 1`，而下界 `≥ 1` 需要另找依据。** -/

/-! ## 正确的补救（下一轮）

**`deg p = 0` 时 `p = C c`（某个常数 `c`），于是 `X off · C c + X (off+1)`
【正是第 22 轮证过的形状**——`totalDegree_X_mul_C_add_X_ge`（`c ≠ 0`、`a ≠ b`）。**

**⇒ 那条给出 `1 ≤ deg`，配 `totalDegree_add_le` 的上界即得 `= 1`。**

**⚠ 但需要一个「`deg p = 0` ⇒ `p = C c` 且 `c ≠ 0`」的分解引理。
mathlib 里应当有 `MvPolynomial.totalDegree_eq_zero` 或 `eq_C_of_totalDegree_zero`——
第 24 轮查过 `totalDegree_eq_zero` 【不存在**，但 `eq_C_of_totalDegree_zero` 还没查过。**

**⇒ 下一轮第一件事：`#check @MvPolynomial.eq_C_of_totalDegree_zero` 等候选。**

## 另一条更简单的路

**放弃 `C x` 作为输入，改用 `X 0`——它的次数是 1，`1 ≤ deg` 直接满足。**

**代价**：**输出多项式的次数变成 `1 + 长度`，而不是 `长度`。**

**⇒ 而那是【诚实**的：**输入变量本身也是一个变量，所以「输出的总次数 = 层数 + 1」是更准确的说法。**
**⇒ 若 `eq_C_of_totalDegree_zero` 不存在，下一轮就走这条，并在陈述里写明那多出来的一次来自输入。** -/


/-! ## ⭐⭐⭐ 压顶定理：链的输出是参数的一个显式多项式

**第 36 轮发现 `deg p = 0` 是一个真正的数学边界：`C x` 的次数是 0，
而 `chainNatPoly_totalDegree` 要求 `1 ≤ deg p`。**

**⇒ 本节把结论分成两条，各自在【能成立的前提】**下陈述：

1. **次数**：以 `X 0` 为输入（次数 1），得 `deg = 1 + 长度`；
2. **求值**：以 `C x` 为输入（真实标量输入），得 `eval = flatChainAct`。

**⚠ 后者不需要次数信息——它只依赖 `chainNatPoly_eval_act`、`chainNatAct_eq_chainOneAct`
与 `chainOneAct_eq_flatChainAct` 三条，全部已证。** -/

/-- ⭐ **`X 0` 的次数是 1**。 -/
theorem totalDegree_X_zero_nat : (MvPolynomial.X 0 : MvPolynomial ℕ ℝ).totalDegree = 1 :=
  MvPolynomial.totalDegree_X _

/-- ⭐⭐ **以 `X 0` 为输入时，输出次数 = `1 + 层数`**——**（输入那一次是变量本身）。** -/
theorem chainNatPoly_X0_totalDegree (ls : ChainList) :
    (chainNatPoly ls (MvPolynomial.X 0)).totalDegree = 1 + ls.length := by
  have hne : (MvPolynomial.X 0 : MvPolynomial ℕ ℝ) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hdeg : 1 ≤ (MvPolynomial.X 0 : MvPolynomial ℕ ℝ).totalDegree := by
    rw [totalDegree_X_zero_nat]
  rw [chainNatPoly_totalDegree ls (MvPolynomial.X 0) hne hdeg, totalDegree_X_zero_nat]

/-- ⭐⭐⭐ **压顶（求值形式）**：**链的多项式在 `readSlot gN` 处的值，就是网络的输出。**

**⚠ 这是整条链的终点陈述：`ℕ` 下标载体（`foldl`，无递归展开）
→ `ChainOne`（第 35 轮）→ `flatChainAct`（第 17 轮）。** -/
theorem chainList_output_eval {N : ℕ} (ls : ChainList)
    (hN : 0 + 2 * ls.length + 1 < N) (x : ℝ) (gN : Fin N → ℝ) :
    (chainNatPoly ls (MvPolynomial.C x)).eval (fun k => readSlot gN k)
      = flatChainAct (N := N) (chainOneToChain (listToChainOne ls)) 0 gN
          (fun _ => x) (0 : Fin 1) := by
  have hN' : 0 + 2 * chainOneDepth (listToChainOne ls) + 1 < N := by
    rw [chainOneDepth_listToChainOne]
    exact hN
  rw [chainNatPoly_eval_act]
  simp only [chainNatAct]
  rw [chainNatAct_eq_chainOneAct ls (0, (MvPolynomial.C x).eval (fun k => readSlot gN k)) gN]
  simp only [MvPolynomial.eval_C]
  exact chainOneAct_eq_flatChainAct (listToChainOne ls) 0 hN' gN x

/-- ⭐⭐⭐ **压顶（合取形式）**：**次数在 `X 0` 输入下、求值在 `C x` 输入下，一并陈述。** -/
theorem chainList_output_is_polynomial {N : ℕ} (ls : ChainList)
    (hN : 0 + 2 * ls.length + 1 < N) (x : ℝ) :
    (chainNatPoly ls (MvPolynomial.X 0)).totalDegree = 1 + ls.length
      ∧ ∀ (gN : Fin N → ℝ),
          (chainNatPoly ls (MvPolynomial.C x)).eval (fun k => readSlot gN k)
            = flatChainAct (N := N) (chainOneToChain (listToChainOne ls)) 0 gN
                (fun _ => x) (0 : Fin 1) :=
  ⟨chainNatPoly_X0_totalDegree ls, fun gN => chainList_output_eval ls hN x gN⟩


/-! ## ⚠⚠ 第 38 轮：`deg p = 0` 的两处具体修法（已定位，未完成）

## 要补的两条

1. **`totalDegree_X_mul_C_add_X_zero_nat`**（`ℕ` 下标的 `X a · C c + X b` 次数 = 1）——
   **第 22 轮 `Fin N` 版本的对应物**；
2. **`eq_C_of_totalDegree_zero_nat`**（`deg p = 0 ⇒ p = C (coeff 0 p)`）。

## 第一处的现状

**它有 `le_antisymm` 两支：上界用 `totalDegree_add` + `totalDegree_mul` + `totalDegree_X` + `totalDegree_C`；
下界用 `coeff (single a 1)` + `le_totalDegree`。**

**本轮把它写进了文件，编译【通过**——**所以第一条本身没有障碍。**

## 第二处失败的两个具体点

**⚠ 1. 分支目标 `⊢ 0 = if 0 = m then coeff 0 p else 0`（其中 `m ≠ 0`）。**
**`simp` 需要知道 `0 ≠ m`，而 `m ≠ 0` 已有——但 `simp` 没有用它，
因为 `if 0 = m` 里 `0` 是【字面量**而 `m` 是变量，判据方向相反。**

**⇒ 修法：在 `simp` 前先 `have : (0 : ℕ →₀ ℕ) ≠ m := fun h => hm h.symm`，
然后 `simp [this]`，或直接 `rw [if_neg this]`。**

**⚠ 2. `simp only [stepNat, hC]` 报 `maximum recursion depth has been reached`。**
**展开 `MvPolynomial.C` 再展开 `stepNat` 的组合让 `simp` 递归过深。**

**⇒ 修法：不用 `simp`，改用 `rw [hC]` 单独替换，再 `rw [totalDegree_X_mul_C_add_X_zero_nat …]`。**

## 结论

**本轮没有代码入库（回退到 738）。**

**⇒ 下一轮按上面两条具体修法重做，两条都只需改一行。** -/


/-- ⭐⭐ **`ℕ` 下标版：`deg(X a · C c + X b) = 1`**（`c ≠ 0`、`a ≠ b`）。

**⚠ 第 22 轮 `Fin N` 版本的对应物——`deg p = 0` 情形所需的原子步骤。** -/
theorem totalDegree_X_mul_C_add_X_zero_nat (a b : ℕ) (hab : a ≠ b)
    {c : ℝ} (hc : c ≠ 0) :
    (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
      : MvPolynomial ℕ ℝ).totalDegree = 1 := by
  apply le_antisymm
  · calc (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
          : MvPolynomial ℕ ℝ).totalDegree
        ≤ max (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial ℕ ℝ).totalDegree
            (MvPolynomial.X b : MvPolynomial ℕ ℝ).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ 1 := by
          rw [max_le_iff]
          constructor
          · calc (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial ℕ ℝ).totalDegree
                ≤ (MvPolynomial.X a : MvPolynomial ℕ ℝ).totalDegree
                  + (MvPolynomial.C c : MvPolynomial ℕ ℝ).totalDegree :=
                  MvPolynomial.totalDegree_mul _ _
              _ = 1 := by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
          · rw [MvPolynomial.totalDegree_X]
  · have hkey : MvPolynomial.coeff (Finsupp.single a 1)
        (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
          : MvPolynomial ℕ ℝ) = c := by
      rw [MvPolynomial.coeff_add]
      have h1 : MvPolynomial.coeff (Finsupp.single a 1)
          (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial ℕ ℝ) = c := by
        have heq : (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial ℕ ℝ)
            = MvPolynomial.C c * MvPolynomial.X a := by ring
        rw [heq, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
        ring
      have h2 : MvPolynomial.coeff (Finsupp.single a 1)
          (MvPolynomial.X b : MvPolynomial ℕ ℝ) = 0 := by
        rw [MvPolynomial.coeff_X']
        have hba : (Finsupp.single b 1 : ℕ →₀ ℕ) ≠ Finsupp.single a 1 := by
          rw [Ne, Finsupp.single_eq_single_iff]
          omega
        simp [hba]
      rw [h1, h2, add_zero]
    have hne : MvPolynomial.coeff (Finsupp.single a 1)
        (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
          : MvPolynomial ℕ ℝ) ≠ 0 := by
      rw [hkey]; exact hc
    have hmem := MvPolynomial.mem_support_iff.mpr hne
    have hdeg := MvPolynomial.le_totalDegree hmem
    simpa using hdeg

/-- ⭐⭐ **`deg p = 0` ⇒ `p` 是常数**（形如 `C c`）。

**⚠ 第 38 轮定位的第一处：`if 0 = m` 的判据是【字面量在左**，
与假设 `m ≠ 0` 方向相反，所以 `simp` 关不掉它——必须显式 `rw [if_neg]`。** -/
theorem eq_C_of_totalDegree_zero_nat (p : MvPolynomial ℕ ℝ) (h : p.totalDegree = 0) :
    p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
  ext m
  by_cases hm : m = 0
  · subst hm; simp
  · have hsupp : m ∉ p.support := by
      intro hmem
      have hall := (MvPolynomial.totalDegree_eq_zero_iff ℕ p).mp h m hmem
      apply hm
      ext x
      exact hall x
    rw [MvPolynomial.mem_support_iff] at hsupp
    push_neg at hsupp
    have h0m : (0 : ℕ →₀ ℕ) ≠ m := fun hh => hm hh.symm
    rw [hsupp]
    simp only [MvPolynomial.coeff_C]
    rw [if_neg h0m]

/-- ⭐⭐ **`deg p = 0` 时的 `stepNat` 次数是 1**——**第 36 轮标出的边界的解法。** -/
theorem stepNat_totalDegree_zero (off : ℕ) (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0)
    (hdeg : p.totalDegree = 0) :
    (stepNat (off, p)).2.totalDegree = 1 := by
  have hC : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
    eq_C_of_totalDegree_zero_nat p hdeg
  have hc : MvPolynomial.coeff 0 p ≠ 0 := by
    intro h
    rw [hC, h, MvPolynomial.C_0] at hp
    exact hp rfl
  simp only [stepNat]
  rw [hC]
  exact totalDegree_X_mul_C_add_X_zero_nat off (off + 1) (by omega) hc


/-- ⭐⭐⭐ **`foldl` 的次数：对所有非零 `acc.2` 成立**——**不再需要 `1 ≤ deg`。**

**⚠ 归纳里按 `deg acc.2` 分两支：**
- **`deg = 0`**：用 `stepNat_totalDegree_zero`（第 39 轮），结果次数是 1；
- **`deg ≥ 1`**：用 `stepNat_snd_totalDegree`（第 33 轮），结果次数是 `1 + deg`。

**⚠ 关键：两支的结果都满足 `1 ≤` 与新次数，所以归纳假设可以在【同一形式**下递归。** -/
theorem foldl_step_totalDegree_any :
    ∀ (ls : ChainList) (acc : ℕ × MvPolynomial ℕ ℝ),
      acc.2 ≠ 0 →
      (ls.foldl (fun a _ => stepNat a) acc).2.totalDegree = acc.2.totalDegree + ls.length
  | [], acc, _ => by
      simp
  | l :: ls, acc, hne => by
      obtain ⟨off, p⟩ := acc
      simp only at hne
      rw [List.foldl_cons]
      by_cases h0 : p.totalDegree = 0
      · -- deg p = 0 支
        have hstep : (stepNat (off, p)).2.totalDegree = 1 :=
          stepNat_totalDegree_zero off p hne h0
        have hne' : (stepNat (off, p)).2 ≠ 0 := by
          intro h
          rw [h, MvPolynomial.totalDegree_zero] at hstep
          omega
        rw [foldl_step_totalDegree_any ls (stepNat (off, p)) hne']
        rw [hstep]
        simp only [List.length_cons]
        omega
      · -- deg p ≥ 1 支
        have h1 : 1 ≤ p.totalDegree := by omega
        have hstep : (stepNat (off, p)).2.totalDegree = 1 + p.totalDegree :=
          stepNat_snd_totalDegree off p hne h1
        have hne' : (stepNat (off, p)).2 ≠ 0 :=
          stepNat_snd_ne_zero off p hne h1
        rw [foldl_step_totalDegree_any ls (stepNat (off, p)) hne']
        rw [hstep]
        simp only [List.length_cons]
        omega

/-- ⭐⭐⭐ **链多项式的次数 = `deg p + 层数`，对【任意非零 `p`】**——**包括常数 `C x`。** -/
theorem chainNatPoly_totalDegree_any (ls : ChainList) (p : MvPolynomial ℕ ℝ)
    (hp : p ≠ 0) :
    (chainNatPoly ls p).totalDegree = p.totalDegree + ls.length := by
  simp only [chainNatPoly]
  exact foldl_step_totalDegree_any ls (0, p) hp


/-- ⭐ **`C x ≠ 0`**（当 `x ≠ 0`）。 -/
theorem C_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    (MvPolynomial.C x : MvPolynomial ℕ ℝ) ≠ 0 := by
  intro h
  have h0 : x = 0 := (MvPolynomial.C_inj ℝ x 0).mp (by rw [h, MvPolynomial.C_0])
  exact hx h0

/-- ⭐⭐ **标量输入的次数是 0**。 -/
theorem totalDegree_C_zero (x : ℝ) :
    (MvPolynomial.C x : MvPolynomial ℕ ℝ).totalDegree = 0 :=
  MvPolynomial.totalDegree_C x

/-- ⭐⭐⭐ **统一压顶定理**：**链的输出就是参数的一个显式多项式，
其次数【恰为层数**（当输入 `x ≠ 0`），**而它的求值就是网络的输出。**

**⚠ 第 37 轮那两条的分支合并版：第 40 轮的 `chainNatPoly_totalDegree_any`
取消了 `1 ≤ deg p` 的前提，于是 `C x` 也能带次数结论。** -/
theorem chainList_output_full {N : ℕ} (ls : ChainList)
    (hN : 0 + 2 * ls.length + 1 < N) {x : ℝ} (hx : x ≠ 0) :
    (chainNatPoly ls (MvPolynomial.C x)).totalDegree = ls.length
      ∧ ∀ (gN : Fin N → ℝ),
          (chainNatPoly ls (MvPolynomial.C x)).eval (fun k => readSlot gN k)
            = flatChainAct (N := N) (chainOneToChain (listToChainOne ls)) 0 gN
                (fun _ => x) (0 : Fin 1) := by
  constructor
  · rw [chainNatPoly_totalDegree_any ls (MvPolynomial.C x) (C_ne_zero_of_ne_zero hx),
      totalDegree_C_zero]
    omega
  · intro gN
    have hN' : 0 + 2 * chainOneDepth (listToChainOne ls) + 1 < N := by
      rw [chainOneDepth_listToChainOne]
      exact hN
    rw [chainNatPoly_eval_act]
    simp only [chainNatAct]
    rw [chainNatAct_eq_chainOneAct ls
      (0, (MvPolynomial.C x).eval (fun k => readSlot gN k)) gN]
    simp only [MvPolynomial.eval_C]
    exact chainOneAct_eq_flatChainAct (listToChainOne ls) 0 hN' gN x

/-- ⭐⭐⭐ **次数界是【紧】的**：**对每个 `d`，存在长度为 `d` 的层列表，
其输出多项式的次数恰为 `d`。** -/
theorem chainList_degree_attained {N : ℕ} (d : ℕ) (hN : 0 + 2 * d + 1 < N) :
    ∃ (ls : ChainList),
      ls.length = d
        ∧ (chainNatPoly ls (MvPolynomial.C 1)).totalDegree = d := by
  refine ⟨List.replicate d twoLayerProbeRest, List.length_replicate d twoLayerProbeRest, ?_⟩
  have := (chainList_output_full (List.replicate d twoLayerProbeRest)
    (by rw [List.length_replicate]; exact hN) one_ne_zero).1
  rw [this, List.length_replicate]


/-! ## ⭐⭐⭐ 宽度 > 1：多项式向量载体

**宽 1 时载体是【一个**多项式；宽 `b` 时一层的输出是 `b` 个多项式，
**⇒ 载体是 `Fin b → MvPolynomial ℕ ℝ`。**

**槽位约定与 `flatParamActSafe` 完全一致：`slotOf off a i j = off + i*a + j`。** -/

/-- ⭐ **有限和的次数界**——**每一项次数 ≤ `d` 则和 ≤ `d`。** -/
theorem totalDegree_finset_sum_le {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial ℕ ℝ) (d : ℕ) (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (∑ i ∈ s, f i).totalDegree ≤ d := by
  classical
  refine Finset.sum_induction f (fun p => p.totalDegree ≤ d) ?_ ?_ hf
  · intro x y hx hy
    refine le_trans (MvPolynomial.totalDegree_add x y) ?_
    rw [max_le_iff]
    exact ⟨hx, hy⟩
  · simp

/-- **一层作用在多项式向量上**——**与 `flatParamActSafe` 逐字对应。** -/
noncomputable def polyLayerStep (a b : ℕ) (off : ℕ) :
    (Fin a → MvPolynomial ℕ ℝ) → (Fin b → MvPolynomial ℕ ℝ) :=
  fun v j => (∑ i : Fin a, MvPolynomial.X (slotOf off b i.val j.val) * v i)
    + MvPolynomial.X (off + a * b + j.val)

/-- ⭐⭐ **一层的次数界**：**输入次数 ≤ `d` ⇒ 输出次数 ≤ `d + 1`。** -/
theorem polyLayerStep_totalDegree_le (a b : ℕ) (off : ℕ)
    (v : Fin a → MvPolynomial ℕ ℝ) (d : ℕ)
    (hv : ∀ i, (v i).totalDegree ≤ d) :
    ∀ j, (polyLayerStep a b off v j).totalDegree ≤ d + 1 := by
  intro j
  simp only [polyLayerStep]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  rw [max_le_iff]
  constructor
  · refine totalDegree_finset_sum_le Finset.univ _ (d + 1) ?_
    intro i _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_X]
    have := hv i
    omega
  · rw [MvPolynomial.totalDegree_X]
    omega


/-! ## ⭐⭐⭐ 宽度 > 1：链的多项式载体

**第 42 轮给出了【一层】**（`polyLayerStep`）**及其次数界。
本节把它沿链迭代。**

**⚠ 链的宽度是【依赖**的（每层的输入宽度 = 上一层的输出宽度），
所以载体用一个索引归纳类型 `PolyChain m n`，而【不是 `List`**。** -/

/-- **宽度依赖的链（多项式侧）**——**每层携带自己的输入／输出宽度。** -/
inductive PolyChain : ℕ → ℕ → Type
  | idf (n : ℕ) : PolyChain n n
  | cons {a b c : ℕ} : MLayer a b → PolyChain b c → PolyChain a c

/-- **层数**。 -/
def polyChainDepth : {m n : ℕ} → PolyChain m n → ℕ
  | _, _, .idf _ => 0
  | _, _, .cons _ rest => polyChainDepth rest + 1

/-- **参数槽位总数**（沿链累加）。 -/
def polyChainParamCount : {m n : ℕ} → PolyChain m n → ℕ
  | _, _, .idf _ => 0
  | _, _, .cons (a := a) (b := b) _ rest => layerParamCount a b + polyChainParamCount rest

/-- **链的多项式作用**——**`off` 是当前层的起始槽位。** -/
noncomputable def polyChainAct : {m n : ℕ} → (ch : PolyChain m n) → (off : ℕ) →
    (Fin m → MvPolynomial ℕ ℝ) → (Fin n → MvPolynomial ℕ ℝ)
  | _, _, .idf _, _, v => v
  | _, _, .cons (a := a) (b := b) l rest, off, v =>
      polyChainAct rest (off + layerParamCount a b)
        (polyLayerStep a b off v)

/-- ⭐⭐ **`idf` 支**——**定义级。** -/
theorem polyChainAct_idf (n off : ℕ) (v : Fin n → MvPolynomial ℕ ℝ) :
    polyChainAct (PolyChain.idf n) off v = v := rfl

/-- ⭐⭐ **`cons` 支**——**定义级。** -/
theorem polyChainAct_cons {a b c : ℕ} (l : MLayer a b) (rest : PolyChain b c)
    (off : ℕ) (v : Fin a → MvPolynomial ℕ ℝ) :
    polyChainAct (PolyChain.cons l rest) off v
      = polyChainAct rest (off + layerParamCount a b) (polyLayerStep a b off v) := rfl


/-- ⭐⭐⭐ **链的次数界**：**若每个输入坐标的次数 ≤ `d`，则每个输出坐标的次数 ≤ `d + 层数`。**

**⚠ 这是第 42 轮单层界沿链的迭代——无关于宽度。** -/
theorem polyChainAct_totalDegree_le {m n : ℕ} : (ch : PolyChain m n) → (off : ℕ) →
    (v : Fin m → MvPolynomial ℕ ℝ) → (d : ℕ) →
    (∀ i, (v i).totalDegree ≤ d) →
    ∀ j, (polyChainAct ch off v j).totalDegree ≤ d + polyChainDepth ch
  | .idf _, off, v, d, hv, j => by
      simp only [polyChainAct, polyChainDepth]
      exact hv j
  | .cons (a := a) (b := b) l rest, off, v, d, hv, j => by
      simp only [polyChainAct, polyChainDepth]
      have hstep : ∀ i, (polyLayerStep a b off v i).totalDegree ≤ d + 1 :=
        fun i => polyLayerStep_totalDegree_le a b off v d hv i
      have ih := polyChainAct_totalDegree_le rest (off + layerParamCount a b)
        (polyLayerStep a b off v) (d + 1) hstep j
      omega


/-! ## ⚠⚠ 第 44 轮：宽 > 1 对接的两步，第二步需要【非线性】算术

## 拆成两步

「polyLayerStep」的变量下标是 ℕ，而「flatParamActSafe」的「g」是 Fin N → ℝ。
∴ 分两步：

1. 「polyLayerStep_eval」：求值等于 「natParamAct」（ℕ 下标的数值作用）；
2. 「natParamAct_eq_flatParamActSafe」：两者在 g := readSlot gN 下一致。

## 第一步本轮已经通过

所用的关键引理是 「MvPolynomial.eval_sum」（不是我以为的 eval_finset_sum）。
配 eval_add、eval_mul、eval_X 与 Finset.sum_congr rfl，证明是三行。

## 第二步卡在：「slotOf」的界需要非线性推理

要证 slotOf off a i j < N，已知：

- i < a、j < b（Fin 的内建约束）；
- off + a * b + b ≤ N（即 hN）。

而 slotOf off a i j = off + i * a + j。∴ 需要 i * a + j < a * b + b，
那是一个【乘法】不等式。

⚠ omega 做不到——它是线性算术。
它报出的反例约束正是缺了 i*a 与 a*b 的关系。

⇒ 修法：先证一条纯算术引理

    theorem slotOf_lt {a b i j : ℕ} (hi : i < a) (hj : j < b) (off : ℕ) :
        slotOf off a i j < off + a * b + b

⚠ 而那条引理本身也需要非线性推理：i * a + j < a * b + b
由 i * a ≤ (a-1) * a 与 j ≤ b-1 得到——两步都需要乘法单调性。

⇒ 下一轮的第一件事：写那条 slotOf_lt 的纯算术引理，
用 nlinarith 或 Nat.mul_lt_mul_of_lt_of_le 一类的引理。

## 结论

本轮没有代码入库（回退到 744）。
第一步已验证可通过，第二步的障碍是一条纯算术引理。 -/


/-- ⭐⭐ **槽位算术界**：**`slotOf off b i j < off + a*b + b`**（当 `i < a`、`j < b`）。

**⚠ 关键：`slotOf` 的行步长是 `b`（输出宽度），这是 `flatParamActSafe` 的约定。
第 45 轮发现 `polyLayerStep` 原先写的 `slotOf off a …` 是【错的**，已修正。** -/
theorem slotOf_lt_bound {a b i j : ℕ} (hi : i < a) (hj : j < b) (off : ℕ) :
    slotOf off b i j < off + a * b + b := by
  simp only [slotOf]
  have h1 : i * b ≤ (a - 1) * b := Nat.mul_le_mul_right b (by omega)
  have h2 : j ≤ b - 1 := by omega
  have h3 : (a - 1) * b + (b - 1) < a * b + b := by
    have ha : 1 ≤ a := by omega
    have key : a * b = (a - 1) * b + b := by
      conv_lhs => rw [← Nat.sub_add_cancel ha]
      ring
    omega
  omega

/-- **`ℕ` 下标的数值层作用**——**与 `polyLayerStep` 逐字对应。** -/
noncomputable def natParamAct (a b off : ℕ) (g : ℕ → ℝ) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i : Fin a, g (slotOf off b i.val j.val) * x i) + g (off + a * b + j.val)

/-- ⭐⭐⭐ **一层的求值一致**：**`polyLayerStep` 的求值 = `natParamAct`。** -/
theorem polyLayerStep_eval (a b off : ℕ) (v : Fin a → MvPolynomial ℕ ℝ)
    (g : ℕ → ℝ) (j : Fin b) :
    (polyLayerStep a b off v j).eval g
      = natParamAct a b off g (fun i => (v i).eval g) j := by
  simp only [polyLayerStep, natParamAct]
  rw [MvPolynomial.eval_add, MvPolynomial.eval_sum, MvPolynomial.eval_X]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]

/-- ⭐⭐⭐ **`ℕ` 数值作用与 `flatParamActSafe` 一致**——**`g` 取 `readSlot gN`。** -/
theorem natParamAct_eq_flatParamActSafe {N : ℕ} (a b off : ℕ) (gN : Fin N → ℝ)
    (x : Fin a → ℝ) (hN : off + a * b + b ≤ N) :
    natParamAct a b off (fun k => readSlot gN k) x
      = flatParamActSafe (N := N) (a := a) (b := b) off gN x := by
  funext j
  simp only [natParamAct, flatParamActSafe]


/-- **`PolyChain` → `Chain` 的翻译**——**两者的唯一关系，是一个函数。** -/
def polyChainToChain : {m n : ℕ} → PolyChain m n → Chain m n
  | _, _, .idf _ => Chain.idf _
  | _, _, .cons l rest => Chain.cons l (polyChainToChain rest)

/-- ⭐ **翻译保持层数**——**`chainDepth` 与 `polyChainDepth` 一致。** -/
theorem chainDepth_polyChainToChain {m n : ℕ} (ch : PolyChain m n) :
    chainDepth (polyChainToChain ch) = polyChainDepth ch := by
  induction ch with
  | idf k => rfl
  | cons l rest ih =>
      simp only [polyChainToChain, polyChainDepth, chainDepth_cons, ih]


/-- ⭐⭐⭐ **整体桥接**：**`polyChainAct` 逐点求值 = `flatChainAct`。**

**⚠ 第 45 轮逐层桥接沿链的提升。`g` 取 `readSlot gN`，
`hN : off + polyChainParamCount ch + 1 ≤ N` 保证所有槽位在 `N` 内。** -/
theorem polyChainAct_eval {N : ℕ} : {m n : ℕ} → (ch : PolyChain m n) → (off : ℕ) →
    (v : Fin m → MvPolynomial ℕ ℝ) → (gN : Fin N → ℝ) →
    (hN : off + polyChainParamCount ch + 1 ≤ N) →
    ∀ j, (polyChainAct ch off v j).eval (fun k => readSlot gN k)
      = flatChainAct (N := N) (polyChainToChain ch) off gN
          (fun i => (v i).eval (fun k => readSlot gN k)) j
  | _, _, .idf _, off, v, gN, hN, j => by
      simp only [polyChainAct, polyChainToChain, flatChainAct]
  | _, _, .cons (a := a) (b := b) l rest, off, v, gN, hN, j => by
      -- 展开 hN 与两边
      have hN' : off + layerParamCount a b + polyChainParamCount rest + 1 ≤ N := by
        simp only [polyChainParamCount] at hN
        omega
      have hcur : off + a * b + b ≤ N := by
        have hpc : layerParamCount a b = a * b + b := rfl
        omega
      simp only [polyChainAct, polyChainToChain, flatChainAct, polyChainParamCount]
      -- 用归纳假设
      rw [polyChainAct_eval rest (off + layerParamCount a b)
        (polyLayerStep a b off v) gN (by simpa using hN')]
      -- 现在需要把左边的求值换成 flatParamActSafe
      congr 1
      funext i
      exact (polyLayerStep_eval a b off v (fun k => readSlot gN k) i).trans
        (congrFun (natParamAct_eq_flatParamActSafe a b off gN
          (fun i => (v i).eval (fun k => readSlot gN k)) hcur) i)


/-- ⭐⭐⭐ **宽度 > 1 的压顶定理**：**任意宽度 `m → n` 的链，其输出就是参数的显式多项式向量，
每个坐标的次数 ≤ 输入次数 + 层数，且该向量的求值就是网络的输出。**

**⚠ 这是第 41 轮宽度 1 压顶定理的任意宽度推广——
把第 43 轮的次数界（`polyChainAct_totalDegree_le`）与
第 47 轮的求值一致（`polyChainAct_eval`）合成【一条**。** -/
theorem polyChain_output_full {N m n : ℕ} (ch : PolyChain m n) (off : ℕ)
    (v : Fin m → MvPolynomial ℕ ℝ) (d : ℕ) (hv : ∀ i, (v i).totalDegree ≤ d)
    (gN : Fin N → ℝ) (hN : off + polyChainParamCount ch + 1 ≤ N) :
    (∀ j, (polyChainAct ch off v j).totalDegree ≤ d + polyChainDepth ch)
      ∧ ∀ j, (polyChainAct ch off v j).eval (fun k => readSlot gN k)
          = flatChainAct (N := N) (polyChainToChain ch) off gN
              (fun i => (v i).eval (fun k => readSlot gN k)) j :=
  ⟨polyChainAct_totalDegree_le ch off v d hv,
    polyChainAct_eval ch off v gN hN⟩

/-- ⭐⭐ **压顶（以常数输入）**：**宽度 1 的输入 `C x` 时，次数恰为层数。**

**⚠ 这是宽度 > 1 框架对第 41 轮结果的【复核**：
取 `m = 1`、`v = fun _ => C x`，则 `d = 0`，次数 ≤ 层数。** -/
theorem polyChain_output_width_one {N n : ℕ} (ch : PolyChain 1 n) (off : ℕ)
    (x : ℝ) (gN : Fin N → ℝ) (hN : off + polyChainParamCount ch + 1 ≤ N) :
    (∀ j, (polyChainAct ch off (fun _ => MvPolynomial.C x) j).totalDegree
        ≤ polyChainDepth ch)
      ∧ ∀ j, (polyChainAct ch off (fun _ => MvPolynomial.C x) j).eval
          (fun k => readSlot gN k)
          = flatChainAct (N := N) (polyChainToChain ch) off gN
              (fun _ => x) j := by
  have hv : ∀ i : Fin 1,
      ((fun _ : Fin 1 => (MvPolynomial.C x : MvPolynomial ℕ ℝ)) i).totalDegree ≤ 0 := by
    intro i
    simp [totalDegree_C_zero]
  have := polyChain_output_full ch off
    (fun _ : Fin 1 => (MvPolynomial.C x : MvPolynomial ℕ ℝ)) 0 hv gN hN
  refine ⟨fun j => ?_, ?_⟩
  · have h1 := this.1 j
    omega
  · intro j
    have h2 := this.2 j
    have h3 : (fun i : Fin 1 =>
        ((fun _ : Fin 1 => (MvPolynomial.C x : MvPolynomial ℕ ℝ)) i).eval
          (fun k => readSlot gN k)) = (fun _ => x) := by
      funext i
      simp
    rw [h3] at h2
    exact h2

/-! Round 49: reverse direction attempted.

Attempted: coeff (Finsupp.single off 1) (X off * C c + X (off+1)) = c,
the atomic step of reading a weight back out of its polynomial.

Obstacles: the definition needs noncomputable, and the docstring needed its
closing marker. Both are one-line fixes; this round's fix scripts failed to
match their search strings.

Design finding: the bias is NOT among the coefficients. A layer polynomial is
X off * C c + X (off+1), so the bias slot carries coefficient 1 and its VALUE
is read from g at evaluation time. Hence the correct reverse statement concerns
STRUCTURAL POSITIONS, already given by polyChainParamCount, slotOf and
layerParamCount, rather than coefficient recovery.

No code in the tree this round.
-/


/-- A one-layer polynomial: `X off * C c + X (off+1)`. -/
noncomputable def oneLayerPolyNat (off : ℕ) (c : ℝ) : MvPolynomial ℕ ℝ :=
  MvPolynomial.X off * MvPolynomial.C c + MvPolynomial.X (off + 1)

/-- The weight coefficient of a one-layer polynomial: `c` at `X off`.

This is the atomic step of the reverse direction: the forward direction writes the
weight into the polynomial, this reads it back. -/
theorem oneLayerPolyNat_coeff_weight (off : ℕ) (c : ℝ) :
    MvPolynomial.coeff (Finsupp.single off 1) (oneLayerPolyNat off c) = c := by
  simp only [oneLayerPolyNat]
  rw [MvPolynomial.coeff_add]
  have h1 : MvPolynomial.coeff (Finsupp.single off 1)
      (MvPolynomial.X off * MvPolynomial.C c : MvPolynomial ℕ ℝ) = c := by
    have heq : (MvPolynomial.X off * MvPolynomial.C c : MvPolynomial ℕ ℝ)
        = MvPolynomial.C c * MvPolynomial.X off := by ring
    rw [heq, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    ring
  have h2 : MvPolynomial.coeff (Finsupp.single off 1)
      (MvPolynomial.X (off + 1) : MvPolynomial ℕ ℝ) = 0 := by
    rw [MvPolynomial.coeff_X']
    have hne : (Finsupp.single (off + 1) 1 : ℕ →₀ ℕ) ≠ Finsupp.single off 1 := by
      rw [Ne, Finsupp.single_eq_single_iff]
      omega
    simp [hne]
  rw [h1, h2, add_zero]


/-- Weight slots live strictly below the bias block: slotOf off b i j < off + a*b.

This is the position-structure fact behind the reverse direction: which slots are
weights and which are biases is decided by ARITHMETIC on the shape, never by
inspecting coefficients. -/
theorem slotOf_weight_lt {a b i j off : Nat} (hi : i < a) (hj : j < b) :
    slotOf off b i j < off + a * b := by
  simp only [slotOf]
  have h2 : i * b + b <= a * b := by
    have h := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hi)
    simpa [Nat.succ_mul] using h
  omega

/-- The bias slot is exactly where the weight block ends. -/
theorem bias_slot_eq_slotOf (off a b j : Nat) :
    off + a * b + j = slotOf off b a j := by
  simp only [slotOf]


/-- stepNat on a constant input reads its weight coefficient back.

The forward step takes `C c` to `X off * C c + X (off+1)`; this recovers `c` from
the result. This is the reverse direction at the level of one step. -/
theorem stepNat_coeff_weight (off : ℕ) (c : ℝ) :
    MvPolynomial.coeff (Finsupp.single off 1)
      ((stepNat (off, MvPolynomial.C c)).2) = c := by
  simp only [stepNat, oneLayerPolyNat]
  exact oneLayerPolyNat_coeff_weight off c

/-- The bias slot carries coefficient 1, not the bias value.

Round 49's design finding as a theorem: the bias is recorded POSITIONALLY, and its
value is read from g only at evaluation time. -/
theorem stepNat_coeff_bias (off : ℕ) (c : ℝ) :
    MvPolynomial.coeff (Finsupp.single (off + 1) 1)
      ((stepNat (off, MvPolynomial.C c)).2) = 1 := by
  simp only [stepNat, oneLayerPolyNat]
  rw [MvPolynomial.coeff_add]
  have h1 : MvPolynomial.coeff (Finsupp.single (off + 1) 1)
      (MvPolynomial.X off * MvPolynomial.C c : MvPolynomial ℕ ℝ) = 0 := by
    have heq : (MvPolynomial.X off * MvPolynomial.C c : MvPolynomial ℕ ℝ)
        = MvPolynomial.C c * MvPolynomial.X off := by ring
    rw [heq, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    have hne : (Finsupp.single off 1 : ℕ →₀ ℕ)
        ≠ Finsupp.single (off + 1) 1 := by
      rw [Ne, Finsupp.single_eq_single_iff]
      omega
    simp [hne]
  have h2 : MvPolynomial.coeff (Finsupp.single (off + 1) 1)
      (MvPolynomial.X (off + 1) : MvPolynomial ℕ ℝ) = 1 := by
    rw [MvPolynomial.coeff_X']
    simp
  rw [h1, h2, zero_add]


/-- A constant polynomial has zero coefficient at every nonzero monomial. -/
theorem coeff_C_of_ne_zero (c : ℝ) {m : ℕ →₀ ℕ} (hm : m ≠ 0) :
    MvPolynomial.coeff m (MvPolynomial.C c : MvPolynomial ℕ ℝ) = 0 := by
  rw [MvPolynomial.coeff_C]
  rw [if_neg (Ne.symm hm)]

/-- The empty chain returns its input unchanged, so its coefficients are the input's. -/
theorem chainNatPoly_nil (p : MvPolynomial ℕ ℝ) :
    chainNatPoly [] p = p := by
  simp [chainNatPoly]

/-- A single step already recovers the weight from the output polynomial.

This is the reverse direction at chain level for a one-element chain: forward writes
the weight into slot 0, and this reads it back from the SAME slot of the output. -/
theorem chainNatPoly_single_coeff_weight (l : MLayer 1 1) (c : ℝ) :
    MvPolynomial.coeff (Finsupp.single 0 1)
      (chainNatPoly [l] (MvPolynomial.C c))
      = c := by
  simp only [chainNatPoly, List.foldl_cons, List.foldl_nil]
  exact stepNat_coeff_weight 0 c

/-- The same step records the bias positionally: its slot carries coefficient 1. -/
theorem chainNatPoly_single_coeff_bias (l : MLayer 1 1) (c : ℝ) :
    MvPolynomial.coeff (Finsupp.single 1 1)
      (chainNatPoly [l] (MvPolynomial.C c))
      = 1 := by
  simp only [chainNatPoly, List.foldl_cons, List.foldl_nil]
  exact stepNat_coeff_bias 0 c


/-- After `stepNat` from offset 0, slot 0's coefficient is inherited from the input's
constant coefficient.

This generalises `stepNat_coeff_weight` away from the constant-input case. -/
theorem stepNat_coeff_zero_of_no_const (p : MvPolynomial ℕ ℝ) (c : ℝ)
    (hp : MvPolynomial.coeff 0 p = c) :
    MvPolynomial.coeff (Finsupp.single 0 1) ((stepNat (0, p)).2) = c := by
  simp only [stepNat]
  rw [MvPolynomial.coeff_add]
  have h1 : MvPolynomial.coeff (Finsupp.single 0 1)
      (MvPolynomial.X 0 * p : MvPolynomial ℕ ℝ) = MvPolynomial.coeff 0 p := by
    have heq : (MvPolynomial.X 0 * p : MvPolynomial ℕ ℝ)
        = p * MvPolynomial.X 0 := by ring
    rw [heq]
    have := MvPolynomial.coeff_mul_X (0 : ℕ →₀ ℕ) 0 p
    simpa using this
  have h2 : MvPolynomial.coeff (Finsupp.single 0 1)
      (MvPolynomial.X (0 + 1) : MvPolynomial ℕ ℝ) = 0 := by
    rw [MvPolynomial.coeff_X']
    have hne : (Finsupp.single 1 1 : ℕ →₀ ℕ)
        ≠ Finsupp.single 0 1 := by
      rw [Ne, Finsupp.single_eq_single_iff]
      omega
    simp [hne]
  rw [h1, h2, add_zero, hp]


/-! ## Round 54: the positional fact behind multi-layer extraction, and its exact proof

## The fact

**Multi-layer extraction reduces to one positional observation:**

    At offset >= 2, a step cannot touch slot 0.

**Reason**: a step writes `X off * p + X (off+1)`, and both factors carry a variable
index >= 2, so neither can contribute to the monomial `single 0 1`.

**Formally**:

    theorem stepNat_coeff_zero_irrelevant (off : Nat) (hoff : 2 <= off)
        (p : MvPolynomial Nat Real) :
        MvPolynomial.coeff (Finsupp.single 0 1) ((stepNat (off, p)).2)
          = MvPolynomial.coeff (Finsupp.single 0 1) p

## Why this round did not land it

**The needed sub-fact is `coeff (single 0 1) (X off * p) = 0` for `off >= 1`.**

**I tried `coeff_mul_X`, whose pattern is `coeff (m + single s 1) (p * X s)` --
but here the monomial is `single 0 1`, which is NOT of the form `m + single off 1`
for `off >= 1`, so the rewrite does not apply.**

**Then I tried `coeff_mul` with `Finset.sum_eq_single 0`, and the side conditions
required `Finsupp.single_add_single_one`, which does not exist.**

## The proof that should work next round

**`coeff_mul` expands to a sum over `Finset.antidiagonal (single 0 1)`. Since
`single 0 1` has total degree 1, that antidiagonal is exactly
`{(0, single 0 1), (single 0 1, 0)}`. Both cross terms with `X off` vanish because
`coeff m (X off) = 0` whenever `m != single off 1`, and `off >= 2` makes
`single off 1 != 0` and `!= single 0 1`.**

**So the proof is: enumerate the antidiagonal (it has two elements), discharge both
with `coeff_X'` and `omega`-style index arithmetic, done.**

**A shorter route, if it exists**: mathlib likely has a lemma stating that
`coeff m (X s * p) = 0` when `m s = 0`. That is exactly the case here (`off >= 2`
means `single 0 1` has exponent 0 at `off`). **=> next round should `#check` for a
name like `coeff_X_mul_of_not_mem` / `coeff_mul_X_of_ne` before writing the
enumeration by hand.**

## Conclusion

**No code in the tree this round (reverted to 755).**

**=> the multi-layer extractor is ONE positional sub-fact away, and the sub-fact has
a two-case antidiagonal proof or a one-line library lemma behind it.**
-/


/-! ## Round 55: the library lemma found, and a CORRECTION to round 54's claim

## The lemma round 54 was looking for

**Enumeration found it:**

    MvPolynomial.coeff_X_mul' (m : sigma ->0 Nat) (s : sigma) (p : MvPolynomial sigma R) :
        coeff m (X s * p) = if s in m.support then coeff (m - single s 1) p else 0

**With `m = single 0 1` and `s = off >= 2`: the support of `single 0 1` is `{0}`, so `off` is NOT in it, and the
coefficient is 0.**

**This is exactly the sub-fact round 54 named but could not locate.**

## But the correction: round 54's STATEMENT was wrong

**Round 54 proposed:**

    coeff (single 0 1) (stepNat (off, p)).2 = coeff (single 0 1) p

**That is FALSE.** **With `off >= 2`, both terms of `stepNat` contribute 0 at slot 0 --
`X off * p` because `off` is not in the support of `single 0 1`, and `X (off+1)` because its own support is
`single (off+1) 1`.**

**=> so the right statement is:**

    theorem stepNat_coeff_zero_irrelevant (off : Nat) (hoff : 2 <= off)
        (p : MvPolynomial Nat Real) :
        MvPolynomial.coeff (Finsupp.single 0 1) ((stepNat (off, p)).2) = 0

**And that is even BETTER for extraction**: **it says later layers write NOTHING to slot 0**, so the first layer's
weight placed there by `stepNat (0, ...)` survives untouched through the whole foldl.**

## Why this round still did not land it

**My edit script replaced `rw [h1, h2, add_zero]` GLOBALLY, and that line also occurs in an earlier theorem
(`totalDegree_X_mul_C_add_X_zero_nat`), which it corrupted.**
**The build then failed at line 4337, far from the edit site.**

**=> the same global-replace hazard as round 32, in a different guise: not a global TEXT replace, but a global
STRING replace inside a patch script.** **The fix is to scope each replacement to a unique anchor.**

## The proof that will work

    theorem stepNat_coeff_zero_irrelevant (off : Nat) (hoff : 2 <= off)
        (p : MvPolynomial Nat Real) :
        MvPolynomial.coeff (Finsupp.single 0 1) ((stepNat (off, p)).2) = 0 := by
      simp only [stepNat]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_X_mul']
      have hnotmem : off notin (Finsupp.single 0 1 : Nat ->0 Nat).support := ...
      rw [if_neg hnotmem, MvPolynomial.coeff_X']
      ...

**`hnotmem` follows from `Finsupp.support_single_ne_zero` plus `omega` on `off >= 2`.**

## Conclusion

**No code in the tree this round (reverted to 756).**

**=> next round: apply the corrected statement with a SCOPED patch, then the multi-layer extractor is an induction
away.**
-/


/-- At offset >= 2, a step writes NOTHING to slot 0.

The positional fact behind multi-layer extraction: a later layer writes to slots >= 2,
so the first layer's weight at slot 0 is never overwritten by the rest of the foldl.

Round 54 proposed the false statement `= coeff (single 0 1) p`; both terms of `stepNat`
in fact contribute 0 there, so the coefficient is 0 outright.

The key lemma is `MvPolynomial.coeff_X_mul'`:
    coeff m (X s * p) = if s in m.support then coeff (m - single s 1) p else 0
-/
theorem stepNat_coeff_zero_irrelevant (off : ℕ) (hoff : 2 ≤ off)
    (p : MvPolynomial ℕ ℝ) :
    MvPolynomial.coeff (Finsupp.single 0 1) ((stepNat (off, p)).2) = 0 := by
  simp only [stepNat]
  rw [MvPolynomial.coeff_add]
  have hnotmem : off ∉ (Finsupp.single 0 1 : ℕ →₀ ℕ).support := by
    have h : (Finsupp.single 0 1 : ℕ →₀ ℕ).support = {0} := by
      rw [Finsupp.support_single_ne_zero]
      simp
    rw [h]
    simp only [Finset.mem_singleton]
    omega
  have h1 : MvPolynomial.coeff (Finsupp.single 0 1)
      (MvPolynomial.X off * p : MvPolynomial ℕ ℝ) = 0 := by
    rw [MvPolynomial.coeff_X_mul', if_neg hnotmem]
  have h2 : MvPolynomial.coeff (Finsupp.single 0 1)
      (MvPolynomial.X (off + 1) : MvPolynomial ℕ ℝ) = 0 := by
    rw [MvPolynomial.coeff_X']
    have hne : (Finsupp.single (off + 1) 1 : ℕ →₀ ℕ)
        ≠ Finsupp.single 0 1 := by
      rw [Ne, Finsupp.single_eq_single_iff]
      omega
    simp [hne]
  rw [h1, h2, add_zero]


/-- Slot 0 is dead once the offset is >= 2: the foldl preserves a zero there.

The statement carries BOTH hypotheses -- offset >= 2 AND slot 0 already zero -- because
the empty list returns its accumulator unchanged, so neither hypothesis alone suffices.

The cons case uses `stepNat_coeff_zero_irrelevant` to re-establish the zero for the tail,
while `stepNat` keeps the offset at >= 2. -/
theorem foldl_coeff_zero_irrelevant :
    ∀ (ls : List (MLayer 1 1)) (off : ℕ) (p : MvPolynomial ℕ ℝ),
      2 ≤ off → MvPolynomial.coeff (Finsupp.single 0 1) p = 0 →
      MvPolynomial.coeff (Finsupp.single 0 1)
        ((ls.foldl (fun acc _ => stepNat acc) (off, p)).2) = 0
  | [], off, p, hoff, hp => by
      simp only [List.foldl_nil]
      exact hp
  | l :: ls, off, p, hoff, hp => by
      rw [List.foldl_cons]
      have h2 : 2 ≤ (stepNat (off, p)).1 := by
        simp only [stepNat]
        omega
      have hz : MvPolynomial.coeff (Finsupp.single 0 1) ((stepNat (off, p)).2) = 0 :=
        stepNat_coeff_zero_irrelevant off hoff p
      exact foldl_coeff_zero_irrelevant ls (stepNat (off, p)).1 (stepNat (off, p)).2 h2 hz


/-! ## Round 58: a CORRECTION -- slot 0 is ZEROED, not preserved

## What rounds 56 and 57 assumed

**Round 56 proved `stepNat (off, p)` has coefficient 0 at slot 0 whenever `off >= 2`.**
**Round 57 lifted that to the whole foldl: `foldl_coeff_zero_irrelevant` says that once the
offset is >= 2 AND slot 0 is already zero, the rest of the list keeps it zero.**

**Both are correct. But this round tried to conclude something they do not give.**

## The false step

**I wanted: "the first layer writes `c` at slot 0, and later layers preserve it".**

**That requires preserving a NONZERO slot 0. But `stepNat (off, p)` at `off >= 2` sets slot 0
to ZERO -- it does not preserve whatever was there. So:**

    coeff (single 0 1) (stepNat (off, p)).2 = 0        (off >= 2)
    coeff (single 0 1) p = c                            (hypothesis)

**These are compatible ONLY when `c = 0`.** **A general "preservation" lemma with arbitrary
`c` is therefore FALSE, and my draft's induction step was looking for a contradiction
where none exists.**

## What this means for the extractor

**`chainNatPoly (l :: ls) (C c)` places `c` at slot 0 in the FIRST step; the SECOND step,
running at offset 2, zeroes it. So the final slot 0 carries no trace of the first layer
whenever the list has length >= 2.**

**=> slot 0 is NOT the right slot to read a deep chain's weights from.**

**=> the multi-layer extractor needs a different positional argument: the coefficient at
`single (2k) 1` (the k-th weight slot) is only touched by steps whose offset is exactly
`2k`, which happens exactly once along the foldl.**

## The corrected next step

**State the invariant per slot, not for slot 0 alone:**

    for the k-th layer's weight slot (2k), every step other than the k-th has offset != 2k,
    so by the same `coeff_X_mul'` argument it contributes 0 there.

**=> the general statement is "coefficient at slot 2k of the final polynomial equals the
k-th layer's weight", proved by an induction that tracks BOTH the accumulated offset and
the target slot.**

**That is a bigger induction than the one rounds 56-57 set up, and it replaces them rather
than extending them.**

## Conclusion

**No code in the tree this round (reverted to 759).**

**Rounds 56 and 57 remain correct as stated -- round 57's lemma is a genuine theorem about
zeros. What was wrong was the APPLICATION I was about to build on top of them.**
-/



/-- A step at offset `m` writes nothing to slot `2k` when `m != 2k` and `m + 1 != 2k`.

Generalises round 56 from slot 0 to an arbitrary slot: the two monomials `X m` and
`X (m+1)` are the only places a step touches, so any OTHER slot is untouched.

This is the per-slot argument round 58 identified as the right one. -/
theorem stepNat_coeff_other_slot (m : ℕ) (p : MvPolynomial ℕ ℝ)
    (s : ℕ →₀ ℕ) (hs : s ≠ 0)
    (h1 : m ∉ s.support) (h2 : m + 1 ∉ s.support) :
    MvPolynomial.coeff s ((stepNat (m, p)).2) = 0 := by
  simp only [stepNat]
  rw [MvPolynomial.coeff_add]
  have hx1 : MvPolynomial.coeff s (MvPolynomial.X m * p : MvPolynomial ℕ ℝ) = 0 := by
    rw [MvPolynomial.coeff_X_mul', if_neg h1]
  have hx2 : MvPolynomial.coeff s (MvPolynomial.X (m + 1) : MvPolynomial ℕ ℝ) = 0 := by
    rw [MvPolynomial.coeff_X']
    have hne : (Finsupp.single (m + 1) 1 : ℕ →₀ ℕ) ≠ s := by
      intro h
      apply h2
      rw [← h]
      exact Finsupp.mem_support_iff.mpr (by simp)
    simp [hne]
  rw [hx1, hx2, add_zero]



/-! ## Round 60: the fold needs to carry `coeff s p`, not just the zero

## What was attempted

**Round 59 proved `stepNat_coeff_other_slot`: a step at offset `m` gives coefficient 0 at
any `s` whose support avoids both `m` and `m+1`.**

**This round tried to fold it: "if every step's offset avoids `s`, then the whole foldl
preserves `coeff s p`."**

## Why that is FALSE as an induction

**The step gives `coeff s (stepNat (off, p)).2 = 0`, NOT `= coeff s p`.**

**The induction's cons case then needs `coeff s p = 0`, which does not follow from
`off notin s.support` -- `p` is an arbitrary polynomial, and `s` avoiding `off` says
nothing about whether `p` has a term at `s`.**

**Concretely: the theorem I wrote ended with `exact hz` where the goal was
`coeff s (stepNat (off, p)).2 = coeff s p`, i.e. `0 = coeff s p`. No hypothesis supplies
that.**

## The corrected statement

**The fold invariant must carry the target value, not just aim at zero:**

    forall (ls) (off) (p) (s),
      (forall k < ls.length,
         off + 2*k notin s.support and off + 2*k + 1 notin s.support) ->
      coeff s ((ls.foldl step (off, p)).2) = coeff s p

**The cons case then goes through a DIFFERENT lemma:**

    stepNat_coeff_other_slot_preserves :
        off notin s.support -> off + 1 notin s.support ->
        coeff s ((stepNat (off, p)).2) = coeff s p

**which is NOT round 59's lemma -- round 59's lemma additionally assumed `s != 0` to kill
the `X (off+1)` term, whereas preservation must handle the case `s = single (off+1) 1`
SEPARATELY (in which case the `X (off+1)` term contributes 1, so preservation fails and
the precondition correctly excludes it).**

**So the preservation lemma needs: `off notin s.support` AND `off + 1 notin s.support`,
plus the observation that `X (off+1)`'s support is `single (off+1) 1`, whose only element
`off+1` is excluded by hypothesis -- hence that term is 0 and the product term reduces to
`coeff s p` by `coeff_X_mul'`.**

## Conclusion

**No code in the tree this round (reverted to 761).**

**Round 59 remains correct. What this round establishes is that the FOLD needs a
preservation lemma rather than a vanishing lemma, and the preservation form is
`coeff s ((stepNat (off, p)).2) = coeff s p`, provable from the same two support
hypotheses.**

**=> next round: state and prove `stepNat_coeff_preserved`, then the fold by induction.**
-/



/-! ## Round 61: `coeff_X_mul'` gives ZERO, not `coeff s p` -- a misreading

## What round 60 proposed

**Round 60 concluded that the fold needs a PRESERVATION lemma**

    coeff s ((stepNat (off, p)).2) = coeff s p       (for off, off+1 notin s.support)

**and argued that `X off * p`'s coefficient at `s` "reduces by `coeff_X_mul'` to
`coeff s p`".**

**That is a misreading of `coeff_X_mul'`, and this round hit it head on.**

## What `coeff_X_mul'` actually says

    coeff_X_mul' (m : sigma ->0 Nat) (s : sigma) (p : MvPolynomial sigma R) :
        coeff m (X s * p) = if s in m.support then coeff (m - single s 1) p else 0

**In the notation of our goal: with `m := s` (the target monomial) and `s := off`
(the variable), and `off notin s.support`, the result is ZERO -- not `coeff s p`.**

**The `else 0` branch is exactly the case `off notin s.support`.**

**=> so `X off * p` contributes 0 at any `s` whose support omits `off`.**
**That is the SAME content as round 59's lemma, and it means the product term does NOT
carry `p`'s coefficient at `s` through.**

## What this implies

**The true behaviour of a step at offset `off` at a slot `s` avoiding `off` and `off+1`:**

    coeff s (stepNat (off, p)).2 = 0

**-- a VANISHING, not a preservation.** **Round 59's lemma was right after all; round 60's
"correction" was itself the error, and it was caused by reading `coeff_X_mul'`'s `else`
branch as if it were the `then` branch.**

**=> the fold statement must therefore be about SLOTS THAT ARE LATER THAN THE OFFSET, and
the extraction argument cannot be "the k-th weight survives"; it must be "the k-th weight
is CREATED at the k-th step and then DESTROYED by the next one" -- which means the final
polynomial carries, at slot 2k, the value produced by step k+1, not step k.**

## Where that leaves the extractor

**`chainNatPoly` cannot be inverted by reading individual coefficients of the final
polynomial directly: each slot holds the residue of the step AFTER the one that wrote the
weight.**

**=> the reverse direction needs either (a) intermediate polynomials, not just the final
one, or (b) a different encoding in which each weight occupies a slot that no later step
touches (e.g. reserving slot `2k` and shifting later steps past it).**

**Option (b) is a change to `stepNat`'s slot assignment, i.e. an architecture-level change;
per the project rule it would go on a branch.**

## Honest accounting

**No code in the tree this round (reverted to 762).**

**The value of this round is entirely negative and entirely definite: it fixes which of
rounds 59/60 is correct (59) and identifies that the obstacle is the SLOT ASSIGNMENT, not
the proof strategy.**
-/



/-- The intermediate polynomials of a foldl: the accumulator's polynomial after each
prefix of the layer list.

This is the object round 61 identified as the right one for the reverse direction:
because each step's contribution to slot `2k` is destroyed by the NEXT step, only the
INTERMEDIATE polynomial carries the k-th layer's weight. -/
noncomputable def chainNatPolyAfter (ls : List (MLayer 1 1)) (p : MvPolynomial ℕ ℝ)
    (k : ℕ) : MvPolynomial ℕ ℝ :=
  (((ls.take k).foldl (fun acc _ => stepNat acc) (0, p))).2

/-- After zero layers, the polynomial is the input. -/
theorem chainNatPolyAfter_zero (ls : List (MLayer 1 1)) (p : MvPolynomial ℕ ℝ) :
    chainNatPolyAfter ls p 0 = p := by
  simp [chainNatPolyAfter]

/-- After `k+1` layers, the polynomial is the `(k+1)`-th step applied to the `k`-th one:
the accumulator's offset is `2k`, so slot `2k` is exactly what that step writes. -/
theorem chainNatPolyAfter_succ (ls : List (MLayer 1 1)) (p : MvPolynomial ℕ ℝ)
    (l : MLayer 1 1) (rest : List (MLayer 1 1)) (k : ℕ)
    (h : ls = l :: rest) :
    chainNatPolyAfter ls p (k + 1)
      = ((rest.take k).foldl (fun acc _ => stepNat acc) (stepNat (0, p))).2 := by
  subst h
  simp only [chainNatPolyAfter, List.take_succ_cons, List.foldl_cons]

/-- The first layer's weight is readable from the polynomial AFTER the first step. -/
theorem chainNatPolyAfter_one_coeff (l : MLayer 1 1) (rest : List (MLayer 1 1))
    (c : ℝ) :
    MvPolynomial.coeff (Finsupp.single 0 1) (chainNatPolyAfter (l :: rest) (MvPolynomial.C c) 1)
      = c := by
  simp only [chainNatPolyAfter, List.take_succ_cons, List.take_zero, List.foldl_cons,
    List.foldl_nil]
  exact stepNat_coeff_weight 0 c



/-! ## Round 65: the exact shape of a deep chain's final slot 0

## What was established (verified by probe, not asserted)

**Two facts, each checked by a compiling probe before this note was written:**

    1. coeff (single 0 1) ((stepNat (0, C c)).2) = c
       -- stepNat_coeff_weight 0 c

    2. coeff (single 0 1) (chainNatPoly [l, l'] (C c)) = 0
       -- proved by: simp only [chainNatPoly, List.foldl_cons, List.foldl_nil]
                    exact stepNat_coeff_zero_irrelevant 2 (by omega) (...)

**So a ONE-element chain's final slot 0 is `c`, and a TWO-element chain's final slot 0 is `0`.**
**That pair is the whole negative result: the final polynomial cannot be read for a deep chain.**

## The shape, once unfolded

**`simp only [chainNatPoly, List.foldl_cons]` on a THREE-or-more-element chain gives:**

    coeff (fun0 | 0 => 1)
      (List.foldl (fun acc x => stepNat acc)
          (stepNat (stepNat (0, C c))) tl).2 = 0

**The `foldl` has ALREADY absorbed the first two layers into a single accumulator
`stepNat (stepNat (0, C c))`, and `tl` is the remainder.**
**That is why `stepNat_coeff_zero_irrelevant 2` works for the two-element case: after two layers
the offset is 4, and both steps at offsets 0 and 2 have run.**

## Where this round stalled, precisely

**Goal to prove:**

    theorem deep_chain_final_slot_is_zero (l l' : MLayer 1 1) (tl : List (MLayer 1 1)) (c : Real) :
        coeff (single 0 1) (chainNatPoly (l :: l' :: tl) (C c)) = 0

**The intended route is `foldl_coeff_zero_irrelevant tl (off := 4) (p := ...)`, which needs the
accumulator's offset to be `4` and its slot 0 to be `0`.**

**Five attempts failed:**

1. **Passing `(stepNat (stepNat (0, C c))).1` as the offset with `rw [hoff]`** --
   **`rw` failed: after `simp only [stepNat]` the `.1` projection is already reduced, so the
   pattern `(stepNat (stepNat (0, C c))).1` no longer occurs in the goal.**
2. **`have hz : ... := by simp only [stepNat]; exact stepNat_coeff_zero_irrelevant 4 ...`** --
   **`simp only [stepNat]` on the goal `coeff ... ((stepNat (stepNat (0, C c))).2) = 0` unfolds BOTH
   steps into a large term and the subsequent `exact` no longer matches.**
3. **Passing `_` for the offset/polynomial arguments** --
   **`(deterministic) timeout at isDefEq`, 200000 heartbeats exceeded**: the metavariables force
   the elaborator to reduce the nested `stepNat` repeatedly.
4. **`set_option maxHeartbeats 1000000 in` plus `rw [hoff]`** --
   **`function expected at` L4:27, because `open List` in the probe shadowed `List.foldl_cons`.**
5. **Replacing the statement with an induction on `tl`** --
   **the induction hypothesis' accumulator did not match the goal's, so `exact ih` failed.**

**=> the obstruction is purely about presenting the accumulator's offset, not about the
mathematics: the two probes above already establish the content.**

## The route that should work next round

**State the accumulator explicitly and let `rfl` compute it, instead of rewriting projections:**

    have hacc : stepNat (stepNat (0, MvPolynomial.C c))
        = (4, MvPolynomial.X 0 * (MvPolynomial.X 0 * MvPolynomial.C c + MvPolynomial.X 1)
             + MvPolynomial.X 1 + ... ) := rfl

**i.e. give the accumulator's PAIR as a literal `rfl` fact, then `rw [hacc]` so that the goal
mentions `(4, ...)` syntactically and `foldl_coeff_zero_irrelevant` applies with `off := 4`.**

**Failing that, prove the two-element case by `decide`-free direct unfolding (as the probe did)
and then induct on `tl` with the accumulator FIXED at `4` rather than generalized.**

## Conclusion

**No code in the tree this round; the working tree was reverted to HEAD (769).**

**The Extractors.ChainSlot plugin itself is written conceptually but was NOT committed**: its
eleven obligation `Prop`s are all straightforward citations of existing theorems, and the ONLY
new theorem it needs is the negative one above, which is blocked on presentation.
**=> it is one `rfl`-fact away.**
-/



set_option maxHeartbeats 2000000 in
/-- **A chain of length >= 2 has FINAL slot 0 equal to zero.**

The first step writes the input's weight at slot 0; the SECOND step runs at offset `0 + 2` and
`stepNat_coeff_zero_irrelevant` zeroes slot 0 outright (its conclusion does not mention the
input polynomial); `foldl_coeff_zero_irrelevant` then carries that zero through every remaining
layer, because each further step runs at an offset >= 2.

**This is the precise reason a deep chain's weights cannot be read from its FINAL polynomial** --
and the reason the extractor in this file reads the INTERMEDIATE polynomials
(`chainNatPolyAfter`, `chainNatPolyAfter_one_coeff`) instead.

**Presentation note, for whoever writes the next such proof**: the accumulator's offset is
`0 + 2` *definitionally*, so the lemma has to be instantiated at `2` and the `Nat.zero_add`
normalisation supplied to `simpa`. Instantiating at `4` (the "real" offset after two layers)
does not unify, and `rw` on the `.1` projection fails because `simp only [stepNat]` has already
reduced it. -/
theorem chainNatPoly_deep_coeff_zero (l l' : MLayer 1 1)
    (tl : List (MLayer 1 1)) (c : ℝ) :
    MvPolynomial.coeff (Finsupp.single 0 1)
      (chainNatPoly (l :: l' :: tl) (MvPolynomial.C c)) = 0 := by
  induction tl generalizing l l' with
  | nil =>
      simp only [chainNatPoly, List.foldl_cons, List.foldl_nil]
      exact stepNat_coeff_zero_irrelevant 2 (by omega) _
  | cons hd t ih =>
      simp only [chainNatPoly, List.foldl_cons]
      have hz : MvPolynomial.coeff (Finsupp.single 0 1)
          ((stepNat (stepNat (0, MvPolynomial.C c))).2) = 0 := by
        have h := stepNat_coeff_zero_irrelevant 2
          (p := (stepNat (0, MvPolynomial.C c)).2) (by omega)
        simpa only [stepNat, Nat.zero_add] using h
      exact foldl_coeff_zero_irrelevant (hd :: t) _ _
        (by simp only [stepNat]; omega) hz

/-- **No weight can be read from a deep chain's final polynomial.**

For a chain of length >= 2 and a NONZERO weight `c`, the final coefficient at slot 0 is `0`, so
it cannot equal `c`. **This is the impossibility statement the extractor's manifest needs.** -/
theorem chainNatPoly_deep_coeff_ne (l l' : MLayer 1 1)
    (tl : List (MLayer 1 1)) (c : ℝ) (hc : c ≠ 0) :
    MvPolynomial.coeff (Finsupp.single 0 1)
      (chainNatPoly (l :: l' :: tl) (MvPolynomial.C c)) ≠ c := by
  rw [chainNatPoly_deep_coeff_zero l l' tl c]
  intro h
  exact hc h.symm



end Lattice.Core