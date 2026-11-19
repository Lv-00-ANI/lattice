/-
# `Compose/Iterate` —— 循环：测度、可达链、燃料

## 0. 思路（先写思路再写证明）

`DIRECTORY-DESIGN.md` §6 给 `iterate` 一行：「循环，需要 measure」。
**那一行里藏着两个不同的东西**：

| 需要什么 | 是什么 | 本节做到了吗 |
|:--|:--|:--|
| **终止** | 测度沿步严格下降 ⟹ 步数有上界 | ✅ **`Reaches.meas_add_le`** |
| **正确性** | 循环停下时 `dec` 为真 | ⚠ **不是可证的**（见 §3） |

**终止可证，因为它是纯算术**：若每一步 `meas` 都严格下降、而 `meas : I → ℕ` 不可能为负，
则链长不超过 `meas x`。**这是本节唯一的真定理。**

**「停下时 `dec` 为真」不可证**，所以 `iterate` **不作为 `sound` 的 `Primitive` 交付**——
理由在 §3，那是本节最重要的部分。

## 1. 可达链

`Reaches p n x z`：从 `x` 走 `n` 步 `p` 到达 `z`，每一步都满足 `p.post`。

**为什么用归纳定义而不是 `Nat` 递归函数**：`p.post` 是 `Prop`，一条链**不必唯一**
（`post` 可以有多个见证）。归纳定义能表达「**存在**这样一条链」，而递归函数只能表达「**按
`p.run` 走的**那一条」。**两者在 §3 的缺口里是不同的东西**，所以这里选能表达存在的那一个。

## 2. 终止定理

`Reaches.meas_add_le`：若 `hdec : ∀ x y, p.post x y → meas y < meas x`，则
**`Reaches p n x z → meas z + n ≤ meas x`**。

它是「步数有上界」的精确形式：链长不超过起始测度，且末态测度比初态小至少 `n`。

## 3. ⚠ 为什么 `iterate` **不**作为 `Primitive` 交付

要做成 `Primitive I I`，`sound` 需要：从 `pre` 成立**推出** `run` 成功且 `post` 成立。
而 `run` 是按 `p.run` 走的那条**确定的**路径，`post` 要说的却是「停下了且 `dec` 为真」。

**缺口在这**：`pre` 若写「存在一条到达 `dec` 为真的链」，**那条链未必是 `p.run` 走的那条**。
`p.post` 可以有多个见证，`p.sound` 只保证 `p.run` 的**那一个**见证满足 `post`，
**不保证它沿着 `pre` 许诺的那条链**。

**所以正确的 `pre` 必须写成**对 `p.run` 的**确定性**要求，例如：

```lean
pre := fun x => ∃ n z, loop p dec meas x n = some z ∧ dec z = true
```

**而那样的 `pre` 就是 `run` 成功本身**（循环论证）——它让 `sound` 变成 `id`。
这正是审计判过的「`:= h` 复述」形状，**不能这么写**。

**§6 缺的那一条是**：「在这个测度下，沿 `p.run` 的确定性路径**必然**到达 `dec` 为真的状态」。
它是一条**额外假设**，不是从 `Primitive` 契约能推出来的。**本节把它作为缺口登记，不掩盖它。**

## 4. 交付

| 声明 | 内容 |
|:--|:--|
| **`Reaches`** | `n` 步可达（归纳定义，表达**存在**） |
| **`Reaches.meas_add_le`** | **终止：`meas z + n ≤ meas x`** |
| `loop` | 按 `p.run` 走的燃料版循环（`Nat` 燃料，结构递归） |
| `loop_done` | `dec x = true` 时立即返回 `x` |
| `loop_step` | `dec x = false` 时走一步再递归 |

## 5. 边界

- **`loop` 是函数，不是 `Primitive`**（见 §3）。
- **`loop` 的 `post` 无从谈起**：它没有 `sound`，因为它**不总能成功**（燃料耗尽且 `dec` 仍假时为 `none`）。
- **`Reaches` 不声称唯一性**：同一对 `(x, z)` 可能有多条链，本节只需存在性。 -/
import Mathlib
import Lattice.Compose.Primitive

namespace Lattice.Compose

/-! ## 一、可达链 -/

/-- **`n` 步可达**：从 `x` 走 `n` 步 `p` 到 `z`，每一步都满足 `p.post`。

用归纳定义而**不是** `Nat` 递归函数，因为它要表达「**存在**一条链」；
`post` 可以有多个见证，递归函数只能表达「按 `run` 走的那一条」。 -/
inductive Reaches {I : Type} (p : Primitive I I) : ℕ → I → I → Prop
  /-- 零步到达自身。 -/
  | refl (x : I) : Reaches p 0 x x
  /-- 走一步再走 `n` 步。 -/
  | step {n : ℕ} {x y z : I} : p.post x y → Reaches p n y z → Reaches p (n + 1) x z

/-! ## 二、终止：本节唯一的真定理 -/

/-- **测度沿链严格下降**：`Reaches p n x z` 且每步都使 `meas` 严格下降
⟹ **`meas z + n ≤ meas x`**。

这是「步数有上界」的精确形式：链长不超过起始测度，且末态测度至少小了 `n`。

**这是纯算术**，与 `Primitive` 的正确性无关——所以它能证，而 §3 的出口条件不能。 -/
theorem Reaches.meas_add_le {I : Type} {p : Primitive I I} {meas : I → ℕ}
    (hdec : ∀ x y, p.post x y → meas y < meas x)
    {n : ℕ} {x z : I} (h : Reaches p n x z) : meas z + n ≤ meas x := by
  induction h with
  | refl x => simp
  | @step n x y z hpost _hrest ih =>
      -- `ih : meas z + n ≤ meas y`, and one more step drops `meas` strictly
      have h2 : meas y < meas x := hdec x y hpost
      omega

/-- **链长有界**：`Reaches p n x z` ⟹ `n ≤ meas x`。 -/
theorem Reaches.length_le {I : Type} {p : Primitive I I} {meas : I → ℕ}
    (hdec : ∀ x y, p.post x y → meas y < meas x)
    {n : ℕ} {x z : I} (h : Reaches p n x z) : n ≤ meas x := by
  have := Reaches.meas_add_le hdec h
  omega

/-! ## 三、燃料版循环（函数，不是 `Primitive`） -/

/-- **按 `p.run` 走的燃料版循环**：`dec x = true` 时返回 `x`，否则走一步并消耗一格燃料。

**它是函数而不是 `Primitive`**——理由见文件头 §3：它的 `sound` 需要一条本节证不出的
出口存在性假设。 -/
def loop {I : Type} (p : Primitive I I) (dec : I → Bool) : ℕ → I → Option I
  | 0, x => if dec x then some x else none
  | n + 1, x => if dec x then some x else (p.run x).bind (loop p dec n)

/-- **已满足则立即返回。** -/
theorem loop_done {I : Type} (p : Primitive I I) (dec : I → Bool) (n : ℕ) (x : I)
    (h : dec x = true) : loop p dec n x = some x := by
  cases n with
  | zero => simp [loop, h]
  | succ k => simp [loop, h]

/-- **未满足则走一步再递归。** -/
theorem loop_step {I : Type} (p : Primitive I I) (dec : I → Bool) (n : ℕ) (x : I)
    (h : dec x = false) :
    loop p dec (n + 1) x = (p.run x).bind (loop p dec n) := by
  simp [loop, h]

/-- **燃料耗尽且未满足 ⟹ 失败。** -/
theorem loop_zero_none {I : Type} (p : Primitive I I) (dec : I → Bool) (x : I)
    (h : dec x = false) : loop p dec 0 x = none := by
  simp [loop, h]

/-! ## 四、燃料单调性：更多燃料只会更好 -/

/-- **更多燃料不会变坏**：若 `n` 格燃料已成功，则任何 `n + k` 格也成功，且**结果相同**。

**它是 `iterate` 那条 `pre` 与 `run` 之间的桥**：`pre` 只许诺「某个不超过 `meas x` 的燃料成功」，
而 `run` 用的是 `meas x` 格。没有这条，`sound` 就得假设「恰好 `meas x` 格成功」——那是 `id`。

归纳做在 `n` 上：`n = 0` 时成功意味着 `dec x` 已真，于是任何燃料都直接返回 `x`；
`n + 1` 时分 `dec x` 两种情况，真则同上，假则把 `bind` 拆开并对输出用归纳假设。 -/
theorem loop_mono {I : Type} (p : Primitive I I) (dec : I → Bool) :
    ∀ (n : ℕ) (x z : I), loop p dec n x = some z → ∀ k, loop p dec (n + k) x = some z := by
  intro n
  induction n with
  | zero =>
      intro x z h k
      have hx : dec x = true := by
        by_contra hne
        have hf : dec x = false := by
          cases hv : dec x
          · rfl
          · exact absurd hv hne
        rw [show loop p dec 0 x = none from by simp [loop, hf]] at h
        exact absurd h (by simp)
      have hz : z = x := by
        rw [show loop p dec 0 x = some x from by simp [loop, hx]] at h
        exact (Option.some.inj h).symm
      rw [hz]
      exact loop_done p dec (0 + k) x hx
  | succ n ih =>
      intro x z h k
      by_cases hd : dec x = true
      · have hz : z = x := by
          rw [show loop p dec (n + 1) x = some x from by simp [loop, hd]] at h
          exact (Option.some.inj h).symm
        rw [hz]
        exact loop_done p dec (n + 1 + k) x hd
      · have hf : dec x = false := by
          cases hv : dec x
          · rfl
          · exact absurd hv hd
        rw [show loop p dec (n + 1) x = (p.run x).bind (loop p dec n) from by simp [loop, hf]] at h
        -- split on p.run x instead of using Option.bind_eq_some_iff, whose name differs here
        cases hr : p.run x with
        | none => simp [hr] at h
        | some y =>
        have hly : loop p dec n y = some z := by simpa [hr] using h
        have him : loop p dec (n + k) y = some z := ih y z hly k
        have hstep : loop p dec (n + 1 + k) x = (p.run x).bind (loop p dec (n + k)) := by
          have he : n + 1 + k = (n + k) + 1 := by omega
          rw [he]
          simp [loop, hf]
        rw [hstep, hr]
        simpa using him

/-! ## 五、`iterate`：把出口条件作为**显式 `pre`**（第 235 轮的裁决）

### `pre` 写什么

**不能写成「循环成功」**——那样 `sound` 就是 `id`，是审计判过的 `:= h` 复述形状。

**写成**：存在一个**不超过 `meas x` 的燃料** `n`，使循环在 `n` 格内成功抵达一个 `dec` 为真的状态：

```lean
pre x := ∃ n z, n ≤ meas x ∧ loop p dec n x = some z ∧ dec z = true
```

**它比 `run` 的成功严格弱**：`run` 用 `meas x` 格，而 `pre` 只许诺**某个** `n ≤ meas x`。
所以 `sound` 必须干活——干的是 `loop_mono`：把 `n` 格的保证推到 `meas x` 格。

### `post` 只说 `dec z = true`

**不说可达性**。原因是诚实的：`pre` 许诺的那条链是「某个 `n` 的成功」，而 `run` 的实际路径
是唯一的；要断言 `Reaches`，需要从 `loop` 抽出见证链——那可以再证（`loop_witness`），
**但本节不做**，因为 `post := dec z = true` 已经是 `iterate` 的正确性内容，
而可达性属于 §二 的 `Reaches`（它有自己的 `meas_add_le`）。

**把没证的东西写进 `post` 会让 `sound` 变成假声称。** -/

/-! ## 五、从成功的循环抽出可达链

### 需要的假设恰好是「要迈步时前置成立」

循环的执行走 `p.run`，而 `p.post` 只在 `p.pre` 成立时由 `p.sound` 保证。
所以要断言 `Reaches`，需要一条关于 `p.pre` 的假设。

**两条候选，选弱的那条**：

| 假设 | 是否够 | 对 `descentStep` 是否成立 |
|:--|:--|:--|
| `∀ y, p.pre y`（处处成立） | 够，但过强 | ❌ **在解处不成立**（`β + c = 0` 时 `pre` 是假） |
| **`∀ y, dec y = false → p.pre y`**（要迈步时成立） | **够** | ✅ 正好：`dec` 为假就是「还没到解」 |

**所以用第二条**：它恰好是循环需要的那一点，不多不少。
`dec y = true` 时不迈步，所以那时 `p.pre` 真假无关。

### 结果

`loop p dec n x = some z` ⟹ **存在 `k ≤ n` 与一条 `Reaches p k x z`**。

**这把 `loop` 的成功与 §二 的 `Reaches` 接上了**，因此 `iterate.post` 可以升级为含可达性。 -/

/-- **成功的循环给出可达链**：`loop p dec n x = some z` ⟹ `∃ k ≤ n, Reaches p k x z`。

归纳在燃料 `n` 上。迈步那支需要 `p.pre x`——由 `hp` 与 `dec x = false` 得到，
再由 `p.sound` 得到 `p.post x y`（`y` 是 `p.run x` 的实际输出）。 -/
theorem loop_witness {I : Type} (p : Primitive I I) (dec : I → Bool)
    (hp : ∀ y, dec y = false → p.pre y) :
    ∀ (n : ℕ) (x z : I), loop p dec n x = some z → ∃ k, k ≤ n ∧ Reaches p k x z := by
  intro n
  induction n with
  | zero =>
      intro x z h
      have hx : dec x = true := by
        by_contra hne
        have hf : dec x = false := by
          cases hv : dec x
          · rfl
          · exact absurd hv hne
        rw [show loop p dec 0 x = none from by simp [loop, hf]] at h
        exact absurd h (by simp)
      have hz : z = x := by
        rw [show loop p dec 0 x = some x from by simp [loop, hx]] at h
        exact (Option.some.inj h).symm
      refine ⟨0, by omega, ?_⟩
      rw [hz]
      exact Reaches.refl x
  | succ n ih =>
      intro x z h
      by_cases hd : dec x = true
      · have hz : z = x := by
          rw [show loop p dec (n + 1) x = some x from by simp [loop, hd]] at h
          exact (Option.some.inj h).symm
        refine ⟨0, by omega, ?_⟩
        rw [hz]
        exact Reaches.refl x
      · have hf : dec x = false := by
          cases hv : dec x
          · rfl
          · exact absurd hv hd
        rw [show loop p dec (n + 1) x = (p.run x).bind (loop p dec n) from by simp [loop, hf]] at h
        cases hr : p.run x with
        | none => simp [hr] at h
        | some y =>
            have hly : loop p dec n y = some z := by simpa [hr] using h
            obtain ⟨k, hk, hR⟩ := ih y z hly
            have hpre : p.pre x := hp x hf
            obtain ⟨y', hy', hpost⟩ := p.sound x hpre
            have hyy : y' = y := by
              rw [hr] at hy'
              exact (Option.some.inj hy').symm
            exact ⟨k + 1, by omega, Reaches.step (hyy ▸ hpost) hR⟩

/-! ## 六、`iterate`：出口条件为显式 `pre`，且 `post` 含可达性 -/

/-- **循环组合子**：在测度下重复 `p`，直到 `dec` 为真。

**`pre`（显式出口假设，第 235 轮裁决）**：某个不超过 `meas x` 的燃料足以成功。

**`post`（第 236 轮升级）**：`dec z = true` **且** `z` 由一条合法的 `p` 链可达。
升级靠 `loop_witness`；它需要 `hp`——「要迈步时 `p.pre` 成立」。

⚠ **`hp` 是第 236 轮新增的假设**：`post` 变强，代价是多一个前提。
**这是加价不是白拿**，写在这里以免被读成「免费升级」。 -/
def iterate {I : Type} (p : Primitive I I) (dec : I → Bool) (meas : I → ℕ)
    (hp : ∀ y, dec y = false → p.pre y) : Primitive I I where
  pre := fun x => ∃ (n : ℕ) (z : I), n ≤ meas x ∧ loop p dec n x = some z ∧ dec z = true
  post := fun _ z => dec z = true ∧ ∃ k, Reaches p k _ z
  run := fun x => loop p dec (meas x) x
  sound := by
    intro x hx
    obtain ⟨n, z, hn, hl, hd⟩ := hx
    refine ⟨z, ?_, hd, ?_⟩
    · have hmono : loop p dec (n + (meas x - n)) x = some z := loop_mono p dec n x z hl (meas x - n)
      have he : n + (meas x - n) = meas x := by omega
      rwa [he] at hmono
    · have hmono : loop p dec (n + (meas x - n)) x = some z := loop_mono p dec n x z hl (meas x - n)
      obtain ⟨k, _hk, hR⟩ := loop_witness p dec hp n x z hl
      exact ⟨k, hR⟩
  strength := p.strength
  coverage := p.coverage

/-- **`iterate` 的 `sound`**：可直接引用的一条。 -/
theorem iterate_sound {I : Type} (p : Primitive I I) (dec : I → Bool) (meas : I → ℕ)
    (hp : ∀ y, dec y = false → p.pre y) (x : I) (hx : (iterate p dec meas hp).pre x) :
    ∃ z, (iterate p dec meas hp).run x = some z ∧ (iterate p dec meas hp).post x z :=
  (iterate p dec meas hp).sound x hx

/-- **`iterate` 的强度不变**：循环不新增承诺。 -/
theorem iterate_strength {I : Type} (p : Primitive I I) (dec : I → Bool) (meas : I → ℕ)
    (hp : ∀ y, dec y = false → p.pre y) :
    (iterate p dec meas hp).strength = p.strength := rfl

end Lattice.Compose
