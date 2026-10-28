import Mathlib
import Lattice.Lib.Compiler.ModConstraint
import Lattice.Runtime.RealModLoss
/-!
# LATTICE: 同余三重桥接 —— Congruent ↔ CongruentInt ↔ Int.ModEq ↔ Divisible

## 缺口（本文件证的是什么）

库中同余语义存在**三份彼此平行、从未被互相桥接**的陈述：

  1. `Lattice.Congruent`     (ModConstraint.lean:23)  `x a m : Int`, `m ∣ x - a`
  2. `Lattice.CongruentInt`  (RealModLoss.lean:30)    `x a m : ℤ`,   `m ∣ x - a`
  3. `Int.ModEq m x a`        (mathlib, 符号 `x ≡ a [ZMOD m]`)  `x % m = a % m`

三者**互相蕴含**，但库中没有任何定理把其中任意两者连起来：
RealZMod.lean 只桥了 `ZMod p` 与 `Int.ModEq`（`zmod_eq_iff_modEq`），
从未触及 `Lattice.Congruent` / `Lattice.CongruentInt`。
`ModConstraint.lean:120-122` 的注释更把 `x % m = a % m ⟺ m ∣ x - a` 明确
标注为**未证**（"依赖 mathlib；此处给出 m=±1 的退化特例"）。

本文件用 mathlib `Int.modEq_iff_dvd`（`a ≡ b [ZMOD n] ↔ n ∣ b - a`，commit
4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84 的 Mathlib/Data/Int/ModEq.lean:78）
及其别名 `modEq_of_dvd` / `ModEq.dvd`（同文件:86）补齐这一缺口，
**消除**该退化特例的必要性。

## 方向约定（关键，易错）

`Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a`——注意右侧是 `b - a`（**反序**）。
本文件的目标陈述是 `Int.ModEq m x a`（即 `x ≡ a`，x 在前），
对应右侧 `m ∣ a - x`。而库中 `Congruent x a m` 的定义是 `m ∣ x - a`。
二者相差一个符号：由 `Int.dvd_neg`（`m ∣ -(x-a) ↔ m ∣ x-a`）消去。

因此：
  · 正向 `m ∣ x - a ⟹ x ≡ a [ZMOD m]`：用 `modEq_of_dvd`（给出 `a ≡ x`）
    再 `Int.ModEq.symm` 翻成 `x ≡ a`。
  · 反向 `x ≡ a [ZMOD m] ⟹ m ∣ x - a`：用 `Int.ModEq.dvd`
    （给出 `m ∣ a - x`）再经 `Int.dvd_neg` 与 `a - x = -(x - a)` 改写。

## 桥接图（本文件证出的边）

    Lattice.Congruent x a m  ⇄  Int.ModEq m x a      (定理一/二，双向)
            ⇕                            ⇕
    Lattice.CongruentInt x a m ⇄ m ∣ x - a          (定理三/四)

    Lattice.Congruent x a m  ⇄  Lattice.Divisible (ModOut x a) m   (定理五/六，双向)

（`Congruent` 与 `CongruentInt` 定义体同为 `m ∣ x - a`，二者的等价是定义展开；
但与 `Int.ModEq` 的桥是**实质内容**——见定理一/二。）

## 依赖
纯 mathlib（`Int.ModEq`）+ 本库两条同余线（ModConstraint / RealModLoss）。
-/

namespace Lattice

/-! ## 定理一：`Congruent` ⟹ `Int.ModEq`（正向桥）

`m ∣ x - a` ⟹ `x ≡ a [ZMOD m]`。 -/

theorem congruent_to_modEq {x a m : Int} (h : Congruent x a m) : Int.ModEq m x a := by
  -- Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a；取 a:=a, b:=x，
  -- mpr 方向得 a ≡ x，再取 symm 得到目标 x ≡ a。
  exact ((Int.modEq_iff_dvd (n := m) (a := a) (b := x)).mpr h).symm

/-! ## 定理二：`Int.ModEq` ⟹ `Congruent`（反向桥）

`x ≡ a [ZMOD m]` ⟹ `m ∣ x - a`。 -/

theorem modEq_to_congruent {x a m : Int} (h : Int.ModEq m x a) : Congruent x a m := by
  -- ModEq.dvd : a ≡ b [ZMOD n] → n ∣ b - a；取 a:=x, b:=a 得 m ∣ a - x。
  have hd : m ∣ a - x := Int.ModEq.dvd (n := m) (a := x) (b := a) h
  -- a - x = -(x - a)，故 m ∣ x - a。
  have : a - x = -(x - a) := by ring
  rw [this] at hd
  exact Int.dvd_neg.mp hd

/-! ## 定理一/二的合并形式（双向等价，主桥） -/

theorem congruent_iff_modEq (x a m : Int) : Congruent x a m ↔ Int.ModEq m x a :=
  ⟨congruent_to_modEq, modEq_to_congruent⟩

/-! ## 定理三：`CongruentInt` ⟹ `Int.ModEq`（RealModLoss 线并入） -/

theorem congruentInt_to_modEq {x a m : Int} (h : CongruentInt x a m) : Int.ModEq m x a := by
  exact congruent_to_modEq h

/-! ## 定理四：`Int.ModEq` ⟹ `CongruentInt`（反向） -/

theorem modEq_to_congruentInt {x a m : Int} (h : Int.ModEq m x a) : CongruentInt x a m := by
  exact modEq_to_congruent h

/-! ## 定理三/四的合并形式 -/

theorem congruentInt_iff_modEq (x a m : Int) : CongruentInt x a m ↔ Int.ModEq m x a :=
  ⟨congruentInt_to_modEq, modEq_to_congruentInt⟩

/-! ## 定理五：`Congruent` ⟹ `Divisible`（整除判定侧，正向）

模神经元输出 `ModOut x a = x - a`；同余 ⟹ 输出被 m 整除。 -/

theorem congruent_to_divisible {x a m : Int} (h : Congruent x a m) :
    Divisible (ModOut x a) m := by
  exact h

/-! ## 定理六：`Divisible` ⟹ `Congruent`（反向） -/

theorem divisible_to_congruent {x a m : Int} (h : Divisible (ModOut x a) m) :
    Congruent x a m := by
  exact h

/-! ## 定理五/六的合并形式 -/

theorem congruent_iff_divisible (x a m : Int) :
    Congruent x a m ↔ Divisible (ModOut x a) m :=
  ⟨congruent_to_divisible, divisible_to_congruent⟩

/-! ## 定理七：三段闭合 —— 经 `Int.ModEq` 中转的整除桥

`Congruent x a m ⟹ Int.ModEq m x a ⟹ m ∣ x - a ⟹ Divisible (ModOut x a) m`。
把桥走一个完整来回，证明三条路径**终点的定义相等**。 -/

theorem congruent_divisible_via_modEq (x a m : Int) (h : Congruent x a m) :
    Divisible (ModOut x a) m := by
  have hmod : Int.ModEq m x a := congruent_to_modEq h
  have hd : m ∣ a - x := Int.ModEq.dvd (n := m) (a := x) (b := a) hmod
  have hsub : a - x = -(x - a) := by ring
  rw [hsub] at hd
  exact Int.dvd_neg.mp hd

/-! ## 定理八：`Congruent` ⟺ `CongruentInt`（两条库内线合一）

两定义体同为 `m ∣ x - a`（ModConstraint.lean:23-24, RealModLoss.lean:30），
故等价是定义展开（`Iff.rfl` 在此确为定义展开，非证明偷懒）。 -/

theorem congruent_iff_congruentInt (x a m : Int) : Congruent x a m ↔ CongruentInt x a m :=
  Iff.rfl

end Lattice