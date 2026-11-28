import Mathlib
import Lattice.Plugins.Manifest

/-!
# `Lattice.Compose.Contract` —— `PrimitiveContract` 与它的两个实例（W5-2）

## 规格（`IR-CANONICAL.md` §7bis.2）与它的**一处**缺陷

规格写的是：

```lean
structure PrimitiveContract (Sym W : Type) where
  key plugin arity : …
  Sym : Type        -- ← 与类型参数同名
  W   : Type        -- ← 与类型参数同名
  sym : Sym → Prop ; weight : W → Prop ; build : Sym → W
  sound : ∀ s, sym s → weight (build s)
```

**⇒ `Sym` 与 `W` **既是类型参数、又是字段名**——Lean 里那会让字段遮蔽参数，`build : Sym → W` 也就指不清哪个 `Sym`。**
**⇒ 故本文件**删掉那两个冗余字段**（它们与参数**逐字重复**，不添任何信息），其余七个字段照规格。**
**⇒ 这是**第 8 处**规格被测量/类型检查推正的地方，而它与 `rank_key_total` 同类：**一句话里塞了两件事**。**
-/

namespace Lattice.Compose.Contract

open Lattice.Plugins (ServiceKey PluginName)

/-- **原语级语义契约**（`IR-CANONICAL.md` §7bis.2，**去掉两个与类型参数重名的冗余字段**）。

**⇒ `sound` 是**字段**而不是定理：一条契约**自带**它成立的理由，故实例化它就是证明。 -/
structure PrimitiveContract (Sym W : Type) where
  /-- 槽/服务键。 -/
  key : ServiceKey
  /-- 提供者。 -/
  plugin : PluginName
  /-- 参数个数。 -/
  arity : ℕ
  /-- 符号侧要求。 -/
  sym : Sym → Prop
  /-- 权重侧要求。 -/
  weight : W → Prop
  /-- 构造。 -/
  build : Sym → W
  /-- **契约成立**：符号侧满足 ⇒ 权重侧满足。 -/
  sound : ∀ s, sym s → weight (build s)

/-- **实例一：恒等**（`IR-CANONICAL.md` §7bis.8 指定的 `identity`）。

**⇒ 符号侧与权重侧**同一类型**，`build := id`，两侧要求都给 `True`。⇒ 于是「契约成立」只需 `trivial`。** -/
def identityContract (key : ServiceKey) (plugin : PluginName) (T : Type) :
    PrimitiveContract T T where
  key := key
  plugin := plugin
  arity := 1
  sym := fun _ => True
  weight := fun _ => True
  build := id
  sound := by intro s _; trivial

/-- **实例二：常值**（§7bis.8 指定的 `const`）。

**⇒ `build := fun _ => c`，权重侧要求 `= c`，故 `sound` 是 `rfl`——**
**⇒ 这条契约的**内容**全在 `weight` 里：它说「产物必须是 `c`」。 -/
def constContract (key : ServiceKey) (plugin : PluginName) (Sym W : Type) (c : W) :
    PrimitiveContract Sym W where
  key := key
  plugin := plugin
  arity := 1
  sym := fun _ => True
  weight := fun w => w = c
  build := fun _ => c
  sound := by intro s _; rfl

/-- **⭐ 恒等契约的 `sound`（作为一条可引用的定理）。** -/
theorem identityContract_sound {T : Type} (key : ServiceKey) (plugin : PluginName) (s : T) :
    (identityContract key plugin T).weight
      ((identityContract key plugin T).build s) :=
  (identityContract key plugin T).sound s trivial

/-- **⭐ 常值契约的 `sound`，且结论**显式**是 `= c`（而不是一个抽象谓词）**。 -/
theorem constContract_sound {Sym W : Type} (key : ServiceKey) (plugin : PluginName) (c : W) (s : Sym) :
    (constContract key plugin Sym W c).build s = c := rfl

end Lattice.Compose.Contract