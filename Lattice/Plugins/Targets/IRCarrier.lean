import Mathlib
import Lattice.Core.Data.Models
import Lattice.Core.IR.Semantics

/-!
# 判据的 IR 载体：把 `ProofComplete` 接回主线

## 这个文件为什么存在

**审计的核心指控是：`ProofComplete` 的 23 个来源文件对 `Core.IR` 与 `Core.CIC` 的引用数是 **0**。**

**⇒ 也就是说，判据陈述的东西与表示链**没有任何可验证的关系** —— 它可以为真，而链可以完全不做这些事。**

**本文件给出判据的 IR 侧内容。做法不是替换掉旧的几何靶定理（那是「切换期」之后的事），
而是**追加**一组必须同时成立的主线事实（`CARRIER-REPLACEMENT.md` §48 的双写策略）。**

## 每一项对应链条的哪一段

| 项 | 陈述 | 对应 |
|:--|:--|:--|
| `ir_data_models` | 数据 → 骨架 → 权重被 `models` 接受 | **L0 → L3** |
| `ir_parse_models` | 任意 term 解析出的骨架可被权重实现 | **L2 → L3** |
| `ir_chain_closes` | 提取 ∘ 编译 = 恒等（在骨架上） | **L3 → L2 逆向** |
| `ir_token_count` | token 数 = 语料宽度 | **L0 → L1** |
| `ir_encode_sound` | 有效数据的编码有类型 | **L0 → L2** |
| `ir_decode_shape` | 数据 → term → 数据保持形状 | **L2 → L0 逆向** |

**=> 六项合起来覆盖链的**四跳与两个逆向**，而它们都是主线的定理，不是几何实例的定理。**
**⇒ 这就是「判据接 IR」的全部内容：让判据说出链真的做了哪些事。** -/

namespace Lattice.Plugins.Targets
namespace IRCarrier

open Lattice.Core.IR
open Lattice.Data

/-- **L0 → L3：数据经骨架编译成权重，该权重被 `models` 判定为实现。**

**=> 链的第一段与最后一段连起来：给定任意数据与任意读取约定 `f`，存在权重被 `models` 接受。**
**权重由 `compileWith` 显式构造，因此这不是存在性断言，而是构造性闭环。** -/
def ir_data_models : Prop :=
  ∀ (d : Data) (f : (s : TensorShape) → Fin s.shape.prod → ℝ),
    models (Bridge.bridge d) (compileWith (Bridge.bridge d) f) f

/-- **`ir_data_models` 成立。**

**=> 直接引用 `Models.data_models` —— 数据层已证过的事实在判据里被**点名**。**
**这一步的全部价值在于让判据与主线之间有一条可检查的引用边。** -/
theorem ir_data_models_holds : ir_data_models :=
  fun d f => Models.data_models d f

/-- **L2 → L3：任意 CIC term 解析出的骨架，都可被权重实现。**

**=> 与上一项平行，但入口是 term 而不是数据。**
**它说明「符号模型 → 权重」这一跳对**任意**语法项都成立，而不只对数据编出的项。** -/
def ir_parse_models : Prop :=
  ∀ (t : Lattice.Core.CIC.Term) (f : (s : TensorShape) → Fin s.shape.prod → ℝ),
    models (parseWithRelations t) (compileWith (parseWithRelations t) f) f

/-- **`ir_parse_models` 成立。**

**=> 直接引用 `parse_models_full`：`Core.IR` 已证过的事实在判据里被点名。** -/
theorem ir_parse_models_holds : ir_parse_models :=
  fun t f => parse_models_full t f

/-- **L3 → L2：从编译出的权重里提取，得到原来的骨架。**

**=> 逆向方向：`extract ∘ compileWith` 在骨架上是恒等。**
**它与上面两项合起来说明：正向可编译、逆向可提取，且两者互逆。** -/
def ir_chain_closes : Prop :=
  ∀ (k : IRSkeleton) (f : (s : TensorShape) → Fin s.shape.prod → ℝ),
    extract (compileWith k f) = some k

/-- **`ir_chain_closes` 成立。**

**=> 直接引用 `extract_compileWith`。**
**⇒ 这三项放在一起，就是「闭环」在判据里的形式：正向、逆向、互逆，全部点名。** -/
theorem ir_chain_closes_holds : ir_chain_closes :=
  fun k f => extract_compileWith k f

/-- **L0 → L1：token 数恰等于语料的宽度。**

**=> 第一跳的守恒律。它排除「token 化丢坐标」与「token 化造坐标」两种失败。** -/
def ir_token_count : Prop :=
  ∀ (c : List Sample), (Token.tokenize c).length = Corpus.width c

/-- **`ir_token_count` 成立。**

**=> 直接引用 `Models.token_count`。** -/
theorem ir_token_count_holds : ir_token_count :=
  fun c => Models.token_count c

/-- **L0 → L2：被常量集覆盖的数据，其编码可类型化。**

**=> 这一步把「数据」与「项」接起来，而接口是一条**类型**关系。
它是链在语法层的合法性来源。** -/
def ir_encode_sound : Prop :=
  ∀ {K : Lattice.Core.CIC.ConstSet} (d : Data) (Γ : Lattice.Core.CIC.CICCtx),
    Encode.Covered K d → Lattice.Core.CIC.Typable K Γ (Encode.encode d)

/-- **`ir_encode_sound` 成立。**

**=> 直接引用 `Encode.encode_sound`。** -/
theorem ir_encode_sound_holds : ir_encode_sound :=
  fun d Γ h => Encode.encode_sound d Γ h

/-- **L2 → L0：数据经 term 往返后保持形状。**

**=> 逆向的第一跳。注意它说的是**形状**：数值不进 term，因此「数据可逆」是假命题，
而「形状可逆」是真的。判据里写真的那一条。** -/
def ir_decode_shape : Prop :=
  ∀ (d : Data), ∃ d' : Data, Decode.decode (Encode.encode d) = some d'
    ∧ d'.corpus.length = d.corpus.length

/-- **`ir_decode_shape` 成立。**

**=> 直接引用 `Models.decode_shape_roundtrip`。** -/
theorem ir_decode_shape_holds : ir_decode_shape :=
  fun d => Models.decode_shape_roundtrip d

/-- **六项合取：判据的 IR 侧汇总。**

**=> 这是 `ProofComplete` 追加的那一个合取项（一个 `Prop` 定义，因此判据可以**指名**它）。**
**它把链条的四跳与两个逆向都点名为**主线**定理，
因此判据从此与表示链之间存在六条可检查的引用边（审计实测的那 0 条）。** -/
def irCarrierAdditions : Prop :=
  ir_data_models ∧ ir_parse_models ∧ ir_chain_closes
    ∧ ir_token_count ∧ ir_encode_sound ∧ ir_decode_shape

/-- **`irCarrierAdditions` 成立。**

**=> 六条 `*_holds` 的合取。这是判据新增项的证明，也是「判据与主线不再脱钩」这一步的凭据。** -/
theorem irCarrierAdditions_holds : irCarrierAdditions :=
  ⟨ir_data_models_holds, ir_parse_models_holds, ir_chain_closes_holds,
   ir_token_count_holds, ir_encode_sound_holds, ir_decode_shape_holds⟩

end IRCarrier
end Lattice.Plugins.Targets
