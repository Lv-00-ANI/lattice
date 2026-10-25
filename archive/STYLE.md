# LATTICE 形式化风格指南（STYLE）

> 本文件把**在 mathlib 4.14 上实际编译 179 个文件过程中积累的约定与坑**固化为规范，
> 使后续新增证明"一出生就合规"。配套：`CORRECTIONS.md`、`ASSUMPTIONS.md`、`scripts/verify.ps1`。

---

## 1. 文件骨架（强制）

```lean
import Mathlib
import <本文件依赖的 LATTICE 模块>   -- 全部 import 必须在 docstring 之前

/-!
# LATTICE: <主题>——<一句话定位>

<设计说明：命题、路线、与既有文件的衔接>

**诚实边界**（本文件不证 / 不声称的）：
- …
- mathlib 4.14 缺 …，故退化为 …
- 未做：…（标注为后续工作）

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section   -- 必须在 namespace 之前！

namespace Lattice

variable {k : ℕ}   -- 共享变量

/-! ## 定义 -/
/-! ## 定理一：… -/

end Lattice
```

**为什么 `noncomputable section` 必须在 `namespace` 之前**：放在 `namespace Lattice` 之后会让末尾 `end Lattice` 报
`invalid 'end', name mismatch (expected nothing)`（带名 `end` 无法跳过未命名 section）——已在 `RealSubgradient` 实测。

---

## 2. 命名约定

| 类别 | 约定 | 例 |
|:--|:--|:--|
| 定义 | 小驼峰，无前缀 | `mixDist`、`fDivergence`、`linearAttentionOutput` |
| 定理 | 小驼峰 + 结论导向 | `entropy_le_log_card`、`prox_nonexpansive` |
| 等价刻画 | `_iff` / `_iff_*` | `andC_eq_zero_iff`、`zero_gap_iff_complementary_slackness` |
| 界 | `_bound` / `_le_*` | `convComb_norm_bound`、`rmsNorm_constant_lower_bound` |
| 特例回收 | `_is_*_special` / `_recovers_*` | `gqa_is_mha_special`、`orthogonal_gram_recovers_closed_form` |
| 实例化 | `complex_*`（ℂ 实例）、`scalar_*`（𝕜 泛型） | `complex_GD_converges` |
| 反例 | `not_*` / `*_counterexample` / `*_fails` | `ce_not_joint_convex`、`gd_divergence_counterexample` |
| 诚实降级 | 名字保持但 docstring 说明 | `silu_lipschitz_on`（有界域版） |

**避免**：与既有文件**同命名空间**下的同名定理（已在 `RealLoRAEditJoint` 撞到 `lora_edit_bound`，改名 `lora_edit_joint_bound`）。新增定理前先 `grep` 全库同名。

---

## 3. 数学写法约定

1. **平方**：优先 `x ^ 2`（与 `sq_le_sq'`、`mul_self_lt_mul_self` 等引理匹配）；`x * x` 仅在需要 `ring` 消去时用，且同一目标内不混用（混用会让 `linarith` 原子不匹配）。
2. **内积**：`⟪x, y⟫` 在 ℝ/ℂ 上可用；**任意 `RCLike 𝕜` 无裸记法**，需文件内
   `local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y`（**local notation 不跨文件**）。
3. **实数标量乘**：`a • x` 与 `a * x` 在 ℝ 上是 rfl 级相等，但**不要**在 `show`/`linarith` 里混用（用同形 `calc` 或统一 `*`）。
4. **求和体部**：`∑ x : α, A + B` 中 `+ B` 会**逃出求和体**（`x` 变自由变量）——必须写 `∑ x : α, (A + B)`。已多次实测。
5. **0 的类型**：内积/范数等式里的 `0` 需显式 `(0 : ℝ)`/`(0 : 𝕜)`（否则默认 ℕ，`Inner ℕ F` 合成失败）。
6. **函数值形态**：`f x` 与 `f * x` 在门控/激活文件中要明确（`Gated` 用前者）。
7. **定义域假设**：`Real.log` 是全函数（非正处取 0），含 log 的等式在 `0 < p`、`0 < q` 下陈述——这是**语义标注**，同时为 `Real.log_mul`/`log_div`（需非零参数）所用。

---

## 4. mathlib 4.14 已知坑（速查表）

| 坑 | 正确写法 |
|:--|:--|
| `λ` 是保留字 | 改名 `lam` |
| `inner` 无类型上下文时类型类卡死（`Inner ?𝕜 E`） | 写 `(inner x y : ℝ)` |
| `norm_eq_abs` 不在根命名空间 | `Real.norm_eq_abs` |
| `norm_apply_le` | `ContinuousLinearMap.le_opNorm` |
| `abs_inner_le_norm` | `abs_real_inner_le_norm` |
| `le_sSup`/`sSup_le` 需 CompleteSemilatticeSup | `le_csSup`/`csSup_le` + `Real.sSup_empty` |
| `Finset.abs_sum_le_sum_abs` | 在 `Finset` 命名空间 |
| `max_eq_left`/`max_eq_right` | ⚠ **本条已作废（v14）**：原写"4.14 语义互换"，**该说法已由 pinned 源码推翻**——见本文件详条「`min_eq_left/right` 与 `max_eq_left/right` 的**假设方向**不一致」：**结论与名字一致**，反的是 **`max` 族的**假设**方向**（`max_eq_left` 要 `b ≤ a`）。<br>⚠ **作废原因（S10 审计发现）**：本条曾被 `pitfalls.json` 的 P008 **落盘为权威 remedy**，而 `find-pitfall.ps1` 只打印本行 ⟹ **作者命中陷阱时只会看到错的那条** —— 这是"**每次读错**"而非"读错一次"。 |
| `sq_le_sq'` | 双前提 `(-b ≤ a) (a ≤ b)` |
| `sq_le_self` 不存在 | `mul_self_lt_mul_self` |
| `Point2R.ext` 不生成 | `Point2R.mk.injEq` |
| `Real.sqrt_mul` / `Real.sqrt_sq_eq_abs` | 参数是**数值**（非证明） |
| `HasFDerivAt.pow` 不存在 | `HasFDerivAt.mul` |
| `fderiv_sum` / `DifferentiableAt.sum` | 需显式 `(x := …)` |
| `Matrix.invertibleOfDetNeZero` 不存在 | `Matrix.invertibleOfIsUnitDet` |
| `mul_pos_of_pos_of_pos` 不存在 | `mul_pos` |
| `Summable.sum_le_tsum` 不存在 | `Real.tsum_le_of_sum_range_le` |
| `ZMod.fermat` 不存在 | `ZMod.pow_card` |
| ℂ 无 `Abs` 实例，`|z|` 记法不可用 | `Complex.abs z` |
| `𝕜.re` / `𝕜.im` | `RCLike.re` / `RCLike.im`；`RCLike.I` 需 `(RCLike.I : 𝕜) • v` |
| `by decide` 对 ℚ 卡（`Rat.normalize`） | 用 ℤ/ℕ 版做可计算认证 |
| `positivity` 对 `0 ≤ (n:ℝ)` 失效 | `exact_mod_cast (Nat.zero_le n)` |
| `nlinarith` 不处理 `↑(n+1)` | 先 `rw [Nat.cast_add, Nat.cast_one]` |
| `linarith`/`nlinarith` 不会用 `a+b=1` | 先 `rw [← mul_add, hab, mul_one]` |
| dot-notation 节点上写命名实参 | 先 `have hcf := h.2` 再对 `hcf` 用 `(a := …)` |
| `field_simp` 有时直接关目标 | 之后不要再跟 `ring`（会 "no goals"） |
| 新写语句中的 `inner (x - y) z` 模式 | 会让 HSub 开放元变量卡死——用 rw 作用于已展开目标 |
| `noncomputable section` 位置 | 必须在 `namespace` 之前 |
| `Type` vs `Type*` | `RealLoop.iterate` 固定在 `Type`，混用会让类型推断 stuck |
| `‖x‖^2` 的展开 | `inner_self_eq_norm_sq` 显式 `(𝕜 := ℝ)`；`norm_add_sq` 同 |
| `T ^ n x` 解析成 `T ^ (n x)`（应用结合比 `^` 紧） | 必须写 `(T ^ n) x` |
| **`Get-Content` 在有中文的 `.lean` 上静默丢行** ⚠️ **测量缺陷（v14 新发现）** | 本机 `Get-Content` 默认按 **ANSI/GBK** 解码 UTF-8 源码 ⟹ 中文多字节被误解码、**相邻行被合并**。**实测**：`RealLv00Systems` `Get-Content`=**444** vs `ReadAllLines`=**541**（差 97）；`RealFenchelLSC` 166 vs **261**（差 95）；`RealQATRate` 509 vs **669**（差 160）；`RealInContextLearning` 544 vs **638**（差 94）。<br>⇒ **判据（全项目统一）**：**行数一律用** `[System.IO.File]::ReadAllLines($f,[System.Text.UTF8Encoding]::new($false)).Count`（或 `ReadAllText(...).Split("` + "`n" + `).Count`）；**版本判据一律用 字节数 + SHA256**（行数不可靠，已多次导致版本错位误判）；**禁止**用 `Get-Content`/`Set-Content` 处理 `.lean`（前者丢行，后者加 BOM + 中文二次乱码）。<br>⚠ **影响面**：本轮大量代理报告的行数（444/166/318…）**普遍偏小约 100 行**；`doc/12` 与各报告的历史行数需按此口径重算。<br>（来源：H6 首次发现，coordinator 在 4 个文件上独立复现。） |
| **不要用 PowerShell 追加中文到 `.lean`/`.md`** ⚠️ v14 实例 | 我用 `Out-File -Encoding utf8 -Append` 追加中文到 `STYLE.md`，**追加内容全部变成乱码**（`鍒ゆ嵁` 之类）。⇒ **改中文一律用 `edit`/`write` 工具**，或**先写好 ASCII 文件再转**；**禁止** `Out-File`/`Add-Content`/`Set-Content` 处理含中文的文本文件。 |
| **`Get-Content -Raw` 读入也会破坏 Unicode** ⚠️ v14 实例 | `Copy-Item` 是**字节级复制**（安全）；但 **`Get-Content -Raw` 读取 + `WriteAllText` 写回**会破坏编码——实测把两文件正文拼成一个探针时，**中文注释与 `ℝ`/`ι`/`⟺` 所在行报出 40+ 条 `error: expected token`**。<br>⇒ **任何脚本化拼接/生成 `.lean` 必须走 .NET 显式 UTF-8（无 BOM）**：<br>`[System.IO.File]::ReadAllText($p, [System.Text.UTF8Encoding]::new($false))` + `WriteAllText(..., 同编码)`。<br>（与"禁用 PowerShell 文本 cmdlet 改写 `.lean`"是**同一根因的另一个面**：**"读文本再写回"才出事**，`Copy-Item` 不出事。） |
| **`.olean` 的 `CreationTime` ≠ `LastWriteTime` 时，其"新鲜度"不可信** ⚠️ v14 | 实例：某模块源 mtime `18:31:17`、olean `LastWriteTime` `19:05:18`（看似新鲜），但 olean 的 **`CreationTime` 是 `05:59:06`** ⟹ **该 olean 不是 19:05 那次编译的产物**。<br>⇒ **判据链（按权威性）**：**`lake` 的 `Built <Mod>` 行 / `error:` 行 / exit code（权威）** → **`LastWriteTime` 比较（辅助，须同时看 `CreationTime`）** → **从 olean grep 声明名（仅供参考，单独不可用）**。<br>⚠ **"olean 内含新声明名 ⟹ 编译成功"是错推理**：`.olean` 之间会**共享/合并符号信息**（同目录、批量构建、依赖链）⟹ grep 可能命中**依赖链**的符号。 |
| **`Polynomial.induction_on` 的分支名不是 `C`/`add`/`monomial`** | 正确名是 **`h_C` / `h_add` / `h_monomial`**（`Polynomial/Basic.lean:917` 的参数名）。用错名字报 `invalid alternative name 'C', expected 'h_C', 'h_add' or 'h_monomial'`（**错误信息本身给了正确答案**）。 |
| **mathlib 里"定义在 `namespace` 之前"的常量，全名不带该 namespace** ⚠️ v14 | 实例：`spectralRadius` 定义在 `Spectrum.lean:56`，**位于 `namespace spectrum`（`:62`）之前** ⟹ 全名是**根命名空间的 `spectralRadius`**；<br>而 `spectralRadius_le_nnnorm`（`:176`）**在** `namespace spectrum` **内** ⟹ 全名是 **`spectrum.spectralRadius_le_nnnorm`**。<br>⇒ **两者命名空间不同**，统一写 `spectrum.spectralRadius` **全错**。**用前先 `#check` 或看源码中 `namespace` 的位置**。 |
| **`Tree.node.injEq` 是命题等式而非 `↔`** | `Tree.node.injEq : a = b ∧ ts = us`（**是命题**）⟹ 用 `.1`/`.mp` 报 `invalid projection`；须用 **`Eq.mp`**。 |
| **`mutual` 块前紧邻的 `/-- -/` 文档注释** | 报 `unexpected token 'mutual'; expected 'lemma'`（**比"块内禁用 docstring"更严一档**）⟹ 须改用 **`/-! -/` 小节注释**。 |
| **`def … := fun σ => if …` 上 `rw [if_pos]` 会失败** | `unfold`/`simp only` **只到 λ**，`if` 留在 lambda 内 ⟹ 先 **`change`** 显式 β-归约再 `rw`。 |
| ⭐ **内联探针法：依赖未编译也能验证整条依赖链** ⚠️ v14（**解决长队列下的核心瓶颈**） | **问题**：模块 A `import` B，而 **B 没有 olean** ⟹ 探针 A 报 `unknown module prefix 'B'`，**完全无法验证**；等 B 排到队又要很久。<br>**做法**：把 **B 的正文（剥去其 `import` 行）与 A 的正文（剥去其 `import`）拼接**成一个 `_probe_*.lean`，**只保留最底层依赖的 `import`** ⟹ **无需任何 olean 即可验证两文件全文**。<br>⚠ **必须用 .NET 显式 UTF-8（无 BOM）读写**：实测用 `Get-Content -Raw` 拼接会把 Unicode 全毁，Lean 报 **40+ 条 `expected token`**（中文注释与 `ℝ`/`ι`/`⟺` 所在行）。<br>**实证收益**：某代理用它验证了 955 行的 `RealWLRefinement` + `RealGraphExpressivity` 全文（否则二者都因缺 olean 而无法验证）。 |
| **静态复核对 `decide` 燃料的判断不可靠——必须实跑** ⚠️ v14 | 两位静态复核者**都**对 `simp only [...]; decide` 能否闭合 `Fin 6` 上的 2-正则性**持保留意见**（认为 `whnf` 穿透 `nbhdSet`→`Finset.univ`→`List.range`→`filter` 的燃料"无法静态确认"）。<br>**实跑结果：`decide` 通过** ✅。真正的错误只有 2 条，且**都在 `decide` 之外**——是 `Finset.sum_const` + `nsmul_eq_mul` 把 `∑ const` 化成 `↑(card) * c`，与陈述里写的 `c * ↑(card)` **方向相反** ⟹ 补 `ring` 即可（`norm_num` 不处理**变量**的交换律）。<br>⇒ **教训**：**"静态无法判定"不等于"会失败"**；对 `decide`/归约燃料类问题，**实跑一次比两轮静态论证更省**。 |
| **`FileShare.None` 独占锁的文件是 0 字节且 mtime 永不更新** ⚠️ v14（**已两次误导代理**） | 实测两个代理据"锁文件 0 字节 + 时间戳是昨天"推断**"锁已损坏/陈旧、没起到互斥作用"**——**推断错误**。<br>独占锁靠**独占打开**实现互斥，**文件内容恒为空、时间戳只在创建时写一次** ⟹ **0 字节是正常状态**。<br>⇒ **判"谁持锁"看 `lean/.lake/lattice-build.owner`（含 `pid|时间戳|targets`）**，**不要**看锁文件的大小/时间。<br>⚠ 一般化教训（提问者原话）：**不要把"文件系统中可见的状态"当作"互斥机制的可见状态"——独占锁的本质就是不可见的。** |
| **`Get-Content` 行计数 + 相对路径 `.NET` 调用都会给假读数** ⚠️ v14 | 同一文件被报出 **225 / 228 / 294 / 299** 四种行数：`Get-Content \| .Count` 受编码影响（中文行丢行）；而 **`cd` 不跨 pwsh 调用持久** ⟹ `[System.IO.File]::ReadAllText('lean\X.lean')` 这类**相对路径会落到父目录**。<br>⇒ **共享文件的状态判定必须走绝对路径 + 字节级读取**：<br>`[System.IO.File]::ReadAllText((Join-Path $PWD 'X.lean'), [System.Text.UTF8Encoding]::new($false))`。<br>⇒ 且**共享文件的"版本"必须用 SHA256**，不要用行数（本波次因行数假象两次报错哈希）。 |
| ⭐ **注释内引用定界符：**成对引用是安全的，"只引开定界符"才致命** ⚠️ v14（**精化了"元陷阱"那条**） | ⚠ **上一版本条写得过宽**。用 `scripts\_probe-nested-delims.ps1` 全库实测 **8 处**"注释内出现开定界符"，
但**这 8 处的 4 个文件全部注释平衡（深度 0）且编译正常**。<br>
**精确机制**：关键在于**引用了几个**：
- ✅ **成对引用**（同一行写出 `` `/-- … -/` `` 或 `` `/-! … -/` ``）⟹ 该行 `(+1/-1)` **自平衡**，**无害**；
- ❌ **只引开定界符**（如只写 `` `/--` `` 而不写闭定界符）⟹ **开启一个嵌套注释**，
  必须靠**后面的** `-/` 来配 ⟹ **吞掉本应闭合的那一层** ⟹ `unterminated comment`（**报错在文件末尾**）。<br>
**⇒ 精确纪律**：**在注释里谈定界符时，要么**成对**写出（自平衡），要么**完全用文字描述**；
**绝不能只写开定界符**。**<br>
⚠ **诊断工具**：`scripts\check-structure.ps1`（查**最终深度 ≠ 0**，即**已发生**的失衡）
+ `scripts\_probe-nested-delims.ps1`（列**所有**"注释内含开定界符"的**位置**，供人工判断是成对还是单个）。<br>
**⇒ 一般化**：**"引用了危险 token"与"触发了危险 token"的差别，常常就是"写了一个还是两个"。** |
| ⭐ **写"陷阱说明"时，陷阱的定界符必须用**文字描述**，不可字面书写** ⚠️ v14（**元级陷阱，本波次三人各中一次**） | ⚠ **这是一个"元陷阱"**：**在注释/docstring 里解释某个陷阱时，容易把该陷阱复现一遍**。<br>
**两个独立实例（本波次）**：
1. **`RealBanditTheory`**：在 `/-!` 里解释"doc-comment 必须紧跟声明"时，**字面写了另两种开定界符** ⟹
   **注释嵌套失衡** ⟹ **余下 294 行全被吞掉**，报 `unterminated comment`（**报错在文件末尾**）。
   ⚠ **且我第一版修法在解释该陷阱时又字面写了一次，于是再次不配平** —— **必须真的只写文字**。
2. **`RealSparseCoding`**：在 docstring 里讨论假命题时用了代码围栏，**但这在 Lean 里是安全的**；
   **同一代理随后把"假命题之四"写成第二个 doc-comment**，紧跟在上一个 `-/` 之后 ⟹
   **复现了 STYLE 已登记的"孤儿 doc-comment"坑**（它自己承认"复制粘贴时又犯了一次"）。<br>
⇒ **纪律**：**写陷阱说明时，(a) 定界符一律用文字描述**（"斜杠加双横线"）；
**(b) 写完立即用结构性自检**（见下）**验证没有复现**。<br>
⚠ **通用形式**：**"解释一个失败模式"与"触发该失败模式"在文本上可能只差一个字符** ——
**故任何"陷阱登记"本身都应被结构性检查一遍**。 |
| ⭐ **结构自检：逐行累计注释嵌套深度 + 检查每个 doc-comment 后是否紧跟声明** ⚠️ v14（**零锁、纯文本**） | **两项自检（写完后立刻跑，成本≈0）**：
1. **注释配平**：逐行累计 `/-` 与 `-/` 的**嵌套深度**（`o` 为开、`c` 为闭，`depth += o - c`），
   **最终 `depth ≠ 0` ⟹ 有未闭合注释**；**深度异常的行即真凶所在**（报错行常在文件末尾，相距数百行）。
2. **孤儿 doc-comment**：每个 `/-- … -/` **之后的下一个非空行必须是声明**
   （`theorem`/`lemma`/`def`/`abbrev`/`structure`/`instance`/`class`/字段名…）；
   **结构字段的 docstring 例外**（其后是 `fieldName : Type`）。
⚠ **本波次这两项各抓到过真缺陷**（前者抓 `unterminated comment`，后者抓过 6 处孤儿）。 |
| **docstring 里引用的定理名会随改名静默漂移** ⚠️ v14（**已工具化**） | 改了命题名（或删掉一条假命题）后，docstring 的"本文件建立"清单**仍留着旧名** ⟹ 构建全绿、命题全真、**而文档指向不存在的定理**。实测某文件引用 **11 个全库不存在的名字**。<br>⇒ **用 `scripts/check-xref.ps1 -All`**（**纯静态、零锁**）：索引全库声明名，与每个文件 docstring 中反引号标识符做差集，分 `DECLARED-HERE` / `ELSEWHERE-IN-REPO` / **`ABSENT`** 三类。<br>**首跑结果**：401 文件 / **822 个全库不存在的被引标识符**，最严重的**全是 Lv-00 采集模块**（57/41/31/29/28/22…）——**根因是 docstring 继承自上游、合并时名字被改过**。<br>⚠ **`ABSENT` 是待人工复核清单，不是判决**（散文里的局部变量名/核心引理如 `pow_two` 会误报）。 |
| **`rw` 抓不到"被构造子包裹的子项"** ⚠️ v14（**重写失配的独立子类**） | 目标 `some (c :: List.map mkConstraint …) = some (c :: cs)`，而假设 `ih` 的 LHS 是**整个** `some (…)` ⟹ **`rw` 匹配不到 `c ::` 内部那个子项**，报 `did not find instance of the pattern`。<br>⇒ **先解开包裹取出内层等式再重写**：<br>`have ih' : List.map mkConstraint (toSegs (encode cs)) = cs := (Option.some.injEq _ _).mp ih; rw [ih']`。<br>（同族工具：`List.cons.injEq`、`Prod.ext`、`Subtype.ext`。）**区别于"模式不存在"，这是"模式被包裹"。** |
| ⭐ **"以名字判有无"是系统性错误源 —— 本波次已累计 9 例** ⚠️ v14（**最高频陷阱之一**） | **纪律：引用任何引理前，用 pinned checkout 的 `#check` 或 `grep` 核实其**真实名称与形状**；不要靠记忆或直觉。**<br>
**本波次实测的 9 例**（名字**存在**但**不是你要的东西**，或**不存在**）：
| 你以为的名字 | 实际情况 |
|:--|:--|
| `Nat.one_ne_two` | **不存在** |
| `Real.exp_one_gt_two` | 真名 **`Real.exp_one_gt_d9`** |
| `inv_two_mul` | **不存在** |
| `Finset.card_Ioi` | 真名 **`Fin.card_Ioi`**（已验证于 pinned checkout） |
| `Nat.catalan` | 真名是**裸 `catalan`**（在 root namespace） |
| `neg_one`（当 `-(1) = -1` 用） | 实为 `PrimitiveRoots.lean:395` 的 **`CharP` 定理** |
| `RealAbsPosEncoding.abs_pos_pythagorean`（当取等用） | 该引理**只给 `≤`，不给取等** |
| `abs_sub_abs_le_abs_sub`（当 `\|u-v\| ≤ w` 用） | 实给 **`\|u\| - \|v\| ≤ \|u - v\|`**（**左边不带绝对值**） |
| `Matrix.eval_charpoly` | 真名 **`Matrix.eval_det`** |
⇒ ⚠ **且有一处更隐蔽**：`RealGelfand.gelfand_opNorm_one` **不存在**（真名 `gelfand_opNorm_one_le`/`_of_pos`）
—— **同一文件内的自引用也可能写错名**。 |
| ⭐ **`rw [未知名字]` 连 `unknown identifier` 都不报 —— "以名字判有无"的最隐蔽变体** ⚠️ v14 | **实测**：`rw [← Finset.sum_filter]` 报
**`did not find instance of the pattern in the target expression`**，
看起来完全像"语法模式失配"，**实则该名字 grep 不到**。<br>
⚠ **但精确的表述要更正**（由发现者本人补充，我采信）：**机制是存在的**——
`Finset.sum_filter` 由 **`to_additive` 从 `prod_filter` 自动生成**，故**直接 grep 该名字搜不到**；
其语句形状是 `∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0`（**注意 `else 0`**）。<br>
⇒ **纪律**：**`rw` 报 pattern 失配时，先确认该名字真的可用**：
**grep 不到时也要考虑**它是 `to_additive`/`@[simp]`/派生机制生成的**，不要直接断定"不存在"。<br>
⚠ **本波次"以名字判有无"已累计 9 例，而这一例最隐蔽**——其余 8 例都在**编译期**报 `unknown identifier`，
**只有在 `rw` 的引理列表里，未知/不可用名字才完全静默**，只留下一个"模式失配"的假象。 |
| ⭐ **`min_eq_left/right` 与 `max_eq_left/right` 的**假设方向**不一致（不是"结论互换"）** ⚠️ v14（**两个代理曾各执一词，已实测定案**） | **权威语句**（pinned `Mathlib/Order/Defs/LinearOrder.lean`，**coordinator 亲自读源码核实**）：
```
L205  lemma min_eq_left  (h : a ≤ b) : min a b = a
L208  lemma min_eq_right (h : b ≤ a) : min a b = b
L232  lemma max_eq_left  (h : b ≤ a) : max a b = a     ← 假设方向**反了**！
L235  lemma max_eq_right (h : a ≤ b) : max a b = b     ← 假设方向**反了**！
```
⇒ ⭐ **准确表述**：**`min` 族的假设方向与名字一致**（`_left` 要 `a ≤ b`），
而 **`max` 族的假设方向与名字相反**（`_left` 要 **`b ≤ a`**）—— **结论**（取哪个操作数）**与名字一致**。
⚠ **两位代理曾各执一词**：一位说"`min_eq_left`/`min_eq_right` 语义与名字直觉相反"，
另一位说"`max_eq_left`/`max_eq_right` 不互换"。
**实测：后者更准确，前者是误述**（`min_eq_left h` 的类型确实是 `min a b = a`，与名字一致；
真正反直觉的是 **`max` 族的假设方向**）。<br>
**⇒ 纪律**：**这类"名字 vs 方向"的争议，一律读 pinned 源码定案，不要靠记忆或类推**。 |
| ⭐ **`Finset.sup'` 的 `Nonempty` 是**显式参数**，且 `Nonempty (Fin n)` **不足以**合成 filtered 集合的非空** ⚠️ v14 | `(univ.filter (·.1 ≠ ·.2)).Nonempty` 在 **`n = 1` 时为空**（无相异对）⟹
仅凭 `Nonempty (Fin n)` **合成失败**。<br>⇒ **修法**：**加 `(hn : 2 ≤ n)`** 并用 **`(0,1)` 显式构造** `Nonempty`。<br>
⚠ **同族**：`Finset.univ.sup'` 需要 `Nonempty (Fin n)` ⟹ **`0 < n` 不可省**。 |
| ⭐ **`rw [未知名字]` 的"假模式失配"也可能是**真名不同**** ⚠️ v14 | `abs_min_sub_min_le_abs` **不存在** ⟹ 真名 **`abs_min_sub_min_le_max`**（给的是 `max |a-c| |b-d|`）；<br>
`Finset.sum_eq_single` 是**双绑定**，单绑定目标用不了。 |
| ⭐ **`rw [未知名字]` 连 `unknown identifier` 都不报（旧版重复条目，见上）** | （本条为上条的早期措辞，保留以免破坏行号引用；**以上面那条为准**。） |
| ⭐ **`Finset.sum_univ` **不存在**；抬单绑定→双绑定的真工具是 `Finset.sum_attach`** ⚠️ v14（**"以名字判有无"第 10 例的邻居**） | **实测**：pinned mathlib 全树对 `theorem sum_univ`/`lemma sum_univ` **0 处命中**（该名字不存在）。<br>
**用途场景**：要把单绑定 `∑ i : ι` 抬成 `Finset.sum_comm` 所需的**双绑定**形式。<br>
**真工具**：**`Finset.sum_attach (s) (f) : ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x`**（已 `#check` 核实）。<br>
⇒ 用法：在**两层**都用其**反向**，再 `Finset.sum_comm`。 |
| ⭐ **`rw [Finset.sum_eq_single a]` 会**自动关闭主目标**** ⚠️ v14（**"no goals" 家族的新成员**） | 实测症状：**`introN failed, insufficient number of binders` + `no goals to be solved`**（**两条 error、一个根因**）——
因为 `rw` 把主目标解成 `rfl` **直接关掉**，后续两个 `intro` **落在已关闭的目标上**。<br>
⇒ **修法**：改用 **`refine Finset.sum_eq_single i ?_ ?_`**（**只**提供那两个侧条件，**不要 `intro`**）。<br>
⚠ **与已登记的"多余收尾"同族但不同**：那条是"目标已关还继续收尾"，这条是"**`rw` 替你把主目标证掉了，侧条件不能再 `intro`**"。 |
| ⭐ **`OrthonormalBasis.orthonormal b : Orthonormal 𝕜 ⇑b` 是**整体**给出的** ⚠️ v14 | `obtain ⟨hBorth, _⟩ := B.orthonormal` **会把它降级成第一个投影** `∀ i, ‖B i‖ = 1`，
于是 `orthonormal_iff_ite.mp hBorth` **类型失败**（因为 `mp` 要的是整体 `Orthonormal`）。<br>⇒ **修法**：**保持整体** —— `have hBorth : Orthonormal ℝ (B : _ → V) := OrthonormalBasis.orthonormal B`。<br>
⚠ **同一处的两个面**：本波次另记的"**点记法用在显式参数上**"是**取用**侧的同类坑（`B.orthonormal` 不解析）。<br>
⚠ **且"只修一处会漏"**：某代理先前只修了 `bessel_subspace`，**`superposition_capacity_bound_unit` 仍是旧写法** ⟹
**纪律：改完一类写法后全库 grep 同一模式**（本波次已独立总结过这条）。 |
| ⭐ **`Module.finrank_bot` 不存在；真名是**裸 `finrank_bot`**** ⚠️ v14（**"以名字判有无"第 10 例**） | **实测**：`finrank_bot` 出现在 **`Mathlib/LinearAlgebra/.../Adjoin.lean:1005`** 等，
是**裸名**（限定后搜不到）。⚠ **注意**：`Adjoin.lean` 的那条是 **`IntermediateField` 版本**，
**与一般 `Submodule` 的 `finrank ⊥` 不是同一条** ⟹ **引用前必须 `#check` 看类型**。<br>
⇒ 这是本波次"**名字存在但**限定方式或所指对象**不对**"的第 **10** 例。 |
| ⭐ **`Algebra.mul_smul_comm` 名义上可用，实际**要 `CommSemiring 𝔸`**** ⚠️ v14（**`NormedRing` 上会失败**） | 在 **`NormedRing`（不交换）** 上用 `Algebra.mul_smul_comm` 会报 **`failed to synthesize CommSemiring 𝔸`**。<br>**源码依据**：`Mathlib/Algebra/Algebra/Defs.lean:309` 的证明体是 `rw [smul_def, smul_def, left_comm]` —— **`left_comm` 需要交换性**。<br>⇒ **修法**：改用 **`Algebra.commutes`** 提供 `algebraMap` 的**中心性**（`hcent : ∀ c, A * algebraMap c = algebraMap c * A`），再 `simp only [hcent]` 归一化后 `noncomm_ring` 收尾。<br>⚠ **这与"`smul_smul` 必须显式传参"是两个独立的坑**，别混为一谈。<br>⚠ **另注**：`grep` 能判"名字有无"，**不能判"类型类是否可合成"**（本例即是）——那类必须靠探针或读源码的**证明体**。 |
| ⭐ **字段记法对带隐式参数的引理会失效** ⚠️ v14 | `(Finset.sum_mul).symm` 报 **`invalid field notation … sum_mul has type ∀ (s) (f) (a), …`**（**字段记法要求第一个**显式**参数是接收者**）。<br>⇒ **修法**：写**全名** `(Finset.sum_mul _ _ _).symm`。 |
| ⭐ **先测 API 假设（`#check`/小探针），再写长证明** ⚠️ v14（**方法学，来自 4 次失败**） | 某代理在同一个 CN 缺陷证明上**反复失败 4 次**（`smul_smul` 方向、`mul_smul_comm` 需交换性、`Finset.sum_mul` 字段记法、`set_option` 位置），
**根因全是"对本版 mathlib 的 API 约束不熟"，不是数学问题**（CN 因式化它用 Python 验到 `n=1..39`）。<br>⇒ **纪律**：**先在探针里 `#check`/试写那一行**，确认 API 可用后再展开长证明。
**长证明里每次失败都要重跑一次锁构建** ⟹ **探针的成本远低于一次构建往返**。 |
| ⭐ **构建日志是"事实"来源，不要只做静态近似** ⚠️ v14（**方法学**） | 任务曾假设"`unused variable` 只在编译时产生 ⟹ 不能跑 Lean 就只能静态近似"。**该假设是错的**：仓库 `lean/*.log` 里已沉淀 **93 份真实构建日志**，含 **171 条 `unused variable` 命中 / 95 条去重警告**（带 `文件:行:列` + 变量名）。<br>⇒ **主证据应是 Lean 自己的输出（事实）**，静态扫描器**退为补充**，且**必须先在真实警告上做召回率校准**（实测召回 **90.4%**，8 条漏报中 7 条是"日志相对源码陈旧"、1 条是真实解析缺陷）。<br>⚠ **一般化**：**本项目已积累大量构建日志与探针日志**——它们是**零成本的事实数据库**，优先于任何近似推断。 |
| **`unused variable` 警告 = "假设没进证明"，但要区分两种后果** ⚠️ v14 | 实例：`nlinarith` 漏喂关键假设仍"证"出目标（数学上不可能）；另一实例：结论与假设**逐字相同**（`:= hstep`）而 docstring 称其为"核心定理"。<br>⇒ **两种后果必须分开**：**(i) 证明漏用了关键假设**（危险，命题可能未被真正证明）；**(ii) 假设本身多余**（无害的虚假前提，应删）。区分需要**读证明体**，不是看计数。<br>⚠ **且"假设名未出现"本身会产生大量误报**：实测 4,100 个"未出现"名字里 **97.3% 是类型参数**（Lean 根本不会报）；`linarith`/`nlinarith`/`simp`/`omega` **会隐式消费**假设 ⟹ **只把 Lean 真报过的当事实**。 |
| ⭐ **`unknown identifier 'X'` 可能只是"多余收尾"的**伪装**，不是名字问题** ⚠️ v14（**归因更正，值得单列**） | 某代理先报 `RealPosEncodingInterface:305` 的 `unknown identifier 'neg_one'`，
把它归因为"`neg_one` 在 mathlib 里含义不同"（**这个事实本身成立**：它是 `PrimitiveRoots.lean:395` 的 `CharP` 定理）。<br>**但它随后自己实测更正了归因**：<br>```
rw [abs_of_neg h, div_neg_eq_neg_div, div_self (ne_of_lt h)]   -- 此链**已闭合目标**
ring                                                          -- 多余 ⟹ no goals to be solved
```<br>⇒ **`rw` 链把 `θ/|θ| = -1` 依次化为 `θ/-θ = -1` → `-(θ/θ) = -1` → `-1 = -1`（`rfl` 闭合）** ⟹
后面任何收尾 tactic 都是**多余**的；而**当目标已闭合时，`rw [neg_one]` 会被 Lean 当作"待重写的引理"去解析并报 `unknown identifier`**
——**症状完全指向"名字不存在"，真因是"没有目标了"**。<br>**⛔ 把 `ring` 换成别的东西没用**（换一个同样多余的收尾）；**正解是"不要收尾"**。<br>⇒ **同族**：`field_simp` 已关目标后再跟 `ring` 报 `no goals to be solved`。<br>
**⇒ 判别法：见到 `unknown identifier` 时，先看**该行前面是否已有 tactic 把目标关掉了**。** |
| ⭐ **`Replayed` ≠ 真编译 —— 它可能复用**更早**的 olean** ⚠️ v14（**判据陷阱**） | 某模块连续**三轮**都是 `⚠ [N/N] Replayed <Mod>`，被误判为"已通过"。
**实测**：该模块的源码**有 11–13 条真 error**（`v6.evidence.txt` 佐证）⟹
**那个 `Replayed` 复用的是**更早、内容不同**版本的 olean**。<br>⇒ **纪律**：`Built <Mod>` 才是"从当前源码编过"的**唯一**权威证据；
**`Replayed` 只能说明"lake 认为无需重编"**，**不能**作为"该源码可编译"的证据。<br>
⇒ **且这也是"判据必须能证伪"的又一例**：`Replayed` 看起来**像成功**（绿色、无 error），
而它**恰恰是"没有编译任何东西"**——**与"对已最新目标短路"是同一类陷阱的两种表现**。 |
| ⭐ **`neg_one` 不是 `-(1) = -1` 的重写引理** ⚠️ v14（**"名字存在但含义不同"第 7 例**） | mathlib 4.14 里 **`neg_one` 是 `RingTheory/RootsOfUnity/PrimitiveRoots.lean:395` 关于 `CharP` 的定理**：<br>`theorem neg_one (p : ℕ) [Nontrivial R] [CharP R p] (hp : p ≠ 2) : ...`<br>⇒ 写 `rw [..., neg_one]` 报 **`unknown identifier 'neg_one'`**（因为它**不在作用域**，而非"不存在"）。<br>**正解**：`rw [abs_of_neg h, div_neg_eq_neg_div, div_self (ne_of_lt h)]; ring`。<br>⚠ 这是 STYLE 已两度警告的"以名判有无"陷阱的**第 7 次实例**——
**名字存在 ≠ 名字是你要的东西**（同族：`Nat.one_ne_two` 不存在、`Real.exp_one_gt_two` 真名 `Real.exp_one_gt_d9`、`Finset.card_Ioi` 真名 `Fin.card_Ioi`、`Nat.catalan` 真名裸 `catalan`）。 |
| ⭐ **`u - v ≤ w` 与 `\|u - v\| ≤ w` 是**不同命题**** ⚠️ v14（**两个代理独立踩中**） | `abs_sub_abs_le_abs_sub u v` 给的是 **`\|u\| - \|v\| ≤ \|u - v\|`**（**左边不带绝对值**）；而 `IsOneLipschitz f` 要的是 **`\|f a - f b\| ≤ \|a - b\|`**（**左边带**）⟹ **直接 `exact` 必报 `type mismatch`**。<br>**正解**：`rw [abs_sub_le_iff]` 拆成两个单侧，或补 `abs_sub_comm` 对齐。<br>⚠ **另一代理独立报了同一条** —— **两处独立观测 = 强证据**。<br>⇒ **配套坑**：若先 `rw` 把 `\|f x - f y\|` 展开成 `f x - f y`，就**离开了** `abs_sub_abs_le_abs_sub` 的适用范围，需额外 `abs_of_nonneg` 或改用 `abs_sub_le_iff`。 |
| ⭐ **`set_option ... in` 必须在 docstring **之前**** ⚠️ v14（**报错点≠真凶，第四例**） | 错误写法（**docstring 在前、`set_option` 夹在 docstring 与 `theorem` 之间**）：<br>```lean
/-- ... -/
set_option maxHeartbeats 1600000 in
theorem ...
```<br>⟹ 报 **`unexpected token 'set_option'; expected 'lemma'`**（**报错点在 383，真凶是 384 的 `set_option`**）。<br>**正确**：`set_option … in` 必须在 **docstring 之前**。<br>⇒ ⭐ **这与另外三例同族**（**报错点是"被挤错位"的 token，不是真凶**）：<br>• 孤儿 `/--` ⟹ **下一个** `/--` 报错；<br>• `have` 搁在 `calc` **之后** ⟹ 报 `unexpected token 'have'`；<br>• `set_option` 夹在 docstring 与声明之间 ⟹ 报 `unexpected token 'set_option'`。<br>**⇒ 见到 `unexpected token X` 时，一律往回看，找"本该在 X 之前的那个东西"。** |
| ⭐ **`edit` 报 `EACCES (Win32 5)` 时，先查**文件属性**而不是查锁** ⚠️ v14（**环境级，非锁问题**） | 一位代理的 `edit` **全部**报 `ReplaceFileW EACCES (Win32 5)`，而 `who-holds.ps1` 显示**无 bypasser**、锁正常 ⟹
**根因是文件带 `ReadOnly` 属性**（`Get-Item` 的 `Attributes` 含 `ReadOnly`），**不是锁、不是他人占用**。<br>
**修法**：`$it.IsReadOnly = $false`（或 `attrib -R`），然后即可写。<br>
⚠ **⇒ 排查顺序**：**写失败 ⟹ ① 文件属性（`IsReadOnly`）② 锁与占用 ③ 权限/沙箱**。
**不要一上来就怀疑锁**（本波次已有多次误判锁的先例）。<br>
**⇒ 已核实**：全库曾有 **1** 个残留（`RealHypothesisTesting.lean`），**coordinator 已清除**。 |
| ⭐ **`Fintype.card_ne_zero` 的**语句自带 `[Nonempty α]`** ⟹ 用它推 `Nonempty α` 是**循环论证**** ⚠️ v14（**归因更正：曾被误判为"布局陷阱"**） | **pinned 源码**（`Mathlib/Data/Fintype/Card.lean:507`）：
```
theorem card_ne_zero [Nonempty α] : card α ≠ 0
```
⇒ **要证 `Nonempty α` 却先用了需要 `Nonempty α` 的引理** ⟹ **必然合成失败**，
**报错为 `failed to synthesize Nonempty ι`**。<br>
⇒ **正确修法**：把 `[Nonempty ι]` 提为**显式的类型类参数**（⚠ 这正是**本文件另一条已登记的纪律**：
`haveI` **不能**覆盖**定理陈述**里的实例需求，因为陈述在证明体之前精化）。<br>
⚠ **本条曾被我误登记为"`have … := by` 换行后被解析为独立 tactic 块"的**布局陷阱**** ——
**该归因是错的，且已被反例推翻**：
同文件 `avgSmooth_deviation_shrink`（L248 **有** `[Nonempty ι]`）的 **L252-253 用了完全相同的换行写法**，
而它 **不在任何 error 名单里** ⟹ **换行写法本身无害**。<br>
⇒ ⭐ **一般教训**：**"报错出现在某一行"不等于"该行的形式是病因"** ——
必须用**同型对照**（同写法、别的实例、能过）排除形式因素，**再判语义因素**（这里是循环依赖）。<br>
⚠ **且若把本条登记为"布局陷阱"，会引导后续代理去调缩进**（改不动，因为不是那里错）。** |
| ⭐ **`haveI` 不能覆盖**定理陈述**里的实例需求** ⚠️ v14（**推翻一个常见判断**） | 某代理原以为"把 `haveI` 放进证明体即可满足 `Finset.univ_nonempty` 所需的 `Nonempty (Fin n)`"——**错**。<br>
**根因**：**定理陈述在证明体之前精化**，而 `haveI` 是**证明体内的局部实例** ⟹ **不覆盖陈述**。<br>
⇒ **修法**：把 `Nonempty (Fin n)` 提为**显式的类型类参数** `[Nonempty (Fin n)]`，
使**陈述与证明体同处一个实例作用域**（此时 `hn : 0 < n` 变为**冗余**，可删）。<br>
⚠ **判别法**：报错信息里的位置（**陈述** vs **证明体**）决定 `haveI` 能否生效。 |
| ⭐ **`Nat.ceil` 的最小性引理：要的是 `ceil_lt_add_one`，不是"`< ⌈a⌉₊`"** ⚠️ v14 | 某代理在 `conformal_quantile_minimal` 上反复 `linarith failed`，**根因是选错了引理**：
最小性的内容是 **`⌈a⌉₊ − 1 < a`**，而不是 **`< ⌈a⌉₊`**（后者与 `a ≤ ⌈a⌉₊ − 1` **并不矛盾**）。<br>
**正确引理**：**`Nat.ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : ℝ) < a + 1`**（`Floor.lean:450`），变形即得。<br>
⇒ **教训**：**`linarith failed` 未必是"喂的项不够"，也可能是"引理选错"** ——
**先写下你需要的**不等式方向**，再去找匹配的引理**。 |
| ⭐ **`1/2 * card / den` 按**左结合**解析** ⚠️ v14 | `1/2 * card / den` = **`(1/2 * card) / den`**，故 `apply mul_nonneg` 的第二个子目标变成
`0 ≤ den⁻¹`（**不是** `0 ≤ card/den`）⟹ 报 `unsolved goals` / `expected '{'`。<br>
⇒ **修法**：对**整个商**用 **`div_nonneg`** + 显式提供 `hden : 0 ≤ ↑card * ↑den`。 |
| ⭐ **`Nat.cast` 挡住 `rw`：`↑(a*b)` vs `↑a * ↑b`** ⚠️ v14 | `rw [← hPcard]` 的 `hPcard` 右端是 **ℕ 乘法**，而目标里是 **ℝ 乘法** ⟹ 模式不匹配。<br>
⇒ **修法**：先在 ℝ 上建立对应等式（用 `Nat.cast_mul` 桥接），再 `rw`。 |
| ⭐ **`softThresh` 型定义的**证明路线**可能本质上够不到紧界** ⚠️ v14（**"命题真、路线假"**） | 某代理用 `max(y−λ,0) + min(y+λ,0)` 配三角不等式收尾到 `≤ \|y₁-y₂\|`，
**但 `2\|d\| ≤ \|d\|` 是假命题** ⟹ **该路线达不到紧的 `1·\|d\|`**：
**`f ≥ 0 ≥ g` 这一"取值区间相反"的关键事实被三角不等式丢掉了**。<br>
⇒ **正解**：按**分段形式**做区域分情形（每支里 `soft` 是常数或 `y ± λ`，Lipschitz 平凡）。<br>
⇒ **纪律**：**证明走不通时，先问"我的路线是否丢掉了某个关键事实"**，而不是继续调 tactic。 |
| ⭐ **`rw` 会同时命中左右两侧时，用 `conv_rhs`/`conv_lhs` 做**定向重写**** ⚠️ v14（**新坑，实测**） | **症状**：某代理用 `show` 显式化目标后，`rw [← hfix]` 把**左边**的 `xstar` 也替换了 ⟹
`hG` 类型不匹配（报 `xstar` vs `G xstar`）。<br>
**根因**：`rw` **重写目标中所有匹配的子项**，无法只改一侧。<br>
⇒ **修法**：`conv_rhs => rw [← hfix]`（**只在右侧替换**）。
**同族工具**：`conv_lhs`、`nth_rewrite`、`conv … => …` 的组合。<br>
⭐ **一般化**：**"我要改的"与"`rw` 会改的"不总是同一集合** ——
当同一子项在目标里出现两次而只需改一次时，**必须用定向重写**。 |
| ⭐ **`exact ⟨a, b⟩` 误拆成两个 `·` 分支 ⟹ `type mismatch` + 级联 `no goals`** ⚠️ v14 | **症状**：报 `type mismatch` **加** `no goals to be solved`（**两条 error、一个根因**）。<br>
**根因**：目标是**单个 `∧`** 时，必须先 `constructor`/`refine` 才能分两支；
直接写 `· exact a` / `· exact b` ⟹ 第一支就把整个 `∧` 目标交给 `a` ⟹ 类型不符；
第二支落在**已关闭的**目标上 ⟹ `no goals`。<br>
⇒ **修法**：改回 `exact ⟨_, _⟩`（或**先** `constructor` **再**分两支）。<br>
⚠ **与已登记的"多余收尾"同族但不同**：那条是"目标已关还继续收尾"，
这条是"**结构错位导致第二支无目标**"——**报错点（`no goals`）在后果处，真凶在前一行**。 |
| ⭐ **多行 `\| arm =>` 体必须用 `·` 聚焦子弹包裹** ⚠️ v14（**24 处 → 0 error 的一条形态律**） | 否则 Lean 把**后续的 `\| cons …` 解析进 arm 体内**，报
**`alternative 'cons' has not been provided`** + `unexpected token`。<br>
**固定形态**（实测把 **24 处** arm 全改成它后：**24 error → 0 error**）：
```lean
| cons a3 r3 => cases r3 with
  | nil =>
    · simp only [compile_constraint] at h
      injection h with h'
      subst h'
      exact degenerate_collinear a1 a2 a3
  | cons _ _ => simp [compile_constraint] at h
```
⚠ **配套事实**：命中分支的 `h` 形状是 **`some (IRConstraint.collinear a1 a2 a3) = some ir`（有 `some`）** ⟹
**`injection h with h'` + `subst h'` 是正确方向**，**但必须配 `·` 子弹才能生效**。<br>
⇒ **与"`<;>` 作用域"那条合起来**：**`cases … with` 的分支体既不能依赖尾部 `<;>`，多行时又必须用 `·`**。 |
| ⭐ **`cases … with \| arm => tac` 的尾部 `<;>` 不会作用到前面 arm 的目标** ⚠️ v14（**最难查的一类**） | **最小复现**（已实测）：
```lean
cases kind <;>
  (cases args with
   | nil => simp [f] at h        -- ← 这个 arm 的目标「逃逸」了尾部 <;>
   | cons a1 r1 => …) <;>
  (我的收尾)
```
报 **`case mk.a.cons.cons.cons.nil … ⊢ sem ir`**，**行号恰好指向 `\| nil =>` 那一行**。<br>⇒ **看起来像"arm 的 tactic 失败"，实为"我的收尾从未被执行"**。<br>⚠ **这解释了为什么连续 4 轮把 `rw`→`subst h`→`cases h`→`injection h` 换了个遍都报同一个错**——
**它们根本没跑**。<br>⇒ **修法：把收尾写进每个 arm 内部**（平铺、逐 arm 自闭合），**不要依赖尾部 `<;>`**。 |
| ⭐ **`first` 的杀手不是"成功但不闭合的 `simp`"，而是"不报错的 `exact`"** ⚠️ v14（**归因细化**） | 某代理先用探针证实：`exact degenerate_collinear _ _ _` 在**构造子不匹配**时**并不报错**——
它把隐式 `String` 元变量留下、**目标未闭合**，于是 **`first` 立刻接受第一个分支、从不尝试后续 11 个**。<br>⇒ 探针同时给出 `warning: 'exact sem_b _ _' tactic does nothing` / `this tactic is never executed`。<br>**修法**：给每个 `exact` 后面加 **`<;> done`**，**逼它真失败**——而不是"显式穷举 12 形状"（那是另一个正确但更笨的办法）。<br>⚠ **与上一条的区别**：`<;>` 作用域问题让收尾**从不执行**；`first` 问题让首个分支**假成功**。**两者症状都是"报错指向 arm 那一行"，但病因不同。** |
| ⭐ **判"谁在排队/谁在绕锁"必须看**父进程链**，不能看**进程计数**** ⚠️ v14（**我在同一个错误上栽了两次**） | **第 1 次**：我用"`lean.exe` 计数"判断是否有代理绕过锁 ⟹ 误判（因为 `lean-lock.ps1` **自己**就会执行 `lake env lean`，那是**合法**的）。改用 **`scripts/who-holds.ps1` 的父进程链**才对。<br>
**第 2 次**（v14）：我用"命令行含 `lake-lock` 的进程计数"判断**重复排队** ⟹ 得到"31 个进程、10 组目标、近一半重复"的结论，**并据此向一位代理发出了"你是否重复入队"的质询**。<br>
**实测父子关系后推翻**：每一组都是「**一个顶层 + 一个子 shell**」（子 shell 来自 `Tee-Object`/`Out-String` 等管道），
**不是两个独立排队者** ⟹ **真实排队者 = 10，与票数吻合** ⟹ **没有任何人重复排队**。<br>
⇒ ⭐ **纪律**：**凡"计数"得出的结论，先问"这些进程/文件的**父子/归属**关系是什么"**。<br>
**⇒ 一般化**：**表象计数 ≠ 机制计数**；**机制要靠关系（父链、所有权、票龄）而非数量**。<br>
⚠ **且我因此向代理发出了一个错误质询** —— **发现后立即撤回并道歉**（撤回留痕同样是纪律）。 |
| ⭐ **锁等待期间只做**只读分析**，不做编辑** ⚠️ v14（**编排纪律，来自实测数据**） | **实测**：单次构建的**等待**时长可达 **2725s ~ 8536s**（45 分钟 ~ 2.4 小时），
而**构建本身**只占几分钟 ⟹ **瓶颈是排队，不是计算**。<br>
**后果**：代理在等待里**持续编辑** ⟹ **改动层层叠加、未经任何检验** ⟹
某代理实测"**45 条 error 中 15 条是自己在等待期间引入的**"。<br>⇒ **纪律**：**在锁等待期间，(a) 读诊断、(b) 读 pinned 源码核实 API、(c) 代小整数验命题真假
—— 这三件都是**只读**的、**不会堆积未检验改动**；(d) **不要编辑**。**<br>
**配套**：**改动分批冻结**（每批一个逻辑单元），**改完即入队**，不要"等锁期间无限叠加"。 |
| ⭐ **命名前先 grep **大小写变体**** ⚠️ v14（**本波次已两例；且第一次的检测工具本身有大小写缺陷**） | **两个实例**：<br>
① `GD_converges` vs `gd_converges` —— ⚠ **检测工具用 PowerShell `@{}`（默认大小写不敏感）** ⟹
**误报 14 处"幽灵冲突"**；改用 `StringComparer::Ordinal` 才得到 **1 处真冲突**；<br>
② `normsq`（`RealProximalMoreau:65`，**0 importer**）vs `normSq`（`RealHessian:60`，**6 importer**）——
**定义体逐字符相同、仅差一个字母的大小写**；**当前无文件同时 import 两者** ⟹
属 **X3 所记"潜伏命名冲突"**，不是活冲突。<br>
⇒ **纪律**：**给新定义命名前 grep 大小写变体**；<br>
⚠ **且检测工具必须大小写敏感**（PowerShell `-match` **默认忽略大小写** ⟹ 用 **`-cmatch`** 或 grep 工具）。<br>
⚠ **风险面**：一旦某文件同时 import 两者，在 `open Lattice` 下**一字母之差肉眼不可辨** ⟹ 误用。 |
| ⭐ **"存在更一般的实现" ≠ "应该换成它" —— 泛化只在**下游真需要**时才付代价** ⚠️ v14（**重复收敛的处置原则**） | **实例**：全库有两份法方程——`RealNormalEquation`（**`ℝ` 版**）与 `RealNormalEquationScalar`
（**域参数化到任意 `RCLike 𝕜`**）。`RealGaussianProcess` 引用的是 `ℝ` 版，**只 import `RealLeastSquares`（`ℝ` 版）**。<br>
**朴素的读法**："有更一般的版本 ⟹ 应该换过去"。**实测的正确判断**：
> **该定理的所有对象（`K`/`y`/`mu`）本身就是 `ℝ` 值** ⟹
> **换用一般版只增加 import 面，无任何实质收益** ⟹ **保留 `ℝ` 版 + 加交叉引用**。

⇒ **纪律**：**收敛"平行实现"时，先问"调用方的类型是否已特化"**：
- **已特化** ⟹ **保留现状 + 交叉引用**（**零风险**）；
- **确实需要一般性** ⟹ 才换，**并评估 import 面与成环风险**。<br>
⚠ **同族的反向教训**：`RealRMSNormSharpness` 的紧常数 `√n/c` **确实应该被下游采用**
（下游**已经在用松弛版**，换过去有**实质收益**：端到端常数收紧 2 倍）——
**这两种情形必须区分**：**"更强的结论下游没用上"是真缺陷；"更一般的类型下游不需要"不是。** |
| ⭐ **协调者批量**会与代理的**单独调用**重复排队 ⟹ 排前先查"这个模块是否已有人在建"** ⚠️ v14（**编排层，实测**） | **实测**：我排的 v11（19 模块）里，**4 个模块（`RealOverSmoothingSharp`/`RealConversionStability`/`RealConformalPrediction`/`RealSSMDiscretization`）
同时被它们各自的代理以单模块形式排队** ⟹ **同一文件占两个队位**。<br>
⚠ **背景数据**：单次构建**等待** 2725~8536 秒，而**构建本身只几分钟** ⟹ **瓶颈是队列长度** ⟹ **每个重复队位都直接推后所有人**。<br>
⇒ **纪律（协调者视角）**：
1. **排批量前，先枚举当前所有 `lake-lock`/`lean-lock` 顶层进程的目标**（见下），**扣除**已有人在建的；
2. **只排"没人覆盖"的模块** —— 实测本波次真正无代理覆盖的只有 **2 个**（`RealKRDuality`/`RealLayerScaleDepth`）；
3. **宁可批次小**：**2 个不重复的模块** 优于 **19 个含 4 个重复的模块**。<br>
**枚举命令**（一行）：列出顶层 lock 进程与其目标，**用父进程去重**避免把子 shell 算成独立排队者：
```powershell
$procs = Get-CimInstance Win32_Process -Filter "Name='powershell.exe'" |
  Where-Object { $_.CommandLine -match '(lake-lock|lean-lock)\.ps1' }
$seen=@{}; foreach($p in $procs){ if($seen.ContainsKey($p.ParentProcessId)){continue}; $seen[$p.ParentProcessId]=$true
  [regex]::Match($p.CommandLine,'(lake-lock|lean-lock)\.ps1"?\s*([^\s|&]*)').Groups[2].Value }
```
⚠ **注意**：**必须按 `ParentProcessId` 去重** —— 实测 28 个进程里约一半是**子 shell**（`| Out-File` 产生），
**不是独立排队者**（本波次我已因此误判过一次并错误质询了代理）。 |
| ⭐⭐ **PowerShell 5.1 把**无 BOM** 的 UTF-8 脚本当 ANSI 读 ⟹ 脚本里的中文字面量变 `????`** ⚠️ v14（**"检查器静默地什么都没查"**） | **实测**：一个含中文正则的脚本报
`Cannot convert value "(?:????)" to type Regex ... Quantifier {x,y} following nothing`
—— **中文字面量被解成 `????`**。<br>
⇒ ⚠ **最危险的形态不是报错，而是**静默**：某检查器因该原因报"**0 处命中**"，
而它本该在含 **300+ 命中行**的库里找到东西** ⟹ **一个看起来通过的检查器，什么也没查**。<br>
⇒ **修法（在脚本里）**：**用码点构造中文字符串**，不要写字面量：
```powershell
function Get-CpString { param([int[]]$Codes) -join ($Codes | ForEach-Object { [char]$_ }) }
$pattern = Get-CpString @(0x673A, 0x5668, 0x9A8C, 0x8BC1)   # 机器验证
```
⚠ **且函数名不要用 `CP`** —— 它是 `Copy-Item` 的**别名**，会被解析成命令（实测报
`Cannot find path '...\26426'`）。用 `Get-CpString` 这类**动词-名词**形式。<br>
⚠ **这是本项目已登记的"编码陷阱"的新变体**：原先记的是**输出**编码（`Set-Content -Encoding UTF8` 加 BOM、
`Get-Content -Raw` 破坏 Unicode），**现在是**脚本输入**编码** —— **同一问题的另一面**。<br>
⇒ ⭐ **一般教训**：**"检查器报 0" 与 "检查器正确且库里真没有" 是两件事**；
**上线任何检查器前，必须用一个人为植入的已知缺陷验证它能报出来**（本次即用合成文件验证 `0 → 1`）。 |
| ⭐ **`rw [a, b, c]` 是**顺序执行**的 —— 第一条改写后，后续模式可能已失配** ⚠️ v14 | **症状**：`rw [max_eq_left h1, if_neg h3, …]` 报
`pattern -lam ⊔ 0` **失配**。<br>
**根因**：`rw` 的列表**按序**改写，**第一条改写后目标已变形**，第二条起的模式是基于**旧形状**写的。<br>
⇒ **修法**：改用 **`simp only [max_eq_left h1, if_neg h3, …]`**（**一次性**，simp 在**同一轮**内匹配）。<br>
⚠ **同族**：**不要在同一条 `rw` 链里混用"改写前/改写后"两种形式的引理**（另一代理独立总结过）。 |
| ⭐ **定义相等但**句法不同** ⟹ `rw` 失配** ⚠️ v14（**`-lam` vs `0 - lam`**） | `subst hy` 之后目标里是 **`0 - lam`**，而假设写的是 **`-lam`**
—— **两者定义相等，但 `rw` 做的是**句法**匹配** ⟹ 失配。<br>
⇒ **纪律**：**假设的陈述形式要按目标的**字面形式**写**（或改用 `simp only`/`ring_nf` 归一化后再匹配）。<br>
⚠ **同族**：`⊔` vs `max`、`n+1` vs `n`、`↑(a*b)` vs `↑a * ↑b`。 |
| ⭐ **`subst` 会把字面模式**消掉**（`?a - 0` 消失）** ⚠️ v14 | `subst h` 把目标变成 `(1/2)(0-y)^2 + lam*0 - (1/2)y^2` ⟹ **没有字面的 `- 0`**，
故 `rw [sub_zero]` 报 `pattern ?a - 0` **失配**。<br>
⇒ **修法**：`subst` 之后**用 `simp only`/`ring` 而非针对旧字面形状的 `rw`**。<br>
⚠ **同族**：`subst` 后 `rw [h]`/`rw [hst]` 失效（本波次已多次记录）。 |
| ⭐ **显式参数必须按位置传（`l1Objective_of_neg lam y (y + lam) hneg`）** ⚠️ v14 | `(lam y x : ℝ) (hx : x < 0)` 中 **`x` 是显式参数** ⟹
写成 `l1Objective_of_neg lam y hneg` 会把 `hneg` 当 `x` ⟹ 报
`application type mismatch: expected ℝ but got y+lam < 0`。<br>
⇒ **纪律**：**看到 `expected ℝ but got <Prop>` 这类报错，就是在提示你把证明当成了参数。** |
| ⭐⭐ **把 `(by …)` **内联进 tactic 的参数列表**会让类型类合成"卡住"** ⚠️ v14（**新失败模式**） | **实测**（一位代理在真编译中命中，**coordinator 已核实其源码注释**）：
```lean
-- ❌ 报：typeclass instance problem is stuck: PosMulStrictMono ?m.149995
--        连带：unexpected identifier; expected ']'
nlinarith [sq_nonneg x, mul_nonneg (le_of_lt h) (by linarith : (0:ℝ) ≤ lam - y)]
--          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- ✅ 修法：把侧条件**提成命名 `have`**，再用 `mul_pos`/`mul_nonneg` 建事实
have hside : (0:ℝ) ≤ lam - y := by linarith
have hprod : 0 ≤ x * (lam - y) := mul_nonneg (le_of_lt h) hside
nlinarith [sq_nonneg x, hprod]
```
⚠ **根因**：**Lean 先对 `mul_nonneg` 做类型类合成**，
而**内联证明的惰性**让实例参数（如 `PosMulStrictMono ?m`）**在需要实例名处仍是元变量** ⟹ **卡住**。<br>
⭐ **⇒ 且它有一个**误导性的连带症状**：`unexpected identifier; expected ']'` ——
**那是列表因类型类卡死而解析失败的**语法**表现**，
⚠ **若只盯着语法错会修错方向**（**同族：已登记的"`unexpected token X` 的报错点是被挤错位的 token"**）。<br>
⭐ **判据**：**tactic 参数列表里出现 `(by …)` ⟹ 考虑先提成 `have`** ——
**代价是两行，收益是避开一个难判读的卡死**。<br>
⭐⭐ **⚠ 但必须区分两类内联 —— 一位代理实测给出精确边界**（**coordinator 已核实其两处实例**）：
| 内联位置 | 是否危险 | 理由 |
|:--|:--|:--|
| ⚠ **传给"需要类型类合成的算子"**<br>（`mul_pos`/`mul_nonneg`/`smul`/`pow` …）| ❌ **危险** | **算子要先合成实例**（`PosMulStrictMono`/`MulPosMono` 家族）<br>⟹ **惰性让实例参数停留为元变量 ⟹ 卡住** |
| ✅ **传给 `rw`/`simp` 作为**命题****<br>（`rw [if_neg (by linarith : ¬ P)]`）| ✅ **安全** | **它们只要一条**证明项**，**不涉及实例合成**** |
**⇒ 判据（精确版）**：**问"这个 `(by …)` 是**实例的实参**还是**命题的实参**"** ——
**前者提成 `have`，后者可留。**<br>
⚠ **且一位代理用此判据发现它"修了一处、漏了同族的另一处"**（**修了 `mul_pos` 却漏了 `mul_nonneg`**）
⟹ ⭐ **⇒ 修完一处后，**按模式扫描全文件的同类用法**（**这是"只读审读"能抓、而编译反馈要等一轮的缺陷**）。 |
| ⭐⭐ **免锁 `lake env lean` 的**精确适用条件**：被 import 的本项目模块**必须已有 olean**** ⚠️ v14（**coordinator 两组对照实验实测；一条过强结论被收窄**） | **coordinator 的对照实验**（**都是裸跑**，不经 `lean-lock`）：
| 探针 | 结果 |
|:--|:--|
| `import RealFCA`（**该模块**有 olean**）| ✅ **`exit=0`**，`#check @Lattice.intent` **正常解析** |
| `import RealRKHSKernel`（**该模块**无 olean**）| ❌ `exit=1`：`unknown module prefix 'RealRKHSKernel'` |
⇒ ⭐⭐ **精确结论**：
> **免锁通道可用 ⟺ 被 import 的本项目模块**已有 olean****；
> ⚠ **它**不会凭空编译依赖** ⟹ **依赖尚未构建时，探针**必须**走 `lean-lock` 排队。**

⚠ **本条的来历值得记录**：**一位代理报"免锁自检**不可行**"**（**它 15 轮探针全部排队**）；
**另一位代理**则用它成功验证了 5 个模块**。
⇒ ⭐ **⇒ 两者都对，差别在**依赖是否已构建**** ——
**coordinator 的对照实验把"不可行"收窄为"条件性可行"。**<br>
⚠ **教训**：**报告"某方法不可行"时，要给出**触发条件**，否则会误禁一个有效手段**（**反向亦然**）。 |
| ⭐⭐⭐ **引用了一条**根本不存在的** mathlib 引理（**伪造名字**）** ⚠️ v14（**本波次已 5 例，高频类**） | **实测**：`Real.sqrt_sum_sq_add_sqrt_sum_sq_le` —— ⚠ **该引理在 mathlib 4.14 **完全不存在****<br>（`#check` 证实；**试了 6 个候选名**全部 `unknown`；**coordinator 全库 grep = 0 处**）。<br>⚠ **它比"拼错名字"更隐蔽**：<br>| 情形 | 表现 |<br>|:--|:--|<br>| 拼错**已存在**的名字 | `unknown constant` ⟹ 作者会去查真名 |<br>| ⭐ **伪造一个**结构合理、像真的**名字** | ⭐ **同样报 `unknown constant`**，<br>⚠ **但作者/审阅者会以为"我记错了"而非"它根本不存在"** |<br>⭐⭐ **⇒ 判据**：**凡引用 mathlib 引理，**必须先 `#check` 或 grep 确认其存在**** ——<br>⚠ **"名字看起来对"不是证据**。<br>⭐ **⇒ 同族已有 5 例**：`mul_self_sqrt`（真名 `Real.mul_self_sqrt`）/ `Fin.val_castSucc`（真名 `Fin.coe_castSucc`）/ <br>`Finset.sum_filter`（真名是 `prod_filter` 的 `to_additive`）/ `div_congr`（无此名）/ **本条**。 |
| ⭐⭐⭐ **错误信息里出现 `(fun … => h)` / `(fun {n} => h)` ⟹ **不是"缺实参"，而是 `Prop` 假设被强制转换成函数**** ⚠️ v14（**两位代理 + coordinator 都误判为"缺实参"**） | **实测**（探针坐实，非推断）：<br>``IsPSDKernel`` 是**定义体本身为 ∀-函数的 `def`** ⟹ **`hpsd : IsPSDKernel K` **可强制转换为函数****<br>（**`hpsd x v` 能通过类型检查**）。<br>⚠ **后果**：`f K hpsd a b` 中，**Lean 走"`hpsd` 其实是函数"这条路**，<br>**把 `a` 吃成 `{n}`/`x`、`b` 吃成 `v`**，**然后发现第 3 个实参缺失** ⟹<br>**报 `argument `a` has type α but is expected to have type IsSymmKernel K`**。<br>⭐⭐ **⇒ 判据**：**错误信息里的 `(fun … => h)` 是那次强制转换的**证据****，**不是笔误**。<br>⭐ **修法**：**补齐真正缺失的那个实参**（**而非"再加一个"**）。<br>⚠ **⇒ 同族（本波次）**：**"`def` 是不透明的 ⟹ instance 搜索不展开它"**（**`DecidablePred` 失败**）；<br>⭐ **两者都是"`def` 的展开性"造成的误判****：<br>**前者是 instance 搜索**该展开却不展开**；后者是 elaboration **不该展开却展开了****。 |
| ⭐⭐ **`unused variable 'h…'` 是「空洞性**候选**信号」，**候选 ≠ 判定**** ⚠️ v14（**本波次已 3 次被推翻**） | **实测（本波次三次实例）**：<br>| # | 候选信号 | 被推翻为 |<br>|--:|:--|:--|<br>| 1 | `unused variable 'hD'` ⟹ 审计判**"假命题"** | ⭐ **空洞真**（`c<0` 时 `hConc` 不可满足）|<br>| 2 | `unused variable 'hAx'` ⟹ 判"前提夸大" | ⭐ **真冗余**（删后证明体原样通过）|<br>| 3 | ⭐ **5 处 `unused variable 'h…'` ⟹ 判"空洞性候选"** | ⭐ **4/5 是**真冗余****（仅 `hN` 沾边界空洞）|<br>⭐⭐ **⇒ 正确流程（三步，缺一不可）**：<br>**① 取编译器报的 `文件:行:列`**（⚠ **不能靠"名字出现几次"判断**）；<br>**② 判断是**命题假设**（`h…`）还是**类型/数据参数**（`A`/`k`）；<br>**③ 对假设做**去假设 / 边界见证****：<br>&nbsp;&nbsp;· 删掉后**证明体原样通过** ⟹ ⭐ **真冗余（可删）**；<br>&nbsp;&nbsp;· 删掉后**结论为假** ⟹ ⭐ **承重假设**；<br>&nbsp;&nbsp;· **假设本身不可满足** ⟹ ⭐ **空洞真**；<br>&nbsp;&nbsp;· **该假设被其它假设蕴含** ⟹ ⭐ **可导出 ⟹ 真冗余**。<br>⚠ **⇒ 且"可删"与"该删"不同**：若它是**接口对齐**或**语义标注** ⟹ **保留 + docstring 注明**。 |
| ⭐⭐⭐ **"假命题" vs "空洞真"的分界：反例是否满足该命题【**原有的全部假设**】** ⚠️ v14（**本波次一次审计误判的根因**） | **判据（三分类）**：<br>**① 反例**满足**原有全部假设 ⟹ **命题为假****（该假设不排除它，命题真的错）；<br>**② 反例**违反**某假设 ⟹ **不是反例**；若"去掉该假设后命题为假" ⟹ **该假设是**承重的****；<br>**③ 某假设**本身不可满足**** ⟹ ⭐ **空洞真（vacuity）**。<br>⭐⭐ **⇒ 本波次实例**（一次审计与一位修复代理的**分歧**，后者正确）：<br>审计称 `RealScalingLawBound` 为**假**，反例 `D=0, f=[1,0]`；<br>⚠ **但 `hConc : E[(f−Ef)²] ≤ c/D` 在 `D=0` 时要求 `1/4 ≤ 0`** ⟹ ⭐ **反例**违反**假设** ⟹ **不是反例**。<br>⭐ **正确类别是 **空洞真****（`c < 0` 时 `hConc` 不可满足）。<br>⭐⭐ **⇒ 且 `unused variable 'hD'` 的真实含义由此明确**：<br>**它不是"假设可省"，而是"**该假设想排除的边界从未被真正排除**"** ⟹ ⭐ **对应**空洞性**，不直接对应"假命题"**。<br>⚠ **⇒ 行动判据**：**见到 `unused variable 'h…'`（命题假设）时，构造**去假设**反例**（**不是"反命题"反例**）；<br>⭐ **且 `unused variable 'A'/'α'`（类型参数）属于**接口形状**** ⟹ **保留 + 注明**。 |
| ⭐⭐ **"加假设"**不等于**"修命题"**：若加的假设在证明中**未被使用**，那只是**缩小定义域**** ⚠️ v14（**`unused variable` 是最强判据**） | **实测**（审计代理发现，coordinator 复核）：<br>`isSymmKernel_iff_gram_psd (hsymm : IsSymmKernel K)` 被登记为"**显式加对称假设的正确版本**"，<br>⚠ **而内核报 `unused variable 'hsymm'`**，且探针坐实 **`IsPSDK K ↔ GramPSDK K` 是 `Iff.rfl`**（**完全不需要对称性**）。<br>⇒ ⭐ **⇒ 它并**不修复** `⟸` 方向，只把**定义域缩小**到对称核。**<br>⭐⭐ **⇒ 判据**：**凡"被登记为修复"的加假设，必须检查该假设是否**真的被使用**** ——<br>⚠ **若 `unused variable`，则它是**接口约定**（缩小定义域），**不是定理修复**。**<br>⚠ **⇒ 同族**：本波次"假设写松"家族已 5 例（缺 `0≤λ` / `1≤σ²` / `Σp=Σq` / `Σp=1` / **`0≤c` + 未用 `hD`**）——<br>⭐ **而 `unused variable` 正是它们的**共同机械信号****。 |
| ⭐⭐ **`nlinarith only [...]` 是**白名单**，不是"提示"** —— 缩小搜索集时**必须逐一核对必需假设**** ⚠️ v14（**"性能修复引入逻辑缺陷"的典型**） | **实测**（一位代理连续三轮，错误性质来回摆动）：<br>`r14` 真逻辑缺陷 → `r15` **心跳超时**（性能）→ `r16` **`linarith failed`**（⚠ **修过头**）。<br>**根因**：把 `by nlinarith : False` 改为 `nlinarith only [hxeq]` 修性能，<br>⚠ **却把推出矛盾所必需的 `hy' : y < -lam` 排除了**（**报错上下文里 `hy'` 明明存在却未被使用**）。<br>⭐ **判据**：**看报错上下文与 `only` 列表的**差集****。<br>⚠ **症状**：`linarith failed to find a contradiction`，**而上下文里有关键假设未被使用**。<br>⭐⭐ **⇒ 与"心跳超时"（假设太多，用 `only` 减）配对**：<br>**`only` 用过头 = 又把必需假设排除了** —— ⚠ **两者是一对相反的错误，必须在同一处反复核对。** |
| ⭐⭐ **`nlinarith only [...]` 的白名单必须含**非负性提示**（`sq_nonneg`/`abs_nonneg`）** ⚠️ v14（**与"心跳超时""only 漏假设"构成三件套**） | **实测**：结论为"**某个由非负项组成的和 = 0 ⟹ 不可能**"时，<br>⚠ **必须显式把 `sq_nonneg …` / `abs_nonneg …` 列进白名单** ——<br>**否则 `nlinarith` **只做线性组合**，**不会自己构造"平方 ≥ 0"**。<br>⚠ **与全上下文 `nlinarith` 不同**：**全上下文时会自动捡起上下文里的非负性引理，`only` **不会**。**<br>⭐⭐ **⇒ 三件套（同一 tactic 的三个相反坑）**：<br>| # | 现象 | 根因 | 修法 |<br>|--:|:--|:--|:--|<br>| 1 | `timeout` | **假设太多** | **加** `only [...]` |<br>| 2 | `linarith failed`（上下文有未用假设）| **`only` 漏了必需假设** | **补回** |<br>| 3 | `linarith failed`（上下文无非负提示）| ⭐ **`only` 缺 `sq_nonneg` 类提示** | ⭐ **显式列出** |<br>⇒ ⭐ **判据**：**`only` 列表必须含三类**：① 等式 ② 不等式 ③ **非负性提示**。<br>⚠ **缺任何一类都以 `linarith failed` 失败，而报错**不指出缺了哪一类**。** |
| ⭐⭐ **`nlinarith` 默认吃**整个上下文** ⟹ 在"大上下文"里会**心跳超时**（性能，非逻辑）** ⚠️ v14（**与"缺假设"修法**相反****） | **实测**：`(deterministic) timeout at `isDefEq`` / `Linarith.SimplexAlgorithm.Gauss.getTableauImp`，<br>**报错行号指向 `nlinarith` 那一行**，且**报文里完全不提"哪个假设太多"**。<br>**根因**：`nlinarith` 把上下文**所有**假设纳入 `Simplex` 搜索；<br>⚠ **当上下文含大量大公式（如 `∀ x, 0 ≤ x → … → 0 ≤ l1Objective …`）时表爆炸。**<br>⭐ **修法**：⭐ **`nlinarith only [h₁, h₂]`**（**显式最小假设集**）。<br>⭐⭐ **⇒ 与"逻辑失败"的区分（修法相反）**：<br>| 报文 | 含义 | 修法 |<br>|:--|:--|:--|<br>| `linarith failed to find a contradiction` | **缺假设** | **补**假设 / 换 tactic |<br>| ⭐ **`timeout at …` / `max heartbeats`** | ⭐ **假设太多** | ⭐ **减**假设（`only [...]`）|<br>⭐ **判据**：**同一个 `nlinarith` 在"小上下文"里能过、在"大上下文"里超时** ⟹ 用 `only`。 |
| ⭐⭐ **`rw` **不**做环归一 ⟹ `0 = a − a` / `x + 0 = x` 这类"定义相等但非语法同一"的目标**不会**被关掉** ⚠️ v14（**报 `unsolved goals` 但看起来"该关的已经关了"**） | **实测**：`rw` **只在结果变成 `a = a`（语法同一）时自动闭合**；<br>⚠ **对 `0 = lam − lam`、`x + 0 = x`、`a * 1 = a` 这类**定义上相等但句法不同**的目标，`rw` **不替你关掉** ⟹ 报 `unsolved goals`。<br>⭐ **修法**：补一行 **`ring`**（或 `simp`）。<br>⚠ **且这与 `linarith` 的原子问题**同族**：<br>⭐⭐ **`linarith`/`omega`/`ring` 都只认**句法同形**的原子** ——<br>**若两条假设谈同一个量但一个已展开、一个未展开（如 `l1Objective lam y x` vs `½(x−y)² − λx`），<br>`linarith` 视为**两个不同原子** ⟹ 无法连接**。<br>⇒ ⭐ **判据（合并条）**：**改写必须对**所有相关假设同步进行**（`rw … at h₁; rw … at h₂`），<br>且**`rw` 之后若目标是定义相等的非语法同一式，必须补 `ring`/`simp`**。<br>⚠ 本波次同族已 2 例（`unfold … at *` 破坏 `omega` 原子对齐 / **本条"只展开了一条假设"**）。 |
| ⭐⭐ **"路线级缺陷"的第四形态：**中间断言本身为假****（**看似显然的严格不等式，在小整数边界处假**）⚠️ v14（**一位代理花了 5 轮，而代一个整数 1 秒可验**） | **实测**（coordinator 用精确有理数复现）：<br>**上下文** `-lam ≤ y ≤ lam` 且 `x > 0`；**中间断言** `hpos3 : 0 < lam - y`。<br>⚠ **取 `y = lam`**（**被 `y ≤ lam` 允许**）⟹ `lam - y = 0` ⟹ ⭐ **`0 < 0` **假**** ⟹ **`linarith` 必然失败**。<br>⭐ **正确中间量**：由 `hxeq` 得 `0 = x·(x/2 − y + lam)` ⟹ `x > 0` ⟹ `½x = y − lam ≤ 0` ⟹ **与 `x > 0` 矛盾**。<br>⭐⭐ **⇒ 四种路线级缺陷（完整表）**：<br>① **循环论证**（用待证命题证自己）；② **整节路线结构错**（拆分方式不可能成功）；<br>③ **假中间引理**（整条 `have` 陈述假）；⭐ ④ **中间断言本身为假**（**看起来"显然"**）。<br>⚠ **③ 与 ④ 的区别**：**③ 容易怀疑（陈述复杂）；④ 不易怀疑（断言短、像公理）**。<br>⭐ **判据**：**凡**严格不等式**（`0 < …` / `<`）都要问"**取等号时成立吗**"** ——<br>⚠ **本波次"边界取等"家族已有 5 例**（`conformal_quantile_minimal` / `marginal_…` / `softThresh_eq` / `posteriorVariance_nonneg` / **本条**）。 |
| ⭐⭐⭐ **循环论证："单调性 + 绝对值拆分"关闭 Lipschitz 类证明时，第二个分量需要的**上界**正是待证命题** ⚠️ v14（**新失败类；coordinator 已逐步复现**） | **实测**（一位代理在**同一位置**连续两轮撞同一错，**换 `nlinarith`/改名/重排均无效**）：<br>
```lean
-- 目标：|f(y₁) − f(y₂)| ≤ |y₁ − y₂|
-- `abs_sub_le_iff` 拆成两个单侧目标。在 `y₁ ≤ y₂` 支（|y₁−y₂| = y₂−y₁）：
--   (A) f(y₁) − f(y₂) ≤ y₂ − y₁   ← 左端 ≤ 0（单调性）、右端 ≥ 0 ⟹ 【平凡】
--   (B) f(y₂) − f(y₁) ≤ y₂ − y₁   ← ⚠⚠ 【这就是待证命题本身】
```
⚠ **而单调性只给 `f(y₂) − f(y₁) ≥ 0`（**下界**），(B) 要的是**上界** `≤ y₂ − y₁`**
⟹ **那个上界正是 1-Lipschitz 性质本身** ⟹ ⭐ **循环。**<br>
⭐ **coordinator 的数值确认**（`f = softThresh 1`）：`y₁=1.5, y₂=1.6` 时
**`f(y₂)−f(y₁) = 0.1 = y₂−y₁`（取等）** ⟹ **上界是**紧的**，不可能由下界推出**。<br>
⭐⭐ **⇒ 这是"归因错误"的**第三种形态****：
| 形态 | 症状 |
|:--|:--|
| ① **级联症状** | 一个根因产生大量 `unknown identifier` |
| ② **测量口径** | 数错了（计数 vs 父链、队列龄 vs 持锁龄）|
| ⭐ **③ 循环论证** | ⭐ **`linarith failed` 在**同一位置反复出现**，**换 tactic/改名/重排均无效**** |
⇒ ⭐ **判据**：**结构性收敛的证明（Lipschitz/单调/非扩张）若用"单调性 + 绝对值拆分"关闭，
必须**单独检查第二个分量是否需要上界****；**若要，则路线无效，须改用**区域直接分情形****
（每支里函数是常数或平移 ⟹ 差值平凡）。<br>
⚠ **⇒ 与"命题为假"的区别**：**命题是真的**（**只是证法不可能成功**）——
**同族但更严重：假命题可改命题；循环论证只能重写路线。** |
| ⭐⭐ **`unknown identifier` 的**第三类**：**前向引用**（名字在**作用域内的未来**）** ⚠️ v14（**新增，前两类未覆盖**） | **本文件原登记两类**：(a) **目标已被前面的 tactic 关掉**；(b) **名字真不在作用域/写错**。<br>
⭐ **一位代理发现了第三类**（**coordinator 已核实**）：
> **名字**确实存在**、写法**完全正确**、**类型本身合成正常**，
> **但它声明在**使用点之后** ⟹ Lean **逐条顺序处理声明** ⟹ 使用处尚未进入作用域。**

**实测**（`RealInformationGeometry.lean`）：
```lean
-- 修前：使用在前、声明在后
L231: theorem fisherMetric_cauchy_schwarz … := by
L246:   rw [fisherMetric_eq_score_inner]      -- ❌ unknown identifier
L265: theorem fisherMetric_eq_score_inner …   -- 声明在这里（太晚）
```
**⇒ 修法**：**把 `fisherMetric_eq_score_inner` 整条**上移**到使用点之前**（语义零变更，纯重排）。<br>
⭐⭐ **如何与另两类区分**（**该代理给出的判据，值得照用**）：
| 类 | 判据 |
|:--|:--|
| (a) **目标已被关掉** | 该行**前面**已有 tactic 闭合了目标 |
| (b) **名字真不在/写错** | 全库 grep **0 处声明**（⚠ **注意 `to_additive` 变体与三个搜索域**）|
| ⭐ **(c) 前向引用** | ⭐ **该名字**在**本文件更后面**有完整声明**（**类型合成正常、其自身证明体零 error**）；<br>**且报错行的**目标完整显示出来了**（不是"have 未定义"式级联） |
<br>⚠ **为什么会混淆**：**三类都报同一个 `unknown identifier`**，
**且 (c) 与"级联"极易混**（级联的症状也是 `unknown identifier`）。
⇒ ⭐ **判据**：**(c) 的报错行**目标完整**、被引用者**自身零 error**；
级联则**被引用者**自己**先报错**。** |
| ⭐⭐ **`Algebra.smul_def` 与 `Algebra.commutes` 的**范式方向相反**** ⟹ **三者混用会让 `noncomm_ring` 卡住** ⚠️ v14（**一位代理三次误判后由探针定位**） | **pinned 源码逐字**（**coordinator 已核实**）：
```lean
-- Mathlib/Algebra/Algebra/Defs.lean:265
theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r * x      -- ⚠ 把 algebraMap 放【左】
-- Mathlib/Algebra/Algebra/Defs.lean:277
theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r   -- ⚠ 把 algebraMap 推【右】
```
⇒ ⭐ **两者方向**相反****；若再加一个自造的 `hcent : A * algebraMap c = algebraMap c * A`
（= `commutes.symm`，把 `algebraMap` 推【左】）⟹ **三种范式互相打架**，
**`noncomm_ring` 面对未归一的残余就卡住**。<br>
⇒ ⭐ **修法**：**让所有归一化方向一致** —— 用 **`Algebra.commutes` 的自然方向**（推右），
**并删掉自造的 `hcent`**：
```lean
simp only [Algebra.smul_def, hcomm, Algebra.commutes]
noncomm_ring
```
⚠ **且由此确立两条判据**：
1. ⭐ **`ring_nf`/`ring`/`noncomm_ring` **都不认识 `SMul.smul`**** ——
   它们的差别是**归一化强度**，**不是"懂不懂 `•`"**
   （⚠ **我曾向代理建议"`ring_nf` 会自动处理 `smul`"，该建议是**错的**，已撤回**）；
2. ⭐ **收尾前，目标里必须**已经不出现 `•`**** —— 若还出现，**换什么收尾 tactic 都没用**。<br>
⚠ **本例的诊断过程值得记录**：代理**前两轮都归因错**（先猜"`simp` 顺序"，再猜"项形状不匹配"），
**最后靠**零锁探针打印 `#check` 的**真实签名**才定位** ——
**⇒ "读被引用者的**实际签名**，而不是猜它的方向"。** |
`web_fetch` 对 `github.com` / `raw.githubusercontent.com` / `ifaamas.org` **全部失败**，报
`URL hostname resolves to a non-public IP address`。<br>
⭐ **而 `pwsh Invoke-WebRequest -UseBasicParsing` 可直连** —— coordinator 复现：
```powershell
Invoke-WebRequest -Uri "https://raw.githubusercontent.com/digama0/lean4lean/master/divergences.md" -UseBasicParsing
# → HTTP 200, 11367 字符 ✅
```
⇒ ⚠ **⇒ "`web_fetch` 抓不到" ≠ "该资源不存在"** —— **这正是本项目"三域核实法"在**网络域**的对应**。<br>
⇒ ⭐ **一般化**：**工具失败必须与资源缺失分开**；
**任何"查不到"的结论都要注明"用什么工具、查了哪个域"**。<br>
⚠ **且本波次已有多例同族**：`grep` 不到（三个搜索域）/ 检查器报 0（脚本编码）/
`Select-String` 对含 `?` 的名字静默失配 / **本次的 `web_fetch` 被拒**。 |
| ⭐⭐ **`class Decidable` 在 **mathlib 全库 = 0 命中**，因为它在 **Lean core**** ⚠️ v14（**"搜索域"陷阱的又一实例**） | **实测**（同上代理，coordinator 采信）：
| 搜索域 | 文件数 | `class Decidable` 命中 |
|:--|--:|--:|
| `mathlib\Mathlib\` | **5382** | **0** ⚠ |
| **Lean core `src\lean\`**（**不在 `.lake` 下**） | **1260** | **1**（`Init\Prelude.lean:841`）|
⇒ ⚠ **若只查 mathlib 就会**误报"mathlib 没有 `Decidable`"**** —— 而它是 Lean 的**核心类型类**。<br>
⭐ **同族实证**：`class Nonempty`（`Prelude.lean:709`）、`axiom Classical.choice`（`:735`）
**也都在 core**。<br>
⇒ **本文件已登记的"三个搜索域"（本仓库 / mathlib / Lean core）在此再次得到验证** ——
⚠ **且这次是**类型类**（而非引理），说明该陷阱**不限于引理名**。 |
| ⭐⭐ **`@[to_additive]` **生成的**名字，grep 声明行必然 0 命中** ⚠️ v14（**"grep 不到≠不存在"的新变体**） | **实测**（由一位代理用 pinned 源码定位）：`RealFisherMatrix:256` 用了 **`Fintype.sum_fin_two`** 并报
`unknown constant`。**真名是 `Fin.sum_univ_two`** —— 而它**不是**显式 `theorem` 声明的：
```lean
-- Mathlib/Algebra/BigOperators/Fin.lean:102-103
@[to_additive (attr := simp)]
theorem prod_univ_two [CommMonoid β] (f : Fin 2 → β) : ∏ i, f i = f 0 * f 1 := by
```
⇒ **`sum_univ_two` 由 `@[to_additive]` **自动生成**** ⟹
**任何 `grep 'theorem sum_univ_two'` 都会 0 命中**（**该文件的命中全是**使用**，无声明行**）。<br>
⚠ **危险**：**"grep 不到 ⟹ 名字写错 ⟹ 去改一个**正确的**引用"** 的路径由此打通。<br>
⇒ ⭐ **判据**：**加法版的引理若在乘法版附近找不到声明，先找`乘法版`** ——
`prod_*` ⟷ `sum_*`、`mul_*` ⟷ `add_*`、`one_*` ⟷ `zero_*`。
**⇒ 且这解释了为什么本库有 113 处 `Finset.sum_filter` 使用而 grep 不到声明**（同族，已登记）。<br>
⇒ **本文件"grep 不到≠不存在"家族现已有 4 个变体**：
① **三个搜索域**（本仓库/mathlib/**Lean core 不在 `.lake` 下**）；
② **`to_additive` 生成**（本条）；
③ **`Select-String` 对含 `?` 的名字静默失配**；
④ **"某目录下 0 个 X" 要先确认目录本身对不对**。 |
| ⭐⭐ **半完成的接口重构 = 最坏状态**："核心接口改了、调用点没改" ⚠️ v14（**比"不改"更糟**） | **实测**：某代理从 `RealConvergence.contraction_converges` 删除了死参数 `(e0) (_he0)`（**删除本身正确**），
但**全库 19 个文件**提及该定理，其中 **3 处仍在传已删除的实参**：
```
RealConversionStability:194  contraction_converges (e := e) c e0 hc0 hc1 he0 hstep hnonneg
RealLRDecay:177              contraction_converges (1 - η₀) (e 0) (by linarith) (by linarith) (he 0) hdec he
RealTD:141                   contraction_converges (1 - α + α * γ) (e 0) hc0 hc1 he0 hstep hnonn
```
⇒ ⚠ **此时全库任何依赖它的构建都会失败** ——
**而"完全不改"至少是自洽的**。<br>
⇒ ⭐ **纪律**：
1. **改核心接口前，先枚举全部调用点**（`grep` 该定理名，**含注释中的提及**以便判断影响面）；
2. **分块：先改接口 + 改完所有调用点，再一次构建** ——
   **不要"改了接口、先构建看看"**（那必然失败且淹没在噪声里）；
3 **若必须中断，优先**回退接口**而不是留下它** ——
   **半成品比未开始更危险**（它把"能编译"变成"不能编译"）。<br>
⚠ **同族**（本波次已登记）：**"B60 空洞 → 编译错误"的转换** ——
两者共同点是：**改动方向对，但中间状态破坏了可编译性**。 |
| ⭐⭐ **锁等待期的"只读审读"**不仅少引入缺陷，还能**发现已引入的缺陷**** ⚠️ v14（**一条纪律的独立实证**） | **背景**：本文件已登记"等待期只做只读工作"（**实测依据**：某代理 r1→r2 只把 error 从 27 降到 22，
**因为它在 r2 里引入了 9 类新缺陷**）。<br>
⭐ **但一次更强的实测**（另一代理，`RealSparseCoding` r3→r4）：
> **两次"只读审读"各抓到一个真 bug**，**而这两个 bug 在"边等边改"模式下**不可能被发现** ——
> **因为每次编辑后立刻叠加下一次编辑，从未"重读自己写的东西"。**

**它抓到的两个 bug**（**都是**只读**才能发现的**）：
1. **if 条件**不同形****：`softThresh_eq` 的 if 链用 `<`（`lam < y`），而 `hreg` 用 `≤`（`y ≤ -lam`）；
   `rw [if_neg h1]` 去动一个 `<` 的 if **会失配**（`h1 : ¬(y ≤ -lam)` 不是 `¬(y < -lam)`）
   ⟹ **修法：为每个 if 单独构造**字面同形**的条件命题**（`by linarith : ¬ (y ≤ -lam)`）；
2. **残留旧证明体**：从 `max`/`min` 路线改写为分段路线后，
   **旧的 `hmax`/`hmin`/`linarith` 三行没删** ⟹ 留下无法闭合的尾随目标。<br>
⇒ ⭐ **⇒ 纪律（强化版）**：**"等待期只读"有三个价值，不只是"少犯错"**：
> ① **不引入新缺陷**；② **发现已引入的缺陷**（**叠加编辑会掩盖它们**）；
> ③ **把"重读自己写的东西"从可选项变成唯一可做的事**。<br>
⚠ **操作性建议**：**入队冻结后，把等待时间用于通读全文找同类问题，
但只记录、不修改，留到 verdict 之后一次性处理。** |
| ⭐⭐ **"排队年龄" ≠ "持锁时长"：判"持锁者僵持"必须用 owner 记录的时间戳** ⚠️ v14（**测量口径错误家族第 4 例**） | **实测**：某代理看到"前方最老等待者 78.8 分钟"便推断**持锁者在僵持**，
并报告"**持锁 78 分钟、无 `lean.exe` 子进程 ⟹ 可能卡死**"。<br>
**实测真相**：
- **78.8 分钟是它自己的**ticket 年龄**（它 10:57 就**入队**），而它**真正**拿到锁**是 **11:56**（**只持 22 分钟**）；
- **且**当时有**一个 `lean.exe` 在跑**（`RealLv00Geometry`，CPU 在累积）⟹ **它在正经干活**，只是 11 个模块很慢。<br>
⇒ ⭐ **判"持锁者是否僵持"的三个正确依据**：
1. **`owner` 记录里的**时间戳****（`lattice-build.owner` 的第 2 字段），**不是** ticket 年龄；
2. **它的 `lean.exe` 是否在**累积 CPU****（`Get-Process -Id <pid> | Select CPU`，两次采样比较）；
3. **`who-holds.ps1` 的**父链**是否完整**。<br>
⚠ **为什么这个错误危险**：**它会导致"kill 掉一个正经干活的持锁者"** ——
**而那会作废它整批的排队（45 分钟~2.4 小时）**。<br>
⇒ ⭐ **本波次"测量口径错误"家族（4 例，全部已登记）**：
① 我用**进程计数**判"重复排队"（错；应看父链）；
② 某代理用错 olean 路径（`.lake\build\lib\lean\`）得"全库 0 olean"；
③ `Select-String` 正则对含 `?` 的名字**静默失配**（`find?_eq_none`）；
④ **本条：排队年龄 vs 持锁时长**。<br>
**⇒ 共同教训：任何"计数/时长/存在性"结论，先确认**度量的对象**是否正确。** |
| ⭐⭐ **点对前提必须设在**被引用者的实际输入**上，不是设在调用者手里的那个变量上** ⚠️ v14（**"空洞 → 编译错误"的转换**） | **实测**（`RealBlockConstants:299/312`）：
```lean
(hx : c ≤ ‖x‖)                                  -- 前提设在 x 上
have hF : ∀ u v, ‖RMSNormOp u - RMSNormOp v‖ ≤ (√n/c) * ‖u - v‖ := by
  exact rmsNormE_sqrt_lipschitz u v c hc (le_trans hx ?_)   -- 但需要 c ≤ ‖u‖
```
⚠ **`RMSNormOp` 实际作用于内层和 `x + Attn x + W x`**，**不是 `x`** ⟹
`?_` 要求 **`‖x‖ ≤ ‖u‖` 对**任意 `u`** 成立** ⟹ **取 `u = 0` 即假**（`‖0‖ = 0 < c`）。<br>
⇒ ⭐ **本条的**价值在于失败形态发生了**转换**而非消除**：
| 阶段 | 状态 | 危害 |
|:--|:--|:--|
| 原稿 `∀ z, c ≤ ‖z‖` | **前提恒假** ⟹ **空洞** | ⚠ **编译通过**，**看起来像已验证成果** |
| 错误"修复"（设在 `x`） | `?_` 是假命题 | ⚠ **编译不通过**，**但空洞没被真正消除** |
<br>⇒ ⭐ **一般陷阱**：**`le_trans hx ?_` 这类"用传递性把已有界升到所需界"的写法**，
**前提位置对时合法；位置错时它**静默地要求一个假命题**** ——
**而 Lean 只报"`?_` 填不满"，**不会告诉你"前提设错了对象"****（**"报错点 ≠ 真凶"的新实例**）。<br>
⇒ ✅ **正确契约**：把点对前提设在 **RMSNorm 的**实际输入**（内层和）**上；
**可满足性见证**：`A := 0`、`W := 0`、`x = y = c • e₀` ⟹ 内层和 = `c • e₀`，`‖·‖ = c` ✓ |
| ⭐⭐ **"取倒数/取对数"的不等式变形：先把**等价条件**写成一行，再问"假设里有它吗"** ⚠️ v14（**一位代理连续改错**两次**后自纠**） | **实例**：`neumann_stable_under_perturbation` 原稿写 `(1−t−ε)⁻¹ ≤ (1−s)⁻¹`，
**该代理判定"方向反了"并改成** `(1−s)⁻¹ ≤ (1−t)⁻¹` —— **两个都是假的**：
| 版本 | 等价条件 | 假设里有没有？ | 真值 |
|:--|:--|:--|:--|
| 原稿 `(1−t−ε)⁻¹ ≤ (1−s)⁻¹` | `s ≥ t+ε` | ❌（只有 `s ≤ t+ε` 与 `s ≥ \|t−ε\|`） | **假**（`t=0.1,ε=0.3,s=0.2`：`1.666 ≤ 1.25` 假） |
| "更正" `(1−s)⁻¹ ≤ (1−t)⁻¹` | `s ≥ t` | ❌（**取 `δT=−T` 可令 `s=0`**） | **假** |
| ✅ **正解** `(1−s)⁻¹ ≤ (1−t−ε)⁻¹` | 用**可保证上界** `s ≤ t+ε` | ✅ | **真** |
<br>⇒ ⭐ **判据（可机械执行）**：
> **任何"取倒数/取对数"的变形，先把该不等式**等价地写成一个显式条件**（如 `s ≥ t+ε`），
> 再问"**这个条件在假设里吗？**"** —— 若没有，**两个方向都不成立**，
> **该比较根本不被假设决定**。<br>
⚠ **为什么容易连错两次**：**"方向直觉"（"扰动后常数应该变大/变小"）会替代**等价条件**的检查**；
而**倒数把 `≥` 翻成 `≤`**，**直觉在两次翻转后极易失效**。<br>
⚠ **且该代理的另一发现值得并列**：它用**浮点大规模搜索**报的"反例"**全是
`1−t−ε` 极小时的舍入伪影**（**那些"反例"里 LHS 与 RHS 完全相等**）⟹
**改用精确有理数后零反例**。**⇒ 判不等式的真伪，用精确算术，不要用浮点搜索。** |
| ⭐ **`abs_nonneg` 用在"已经带绝对值"的定义上会得到**双层绝对值**** ⚠️ v14 | 若 `coherence` 的定义体**已含 `\|·\|`**，则 `abs_nonneg (coherence A i j)` 给的是 `\|(\|⋯\|)\|`（**双层**），
而目标要 `\|⋯\| ≤ μ` ⟹ 报 `has type … ≤ μ but expected \|…\| ≤ μ`。<br>
⇒ **修法**：把 `abs_nonneg` 用在**内层**和式上。 |
| ⭐ **`inf'` 是**下确界**：`s i < s o₀` **推不出** `s i < s.inf'`** ⚠️ v14（**真数学错误，非记法问题**） | **错误推理**：由**单个** `o₀` 的 `s i < s o₀` 得 `s i < ood.inf' ⋯ s`。
**反例**：`inf' ≤ s o₀` 与 `s i < s o₀` **可以同时成立**而 `s i ≥ inf'`。<br>
**正确引理**：**`Finset.lt_inf'_iff : a < s.inf' H f ↔ ∀ i ∈ s, a < f i`**
（`Mathlib/Data/Finset/Lattice/Fold.lean:1138`）—— **「小于下确界 ⟺ 小于所有元素」**。<br>
⚠ **登记原因**：**这条的报错症状（`rw`/`exact` 失配）与本波次大量"记法/形状"陷阱**完全一样**，
但它**根本不是记法问题，是命题为假** —— **必须靠"把结论代具体值判真假"才能区分**。<br>
**⇒ 同族**：`abs_nonneg` 的双层绝对值、`linarith` 的"引理选错"—— **都属于"看起来像形状问题，实为数学问题"。** |
| ⭐⭐ **核实"某引理是否存在"必须查**三个域** —— 只查一个会得到假阴性** ⚠️ v14（**一位代理三次踩中，后自查纠正**） | **三个域**：
1. **mathlib**：`lean/.lake/packages/mathlib/Mathlib/`
2. **本仓库自制**：`lattice/lean/*.lean`（**自制引理会与 mathlib 同名不同源**）
3. ⭐ **Lean core**：`~/.elan/toolchains/<tc>/src/lean/` —— **不在 `.lake` 下！**<br>
⚠ **第 3 条最危险**：`Get-ChildItem .lake -Recurse` **看不到 core**，因为 toolchain 在 `~/.elan` 下。
**"在整个 `.lake` 里 grep 不到"完全可以发生在 core 引理上** —— 而那会让人去**修一个根本没错的引用**。<br>
**实测三例**（coordinator 已独立复验）：
| 引理 | 只查 mathlib 的结论 | 真相 |
|:--|:--|:--|
| `real_conjTranspose_eq_transpose` | ❌ 误判"不存在" | **`RealSVD.lean:54`**（域 2）|
| `taylor_mean_remainder` | ❌ 误判"疑似不存在" | **mathlib `Taylor.lean:222`** |
| `find?_eq_none` / `mem_of_find?_eq_some` / `length_filter_le` | ❌ 误判"全库不存在" | **core**：`Find.lean:431` / `Find.lean:263` / `Lemmas.lean:1408` |
⚠ **且测量工具本身也有缺陷**：**PowerShell `Select-String` 的正则对含 `?` 的名字会**静默失配****
（`find?_eq_none` 正是此类），`-SimpleMatch` 对某些名字也不可靠。
⇒ **可靠做法：逐行 `[System.IO.File]::ReadAllLines` + `String.Contains`**。
（⚠ **coordinator 复验时先用 `Select-String` 也全部漏掉，改用 `.Contains` 才找到** —— **同一坑当场复现**。）<br>
⇒ ⭐ **一般化**：**"grep 不到" ≠ "不存在"** —— **必须问"我查的域是否覆盖了它可能所在的地方"**。
**同族**（本文件已登记）：**"检查器报 0" ≠ "库里真没有"**（脚本编码陷阱）、
**"某目录下 0 个 X" 要先确认目录本身对不对**（另一代理的 `.lake\build\lib\lean\` 路径错误）。<br>
⚠ **且该缺陷已**工具化修复****：`check-xref.ps1` 原先**只索引域 1**，
故**所有 mathlib/core 引理都报 `ABSENT`**（首跑 **822** 条，**绝大多数是误报**）
—— **这可能诱导代理去改**正确的**引用**。
**⇒ 已把域 2、3 并入索引 ⟹ `ABSENT` 从 822 降到 **381**（降幅 54%）。** |
| ⭐ **`unfold <name>` **不做 β-归约**；`simp only [<name>]` 做** ⚠️ v14（**λ 里的项**） | `unfold auroc` 产出 `↑↑p.2`（把 `fun i => (↑i : ℝ)` 当作**未归约的 λ**），
而假设写的是 `p.2` ⟹ `rw` 失配。<br>⚠ **补 `beta_reduce` 仍不够**（残留 `↑↑`）。<br>
⇒ **正解**：**用 `simp only [auroc]` 代替 `unfold auroc`** —— `simp` 会**正确 β-化简**
（探针 `exit 0` 验证）。<br>
⚠ **同族**（本波次已多次记录）：`unfold`/`simp only` 都不做 β-归约的说法**需修正**：
**`unfold` 不做，`simp only` 做**。**当定义体是 λ 时，一律用 `simp only`。** |
| ⭐⭐ **同一报错重复出现 = 归因错误的信号（附**三次错误的完整演进**）** ⚠️ v14（**本波次最强的实证**） | **实例**：同一个 `omega could not prove the goal` 在同一文件报了**三次**（v9`:927` / v10`:1229` / v12`:1302`），**前两次归因都错**：
| 次序 | 归因 | 判定 |
|:--|:--|:--|
| 1 | 「`omega` 不认 `Finset.card`」 | ❌ **错**（`omega` 把 `card` 当**不透明 ℕ 原子**，完全能解） |
| 2 | 「`unfold … at *` 破坏原子对齐」⟹ 改成 `unfold … at hsx hsy ⊢` | ⚠ **部分对但不够** —— **分两步后仍然失败** |
| 3 | 看到报错里的 **`a := ↑k`** 才定位真因：**`2 * k` 被当成 ℕ 乘法**，而 `hsx` 展开后是 `card ≤ k` ⟹ **ℕ 域约束没对齐** | ✅ **正解**：`simp only [IsSparse, l0Norm] at hsx hsy ⊢`（**一次性、同一策略展开三处**，保证项逐字同形），再 `omega` |

⇒ ⭐ **操作性判据（本条最有用的部分）**：**`omega` 失败时，先读报错里的 `where a := … b := …` 段** ——
**它直接告诉你 `omega` 把哪些项当成了变量**。本次 **`a := ↑k`** 立刻暴露了 `ℕ`/`ℝ` 混淆。
（**报错文本里已经给了答案，只是需要读对位置。**）<br>
⇒ **纪律**：**同一错误第二次出现时就该怀疑归因，而不是再修一次**。**第三次才做对，代价是两轮白工。** |
| ⭐ **`unfold … at *` 会破坏 `omega` 的**原子对齐**** ⚠️ v14（**同一报错两次复现，第一次归因错误**） | `unfold l0Norm IsSparse at *` 会把 `l0Norm` **在 `hsupp` 内部也展开** ⟹
`hsupp` 里的 `Finset.card` 项与目标的项**不再是同一个句法原子**（`omega` **只做句法匹配**）⟹
`omega could not prove the goal`。<br>⇒ **修法**：**只 unfold 必要的位置** —— `unfold l0Norm at hsx hsy ⊢`
（只展目标与来源假设），**不要 `at *`**。<br>
⚠ **本条特别值得记**：**同一报错在 v9/v10 两次出现**，而**第一次归因（"`omega` 不认 `Finset.card`"）是错的**；
**真因是作用域太广**。⇒ **"同一错误重复出现"是"归因可能错误"的信号**，不要重复同一个修法。 |
| ⭐ **`unfold` / `simp only` 都**不做 β-归约**** ⚠️ v14 | `unfold projMatrix projFeature` 把定义体塞进目标后，**`if`/`dite` 仍埋在 λ 里** ⟹
所有 `if_pos`/`dif_neg` 报 `did not find instance of the pattern … dite (↑k < d) ?m ?m`。<br>⇒ **修法**：用 **`simp only [defs]`** 取代 `unfold`（**simp 做 β-归约**）。<br>⚠ 同族：**`rw [if_pos h]` 在 beta-redex 上必败**（改 `simp only [if_pos h]`）——**同一根因的两个面**。 |
| ⭐ **`unfold … at *` 的同族：任何"作用域过广"的重写都会破坏后续自动化** ⚠️ v14 | 同族实例：`unfold`/`simp`/`rw` 的 `at *` 变体、`simp_all`、`subst` 的全局版本。<br>
**共性**：后续的 `omega`/`linarith`/`ring` 依赖**句法原子的同一性**，
**一旦你把某个定义在**不该展开的位置**也展开了，原子就对不上**。<br>⇒ **纪律**：**自动化的强依赖"形状"** ⟹
**"尽可能局部化"**（`at h1 h2 ⊢` 而非 `at *`）。 |
| ⭐ **`OfNat (Fin n)` 需要 `NeZero n`，而 `2 ≤ n` **不自动**给你它** ⚠️ v14 | `(0 : Fin n)` / `(1 : Fin n)` 报 `failed to synthesize OfNat (Fin n) 0`，
并**级联**成 `unsolved goals ⊢ False`（实测 6 条）。<br>⇒ **修法**：用**具名构造** `⟨0, by omega⟩` / `⟨1, by omega⟩`，**不要**依赖 `OfNat` 实例。 |
| ⭐ **`mul_sub` 之类"方向本来对"的引理，多写 `.symm` 会反向** ⚠️ v14 | 报错原文直接给出类型对比：
`Eq.symm (mul_sub …) has type 'a*x - a*y = a*(x-y)' but expected 'a*(x-y) = a*x - a*y'` ⟹ **删掉 `.symm`**。<br>
⚠ **同族**：`smul_smul` 的"方向是**独立**于占位符的第二个问题"——**不要用 `.symm` 去"修"其它问题**。 |
| ⭐ **`by tauto` 在 `by_cases` 分支里必失败** ⚠️ v14 | 因该分支**同时**拥有 `hk` 与 `¬hk`，且常需证 `¬(A ∧ B)` 这类**非命题逻辑**目标 ⟹ `tauto failed to solve some goals`。<br>⇒ **改 `rw [if_pos hk]` / `simp [hk, hl]`**。 |
| ⭐ **`rw [eq_self, and_true, …]` 报 `motive is not type correct`** ⚠️ v14 | 当**判别式出现在 `if` 的类型里**时，`rw` 的 motive 不合法。<br>⇒ **写成 `rw [if_pos ⟨hk, rfl⟩, one_mul]`**（把侧条件**连同等式**一起供给）。 |
| ⭐ **`pow_succ` 与 `pow_succ'` 只差交换律，但 `rw` 是语法匹配** ⚠️ v14（**形近名对**） | `pow_succ' : a^(n+1) = a * a^n`（**左乘**），`pow_succ : a^(n+1) = a^n * a`（**右乘**）。<br>⇒ **用错必报 `did not find instance of the pattern`**。<br>**同族**：`Finset.prod_univ_sum` vs `Fintype.prod_sum`、`Function.iterate_succ_apply` vs `_apply'`。 |
| ⭐ **`smul_smul` 传了显式参数之后，就变成**方向**问题** ⚠️ v14 | 某代理先遇 `MulAction ?m stuck`（**`_` 泄漏 metavariable**），于是"加 `.symm` 绕过"——**反而更糟**。<br>**真因分解为两步**：① 先要把 `_` 改成**显式传参**（否则 stuck）；② 传参后**方向才对得上**，**多加 `.symm` 就反了**。<br>⇒ **纪律**：遇到 `stuck` 时**先修占位符，不要改方向**；方向是**独立的**第二个问题。 |
| ⭐ **`Finset.sum_mul` 只匹配 `(∑ f k) * a`，不匹配 `∑ (f k * M)`** ⚠️ v14 | **M 在项**内**时不匹配**。<br>⇒ **修法**：先用 **`(Finset.sum_mul).symm` 把 M 提到和式**外****，再 `sum_range_reflect` 换元，最后 `ring`。 |
| ⭐ **`♯` 是 Lean 的保留 token，不能作标识符** ⚠️ v14（**一个字符级联 20+ 条 error**） | 某代理全文件用 `step♯` 命名，导致 **5 条 `expected token` + 级联 20+ 条 error**。<br>⇒ **全部改 ASCII `stepSharp`**。**同类保留 token 还包括 `♭`/`†`/`‡` 等** —— 命名一律用 ASCII。 |
| ⭐ **`GaloisConnection` 的类型必须让两侧回到同一层** ⚠️ v14 | `GaloisConnection α (fun a => {c | c ∈ γ a})` **类型非法**：`u` 的陪域必须回到 `Concrete`，而 `γ` 的值域是 `Set Concrete`。<br>⇒ **正确配对是集合层** `GaloisConnection αS γ`（`αS : Set Concrete → Abstract`，`Set Concrete` 自带 `CompleteLattice`）。<br>**副产品**：这样配对后 `bestAbstract` 可证**最优 + 可靠**，**且不需要 `f` 单调**（单调性由 `αS` 从 Galois 连接免费获得）。 |
| ⭐ **区间抽象必须用「反向包含序」** ⚠️ v14 | `le a b := b.lo ≤ a.lo ∧ a.hi ≤ b.hi`（**反向包含**）才能使 `point x ≤ iv ↔ x.contains` 成为 **`Iff.rfl`**（**机器证据**）。<br>某代理先写**逐点序**，导致该等价**为假**。⚠ **代价**：该序下 `γ` 经实测是**正变**（原写 `Antitone` 是错的）；好消息是第一节的 `gamma_monotone` 框架**反而适用**。 |
| ⭐ **`Fin` 强制转换在项里出现两次（`↑↑a`），会让 `ring`/`linarith` 一律失败** ⚠️ v14（**极难定位**） | 任何含 `(x : ℝ)`（`x : Fin n`）的 `ring`/`linarith` 子目标**一律失败**：实测目标变成<br>`↑↑x - ↑↑b * 2 + ↑↑y = ↑↑x - ↑↑y`（把 `↑b` 当**多项式变量**乘了 2 倍）。<br>⇒ **修法**：把 `↑x - ↑b - (↑b - ↑y) = ↑x - ↑y` 这类消去**提到 `calc` 之外的 `have`** 里证（其目标里 `↑b` 是**原子**，`ring` 可解），再用 `rw [hxy]`。<br>⚠ **伪装性强**：会报成 `did not find instance of the pattern` 或 `unsolved goals`。 |
| ⭐ **`rw [if_pos h]` / `rw [if_neg h]` 在 beta-redex 上**必然**失败** ⚠️ v14 | 目标为 `(fun k => if k = i then a else b) x` 时，`rw [if_pos h]` 报<br>`did not find instance of the pattern: if ?m = ?m then ?m else ?m`（**连 `if True then …` 形态也一样失败**）。<br>⇒ **修法：一律改 `simp only [if_pos h]` / `simp only [if_neg h]`** —— **`simp` 会做 β-归约，`rw` 不会**。 |
| ⭐ **`rw` 是语法模式匹配：「同形」才可重写，指数 `n` vs `n+1` 就不同形** ⚠️ v14 | 目标 `(algebraMap ℝ ℂ) a * star mu ^ (n + 1) = star (...)`，而归纳假设 `ih` 说的是 `… * star mu ^ n` ⟹ **`rw [ih]` 报 `did not find instance of the pattern`**。<br>**这不是数学错**（命题为真），是**机制性陷阱**：`rw` 匹配**语法子项**，`n` 与 `n+1` 不同形。<br>⇒ **修法（用 `calc` + 先把形状对齐）**：<br>```lean
calc (algebraMap ℝ ℂ) a * star mu ^ (n + 1)
    = (algebraMap ℝ ℂ) a * star mu ^ n * star mu := by rw [pow_succ]; ring
  _ = star ((algebraMap ℝ ℂ) a * mu ^ n) * star mu := by rw [ih]   -- 此时形状已同
  …
```<br>**关键**：**先用 `pow_succ; ring` 把 `star mu ^ (n+1)` 变成 `star mu ^ n * star mu`**，使 `ih` 的左式成为**语法子项**，`rw` 才能命中。 |
| ⭐ **`pow_le_pow_right₀` 的首参是 `1 ≤ a`，不是 `0 ≤ a`** ⚠️ v14 | 传 `hC0 : 0 ≤ C` 会得 `application type mismatch`（**与直觉相反**）。<br>⇒ 实数上要用 `0 ≤ a` 版本应改用 **`pow_le_pow_left₀`**，或先 `nlinarith` 补出 `1 ≤ a`。 |
| ⭐ **`NormedRing`（非交换）下 `smul_smul` 等必须传显式参数** ⚠️ v14（**症状看不出真因**） | `smul_smul` / `Algebra.mul_smul_comm` / `Algebra.smul_mul_assoc` 留 `_` 占位会触发<br>`typeclass instance problem is stuck … MulAction ?m ?m`。<br>⇒ **报错信息完全看不出真因**（症状在 `MulAction`，**根因是 `_` 泄漏 metavariable**）。**必须显式传参**。 |
| ⭐ **`Finset.sum_const` 对向量值求和体给 `nsmul` 形** ⚠️ v14 | 需 `Nat.cast_smul_eq_nsmul` / `nsmul_eq_smul_cast` 再转实标量；对 `∑ j, (const)` 形需先 `show ... = (card:ℝ) * c`。 |
| **`Real.exp_nat_mul` 是定理非 simp 引理** | 反向重写**必须显式传参** `Real.exp_nat_mul a n`（否则 `rw` 静默失败）。 |
| ⭐ **`Matrix.nonsing_inv_mul` 的 `A` 是显式参数 —— 写 `_` 占位会炸** ⚠️ v14（**惰性占位符用在显式参数上**） | mathlib 4.14 `LinearAlgebra/Matrix/NonsingularInverse.lean`：<br>`L67 variable (A : Matrix n n α)` ← **圆括号 = 显式**；`L248 mul_nonsing_inv`、`L254 nonsing_inv_mul` 因此**都必须显式传矩阵**。<br>⇒ 写 `Matrix.nonsing_inv_mul _ hK`：对**裸变量**（如 `K`）`_` 可能统一上；但对**复合项**（`noiseMatrix K sigmaSq`）**无法统一** ⟹ 报 `failed to synthesize`。<br>**正确写法**：`Matrix.nonsing_inv_mul <矩阵> <可逆性证明>`（本库活样本：`RealPseudoInverse.lean:91`、`RealPrimeFieldExt.lean:146`）。<br>⚠ **建议全库扫** `grep -n 'nonsing_inv_mul _\|mul_nonsing_inv _' *.lean`。 |
| ⭐ **`Finset.univ.sup'` / `inf'` 需要 `Nonempty` ⟹ `0 < n` 不可省** ⚠️ v14 | `Finset.univ_nonempty : s.Nonempty` 对 `s = Finset.univ : Finset (Fin n)` **需要 `Nonempty (Fin n)`**，而 **`n = 0` 时 `Fin 0` 为空** ∃⟹ 合成失败。<br>⇒ `l1_le_l0_mul_sup` 用 `Finset.univ.sup'` **必须**加 `(hn : 0 < n)` 并 `haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn`。<br>⚠ **且会级联**：缺 `Nonempty` ⟹ 定理**陈述本身**合成失败 ⟹ 其内所有 `have` 未定义 ⟹ 后续报多条 `unknown identifier`（**1 个根因 → 4 条 error**）。 |
| ⭐ **`unknown identifier` / `failed to synthesize` 常是「级联症状」而非独立缺陷** ⚠️ v14（**与"解析失败掩护真错误"对称**） | **判别法：找"最近的前置失败声明"** —— 若某条 `have h : <类型>` 的**类型本身**合成失败，则 `h` **根本未定义**，其所有引用都报 `unknown identifier`。<br>**实证**：某文件缺 `0 < n`（**1 个根因**）→ **4 条 error**（3 条 `failed to synthesize` + 1 条 `unknown identifier 'hterm'`）；另一文件 `_` 占位（**1 个根因**）→ **9 处调用点**（十几条 error）。<br>⇒ **「error 条数」严重高估「缺陷个数」**。按根因分组时**先找最近的前置失败声明**，而不是逐个改。<br>⚠ **这也修正"前向引用"的判据**：前向引用的前提是**该 `have` 本身成功定义**；若它所在的目标已被污染，那是**级联**，不是前向引用。<br>（实测反例：`hterm` 声明在 L293、使用在 L303，**顺序完全正确**——真凶是 `Nonempty` 合成失败。） |
| ⭐ **解析失败会「掩护」后续的真错误 —— 修好解析层后必须重编** ⚠️ v14（**诊断纪律**） | 当文件在解析层失败（如孤儿 `/--`）时，**Lean 对后续内容的分析是残缺的** ⟹ 报出的 N 条 error 里**混着"解析级联"与"真证明错误"**，**无法区分**。<br>**实测**：`RealSparseCoding` 修好 `/--` 后 `unexpected token` **从命中多处 → 0 处**，但 error 总数只从 **136 → 128** —— **那 128 条是原先被解析失败掩盖的真错误**。<br>⇒ **纪律**：**修好解析层后必须重编一次**，才能拿到**真正的缺陷清单**；**不要**以为"修了那一个字符就该归零"。<br>（这与"解析失败导致后续行号全部错位"是**同一现象的两种表现**：**解析失败会让整份诊断都不可信**。） |
| ⭐ **登记缺陷要记「锚点文本」，不要只记行号** ⚠️ v14（**并发环境下的必然教训**） | 本波次**反复**因行号漂移而误判：<br>• 日志里的 `行:列` 相对**当前源码**已陈旧（源码被改过）⟹ 按行号找会找到**无关代码**；<br>• 多代理**并发编辑**同一文件 ⟹ 别人的插入会把你的目标行**整体下推**（实测 `RealRKHSKernel` 被他人插入 5 行，把 `/--` 从 L209 推到 L214）；<br>• `CORRECTIONS` 里按行号登记的锚点会**静默失效**。<br>⇒ **纪律**：登记/引用缺陷时记 **「锚点文本（grep 唯一的片段）」+ 行号**，**以锚点为准**；<br>**引用日志诊断前先确认该日志对应的是哪一版源码**（看 manifest 哈希或 mtime）。 |
| ⭐ **`/--` 必须紧跟声明，否则报 `unexpected token '/--'; expected 'lemma'`** ⚠️ v14（**一个字符毁整个文件**） | Lean 区分两种块注释：<br>• **`/-- … -/`（doc-comment）** —— **必须紧跟一个声明**（`theorem`/`lemma`/`def`/`structure`/`instance`…）；<br>• **`/-! … -/`（section comment）** —— **可以独立存在**，用于说明一段内容。<br>⇒ **若 `/--` 后面跟的是另一个 `/--`（或散文、空行），就报 `unexpected token '/--'; expected 'lemma'`**。<br>**实测**：`RealSparseCoding.lean` 的 **L165** 开 `/--` 说明"登记在案的假命题"，而**下一个声明在 L195**，中途 **L189** 又开一个 `/--` ⟹ **全文件报 136 条 error**。**修法：把 L165 的 `/--` 改成 `/-!`（一个字符）**。<br>⚠ **注意错误位置是"第二个 `/--` 那一行"**（报 `L189` 而非 `L165`）——**真凶是前一个没有声明的 `/--`**，**要看它后面有没有声明**。<br>✅ **已由探针端到端证实**（含对照组）：孤儿 `/--` + 后随 `/--` ⟹ 报错列号 = **第二个** `/--` 的位置；仅改 `/-!` ⟹ **exit 0 零 error**。 |
| ⭐ **不要在 `Finset.sum` / `prod` 体内 `rw` 定义等式** ⚠️ v14（**症状是 `typeclass stuck`**） | 在 `Finset.sum_congr` **内部**写 `rw [diracVec_apply]`（展开一个 `def … := fun j => if …`），会让 `∑` 的**幺半群类型参数留成元变量**，报 `typeclass instance problem is stuck, … AddCommMonoid ?m`。<br>⇒ **正解（单点求和）**：改用 **`Finset.sum_eq_single`**，并把定义等式放在**外层目标**上 `rw`：<br>```lean
rw [pairing_eq_col]
rw [Finset.sum_eq_single j₀]
· rw [show diracVec j₀ j₀ = (1:ℝ) from by rw [diracVec_apply, if_pos rfl], mul_one]
· intro j _ hj
  rw [show diracVec j₀ j = (0:ℝ) from by rw [diracVec_apply, if_neg hj], mul_zero]
· intro h; exact absurd (Finset.mem_univ j₀) h
```<br>⭐：`show … from by rw [...]` 把 `<br>rw` 限制在**外层目标**，**不进入求和体**。 |
| ⭐ **`csInf_le` / `le_csInf` 的 `BddBelow` 里"界的点"必须与目标里的点一致** ⚠️ v14 | 写了 `⟨transportCost c π, …⟩` 却想用 `le_of_eq hEq`（`hEq : transportCost c ρ = z`）去证 `transportCost c π ≤ z`——**但 `ρ` 与 `π` 无关，该命题本身为假**（编译器的 `application type mismatch` 正是在拦这个）。<br>⇒ **正解**：把 `BddBelow` 提成命名假设，**界的点就用目标里的那个点本身**：<br>```lean
have hbdd : BddBelow (image) := ⟨transportCost c π, fun z hz => by
  obtain ⟨ρ, hρ, hEq⟩ := hz; rw [← hEq]; exact hmin hρ⟩
have hmem : transportCost c π ∈ image := ⟨π, hπ, rfl⟩
exact ⟨π, hπ, le_antisymm (le_csInf ⟨_, hmem⟩ hbdd) (csInf_le hbdd hmem)⟩
```<br>⚠ **`rw [← hEq]` 的方向**（`hEq : transportCost c ρ = z`，要把目标里的 `z` 换成 `transportCost c ρ`）——**写成 `rw [hEq]` 就是方向反了**，这是同一错误反复出现的真正原因。 |
| ⭐ **常数约定冲突：不要靠"定义形式"判，要找文件内已证的实例校准** ⚠️ v14（**推理纪律·重要**） | 实例：扫描者见 `RealMcDiarmid` 的有界差分定义是**增量形式**（`abs(f z - f (update z i z')) ≤ c i`），就断言该约定下常数应为 `/2`、而 `:165` 的 `/8` 是错的。<br>**实测反例（同文件已证）**：`:353 mcdiarmid_additive_mgf : E[e^{λ·Σgᵢ}] ≤ e^{nλ²/2}`（`cᵢ = 2`）。<br>&nbsp;&nbsp;• 用 `/8`：`λ²·4n/8 = nλ²/2` —— **逐字吻合** ✅<br>&nbsp;&nbsp;• 用 `/2`：`e^{2nλ²}` —— **与已证事实差 8 倍** ⟹ **会把定理改成假命题** ❌<br>⇒ **正确做法**：**去找该文件内已证的、能用具体数值一票判定的实例**。<br>（附加事实：增量条件与**极差**界**等价**；`RealAzuma` 的 `/2` 是**绝对界约定**下的同一个界：`Σc_极差²/8 = Σ(2c_绝对)²/8 = Σc_绝对²/2`。） |
| ⭐ **Lean 报错里的 `pattern:` 行就是该引理的真实记法形状** ⚠️ v14（**比写探针更省**） | 当 `rw [X]` 失败时，Lean 会打印它**实际在找的模式**：<br>```
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  ∑ p ∈ ?s.pi ?t, ∏ x ∈ ?s.attach, …      ← 这就是 Lean 打印的真实模式（双绑定）
⊢ ∑ w, ∏ i, …                              ← 而目标是这样（单绑定）
```<br>**实测**：某代理据此**一眼看出**"引理是**双绑定**、目标是**单绑定**"，从而找到真名 `Fintype.prod_sum`（**不是** `Finset.prod_sum`，后者是双绑定版）。<br>⇒ **不要猜记法形状——`pattern:` 行已经替你打印出来了。**（这是"写形状探针"的**零成本版本**。） |
| **`Finset.prod_univ_sum` vs `Fintype.prod_sum`** ⚠️ **易混名对** | `Finset.prod_univ_sum` 是**双绑定**形式（`∏ x ∈ s.attach, …`）；单绑定形式（`∏ i, ∑ j, f i j = ∑ x : ∀ i, κ i, ∏ i, f i (x i)`）的真名是 **`Fintype.prod_sum`**（在 `namespace Fintype` 内，`Algebra/BigOperators/Ring.lean:286`）。**两者名字极像但绑定结构不同。** |
| ⭐ **`unused variable` 通道对"重言式本身"有结构性盲区** ⚠️ v14（**方法学·重要**） | **若假设本身就是证明体**（`theorem foo (h : P) : P := h`），**Lean 认为该假设"被使用了"、不报任何警告**。<br>⇒ **用 `unused variable` 找重言式，只能找到重言式的"陪衬假设"，找不到重言式本身。**<br>**最强实证**：`RealHoeffdingInequality.lean` 有 **2 个重言式、0 条警告**——只看日志该文件**完全隐形**；而 `RealFedAsync:107` 从未被警告过 `hstep`（被警告的是 `hμ`/`hη`）。<br>⇒ **必须建独立通道**：抽取**每个假设的陈述**与**结论的陈述**，做归一化（统一空白 / Unicode→ASCII / 剥冗余括号 / **顶层 `∧` 交换** / **剥 `∀` 前缀做 α-等价** / 合取项包含），**再真的读证明体坐实**。<br>（该通道是**语法级**⟹ 结果是**下界**：不做 `a*b↔b*a`、不做 `‖x‖↔dist x 0`、不做定义展开。） |
| **`RealFedAsync` 的 `hstep` 是同一文件里的两个不同命题** ⚠️ v14（**最危险的命名冲突**） | `:107`/`:280` 的 `hstep` 是**待证的核心递推**；`:603`/`:648` 的 `hstep` 是**迭代格式** `x(t+1) = x t − η·d t`。<br>⇒ **同一文件同名不同命题**，极易误引。**同族**：`ir_sem`(Compiler)/`irSem`(Systems) 跨文件 5/15 分支不均匀；`sigmoid`/`geluTanh` 跨文件潜伏冲突。 |
| **`Finset.max'` / `min'` 比较的是「指标」而非「函数值」** ⚠️ **名字误导型（v14 新发现）** | `Finset.le_max' _ _ (Finset.mem_univ i)` 给出的是 **`i ≤ max'`**（**指标**在界内），**不是** `M i ≤ M (max')`。⇒ 要点式取确界，用 **`Finset.univ.sup' M` / `inf' M`**（对**函数值**取上/下确界）配 **`Finset.le_sup'` / `Finset.inf'_le`**。<br>⚠ 该陷阱隐蔽：可能**编译通过但证的是另一个命题**，或在后续 `linarith` 处**莫名失败**（因为拿到的是一堆指标不等式）。 |
| **`Finset.le_sup'` / `inf'_le` 的 `s`、`f` 是命名实参** | 位置传参会**错位**（`le_sup' M (mem_univ i)` 会失败）⇒ 必须写 `Finset.le_sup' (s := Finset.univ) (f := M) (Finset.mem_univ i)`。 |
| **`BddBelow` / `BddAbove` 的展开形状** | `BddBelow s := (lowerBounds s).Nonempty`，而 `lowerBounds s = {a | ∀ ⦃b⦄, b ∈ s → a ≤ b}` ⟹ 展开后是 **`∃ a, ∀ b, b ∈ s → a ≤ b`**（**单层 binder，且第二段是函数不是存在量词**）。⇒ `obtain ⟨ρ, -, hEq⟩ := hz` 是**错的**；正确用法是把 `hz` 当函数用：`exact hz (transportCost c π) ⟨π, hπ, rfl⟩`。 |
| **`unfold f` 在 `Finset.sum_congr` 内部会让实例合成卡住** | 报 `AddCommMonoid ?m` / `Finset ?m` **stuck** ⟹ 用 **`show`** 做 beta 展开，而**不要** `unfold`。 |
| **`subst` 会"消去"变量，方向由 Lean 选** ⚠️ **症状极具误导性（v14 新发现）** | 有 `h : z = p` 时写 `subst h` **不是**把 `z` 换成 `p`——`subst` 会**消去其中一个变量**并让另一个成为代表元；实测它**消去了 `p`**，于是其后所有 `p` 的引用变成 **`unknown identifier 'p'`**（同一行 `∑` 里三个 `p` 就报三处 `280:32/40/46`）。<br>⇒ **症状（未知标识符）与病因（变量被 subst 主动删除）看起来无关**，极易误判为"binders 写漏/变量未绑定"。<br>⇒ **修法**：需要"**只替换、不消去**"时改用 **`rw [h]`**；需要消去时确认**消的是你想消的那个变量**。 |
| `def f (g z : T)` 会绑定**两个**变量 `g z : T` | 函数参数必须写 `(g : T → T) (z : T)` |
| ℂ 上 `conj` 未进作用域 | 用 `star` / `starRingEnd ℂ`；且 `Complex.conj_re` 左式是 `((starRingEnd ℂ) ?z).re`，`star w` **不匹配**——写 `starRingEnd ℂ w` |
| `Complex.normSq_apply` | 是 `re*re + im*im`（**不是** `re^2 + im^2`，与 `sq` 混用要 `ring`） |
| `sq_abs` | ℝ：`|a|^2 = a^2`；ℂ：`Complex.sq_abs : Complex.abs z ^ 2 = normSq z`（反向） |
| `Complex.abs z` 的非负性 | `Complex.abs.nonneg z`（AbsoluteValue 结构字段） |
| `Finset.sum_eq_single` / `prod_eq_single` | 结论是**双绑定**形式 `∑ x ∈ s, f x = f a`，对 `∑ x, f x = f a` 用不了（报 `AddCommMonoid ?m` 卡死）——改用 `Finset.sum_congr` + `if i = k then f k else 0` + `simp` |
| `Finset.prod_eq_zero` | 双绑定形式：`(hi : i ∈ s) (h : f i = 0) : ∏ j ∈ s, f j = 0` |
| `Finset.prod_eq_one` | `(h : ∀ x ∈ s, f x = 1)` |
| `Finset.any` 不存在 | `Finset.toList.any`（配 `List.any_eq_true`） |
| `pow_le_pow_left` 已弃用 | `pow_le_pow_left₀` |
| `linarith`/`nlinarith` 遇目标里的 `min`/`max` 失败 | 用 `sub_nonneg.mpr (min_le_left …)`、`add_le_add` + `mul_le_mul_of_nonneg_left` 显式组合 |
| `ContinuousLinearMap.opNorm_comp_le` 的位置参数（`h` 为自动绑定）歧义 | 用 `opNorm_le_bound` 自证次乘性，勿猜参数顺序 |
| 索引类型 vs 值类型混用 | 拉格朗日插值：节点 `x : n → ℝ` 时是 `∑ i, f i * lagrange x i (x k) = f k`，**不是** `f (x i)` |
| 分离定理"不存在"（早前判断） | **错**：4.14 已有 `geometric_hahn_banach_*`（`Mathlib/Analysis/NormedSpace/HahnBanach/Separation.lean`），见 `CORRECTIONS.md` B6 |
| `lake build lattice` 的 roots 是**显式白名单** | 新文件不加进 `lakefile.toml` 的 `roots` 就不会被编译/校验 |
| 任一 roots 源文件缺失 | `lake build lattice` **整体立即失败**（`no such file or directory`），不会只跳过该模块——先建文件再全量构建 |
| `ConvexOn`/`StrictConvexOn`/`ConcaveOn`/`StrictConcaveOn` **不是 structure**，而是 `def` 别名（定义体是合取式 `Convex 𝕜 s ∧ (∀ ⦃x⦄, …)`，见 `Mathlib/Analysis/Convex/Function.lean`） | 点号投影 `hf.1` / `hf.2` **会失败**（Lean 把 `hf.2` 当 `And.right hf` 后再吃后续实参，报出极具误导的 `application type mismatch @And.right lam` / `invalid argument name 'x' for function 'And.right'`）→ 用 `obtain ⟨hconv, hstrict⟩ := hf`（或 `obtain ⟨-, hstrict⟩ := hf`） |
| 同上：这些定义里 `⦃a b : ℝ⦄` 是**隐式绑定** | 目标里出现 `1 - lam` 这类复合项时无法反推 `a`/`b`，必须显式写 `(a := lam) (b := 1 - lam)`；否则 `b` 被错误统一成 `lam`（症状：`⊢ lam * 2 = 1`，极难看出） |
| `Finset.induction with \| insert a t ha ih` | **只接受 2 个显式名**（`insert a t`），多写报 `too many variable names provided` → 改用 `Finset.induction_on t` 显式绑定 `a t ha ih` |
| `set m := ∑ i, z i` | 会**连假设一起重写**；之后再 `rw [h1]`（`h1 : ∑ i, z i = m`）必然失败（模式已被替换掉）——这类"多余重写"是隐蔽错误源 |
| `𝓝[>]` | 需 `open scoped Topology`，否则 `𝓝` 是未知标识符；且 `IsClosed.mem_of_tendsto` 的 `[NeBot b]` 在 `b` 仍是元变量时会卡住——显式传 `(f := …) (b := …)` 并 `haveI` 给 `NeBot`（如 `nhdsWithin_Ioi_neBot' ⟨1, by simp⟩ le_rfl`） |
| `ring`/`ring_nf` 无法消耗 `hcd : c + d = 1`；`rw` 只重写**首个**匹配 | 不要写 `rw [← add_mul, hcd]`（常失败）→ 先 `have hb : c*b + d*b = b := by rw [← add_mul, hcd, one_mul]`，再 `linarith [hb]` |
| `Nat.cast_nonneg n` 在目标类型含元变量时 | 必须标注类型：`(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))` |
| `ℝ≥0` 记法无法解析（报 `failed to synthesize LE Type` / `OfNat Type 0`，极具误导） | 缺 `open scoped NNReal` |
| `MeasureTheory.maximal_ineq` 的 `{ε : ℝ≥0}` 是**隐式绑定且在 `n` 之前** | 必须显式 `(ε := …)`，否则 `n` 被喂给 `ε` |
| `ENNReal.toReal_coe` 在本版不存在 | 正确名是 **`ENNReal.coe_toReal`** |
| `Adapted` 没有 `.stronglyMeasurable` 字段（点号投影失败） | 展开为 `∀ i, StronglyMeasurable[𝒢 i] (f i)` |
| `condexp_of_stronglyMeasurable` 返回 `= f`（**不是** `=ᵐ`） | 需 `[SigmaFinite (μ.trim hm)]`，通常由 `𝒢.le i` 自动合成 |
| `linarith` 无法统一 `condexp` 项里隐藏的 instance 参数（字面相同却报 `linarith failed`） | 改 `sub_nonneg.mpr` 或显式喂项 `linarith [hω]` |
| 自定义 `local notation "x"` 后接投影语法 | 报 `no macro or quot_precheck instance for syntax kind 'Lean.Parser.Term.proj'` → 别用自定义记法包投影，改内联 `Finset.sup'` |
| 隐式绑定中"先用后绑"的变量 | Lean 自动重命名为 `lam✝`，导致假设类型不匹配 → 把 `{lam}` 提到使用它的假设**之前** |
| `MeasureTheory.measureReal_def` **在本版 mathlib 完全不存在**（被反复复制的假引理名） | 用 `MeasureTheory.integral_const` + `MeasureTheory.measure_univ` + `norm_num`；`ENNReal.toReal_one` 同样不存在 |
| ~~`Measure.integrable_toReal_rnDeriv` 不存在~~ ⚠️ **本条目 v14 已更正：该引理 EXISTS** | **旧条目声称"不存在"——是错的**（"以名字判有无"的第 6 次同族失误）。**实测**：`MeasureTheory/Decomposition/Lebesgue.lean:361`：`lemma integrable_toReal_rnDeriv [IsFiniteMeasure μ] : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν`。<br>⚠ **替换时易搞反方向**：该引理的**被积函数里 `rnDeriv` 的前件 = 积分测度**。LATTICE 侧写 `ρ = ν.rnDeriv μ`（其前件是 `ν`、积分测度是 `μ`）——**代入 `τ := ν`、`υ := μ` 即逐字命中**，**不需要** `ν.rnDeriv μ` 与 `μ.rnDeriv ν` 的任何转换关系。<br>⇒ **`RealRNGibbs` 的显式假设 `hintρ` 已因此删除，3 条定理升级为无条件版**（v14，构建 exit 0）。<br>（**仍成立**的部分：`Measure.rnDeriv_ne_top` 是 **a.e. 陈述**，形如 `∀ᵐ x ∂ν, … ≠ ∞`，**不能当逐点等式用** → 必须进 `filter_upwards`。） | |
| `abs_integral_le_integral_abs` **只存在于 `IntervalIntegral`**（且带 `hab : a ≤ b`） | 全空间版是 `norm_integral_le_integral_norm` |
| `^` 的指数类型会被推断成 `ℕ` | `q i ^ (1 - 2)` 里 `1-2` 是 ℕ 减法（`rw [show (1:ℝ)-2 = -1]` 永不匹配）→ 必须写 `(1:ℝ) - 2`；且 `p i ^ (2:ℝ)`（rpow）与 `p i ^ 2`（pow）**不是 defeq**，需单独 `norm_num` 桥接 |
| `Finset.sum_mul_sq_le_sq_mul_sq` 是**双绑定** `∑ i ∈ s` | 不是单绑定；`Finset.sum_univ` **不是有效标识符** |
| `div_le_iff` / `div_le_div_iff` 已弃用 | 改用 `div_le_iff₀` / `div_le_div_iff₀` |
| 遇到"类型对不上"时的优先解 | **优先泛化索引类型而非削弱命题**：把 `renyiDivergence {n} (p q : Fin n → ℝ)` 泛化为 `{ι} [Fintype ι]` 是**严格更一般**的定义，接口打通而命题强度不变（`RealRenyiDP` 实例） |
| `omit ... in` 的位置 | **必须写在 docstring 之前**；写在 `/-- … -/` 之后报 `unexpected token 'omit'; expected 'lemma'`（本轮 4 个文件共 8 处） |
| `toEuclideanCLM` 的首参是 **`Type`** | 要写 `(n := Fin n)`，写 `(n := n)`（自然数）报 application type mismatch |
| `(A).HasEigenvalue μ` 点号投影失败 | `LinearMap.HasEigenvalue` 不存在 → 用前缀形式 **`Module.End.HasEigenvalue f μ`** |
| `Complex.star_def` 是**函数级**等式 `(star : ℂ → ℂ) = conj` | 不能 pointwise `rw`；`star μ = μ` 由 `conj μ = μ` **定义相等**直接给出（另需 `open scoped ComplexConjugate`） |
| `Field` / 类型类目标是 **Type 层而非 Prop** | 写成 `theorem ... : Field (AdjoinRoot p)` 会报 `type of theorem ... is not a proposition` → 必须用 **`def`**（语义不变，但要在 docstring 标注"形式调整"，避免被当命题引用） |
| `local notation` 的 `𝕜` 在定理自身 `{𝕜 E}` 绑定**之前**解析 | 会报 `failed to synthesize Inner 𝕜✝ E`（section variable 被重命名为 `𝕜✝`）→ 显式 `@inner 𝕜 E _` 是唯一稳的解 |
| `Finset.sum_comm` / `Finset.sum_div` / `Finset.sum_mul_sq_le_sq_mul_sq` **都是双绑定**（`∑ x ∈ s, …`） | 对单绑定 `∑ i : ι,` 目标**能用**，但对已被改写成别的形状的目标会**静默匹配失败**（`did not find instance of the pattern`）→ 先 `rw` 成目标形状或改用 `Finset.sum_congr` |
| `field_simp` 遇到"除数是自由变量"时 | 会留下 `True ∨ x = 0` 之类除零义务，**且可能已把主目标关掉** → 后面跟 `ring` 报 `no goals to be solved`；正确做法：只留 `field_simp`，或显式 `exact Or.inl (mul_comm _ _)` 收尾 |
| `Finset.mul_sum` 正向是 `a * ∑ f = ∑ a * f` | 反向用须 `rw [← hmul]` 且 `hmul` 左右式写对，否则 `did not find instance of the pattern` |
| `∑ i ∈ range n, x ^ i / i !` 里的后缀阶乘记法 `i !` | 与双绑定求和体组合时解析崩溃，报极具误导的 `function expected at i, term has type ℕ` + `failed to synthesize AddCommMonoid (Sort ?u)` → 写 `(Nat.factorial i : ℝ)` |
| 构建日志里出现 `⊢ sorry` | **不一定是源码有 sorry**：那是 `have h` 证明失败时 Lean 插入的合成占位符 → 用剥注释后的源码扫描判定（`grep -n '^\s*sorry'`） |
| `Summable.norm` / `summable_norm_iff` 在 4.14 **要求 `FiniteDimensional ℝ E`** | 对一般完备赋范环/巴拿赫空间**不可用**（报误导性的 `failed to synthesize FiniteDimensional ℝ 𝔸`）→ 改用 `Summable.of_nonneg_of_le` + `Summable.of_norm` |
| `norm_mul`（**等式**）只对 `NormedDivisionRing` 可用 | 一般 `NormedRing` 只有 `norm_mul_le`（不等式）→ `rw [norm_mul]` 报 `did not find instance of the pattern ‖?a * ?b‖`；证明须全程用 `≤` |
| 后缀记法 `n!⁻¹`（`!` 紧跟 `⁻¹`） | **解析失败**（`unexpected token '!'`）→ 写 `((n.factorial : ℝ))⁻¹` |
| `NormedSpace.exp` 的首参是**显式标量域** | `(𝕂 : Type) → {𝔸 : Type} → …`；在目标类型未定的**陈述**里必须写 `NormedSpace.exp ℝ x`，否则 `x : 𝔸` 被当成 `𝕂` |
| 非交换 `Monoid` 下的乘积 | `Finset.prod` 要 `CommMonoid` → 只能用 **`List.prod`** |
| `lakefile.toml` 被并发写入破坏的征兆 | `lake build <任意目标>` **在解析阶段就失败**（`unexpected 'r'; expected ']'` / `expected end of input`）且与模块无关 → 检查 `roots = [` 是否重复、括号是否平衡（本项目曾出现 `roots = [roots = [` 与多余 `]]`）；`roots` 应只出现一次 |
| **`while` 是 Lean 保留字** | 不能作 `cases S with \| while b body =>` 或 `case while b body =>` 的分支名（报 `unexpected token 'while'; expected '_' or identifier`）→ 用 **`cases S`（不带 `with`）+ 前几个 `case 构造子名 =>` + 末分支位置式 `rename_i b body`** |
| `WellFounded` 是 **inductive**（不是 def 别名） | `intro n` 报 `insufficient number of binders` → 须 `refine WellFounded.intro ?_` |
| `WellFounded.induction` 的动机是 `a` **之前**的隐式参数 | 只写 `hT.induction a ?_` 会失败 → 须命名：`hT.induction (C := fun x => ∀ b c, …) a ?_` |
| `def` 别名（`Joinable` / `VectorConstraintSat` / `wp` / `ConvexOn` 族）是**不透明**的 | 三种症状与对策：点号投影失败（`h.1`/`h.2`）→ `obtain`；`rw` 找不到模式 → 先 `unfold`；`decide` 报 `failed to synthesize Decidable …` → 先 `unfold` |
| `h : n₁ = d`、`h' : n₂ = d` 要合成 `n₁ = n₂` | 写 `h.trans h'.symm`；`h.symm.trans h'.symm` 是类型错误 |
| **`one_le_mul` 在 mathlib 4.14 不存在** | 真名是 `one_le_mul_of_one_le_of_one_le`（但类型类前提常不匹配）→ 安全写法：`calc (1:ℝ) = 1 * 1 := by ring; _ ≤ a * b := mul_le_mul ha hb (by norm_num) (by linarith)` |
| **`rw [h]` 在 `abs` / `congrArg` 内部重写，且 `h` 的 LHS 是自身 RHS 的子项** | 会**自我嵌套发散**，错误信息里出现**双重展开项**（如 `\|… - y + y - y + y\|`），伪装成类型错误 → 改用项级操作：`abs_add` + `rwa [hid] at h` |
| `linarith` 不认 `a + b - a` 即 `b` | 先 `have : a + b - a = b := by ring` 再喂给它 |
| `lake build` 只接受 lakefile `roots` 里的目标 | `lake build _probe.lean` 与 `lake build _probe` 都报 `unknown target` → 探针用 `lake env lean <file>`（但同样要抢构建锁，排队代价高；**建议直接在正式文件里改完再批量构建**） |
| `#eval` 自检里对含 `Float.log`/`Float.exp` 的量做 `==` 精确断言 | **数学上常为错**（例：`softplus 0 = log 2 ≈ 0.693147 ≠ 0`）→ 只对**精确可实现**的等式断言（max、`sigmoid 0 = 0.5`、`rope θ=0`），超越量改用**区间断言**并在 docstring 标注"不做浮点精确断言" |
| 判断共享文件（如 `lakefile.toml`）是否真的被写坏 | **PowerShell 控制台的自动折行会伪造出"多余括号/重复前缀"的假象**（屏幕上是 `]]`，文件其实是合法 TOML）→ 必须**字节级核验**：`[System.IO.File]::ReadAllText($p, UTF8)` 后统计 `roots\s*=` 出现次数与 `[`/`]` 配对数，或用 `Format-Hex`；**不要凭折行渲染就动共享文件** |
| 三重求和 `∑ a, ∑ b, ∑ c` 中 `rw` 报 "pattern not found" | 常见根因是**binder 遮蔽（shadowing）**：内层 `a` 遮蔽了外层 `b`，使 `hπ.2.2 b` 里的 `b` 指错变量 → 先用 `Finset.sum_comm` 把需要的变量提到未遮蔽的外层再重写（靠试 API 名字修不出来） |
| `Finset.sum_ite_eq` / `sum_ite_eq'` / `sum_mul` / `sum_div` 的首参 | 是**显式** `s : Finset α` → 旧写法漏传会报 pattern 不匹配，须补 `Finset.univ`；且 `∑ c, x * y c / q` 这种"先乘后除"的顺序与 `sum_mul` 的模式不符，需 `sum_div` + `mul_sum` 组合 |
| **十进制字面量被 Lean 归一化**（如 `0.044715` 显示/归一为 `44715e-6`） | 使 `rw` / `ring` 的**语法模式匹配静默失败**（目标里的写法与源码里的写法不再字面相同）→ 遇 `44715e-6`/`e-6` 出现在目标中时，改用显式 `show` / `calc`，不要依赖 `rw` 模式 |
| 目标出现 `⊢ ?m.xxxx`（**未赋值元变量**） | 通常是某处的类型/隐式参数无法推断（常量字面量、`abs` 内的 `0`、overload 的运算）→ 用 `show <完整类型>` 显式化，或给隐式参数具名传参；级联出现的 `unexpected token 'λ'` 往往是同一根因（Lean 把待定项解析成了 lambda 位置） |
| 反向三角不等式（复数/向量范数） | 用 `abs_norm_sub_norm_le : \|‖x‖ − ‖y‖\| ≤ ‖x − y‖`（`abs_abs_sub_abs_le_abs_sub` 是其标量版）——modReLU/RMSNorm 这类"径向缩放"的 Lipschitz 证明几乎都要它 |
| **`λ` 被用作标识符**（如 `hλz`、`hλw`、`hλzpos`） | `λ` 是 Lean **保留 token** → 症状是 `⊢ ?m.xxxx` **未赋值元变量 + 级联 `unexpected token 'λ'`**，**且报错位置指向所在分支的首行而非真正出错处**（极难定位；本轮实测改名 `hlam*` 后两处错误同时消解） |
| `AbsoluteValue.map_add_le` **不存在** | 正确名是 **`AbsoluteValue.add_le`** |
| **`mutual` 命题块**（⚠ **归因已更正，见 R2 调研**） | 实测报错是 `unexpected token 'mutual'; expected 'lemma'`。**但这并非"4.14 版本限制"**：两套 Lean 源码树（v4.14 / v4.33）逐行对照显示 `isDefLike` **两版都含 `theorem`**，且 `checkKinds` 两版都写 `"cannot mix theorems and definitions"`（该分支存在的前提就是 theorem **能**进 mutual 块）。**真实原因多半是用法/报错误导** ⇒ **不要为"等升级解决"而重写**；建议先用一次探针实测三种写法（无文档注释的 `mutual theorem` / 块级 docstring / 块内元素级 docstring）。若 (a) 通过，则本条与下一条可合并 |
| `mutual` 块内使用 `/-- … -/` **文档注释**（⚠ **归因已更正**） | 实测非法，但**同样是设计使然**：`mutual` 是**独立 `commandParser`**，**不经 `declModifiers`**（v4.33 亦然，parser 逐字相同）⇒ **不会被升级修好**。对策：块内改普通注释，块级说明上提到小节标题 |
| **多叉树递归**：`termination_by t => sizeOf t` + `decreasing_by`（⚠ **归因已更正 + 引理名更正**） | ⚠ **引理名错**：本条曾引用 `List.sizeOf_lt_sizeOf_of_mem`，**该名字不存在**；真名是 **`List.sizeOf_lt_of_mem`**（`Init/Data/List/BasicAux.lean:185`，v4.14）——照抄必失败。<br>⚠ **归因错**：这不是"4.14 限制"。两版源码 `shouldUseStructural` 逻辑相同：**一旦写了 `decreasing_by` 就强制走 well-founded recursion**，而 WF 归纳的上下文里**没有 membership 假设**（goal 形如 `⊢ sizeOf a < 1 + sizeOf ts`）——这是 **WF 归纳的数学本质**，**任何升级都不会改变**。<br>对策（不变）：改用 **`Tree` 与 `List (Tree α)` 互递归**（Lean 自动接受结构递归），终止性证据移到显式引理（`child_sizeOf_lt` 等） |
| 自定义 `def … : Prop := A ∧ B`（如 `IsMedian`）的 `.1`/`.2` 投影 | 与 `ConvexOn` 陷阱同源（def 别名不透明）→ 用 `obtain ⟨h1, h2⟩ := h` |
| `Finset.mul_sum` / `sum_add_distrib` 对**双绑定**目标 | `rw` 可能**静默匹配失败**；也可能**已直接关掉目标**，其后紧跟 `exact` 会报 `no goals to be solved` |
| **禁止用 PowerShell 文本 cmdlet 改写 `.lean` 文件** | `Set-Content -Encoding UTF8` 会**加 BOM** 并把**中文注释转成 U+FFFD**，Lean 报 `expected token` / `invalid UTF-8`（仓库含大量中文 docstring，本轮因此重写过一个文件）→ 一律用 `edit`/`write` 工具，或 .NET 显式 `UTF8Encoding($false)` |
| `Equiv.Perm.symm_mul` 名字**具误导性** | 它是 `e.symm * e = 1`，**不是** `(π*σ)⁻¹ = σ⁻¹*π⁻¹`；后者须用 `Equiv.symm_apply_eq` 手证 |
| 卡片计数过滤引理的名字 | 是 **`Finset.filter_card_add_filter_neg_card_eq_card`**（**不是** `card_filter_add_card_filter_not`） |
| `Finset.card_eq_two` / `card_eq_three` 是 **iff** | 不能 `rw` 当等价式用 → 配 `Finset.card_pair` 或显式 `card_insert_of_not_mem` 更稳 |
| `Nat.div` 与 `omega` | `omega` **穿不透** `Nat.div`（如 `nb*(nb+1)/2 ≤ nb*nb`）→ 用 `Nat.two_mul_div_two_of_even` + `Nat.even_mul_succ_self` 先把除法消成乘法；`Nat.div_le_iff_le_mul_add_pred` 可把 `/2 ≤` 转为 `≤ 2*_+1` |
| 绝对值下的 min 恒等式 | `min a b = (a + b − \|a−b\|)/2`（**不是** `a − \|a−b\|/2`，后者在 `a<b` 时给出 `(3a−b)/2 ≠ a`）；且 `abs_neg` 只改 `\|−x\|`，遇裸 `−(a−b)` **不匹配** |
| `Finset.sum_sdiff` 的 LHS 顺序 | 是 `∑_{s\t} + ∑_t`（**后项在前**）→ 直接 `rw` 常失败；配 `simp only [Finset.sdiff_eq_filter, Finset.sum_filter]` + `abel`/`linarith` 更稳 |
| `Finset.sum_range_succ'` 去**首**项 vs `sum_range_succ` 去**末**项 | `∑_{t<k} 0^t` 的拆分**必须去首项**（`t=0` 项是 `0^0 = 1`）；用去末项的版本会得到错的目标 |
| **非交换环中乘积顺序**（选择性 SSM 类） | 递推 `h_{n+1} = A_n h_n` 中 `A_n` 在**左** ⟹ 展开是 `A_{t-1}(⋯(A_k h_k))`，即乘积**下标递减**；写成递增 `A_k⋯A_{t-1}` 在非交换环中**数学上为假**（见 CORRECTIONS B18） |
| **`ring`/`linarith` 证不出某目标时** | **先判断目标是否为真**：代入小整数（如 `a=1,b=2,c=3,d=4`）算一遍。Lean 打印的是**归一化后的「剩余目标」**，**不是**"ring 算错后的归一形"——目标之所以剩下，往往正因为**原命题为假**。本轮有代理把三个**本身为假**的多变量等式误判为"`ring` 在本环境失效"，进而**绕开 ring 重写证明**、并建议**全库排查**与**重建 mathlib**——误诊代价极高。<br>判据：目标为假 → **改命题**；目标为真 → 再查原子匹配（`x*x` vs `x^2`、隐式强制转换、`/` 与 `*` 形状不一致等） |
| **快速迭代探针法** ⚠️ **本条已于 v14 修订；旧做法不再获授权** | **旧原文**曾写「`Copy-Item Foo.lean _probe_Foo.lean` 后跑 `lake env lean _probe_Foo.lean`——**秒级返回、不抢锁**……**锁只用于最终验证**」。该写法**只在【单代理、无争用】语境下成立，现已作废**。<br>**现行纪律（优先于本条）**：⭐ **单文件探针一律用 `scripts\probe.ps1 <文件>`**（它是 `lean-lock.ps1` 的薄封装：**同一把锁**、**默认拒绝在有人裸跑时启动**）：

```
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\probe.ps1 lean\_probe_foo.lean
powershell ... -File scripts\probe.ps1 -Scratch lean\Foo.lean   # 自动做 _probe_Foo.lean 副本（副本在锁内产生）
powershell ... -File scripts\probe.ps1 -Soft  lean\Foo.lean     # 明知有裸跑者仍要跑（结果可能含幻影错误）
```

**底层入口**：`lake env lean` **必须**走 `scripts\lean-lock.ps1 <单个文件名>`（与构建**同一把锁**；**一次只许传一个文件**，否则脚本直接拒绝）。<br>**为何修订（实测）**：① 11–14 个并发探针把 lean 内存推到 **28.5 GB**（机器 15.7 GB）、空闲内存跌到 **0.5 GB**；② "免锁快路径"单次 **114–182 秒**，**比被锁的真实构建（88 秒）还慢**；③ 本项目实测**两次 60 分钟探针超时**、**55–67 个进程排队**，均因"免锁探针"与长构建叠加。<br>⚠️ **v14 封堵实测（A1）**：本纪律**不是规则模糊，而是已撤销的做法仍在被使用**——快照实测 **RAW 21 / locked 3**（**leaf `lean.exe` = 8**，即约 8 个并发 mathlib 载入）。故 v14 不再只靠"写明规则"，而是**技术性封堵**：`probe.ps1` / `lean-lock.ps1 -NoBypass` 在检测到裸跑者时**拒绝启动（exit 9）**，`verify.ps1` 增加 **lock discipline advisory** 段（`-StrictLock` ⟹ exit 7）。<br>**现行推荐**：**代码写完 → 报协调者 → 由协调者一次 `lake-lock.ps1` 批量构建多模块**（实测 **31 模块/42 分钟**，远优于 31 次各自排队）。探针名用 `_probe*`（已 gitignore），完工删除。<br>（另注：`lake build _probe` 不行——lake 只接受 roots 里的 target；且**不要把 `.lean` 文件名传给 `lake-lock.ps1`**，那会让它逐个跑 `lake env lean` 并长期独占构建锁。） |
| 数值假设类命题**务必代小整数复核** | 本轮实测两例：`eps·(m+1) + tiny ≤ m`（`m=1, eps=1/2` 即假）与 `(ηζ²/μ)·(1/(μη)) = ηζ²/μ²`（`η=2,μ=3,ζ=1` 即假，正解是 `η` 约掉的 `ζ²/μ²`）。**"看起来合理"的数值假设最容易藏假命题**，且会让下游结论全部失去支撑（见 CORRECTIONS B21/B22） |
| **`Fact (Irreducible p)` 不会合成 `Fact (p ≠ 0)`** | Lean 的 `Fact` 是 `Prop` 包裹的普通记录、**没有类型类蕴含机制**，故 `Fact (Irreducible p) → Fact (p ≠ 0)` **不能**声明为 `instance` 自动合成。`AdjoinRoot.powerBasis` 要求后者 → 必须显式装配：`haveI : Fact (p ≠ 0) := ⟨(Fact.out : Irreducible p).ne_zero⟩`（WP13 `RealAdjoinRootCard.arc_fact_ne_zero`） |
| **`AdjoinRoot` 没有 `Fintype` 实例**（4.14 与 4.33 均无） | 手写是**必要**的：`Fintype.ofEquiv (Fin dim →₀ F) (basis.repr.symm)`，其中 `dim = (AdjoinRoot.powerBasis f hf).dim`；**注意 `repr` 方向**是 `AdjoinRoot p ≃ₗ (Fin dim →₀ F)`，`Fintype.ofEquiv` 要求「待赋实例的类型在左」，故必须 `.symm`。<br>**接口写法**：把 `Fintype (AdjoinRoot p)` 作为**显式参数** `(inst : Fintype (AdjoinRoot p))` 传入，语句里即可写干净的 `Fintype.card (AdjoinRoot p)`；**不要**写 `@Fintype.card _ (实例项)`（`@` 形式下隐式 `Fact` 参数会让 `Fintype.card` 综合卡死：`function expected at …`） |
| **`Matrix.eval_charpoly` / `Polynomial.eval_det` 在 4.14 都不存在** | 正确名是 **`Matrix.eval_det`**（`LinearAlgebra/Matrix/Charpoly/Coeff.lean:166`，语句 `Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).det`）配 **`matPolyEquiv_charmatrix`**（`Charpoly/Basic.lean:61`）。<br>**通用教训**：`unknown constant` ≈ **名字记错**，**不等于**「定理不存在」——先在本仓库 `.lake/packages/mathlib` 里 grep 关键字（如 `eval_det`、`charpoly_map`）再下结论（本项目 B6/B23/B24/B25 均为此族失误） |
| **`Polynomial.eval_map` 产出 `eval₂`，不是 `eval`** | `rw [Polynomial.eval_map]` 后目标是 `Polynomial.eval₂ (algebraMap ℝ ℂ) μ p`；要按系数展开必须用 **`Polynomial.eval₂_eq_sum_range`**（用 `Polynomial.eval_eq_sum_range` 会 `pattern not found`） |
| **`Lagrange.eval_interpolate_at_node` 等 `s`/`v`/`r` 是 implicit** | 它们来自 `Lagrange.lean` 的 section `variable {s t} {v} (r r')`，**不能按位置传**（会报 `application type mismatch … has type Finset … but is expected to have type ? → ?`，极具误导）→ 必须具名：`Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := alpha) (r := y) hvs hi` |
| **`Real.rpow_mul` 的方向** | 语句是 `x ^ (y * z) = (x ^ y) ^ z`（**先积后幂**在左），故把 `(x^a)^b` 化成 `x^(a*b)` 要用 **`rw [← Real.rpow_mul hx]`**，用正向会报 `did not find instance of the pattern` |
| **`ContinuousLinearMap.norm_id` 要求 `[Nontrivial E]`** | `EuclideanSpace ℝ (Fin 0)` 是**单点空间**（不 `Nontrivial`），故 `‖matCLME (1 : Matrix (Fin 0) (Fin 0) ℝ)‖ = 1` **不成立**。写成 `≤ 1`（`ContinuousLinearMap.norm_id_le`，**无条件**）再在 `0 < n` 时升级为 `= 1`；另外造 `Nontrivial (EuclideanSpace ℝ (Fin n))` 用常函数 `1 ≠ 0` 直接给（`Pi.single` 会触发 `isDefEq` 心跳超时） |
| **用名称判断「定理是否存在」是系统性错误源** | mathlib 会**把定理搬进新文件而不新增定理**（如 v4.24 只是把 Gelfand 公式拆到 `GelfandFormula.lean`，而 4.14 的 **`Spectrum.lean:374` 早已有** `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`）。判据：**在本地 `.lake/packages/mathlib` grep 定理名/关键字，看 `文件:行号`**，不要用「有没有某个文件」推断（CORRECTIONS B25） |
| ⭐ **`unfold`/`simp only` 都【不做 β-归约】⟹ `if_pos`/`dif_pos` 全会失配** ⚠️ v14（**F3 新发现，成片 error 的隐藏主因**） | `def f := fun k => if (k:ℕ) < d then … else …` 上写 `unfold f` 后，`if` **仍埋在 λ 里**，于是 `rw [if_pos hk]` / `rw [dif_pos hk]` 一律报<br>`did not find instance of the pattern … dite (↑k < d) ?m ?m`。<br>**修法**：改用 **`simp only [f]`**（`simp` 会做 β-归约，把两侧 λ 打开）；`unfold` **不能**替代。<br>⚠ 另一面：**不要**用 `simp only [eq_self, and_true, …]` 去消 `if` 的**判别式**——报 `tactic 'rewrite' failed, motive is not type correct`；正解是 **`rw [if_pos ⟨hk, rfl⟩]`** 交出整个合取。<br>（实证：`RealInContextLearning` 的 `projMatrix_mulVec` / `projLabelMatrix_mulVec` / `sum_projLabelMatrix_mul`，修复后 exit 0。） |
| ⭐ **`first` 组合子的杀手是【放在首位的 `exact`】，不是 `simp`** ⚠️ v14（**修正了此前的归因**） | 实测（锁定探针）：`first \| exact lem_a _ \| exact lem_b _ _` 中，当 `lem_a` 的构造子**不匹配**时，`exact lem_a _` **不报错**——它把隐式参数留成元变量、目标未闭合，Lean 只发 `warning: this tactic is never executed` / `'exact …' tactic does nothing`，而 **`first` 立刻接受该分支**（`first` 判据是"没报错"）。<br>⇒ **正解**：给每个分支加 **`<;> done`**（`exact lem_a _ _ _ <;> done`），逼它真失败，`first` 才会续试。<br>⇒ **且**：`cases h` 在 `h : <构造子> = some ir` 且 `ir` 是**局部假设**时会**朝错误方向消去**；须先 `injection h with h'` 再 `subst h'`。<br>（实证：`RealLv00Compiler` 24 条 `unsolved goals` 由此归零。） |
| **`rw` 不穿透 `∑` 的 binder ⟹ 用 `conv_lhs => enter […]`** ⚠️ v14 | `rw [Finset.mul_sum]` 对 `∑ x, (a x * ∑ i, f i x)` 报 `did not find instance of the pattern ?a * ∑ i ∈ ?s, ?f i`——因为 `a x * ∑ i, …` 在 **binder 体内**。<br>⇒ 用 **`conv_lhs => enter [2, x]; rw [Finset.mul_sum]`** 进体内改写；或先 `apply Finset.sum_congr rfl; intro x _` 再 `rw`。 |
| **两侧 `∑` 指标类型不同时 `apply Finset.sum_congr` 必失败** ⚠️ v14 | 目标 `∑ x : Fin (d+1), … = ∑ i : Fin n, …` 上 `apply Finset.sum_congr rfl` 报 `apply failed to unify ?m.sum ?m = ?m.sum ?m`（`sum_congr` 要求**同型**）。<br>⇒ 必须**先把一侧的内层 `∑` 用 `Finset.sum_comm` 提到外层**使两侧同型，再 `sum_congr`。 |
| **`field_simp`-free 处理 `b / a` 的稳妥配方** ⚠️ v14（**F3 实证 exit 0**） | 形如 `a * (b / a) = b` / 配方法这类目标，若禁用 `field_simp`：<br>① `simp only [div_eq_mul_inv]` 把 `b / a` 全换成 `b * a⁻¹`；<br>② 记 **`hba : a * (b * a⁻¹) = b`**，证法是 **`rw [← mul_assoc, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha, mul_one]`**<br>&nbsp;&nbsp;⚠ **必须 `← mul_assoc` 起手**：目标 `a * (b * a⁻¹)` 是**右结合**，直接 `rw [mul_assoc]` 报 `did not find instance of the pattern ?a * ?b * ?c`；<br>③ 降幂用 `hsq : a * (b * a⁻¹)^2 = b * (b * a⁻¹)`（`rw [pow_two, ← mul_assoc, hba]`）；<br>④ 右式 `a * (η - b*a⁻¹)^2` 先用 `key`（`ring` 证）展开成 `a*η^2 - 2*(a*(b*a⁻¹))*η + a*(b*a⁻¹)^2`；<br>⑤ `rw [key, hba, hsq]` 后 `ring` 闭合。<br>⚠ **纯 `ring_nf` 收不掉**：归一形里 `a⁻¹` 以 `a * b^2 * a⁻¹^2` 这类形态出现，`rw [mul_inv_cancel₀ ha]` 匹配不到（实测 `did not find instance of the pattern a * a⁻¹`）。 |

---

## 5. 证明策略约定

1. **诚实降级优先**：命题太难就**缩小陈述**并在 docstring 写清"缩了什么、为什么、留待什么"，**绝不 sorry**。
2. **假命题处理**：发现原稿命题为假 ⟹ **不证**，给出反例（能在内核验证的写为定理，如 `ce_not_joint_convex`），并登记到 `CORRECTIONS.md`。
3. **常数收紧**：给界时若发现可收紧（如 `2/c → 1/c`），另立紧版定理并说明与旧版的关系，**不删旧版**（旧版仍是有效上界）。
4. **降级要可审计**：docstring 里用统一关键词 `诚实`/`未证`/`未做`/`降级`/`标注`，便于 `ASSUMPTIONS.md` 自动提取。
5. **优先复用**：新定理先查既有文件（如 `convComb_norm_bound`、`block_lipschitz_bound`、`chainN_error_bound`、`logsum_le`），绝大多数结构性质已有骨架，实例化即可。
6. **反例也很有价值**：不可证 ≠ 无价值；给出**具体反例 + 反例为何成立的证明**同样计入成果（`gd_oscillation_counterexample`、`slater_not_sufficient_discrete` 等）。
7. ⭐⭐ **零化范式下「零集 ≠ 取值」——组合子的零集承载逻辑语义，其数值承载的是编码的代数残余** ⚠️ v14（**R4 从一处真事故中得来**）

   LATTICE 的组合子用「**一个表达式 = 0 ⟺ 逻辑条件成立**」编码逻辑。⚠ **但这只约束【零集】，
   对【数值本身】不施加任何约束** —— 两者一般**不同**。实证（`CombinatorsXorNot.lean`）：

   ```
   orC X Y = X · Y
     零集：  X = 0 ∨ Y = 0              ← **析取**（这是「OR」名字的来源）
     数值：  两者都非零 ⟹ 乘积非零        ← **合取**的代数像
   ```

   ⇒ ⭐ **两者叠加，恰好把 XOR 翻成 XNOR**：
   ```
   xorC a b 的【零集】：(0,0)假 (0,1)真 (1,0)真 (1,1)假   ⟹ **正是 XOR** ✓
   xorC a b 的【取值】：  1      0      0      1          ⟹ ⚠ **是 XNOR**
   ```

   ⚠⚠ **本条是从一处【假命题】中得来的**：初稿写 `notC a = xorC a 1`，
   **被 `decide` 否证**（报 `tactic 'decide' proved that the prop…`）。
   ⭐ **且它在【两个点上都反】** —— 只看 `(0,0)` 或只看一种情形**会漏**。

   ⇒ ⭐⭐ **纪律（可复用）**：
   | 要做的事 | 正确形态 |
   |:--|:--|
   | 陈述「组合子 X 与逻辑 Y 等价」 | ⭐ **用零化命题 `X = 0 ↔ …`** |
   | 陈述「两个组合子同源」 | ⭐ **用零化等价**（`notC a = 0 ↔ xorC a 0 = 0`），**不可用取值相等** |
   | ⚠ 非要用取值相等时 | ⚠ **必须先在 `{0,1}` 上【逐点验算全部四种情形】** |

   ⭐ **命名判据（同时确认）**：`andC`/`orC`/`xorC` **全部按【零集】命名**，**不按取值命名**
   （`orC 1 1 = 1` 取值非零却叫 OR）⟹ **不可因"取值是 XNOR"而把 `xorC` 改名**。

   ⭐ **这是 B222.2（`X ↔ X` 能编译但什么都不说）的**对偶面**：B222.2 是「看着空洞」，
   本条是「**看着显然、实为假**」—— 而 `decide` 是**唯一**可靠的仲裁者。
   （登记：`DIVERGENCES.md` **C-26**、`CORRECTIONS.md` **B247**。）

---

## 6. 提交前检查（`scripts/verify.ps1` 自动做）

1. `scripts/verify.ps1`：roots/文件/olean 完整性 + 真实 sorry 扫描（剥注释后）+ 统计；
2. `scripts/verify.ps1 -Build`：附加 `lake build lattice` 全量构建；
3. `scripts/verify.ps1 -Build -UpdateDocs`：用真实数字同步 `README.md`/`VERIFICATION.md` 的统计行（消除人工漂移）；
4. 新增更正 → 追加 `CORRECTIONS.md`；新增降级 → 由脚本重生成 `ASSUMPTIONS.md`。
| **「单点必要条件」不是全称命题的可满足性见证**（**B357**，内核反证）| 由「对某个 `x₀`，`P x₀` 的**必要条件**成立」推出「`P` 可满足」—— ⚠ **无效**。事故：`hB : ∀ z, ‖z‖ ≤ B` 被注释为「`z = 0` 处给 `0 ≤ B`，可满足」，**而 `hB` 实际不可满足**（由它得 `∀ t : ℝ, |t| ≤ B` ⟹ `False`）。⭐ 同文件 `:44-46` 用同一条单点逻辑判 `hxdom` 空洞 ⟹ **判据自相矛盾**。**正解**：可满足性须给**充分**见证（展示 `x₀` 使 `P x₀` 成立）；全称命题不能由真子域实例证明；并自查文件内推理一致性。|
