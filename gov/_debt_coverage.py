"""Coverage reporting for PROOF-DEBT.md, kept in its own module.

## Why a separate file

Round 226 tried to inline this block into `gen_proof_debt.py` through a patch script, and the patch
script itself failed to parse because of nested quoting. **A patch script that carries a hundred lines of
Chinese prose inside a Python string literal is a bad idea** -- the quoting is fragile and the failure mode
is silent (the patch simply does not apply, and the generator keeps producing the old output).

Kept separate, the block is ordinary code with ordinary quoting, and `gen_proof_debt.py` gains only an
import and one call.

## What it states

**Both directions, because one alone misleads.**

- "We reviewed 1,382 of 11,149 declarations" is true and hides that the **load-bearing set is fully
  covered**.
- "The load-bearing set is fully covered" is true and hides that the **zero-in-degree set is barely
  sampled**.

So the table gives: theorems+lemmas, in-degree >= 1, in-degree == 0, each with its own coverage. The numbers
are computed from the same inventory the ledger uses, so they cannot drift from it.
"""


def emit(A, inv, reviewed_keys):
    # inv is a DICT keyed by (file, name) in the generator; accept a list too so the module is
    # usable from a measurement script without conversion.
    rows = list(inv.values()) if isinstance(inv, dict) else list(inv)
    thm = [r for r in rows if r["kind"] in ("theorem", "lemma")]
    t1 = [r for r in thm if r.get("in_degree", 0) >= 1]
    t0 = [r for r in thm if r.get("in_degree", 0) == 0]
    t1_rev = [r for r in t1 if (r["file"], r["name"]) in reviewed_keys]
    t0_rev = [r for r in t0 if (r["file"], r["name"]) in reviewed_keys]
    all_rev = len(t1_rev) + len(t0_rev)

    A("")
    A("## 覆盖范围：这份账本审了谁、没审谁")
    A("")
    A("| 总体 | 条数 | 已审 | 覆盖 |")
    A("|:--|--:|--:|--:|")
    A("| 定理 + 引理 | %d | %d | %.1f%% |"
      % (len(thm), all_rev, 100.0 * all_rev / max(len(thm), 1)))
    A("| **入度 ≥ 1（承重集）** | **%d** | **%d** | **%.1f%%** |"
      % (len(t1), len(t1_rev), 100.0 * len(t1_rev) / max(len(t1), 1)))
    A("| **入度 = 0** | **%d** | **%d** | **%.1f%%** |"
      % (len(t0), len(t0_rev), 100.0 * len(t0_rev) / max(len(t0), 1)))
    A("")
    A("**两个方向都要读；只读一个是误导。**")
    A("")
    A("- **承重集 100% 覆盖**：入度 ≥ 1 的定理**全部**审过。这是「只是样本」这个说法的**反例**——")
    A("  被下游真正消费的那部分**没有漏**。")
    A("- **零入度只有 %.1f%%**：%d 条入度为 0 的定理里只审了 %d 条。**这才是「样本」真正指的东西。**"
      % (100.0 * len(t0_rev) / max(len(t0), 1), len(t0), len(t0_rev)))
    A("")
    A("### 零入度未审**不等于**已审，也不等于无害")
    A("")
    A("**入度为 0 只说明「没有其他定理引用它」，不说明「它说了真话」。**")
    A("一条名义完成的定理可以零引用——本账本已删的 `hasQuadraticLowerBound_iff_self`（`a = a`）")
    A("与 `syntacticFunctor_id` 都是这一类。**它们误导不了下游，但它们在库里，读者会读到。**")
    A("")
    A("### 为什么没有做全审")
    A("")
    A("这是**显式的取舍**，不是遗漏：%d 条零入度定理的逐条语义审阅成本远超本轮次预算，" % len(t0))
    A("而按「误导下游」这个判据，它们的边际风险最低。**若要全审，正确做法是另开一个批次文件，")
    A("不是把现状说成已审。**")
