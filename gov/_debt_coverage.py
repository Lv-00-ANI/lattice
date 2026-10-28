"""Coverage reporting for PROOF-DEBT.md, kept in its own module.

## Why a separate file

Round 226 tried to inline this block into `gen_proof_debt.py` through a patch script, and the patch script
itself failed to parse because of nested quoting. **A patch script that carries a hundred lines of Chinese
prose inside a Python string literal is a bad idea** -- the quoting is fragile and the failure mode is silent
(the patch simply does not apply, and the generator keeps producing the old output).

## Round 27: the numbers now come from the measurement, not from the inventory

Before this round the table was computed from `inv`'s **stored** `in_degree`, which came from the review
inventory and was itself computed by a defective metric. The generator's own prose then said the load-bearing
set was **100%** covered while the table two lines above it said **78.2%**, and a caveat further down said the
set had been computed wrongly in the first place. **Three numbers, one quantity, no instrument.**

So `emit` now takes the dict produced by `check_coverage_claim.measure()` -- **the same function the gate
compares against**. Generator and gate cannot drift, because they share one measurement.

The definition is stated in that module: theorem+lemma only; code only (comments and docstrings stripped);
the citing file must `import` the defining module.
"""


def emit(A, cov):
    """Emit the coverage section from the measured dict `cov`."""
    total = cov["total"]
    load, load_a = cov["load"], cov["load_audited"]
    zero, zero_a = cov["zero"], cov["zero_audited"]
    missing = cov["unaudited_load_bearing"]

    def pc(a, b):
        return 100.0 * a / b if b else 0.0

    A("")
    A("## 覆盖范围：这份账本审了谁、没审谁")
    A("")
    A("**这张表的数字由 `gov/check_coverage_claim.py` 计算，并由同一个脚本作为门禁核对。**")
    A("生成器与门禁**共用同一个测量函数**，所以它们不可能互相漂。")
    A("")
    A("定义（三条都要满足才算「被引用」）：")
    A("")
    A("1. **只数定理与引理**——`def`/`structure` 没有可审的证明；")
    A("2. **只数代码**——剥掉注释与 docstring，散文里提到一个名字不算引用；")
    A("3. **引用方必须真的 `import` 定义所在模块**——另一个命名空间里的同名声明不算。")
    A("")
    A("| 总体 | 条数 | 已审 | 覆盖 |")
    A("|:--|--:|--:|--:|")
    A("| 定理 + 引理 | %d | %d | %.1f%% |" % (total, load_a + zero_a, pc(load_a + zero_a, total)))
    A("| **入度 ≥ 1（承重集）** | **%d** | **%d** | **%.1f%%** |" % (load, load_a, pc(load_a, load)))
    A("| **入度 = 0** | **%d** | **%d** | **%.1f%%** |" % (zero, zero_a, pc(zero_a, zero)))
    A("")
    A("**两个方向都要读；只读一个是误导。**")
    A("")
    A("- **承重集 %.1f%% 覆盖**：%d 条被下游真正消费的定理里审了 %d 条。"
      % (pc(load_a, load), load, load_a))
    A("  ⚠ **第 27 轮修正**：此前这里写的是「**100% 覆盖**」，而它上面的表格写的是 78.2%——")
    A("  **同一页三个数字**（表格 78.2%、正文 100%、更正段说集合算错、正确值是 839）。")
    A("  三个都来自**手写或过期的入度**，没有一个来自能复算的仪器。**现在只有一个数字，来自一个函数。**")
    A("- **零入度只有 %.1f%%**：%d 条入度为 0 的定理里审了 %d 条。**这才是「样本」真正指的东西。**"
      % (pc(zero_a, zero), zero, zero_a))
    A("")
    if missing:
        A("### 承重集里**尚未审阅**的 %d 条（逐条列出，不做汇总）" % len(missing))
        A("")
        A("**这是本轮唯一还没做到的百分之几。** 它们入度 ≥ 1、被下游引用、但还没有判定：")
        A("")
        for n in missing:
            A("- `%s`" % n)
        A("")
        A("**为什么列出来而不是抹平**：把这 %d 条补审之后，承重集才能真的说 100%%。" % len(missing))
        A("在此之前它说 **%.1f%%**，并且**说得出缺的是哪些**——这比一个漂亮的整数有用。"
          % pc(load_a, load))
        A("")
    else:
        A("### 承重集**已全部审阅**")
        A("")
        A("入度 ≥ 1 的定理全部有判定。这不是声称，是 `check_coverage_claim.py` 每次重新算出来的。")
        A("")
    A("### 零入度未审**不等于**已审，也不等于无害")
    A("")
    A("**入度为 0 只说明「没有其他定理引用它」，不说明「它说了真话」。**")
    A("一条名义完成的定理可以零引用——本账本已删的 `hasQuadraticLowerBound_iff_self`（`a = a`）")
    A("与 `syntacticFunctor_id` 都是这一类。**它们误导不了下游，但它们在库里，读者会读到。**")
    A("")
    A("### 零入度的抽样协议（第 27 轮写下）")
    A("")
    A("**%d 条零入度定理不逐条语义审阅，这是显式取舍，不是遗漏。**" % zero)
    A("")
    A("**抽样的依据**：过去的审阅按「旧的有缺陷的入度」选第一层，因此其中约三百多条")
    A("实际入度为 0——**它们不是为「零入度」抽的样，而是为「高价值」抽的样，事后发现落在零入度里。**")
    A("所以这个 %d 条样本**不是随机抽样**，**偏向「曾经看起来重要」的那一侧**，" % zero_a)
    A("这对零入度集合是**有偏**的（偏向复杂的、被写进 docstring 的、跨文件重名的）。")
    A("")
    A("**边界，写成可核对的断言**：")
    A("")
    A("1. **不声称零入度集合已审**——覆盖率就是上表那个数字；")
    A("2. **不声称它不需要审**——`a = a` 这类重言正是零引用也能存在的；")
    A("3. **不按「误导下游」给零入度排序**：它们不误导下游，**它们误导读者**——")
    A("   而读者的检索路径不可形式化，所以**这里没有可证的优先级**，只有一条明说的取舍。")
    A("")
    A("**若要全审**：正确做法是另开批次文件（`agent-tmp/review/batch_*.jsonl` 现有格式已支持），")
    A("**不是把现状说成已审**。")
