"""gen_objective_map.py -- the objective's 14 clauses, each with its carrier located and counted.

The objective is a paragraph, not a checklist, but it decomposes into 14 claims
(check_objective_coverage.CLAUSES already records that decomposition for its rule A). Rule A only
asks "does a declaration with this name exist". That is the weakest possible reading, and rounds
102-107 showed exactly why it is not enough: a name can exist, compile, be correct, and still be
reachable from nothing.

This generates the stronger table: for every clause, every carrier, WHERE it is defined and HOW MANY
places reference it. A carrier with zero external references is a name, not a delivery.

Output goes to OBJECTIVE-MAP.md. Regenerating it is the point -- a static table rots, and the
doc-consistency checks cannot see prose that has quietly become false.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.abspath(os.path.join(HERE, "..", "Lattice"))
OUT = os.path.abspath(os.path.join(HERE, "..", "OBJECTIVE-MAP.md"))

sys.path.insert(0, HERE)
from check_objective_coverage import CLAUSES  # noqa: E402

DECL = re.compile(r"(?m)^(?:noncomputable\s+)?(?:private\s+)?(?:def|theorem|abbrev|structure|inductive)\s+(\w+)")


#: Carriers with no consumer BY DESIGN, each with the reason. A carrier listed here is the END of its
#: clause's chain: it states the clause, so nothing downstream consumes it. A carrier that is dead and
#: NOT listed here fails the generator -- that is the "written and forgotten" case.
#:
#: Round 178, P2-9. Before this round the counts were taken from RAW source, so a name mentioned only in
#: a docstring counted as used, and the table reported `dead=0`. With comments stripped the true number
#: is 3 -- and all three are end-of-chain, which is why the number being wrong never showed up as a
#: broken build.
END_OF_CHAIN = {
    "synth_coverage":
        "clause 2.2's conclusion: k synthetic samples are pairwise separated. There is no stronger "
        "statement above it for it to feed.",
    "compile_sound_n":
        "clause 2.3's endpoint: `compileToLayerN s` maps zero to zero when every residual vanishes. "
        "The branch that consumes compilation downstream goes through `weightLadderN.l2l3_sound`.",
    "partial_reinject_bound":
        "clause 3.4's translation step: residual bound -> loss bound. It translates and stops.",
}
def corpus():
    """Comments are STRIPPED here, once, for both the cross-file and the same-file count.

    Round 178, P2-9. Before this, the counts were taken from raw source, so a carrier whose name is
    only mentioned in a docstring -- "see `penaltyToLoss` below" -- was counted as USED. That is the
    exact defect this file exists to report: round 102-107 established that a name can exist, compile
    and be correct while being unreachable, and a docstring mention is the mildest possible form of
    "something refers to it".

    Stripping once in the corpus (rather than per lookup) also guarantees the two counts cannot
    disagree about what counts as a reference.
    """
    from tools.sorry_axiom_census import strip_comments
    out = {}
    for dirpath, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            raw = io.open(p, "rb").read().decode("utf-8", errors="replace")
            out[rel] = strip_comments(raw)
    return out


def render(C):
    """Build the document text; separated so --check can compare without writing."""
    rows = []
    for clause, names in CLAUSES.items():
        cells = []
        for name in names:
            where = None
            for rel, src in sorted(C.items()):
                if rel.startswith("Reference/"):
                    continue
                m = DECL.search(src)
                if re.search(r"(?m)^(?:noncomputable\s+)?(?:private\s+)?(?:def|theorem|abbrev|structure|inductive)\s+%s\b"
                             % re.escape(name), src):
                    where = rel
                    break
            # users: files (other than the definer's) that mention the name
            users = [rel for rel, src in C.items()
                     if rel != where and not rel.startswith("Reference/")
                     and re.search(r"\b%s\b" % re.escape(name), src)]
            # Same-file mentions are not nothing: a carrier used four theorems down its own file is
            # used, just locally. Counting only cross-file references conflated "unused" with
            # "used in place", and the first run of this script reported `penaltyToLoss` as dead
            # when its own file spends four theorems on it.
            local = 0
            if where is not None:
                src = C.get(where, "")
                local = len(re.findall(r"\b%s\b" % re.escape(name), src)) - 1
            cells.append((name, where, len(users), local, users[:2]))
        rows.append((clause, cells))

    lines = []
    lines.append("# 目标条款 → 载体 → 位置 → 使用者")
    lines.append("")
    lines.append("**本文件由 `gov/gen_objective_map.py` 生成，勿手改。**")
    lines.append("")
    lines.append("目标是一段话，不是一个清单。`check_objective_coverage.py` 把它的 14 个断言")
    lines.append("（`CLAUSES`）作为规则 A 的依据——**但规则 A 只问「有这个名字吗」，那是最弱的读法**。")
    lines.append("第 102–107 轮反复证明：一个名字可以存在、可以编译、可以正确，**却从任何地方都不可达**。")
    lines.append("")
    lines.append("所以本表记录更强的东西：**每个载体的定义位置，以及有多少处引用它**。")
    lines.append("**外部引用数为 0 的载体是一个名字，不是一次交付。**")
    lines.append("")
    lines.append("| 条款 | 载体 | 定义于 | 跨文件 | 同文件 | 例 |")
    lines.append("|:--|:--|:--|--:|--:|:--|")
    weak = 0
    localonly = 0
    dead_names = []
    for clause, cells in rows:
        for name, where, n, local, examples in cells:
            if where is None:
                lines.append("| %s | `%s` | **未找到** | — | — | — |" % (clause, name))
                weak += 1
                continue
            ex = ", ".join("`%s`" % e for e in examples) if examples else "—"
            if n > 0:
                flag = ""
            elif local > 0:
                flag = " *(仅本文件)*"
                localonly += 1
            else:
                flag = " **← 死代码**"
                weak += 1
                dead_names.append(name)
            lines.append("| %s | `%s` | `%s` | %d%s | %d | %s |"
                         % (clause, name, where, n, flag, local, ex))
    lines.append("")
    lines.append("## 汇总")
    lines.append("")
    total = sum(len(c) for _, c in rows)
    lines.append("- 条款数：%d" % len(rows))
    lines.append("- 载体总数：%d" % total)
    lines.append("- **死代码载体（同文件也不用）：%d**" % weak)
    lines.append("- 仅同文件使用的载体：%d" % localonly)
    lines.append("")
    lines.append("「仅同文件使用」不等于无价值：一个框架的示例实例本来就没有外部调用者。")
    lines.append("**「死代码」才是问题**——连它自己所在的文件都不用它。")
    lines.append("")
    lines.append("### 三条死代码载体的性质：terminal by design，不是遗漏")
    lines.append("")
    lines.append("按上面这个更强的判据（**剥离注释**后计数），原先报「0 死代码」，实际有 3 条。")
    lines.append("三条都**有真实内容**，是各自条款的**终端结论**——它们的职责是「这条条款成立」，")
    lines.append("而不是「被别人调用」。**一条链的最后一环没有下游，这是链的性质，不是缺陷。**")
    lines.append("")
    lines.append("| 载体 | 条款 | 它是什么 | 为什么没有下游 |")
    lines.append("|:--|:--|:--|:--|")
    lines.append("| `synth_coverage` | 2.2 数据合成 | "
                 "「合成 k 个样本 ⟹ k 个样本两两分离」的不等式 | "
                 "覆盖率**就是**这条条款要的东西；再往上没有更强的结论 |")
    lines.append("| `compile_sound_n` | 2.3 结构化初始化 | "
                 "`compileToLayerN s` 在零点映零点（`resid = 0` 时） | "
                 "它是编译正确性的**端点**；下游是 `weightLadderN` 的 `l2l3_sound`，"
                 "走的是另一条路 |")
    lines.append("| `partial_reinject_bound` | 3.4 再注入 | "
                 "`|poly| ≤ ε ⟹ loss ≤ ε²` | "
                 "它把残差界翻译成损失界，**翻译完就结束了** |")
    lines.append("")
    lines.append("**审计 P1-17 要求「加外部使用者，或标 terminal by design」**——本节选后者，")
    lines.append("并对每一条给出理由。**这不是把死代码说成活的**：`死代码载体：3` 这个数字仍然如实报告，")
    lines.append("分类只是说明「死」在这里的含义是「链的末端」，而不是「写完忘了用」。")
    lines.append("")
    lines.append("**如果将来其中一条真的该被使用**，做法是给它加一个消费者，那时数字会变成 2、1、0，")
    lines.append("而这个表格会随之需要修正——**这正是把它写进生成文档而不是写进散文的原因**。")

    return "\n".join(lines) + "\n", weak, localonly, dead_names


def main(argv):
    C = corpus()
    text, weak, localonly, dead_names = render(C)
    if "--check" in argv:
        # does the committed file still match the tree?
        if not os.path.exists(OUT):
            print("OBJECTIVE-MAP: missing")
            return 1
        old = io.open(OUT, encoding="utf-8").read()
        if old != text:
            print("OBJECTIVE-MAP: STALE -- regenerate with gov/gen_objective_map.py")
            return 1
        print("OBJECTIVE-MAP: up to date")
        return 0
    io.open(OUT, "w", encoding="utf-8", newline="\n").write(text)
    print("wrote", OUT)
    # `carriers` was a literal 0 in this format string while the document listed 27. A generator that
    # misreports its own output is the same shape as a guard that reads its own constant: the summary
    # line and the table could disagree and nothing compared them.
    carriers = sum(len(v) for v in CLAUSES.values())
    print("clauses=%d carriers=%d dead=%d localonly=%d"
          % (len(CLAUSES), carriers, weak, localonly))
    # Round 178: "dead" is not automatically a failure any more. A END-OF-CHAIN carrier has no
    # downstream because it IS the clause's conclusion -- that is a property of the chain, not a defect.
    # What must fail is a carrier that is neither used NOR explained: an unexplained dead carrier is
    # exactly the "written and forgotten" case this table exists to catch.
    unexplained = sorted(set(dead_names) - set(END_OF_CHAIN))
    if unexplained:
        print("DEAD CARRIERS WITH NO EXPLANATION: %s" % unexplained)
        print("Either give each one a consumer, or add it to END_OF_CHAIN with the reason.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
