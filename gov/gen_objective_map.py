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
    # Round 1091: these two were NOT dead by the old count -- `Usage/Examples.lean` mentions them, and an
    # example IS a cross-file reference. They are dead by the STRONGER count introduced this round, which
    # excludes `Usage/`: the data-synthesis clause has no consumer inside LATTICE at all.
    "covered_of_vanishing":
        "clause 2.2's covering statement, about a data function the CALLER supplies. Nothing in the tree "
        "consumes that hypothesis: there is no training step and no downstream verdict that needs "
        "`covered`. The consumer lives OUTSIDE by positioning (LATTICE does not implement a training "
        "framework), not by oversight.",
    "models_of_covered_data":
        "clause 2.2's model statement. Its first conjunct is `rfl` and its second is the covering above, so "
        "it is the same situation: proved, and consumed only outside the project.",
    # Round 1092: the four below are dead by the CHAIN count (round 1091's column), and each reason was
    # written after reading the statement AND its proof shape -- not inferred from the name.
    "closed_loop_partial_reinject":
        "one-step unfolding: `g (V.run 1 x) = g (V.repair.fix x)`, proved by `iterate_succ` then `rfl`. "
        "A caller that needs it unfolds `run` itself, so there is nothing for it to feed.",
    "loop_is_criterion_not_repair":
        "an idempotence statement: `compile (extract (compile (extract ls))) = ls`. A property of the pair of "
        "steps, not a step -- no downstream verdict consumes idempotence.",
    "hasType_to_hasTypeW":
        "clause 5's bridge: `HasType K Gamma t A -> HasTypeW E K Gamma t A`, i.e. CIC typing implies the "
        "weight-tagged typing. Consumed by callers that reason inside the CIC; no in-tree step uses it, which "
        "is why the example is its only citation.",
    "sqDistHalving_terminates_and_stabilises":
        "termination plus stability of the DEMONSTRATION instance on `Nat` (`exists k, Sat (iterate k n) and "
        "the fixpoint is stable`). It is that instance's endpoint, not a step of the chain.",
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
    clause_of = {}
    for clause, names in CLAUSES.items():
        cells = []
        for name in names:
            where = None
            for rel, src in sorted(C.items()):
                if rel.startswith("Reference/"):
                    continue
                m = DECL.search(src)
                # **Round 1023: this pattern was TOO NARROW and produced eight false "not found"
                # entries -- including every carrier of clause 3.3 (repair), clause 3.4 (re-injection)
                # and clause 5 (the symbolic engine), i.e. two steps the objective names explicitly.
                # The names all exist in the tree; they are written with attributes (`@[simp]`), with
                # `lemma`, or with modifiers in an order the old alternation rejected.
                # **`check_objective_coverage.py` had been passing the whole time, and that
                # disagreement is what exposed this: the weak reader and the strong reader disagreed,
                # and the WEAK one was right.**
                if re.search(
                        r"(?m)^\s*(?:@\[[^\]]*\]\s*)*"
                        r"(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
                        r"(?:def|theorem|lemma|abbrev|structure|inductive)\s+%s\b"
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
            # **Round 1091: an EXAMPLE is not a consumer.** `Usage/Examples.lean` is a demonstration, so a
            # carrier mentioned only there is unreachable from the chain even though the cross-file count is
            # positive. Measuring the two counts separately distinguishes "used by the chain" from "shown in
            # an example" -- and rounds 1080/1090 measured forward carriers at 17 real consumers while clause
            # 2.2's two carriers had NONE, with the old table reporting both the same way.
            real = [u for u in users if not u.startswith("Usage/")]
            cells.append((name, where, len(users), len(real), local, users[:2]))
            clause_of[name] = clause
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
    lines.append("| 条款 | 载体 | 定义于 | 跨文件 | 链内 | 同文件 | 例 |")
    lines.append("|:--|:--|:--|--:|--:|--:|:--|")
    weak = 0
    localonly = 0
    dead_names = []
    chainless = []
    for clause, cells in rows:
        for name, where, n, nreal, local, examples in cells:
            if where is None:
                lines.append("| %s | `%s` | **未找到** | — | — | — | — |" % (clause, name))
                weak += 1
                continue
            ex = ", ".join("`%s`" % e for e in examples) if examples else "—"
            # **Round 1092: the flag must be driven by the CHAIN count, not the cross-file count.** A carrier
            # whose only other-file references is `Usage/Examples.lean` is used in place, and calling that
            # "used" hid six carriers last round. The flag now says what the measurement says:
            #   chain > 0            -> used by the chain
            #   chain = 0, local > 0 -> used only inside its own file  (measured, not judged)
            #   chain = 0, local = 0 -> dead; must be registered in END_OF_CHAIN with a reason
            if nreal > 0:
                flag = ""
            elif local > 0:
                flag = " *(仅本文件)*"
                localonly += 1
            else:
                flag = " **← 死代码**"
                weak += 1
                dead_names.append(name)
            # Only DEAD-but-unexplained is an error: `local > 0` means the carrier is used inside its own
            # file, which is a measurement, not a defect. **Round 1092: the first version of this line
            # listed all chain-less carriers and thereby mislabelled two local-only ones as unexplained.**
            if nreal == 0 and local == 0 and name not in END_OF_CHAIN:
                chainless.append(name)
            lines.append("| %s | `%s` | `%s` | %d%s | %d | %d | %s |"
                         % (clause, name, where, n, flag, nreal, local, ex))
    lines.append("")
    lines.append("## 汇总")
    lines.append("")
    total = sum(len(c) for _, c in rows)
    lines.append("- 条款数：%d" % len(rows))
    lines.append("- 载体总数：%d" % total)
    lines.append("- **死代码载体（同文件也不用）：%d**" % weak)
    lines.append("- 仅同文件使用的载体：%d" % localonly)
    nrealzero = sum(1 for _, cells in rows for name, where, n, nreal, local, ex in cells
                    if where is not None and nreal == 0)
    lines.append("- **链内消费者为 0 的载体：%d**（`Usage/` 不计为消费者）" % nrealzero)
    if chainless:
        lines.append("- **未登记理由的零链内消费者：%d（`%s`）**" % (len(chainless), "`, `".join(chainless)))
    lines.append("")
    lines.append("「仅同文件使用」不等于无价值：一个框架的示例实例本来就没有外部调用者。")
    lines.append("**「死代码」才是问题**——连它自己所在的文件都不用它。")
    lines.append("")
    # **Round 1035: this heading used to be the hard-coded words "三条", printed even when the count was
    # 0 or 1 -- a doc that states a number it did not measure. It is now conditional on `weak`.**
    if weak:
        lines.append("### %d 条死代码载体的性质：terminal by design，不是遗漏" % weak)
    lines.append("")
    lines.append("按上面这个更强的判据（**剥离注释**后计数），本期实测为 %d 条。" % weak)
    lines.append("每一条都**有真实内容**，是各自条款的**终端结论**——它们的职责是「这条条款成立」，")
    lines.append("而不是「被别人调用」。**一条链的最后一环没有下游，这是链的性质，不是缺陷。**")
    lines.append("")
    lines.append("下表的每一行都来自 `END_OF_CHAIN`，**理由是在读过陈述与证明形状之后写的**，"
                 "并逐条注明它是「展开」「幂等」「包含」还是「实例端点」。")
    lines.append("")
    lines.append("| 载体 | 条款 | 它是什么 | 为什么没有下游 |")
    lines.append("|:--|:--|:--|:--|")
    # **Round 1092: render only the carriers the MEASUREMENT called dead.** Rendering all of END_OF_CHAIN while
    # the heading states `dead=4` produced a seven-row table under a "4 条" heading -- a doc claiming a number it
    # did not measure, which is the exact defect the comment above this section warns about.
    for nm in sorted(END_OF_CHAIN):
        if nm in clause_of and nm in dead_names:
            lines.append("| `%s` | %s | %s |" % (nm, clause_of[nm], END_OF_CHAIN[nm]))
    lines.append("")
    lines.append("**审计 P1-17 要求「加外部使用者，或标 terminal by design」**——本节选后者，")
    lines.append("并对每一条给出理由。**这不是把死代码说成活的**：`死代码载体：%d` 这个数字仍然如实报告，" % weak)
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
