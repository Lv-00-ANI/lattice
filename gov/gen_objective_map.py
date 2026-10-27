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


def corpus():
    out = {}
    for dirpath, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            out[rel] = io.open(p, "rb").read().decode("utf-8", errors="replace")
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

    return "\n".join(lines) + "\n", weak, localonly


def main(argv):
    C = corpus()
    text, weak, localonly = render(C)
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
    return 0 if weak == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
