# -*- coding: utf-8 -*-
"""任务 B：Legacy 定理密度统计（只读）。

口径：
  * 文件集：`gov/legacy_isolation_set.json` 的 `keep_final`（437 个保留目标）
  * 定理计数：用 `gov/tools/sorry_axiom_census.py` 的 `strip_comments` 剥离注释后，
    匹配行首的 `theorem` / `lemma` 声明
  * 同时统计 `def`/`structure`/`inductive`/`instance` 作为「其他声明」
  * 能编译：`.lake/build/lib/Zero/Legacy/<name>.olean` 是否存在
"""
import io
import json
import os
import re
import sys
from collections import Counter

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEG = os.path.join(ZERO, "Lattice", "Legacy")
LIB = os.path.join(ZERO, ".lake", "build", "lib", "Lattice", "Legacy")
PLAN = os.path.join(ZERO, "gov", "legacy_isolation_set.json")
OUT = os.path.join(ZERO, "gov", "legacy_density.json")

sys.path.insert(0, os.path.join(ZERO, "gov", "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

THM = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+)*(theorem|lemma)\s+", re.M)
OTHER = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+)*"
                   r"(def|abbrev|structure|inductive|instance|class)\s+", re.M)


def main():
    plan = json.loads(io.open(PLAN, encoding="utf-8").read())
    keep = [k for k in plan["keep_final"] if re.match(r"^[A-Za-z][A-Za-z0-9_]*$", k)]

    rows = []
    for k in keep:
        p = os.path.join(LEG, k + ".lean")
        raw = io.open(p, "rb").read().decode("utf-8", "replace")
        s = strip_comments(raw)
        rows.append({
            "file": k,
            "lines": len(raw.splitlines()),
            "theorems": len(THM.findall(s)),
            "others": len(OTHER.findall(s)),
            "built": os.path.exists(os.path.join(LIB, k + ".olean")),
        })

    t = [r["theorems"] for r in rows]
    print("=" * 68)
    print("Legacy 定理密度（%d 个保留目标）" % len(rows))
    print("=" * 68)
    print("总文件数        :", len(rows))
    print("总行数          :", sum(r["lines"] for r in rows))
    print("定理总数        :", sum(t))
    print("其他声明总数    :", sum(r["others"] for r in rows))
    print("已编译          :", sum(1 for r in rows if r["built"]))
    print()

    print("--- 定理数分布 ---")
    buckets = [("0", lambda n: n == 0),
               ("1-5", lambda n: 1 <= n <= 5),
               ("6-20", lambda n: 6 <= n <= 20),
               ("21-50", lambda n: 21 <= n <= 50),
               ("50+", lambda n: n > 50)]
    for label, f in buckets:
        c = sum(1 for n in t if f(n))
        print("   %-6s %4d 个文件  (%5.1f%%)" % (label, c, 100.0 * c / len(rows)))

    zero = [r for r in rows if r["theorems"] == 0]
    print()
    print("--- 定理数为 0 的文件（%d 个，全列）---" % len(zero))
    for r in sorted(zero, key=lambda x: -x["lines"]):
        kind = "空文件" if r["others"] == 0 else "仅 %d 个定义" % r["others"]
        print("   %-44s %5d 行  %-14s built=%s" % (r["file"], r["lines"], kind, r["built"]))

    print()
    print("--- 定理最多的 5 个文件 ---")
    for r in sorted(rows, key=lambda x: -x["theorems"])[:5]:
        print("   %-44s %4d 定理  %5d 行" % (r["file"], r["theorems"], r["lines"]))

    io.open(OUT, "w", encoding="utf-8", newline="\n").write(
        json.dumps(rows, ensure_ascii=False, indent=1))
    print()
    print("明细写出:", OUT)


if __name__ == "__main__":
    main()
