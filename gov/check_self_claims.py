#!/usr/bin/env python
"""check_self_claims.py -- a file that says "this file carries no declarations" must actually carry none.

**Why this exists.** `Primitives/TokenizeStrategy.lean` began with "本文是一个只含注释的 Lean 文件：它不含任何声明"
and then, several rounds later, gained five probe theorems. The sentence stayed. No existing checker could see it:
`check_doc_names` asks whether cited NAMES exist, `audit_docs` compares doc tables to the tree -- but a claim about
the file ITSELF going stale is invisible to both, because there is nothing to look up.

**Scope matters, and this tool learned that the hard way.** The first version matched any occurrence of
"没有任何声明" in the first 40 lines. It flagged `Lib/LearningTheory/RealRecoverEndpoint.lean:21`, whose text reads
"全库 `def recover` 0 命中" -- a HISTORICAL statement about the library, immediately followed by "本文件补上
recover ...". That is not a self-description and must not be "fixed". So the pattern requires self-reference
(本文 / 本文件 / this file) in the SAME line, and only then asks the tree whether it is true.

**What it checks.** For every Lean file, the first 40 lines are scanned for a self-referential claim of the form
"this file contains no declarations". If found, the file is counted; if the file also declares something, that is a
violation.

Usage:
    python check_self_claims.py             # report
    python check_self_claims.py --check     # exit 1 on any violation
"""

import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LAT = os.path.join(ROOT, "Lattice")

#: self-reference AND the "no declarations" claim, in one line
SELF = r"(?:\u672c\u6587|\u672c\u6587\u4ef6|this file)"
CLAIM = r"(?:\u53ea\u542b\u6ce8\u91ca|\u4e0d\u542b\u4efb\u4f55\u58f0\u660e|\u6ca1\u6709\u4efb\u4f55\u58f0\u660e|contains no declarations)"
PATTERN = re.compile(SELF + r".{0,40}" + CLAIM + r"|" + CLAIM + r".{0,40}" + SELF)

DECL = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|inductive|class|instance)\s+\w+"
)


def main(argv):
    claimed, bad = 0, []
    for root, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace(os.sep, "/")
            src = io.open(p, "rb").read().decode("utf-8", errors="replace")
            head = "\n".join(src.split("\n")[:40])
            m = PATTERN.search(head)
            if not m:
                continue
            claimed += 1
            n = len(DECL.findall(src))
            if n:
                bad.append((rel, n, m.group(0)[:60]))

    # **Round 1157: a second class of self-claim, also mechanically checkable.**
    # A docstring that records a MERGE -- "`X.lean` 已并入本文件" -- asserts that X no longer exists. That is a fact
    # about the tree, so it can go stale exactly the way the "pure commentary" sentence did.
    MERGE = re.compile(r"`([\w/]+\.lean)`\s*\u5df2\u5e76\u5165\u672c\u6587\u4ef6")
    merge_claims, merge_bad = 0, []
    for root, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace(os.sep, "/")
            src = io.open(p, "rb").read().decode("utf-8", errors="replace")
            for m in MERGE.finditer(src):
                merge_claims += 1
                gone = m.group(1)
                # The claim usually names a BARE filename, not a path -- so existence means "somewhere in the tree",
                # not "at this joined path". Checking the join first made the test below pass while the claim was
                # false, which is why the injected case was counted but not flagged.
                base = os.path.basename(gone)
                exists = os.path.exists(os.path.join(LAT, gone)) or os.path.exists(os.path.join(ROOT, gone))
                if not exists:
                    for r2, _, f2 in os.walk(LAT):
                        if base in f2:
                            exists = True
                            break
                if exists:
                    merge_bad.append((rel, gone))

    print("  files that claim to carry no declarations : %d" % claimed)
    for rel, n, line in bad:
        print("      VIOLATION %-52s declares %d   (%s)" % (rel, n, line))
    print("  violations                                : %d" % len(bad))
    print("  merge claims ('X.lean 已并入本文件')        : %d" % merge_claims)
    for rel, gone in merge_bad:
        print("      STALE MERGE %-50s says %s is merged, but it exists" % (rel, gone))
    print("  stale merge claims                        : %d" % len(merge_bad))
    if (bad or merge_bad) and "--check" in argv:
        print("SELF CLAIMS: %d false declaration claim(s), %d stale merge claim(s)"
              % (len(bad), len(merge_bad)))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))