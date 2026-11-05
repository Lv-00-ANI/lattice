#!/usr/bin/env python
"""gov/check_carrier_claims.py -- `ARCHITECTURE-CARRIERS.md` must not claim what the tree lacks.

WHY THIS EXISTS

    Round 125 found `ARCHITECTURE-CARRIERS.md` listing `Conv`, `Attention` and `DAG` beside `Norm`, with a
    directory block and per-carrier proof names -- while only `Norm` and `GNN` existed on disk, and none of
    the listed proof names could be found.

    That is the M5 failure mode of the `incomplete-implementation` taxonomy: a document that says
    "implemented" where the tree says otherwise. It is a CORRECTNESS problem, not a cosmetic one, because a
    later round plans against the document.

    A one-off correction decays. This check makes the claim machine-verifiable: every directory the document
    marks `-- 已实现` must exist, and every directory it marks `-- 未实现` must NOT exist.

WHAT IT CHECKS

    1. Each line of the directory block that carries a `-- 已实现` marker names an existing directory.
    2. Each line carrying `-- 未实现` names a directory that does NOT exist.
    3. A directory that exists but appears in NO line is reported -- the document is silent about a real
       carrier, which is the same defect from the other side.

WHAT IT DOES NOT CHECK

    It does not verify the PROOF NAMES the document lists. Those move between files, and a name check would
    produce churn without catching the failure that matters (claiming a whole carrier that is absent).
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
DOC = os.path.join(REPO, "ARCHITECTURE-CARRIERS.md")
ARCH = os.path.join(REPO, "Lattice", "Plugins", "Architectures")

#: `已建` (possibly with a parenthetical caveat) means the directory must exist.
DONE = "已建"
#: `未建` means it must not.
TODO = "未建"

#: `-- 已建（...）` and `-- 未建` are both matched; the parenthetical is the doc's own caveat and is kept
#: out of `status` so the comparison stays exact.
LINE = re.compile(r"^\s*Lattice/Plugins/Architectures/(\w+)/\s*--\s*(\S+?)(?:\uff08.*\uff09)?\s*$")


def parse():
    text = io.open(DOC, encoding="utf-8").read()
    rows = []
    for ln in text.split("\n"):
        m = LINE.match(ln)
        if m:
            rows.append((m.group(1), m.group(2)))
    return rows


def on_disk():
    if not os.path.isdir(ARCH):
        return set()
    return {d for d in os.listdir(ARCH) if os.path.isdir(os.path.join(ARCH, d))}


def main():
    rows = parse()
    if not rows:
        print("CARRIER CLAIMS: no parseable directory block in ARCHITECTURE-CARRIERS.md")
        return 1

    disk = on_disk()
    problems = []

    for name, status in rows:
        exists = name in disk
        if status == DONE and not exists:
            problems.append("%s: document says %s, directory is MISSING" % (name, DONE))
        elif status == TODO and exists:
            problems.append("%s: document says %s, directory EXISTS -- promote it" % (name, TODO))
        elif status not in (DONE, TODO):
            problems.append("%s: unparseable status %r" % (name, status))

    claimed = {name for name, _ in rows}
    for name in sorted(disk - claimed):
        problems.append("%s: exists on disk but the document is SILENT about it" % name)

    for p in problems:
        print("  " + p)

    print("CARRIER CLAIMS: %s" % ("consistent with the tree" if not problems
                                  else "%d problem(s)" % len(problems)))
    return 0 if not problems else 1


def _self_test():
    """Prove the three failure modes are DETECTED, not merely described.

    The gate's job is to fail when the document and the tree disagree. A checker that cannot demonstrate
    that is a checker that could silently pass forever -- which is exactly the round-125 defect one level up.

    The fixtures live under the repository's own `agent-tmp/`, not under the system temp directory: the
    sandbox denies writes there, and a self-test that cannot create its fixture cannot fail either.
    """
    import shutil

    root = os.path.join(REPO, "agent-tmp", "_carrier_selftest")

    def run(doc_text, dirs):
        if os.path.isdir(root):
            shutil.rmtree(root)
        arch = os.path.join(root, "Lattice", "Plugins", "Architectures")
        os.makedirs(arch)
        for d in dirs:
            os.makedirs(os.path.join(arch, d))
        doc = os.path.join(root, "ARCHITECTURE-CARRIERS.md")
        io.open(doc, "w", encoding="utf-8").write(doc_text)
        global DOC, ARCH
        old = (DOC, ARCH)
        DOC, ARCH = doc, arch
        try:
            return main()
        finally:
            DOC, ARCH = old

    doc = ("```text\n"
           "Lattice/Plugins/Architectures/A/  -- 已建\n"
           "Lattice/Plugins/Architectures/B/  -- 未建\n"
           "```\n")

    cases = [
        ("consistent", doc, ["A"], 0),
        ("claims a missing carrier", doc, [], 1),
        ("a carrier claims to be absent but exists", doc, ["A", "B"], 1),
        ("a carrier on disk is unmentioned", doc, ["A", "C"], 1),
    ]

    ok = True
    try:
        for name, text, dirs, want in cases:
            got = run(text, dirs)
            if got != want:
                print("  SELF-TEST FAIL: %s -- expected %d, got %d" % (name, want, got))
                ok = False
    finally:
        if os.path.isdir(root):
            shutil.rmtree(root, ignore_errors=True)

    print("CARRIER CLAIMS SELF-TEST: %s" % ("all four cases behave" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(_self_test())
    sys.exit(main())
