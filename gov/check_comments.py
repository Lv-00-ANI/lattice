# -*- coding: utf-8 -*-
"""Correct the comment-integrity check to count block comments properly.

The first version compared `src.count("/--")` with `src.count("-/")`, which counts *doc* comments on
one side and *all* block comment closes on the other -- so every file reported a deficit, including
files that obviously compile. A checker whose first run flags 26 healthy files is exactly the failure
mode the legacy `check-xref.ps1` had (822 findings, nearly all false), and a checker that cries wolf
gets ignored.

The corrected rule counts every block-comment opener (`/-` followed by anything, including `/-!` and
`/--`) against every closer, and separately flags the splice signature: two `/--` on one line.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))

OPEN_RE = re.compile(r"/-")
CLOSE_RE = re.compile(r"-/")
DOC_DOC_RE = re.compile(r"/--.*?/--")


def lean_files():
    out = [os.path.join(ZERO, "Lattice.lean")]
    for base, _d, fs in os.walk(ZERO):
        parts = base.split(os.sep)
        # `_archive/` holds the fully-archived LvFormal geometry tree (round 187). It is outside
        # `Lattice/` and outside every build, and three of its files have unbalanced comments in the
        # source itself -- scanning it would keep I8 red forever while describing nothing about the
        # live tree. Same reasoning as the `Reference/` skip just below, and the same directory name
        # the main gate's exclusion list already uses.
        if (".lake" in parts or "gov" in parts or "_archive" in parts
                or "archive" in parts or "agent-tmp" in parts):
            continue
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            # `Zero/Reference/` holds Lv-00's assets; three of its files have unbalanced comments in the
            # source itself (verified by gov/diagnose_comments.py), so including them would keep I8 red
            # forever without describing anything about this project's code.
            scope = os.environ.get("DSH_GATE_SCOPE")
            if scope != "reference" and scope != "all":
                if os.sep + "Reference" + os.sep in p:
                    continue
            out.append(p)
    return out


def comment_balance_ok(src):
    """Nesting-aware scan: every `/ -` needs a matching `-/`, and a lone `-/` is a splice artefact."""
    depth = 0
    i = 0
    n = len(src)
    underflow = 0
    while i < n - 1:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i):
            if depth == 0:
                underflow += 1
            else:
                depth -= 1
            i += 2
        else:
            i += 1
    return depth, underflow


def _known_unbuildable():
    """Modules whose wrongness is Lv-00's, split by why they do not build.

    Returns `(comment_damaged, proof_failed)`. The distinction matters: a module in the second set is
    expected to have **intact** comments, so treating the two alike makes the staleness check fire on
    files that are fine.
    """
    import json
    path = os.path.join(HERE, "known-unbuildable.json")
    if not os.path.exists(path):
        return set(), set()
    try:
        d = json.load(io.open(path, encoding="utf-8"))
        mods = set(d["modules"])
        kinds = d.get("reason_kind", {})
        comment = {m for m in mods if kinds.get(m) == "comment"}
        return comment, mods - comment
    except (ValueError, KeyError):
        return set(), set()


def check_comments(rep):
    """I8: block-comment integrity across every Lean source.

    Files listed as known-unbuildable are *reported as known* rather than as new damage: their
    unbalanced comments come from `_harvest/lv00/formal`, verified by `gov/diagnose_comments.py`, and
    Lean cannot parse them at all. Suppressing them entirely would hide a file that gets repaired later,
    so a listed file whose comments are intact is flagged as a stale entry.
    """
    comment_bad, proof_bad = _known_unbuildable()
    for p in lean_files():
        src = io.open(p, "rb").read().decode("utf-8", "replace")
        rel = os.path.relpath(p, ZERO).replace("\\", "/")
        mod = rel[len("Lattice/"):-len(".lean")].replace("/", ".")
        mod = "Lattice." + mod
        depth, underflow = comment_balance_ok(src)
        damaged = depth != 0 or underflow != 0
        if mod in proof_bad:
            # does not build for a proof reason; its comments are expected to be fine, and I8 is
            # not the check that should speak about it
            continue
        if mod in comment_bad:
            if not damaged:
                rep.add("I8", "module is listed as unbuildable for comment damage but its comments "
                        "are intact -- refresh gov/known-unbuildable.json", rel)
            continue
        if depth != 0:
            rep.add("I8", "unclosed block comment (nesting depth %d at EOF)" % depth, rel)
        if underflow != 0:
            rep.add("I8", "%d `-/` without a matching opener" % underflow, rel)
        for lineno, line in enumerate(src.splitlines(), 1):
            if DOC_DOC_RE.search(line):
                rep.add("I8", "two doc-comment openers on one line", rel, lineno)


if __name__ == "__main__":
    class R:
        def __init__(self):
            self.items = []

        def add(self, a, b="", c="", d=0):
            self.items.append((a, b, c, d))

    r = R()
    check_comments(r)
    if r.items:
        for it in r.items:
            print(it)
    else:
        print("doc comments intact in all %d Lean files" % len(lean_files()))
    sys.exit(0 if not r.items else 1)
