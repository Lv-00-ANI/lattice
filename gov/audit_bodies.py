# -*- coding: utf-8 -*-
"""Second audit pass: are the *bodies* the same even when the signatures differ?

The signature audit showed only 2 of 10 groups with identical signatures, which is not enough to
conclude "no duplication" -- a specialisation can carry a copy-pasted proof. What matters for the merge
decision is whether one proof is an *instance* of another (good: replace the specific one by a
`simpa` from the general one) or an independent argument (then they are two facts, not one duplicated).

For each group this prints the normalised body length and the first line, so a human can judge whether
the argument is the same. Bodies are compared after stripping whitespace, so a reformatted copy still
matches.

No file is modified.
"""
import io
import os
import re
import sys
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

DECL = re.compile(
    r"^(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+|@\[[^\]]*\][ \t]*)*"
    r"(theorem|lemma|def)[ \t]+([A-Za-z0-9_']+)", re.M)

GROUPS = ["localMin_of_feasible", "exists_decrease", "not_localMin_of_resid_ne_zero",
          "localMin_iff_feasible"]


def files():
    for base, _d, fs in os.walk(os.path.join(ZERO, "Lattice")):
        for f in sorted(fs):
            if f.endswith(".lean"):
                yield os.path.join(base, f)


def asc(s):
    return "".join(c if ord(c) < 128 else "?" for c in s)


def body_of(src, start):
    nxt = DECL.search(src, start + 1)
    end = nxt.start() if nxt else len(src)
    chunk = src[start:end]
    i = chunk.find(":=")
    body = chunk[i + 2:] if i >= 0 else chunk
    return " ".join(body.split())


def main():
    found = collections.defaultdict(list)
    for p in files():
        src = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
        for m in DECL.finditer(src):
            if m.group(2) in GROUPS:
                found[m.group(2)].append(
                    (os.path.relpath(p, ZERO).replace("\\", "/"), body_of(src, m.start())))

    for g in GROUPS:
        print("=" * 76)
        print(g)
        print("=" * 76)
        for f, b in found[g]:
            print("  %-42s body %4d chars" % (f, len(b)))
            print("     %s" % asc(b[:130]))
        bodies = {b for _f, b in found[g]}
        print("  -> %d distinct bodies among %d occurrences" % (len(bodies), len(found[g])))
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
