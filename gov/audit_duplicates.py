# -*- coding: utf-8 -*-
"""Audit: for each duplicated name, what is actually duplicated?

Round 27's whole-repo scan found 13 groups of same-named declarations. Merging them blindly would be
wrong -- some are *specialisations* (the same statement at a different carrier), and some are genuinely
the same proof copy-pasted.

This audit prints, per duplicated name: the files, the full signature of each occurrence, and whether
the signatures are textually identical. Identical signatures are the strongest merge candidates;
different ones need a judgement about whether one generalises the other.

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
    r"(theorem|lemma|def|abbrev|structure|inductive|instance)[ \t]+([A-Za-z0-9_']+)",
    re.M)


def files():
    out = []
    for base, _d, fs in os.walk(os.path.join(ZERO, "Lattice")):
        for f in sorted(fs):
            if f.endswith(".lean"):
                out.append(os.path.join(base, f))
    return out


def signature_after(src, start):
    """The declaration text up to the first ':=' or 'where' -- i.e. its signature."""
    end = len(src)
    for marker in (" :=", "\n  where", "\n:="):
        i = src.find(marker, start)
        if i >= 0:
            end = min(end, i)
    raw = " ".join(src[start:end].split())
    # ASCII-safe: the Windows console codepage cannot encode Lean's unicode tokens
    return "".join(c if ord(c) < 128 else "<U+%04X>" % ord(c) for c in raw)


def main():
    occ = collections.defaultdict(list)
    for p in files():
        src = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
        for m in DECL.finditer(src):
            occ[m.group(2)].append((os.path.relpath(p, ZERO).replace("\\", "/"),
                                    m.group(1), signature_after(src, m.start())))

    dup = {k: v for k, v in occ.items() if len(v) > 1}
    print("=" * 78)
    print("DUPLICATE AUDIT  (%d groups)" % len(dup))
    print("=" * 78)
    identical, differing = [], []
    for name in sorted(dup):
        sigs = {s for (_f, _k, s) in dup[name]}
        (identical if len(sigs) == 1 else differing).append(name)

    print("\n--- IDENTICAL signatures (strongest merge candidates) ---")
    for name in identical:
        print("\n%s  (%d occurrences)" % (name, len(dup[name])))
        for f, k, s in dup[name]:
            print("   %-44s %s" % (f, k))
        print("   signature: %s" % dup[name][0][2][:150])

    print("\n--- DIFFERING signatures (need a generalisation judgement) ---")
    for name in differing:
        print("\n%s  (%d occurrences)" % (name, len(dup[name])))
        for f, k, s in dup[name]:
            print("   %-44s %s" % (f, k))
            print("      %s" % s[:160])

    print("\n" + "=" * 78)
    print("identical: %d   differing: %d" % (len(identical), len(differing)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
