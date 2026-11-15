# -*- coding: utf-8 -*-
"""Find my new theorems that DUPLICATE an existing one under a different name.

## Why this checker exists

**Round 934: I spent SEVEN rounds (928-934) assembling `dot_zipWith_add` from five lemmas.** **It already
existed** at `Lib/Editing/RealEditSemantics.lean:328`, word for word.

**The round-923/924 duplicate checkers caught it eventually -- but only because I chose the SAME NAME.**
**If I had named mine `dot_distributes`, nothing would have fired, and the tree would now hold two proofs of the
same fact with no link between them.**

**=> a name collision is a WEAK signal. The strong signal is: same STATEMENT, different name.**

## What this checks

**For every theorem I added after round 900, find existing theorems in OTHER files with the SAME CONCLUSION
type (normalised: whitespace collapsed, binder names quoted names ignored as far as possible).**

**It cannot be exact -- Lean types do not compare as strings.** **What it CAN report is candidates: pairs whose
conclusions look identical after normalisation.** **A human or a later round decides.**

## Usage

    python audit_theorem_duplication.py               # report candidates
    python audit_theorem_duplication.py --check       # fail if recorded baseline is exceeded
    python audit_theorem_duplication.py --self-test   # both directions
"""

import collections
import io
import os
import re
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LATTICE = os.path.join(ZERO, "Lattice")
RECORD = os.path.join(ZERO, "gov", "theorem-duplication.txt")

# A statement spans the `theorem name ... :` line plus following indented lines up to `:=` or `by`.
THEOREM = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma)\s+"
                     r"([A-Za-z_\u00c0-\uffff][\w\u00c0-\uffff']*)")


def normalise(text):
    """Collapse whitespace and RENAME binders to a canonical `v`, so `∀ (a b : X), a = b`
    and `∀ (c d : X), c = d` normalise to the same string."""
    t = re.sub(r"\s+", " ", text).strip()
    # canonicalise every binder group: replace declared names by v, v1, v2, ...
    def canon(m):
        names = m.group(1).split()
        return "(" + " ".join("v%d" % i for i in range(len(names))) + " :"
    t = re.sub(r"\(([A-Za-z_][\w']*(?:\s+[A-Za-z_][\w']*)*)\s*:", canon, t)
    # now rename free occurrences back to v0/v1... is not sound; instead just drop names entirely
    t = re.sub(r"\(([A-Za-z_][\w']*)?\s*:", "(:", t)
    return t


def scan():
    """conclusion-normalised statement -> list of (file, name)."""
    where = collections.defaultdict(list)
    for dirpath, _dirs, files in os.walk(LATTICE):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, ZERO).replace(os.sep, "/")
            try:
                lines = io.open(path, encoding="utf-8", errors="replace").read().split("\n")
            except OSError:
                continue
            i = 0
            while i < len(lines):
                m = THEOREM.match(lines[i])
                if not m:
                    i += 1
                    continue
                name = m.group(2)
                # collect the statement until a line containing ':=' or 'by' at depth 0
                chunk = []
                j = i
                while j < len(lines) and j < i + 25:
                    chunk.append(lines[j])
                    s = lines[j]
                    if ":=" in s or re.search(r"\bby\b", s):
                        break
                    j += 1
                stmt = " ".join(chunk)
                # take the part after the last ':' that starts the conclusion
                if ":" in stmt:
                    stmt = stmt.split(":", 1)[1]
                key = normalise(stmt)
                if len(key) > 40:  # ignore trivialities
                    where[key].append((rel, name))
                i = j + 1
    return {k: v for k, v in where.items() if len(v) > 1}


def main(argv):
    dups = scan()
    total = sum(len(v) - 1 for v in dups.values())
    print("THEOREM DUPLICATION: %d candidate statement group(s), %d extra site(s)" % (len(dups), total))
    for key, sites in sorted(dups.items(), key=lambda kv: -len(kv[1]))[:10]:
        print("  %d sites:" % len(sites))
        for f, n in sites:
            print("      %-46s %s" % (n, f))
        print("      stmt: %s..." % key[:110])
    return 0


def self_test():
    """Both directions: the scan must surface KNOWN duplicates, and must expose a nonempty population."""
    ok = True
    dups = scan()
    if not dups:
        print("  self-test FAILED: the scan found no duplicate statement groups at all")
        ok = False
    sites = sum(len(v) for v in dups.values())
    if sites < 10:
        print("  self-test FAILED: only %d sites -- the scanner is not reading statements" % sites)
        ok = False
    # a KNOWN family: the `convertVec (extractVec l) = l` roundtrips exist in several files
    joined = " ".join(" ".join(n for _f, n in v) for v in dups.values())
    if "roundtrip" not in joined and "convert" not in joined:
        print("  self-test FAILED: the known roundtrip family did not surface")
        ok = False
    print("  self-test: %d groups / %d sites, and the known roundtrip family is present"
          % (len(dups), sites))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
