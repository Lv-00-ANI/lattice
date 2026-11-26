#!/usr/bin/env python
"""check_theorem_liveness.py -- measure how much of the theorem corpus is actually consumed.

**Why this exists.** Round 1161 censused all 10,286 theorem/lemma declarations:

    consumed by another file   1,569   15%
    used inside its own file   3,445   33%
    used NOWHERE               5,272   51%

so 'give every dead theorem a reason' is arithmetically impossible here -- 5,211 unregistered entries would be noise.
But the RATIOS are meaningful and they can move: a change that creates a wave of never-used theorems is a real
regression even though each individual leaf is not.

**What it does.** Recomputes the three counts and fails only if the CHAIN-CONSUMED RATIO falls more than
`TOLERANCE_POINTS` below the recorded baseline. The other two ratios are printed for context but never gate: a leaf is
a legitimate shape (a library of statements, like mathlib), and the point of the gate is to catch a TREND, not a leaf.

**Why a ratio and not a count.** The corpus grows. Writing thirty theorems where five are consumed is 17% -- normal.
Writing thirty where none are consumed is 0% for that batch, and the ratio is what shows it.

Usage:
    python check_theorem_liveness.py             # report
    python check_theorem_liveness.py --check     # exit 1 if the chain ratio fell below baseline - tolerance
    python check_theorem_liveness.py --write     # rewrite the baseline from today's measurement
"""

import collections
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import chain_connectors as CC  # noqa: E402

BASELINE = os.path.join(HERE, "theorem-liveness-baseline.txt")
TOLERANCE_POINTS = 2.0
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def measure():
    corpus = CC.chain_corpus()
    idx = {}
    for rel, src in corpus.items():
        for tok, n in collections.Counter(TOK.findall(src)).items():
            idx.setdefault(tok, {})[rel] = n

    total = chain = in_file = nowhere = 0
    for rel, name, line, text in CC.statements():
        total += 1
        locs = idx.get(name, {})
        own = locs.get(rel, 0)
        others = [r for r, n in locs.items() if r != rel and not r.startswith("Usage/")]
        if others:
            chain += 1
        elif own <= 1:
            nowhere += 1
        else:
            in_file += 1
    return {"total": total, "chain": chain, "in_file": in_file, "nowhere": nowhere}


def read_baseline():
    if not os.path.exists(BASELINE):
        return None
    out = {}
    for line in io.open(BASELINE, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        k, _, v = line.partition("=")
        out[k.strip()] = float(v)
    return out


def main(argv):
    m = measure()
    chain_pct = 100.0 * m["chain"] / m["total"] if m["total"] else 0.0
    in_pct = 100.0 * m["in_file"] / m["total"] if m["total"] else 0.0
    none_pct = 100.0 * m["nowhere"] / m["total"] if m["total"] else 0.0

    print("  theorem/lemma declarations : %d" % m["total"])
    print("  consumed by another file   : %5d  %5.1f%%" % (m["chain"], chain_pct))
    print("  used inside its own file   : %5d  %5.1f%%" % (m["in_file"], in_pct))
    print("  used nowhere               : %5d  %5.1f%%" % (m["nowhere"], none_pct))
    print("  (the first ratio gates; the other two are context -- a leaf is a legitimate shape)")

    if "--write" in argv:
        body = ["# theorem-liveness baseline -- written by check_theorem_liveness.py --write",
                "# only `chain` gates: the CHAIN-CONSUMED RATIO may not fall below baseline - tolerance",
                "total=%d" % m["total"], "chain=%d" % m["chain"],
                "in_file=%d" % m["in_file"], "nowhere=%d" % m["nowhere"],
                "tolerance_points=%g" % TOLERANCE_POINTS]
        io.open(BASELINE, "w", encoding="utf-8", newline="\n").write("\n".join(body) + "\n")
        print("  baseline written to %s" % os.path.basename(BASELINE))
        return 0

    base = read_baseline()
    if base is None:
        print("  no baseline (%s absent) -- run --write to create it" % os.path.basename(BASELINE))
        return 0

    base_chain_pct = 100.0 * base["chain"] / base["total"] if base["total"] else 0.0
    tol = base.get("tolerance_points", TOLERANCE_POINTS)
    floor = base_chain_pct - tol
    print("  baseline chain ratio       : %5.1f%%   floor (baseline - %.1f) %5.1f%%"
          % (base_chain_pct, tol, floor))
    if "--check" in argv and chain_pct < floor:
        print("  THEOREM LIVENESS: chain ratio %.1f%% fell %.1f points below the baseline -- the tree is producing "
              "theorems nothing consumes" % (chain_pct, base_chain_pct - chain_pct))
        return 1
    if chain_pct < floor:
        print("  WARNING: chain ratio %.1f%% is below the floor %.1f%%" % (chain_pct, floor))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))