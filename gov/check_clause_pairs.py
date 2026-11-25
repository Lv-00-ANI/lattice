#!/usr/bin/env python
"""check_clause_pairs.py -- are two adjacent OBJECTIVE clauses ever spoken of in one statement?

**Why this exists.** Every earlier measurement in this project asked whether a carrier had a CONSUMER. Rounds
1135-1143 asked a different question: does any theorem mention BOTH sides of two adjacent clauses? That is a
stronger test of whether the chain is connected than carrier liveness, because a clause can have live carriers and
still share no statement with its neighbour.

**What it counts.** For each clause, the registered carriers (`check_objective_coverage.CLAUSES`); a declaration is
"about" a clause when its STATEMENT (comments stripped, `Usage/` excluded) contains one of that clause's carrier
names. A pair is connected when at least one statement mentions carriers of both.

**Two failures this metric produced, both recorded rather than hidden:**
  * round 1136 -- `eps_repair_requires_descent` IS the 3.2->3.3 bridge, but the script of the day counted nothing
    because it spoke of the TYPE `Repair` rather than a carrier NAME. The seam tool saw it; this one did not.
  * rounds 1141/1143 -- clauses 2.2 and 5 looked disconnected only because their DATA-level and CIC-level carriers
    (`corpusToLayer`, `CoversCorpus`, `CICCtx`, `cicToConstraint`) were never registered. Registering them moved two
    pairs from 0 to non-zero WITHOUT writing a theorem.

So the lesson is in the tool: a zero here means "these two vocabulary lists do not meet in one statement", which may
be a fact about the tree OR a gap in the vocabulary. Always check the second before concluding the first.

Usage:
    python check_clause_pairs.py             # report
    python check_clause_pairs.py --check     # exit 1 if any adjacent pair is EMPTY
"""

import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import chain_connectors as CC  # noqa: E402
from check_objective_coverage import CLAUSES  # noqa: E402

ADJACENT = [
    ("1.1 data -> token", "1.2 token -> symbol"),
    ("1.2 token -> symbol", "1.3 symbol -> weight"),
    ("1.3 symbol -> weight", "1.4 weight -> symbol"),
    ("1.4 weight -> symbol", "3.2 inverse: verification"),
    ("3.2 inverse: verification", "3.3 inverse: repair"),
    ("3.3 inverse: repair", "3.4 inverse: re-injection"),
    ("3.4 inverse: re-injection", "4 loop"),
    ("2.1 forward: constraint loss", "1.3 symbol -> weight"),
    ("2.2 forward: data synthesis", "1.3 symbol -> weight"),
    ("2.3 forward: structured init", "1.3 symbol -> weight"),
    ("5 symbolic engine", "1.3 symbol -> weight"),
    ("8 Lean guarantee", "3.2 inverse: verification"),
]


def pair_counts():
    corpus = CC.chain_corpus()
    clauses = list(CLAUSES.keys())
    rx = {c: re.compile(r"\b(?:%s)\b" % "|".join(re.escape(n) for n in CLAUSES[c])) for c in clauses}
    out = {}
    for rel, name, line, text in CC.statements():
        hit = [c for c in clauses if rx[c].search(text)]
        for i in range(len(hit)):
            for j in range(i + 1, len(hit)):
                k = tuple(sorted((hit[i], hit[j])))
                out.setdefault(k, []).append((rel, name))
    return out, corpus


def main(argv):
    pairs, _ = pair_counts()
    print("%-30s <-> %-30s %4s" % ("clause", "clause", "theorems"))
    empty = 0
    for a, b in ADJACENT:
        k = tuple(sorted((a, b)))
        got = pairs.get(k, [])
        print("%-30s <-> %-30s %4d %s" % (a[:30], b[:30], len(got), "" if got else "  EMPTY"))
        if not got:
            empty += 1
    print()
    print("adjacent pairs: %d ; empty: %d" % (len(ADJACENT), empty))
    print("REMINDER: an EMPTY may be a vocabulary gap, not a missing theorem -- see this file's docstring.")
    if empty and "--check" in argv:
        print("CLAUSE PAIRS: %d adjacent pair(s) share no statement" % empty)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))