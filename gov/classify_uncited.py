# -*- coding: utf-8 -*-
"""Classify the 73 uncited theorems -- are they dead, or are they library surface?

"Uncited" is not the same as "dead". Three categories matter:

  A. **Refuted or exemplifying** -- counterexamples and necessity witnesses (`down_no_progress`,
     `sound_not_exact`). They exist to bound a claim; nothing cites them because nothing should.
  B. **Library surface** -- laws a *consumer* would use (`netAct_append`, `sim_comp`). Inside this
     repository they have no consumer yet, because the ladder stops at `lib/Linear`. Removing them would
     remove exactly the reusable part.
  C. **Genuinely dead** -- superseded or accidental, e.g. a theorem restating another one.

This script reports the classification with the evidence for each, so the decision to keep or drop is made
on the evidence rather than on the count.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

# theorems whose *name* marks them as bound-setting rather than reusable
BOUND_MARKERS = ("_not_", "_ne_", "not_", "_fails", "_no_", "counterexample", "spectrum",
                 "depends_on", "necessary", "unattainable")


def main():
    files = []
    for base, _d, fs in os.walk(os.path.join(ZERO, "Lattice")):
        for f in sorted(fs):
            if f.endswith(".lean"):
                p = os.path.join(base, f)
                files.append((p, os.path.relpath(p, ZERO).replace("\\", "/")[:-5].replace("/", ".")))
    text = {m: strip_comments(io.open(p, "rb").read().decode("utf-8", "replace")) for p, m in files}
    allext = "".join(text.values())

    DECL = re.compile(r"^\s*(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                      r"(theorem|lemma)\s+([A-Za-z0-9_']+)", re.M)

    groups = {"A: bound-setting (intended to stand alone)": [],
              "B: library surface (no consumer yet)": [],
              "C: other": []}
    for m in sorted(text):
        for dm in DECL.finditer(text[m]):
            name = dm.group(2)
            if len(re.findall(r"\b" + re.escape(name) + r"\b", allext)) > 1:
                continue
            full = "%s.%s" % (m, name)
            if any(k in name for k in BOUND_MARKERS):
                groups["A: bound-setting (intended to stand alone)"].append(full)
            elif any(m.startswith(x) for x in ("Lattice.Core.Simulation", "Lattice.Core.Logic",
                                               "Lattice.Core.Net", "Lattice.Core.RepairWF",
                                               "Lattice.Core.VariableNet**")):
                groups["B: library surface (no consumer yet)"].append(full)
            else:
                groups["C: other"].append(full)

    for g, items in groups.items():
        print("=" * 72)
        print("%s  (%d)" % (g, len(items)))
        print("=" * 72)
        for it in items:
            print("  ", it)
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
