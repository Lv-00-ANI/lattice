"""Baseline the anti-tautology guard against the current findings.

## The design problem

A guard that fails on 28 pre-existing findings gets switched off, and then it catches nothing. A guard
whose allow-list can grow without bound becomes the excuse pile it was meant to replace.

## The resolution

`gov/proof_strength_baseline.txt` is a **frozen snapshot with a date and a reason per line**, and the
guard enforces two directions:

  - a finding NOT in the baseline **fails** (no new nominally-complete proofs);
  - a baseline entry that no longer fires **also fails** (the baseline may only shrink -- paying off
    debt requires deleting the line, so the file is a ledger, not a graveyard).

That is the same two-way discipline `check_ladder_rungs` and `check_doc_names` already use.
"""
import io
import os
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

GOV = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.join(GOV, "proof_strength_baseline.txt")

sys.path.insert(0, GOV)
import check_proof_strength as cps  # noqa: E402

findings = cps.scan()

lines = [
    "# Proof-strength baseline -- FROZEN SNAPSHOT",
    "#",
    "# Generated from `check_proof_strength.py` at the moment the guard was introduced.",
    "# Every line is a KNOWN shape of nominally-complete proof. The discipline is two-way:",
    "#   * a finding not listed here FAILS  (no new ones)",
    "#   * a listed entry that no longer fires FAILS  (the list may only shrink)",
    "#",
    "# To pay off an entry: fix the theorem, then DELETE its line here.",
    "# Bulk-approving this file defeats the only purpose it has.",
    "#",
    "# Format:  <file>\\t<line>\\t<kind>\\t<declaration>",
    "#",
]
for rel, line, kind, detail in sorted(findings):
    name = detail.split(":")[0].split()[-1]
    lines.append("%s\t%d\t%s\t%s" % (rel, line, kind, name))

io.open(BASE, "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")
print("wrote %s (%d entries)" % (BASE, len(findings)))
