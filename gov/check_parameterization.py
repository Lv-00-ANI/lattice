#!/usr/bin/env python
"""gov/check_parameterization.py -- the 18 "concrete instance vs abstract role" defects must stay registered.

WHY THIS EXISTS

    Round 135's audit found eighteen places where an ABSTRACT ROLE was welded to a CONCRETE INSTANCE:
    `Weights` as a bare vector, `State` as `K -> Option Nat`, `Obligation.theoremName` as a `String`,
    and so on. Each compiles and each proves something; what they cost is EXPRESSIVENESS -- the day a
    direction needs more structure, the chosen instance is not enough and changing it moves the whole chain.

    A list in a markdown file decays. This check makes the list EXECUTABLE: every registered item must
    still be present in the code, and when an item is fixed the gate says so, so the list shrinks by
    evidence rather than by memory.

WHAT IT CHECKS

    A. Every item in `PARAMETERIZATION-AUDIT.md`'s numbered table is still registered (the count is 18).
    B. For each item with a `PROBES` entry, the code still contains the CONCRETE INSTANCE the audit named.
       If the probe no longer matches, the item has been PARAMETERISED and the audit is stale.
    C. Items with NO probe are reported as `unprobed` -- they are registered but not machine-checkable,
       and saying so is better than pretending the check covers them.

WHAT IT DOES NOT DO

    It does not fail the build. All eighteen are REGISTERED TECHNICAL DEBT, not defects: the project's
    judgement is that they can live until their phase arrives. The gate reports a COUNT, exactly as
    `prop-def-baseline.txt` does for its own findings.
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
AUDIT = os.path.join(REPO, "PARAMETERIZATION-AUDIT.md")

#: Each entry: (item id, human name, a probe (path substring, regex) or None).
#:
#: A probe matches when the FILE at `path` exists AND the regex is found in it. `None` means the item is
#: registered but not machine-checkable at this level (documented in the report).
PROBES = [
    ("1", "Weights as a bare vector", ("Core/ModelArtifact.lean", r"\u2192\s*Pt\s+n|Weights\s*:=\s*\u2115\s*\u2192")),
    ("2", "State as K -> Option Nat", ("Plugins/Runtime/Spatiotemporal/Model.lean", r"abbrev\s+RState.*Option")),
    ("3", "Effect as single-key overwrite", ("Plugins/Runtime/Spatiotemporal/Model.lean", r"structure\s+Effect")),
    ("4", "Term has no Prop/Type split", ("Core/CIC/Syntax.lean", r"\|\s*sort\s*:\s*Level\s*\u2192")),
    ("5", "Obligation.theoremName is a String", ("Plugins/Manifest.lean", r"theoremName\s*:\s*String")),
    ("6", "Arch as a layer list", ("Core/ModelArtifact.lean", r"widths\s*:\s*List")),
    ("7", "Behavior as a function", None),
    ("8", "Spec as a constraint list", None),  # covered by the CIC decision; no probe by design
    ("9", "ServiceKey is a String", ("Plugins/Manifest.lean", r"abbrev\s+ServiceKey\s*:=\s*String")),
    ("10", "ResultEquiv as three parallel branches", None),
    ("11", "ProofComplete as a flat conjunction", None),
    ("12", "Plugin as directory only", None),
    ("13", "Layer as a fixed enum", ("Plugins/Manifest.lean", r"inductive\s+PluginLayer")),
    ("14", "Repair.mu as Nat", None),
    ("15", "SafeBranch as a False branch", None),
    ("16", "Spec existence as Nonempty", None),
    ("17", "Fiber lifecycle as Bool", None),
    ("18", "Card claims as `:= rfl`", None),
]

EXPECTED = 18


def registered_ids():
    """The numbered rows of the audit's summary table, as strings."""
    text = io.open(AUDIT, encoding="utf-8").read()
    ids = re.findall(r"^\|\s*\**(\d+)\**\s*\|", text, re.M)
    return set(ids)


def probe_hits(path_sub, pattern):
    """`True` when the probe still matches -- i.e. the concrete instance is UNCHANGED."""
    full = os.path.join(REPO, "Lattice", path_sub)
    if not os.path.isfile(full):
        return False
    text = io.open(full, encoding="utf-8").read()
    return re.search(pattern, text) is not None


def main():
    if not os.path.isfile(AUDIT):
        print("PARAMETERIZATION: the audit file is MISSING")
        return 1

    ids = registered_ids()
    problems = []

    # A. Registration completeness.
    if len(ids) != EXPECTED:
        problems.append("registered %d items, expected %d" % (len(ids), EXPECTED))
    for item, name, _ in PROBES:
        if item not in ids:
            problems.append("item %s (%s) is NOT registered" % (item, name))

    # B/C. Probe status.
    still_concrete = []
    parameterised = []
    unprobed = []
    for item, name, probe in PROBES:
        if probe is None:
            unprobed.append((item, name))
            continue
        if probe_hits(*probe):
            still_concrete.append((item, name))
        else:
            parameterised.append((item, name))

    for item, name in still_concrete:
        print("  OPEN   %-3s %s" % (item, name))
    for item, name in parameterised:
        print("  FIXED  %-3s %s -- remove it from PARAMETERIZATION-AUDIT.md" % (item, name))
    for item, name in unprobed:
        print("  n/a    %-3s %s -- registered, not machine-checkable" % (item, name))

    for p in problems:
        print("  " + p)

    print("PARAMETERIZATION: %d registered, %d open, %d fixed, %d unprobed%s"
          % (len(ids), len(still_concrete), len(parameterised), len(unprobed),
             "" if not problems else " -- %d REGISTRATION problem(s)" % len(problems)))

    # Only a REGISTRATION problem fails: an open item is registered debt, and a fixed item means the audit
    # needs a one-line edit, not that the tree is wrong.
    return 0 if not problems else 1


def _self_test():
    """Prove all three report classes can fire."""
    ok = True

    # A probe that matches must be classified OPEN.
    if not probe_hits("Plugins/Manifest.lean", r"theoremName\s*:\s*String"):
        print("  SELF-TEST FAIL: item 5's probe no longer matches")
        ok = False

    # A probe that cannot match must be classified FIXED.
    if probe_hits("Plugins/Manifest.lean", r"THIS_IDENTIFIER_DOES_NOT_EXIST_ANYWHERE"):
        print("  SELF-TEST FAIL: a non-matching probe matched")
        ok = False

    # Registration must be complete on the real file.
    if len(registered_ids()) != EXPECTED:
        print("  SELF-TEST FAIL: registration count is %d, not %d" % (len(registered_ids()), EXPECTED))
        ok = False

    print("PARAMETERIZATION SELF-TEST: %s" % ("all three classes behave" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(_self_test())
    sys.exit(main())
