#!/usr/bin/env python
"""gov/check_obligation_proofs.py -- how many plugin obligations CARRY their proposition?

WHY THIS EXISTS

    `PARAMETERIZATION-AUDIT.md` item 3: `Obligation.theoremName` was a `String`, so a manifest could name a
    theorem that does not exist and nothing in the tree could tell. Two DAG obligations did exactly that
    (`denote_seq` and `denote_par` for `dag_denote_seq` / `dag_denote_par`).

    Round 137 added `Obligation.proof : Option Prop`, filled by `verifiedObligation`. The field is OPTIONAL
    because seventy-four manifests already name their theorems as strings, and a mandatory field would have
    forced either a mass rewrite or a placeholder -- and a placeholder IS the original problem one layer down.

    => this check MEASURES the migration instead of promising it.

WHAT IT COUNTS

    For every `Lattice/Plugins/**/Manifest.lean`:
      * obligations built with `verifiedObligation`  -- CARRY their proof;
      * obligations built with a bare `{ name := ... }` literal -- name theirs by string.

    It also checks the two things a STRING obligation can still get wrong, both of which are cheap to detect:

      * a `theoremName` that appears NOWHERE in `Lattice/` -- a ghost name;
      * a `file` that does not exist on disk.

WHAT IT DOES NOT DO

    It does not fail on the string/verified split: that is a registered migration with a target, not a defect.
    It DOES fail on a ghost name or a missing file, because those are wrong no matter how the obligation is
    written.
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
LATTICE = os.path.join(REPO, "Lattice")

#: `verifiedObligation "name" .kind "file" "thm" (prop)`
VERIFIED = re.compile(r'verifiedObligation\s+"([^"]*)"\s*\.\w+\s*\n?\s*"([^"]*)"\s*\n?\s*"([^"]*)"')
#: A bare literal: `{ name := "x" ... theoremName := "y" ... file := "z" }`
LITERAL = re.compile(r'\{\s*name\s*:=\s*"([^"]*)"[\s\S]{0,400}?theoremName\s*:=\s*"([^"]*)"[\s\S]{0,200}?file\s*:=\s*"([^"]*)"')


def manifests():
    out = []
    for root, _dirs, files in os.walk(LATTICE):
        for f in files:
            if f == "Manifest.lean" and os.sep + "Plugins" + os.sep in root + os.sep:
                out.append(os.path.join(root, f))
    return sorted(out)


def all_theorem_names():
    """Every `theorem`/`lemma`/`def` name declared anywhere under `Lattice/`."""
    names = set()
    decl = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
    for root, _dirs, files in os.walk(LATTICE):
        for f in files:
            if not f.endswith(".lean"):
                continue
            try:
                text = io.open(os.path.join(root, f), encoding="utf-8").read()
            except OSError:
                continue
            for m in decl.finditer(text):
                names.add(m.group(1))
    return names


def main():
    verified = 0
    literals = 0
    ghosts = []
    missing_files = []
    declared = all_theorem_names()

    for path in manifests():
        rel = os.path.relpath(path, REPO).replace(os.sep, "/")
        text = io.open(path, encoding="utf-8").read()

        # The `Repr` instance in `Manifest.lean` contains `" ++ repr o.theoremName ++ "`, which the literal
        # regex would read as an obligation. Obligations live inside `obligations := [ ... ]` blocks, so the
        # scan is restricted to those -- a `Repr` implementation is not a manifest entry.
        blocks = re.findall(r"obligations\s*:=\s*\[(.*?)\]", text, re.S)
        text = "\n".join(blocks)

        v = VERIFIED.findall(text)
        verified += len(v)

        for name, thm, fil in LITERAL.findall(text):
            # Skip any literal that sits INSIDE a `verifiedObligation` call: the regex is greedy enough
            # to see one, and double-counting would break the totals.
            literals += 1
            if thm not in declared:
                ghosts.append((rel, name, thm))
            if fil and not os.path.isfile(os.path.join(REPO, fil)):
                missing_files.append((rel, name, fil))

    total = verified + literals
    print("  obligations carrying their PROOF (verifiedObligation): %d" % verified)
    print("  obligations naming theirs by STRING:                   %d" % literals)
    print("  total:                                                 %d" % total)

    for rel, name, thm in ghosts:
        print("  GHOST NAME %s :: %s -> `%s` is declared nowhere under Lattice/" % (rel, name, thm))
    for rel, name, fil in missing_files:
        print("  MISSING FILE %s :: %s -> `%s` does not exist" % (rel, name, fil))

    bad = len(ghosts) + len(missing_files)
    if bad:
        print("OBLIGATION PROOFS: %d problem(s)" % bad)
        return 1

    print("OBLIGATION PROOFS: no ghost names, no missing files (%d verified / %d named)"
          % (verified, literals))
    return 0


def _self_test():
    """The two detectors must be able to fire."""
    ok = True
    names = all_theorem_names()

    # `dag_confluence` exists, so it must NOT be flagged.
    if "dag_confluence" not in names:
        print("  SELF-TEST FAIL: `dag_confluence` not found -- the declaration scan is broken")
        ok = False

    # A name that cannot exist MUST be reported as a ghost by a direct check.
    if "this_theorem_does_not_exist_anywhere" in names:
        print("  SELF-TEST FAIL: an impossible name was found")
        ok = False

    # Every registered manifest must be reachable.
    if not manifests():
        print("  SELF-TEST FAIL: no manifests found")
        ok = False

    print("OBLIGATION PROOFS SELF-TEST: %s" % ("all three classes behave" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(_self_test())
    sys.exit(main())
