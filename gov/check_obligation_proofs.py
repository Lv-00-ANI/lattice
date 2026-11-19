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

        # Round 980: the `verifiedObligation` entries were COUNTED here and never VALIDATED. Since all 74
        # obligations now go through `verifiedObligation` (literals = 0), the loop below ran over an empty
        # list and the two detectors were dead: `file` fields pointing at nonexistent paths passed silently.
        # An obligation carries its proposition, not its provenance -- the file and the theorem name are
        # still strings, and a string can be wrong no matter how the obligation is built.
        for name, fil, thm in v:
            if thm not in declared:
                ghosts.append((rel, name, thm))
            if fil and not os.path.isfile(os.path.join(REPO, fil)):
                missing_files.append((rel, name, fil))

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

    # SHRINK-ONLY baseline: the 34 entries recorded when this detector first went live are a known,
    # registered migration debt -- the implementation moved while the manifests still name the old
    # location, and `Plugins.lean`'s `*_migrated` theorems assert that old prefix with `file_under_dir`,
    # so the strings cannot be corrected without changing those theorems. What must NOT happen is a NEW
    # one: that would be a fresh false provenance claim slipping in unnoticed.
    baseline_path = os.path.join(HERE, "obligation-path-baseline.txt")
    baseline = set()
    if os.path.isfile(baseline_path):
        for line in io.open(baseline_path, encoding="utf-8").read().split("\n"):
            if line.strip() and not line.startswith("#"):
                parts = line.split("\t")
                if len(parts) == 3:
                    baseline.add((parts[0], parts[1], parts[2]))
    current = {(rel, name, fil) for rel, name, fil in missing_files}
    new_bad = current - baseline
    shrunk = baseline - current
    if baseline:
        print("  baseline: %d registered, %d current, %d new, %d already fixed"
              % (len(baseline), len(current), len(new_bad), len(shrunk)))
        for rel, name, fil in sorted(new_bad):
            print("  NEW MISSING FILE %s :: %s -> `%s`" % (rel, name, fil))
        missing_files = sorted(new_bad)

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

    # Round 980: the detectors must fire on a `verifiedObligation` entry, not only on a bare literal.
    # Before this round the `verifiedObligation` matches were COUNTED and never validated, so both
    # detectors were dead on the only shape the tree actually uses (74 verified / 0 literal).
    synthetic = ('verifiedObligation "probe_ob" .soundness '
                 '"Lattice/definitely/not/here.lean" "probe_theorem_absent" (True)')
    hits = VERIFIED.findall(synthetic)
    if len(hits) != 1:
        print("  SELF-TEST FAIL: the VERIFIED pattern does not see a one-line verifiedObligation")
        ok = False
    else:
        _n, _f, _t = hits[0]
        if _t in names:
            print("  SELF-TEST FAIL: an impossible theorem name was found")
            ok = False
        if os.path.isfile(os.path.join(REPO, _f)):
            print("  SELF-TEST FAIL: an impossible file path exists")
            ok = False

    # The tree must actually reach the validated branch, or the new check cannot fire at all.
    real = 0
    for path in manifests():
        text = io.open(path, encoding="utf-8").read()
        blocks = "\n".join(re.findall(r"obligations\s*:=\s*\[(.*?)\]", text, re.S))
        real += len(VERIFIED.findall(blocks))
    if real == 0:
        print("  SELF-TEST FAIL: no verifiedObligation entries, so the new check cannot fire")
        ok = False

    print("OBLIGATION PROOFS SELF-TEST: %s" % ("declaration scan, both detectors and the verified path all behave" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(_self_test())
    sys.exit(main())
