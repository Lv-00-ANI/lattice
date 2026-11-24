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

# EXEMPT families (skill 1.1: pseudoisomorphic -- same SHAPE, different SEMANTIC object).
# `manifest_no_<claim>` in every Plugin/*/Manifest.lean asserts a DIFFERENT `manifest`. Merging them would make
# one plugin prove another plugin's manifest -- a semantic error, not a consolidation. Recorded, not silently
# dropped: they still show in the report so a future round can re-decide.
# Statements whose CONCLUSION repeats but whose PROOF PATH carries independent content: the proof goes THROUGH an
# abstraction (e.g. `Carrier.criterion`) and thereby establishes that the abstraction is complete. Replacing it by
# `exact <concrete>` would keep the conclusion and LOSE the structural fact. Classified `bridge`, not merged.
BRIDGE_MARKERS = ("Carrier.criterion", "Carrier.", "criterion ")

EXEMPT_NAME_PREFIX = (
    "manifest_no_",
    # `verified.manifest.obligations.length = N` -- N differs per plugin (3,4,6,7,7,8,10,11,12) and `verified`
    # is a DIFFERENT object in each. Constant difference AND semantic difference => pseudoisomorphic.
    "verified_obligations",
    # `fderiv_apply_direction` / `_scalar` / `_vector` / `_fin`: the SAME lemma instantiated at DIFFERENT spaces
    # (general `E`, `E = ℝ`, `Fin k → ℝ`). The binder TYPE differs, which the normalisation erases. Kept separate
    # because each instantiation is a different theorem about a different space.
    "fderiv_apply_direction",
    # `hoeffding_*`: the SAME concentration bound with DIFFERENT HYPOTHESIS SETS -- `hbdd + hmean` at the
    # concrete layer vs `hcoord` (the mgf bound) at the intermediate layer. The CONCLUSION is identical, the
    # PREMISES are not. These are two abstractions of one result, not duplication.
    "hoeffding_",
)

# Measured at round 936 AFTER consolidating the six `convertVec (extractVec l) = l` copies.
# Round 935 measured 260 sites; round 936 brought it to 143. The check fails only if it GROWS.
# round 1078: +2 because the ANALYTIC layer restates the capability layer's two main theorems at a
# weaker hypothesis (no symbolic evidence). The two layers are connected by
# `capability_select_is_analytic`, so these are deliberate parallels across a refinement, not
# accidental duplication: `sufficient_implies_meets` / `select_gives_precision` (capability) and
# `analytic_sufficient_implies_meets` / `analytic_select_gives_precision` (analytic).
# round 1103: +2 for a deliberate PREMISE LADDER -- three theorems with the SAME conclusion
# (`AllSatisfied (extractLayer ls) x`) at decreasing premise strength:
#   extract_after_repair       (forall ls, Sat ls <-> LayerSat cs ls)
#   extract_after_repair_weak  (forall ls, Sat ls ->  LayerSat cs ls)
#   layerZeroRepair_extract    (the instance, mu = 0)
# The gate compares conclusions only, so it cannot see the difference; keeping all three is the point:
# the first cannot be applied to any instance in the tree, the third is the one that has a consumer.
BASELINE = 196   # sites; INDEPENDENT-proof groups: 119 after round 940's classifier fixes   # round 940: the conclusion extraction was TRUNCATED at the binder group's first ':'
#               so multi-line statements were compared only on their LEFT half. Fixing it raised the true
#               count from 143 to 192 -- the earlier numbers were UNDER-measurements, not improvements.

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
                while j < len(lines) and j < i + 30:
                    chunk.append(lines[j])
                    s = lines[j]
                    # stop only at the PROOF INTRODUCER, never at a bare '='
                    if ":=" in s or s.rstrip().endswith(" by") or s.strip() == "by":
                        break
                    j += 1
                stmt = " ".join(chunk)
                # drop only the DECLARATION HEADER: `theorem <name>` plus its binder group.
                # The conclusion is what follows the binder group's closing `) :`, NOT the first ':'.
                mm = re.match(r".*?\)\s*:", stmt, re.S)
                if mm:
                    stmt = stmt[mm.end():]
                elif ":" in stmt:
                    stmt = stmt.split(":", 1)[1]
                key = normalise(stmt)
                # classify the PROOF: an alias delegates, an independent proof does the work again
                body = " ".join(lines[j:min(j + 8, len(lines))])
                # an ALIAS delegates: `:= exact Some.Namespaced.name ...` (possibly after `by`)
                if re.search(r"Lattice\.[\w.]*\w+\s+\w", body) or re.search(r"exact\s+Lattice\.", body):
                    kind = "alias"
                elif "by" not in body and "rfl" not in body and re.search(
                        r":=\s*\n?\s*[a-z_][\w.]*\s", body):
                    kind = "alias"   # `:= someExistingTheorem args` with no tactic block
                elif re.search(r"by\s*cases\b.*rfl", body) or re.search(r"by\s*rfl", body):
                    kind = "rfl"          # definitional roundtrip, no shared authority
                elif any(m in body for m in BRIDGE_MARKERS):
                    kind = "bridge"      # proves through an abstraction; the path IS the content
                else:
                    kind = "independent"
                if len(key) > 40:  # ignore trivialities
                    where[key].append((rel, name, kind))
                i = j + 1
    return {k: v for k, v in where.items() if len(v) > 1}


def main(argv):
    dups = scan()
    total = sum(len(v) - 1 for v in dups.values())
    check = "--check" in argv
    print("THEOREM DUPLICATION: %d candidate statement group(s), %d extra site(s)"
          % (len(dups), total))
    if check:
        if total > BASELINE:
            print("  %d > baseline %d -- a new duplicated statement appeared" % (total, BASELINE))
            return 1
        print("  %d <= baseline %d" % (total, BASELINE))
        return 0
    print("THEOREM DUPLICATION: %d candidate statement group(s), %d extra site(s)" % (len(dups), total))
    indep = 0
    bridges = 0
    exempt = 0
    for key, sites in dups.items():
        if all(n.startswith(EXEMPT_NAME_PREFIX) for (_f, n, _k) in sites):
            exempt += 1
            continue
        kinds = set(k for (_f, _n, k) in sites)
        if "independent" in kinds:
            indep += 1
        elif "bridge" in kinds:
            bridges += 1
    print("  of which have at least one INDEPENDENT proof (the real signal): %d group(s)" % indep)
    print("  exempt as pseudoisomorphic (different `manifest` object): %d group(s)" % exempt)
    print("  bridge groups (same conclusion, proof path is the content): %d group(s)" % bridges)
    for key, sites in sorted(dups.items(), key=lambda kv: -len(kv[1]))[:6]:
        kinds = collections.Counter(k for (_f, _n, k) in sites)
        print("  %d sites  %s" % (len(sites), dict(kinds)))
        for f, n, k in sites:
            print("      [%-11s] %-40s %s" % (k, n, f))
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
    joined = " ".join(" ".join(n for _f, n, _k in v) for v in dups.values())
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
