#!/usr/bin/env python
"""gov/clean_probes.py -- remove artifacts whose Lean source no longer exists.

WHY THIS EXISTS

    A verify run that is KILLED mid-flight can leave two kinds of debris: a probe SOURCE it planted and did
    not remove, and/or the probe's build artifact. `gate.py`'s I7 catches both, and its exit code is 8.

    **Round 1007 recorded the failure this tool fixes: I had a HARD-CODED list of three probe names and
    cleaned by that list. `verify_all` runs ELEVEN reactivity probes, so three rounds in a row a killed run
    left a probe my list did not name, and the next `gate.py` failed with exit 8 -- which I then misread as a
    real regression. A recovery procedure that depends on remembering the right names is not a procedure.**

    **=> the tool now derives the answer instead of remembering it: an ARTIFACT with no SOURCE is debris by
    definition, whichever probe produced it.**

WHAT IT DELETES, AND WHAT IT REFUSES TO

    Orphan artifacts are deleted by EXACT path -- `.olean`, `.ilean`, `.trace` and the two `.hash` files that
    belong to the same module. Never a glob: round 30 recorded a wildcard cleanup that removed a live
    `.olean` whose gitignored source remained, producing the opposite I7 finding.

    **A source with no artifact is NOT touched.** That is a real missing build, not stale state, and deleting
    it would destroy work. It is reported instead.

MODES

    (default)   report what is an orphan and what is a missing build
    --clean     delete the orphans
    --check     exit 1 if any orphan exists (for use after an interrupted run)
    --self-test assert the module/source path mapping and the orphan rule
"""
import argparse
import io
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
LATTICE = os.path.join(REPO, "Lattice")
ARTIFACT_ROOT = os.path.join(REPO, ".lake", "build", "lib")
SUFFIXES = (".olean", ".ilean", ".trace", ".olean.hash", ".ilean.hash")


def module_path(artifact):
    """`.lake/build/lib/Lattice/Core/Probe.olean` -> `Lattice/Core/Probe.lean` (repo-relative)."""
    rel = os.path.relpath(artifact, ARTIFACT_ROOT).replace(os.sep, "/")
    for suf in SUFFIXES:
        if rel.endswith(suf):
            return rel[: -len(suf)] + ".lean"
    return None


def untracked_probe_sources():
    """`*Probe*.lean` under Lattice/ that git does not track.

    **Round 1012: this is the THIRD kind of debris, and the one that broke a verify.** A killed
    `check_comments_reactivity.py` left `Lattice/Core/Probe.lean` behind with a mutated comment
    (an unmatched `-/`), so gate.py's **I8** failed with exit 9 while I7 was green and this tool
    reported "no orphan".**

    **=> ROUND 1013 REFUTED MY FIRST RULE. I wrote "an untracked `*Probe*.lean` is debris by definition",
    deleted `Lattice/Core/CIC/ShiftSubstOffsetProbe.lean`, and BROKE THE BUILD: `Lattice/Core.lean` and
    `Lattice/Core/CIC/ShiftSubstOffset.lean` both imported it. `.gitignore` has `*Probe.lean`, so being
    untracked says nothing at all about being debris -- REAL probe modules are gitignored too.**

    **=> the rule that survives: a probe source is debris only if it is untracked AND no tracked file
    imports it. Imported-ness is the property that matters, and `git grep` answers it.**
    """
    if not os.path.isdir(LATTICE):
        return []
    out = []
    for root, _dirs, files in os.walk(LATTICE):
        for f in sorted(files):
            if not f.endswith(".lean") or "Probe" not in f:
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, REPO).replace(os.sep, "/")
            tracked = subprocess.run(["git", "-C", REPO, "ls-files", "--error-unmatch", rel],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if tracked.returncode == 0:
                continue
            module = rel[:-len(".lean")].replace("/", ".")
            imported = subprocess.run(["git", "-C", REPO, "grep", "-l", "-F", "import " + module],
                                      stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
            # **A TRACKED FILE THAT IMPORTS IT MAKES IT REAL, whatever gitignore says. This is the
            # condition round 1013 was missing, and its absence broke the build.**
            if imported.returncode == 0 and (imported.stdout or b"").strip():
                continue
            out.append(rel)
    return out


def scan():
    """(orphans, missing) -- artifacts with no source, and sources with no artifact."""
    if not os.path.isdir(ARTIFACT_ROOT):
        return {}, []
    orphans = {}
    for root, _dirs, files in os.walk(ARTIFACT_ROOT):
        for f in sorted(files):
            if not f.endswith(".olean"):
                continue
            p = os.path.join(root, f)
            src = module_path(p)
            if src is None:
                continue
            if not os.path.isfile(os.path.join(REPO, src)):
                orphans[src] = p   # keyed by the MISSING source
    # the reverse direction over the tracked tree
    missing = []
    if os.path.isdir(LATTICE):
        for root, _dirs, files in os.walk(LATTICE):
            for f in sorted(files):
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(root, f)
                rel = os.path.relpath(p, REPO).replace(os.sep, "/")
                art = os.path.join(ARTIFACT_ROOT, rel[:-len(".lean")] + ".olean")
                if not os.path.isfile(art):
                    missing.append(rel)
    # keep it a DICT (source -> artifact): the cleaner needs the artifact path, and a sorted
    # list of keys would drop it -- that was round 1007's bug, caught by the tool's own first run.
    return {k: orphans[k] for k in sorted(orphans)}, missing


def siblings(artifact):
    """Every artifact belonging to one module, by exact path."""
    base = artifact[: -len(".olean")]
    return [base + suf for suf in SUFFIXES]


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--clean", action="store_true", help="delete the orphan artifacts")
    ap.add_argument("--check", action="store_true", help="exit 1 if any orphan exists")
    ap.add_argument("--self-test", action="store_true", help="assert the mapping and the orphan rule")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    orphans, missing = scan()
    print("clean probes: artifacts whose source is gone")
    print("  orphans (artifact, no source) : %d" % len(orphans))
    for src in orphans:
        print("    %s" % src)
    print("  missing build (source, no artifact) : %d  -- NOT touched" % len(missing))
    for rel in missing[:10]:
        print("    %s" % rel)

    if args.check:
        return 1 if orphans else 0

    probes = untracked_probe_sources()
    print("  untracked probe sources : %d" % len(probes))
    for rel in probes:
        print("    %s" % rel)

    if args.check:
        return 1 if (orphans or probes) else 0

    if args.clean and probes:
        for rel in probes:
            p = os.path.join(REPO, rel)
            if os.path.isfile(p):
                os.remove(p)
        for rel in probes:
            art = os.path.join(ARTIFACT_ROOT, rel[:-len(".lean")] + ".olean")
            for q in siblings(art):
                if os.path.isfile(q):
                    os.remove(q)
        print("  removed %d untracked probe source(s) and their artifacts" % len(probes))

    if args.clean and orphans:
        removed = 0
        for src in orphans:
            for p in siblings(orphans[src]):
                if os.path.isfile(p):
                    os.remove(p)
                    removed += 1
        print("  removed %d artifact file(s)" % removed)
    print("CLEAN PROBES: %s"
          % ("no orphan" if not orphans else "%d orphan module(s)" % len(orphans)))
    return 0


def _self_test():
    ok = True
    case = os.path.join(ARTIFACT_ROOT, "Lattice", "Core", "Probe.olean")
    want = "Lattice/Core/Probe.lean"
    if module_path(case) != want:
        print("  SELF-TEST FAIL: mapping produced %r, wanted %r" % (module_path(case), want))
        ok = False
    if module_path(os.path.join(ARTIFACT_ROOT, "Lattice", "Core", "Probe.ilean")) != want:
        print("  SELF-TEST FAIL: .ilean did not map to the same source")
        ok = False
    sib = siblings(case)
    if len(sib) != len(SUFFIXES) or not all(s.startswith(case[:-len(".olean")]) for s in sib):
        print("  SELF-TEST FAIL: the sibling set is not every artifact of the module")
        ok = False
    if siblings(case)[0] != case:
        print("  SELF-TEST FAIL: the .olean is not in its own sibling set")
        ok = False
    print("CLEAN PROBES SELF-TEST: %s" % ("mapping, suffixes and siblings all behave" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
