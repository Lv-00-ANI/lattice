"""gov/audit_reproducible_numbers.py -- which headline numbers can be recomputed from TRACKED SOURCES alone.

## Why this file exists

Plan 6.3 asks for four tiers of evidence, the last being **可复现 / reproducible**: "recheck dependencies, build,
examples and proofs in a clean environment". A full cold build is not possible in this checkout -- it would
have to rebuild mathlib -- so this file pins down the part that IS checkable, and states the boundary instead
of claiming the tier wholesale:

> For each headline number the documents claim, is the number produced by a script that reads ONLY tracked
> sources, or does its producer read build artifacts (`.lake/...` oleans)?

That distinction is not cosmetic. A number produced from sources can be recomputed from a `git archive`; a
number produced from artifacts cannot, because the artifacts are not in the repository.

## The classification has to tell READING from SKIPPING

Almost every tool under `gov/` mentions `.lake`, because the standard walk is

    dirs[:] = [d for d in dirs if d != ".lake"]

i.e. it SKIPS the build directory. Treating a mention as a dependency would mark the whole tree as
artifact-dependent, which is false. So the classifier looks at the line's shape: a line that mentions
`.lake`/`olean`/`ilean` AND contains a skip idiom (`not in`, `dirs[:]`, `skip`, `exclude`, ...) is a skip;
otherwise, if it contains an open/exists/glob idiom, it is a READ.

## Interface

    python audit_reproducible_numbers.py            # report: per metric, its class and the evidence
    python audit_reproducible_numbers.py --check    # gate: a "source" metric must have no reading producer;
                                                    # and an "artifact" metric must have one (else the
                                                    # classification is stale)
    python audit_reproducible_numbers.py --self-test
"""

import argparse
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# **A mention of the build directory is a DEPENDENCY only if the line also reads it. These two regexes are the
# whole classifier, and the self-test pins both directions -- including the standard skip idiom, which is the
# case that would otherwise produce a false "artifact-dependent" verdict for nearly every tool.**
MENTION = re.compile(r"\.lake|olean|ilean")
SKIP_IDIOM = re.compile(r"not in|dirs\[:\]|skip|exclude|ignore|startswith\(['\"]\.lake")
READ_IDIOM = re.compile(r"open\(|io\.open|path\.exists|os\.path\.join\([^)]*\.lake|glob|listdir|\.olean|\.ilean")

# **Each headline number, the class it claims, and the script(s) that produce it. The class is a CLAIM, and
# `--check` fails when the claim disagrees with the code -- that is the point of the file.**
METRICS = [
    ("module count",               "source",   ["audit_counts.py"]),
    ("declaration count",          "source",   ["audit_counts.py"]),
    ("theorem + lemma count",      "source",   ["audit_counts.py"]),
    ("load-bearing audited",       "source",   ["check_coverage_claim.py"]),
    ("refutation count",           "source",   ["check_refutation_census.py"]),
    ("checks / gates / reporters", "source",   ["verify_all.py"]),
    ("objective carriers / dead",  "source",   ["gen_objective_map.py"]),
    ("vacuous plugin slots",       "source",   ["audit_plugin_slots.py"]),
    ("olean presence (gate I7)",   "artifact", ["check_olean_presence.py"]),
]


def artifact_reads(script):
    """Return the lines of `script` that READ build artifacts (skips and comments do not count)."""
    path = os.path.join(HERE, script)
    if not os.path.exists(path):
        return None, ["MISSING SCRIPT %s" % script]
    src = io.open(path, encoding="utf-8", errors="replace").read()
    reads, skipped = [], 0
    for raw in src.split("\n"):
        line = raw.strip()
        if not MENTION.search(line):
            continue
        if line.startswith("#") or line.startswith('"') or line.startswith("'"):
            continue  # a comment or a string in prose is not a read
        if SKIP_IDIOM.search(line):
            skipped += 1
            continue
        if READ_IDIOM.search(line):
            reads.append(line[:110])
    return reads, skipped


def self_test():
    bad = 0
    skip_line = 'dirs[:] = [d for d in dirs if d != ".lake"]'
    read_line = 'src = io.open(os.path.join(base, ".lake", "build", x))'
    if artifact_reads.__name__ != "artifact_reads":
        bad += 1
    # the classifier must call the skip idiom a skip and the open a read
    if not SKIP_IDIOM.search(skip_line):
        print("  SELF-TEST FAIL: the standard walk skip was not recognised as a skip")
        bad += 1
    if SKIP_IDIOM.search(read_line):
        print("  SELF-TEST FAIL: an actual open was classified as a skip")
        bad += 1
    if not READ_IDIOM.search(read_line):
        print("  SELF-TEST FAIL: an actual open was not recognised as a read")
        bad += 1
    if READ_IDIOM.search(skip_line):
        print("  SELF-TEST FAIL: the skip line matched the read idiom")
        bad += 1
    print("  reproducible-numbers self-test: %s" % ("ok" if bad == 0 else "%d FAILURES" % bad))
    return 0 if bad == 0 else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()

    print("  %-28s %-9s %s" % ("metric", "claimed", "evidence"))
    problems = []
    for metric, claim, producers in METRICS:
        any_read, any_skip, detail = False, 0, []
        for script in producers:
            reads, skipped = artifact_reads(script)
            if reads is None:
                detail.extend(skipped)
                continue
            any_skip += skipped
            if reads:
                any_read = True
                detail.append("%s READS: %s" % (script, reads[0]))
            else:
                detail.append("%s: %d skip(s), 0 read(s)" % (script, skipped))
        verdict = "artifact" if any_read else "source"
        mark = "ok" if verdict == claim else "*** MISMATCH ***"
        print("  %-28s %-9s %s" % (metric, claim, mark))
        for d in detail:
            print("      %s" % d)
        if verdict != claim:
            problems.append((metric, claim, verdict))

    if problems:
        for metric, claim, verdict in problems:
            print("  MISMATCH: %r claimed %s but the code says %s" % (metric, claim, verdict))
        if args.check:
            print("  REPRODUCIBLE NUMBERS: %d metric(s) mis-classified" % len(problems))
            return 1
    if args.check:
        print("  REPRODUCIBLE NUMBERS: every claimed class matches the code")
        print("  boundary: numbers classed 'source' survive a `git archive` alone; those classed")
        print("  'artifact' cannot be recomputed without `.lake/`, which is NOT in the repository.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())