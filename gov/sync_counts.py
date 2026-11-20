#!/usr/bin/env python
"""gov/sync_counts.py -- update the documents' numbers from the CHECKERS' own disagreement reports.

WHY THIS EXISTS

    Every round ends with a documented-count sync, and I had been doing it by hand with one `re.sub` per
    document. Round 1012 recorded what that costs: **two numbers were typed one off** (9843 where the tree
    had 9844, 8787 where it had 8788), and it was `check_coverage_claim.py` that caught them, not me.

    **=> a number a human retypes is a number a human can mistype. So the OLD value now comes from the
    document itself, as the checker reports it, and the NEW value comes from the checker's measurement.
    Neither is typed here.**

THE ORACLE

    Three existing checkers already print exactly the pairs needed:

      check_usage_claims.py     `<label> <doc> <measured> *** WRONG ***`
      check_coverage_claim.py   `<label> doc <doc>, measured <measured>`
      audit_counts.py           `README 写 <doc>   实测 <measured>   MISMATCH`

    This tool parses those three, unions the mappings, and applies them word-boundary-safely to the root
    documents. **It cannot invent a number**: if the checkers agree with the documents, the mapping is empty
    and nothing changes.

WHAT IT REFUSES TO DO

    It does not guess a mapping whose old value is ambiguous (e.g. two different labels disagreeing about
    what a document should say for the same old number). Such a conflict is reported and the run stops,
    because silently picking one is how a sync corrupts a document.
"""
import argparse
import io
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
DOCS = ["README.md", "STATE-FINAL.md", "DELIVERY.md", "CONVENTIONS.md", "OBJECTIVE-AUDIT.md",
        "USAGE.md", "PROOF-DEBT.md", "MACRO-COGNITION.md", "MACRO-COGNITION-148.md"]

USAGE_WRONG = re.compile(r"(-?\d[\d,]*)\s+(-?\d[\d,]*)\s+\*{3} WRONG")
COVERAGE_WRONG = re.compile(r"doc\s+(\d[\d,]*),\s*measured\s+(\d[\d,]*)")
COUNTS_WRONG = re.compile(r"README \u5199\s+(\d[\d,]*)\s+\u5b9e\u6d4b\s+(\d[\d,]*)\s+MISMATCH")


def _run(script):
    # Windows defaults the child's stdout to the console code page, so decoding Chinese labels as UTF-8
    # raised in the reader thread (round 1013). The encoding is forced on both sides.
    env = dict(os.environ)
    env["PYTHONIOENCODING"] = "utf-8"
    r = subprocess.run([sys.executable, os.path.join(HERE, script)],
                       capture_output=True, cwd=HERE, env=env)
    return ((r.stdout or b"").decode("utf-8", "replace")
            + (r.stderr or b"").decode("utf-8", "replace"))


def collect():
    """{old_number_as_written: {new_number_as_written}} plus a list of conflicting keys."""
    pairs = {}
    for script, rx in (("check_usage_claims.py", USAGE_WRONG),
                       ("check_coverage_claim.py", COVERAGE_WRONG),
                       ("audit_counts.py", COUNTS_WRONG)):
        for old, new in rx.findall(_run(script)):
            pairs.setdefault(old, set()).add(new)
    conflicts = {k: v for k, v in pairs.items() if len(v) > 1}
    mapping = {k: sorted(v)[0] for k, v in pairs.items() if len(v) == 1}
    return mapping, conflicts


def _variants(n):
    """`1076` and `1,076` are the same number; a document may write either."""
    plain = n.replace(",", "")
    try:
        grouped = "{:,}".format(int(plain))
    except ValueError:
        grouped = plain
    return {plain, grouped}


def apply(mapping, write):
    changed = {}
    for name in DOCS:
        path = os.path.join(REPO, name)
        if not os.path.isfile(path):
            continue
        text = io.open(path, encoding="utf-8").read()
        before = text
        for old, new in mapping.items():
            for ov in _variants(old):
                if not re.search(r"(?<![\d,])" + re.escape(ov) + r"(?![\d,])", text):
                    continue
                new_v = new
                if "," in ov:
                    try:
                        new_v = "{:,}".format(int(new.replace(",", "")))
                    except ValueError:
                        new_v = new
                text = re.sub(r"(?<![\d,])" + re.escape(ov) + r"(?![\d,])", new_v, text)
        if text != before:
            changed[name] = True
            if write:
                io.open(path, "w", encoding="utf-8", newline="\n").write(text)
    return changed


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true", help="rewrite the documents (default: report only)")
    ap.add_argument("--self-test", action="store_true", help="assert the parsers and the ambiguity guard")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    mapping, conflicts = collect()
    print("sync counts: the checkers' own old -> new pairs")
    print("  pairs   : %d" % len(mapping))
    for old in sorted(mapping):
        print("    %s -> %s" % (old, mapping[old]))
    if conflicts:
        print("  CONFLICT: %d old value(s) map to more than one new value" % len(conflicts))
        for old in sorted(conflicts):
            print("    %s -> %s" % (old, sorted(conflicts[old])))
        print("SYNC COUNTS: refusing to guess; resolve by re-reading the checkers' labels")
        return 1

    changed = apply(mapping, args.write)
    print("  documents needing change : %d" % len(changed))
    for name in sorted(changed):
        print("    %s" % name)
    if not args.write and changed:
        print("SYNC COUNTS: %d document(s) would change (rerun with --write)" % len(changed))
        return 0
    print("SYNC COUNTS: done")
    return 0


def _self_test():
    ok = True
    if USAGE_WRONG.search("  X: module count    1083       1084       *** WRONG ***") is None:
        print("  SELF-TEST FAIL: the usage-checker line was not parsed")
        ok = False
    if COVERAGE_WRONG.search("theorem+lemma            doc 9843, measured 9844") is None:
        print("  SELF-TEST FAIL: the coverage-checker line was not parsed")
        ok = False
    if COUNTS_WRONG.search("Le\u0430n \u6a21\u5757\u603b\u6570   README \u5199 1076  \u5b9e\u6d4b 1077  MISMATCH") is None:
        print("  SELF-TEST FAIL: the counts-checker line was not parsed")
        ok = False
    if _variants("1,076") != {"1076", "1,076"}:
        print("  SELF-TEST FAIL: the grouped/plain variants are wrong")
        ok = False
    if _variants("1076") != {"1076", "1,076"}:
        print("  SELF-TEST FAIL: a plain number did not produce its grouped variant")
        ok = False
    print("SYNC COUNTS SELF-TEST: %s" % ("three parsers and the variants all behave" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
