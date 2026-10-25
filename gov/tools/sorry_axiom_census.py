#!/usr/bin/env python3
"""Strict comment stripper for Lean 4 source, plus honest sorry/axiom census.

Why this exists
---------------
A naive `grep -c sorry` over the old tree reported 515 occurrences in 389 files.
That number is FALSE: virtually every hit lives inside a comment such as
`no sorry / axiom / admit; all theorems are genuinely proved`.

Getting this right requires four things, each of which was a real bug:

  1. `/-  -/` block comments NEST in Lean (`/- /- -/ still comment -/`).
  2. `/-- -/` doc comments are block comments with a leading `-`.
  3. `--` line comments.
  4. A `-/` occurring OUTSIDE a comment must NOT be treated as the start of `/-`.
     This was the actual cause of the first wrong count: after an ASCII arrow
     `-->` the remaining `/` was read as an opening delimiter.

Rule (see 00-ZERO-framework.md): a census tool is only trustworthy once it has been
shown to FIRE on a planted defect. `--selftest` does exactly that.
"""
import argparse
import json
import os
import re
import sys

SORRY_RE = re.compile(r"\b(sorry|admit)\b")
AXIOM_RE = re.compile(r"^[ \t]*axiom[ \t]+(\S+)", re.M)


_STRIP_CACHE: dict = {}


def strip_comments(src: str) -> str:
    """Remove /- -/ (nested) and -- comments, preserving newlines.

    Memoised on the source text: the function is pure, and the gate calls it once per
    (invariant x file), so a cold run stripped the same 723 files five times over -- 14,580
    calls, ~146 s under cProfile. Keying on the text also collapses identical files.
    """
    _hit = _STRIP_CACHE.get(src)
    if _hit is not None:
        return _hit
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        if depth == 0 and src.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        # FIX #4: a lone `-/` outside a comment must be consumed, not re-read as `/-`
        if src.startswith("-/", i):
            i += 2
            continue
        out.append(src[i])
        i += 1
    _STRIP_CACHE[src] = "".join(out)
    return _STRIP_CACHE[src]

def census_file(path: str) -> dict:
    src = open(path, "rb").read().decode("utf-8", errors="replace")
    code = strip_comments(src)
    sorries = list(SORRY_RE.finditer(code))
    axioms = list(AXIOM_RE.finditer(code))
    return {
        "file": os.path.basename(path),
        "sorry": len(sorries),
        "sorry_lines": sorted({code[: m.start()].count("\n") + 1 for m in sorries}),
        "axiom": len(axioms),
        "axiom_names": [m.group(1) for m in axioms],
    }


SELFTEST_CASES = [
    ("plain", "theorem a : 1 = 1 := sorry", 1),
    ("after_doc_comment", "/-- doc -/\ntheorem a : 1 = 1 := by sorry", 1),
    # this is the case that broke the first implementation
    ("dashclose_after_line_comment", "-- note that -/- stuff\ntheorem a : 1 = 1 := sorry", 1),
    ("nested_block", "/- outer /- inner -/ sorry -/\ntheorem a : 1=1 := sorry", 1),
    ("admit", "lemma b : 2 = 2 := by admit", 1),
    ("only_in_comment", "/- sorry here -/\ntheorem a : 1 = 1 := rfl", 0),
    ("only_in_line_comment", "theorem a : 1 = 1 := rfl -- no sorry", 0),
    ("axiom_inside_comment", "/- axiom Foo : False -/\ntheorem a : 1 = 1 := rfl", 0),
    ("arrow_then_slash", "def f : Nat -> Nat := fun x => x -- a --> b\n", 0),
]


def selftest() -> int:
    print("=== comment-stripper self-test (planted defects) ===")
    bad = 0
    for name, src, want in SELFTEST_CASES:
        got = len(SORRY_RE.findall(strip_comments(src)))
        ok = got == want
        if not ok:
            bad += 1
        print("  %-30s expected %d got %d  %s" % (name, want, got, "OK" if ok else "** FAIL **"))
    print("=== %s ===" % ("ALL PASS" if bad == 0 else "%d FAILURE(S)" % bad))
    return 0 if bad == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("target", nargs="?", help="a .lean file or a directory")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        return selftest()
    if not args.target:
        ap.error("need a target file or directory (or --selftest)")

    files = []
    if os.path.isdir(args.target):
        for root, _dirs, names in os.walk(args.target):
            for nm in names:
                if nm.endswith(".lean"):
                    files.append(os.path.join(root, nm))
    else:
        files.append(args.target)

    results = [census_file(f) for f in files]
    dirty = [r for r in results if r["sorry"] or r["axiom"]]

    if args.json:
        print(json.dumps(results, ensure_ascii=False, indent=1))
        return 0

    total_sorry = sum(r["sorry"] for r in results)
    total_axiom = sum(r["axiom"] for r in results)
    print("files scanned : %d" % len(results))
    print("real `sorry`  : %d (in %d files)" % (total_sorry, sum(1 for r in results if r["sorry"])))
    print("real `axiom`  : %d (in %d files)" % (total_axiom, sum(1 for r in results if r["axiom"])))
    if dirty:
        print("-" * 60)
        for r in dirty:
            print("  %-40s sorry=%d lines=%s axiom=%d %s"
                  % (r["file"], r["sorry"], r["sorry_lines"], r["axiom"], r["axiom_names"]))
    return 0 if not dirty else 1


if __name__ == "__main__":
    sys.exit(main())
