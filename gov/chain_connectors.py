"""gov/chain_connectors.py -- which pairs of pipeline stages are actually CONNECTED by a theorem, and how
OLD that connection is.

## Why this file exists

Three rounds in a row I guessed at a missing connector in the objective's chain and found it already built:

  round 76  "the loop is not formalised"        -> `Runtime/LoopClosure.lean` IS the loop
  round 78  "the `none` branch is uncovered"    -> `decodeSpec_none_of_not_code`, `hop_verdict` item 1,
                                                   `relu_not_reversible`
  round 79  "extraction is not wired to repair" -> `RepairClosure.extract_after_repair`

That is a pattern: **my hypotheses about gaps are unreliable, because the tree is denser than my guesses.**
So this tool ENUMERATES the pairs instead of guessing them.

## What it measures

For every ORDERED PAIR of stages it counts theorems whose STATEMENT mentions a marker of each side. Two
deliberate choices:

  * statements only, not proofs -- a proof mentions whatever it needs, so proofs would manufacture
    connectors wherever two stages share a helper lemma;
  * whole-word matching -- otherwise `extract` matches `extractWith` and inflates every cell.

A zero in a non-adjacent cell usually means nothing (those stages are not supposed to meet directly). A zero
in an ADJACENT cell is the finding.

## What `--provenance` adds, and why it matters

A link can be CONNECTED and still rest entirely on code introduced moments ago. `3.3 repair -> 3.4 reinject`
turned out to have exactly three connectors, all authored in the two rounds before this tool grew the
provenance column -- so the link is real, but its support is not independent of the work that created it.

`--provenance` blames each connector's declaration line and reports, per adjacent link, how many of its
connectors predate the last `K` commits (`--recent`, default 30). A link with `old == 0` is flagged
`**FRESH-ONLY**`: not wrong, but it has no independent support older than the recent work.

Reading the flag honestly: a fresh-only link is a NOTE, not a defect. Proven theorems are proven. What it
says is that if a future round changes the receiving stage, nothing older than the recent commits will
notice.

## Interface

    python chain_connectors.py            # matrix + adjacent-link verdicts
    python chain_connectors.py --check    # gate: fail if any adjacent link is EMPTY
    python chain_connectors.py --list A B # the theorems behind one cell
    python chain_connectors.py --provenance [--recent K]
    python chain_connectors.py --self-test
"""

import argparse
import io
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from audit_definitional_proofs import DECL, _statement_end, _indent_of, _next_decl_indent  # noqa: E402
from tools.sorry_axiom_census import strip_comments  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LAT = os.path.join(ROOT, "Lattice")

# **The stages, named after the objective's own words, each with the markers the CLAUSES table already
# uses. Adding a marker is a claim that it names the stage -- keep the lists short and specific.**
STAGES = [
    ("1.1 data->token",    ["tokenize_detok", "CharToken", "tokenizeV"]),
    ("1.2 token->symbol",  ["SymToken", "decodePayload", "encodeForm"]),
    ("1.3 symbol->weight", ["compileToLayer", "compileSkel", "compileWith"]),
    ("1.4 weight->symbol", ["extract", "extractLayer", "extractWith"]),
    # **The first run reported `verify -> repair` and `reinject -> loop` as EMPTY. Both were artefacts of
    # the lexicon, not gaps: `RepairClosure.lean` states the verify/repair link using `AllSatisfied` and
    # `LayerSat`, and `VerificationLoop` states the reinject/loop link using `V.run`. A zero in this matrix
    # is a claim about MY WORDS until the tree's own words are in the list.**
    ("3.2 verify",         ["EpsSat", "PenaltyExact", "models", "agrees",
                            "AllSatisfied", "LayerSat", "satW", "Satisfies"]),
    ("3.3 repair",         ["Repair", "sqDistHalvingRepair", "repair"]),
    ("3.4 reinject",       ["reinject", "objective", "VerificationLoop"]),
    ("4 loop",             ["converges_within", "bidirRepair", "loop_end_sat",
                            "run", "iterate"]),
]


def _marker_re(words):
    return re.compile(r"\b(?:%s)\b" % "|".join(re.escape(w) for w in words))


def statements():
    """Yield (rel, name, line, statement_text) for every theorem/lemma in the mainline tree."""
    for root, _, fs in os.walk(LAT):
        if os.sep + "Reference" in root:
            continue
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace(os.sep, "/")
            try:
                src = io.open(p, "rb").read().decode("utf-8", errors="replace")
            except OSError:
                continue
            code = strip_comments(src)
            for m in DECL.finditer(code):
                name = m.group(1).split(".")[-1]
                end = _statement_end(code, m.end())
                if end is None:
                    continue
                # **Blame the line the NAME sits on, not the declaration's first character: the name is
                # unambiguous, and a leading attribute (`@[simp]`) would otherwise blame the wrong line.**
                line = code.count("\n", 0, m.start(1)) + 1
                yield rel, name, line, code[m.end():end - 2]


def measure():
    pats = [(label, _marker_re(words)) for label, words in STAGES]
    matrix = {(a, b): [] for a, _ in pats for b, _ in pats}
    total = 0
    for rel, name, line, stmt in statements():
        total += 1
        hit = [label for label, pat in pats if pat.search(stmt)]
        for a in hit:
            for b in hit:
                if a != b:
                    matrix[(a, b)].append((rel, name, line))
    return matrix, total


def recent_shas(k):
    r = subprocess.run(["git", "log", "-n", str(k), "--format=%H"], cwd=ROOT,
                       capture_output=True, text=True)
    return set(x.strip() for x in r.stdout.split("\n") if x.strip())


def blamed_sha(rel, line):
    r = subprocess.run(["git", "blame", "-L", "%d,%d" % (line, line), "--porcelain",
                        "--", "Lattice/" + rel], cwd=ROOT, capture_output=True, text=True)
    first = (r.stdout or "").split("\n")[0].strip()
    return first.split(" ")[0] if first else ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--check", action="store_true",
                    help="gate: fail if any adjacent chain link has no connecting theorem")
    ap.add_argument("--list", nargs=2, metavar=("A", "B"),
                    help="print the theorems whose statements mention both stages A and B")
    ap.add_argument("--provenance", action="store_true",
                    help="report how many connectors of each adjacent link predate the last K commits")
    ap.add_argument("--recent", type=int, default=30, help="K for --provenance (default 30)")
    args = ap.parse_args()

    if args.self_test:
        bad = 0
        r = _marker_re(["extract"])
        cases = [("extract W = some k", True), ("extractWith k f = 0", False),
                 ("Lattice.Core.IR.extract W", True), ("extractor thing", False)]
        for text, want in cases:
            if bool(r.search(text)) != want:
                print("  SELF-TEST FAIL: %r -> %s, want %s" % (text, bool(r.search(text)), want))
                bad += 1
        if _marker_re(["Repair"]).search(strip_comments("/- mention Repair here -/ x = 1")):
            print("  SELF-TEST FAIL: comment leaked into the statement scan")
            bad += 1
        print("  chain-connector self-test: %s" % ("ok" if bad == 0 else "%d FAILURES" % bad))
        return 0 if bad == 0 else 1

    matrix, total = measure()
    labels = [l for l, _ in STAGES]

    if args.list:
        a, b = args.list
        for want in (a, b):
            if want not in labels:
                print("  unknown stage %r; known: %s" % (want, ", ".join(labels)))
                return 2
        names = matrix[(a, b)]
        print("  %d theorem(s) state both %s and %s:" % (len(names), a, b))
        for rel, n, _ln in sorted(names):
            print("    %s :: %s" % (rel, n))
        return 0

    print("  statements scanned: %d" % total)
    print("  connector counts (theorem statements mentioning BOTH stages):")
    width = max(len(l) for l in labels) + 2
    print("  %-*s%s" % (width, "", "".join("%-12s" % l.split(". ", 1)[-1] for l in labels)))
    for a in labels:
        row = "".join("%-12d" % len(matrix[(a, b)]) if a != b else "%-12s" % "-" for b in labels)
        print("  %-*s%s" % (width, a, row))

    print("  adjacent pairs (the chain's own links):")
    empty = []
    for i in range(len(labels) - 1):
        a, b = labels[i], labels[i + 1]
        n = len(matrix[(a, b)])
        mark = "OK" if n else "**EMPTY**"
        print("    %-24s -> %-24s %4d  %s" % (a, b, n, mark))
        if not n:
            empty.append((a, b))
    print("  empty adjacent pairs: %d" % len(empty))

    if args.provenance:
        rec = recent_shas(args.recent)
        print("  connector provenance (a connector is OLD if its declaration predates the last %d"
              " commits):" % args.recent)
        for i in range(len(labels) - 1):
            a, b = labels[i], labels[i + 1]
            names = matrix[(a, b)]
            if not names:
                continue
            old = fresh = unknown = 0
            rows = []
            for rel, n, ln in sorted(names):
                sha = blamed_sha(rel, ln)
                if not sha:
                    unknown += 1
                    tag = "?"
                elif sha in rec:
                    fresh += 1
                    tag = "recent"
                else:
                    old += 1
                    tag = "old"
                rows.append((tag, rel, n, sha[:8]))
            flag = "  **FRESH-ONLY**" if old == 0 and fresh else ""
            print("    %-24s -> %-24s total %2d  old %2d  recent %2d  unknown %d%s"
                  % (a, b, len(names), old, fresh, unknown, flag))
            for tag, rel, n, sha in rows:
                print("        %-7s %s :: %s  (%s)" % (tag, rel, n, sha))

    if args.check:
        # **The gate is "no adjacent link may go empty". It cannot require a number of connectors -- one
        # is enough for a link to exist -- and it does not police non-adjacent cells, where two stages are
        # not supposed to meet. The lexicon above is part of the contract: widening it is a deliberate
        # change, the same way a baseline is.**
        if empty:
            print("  CHAIN CONNECTORS: %d adjacent link(s) have no connecting theorem: %s"
                  % (len(empty), ", ".join("%s->%s" % (a, b) for a, b in empty)))
            return 1
        print("  CHAIN CONNECTORS: every adjacent link has a connecting theorem (%d links)"
              % (len(labels) - 1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())