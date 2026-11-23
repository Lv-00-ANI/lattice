"""gov/chain_connectors.py -- which pairs of pipeline stages are actually CONNECTED by a theorem.

## Why this file exists

Three rounds in a row I guessed at a missing connector in the objective's chain and found it already
built:

  round 76  "the loop is not formalised"        -> `Runtime/LoopClosure.lean` IS the loop
  round 78  "the `none` branch is uncovered"    -> `decodeSpec_none_of_not_code`, `hop_verdict` item 1,
                                                   `relu_not_reversible`
  round 79  "extraction is not wired to repair" -> `RepairClosure.extract_after_repair`

That is a pattern, not bad luck: **my hypotheses about gaps are unreliable, because the tree is denser
than my guesses about it.** The productive method is therefore not to guess a gap but to ENUMERATE the
pairs and look at the empty cells.

## What it measures

The objective's chain has named stages. For every ORDERED PAIR of stages (A, B) this counts the theorems
whose STATEMENT mentions a marker of A and a marker of B. A pair with 0 is a place where the chain is
described at both ends but no theorem says the two ends meet.

Two deliberate choices, both learned from earlier instruments in this repo:

1. **Statements only, not proofs.** A proof mentions whatever it needs; a statement is the contract. Using
   proofs would report a connector wherever two stages happen to share a lemma.
2. **Exact whole-word marker matches.** Substring matching would let `extract` match `extractWith` and
   inflate every cell.

## Reading the output

    `A -> B` is the count for "theorem mentioning A and B". The chain is `data -> token -> symbol -> weight`
    forward and `weight -> symbol -> verify -> repair -> reinject` backward, so the cells worth staring at
    are (stage i, stage i+1). A zero there is the finding; a zero elsewhere usually is not, because those
    two stages are not supposed to meet directly.

`--self-test` pins the marker matching, including the whole-word rule.
"""

import argparse
import io
import os
import re
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
    # **The first run of this matrix reported `verify -> repair` and `reinject -> loop` as EMPTY. Both
    # were artefacts of the lexicon, not gaps: `RepairClosure.lean` states the verify/repair link using
    # `AllSatisfied` and `LayerSat`, and `VerificationLoop` states the reinject/loop link using `V.run`.
    # A zero in this matrix is a claim about MY WORDS until the tree's own words are in the list.**
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
    """Yield (rel, name, statement_text) for every theorem/lemma in the mainline tree.

    The statement is everything between the declaration's name and its proof's `:=`. Comments are
    stripped, so a docstring cannot create a connector.
    """
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
                stop = _next_decl_indent(code[end:], _indent_of(code, m.start()))
                yield rel, name, code[m.end():end - 2]


def measure():
    pats = [(label, _marker_re(words)) for label, words in STAGES]
    matrix = {(a, b): [] for a, _ in pats for b, _ in pats}
    total = 0
    for rel, name, stmt in statements():
        total += 1
        hit = [label for label, pat in pats if pat.search(stmt)]
        for a in hit:
            for b in hit:
                if a != b:
                    matrix[(a, b)].append((rel, name))
    return matrix, total


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--pairs", action="store_true", help="list the theorems for each empty adjacent pair")
    ap.add_argument("--check", action="store_true",
                    help="gate: fail if any adjacent chain link has no connecting theorem")
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
        # a comment must not create a connector: strip_comments then match
        if _marker_re(["Repair"]).search(strip_comments("/- mention Repair here -/ x = 1")):
            print("  SELF-TEST FAIL: comment leaked into the statement scan")
            bad += 1
        print("  chain-connector self-test: %s" % ("ok" if bad == 0 else "%d FAILURES" % bad))
        return 0 if bad == 0 else 1

    matrix, total = measure()
    labels = [l for l, _ in STAGES]
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
    if args.pairs:
        for a, b in empty:
            print("    no theorem states both %s and %s" % (a, b))
    if args.check:
        # **The gate is "no adjacent link may go empty". It cannot require a number of connectors --
        # one is enough for a link to exist -- and it does not police non-adjacent cells, where two
        # stages are not supposed to meet. The lexicon above is part of the contract: widening it is a
        # deliberate change, the same way a baseline is.**
        if empty:
            print("  CHAIN CONNECTORS: %d adjacent link(s) have no connecting theorem: %s"
                  % (len(empty), ", ".join("%s->%s" % (a, b) for a, b in empty)))
            return 1
        print("  CHAIN CONNECTORS: every adjacent link has a connecting theorem (%d links)"
              % (len(labels) - 1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())