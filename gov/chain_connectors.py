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


#: **连接器在链内没有消费者，但那是**按构造**的——每条附理由。**
#:
#: **Round 1107. 一个没有消费者的连接器要么是 (a) 终态结论——下游不读它；要么是 (b) 缺口。
#: ⇒ 两者在表里长得一样。⇒ 本表是有意的 (a) 的登记处，而门禁只对**相邻接缝**生效：
#: 非相邻的格子本就不应相遇，故它们的 0 不是对链的断言。**
#: **Round 1107: how many dead connectors on ADJACENT seams are still UNREGISTERED.**
#:
#: The gate forbids this number from GROWING; each round that adjudicates a seam lowers it. It exists because a
#: rule that demanded all of them at once could not be adopted -- the 1.4->3.2 seam alone has 17, and writing
#: seventeen unread reasons is exactly the invention this file's disciplines forbid. A budget makes the state
#: visible and monotone instead of pretending it is empty.
UNREGISTERED_BUDGET = 69

TERMINAL_CONNECTORS = {
    "twoSlopeLoop_objective_vanishes":
        "round 1085's instance of `closed_loop_reinject_vanishes` on the artifact payload: it states that the "
        "defect is zero at the loop's end. Nothing in the tree READS a defect value, so there is no downstream "
        "step for it to feed -- it is that seam's conclusion, not a missing link.",
    "extract_after_repair":
        "requires `hSat : forall ls, R.Sat ls <-> LayerSat cs ls` -- an EQUIVALENCE between the repair's verdict "
        "and zero-output. A verdict can normally be shown to IMPLY that, not to be equivalent to it, so this "
        "theorem cannot be applied to any instance in the tree (round 1103 measured this and supplied the "
        "one-directional sibling that IS applied). Dead because its premise is unattainable here.",
    "carrier_covers_two_segments_plus_one_direction":
        "a SUMMARY: a conjunction of compile soundness, the extraction round trip and repair termination. "
        "Nothing consumes a summary, and that is a property of what it is (round 1104 renamed it so the name "
        "stops claiming more than the statement proves).",
}



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
            # **Round 1106: an example's theorems are demonstrations, not chain facts.** Counting them made four
            # Usage/-defined theorems look "dead" (two of the three in the 3.3->3.4 seam) -- a metric artefact,
            # not a finding. Round 1091 stopped `Usage/` counting as a CONSUMER; this stops it as a PRODUCER.
            if rel.startswith("Usage/"):
                continue
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


def chain_corpus():
    """Comment-STRIPPED sources, so a docstring mention does not count as a consumer.

    **Round 1098: added because `--provenance` alone was read as a liveness measure and is not one.** It reports
    when a connector was WRITTEN. A connector can be a year old and still have live consumers, or two days old
    with none. Rounds 1080 and 1097 both read "old" as "disconnected" -- the same one-number-two-meanings error the
    objective map had with `Usage/` (round 1091).
    """
    out = {}
    for root, _, fs in os.walk(LAT):
        if os.sep + "Reference" in root:
            continue
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            fp = os.path.join(root, f)
            rel = os.path.relpath(fp, LAT).replace(os.sep, "/")
            try:
                out[rel] = strip_comments(io.open(fp, "rb").read().decode("utf-8", errors="replace"))
            except OSError:
                continue
    return out


def chain_users(corpus, name, definer):
    """Files that USE `name` inside the chain: not its definer, not `Usage/`.

    An example is a demonstration, not a consumer -- the judgement round 1091 made for the objective map.
    """
    rx = re.compile(r"\b%s\b" % re.escape(name))
    return [rel for rel, src in corpus.items()
            if rel != definer and not rel.startswith("Usage/") and rx.search(src)]


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
        CC = chain_corpus()
        rec = recent_shas(args.recent)
        print("  connector provenance (a connector is OLD if its declaration predates the last %d"
              " commits):" % args.recent)
        for i in range(len(labels) - 1):
            a, b = labels[i], labels[i + 1]
            names = matrix[(a, b)]
            if not names:
                continue
            old = fresh = unknown = pending = 0
            rows = []
            for rel, n, ln in sorted(names):
                sha = blamed_sha(rel, ln)
                if not sha:
                    unknown += 1
                    tag = "?"
                elif set(sha) == {"0"}:
                    # **An UNCOMMITTED line blames to the all-zero sha. It is neither old nor recent: it is
                    # not in the record yet, and calling it "old" let the work under review count as its own
                    # support -- which is exactly how this was found.**
                    pending += 1
                    tag = "pending"
                elif sha in rec:
                    fresh += 1
                    tag = "recent"
                else:
                    old += 1
                    tag = "old"
                rows.append((tag, rel, n, sha[:8]))
            flag = "  **FRESH-ONLY**" if old == 0 and fresh else ""
            print("    %-24s -> %-24s total %2d  old %2d  recent %2d  pending %d  unknown %d%s"
                  % (a, b, len(names), old, fresh, pending, unknown, flag))
            # **Round 1098: liveness is a SECOND, independent number.** `live` counts connectors with at least
            # one chain-internal consumer; `dead` names those with none. Printing both side by side makes it
            # impossible to read "old" as "disconnected" without seeing the other column.
            dead = [n for rel, n, _ln in sorted(names) if not chain_users(CC, n, rel)]
            live = len(names) - len(dead)
            print("      live %d/%d connectors have a chain-internal consumer%s"
                  % (live, len(names),
                     ("; NO CONSUMER: " + ", ".join(dead)) if dead else ""))
            for tag, rel, n, sha in rows:
                print("        %-7s %s :: %s  (%s)" % (tag, rel, n, sha))

    if args.check:
        # **The gate is "no adjacent link may go empty". It cannot require a number of connectors -- one
        # is enough for a link to exist -- and it does not police non-adjacent cells, where two stages are
        # not supposed to meet. The lexicon above is part of the contract: widening it is a deliberate
        # change, the same way a baseline is.**
        # **Round 1107: a dead connector on an ADJACENT seam must be registered in TERMINAL_CONNECTORS.**
        # Two different questions live here: the age column asks WHEN a connector was written, the liveness
        # column asks whether the chain USES it. This third check asks whether the absence of a user is
        # DELIBERATE -- without it, `dead` grows silently and every round rediscovers the same zeros.
        CC2 = chain_corpus()
        dead_adj = []
        for i2 in range(len(labels) - 1):
            a2, b2 = labels[i2], labels[i2 + 1]
            for rel2, n2, _ln2 in sorted(matrix[(a2, b2)]):
                if not chain_users(CC2, n2, rel2) and n2 not in TERMINAL_CONNECTORS:
                    dead_adj.append((a2, b2, n2))
        unreg = [x for x in dead_adj if x[2] not in TERMINAL_CONNECTORS]
        if unreg:
            print("  DEAD CONNECTORS ON ADJACENT SEAMS WITH NO REASON: %d (budget %d)"
                  % (len(unreg), UNREGISTERED_BUDGET))
            for a2, b2, n2 in unreg:
                print("    %s -> %s :: %s" % (a2, b2, n2))
        if len(unreg) > UNREGISTERED_BUDGET:
            print("  The budget grew: adjudicate a seam or register a reason before adding a dead connector.")
            return 1

        if empty:
            print("  CHAIN CONNECTORS: %d adjacent link(s) have no connecting theorem: %s"
                  % (len(empty), ", ".join("%s->%s" % (a, b) for a, b in empty)))
            return 1
        print("  CHAIN CONNECTORS: every adjacent link has a connecting theorem (%d links)"
              % (len(labels) - 1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())