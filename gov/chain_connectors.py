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
UNREGISTERED_BUDGET = 0

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
    # Round 1108: the 1.1->1.2 seam (four connectors, all terminal). Each reason was written after reading the
    # statement AND its proof shape.
    "E1Bridge_cons":
        "definitional unfolding of the bridge's cons case, proved by `rfl`. A consumer that needs it unfolds "
        "the definition itself, so there is nothing to feed.",
    "E1BridgeNoSep_cons":
        "the same for the `sep`-dropping bridge: a `rfl` equation. Terminal for the same reason.",
    "E8_source_count_exactly_one":
        "an ASSERTION ABOUT THE TREE, not a step: it conjoins 'a source exists, with an explicit witness' and "
        "'there is no source on the L2->L3 hop'. Facts of this shape are conclusions no downstream reads.",
    "d41_L1Bridge_not_injective":
        "a NEGATION (`not injective`): a separation theorem. Negations are terminal by nature -- nothing uses "
        "'it cannot be' as an input to a construction.",
    "e2e_vacuous_composition":
        "compile soundness restated with an UNUSED (ts : List SymToken). Its point is that the second hop does "
        "not consult the token list -- a non-dependency witness, terminal by design.",
    "e2e_extract_hypothesis_is_not_load_bearing":
        "the same statement with an unused `Extract ts cs` hypothesis. The NAME is the claim: that hypothesis "
        "carries no weight in this hop.",
    "extract_to_weights":
        "again the same conclusion with an unused `Extract` hypothesis, in the extraction-direction file -- a "
        "third non-dependency witness.",
    "e2e_contribution_of_L1L2":
        "an assertion about the chain's composition (what `toSegs ts` yields, and the uniqueness of `Extract`'s "
        "output). A conclusion about the whole, not a step.",
    "e2e_loss_compound":
        "an existence conjunction: two tokens collide, two constraint sets give different layers. It states "
        "that losses COMPOUND; nothing downstream consumes that fact.",
    "E8_load_bearing_summary":
        "a summary of which maps do and do not merge: negation for compileToLayer and encode, positive for "
        "E8CollapseLayer. A summary is terminal by construction.",
    "extract_after_zero_repair":
        "round 1102's sibling of extract_after_repair: an all-zero layer's extracted constraints are satisfied "
        "for ANY input. Nothing downstream reads it -- it exists to show the zero instance supports a "
        "post-repair extraction statement, which is a conclusion, not a step.",
    # Round 1136: the bridge that makes 3.2 (verify) and 3.3 (repair) share ONE predicate. Before it, `EpsSat`
    # and `Repair` never appeared in the same statement -- the seam had nothing to connect.
    "eps_repair_requires_descent":
        "THE bridge: if a Repair's Sat IS EpsSat, then off the epsilon-set its measure strictly descends. This is the "
        "one statement that mentions both worlds, which is why it IS the 3.2->3.3 connector. Terminal by nature -- a "
        "criterion identity is what the loop needs, not a step something composes.",
    "eps_repair_not_constant_measure":
        "the LIMIT of that bridge, proved: if epsilon-satisfaction is not universal, the measure cannot be constant. So "
        "'define an epsRepair' cannot be done by a `def` alone -- the epsilon criterion supplies a predicate, not a "
        "descent structure. A negative result, hence terminal.",
    "closed_loop_reinject_vanishes_from_within":
        "a DERIVATION: it re-proves the original vanishing theorem as the epsilon = 0 case of the tolerance version. "
        "Stated so the GENERALISATION is visible in the tree rather than living in a commit message. Terminal -- it "
        "exists to show the relation, and `closed_loop_reinject_within` is what a consumer would cite.",
    "no_unsatisfiable_objective":
        "round 1133 s statement that NO objective is unsatisfiable: it refutes the hypothesis of "
        "`no_loop_fixes_unsatisfiable` using round 1094 s `sat_not_empty`. A refutation of a premise is a conclusion "
        "-- nothing downstream acts on it, which is exactly why the theorem it comments on is vacuous.",
    # Round 1110: the 1.4->3.2 seam, grouped by conclusion SHAPE (verified by reading, not by name).
    "compile_extract_end_to_end": "a RESTATEMENT of the round-trip semantics lemma at the module that owns the definition: the tree's convention of quoting a fact where it is used. Its content IS the semantics equivalence, so nothing downstream reads it; terminal by construction.",
    "compile_extract_semantics_closed": "a RESTATEMENT of the round-trip semantics lemma at the module that owns the definition: the tree's convention of quoting a fact where it is used. Its content IS the semantics equivalence, so nothing downstream reads it; terminal by construction.",
    "roundtrip_preserves_semantics": "a RESTATEMENT of the round-trip semantics lemma at the module that owns the definition: the tree's convention of quoting a fact where it is used. Its content IS the semantics equivalence, so nothing downstream reads it; terminal by construction.",
    "extract_compile_semantically_equal": "a RESTATEMENT of the round-trip semantics lemma at the module that owns the definition: the tree's convention of quoting a fact where it is used. Its content IS the semantics equivalence, so nothing downstream reads it; terminal by construction.",
    "satisfies_iff_extractLayer": "a RESTATEMENT of the round-trip semantics lemma at the module that owns the definition: the tree's convention of quoting a fact where it is used. Its content IS the semantics equivalence, so nothing downstream reads it; terminal by construction.",
    "rt1_is_instance_of_branch_B":
        "one of a PAIR with rt1_matches_existing: the two have the same conclusion, one wrapping the other. The wrapper exists so the equivalence can be cited under the name the vacuity argument uses.",
    "rt1_matches_existing":
        "the other half of that pair; see rt1_is_instance_of_branch_B.",
    "activated_extract_cannot_repair":
        "a NEGATION: no activated-relu zero makes compile-then-extract satisfy the constraints. Separation theorems are terminal by nature.",
    "not_agrees_of_disagreement":
        "a NEGATION: disagreement at one coordinate refutes agreement. Terminal for the same reason.",
    "honesty_register":
        "a CONJUNCTION (the round-trip identity plus an equivalence-of-equivalences). A register of what is true, not a step.",
    "structured_init_complete":
        "a THREE-WAY conjunction about structuredInit: soundness, the converse, and extractLayer recovery. A completeness summary.",
    "parse_chain_summary":
        "a summary of the parseWithRelations chain. Terminal by construction.",
    "models_structure":
        "an IMPLICATION (models -> extract = some k): one direction of the model/extract relationship. A direction is a conclusion, not a step.",
    "layerZeroRepair_extract":
        "round 1103 its instance of extract_after_repair_weak on the zero repair. It exists to BE that seam s live connector; nothing further consumes an extraction guarantee.",
    "approx_ladder_forward":
        "one direction of the approximation ladder: satSym -> satW plus the round-trip distance bound. A forward fact, terminal.",
    "roundingLadder_forward":
        "the same for the rounding ladder. Terminal for the same reason.",
    # Round 1112: the three extractWith_* lemmas that are genuinely unused (the other three are the summary
    # and the base lemmas it consumes, which round 1111 showed are "used in place", not dead).
    "extractWith_collision":
        "an EQUATION: when two tensors share an id, reading one position returns the other id s cell. A base fact about the encoding, not a step -- nothing composes it.",
    "extractWith_overwrite_footprint":
        "a CONJUNCTION of extractWith_overwrite and extractWith_overwrite_local: what an overwrite returns at its own position and nowhere else. Those two are its content, so the summary adds packaging, not a fact.",
    "extractWith_spec":
        "a CONJUNCTION of extractWith_compileWith and extractWith_absent: extract after compile is the identity on the skeleton s tensors and zero elsewhere. A specification of the pair, i.e. an endpoint.",
    # Round 1113: the compile_extract_* trio -- all three are restatements of the round-trip PAIR.
    "compile_extract_invertible_pair":
        "a CONJUNCTION of Function.LeftInverse and Function.RightInverse for the same pair, assembled from the two lemmas that already state each direction. A summary.",
    "compile_extract_mutually_refines":
        "a CONJUNCTION of the two fibreRefines statements: each side refines the other. A structural summary of what the round trip means at the fibre level.",
    "compile_extract_weight_side":
        "a RESTATEMENT on the weight side: zero-output is preserved by compile-then-extract, obtained by rewriting with compileToLayer_extractLayer. Its content is that lemma, quoted where the weight reader needs it.",
    # Round 1114: the inverse/fixpoint family. FIVE names, ONE equation -- except the last, which
    # characterises rather than restates.
    "extractLayer_leftInverse": 'ONE EQUATION IN ANOTHER VOCABULARY: `compileToLayer (extractLayer ls) = ls` and its converse. Four of the five theorems here are that single content in four forms -- Function.LeftInverse, Function.RightInverse, the raw equation, and a re-export for the vacuity file. Each form exists because a different consumer vocabulary needs it; none is a step.',
    "extractLayer_rightInverse": 'ONE EQUATION IN ANOTHER VOCABULARY: `compileToLayer (extractLayer ls) = ls` and its converse. Four of the five theorems here are that single content in four forms -- Function.LeftInverse, Function.RightInverse, the raw equation, and a re-export for the vacuity file. Each form exists because a different consumer vocabulary needs it; none is a step.',
    "rt1_leftInverse": 'ONE EQUATION IN ANOTHER VOCABULARY: `compileToLayer (extractLayer ls) = ls` and its converse. Four of the five theorems here are that single content in four forms -- Function.LeftInverse, Function.RightInverse, the raw equation, and a re-export for the vacuity file. Each form exists because a different consumer vocabulary needs it; none is a step.',
    "compiled_roundTrip_fixed": 'ONE EQUATION IN ANOTHER VOCABULARY: `compileToLayer (extractLayer ls) = ls` and its converse. Four of the five theorems here are that single content in four forms -- Function.LeftInverse, Function.RightInverse, the raw equation, and a re-export for the vacuity file. Each form exists because a different consumer vocabulary needs it; none is a step.',
    "compiled_roundTrip_fixed_iff":
        "a CHARACTERISATION, not a restatement: for a single layer, being a fixpoint of compile-then-extract is equivalent to being the image of some constraint. It adds information the four restatements do not -- still a conclusion, so terminal, but the only member of this family that is not one equation re-spelled.",
    # Round 1115: the loop-property family -- four idempotence statements plus one locality restatement.
    "adjunction_triangle_idem": "IDEMPOTENCE: the loop is a projection, so two applications equal one. Derived from the round-trip equation by rewriting. An idempotence STATEMENT is a conclusion -- nothing composes 'is idempotent' into a next step.",
    "closed_loop_idempotent": "IDEMPOTENCE: the loop is a projection, so two applications equal one. Derived from the round-trip equation by rewriting. An idempotence STATEMENT is a conclusion -- nothing composes 'is idempotent' into a next step.",
    "loop_is_criterion_not_repair": "IDEMPOTENCE: the loop is a projection, so two applications equal one. Derived from the round-trip equation by rewriting. An idempotence STATEMENT is a conclusion -- nothing composes 'is idempotent' into a next step.",
    "adjunction_triangle_object":
        "a CONJUNCTION of the two round-trip equations themselves, boxed for the categorical reading. The box is the point (it names the adjunction triangle), but its content is the pair already stated.",
    "loop_preserves_others":
        "LOCALITY of an overwrite at another coordinate -- the same content as extractWith_overwrite_local, under a second name in the same file. A base fact; nothing composes it.",
    # Round 1116: the last nine, all terminal. Categorised by shape, reasons written per shape.
    "compileWith_roundtrip": 'a SUMMARY: a top-level conjunction of facts already stated elsewhere (round-trip / extraction / coding). Nothing consumes a conjunction of known facts; it exists so one citation carries the whole picture.',
    "recover_is_load_bearing": 'a SUMMARY: a top-level conjunction of facts already stated elsewhere (round-trip / extraction / coding). Nothing consumes a conjunction of known facts; it exists so one citation carries the whole picture.',
    "s02_list_realization_witness_is_mechanical": 'a SUMMARY: a top-level conjunction of facts already stated elsewhere (round-trip / extraction / coding). Nothing consumes a conjunction of known facts; it exists so one citation carries the whole picture.',
    "layer_partial_section_never_fails": 'a SUMMARY: a top-level conjunction of facts already stated elsewhere (round-trip / extraction / coding). Nothing consumes a conjunction of known facts; it exists so one citation carries the whole picture.',
    "reinject_restores":
        "a RESTORATION statement: extracting from the compiled weights returns the synthesised data. A round-trip fact stated in the data vocabulary; nothing composes it.",
    "compiled_weights_extract": 'a ROUND-TRIP COROLLARY: a direct consequence of compile-then-extract being the identity. Its content is the round-trip equation, specialised to one direction; it is a conclusion, not a step.',
    "extract_witness_is_preimage": 'a ROUND-TRIP COROLLARY: a direct consequence of compile-then-extract being the identity. Its content is the round-trip equation, specialised to one direction; it is a conclusion, not a step.',
    "verify_loop_stable_on_image":
        "IDEMPOTENCE on the image: applying compile-then-extract to a compiled layer changes nothing. The same content as closed_loop_idempotent, stated on the other side of the pair.",
    "unfaithful_iff_extract_ne":
        "a CHARACTERISATION: unfaithfulness is equivalent to extraction disagreeing with the corpus. An iff that names what unfaithfulness IS -- terminal, and the only member of this last group that adds a definition rather than restating one.",
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


def used_in_place(rel, name):
    """Occurrences of `name` inside its OWN file, minus the declaration itself.

    **Round 1111: the same distinction the objective map needed in round 1092.** `chain_users` excludes the definer
    by design (a theorem does not consume itself), but that also hides the case where the definer's file USES it --
    `extractWith_absent` is consumed by `extractWith_spec` three lines down, and calling that 'dead' is the
    'unused vs used in place' conflation all over again.

    A global corpus is built per call here rather than threaded through, because this file is a report and the
    clarity is worth more than the microseconds.
    """
    return len(re.findall(r"\b%s\b" % re.escape(name), chain_corpus().get(rel, ""))) - 1


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
            dead = [n for rel, n, _ln in sorted(names)
                    if not chain_users(CC, n, rel) and used_in_place(rel, n) <= 0]
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
                if (not chain_users(CC2, n2, rel2) and used_in_place(rel2, n2) <= 0
                        and n2 not in TERMINAL_CONNECTORS):
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