# -*- coding: utf-8 -*-
"""gov/audit_reversibility_coverage.py -- which encoders have which reversibility evidence.

## Why this exists

`PLAN-STAGES.md` O-3 says "more reversibility instances". Twice now I guessed what was missing from the
ledger and was wrong (round 972: O-2 was mis-recorded; round 977: the data<->token hop turned out to be fully
covered). So the question "which hop still lacks its evidence?" must be MEASURED, not recalled.

## What it measures, and what it deliberately does not

For every `theorem`/`lemma` it classifies, BY NAME AND STATEMENT SHAPE, into three kinds:

  roundtrip   the decode/encode round trip, or the "<x>_code" form
  faithful    the reverse direction: "decoding yields only real codes"
  loss        a refutation naming what is lost

and groups them by the ENCODER identifier that appears in the statement.

=> the classification is HEURISTIC. It is a MAP, not a proof: it tells you where to look. The document
`REVERSIBILITY-MAP.md` records the curated reading of its output, and `--check` guards the curated names.

## Contract card

semantics      scan Lattice/**/*.lean, classify reversibility theorems, group by encoder
preconditions  the tree is checked out; `tools/lean_source.strip_comments` is importable
failure        exit 1 if a curated name in REVERSIBILITY-MAP.md does not exist as a declaration
boundary       name/shape heuristics only -- it never decides semantic equivalence
extension      add a curated row to REVERSIBILITY-MAP.md and a case to CASES
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from tools.lean_source import strip_comments  # noqa: E402

LAT = os.path.join(ZERO, "Lattice")
DOC = os.path.join(ZERO, "REVERSIBILITY-MAP.md")

DECL = re.compile(r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?]*)", re.M)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")


def declarations():
    """(name, file, statement-snippet) for every theorem/lemma, comments stripped."""
    out = []
    for dirpath, dirs, files in os.walk(LAT):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            src = strip_comments(io.open(path, encoding="utf-8", errors="replace").read())
            for m in DECL.finditer(src):
                tail = src[m.end():m.end() + 400]
                cut = tail.find(":=")
                stmt = tail[:cut] if cut >= 0 else tail[:200]
                out.append((m.group(2), os.path.relpath(path, ZERO).replace(os.sep, "/"),
                            " ".join(stmt.split())))
    return out


def kind(name, stmt):
    """Classify by name AND statement shape.

    The name alone cannot tell "recovered exactly" from "recovered only in shape":
    `decode_encode_shape d : exists d', decode (encode d) = some d' ∧ d'.corpus.length = d.corpus.length ∧ d'.indices = []`
    is a LOSS statement wearing a round trip's name. The distinguishing mark is the existential
    plus a non-trivial conjunct, so that is what decides.
    """
    low = name.lower()
    if low.endswith("_faithful") or "faithful" in low:
        return "faithful"
    if any(t in low for t in ("_fails", "not_injective", "lost", "_drops", "not_absorbable",
                              "no_roundtrip", "_breaks")):
        return "loss"
    shape_only = ("∃" in stmt) and ("∧" in stmt)
    if "roundtrip" in low or "decode_encode" in low or "encode_decode" in low:
        return "shape" if shape_only else "roundtrip"
    # the "_code" form is the round trip written as "decode (code x) = some x"; but
    # "…_none_of_not_code" also ENDS with "_code" and is the FAITHFUL form, so exclude it
    if low.endswith("_code") and "not_code" not in low and "none_of" not in low:
        return "shape" if shape_only else "roundtrip"
    if stmt.lstrip().startswith("\u00ac") or stmt.lstrip().startswith("not "):
        return "loss"
    return None


ENCODER_HINT = re.compile(r"\b([A-Za-z_][A-Za-z0-9_']*(?:Code|code|encode|Encode|compile|Compile|"
                          r"convert|Convert|Bridge|bridge|tokenize|Tokenize))\b")


def coverage(decls):
    """encoder -> {'roundtrip': [names], 'faithful': [...], 'loss': [...]}."""
    table = {}
    for name, _f, stmt in decls:
        k = kind(name, stmt)
        if k is None:
            continue
        encs = set(ENCODER_HINT.findall(stmt)) or set(ENCODER_HINT.findall(name))
        for e in encs:
            table.setdefault(e, {"roundtrip": [], "faithful": [], "loss": [], "shape": []})[k].append(name)
    return table


def curated_rows():
    """Rows of REVERSIBILITY-MAP.md: (encoder, roundtrip, faithful, loss) with '-' for none."""
    if not os.path.exists(DOC):
        return []
    rows = []
    for line in io.open(DOC, encoding="utf-8").read().split("\n"):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 4 or cells[0].startswith(":") or cells[0] in ("encoder", ""):
            continue
        if not cells[0].startswith("`"):
            continue
        rows.append((cells[0].strip("`"), [x.strip("` ") for x in cells[1].split(",") if x.strip()],
                     [x.strip("` ") for x in cells[2].split(",") if x.strip()],
                     [x.strip("` ") for x in cells[3].split(",") if x.strip()]))
    return rows


def check():
    decls = declarations()
    have = {n for n, _f, _s in decls}
    rows = curated_rows()
    if not rows:
        print("  REVERSIBILITY MAP: no curated rows found in REVERSIBILITY-MAP.md")
        return False
    bad = 0
    for enc, rt, fa, lo in rows:
        for group, names, label in (("roundtrip", rt, rt), ("faithful", fa, fa), ("loss", lo, lo)):
            for n in names:
                if n in ("-", ""):
                    continue
                if n not in have:
                    print("  MISSING %-40s (%s, listed under encoder %s)" % (n, group, enc))
                    bad += 1
    print("  REVERSIBILITY MAP: %d curated row(s), %d declaration(s) checked, %d missing"
          % (len(rows), sum(len(a) + len(b) + len(c) for _e, a, b, c in rows), bad))
    return bad == 0


def report():
    decls = declarations()
    table = coverage(decls)
    print("  encoder                                    roundtrip shape faithful loss")
    print("  " + "-" * 82)
    for enc in sorted(table):
        c = table[enc]
        if not (c["roundtrip"] or c["faithful"] or c["loss"] or c["shape"]):
            continue
        print("  %-42s %5d %5d %6d %4d" % (enc[:42], len(c["roundtrip"]), len(c["shape"]), len(c["faithful"]), len(c["loss"])))
    print("  --- encoders with a round trip but NO faithful and NO loss theorem (candidate gaps) ---")
    gaps = [e for e in sorted(table)
            if table[e]["roundtrip"] and not table[e]["faithful"] and not table[e]["loss"] and not table[e]["shape"]]
    for e in gaps:
        print("  GAP %-50s roundtrip: %s" % (e[:50], ", ".join(sorted(set(table[e]["roundtrip"]))[:3])))
    print("  %d candidate gap(s)" % len(gaps))


CASES = [
    ("decode_encode", "roundtrip"),
    ("decodeSkeletonStrict_faithful", "faithful"),
    ("encode_drop_b_roundtrip_fails", "loss"),
    ("decodeSkeletonStrict_none_of_not_code", None),
]


def self_test():
    ok = True
    for name, want in CASES:
        got = kind(name, "")
        if got != want:
            print("  FAIL classify %-42s got %r want %r" % (name, got, want))
            ok = False
    if kind("anything", "\u00ac Function.Injective f") != "loss":
        print("  FAIL a leading negation in the statement must classify as loss")
        ok = False
    print("  audit_reversibility_coverage self-test: %s" % ("PASS" if ok else "FAIL"))
    return ok


def main():
    args = sys.argv[1:]
    if "--self-test" in args:
        return 0 if self_test() else 1
    if "--report" in args:
        report()
        return 0
    return 0 if check() else 1


if __name__ == "__main__":
    sys.exit(main())
