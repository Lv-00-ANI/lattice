"""gov/check_ladder_rungs.py -- an identity `l1l2` is either correct or a defect; say which.

Rounds 108-150 found that `geoLadder`'s `l1l2` was a placeholder, and that the reason ran deeper than
a missing adapter:

    Ladder Data Tok Sym W has ONE Tok, shared by l0l1 and l1l2.

With `Tok = EqConstraint n`, any `Tokenizer (EqConstraint n) (EqConstraint n)` is forced to be a
repackaging. Round 150 fixed it by changing `Tok` to `EqTok` and supplying `decCon_enc_nil`.

But surveying the tree this round shows the SAME syntactic shape in four other instances, and most of
them are RIGHT:

    NondegenerateInstance   Ladder (List R) R (List R) ...      l1l2 := identityTokenizer R
    WeightLadderN           Ladder (List R) R (List R) ...      l1l2 := identityTokenizer R
    MultiLayerLadder        Ladder ... (NetSym n) (NetSym n)    l1l2 := { encode := fun s => [s] }
    WeightLadder            Ladder ... Sym Sym ...              l1l2 := { encode := fun s => [s.coef, s.const] }

When `Sym` is `List Tok`, or when `Sym`'s elements ARE the token type, the identity IS the correct
tokenizer -- there is nothing to encode. The defect is narrower than "identity l1l2": it is an
identity `l1l2` where `Sym` carries structure the token type cannot hold.

So this checker does not condemn identity rungs. It classifies every `Ladder` instance's `l1l2` and
prints the classification, so that
  (a) a genuinely-forced identity is visibly bounded, and
  (b) a NEW identity rung cannot appear without being listed.

Report-only, deliberately: deciding whether a given `Sym` is "structure the token type cannot hold"
needs judgement, and a gate that guesses would be worse than a report that shows.
"""
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _paths import resolve  # noqa: E402  (path-keyed artifact: see _paths.py)

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.abspath(os.path.join(HERE, "..", "Lattice"))

#: `Ladder D T S W where` -- the def's header, possibly spanning lines.
LADDER_HEAD = re.compile(
    r"Ladder\s+([^\n]+?)\s+([A-Za-z0-9_.'{}()\s,→ℕℝ]+?)\s+where", re.S)


def instances(root=LAT):
    """(file, line, header, l0l1 text, l1l2 text) for every `Ladder ... where` in the tree."""
    out = []
    for dirpath, _, files in os.walk(root):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, root).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            src = io.open(p, "rb").read().decode("utf-8", errors="replace")
            lines = src.split("\n")
            for i, ln in enumerate(lines):
                # an instance is a `def ... : Ladder ... where`; skip the structure and variables
                if not re.search(r"(?<![A-Za-z])Ladder\b", ln):
                    continue
                stripped = ln.lstrip()
                if stripped.startswith(("-", "/-", "*", "|")) or stripped.startswith("`"):
                    continue
                chunk = "\n".join(lines[i:i + 8])
                head_line = " ".join(lines[i:i + 3])
                if "structure" in head_line or "variable" in head_line:
                    continue
                if not re.search(r"(?<![A-Za-z])Ladder\b", chunk):
                    continue
                m = re.search(r"Ladder\s+(.*?)\s+where", chunk, re.S)
                if not m:
                    continue
                header = " ".join(m.group(1).split())
                # the body: up to the next blank-line-then-/-- or 40 lines
                body = "\n".join(lines[i:i + 40])
                l0 = re.search(r"l0l1\s*:=\s*([^\n]+(?:\n(?!\s*l1l2)[^\n]+)*)", body)
                l1 = re.search(r"l1l2\s*:=\s*([^\n]+(?:\n(?!\s*l2l3)[^\n]+)*)", body)
                out.append((rel, i + 1, header,
                            (l0.group(1).strip() if l0 else "?"),
                            (l1.group(1).strip() if l1 else "?")))
    return out


def classify(l1l2):
    """Rough shape of an l1l2 body."""
    flat = " ".join(l1l2.split())
    if "identityTokenizer" in flat:
        return "identity (identityTokenizer)"
    m = re.search(r"encode\s*:=\s*fun\s+(\w+)\s*=>\s*\[\s*(\w+)\s*\]", flat)
    if m and m.group(1) == m.group(2):
        return "identity (singleton)"
    if re.search(r"encode\s*:=\s*fun\s+\w+\s*=>\s*\[[^\]]*,[^\]]*\]", flat):
        return "field projection (>=2 tokens)"
    if "encodeForm" in flat or "decodePayload" in flat or "decCon" in flat or "encCon" in flat \
            or "eqConstraintTokenizer" in flat:
        return "real encoder"
    # a named tokenizer (e.g. `boolTok`) that is not identity-shaped: accept it, but say so
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", flat):
        return "named tokenizer (%s)" % flat.split(".")[-1]
    return "other"


#: Identity `l1l2` rungs that are CORRECT, each with the type reason that makes them correct.
#:
#: An identity rung is right exactly when `Sym` is `List Tok` or `Sym`'s elements ARE `Tok` -- then there
#: is nothing to encode, and `identityTokenizer` is the honest answer rather than a placeholder. It is a
#: DEFECT when `Sym` carries structure the token type cannot hold: that was `geoLadder` before round 150,
#: where the rung claimed to encode and did not.
#:
#: Round 167 promotes this checker from report-only to a gate. The rule is:
#:   * an identity rung NOT in this table        -> FAIL (a new one appeared; justify it or fix it)
#:   * an entry in this table with no instance   -> FAIL (the justification has rotted)
#:   * an entry whose rung is no longer identity -> FAIL (stale table)
#: That makes the table a register rather than a comment.
IDENTITY_OK = {
    "Lift/MultiLayerLadder.lean":
        "Sym = NetSym and Tok = NetSym -- the same type, so there is nothing to encode",
    "Lift/NondegenerateInstance.lean":
        "Sym = List ℝ and Tok = ℝ, so Sym IS List Tok",
    "Lift/WeightLadderN.lean":
        "Sym = List ℝ and Tok = ℝ, so Sym IS List Tok",
    # Round 168. This is the one ladder whose l2l3 genuinely CHANGES the representation
    # (`CExpr` tree -> `List StackOp`), so its l1l2 has nothing to do: Sym and Tok are both
    # `ShallowCExpr n`. The substantive rung here is l2l3, whose proof uses `toStack_correct`.
    "Geo/CodegenLadder.lean":
        "Sym = ShallowCExpr and Tok = ShallowCExpr -- the same type; the substance is in l2l3",
    # Round 180. Same types (`List ℝ` / `ℝ`), so `identityTokenizer` is the honest rung. The point of
    # this ladder is l2l3: it uses the FULL-WIDTH encoder, which has an exact inverse, where
    # `weightLadderN`'s rank-one encoder provably has none.
    "Lift/WeightLadderFullWidthInstance.lean":
        "Sym = List ℝ and Tok = ℝ, so Sym IS List Tok; the substance is the full-width l2l3",
    # Round 200. Same reason: Sym = List Unit and Tok = Unit. The substance is l2l3, which produces a
    # REAL affine weight layer whose action is exactly the coordinate difference -- and `satW` is `∀`.
    "Geo/WeightSideLadder.lean":
        "Sym = List Unit and Tok = Unit, so Sym IS List Tok; the substance is the weight-side l2l3",
}

# Round 241, the EIGHTH path-keyed artifact found in this tree (see gov/_paths.py for the list).
# The table is keyed on `Lattice/`-relative paths, so a `git mv` produced TWO symptoms at once:
# the moved file "has an identity l1l2 and is not registered", AND its entry "has no identity l1l2 any
# more". Map the KEYS at load time; never edit the table for a move.
IDENTITY_OK = {resolve(k): v for k, v in IDENTITY_OK.items()}

#: The classification strings that count as an identity rung.
IDENTITY_KINDS = ("identity (identityTokenizer)", "identity (singleton)")


def check(rows):
    """Return a list of problems with the identity rungs. Empty means the register is honest."""
    problems = []
    seen_identity = {}
    for rel, line, header, l0, l1 in rows:
        kind = classify(l1)
        if kind in IDENTITY_KINDS:
            seen_identity[rel] = (line, kind)
            if rel not in IDENTITY_OK:
                problems.append(
                    "%s:%d has an identity l1l2 (%s) and is not registered in IDENTITY_OK --"
                    " either give the type reason it is correct, or implement the rung"
                    % (rel, line, kind))
    for rel, why in IDENTITY_OK.items():
        if rel not in seen_identity:
            problems.append(
                "IDENTITY_OK lists %s (%s) but that file has no identity l1l2 any more --"
                " remove the stale entry" % (rel, why))
    return problems


def main(argv):
    rows = instances()
    # a definition can be reached from several lines of its header; keep the first
    seen = set()
    uniq = []
    for r in rows:
        key = (r[0], r[2][:60])
        if key in seen:
            continue
        seen.add(key)
        uniq.append(r)
    rows = uniq
    if not rows:
        print("LADDER RUNGS: no instances found (pattern drift?)")
        return 1

    print("=" * 88)
    print("every Ladder instance and the shape of its l1l2 rung")
    print("=" * 88)
    counts = {}
    for rel, line, header, l0, l1 in rows:
        kind = classify(l1)
        counts[kind] = counts.get(kind, 0) + 1
        print("  %-42s L%-5d %s" % (rel, line, kind))
        print("      types: %s" % header[:100])
        print("      l1l2 : %s" % " ".join(l1.split())[:90])

    print()
    for k in sorted(counts):
        print("  %-28s %d" % (k, counts[k]))
    print()
    print("An identity l1l2 is CORRECT when Sym is List Tok or Sym's elements are Tok --")
    print("there is nothing to encode. It is a DEFECT when Sym carries structure the token")
    print("type cannot hold (that was geoLadder before round 150). Deciding which needs")
    print("reading the types, which is why this prints them.")
    print()

    if "--self-test" in argv:
        # two-way: a registered table with the real rows must be clean, and an unregistered identity
        # must be reported, and a rotted entry must be reported.
        base = check(rows)
        planted = list(rows) + [("Lift/Planted.lean", 1, "types: x", "a", "identityTokenizer ℝ")]
        p1 = check(planted)
        p2 = check([r for r in rows if r[0] != "Lift/WeightLadderN.lean"])
        ok = (not base) and bool(p1) and bool(p2)
        print("live run problems :", base)
        print("after planting    :", [p for p in p1 if "Planted" in p])
        print("after removing one:", [p for p in p2 if "WeightLadderN" in p])
        print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
        return 0 if ok else 2

    problems = check(rows)
    if problems:
        print("LADDER RUNGS: %d identity rung(s) unaccounted for" % len(problems))
        for p in problems:
            print("  " + p)
        return 1
    print("LADDER RUNGS: every identity rung is registered with a type reason")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
