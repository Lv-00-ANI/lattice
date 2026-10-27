"""gov/check_none_branches.py -- every wildcard `| _ => none` must have a stated reason.

## Why

A `| _ => none` inside a decoder is a failure branch. `none` means "these tokens are not a valid
encoding", and it is *syntactically* unavoidable: the match must be total. Whether it is
*semantically* reachable is a question about the encoder, and that question is exactly what a
round-trip theorem answers.

The audit (P2-16) found 21 of these in the kernel and noted that nobody had judged them. Judging 21
branches by hand once is not the fix; the fix is to make the judgement **recorded and checked**, so a
22nd branch cannot appear unexamined.

## The three reasons a branch can be justified

1. **covered by a round-trip theorem.** `Geo/EqConstraintToken.lean` has `decCon_expr`,
   `decCon_samePoint`, `decCon_perp`, `decCon_distEq` -- one per constructor -- plus `decCon_enc_nil`.
   Those theorems say the branch on a well-formed encoding takes the `some` arm, so the `none` arm is
   unreachable on anything `encCon` can produce.
2. **upstream Lv-00 carried code.** Those files came from the reference project and are carried
   verbatim; changing their matches would be rewriting evidence.
3. **a partial decoder by design.** `LvDSLPartial` says in its name and docstring that it decodes a
   subset.

A file that contains a wildcard `| _ => none` and is **not** in `COVERED` fails this checker, with the
line numbers, so the next one is judged rather than counted.

## Not a proof

This checker does NOT prove reachability. It records which of the three reasons applies, so the audit's
question has an answer per site instead of a total. Saying that plainly matters: a check that reports
"covered" is doing bookkeeping, not verification, and the two must not be confused.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")

#: a wildcard arm returning `none`
WILDCARD_NONE = re.compile(r"\|\s*_\s*=>\s*none")

#: file (relative to `Lattice/`) -> (reason, the theorem or justification)
COVERED = {
    "Geo/EqConstraintToken.lean": (
        "covered by round-trip",
        "`decCon_expr` / `decCon_samePoint` / `decCon_perp` / `decCon_distEq` give the `some` arm on "
        "each constructor's payload; `decCon_enc_nil` gives the round-trip. The `none` arms are "
        "unreachable on any list `encCon` produces."),
    "Geo/RealToken.lean": (
        "covered by round-trip",
        "`decExpr_coord` / `decExpr_const` plus `decExpr_enc` -- same shape as `EqConstraintToken`."),
    "Lift/WeightLadder.lean": (
        "covered by round-trip",
        "the decoder's accepting case is the two-token encoding of `SymOne`; the wildcard is the "
        "rejection arm and `l1l2`'s round-trip field is the theorem."),
    "Lift/IntRoundtrip.lean": (
        "covered by round-trip",
        "`IntRoundtrip`'s round-trip theorem is the whole point of the file; the wildcard is the "
        "rejection arm."),
    "Lib/Compiler/RealLv00CompilerCodegen.lean": (
        "upstream Lv-00 carried",
        "came from the reference project; its `match c.args with | [...] => some ... | _ => none` "
        "shape is the upstream encoding, and rewriting it would be editing evidence."),
    "Lib/Chain/RealLv00Systems.lean": (
        "upstream Lv-00 carried", "same as above."),
    "Lib/Compiler/RealFirstOrderLogic.lean": (
        "partial decoder by design",
        "first-order syntax is decoded for the fragment the file states; the wildcard is the "
        "out-of-fragment rejection."),
    "Lib/Compiler/LvDSLPartial.lean": (
        "partial decoder by design", "the file's name and docstring say `Partial`."),
}

VALID_REASONS = {"covered by round-trip", "upstream Lv-00 carried", "partial decoder by design"}


def scan(root=None):
    """Return `(unregistered, bad_reason)`: each a list of `(rel, lines)`."""
    root = root or LAT
    unregistered, bad_reason = [], []
    for dirpath, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, root).replace("\\", "/")
            src = io.open(p, "rb").read().decode("utf-8", "replace")
            lines = [src[:m.start()].count("\n") + 1 for m in WILDCARD_NONE.finditer(src)]
            if not lines:
                continue
            if rel not in COVERED:
                unregistered.append((rel, lines))
            elif COVERED[rel][0] not in VALID_REASONS:
                bad_reason.append((rel, COVERED[rel][0]))
    # an entry whose file no longer has any wildcard arm is stale
    stale = []
    for rel in COVERED:
        p = os.path.join(root, rel)
        if not os.path.exists(p):
            stale.append((rel, "file does not exist"))
            continue
        src = io.open(p, "rb").read().decode("utf-8", "replace")
        if not WILDCARD_NONE.search(src):
            stale.append((rel, "no `| _ => none` left -- remove the entry"))
    return unregistered, bad_reason, stale


def main(argv):
    unregistered, bad_reason, stale = scan()

    if "--self-test" in argv:
        import shutil
        tmp = os.path.join(HERE, ".none-selftest")
        shutil.rmtree(tmp, ignore_errors=True)
        os.makedirs(os.path.join(tmp, "Sub"))
        failures = []
        try:
            io.open(os.path.join(tmp, "Sub", "Planted.lean"), "w", encoding="utf-8").write(
                "def f : List Nat -> Option Nat\n  | _ => none\n")
            u, _, _ = scan(tmp)
            if not [x for x in u if "Planted" in x[0]]:
                failures.append("an unregistered wildcard `| _ => none` was NOT reported")
            COVERED["Sub/Planted.lean"] = ("covered by round-trip", "planted")
            try:
                u2, _, _ = scan(tmp)
                if [x for x in u2 if "Planted" in x[0]]:
                    failures.append("a registered file was still reported unregistered")
            finally:
                del COVERED["Sub/Planted.lean"]
            COVERED["Sub/Planted.lean"] = ("because I say so", "planted")
            try:
                _, b, _ = scan(tmp)
                if not [x for x in b if "Planted" in x[0]]:
                    failures.append("an invalid reason string was NOT reported")
            finally:
                del COVERED["Sub/Planted.lean"]
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        if failures:
            for f in failures:
                print("SELF-TEST FAILED: %s" % f)
            return 2
        print("SELF-TEST: unregistered arm caught, registered arm accepted, invalid reason caught")
        return 0

    total = 0
    for rel, (reason, why) in sorted(COVERED.items()):
        print("  %-46s %s" % (rel, reason))
        print("      %s" % why)
    print()
    for rel, lines in unregistered:
        total += len(lines)
        print("  UNREGISTERED %s lines %s" % (rel, lines))
    for rel, r in bad_reason:
        print("  BAD REASON   %s -> %r (must be one of %s)" % (rel, r, sorted(VALID_REASONS)))
    for rel, why in stale:
        print("  STALE ENTRY  %s -- %s" % (rel, why))
    print()
    if unregistered or bad_reason or stale:
        print("NONE BRANCHES: %d unregistered arm(s), %d bad reason(s), %d stale entr(ies)"
              % (total, len(bad_reason), len(stale)))
        return 1
    print("NONE BRANCHES: every wildcard `| _ => none` in the kernel has a recorded reason")
    print("(This is bookkeeping, not a reachability proof -- see the module docstring.)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
