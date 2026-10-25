"""Govern the chain status table: every "load-bearing carrier" it names must EXIST.

`check_proof_chain_rung.py` verified the instance census and the `encode := id` fact, but not the
status table's carriers -- which is why the table could say "L1->L2 has no carrier" for 27
rounds after one was proved.

This adds that check: extract the identifiers named in the carrier column and confirm each is a
declaration in the tree.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(LAKE, "Lattice")
DOC = os.path.join(LAKE, "PROOF-CHAIN-RUNG.md")

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(?:theorem|lemma|def|structure|abbrev|inductive|class)"
                  r"[ \t]+([A-Za-z0-9_'!?]+)")


def tree_names():
    names = set()
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            t = io.open(os.path.join(root, f), "rb").read().decode("utf-8", errors="replace")
            for m in DECL.finditer(t):
                names.add(m.group(1))
    return names


def carriers_from_table():
    """Identifiers in the 承重载体 column of the status table (lines starting with `| L`)."""
    t = io.open(DOC, encoding="utf-8").read()
    out = []
    for line in t.split("\n"):
        if not line.startswith("| L") and not line.startswith("| 闭环"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 5:
            continue
        carrier = cells[4]
        for m in re.finditer(r"`([A-Za-z][A-Za-z0-9_.']*)`", carrier):
            ident = m.group(1).split(".")[-1]
            if ident and ident not in ("ε",):
                out.append((cells[0], ident))
    return out


def main(argv):
    names = tree_names()
    carriers = carriers_from_table()
    problems = 0
    print("chain status table: %d carrier reference(s)\n" % len(carriers))
    print("%-10s %-42s %s" % ("jump", "carrier", "verdict"))
    seen = set()
    for jump, ident in carriers:
        if (jump, ident) in seen:
            continue
        seen.add((jump, ident))
        ok = ident in names
        print("%-10s %-42s %s" % (jump, ident, "ok" if ok else "*** NOT IN TREE ***"))
        if not ok:
            problems += 1

    if "--self-test" in argv:
        # plant a nonexistent carrier and confirm it is reported
        fake = "thisCarrierDoesNotExist"
        ok = fake in names
        print("\n[self-test] planted `%s`: reported as missing = %s"
              % (fake, "yes" if not ok else "NO"))
        return 1 if not ok else 0

    print("\n" + "=" * 60)
    print("CHAIN TABLE: %s" % ("every carrier exists" if problems == 0
                               else "%d missing carrier(s)" % problems))
    return 0 if problems == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
