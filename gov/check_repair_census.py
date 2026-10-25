"""gov/check_repair_census.py -- keep REPAIR-CENSUS's numbers honest.

Round 38 found the census had drifted from 6 files / 27 declarations to 9 / 28, and nobody
noticed because nothing measured it. This makes it measurable.

Three classes, exactly as the census defines them:
  A  files containing `: Repair ... where`          (defines an instance)
  B  files mentioning `Repair` and having fix-named declarations, but not A
  C  files with fix-named declarations and no `Repair` anywhere

`--self-test` plants a wrong expectation and asserts the checker reports it.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(LAKE, "Lattice")

# The census's recorded numbers (REPAIR-CENSUS.md §1).
EXPECTED = {"A_files": 10, "A_decls": 29, "B_files": 18, "B_decls": 47,
            "C_files": 56, "C_decls": 245}

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(?:theorem|lemma|def|structure|abbrev|inductive)[ \t]+"
                  r"([A-Za-z0-9_'!?]+)")


def measure():
    A = B = C = 0
    a_d = b_d = c_d = 0
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            t = io.open(p, "rb").read().decode("utf-8", errors="replace")
            fix_names = [m.group(1) for m in DECL.finditer(t)
                         if re.search(r"fix|Fix|repair|Repair", m.group(1))]
            # A is decided on its OWN criterion: does the file define an instance?
            # It must NOT require a fix-named declaration -- `countdown` and `mkWithAtomic`
            # define instances under those names. Conflating the two questions is what made
            # the first version of this checker report A=7 instead of 9.
            defines = re.search(
                r":\s*(?:Lattice\.Core\.)?Repair\b[^:]{0,400}?\bwhere\b", t,
                re.S) is not None
            if defines:
                A += 1
                a_d += len(fix_names)
                continue
            if not fix_names:
                continue
            mentions = re.search(r"\bRepair\b", t) is not None
            if mentions:
                B += 1; b_d += len(fix_names)
            else:
                C += 1; c_d += len(fix_names)
    return {"A_files": A, "A_decls": a_d, "B_files": B, "B_decls": b_d,
            "C_files": C, "C_decls": c_d}


def main(argv):
    got = measure()
    expect = dict(EXPECTED)
    if "--self-test" in argv:
        expect["A_files"] = got["A_files"] + 1

    problems = 0
    print("repair census check\n")
    print("%-10s %-10s %-10s %s" % ("metric", "expected", "actual", "verdict"))
    for k in ("A_files", "A_decls", "B_files", "B_decls", "C_files", "C_decls"):
        ok = got[k] == expect[k]
        print("%-10s %-10d %-10d %s" % (k, expect[k], got[k], "ok" if ok else "DRIFT"))
        if not ok:
            problems += 1

    print("\n" + "=" * 56)
    if "--self-test" in argv:
        if problems > 0:
            print("SELF-TEST PASS: a wrong expectation is reported")
            return 1
        print("SELF-TEST FAIL: a wrong expectation was NOT reported")
        return 0
    print("REPAIR CENSUS: %s" % ("consistent" if problems == 0
                                 else "%d drift(s) -- update REPAIR-CENSUS.md" % problems))
    return 0 if problems == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
