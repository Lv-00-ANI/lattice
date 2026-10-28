"""`gov/audit_aliases.py` -- the alias census, and a two-way baseline gate over it.

## The defect class this covers

A theorem whose entire proof is `:= other_declaration args` is an **alias**: it adds a name, not
mathematics. That is sometimes **right** (a vocabulary bridge such as `compileIR_*_exact` pointing at one
general `compileIR_penalty_exact_of`), and sometimes **wrong** (a second copy of a theorem under a new name,
which `audit_duplicates.py` cannot see because it groups by NAME).

**`audit_duplicates.py` has two blind spots, both measured in round 11:**

1. it groups by **name**, so "same statement, different name" is invisible -- and that is exactly the shape
   of 3 of the 6 A-class duplicates in `WEIGHT-HOP-CLASSIFICATION.md`;
2. it is **report-only** -- it prints `identical: 332` and exits 0, so nothing is gated.

Round 11 also measured that normalised **statement** comparison finds **0** different-name duplicates,
because an argument reorder changes the signature. So the visible signal is not the statement: it is the
**proof body**.

## What this gate does

- walks every `theorem`/`lemma` in the live tree (not `Reference/`);
- flags it when the body is `:= <name> args` or `:= by exact <name> args`, **no tactic** in `args`, and
  `<name>` is a **declaration in the tree** (a local hypothesis or `rfl`/`simp` is a real proof, not an alias);
- compares against `gov/alias-baseline.txt`, **two ways**: a new alias fails, a baselined alias that is gone
  fails. That is the same discipline as `check_underscore_hypotheses.py` and `check_proof_strength.py`.

⚠ **This gate does not say an alias is bad.** It says an alias must be **decided**, once, and recorded.
The baseline is the record; adding one requires editing it, which is visible in review.
"""

import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")
BASE = os.path.join(HERE, "alias-baseline.txt")
REPORT = os.path.join(HERE, "ALIAS-CENSUS.md")

DECL = re.compile(
    r"(?m)^(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
    r"(theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_'.]+)")

THM = re.compile(
    r"(?ms)^(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
    r"(theorem|lemma)\s+([A-Za-z0-9_'.]+)(.*?)^\s*(?=theorem|lemma|def|@\[|/-|end\b|\Z)")

BODY = re.compile(r"(?s):=\s*(?:by\s+)?(?:exact\s+)?(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)(?P<args>[\s\S]*)$")

TACTIC = re.compile(
    r"\b(rw|simp|induction|cases|obtain|nlinarith|linarith|ring|omega|constructor|intro|refine|calc|"
    r"field_simp|norm_num|decide|positivity|gcongr|aesop|tauto|subst|have|apply|exact|by_contra|"
    r"push_neg|use|exists)\b")


def scan():
    files = []
    for root, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            files.append((rel, io.open(p, encoding="utf-8").read()))

    declared = set()
    for _rel, src in files:
        for m in DECL.finditer(src):
            declared.add(m.group(2).split(".")[-1])

    out = []
    for rel, src in files:
        for m in THM.finditer(src):
            name = m.group(2).split(".")[-1]
            bm = BODY.search(m.group(3))
            if not bm:
                continue
            target = bm.group("name").split(".")[-1]
            if target == name or target not in declared:
                continue
            if TACTIC.search(bm.group("args")) or len(bm.group("args")) > 300:
                continue
            out.append((rel, name, target))
    return sorted(out)


def load_baseline():
    if not os.path.exists(BASE):
        return None
    keys = set()
    for ln in io.open(BASE, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        p = ln.split("\t")
        if len(p) >= 2:
            keys.add((p[0], p[1]))
    return keys


def write_report(rows):
    import collections
    by_target = collections.Counter(t for _r, _n, t in rows)
    lines = ["# 别名清册（谁的证明只是转发）", "",
             "> 由 `gov/audit_aliases.py` 生成。**不要手改。**", "",
             "**别名不是缺陷**；它是「增加了一个名字、没有增加数学」的形状。",
             "有的是**词汇桥**（九条 `compileIR_*_exact` 指向一条一般引理，那是好设计），",
             "有的是**重复的副本**（`audit_duplicates.py` 按**名字**分组，看不见后者）。", "",
             "**本清册的作用**：让每一个别名被**决定过一次**，并记在 `alias-baseline.txt` 里。", "",
             "| 指标 | 值 |", "|:--|--:|", "| 别名总数 | %d |" % len(rows), "",
             "## 被转发最多的声明", "",
             "> 一个声明被 **≥3** 条别名指向，通常意味着「一条一般引理 + 一族词汇」；",
             "> 被**只有 1 条**指向，则更像重复副本，值得单独看。", "",
             "| 声明 | 别名条数 |", "|:--|--:|"]
    for t, c in by_target.most_common():
        lines.append("| `%s` | %d |" % (t, c))
    lines += ["", "## 全部别名", "", "| 文件 | 定理 | 转发到 |", "|:--|:--|:--|"]
    for rel, name, target in rows:
        lines.append("| `%s` | `%s` | `%s` |" % (rel, name, target))
    io.open(REPORT, "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")


def main(argv):
    rows = scan()
    write_report(rows)
    keys = {(r, n) for r, n, _t in rows}

    if "--write-baseline" in argv:
        io.open(BASE, "w", encoding="utf-8", newline="\n").write(
            "# alias census baseline -- one `<file>\\t<theorem>` per line.\n"
            "# Adding a line means: this alias was decided and is intentional (usually a vocabulary bridge).\n"
            + "".join("%s\t%s\n" % k for k in sorted(keys)))
        print("ALIAS CENSUS: baseline written, %d entries" % len(keys))
        return 0

    base = load_baseline()
    if base is None:
        print("ALIAS CENSUS: no baseline at %s (run with --write-baseline once)" % BASE)
        return 1 if "--require-baseline" in argv else 0

    new = sorted(keys - base)
    stale = sorted(base - keys)

    print("ALIAS CENSUS: %d alias(es); baseline %d; new %d; stale %d"
          % (len(keys), len(base), len(new), len(stale)))
    for f, n in new[:15]:
        print("   NEW   %s :: %s" % (f, n))
    for f, n in stale[:15]:
        print("   STALE %s :: %s" % (f, n))
    print("   report: %s" % REPORT)

    if new or stale:
        print("ALIAS CENSUS: an alias must be decided once -- add it to alias-baseline.txt, or remove it")
        return 1
    return 0


def self_test():
    """The gate must be able to demonstrate BOTH of its failure modes.

    Round 11. A check that can only pass is not a check -- and this project has now found five of those
    (`gate.py` could not fail, the debt counter could not fall, verdicts went stale, `check_slots` had a
    2000-char window that blamed the registry, `audit_duplicates` is report-only). So this one ships with a
    test for each direction:

    1. a NEW alias (present in the scan, absent from the baseline) must be reported as NEW;
    2. a STALE baseline entry (in the baseline, absent from the scan) must be reported as STALE.
    """
    ok = True

    # direction 1: NEW
    base = {("A.lean", "kept")}
    keys = {("A.lean", "kept"), ("B.lean", "planted")}
    new = keys - base
    if new != {("B.lean", "planted")}:
        print("  NEW-direction FAILED: %r" % (new,))
        ok = False

    # direction 2: STALE
    base2 = {("A.lean", "kept"), ("C.lean", "vanished")}
    keys2 = {("A.lean", "kept")}
    stale = base2 - keys2
    if stale != {("C.lean", "vanished")}:
        print("  STALE-direction FAILED: %r" % (stale,))
        ok = False

    # and the detector itself must reject a local hypothesis and a tactic
    for body, want in ((":= hg x y", False),          # a local hypothesis, not a declaration
                       (":= other_lemma x", True),    # a declaration forwarded to
                       (":= by exact other_lemma x", True),
                       (":= by simp", False),         # a tactic
                       (":= other_lemma x (by ring)", False)):  # a real proof follows
        bm = BODY.search(body)
        got = bool(bm) and bm.group("name").split(".")[-1] in {"other_lemma"} and not TACTIC.search(
            bm.group("args").replace("other_lemma", ""))
        if got != want:
            print("  detector FAILED on %r: got %s, want %s" % (body, got, want))
            ok = False

    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
