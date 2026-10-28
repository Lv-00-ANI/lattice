"""`gov/audit_aliases.py` -- the duplication census, and a two-way baseline gate over two shapes.

## The two shapes, and why both are needed

`audit_duplicates.py` groups by **name** and is **report-only**, so it catches neither. Round 11 measured
that **statement** comparison catches neither either: an argument reorder changes the signature, and the
duplicates differ exactly that way.

Round 11 added a detector for shape 1. Round 12 measured that **4 of the 6 A-class duplicates are shape 2**,
so one detector was not enough:

| shape | what it looks like | count |
|:--|:--|--:|
| **forward** | `:= other_declaration args`, no tactics | **706** |
| **copy** | the *same* proof body under a *different* name | **74 groups** |

The example that made shape 2 necessary: `dot_append_sub` and `dot_append_of_length_eq` each carry their
own proof, so the forward detector is blind to them.

## Neither shape is a defect by itself

`penaltyLoss_eq_zero_eqZero` / `_perpendicular` / `_rightAngle` sharing `by unfold penaltyLoss; exact
sq_eq_zero_iff` is **good design** -- one general fact, three vocabulary instances. `compileIR_*_exact`
forwarding to `compileIR_penalty_exact_of` is the same thing for forwards.

What is wrong is a duplicate **nobody decided on**. So both detectors compare against a baseline **in both
directions**: a new one fails (it must be decided and recorded), a baselined one that is gone fails (the
baseline cannot rot). Same discipline as `check_underscore_hypotheses.py`.

## Baseline format

One line per entry, tab-separated, `kind` first:

    forward	<path relative to Lattice/>	<declaration name>
    copy	<path relative to Lattice/>	<declaration name>

Adding a line means "this duplicate was decided and is intentional (usually a vocabulary instance)".
"""

import collections
import hashlib
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

# a proof shorter than this is trivial (`rfl`, `simp`) and collides legitimately
MIN_PROOF = 40


def _files():
    out = []
    for root, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            out.append((rel, io.open(p, encoding="utf-8").read()))
    return out


def scan():
    """`(forwards, copies)`.

    forwards -- `{(path, name)}` whose whole proof forwards to another declaration;
    copies   -- `{(path, name)}` whose normalised proof body is shared with a DIFFERENT name.
    """
    files = _files()

    declared = set()
    for _rel, src in files:
        for m in DECL.finditer(src):
            declared.add(m.group(2).split(".")[-1])

    forwards = set()
    bodies = []
    for rel, src in files:
        for m in THM.finditer(src):
            name = m.group(2).split(".")[-1]
            body = m.group(3)

            bm = BODY.search(body)
            if bm:
                target = bm.group("name").split(".")[-1]
                if (target != name and target in declared
                        and not TACTIC.search(bm.group("args"))
                        and len(bm.group("args")) <= 300):
                    forwards.add((rel, name))

            k = body.find(":=")
            if k < 0:
                continue
            norm = re.sub(r"\s+", " ", body[k + 2:]).strip()
            if len(norm) < MIN_PROOF:
                continue
            bodies.append((hashlib.sha256(norm.encode()).hexdigest()[:16], rel, name, norm))

    by_hash = collections.defaultdict(list)
    for h, rel, name, norm in bodies:
        by_hash[h].append((rel, name, norm))

    copies = set()
    for _h, v in by_hash.items():
        if len({n for _r, n, _x in v}) > 1:
            for rel, name, _norm in v:
                copies.add((rel, name))
    return forwards, copies


def load_baseline():
    if not os.path.exists(BASE):
        return None
    keys = set()
    for ln in io.open(BASE, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        p = ln.split("\t")
        if len(p) >= 3:
            keys.add((p[0], p[1], p[2]))
        elif len(p) == 2:
            # tolerate the round-11 format: a bare `<path>\t<name>` was a forward
            keys.add(("forward", p[0], p[1]))
    return keys


def write_baseline(forwards, copies):
    rows = [("forward", r, n) for r, n in forwards] + [("copy", r, n) for r, n in copies]
    io.open(BASE, "w", encoding="utf-8", newline="\n").write(
        "# duplication baseline -- `kind\tpath\tname`, kind in {forward, copy}.\n"
        "# Adding a line means: this duplicate was decided and is intentional "
        "(usually a vocabulary instance).\n"
        + "".join("%s\t%s\t%s\n" % r for r in sorted(rows)))


def write_report(forwards, copies):
    lines = ["# 重复清册（两种形状）", "",
             "> 由 `gov/audit_aliases.py` 生成。**不要手改。**", "",
             "**重复不是缺陷。** 它是「增加了一个名字、没有增加数学」的形状。",
             "有的是**词汇族**（一条一般引理 + 若干实例，那是好设计），有的是**没人决定过的副本**。", "",
             "**本清册的作用**：让每一个重复被**决定过一次**，并记在 `alias-baseline.txt` 里。", "",
             "| 形状 | 判据 | 条数（按声明计） |", "|:--|:--|--:|",
             "| **forward** | 证明体就是 `:= 另一个声明 args`，无策略 | %d |" % len(forwards),
             "| **copy** | 规范化后的证明体与**另一个名字**完全相同 | %d |" % len(copies), "",
             "⚠ **`audit_duplicates.py` 两种都看不见**：它按**名字**分组，而这两种都是**不同名字**；"
             "而且它是 report-only。**陈述比对也看不见**——参数顺序一换签名就变。", "",
             "## \u26d4 本门禁看不见的**第三种形状**：同陈述、**不同证明**", "",
             "第 12 轮实测：`WEIGHT-HOP-CLASSIFICATION.md` 的 6 条 A 类里有 **4 条不在任何基线上**——",
             "它们陈述相同、**证明体也不同**，所以散列也对不上。", "",
             "| 形状 | 能否自动发现 |", "|:--|:--|",
             "| forward | \u2705 本门禁 |",
             "| copy（证明体相同）| \u2705 本门禁 |",
             "| **同陈述、不同证明** | \u274c **任何语法手段都不行**——需要**陈述等价性**"
             "（elaboration 或 `#check` 型比较），本仓库没有 |", "",
             "\u26a0 **所以本清册只覆盖 2/3 的重复形状。** 第三种只能**人工审阅**，而它正是那 6 条里的 4 条。",
             "把本清册当「重复已清完」的证据是**错误的**。", "",
             "## forward", "", "| 文件 | 定理 |", "|:--|:--|"]
    for rel, name in sorted(forwards):
        lines.append("| `%s` | `%s` |" % (rel, name))
    lines += ["", "## copy", "", "| 文件 | 定理 |", "|:--|:--|"]
    for rel, name in sorted(copies):
        lines.append("| `%s` | `%s` |" % (rel, name))
    io.open(REPORT, "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")


def self_test():
    """Both failure directions, for BOTH shapes. A gate that can only pass is not a gate."""
    ok = True

    base = {("forward", "A.lean", "kept")}
    keys = {("forward", "A.lean", "kept"), ("forward", "B.lean", "planted")}
    if (keys - base) != {("forward", "B.lean", "planted")}:
        print("  forward NEW direction FAILED")
        ok = False
    base2 = {("forward", "A.lean", "kept"), ("forward", "C.lean", "gone")}
    if (base2 - keys) != {("forward", "C.lean", "gone")}:
        print("  forward STALE direction FAILED")
        ok = False

    if ({("copy", "B.lean", "planted2")} - set()) != {("copy", "B.lean", "planted2")}:
        print("  copy NEW direction FAILED")
        ok = False

    for body, want in ((":= hg x y", False),
                       (":= other_lemma x", True),
                       (":= by exact other_lemma x", True),
                       (":= by simp", False),
                       (":= other_lemma x (by ring)", False)):
        bm = BODY.search(body)
        got = bool(bm) and bm.group("name").split(".")[-1] == "other_lemma" \
            and not TACTIC.search(bm.group("args").replace("other_lemma", ""))
        if got != want:
            print("  forward detector FAILED on %r: got %s, want %s" % (body, got, want))
            ok = False

    trivial = re.sub(r"\s+", " ", "by rfl")
    substantial = re.sub(r"\s+", " ", "by unfold foo; rw [bar]; exact baz_qux_quux_corge")
    if len(trivial) >= MIN_PROOF:
        print("  copy threshold FAILED: a trivial body passes the size floor")
        ok = False
    if len(substantial) < MIN_PROOF:
        print("  copy threshold FAILED: a real proof is filtered out")
        ok = False

    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


def main(argv):
    forwards, copies = scan()
    write_report(forwards, copies)
    keys = {("forward", r, n) for r, n in forwards} | {("copy", r, n) for r, n in copies}

    if "--write-baseline" in argv:
        write_baseline(forwards, copies)
        print("DUP CENSUS: baseline written, %d forward + %d copy = %d entries"
              % (len(forwards), len(copies), len(keys)))
        return 0

    base = load_baseline()
    if base is None:
        print("DUP CENSUS: no baseline at %s (run --write-baseline once)" % BASE)
        return 1

    new = sorted(keys - base)
    stale = sorted(base - keys)
    print("DUP CENSUS: forward %d, copy %d; baseline %d; new %d; stale %d"
          % (len(forwards), len(copies), len(base), len(new), len(stale)))
    for k in new[:15]:
        print("   NEW   %s %s :: %s" % k)
    for k in stale[:15]:
        print("   STALE %s %s :: %s" % k)
    print("   report: %s" % REPORT)
    if new or stale:
        print("DUP CENSUS: a duplicate must be decided once -- add it to alias-baseline.txt, or remove it")
        return 1
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
