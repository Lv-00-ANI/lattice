"""gov/check_underscore_hypotheses.py -- hypotheses the author already knew were unused.

## The signal, and why it is exact

Lean's `linter.unusedVariables` reports hypotheses that are never mentioned in a proof. **But it stays
silent when the binder name starts with an underscore** -- that prefix is the language's conventional way of
saying "I know this is unused".

So `_hrest`, `_hTaylor`, `_hbound` are not merely unused: **the author declared them unused.** That makes
them a zero-false-positive, mechanically enumerable candidate list, which is exactly what the review
process needed and did not have.

This is how `top1_output_is_hard` was found: its `_hrest : ∀ j, j ≠ i → w j = 0` could never be used, because
the sum ranged over the singleton `{i}` and never reached `j ≠ i`. **The theorem's name said "hard routing"
while the hypothesis that makes routing hard was structurally unreachable.** Reviewers found it by reading;
this file finds it by pattern.

## What a finding means

A bare `_` binder is a **wildcard** and is NOT reported -- that is normal Lean style for a discarded
argument. Only `_name` with a real name after the underscore is a finding.

A finding does **not** automatically mean the theorem is wrong. It means one of:

1. **The hypothesis is structurally unreachable** (the `{i}` case) -- the statement is weaker than its name;
2. **The hypothesis is redundant** (provable from the others) -- it should be deleted, making the theorem
   stronger (this is what `fixPerp_absorbs` needed);
3. **The binder is genuinely unused but the hypothesis is needed for symmetry / interface** -- legitimate,
   and it goes in the baseline **with a reason**.

## Discipline

Baseline-driven, two-way: a new finding fails, and a baselined one that disappeared also fails (the ledger
may only shrink). Each baseline line carries the theorem name so the reason is one lookup away.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")
BASELINE = os.path.join(HERE, "underscore_hypotheses_baseline.txt")

DECL = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma)\s+([\w'.ᵢ-₉]+)")

#: a named binder whose name starts with `_` followed by at least one more identifier char
UNDERSCORE_BINDER = re.compile(r"[\(\{]\s*(_[A-Za-z\u03b1-\u03c9][\w'₀-₉]*)\s*[:\}]")


def strip_comments(src):
    out = []
    i, n = 0, len(src)
    while i < n:
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                break
            out.append(" " * (j - i))
            i = j
            continue
        if src.startswith("/-", i):
            j = src.find("-/", i + 2)
            if j < 0:
                out.append(" " * (n - i))
                break
            out.append("".join(c if c == "\n" else " " for c in src[i:j + 2]))
            i = j + 2
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def scan(root=None):
    root = root or LAT
    found = []
    for dp, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, root).replace("\\", "/")
            src = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
            starts = [(m.start(), m.group(1)) for m in DECL.finditer(src)]
            for idx, (pos, name) in enumerate(starts):
                end = starts[idx + 1][0] if idx + 1 < len(starts) else len(src)
                block = src[pos:end]
                depth, cut = 0, len(block)
                for i in range(len(block) - 1):
                    ch = block[i]
                    if ch in "([{":
                        depth += 1
                    elif ch in ")]}":
                        depth -= 1
                    elif depth == 0 and block.startswith(":=", i):
                        cut = i
                        break
                stmt = block[:cut]
                body = block[cut:]
                for m in UNDERSCORE_BINDER.finditer(stmt):
                    var = m.group(1)
                    line = src[:pos + m.start()].count("\n") + 1
                    # Does the proof mention the binder? `_htri` was prefixed AND used -- that is a
                    # misnamed binder, not a redundant hypothesis. Different defect, different fix.
                    used = re.search(r"(?<![\w'\u2080-\u2089])%s(?![\w'\u2080-\u2089])" % re.escape(var),
                                     body) is not None
                    found.append((rel, line, name, var, used))
    return found


def load_baseline():
    if not os.path.exists(BASELINE):
        return set()
    # Round 238. This is the THIRD path-keyed baseline in the tree, and it had the same defect as the
    # other two: a `git mv` makes every entry for the moved file look BOTH "new" (the finding appears at
    # the new path) AND "stale" (the old path vanishes). Measured this round on `Runtime/Extraction.lean`
    # `_hsem`. Fixed identically: map the baseline's path through `PATH_MAP`, never edit the baseline
    # file for a move.
    sys.path.insert(0, HERE)
    try:
        from _debt_path_map import PATH_MAP
    except ImportError:
        PATH_MAP = {}
    out = set()
    for ln in io.open(BASELINE, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        p = ln.split("\t")
        if len(p) >= 2:
            out.add((PATH_MAP.get(p[0].strip(), p[0].strip()), p[1].strip()))
    return out


def main(argv):
    if "--self-test" in argv:
        import shutil
        tmp = os.path.join(HERE, ".undhyp-selftest")
        shutil.rmtree(tmp, ignore_errors=True)
        os.makedirs(tmp)
        failures = []
        try:
            def one(name, body):
                d = os.path.join(tmp, name)
                os.makedirs(d, exist_ok=True)
                io.open(os.path.join(d, "X.lean"), "w", encoding="utf-8").write(body)
                return scan(d)

            fs = one("a", "theorem t (_h : 1 = 1) : 1 = 1 := rfl\n")
            if not fs:
                failures.append("an underscored named binder was NOT caught")

            fs = one("b", "theorem t (_ : 1 = 1) : 1 = 1 := rfl\n")
            if fs:
                failures.append("a bare `_` wildcard was reported: %r" % (fs,))

            fs = one("c", "theorem t (h : 1 = 1) : 1 = 1 := rfl\n")
            if fs:
                failures.append("a normal binder was reported: %r" % (fs,))

            fs = one("d", "theorem t {_hx : Nat} : 1 = 1 := rfl\n")
            if not fs:
                failures.append("an implicit underscored binder was NOT caught")
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        if failures:
            for f in failures:
                print("SELF-TEST FAILED: %s" % f)
            return 2
        print("SELF-TEST: `_h` caught, bare `_` ignored, plain binder ignored, implicit caught")
        return 0

    found = scan()
    base = load_baseline()
    cur = {(rel, name) for rel, _, name, _, _ in found}

    new = [f for f in found if (f[0], f[2]) not in base]
    gone = sorted(base - cur)

    for rel, line, name, var, used in new:
        if used:
            print("  NEW-A  %s:%d  [%s]  `%s` is PREFIXED `_` but IS used in the proof -- rename it"
                  % (rel, line, name, var))
        else:
            print("  NEW-B  %s:%d  [%s]  `%s` is never used -- the hypothesis is redundant or unreachable"
                  % (rel, line, name, var))
    for rel, name in gone:
        print("  STALE  baseline entry no longer present: %s [%s] -- delete it from the baseline" % (rel, name))

    n_used = sum(1 for f in found if f[4])
    print()
    print("UNDERSCORE HYPOTHESES: %d total -- %d prefixed-but-used (rename), %d genuinely unused"
          % (len(found), n_used, len(found) - n_used))
    print("  baselined %d, new %d, stale %d" % (len(found) - len(new), len(new), len(gone)))
    if new or gone:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
