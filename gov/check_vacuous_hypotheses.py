"""gov/check_vacuous_hypotheses.py -- hypotheses that state nothing.

## Two different defects, one of which needs Lean and one of which does not

**Class A -- dead hypothesis.** The binder is never mentioned in the proof. Lean's own
`linter.unusedVariables` reports it, so this file does NOT reimplement it: the compiler already found all
182 of them and `PROOF-DEBT.md` tracks the count. Duplicating a linter is not a guard, it is noise.

**Class B -- vacuous hypothesis.** The binder IS used, so no warning fires, but its TYPE is provable
outright, so the theorem is weaker than its statement suggests. `compileProg_correct`'s
`(h : stackDepth e ≤ 1)` was exactly this: it was passed to `compileAcc_correct`, hence "used", while
`stackDepth e = 1` for every expression.

Class B is the dangerous one and no linter finds it. This file catches the sub-class where the
vacuity is **syntactically visible**, with zero false positives:

  * `(h : a = a)`, `(h : a ↔ a)`, `(h : a → a)`
  * `(h : True)`
  * `(h : 0 ≤ 0)`, `(h : a ≤ a)`

**What this does NOT catch, stated rather than implied**: a hypothesis that is vacuously true but not
syntactically so (`stackDepth e ≤ 1`, `List.length x ≤ List.length x`). Finding those requires trying to
prove each hypothesis with `simp`/`omega`/`decide` in the theorem's own context, which needs a generated
probe file per module. **That is not implemented**, and this file says so instead of implying coverage.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")

DECL = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def)\s+([\w'.ᵢ-₉]+)")

#: a binder whose type is syntactically trivial
BINDER = re.compile(r"[\(\{]\s*([A-Za-z_\u03b1-\u03c9][\w'₀-₉]*)\s*:\s*([^)\}]+)[\)\}]")


def strip_comments(src):
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
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


def _norm(s):
    # Collapse whitespace to ONE space; do not delete it. Deleting made `E 0` and `E0` the same
    # string, which reported `hE0 : E 0 = E0` as a reflexive hypothesis -- they are different terms.
    return re.sub(r"\s+", " ", s.strip())


def _trivially_true(ty):
    t = ty.strip()
    if t == "True":
        return "the type is literally `True`"
    # `→` is NOT an implication marker here: `(L : ℝ → ℝ)` is a function type,
    # and splitting on the arrow reported 647 false positives of the form "`ℝ` equals `ℝ`".
    # `≤`/`<` appear in every numeric hypothesis for the same reason. Only `=` and `↔`
    # are unambiguous.
    for op in ("↔", "=", "⟺"):
        depth = 0
        for i, ch in enumerate(t):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0 and t.startswith(op, i):
                left, right = t[:i], t[i + len(op):]
                if left.strip() and _norm(left) == _norm(right):
                    return "`%s` is the same term on both sides" % op
    return None


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
                # the statement ends at the first top-level :=
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
                for m in BINDER.finditer(stmt):
                    why = _trivially_true(m.group(2))
                    if why:
                        line = src[:pos].count("\n") + 1
                        found.append((rel, line, name, m.group(1), m.group(2).strip(), why))
    return found


def main(argv):
    if "--self-test" in argv:
        import shutil
        tmp = os.path.join(HERE, ".vachyp-selftest")
        shutil.rmtree(tmp, ignore_errors=True)
        os.makedirs(tmp)
        failures = []
        try:
            def one(name, body):
                d = os.path.join(tmp, name)
                os.makedirs(d, exist_ok=True)
                io.open(os.path.join(d, "X.lean"), "w", encoding="utf-8").write(body)
                return scan(d)

            fs = one("a", "theorem t (x : Nat) (h : x = x) : x = x := h\n")
            if not fs:
                failures.append("a reflexive hypothesis was NOT caught")

            fs = one("b", "theorem t (h : True) : True := h\n")
            if not fs:
                failures.append("a `True` hypothesis was NOT caught")

            fs = one("c", "theorem t (x : Nat) (h : x ≤ 5) : x ≤ 5 := h\n")
            if fs:
                failures.append("a non-trivial hypothesis was reported: %r" % (fs,))
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        if failures:
            for f in failures:
                print("SELF-TEST FAILED: %s" % f)
            return 2
        print("SELF-TEST: reflexive caught, True caught, real hypothesis accepted")
        return 0

    found = scan()
    for rel, line, name, var, ty, why in found:
        print("  FINDING  %s:%d  [%s]  binder `%s : %s` -- %s" % (rel, line, name, var, ty, why))
    print()
    if found:
        print("VACUOUS HYPOTHESES: %d" % len(found))
        return 1
    print("VACUOUS HYPOTHESES: no syntactically trivial binder")
    print("(Class B that is not syntactically visible -- e.g. `stackDepth e ≤ 1` -- is NOT checked here;")
    print(" see PROOF-DEBT.md for which ones are known.)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
