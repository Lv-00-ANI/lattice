"""gov/check_proof_strength.py -- catch the three shapes of NOMINALLY-COMPLETE proofs.

## Why this file exists And what it is NOT

The project's completion standard has been "it has a name, it is a theorem, it has 0 `sorry`". Lean
checks exactly that and nothing more: it verifies the theorem is TRUE, never that it is STRONG. So a
theorem whose proof is `exact h`, or whose conclusion is `p = p`, or which covers 4 of 12 constructors,
imports and cites exactly like a complete one.

**This checker is deliberately narrow.** It catches three shapes that are syntactically decidable, where
a finding is not a judgement call:

  A. **reflexive statement**  -- the conclusion is literally `a = a`, `a ↔ a`, or `a → a`.
     No proof of such a statement can carry information. Zero false positives: it is pure syntax.

  B. **bare-hypothesis proof** -- the whole proof is `exact h` / `assumption` / `simpa using h` where
     `h` is one of the theorem's own binders. The theorem restates a hypothesis. This is the shape of
     `l2l3_sound := exact h` and of the first version of `approx_ladder_bound_mono`.

  C. **`Prop`-valued `def` named `True`-like** -- e.g. a field `conflict_free : R.conflicts =
     R.conflicts`. Shape A catches this one at the field level too.

**What it does NOT catch, and I am saying so rather than implying coverage:**

  - a theorem that is TRUE and NON-tautological but covers 4 of 12 constructors;
  - a theorem with a hypothesis that is vacuous but not syntactically so (round 187 found one: an
    `unused variable` warning, which the compiler does catch);
  - a theorem that is correct but whose STRENGTH is below what downstream claims.

Those need the coverage counts and the strength lattice, which are separate. **A checker that claims to
verify "proof strength" while only verifying syntax would be the very defect it is meant to catch.**

## Rule for "finding" vs "registered"

Same discipline as the rest of `gov/`: a finding is a failure unless it is registered in `ALLOWED` with a
reason. `ALLOWED` entries are checked for rot -- an entry whose site no longer exists fails, so the
registry cannot accumulate dead excuses.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")

#: `(file, decl_name) -> reason`. Keyed by NAME, not line: deleting a line elsewhere in the file
#: would otherwise silently move every registration onto a different theorem.
#:
#: Only `bare-hypothesis` can be registered. A **reflexive** conclusion (`a = a`, `a <-> a`,
#: `a -> a`) has no legitimate use -- the statement carries no information whatever the proof is --
#: so it is a failure unconditionally. That asymmetry is the point: `exact h` can be an honest
#: interface lemma (a definitional unfolding), but `a = a` never is.
ALLOWED = {}

#: Theorem/lemma/def start. Captures the name so the report is readable.
DECL_START = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|instance)\s+([\w'.ᵢ-₉]+)")

#: strip line comments and block comments so that docstring code blocks are not scanned
def strip_comments(src):
    out = []
    i = 0
    n = len(src)
    depth = 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                break
            out.append(" " * (j - i))
            i = j
            continue
        if src.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
            continue
        out.append(src[i] if depth == 0 else ("\n" if src[i] == "\n" else " "))
        i += 1
    return "".join(out)


def _split_statement(block):
    """Return `(statement, proof)` split at the first top-level `:=` or `where`."""
    # find `:=` at bracket depth 0
    depth = 0
    i = 0
    n = len(block)
    while i < n - 1:
        ch = block[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and block.startswith(":=", i):
            return block[:i], block[i + 2:]
        i += 1
    return block, ""


def _binder_names(statement):
    """Local hypothesis names introduced by the statement's binder groups."""
    names = set()
    # `(h : P)` / `{h : P}` / `(hε : 0 < ε)` / `[inst : C]`
    for m in re.finditer(r"[\(\{\[]\s*([A-Za-z_\u03b1-\u03c9][\w'₀-₉]*)\s*:", statement):
        names.add(m.group(1))
    # `(h1 h2 : P)` -- several names before one colon
    for m in re.finditer(r"[\(\{]\s*([A-Za-z_\u03b1-\u03c9][\w'₀-₉]*(?:\s+[A-Za-z_\u03b1-\u03c9][\w'₀-₉]*)+)\s*:", statement):
        for nm in m.group(1).split():
            names.add(nm)
    return names


def _normalize(expr):
    return re.sub(r"\s+", "", expr)


def _conclusion(statement):
    """The conclusion: everything after the LAST top-level `:` that is not a binder colon.

    Taking the FIRST colon is wrong -- `theorem bad (x : Nat) : x = x` would yield `Nat) : x = x`
    from the binder's colon, which is how the first version failed its own self-test.
    """
    depth = 0
    last = -1
    for i, ch in enumerate(statement):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ch == ":" and not statement.startswith(":=", i):
            last = i
    return statement[last + 1:] if last >= 0 else statement


def _reflexive(statement):
    """True if the conclusion is `a = a` / `a ↔ a` / `a → a` (same text both sides)."""
    concl = _conclusion(statement).strip()
    for op in ("↔", "=", "→", "⟺"):
        depth = 0
        for i, ch in enumerate(concl):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0 and concl.startswith(op, i):
                left = concl[:i]
                right = concl[i + len(op):]
                if left.strip() and _normalize(left) == _normalize(right):
                    return True, op
    return False, None


def _bare_hypothesis(proof, binders):
    """True if the proof is nothing but one of the theorem's own hypotheses."""
    p = proof.strip()
    p = re.sub(r"^by\s*", "", p)
    p = re.sub(r";?\s*$", "", p).strip()
    for pat in (r"exact\s+([\w'₀-₉]+)$", r"([\w'₀-₉]+)$",
                r"assumption$", r"simpa(?:\s+only\s*\[[^\]]*\])?\s+using\s+([\w'₀-₉]+)$"):
        m = re.match(pat, p)
        if not m:
            continue
        if m.lastindex is None:
            return True, "assumption"
        nm = m.group(1)
        if nm in binders:
            return True, nm
    return False, None


def _declares_prop(stmt):
    """True when a declaration's TYPE is `Prop` -- e.g. `def foo : Prop := ...`.

    **Round 773.** The `def` exemption in `scan` must not cover `Prop`-valued defs: those are
    propositions, and the whole point of this checker is that a proposition's proof should not be
    a tautology. Detecting it syntactically is enough for the same reason the rest of this file is
    syntactic: a `Prop`-typed declaration is `: Prop` at the top level of its statement.
    """
    flat = " ".join(stmt.split())
    return flat.rstrip().endswith(": Prop") or " : Prop :=" in flat or flat.rstrip().endswith(":Prop")


def scan(root=None):
    root = root or LAT
    findings = []   # (rel, line, kind, detail)
    for dirpath, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, root).replace("\\", "/")
            raw = io.open(p, "rb").read().decode("utf-8", "replace")
            src = strip_comments(raw)
            starts = [(m.start(), m.group(1), m.group(2)) for m in DECL_START.finditer(src)]
            for idx, (pos, kind, name) in enumerate(starts):
                end = starts[idx + 1][0] if idx + 1 < len(starts) else len(src)
                block = src[pos:end]
                line = src[:pos].count("\n") + 1
                stmt, proof = _split_statement(block)
                binders = _binder_names(stmt)
                # A `def` declares a TERM, not a proof. Its body being `fun x => ...` or a
                # constructor is not a tautology, and treating it as one is a false positive --
                # which the first version produced (`def quant: proof is just `a -> a``).
                #
                # **Round 773 (STAGE 4, gate defect G-4): the exemption above is TOO WIDE.**
                # `def X : Prop := <statement>` declares a PROPOSITION, and a proposition is
                # exactly the kind of declaration whose "proof" can be a tautology. **The audit
                # named this blind spot: `check_proof_strength` was structurally immune to
                # `def ... : Prop`, so a `Prop`-valued def could be reflexive or bare-hypothesis
                # and no gate would say so.**
                # **=> narrow the exemption: skip `def` UNLESS its declared type is `Prop`.**
                if kind not in ("theorem", "lemma"):
                    if not _declares_prop(stmt):
                        continue
                is_refl, op = _reflexive(stmt)
                if is_refl:
                    findings.append((rel, line, "reflexive", "%s %s: conclusion is `a %s a`"
                                     % (kind, name, op)))
                    continue
                if proof.strip():
                    bare, h = _bare_hypothesis(proof, binders)
                    if bare:
                        findings.append((rel, line, "bare-hypothesis",
                                         "%s %s: proof is just `%s`" % (kind, name, h)))
    return findings


def main(argv):
    if "--self-test" in argv:
        import shutil
        tmp = os.path.join(HERE, ".strength-selftest")
        shutil.rmtree(tmp, ignore_errors=True)
        os.makedirs(tmp)
        failures = []
        def one(name, body):
            """Scan a directory holding exactly one file, so the three cases cannot contaminate
            each other. The first version reused one directory and reported its own fixtures as
            false positives."""
            d = os.path.join(tmp, name)
            os.makedirs(d, exist_ok=True)
            io.open(os.path.join(d, "X.lean"), "w", encoding="utf-8").write(body)
            return scan(d)

        try:
            fs = one("a", "theorem bad (x : Nat) : x = x := rfl\n")
            if not [f for f in fs if f[2] == "reflexive"]:
                failures.append("a reflexive conclusion was NOT caught")

            fs = one("b", "theorem bad2 (p q : Prop) (h : p -> q) : p -> q := by exact h\n")
            if not [f for f in fs if f[2] == "bare-hypothesis"]:
                failures.append("a bare-hypothesis proof was NOT caught")

            fs = one("c", "theorem good (x : Nat) : x + 0 = x := by omega\n")
            if fs:
                failures.append("a genuine proof was reported: %r" % (fs,))

            # a `def` body is a term, not a proof -- must not be reported
            fs = one("d", "def f (x : Nat) : Nat := x\n")
            if fs:
                failures.append("a `def` was treated as a proof: %r" % (fs,))
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        if failures:
            for f in failures:
                print("SELF-TEST FAILED: %s" % f)
            return 2
        print("SELF-TEST: reflexive caught, bare hypothesis caught, genuine proof accepted,"
              " `def` not treated as a proof")
        return 0

    findings = scan()

    # Two-way baseline discipline: the baseline may only shrink.
    #
    # Round 237. The baseline is keyed on (path, line, shape), so a `git mv` makes every entry for the
    # moved file look BOTH "paid off" (old path vanishes from the scan) AND "new" (the finding now
    # appears at the new path). That is the same orphaning defect as PROOF-DEBT's key join, and it is
    # fixed the same way: map the baseline's path through `PATH_MAP` before comparing. The baseline
    # FILE is not edited by a move -- only the map is.
    sys.path.insert(0, HERE)
    try:
        from _debt_path_map import PATH_MAP
    except ImportError:
        PATH_MAP = {}
    base_path = os.path.join(HERE, "proof_strength_baseline.txt")
    baseline = {}
    if os.path.exists(base_path):
        for ln in io.open(base_path, encoding="utf-8"):
            ln = ln.rstrip("\n")
            if not ln or ln.startswith("#"):
                continue
            parts = ln.split("\t")
            if len(parts) >= 4:
                parts[0] = PATH_MAP.get(parts[0], parts[0])
                # Round 238. The key used to include the LINE NUMBER, which made the baseline break on
                # any edit that added or removed a line above the theorem -- including a purely
                # mechanical import rewrite. Round 238 hit exactly that: rewriting 127 import lines with
                # `^import ...\s*$` swallowed a following blank line in two files, shifting two
                # theorems from 93 to 92 and from 128 to 127, and the baseline reported them as BOTH
                # "new finding" and "paid off" for the same theorems.
                # The name is already in the entry and is unique within a file, so (path, kind, name) is
                # a stable key. The line is kept in the file for a human reader, not for the join.
                baseline[(parts[0], parts[2], parts[3])] = parts[3]

    bad = 0
    fired = set()
    for rel, line, kind, detail in findings:
        name = detail.split(":")[0].split()[-1]
        key = (rel, kind, name)
        fired.add(key)
        if kind == "reflexive":
            print("  FINDING  %s:%d  [reflexive]  %s" % (rel, line, detail))
            print("           `a = a` carries no information whatever the proof is -- delete it")
            bad += 1
        elif key in baseline:
            print("  known    %s:%d  [%s]  %s  (see PROOF-DEBT.md)" % (rel, line, kind, name))
        else:
            print("  FINDING  %s:%d  [%s]  %s" % (rel, line, kind, detail))
            print("           not in the baseline -- either fix the statement or add it WITH a reason")
            bad += 1

    for key, name in sorted(baseline.items()):
        if key not in fired:
            print("  PAID OFF %s  [%s]  %s -- delete this line from the baseline"
                  % (key[0], key[1], name))
            bad += 1

    print()
    if bad:
        print("PROOF STRENGTH: %d problem(s)" % bad)
        return 1
    print("PROOF STRENGTH: %d known shape(s), none new, none paid off silently"
          % len(baseline))
    print("(Syntax only. Coverage counts and the strength lattice are separate -- see PROOF-DEBT.md.)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
