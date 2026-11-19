#!/usr/bin/env python3
"""`gov/check_prop_def_strength.py` -- a `def X : Prop` whose PROOF discards its binders is not a claim.

## The failure this file exists to catch

**Round 99 found `ladder_end_to_end`.**
**It was a `def ... : Prop := ∀ {Data Tok Sym W} (L : Ladder ...), (soundness) → ∀ (d : Data) (s : Sym),
hwalk → satSym s → satW (l2l3 s)`, and its proof was `exact hsound s hsat`.**
**=> `d` and `hwalk` were BINDERS THE CONCLUSION DID NOT USE, so the proposition asserted "end to end"
while being a restatement of the L2 -> L3 rung.**

**`check_proof_strength.py` did not catch it, and could not: it analyses `theorem` bodies, and the
offending artefact was a `def ... : Prop` plus a SEPARATE theorem discharging it.**

**=> this checker looks at that pair: for each `def X : Prop` that quantifies over binders, find the
theorem proving `X` and check whether the proof's conclusion actually mentions those binders.**

## What counts as a finding

**A `def ... : Prop` whose statement binds a variable that appears NOWHERE in the proof's body.**
**That is necessary, not sufficient, for vacuity -- but it is exactly the shape the ladder had, and it is
cheap to check exactly.**

**Registered findings live in `gov/prop-def-baseline.txt`, keyed by `NAME`, so a line shift cannot silently
re-key them.**

## What this checker does NOT do

**It does not decide whether a proposition is TRUE or USEFUL, and it does not read Lean's elaboration.**
**It is a syntactic scan over the source, which is why it can be wrong in both directions: a binder used
only inside a term that the regex cannot see will look unused.**
**=> findings must be either fixed or registered WITH A REASON, and the register is the honest place for
the remainder.**
"""

import argparse
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LAT = os.path.join(ROOT, "Lattice")
BASE = os.path.join(HERE, "prop-def-baseline.txt")

#: `def NAME ... : Prop :=` -- capture the name and the rest of the declaration.
#:
#: **Round 774 (STAGE 4, gate defect G-5): the `[^\n]*` confined the match to ONE LINE, so a
#: declaration written as**
#:
#:     def X
#:         : Prop := ...
#:
#: **was invisible. This file's entire subject is `def _ : Prop`, and the pattern that finds them
#: required the type on the SAME LINE -- a formatting choice, not a semantic one.**
#:
#: **=> `(?:[^\n]*\n)*?` lets the type sit on a following line, NON-GREEDILY, so the match still
#: stops at the FIRST `: Prop :=` instead of swallowing later declarations.**
PROP_DEF = re.compile(
    r"^\s*def\s+([\w'₀-₉.]+)(?:[^\n]*\n)*?[^\n]*:\s*Prop\s*:=", re.M)

#: `theorem NAME : TARGET :=` -- capture the name and what it proves.
THEOREM = re.compile(r"^\s*theorem\s+([\w'₀-₉.]+)[^\n]*:\s*([\w'₀-₉.]+)\s*:=", re.M)

#: Binders a `∀` in the Prop body introduces.
BINDER = re.compile(r"∀|\bforall\b|\((\w+)\s*:|\{(\w+)\s*:|\⦃(\w+)\s*:")

IDENT = re.compile(r"[\w'₀-₉]+")


def strip_comments(src):
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    src = re.sub(r"--[^\n]*", "", src)
    return src


def decl_end(src, start):
    """The end offset of a declaration beginning at `start`.

    **Round 99 rewrote this five times. Each failure tried to recognise a boundary by pattern-matching
    keywords or indentation, and each got the offset arithmetic subtly wrong -- at one point the returned
    slice was a single newline, which made every binder look unused.**

    **=> the rule is now: skip the declaration's own first line, then end at the next BLANK LINE followed
    by an unindented line.** **The first-line skip is essential and was the last bug: `start` sits exactly
    at a `\\n\\n` left by the PREVIOUS declaration, so searching from `start` returned `start` itself and
    every slice came back empty.**
    """
    nl = src.find("\n", start)
    if nl == -1:
        return len(src)
    pos = nl + 1
    n = len(src)
    while True:
        j = src.find("\n\n", pos)
        if j == -1:
            return n
        k = j + 2
        while k < n and src[k] in "\n\r":
            k += 1
        if k >= n:
            return n
        if not src[k].isspace():
            return j
        pos = j + 2


def prop_binders(statement):
    """The variables the LEADING `∀`-chain of a `def X : Prop` quantifies over.

    **Round 99 rewrote this three times, and the third run is what made the checker honest.**

    **Attempt 2 collected every `∀` in the body, so the INNER quantifier of `ExactnessProp`
    (`(∀ (a b : ℕ) (d : GeoExpr n), ...)` inside a conjunction) reported `d` and `e` as discarded
    binders. Those are covered by the theorem the proof cites, so this was a false positive.**

    **Attempt 3 kept only the quantifier on the FIRST line. It then failed to detect the very defect it
    was written for: the original `ladder_end_to_end` introduced `d` and `s` on a SECOND `∀` line of
    its leading chain, so the checker saw only `L` and reported nothing.**
    **A checker that cannot see the bug it was built for is worse than no checker.**

    **=> the rule is now: binders are collected from the leading quantifier CHAIN -- consecutive lines
    beginning (possibly after indentation) with `∀`/`forall` -- and the chain stops at the first line that
    does not.**
    **That is exactly where `d` and `s` lived, and it stops before the inner `∀` of a conjunction because
    a conjunction line starts with `∧`, not `∀`.**
    """
    names = []
    started = False
    for line in statement.split("\n"):
        s = line.strip()
        # A chain link may open with `(`, `{` or `⦃` before the quantifier: `(forall s : Sym, ...) ->`.
        t = s.lstrip("({⦃ ")
        is_link = t.startswith("∀") or t.startswith("forall")
        if not is_link:
            if started:
                break
            continue
        started = True
        head = line.split(",", 1)[0]
        names += re.findall(r"\((\w+)\s*:", head)
        names += re.findall(r"\{(\w+)\s*:", head)
        names += re.findall(r"⦃(\w+)\s*:", head)
    return sorted(set(names))


def binder_prefix(decl_text):
    """The binder prefix of a `def … : Prop := ∀ …, …` body, or None if it never ends.

    **Round 1001 measured this properly instead of guessing. Of 73 "unused binder" occurrences the
    detector reported, 67 were binders used THROUGH ANOTHER BINDER'S TYPE (`ι` in `s : ι → ℝ`,
    `n` in `mask : Fin n → Fin n → Prop`) and only 6 were genuine. Three earlier attempts to encode
    that fact failed because they scanned the wrong region; this one scans the region where the fact
    lives: the body up to the first `,` or `→` at bracket depth 0.**

    **`None` when the prefix never ends -- a conjunction such as
    `(∀ {iι} (X : ι → ℝ), …) ∧ (∀ {ι} (X : ι → ℝ), …)` has no top-level comma, and treating the
    whole body as a prefix would suppress real findings.**
    """
    body = decl_text.split(":=", 1)[1] if ":=" in decl_text else decl_text
    depth = 0
    for idx, ch in enumerate(body):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        elif depth == 0 and ch in ",→":
            return body[:idx]
    return None


def scan():
    findings = []
    for dirpath, _dirs, files in os.walk(LAT):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, LAT).replace(os.sep, "/")
            src = strip_comments(io.open(path, encoding="utf-8").read())

            # All `def X : Prop :=` bodies, so we can find the theorem that discharges each.
            props = {}
            for m in PROP_DEF.finditer(src):
                name = m.group(1).split(".")[-1]
                end = decl_end(src, m.start())
                props[name] = src[m.start():end]

            for m in THEOREM.finditer(src):
                thm, target = m.group(1), m.group(2).split(".")[-1]
                if target not in props:
                    continue
                binders = prop_binders(props[target])
                if not binders:
                    continue
                end = decl_end(src, m.start())
                body = src[m.start():end]
                # **Round 99: `intro` is not USE.** A proof that opens with
                #   `intro Data Tok Sym W L hsound d s hwalk hsat; exact hsound s hsat`
                # names every binder and then ignores `d` and `hwalk`. Counting the `intro` line as
                # usage is exactly how the ladder's vacuity went unnoticed, so the scan is done over
                # the body with `intro` lines REMOVED.
                after_intro = re.sub(r"^\s*intro\b[^\n]*$", "", body, flags=re.M)
                used = set(IDENT.findall(after_intro))
                # Round 1001: a binder used through another binder's TYPE is used. See `binder_prefix`.
                prefix = binder_prefix(props[target])

                def used_in_a_binder_type(b):
                    if prefix is None:
                        return False
                    return len(re.findall(r"\b" + re.escape(b) + r"\b", prefix)) >= 2

                unused = [b for b in binders if b not in used and not used_in_a_binder_type(b)]
                if unused:
                    # Round 99 bug this replaces: the report used `name`, a LEFTOVER from the
                    # `PROP_DEF` loop above, so every finding named whichever Prop was defined LAST in
                    # the file while citing a theorem about a different one. The finding is now keyed
                    # by `target` -- the Prop the theorem actually discharges.
                    findings.append((rel, target, thm, unused))
    return findings


def load_baseline():
    if not os.path.exists(BASE):
        return {}
    out = {}
    for line in io.open(BASE, encoding="utf-8"):
        line = line.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) >= 2:
            out[parts[1]] = parts[0]
    return out


def _self_test():
    """Lock in the Round-1001 rule: a binder used through another binder's TYPE must not be reported.

    **The three earlier attempts at this rule each failed in a way the exit code did not show, so the
    behaviour is asserted here rather than described in a comment.**
    """
    ok = True

    # the case the rule exists for: `n` lives only inside `Fin n -> Fin n -> Prop`
    dependent = "def X : Prop := \u2200 {n : \u2115} (m : Fin n \u2192 Fin n \u2192 Prop), (fun i j => True) = m\n"
    pre = binder_prefix(dependent)
    if pre is None:
        print("  SELF-TEST FAIL: the dependent-binder prefix was not found")
        ok = False
    else:
        n_hits = len(re.findall(r"\bn\b", pre))
        if n_hits < 2:
            print("  SELF-TEST FAIL: `n` occurs %d time(s) in the prefix, expected >= 2" % n_hits)
            ok = False

    # the case that must NOT be suppressed: a conjunction has no top-level comma, so no prefix
    conj = "def Y : Prop := (\u2200 (a : \u2115), a = a) \u2227 (\u2200 (b : \u2115), b = b)\n"
    if binder_prefix(conj) is not None:
        print("  SELF-TEST FAIL: a conjunction produced a binder prefix, which would suppress real findings")
        ok = False

    # and a genuinely discarded binder keeps a prefix in which it occurs ONCE
    genuine = "def Z : Prop := \u2200 (a b : \u2115), a = a\n"
    pre2 = binder_prefix(genuine)
    if pre2 is None or len(re.findall(r"\bb\b", pre2)) != 1:
        print("  SELF-TEST FAIL: a discarded binder was not left at exactly one occurrence")
        ok = False

    print("PROP DEF STRENGTH SELF-TEST: %s"
          % ("dependent binder suppressed, conjunction kept, discarded binder kept" if ok else "FAILED"))
    return 0 if ok else 1


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if an UNREGISTERED prop-def finding exists")
    ap.add_argument("--self-test", action="store_true",
                    help="assert the dependent-binder rule and the conjunction guard")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    if not os.path.isdir(LAT):
        print("PROP DEF STRENGTH: no Lattice/ at %s" % LAT)
        return 1

    findings = scan()
    base = load_baseline()

    print("prop-def strength: a `def X : Prop` whose proof discards its binders")
    print("  seeded findings : %d" % len(findings))
    print("  registered      : %d" % len(base))

    new = [(rel, name, thm, unused) for (rel, name, thm, unused) in findings if name not in base]
    for rel, name, thm, unused in new:
        print("  NEW %-40s %s (proved by %s; unused: %s)"
              % (rel, name, thm, ", ".join(unused)))

    if args.check and new:
        print("\nPROP DEF STRENGTH: %d unregistered prop-def finding(s)" % len(new))
        print("  either make the proof use the binders, or register the entry WITH A REASON in")
        print("  gov/prop-def-baseline.txt")
        return 1

    if args.check:
        print("\nPROP DEF STRENGTH: no unregistered finding")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
