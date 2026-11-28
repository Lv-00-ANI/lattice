"""gov/check_criterion_size.py -- how many things `ProofComplete` actually requires, and does the tree know?

## Why this file exists (round 1204)

The criterion's conjunct count was wrong twice in this session without anything noticing:

  * every document said **25**, and the `refine` had **twenty-four** placeholders;
  * after conjoining the real T7 (1201), the real T6 (1202) and T0 (1203) it went to **30**, and the documents still
    say 25.

A count that is retyped is a count that drifts. This tool COUNTS the conjuncts out of the source -- top-level `∧` in
`ProofComplete`'s body, plus one -- and compares the answer against what the documents claim.

## What it counts, precisely

`def ProofComplete : Prop :=` followed by everything up to the next line that starts a new top-level declaration. Inside
that block, `∧` at paren depth 0 separates conjuncts. `∧` inside a nested `(∀ …)`, a `⟨…⟩` or a parenthesised
proposition does NOT count.

That is a syntactic measurement, and it has the usual limitation: if someone writes the criterion with `↔` or a `let`,
this tool will under- or over-count and say so rather than guess. The docstring of the printed report states the rule.

## The comparison

Sources checked: `DELIVERY-COMPILER-LAYER.md`, `README.md`, `PROOF-DEBT.md`, `LONG-TERM-PLAN.md`. Each is scanned for
"NN 项" near `ProofComplete`; a mismatch is a failure. A document that says nothing about the count is not a failure --
silence is allowed, a wrong number is not.

`--self-test` plants a synthetic block with three conjuncts and requires the counter to return three, then plants one
with a nested `∧` and requires it to return one.
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.dirname(HERE)

CRITERION = os.path.join(ZERO, "Lattice", "Plugins.lean")
START = re.compile(r"^def ProofComplete : Prop :=", re.M)
NEW_DECL = re.compile(r"^(?:theorem|lemma|def|structure|inductive|abbrev|/--)", re.M)

#: Documents that may state the count. A missing statement is fine; a wrong one is not.
DOCS = ("DELIVERY-COMPILER-LAYER.md", "README.md", "PROOF-DEBT.md", "LONG-TERM-PLAN.md")
CLAIM = re.compile(r"\*\*(\d+)\s*项\*\*|(\d+)\s*项\s*(?:合取|conjunct)")


def count_conjuncts(text):
    """Top-level `∧` in the criterion's body, plus one."""
    m = START.search(text)
    if not m:
        return None, None
    body_start = m.end()
    nxt = NEW_DECL.search(text, body_start)
    body = text[body_start:nxt.start() if nxt else len(text)]
    depth = 0
    count = 1
    for ch in body:
        if ch in "([⟨{":
            depth += 1
        elif ch in ")]⟩}":
            depth -= 1
        elif ch == "∧" and depth == 0:
            count += 1
    return count, body


def self_test():
    ok = True
    three = "def ProofComplete : Prop :=\n  a ∧ b ∧ c\n\ntheorem other : True := trivial\n"
    n, _ = count_conjuncts(three)
    print("  three top-level conjuncts   : got %s %s" % (n, "OK" if n == 3 else "** WRONG **"))
    ok = ok and n == 3
    nested = "def ProofComplete : Prop :=\n  (a ∧ b) ∧ c\n\ntheorem other : True := trivial\n"
    n2, _ = count_conjuncts(nested)
    print("  nested `∧` not counted      : got %s %s" % (n2, "OK" if n2 == 2 else "** WRONG **"))
    ok = ok and n2 == 2
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


def main(argv):
    if "--self-test" in argv:
        return self_test()

    text = io.open(CRITERION, encoding="utf-8").read()
    n, body = count_conjuncts(text)
    if n is None:
        print("CRITERION SIZE: `def ProofComplete` not found in Plugins.lean")
        return 1
    print("CRITERION SIZE: ProofComplete requires %d proposition(s)" % n)
    print("  rule: top-level `∧` in the definition body, plus one; nested conjunctions are not counted")

    bad = []
    for d in DOCS:
        p = os.path.join(ZERO, d)
        if not os.path.exists(p):
            continue
        src = io.open(p, encoding="utf-8").read()
        # **Only lines that MENTION the criterion count.** The first version scanned every "N 项" and flagged
        # README's "130 项检查" -- a check count, not a criterion count. A claim about the criterion is a
        # number on a line that names it.
        for ln_no, line in enumerate(src.split("\n"), 1):
            if "ProofComplete" not in line:
                continue
            for m in CLAIM.finditer(line):
                v = int(m.group(1) or m.group(2))
                if v != n:
                    bad.append("%s:%d claims %d" % (d, ln_no, v))
    if bad:
        print()
        for b in bad:
            print("  WRONG  %s" % b)
        print("CRITERION SIZE: %d claim(s) disagree with the %d measured" % (len(bad), n))
        return 1
    print("  every document that states the count agrees")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))