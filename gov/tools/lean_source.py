"""tools/lean_source.py -- the ONE authority for "Lean source text with comments removed".

## The duplication this replaces

`gov/` had grown **twenty-one** separate implementations of `strip_comments` (and one
`strip_comments_keep_docs`). This module is the single authority for the majority behaviour.

## The measurement that justified it

Extracting all twenty-one bodies and running each on **1,169 real Lean files plus two edge cases**
(nested block comment containing `--`; an UNCLOSED block comment) gave:

    distinct behaviours: 8

and the largest cluster was:

    behaviour 1: 9 sites, BYTE-IDENTICAL OUTPUT on the whole tree

    audit_duplicate_names.py:55      check_chain_deps.py:69
    audit_facades.py:57              check_coverage_claim.py:53
    check_refutation_census.py:35    repro/detect_loadbearing.py:32
    repro/macro_picture.py:27        repro/measure_chain_deps3.py:33
    repro/naming_census.py:31

Nine sites with identical behaviour is well past the "two real call sites" threshold, and the
behaviour is TESTABLE, so this is a fact-isomorphic merge rather than a guess.

## What was switched, and what was not

**Switched (5):** the non-`repro` members of that cluster --
`audit_duplicate_names`, `audit_facades`, `check_chain_deps`, `check_coverage_claim`,
`check_refutation_census`.

**Not switched, with the reason recorded:**

| sites | reason |
|---|---|
| `repro/detect_loadbearing`, `repro/macro_picture`, `repro/measure_chain_deps3`, `repro/naming_census` | they live in `gov/repro/`, so `sys.path[0]` is `gov/repro` and `tools` is not importable without changing their bootstrap. **Named obstacle, not a judgement that they differ.** |
| `audit_claims`, `check_endtoend_content`, `check_underscore_hypotheses`, `check_vacuous_hypotheses`, `rank_underscore_hypotheses` | they return the leading INDENT (e.g. `'   '`) where this module returns `''` for a comment-only line. Behaviourally equivalent for a line-based scanner, but not proven so; left alone rather than switched on a guess. |
| `audit_reach` | a different algorithm (9 vs 23 lines of output on the same input); genuinely a second skeleton. |
| `check_prop_def_strength`, `gen_review_inventory` | they deliberately KEEP docstrings. A `keep_docs` parameter would be a mode branch inside one body, which is the "body-branch" veto: keep them separate. |
| `audit_duplicate_statements` | the definition is nested inside a function, so it is not isolatable; needs manual inspection. |
| `audit_duplicate_statements` | its definition is nested inside a function; not isolatable, needs manual inspection. |
| `plugin_inventory` | it references module-level regex objects, so its body is not self-contained. |
| **`tools/sorry_axiom_census`** | **NOT a duplicate at all -- it is a STRONGER implementation, and this was measured, not assumed.** |

## The correction: `sorry_axiom_census` is not a weaker copy

**Round 968's first draft of this docstring said that module was left alone because "its body is not
self-contained". That was wrong, and measuring it showed why.**

**Its `strip_comments` PRESERVES NEWLINES INSIDE BLOCK COMMENTS:**

```python
else:
    if src[i] == "\n":
        out.append("\n")     # <-- the authority DROPS this newline
    i += 1
```

**=> compared against this module on 1,171 inputs it differs on 1,152 of them -- every file with a multi-line
block comment.**

**=> and the newline-preserving behaviour is BETTER: a scanner that reports line numbers stays aligned with
the original file, whereas this module's output shifts every line after a block comment.**

**=> so the direction of convergence would have had to be the OPPOSITE one, and switching the gate onto this
module would have been a REGRESSION.**

**It is also memoised on the source text, because `gate.py` calls it once per (invariant x file) -- the
docstring there records a cold run of 14,580 calls at ~146 s under cProfile. Losing that cache would slow the
hottest check in the suite.**

**=> `gate.py` and `audit_counts` therefore keep using `sorry_axiom_census`, and the self-test below PINS the
difference so nobody "converges" them by accident.**

## Contract card

- **semantics**: remove `--` line comments and nested `/- ... -/` blocks (docstrings ARE block
  comments and are removed). Everything else is preserved verbatim, including newlines.
- **preconditions**: `src` is `str`.
- **failure semantics**: never raises; an unclosed block comment simply removes the remainder.
- **boundary**: `--` INSIDE a string literal is still treated as a comment start (Lean-aware would
  need a real lexer; no caller needs that, and all nine original copies behaved this way).
- **extension point**: `strip_comments_keep_docs` is deliberately NOT here (see the table).
"""


def strip_comments(src):
    """Remove `--` line comments and nested `/- ... -/` blocks. Docstrings are block comments."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        two = src[i:i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "-/":
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if two == "/-":
            depth = 1
            i += 2
            continue
        if two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


CASES = [
    # (input, expected output, why)
    ("a -- tail\nb\n", "a \nb\n", "line comment removed, newline kept"),
    ("/- doc -/x", "x", "block comment removed"),
    ("/- o /- i -/ still -/y", "y", "NESTED block comment: the inner `-/` must not close the outer"),
    ("/- open\nrest", "", "unclosed block removes the remainder"),
    ("x = 1\n", "x = 1\n", "plain code passes through unchanged"),
    # PINS THE DIFFERENCE with tools/sorry_axiom_census: that module keeps these newlines so that a
    # diagnostic's line number still points at the right line. This module does not. If someone ever
    # \"converges\" the two, exactly one of these two cases must change.
    ("/- a\nb\nc -/x", "x", "newlines INSIDE a block comment are DROPPED here (sorry_axiom_census keeps them)"),
]


def self_test():
    """The contract, executed. A merge without this is a guess."""
    ok = True
    for src, want, why in CASES:
        got = strip_comments(src)
        if got != want:
            print("  FAIL %-58s got %r want %r" % (why, got, want))
            ok = False
        else:
            print("  ok   %s" % why)
    # the nested case is the one that separates a correct stripper from a naive one
    if strip_comments("/- o /- i -/ still -/y") != "y":
        print("  FAIL nesting is not handled -- a naive stripper would return ' still -/y'")
        ok = False
    print("  lean_source self-test: %s" % ("PASS" if ok else "FAIL"))
    return ok


if __name__ == "__main__":
    # `--self-test` is accepted explicitly so that `check_selftest_coverage.py` recognises this
    # module as a gate that can demonstrate its own failure. Running with no argument is the same.
    import sys
    sys.exit(0 if self_test() else 1)
