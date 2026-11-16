# -*- coding: utf-8 -*-
"""Replace a declaration's FULL body span (declaration through the end of its proof) with an alias.

## Why this exists

**Round 936 and 938's consolidations used a line-based rewriter that found the line containing `:=` and replaced
only that line.** **When the original body continued on following lines, the rewriter left them behind:**

```lean
theorem extract_compile_identity_vec (c : VectorConstraint) :
    extractVec (convertVec c) = c := Lattice.roundtrip_extractVec c
  roundtrip_extractVec c          <-- stray
```

**The build caught it three times (`function expected at`), but only because Lean is strict.**

**This rewriter computes the declaration's span FIRST:**
**from the `theorem` line, walk forward until the proof body ends (a line whose indentation returns to the
declaration's level, or a blank line, or an end-of-block marker), then replace that WHOLE span.**

## Contract

- **input: `(file, name, alias_expr, import)`**
- **refuses to act if the declaration is inside a doc comment (a ``` fence is open)**
- **refuses to act if the span cannot be bounded**
- **prints the exact span it replaces, so a human can audit the decision**
"""

import io
import os
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LATTICE = os.path.join(ZERO, "Lattice")


def find_decl_span(lines, name):
    """Return (start, end_exclusive, indent) of the declaration named `name`, or None.

    `end` is the first line AFTER the body: a line that is blank, dedents to the declaration's own indentation
    and is not a continuation, or starts a new top-level command.
    """
    start = None
    for k, l in enumerate(lines):
        s = l.strip()
        if s.startswith("theorem %s " % name) or s.startswith("lemma %s " % name):
            indent = len(l) - len(l.lstrip())
            start = (k, indent)
            break
    if start is None:
        return None
    k0, indent = start
    # a doc comment opened before the declaration and not closed by it means we are inside ```
    open_fence = 0
    for l in lines[:k0]:
        open_fence += l.count("```")
    if open_fence % 2 == 1:
        return ("DOC_COMMENT", k0, k0, indent)
    # walk forward
    k = k0
    seen_body = False
    while k + 1 < len(lines):
        k += 1
        cur = lines[k]
        s = cur.strip()
        if seen_body and (s == "" or s.startswith("/--") or s.startswith("/-!") or s.startswith("theorem ")
                          or s.startswith("lemma ") or s.startswith("def ") or s.startswith("end ")):
            return (k0, k, indent)
        if ":=" in cur or s.endswith(":= by") or s == "by" or s.startswith("by "):
            seen_body = True
        # a dedent below the declaration's indent also ends it
        if s != "" and (len(cur) - len(cur.lstrip())) < indent and seen_body:
            return (k0, k, indent)
        if k - k0 > 40:
            return ("UNBOUNDED", k0, k, indent)
    return (k0, len(lines), indent)


def rewrite(rel, name, alias_expr, import_line=None, dry=False):
    path = os.path.join(LATTICE, rel)
    lines = io.open(path, encoding="utf-8").read().split("\n")
    span = find_decl_span(lines, name)
    if span is None:
        return "%s: declaration not found" % rel
    if span[0] == "DOC_COMMENT":
        return "%s: SKIPPED -- inside a doc comment" % rel
    if span[0] == "UNBOUNDED":
        return "%s: SKIPPED -- span unbounded" % rel
    k0, k1, indent = span
    head = lines[k0]
    # the statement is everything up to ':=' ; if ':=' is on a later line we keep up to that line's prefix
    stmt_lines = []
    body_started = False
    for k in range(k0, k1):
        if ":=" in lines[k]:
            stmt_lines.append(lines[k].split(":=")[0].rstrip())
            body_started = True
            break
        stmt_lines.append(lines[k])
    if not body_started:
        return "%s: SKIPPED -- no ':=' inside the span" % rel
    pad = " " * indent
    new_block = stmt_lines[:-1] + [stmt_lines[-1] + ":= " + alias_expr]
    if dry:
        return "%s: would replace lines %d-%d (%d lines) with %d" % (rel, k0 + 1, k1, k1 - k0, len(new_block))
    out = lines[:k0] + new_block + lines[k1:]
    text = "\n".join(out)
    if import_line and import_line not in text:
        ls = text.split("\n")
        last = 0
        for i, l in enumerate(ls):
            if l.startswith("import "):
                last = i
        ls = ls[: last + 1] + [import_line] + ls[last + 1:]
        text = "\n".join(ls)
    io.open(path, "w", encoding="utf-8", newline="\n").write(text)
    return "%s: replaced lines %d-%d" % (rel, k0 + 1, k1)


if __name__ == "__main__":
    print("library module -- import and call rewrite()")
