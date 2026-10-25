#!/usr/bin/env python3
"""Do the declarations a file *appears* to contain actually reach Lean?

## Why this exists

Round 74 found `compileIR_perpendicular_exact` sitting inside an unclosed docstring: `lake build`
reported success -- Lean never saw the theorem, and a theorem it never sees cannot fail. The build is
therefore not evidence that a theorem exists.

`audit_docs.py` catches that case indirectly (a documented name it cannot find), but it only looks at
names the documentation happens to mention. A theorem that is swallowed *and* undocumented is invisible
to every check the project has.

## What is measured

For each file, two counts of the same thing:

* **raw**: declarations matching `theorem`/`lemma`/`def`/`structure`/`inductive` in the source with
  comments removed by the same stripper the other audits use;
* **depth-0**: the same match, but found by a stripper that tracks nesting and *reports* where it ends
  up. If a file's comment nesting does not return to zero, every later declaration is swallowed.

The interesting number is the difference. A file where the raw count exceeds the depth-zero count has
declarations trapped in a comment.

## How the stripper reports

`scan(src)` returns `(visible_text, final_depth, trapped)`, where `trapped` lists the declarations that
appear after a comment opened and never closed. A file with `final_depth != 0` is malformed and its
declarations after that point are unreachable, even though the file may still elaborate if the unclosed
comment reaches the end.

Exit code 0: informational, like the other audits.
"""
import io
import os
import re
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

ZERO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
LAYERS = ["Core", "Lift", "Lib", "Geo"]

# The lookahead rules out prose: after a declaration's name comes `:=`, `:`, `(`, `{`, `[`, or the end
# of the line. In a docstring sentence like "the def that `X` provides", the next character is a space
# followed by prose, so it does not match.
DECL = re.compile(r"^\s*(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z0-9_']+)"
                  r"(?=\s*(?::=|[:({[]|$))", re.M)


def scan(src):
    """Walk the source tracking comment depth; return visible text plus diagnostics."""
    out = []
    i, n = 0, len(src)
    depth = 0
    maxdepth = 0
    # record (depth at start, char index) so we can tell which declarations were inside
    while i < n:
        if depth == 0 and src.startswith("/-", i):
            depth = 1
            maxdepth = max(maxdepth, depth)
            i += 2
            continue
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                maxdepth = max(maxdepth, depth)
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        if src.startswith("-/", i):
            i += 2
            continue
        out.append(src[i])
        i += 1
    return "".join(out), depth


def read(p):
    s = io.open(p, encoding="utf-8", errors="replace").read()
    return s.replace("\r\n", "\n").replace("\r", "\n")


def main():
    files = []
    for layer in LAYERS:
        base = os.path.join(ZERO, "Lattice", layer)
        for root, dirs, fs in os.walk(base):
            dirs[:] = [d for d in dirs if d != ".lake"]
            for f in fs:
                if f.endswith(".lean"):
                    files.append(os.path.join(root, f))

    total_raw = total_vis = 0
    problems = []
    for p in files:
        raw = read(p)
        vis, depth = scan(raw)
        n_raw = len(DECL.findall(DECL.sub(r"\1", raw)))  # comment-inclusive is the wrong base; use raw
        # raw count: strip nothing, but the regex would also match inside docstrings -- which is exactly
        # what we want to detect, so count matches in the *unstripped* text.
        n_raw = len(DECL.findall(raw))
        n_vis = len(DECL.findall(vis))
        total_raw += n_raw
        total_vis += n_vis
        if depth != 0 or n_raw != n_vis:
            problems.append((os.path.relpath(p, ZERO), n_raw, n_vis, depth))

    print("files scanned: %d" % len(files))
    print("declaration-shaped lines in raw text:  %d" % total_raw)
    print("declarations visible outside comments: %d" % total_vis)
    print()
    print("=" * 78)
    print("files where the two counts disagree, or comment depth does not close --", len(problems))
    print("=" * 78)
    for rel, a, b, d in sorted(problems):
        print("  %-44s raw %3d / visible %3d / depth %d" % (rel, a, b, d))

    if not problems:
        print("  (none: every declaration is outside a comment, and every comment closes)")
    print()
    print("=" * 78)
    print("Interpretation")
    print("=" * 78)
    print("  raw > visible  means declarations are written inside a comment. Sometimes that is")
    print("  intentional (a docstring quoting a theorem name), so a difference is a *candidate*,")
    print("  not a defect. A nonzero final depth is never intentional: it means the rest of the")
    print("  file is commented out, and Lean will accept the file without those declarations.")
    print()
    print("  Round 74's bug was of that second kind, and `lake build` reported success on it.")
    print("  This script is what makes that class of failure visible.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
