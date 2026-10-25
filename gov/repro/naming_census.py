"""Naming-convention census -- computed on comment-stripped source.

An earlier one-liner matched `theorem` inside doc comments ("theorem that consumes it: ...")
and reported three non-existent declarations. The lesson is the one this repository keeps
re-learning: any count over Lean source must strip comments first, with a NESTED-aware
stripper (`/- -/` nests).

Reports, for every theorem/lemma/def in the kernel:
  * snake_case vs not
  * names ending in `'` or containing `_aux`/`_tmp` (style smells)
  * declarations whose name claims a conclusion (`_exact`, `_sound`, `_converges`, `_e2e`,
    `end_to_end`) -- the population the roadmap's load-bearing audit must target
"""
import io
import os
import re
import sys
from collections import Counter
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
NEW = _os.path.join(_REPO, "Lattice")


def strip_comments(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if not depth and src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if not depth:
            out.append(src[i])
        i += 1
    return "".join(out)


DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(theorem|lemma|def|abbrev)[ \t]+([A-Za-z0-9_'!?]+)")

decls = []
for root, _, files in os.walk(NEW):
    if "Reference" in root:
        continue
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        code = strip_comments(io.open(p, "rb").read().decode("utf-8", errors="replace"))
        for m in DECL.finditer(code):
            decls.append((m.group(1), m.group(2), os.path.relpath(p, NEW)))

print("total declarations:", len(decls))
kinds = Counter(k for k, _, _ in decls)
print("by kind:", dict(kinds))

names = [n for _, n, _ in decls]
non_snake = [n for n in names if "_" not in n]
print("\nwithout underscore (not snake_case): %d" % len(non_snake))
print("  sample:", non_snake[:20])

primes = [n for n in names if "'" in n]
print("\nwith prime '  : %d   sample: %s" % (len(primes), primes[:10]))

suffixes = Counter()
for n in names:
    for suf in ("_aux", "_tmp", "_test", "_probe", "_example", "_2", "_3"):
        if n.endswith(suf):
            suffixes[suf] += 1
print("\nstyle-smell suffixes:", dict(suffixes))

claims = [n for n in names if re.search(r"(_exact|_sound|_converges|_e2e|end_to_end|_correct|_complete)$", n)]
print("\ndecs whose NAME claims a conclusion: %d" % len(claims))
print("  sample:", claims[:15])

byfile = Counter(f for _, _, f in decls)
print("\nfiles with most declarations:")
for f, c in byfile.most_common(8):
    print("  %-58s %d" % (f, c))
