"""Fix the three misclassifications found by spot-checking:

  1. `not (P (iterate n k))` -- a refutation that matches no predicate family. Add a
     "predicate not achieved" family for conclusions of the form `not (f ... )` where the
     conclusion is an APPLICATION (not an equality, not a quantifier).
  2. `not IsLocalMin ...` -- same shape; currently lands in "界/不等式" because the inner text
     has `<`. Families must be matched on the OUTERMOST constructor, in a fixed order.
  3. `not (x = 0) <-> ...` -- a biconditional whose left side is a negation. That IS a
     refutation-shaped statement but about an equivalence; classify by what follows the `¬`.

Rather than perfect this, classify by the OUTERMOST form and list the residual bucket
explicitly with examples.
"""
import io
import re
import sys
from collections import Counter, defaultdict
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))
_WORK = _os.path.join(_HERE, "_work")
_os.makedirs(_WORK, exist_ok=True)


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
SRC = _os.path.join(_WORK, "neg_full.txt")
recs = [tuple(l.split("\t")) for l in io.open(SRC, encoding="utf-8").read().split("\n") if l.strip()]


def strip_neg(c):
    """Strip a leading negation and any surrounding parens, to see the refuted core."""
    s = c.strip()
    s = s.lstrip("¬").strip()
    s = s.lstrip("not ").strip()
    while s.startswith("(") and s.endswith(")") and s.count("(") == 1 and s.count(")") == 1:
        s = s[1:-1].strip()
    return s


def family(c):
    core = strip_neg(c)
    if "False" in c.split("→")[-1]:
        return "矛盾不可满足 (→ False)"
    if "Injective" in core:
        return "单射性被否"
    if "Surjective" in core:
        return "满射性被否"
    if re.match(r"^(∃|exists)", core):
        return "存在性被否"
    if re.match(r"^(∀|forall)", core):
        return "全称命题被否（给出反例）"
    if "↔" in core:
        return "等价被否"
    if "=" in core and "→" not in core:
        return "等式被否（含不相等）"
    if "IsLocalMin" in core or "IsLocalMax" in core or "IsMin" in core or "IsMax" in core:
        return "极值/极小性被否"
    if any(k in core for k in ("<", "≤", ">", "≥")):
        return "界/不等式被否"
    return "谓词不可达（结论是某性质不成立）"


fam = Counter()
by = defaultdict(list)
for rel, name, c in recs:
    f = family(c)
    fam[f] += 1
    by[f].append((rel, name, c))

print("=== corrected families ===")
for f, n in fam.most_common():
    print("  %-38s %d" % (f, n))
print("\ntotal: %d" % sum(fam.values()))

print("\n=== samples from the two families that were wrong before ===")
for f in ("谓词不可达（结论是某性质不成立）", "极值/极小性被否"):
    for rel, name, c in by[f][:3]:
        print("  [%s] %s" % (f[:8], name))
        print("       %s" % c[:110])

# persist for the document
with io.open(_os.path.join(_WORK, "neg_families.txt"), "w",
             encoding="utf-8", newline="\n") as fh:
    for f, n in fam.most_common():
        fh.write("%s\t%d\n" % (f, n))
print("\nfamily counts saved")
