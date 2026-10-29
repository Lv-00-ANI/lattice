"""gov/check_comment_shadow_declarations.py -- `theorem`-shaped text inside comments, split by intent.

## The incident this exists for (round 54)

Round 53 added a theorem to `Lib/Chain/RealEndToEnd.lean` with a **string anchor**. The anchor matched the
**first** occurrence of `symbolToWeight_correct cs x`, which lives inside a **fenced code block in the module
docstring** -- the file *quotes* `extract_to_weights` to explain it. So the new declaration landed **inside a
comment**.

**The build passed** (comment text is not elaborated) and **`audit_counts` correctly did not count it**
(`strip_comments` removes comments; the docstring there says exactly that). Round 53's commit message blamed the
counter -- *"a theorem placed high in that file was invisible to the counter"* -- **and that accusation was
wrong: the counter was right, the insertion was in a comment.** Only after moving it to line 595 did the count
become 8,689.

**So the missing instrument is not "does the counter see it" -- the counter saw it fine. It is "did my text land
in a comment", and nothing reported that.**

## What this reports, and why it does not fail

Three shapes, and only the first is definitely fine:

  1. `theorem`-shaped text inside a comment **inside a ``` fence** -- the file is *quoting* code. Normal, and in
     `RealEndToEnd.lean` it is deliberate.
  2. `theorem`-shaped text inside a comment **outside any fence** -- could be prose, or could be an insertion
     that went wrong. **Worth looking at, not worth failing on**: a docstring may legitimately write
     "theorem `foo` says ..." in prose.
  3. `theorem`-shaped text in code -- the ordinary case.

**Report-only**, with the counts, because turning shape 2 into a gate would produce findings that cannot be
fixed beyond rewording.

## The rule this exists to make checkable

    After adding a declaration, the declaration count must MOVE.

That is discipline, not a gate -- but the reason round 53's slip was catchable at all is that the count did
**not** move. This file makes the same information available **at the moment of the edit** rather than one
`audit_counts` run later.
"""

import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ROOT, "Lattice")

THEOREM_LINE = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                          r"noncomputable[ \t]+)*(?:theorem|lemma)[ \t]+([A-Za-z0-9_'.\u2080-\u209c]+)")
FENCE = re.compile(r"^\s*```")


def comment_spans(src):
    """Spans of `/- ... -/` block comments and `--` line comments. Deliberately simple: nested block comments
    are handled by depth counting, which is what Lean does."""
    spans = []
    i, n = 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            spans.append((i, j))
            i = j
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            spans.append((i, j))
            i = j
        else:
            i += 1
    return spans


def inside(spans, pos):
    for a, b in spans:
        if a <= pos < b:
            return (a, b)
    return None


def fenced(src, start, end, pos):
    """Is `pos` between fences within the comment `[start, end)`?"""
    depth = 0
    i = start
    while i < pos:
        nl = src.find("\n", i)
        if nl < 0 or nl >= pos:
            break
        if FENCE.match(src[i:nl]):
            depth = 1 - depth
        i = nl + 1
    return depth == 1


def self_test():
    """The two functions that can be wrong are `comment_spans` and `fenced`; test them on one snippet."""
    ok = True
    src = ("/-! doc\n```\ntheorem quoted : True := trivial\n```\ntheorem that is prose\n-/\n"
           "theorem real : True := trivial\n")
    spans = comment_spans(src)
    m = THEOREM_LINE.search(src, src.index("```\n") + 4)
    sp = inside(spans, m.start()) if m else None
    if sp is None:
        print("  SELF-TEST: a theorem inside a docstring was reported as code")
        ok = False
    elif not fenced(src, sp[0], sp[1], m.start()):
        print("  SELF-TEST: a theorem inside a ``` fence was not seen as fenced")
        ok = False
    m2 = THEOREM_LINE.search(src, src.index("theorem real"))
    if inside(spans, m2.start()) is not None:
        print("  SELF-TEST: a real theorem was reported as being in a comment")
        ok = False
    m3 = THEOREM_LINE.search(src, src.index("theorem that is prose"))
    sp3 = inside(spans, m3.start()) if m3 else None
    if sp3 is None or fenced(src, sp3[0], sp3[1], m3.start()):
        print("  SELF-TEST: prose inside a docstring but outside a fence was misclassified")
        ok = False
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2
def main(argv):
    shape1 = shape2 = shape3 = 0
    suspicious = []
    for root, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            src = io.open(p, encoding="utf-8", errors="replace").read()
            spans = comment_spans(src)
            for m in THEOREM_LINE.finditer(src):
                sp = inside(spans, m.start())
                if sp is None:
                    shape3 += 1
                elif fenced(src, sp[0], sp[1], m.start()):
                    shape1 += 1
                else:
                    shape2 += 1
                    suspicious.append((rel, src[:m.start()].count("\n") + 1, m.group(0).strip()[:70]))

    print("COMMENT SHADOW DECLARATIONS (`theorem`-shaped text, by where it landed)")
    print("  in code (ordinary)                        : %d" % shape3)
    print("  in a comment, inside a ``` fence (quote)  : %d" % shape1)
    print("  in a comment, NOT in a fence (look at it) : %d" % shape2)
    if suspicious:
        print()
        for rel, line, text in suspicious[:15]:
            print("   %-44s :%-5d %s" % (rel, line, text))
        if len(suspicious) > 15:
            print("   ... and %d more" % (len(suspicious) - 15))
    print()
    print("REPORT-ONLY: a `theorem` in a comment is not a declaration. If you just added one and the")
    print("declaration count did not move, look here first -- round 53 lost a theorem to a fenced quote.")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
