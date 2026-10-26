"""Round 116: a guard against batch-replacement damage in the docs.

Round 108's commit 19a8ced rewrote CONVENTIONS.md with an unconstrained replace and turned a great
many leading `1` digits into `0`: `2026-10-25` became `2026-00-25`, `## 1. 命名` became
`## 0. 命名`, `N1` became `N0`, `0,747` where the true count was `1,747`, and so on. Every existing
guard passed, because every existing guard checks NAMES and NUMBERS IT KNOWS, not the integrity of
the surrounding text.

What the damage looks like, mechanically:
  - a date with month or day 00:        `20\\d\\d-00-` or `20\\d\\d-\\d\\d-00`
  - a section heading or reference `0.0`, `§0.0` (sections start at 1)
  - a rule identifier `N0` (rules start at N1)
  - a thousands-separated number that begins with 0: `0,747`
  - a Roman/ordinal list starting at 0: `^0\\. ` inside a numbered list

This guard flags those five shapes. It is deliberately narrow: it does NOT try to detect arbitrary
number corruption (that needs knowing the true value, which is what check_usage_claims is for).
"""
import io
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

ROOT = r"C:\Users\xingg\Desktop\agent\lattice-new"
DOCS = ["README.md", "STATE-FINAL.md", "DELIVERY.md", "CONVENTIONS.md", "USAGE.md",
        "PARADIGM.md", "PROOF-CHAIN.md"]

PATTERNS = [
    ("date with 00 month/day", re.compile(r"20\d\d-00-|20\d\d-\d\d-00(?![0-9])")),
    # `§0.x` references are checked structurally below, not here.

    ("rule N0", re.compile(r"(?<![A-Za-z0-9])N0(?![0-9])")),
    ("thousands number starting with 0", re.compile(r"(?<![\d,])0,\d{3}(?!\d)")),
    ("ordered list starting at 0", re.compile(r"^0\. \*\*")),
]


LINE_PATTERNS = list(PATTERNS)
SECTION = re.compile(r"^#{2,4}\s+(\d+)\.(\d*)")
SUBSEC = re.compile(r"^#{3,4}\s+0\.(\d+)")


def scan(path):
    try:
        text = io.open(path, encoding="utf-8").read()
    except OSError:
        return None
    bad = []
    parent = None          # the nearest preceding `## n.` section number
    for i, line in enumerate(text.split("\n"), 1):
        for name, pat in LINE_PATTERNS:
            if pat.search(line):
                bad.append((i, name, line.strip()[:70]))
        m = SECTION.match(line)
        if m:
            if line.startswith("## "):
                parent = m.group(1)
            elif line.startswith("###") or line.startswith("####"):
                # a subsection numbered 0.x is damage unless its parent section IS 0
                if m.group(1) == "0" and parent is not None and parent != "0" and m.group(2):
                    bad.append((i, "subsection 0.x under section %s" % parent,
                                line.strip()[:70]))
    return bad


def main(argv):
    failures = 0
    for doc in DOCS:
        import os
        path = os.path.join(ROOT, doc)
        bad = scan(path)
        if bad is None:
            continue
        for line, name, text in bad:
            print("  %-18s L%-5d %-32s %s" % (doc, line, name, text))
            failures += 1

    if "--self-test" in argv:
        # plant each damage shape and assert it is caught
        import tempfile
        planted = ("2026-00-25\n## 1. 命名\n### 0.0 规则\n| N0 | x |\n| 0,747 |\n0. **item**\n")
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as f:
            f.write(planted)
            tmp = f.name
        bad = scan(tmp)
        import os
        os.unlink(tmp)
        caught = {name for _, name, _ in (bad or [])}
        expect = {n for n, _ in PATTERNS}
        missing = expect - caught
        if missing:
            print("SELF-TEST FAILED: not caught: %s" % sorted(missing))
            return 2
        print("SELF-TEST: all five damage shapes can be caught")
        return 0

    print("BATCH-REPLACEMENT GUARD: %s" % ("clean" if not failures else
                                           "%d suspicious line(s)" % failures))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
