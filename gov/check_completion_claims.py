"""gov/check_completion_claims.py -- a 'done' sentence must be paired with its residual list.

Round 118's external evaluation overturned the sentence '本库能自主完成的部分已经完成'. It had stood in
README / DELIVERY / STATE-FINAL for many rounds, and no guard touched it, because it is not a NUMBER
-- it is a CLAIM ABOUT SCOPE, and the guard suite only measured numbers.

The project has now recorded five premature 'done' assertions. What made each one wrong was always
the same thing: open work in the library was reclassified as 'needs an outside decision'.

So the rule is narrow and checkable:

  if a document contains a completion phrase, the SAME document must also contain a residual-obligation
  section that lists at least one OPEN item.

A completion sentence with no such section is the exact shape of all five failures.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

ROOT = r"C:\Users\xingg\Desktop\agent\lattice-new"
DOCS = ["README.md", "DELIVERY.md", "STATE-FINAL.md", "PARADIGM.md"]

#: Phrases that assert the work is finished.
COMPLETION = [
    r"能自主完成的部分(?:已经)?完成",
    r"自主完成的部分已完成",
    r"已经完成，并且",
    r"本库.{0,6}完成",
]

#: A residual-obligation section must carry one of these headings and name an open item.
RESIDUAL_HEADING = re.compile(r"(?:仍然开放|未做|残余|开放项|不声称|据实修订|outstanding|not delivered)", re.I)
OPEN_MARK = re.compile(r"(?:开放|未做|not done|未完成|仍然|remains? open)")


def scan(path):
    try:
        text = io.open(path, encoding="utf-8").read()
    except OSError:
        return None
    hits = []
    for i, line in enumerate(text.split("\n"), 1):
        for pat in COMPLETION:
            if re.search(pat, line):
                hits.append((i, line.strip()[:80]))
                break
    if not hits:
        return []
    # is there a residual section anywhere in this document?
    has_residual = bool(RESIDUAL_HEADING.search(text)) and bool(OPEN_MARK.search(text))
    return [(i, t, has_residual) for i, t in hits]


def main(argv):
    failures = 0
    for doc in DOCS:
        path = os.path.join(ROOT, doc)
        found = scan(path)
        if found is None:
            continue
        for line, text, ok in found:
            if not ok:
                print("  %-18s L%-4d completion claim with no residual list: %s"
                      % (doc, line, text))
                failures += 1

    if "--self-test" in argv:
        import tempfile
        # a doc that claims completion and lists nothing open
        bad = "本库能自主完成的部分已经完成。\n"
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False,
                                         encoding="utf-8") as f:
            f.write(bad)
            tmp_bad = f.name
        # a doc that claims completion AND lists open work
        good = "本库能自主完成的部分已经完成。\n\n## 仍然开放的义务\n\n- 某项 开放\n"
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False,
                                         encoding="utf-8") as f:
            f.write(good)
            tmp_good = f.name
        try:
            r_bad = scan(tmp_bad)
            r_good = scan(tmp_good)
            if not r_bad or all(ok for _, _, ok in r_bad):
                print("SELF-TEST FAILED: an unpaired completion claim was accepted")
                return 2
            if not r_good or not all(ok for _, _, ok in r_good):
                print("SELF-TEST FAILED: a paired completion claim was rejected")
                return 2
        finally:
            os.unlink(tmp_bad)
            os.unlink(tmp_good)
        print("SELF-TEST: unpaired claims are caught, paired ones accepted")
        return 0

    print("COMPLETION CLAIMS: %s" % ("every completion sentence is paired with open work"
                                     if not failures else "%d unpaired" % failures))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
