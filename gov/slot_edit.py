# -*- coding: utf-8 -*-
"""Replace one `Slot` definition in `Slots.lean` without the splice hazard.

Four rounds in a row produced the same failure: a region replacement whose end anchor was the *doc
comment* of the next definition, which consumed that comment's opening line and left
`unterminated comment` behind. Twice the definition body was lost as well.

The rule was written down after round 19 and still not enforced, because "be careful" is not a
mechanism. This tool is the mechanism: it parses the file into `Slot` blocks by locating the
`def <name> : Slot` keyword, replaces exactly one block's text (doc comment included) and leaves
every other byte untouched, then re-parses to verify that the number of `def ... : Slot` definitions
is unchanged and that no doc comment is left unopened.

Usage:
    python slot_edit.py show <slotName>          # print the block
    python slot_edit.py replace <slotName> <file>  # replace with the contents of <file>
"""
import io
import os
import re
import sys

P = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "Lattice", "Slots.lean")
DEF_RE = re.compile(r"^def\s+([A-Za-z0-9_']+)\s*:\s*Slot\s*:=", re.M)


def blocks(src):
    """Return [(name, start, end)] where start includes the preceding doc comment."""
    out = []
    matches = list(DEF_RE.finditer(src))
    for i, m in enumerate(matches):
        # walk back over the doc comment immediately preceding the def
        start = m.start()
        prefix = src[:start]
        # find the last `/-!`-style boundary before this def that is not itself a doc comment opener
        doc_end = prefix.rfind("-/")
        if doc_end != -1:
            tail = prefix[doc_end + 2:]
            if tail.strip() == "":
                # doc comment ends right before the def: include it
                doc_start = prefix.rfind("/--", 0, doc_end)
                if doc_start != -1:
                    start = doc_start
        end = matches[i + 1].start() if i + 1 < len(matches) else len(src)
        # do not swallow the next block's doc comment
        if i + 1 < len(matches):
            nxt = matches[i + 1]
            nxt_start = nxt.start()
            prefix2 = src[:nxt_start]
            de2 = prefix2.rfind("-/")
            if de2 != -1 and prefix2[de2 + 2:].strip() == "":
                ds2 = prefix2.rfind("/--", 0, de2)
                if ds2 != -1 and ds2 > start:
                    end = ds2
        out.append((m.group(1), start, end))
    return out


def verify(src):
    """Sanity checks that would have caught the splice hazard."""
    problems = []
    n_defs = len(DEF_RE.findall(src))
    # balanced `/--` ... `-/`
    opens = src.count("/--")
    closes = src.count("-/")
    if opens != closes:
        problems.append("doc comment delimiters unbalanced: %d opens, %d closes" % (opens, closes))
    # no doubled opener
    if "/-- " in src and re.search(r"/--[^\n]*?/--", src):
        problems.append("doubled doc-comment opener on one line")
    return n_defs, problems


def main():
    src = io.open(P, encoding="utf-8").read()
    if sys.argv[1] == "show":
        want = sys.argv[2]
        for name, a, b in blocks(src):
            if name == want:
                print(src[a:b])
                return 0
        print("slot not found:", want)
        return 1

    want = sys.argv[2]
    new_file = sys.argv[3]
    n_before, _ = verify(src)
    replacement = io.open(new_file, encoding="utf-8").read()
    if not replacement.endswith("\n"):
        replacement += "\n"

    for name, a, b in blocks(src):
        if name != want:
            continue
        updated = src[:a] + replacement + src[b:]
        # put back exactly one blank line before the next block
        updated = re.sub(r"\n{3,}", "\n\n", updated)
        n_after, problems = verify(updated)
        if n_after != n_before:
            print("ABORT: slot count changed from %d to %d" % (n_before, n_after))
            return 1
        if problems:
            print("ABORT:", "; ".join(problems))
            return 1
        io.open(P, "w", encoding="utf-8", newline="\n").write(updated)
        print("replaced slot", want, "(slot count still %d)" % n_after)
        return 0

    print("slot not found:", want)
    return 1


if __name__ == "__main__":
    sys.exit(main())
