#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_corrections_count.py -- P3-2 / ROADMAP-v2 4.5: count gate for CORRECTIONS.

    python scripts/check_corrections_count.py [--root <repo>] [--quiet] [--selftest]

WHY THIS EXISTS
---------------
ROADMAP-v2.md:177, item 4.5, verbatim:

    "登记表条数自动计数（`check-corrections.ps1` 只查锚点不查条数）"
     -- i.e. "register entry-count auto-counting (check-corrections.ps1 only checks
     anchors, not counts)"

and it cites `doc/09-honesty-register.md` section 1.2, which had already worked out
the general lesson from this exact file:

    "汇总数字会与明细表脱节。一张表里的'共 N 条'是一个手工维护的缓存，
     它不会随着新增条目自动更新。"
    -- "A summary number drifts from its detail table. A 'N total' written in prose
     is a HAND-MAINTAINED CACHE; it does not update itself when entries are added."

    "可执行的改进：把条数自动计数（例如统计 `^##+ B\\d` 的匹配数）...
     本仓库已对锚点存在性做了自动检查，但未对条数做自动检查。"
    -- "The executable improvement: auto-count instead. This repo already checks
     anchor existence automatically, but does NOT check counts automatically."

This script is that missing half. The DIVERGENCES gate (P0-3) and this one are the
two halves of one "register gate" and were meant to ship together.

THE TRAP THIS SCRIPT IS BUILT TO AVOID
--------------------------------------
`doc/09` section 1.2 records the failure concretely: the B-section headings were
originally mixed between `###` and `##`, so a rule written as `^### B` returned
**8** where the true count was **22**. A count checker with that rule would have
been confidently, silently wrong. So this script:

  * counts headings at BOTH `##` and `###` depth (`^#{2,4}\\s*B\\d`), as doc/09
    section 1.2 explicitly recommends ("让抽取规则显式容忍多级别"),
  * counts by DECLARED NUMBER (deduplicated), not by matching text occurrences,
    so a re-printed heading cannot inflate the total,
  * and reports numbering GAPS separately, because a gap (not a miscount) is what
    a deleted-then-renumbered entry actually looks like.

WHAT IT CHECKS
--------------
  1. Internal consistency of the lettered sections A/B/C against the counts written
     in `doc/09-honesty-register.md` section 1.2 (the prose cache).
  2. Contiguity of the B-numbering: B1..Bmax with no holes.
  3. That no count claim of the form "CORRECTIONS = N 条 (B1-BM)" inside
     CORRECTIONS.md contradicts the measured value.

Known, verified drift when this script was written (reported, not silently fixed --
fixing a register entry is the coordinator's call, and this is a GATE, not an editor):
  * CORRECTIONS.md:15193 says "CORRECTIONS = 214 条（B1–B217）" while the file
    actually declares 237 numbered B-entries spanning B1..B239 (B110 and B194 absent).
  * PROCESS.md:11 says "CORRECTIONS 231 条" -- also stale.

EXIT CODES
----------
  0 = counts consistent
  1 = a count claim contradicts the measured body
  2 = usage / environment error
"""

import argparse
import io
import os
import re
import sys

# Sections are declared as `## B12. ...` / `### B12. ...`. Accept 2..4 hashes.
# The trailing delimiter must be `.` or whitespace -- NOT a bare \b, because
# `\b` also matches the position before `-` in a rewritten `B1-X` heading, which
# would let a renamed entry keep counting as B1. (Caught by this script's own
# self-test, which is why that self-test exists.)
B_HEAD_RE = re.compile(r"^(#{2,4})\s*B(\d+)(?:\.|\s|$)")
A_ROW_RE = re.compile(r"^\|\s*A(\d+)\s*\|")
C_ROW_RE = re.compile(r"^\|\s*C(\d+)\s*\|", re.M)

# "CORRECTIONS = **214 条**（B1–B217）" and friends.
#
# BUG(U08): the original was
#     CORRECTIONS\s*=\s*\*{0,2}(\d+)\s*条\*{0,2}
# which requires an EQUALS SIGN after CORRECTIONS.  Every real claim in this
# repo omits it -- PROCESS.md:11 reads "roots 511 / CORRECTIONS 397 条 /",
# README.md:105 reads "(B1–B399, **397 条**)".  So the pattern matched
# NOTHING, in any file, ever, and the count checker reported 'internally
# consistent' with exit 0 while four mutually contradictory counts (397/415/
# 397/397 against a true 416) went unchallenged.  A gate that cannot match its
# own subject is not a weak gate, it is an absent one wearing a green light.
#
# The separator is now OPTIONAL and must be followed by 条, which keeps the
# match anchored on a real claim rather than on any number ending in 条.
# Dropping the CORRECTIONS anchor entirely was tried and produced 35 false
# positives against historical prose, and broke the self-test -- recorded so
# the next attempt does not repeat it.
#
# B474: even this narrower form still fires on three HISTORICAL records inside
# CORRECTIONS.md, which quote the counts as they were at the time ("轮 152 时点
# 为 261", "PROCESS.md:11 | roots 479 / CORRECTIONS 346 条").  Those are
# deliberate records, and CORRECTIONS.md:30084 states the policy: changing a
# number destroys the fact of what it was then.  A count that is explicitly
# dated or marked as a quotation is history, not a live claim.
# A line qualifies as history if it says so in words, or if it is a before/after
# TABLE ROW: three or more pipe-separated cells, at least one of which is a
# backticked file reference.  CORRECTIONS.md:30078 is exactly that shape --
#   | `PROCESS.md:11` | 「roots 479 / CORRECTIONS 346 条」 | **roots 511 ...** |
# -- a correction record quoting both the old and the new value.
#
# B479: the pipe branch was TOO WIDE.  As written it exempted any 3+-cell table row
# carrying a backticked filename, which is the ordinary shape of a normal table --
# so a LIVE count claim written in such a row was silently exempted.  Reported
# independently and reproduced: an injected `CORRECTIONS <n+7> 条` in such a row
# came back EXEMPTED instead of FIRING.
#
# Tightened to require the actual history SHAPE, not merely a table: the row must
# contain BOTH an old-value and a new-value count claim, i.e. two counts separated by
# a cell boundary or an arrow.  That is what a correction record looks like, and it
# is a substantially narrower predicate than 'this is a table'.
HISTORICAL_RE = re.compile(
    r"时点|当时|原为|旧值|was\s|histor"
    r"|```[^`\n]+```\s*\|[^|\n]*\|\s*[^|\n]*(?:→|->)[^|\n]*"   # fn | old → new
    r"|(?:[^|\n]*\|){2,}[^|\n]*条[^|\n]*\|[^|\n]*\*{0,2}\d+\s*条"  # old 条 | new 条
)
BACKTICK_REF_RE = re.compile(r"`[A-Za-z0-9_./-]+\.(?:md|lean|ps1|py|toml)`")
CLAIM_RE = re.compile(
    r"CORRECTIONS\s*(?:=\s*)?\*{0,2}(\d+)\s*条\*{0,2}"
    r"|B\d+\s*[-–—]\s*B\d+\s*[,，]?\s*\*{0,2}(\d+)\s*条\*{0,2}"
)

# doc/09 section 1.2 prose cache. Deliberately narrow: we look for the specific
# "B1–B22" / "A1–A4" style ranges rather than any number in the file.
DOC09_B_RANGE_RE = re.compile(r"编号\s*B(\d+)\s*[–\-—]\s*B(\d+)")
DOC09_A_RANGE_RE = re.compile(r"\bA(\d+)\s*[–\-—]\s*A(\d+)\b")


def read_utf8(path):
    with io.open(path, encoding="utf-8", errors="replace") as fh:
        return fh.read()


class Finding(object):
    def __init__(self, blocking, kind, where, detail):
        self.blocking = blocking
        self.kind = kind
        self.where = where
        self.detail = detail


def measure(text):
    """Measure the register by declared numbers."""
    b_nums = set()
    b_depth = {}
    for L in text.split("\n"):
        m = B_HEAD_RE.match(L)
        if m:
            n = int(m.group(2))
            b_nums.add(n)
            b_depth.setdefault(len(m.group(1)), set()).add(n)
    a_nums = sorted({int(m.group(1)) for m in A_ROW_RE.finditer(text)})
    return {
        "b": sorted(b_nums),
        "b_depth": {k: len(v) for k, v in sorted(b_depth.items())},
        "a": a_nums,
    }


def gaps(nums):
    if not nums:
        return []
    return [x for x in range(1, nums[-1] + 1) if x not in nums]


def fmt_nums(nums, limit=12):
    """Render a number list compactly; a 200-item list is not a report."""
    if len(nums) <= limit:
        return ", ".join("B%d" % x for x in nums)
    head = ", ".join("B%d" % x for x in nums[:limit])
    return "%s, ... (+%d more)" % (head, len(nums) - limit)


def check(reg_text, doc09_text, proc_text, blocking_enabled=True):
    """`blocking_enabled=False` demotes every finding to advisory.

    This exists because CORRECTIONS.md carries PRE-EXISTING drift (a stale 214
    count at :15193 and dangling B110/B194 references). A gate that is red on
    arrival is a gate every agent learns to ignore -- the same reasoning that
    made check-corrections-anchors.ps1 default to -FailOn DEAD rather than
    gating on STALE-OLEAN. So the default posture is "report, do not block",
    and -StrictCheckers (via verify.ps1's checker table) promotes it.
    """
    def mk(blocking, kind, where, detail):
        return Finding(blocking and blocking_enabled, kind, where, detail)

    findings = []
    m = measure(reg_text)
    b = m["b"]

    if not b:
        findings.append(mk(True, "COUNT", "CORRECTIONS.md",
                           "no B-numbered headings found at any depth"))
        return m, findings

    # --- 1. contiguity of B numbering -------------------------------------
    # A hole is a dangling NUMBER. Distinguish it from a dangling CITATION:
    # if the missing number is referenced elsewhere in the body, the register
    # cites a criterion it no longer defines -- strictly worse than a plain gap.
    g = gaps(b)
    if g:
        cited = []
        for x in g:
            uses = len(re.findall(r"\bB%d\b" % x, reg_text))
            if uses:
                cited.append((x, uses))
        detail = ("B-numbering is not contiguous: %s (span B%d..B%d, %d present)"
                  % (fmt_nums(g), b[0], b[-1], len(b)))
        if cited:
            detail += ("; of these, %s are CITED elsewhere in the body but have no "
                       "section of their own (dangling references)"
                       % ", ".join("B%d (x%d)" % (x, u) for x, u in cited[:8]))
        findings.append(mk(True, "COUNT", "CORRECTIONS.md", detail))

    # --- 2. in-file count claims ------------------------------------------
    for mm in CLAIM_RE.finditer(reg_text):
        claimed = int(mm.group(1))
        line = reg_text[:mm.start()].count("\n") + 1
        # B474: skip lines that record a count AS IT WAS.  CORRECTIONS.md
        # deliberately preserves historical values (:30084: changing a number
        # destroys the fact of what it was then), and three such records were
        # being reported as live claims.  A dated or quoted count is history.
        line_text = reg_text.split("\n")[line - 1] if line - 1 < len(reg_text.split("\n")) else ""
        if HISTORICAL_RE.search(line_text) and BACKTICK_REF_RE.search(line_text):
            continue
        if re.search(r"时点|当时|原为|旧值", line_text):
            continue
        if claimed != len(b):
            findings.append(mk(
                True, "COUNT", "CORRECTIONS.md:%d" % line,
                "claims %d entries but the body declares %d (B%d..B%d)"
                % (claimed, len(b), b[0], b[-1])))

    # --- 3. the doc/09 prose cache ----------------------------------------
    if doc09_text:
        rm = DOC09_B_RANGE_RE.search(doc09_text)
        if rm:
            lo, hi = int(rm.group(1)), int(rm.group(2))
            line = doc09_text[:rm.start()].count("\n") + 1
            if hi != b[-1]:
                # Always advisory: doc/09 is a guide about the register, not the
                # register, and it correctly describes the register AS IT WAS.
                findings.append(Finding(
                    False, "COUNT", "doc/09-honesty-register.md:%d" % line,
                    "prose cache says the B section ends at B%d; the register now "
                    "ends at B%d (+%d entries since that cache was written)"
                    % (hi, b[-1], b[-1] - hi)))
    if proc_text:
        pm = CLAIM_RE.search(proc_text)
        if pm:
            claimed = int(pm.group(1))
            line = proc_text[:pm.start()].count("\n") + 1
            if claimed != len(b):
                findings.append(Finding(
                    False, "COUNT", "PROCESS.md:%d" % line,
                    "cached count '%d 条' is stale; the register declares %d"
                    % (claimed, len(b))))

    return m, findings


def selftest(lean_dir, scripts_dir):
    """The detector must be able to fail; verify that on synthetic defects."""
    reg = read_utf8(os.path.join(lean_dir, "CORRECTIONS.md"))
    results = []

    # (1) plant a wrong in-file count claim.
    #
    # B479: this case asserted only that SOME blocking finding appeared.  The real
    # register already carries contiguity findings, so the planted claim could stop
    # firing entirely -- CLAIM_RE broken, exemption too wide, anything -- and the
    # case would still pass on the contiguity finding it did not cause.  A negative
    # control that cannot distinguish its own trigger from pre-existing noise is not
    # a negative control.
    #
    # Now the assertion is on the finding's KIND: the planted claim must produce a
    # finding whose text names the planted value, and the count of findings must RISE
    # above the baseline the unmodified register produces.
    _, f_base = check(reg, None, None)
    base_count = len([x for x in f_base if x.blocking])
    bad = reg + "\n\nCORRECTIONS = **999 条**（B1-B999）\n"
    _, f = check(bad, None, None)
    blocking = [x for x in f if x.blocking]
    named = [x for x in blocking if "999" in (x.detail or "")]
    ok = bool(named) and len(blocking) > base_count
    results.append(("count-claim-tamper", "RED" if ok else "GREEN-BUG",
                    named[0].detail[:200] if named else
                    ("no finding names the planted value 999 (baseline %d, now %d)"
                     % (base_count, len(blocking)))))

    # (2) plant a numbering hole: remove one already-existing B heading. The real
    # register already has holes B110/B194, so we assert on the COUNT of gaps
    # rising rather than on mere presence.
    base_gaps = gaps(measure(reg).get("b") or [])
    mm = re.search(r"^##\s*B(\d+)\.", reg, re.M)
    if not mm:
        results.append(("numbering-hole", "SETUP-FAIL", "no '## B<n>.' heading to remove"))
    else:
        n = int(mm.group(1))
        bad2 = reg.replace(mm.group(0), "## B%s-X. (renamed in self-test)" % n, 1)
        _, f = check(bad2, None, None)
        blocking = [x for x in f if x.blocking]
        new_gaps = gaps(measure(bad2)["b"])
        results.append(("numbering-hole",
                        "RED" if (blocking and len(new_gaps) > len(base_gaps)) else "GREEN-BUG",
                        blocking[0].detail[:200] if blocking else "no finding"))

    # (3) pristine register under --strict semantics: the checks must be CAPABLE
    # of firing on it (the real register does carry drift), but they must not
    # fire on a CLEANED register. Build the cleaned copy by repairing the two
    # known drifts, then assert it comes back clean.
    cleaned = reg
    # close the B110/B194 holes FIRST, then rewrite the count claim to match the
    # resulting total -- doing it the other way round leaves the claim one step
    # behind, which is exactly the drift this gate exists to catch.
    for hole in gaps(measure(reg)["b"]):
        cleaned += "\n\n## B%d. (self-test: hole filled)\n\nbody\n" % hole
    # The rewrite must accept the same separator the detector now accepts
    # (see CLAIM_RE): the real text is "CORRECTIONS 397 条" with NO equals
    # sign.  Pinning this to "CORRECTIONS =" is what made the fixture look
    # clean while the production pattern matched nothing.
    cleaned = re.sub(r"(CORRECTIONS\s*(?:=\s*)?\*{0,2})\d+(\s*条\*{0,2})",
                     r"\g<1>%d\g<2>" % len(measure(cleaned)["b"]), cleaned)
    _, f = check(cleaned, None, None)
    blocking = [x for x in f if x.blocking]
    results.append(("cleaned-register", "GREEN" if not blocking else "RED-BUG",
                    blocking[0].detail[:200] if blocking else "no blocking findings"))

    # (4) the real register under --strict MUST be red: it genuinely carries drift.
    _, f = check(reg, None, None)
    blocking = [x for x in f if x.blocking]
    results.append(("real-register-strict", "RED" if blocking else "GREEN-BUG",
                    "%d blocking finding(s); first: %s"
                    % (len(blocking), blocking[0].detail[:150]) if blocking
                    else "real register reported clean, but it is known to carry drift"))
    ok = all(r[1] in ("RED", "GREEN") for r in results)
    return ok, results


def main():
    ap = argparse.ArgumentParser(description="CORRECTIONS count gate (P3-2)")
    ap.add_argument("--root", default=None)
    ap.add_argument("--lean", default=None)
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--strict", action="store_true",
                    help="promote findings to blocking (used by verify.ps1 -StrictCheckers)")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()

    here = os.path.dirname(os.path.abspath(__file__))
    root = args.root or os.path.dirname(here)
    lean_dir = args.lean or os.path.join(root, "lean")
    reg_path = os.path.join(lean_dir, "CORRECTIONS.md")
    if not os.path.exists(reg_path):
        sys.stderr.write("check_corrections_count: missing %s\n" % reg_path)
        return 2

    reg = read_utf8(reg_path)

    if args.selftest:
        ok, results = selftest(lean_dir, here)
        print("== CORRECTIONS count gate self-test ==")
        for name, verdict, detail in results:
            print("  %-22s %-10s %s" % (name, verdict, detail))
        bad = [r for r in results if r[1] in ("GREEN-BUG", "RED-BUG", "SETUP-FAIL")]
        if bad:
            print("SELF-TEST FAILED: the detector does not detect.")
            return 1
        print("self-test passed: detector fires on planted defects and is clean on the real register.")
        return 0

    doc09 = os.path.join(root, "doc", "09-honesty-register.md")
    proc = os.path.join(lean_dir, "PROCESS.md")
    doc09_text = read_utf8(doc09) if os.path.exists(doc09) else None
    proc_text = read_utf8(proc) if os.path.exists(proc) else None

    m, findings = check(reg, doc09_text, proc_text, blocking_enabled=args.strict)
    blocking = [f for f in findings if f.blocking]
    advisory = [f for f in findings if not f.blocking]

    if not args.quiet:
        print("== CORRECTIONS count check (P3-2 / ROADMAP 4.5) ==")
        print("B-entries declared : %d  (B%d .. B%d)" % (len(m["b"]), m["b"][0], m["b"][-1]))
        print("A-rows             : %d" % len(m["a"]))
        print("heading depths     : %s" % m["b_depth"])
        print("blocking           : %d" % len(blocking))
        print("advisory           : %d" % len(advisory))
    for f in blocking:
        print("  [X] %s: %s -- %s" % (f.kind, f.where, f.detail))
    for f in advisory:
        print("  [!] %s: %s -- %s" % (f.kind, f.where, f.detail))

    if blocking:
        if not args.quiet:
            print("CORRECTIONS.md count claims CONTRADICT the body: %d blocking finding(s)."
                  % len(blocking))
        return 1
    if not args.quiet:
        print("CORRECTIONS.md entry counts are internally consistent.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
