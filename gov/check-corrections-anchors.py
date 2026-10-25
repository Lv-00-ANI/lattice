#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""check-corrections-anchors.py -- equivalent Python port of
scripts/check-corrections-anchors.ps1 (F7: cross-check every CORRECTIONS.md
entry against the source tree, and say honestly which anchors cannot be
machine verified).

Port target : lattice HEAD 9d3fd85
Source      : scripts/check-corrections-anchors.ps1 (440 lines, LF-only,
              pure ASCII, no BOM)
Reference   : scripts/tests/test_check_corrections_anchors.py (the port's own
              suite: behaviour, exit codes, the parity gate against the .ps1,
              and the negative controls)

    python  scripts/check-corrections-anchors.py
    python  scripts/check-corrections-anchors.py --self-test
    python  scripts/check-corrections-anchors.py --section B
    python  scripts/check-corrections-anchors.py --out-file lean/CORRECTIONS-ANCHORS.md

WHAT IT CLASSIFIES. Every backticked `Module.name` token in CORRECTIONS.md goes
into exactly one bucket:

    RESOLVED      declaration found, and its file has a fresh olean
    STALE-OLEAN   declaration found, but the olean is missing or older than source
    DEAD          declaration NOT found in the named module
    NEEDS-HUMAN   the token is not a theorem reference (file name, concept,
                  mathlib API, prose) -- a human must confirm it
    ALLOWLISTED   explicitly retired, per scripts/corrections-allowlist.txt

READ-ONLY BY DEFAULT. A default invocation WRITES NOTHING. It only reads
lean/CORRECTIONS.md, lean/<Module>.lean, the olean mtimes under
lean/.lake/build/lib/, and scripts/corrections-allowlist.txt. `--out-file` is
the single writer and is opt-in; it emits a DERIVED report (the repository's own
invocation targets lean/CORRECTIONS-ANCHORS.md), never source. No subprocess, no
Lean toolchain and no lock is involved, which is why this script is one of the
"zero-lock read-only" checkers (doc/17-S10-REGISTRY-AUDIT.md:366) and lands in
the migration plan's M1 "pure read" batch (doc/29-...:100).

EXIT CODES (the .ps1's own contract, L34-37)
    0 = no findings in the states selected by --fail-on
    1 = at least one finding in a selected state
    2 = usage error (an unrecognised --fail-on state)

MEASURED ON THE .ps1 (2026-10-12, HEAD 9d3fd85, Windows PowerShell 5.1.26100.9444,
both implementations captured through subprocess pipes):

  * stdout is LF-ONLY (0x0A), never CRLF: `Write-Host` emits LF through a pipe
    even on Windows. This port pins sys.stdout to newline="\n", so its stdout is
    BYTE-IDENTICAL to the .ps1's. (No newline deviation has to be registered,
    unlike the sibling check-roots-census port.)
  * `-FailOn BOGUS` exits 2 and prints the diagnostic on STDOUT -- it is a
    Write-Host, not a Write-Error -- with EMPTY stderr and no other output.
    Note the ORDER: the classification runs BEFORE --fail-on is validated
    (L294-352), so a bad --fail-on still does all the work and then prints only
    that one line.
  * A MISSING CORRECTIONS.md exits 1, NOT 2. The .ps1's own header documents
    "2 = usage error", but L281 is `Write-Error ...; exit 2` and
    `$ErrorActionPreference = 'Stop'` (L76) turns Write-Error into a TERMINATING
    error, so the script dies at Write-Error and the `exit 2` on the same line
    never executes. This port reproduces the MEASURED behaviour (exit 1), not
    the documented one.

DEVIATIONS (registered, each with the measurement that fixes it)

  D1  USAGE-ERROR EXIT CODE. The .ps1 declares
      [ValidateSet('A','B','C','D','ALL')] on -Section, so PowerShell rejects an
      out-of-set value during PARAMETER BINDING: measured exit 1, stderr, empty
      stdout. An unknown parameter name behaves the same way. The port reports
      any usage error as exit 2 -- the script's OWN documented usage-error code
      -- with the usage text on stderr and empty stdout. Exit code 2 is
      otherwise reachable in both implementations only through the --fail-on
      path, which is byte-identical.
  D2  STDERR TEXT for a missing CORRECTIONS.md. PowerShell formats a whole
      ErrorRecord (script path, CategoryInfo, FullyQualifiedErrorId, source
      position); the port writes the single line `missing <path>`. The exit code
      and the empty stdout are identical; only the diagnostic prose differs.
  D3  UNREADABLE SOURCE. `$ErrorActionPreference = 'Stop'` makes ReadAllText /
      Get-Item terminating errors. The port models that at the top level (an
      OSError is reported on stderr and the process exits 1) rather than
      swallowing it, so a source that cannot be read still fails the run
      instead of being classified as if it were empty.
  D4  -OutFile LINE SEPARATOR. [System.IO.File]::WriteAllLines uses
      Environment.NewLine, so the report is CRLF on Windows and LF elsewhere;
      the port uses os.linesep, which is the same rule.

CASE SENSITIVITY, PRESERVED EXACTLY (this is not cosmetic). The .NET regex
statics are case-SENSITIVE while the PowerShell operators and hashtable key
lookups are case-INSENSITIVE, and this script leans on BOTH. The split is kept:

    ANCHOR_RE, SECTION_RE, the declaration regex   -> case-sensitive
    '\.lean$' / '\.md$'            (ps1 -match)    -> re.IGNORECASE
    the B-entry heading scan       (ps1 -match)    -> re.IGNORECASE
    allowlist membership           (hashtable key) -> case-insensitive
    the `anchor` repeat key        (hashtable key) -> case-insensitive
    the literal `anchor` line search (String.Contains, ordinal) -> case-SENSITIVE

Deliberate non-reproduction: nothing here models $ErrorActionPreference,
$LASTEXITCODE or the culture-dependent collation, because this script has no
Sort-Object, no native child process and no [int]/[math] cast on anything but a
positive whole-second difference.
"""

import argparse
import os
import re
import sys
import time

# ---------------------------------------------------------------- exit codes
EXIT_PASS = 0
EXIT_BLOCKING = 1
EXIT_USAGE = 2

# ps1 L340. The order matters twice: it is the expansion of -FailOn ALL and the
# row order of the summary table in the -OutFile report.
VALID_STATES = ("RESOLVED", "STALE-OLEAN", "ALLOWLISTED", "NEEDS-HUMAN", "DEAD")
# ps1 L432: the states that produce the "advisory" line when they do not block.
ADVISORY_STATES = ("DEAD", "STALE-OLEAN", "NEEDS-HUMAN")
# ps1 L406: the order of the per-state sections in the -OutFile report.
REPORT_GROUPS = ("DEAD", "STALE-OLEAN", "NEEDS-HUMAN", "RESOLVED")
# ps1 L67: [ValidateSet('A','B','C','D','ALL')].
VALID_SECTIONS = ("A", "B", "C", "D", "ALL")

# ---------------------------------------------------------------------------
# Regexes, kept verbatim from the .ps1
# ---------------------------------------------------------------------------
# ps1 L87: [regex]'`([A-Za-z][A-Za-z0-9_]*\.[A-Za-z_][A-Za-z0-9_.]*)`'
# Used through [regex]::Matches, i.e. case-SENSITIVE.
ANCHOR_RE = re.compile(r"`([A-Za-z][A-Za-z0-9_]*\.[A-Za-z_][A-Za-z0-9_.]*)`")

# ps1 L125: [regex]::Match($lines[$i], '^##\s+([A-Z])[\.\s]') -- case-sensitive.
SECTION_RE = re.compile(r"^##\s+([A-Z])[\.\s]")

# ps1 L253/L256: $Anchor -match '\.lean$' / '\.md$'. The -match OPERATOR is
# case-insensitive, so `Foo.LEAN` is a file reference here, not a declaration.
LEAN_SUFFIX_RE = re.compile(r"\.lean$", re.IGNORECASE)
MD_SUFFIX_RE = re.compile(r"\.md$", re.IGNORECASE)

# ps1 L310: $sec.Lines[$k] -match '^#{2,3}\s+(B[0-9]+[a-z]?|[A-D][0-9]+)'.
# Also the -match operator, hence case-insensitive.
ENTRY_RE = re.compile(r"^#{2,3}\s+(B[0-9]+[a-z]?|[A-D][0-9]+)", re.IGNORECASE)

# ps1 L92-94: Get-DeclRegex builds this by concatenating a literal prefix with
# [regex]::Escape($Name). re.escape() is the direct analogue, and for the names
# this script can emit -- Get-AnchorClass always passes the LAST dot-separated
# component of a token ANCHOR_RE matched, i.e. [A-Za-z0-9_]* -- it is the
# identity, exactly as [regex]::Escape is.
DECL_PREFIX = (
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|example)\s+"
    r"(?:[A-Za-z_][A-Za-z0-9_]*\.)*"
)


def _decl_regex(name):
    """ps1 L89-95: Get-DeclRegex."""
    return re.compile(DECL_PREFIX + re.escape(name) + r"\b")


# ---------------------------------------------------------------------------
# PowerShell value semantics this script actually depends on
# ---------------------------------------------------------------------------

# Join-Path rewrites the FOREIGN separator in the child (and only there). Measured
# on Windows PowerShell 5.1 for this machine:
#     Join-Path 'C:\a' 'b/c'   -> C:\a\b\c      ('/' becomes '\')
#     Join-Path 'C:\a' 'b//c'  -> C:\a\b\\c     (no collapsing)
#     Join-Path 'C:\a' './b'   -> C:\a\.\b      ('.' is NOT resolved)
#     Join-Path 'C:\a\' 'b'    -> C:\a\b        (a base separator is not doubled)
#     Join-Path 'C:\a' ''      -> C:\a\         (an empty child still gets one)
# So Join-Path is concatenation plus separator normalisation -- never a lexical
# normalisation of '.' or '..'.
_FOREIGN_SEP = "\\" if os.sep == "/" else "/"


def _join(base, child):
    """Join-Path. PS keeps the literal string; a child is NOT re-anchored."""
    b = base.rstrip("\\/")
    if b == "":
        return child
    return b + os.sep + child.replace(_FOREIGN_SEP, os.sep)


def _exists(path):
    """Test-Path: existence of the literal path string.

    A DIRECTORY answers True, exactly as Test-Path does -- which is what makes
    "a directory where a .lean file is expected" a reachable state (see D3).
    """
    try:
        return os.path.exists(path)
    except OSError:
        return False


def _read_text(path):
    """[System.IO.File]::ReadAllText($path, UTF8Encoding($false)).

    .NET's File.ReadAllText constructs its StreamReader with
    detectEncodingFromByteOrderMarks: true, so a leading BOM is consumed rather
    than returned as U+FEFF; and UTF8Encoding($false) is the non-throwing
    decoder, i.e. malformed bytes become U+FFFD. Python's 'utf-8-sig' plus
    errors='replace' is that same pair.
    """
    with open(path, "rb") as fh:
        raw = fh.read()
    return raw.decode("utf-8-sig", errors="replace")


def _ps_int_cast(value):
    """`[int]` on a positive double.

    PowerShell's [int] cast routes through Convert.ToInt32(double), which rounds
    HALF TO EVEN; so does Python's round(). The only value this is applied to is
    a positive whole-second difference between two file timestamps.
    """
    return int(round(value))


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------

def _test_olean_fresh(lean_dir, module):
    """ps1 L97-115: Test-OleanFresh. Returns (state, why).

    `lake build` writes .lake/build/lib/<Module>.olean, or a nested path for a
    dotted module name; both spellings are tried in the .ps1's order.
    """
    candidates = (
        _join(lean_dir, os.path.join(".lake", "build", "lib", module + ".olean")),
        _join(lean_dir, os.path.join(".lake", "build", "lib",
                                     module.replace(".", os.sep) + ".olean")),
    )
    src = _join(lean_dir, module + ".lean")
    for candidate in candidates:
        if not _exists(candidate):
            continue
        if not _exists(src):
            return ("stale", "olean exists but source is gone")
        o = os.path.getmtime(candidate)
        s = os.path.getmtime(src)
        if o >= s:
            return ("fresh", "olean newer than source")
        return ("stale", "olean older than source by %ds" % _ps_int_cast(s - o))
    return ("missing", "no olean found under .lake/build/lib")


def _anchor_class(anchor, lean_dir, allow):
    """ps1 L247-275: Get-AnchorClass. Returns (state, why).

    The bucket order is load-bearing: the allowlist wins over everything, and a
    file/document reference is decided BEFORE the module lookup, so
    `RealKL.lean` is never called DEAD for lacking a declaration named `lean`.
    """
    # ps1 L250: $Allow.ContainsKey($Anchor) -- a PowerShell hashtable literal
    # compares keys case-INSENSITIVELY, so the allowlist is keyed lowercased.
    if anchor.lower() in allow:
        return ("ALLOWLISTED", "retired per corrections-allowlist.txt")
    if LEAN_SUFFIX_RE.search(anchor):
        return ("NEEDS-HUMAN", "reference to a FILE, not a theorem")
    if MD_SUFFIX_RE.search(anchor):
        return ("NEEDS-HUMAN", "reference to a sibling document, not a theorem")
    parts = anchor.split(".")
    mod = parts[0]
    leaf = parts[-1]
    src = _join(lean_dir, mod + ".lean")
    if not _exists(src):
        return ("NEEDS-HUMAN",
                "module '%s' not in this repo (mathlib API or a concept name?)" % mod)
    if not _decl_regex(leaf).search(_read_text(src)):
        return ("DEAD", "no declaration '%s' in %s.lean" % (leaf, mod))
    fresh = _test_olean_fresh(lean_dir, mod)
    if fresh[0] == "fresh":
        return ("RESOLVED", fresh[1])
    return ("STALE-OLEAN", fresh[1])


def _section_anchors(text, section):
    """ps1 L117-138: Get-SectionAnchors. Returns [(section_letter, [lines])].

    Split on top-level `## X.` headings. A section with no body lines is
    DROPPED (the .ps1 only appends when $buf.Count -gt 0), and the lines before
    the first heading form a section whose letter is the empty string.
    """
    lines = re.split(r"\r?\n", text)
    out = []
    cur = ""
    buf = []
    for line in lines:
        m = SECTION_RE.match(line)
        if m:
            if buf:
                out.append((cur, buf))
            cur = m.group(1)
            buf = []
            continue
        buf.append(line)
    if buf:
        out.append((cur, buf))
    # ps1 L136: `if ($Section -eq 'ALL')` -- -eq is case-insensitive, and the
    # raw value is still what gets PRINTED, so the caller's spelling is kept.
    if section.upper() == "ALL":
        return out
    want = section.upper()
    return [s for s in out if s[0] == want]


def _collect_rows(sections, lean_dir, allow):
    """ps1 L294-321: the main anchor sweep. Returns a list of row dicts."""
    rows = []
    seen = set()
    for section, lines in sections:
        body = "\n".join(lines)
        for m in ANCHOR_RE.finditer(body):
            anchor = m.group(1)
            # ps1 L303: $key = "$($sec.Section)|$a" into a hashtable, so a
            # repeat is detected case-INSENSITIVELY: within one section,
            # `Alpha.ncd` and `alpha.ncd` are ONE finding.
            key = ("%s|%s" % (section, anchor)).lower()
            if key in seen:
                continue
            seen.add(key)
            state, why = _anchor_class(anchor, lean_dir, allow)
            # ps1 L308-312: the nearest preceding B<n>/A<n> heading. The scan
            # BREAKS at the first line carrying the anchor, and String.Contains
            # is ordinal, so this search is case-SENSITIVE even though the
            # heading match above is not.
            entry = ""
            for line in lines:
                em = ENTRY_RE.match(line)
                if em:
                    entry = em.group(1)
                if ("`" + anchor + "`") in line:
                    break
            rows.append({"section": section, "entry": entry, "anchor": anchor,
                         "state": state, "why": why})
    return rows


# ---------------------------------------------------------------------------
# Inputs
# ---------------------------------------------------------------------------

def _repo_dir():
    """ps1 L78: (Resolve-Path (Join-Path $PSScriptRoot '..')).Path.

    The repository is the PARENT OF THIS SCRIPT'S DIRECTORY -- the same rule the
    .ps1 uses, and the reason the test suite can relocate a copy of either
    implementation into a synthetic tree without any new flag.
    """
    here = os.path.dirname(os.path.abspath(__file__))
    return os.path.dirname(here)


def _read_allowlist(scripts_dir):
    """ps1 L285-292. Returns a lowercase-keyed dict (case-insensitive keys)."""
    allow = {}
    path = _join(scripts_dir, "corrections-allowlist.txt")
    if _exists(path):
        for line in _read_text(path).split("\n"):
            s = line.split("#")[0].strip()
            if s != "":
                allow[s.lower()] = True
    return allow


def _parse_fail_on(fail_on):
    """ps1 L338-352. Returns (fail_states, bad_state_or_None).

    An unrecognised name must NOT silently disable the gate, so it is a usage
    error rather than an empty (always-passing) set.
    """
    fail_states = []
    for part in fail_on.split(","):
        t = part.strip().upper()
        if t == "":
            continue
        if t == "ALL":
            fail_states = list(VALID_STATES)
            break
        if t not in VALID_STATES:
            return None, t
        fail_states.append(t)
    # ps1 L352: @($failStates | Select-Object -Unique) -- case-insensitive,
    # order-preserving. The values are already uppercase, so this is a dedupe.
    uniq = []
    for s in fail_states:
        if s not in uniq:
            uniq.append(s)
    return uniq, None


# ---------------------------------------------------------------------------
# The -OutFile report (the ONLY writer in this script, and it is opt-in)
# ---------------------------------------------------------------------------

def _write_report(out_file, repo_dir, section, rows, by_state):
    """ps1 L382-417. Writes the derived Markdown report; returns its path."""
    out_path = out_file if os.path.isabs(out_file) else _join(repo_dir, out_file)
    lines = [
        "# CORRECTIONS anchor cross-check",
        "",
        "> Generated by scripts\\check-corrections-anchors.ps1 (F7).",
        "> %s ; section %s ; anchors %d" % (time.strftime("%Y-%m-%d %H:%M"),
                                            section, len(rows)),
        ">",
        "> RESOLVED = declaration present and its olean is newer than the source.",
        "> STALE-OLEAN = declaration present but not currently compiled, so the",
        '>   "machine-verified counterexample" claim is not backed right now.',
        "> NEEDS-HUMAN = the token is a file name / concept / mathlib API rather than",
        ">   a theorem of this repo; a human must confirm. Never silently accepted.",
        "> DEAD = the named module exists but declares no such name.",
        "",
        "## Summary",
        "",
        "| state | count |",
        "|:--|--:|",
    ]
    for k in VALID_STATES:
        lines.append("| %s | %d |" % (k, len(by_state.get(k, []))))
    lines.append("")
    for group in REPORT_GROUPS:
        members = by_state.get(group, [])
        lines.append("## %s" % group)
        lines.append("")
        if not members:
            lines.append("(none)")
            lines.append("")
            continue
        lines.append("| entry | anchor | why |")
        lines.append("|:--|:--|:--|")
        for r in members:
            lines.append("| %s | `%s` | %s |" % (r["entry"], r["anchor"], r["why"]))
        lines.append("")
    # ps1 L415: [System.IO.File]::WriteAllLines uses Environment.NewLine between
    # every element AND after the last one (see D4).
    data = "".join(line + os.linesep for line in lines)
    with open(out_path, "wb") as fh:
        fh.write(data.encode("utf-8"))
    print("wrote %s" % out_path)
    return out_path


# ---------------------------------------------------------------------------
# -SelfTest (ps1 L142-243): the built-in suite, which NEVER falls through to the
# main path -- Invoke-SelfTest ends in `exit`.
# ---------------------------------------------------------------------------

def _self_test(lean_dir):
    print("== check-corrections-anchors -SelfTest ==")
    passed = 0
    failed = 0
    ran = 0

    # 1. The declaration regex must match each declaration keyword form, and
    #    must NOT match a prefix of a longer name (the trailing \b).
    cases = (
        ("theorem foo_bar : True := trivial", "foo_bar", True),
        ("lemma baz (x : Nat) : x = x := rfl", "baz", True),
        ("private theorem priv : True := trivial", "priv", True),
        ("noncomputable def ncd : Nat := 1", "ncd", True),
        ("theorem NS.qualified : True := trivial", "qualified", True),
        ("theorem foo_bar_baz : True := trivial", "foo_bar", False),
    )
    for source, name, want in cases:
        ran += 1
        got = _decl_regex(name).search(source) is not None
        if got == want:
            passed += 1
        else:
            failed += 1
            print("  [FAIL] decl match '%s' in '%s' want %s got %s"
                  % (name, source, want, got))

    # 2. Anchor extraction: dotted backticked tokens only, prose ignored.
    prose = ("entry cites `RealKLJointConvex.ce_not_joint_convex` and "
             "`RealMEMIT.memit_edit_verdict`, plus the file `RealKL.lean`, and "
             "plain text not_an_anchor.")
    ran += 1
    found = [m.group(1) for m in ANCHOR_RE.finditer(prose)]
    if ("RealKLJointConvex.ce_not_joint_convex" in found
            and "RealMEMIT.memit_edit_verdict" in found
            and "RealKL.lean" in found
            and "not_an_anchor" not in found):
        passed += 1
    else:
        failed += 1
        print("  [FAIL] anchor extraction produced: %s" % ", ".join(found))

    # 3. A .lean token is a FILE reference: NEEDS-HUMAN, never DEAD.
    #    CRITERION 13: assert the (State, Why) PAIR, not the state alone -- a
    #    classifier neutralised into returning NEEDS-HUMAN for the WRONG reason
    #    (the module-absent branch) passes a state-only assertion with
    #    byte-identical output.
    ran += 1
    state, why = _anchor_class("RealKL.lean", lean_dir, {})
    if state == "NEEDS-HUMAN" and "reference to a FILE" in why:
        passed += 1
    else:
        failed += 1
        print("  [FAIL] 'RealKL.lean' want NEEDS-HUMAN/*reference to a FILE* got %s/%s"
              % (state, why))

    # 4. A module that does not exist is NEEDS-HUMAN (it could be a mathlib
    #    concept); DEAD is reserved for "module exists but the name does not".
    ran += 1
    state, why = _anchor_class("NoSuchModule.no_such_lemma", lean_dir, {})
    if state == "NEEDS-HUMAN" and "not in this repo" in why:
        passed += 1
    else:
        failed += 1
        print("  [FAIL] unknown module want NEEDS-HUMAN/*not in this repo* got %s/%s"
              % (state, why))

    # 5. A module that DOES exist, with a lemma that does not, is DEAD. A missing
    #    fixture is a FAILURE, not a silent skip: the .ps1 used to guard this
    #    case with `if ($existing)`, so running the same bytes from a directory
    #    with no lean/ tree made the case VANISH while the suite still printed a
    #    pass.
    ran += 1
    if not _exists(_join(lean_dir, "RealKL.lean")):
        failed += 1
        print("  [FAIL] FIXTURE: %s has no RealKL.lean; cannot exercise DEAD" % lean_dir)
    else:
        state, why = _anchor_class("RealKL.this_lemma_does_not_exist_zzz", lean_dir, {})
        if state == "DEAD" and "no declaration" in why:
            passed += 1
        else:
            failed += 1
            print("  [FAIL] missing lemma want DEAD/*no declaration* got %s/%s"
                  % (state, why))

    # 6. The allowlist wins over every other bucket.
    ran += 1
    state, why = _anchor_class("RealKL.retired_thing", lean_dir,
                               {"realkl.retired_thing": True})
    if state == "ALLOWLISTED" and "allowlist" in why:
        passed += 1
    else:
        failed += 1
        print("  [FAIL] allowlisted anchor want ALLOWLISTED/*allowlist* got %s/%s"
              % (state, why))

    # CRITERION 13, part 2: assert HOW MANY cases ran. A case that silently
    # vanishes lowers the pass count and raises nothing. The expected count
    # derives from the declared array, not from a magic number.
    expected_ran = len(cases) + 5
    if ran != expected_ran:
        failed += 1
        print("  [FAIL] ran %d cases, expected %d (silent skip)" % (ran, expected_ran))

    print("")
    print("self-test: %d passed, %d failed, %d/%d cases"
          % (passed, failed, ran, expected_ran))
    return EXIT_BLOCKING if failed > 0 else EXIT_PASS


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def _build_parser():
    ap = argparse.ArgumentParser(
        prog="check-corrections-anchors.py",
        description="LATTICE CORRECTIONS anchor cross-check (port of "
                    "check-corrections-anchors.ps1).")
    # Both spellings are accepted for every parameter so the port is a drop-in
    # for callers migrated one at a time (the constraint is that the .ps1 and
    # the port keep working side by side during the comparison window).
    ap.add_argument("-LeanDir", "--lean-dir", dest="lean_dir", default="",
                    metavar="DIR",
                    help="directory holding CORRECTIONS.md and the modules "
                         "(default: <repo>/lean)")
    ap.add_argument("-Corrections", "--corrections", dest="corrections",
                    default="", metavar="FILE",
                    help="the register to audit (default: <lean-dir>/CORRECTIONS.md)")
    ap.add_argument("-OutFile", "--out-file", dest="out_file", default="",
                    metavar="FILE",
                    help="also write the Markdown report here (relative paths "
                         "resolve against the repository root); OPT-IN, this is "
                         "the only thing the script ever writes")
    ap.add_argument("-Section", "--section", dest="section", default="ALL",
                    metavar="A|B|C|D|ALL",
                    help="restrict the audit to one top-level `## X.` section")
    ap.add_argument("-FailOn", "--fail-on", dest="fail_on", default="DEAD",
                    metavar="STATES",
                    help="comma-separated anchor states that block "
                         "(default: DEAD)")
    ap.add_argument("-SelfTest", "--self-test", dest="self_test",
                    action="store_true",
                    help="run the built-in suite and exit (never audits the tree)")
    ap.add_argument("-Quiet", "--quiet", dest="quiet", action="store_true",
                    help="suppress the NEEDS-HUMAN listing (counts are kept)")
    return ap


def main(argv=None):
    args = _build_parser().parse_args(argv)

    # ps1 L67 declares [ValidateSet(...)] on -Section, so PowerShell rejects an
    # out-of-set value during parameter binding. See D1: the port maps that to
    # the script's own documented usage-error code, 2.
    if args.section.upper() not in VALID_SECTIONS:
        sys.stderr.write("invalid -Section '%s'; valid: %s\n"
                         % (args.section, ", ".join(VALID_SECTIONS)))
        return EXIT_USAGE

    # ps1 L78-80.
    repo_dir = _repo_dir()
    lean_dir = args.lean_dir or _join(repo_dir, "lean")
    corrections = args.corrections or _join(lean_dir, "CORRECTIONS.md")

    # ps1 L277: -SelfTest runs the built-in suite and NEVER falls through.
    if args.self_test:
        return _self_test(lean_dir)

    # ps1 L281. Measured: exit 1, not the documented 2 (see the module docstring).
    if not _exists(corrections):
        sys.stderr.write("missing %s\n" % corrections)
        return EXIT_BLOCKING

    text = _read_text(corrections)

    # ps1 L286: the allowlist ALWAYS comes from this script's own directory and
    # is unaffected by -LeanDir.
    allow = _read_allowlist(os.path.dirname(os.path.abspath(__file__)))

    # ps1 L294-327.
    sections = _section_anchors(text, args.section)
    rows = _collect_rows(sections, lean_dir, allow)
    by_state = {}
    for r in rows:
        by_state.setdefault(r["state"], []).append(r)
    dead = by_state.get("DEAD", [])
    stale = by_state.get("STALE-OLEAN", [])
    human = by_state.get("NEEDS-HUMAN", [])
    res = by_state.get("RESOLVED", [])
    alw = by_state.get("ALLOWLISTED", [])

    # ps1 L338-352. This runs AFTER the classification, so a bad --fail-on still
    # does all the work and then prints this one line and nothing else.
    fail_states, bad = _parse_fail_on(args.fail_on)
    if bad is not None:
        print("unknown -FailOn state '%s'; valid: %s, ALL"
              % (bad, ", ".join(VALID_STATES)))
        return EXIT_USAGE

    # ps1 L354-380.
    print("== CORRECTIONS anchor cross-check (F7) ==")
    print("corrections : %s" % corrections)
    print("section     : %s" % args.section)
    print("blocking on : %s"
          % (", ".join(fail_states) if fail_states else "(nothing - report only)"))
    print("anchors     : %d" % len(rows))
    print("  RESOLVED     : %d" % len(res))
    print("  STALE-OLEAN  : %d" % len(stale))
    print("  ALLOWLISTED  : %d" % len(alw))
    print("  NEEDS-HUMAN  : %d" % len(human))
    print("  DEAD         : %d" % len(dead))
    print("")
    if dead:
        print("--- DEAD: cited declaration no longer exists ---")
        for d in dead:
            print("  [%s] %s : %s" % (d["entry"], d["anchor"], d["why"]))
        print("")
    if stale:
        print("--- STALE-OLEAN: file not currently compiled (claim unbacked) ---")
        for d in stale:
            print("  [%s] %s : %s" % (d["entry"], d["anchor"], d["why"]))
        print("")
    if human and not args.quiet:
        print("--- NEEDS-HUMAN: not a theorem reference; confirm by hand ---")
        for d in human:
            print("  [%s] %s : %s" % (d["entry"], d["anchor"], d["why"]))
        print("")

    # ps1 L382-417.
    if args.out_file:
        _write_report(args.out_file, repo_dir, args.section, rows, by_state)

    # ps1 L419-440.
    blocking = []
    for s in fail_states:
        blocking.extend(by_state.get(s, []))
    print("")
    if blocking:
        print("FAIL: %d anchor(s) in blocking state(s): %s"
              % (len(blocking), ", ".join(fail_states)))
        for b in blocking:
            print("  [%s] %s : %s - %s"
                  % (b["entry"], b["anchor"], b["state"], b["why"]))
        return EXIT_BLOCKING
    advisory = []
    for s in ADVISORY_STATES:
        if s not in fail_states:
            advisory.extend(by_state.get(s, []))
    if advisory:
        print("advisory: %d anchor(s) reported but not blocking "
              "(re-run with -FailOn ALL to gate)" % len(advisory))
    print("PASS: no blocking anchor findings")
    return EXIT_PASS


def _reconfigure_streams():
    """Pin LF and never raise on a legacy console code page.

    `Write-Host` emits LF (0x0A) even on Windows; Python's text-mode stdout would
    emit os.linesep (CRLF here), so the newline is pinned to keep the two
    implementations byte-identical on the parity fixtures.
    """
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace", newline="\n")
        except Exception:
            # reconfigure() needs 3.7+; do not fail the run over it.
            pass


_reconfigure_streams()


if __name__ == "__main__":
    try:
        sys.exit(main())
    except OSError as exc:
        # D3: $ErrorActionPreference = 'Stop' makes a failed read a TERMINATING
        # error, so the .ps1 dies with exit 1, whatever it had already put on
        # stdout, plus a diagnostic on stderr. Same code, equivalent message.
        sys.stderr.write("check-corrections-anchors.py: %s\n" % exc)
        sys.exit(EXIT_BLOCKING)
