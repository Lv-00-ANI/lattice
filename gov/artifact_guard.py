"""gov/artifact_guard.py -- generated artifacts are COMPARED on the default path, WRITTEN only on request.

**Why this exists (plan W0-3c).** Seven generators wrote their output unconditionally: `check_slots.py` rewrote
`gov/SLOTS.md` on the path `gate.py`'s I6 check takes, `check_endtoend_content.py` rewrote `ENDTOEND-CENSUS.md` and
`endtoend-cross.tsv`, `check_endtoend_floor.py` rewrote the tsv that its own gate reads, and four more did the same for
`ALIAS-CENSUS.md`, `PROOF-CHAIN.md`, `PROOF-CHAIN-GEO.md` and `PRIMITIVE-MATRIX.md`.

Measured before changing anything: all seven are IDEMPOTENT -- running them on a clean tree leaves `git status` empty.
So the defect is not churn, it is AUTHORITY. A generator that rewrites its artifact on the default path will silently
overwrite a hand edit, and a gate that writes the file it is about to check has checked its own output.

**The rule.** `sync()` compares and reports; only an explicit `--write` writes.

    same      -> "unchanged"   (nothing written; nothing printed)
    differs   -> "stale"       (nothing written; the first differing line is printed)
    differs and allow_write -> "written"

Callers on a gate path should treat "stale" as a failure: the tree no longer matches what the generator produces, which
is exactly the condition a reader would want to know about.
"""

import io
import os


def _read(path):
    if not os.path.exists(path):
        return None
    return io.open(path, encoding="utf-8").read()


def sync(path, text, allow_write=False, label=None, expect_tracked=True):
    """Compare `text` with the file at `path`; write only when `allow_write`.

    Returns one of "unchanged", "written", "stale", "absent".

    `expect_tracked` distinguishes the two reasons a file can be missing. For a tracked artifact, absence is a defect
    (the tree lost it). For an artifact that was NEVER in the repository -- `PRIMITIVE-MATRIX.md` is one -- absence is
    simply "not versioned", and holding the generator to it would make the default path fail on a clean tree.
    """
    name = label or os.path.basename(path)
    if not expect_tracked and not allow_write:
        # **An unversioned artifact has nothing to stay in sync with.** `PRIMITIVE-MATRIX.md` is generated into the
        # repository root and is not tracked, so the default path must neither write it nor fail over it; only
        # `--write` produces it. Absence and difference are both "not our business" here.
        return "absent"
    old = _read(path)
    if old is not None and old == text:
        return "unchanged"
    if allow_write:
        parent = os.path.dirname(path)
        if parent and not os.path.isdir(parent):
            os.makedirs(parent)
        io.open(path, "w", encoding="utf-8", newline="\n").write(text)
        print("  WROTE %s" % name)
        return "written"

    if old is None:
        if not expect_tracked:
            return "absent"
        print("  STALE %s -- absent; run with --write to create it" % name)
        return "stale"

    # Report the first difference rather than a whole diff: the point is that they disagree, and one line is enough
    # to recognise which side moved.
    old_lines, new_lines = old.split("\n"), text.split("\n")
    for i in range(max(len(old_lines), len(new_lines))):
        o = old_lines[i] if i < len(old_lines) else "<absent>"
        n = new_lines[i] if i < len(new_lines) else "<absent>"
        if o != n:
            print("  STALE %s -- line %d differs" % (name, i + 1))
            print("     on disk : %s" % o[:100])
            print("     generated: %s" % n[:100])
            break
    return "stale"


def require_synced(results, script):
    """Turn any "stale" in `results` into exit 1 with the instruction that fixes it."""
    stale = [r for r, state in results if state == "stale"]
    if not stale:
        return 0
    print()
    print("%s: %d artifact(s) no longer match what this script generates (%s)."
          % (script, len(stale), ", ".join(stale)))
    print("A generated file must not be edited by hand; run this script with --write to regenerate it.")
    return 1