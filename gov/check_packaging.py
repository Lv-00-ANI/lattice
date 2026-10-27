"""gov/check_packaging.py -- the repository can be understood from the repository alone.

## Why

`lakefile.toml` declares `license = "MIT"` while **no `LICENSE` file existed** (round 177). A declared
licence with no licence text is not a paperwork detail: it means a reader cannot tell what they may do
with the code, and the declaration alone reads as though they can tell.

The same file also contains `packagesDir = "../lattice/lean/.lake/packages"` -- **a path outside this
repository**. That is a deliberate local optimisation (it reuses an already-compiled 4.2 GB mathlib
instead of copying it in), and removing it is NOT the fix: I tried, and it makes lake emit
`manifest out of date: packages directory changed` on every invocation. The honest position is that the
line is a local convenience which a fresh machine must override, and that must be SAID where a fresh
machine would look.

So this checker guards what CAN be checked mechanically:

  1. a declared licence has a licence file;
  2. every `packagesDir` (if any) is flagged in the report, so it cannot quietly be assumed portable;
  3. the README's build instructions mention the override, so the "fresh machine" path is written down.

`--self-test` removes the licence file and requires the failure, then plants a `packagesDir` with no
README mention and requires that reported too.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))

#: `license = "MIT"` -> the file names a reader will look for.
LICENSE_FILES = {
    "MIT": ["LICENSE", "LICENSE.md", "LICENSE.txt", "COPYING"],
    "Apache-2.0": ["LICENSE", "LICENSE.md", "LICENSE.txt"],
    "BSD-3-Clause": ["LICENSE", "LICENSE.md", "LICENSE.txt"],
}

#: The README must tell a fresh machine how to handle a `packagesDir` that points elsewhere.
README_OVERRIDE = re.compile(r"packagesDir")


def scan(root=None):
    """Return `(problems, notes)`."""
    root = root or ROOT
    problems = []
    notes = []

    lf = os.path.join(root, "lakefile.toml")
    if not os.path.exists(lf):
        return ["lakefile.toml is missing"], notes
    text = io.open(lf, encoding="utf-8", errors="replace").read()

    m = re.search(r'^\s*license\s*=\s*"([^"]+)"', text, re.M)
    if not m:
        notes.append("no `license` field declared")
    else:
        declared = m.group(1)
        candidates = LICENSE_FILES.get(declared, ["LICENSE", "LICENSE.md", "LICENSE.txt"])
        if not any(os.path.exists(os.path.join(root, c)) for c in candidates):
            problems.append(
                'lakefile.toml declares license = "%s" but none of %s exists'
                % (declared, candidates))

    mp = re.search(r'^\s*packagesDir\s*=\s*"([^"]+)"', text, re.M)
    if mp:
        target = mp.group(1)
        outside = target.startswith("..") or os.path.isabs(target)
        notes.append("packagesDir = %r%s" % (
            target, "  (OUTSIDE this repository)" if outside else ""))
        if outside:
            readme = os.path.join(root, "README.md")
            if not os.path.exists(readme):
                problems.append("packagesDir points outside the repo and there is no README to explain it")
            elif not README_OVERRIDE.search(io.open(readme, encoding="utf-8", errors="replace").read()):
                problems.append(
                    "packagesDir points outside this repository but README.md never mentions "
                    "`packagesDir`, so a fresh machine has no instruction for it")
    return problems, notes


def main(argv):
    if "--self-test" in argv:
        import shutil
        tmp = os.path.join(HERE, ".pack-selftest")
        shutil.rmtree(tmp, ignore_errors=True)
        os.makedirs(tmp)
        failures = []
        try:
            # (a) declared MIT, no LICENSE file -> must be reported
            io.open(os.path.join(tmp, "lakefile.toml"), "w", encoding="utf-8").write(
                'name = "x"\nlicense = "MIT"\n')
            io.open(os.path.join(tmp, "README.md"), "w", encoding="utf-8").write("# x\n")
            p, _ = scan(tmp)
            if not [x for x in p if "LICENSE" in x]:
                failures.append("a declared licence with no file was NOT caught")

            # (b) a LICENSE file present -> must NOT be reported
            io.open(os.path.join(tmp, "LICENSE"), "w", encoding="utf-8").write("MIT\n")
            p, _ = scan(tmp)
            if [x for x in p if "LICENSE" in x]:
                failures.append("a present LICENSE file was reported missing")

            # (c) an outside packagesDir with no README mention -> must be reported
            io.open(os.path.join(tmp, "lakefile.toml"), "w", encoding="utf-8").write(
                'name = "x"\nlicense = "MIT"\npackagesDir = "../elsewhere/packages"\n')
            p, _ = scan(tmp)
            if not [x for x in p if "packagesDir" in x]:
                failures.append("an unexplained outside packagesDir was NOT caught")

            # (d) mentioned in the README -> must NOT be reported
            io.open(os.path.join(tmp, "README.md"), "w", encoding="utf-8").write(
                "# x\n\nOn a fresh machine, override `packagesDir`.\n")
            p, _ = scan(tmp)
            if [x for x in p if "packagesDir" in x]:
                failures.append("an explained outside packagesDir was reported as a problem")
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        if failures:
            for f in failures:
                print("SELF-TEST FAILED: %s" % f)
            return 2
        print("SELF-TEST: missing licence caught, present licence accepted, unexplained"
              " packagesDir caught, explained one accepted")
        return 0

    problems, notes = scan()
    for n in notes:
        print("  note: %s" % n)
    for p in problems:
        print("  PROBLEM: %s" % p)
    print()
    if problems:
        print("PACKAGING: %d problem(s)" % len(problems))
        return 1
    print("PACKAGING: declared licence has a file; any outside path is documented")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
