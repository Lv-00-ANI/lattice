# -*- coding: utf-8 -*-
"""OBSOLETE since round 187: the G7 breakpoints describe ARCHIVED geometry code.

## Why this is a stub rather than a check

**`G7-BREAKPOINTS.md` no longer exists in the tree** (it was removed with the geometry material), and the
three files this check used to read -- `Reference/Geometry/LvFormal/Theory/Compiler.lean`, `IR.lean` and the
rest -- were **moved to `archive/LvFormal/`** by round 187, which the user ruled obsolete.

**=> every number this check compared against lived in a document that is gone, about code that is archived.
Re-enabling it would require re-deriving the document first, for content nobody uses.**

**This file stays registered in `verify_all.py` on purpose: deleting a registration silently reduces the
check count, and a check that disappears is indistinguishable from a check that passes. A stub that says
"obsolete, here is why" keeps the count honest and the reason recorded.**

The original implementation is in git history at the commit before round 187.
"""
import sys


def main():
    print("G7 BREAKPOINTS: obsolete -- G7-BREAKPOINTS.md removed with the archived geometry material")
    print("  the three source files now live in archive/LvFormal/ (round 187, user-ruled obsolete)")
    print("  original implementation: see git history before round 187")
    return 0


if __name__ == "__main__":
    sys.exit(main())
