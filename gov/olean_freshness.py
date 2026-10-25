#!/usr/bin/env python3
"""
olean_freshness.py -- find roots whose olean does NOT match the current source.

WHY THIS EXISTS (a blind spot found in the round-129 sweep):

  `check-olean-coverage.ps1` answers "does an olean EXIST". That is not the same question
  as "does the CURRENT SOURCE compile". A root can have an olean from days ago while the
  source has since been edited -- and if that edit broke it, NOTHING reports the problem:
  the coverage gate sees a file, and no error count is ever taken because nobody rebuilds.

  Q3 hit exactly this class (B230.6): two registered roots "never compiled against the
  current toolchain", so the roadmap's description of their state had never been tested.

  A round-129 mtime sweep found 68 roots whose source mtime is newer than their olean.
  MOST OF THAT IS NOISE -- mtime lies (B125), and `touch`-style edits, editor saves and
  line-ending rewrites all bump it without changing meaning (B229).

THE ACTUAL TEST

  Compare CONTENT, not timestamps. For each root we ask lake whether the module is up to
  date by hashing the source and comparing against the olean's recorded trace. Doing that
  properly means invoking lake; doing it cheaply means comparing the sha256 of the source
  against a cached record from the last build.

  This script takes the cheap-but-sound route: it records, per module, the sha256 of the
  source at the moment an olean was produced (from a cache file maintained here), and
  reports modules whose current source hash differs from the recorded one. A module with
  no record is reported as UNKNOWN, never as fresh.

  HONEST SCOPE: this detects "source changed since we last recorded a successful build".
  It does NOT detect a module that never built. For that, use check-olean-coverage.ps1.

USAGE
  python scripts/olean_freshness.py --record      # snapshot current state (after a build)
  python scripts/olean_freshness.py               # report drift
  python scripts/olean_freshness.py --list 20
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

CACHE = "olean-freshness.json"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--record", action="store_true",
                    help="record current source hashes as the baseline")
    ap.add_argument("--list", type=int, default=15)
    args = ap.parse_args(argv)

    root = Path(args.root).resolve()
    lean = root / "lean"
    build = lean / ".lake" / "build" / "lib"
    cache_path = root / "scripts" / CACHE

    lakefile = lean / "lakefile.toml"
    if not lakefile.exists():
        print("  ! lakefile.toml not found")
        return 2
    m = re.search(r"roots\s*=\s*\[(.*?)\]", lakefile.read_text(encoding="utf-8"), re.S)
    names = [s.strip().strip('"') for s in m.group(1).split(",") if s.strip()]

    state: dict[str, str] = {}
    for n in names:
        src = lean / f"{n}.lean"
        if not src.exists():
            continue
        state[n] = hashlib.sha256(src.read_bytes()).hexdigest()

    if args.record:
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        cache_path.write_text(json.dumps(state, indent=1), encoding="utf-8")
        print(f"  recorded {len(state)} module hash(es) -> {cache_path.name}")
        return 0

    if not cache_path.exists():
        print("  no baseline recorded yet; run with --record right after a successful build")
        return 0
    old = json.loads(cache_path.read_text(encoding="utf-8"))

    drifted, unknown, fresh, no_olean = [], [], [], []
    for n, h in sorted(state.items()):
        if not (build / f"{n}.olean").exists():
            no_olean.append(n)
        elif n not in old:
            unknown.append(n)
        elif old[n] != h:
            drifted.append(n)
        else:
            fresh.append(n)

    print("== olean freshness (content-based, not mtime) ==")
    print(f"  roots            : {len(names)}")
    print(f"  source unchanged : {len(fresh)}")
    print(f"  SOURCE CHANGED   : {len(drifted)}   <- olean no longer matches source")
    print(f"  no baseline      : {len(unknown)}   <- recorded before this cache existed")
    print(f"  never built      : {len(no_olean)}  <- use check-olean-coverage.ps1 for these")

    for label, items in (("CHANGED", drifted), ("NO-BASELINE", unknown),
                         ("NEVER-BUILT", no_olean)):
        for n in items[: args.list]:
            print(f"    {label:12} {n}")
        if len(items) > args.list:
            print(f"    ... and {len(items) - args.list} more {label}")

    if drifted:
        print("  These roots need a rebuild before any claim about them is current.")
    return 1 if drifted else 0


if __name__ == "__main__":
    sys.exit(main())
