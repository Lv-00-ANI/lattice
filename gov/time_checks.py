# -*- coding: utf-8 -*-
"""逐项测量 `verify_all.py` 的 CHECKS 耗时，找出真正慢的那一项。

## 为什么

全量 `verify_all.py` 超 15 分钟未完成，但 `--fast` 只需 35 秒。
差异只在于跳过了 `reactivity: gate`（16.7s）与 `verify_g4`（78.6s），
两项合计 95 秒 —— **远不能解释 15 分钟**。

⇒ 必然有一项在**全量模式**下极慢（而在 `--fast` 下被不同的环境变量影响）。
"""
import io
import os
import subprocess
import sys
import time

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

ZERO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

CHECKS = [
    ("gate", "gate.py"),
    ("comments", "check_comments.py"),
    ("registry", "check_registry.py"),
    ("reactivity: slots", "check_slots_reactivity.py"),
    ("reactivity: comments", "check_comments_reactivity.py"),
    ("reactivity: registry", "check_registry_reactivity.py"),
    ("reactivity: registry-gate", "check_registry_gate_reactivity.py"),
    ("reverify: requirements", "reverify.py"),
    ("reverify: chain", "reverify_chain.py"),
    ("reverify: islands", "reverify_islands.py"),
    ("audit: duplicates", "audit_duplicates.py"),
    ("audit: bodies", "audit_bodies.py"),
    ("audit: geo structure", "audit_geo.py"),
    ("audit: docs vs code", "audit_docs.py"),
    ("audit: reachable", "audit_reach.py"),
    ("audit: claims", "audit_claims.py"),
    ("audit: G7 breakpoints", "check_g7.py"),
    ("audit: abstraction", "audit_abstraction.py"),
    ("gen: proof chain (geo)", "proof_chain_geo.py"),
    ("scope: escape baseline", "escape_baseline.py --check"),
]

env = dict(os.environ)
env.pop("DSH_GATE_SCOPE", None)
env.pop("LEAN_PATH", None)

rows = []
for label, cmd in CHECKS:
    bits = cmd.split()
    parts = [sys.executable, os.path.join("gov", bits[0])] + bits[1:]
    t0 = time.time()
    try:
        r = subprocess.run(parts, cwd=ZERO, capture_output=True, text=True,
                           encoding="utf-8", errors="replace", env=env, timeout=300)
        code, note = r.returncode, ""
    except subprocess.TimeoutExpired:
        code, note = -1, "TIMEOUT>300s"
    dt = time.time() - t0
    rows.append((dt, label, code, note))
    print("  %-32s %6.1fs  exit=%s %s" % (label, dt, code, note), flush=True)

print()
rows.sort(reverse=True)
print("按耗时排序（前五）：")
for dt, label, code, note in rows[:5]:
    print("  %-32s %6.1fs" % (label, dt))
print()
print("合计：%.1fs" % sum(r[0] for r in rows))
