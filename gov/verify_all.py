# -*- coding: utf-8 -*-
"""Re-verification scripts must be runnable from the gate, not only by hand.

Round 30 found two real defects (an orphan artifact, an over-general claim) using these scripts. A
measurement that only exists because someone remembered to run it will not run again. `verify_all.py`
chains the reactivity tests, the re-verification scripts, the audits and the two proof-chain
generators into one command with a single
exit code, so "the project is healthy" is one reproducible statement rather than a narrative.

Deliberately NOT wired into `gate.py`: the gate is a fast invariant check run on every edit, while these
are slower audits (they walk the whole tree several times). Keeping them separate keeps the gate cheap
enough that people actually run it.
"""
import io
import os
import subprocess
import sys
import time

# The console codepage may be GBK: any non-ASCII diagnostic must not crash the report itself.
try:
    sys.stdout.reconfigure(errors="replace")
except (AttributeError, ValueError):
    pass


HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))

# Checks declared as REPORT-ONLY.
#
# Measured problem this solves: 16 of the registered scripts end `main()` with a literal
# `return 0`, so their exit code is a constant. Several say so on purpose -- "report
# only", "Exit 0 is deliberate", "a review list, not a verdict" -- because they print
# findings a human must judge. That is a defensible design, but it made the summary line
# "VERIFY ALL: PASS" misleading: it counted 32 processes whose exit code was 0, without
# saying that 16 of them could not have been anything else.
#
# So they still run -- their output is the point -- but they are counted in a separate
# column, and the summary states both numbers. Turning a reporter into a gate is a change
# to what it claims, not a one-line edit; that decision belongs to whoever owns the check.
REPORT_ONLY = {
    "reverify: requirements", "reverify: chain", "reverify: islands",
    "audit: duplicates", "audit: bodies", "audit: docs vs code", "audit: reachable",
    "audit: claims", "audit: liveness", "audit: region", 
"audit: abstraction", "audit: islands",
    "audit: duplicate statements", "audit: untracked work",
    "gen: proof chain (geo)", "gen: proof chain (kernel)",
    "census: end-to-end by content",
      "usage: skeleton main theorems",
}

# (label, script, expects a specific exit code or None for "any")
CHECKS = [
    ("gate", "gate.py"),
    ("gate --selftest", "gate.py --selftest"),
    ("comments", "check_comments.py"),
    ("registry", "check_registry.py"),
    ("reactivity: gate", "gate_reactivity.py"),
    # I4's Geo layer was missing from LAYER_OF until this round, so a Lift -> Geo
    # import was invisible. This proves the rule now fires on exactly that defect.
    ("reactivity: layering", "layer_reactivity.py"),
    # Guards the design property "the chain composes via structure FIELDS, not re-proof":
    # `compileProgram_sound`, `extract_compile`, `ladder_forward` cite ZERO kernel
    # declarations. If that silently changes, the claim behind USAGE §1 becomes false.
    ("chain dependencies", "check_chain_deps.py"),
    # Keeps REPAIR-CENSUS xref numbers honest: the census drifted 6/27 -> 9/28
    # between rounds and nothing measured it. This makes it measurable.
    ("repair census", "check_repair_census.py"),
    # Same guard for REFUTATION-CENSUS: the 387 number and its layer split were
    # verified once by hand and nothing re-measured them.
    ("refutation census", "check_refutation_census.py"),
    # The chain STATUS TABLE said 'L1->L2 has no carrier' for 27 rounds after one
    # was proved. Nothing checked the table itself. This verifies every carrier
    # the table names actually exists.
    ("chain table", "check_chain_table.py"),
    ("reactivity: slots", "check_slots_reactivity.py"),
    ("reactivity: comments", "check_comments_reactivity.py"),
    ("reactivity: I8 gate", "check_i8_reactivity.py"),
    ("reactivity: registry", "check_registry_reactivity.py"),
    ("reactivity: registry-gate", "check_registry_gate_reactivity.py"),
    ("reactivity: G4", "verify_g4.py"),
    ("reverify: requirements", "reverify.py"),
    ("reverify: chain", "reverify_chain.py"),
    ("reverify: islands", "reverify_islands.py"),
    ("audit: duplicates", "audit_duplicates.py"),
    ("audit: bodies", "audit_bodies.py"),
    ("audit: geo structure", "audit_geo.py"),
    ("audit: docs vs code", "audit_docs.py"),
    ("audit: reachable", "audit_reach.py"),
    ("audit: claims", "audit_claims.py"),
    ("audit: liveness", "audit_liveness.py"),
    ("audit: region", "audit_region.py"),
    ("audit: tables", "audit_tables.py"),
    # Gates on the one thing it can decide: whether a check-marked row cites a
    # name that exists. Whether the mark is BACKED stays advisory, as documented.
    ("reactivity: tables", "audit_tables_reactivity.py"),
    ("audit: counts", "audit_counts.py"),
    # audit_counts is a GATE now: it fails when a documented count disagrees with
    # the tree, and this proves the gate can fire on every count it checks.
    ("reactivity: counts", "audit_counts_reactivity.py"),
    ("audit: G7 breakpoints", "check_g7.py"),
    ("audit: proof chain rung", "check_proof_chain_rung.py"),
    # The CI workflow is executable text that nothing executed. The previous version
    # read a path from the pre-migration layout and the job never ran; these two keep
    # that from recurring and prove the checker itself can fail.
    ("ci: workflow refers to this repo", "check_ci_workflow.py"),
    ("reactivity: ci workflow", "check_ci_workflow_reactivity.py"),
    ("audit: abstraction", "audit_abstraction.py"),
    ("audit: islands", "audit_islands.py"),
    ("audit: duplicate statements", "audit_duplicate_statements.py"),
    ("audit: untracked work", "audit_untracked.py"),
    ("gen: proof chain (geo)", "proof_chain_geo.py"),
    # Census, NOT a gate: a theorem that touches one layer is not a defect. What would be a
    # defect is CLAIMING otherwise, and I5 is the gate for that. This runs the same transitive
    # analysis I5 uses, on EVERY theorem instead of only the ones named `e2e` -- round 219
    # measured that the name filter left the chain's own work (Geo) entirely outside coverage.
    ("census: end-to-end by content", "check_endtoend_content.py"),
    ("gen: proof chain (kernel)", "chain.py"),
    ("scope: escape baseline", "escape_baseline.py --check"),
    # Three of this round's fixes were the SAME defect: one measurement written down in two
    # places, only one updated (apostrophes 60 vs 3, oversized 8 vs 10, registry 42 vs 43).
    # A number being right is not enough; the document must agree with itself.
    ("consistency: docs agree with themselves", "check_doc_consistency.py"),
    # Round 167: thirteen docstrings cited declarations that do not exist -- renames left the prose
    # behind, and nothing compared the two. A docstring that cites a theorem IS part of the proof
    # argument, so a phantom citation is a broken argument.
    #
    # This is a curated stale-name list, not a general "every backticked name exists" check: the
    # general version was built and measured at 13,689 findings (Mathlib lemmas, local variables,
    # tactic names), and a gate with 13,689 findings gets switched off. `--survey` reports them for a
    # human instead. See the script's module docstring for the 「」 convention that makes the narrow
    # version honest.
    ("docs: no docstring cites a stale declaration name", "check_doc_names.py"),
    # Round 108 rewrote CONVENTIONS.md with an unconstrained replace and turned leading 1 digits
    # into 0 -- dates, section numbers, rule ids, counts. Every guard passed, because they check
    # names and known numbers, not the integrity of surrounding text. Round 116 restored the file
    # from before the damage and added this guard.
    ("docs: no batch-replacement damage", "check_batch_edit_damage.py"),
    # Round 116: the README correctly says CI has never run. This runs the half of CI that needs no
    # Lean toolchain, step for step, and statically audits the half that does -- then says plainly
    # that the audit is not a run.
    ("ci: job 1 runs locally, job 2 audited", "check_ci_locally.py"),
    # Round 118: five recorded premature 'done' assertions, and no guard touched any of them,
    # because they are claims about scope rather than numbers. This one checks the shape: a
    # completion sentence must sit next to a list of what is still open.
    ("docs: completion claims paired with open work", "check_completion_claims.py"),
    # Round 142: the tree carries 28 honestly-labelled stubs from the upstream Lv-00 files. Nothing
    # checked that a NEW placeholder is labelled, so an unlabelled one would make the theorems about
    # it true-but-empty with no invariant noticing.
    ("stubs: every placeholder definition is labelled", "check_stub_registry.py"),
    # Round 152: rounds 108-150 found that an identity `l1l2` can be CORRECT (Sym is List Tok, so
    # there is nothing to encode) or a DEFECT (Sym carries structure Tok cannot hold). This classifies
    # every Ladder instance's rung.
    #
    # Round 167 promotes it from report-only to a GATE. Printing the classification was not enough: a
    # reader still had to notice. The three current identity rungs are now registered in `IDENTITY_OK`
    # with the type reason that makes each correct, and the register is checked in BOTH directions -- a
    # new unregistered identity fails, and an entry whose instance has gone fails (so the register
    # cannot rot into a list of stale justifications).
    ("ladder: every l1l2 rung classified", "check_ladder_rungs.py"),
    # Round 158: the objective has two halves in one sentence -- "not bound to any vendor" (rule C
    # checks imports) and "does not implement engines, models or training frameworks". A training
    # loop needs no import, so rule C cannot see one. This checks the second half.
    ("positioning: no engine/model/training framework", "check_scope_boundary.py"),
    # Round 159: a clause whose every carrier sits in a leaf module is unreachable -- the objective
    # would depend on something nothing can import. This checks the clause reachability graph.
    ("structure: every clause reachable", "gen_lib_structure.py"),
    # Round 171. Three checks were found that had silently stopped checking: a shape test whose regex
    # could never match a single-line `def`, two doc-consistency patterns that hardcoded a count the
    # tree had outgrown, and a usage-claim rule that `continue`d when its pattern matched nothing. Each
    # was caught by writing a self-test, never by reading the code.
    #
    # So the question "does this gate have a self-test?" is now a build error rather than a matter of
    # diligence. Every gate must carry `--self-test`, have a `*_reactivity.py` companion, or be listed
    # in `check_selftest_coverage.EXEMPT` with the reason it is verified some other way -- and that
    # exemption table is itself checked for rot.
    ("meta: every gate can demonstrate its own failure", "check_selftest_coverage.py"),
    # Round 176. `check_usage_claims` guards 14 counts; these nine were guarded by NOBODY:
    # OBJECTIVE-MAP's clause and carrier counts, OBJECTIVE-AUDIT's theorem count, and the owed /
    # permanent-boundary figures in README, STATE-FINAL and DELIVERY. This round alone moved the
    # theorem count 8,323 -> 8,328 and the boundary count 3 -> 4, each updated by hand in three or four
    # documents -- the only reason they are right is that I remembered. That is the pattern this whole
    # project keeps paying for, so it is now a gate.
    ("docs: freshness of the tree's own figures", "check_doc_freshness.py"),
    # Round 177. `lakefile.toml` declared `license = "MIT"` while no LICENSE file existed, and it
    # carries `packagesDir = "../lattice/lean/.lake/packages"` -- a path outside this repository. The
    # path is a deliberate local optimisation (removing it makes lake report a stale manifest on every
    # invocation), so the fix is to REQUIRE the README to document the override rather than to delete
    # the line. A path that serves only the author's machine and is silent to a reader is the most
    # common packaging defect there is.
    ("packaging: licence file exists, outside paths documented", "check_packaging.py"),
    # Round 208. The completion standard was "has a name, is a theorem, 0 sorry". Lean checks the
    # theorem is TRUE, never that it is STRONG -- so `:= h`, `a = a` and a 4/12 coverage import and
    # cite exactly like a complete theorem, and downstream builds on them.
    # This gate catches the two syntactically decidable shapes (reflexive conclusion, bare-hypothesis
    # proof) with a two-way baseline: a new one fails, and a baselined one that stops firing also
    # fails, so the ledger can only shrink. Semantic strength is audited separately -- see PROOF-DEBT.md.
    ("meta: no nominally-complete proof shapes", "check_proof_strength.py"),
    # Round 197. A hypothesis that is PROVABLE OUTRIGHT makes the theorem weaker than its statement
    # suggests. `compileProg_correct`'s `(h : stackDepth e ≤ 1)` was exactly that: it was passed to
    # `compileAcc_correct`, so `linter.unusedVariables` stayed silent -- while `stackDepth e = 1` for
    # every expression. No linter finds this class. This gate catches the syntactically visible
    # sub-class (`a = a`, `a ↔ a`, `True`) with zero false positives, and the file states plainly
    # which sub-class it does NOT catch.
    ("meta: no vacuously true hypothesis", "check_vacuous_hypotheses.py"),
    # Round 210. An underscore-prefixed NAMED binder (`_hrest`, not the bare `_` wildcard) is the
    # author declaring a hypothesis unused -- and that prefix is exactly what silences Lean's own
    # `linter.unusedVariables`. 139 such binders existed; this gate makes them enumerable. One was
    # prefixed AND used (`_htri`, renamed); the rest are redundant or structurally unreachable
    # hypotheses. Baselined with the theorem name so each reason is one lookup away.
    ("meta: no underscore-prefixed hypothesis", "check_underscore_hypotheses.py"),
    # Round 179, P2-16. 21 wildcard `| _ => none` decoders exist in the kernel and nobody had judged
    # them. Judging them once by hand is not the fix -- a 22nd would appear unexamined. Each file is now
    # registered with one of three reasons (covered by a round-trip theorem / upstream Lv-00 carried /
    # partial decoder by design), and a file with an unregistered arm fails. Bookkeeping, NOT a
    # reachability proof, and the checker says so in its own output.
    ("scope: every wildcard none branch has a reason", "check_none_branches.py"),
    # Round 164: module-level reachability is coarse. This lists skeleton theorems whose name
    # claims a main result and which nothing references -- a reading list, all terminal.
    ("usage: skeleton main theorems", "gen_theorem_usage.py"),
    # Round 154: OBJECTIVE-MAP.md lists all 14 objective clauses with each carrier's location and
    # reference counts. This fails if the committed map no longer matches the tree.
    ("docs: objective map up to date", "gen_objective_map.py --check"),
    # Round 158: OBJECTIVE-AUDIT.md classifies every sentence of the objective as theorem, check, or
    # positioning. The last category is the point: some sentences are claims about the world, and
    # writing them as Lean theorems would be false.
    ("docs: objective audit up to date", "gen_objective_audit.py --check"),
    # Four rounds in a row (73, 81, 82, 84) asserted how much of the objective was covered and were
    # refuted by a fresh enumeration -- every time a throwaway regex, never a work error. The
    # enumeration is now fixed once, with the criteria written down next to the code.
    ("objective coverage: clauses x carriers, naming, vendor imports",
     "check_objective_coverage.py"),
    # check_doc_consistency answers "do two documents agree?" This answers "is the number RIGHT?",
    # which a consistency rule cannot do for a claim that appears exactly once -- round 94's
    # "387 refutations in a USAGE.md heading" was exactly that shape.
    ("usage claims: every measurable number in USAGE.md matches the tree",
     "check_usage_claims.py"),
    # The frozen governance archive is data the gates read, so it needs its own guard:
    # a stale entry-count claim inside CORRECTIONS.md is the exact drift class this
    # repository spent B1-B480 learning. `--lean archive` points the tool at the
    # archive directory instead of a Lean source tree.
    ("archive: corrections count", "check-corrections-count.py --root %s --lean archive" % ZERO),
]


# Checks that are only meaningful (or only affordable) in a full run.
#
# History: this used to be {"reactivity: gate", "reactivity: G4"} -- the two checks that
# prove the gate can FAIL were exactly the two skipped by the recommended `--fast`
# command. That made the advertised fast path prove less than the full one about
# correctness, while looking like the cheap way to check health. They are cheap enough
# now that the kernel tree is a single root: measured 3 s and 6 s respectively.
SLOW_ONLY = set()


def main():
    fast = "--fast" in sys.argv
    if fast:
        os.environ["DSH_GATE_SCOPE"] = "kernel"
    failures = []
    gating_ok = 0
    reports = 0
    t_start = time.time()
    for i, (label, cmd) in enumerate(CHECKS, 1):
        if fast and label in SLOW_ONLY:
            print("  %-30s skipped (--fast)" % label)
            continue
        parts = [sys.executable] + [os.path.join(HERE, p) if p.endswith(".py") else p
                                    for p in cmd.split()]
        t0 = time.time()
        r = subprocess.run(parts, cwd=ZERO, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        dt = time.time() - t0
        report = label in REPORT_ONLY
        if report:
            # mark reporters explicitly so a reader cannot mistake "ok" for "passed a gate"
            status = "reported" if r.returncode == 0 else "FAIL(%d)" % r.returncode
            reports += 1
        else:
            status = "ok" if r.returncode == 0 else "FAIL(%d)" % r.returncode
            if r.returncode == 0:
                gating_ok += 1
        # `flush=True` matters: this run takes minutes, and a redirected stdout otherwise
        # shows nothing until the process exits -- which reads like a hang.
        print("  [%2d/%d] %-30s %-9s %5.1fs" % (i, len(CHECKS), label, status, dt), flush=True)
        if r.returncode != 0:
            failures.append((label, r.returncode, (r.stdout or "") + (r.stderr or "")))
    print("=" * 60, flush=True)
    if failures:
        for label, code, out in failures:
            print("\n--- %s (exit %d) ---" % (label, code))
            print(out.strip()[:1200])
    mode = "fast (kernel only)" if fast else "full"
    # The summary separates the two populations on purpose. A single "32/32 PASS" hid the
    # fact that 16 of those 32 could not have returned anything but 0.
    print("VERIFY ALL [%s]: %s  (%.1fs total)" %
          (mode, "PASS" if not failures else "%d FAILURE(S)" % len(failures),
           time.time() - t_start), flush=True)
    print("  gating checks passed : %d  (these CAN fail)" % gating_ok, flush=True)
    print("  report-only checks   : %d  (these print findings; exit code is not a verdict)"
          % reports, flush=True)
    if fast:
        print("note: --fast restricts every walk to the kernel zone. Run without --fast before "
              "concluding the tree is acceptable.")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
