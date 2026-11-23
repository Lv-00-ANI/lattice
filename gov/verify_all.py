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
    # **Round 776: no longer report-only.** The five bare sections were repaired (the spec states its
    # obligations in fenced `name : ...` blocks, which the checker now reads) and the two remaining
    # broken promises are annotated in the spec AND recorded in `obligations-known-gaps.txt` with a
    # reason. **What is left is a real gate.**
    "gen: proof chain (geo)", "gen: proof chain (kernel)",
    "census: end-to-end by content",
    "gen: primitive matrix",
    # Round 54. The census returns 0 by construction (a `theorem` in a comment is not a declaration,
    # and saying so is not a failure). Registered as gating it would be a check that cannot fail.
    "report: comment shadow declarations",
      "usage: skeleton main theorems",
    # Round 99. A `def X : Prop` whose proof's `intro` binds a variable that then appears nowhere else.
    # REPORT-ONLY because a cited theorem may consume that binder inside its own statement -- `intro n Φ;
    # exact penaltyLoss_eq_zero_iff_holds_sq Φ` has `n` unused HERE and is not vacuous. A regex cannot
    # tell that apart from the ladder's genuinely discarded `hwalk`, so the check reports and a human
    # decides; `gov/prop-def-baseline.txt` records the current 44 so a NEW one shows up as a diff.
    "report: prop-def binder strength",
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
    # Round 242. `audit_geo.py` matched `Zero.Geo.` (the OLD library prefix) for its whole life,
    # so its graph was empty and every finding was vacuous while it sat here as a GATING check.
    # It now has a real `--self-test`; running it is the difference between "has a self-test" and
    # "the self-test is known to work".
    ("audit: geo self-test", "audit_geo.py --self-test"),
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
    # **Round 775 (STAGE 4, gate defect G-12): the SPEC SOURCE had no gate at all.**
    # `PROOF-OBLIGATIONS.md` is the document that says what the project promises to prove, and every
    # other checker guards a DERIVED artifact instead. **=> a spec source that no gate reads can
    # drift from the tree forever without anything failing.**
    # **Report-only while the five bare sections are repaired** -- the checker already finds a real
    # gap, and turning it gating before the gap is closed would block every other check.
    ("obligations doc: sections name their carriers", "check_obligations_doc.py"),
    ("gen: proof chain (geo)", "proof_chain_geo.py"),
    # Census, NOT a gate: a theorem that touches one layer is not a defect. What would be a
    # defect is CLAIMING otherwise, and I5 is the gate for that. This runs the same transitive
    # analysis I5 uses, on EVERY theorem instead of only the ones named `e2e` -- round 219
    # measured that the name filter left the chain's own work (Geo) entirely outside coverage.
    # Round 234. A `git mv` orphans every PROOF-DEBT verdict for the moved file; the join then
    # misses and `in_degree` silently falls back to 0, so the ledger reports reviewed files as
    # unreviewed while the coverage table still claims 100% of the load-bearing set.
    ("debt: no orphaned verdicts", "check_proof_debt_orphans.py"),
    # Round 11. A new defect class: a theorem whose whole proof forwards to another declaration.
    # udit_duplicates.py groups by NAME and is report-only, so it sees neither of these.
    ("audit: alias census", "audit_aliases.py"),
    ("audit: alias self-test", "audit_aliases.py --self-test"),
    ("report: prop-def binder strength", "check_prop_def_strength.py --check"),
    ("meta: prop-def strength self-test", "check_prop_def_strength.py --self-test"),
    # Round 1020: `clean_probes.py --check` was REMOVED from this list. It failed four times in sequence
    # with gate.py and never alone: gate.py leaves an artifact transiently, and a recovery tool positioned
    # as a gate therefore reports a state that is already gone by the time anyone looks. **gate.py's I7 is
    # the designed checker for artifacts in both directions and it IS a gate; clean_probes.py exists to
    # recover from a KILLED run, which is an explicit act, not a periodic check.** Only its self-test
    # stays here, so the parser and the imported-probe rule remain pinned.
    ("meta: probe cleaner self-test", "clean_probes.py --self-test"),
    # Round 1013: the count sync was the last hand-driven step, and round 1012 recorded its cost -- two
    # numbers typed one off, caught by a checker rather than by me. `sync_counts.py` takes both the old and
    # the new value from the CHECKERS, so it cannot invent a number. Only its self-test is a gate: the
    # checkers themselves already gate the documents.
    ("meta: count sync self-test", "sync_counts.py --self-test"),
    # Round 14. A splice ate a file's final end Lattice and lake build still passed.
    ("audit: namespace closure", "check_namespace_balance.py"),
    ("audit: namespace self-test", "check_namespace_balance.py --self-test"),
    # Round 16. The C ABI names are strings; nothing in Lean ties them to the primitives that exist.
    ("audit: C ABI matches primitives", "check_cinterface_abi.py"),
    ("audit: C ABI self-test", "check_cinterface_abi.py --self-test"),
    # Round 26, L4-7. The content census was a REPORTER: 1,827 cross-layer theorems printed and gated on
    # nothing. This is the floor -- losing one fails, gaining one does not.
    ("census: cross-layer floor", "check_endtoend_floor.py"),
    ("census: cross-layer floor self-test", "check_endtoend_floor.py --self-test"),
    # Round 27, L4-1/L4-2. PROOF-DEBT.md carried THREE numbers for one quantity (78.2% in its table,
    # 100% in its prose, 839 in a caveat saying the set was computed wrongly) and no instrument could
    # recompute any of them. This gate recomputes and compares.
    ("debt: coverage table equals the measurement", "check_coverage_claim.py"),
    ("debt: coverage claim self-test", "check_coverage_claim.py --self-test"),
    # Round 29, L4-5. Orphans checked the FILE; nothing checked the NAME. 12 verdicts were judging
    # declarations that no longer exist anywhere, and they printed exactly like live ones.
    ("debt: verdict freshness", "check_verdict_freshness.py"),
    ("debt: verdict freshness self-test", "check_verdict_freshness.py --self-test"),
    ("census: end-to-end by content", "check_endtoend_content.py"),
    # Round 231. Reads each `Primitive`'s `Input := ...` / `Output := ...` SOURCE TEXT and
    # builds the adapter matrix. It CANNOT see Lean types, so "same text" is sufficient but not
    # necessary for "no adapter needed" -- a type synonym or an unfoldable abbrev would be the
    # same type with different text. That is why it is report-only: it is a census, not a gate.
    ("gen: primitive matrix", "gen_primitive_matrix.py"),
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
    # Round 856 (P0-4): the plan asked for the `:= rfl` theorems to be downgraded, quoting 60 of them.
    # Measurement found 246, and they are NOT one kind: 119 are load-bearing API, 41 are constructor
    # unfoldings, and only 85 are leaf numeral/bool literals -- the only class that records a constant
    # nothing consumes. Classifying by CITATION rather than by statement shape (text cannot tell the
    # classes apart: `artifact_layer_count` and `graphTheory_templateNames_length` are identical in form
    # but one is a derivation check and the other a free-floating constant) makes those 85 a registered
    # baseline, so a NEW free-floating literal cannot appear unnoticed while legitimate proofs are
    # never touched.
    ("literals: free-floating `rfl` theorems are registered", "check_literal_rfl.py"),
    # The audit found that `plugin_inventory.py --check` had a HARD-CODED empty `duplicates` dict,
    # so it could never fail, and that it was not wired into any gate at all -- meaning the plugin
    # map could silently acquire an ambiguous attribution. The duplicate detection is now computed
    # and the check runs here.
    ("plugin map: every theorem has exactly one plugin", "plugin_inventory.py --check"),
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
    ("meta: layer cycle does not grow", "check_layer_cycle.py"),
    ("meta: layer health invariants hold", "check_layer_health.py"),
    ("audit: duplicate short names bounded", "audit_duplicate_names.py --check"),
    ("audit: no new duplicated STATEMENTS (not just names)", "audit_theorem_duplication.py --check"),
    ("audit: theorem duplication self-test", "audit_theorem_duplication.py --self-test"),
    ("audit: duplicate names classified, none accidental", "check_duplicate_classes.py --check"),
    # Round 1032: how much of the proof chain is DEFINITIONAL. `check_proof_strength.py` catches
    # reflexive statements, `exact h` proofs and True-like defs; it does NOT catch the shape where a
    # predicate pins its own argument (`def M W k : Prop := W = compile k`) and the proof is
    # `have := h; exact rfl`. That shape appeared in Core/IR AND again in Core/CIC. This checker
    # measures the whole tree, and the baseline can only shrink.
    ("audit: definitional proofs bounded and self-tested",
     "audit_definitional_proofs.py --check"),
    ("audit: definitional proof detector self-test",
     "audit_definitional_proofs.py --self-test"),
    # **Round 1034: the geometry layer is FROZEN. It is an EXAMPLE domain, not part of the chain
    # (data <-> token <-> symbol <-> weight). Measured before obeying the archive instruction: 100
    # modules, ~17.8k lines, 26 direct importers, 43 users of `Lattice.Geo.*`, and the transitive
    # closure of those imports is ALL 100 -- so a physical archive would delete real mainline code.
    # A partial archive (68 of 100) was attempted and failed to build; it is in the branch history.
    # What can be enforced is that the layer stops GROWING: this gate bounds its importer set.**
    ("frozen: geometry layer importers bounded", "check_frozen_reference.py --check"),
    ("frozen: geometry baseline self-test", "check_frozen_reference.py --self-test"),
    # **Round 1039: does every ADJACENT link of the objective's chain have a theorem whose STATEMENT
    # mentions both stages? Three consecutive rounds I guessed at a missing connector and found it
    # already built (LoopClosure, decodeSpec_none_of_not_code, extract_after_repair). Guessing is
    # the unreliable method; this gate enumerates. It cannot demand a COUNT -- one connecting
    # theorem is enough for a link to exist -- only that no adjacent link goes EMPTY.**
    ("chain: every adjacent link has a connecting theorem", "chain_connectors.py --check"),
    ("chain: connector marker matching self-test", "chain_connectors.py --self-test"),
    ("meta: five pipeline stages present", "check_pipeline_stages.py"),
    ("meta: proof chain links present and cited", "gen_proof_chain.py --check"),
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
    # Round 43. Lattice/Compose.lean was on disk but NOT imported by Lattice.lean, so five rounds of
    # Compose work were built only when named explicitly -- and a syntax error sat in that file for five
    # rounds because the file was unreachable. I7 checks that oleans EXIST; it cannot see reachability.
    ("meta: root closure (every layer reachable)", "check_root_closure.py"),
    ("meta: root closure self-test", "check_root_closure.py --self-test"),
    # Round 44. The same question one level down. It also reports EMPTY layer directories:
    # `Lattice/Slots/` was empty, so a file-enumerating scan skipped that whole layer and reported
    # zero unreachable modules for a tree it had not fully examined.
    ("meta: layer reachability", "check_layer_reachability.py"),
    ("meta: layer registry is single-sourced", "check_layer_registry.py"),
    ("meta: archived LvFormal stays out of the build", "check_reference_archive.py"),
    ("meta: layer reachability self-test", "check_layer_reachability.py --self-test"),
    # Round 45. The third variant of the same question: rounds 43 and 44 asked WHICH modules a
    # build reaches; this asks whether a module entered a build at all. It also records the
    # measurement that corrects the forwarded list: "310 stale oleans" is an mtime artifact, not a
    # defect, because `lake` decides from content hashes.
    ("meta: olean presence (non-Reference)", "check_olean_presence.py"),
    ("meta: olean presence self-test", "check_olean_presence.py --self-test"),
    # Round 54. A theorem-shaped line can land in a comment -- round 53 lost one to a fenced
    # quote of `extract_to_weights` inside RealEndToEnd's docstring, and blamed the counter.
    # The counter was right; nothing reported "your text is in a comment".
    ("report: comment shadow declarations", "check_comment_shadow_declarations.py"),
    # The self-test exercises `comment_spans` and `fenced`, the two functions that can be wrong.
    # It failed once already (on a snippet whose prose was not at the start of a line), so it gates.
    ("report: comment shadow self-test", "check_comment_shadow_declarations.py --self-test"),
    ("meta: no nominally-complete proof shapes", "check_proof_strength.py"),
    # Round 197. A hypothesis that is PROVABLE OUTRIGHT makes the theorem weaker than its statement
    # suggests. `compileProg_correct`'s `(h : stackDepth e ≤ 1)` was exactly that: it was passed to
    # `compileAcc_correct`, so `linter.unusedVariables` stayed silent -- while `stackDepth e = 1` for
    # every expression. No linter finds this class. This gate catches the syntactically visible
    # sub-class (`a = a`, `a ↔ a`, `True`) with zero false positives, and the file states plainly
    # which sub-class it does NOT catch.
    ("meta: no vacuously true hypothesis", "check_vacuous_hypotheses.py"),
    # Round 125. ARCHITECTURE-CARRIERS.md listed Conv / Attention / DAG beside Norm, with a
    # directory block and per-carrier proof names, while only Norm and GNN existed on disk.
    # A document that says "implemented" where the tree says otherwise is a CORRECTNESS problem:
    # later rounds plan against it.
    ("docs: carrier claims match the tree", "check_carrier_claims.py"),
    # Round 136. Eighteen places where an ABSTRACT ROLE was welded to a CONCRETE INSTANCE
    # (`Weights` as a bare vector, `State` as `K -> Option Nat`, `Obligation.theoremName` as a
    # `String`, ...). Each compiles and each proves something; what they cost is EXPRESSIVENESS.
    # A list in markdown decays, so the audit is executable: a fixed item must be REMOVED from
    # `PARAMETERIZATION-AUDIT.md`, and the gate says which ones are ready.
    ("report: parameterization audit is live", "check_parameterization.py"),
    # Round 137. `Obligation.theoremName` was a `String`, so a manifest could name a theorem that
    # did not exist -- and TWO DAG OBLIGATIONS DID (`denote_seq`, `denote_par` for
    # `dag_denote_seq`, `dag_denote_par`). `Obligation.proof : Option Prop` now carries the
    # proposition; this check counts the migration and catches ghost names and missing files.
    ("report: obligations carry their proofs", "check_obligation_proofs.py"),
    # Round 982: `PLUGIN-SYSTEM.md` specifies a `plugin.yml` capability index and the tree had ZERO.
    # Eleven now exist, and this check is the only reason they are worth having: it requires each index to
    # agree field-for-field with its Lean manifest, and each named theorem to be DECLARED IN the file it
    # names. `--self-test` pins the parser and both rejections so the gate cannot pass by parsing nothing.
    ("plugins: capability index agrees with the Lean manifests", "check_plugin_yml.py"),
    # Round 994: the audit claimed `ConstraintSet` had 4, `VectorConstraint` 8 and `IRWeights` 3 real
    # definitions. Measured with comment stripping, each has exactly ONE -- the other occurrences are
    # quotations inside docstrings. This keeps the measured count from growing, and its self-test proves
    # the stripper is what decides (a docstring copy must NOT count).
    ("audit: configured types have one real definition", "audit_type_duplication.py"),
    ("meta: type duplication audit self-test", "audit_type_duplication.py --self-test"),
    # Round 995: before filling `PluginProof`'s vacuous slots, answer the question that HAS a mechanical
    # answer -- is every NAMED slot proposition backed by a `<prop>_holds` theorem? Filling a slot with an
    # arbitrary true statement would be the substitution the audit warned about (`na` becomes the new `True`).
    ("audit: plugin slots, named propositions are proved", "audit_plugin_slots.py"),
    ("meta: plugin slot audit self-test", "audit_plugin_slots.py --self-test"),
    ("meta: plugin index checker self-test", "check_plugin_yml.py --self-test"),
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
    # Round 966: the audit table's evidence column is a CURATED list of declaration names, and
    # nothing checked that those names still exist. It had silently gone stale -- after rounds
    # 944-965 the "symbol <-> weight" row still cited only the pre-P8 declarations and knew
    # nothing about the twenty-one P8 files. The generator now refuses to run if any cited
    # identifier is not a declaration, and this self-test proves that refusal can actually fire.
    ("docs: objective audit citations exist (self-test)", "gen_objective_audit.py --self-test"),
    # Round 977: REVERSIBILITY-MAP.md names theorems; this guards that every named theorem exists, and
    # `--self-test` pins the classifier so the guard cannot silently pass by classifying nothing.
    ("docs: reversibility map citations exist", "audit_reversibility_coverage.py"),
    ("meta: reversibility classifier self-test", "audit_reversibility_coverage.py --self-test"),
    # Round 968: twenty-one copies of `strip_comments` had accumulated. Nine were measured
    # BYTE-IDENTICAL on 1,169 Lean files; five of those now import one authority, and this pins that
    # authority's contract -- in particular that NESTED block comments are handled, which no consumer
    # exercises on its own.
    ("meta: comment stripper contract", "tools/lean_source.py --self-test"),
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
# **Round 1015: this set was EMPTY, so `--fast` skipped nothing and only made gate.py cheaper.**
# The machine has run out of memory during the full run for five consecutive rounds, so there was no
# assertable evidence at all. The eleven reactivity checks are the expensive ones AND the ones that
# plant probe sources, so they are the right thing to skip: `--fast` now covers gate.py, every audit,
# every report and every pre-check, and fits in ~3 GB.
SLOW_ONLY = {
    "reactivity: gate", "reactivity: layering", "reactivity: slots", "reactivity: comments",
    "reactivity: I8 gate", "reactivity: registry", "reactivity: registry-gate", "reactivity: G4",
    "reactivity: tables", "reactivity: counts", "reactivity: ci workflow",
}


def main():
    fast = "--fast" in sys.argv
    # **Round 1015: this used to set DSH_GATE_SCOPE=kernel, which CHANGES gate.py's verdict -- the narrowed
    # scope reported six I5 findings that the full scope does not. A "fast" mode that alters a gate's answer is
    # not a fast mode, it is a different gate. `--fast` now only skips the reactivity checks.**
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
    mode = "fast (reactivity skipped)" if fast else "full"
    # The summary separates the two populations on purpose. A single "32/32 PASS" hid the
    # fact that 16 of those 32 could not have returned anything but 0.
    print("VERIFY ALL [%s]: %s  (%.1fs total)" %
          (mode, "PASS" if not failures else "%d FAILURE(S)" % len(failures),
           time.time() - t_start), flush=True)
    # **Round 1032: print the authoritative triple. The governance docs hand-typed it as
    # "120 checks, 94 gates" while the code had 120 checks and 99 gates -- and 94 + 21 reporters
    # does not even sum to 120, so the doc was internally inconsistent and nobody noticed. A number
    # that a run PRINTS cannot drift; a number a person retypes can.**
    n_gating_reg = len([1 for l, _ in CHECKS if l not in REPORT_ONLY])
    print("  registered           : %d checks = %d gating + %d reporters"
          % (len(CHECKS), n_gating_reg, len(REPORT_ONLY)), flush=True)
    print("  gating checks passed : %d  (these CAN fail)" % gating_ok, flush=True)
    print("  report-only checks   : %d  (these print findings; exit code is not a verdict)"
          % reports, flush=True)
    if fast:
        # Round 54 removed the DSH_GATE_SCOPE=kernel trick because narrowing the scope changed gate's
        # verdict (6 I5 findings that the full scope does not produce) and propagated to children.
        # --fast now only skips the reactivity probes, and those are named.
        print("note: --fast SKIPPED %d reactivity probe checks (named in SLOW_ONLY); every walk ran at "
              "full scope. Run without --fast to include them." % len(SLOW_ONLY), flush=True)
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
