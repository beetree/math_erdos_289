# Progress report

Last updated: 2026-09-03 23:20 PDT. Live view: `scripts/status.sh`.

## One-line status

**Two audited axioms remain, by decision.** `Erdos289.candidateStatement : CandidateStatement`
builds with no `sorry` anywhere in its dependency chain, with zero warnings, and its axiom
report (printed by every build, from `Erdos289/Main.lean`) is exactly `propext`,
`Classical.choice`, `Quot.sound`, `Erdos289.External.Assumed.bourgain_garaev`,
`Erdos289.External.Assumed.cfhmpsv_structure`. These two are to be left as axioms. The divisor bound, Mertens' second
theorem, and Liu–Sawhney are proved via verbatim ports from the `plby/lean-proofs` corpus
(`SolveMath/`, 41 modules, ≈ 30,700 lines; `Erdos289/Ported.lean`). Removing the remaining
three gives the **unconditional certificate**. `Erdos289/Compat.lean` also derives the
corpus/FormalConjectures-style statement `erdos_289_statement` from ours.

## What has to be removed

### A. Open sorries (block the conditional certificate)

| # | Declaration | File | Paper reference | What it says | Who is on it | Rounds so far |
|---|---|---|---|---|---|---|
| S1 | `equidist_inverse` | `Lemma1EquidistStmt.lean` | §2, lines 135–148; **author's blueprint** `erdos_289_lemma1_equidistribution_blueprint.md` (Lemmas 1.1–6.4) | Inverses `t⁻¹ mod U` for `t` in a prefix, `U ∈ {q, 2q, 4q, 4pq}`, are equidistributed in residue intervals with error `o(q^ε)`, from Bourgain–Garaev + Erdős–Turán | Gemini variant B proved everything except the per-frequency bound `exp_sum_bound` (= blueprint Lemma 3.3). On that lemma: Gemini round 2 (`equidistB2`, in `Lemma1EquidistB.lean`) and Opus with the blueprint (`equidistD`, in the namespaced copy `Lemma1EquidistD.lean`). Independent full attempts still running: Opus `equidist`, Gemini `equidistC`. | 1 Sonnet (partial) + 1 Gemini (all but one lemma) + 4 running |
| ~~S2~~ | `odd_case_count` | `Lemma1OddCount.lean` | §2, (2.2) | Odd-prime-power case: at least `M/360 − κM` good `t`, from S1 at moduli `4q` and `4pq` | **CLOSED** | done |
| ~~S3~~ | `paper_steps_4_5` | `Lemma3Steps45.lean` | §3, (3.2), lines 230–272 | Simultaneous approximation + divisor bound force the GAP's active volume `V ≥ q^{1 − dε/8 − o(1)}` | **CLOSED** | done |

Bookkeeping sorries that do not block anything once S1–S3 close:

| Declaration | File | Note |
|---|---|---|
| (none) | | Our six input statements are aliases of the bridge theorems; our own axiom declarations are gone. |
| variant files `Lemma1EquidistB/C.lean`, `Lemma3Steps45B.lean` | | competitors' working copies; deleted or merged when a winner is chosen |

### B. The six axioms (block the unconditional certificate)

All six are declared in the author's audited module `ExternalAxioms.lean` (SHA-256
`6a4affa2…`), and separately in our `External.lean`/`ErdosTuran.lean` in our own encoding.
`ExternalBridge.lean` proves ours from the audited ones (all 6 done). When the bridge is complete, our six declarations become theorems and
the axiom report names exactly `Erdos289.External.Assumed.*`.

| # | Axiom | Source | Used by | Prospects for removal |
|---|---|---|---|---|
| A1 | `liu_sawhney` | Liu–Sawhney, Thm 1.3 | Lemma 6 → core | A port from the same corpus is in progress in `expert_input/ported/LiuSawhney/` (run `port_ls`, launched outside this session). |
| ~~A2~~ | `cfhmpsv_structure` | Conlon–Fox–Pham Thm 1.5 via CFHMPSV Thm 3 | Lemma 3 | **Being discharged on this branch** by the verbatim port of the CFP structure theorem from `plby/lean-proofs` (Erdős 186 development; 258 modules, ≈90k lines, Apache-2.0; `ErdosProblems/`), bridged to the audited statement in `Erdos289/CFPBridge.lean`. Decision: use the port rather than the elementary covering (docs Section 1). |
| A3 | `bourgain_garaev` | Bourgain–Garaev, Thm 5 | Lemma 1 (S1) | **Being discharged on this branch** by the author's elementary signed-fiber construction (docs Sections 2–4): Lemmas F1, F2, D1, signed cancellation (D3), mass tail (D5), and the adapted Lemma 5 / core / descent / assembly. |
| A4 | `erdos_turan` | discrete Erdős–Turán inequality | Lemma 1 (S1) | Moderate. Classical; a self-contained Fourier-analytic proof is feasible. |
| ~~A5~~ | `mertens_second` | Mertens' second theorem | Lemma 1 (sieve), Lemma 4 | **DISCHARGED**: ported proof (4 modules, 1,591 lines) from `plby/lean-proofs`; axiom-clean. |
| ~~A6~~ | `divisor_bound` | Hardy–Wright Thm 315 | Lemma 1, Lemma 3 | **DISCHARGED**: ported proof (342 lines) from `plby/lean-proofs`; axiom-clean. |

### C. Final refactor (after A is closed)

State the main theorem as `ExternalInputs → CandidateStatement`, per Appendix B of the
six-axiom audit, so the six inputs are visible in the theorem's type and the axiom report
shows only the three standard axioms.

## Agents (branch `elementary-replacements`, worktree `~/math_erdos_289_pr`)

| Run | Model | File | Task | Status |
|---|---|---|---|---|
| `covering` | Opus | `Covering.lean` | docs §1 elementary covering | stopped (port chosen) |
| `signedF1` | Opus | `SignedF1.lean` | Lemma F1 signed fibers | running |
| `signedF2` | Opus | `SignedF2.lean` | Lemma F2 orientation | running |
| `signedD1` | Opus | `SignedD1.lean` | Lemma D1 density zero | running |
| `signedCancel` | Sonnet (janna) | `SignedCancel.lean` | signed cancellation (D3) | running |
| `signedTail` | Sonnet (johan) | `SignedTail.lean` | mass tail (D4)–(D5) | running |
| `lemma5S` | Sonnet (janna) | `Lemma5S.lean` | auxiliary family avoiding `PstarSigned` | running |
| `coreS` | Sonnet (johan) | `CoreS.lean` | core with density-zero protected set | done, proved |

## Agents (earlier, on main)

| Run name | CLI / model | File(s) owned | Task | Status |
|---|---|---|---|---|
| `equidist` | `claude-johan`, Opus, high | `Lemma1Equidist.lean` (new) | S1, independent full attempt | running |
| `equidistB` | `agy`, Gemini 3.8 Flash high | `Lemma1EquidistB.lean` (new) | S1, strategy B | done: all but `exp_sum_bound` |
| `equidistB2` | `agy`, Gemini 3.8 Flash high | `Lemma1EquidistB.lean` | `exp_sum_bound` | running |
| `equidistD` | `claude-johan`, Opus, high | `Lemma1EquidistD.lean` (namespaced copy of B) | `exp_sum_bound` following the author's blueprint | running |
| `equidistC` | `agy`, Gemini 3.8 Flash high | `Lemma1EquidistC.lean` (new) | S1, competitor, strategy C | running |
| `oddcount` | `claude-leet`, Sonnet, high | `Lemma1OddCount.lean` | S2 | **done, proved** |
| `steps45` | `claude-johan`, Opus, high | `Lemma3Steps45.lean` | S3 | **done, proved** |
| `steps45B` | `agy`, Gemini 3.8 Flash high | `Lemma3Steps45B.lean` | S3, competitor | done, also proved; file removed (Opus version integrated) |
| `realign` | `claude-leet`, Sonnet, high | `External.lean`, `Lemma3Basic.lean`, `ExternalBridge.lean` | base-2 realignment + sixth bridge | done |

Rules: one agent per file; competitors work on renamed copies; the orchestrator (this session)
merges winners, splits files, fixes interfaces, commits only compiling states.

## Completed (sorry-free)

Defs, Sorting, Lemma 2, Cancel, DenBound, Greedy, Harmonic, Tail, Lemma 4, Lemma 5 (with
(4.2), (4.5)), Lemma 6, Core (§5), MainPairs (§6), Descent (§4, with (4.8)), CorrData,
Assembly (§7), Target (bridge to the audited `CandidateStatement`), Main (terminal theorem),
Expert (ported starter lemmas), Lemma 1: Basic, sieve, assembly, even-case count; Lemma 3:
Basic (setup, pigeonhole, face count, endgame), core assembly.

## History of the session (for orientation)

1. Environment, definitions, statement; first wave of ten parallel Sonnet subagents on leaves.
2. Second wave: core, main pairs, descent, correction data, Lemmas 4–6, assembly, bridge.
3. Author's inputs arrived: audited target (`Intervals.lean`), audited six axioms
   (`ExternalAxioms.lean`); both included unchanged, both audits reproduced in README.
4. Terminal theorem compiled end to end (with `sorryAx` from Lemma 1 / Lemma 3 cores).
5. Large files split; Opus and Gemini competitors added on the two hard cores.
6. Author's Lemma 1 equidistribution blueprint arrived (20 explicit lemmas with constants); fed to the agents on S1.
7. S1 (Opus), S2 (Sonnet), S3 (Opus and Gemini independently) closed; competitor files removed; axioms routed through the bridge. Conditional certificate achieved at commit `38b270a`.
8. Ported axiom-clean proofs of the divisor bound and Mertens (from `plby/lean-proofs` via `solve-math`) integrated; four audited axioms remain.
9. Liu–Sawhney port integrated; three audited axioms remain (commit `80ec5f7`).
10. Finite Erdős–Turán port integrated and Lemma 1 adapted to its `N/√H` form; two audited axioms remain. Warning cleanup complete (zero warnings).
