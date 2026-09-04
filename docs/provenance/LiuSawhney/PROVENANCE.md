# Provenance: Liu–Sawhney finite density theorem (Erdős Problem 289, external input 1)

## Source

- Source repository: `/home/johan/solve-math-workers/worker-1/solve-math` (read-only), branch
  `worker-1/plby-import-wave2`, commit `8f953ab3ec714753b2566d51f6dee9f12f4b0b0e`.
- These files were ported into `solve-math` from Boris Alexeev's `plby/lean-proofs`, at pinned
  commit `61fce10ef6671b1df0325f22bc76c8cd1f2fa554` (`src/latest/ErdosProblems/Erdos300.lean`),
  with formal authors Codex / GPT-5.6 Sol.
- **LICENSE STATUS: no LICENSE file found upstream.** (Matches the source header's own remark,
  verbatim: "LICENSE STATUS: NO LICENSE FOUND.", in
  `SolveMath/Edges/Erdos/P300/Statement.lean`.)
- Informal proof authors: Yang P. Liu and Mehtaab Sawhney, "On further questions regarding unit
  fractions", arXiv:2404.07113 (2024), Theorem 1.3.

## Ported modules

The 36 modules listed in `expert_input/ported/ls_kept_modules.txt`, plus one module added beyond
that list (see "Deviation from the given kept-module list" below), for 37 files / 28,789 lines
total:

| Module (relative to `LiuSawhney/SolveMath/`) | Lines |
|---|---|
| `Corpus/Analysis/AdditiveCharacterGeometricSums.lean` | 265 |
| `Corpus/Analysis/RPowIntegralEstimates.lean` (added; not in the given kept list) | 80 |
| `Corpus/Analysis/UnitFractionAnalyticEstimates/AbsVonMangoldtDiv.lean` | 565 |
| `Corpus/Analysis/UnitFractionAnalyticEstimates/DivisorBound₁.lean` | 591 |
| `Corpus/Analysis/UnitFractionAnalyticEstimates/PartialSummation.lean` | 560 |
| `Corpus/Analysis/UnitFractionAnalyticEstimates/PrimeReciprocalEq.lean` | 623 |
| `Corpus/Analysis/UnitFractionAnalyticEstimates/TendstoLogCoeTop.lean` | 318 |
| `Corpus/Analysis/UnitFractionAnalyticEstimates/WeakMertensThirdUpper.lean` | 398 |
| `Corpus/Analysis/UnitFractionFourierAnalysis/Basic.lean` | 630 |
| `Corpus/Analysis/UnitFractionFourierAnalysis/CircleMethod.lean` | 577 |
| `Corpus/Analysis/UnitFractionFourierAnalysis/ExponentialSums.lean` | 765 |
| `Corpus/Analysis/UnitFractionFourierAnalysis/MajorArcs.lean` | 597 |
| `Corpus/NumberTheory/MertensTheorems.lean` | 1739 |
| `Corpus/NumberTheory/PrimeCountingIccCard.lean` | 39 (pruned; see below) |
| `Corpus/NumberTheory/ReciprocalComparison.lean` | 20 |
| `Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/FiniteBernoulliHoeffding.lean` | 541 (pruned; see below) |
| `Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/FiniteWeightedSubsetFourier.lean` | 278 |
| `Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/PrimePowerLCMTelescope.lean` | 4506 |
| `Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/SmoothPrimePowerFactorization.lean` | 1053 |
| `Corpus/NumberTheory/UnitFractionAuxiliaryEstimates/Basic.lean` | 684 |
| `Corpus/NumberTheory/UnitFractionAuxiliaryEstimates/DivisorSelection.lean` | 606 |
| `Corpus/NumberTheory/UnitFractionAuxiliaryEstimates/FinalEstimates.lean` | 839 |
| `Corpus/NumberTheory/UnitFractionAuxiliaryEstimates/LargeN.lean` | 644 |
| `Corpus/NumberTheory/UnitFractionAuxiliaryEstimates/PrimePower.lean` | 806 |
| `Corpus/NumberTheory/UnitFractionAuxiliaryEstimates/ReciprocalSums.lean` | 763 |
| `Corpus/NumberTheory/UnitFractionDensities.lean` | 492 |
| `Corpus/NumberTheory/UnitFractionFinalResults/FilterDiv.lean` | 748 |
| `Corpus/NumberTheory/UnitFractionFinalResults/PrimeCountingSieve.lean` | 1021 (forced-fix lemma added; see below) |
| `Corpus/NumberTheory/UnitFractionFinalResults/UpperDensity.lean` | 904 |
| `Corpus/NumberTheory/UnitFractionSubsumResults/Basic.lean` | 495 |
| `Corpus/NumberTheory/UnitFractionSubsumResults/GoodProperties.lean` | 607 |
| `Corpus/NumberTheory/UnitFractionSubsumResults/LargeEstimates.lean` | 801 |
| `Corpus/NumberTheory/UnitFractionSubsumResults/PruningLemmas.lean` | 543 |
| `Corpus/NumberTheory/UnitFractionSubsumResults/TechnicalProposition.lean` | 644 |
| `Corpus/NumberTheory/UnitFractionSubsumResults/TwoValues.lean` | 508 |
| `Edges/Erdos/P300/Solution.lean` | 3486 (pruned; see below) |
| `Edges/Erdos/P300/Statement.lean` | 53 |

Main ported theorem: `Erdos300.dense_contains_one : Erdos300.DenseContainsOne`, in
`SolveMath/Edges/Erdos/P300/Solution.lean`.

Bridge theorems (new, in `Erdos289Bridge.lean`, namespace `Erdos289.Ported`):
`liu_sawhney` and `liu_sawhney_audited`.

## Edits made

### (a) Import edits (mechanical, per the global rules)

Applied uniformly wherever the given source imported a module outside the kept-module list:

- **Umbrella imports, replaced by direct imports of their kept submodules:**
  - `SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates` → `.Basic`, `.PrimePower`,
    `.LargeN`, `.ReciprocalSums`, `.DivisorSelection`, `.FinalEstimates` (all 6 kept).
  - `SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates` → `.TendstoLogCoeTop`,
    `.PartialSummation`, `.DivisorBound₁`, `.AbsVonMangoldtDiv`, `.PrimeReciprocalEq`,
    `.WeakMertensThirdUpper` (all 6 kept).
  - `SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis` → `.Basic`, `.ExponentialSums`,
    `.MajorArcs`, `.CircleMethod` (all 4 kept).
  - `SolveMath.Corpus.NumberTheory.UnitFractionSubsumResults` → `.Basic`, `.TwoValues`,
    `.GoodProperties`, `.PruningLemmas`, `.LargeEstimates`, `.TechnicalProposition` (the 6 kept
    submodules; the umbrella's 7th import, `.Corollaries`, is not kept and was confirmed unused
    by every file that imported the umbrella).
  - `SolveMath.Corpus.NumberTheory.UnitFractionFinalResults` → `.PrimeCountingSieve`,
    `.FilterDiv`, `.UpperDensity` (the 3 kept submodules; the umbrella's other 3 imports,
    `.HarmonicBounds`, `.HarmonicRegular`, `.HarmonicSmooth`, are not kept and were confirmed
    unused).
  - Applied to: `Edges/Erdos/P300/Solution.lean`,
    `Corpus/NumberTheory/UnitFractionFinalResults/PrimeCountingSieve.lean`,
    `Corpus/NumberTheory/UnitFractionSubsumResults/Basic.lean`,
    `Corpus/NumberTheory/UnitFractionAuxiliaryEstimates/Basic.lean`,
    `Corpus/Analysis/UnitFractionFourierAnalysis/Basic.lean`,
    `Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/{PrimePowerLCMTelescope,SmoothPrimePowerFactorization}.lean`
    (each got only the umbrella replacements its own import list actually named).

- **Non-umbrella, non-kept imports, deleted with no replacement (confirmed unused after
  deletion, except where noted under "Forced minimal fixes" below):**
  - `SolveMath.Corpus.Analysis.UnitFractionAnalyticMisc` (dropped from
    `Corpus/Analysis/UnitFractionAnalyticEstimates/TendstoLogCoeTop.lean`,
    `Corpus/Analysis/UnitFractionFourierAnalysis/Basic.lean`,
    `Corpus/NumberTheory/UnitFractionAuxiliaryEstimates/Basic.lean`,
    `Corpus/NumberTheory/UnitFractionSubsumResults/Basic.lean`; genuinely used by one further
    file, `PrimeCountingSieve.lean` — see forced fix below).
  - `SolveMath.Corpus.NumberTheory.IntervalMultiplesCount` (dropped from
    `Corpus/Analysis/UnitFractionFourierAnalysis/CircleMethod.lean`; confirmed 0 references to
    any of its declaration names in that file).
  - `SolveMath.Corpus.NumberTheory.PrimeNumberTheoremConsequences` (dropped from
    `Corpus/NumberTheory/PrimeCountingIccCard.lean`; used by dead code in that file — see
    forced fix below).
  - `SolveMath.Corpus.NumberTheory.ReciprocalSumLiuSawhneySupport.LiuSawhneyAsymptoticScales`
    (dropped from `Edges/Erdos/P300/Solution.lean`, confirmed unused there beyond the import
    line, and from `.../FiniteBernoulliHoeffding.lean`, whose only uses were in dead trailing
    declarations — see forced fix below).

### (b) Removed `#print axioms` commands

Deleted trailing `#print axioms` lines (rule (b)) from:
`Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/SmoothPrimePowerFactorization.lean` (2 lines),
`Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/PrimePowerLCMTelescope.lean` (2 lines),
`Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/FiniteWeightedSubsetFourier.lean` (2 lines),
and `Edges/Erdos/P300/Solution.lean` (`#print axioms Erdos300.erdos_300`, part of the trailing
Erdős-300-bookkeeping tail dropped along with `erdos_300` itself; see decl pruning below).

### (c) Forced minimal fixes (compile errors)

1. **`Corpus/Analysis/RPowIntegralEstimates.lean` restored beyond the given 36-module kept
   list.** `Corpus/Analysis/UnitFractionAnalyticEstimates/PartialSummation.lean` (kept, and on
   the path to `dense_contains_one`) directly calls `integrable_on_pow_inv_Ioi`, a declaration
   defined only in `RPowIntegralEstimates.lean`, and previously reached it transitively through
   `TendstoLogCoeTop.lean`'s `public import` of that module (Lean's module system re-exports
   `public import`s to importers). `RPowIntegralEstimates.lean` itself was not on the
   precomputed kept-module list. It is a small (80-line), self-contained file with only Mathlib
   imports, so it was copied in unmodified and its import restored in
   `TendstoLogCoeTop.lean` (`public import SolveMath.Corpus.Analysis.RPowIntegralEstimates`).
   This same restored import also transitively re-supplies two root-level Mathlib lemmas
   (`integral_inv_of_pos`, `integral_one`, both from `Mathlib.Analysis.SpecialFunctions.
   Integrals.Basic`, one of `RPowIntegralEstimates.lean`'s own two `public import`s) that
   `PartialSummation.lean` also uses and had previously reached the same transitive way.

2. **`Corpus/NumberTheory/PrimeCountingIccCard.lean`: deleted dead code depending on the
   dropped `PrimeNumberTheoremConsequences` import.** The `namespace SolveMath.PrimeCounting …
   end SolveMath.PrimeCounting` block (originally lines 42–113: `prime_counting_interval_
   tendsto_atTop` and `exists_distinct_primes_in_interval`) calls `tendsto_by_squeeze`, defined
   only in `PrimeNumberTheoremConsequences.lean` (not kept). Confirmed by grep that neither
   declaration is referenced anywhere else in the source repository except by each other, i.e.
   this block is dead code from the point of view of `dense_contains_one`. Deleted the whole
   block; kept `primeCounting_eq_card_Icc_filter_prime` (the file's only other declaration,
   lines 1–40, unmodified).

3. **`Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/FiniteBernoulliHoeffding.lean`:
   deleted dead trailing declarations depending on the dropped `LiuSawhneyAsymptoticScales`
   import.** `theorem tendsto_S_atTop` and `theorem eventually_abs_reciprocal_sum_sub_mean_
   tail_le_inv_four_smoothLcm` (originally lines 536–595) both use qualified
   `LiuSawhneyAsymptoticScales.*` names. Confirmed by grep that `Solution.lean` only calls
   `FiniteBernoulliHoeffding.abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm` (an earlier,
   independent declaration) and never `tendsto_S_atTop` or the deleted `eventually_…` theorem,
   and that no other file in the repository references this file's `tendsto_S_atTop`. Deleted
   both declarations (and their doc comments); the file's opening/closing
   `section`/`namespace` structure was otherwise left untouched.

4. **`Corpus/NumberTheory/UnitFractionFinalResults/PrimeCountingSieve.lean`: inlined a small
   lemma from the dropped `UnitFractionAnalyticMisc` import.** Line 739 (original numbering)
   uses `Icc_sdiff_Icc_left` (a `Finset`-namespaced lemma from `UnitFractionAnalyticMisc.lean`,
   not kept). Confirmed by grep this is the only genuine use of any `UnitFractionAnalyticMisc`
   declaration across all of its former importers. Added a private, verbatim restatement,
   `private lemma _root_.Finset.Icc_sdiff_Icc_left …`, directly above the file's main docstring
   (declared with an explicit `_root_.Finset.` prefix, rather than relying on the file's ambient
   `namespace UnitFractions`, so that the existing unqualified call site — resolved via this
   file's `open _root_.Finset` — still finds it under the same name it originally had).

### (d) `Edges/Erdos/P300/Solution.lean` declaration pruning

Applied every `DROP` range from `expert_input/ported/ls_solution_decl_ranges.txt` (30 ranges,
919 lines total, all Erdős-300 extremal bookkeeping: `erdos300Max`/`lowerSet`/`lowerCutoff`
machinery, `major_arc_card_le`/`weighted_major_arc_bound_recip` reciprocal-form duplicates,
`character_sum_eq_zero_of_avoids*`/`weighted_fourier_eq_empty*`/`weighted_circle_core*` recip
duplicates, and the closing `erdos300_of_dense`/`erdos_300` wrapper), deleted from the bottom of
the file upward so line numbers stayed valid. No `KEEP` declaration needed any `DROP`
declaration restored. Also dropped the trailing `#print axioms Erdos300.erdos_300` (see (b)).
The import of `SolveMath.Edges.Erdos.P300.Statement` was kept (it is on the kept-module list and
`rec_sum`/`UnitFractions` are available through it via its own import of
`UnitFractionDensities`); it is not otherwise referenced by name in `Solution.lean`.

## Build environment note

`expert_input/ported/build.sh` currently fails, for reasons unrelated to this port: it appends
this sandbox's `.out` directory to the *end* of `LEAN_PATH` (after
`lake env printenv LEAN_PATH`), and `/home/johan/math_erdos_289/.lake/build/lib/lean` — a LEAN_PATH
entry ahead of `.out` — already contains a `SolveMath/Corpus/NumberTheory/` subtree (with a
disjoint set of module names, e.g. `AbelSummatoryPrimeRestriction.olean`), evidently populated by
a concurrent porting task's `lake build` elsewhere in this shared project. Lean's module-system
import resolver hard-fails on the first `LEAN_PATH` root with a matching package subdirectory
(even when the specific file is absent there) instead of falling through to `.out`, so
`Edges/Erdos/P300/Statement.lean`'s import of `UnitFractionDensities` fails to resolve even
though `UnitFractionDensities.olean` was just built into `.out`. Reproduced directly (outside
`build.sh`) and confirmed the *only* difference needed is `LEAN_PATH` ordering: with `.out`
placed first, the identical `lean -o …` invocation succeeds. Per the task's global rules,
`build.sh` itself was not modified (it is shared with other concurrent porting tasks) and `.lake`
was not touched. All builds reported in this report instead used a local, unpushed driver script
(`/tmp/build_liusawhney.sh`, not part of this port) that is byte-for-byte identical to
`expert_input/ported/build.sh` except for this one `LEAN_PATH` ordering fix. Re-running the
*unmodified* `expert_input/ported/build.sh` should succeed once the concurrent task's `.lake`
state no longer collides with the `SolveMath` package root.
