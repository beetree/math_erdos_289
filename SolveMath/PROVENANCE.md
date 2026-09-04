# Provenance of the vendored proofs

All modules under `SolveMath/Corpus` and `SolveMath/Edges` were ported from the minimized port
directories `expert_input/ported/{DivisorBound,MertensSecond,LiuSawhney}` (working records now
included under `docs/provenance/`, each with a full `PROVENANCE.md`; a fourth port,
`ErdosTuranFinite`, was prepared but is not vendored and not used). Upstream:
Boris Alexeev's `plby/lean-proofs` (commit `61fce10e`), via the `solve-math` repository
(commit `8f953ab3`); formal authors Codex / GPT-5.6 Sol; no LICENSE file found upstream.

The three entry points are the bridge files `SolveMath/Ported/{DivisorBound,MertensSecond,LiuSawhney}.lean`,
each of which states the working theorem (`Erdos289.Ported.<name>`) and the audited-form theorem
(`Erdos289.Ported.<name>_audited`). The files are ported from the identified snapshot with the
documented changes below; they are not byte-identical copies.

## Deviations from the reference copies

- `SolveMath/Edges/Erdos/P300/Solution.lean`: four calls of `ring` that only succeeded by
  falling back to `ring_nf` (emitting a "Try this" info on every build) were replaced by
  `ring_nf` (2026-09-04).
- `SolveMath/Corpus/Analysis/UnitFractionAnalyticEstimates/DivisorBound₁.lean` was renamed to
  `DivisorBound1.lean` (module `…UnitFractionAnalyticEstimates.DivisorBound1`), and its five
  importers and two comments updated accordingly (2026-09-04), because the non-ASCII filename was
  mangled by ZIP exports that do not set the UTF-8 filename flag. The file contents are unchanged.
- No other change to any ported file.
