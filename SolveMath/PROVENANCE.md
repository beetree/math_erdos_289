# Provenance of the vendored proofs

All modules under `SolveMath/Corpus` and `SolveMath/Edges` were copied from the minimized port
directories `expert_input/ported/{DivisorBound,MertensSecond,LiuSawhney,ErdosTuranFinite}`
(reference copies kept outside the repository, each with a full `PROVENANCE.md`). Upstream:
Boris Alexeev's `plby/lean-proofs` (commit `61fce10e`), via the `solve-math` repository
(commit `8f953ab3`); formal authors Codex / GPT-5.6 Sol; no LICENSE file found upstream.

The four entry points are the bridge files `SolveMath/Ported/*.lean`.

## Deviations from the reference copies

- `SolveMath/Edges/Erdos/P300/Solution.lean`: four calls of `ring` that only succeeded by
  falling back to `ring_nf` (emitting a "Try this" info on every build) were replaced by
  `ring_nf` (2026-09-04). No other change.
