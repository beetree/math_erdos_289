# Pruning data (not applied)

The port keeps every module of the full 258-module import closure of
`Erdos186.CFP.nonemptyIntegerTheorem15`, with the edits documented in `PROVENANCE.md`. A proof-term walk (run on the original v4.33 build, `ClosureConsts.lean`) shows that
only 236 of the modules and roughly 64,000 of the 91,000 lines are used by the proof:

- `docs/provenance/CFP/kept_modules.txt` / `dropped_modules.txt`: the 236 used / 22 unused modules. The unused
  ones are the higher-dimensional corollary chain (`HigherDimensionalCorollary*`,
  `ProjectedProperization{Existence,Theorem}`, the `CenteredScaled*Certificate` variants,
  `AppendixEncoding`, `Bilu.Section5Theorem56`, `Bilu.Section7AffineSliceUnconditional`,
  `Bilu.Section9{1,3}*Presentation`, `RandomGreedyDenseInputs`, `ScaleDyadicPreprocessingWindow`,
  `ScaledCertificateNumerics`, `Corollary217ScaledMapBack`).
- `docs/provenance/CFP/closure_decl_ranges.txt`: for every declaration in every module, `KEEP`/`DROP` (used /
  unused by the proof) with its 1-based, docstring-inclusive line range in the verbatim file.

Module-level pruning was attempted and abandoned: 18 kept files reference the dropped modules
from their own unused declarations, and deleting those declarations cascades. Declaration-level
pruning by the recorded ranges was also attempted and abandoned: the ranges do not account for
`@[to_additive]` twins, notation/macro lines, attribute commands, or rfl-lemmas that `simp`/`dsimp`
use without a trace in the proof term, so a mechanical deletion broke dozens of files. A future
prune should be done by hand, file by file, against this data, with a full rebuild after each file.
