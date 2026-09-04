# Provenance: Conlon–Fox–Pham Theorem 1.5 (the "CFHMPSV" input)

## Source

- Repository: Boris Alexeev, `plby/lean-proofs` (https://github.com/plby/lean-proofs),
  directory `src/latest/`, Lean `v4.33.0`, Mathlib `v4.33.0`.
- Local clone used: `/home/johan/solve-math-workers/worker-1/plby-src`, commit `61fce10ef6671b1df0325f22bc76c8cd1f2fa554`
  (2026-08-31). (Upstream had a later commit, `87b073cb` of 2026-09-02, at the time of porting; the
  terminal theorem is present and unconditional in both.)
- Development: `ErdosProblems/Erdos186/` (the formalization of Erdős Problem 186 by Bosznay /
  Pham–Zakharov), of which the Conlon–Fox–Pham structure theorem is a component. Formal author
  credited in the file headers: Codex. Two Kneser-theorem files come from
  `ErdosProblems/Erdos13/` (authors: Mantas Bakšys, Yaël Dillies, ported from Mathlib work).
- License: every ported file carries the header "Released under Apache 2.0 license as described in
  the file LICENSE", and `src/latest/LICENSE` in the source tree states that such files are
  licensed under the Apache License, Version 2.0. This is better provenance than the solve-math
  ports (which had no license file).

## Main theorem

```lean
theorem Erdos186.CFP.nonemptyIntegerTheorem15 : Erdos186.CFP.NonemptyIntegerTheorem15
```
in `ErdosProblems/Erdos186/CFP/IntegerHigherDimensionalFinal.lean`; the proposition is defined in
`ErdosProblems/Erdos186/CFP/Main.lean` and the witness type in `ErdosProblems/Erdos186/CFP/Witness.lean`
(over `Erdos186.StructureTheorem.CFPWitness`), with the GAP encoding in `ErdosProblems/Erdos186/GAP.lean`.

## Verification of the original (before porting)

The 258-file import closure of the terminal theorem was compiled unchanged on its own toolchain
(Lean v4.33.0, Mathlib v4.33.0) in a throwaway project on 2026-09-04. `lake build` succeeded
(8963 jobs) and the file's own `#print axioms` reported

```
'Erdos186.CFP.nonemptyIntegerTheorem15' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A proof-term walk in that environment (`Lean.ConstantInfo.getUsedConstantsAsSet`, transitive)
found 69,117 constants and no axiom other than those three.

## What was ported

All 258 modules of the import closure, verbatim, preserving module paths (`ErdosProblems/...`):
90,434 lines after the edits below (91,108 before). Not one module was dropped; see
`PRUNING_NOTES.md` for the proof-term data showing that 22 of them are unused and why pruning
was not applied.

## Edits made to the copied files

1. Every `#print axioms`, `#check`, `#eval`, `#guard` command line was removed (480 lines,
   plus their continuation lines). No declaration was touched.
2. One proof fix for the Mathlib v4.33 → v4.34.0-rc2 drift, in
   `ErdosProblems/Erdos186/CFP/Bilu/Proposition75Case2Construction.lean` line 804:
   `f.normDet_ne_zero_tfae.out 0 4` → `f.normDet_ne_zero_tfae.out 1 5`
   (`List.TFAE.out` became 1-indexed). See `PORT_LOG_cfp_w1a.md`.

That is the complete diff: `diff -r` against the source shows only the removed command lines
and this one line.

## Bridge and axiom check

- `Erdos289Bridge.lean` (plain file, namespace `Erdos289.Ported`) proves
  `cfhmpsv_structure_audited : Erdos289.External.CFHMPSVStructureStatement`, the audited
  proposition from `Erdos289/ExternalAxioms.lean`, from `nonemptyIntegerTheorem15`. The
  translation: `c := min (scaleNum/scaleDen) (1/(lossConstant+1))`, `d₀ := D`, `m₀ := 2`;
  the centered GAP (radii `r`) becomes a `GAPRepresentation` with `lower = -r`, `upper = r`;
  the real dilate at scale `c·s` sits inside the integer `k`-dilate because `c·s ≤ k`; the
  `+1` in the loss is absorbed since `s·log₂ m ≥ 1`.
- `Axioms.lean` prints the axioms of the ported theorem and of the bridge theorem.

## Building

`expert_input/ported/build.sh -j 8 expert_input/ported/CFP` (from the project root).

## Deviations in this repository's copy (added on integration, 2026-09-04)

- At 13 sites (listed by `git log -p` of this file's integration commit), the deprecated tactic
  `push_neg` was replaced by its documented replacement `push Not`, to keep the project's build
  warning-free. No other change to any ported file. Linters that would otherwise fire on the
  verbatim code are disabled for this library in `lakefile.toml`.
- In `ErdosProblems/Erdos186/CFP/RandomPartition.lean` and `ErdosProblems/Erdos186/CFP/RandomPartitionSharp.lean`,
  merged consecutive `intro` lines into explicit `intro B hBpart hlarge hzeroB d hd hdRank P hsteps hvolume hcontained`
  to eliminate "Try this" suggestions.
- In `ErdosProblems/Erdos186/CFP/Bilu/Section6DistortingHalfCell.lean` (three sites) and
  `ErdosProblems/Erdos186/CFP/NoCarryEmbedding.lean` (one site), `ring` calls that only succeeded by
  falling back to `ring_nf` (emitting a "Try this" info on every build) were replaced by `ring_nf`.
