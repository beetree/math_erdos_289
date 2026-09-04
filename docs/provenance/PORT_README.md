# Ported proofs of four of the six literature inputs

Each subdirectory is a self-contained Lean development, on the project's pinned toolchain
(Lean `v4.34.0-rc2`, Mathlib `v4.34.0-rc2`), that proves one of the literature results which
`Erdos289/External.lean` and the audited `Erdos289/ExternalAxioms.lean` currently assume as
axioms. Every main theorem and every bridge theorem reports exactly
`[propext, Classical.choice, Quot.sound]`.

| Directory | Result | Files / lines | Main ported theorem | Bridge theorems (`Erdos289.Ported.*`) |
|---|---|---|---|---|
| `DivisorBound/` | τ(n) ≤ n^ε eventually (Hardy–Wright Thm 315) | 1 / 342 | `DivisorCountSubpolynomialGrowth.eventually_divisorCount_le_rpow` | `divisor_bound`, `divisor_bound_audited` |
| `MertensSecond/` | ∑_{p≤x} 1/p − log log x → B₁ (Mertens, convergent form; proved with error O(1/log x)) | 3 / 1,551 | `MeisselMertensConstantAsymptotic.prime_reciprocal` | `mertens_second`, `mertens_second_audited` |
| `LiuSawhney/` | density > 1 − 1/e + ζ forces a subset with reciprocal sum 1 (Liu–Sawhney, arXiv:2404.07113, Thm 1.3) | 37 / 28,789 | `Erdos300.dense_contains_one` | `liu_sawhney`, `liu_sawhney_audited` |
| `CFP/` | Conlon–Fox–Pham Thm 1.5 (= CFHMPSV Thm 3): bounded-rank GAP structure of dense sets with a sparse subset-sum-covering reserve | 258 / 90,434 | `Erdos186.CFP.nonemptyIntegerTheorem15` | `cfhmpsv_structure_audited` |

In each directory:

- `SolveMath/…` are the ported source files, keeping their original module paths.
- `Erdos289Bridge.lean` proves, character for character, the statement of our working axiom
  (`Erdos289.<name>` in `Erdos289/External.lean`) and the audited proposition
  (`Erdos289.External.<Name>Statement` in `Erdos289/ExternalAxioms.lean`, with its helper
  definitions unfolded), so that later `exact Erdos289.Ported.<name>_audited` closes the
  audited proposition by definitional unfolding.
- `Axioms.lean` prints the axiom reports.
- `PROVENANCE.md` records the source commit, upstream authorship, license status, and every
  edit made to the copied files.

## Provenance and license

The first three come from `/home/johan/solve-math-workers/worker-1/solve-math` (branch
`worker-1/plby-import-wave2`), which in turn ported them from Boris Alexeev's
`plby/lean-proofs` (pinned commit `61fce10ef6671b1df0325f22bc76c8cd1f2fa554`, formal authors
credited upstream as Codex / GPT-5.6 Sol); those files carry no license header and the
solve-math notes record "no license found". The CFP port comes directly from the local clone of
`plby/lean-proofs` at the same commit; its files carry Apache-2.0 headers and the source tree has
a LICENSE file naming Apache-2.0 for them. See each `PROVENANCE.md`.

## How the ports were minimized

The set of modules to copy was computed by walking the proof term of each main theorem
(`Lean.ConstantInfo.getUsedConstantsAsSet`, transitively) and collecting the modules that
declare any constant used, rather than by taking the import closure. For Liu–Sawhney this
kept 36 of the 64 modules in the import closure (one further 80-line file was restored when a
kept file turned out to call it directly), and the same walk over the main file identified 30
declarations (919 lines) of Erdős-300 extremal bookkeeping to delete. Imports of dropped
modules were replaced by direct imports of kept modules; stray `#print axioms` commands were
removed; proofs were not otherwise altered. The exact edits are listed per directory.

## Building

```sh
expert_input/ported/build.sh expert_input/ported/<Dir>
```

compiles every `.lean` file under `<Dir>` in import order against the project's Mathlib into
`<Dir>/.out` (never touching `.lake`), then elaborates `<Dir>/Axioms.lean`. The port's own
output directory is placed first on `LEAN_PATH`.

## Using them in the project

The ported files use Lean's module system (`module` / `public import`) and live outside the
`Erdos289` library, so they are not yet part of `lake build`. To discharge an axiom, either add
a second `lean_lib` for `SolveMath` in `lakefile.toml` pointing at one of these trees (all
three trees are disjoint as module sets, so they can be merged into one `SolveMath/`
directory), or vendor the files under `Erdos289/`. Then replace the `axiom` in
`Erdos289/External.lean` by `theorem … := Erdos289.Ported.<name>` and rebuild the bridge in
`Erdos289/ExternalBridge.lean` against the audited statement.

Not covered here: Bourgain–Garaev (no formalization found anywhere) and Erdős–Turán (a finite form exists in the same repository,
`QuantitativeErdosTuran.erdosTuran_fract_count`, but with an N/√H rather than N/H error term,
so it does not prove the axiom as stated; it would instead replace its use in Lemma 1).
