# Erdős 289 Lean formalization: initial checkpoint

**Started, but not compiled and not a formal proof of the conjecture.**

The project contains 652 lines of Lean source with 50 named elementary theorem
drafts, the exact nonadjacent target, and explicit definitions of three unproved
analytic obligations. No project proof uses `sorry`, `admit`, or a custom `axiom`.
All proof scripts still need their first Lean compiler run.

## Implemented source drafts

- Exact ordered interval statement: positive denominators, lengths 2 or 3,
  `b_i + 1 < a_j`, total rational reciprocal mass 1, and bound `20*k`.
- Separation, disjointness, distinct interval indices, and pair-to-triple mass.
- The common-denominator cancellation identity and cancellation of the full q.
- Prime-power smoothness and its inheritance by divisors.
- Finite exact-size padding, scheduled counts, reciprocal budget arithmetic,
  and the final count `(k-R-C)+R+C = k` with `R+C ≤ k` explicit.

The full existence theorem is only a proposition definition. The source does
not assume it or claim to have established it.

## Verification performed

The source/configuration checks passed. Independent source review found a
finite-sum grouping problem in the first cancellation draft; parentheses were
added to make the numerator exactly `u*V - sum A - q*sum B`.

Lean elaboration and axiom-dependency verification **did not run**. Lean/Lake
is absent from this environment, and GitHub compiler/mathlib downloads were
blocked with HTTP 403. The attached `build-report.json` records
`blocked_missing_toolchain`, `kernel_build: not_run`, and `target_proved: false`.

## Reproduce and continue

The ZIP contains a project pinned to Lean 4.19.0 and mathlib v4.19.0, a build
verifier, a GitHub Actions workflow, the current manuscript, and a dependency
roadmap. The workflow has not been executed and no repository was published.

After extracting the ZIP on a machine with Lean/Elan installed, run from the
`erdos289_lean` directory:

```sh
git init
python3 scripts/verify.py
```

The verifier resolves dependencies, fetches the mathlib cache, builds the
project, then prints and checks axiom dependencies for every theorem. The
first build may expose elaboration/API issues; source-only review cannot
exclude those. Commit the generated `lake-manifest.json` once resolved.

The next mathematical milestones are the `ZMod` residue-to-divisibility bridge,
LCM control of denominator prime powers, and the finite descending schedule.
The powersmooth reservoirs, analytic inputs, and asymptotic final assembly
remain unformalized. See `docs/formalization_plan.md` for the full dependency map.
