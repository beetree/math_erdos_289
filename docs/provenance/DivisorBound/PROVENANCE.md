# Provenance: DivisorBound port

## Source

- Repo: `/home/johan/solve-math-workers/worker-1/solve-math`
- Branch: `worker-1/plby-import-wave2`
- Commit: `8f953ab3ec714753b2566d51f6dee9f12f4b0b0e`
- File: `SolveMath/Corpus/NumberTheory/DivisorCountSubpolynomialGrowth.lean` (342 lines)

These files were ported into `solve-math` from Boris Alexeev's `plby/lean-proofs`
(pinned commit `61fce10ef6671b1df0325f22bc76c8cd1f2fa554`), with formal authors
Codex / GPT-5.6 Sol.

**LICENSE STATUS**: no LICENSE file found upstream (checked the `solve-math` repo
root and the immediate module directory tree). The copied source file itself
carries no license or copyright header to copy forward.

## Ported modules

| Module | Path (relative to `DivisorBound/`) | Lines |
|---|---|---|
| `SolveMath.Corpus.NumberTheory.DivisorCountSubpolynomialGrowth` | `SolveMath/Corpus/NumberTheory/DivisorCountSubpolynomialGrowth.lean` | 342 |

Only Mathlib is imported by this module (`public import` of five `Mathlib.*`
modules); it has no dependency on any other `SolveMath` module, so no imports
needed to be removed or redirected.

## Edits made to the copied file

None. The file was copied verbatim:

- No `import`/`public import` of a `SolveMath` module was present to remove.
- No `#print axioms` / `#check` / `#eval` / `#guard` command lines were present
  to remove.
- No compile error occurred, so no forced fixes were needed.

The file compiled clean on the first `build.sh` pass.

## Main theorem

`DivisorCountSubpolynomialGrowth.eventually_divisorCount_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε`

## Bridge theorems (`Erdos289Bridge.lean`, namespace `Erdos289.Ported`)

- `divisor_bound (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in Filter.atTop, (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε`
  — proved by direct application of the ported main theorem (statements are
  syntactically identical).
- `divisor_bound_audited : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ((Nat.divisors n).card : ℝ) ≤ (n : ℝ) ^ ε`
  — proved from `divisor_bound` by unfolding `Filter.eventually_atTop` and
  bumping the witness threshold to `max n₀ 1` to satisfy the `1 ≤ n₀` side
  condition (the audited `DivisorBoundStatement` in `Erdos289/ExternalAxioms.lean`
  with `divisorCount n := (Nat.divisors n).card` unfolded).

## Build result

`expert_input/ported/build.sh expert_input/ported/DivisorBound` exits 0.
`#print axioms` on the ported main theorem and both bridge theorems reports
exactly `[propext, Classical.choice, Quot.sound]` in all three cases.
