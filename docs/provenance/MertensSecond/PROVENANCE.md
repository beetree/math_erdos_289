# Provenance: MertensSecond port

## Source

- Repo: `/home/johan/solve-math-workers/worker-1/solve-math`
- Branch: `worker-1/plby-import-wave2`
- Commit: `8f953ab3ec714753b2566d51f6dee9f12f4b0b0e`
- Source root: `SolveMath/Corpus/NumberTheory/`

These files were ported into `solve-math` from Boris Alexeev's `plby/lean-proofs`
(pinned commit `61fce10ef6671b1df0325f22bc76c8cd1f2fa554`), with formal authors
Codex / GPT-5.6 Sol.

**LICENSE STATUS**: no LICENSE file found upstream (checked the `solve-math` repo
root and the immediate module directory tree). None of the four copied source
files carries a license or copyright header to copy forward.

## Ported modules

| Module | Path (relative to `MertensSecond/`) | Lines |
|---|---|---|
| `SolveMath.Corpus.NumberTheory.AbelSummatoryPrimeRestriction` | `SolveMath/Corpus/NumberTheory/AbelSummatoryPrimeRestriction.lean` | 492 |
| `SolveMath.Corpus.NumberTheory.ChebyshevPsiLogHarmonicBound` | `SolveMath/Corpus/NumberTheory/ChebyshevPsiLogHarmonicBound.lean` | 609 |
| `SolveMath.Corpus.NumberTheory.MeisselMertensConstantAsymptotic` | `SolveMath/Corpus/NumberTheory/MeisselMertensConstantAsymptotic.lean` | 450 |

Total: 1,551 lines. (A fifth module in the original dependency walk, `PrimeReciprocalMertensDeviation`, a 40-line wrapper unused by the bridge, was removed after the first build.)

## Edits made to the copied files

None. All three files were copied verbatim from the source repository:

- Every `SolveMath` module imported by these four files
  (`ChebyshevPsiLogHarmonicBound` imports `AbelSummatoryPrimeRestriction`;
  `MeisselMertensConstantAsymptotic` imports `AbelSummatoryPrimeRestriction` and
  `ChebyshevPsiLogHarmonicBound`) is itself in the kept-module list, so no
  `import`/`public import` of a `SolveMath` module needed to be removed or
  redirected, and no umbrella re-export needed replacing. All other imports in
  the four files are direct `public import`s of `Mathlib.*` modules, left as-is.
- No `#print axioms` / `#check` / `#eval` / `#guard` command lines were present
  in any of the four files.
- No compile error occurred on the first `build.sh` pass (one harmless
  `if_pos`-deprecation warning in `ChebyshevPsiLogHarmonicBound.lean:464`, not
  an error), so no forced fixes were needed.

## Main theorem

`MeisselMertensConstantAsymptotic.prime_reciprocal`:
```
Asymptotics.IsBigO Filter.atTop
  (fun x => AbelSummatoryPrimeRestriction.prime_summatory (fun p => (↑p)⁻¹) 1 x
    - (Real.log (Real.log x) + MeisselMertensConstantAsymptotic.meissel_mertens))
  (fun x => (Real.log x)⁻¹)
```
i.e. `∑_{p≤x} 1/p − log log x → meissel_mertens` at rate `O(1/log x)`.

## Bridge theorems (`Erdos289Bridge.lean`, namespace `Erdos289.Ported`)

- `mertens_second_audited : ∃ B₁ : ℝ, Filter.Tendsto (fun x : ℝ => (∑ p ∈ ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime), (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x)) Filter.atTop (nhds B₁)`
  — proved by taking `B₁ := meissel_mertens`, converting `prime_reciprocal`'s
  `IsBigO ... (fun x => (log x)⁻¹)` bound to a `Tendsto ... (nhds 0)` fact via
  `Asymptotics.IsBigO.trans_tendsto` (using `tendsto_inv_atTop_zero.comp
  Real.tendsto_log_atTop` for `(log x)⁻¹ → 0`), adding the constant
  `meissel_mertens` back via `Filter.Tendsto.add`/`tendsto_const_nhds`, and
  rewriting `AbelSummatoryPrimeRestriction.prime_summatory (fun p => (p:ℝ)⁻¹) 1 x`
  into the target's `(Finset.range (⌊x⌋₊+1)).filter Nat.Prime` sum with a local
  helper lemma `primeSummatory_eq` (`Finset.Icc 1 ⌊x⌋₊ .filter Nat.Prime =
  Finset.range (⌊x⌋₊+1) .filter Nat.Prime` since every prime is `≥ 1`, plus
  `1/p = p⁻¹`). This is exactly the audited `Erdos289.External.MertensSecondStatement`
  from `Erdos289/ExternalAxioms.lean` with `primeReciprocalSum` unfolded.
- `mertens_second : ∃ B₁ : ℝ, Filter.Tendsto (fun x : ℕ => (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p) - Real.log (Real.log x)) Filter.atTop (nhds B₁)`
  — proved from `mertens_second_audited` by composing with
  `tendsto_natCast_atTop_atTop : Filter.Tendsto (Nat.cast : ℕ → ℝ) Filter.atTop Filter.atTop`
  and `Nat.floor_natCast` to eliminate the floor. This is exactly our project's
  working axiom `Erdos289.mertens_second` in `Erdos289/External.lean` (mirroring
  the derivation already used for `Erdos289.bridge_mertens_second` in
  `Erdos289/ExternalBridge.lean`, which currently derives the same statement
  from the *unaudited* `Erdos289.External.Assumed.mertens_second` axiom instead
  of from a real proof).

## Build result

`expert_input/ported/build.sh expert_input/ported/MertensSecond` exits 0 on the
first pass. `#print axioms` on the ported main theorem and both bridge theorems
reports exactly `[propext, Classical.choice, Quot.sound]` in all three cases:

```
'MeisselMertensConstantAsymptotic.prime_reciprocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos289.Ported.mertens_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos289.Ported.mertens_second_audited' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Fidelity note

`mertens_second_audited` is character-for-character the statement given in the
task, and unfolding `Erdos289.External.primeReciprocalSum x := ∑ p ∈
((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime), (1 : ℝ) / (p : ℝ)` into
`Erdos289.External.MertensSecondStatement` reproduces it exactly, so this bridge
theorem is definitionally the audited statement (`Erdos289.ExternalAxioms.lean`
was not modified; the unfolding was checked by inspection, not by importing that
read-only file). `mertens_second` matches `Erdos289.mertens_second`'s statement
(`Erdos289/External.lean`) verbatim as well.
