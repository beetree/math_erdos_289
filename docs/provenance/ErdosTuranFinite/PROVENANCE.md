# Provenance: ErdosTuranFinite port

## Source

- Repo: `/home/johan/solve-math-workers/worker-1/solve-math`
- Branch: `worker-1/plby-import-wave2`
- Commit: `8f953ab3ec714753b2566d51f6dee9f12f4b0b0e`
- File: `SolveMath/Corpus/NumberTheory/QuantitativeErdosTuran.lean` (990 lines)

These files were ported into `solve-math` from Boris Alexeev's `plby/lean-proofs`
(pinned commit `61fce10ef6671b1df0325f22bc76c8cd1f2fa554`), with formal authors
Codex / GPT-5.6 Sol.

**LICENSE STATUS**: no LICENSE file found upstream (checked the `solve-math` repo
root and the immediate module directory tree). The copied source file itself
carries no license or copyright header to copy forward.

## Ported modules

| Module | Path (relative to `ErdosTuranFinite/`) | Lines |
|---|---|---|
| `SolveMath.Corpus.NumberTheory.QuantitativeErdosTuran` | `SolveMath/Corpus/NumberTheory/QuantitativeErdosTuran.lean` | 990 |

Only Mathlib is imported by this module (`public import` of seven `Mathlib.*`
modules: `Mathlib.NumberTheory.ZetaValues`, `Mathlib.Analysis.Fourier.AddCircle`,
`Mathlib.Analysis.PSeries`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds`,
`Mathlib.Analysis.SpecialFunctions.Complex.Circle`,
`Mathlib.Topology.Algebra.InfiniteSum.NatInt`, `Mathlib.Analysis.Real.Pi.Bounds`); it
has no dependency on any other `SolveMath` module, so no imports needed to be removed
or redirected.

## Edits made to the copied file

None. The file was copied verbatim:

- No `import`/`public import` of a `SolveMath` module was present to remove.
- No `#print axioms` / `#check` / `#eval` / `#guard` command lines were present to
  remove.
- No compile error occurred, so no forced fixes were needed.

The file compiled clean (only pre-existing `if_pos`/`if_neg` deprecation warnings,
not errors) on the first `build.sh` pass.

## Main theorem

```
QuantitativeErdosTuran.erdosTuran_fract_count {ι : Type*} (s : Finset ι) (phase : ι → ℝ)
    (H : ℕ) (δ b : ℝ) (hH : 1 ≤ H) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |((s.filter fun i => Int.fract (phase i) < b).card : ℝ) - b * s.card| ≤
      (δ + 4 / (δ * H)) * s.card +
        ∑ h ∈ nonzeroFrequencyWindow H, 8 / |(h : ℝ)| * ‖exponentialSum s phase h‖
```

with `exponentialSum s phase h = ∑ i ∈ s, fourier h (phase i : UnitAddCircle)` and
`nonzeroFrequencyWindow H = Finset.Icc (-(H:ℤ)) H \ {0}`.

## Bridge theorem (`Erdos289Bridge.lean`, namespace `Erdos289.Ported`)

`erdos_turan_weak : ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ), 0 < U → ∀ (N : ℕ) (x : Fin N → ZMod U)
(H : ℕ), 0 < H → ∀ α ℓ : ℕ, α + ℓ ≤ U → |...| ≤ C * (N/√H + ∑ h ∈ Finset.Icc 1 H, (1/h) *
‖∑ j, Complex.exp (2πi h val_j / U)‖)` — stated character-for-character as
`Erdos289.erdos_turan_weak` from `Erdos289/ExternalBridge.lean` with `Erdos289.e`
unfolded (`e (m : ℕ) (x : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x / m)`), so
in the project `theorem erdos_turan_weak := by simpa [e] using Ported.erdos_turan_weak`
closes directly. `C := 32` is used as the witness constant.

### Translation plan actually used

- `s := (Finset.univ : Finset (Fin N))`, `phase j := ((x j).val : ℝ) / U` (lies in
  `[0, 1)` since `0 < U`, so `Int.fract (phase j) = phase j`).
- `A k := s.filter (fun j => (x j).val < k)` for `k ≤ U`; `hcount` identifies
  `s.filter (fun j => Int.fract (phase j) < k/U)` with `A k` via
  `div_lt_div_iff_of_pos_right`.
- The ported theorem is applied twice, at `b₁ = (α+ℓ)/U` and `b₂ = α/U`
  (`hmain (α+ℓ) hαℓ` and `hmain α hle2`), with `δ := 1/√H` (`0 < δ ≤ 1` since `H ≥ 1`).
  Inclusion–exclusion (`hset`, `hcarddiff`, via `Finset.card_sdiff` and
  `Finset.inter_eq_left`) turns the residue-interval count into
  `A(α+ℓ).card − A(α).card`, matching `#{val ∈ [α, α+ℓ)}`; `hbdiff` matches
  `Nℓ/U` to `b₁N − b₂N` (kept as a single cast `((α+ℓ:ℕ):ℝ)` throughout so that it is
  the *same* atom as the one produced by `hmain (α + ℓ) hαℓ` — otherwise `linarith`
  cannot see the two forms as equal, which was the dominant source of iteration in this
  port).
- Signed frequencies: `nonzeroFrequencyWindow H` is split as `negPart ∪ posPart` with
  `negPart = Icc (-H) (-1)`, `posPart = Icc 1 H` (`hunion`, `hdisj`, proved by `omega`
  after unfolding `Finset.mem_Icc`/`mem_erase`). Each half is reindexed against
  `Finset.Icc (1:ℕ) H` via `Finset.sum_nbij'` (`hpossum` using `n ↦ (n:ℤ)`; `hnegsum`
  using `n ↦ -(n:ℤ)`), and `‖exponentialSum s phase (-h)‖ = ‖exponentialSum s phase h‖`
  (via `fourier_neg` + `Complex.norm_conj`, `hconj`/`hnormeq`) folds the two halves into
  `16 * ∑_{n=1}^H (1/n) ‖exponentialSum s phase n‖` (`hwindow`).
- Character match (`hchar`): `exponentialSum s phase (n:ℤ) = ∑ j, Complex.exp(2πi n
  val_j / U)` via `fourier_coe_apply` (`UnitAddCircle` has period `T = 1`, so the `/T`
  vanishes and only the `/U` baked into `phase` survives), giving `hwindow'` with the
  literal target sum.
- Coefficient bound: `δ + 4/(δH) = 5/√H` (`hEq`, via `Real.mul_self_sqrt`), so
  `2 * ((δ + 4/(δH)) * N) = 10 * (N/√H) ≤ 32 * (N/√H)`; combined with the (exact)
  `2 * (16 * Σ) = 32 * Σ` from the window-sum step, `C := 32` covers both applications
  of `hmain` with room to spare.
- `Q := N/√H` and `Tsum := ∑ h ∈ Finset.Icc 1 H, (1/h) ‖...‖` are `set` late (after `h1`,
  `h2` are already in context), so that `set`'s simultaneous rewrite of the goal *and*
  existing hypotheses forces every occurrence into the same named local constant before
  the closing `linarith` calls — `nlinarith`/`linarith` treat non-linear subterms
  (divisions, sums, `Nat.cast` of a sum vs. a sum of `Nat.cast`s) as opaque atoms
  matched purely syntactically, so any of these being spelled two different (but
  provably equal) ways was enough to make the final linear-arithmetic step fail; this
  was the main source of back-and-forth in the proof.

## Build result

`expert_input/ported/build.sh expert_input/ported/ErdosTuranFinite` exits 0 (verified
both incrementally and after a full `rm -rf .out` clean rebuild). `#print axioms` on
the ported main theorem and the bridge theorem reports exactly
`[propext, Classical.choice, Quot.sound]` in both cases.
