import Erdos289.Defs
import Erdos289.External

/-!
# The Erdős–Turán discrepancy inequality

A classical tool (not present in Mathlib) converting bounds on exponential sums into bounds
on the discrepancy of a finite sequence of residues from the uniform distribution modulo `U`.
See the remark at the end of Section 1 of `erdos_289_full_proof.pdf` ("The Erdős–Turán
discrepancy inequality converts the first theorem into equidistribution in intervals"), and
Montgomery, *Ten Lectures on the Interface Between Analytic Number Theory and Harmonic
Analysis*, Chapter 1, Corollary 1.1 (discrete form).

This file states, as a single unproved external input, the finite/discrete form of the
inequality that is used in `Erdos289/Lemma1.lean` to convert the short Kloosterman sum bound
`bourgain_garaev` into equidistribution of modular inverses in residue intervals.
-/

namespace Erdos289

open Filter Finset

/-- **Erdős–Turán discrepancy inequality**, discrete finite form modulo `U`.

Let `x : Fin N → ZMod U` be a finite sequence of residues modulo `U`. For every `H ≥ 1` and
every "genuine" (non-wrapping) residue interval `[α, α + ℓ)` with `α + ℓ ≤ U`, the number of
indices `j` with `x j` in that interval deviates from the expected count `N * ℓ / U` by at most

`C * (N / H + ∑_{h=1}^{H} (1/h) * |∑_j e_U(h * (x j).val)|)`

for an absolute constant `C` (Montgomery, *Ten Lectures*, Ch. 1, Cor. 1.1). This is the form of
the inequality applied, with `x j` the modular inverses `t⁻¹ mod U`, to derive the equidistribution
statement `Erdos289.equidist_inverse`.

This is an unproved external input: it is taken as a black box from the published literature. -/
theorem erdos_turan :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ), 0 < U → ∀ (N : ℕ) (x : Fin N → ZMod U) (H : ℕ), 0 < H →
      ∀ α ℓ : ℕ, α + ℓ ≤ U →
        |((univ.filter (fun j => (x j).val ∈ Finset.Ico α (α + ℓ))).card : ℝ)
              - (N : ℝ) * (ℓ : ℝ) / (U : ℝ)|
          ≤ C * ((N : ℝ) / (H : ℝ)
              + ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
                  ‖∑ j, e U (h * ((x j).val : ℤ))‖) := by
  sorry

end Erdos289
