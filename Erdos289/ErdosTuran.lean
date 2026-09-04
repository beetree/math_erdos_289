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

-- `erdos_turan` is now derived from the audited axiom module; see `ExternalBridge.lean`.

end Erdos289
