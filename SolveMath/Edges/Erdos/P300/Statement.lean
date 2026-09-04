/- leanprover/lean4:v4.34.0-rc2  mathlib v4.34.0-rc2 -/
/-
Canonical frozen statement for Erdős Problem 300.
https://www.erdosproblems.com/300

The official problem: let A(N) denote the maximal cardinality of
A ⊆ {1, ..., N} such that ∑_{n ∈ S} 1/n ≠ 1 for all S ⊆ A. Estimate A(N).

The source proves the sharp asymptotic A(N) = (1 - 1/e + o(1)) N,
due to Liu and Sawhney (arXiv:2404.07113, Theorem 1.3).

Source: plby/lean-proofs, src/latest/ErdosProblems/Erdos300.lean, at pinned commit
61fce10ef6671b1df0325f22bc76c8cd1f2fa554.

Formal proof credited upstream to Codex / GPT-5.6 Sol.
LICENSE STATUS: NO LICENSE FOUND.

Local changes: the statement has been split out here; Solution.lean certifies
it from the corpus proof. No statement change.
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import SolveMath.Corpus.NumberTheory.UnitFractionDensities

@[expose] public section

namespace Erdos300

open Filter Topology Real UnitFractions

/-- A finite set of denominators is admissible for Erdős Problem 300 when none
of its subsets has reciprocal sum exactly one. -/
def AvoidsOne (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → rec_sum B ≠ 1

/-- The finite family over which the extremal function is maximized. -/
noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter AvoidsOne

/-- `erdos300Max N` is the exact maximum cardinality in Erdős Problem 300. -/
noncomputable def erdos300Max (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

/-- Erdős Problem 300: the largest subset of `{1, ..., N}` having no
unit-sum reciprocal subcollection has asymptotic density `1 - 1 / e`. -/
def erdos_300_statement : Prop :=
  Tendsto (fun N : ℕ => (erdos300Max N : ℝ) / (N : ℝ)) atTop (𝓝 (1 - 1 / Real.exp 1))

end Erdos300
