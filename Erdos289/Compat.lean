import Erdos289.Main

/-!
# Compatibility with a `∀ᶠ k, ∃ I : Fin k → ℕ × ℕ` formulation of Erdős Problem 289

This file bridges the audited `CandidateStatement` from `Erdos289/Intervals.lean` to a
*corrected nonadjacent* formulation of Erdős Problem 289 in the `Fin k → ℕ × ℕ` style of
google-deepmind/formal-conjectures, and discharges it from `Erdos289.candidateStatement`.

The formulation below is **not** the Formal Conjectures statement itself. At the cited commit,
`FormalConjectures/ErdosProblems/289.lean` requires only `(I i).2 < (I j).1 ∨ (I j).2 < (I i).1`
for distinct indices, which permits adjacent intervals such as `[4,5]` and `[6,7]`, and it does
not require positive left endpoints (so `[0,1]` would contribute `1` via `(0:ℚ)⁻¹ = 0`). The
statement here strengthens both points, following the corrected version in the `solve-math`
corpus: a gap of at least one integer between any two intervals, and endpoints at least `1`.
See the README's statement of faithfulness for why the adjacency correction is substantive.
-/

namespace Erdos289

/-- A corrected nonadjacent formulation of Erdős Problem 289, adapted from
`FormalConjectures/ErdosProblems/289.lean` in google-deepmind/formal-conjectures at commit
`d1401976` (Apache License 2.0) via `SolveMath/Unsolved/Erdos/P289/Statement.lean` in the
`solve-math` corpus, from which it is copied verbatim. Compared with the Formal Conjectures
statement it requires (a) positive left endpoints `1 ≤ (I i).1` and (b) at least one omitted
integer between distinct intervals, `(I i).2 + 2 ≤ (I j).1 ∨ (I j).2 + 2 ≤ (I i).1`, instead of
the weaker `(I i).2 < (I j).1 ∨ (I j).2 < (I i).1`. -/
def erdos_289_nonadjacent_statement : Prop :=
  ∀ᶠ k : ℕ in Filter.atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, 1 ≤ (I i).1 ∧ (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 2 ≤ (I j).1 ∨ (I j).2 + 2 ≤ (I i).1) ∧
    ∑ i, ∑ n ∈ Finset.Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1

theorem candidateStatement_implies_erdos_289_nonadjacent :
    CandidateStatement → erdos_289_nonadjacent_statement := by
  rintro ⟨k₀, hk₀⟩
  unfold erdos_289_nonadjacent_statement
  rw [Filter.eventually_atTop]
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨W⟩ := hk₀ k hk
  refine ⟨fun i => ((W.intervals i).lo, (W.intervals i).hi), fun i => ⟨W.positive i, ?_⟩,
    fun i j hij => ?_, ?_⟩
  · dsimp only
    rcases W.short i with h | h <;> omega
  · dsimp only
    rcases lt_or_gt_of_ne hij with h | h
    · have hsep := W.separated i j h
      unfold NatInterval.Separated at hsep
      omega
    · have hsep := W.separated j i h
      unfold NatInterval.Separated at hsep
      omega
  · dsimp only
    have := W.total_mass
    simp only [NatInterval.mass, NatInterval.carrier, one_div] at this
    simpa using this

/-- The corrected nonadjacent formulation holds. -/
theorem erdos_289_nonadjacent : erdos_289_nonadjacent_statement :=
  candidateStatement_implies_erdos_289_nonadjacent candidateStatement

end Erdos289

