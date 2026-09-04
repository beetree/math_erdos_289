import Erdos289.Main

/-!
# Compatibility with the standard `∀ᶠ k, ∃ I : Fin k → ℕ × ℕ` statement of Erdős Problem 289

This file bridges the audited `CandidateStatement` from `Erdos289/Intervals.lean` to the
literal statement of Erdős Problem 289 as posed in the `solve-math` corpus and in
google-deepmind/formal-conjectures, and discharges it from `Erdos289.candidateStatement`.
-/

namespace Erdos289

/-- The literal statement of Erdős Problem 289, copied verbatim (down to the choice of
identifiers) from `SolveMath/Unsolved/Erdos/P289/Statement.lean` in the `solve-math`
corpus, which is itself derived from `FormalConjectures/ErdosProblems/289.lean` in
google-deepmind/formal-conjectures at commit `d1401976` (Apache License 2.0). -/
def erdos_289_statement : Prop :=
  ∀ᶠ k : ℕ in Filter.atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, 1 ≤ (I i).1 ∧ (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 2 ≤ (I j).1 ∨ (I j).2 + 2 ≤ (I i).1) ∧
    ∑ i, ∑ n ∈ Finset.Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1

theorem candidateStatement_implies_erdos_289 : CandidateStatement → erdos_289_statement := by
  rintro ⟨k₀, hk₀⟩
  unfold erdos_289_statement
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

theorem erdos_289 : erdos_289_statement := candidateStatement_implies_erdos_289 candidateStatement

end Erdos289

#print axioms Erdos289.erdos_289
