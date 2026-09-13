import Erdos289CLT.Main
import Erdos289.Main

/-!
# The two formalizations answer the same question

`Erdos289.CandidateStatement` (earlier paper: intervals of length two or three inside `[1, 20k]`)
and `Erdos289.CLT.Statement234` (current paper: intervals of length two, three or four, the longer
ones from a fixed finite set) are different strengthenings of the nonadjacent form of Erdős
Problem 289.  Both use the same interval type `NatInterval`, the same reciprocal mass, the same
separation `Separated` and the same `Fin k` indexing.  This file states the bare problem, with
no strengthening, and proves that each formalized theorem implies it.
-/

namespace Erdos289

/-- The nonadjacent form of Erdős Problem 289 with no extra strengthening: `k` intervals of
positive integers, each containing at least two integers, ordered with at least one unused integer
between consecutive ones, reciprocal sum `1`. -/
structure BareWitness (k : ℕ) where
  intervals : Fin k → NatInterval
  positive : ∀ i, 1 ≤ (intervals i).lo
  length_at_least_two : ∀ i, (intervals i).lo + 1 ≤ (intervals i).hi
  separated : ∀ i j, i < j → (intervals i).Separated (intervals j)
  total_mass : ∑ i, (intervals i).mass = 1

def BareStatement : Prop := ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Nonempty (BareWitness k)

theorem bareStatement_of_candidate (h : CandidateStatement) : BareStatement := by
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨W⟩ := hk₀ k hk
  exact ⟨⟨W.intervals, W.positive, fun i => by rcases W.short i with h | h <;> omega,
    W.separated, W.total_mass⟩⟩

theorem bareStatement_of_statement234 (h : CLT.Statement234) : BareStatement := by
  obtain ⟨_, k₀, hk₀⟩ := h
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨W, -⟩ := hk₀ k hk
  exact ⟨⟨W.intervals, fun i => by have := W.two_le i; omega, fun i => (W.short i).1,
    W.separated, W.total_mass⟩⟩

/-- Both formalized theorems prove the bare statement. -/
theorem bareStatement_earlier : BareStatement := bareStatement_of_candidate candidateStatement

theorem bareStatement_current : BareStatement := bareStatement_of_statement234 CLT.statement234

end Erdos289
