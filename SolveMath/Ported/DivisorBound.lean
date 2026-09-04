import SolveMath.Corpus.NumberTheory.DivisorCountSubpolynomialGrowth

namespace Erdos289.Ported

theorem divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε :=
  DivisorCountSubpolynomialGrowth.eventually_divisorCount_le_rpow ε hε

theorem divisor_bound_audited :
    ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧
        ∀ n : ℕ, n₀ ≤ n → ((Nat.divisors n).card : ℝ) ≤ (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (divisor_bound ε hε)
  exact ⟨max n₀ 1, le_max_right _ _, fun n hn => hn₀ n (le_trans (le_max_left _ _) hn)⟩

end Erdos289.Ported
