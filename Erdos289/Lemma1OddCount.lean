import Erdos289.Lemma1EquidistStmt

/-!
# Lemma 1: the odd-case count (open)
-/

namespace Erdos289

open Finset Filter Topology


/-- **Odd case count** (paper display (2.2)): "Since `4 ∣ m`, the additional condition `p ∣ m`
is equivalent to `rt ≡ 1 (mod 4pq)` ... Subtracting leaves `(1-1/p)² M / 160 + o(M) ≥ M/360 +
o(M)`." Stated as the lower bound needed downstream (using `p ≥ 3`, so `(1-1/p)² ≥ 4/9`);
proved (in the paper) from `equidist_inverse` applied at moduli `4q` and `4pq`. -/
theorem odd_case_count (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ p a : ℕ, p.Prime → Odd p → 0 < a → q = p ^ a →
      (q : ℝ) ^ ε / 360 - κ * (q : ℝ) ^ ε ≤
        ((oddCandT q p ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊).card : ℝ) := by
  sorry

end Erdos289
