import Erdos289.Lemma1EquidistStmt

/-!
# Lemma 1: the even-case count (open)
-/

namespace Erdos289

open Finset Filter Topology

/-- **Even case count** (paper: "The count of such `t` is `M/40 + o(M)`. Among them, `2 ∣ m`
iff the inverse modulo `2q` belongs to the same absolute interval; their count is
`M/80 + o(M)`. Thus `M/80 + o(M)` choices have odd `m`."). Stated as the lower bound needed
downstream; proved (in the paper) from `equidist_inverse` applied at moduli `q` and `2q`. -/
theorem even_case_count (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ a : ℕ, 0 < a → q = 2 ^ a →
      (q : ℝ) ^ ε / 80 - κ * (q : ℝ) ^ ε ≤
        ((evenCandT q ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊).card : ℝ) := by
  sorry

end Erdos289
