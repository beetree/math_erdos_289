import Erdos289.Descent

/-!
# Existence of correction data

Lemmas 1, 3 and 5 (with `ε = 1/10`) provide, for every sufficiently large cutoff `L`,
the data `CorrectionData` used by the correction procedure.
-/

namespace Erdos289

/-- Correction data exists for every sufficiently large cutoff `L`
(from Lemmas 1, 3 and 5 with `ε = 1/10`). -/
theorem correctionData_exists : ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → ∃ C : CorrectionData, C.L = L := by
  sorry


end Erdos289
