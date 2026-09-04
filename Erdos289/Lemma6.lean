import Erdos289.Defs
import Erdos289.ExternalBridge
import Erdos289.External

/-!
# Lemma 6: dense subsets of `[T, 4T)` contain a unit-fraction sum of `1`

If `E ⊆ [T, 4T)` has size `o(T)` then `[T, 4T) \ E` has a subset whose reciprocals sum to `1`.
We make `o(T)` explicit as `|E| ≤ T / 4`: then the density of `[T,4T) \ E` in `[1, 4T]` is at
least `3/4 - 1/16 > 1 - 1/e + 1/20`, so Liu–Sawhney with `ζ = 1/20` applies.
-/

namespace Erdos289

open Finset

/-- **Lemma 6** of the paper. -/
theorem lemma6 : ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → ∀ E ⊆ Ico T (4 * T), (E.card : ℝ) ≤ T / 4 →
    ∃ D ⊆ Ico T (4 * T) \ E, ∑ d ∈ D, (1 : ℚ) / d = 1 := by
  have hζ0 : (0 : ℝ) < 1 / 20 := by norm_num
  have hζ1 : (1 : ℝ) / 20 < 1 / 2 := by norm_num
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (liu_sawhney (ζ := 1 / 20) hζ0 hζ1)
  refine ⟨max N₀ 1, fun T hT E hE hEcard => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right N₀ 1) hT
  have hTN0 : N₀ ≤ T := le_trans (le_max_left N₀ 1) hT
  have hN : N₀ ≤ 4 * T := by omega
  have hAsub : Ico T (4 * T) \ E ⊆ Finset.Icc 1 (4 * T) := by
    intro x hx
    simp only [mem_sdiff, mem_Ico] at hx
    simp only [Finset.mem_Icc]
    omega
  -- Cardinality of `A = Ico T (4T) \ E`.
  have hcardIco : (Ico T (4 * T)).card = 3 * T := by
    rw [Nat.card_Ico]; omega
  have hcard_le' : E.card ≤ 3 * T := by
    rw [← hcardIco]; exact Finset.card_le_card hE
  have hcast : ((Ico T (4 * T) \ E).card : ℝ) = 3 * (T : ℝ) - (E.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hE, hcardIco, Nat.cast_sub hcard_le', Nat.cast_mul]
    norm_num
  -- The numeric density bound `1 - 1/e + 1/20 ≤ 11/16`.
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hkey : (1 : ℝ) - 1 / Real.exp 1 + 1 / 20 ≤ 11 / 16 := by
    have h1 : (29 : ℝ) / 80 ≤ 1 / Real.exp 1 := by
      rw [le_div_iff₀ he0]
      nlinarith
    linarith
  have hTreal : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hdensity :
      (1 - 1 / Real.exp 1 + 1 / 20) * ((4 * T : ℕ) : ℝ) ≤ ((Ico T (4 * T) \ E).card : ℝ) := by
    rw [hcast, Nat.cast_mul]
    push_cast
    nlinarith [hkey, hEcard, hTreal]
  obtain ⟨D, hD, hsum⟩ := hN₀ (4 * T) hN (Ico T (4 * T) \ E) hAsub hdensity
  exact ⟨D, hD, hsum⟩

end Erdos289
