import SolveMath.Edges.Erdos.P300.Solution

/-!
# Bridging the ported Liu–Sawhney proof to our target statements

`SolveMath.Edges.Erdos.P300.Solution` (ported from Boris Alexeev's `plby/lean-proofs`, via
`solve-math`) proves `Erdos300.dense_contains_one`, an axiom-free formalization of
Liu–Sawhney (arXiv:2404.07113), Theorem 1.3. This file derives, from that ported theorem,
exactly the two statements our project needs:

* `liu_sawhney`, matching our working axiom `Erdos289.liu_sawhney` in `Erdos289/External.lean`;
* `liu_sawhney_audited`, matching the audited
  `Erdos289.External.LiuSawhneyStatement` in `Erdos289/ExternalAxioms.lean`, with
  `rationalMass` unfolded.
-/

namespace Erdos289.Ported

theorem liu_sawhney (ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ A ⊆ Finset.Icc 1 N,
      (1 - 1 / Real.exp 1 + ζ) * (N : ℝ) ≤ (A.card : ℝ) →
      ∃ D ⊆ A, ∑ d ∈ D, (1 : ℚ) / d = 1 := by
  have h := Erdos300.dense_contains_one ζ hζ0 hζ1
  filter_upwards [h] with N hN A hA hcard
  obtain ⟨B, hBA, hBsum⟩ := hN A hA hcard
  exact ⟨B, hBA, by simpa [UnitFractions.rec_sum] using hBsum⟩

theorem liu_sawhney_audited :
    ∀ ζ : ℝ, 0 < ζ → ζ < (1 : ℝ) / 2 →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        ∀ N : ℕ, N₀ ≤ N →
          ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
            (1 - Real.exp (-1) + ζ) * (N : ℝ) ≤ (A.card : ℝ) →
            ∃ D : Finset ℕ, D ⊆ A ∧ (∑ d ∈ D, (1 : ℚ) / (d : ℚ)) = 1 := by
  intro ζ hζ0 hζ1
  have h := Erdos300.dense_contains_one ζ hζ0 hζ1
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨max N₀ 1, le_max_right _ _, fun N hN A hA hcard => ?_⟩
  have hN' : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hcard' : (1 - 1 / Real.exp 1 + ζ) * (N : ℝ) ≤ (A.card : ℝ) := by
    simpa [Real.exp_neg, one_div] using hcard
  obtain ⟨B, hBA, hBsum⟩ := hN₀ N hN' A hA hcard'
  exact ⟨B, hBA, by simpa [UnitFractions.rec_sum] using hBsum⟩

end Erdos289.Ported
