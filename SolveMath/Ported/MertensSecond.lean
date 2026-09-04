import SolveMath.Corpus.NumberTheory.MeisselMertensConstantAsymptotic

namespace Erdos289.Ported

private theorem primeSummatory_eq (x : ℝ) :
    AbelSummatoryPrimeRestriction.prime_summatory (fun p : ℕ => (p : ℝ)⁻¹) 1 x
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  unfold AbelSummatoryPrimeRestriction.prime_summatory
  rw [show (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime = (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime
      from ?_]
  · exact Finset.sum_congr rfl (fun p _ => (one_div (p : ℝ)).symm)
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_, hp2⟩, hp⟩
      exact ⟨hp2, hp⟩
    · rintro ⟨hp2, hp⟩
      exact ⟨⟨hp.pos, hp2⟩, hp⟩

theorem mertens_second_audited :
    ∃ B₁ : ℝ,
      Filter.Tendsto
        (fun x : ℝ => (∑ p ∈ ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime), (1 : ℝ) / (p : ℝ))
          - Real.log (Real.log x))
        Filter.atTop (nhds B₁) := by
  refine ⟨MeisselMertensConstantAsymptotic.meissel_mertens, ?_⟩
  have hg : Filter.Tendsto (fun x : ℝ => (Real.log x)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h0 := MeisselMertensConstantAsymptotic.prime_reciprocal.trans_tendsto hg
  have hconst : Filter.Tendsto (fun _ : ℝ => MeisselMertensConstantAsymptotic.meissel_mertens)
      Filter.atTop (nhds MeisselMertensConstantAsymptotic.meissel_mertens) := tendsto_const_nhds
  have h1 := h0.add hconst
  rw [zero_add] at h1
  refine h1.congr (fun x => ?_)
  rw [primeSummatory_eq x]
  ring

theorem mertens_second :
    ∃ B₁ : ℝ, Filter.Tendsto
      (fun x : ℕ => (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p)
        - Real.log (Real.log x)) Filter.atTop (nhds B₁) := by
  obtain ⟨B₁, hB₁⟩ := mertens_second_audited
  refine ⟨B₁, ?_⟩
  have hcomp := hB₁.comp tendsto_natCast_atTop_atTop
  have heq : (fun x : ℕ => (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p)
        - Real.log (Real.log x))
      = (fun x : ℝ => (∑ p ∈ ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime), (1 : ℝ) / (p : ℝ))
          - Real.log (Real.log x)) ∘ (Nat.cast : ℕ → ℝ) := by
    funext n
    simp only [Function.comp_apply, Nat.floor_natCast]
  rw [heq]
  exact hcomp

end Erdos289.Ported
