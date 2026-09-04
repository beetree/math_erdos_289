import Erdos289.Defs

/-!
# Tail estimates (4.8) and (4.9)

Tail-sum bound for `∑ n^{-21/20}` and the companion power-sum / stage-mass estimates
used in the proof of Erdős Problem 289.
-/

namespace Erdos289

/-- Tail-sum estimate (4.9): the sum of `n ^ (-21/20)` over `n ∈ (L, H]` is at most
`20 * L ^ (-1/20)`. -/
theorem sum_rpow_tail_le (L H : ℕ) (hL : 1 ≤ L) :
    ∑ n ∈ Finset.Ioc L H, (n : ℝ) ^ (-(21 : ℝ) / 20) ≤ 20 * (L : ℝ) ^ (-(1 : ℝ) / 20) := by
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  by_cases hLH : L ≤ H
  · have hf : AntitoneOn (fun x : ℝ => x ^ (-(21 : ℝ) / 20)) (Set.Icc (L : ℝ) (H : ℝ)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hLpos hx.1) hxy (by norm_num)
    have hmain := AntitoneOn.sum_le_integral_Ico hLH hf
    have e1 : ∑ i ∈ Finset.Ico L H, ((i + 1 : ℕ) : ℝ) ^ (-(21 : ℝ) / 20)
        = ∑ n ∈ Finset.Ioc L H, (n : ℝ) ^ (-(21 : ℝ) / 20) := by
      apply Finset.sum_nbij' (fun i => i + 1) (fun n => n - 1)
      · intro a ha; simp only [Finset.mem_Ico] at ha; simp only [Finset.mem_Ioc]; omega
      · intro a ha; simp only [Finset.mem_Ioc] at ha; simp only [Finset.mem_Ico]; omega
      · intro a _; omega
      · intro a ha; simp only [Finset.mem_Ioc] at ha; omega
      · intro a _; rfl
    have h0 : (0 : ℝ) ∉ Set.uIcc (L : ℝ) (H : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hLH)]
      simp only [Set.mem_Icc, not_and, not_le]
      intro h
      linarith
    have hint : ∫ x in (L : ℝ)..(H : ℝ), x ^ (-(21 : ℝ) / 20)
        = 20 * ((L : ℝ) ^ (-(1 : ℝ) / 20) - (H : ℝ) ^ (-(1 : ℝ) / 20)) := by
      rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
      norm_num
      ring
    have hHnn : (0 : ℝ) ≤ (H : ℝ) ^ (-(1 : ℝ) / 20) := Real.rpow_nonneg (by positivity) _
    calc ∑ n ∈ Finset.Ioc L H, (n : ℝ) ^ (-(21 : ℝ) / 20)
        = ∑ i ∈ Finset.Ico L H, ((i + 1 : ℕ) : ℝ) ^ (-(21 : ℝ) / 20) := e1.symm
      _ ≤ ∫ x in (L : ℝ)..(H : ℝ), x ^ (-(21 : ℝ) / 20) := hmain
      _ = 20 * ((L : ℝ) ^ (-(1 : ℝ) / 20) - (H : ℝ) ^ (-(1 : ℝ) / 20)) := hint
      _ ≤ 20 * (L : ℝ) ^ (-(1 : ℝ) / 20) := by nlinarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity

/-- Power-sum bound (4.8): the sum of `⌊q ^ (1/20)⌋` over prime powers `q ∈ (L, H]`
is at most `H ^ (21/20)`. -/
theorem sum_rpow_le (L H : ℕ) :
    ((∑ q ∈ (Finset.Icc (L + 1) H).filter IsPrimePow, ⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℕ) : ℝ)
      ≤ (H : ℝ) ^ ((21 : ℝ) / 20) := by
  set s := (Finset.Icc (L + 1) H).filter IsPrimePow with hs_def
  have hcard : s.card ≤ H := by
    calc s.card ≤ (Finset.Icc (L + 1) H).card := Finset.card_filter_le _ _
      _ ≤ H := by rw [Nat.card_Icc]; omega
  push_cast
  calc ∑ q ∈ s, (⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℝ)
      ≤ ∑ _q ∈ s, (H : ℝ) ^ ((1 : ℝ) / 20) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqH : q ≤ H := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
        calc (⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 20) :=
              Nat.floor_le (by positivity)
          _ ≤ (H : ℝ) ^ ((1 : ℝ) / 20) :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqH) (by norm_num)
    _ = (s.card : ℝ) * (H : ℝ) ^ ((1 : ℝ) / 20) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H : ℝ) * (H : ℝ) ^ ((1 : ℝ) / 20) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = (H : ℝ) ^ ((21 : ℝ) / 20) := by
        have h1 : (21 : ℝ) / 20 = 1 + 1 / 20 := by norm_num
        rw [h1, Real.rpow_add_of_nonneg (by positivity) (by norm_num) (by norm_num),
          Real.rpow_one]

/-- Stage-mass bound: the reciprocal mass contributed by prime powers `q ∈ (L, H]`,
weighted by `2 s(q)`, is at most `40 * L ^ (-1/20)`. -/
theorem sum_stage_mass_le (L H : ℕ) (hL : 1 ≤ L) :
    ∑ q ∈ (Finset.Icc (L + 1) H).filter IsPrimePow,
        2 * (⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10)
      ≤ 40 * (L : ℝ) ^ (-(1 : ℝ) / 20) := by
  have hIcc_eq : Finset.Icc (L + 1) H = Finset.Ioc L H := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have step1 : ∑ q ∈ (Finset.Icc (L + 1) H).filter IsPrimePow,
        2 * (⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10)
      ≤ ∑ q ∈ Finset.Icc (L + 1) H, 2 * (q : ℝ) ^ (-(21 : ℝ) / 20) := by
    calc ∑ q ∈ (Finset.Icc (L + 1) H).filter IsPrimePow,
        2 * (⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10)
        ≤ ∑ q ∈ (Finset.Icc (L + 1) H).filter IsPrimePow, 2 * (q : ℝ) ^ (-(21 : ℝ) / 20) := by
          apply Finset.sum_le_sum
          intro q hq
          have hqIcc : q ∈ Finset.Icc (L + 1) H := (Finset.mem_filter.mp hq).1
          have hq1 : L + 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
          have hq0 : (0 : ℝ) < (q : ℝ) := by
            have : 0 < q := by omega
            exact_mod_cast this
          have heq : (q : ℝ) ^ ((1 : ℝ) / 20) * (q : ℝ) ^ (-(11 : ℝ) / 10)
              = (q : ℝ) ^ (-(21 : ℝ) / 20) := by
            rw [← Real.rpow_add hq0]; norm_num
          calc 2 * (⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10)
              ≤ 2 * ((q : ℝ) ^ ((1 : ℝ) / 20)) * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
                gcongr
                exact Nat.floor_le (by positivity)
            _ = 2 * ((q : ℝ) ^ ((1 : ℝ) / 20) * (q : ℝ) ^ (-(11 : ℝ) / 10)) := by ring
            _ = 2 * (q : ℝ) ^ (-(21 : ℝ) / 20) := by rw [heq]
      _ ≤ ∑ q ∈ Finset.Icc (L + 1) H, 2 * (q : ℝ) ^ (-(21 : ℝ) / 20) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro q _ _; positivity
  calc ∑ q ∈ (Finset.Icc (L + 1) H).filter IsPrimePow,
      2 * (⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊ : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10)
      ≤ ∑ q ∈ Finset.Icc (L + 1) H, 2 * (q : ℝ) ^ (-(21 : ℝ) / 20) := step1
    _ = ∑ q ∈ Finset.Ioc L H, 2 * (q : ℝ) ^ (-(21 : ℝ) / 20) := by rw [hIcc_eq]
    _ = 2 * ∑ q ∈ Finset.Ioc L H, (q : ℝ) ^ (-(21 : ℝ) / 20) := by rw [Finset.mul_sum]
    _ ≤ 2 * (20 * (L : ℝ) ^ (-(1 : ℝ) / 20)) := by
        apply mul_le_mul_of_nonneg_left (sum_rpow_tail_le L H hL) (by norm_num)
    _ = 40 * (L : ℝ) ^ (-(1 : ℝ) / 20) := by ring

end Erdos289
