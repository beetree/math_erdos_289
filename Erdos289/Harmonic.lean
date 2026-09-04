import Erdos289.Defs

/-!
# Harmonic sum estimates

Elementary bounds on harmonic-type sums used in Sections 5 and 6 of the paper:
an upper bound for a harmonic block `∑_{d=Q}^{BQ-1} 1/d`, upper/lower bounds for
sums of reciprocals over sets confined to a dyadic band, and bounds for the
reciprocal masses `w a`, `Iv.pair a`, `Iv.triple a`.
-/

namespace Erdos289

open Finset

/-- Upper bound for a harmonic block: `∑_{d=Q}^{BQ-1} 1/d ≤ log B + 1/Q`. -/
theorem sum_inv_Ico_le (Q B : ℕ) (hQ : 0 < Q) :
    ∑ d ∈ Finset.Ico Q (B * Q), (1 : ℝ) / d ≤ Real.log B + 1 / Q := by
  rcases Nat.lt_or_ge B 2 with hB | hB
  · interval_cases B <;> simp
  · have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hQR : (1 : ℝ) < (Q : ℝ) + 1 := by linarith
    have hN : Q + 1 ≤ B * Q := by
      have h2 : 2 * Q ≤ B * Q := Nat.mul_le_mul_right Q hB
      omega
    have hlt : Q < B * Q := by omega
    have hmem_not : Q ∉ Finset.Ico (Q + 1) (B * Q) := by simp
    have hins : insert Q (Finset.Ico (Q + 1) (B * Q)) = Finset.Ico Q (B * Q) := by
      have := Finset.insert_Ico_succ_left_eq_Ico hlt
      simpa using this
    rw [← hins, Finset.sum_insert hmem_not]
    have key : ∑ d ∈ Finset.Ico (Q + 1) (B * Q), (1 : ℝ) / d ≤ Real.log B := by
      have hf : AntitoneOn (fun x : ℝ => (x - 1)⁻¹)
          (Set.Icc ((Q + 1 : ℕ) : ℝ) ((B * Q : ℕ) : ℝ)) := by
        apply sub_inv_antitoneOn_Icc_right
        push_cast
        linarith
      have hab : (Q + 1 : ℕ) ≤ (B * Q : ℕ) := hN
      have step := AntitoneOn.sum_le_integral_Ico hab hf
      have lhs_eq : ∑ i ∈ Finset.Ico (Q + 1) (B * Q), ((↑(i + 1) : ℝ) - 1)⁻¹
          = ∑ d ∈ Finset.Ico (Q + 1) (B * Q), (1 : ℝ) / d := by
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        rw [add_sub_cancel_right, one_div]
      rw [lhs_eq] at step
      have hshift : (∫ x in ((Q + 1 : ℕ) : ℝ)..((B * Q : ℕ) : ℝ), (x - 1)⁻¹)
          = ∫ x in (Q : ℝ)..(((B * Q : ℕ) : ℝ) - 1), (x : ℝ)⁻¹ := by
        rw [intervalIntegral.integral_comp_sub_right (fun x => x⁻¹) 1]
        congr 1
        push_cast
        ring
      rw [hshift] at step
      have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
      have hBQ1 : (Q : ℝ) ≤ ((B * Q : ℕ) : ℝ) - 1 := by
        have : ((Q : ℕ) + 1 : ℝ) ≤ ((B * Q : ℕ) : ℝ) := by exact_mod_cast hN
        linarith
      have hnotmem : (0 : ℝ) ∉ Set.uIcc (Q : ℝ) (((B * Q : ℕ) : ℝ) - 1) := by
        rw [Set.uIcc_of_le hBQ1]
        simp only [Set.mem_Icc, not_and, not_le]
        intro _
        linarith
      rw [integral_inv hnotmem] at step
      have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
      have hdiv_le : (((B * Q : ℕ) : ℝ) - 1) / (Q : ℝ) ≤ (B : ℝ) := by
        rw [div_le_iff₀ hQpos]
        push_cast
        nlinarith
      have hdiv_pos : (0 : ℝ) < (((B * Q : ℕ) : ℝ) - 1) / (Q : ℝ) := by
        apply div_pos (by linarith) hQpos
      calc ∑ d ∈ Finset.Ico (Q + 1) (B * Q), (1 : ℝ) / d
          ≤ Real.log ((((B * Q : ℕ) : ℝ) - 1) / (Q : ℝ)) := step
        _ ≤ Real.log (B : ℝ) := Real.log_le_log hdiv_pos hdiv_le
    linarith [key]

/-- The rational-valued version of `sum_inv_Ico_le`, cast to `ℝ`. -/
theorem sum_inv_Ico_le_rat (Q B : ℕ) (hQ : 0 < Q) :
    ((∑ d ∈ Finset.Ico Q (B * Q), (1 : ℚ) / d : ℚ) : ℝ) ≤ Real.log B + 1 / Q := by
  have h := sum_inv_Ico_le Q B hQ
  push_cast at h ⊢
  exact h

/-- Lower bound for a reciprocal sum over a set confined to a dyadic band `[t, 2t]`. -/
theorem sum_inv_ge_card_div {P : Finset ℕ} {t : ℕ} (ht : 0 < t)
    (hP : ∀ n ∈ P, n ≤ 2 * t) (hPt : ∀ n ∈ P, t ≤ n) :
    (P.card : ℚ) / (2 * t) ≤ ∑ n ∈ P, (1 : ℚ) / n := by
  have h := Finset.card_nsmul_le_sum P (fun n => (1 : ℚ) / n) (1 / (2 * t)) ?_
  · rwa [nsmul_eq_mul, mul_one_div] at h
  · intro n hn
    have hn0 : (0 : ℚ) < n := by exact_mod_cast lt_of_lt_of_le ht (hPt n hn)
    have h2t : (0 : ℚ) < 2 * t := by positivity
    exact one_div_le_one_div_of_le hn0 (by exact_mod_cast hP n hn)

/-- Upper bound for a reciprocal sum over a set bounded below by `t`. -/
theorem sum_inv_le_card_div {P : Finset ℕ} {t : ℕ} (ht : 0 < t) (hP : ∀ n ∈ P, t ≤ n) :
    ∑ n ∈ P, (1 : ℚ) / n ≤ (P.card : ℚ) / t := by
  have h := Finset.sum_le_card_nsmul P (fun n => (1 : ℚ) / n) (1 / t) ?_
  · rwa [nsmul_eq_mul, mul_one_div] at h
  · intro n hn
    have htQ : (0 : ℚ) < t := by exact_mod_cast ht
    exact one_div_le_one_div_of_le htQ (by exact_mod_cast hP n hn)

/-- `w a ≤ 2 / a` for `a > 0`. -/
theorem w_le {a : ℕ} (ha : 0 < a) : w a ≤ 2 / a := by
  unfold w
  have ha0 : (0 : ℚ) < a := by exact_mod_cast ha
  have hstep : (1 : ℚ) / (a + 1) ≤ 1 / a := one_div_le_one_div_of_le ha0 (by linarith)
  have : (2 : ℚ) / a = 1 / a + 1 / a := by ring
  linarith

/-- `2 / (a + 1) ≤ w a` for `a > 0`. -/
theorem w_ge {a : ℕ} (ha : 0 < a) : 2 / (a + 1 : ℚ) ≤ w a := by
  unfold w
  have ha0 : (0 : ℚ) < a := by exact_mod_cast ha
  have hstep : (1 : ℚ) / (a + 1) ≤ 1 / a := one_div_le_one_div_of_le ha0 (by linarith)
  have : (2 : ℚ) / (a + 1) = 1 / (a + 1) + 1 / (a + 1) := by ring
  linarith

/-- The reciprocal mass of a pair `[a, a+1]` is at most `2 / a`. -/
theorem pair_mass_le {a : ℕ} (ha : 0 < a) : (Iv.pair a).mass ≤ 2 / a := by
  show mass a (a + 1) ≤ 2 / a
  rw [mass_pair]
  exact w_le ha

/-- The reciprocal mass of a triple `[a, a+2]` is at most `3 / a`. -/
theorem triple_mass_le {a : ℕ} (ha : 0 < a) : (Iv.triple a).mass ≤ 3 / a := by
  show mass a (a + 2) ≤ 3 / a
  rw [mass_triple]
  have ha0 : (0 : ℚ) < a := by exact_mod_cast ha
  have ha1 : 0 < a + 1 := Nat.succ_pos a
  have h1 : w (a + 1) ≤ 2 / (a + 1 : ℕ) := w_le ha1
  have h2 : (2 : ℚ) / ((a + 1 : ℕ) : ℚ) ≤ 2 / a := by
    push_cast
    apply div_le_div_of_nonneg_left (by norm_num) ha0 (by linarith)
  have h3 : (3 : ℚ) / a = 1 / a + 2 / a := by ring
  linarith

end Erdos289
