module

public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.Basic

@[expose] public section

namespace UnitFractions

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Real
open _root_.Finset

noncomputable section

lemma prod_dvd_of_dvd_of_pairwise_disjoint {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}
    (hn : ∀ i ∈ s, f i ∣ n) (h : (s : Set ι).Pairwise fun i j => Nat.Coprime (f i) (f j)) :
    s.prod f ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a r har ihr =>
      rw [Finset.prod_insert har]
      have hcop : Nat.Coprime (f a) (r.prod f) := by
        rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact h (by simp) (by simp [hi]) (ne_of_mem_of_not_mem hi har).symm
      refine hcop.mul_dvd_of_dvd_of_dvd ?_ ?_
      · exact hn a (by simp)
      · refine ihr ?_ ?_
        · intro i hi
          exact hn i (by simp [hi])
        · intro i hi j hj hij
          exact h (by simp [hi]) (by simp [hj]) hij

/-- Lemma 4.10. -/
lemma triv_q_bound {A : Finset ℕ} (hA : 0 ∉ A) (n : ℕ) :
    ↑((ppowers_in_set A).filter fun q => n ∈ local_part A q).card ≤ log n / log 2 := by
  by_cases hn0 : n = 0
  · subst hn0
    simp [zero_mem_local_part_iff, hA, Real.log_zero]
  · have hsubset :
        (ppowers_in_set A).filter (fun q => n ∈ local_part A q) ⊆
          n.divisors.filter (fun q => IsPrimePow q ∧ Nat.Coprime q (n / q)) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqppow, hqn⟩
      rcases (mem_ppowers_in_set.mp hqppow).1 with hqprime
      rcases (mem_local_part (A := A) (q := q) n).mp hqn with ⟨_, hqdvd, hqcop⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · rw [Nat.mem_divisors]
        exact ⟨hqdvd, hn0⟩
      · exact ⟨hqprime, hqcop⟩
    have hcard :
        ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card ≤
          ArithmeticFunction.cardDistinctFactors n := by
      calc
        ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card ≤
            (n.divisors.filter (fun q => IsPrimePow q ∧ Nat.Coprime q (n / q))).card := by
              exact Finset.card_le_card hsubset
        _ = ArithmeticFunction.cardDistinctFactors n := omega_count_eq_ppowers
    have hpow_nat : 2 ^ ArithmeticFunction.cardDistinctFactors n ≤ n := by
      calc
        2 ^ ArithmeticFunction.cardDistinctFactors n ≤ ArithmeticFunction.sigma 0 n :=
          two_pow_card_distinct_divisors_le_divisor_count hn0
        _ ≤ n := by
          rw [ArithmeticFunction.sigma_zero_apply]
          exact Nat.card_divisors_le_self n
    have hpow : (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n ≤ n := by
      simpa [Real.rpow_natCast] using
        (show ((2 ^ ArithmeticFunction.cardDistinctFactors n : ℕ) : ℝ) ≤ n by
          exact_mod_cast hpow_nat)
    have hcardR :
        (((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card : ℝ) ≤
          ArithmeticFunction.cardDistinctFactors n := by
      exact_mod_cast hcard
    have hlog :
        (ArithmeticFunction.cardDistinctFactors n : ℝ) * log 2 ≤ log n := by
      have hlog_aux := Real.log_le_log
        (show 0 < (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n by positivity) hpow
      simpa [Real.log_rpow, mul_comm] using hlog_aux
    have hlog2 : 0 < log 2 := Real.log_pos one_lt_two
    exact le_trans hcardR ((le_div_iff₀ hlog2).2 <| by simpa [mul_comm] using hlog)

/-- Lemma 4.11. -/
lemma orthog_rat {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0) :
    (integer_count A k : ℂ) =
      1 / (lcmA A) *
        (valid_sum_range (lcmA A)).sum (fun h => A.prod (fun n => 1 + e (k * h / n))) := by
  have hA' : ((lcmA A : ℕ) : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.2 ((Finset.lcm_ne_zero_iff (s := A) (f := id)).2
      (by intro x hx hx0; exact hA (hx0 ▸ hx)))
  have hk' : (k : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.2 hk
  have hdiv :
      ∀ S : Finset ℕ, S ⊆ A →
        ((∃ z : ℤ, rec_sum S * (k : ℚ) = z) ↔
          lcmA A ∣ (k * S.sum (fun n => lcmA A / n))) := by
    intro S hS
    have hsum :
        S.sum (fun x => ((lcmA A / x : ℕ) : ℚ)) = rec_sum S * (lcmA A : ℚ) := by
      rw [rec_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : x ≠ 0 := by
        intro hx0
        apply hA
        exact hS (hx0 ▸ hx)
      calc
        (((lcmA A / x : ℕ) : ℚ)) = (lcmA A : ℚ) / x := by
          rw [Nat.cast_div (K := ℚ)]
          · exact Finset.dvd_lcm (hS hx)
          · exact Nat.cast_ne_zero.2 hx0
        _ = ((1 : ℚ) / x) * (lcmA A : ℚ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    rw [← Int.natCast_dvd_natCast, dvd_iff_exists_eq_mul_left]
    apply exists_congr
    intro z
    constructor
    · intro hz
      have hzQ :
          (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) = (z : ℚ) * (lcmA A : ℚ) := by
        calc
          (k : ℚ) * S.sum (fun x => ↑(lcmA A / x))
              = (k : ℚ) * (rec_sum S * (lcmA A : ℚ)) := by
            rw [hsum]
          _ = (rec_sum S * (k : ℚ)) * (lcmA A : ℚ) := by ring
          _ = (z : ℚ) * (lcmA A : ℚ) := by rw [hz]
      apply (Int.cast_inj (α := ℚ)).mp
      rw [Int.cast_natCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_sum]
      simpa [Rat.cast_natCast] using hzQ
    · intro hz
      have hzQ : (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) = (z : ℚ) * (lcmA A : ℚ) := by
        have hsum_int_cast :
            S.sum (fun x => (((lcmA A : ℤ) / (x : ℤ) : ℤ) : ℚ)) =
              S.sum (fun x => (lcmA A : ℚ) / (x : ℚ)) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hx0_nat : x ≠ 0 := by
            intro hx0
            exact hA (hS (hx0 ▸ hx))
          have hx0 : ((x : ℤ) : ℚ) ≠ 0 := by
            exact_mod_cast hx0_nat
          have hxdvd : (x : ℤ) ∣ (lcmA A : ℤ) := by
            exact_mod_cast Finset.dvd_lcm (hS hx)
          simpa [Int.cast_natCast] using (Int.cast_div hxdvd hx0 :
            ((((lcmA A : ℤ) / (x : ℤ) : ℤ) : ℚ) =
              ((lcmA A : ℤ) : ℚ) / ((x : ℤ) : ℚ)))
        have hsum_cast :
            S.sum (fun x => (lcmA A : ℚ) / (x : ℚ)) =
              S.sum (fun x => ↑(lcmA A / x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hx0 : x ≠ 0 := by
            intro hx0
            exact hA (hS (hx0 ▸ hx))
          rw [Nat.cast_div (K := ℚ)]
          · exact Finset.dvd_lcm (hS hx)
          · exact Nat.cast_ne_zero.2 hx0
        have hzQ' :
            (k : ℚ) * S.sum (fun x => (lcmA A : ℚ) / (x : ℚ)) =
              (z : ℚ) * (lcmA A : ℚ) := by
          simpa [hsum_int_cast, Int.cast_natCast, Int.cast_mul, Nat.cast_mul, Nat.cast_sum,
            Rat.cast_natCast] using congrArg (fun t : ℤ => (t : ℚ)) hz
        simpa [hsum_cast] using hzQ'
      have hmul' :
          (lcmA A : ℚ) * (rec_sum S * (k : ℚ)) = (lcmA A : ℚ) * z := by
        calc
          (lcmA A : ℚ) * (rec_sum S * (k : ℚ))
              = (k : ℚ) * (rec_sum S * (lcmA A : ℚ)) := by ring
          _ = (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) := by rw [hsum]
          _ = (z : ℚ) * (lcmA A : ℚ) := hzQ
          _ = (lcmA A : ℚ) * z := by ring
      exact (mul_right_inj' hA').mp hmul'
  have horth :
      ∀ S : Finset ℕ, S ∈ A.powerset →
        (if (∃ z : ℤ, rec_sum S * (k : ℚ) = z) then (1 : ℕ) else 0 : ℂ) =
          1 / (lcmA A) * (valid_sum_range (lcmA A)).sum (fun h => e (k * h * rec_sum S)) := by
    intro S hS
    have ht : (-((lcmA A : ℕ) : ℤ) / 2 : ℤ) < (lcmA A : ℤ) / 2 := by
      apply Int.ediv_lt_of_lt_mul zero_lt_two
      apply lt_of_lt_of_le
      · rw [Right.neg_neg_iff, Int.natCast_pos]
        exact Nat.pos_iff_ne_zero.2 ((Finset.lcm_ne_zero_iff (s := A) (f := id)).2
          (by intro x hx hx0; exact hA (hx0 ▸ hx)))
      · exact mul_nonneg (Int.ediv_nonneg (Int.natCast_nonneg _) zero_le_two) zero_le_two
    rw [Finset.mem_powerset] at hS
    rw [Nat.cast_one, if_congr (hdiv S hS) rfl rfl, mul_comm (_ : ℂ)]
    rw [← orthogonality ((Finset.lcm_ne_zero_iff (s := A) (f := id)).2
      (by intro x hx hx0; exact hA (hx0 ▸ hx))) rfl ht
      (by simp [valid_sum_range, dumb_subtraction_thing])]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_mul, mul_div_assoc, mul_div_assoc, ← mul_assoc, mul_comm (i : ℝ)]
    congr 2
    rw [rec_sum, Nat.cast_sum, Finset.sum_div, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      intro hn0
      apply hA
      exact hS (hn0 ▸ hn)
    have hlcm0 : ((lcmA A : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.lcm_ne_zero_iff (s := A) (f := id)).2
        (by intro x hx hx0; exact hA (hx0 ▸ hx))
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_one]
    calc
      (((lcmA A / n : ℕ) : ℝ) / (lcmA A : ℝ))
          = (((lcmA A : ℕ) : ℝ) / n) / (lcmA A : ℝ) := by
              rw [Nat.cast_div (K := ℝ)]
              · exact Finset.dvd_lcm (hS hn)
              · exact Nat.cast_ne_zero.2 hn0
      _ = (1 : ℝ) / n := by
        field_simp [hlcm0, show (n : ℝ) ≠ 0 by exact_mod_cast hn0]
  rw [integer_count, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_congr rfl horth, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.prod_one_add, e, AdditiveCharacterGeometricSums.additiveCharacter,
    ← Complex.exp_sum, ← Finset.mul_sum, rec_sum, Rat.cast_sum, mul_sum,
    Rat.cast_div, Rat.cast_one, ← div_eq_mul_one_div, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro S hS
  congr 2
  push_cast
  rw [← Finset.mul_sum]

lemma integer_bound_thing {d : ℤ} (hd₀ : 0 ≤ d) (hd₁ : d ≠ 1) (hd₂ : d < 2) :
    d = 0 := by
  omega

lemma orthog_simp_aux {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
    (valid_sum_range (lcmA A)).sum (fun h => A.prod (fun n => 1 + e (k * h / n))) = lcmA A := by
  have hcount : integer_count A k = 1 := by
    have hfilter :
        A.powerset.filter (fun S => ∃ d : ℤ, rec_sum S * k = d) = {∅} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨hSA, d, hd⟩
        have hkQ : (k : ℚ) ≠ 0 := by
          exact_mod_cast hk
        have hkQ_pos : (0 : ℚ) < k := by
          exact_mod_cast Nat.pos_of_ne_zero hk
        have hd0Q : (0 : ℚ) ≤ (d : ℚ) := by
          have hS_nonneg : (0 : ℚ) ≤ rec_sum S := by
            rw [rec_sum]
            exact Finset.sum_nonneg (fun i _ ↦ by positivity)
          have hSk_nonneg : (0 : ℚ) ≤ rec_sum S * k :=
            mul_nonneg hS_nonneg (show (0 : ℚ) ≤ k by exact_mod_cast Nat.zero_le k)
          rw [hd] at hSk_nonneg
          exact hSk_nonneg
        have hd0 : 0 ≤ d := by
          exact_mod_cast hd0Q
        have hdlt2Q : (d : ℚ) < 2 := by
          have hrec_le : rec_sum S ≤ rec_sum A := by
            rw [rec_sum, rec_sum]
            exact Finset.sum_le_sum_of_subset_of_nonneg hSA (fun i _ _ ↦ by positivity)
          have hrec_lt : rec_sum S < 2 / k := hrec_le.trans_lt hA'
          exact (by
            simpa [hd] using (_root_.lt_div_iff₀ hkQ_pos).mp hrec_lt : (d : ℚ) < 2)
        have hdlt2 : d < 2 := by
          exact_mod_cast hdlt2Q
        have hdne1 : d ≠ 1 := by
          intro hd1
          apply hS S hSA
          apply (eq_div_iff hkQ).2
          simpa [hd1] using hd
        have hdzero : d = 0 := integer_bound_thing hd0 hdne1 hdlt2
        have hrec0 : rec_sum S = 0 := by
          have hmul0 : rec_sum S * (k : ℚ) = 0 := by
            simpa [hdzero] using hd
          exact (mul_eq_zero.mp hmul0).resolve_right hkQ
        have hS0 : 0 ∉ S := by
          intro h0S
          exact hA (hSA h0S)
        exact (rec_sum_eq_zero_iff hS0).1 hrec0
      · intro hSe
        subst hSe
        exact ⟨by simp, 0, by simp [rec_sum]⟩
    simp [integer_count, hfilter]
  have hlcm0 : ((lcmA A : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.lcm_ne_zero_iff (s := A) (f := id)).2
      (by intro x hx hx0; exact hA (hx0 ▸ hx))
  apply (div_eq_one_iff_eq hlcm0).mp
  rw [div_eq_mul_one_div, mul_comm, ← orthog_rat hA hk, hcount]
  norm_num

/-- Lemma 4.12. -/
lemma orthog_simp {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
    (valid_sum_range (lcmA A)).sum
        (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) =
      lcmA A := by
  simpa using congrArg Complex.re (orthog_simp_aux hA hk hS hA')

/-- Lemma 4.13. -/
lemma orthog_simp2 {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k)
    (hA'' : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ)) :
    (j A).sum (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) ≤ -2 ^ (A.card - 1 : ℤ) := by
  have hlcm0 := (Finset.lcm_ne_zero_iff (s := A) (f := id)).2
    (by intro x hx hx0; exact hA (hx0 ▸ hx))
  have he_zero : e 0 = 1 := by
    simpa [e, AdditiveCharacterGeometricSums.additiveCharacter] using Complex.exp_zero
  rw [j, Finset.sum_erase_eq_sub (zero_mem_valid_sum_range hlcm0), orthog_simp hA hk hS hA']
  simp only [Int.cast_zero, zero_div, mul_zero, he_zero, Finset.prod_const]
  rw [sub_le_iff_le_add, neg_add_eq_sub]
  refine hA''.trans ?_
  rw [le_sub_iff_add_le]
  have hpow :
      (2 : ℝ) ^ (A.card - 1 : ℤ) + (2 : ℝ) ^ (A.card - 1 : ℤ) =
        ((1 + 1 : ℂ) ^ A.card).re := by
    calc
      (2 : ℝ) ^ (A.card - 1 : ℤ) + (2 : ℝ) ^ (A.card - 1 : ℤ)
          = (2 : ℝ) ^ (A.card - 1 : ℤ) * 2 := by ring
      _ = (2 : ℝ) ^ ((A.card - 1 : ℤ) + 1) := by
        rw [zpow_add₀ two_ne_zero, zpow_one]
      _ = (2 : ℝ) ^ (A.card : ℤ) := by simp
      _ = (2 : ℝ) ^ A.card := by rw [zpow_natCast]
      _ = ((2 : ℂ) ^ A.card).re := by
        simpa [Complex.ofReal_pow] using (Complex.ofReal_re ((2 : ℝ) ^ A.card)).symm
      _ = ((1 + 1 : ℂ) ^ A.card).re := by norm_num
  exact le_of_eq hpow

/-- Lemma 4.14. -/
lemma majorarcs_disjoint {A : Finset ℕ} {k : ℕ} {K : ℝ} (hk : k ≠ 0) (hA : K < lcmA A) :
    (Set.univ : Set ℤ).PairwiseDisjoint (major_arc_at A k K) := by
  intro t₁ _ t₂ _ ht
  change Disjoint (major_arc_at A k K t₁) (major_arc_at A k K t₂)
  rw [Finset.disjoint_left]
  by_cases hK : K < 0
  · intro h hh _
    rw [major_arc_at_of_neg hk hK] at hh
    simp at hh
  · intro h hh₁ hh₂
    have hK' : 0 ≤ K := le_of_not_gt hK
    have hh₁' :=
      (mem_major_arc_at' (A := A) (k := k) (K := K) (t := t₁) hk h).1 hh₁
    have hh₂' :=
      (mem_major_arc_at' (A := A) (k := k) (K := K) (t := t₂) hk h).1 hh₂
    have hbound : |((t₁ : ℝ) - t₂) * (lcmA A : ℝ)| ≤ K := by
      rw [sub_mul]
      refine le_trans (abs_sub_le _ ((h : ℝ) * k) _) ?_
      rw [abs_sub_comm]
      refine le_trans (add_le_add hh₁'.2 hh₂'.2) ?_
      nlinarith
    have hLnonneg : 0 ≤ (lcmA A : ℝ) := by positivity
    have hbound' : (|t₁ - t₂| : ℝ) * (lcmA A : ℝ) ≤ K := by
      simpa [Int.cast_sub, Int.cast_abs, abs_mul, abs_of_nonneg hLnonneg] using hbound
    have ht' : 1 ≤ |t₁ - t₂| := by
      rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
    have ht'' : (1 : ℝ) ≤ (|t₁ - t₂| : ℝ) := by
      exact_mod_cast ht'
    have hge : (lcmA A : ℝ) ≤ (|t₁ - t₂| : ℝ) * (lcmA A : ℝ) := by
      nlinarith
    exact (not_lt.mpr hbound') (lt_of_lt_of_le hA hge)

/-- Lemma 4.15. -/
lemma useful_rewrite {A : Finset ℕ} {θ : ℝ} :
    (A.prod (fun n => 1 + e (θ / n))).re =
      2 ^ A.card * cos (π * θ * rec_sum A) * A.prod (fun n => cos (π * θ / n)) := by
  simp only [one_add_e, Finset.prod_mul_distrib, ← mul_div_assoc]
  rw [Finset.prod_const, ← Nat.cast_two, ← Nat.cast_pow, ← Complex.ofReal_prod]
  have houter :
      ((((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)) *
          ↑(∏ i ∈ A, cos (π * θ / ↑i))).re =
        (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)).re *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
    simpa using
      (Complex.re_mul_ofReal
        (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2))
        (∏ i ∈ A, cos (π * θ / ↑i)))
  have hinner :
      (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)).re =
        (2 ^ A.card : ℝ) * (∏ x ∈ A, e (θ / ↑x / 2)).re := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Complex.re_mul_ofReal
        (∏ x ∈ A, e (θ / ↑x / 2))
        (2 ^ A.card : ℝ))
  have hsum : A.sum (fun n => θ / (n : ℝ)) = θ * rec_sum A := by
    rw [rec_sum, Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [Rat.cast_natCast, div_eq_mul_inv, mul_comm]
  calc
    ((((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)) *
        ↑(∏ i ∈ A, cos (π * θ / ↑i))).re
        = (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)).re *
            ∏ i ∈ A, cos (π * θ / ↑i) := houter
    _ = ((2 ^ A.card : ℝ) * (∏ x ∈ A, e (θ / ↑x / 2)).re) *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
      rw [hinner]
    _ = ((2 ^ A.card : ℝ) * (e (∑ x ∈ A, θ / ↑x / 2)).re) *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
      simp_rw [e, AdditiveCharacterGeometricSums.additiveCharacter]
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [← Finset.mul_sum]
    _ = ((2 ^ A.card : ℝ) * cos ((∑ x ∈ A, θ / ↑x) * π)) *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
      rw [← Finset.sum_div,
        (show (e ((∑ x ∈ A, θ / ↑x) / 2)).re =
          Real.cos ((∑ x ∈ A, θ / ↑x) * Real.pi) by
          simpa [e, AdditiveCharacterGeometricSums.additiveCharacter, mul_assoc, mul_left_comm,
            mul_comm, two_mul] using
            Complex.exp_ofReal_mul_I_re ((∑ x ∈ A, θ / ↑x) * Real.pi))]
    _ = ((2 ^ A.card : ℝ) * cos (π * θ * rec_sum A)) *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
      rw [hsum]
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = 2 ^ A.card * cos (π * θ * rec_sum A) * ∏ i ∈ A, cos (π * θ / ↑i) := by
      ring

lemma prod_major_arc_eq {α : Type*} [CommMonoid α] {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hA : 0 ∉ A) (hk : k ≠ 0) (hA' : K < lcmA A) {f : ℤ → α} :
    (major_arc A k K).prod f = (my_range' A k K).prod (fun t => (major_arc_at A k K t).prod f) := by
  rw [major_arc_eq_union hA hk]
  have hdisj : Set.PairwiseDisjoint (↑(my_range' A k K) : Set ℤ) (major_arc_at A k K) :=
    Set.PairwiseDisjoint.subset (majorarcs_disjoint hk hA') (by simp)
  simpa using
    (Finset.prod_biUnion (s := my_range' A k K) (t := major_arc_at A k K) (f := f) hdisj)

def jt (A : Finset ℕ) (k : ℕ) (K : ℝ) (t : ℝ) : Finset ℤ :=
  (my_range (K / (2 * (k : ℝ)))).filter fun h => ∃ i ∈ j A, (i : ℝ) - t * (lcmA A) / k = h

lemma prod_major_arc_at_eq {α : Type*} [CommMonoid α] {A : Finset ℕ} {k : ℕ} {K : ℝ} {t}
    {f : ℤ → α} (hk : k ∣ lcmA A) :
    (major_arc_at A k K t).prod f = (jt A k K t).prod (fun r => f (t * lcmA A / k + r)) := by
  by_cases hk0 : k = 0
  · have hlcm : lcmA A = 0 := Nat.zero_dvd.mp (by simpa [hk0] using hk)
    simp [major_arc_at, jt, j, valid_sum_range, hk0, hlcm]
  have hdiv : (k : ℤ) ∣ t * lcmA A := by
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hk) t
  let c : ℤ := t * lcmA A / k
  have hc : ((c : ℤ) : ℝ) = t * (lcmA A : ℝ) / k := by
    calc
      ((c : ℤ) : ℝ) = (((t * lcmA A) / k : ℤ) : ℝ) := by rfl
      _ = (((t * lcmA A : ℤ) : ℝ) / ((k : ℤ) : ℝ)) := by
        rw [Int.cast_div hdiv (by exact_mod_cast hk0)]
      _ = (((t * lcmA A : ℤ) : ℝ) / (k : ℝ)) := by simp
      _ = ((((t : ℤ) : ℝ) * (lcmA A : ℝ)) / (k : ℝ)) := by simp
      _ = t * (lcmA A : ℝ) / k := by simp
  apply Eq.symm
  refine Finset.prod_bij (fun h _ => c + h) ?_ ?_ ?_ ?_
  · intro a ha
    rw [jt, Finset.mem_filter] at ha
    rw [mem_major_arc_at]
    rcases ha with ⟨ha, i, hi, hia⟩
    have hbounda : |(a : ℝ)| ≤ K / (2 * k) := (mem_my_range_iff).1 ha
    have hicast : (i : ℝ) = ((c + a : ℤ) : ℝ) := by
      calc
        (i : ℝ) = t * (lcmA A : ℝ) / k + a := by linarith
        _ = (c : ℝ) + a := by rw [hc]
        _ = ((c + a : ℤ) : ℝ) := by norm_num
    have hica : i = c + a := by
      exact Int.cast_inj.mp hicast
    constructor
    · simpa [hica] using hi
    · have hbound : |(c : ℝ) + a - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) := by
        rw [hc]
        simpa using hbounda
      simpa [Int.cast_add] using hbound
  · intro a₁ h₁ a₂ h₂ h
    exact add_left_cancel h
  · intro b hb
    refine ⟨b - c, ?_, ?_⟩
    · rw [mem_major_arc_at] at hb
      rw [jt, Finset.mem_filter]
      rcases hb with ⟨hbj, hbbound⟩
      constructor
      · refine (mem_my_range_iff).2 ?_
        have hbc : (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - t * (lcmA A : ℝ) / k := by
          calc
            (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - c := by norm_num
            _ = (b : ℝ) - t * (lcmA A : ℝ) / k := by rw [hc]
        simpa [hbc] using hbbound
      · refine ⟨b, hbj, ?_⟩
        calc
          (b : ℝ) - t * (lcmA A : ℝ) / k = (b : ℝ) - c := by rw [hc]
          _ = (b - c : ℤ) := by norm_num
    · simp [c]
  · intro a ha
    rfl

lemma majorarcs_at {K : ℝ} {A : Finset ℕ} {k : ℕ}
    (hk : k ≠ 0) (hk' : k ∣ lcmA A) {t : ℤ} :
    (major_arc_at A k K t).sum (fun h => (A.prod (fun n => 1 + e (↑k * ↑h / ↑n))).re) =
      2 ^ A.card *
        (jt A k K t).sum
          (fun r => cos (π * k * r * rec_sum A) * A.prod (fun n => cos (π * (k * r) / n))) := by
  have hdivk : (k : ℤ) ∣ t * lcmA A := by
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hk') t
  have hsum :
      (major_arc_at A k K t).sum (fun h => (A.prod (fun n => 1 + e (↑k * ↑h / ↑n))).re) =
        (jt A k K t).sum
          (fun r => (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re) := by
    let c : ℤ := t * lcmA A / k
    have hc : c = t * lcmA A / k := rfl
    refine Eq.symm <| Finset.sum_bij (fun h _ => c + h) ?_ ?_ ?_ ?_
    · intro a ha
      rw [jt, Finset.mem_filter] at ha
      rw [mem_major_arc_at]
      rcases ha with ⟨ha, i, hi, hia⟩
      have hbounda : |(a : ℝ)| ≤ K / (2 * k) := (mem_my_range_iff).1 ha
      have hicast : (i : ℝ) = ((c + a : ℤ) : ℝ) := by
        calc
          (i : ℝ) = t * (lcmA A : ℝ) / k + a := by linarith
          _ = (c : ℝ) + a := by
            rw [hc]
            rw [Int.cast_div hdivk (by exact_mod_cast hk)]
            simp
          _ = ((c + a : ℤ) : ℝ) := by norm_num
      have hica : i = c + a := Int.cast_inj.mp hicast
      constructor
      · simpa [hica] using hi
      · have hbound : |(c : ℝ) + a - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) := by
          rw [hc]
          rw [Int.cast_div hdivk (by exact_mod_cast hk)]
          simpa using hbounda
        simpa [Int.cast_add] using hbound
    · intro a₁ h₁ a₂ h₂ h
      exact add_left_cancel h
    · intro b hb
      refine ⟨b - c, ?_, ?_⟩
      · rw [mem_major_arc_at] at hb
        rw [jt, Finset.mem_filter]
        rcases hb with ⟨hbj, hbbound⟩
        constructor
        · refine (mem_my_range_iff).2 ?_
          have hbc : (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - t * (lcmA A : ℝ) / k := by
            calc
              (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - c := by norm_num
              _ = (b : ℝ) - t * (lcmA A : ℝ) / k := by
                rw [hc]
                rw [Int.cast_div hdivk (by exact_mod_cast hk)]
                simp
          simpa [hbc] using hbbound
        · refine ⟨b, hbj, ?_⟩
          calc
            (b : ℝ) - t * (lcmA A : ℝ) / k = (b : ℝ) - c := by
              rw [hc]
              rw [Int.cast_div hdivk (by exact_mod_cast hk)]
              simp
            _ = (b - c : ℤ) := by norm_num
      · simp [hc]
    · intro a ha
      simp [hc]
  rw [hsum]
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  calc
    ∑ r ∈ jt A k K t, (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re
        =
          ∑ r ∈ jt A k K t,
            2 ^ A.card *
              (cos (π * k * r * rec_sum A) * A.prod (fun n => cos (π * (k * r) / n))) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hprod :
                A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n)) =
                  A.prod (fun n => 1 + e (↑k * ↑r / ↑n)) := by
              refine Finset.prod_congr rfl ?_
              intro n hn
              by_cases hn0 : n = 0
              · subst hn0
                simp
              · have hdivn : (n : ℤ) ∣ t * lcmA A := by
                  exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr <| Finset.dvd_lcm hn) t
                have hnZ : (n : ℤ) ≠ 0 := by
                  exact_mod_cast hn0
                have hnR : (n : ℝ) ≠ 0 := by
                  exact_mod_cast hn0
                have harg :
                    (↑k : ℝ) * ↑(t * lcmA A / k + r) / ↑n =
                      (((t * lcmA A / n : ℤ) : ℤ) : ℝ) + (↑k * ↑r / ↑n) := by
                  calc
                    (↑k : ℝ) * ↑(t * lcmA A / k + r) / ↑n
                        = ((↑k : ℝ) * ↑(t * lcmA A / k) + ↑k * ↑r) / ↑n := by
                            rw [Int.cast_add, mul_add]
                    _ = (↑k : ℝ) * ↑(t * lcmA A / k) / ↑n + ↑k * ↑r / ↑n := by
                          rw [add_div]
                    _ = ((((t * lcmA A : ℤ) : ℝ) / ↑n)) + ↑k * ↑r / ↑n := by
                          congr 1
                          rw [Int.cast_div_charZero hdivk]
                          field_simp [hkR, hnR]
                          simp [mul_comm, mul_left_comm]
                    _ = ((((t * lcmA A / n : ℤ) : ℤ) : ℝ)) + ↑k * ↑r / ↑n := by
                          rw [Int.cast_div_charZero hdivn]
                          simp
                calc
                  1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n)
                      = 1 + e ((((t * lcmA A / n : ℤ) : ℤ) : ℝ) + (↑k * ↑r / ↑n)) := by
                          rw [harg]
                  _ = 1 + e ((((t * lcmA A / n : ℤ) : ℤ) : ℝ)) * e (↑k * ↑r / ↑n) := by
                        rw [e_add]
                  _ = 1 + e (↑k * ↑r / ↑n) := by
                        rw [e_int, one_mul]
            calc
              (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re
                  = (A.prod (fun n => 1 + e (↑k * ↑r / ↑n))).re := by rw [hprod]
              _ = 2 ^ A.card * cos (π * ((k : ℝ) * r) * rec_sum A) *
                    A.prod (fun n => cos (π * ((k : ℝ) * r) / n)) := by
                    simpa using (useful_rewrite (A := A) (θ := (k : ℝ) * r))
              _ = 2 ^ A.card *
                    (cos (π * k * r * rec_sum A) * A.prod (fun n => cos (π * (k * r) / n))) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = 2 ^ A.card *
          (jt A k K t).sum
            (fun r => cos (π * k * r * rec_sum A) * A.prod (fun n => cos (π * (k * r) / n))) := by
          rw [Finset.mul_sum]

/-- Lemma 4.16. -/
lemma majorarcs {M K : ℝ} {A : Finset ℕ} (hM : ∀ n : ℕ, n ∈ A → M ≤ n) (hK : 0 < K)
    (hKM : K < M) {k : ℕ} (hk' : k ∣ lcmA A) (hA₁ : (2 : ℝ) - k / M ≤ k * rec_sum A)
    (hA₂ : (k : ℝ) * rec_sum A ≤ 2) (hA₃ : A.Nonempty) :
    (0 : ℝ) ≤ (major_arc A k K).sum (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) := by
  have hA : 0 ∉ A := by
    intro h0
    have hM0 : M ≤ 0 := by simpa using hM 0 h0
    linarith
  have hKlcm : K < lcmA A := by
    apply hKM.trans_le
    obtain ⟨n, hn⟩ := hA₃
    refine (hM n hn).trans ?_
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff (s := A) (f := id)).2
        (by intro x hx hx0; exact hA (hx0 ▸ hx)))) (Finset.dvd_lcm hn)
  have hk : k ≠ 0 := ne_zero_of_dvd_ne_zero ((Finset.lcm_ne_zero_iff (s := A) (f := id)).2
    (by intro x hx hx0; exact hA (hx0 ▸ hx))) hk'
  have hdisj : Set.PairwiseDisjoint (↑(my_range' A k K) : Set ℤ) (major_arc_at A k K) :=
    Set.PairwiseDisjoint.subset (majorarcs_disjoint hk hKlcm) (by simp)
  rw [major_arc_eq_union hA hk, Finset.sum_biUnion hdisj]
  simp only [majorarcs_at hk hk', ← Finset.mul_sum, jt, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_nonneg (pow_nonneg zero_le_two _) (Finset.sum_nonneg ?_)
  intro r hr
  rw [mem_my_range_iff] at hr
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ?_ ?_)
  · have hcos :
      cos (π * k * r * rec_sum A) = cos (π * r * (2 - k * rec_sum A)) := by
        calc
          cos (π * k * r * rec_sum A)
              = cos (π * r * (k * rec_sum A - 2)) := by
                  rw [mul_sub, mul_mul_mul_comm, ← mul_assoc, mul_comm π r, mul_assoc ↑r π,
                    mul_comm π 2, Real.cos_sub_int_mul_two_pi]
          _ = cos (-(π * r * (k * rec_sum A - 2))) := by rw [Real.cos_neg]
          _ = cos (π * r * (2 - k * rec_sum A)) := by ring_nf
    rw [hcos]
    apply Real.cos_nonneg_of_mem_Icc
    rw [Set.mem_Icc]
    apply abs_le.mp
    have hA₂' : 0 ≤ 2 - (k : ℝ) * (rec_sum A : ℝ) := sub_nonneg.mpr hA₂
    have hA₁' : 2 - (k : ℝ) * (rec_sum A : ℝ) ≤ (k : ℝ) / M := by linarith
    rw [abs_mul, abs_mul, abs_of_nonneg pi_pos.le, abs_of_nonneg hA₂']
    refine (mul_le_mul_of_nonneg_left hA₁' (mul_nonneg pi_pos.le (abs_nonneg _))).trans ?_
    have hM' : 0 < M := hK.trans hKM
    have hkpos : 0 < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hrk : |(r : ℝ)| * (k : ℝ) ≤ K / 2 := by
      calc
        |(r : ℝ)| * (k : ℝ) ≤ (K / (2 * (k : ℝ))) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hr hkpos.le
        _ = K / 2 := by
          field_simp [hkpos.ne']
    have hratio : |(r : ℝ)| * (k : ℝ) / M ≤ 1 / 2 := by
      apply (div_le_iff₀ hM').2
      linarith [hrk, hKM]
    calc
      π * |(r : ℝ)| * (k / M) = π * ((|(r : ℝ)| * (k : ℝ)) / M) := by ring
      _ ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hratio pi_pos.le
      _ = π / 2 := by ring
  · apply Finset.prod_nonneg
    intro n hn
    apply Real.cos_nonneg_of_mem_Icc
    rw [Set.mem_Icc]
    apply abs_le.mp
    have h2k : 0 < 2 * (k : ℝ) := by
      exact mul_pos zero_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hk)
    replace hr := ((le_div_iff₀ h2k).1 hr).trans (hKM.le.trans (hM n hn))
    have hnpos : 0 < |(n : ℝ)| := by
      apply abs_pos_of_pos
      exact hK.trans (hKM.trans_le (hM n hn))
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg pi_pos.le, div_le_div_iff₀ hnpos zero_lt_two,
      Nat.abs_cast k, Nat.abs_cast n, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ pi_pos.le
    convert hr using 1
    ring_nf

lemma minor_lbound {M : ℝ} {A : Finset ℕ} {K : ℝ} {k : ℕ}
    (hM : ∀ n ∈ A, M ≤ ↑n) (hK : 0 < K) (hKM : K < M) (hkA : k ∣ lcmA A) (hk : k ≠ 0)
    (hA₁ : (2 : ℝ) - k / M ≤ k * rec_sum A) (hA₂ : (k : ℝ) * rec_sum A < 2)
    (hA₃ : A.Nonempty) (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k)
    (hA₄ : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ)) :
    1 / 2 ≤ (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k)) := by
  have hA : 0 ∉ A := by
    intro h0
    have hM0 : M ≤ 0 := by simpa using hM 0 h0
    linarith
  have hkQ : (0 : ℚ) < k := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have hA₂' : rec_sum A < 2 / k := by
    have hA₂'' : (k : ℚ) * rec_sum A < 2 := by
      exact_mod_cast hA₂
    exact (_root_.lt_div_iff₀ hkQ).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA₂'')
  let f : ℤ → ℝ := fun h => (A.prod (fun n => 1 + e (k * h / n))).re
  have hmajor : 0 ≤ (major_arc A k K).sum f := by
    simpa [f] using
      (majorarcs (M := M) (K := K) (A := A) hM hK hKM hkA hA₁ hA₂.le hA₃)
  have hsubset : major_arc A k K ⊆ j A := by
    intro h hh
    rw [major_arc, Finset.mem_filter] at hh
    exact hh.1
  have hsplit :
      (j A \ major_arc A k K).sum f + (major_arc A k K).sum f = (j A).sum f := by
    simpa [f] using (Finset.sum_sdiff hsubset (f := f))
  have hminor_re :
      (j A \ major_arc A k K).sum f ≤ -2 ^ (A.card - 1 : ℤ) := by
    have htotal : (j A).sum f ≤ -2 ^ (A.card - 1 : ℤ) :=
      orthog_simp2 hA hk hS hA₂' hA₄
    rw [← hsplit] at htotal
    linarith
  have hpoint :
      ∀ h ∈ j A \ major_arc A k K, -((2 : ℝ) ^ A.card * cos_prod A (h * k)) ≤ f h := by
    intro h hh
    let z : ℂ := A.prod (fun n => 1 + e (k * h / n))
    have hzre : |z.re| ≤ ‖z‖ := by
      simpa using Complex.abs_re_le_norm z
    have hznorm : ‖z‖ = (2 : ℝ) ^ A.card * cos_prod A (h * k) := by
      dsimp [z]
      rw [norm_prod]
      simp_rw [abs_one_add_e]
      rw [Finset.prod_mul_distrib]
      simp [cos_prod, Int.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm]
    have hbound : -((2 : ℝ) ^ A.card * cos_prod A (h * k)) ≤ z.re := by
      rw [← hznorm]
      exact (abs_le.mp hzre).1
    simpa [f, z] using hbound
  have hminor_cp :
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k))) ≤
        (j A \ major_arc A k K).sum f := by
    calc
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k)))
          = (j A \ major_arc A k K).sum (fun h => -((2 : ℝ) ^ A.card * cos_prod A (h * k))) := by
              rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ ≤ (j A \ major_arc A k K).sum (fun h => f h) := by
            exact Finset.sum_le_sum hpoint
      _ = (j A \ major_arc A k K).sum f := rfl
  have hcard1 : 1 ≤ A.card := Finset.one_le_card.mpr hA₃
  have hpow : (2 : ℝ) ^ (A.card - 1 : ℤ) = (2 : ℝ) ^ A.card / 2 := by
    rw [zpow_sub₀ two_ne_zero]
    simp
  have hfinal :
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k))) ≤
        -(2 : ℝ) ^ (A.card - 1 : ℤ) := by
    exact le_trans hminor_cp hminor_re
  rw [hpow] at hfinal
  have hpowpos : 0 < (2 : ℝ) ^ A.card := pow_pos zero_lt_two _
  nlinarith
