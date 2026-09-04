module

public import SolveMath.Corpus.NumberTheory.UnitFractionSubsumResults.TwoValues

@[expose] public section

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter _root_.Finset Real
open _root_.Finset

lemma force_good_properties_three_values_case
    (N : ℕ) (c : ℝ) (A : Finset ℕ) (x1 x2 x3 : ℕ) (f : ℕ → ℤ)
    (hA : A ⊆ Finset.range (N + 1))
    (hlarge3 : 0 < log (log N))
    (hnum : (102 / 100 : ℝ) ≤ 3 * c - ((1 : ℝ) / 500 + (1 : ℝ) / 500 + (1 : ℝ) / 500))
    (hrecN :
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((Finset.range (N + 1)).filter
                (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
              (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N))
    (hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N))
    (hS1 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (hS2 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (hS3 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x3).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (h21 : f x2 ≠ f x1)
    (h32 : f x3 ≠ f x2)
    (h31 : f x3 ≠ f x1)
    (hclose21 : |(f x2 : ℝ) - f x1| ≤ N)
    (hclose32 : |(f x3 : ℝ) - f x2| ≤ N)
    (hclose31 : |(f x3 : ℝ) - f x1| ≤ N) :
    False := by
  let F1 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1
  let F2 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2
  let F3 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x3
  let S1 := F1.sum fun r : ℕ => (1 : ℝ) / r
  let S2 := F2.sum fun r : ℕ => (1 : ℝ) / r
  let S3 := F3.sum fun r : ℕ => (1 : ℝ) / r
  let S12 := (F1 ∩ F2).sum fun r : ℕ => (1 : ℝ) / r
  let S23 := (F2 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  let S13 := (F1 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  let S123 := (F1 ∩ F2 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  have hsum1 : 3 * c * log (log N) ≤ S1 + S2 + S3 := by
    have hS1' : c * log (log N) ≤ S1 := by simpa [S1, F1] using hS1
    have hS2' : c * log (log N) ≤ S2 := by simpa [S2, F2] using hS2
    have hS3' : c * log (log N) ≤ S3 := by simpa [S3, F3] using hS3
    nlinarith
  have hunion :
      S1 + S2 + S3 =
        (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) + S12 + S13 + S23 - S123 := by
    dsimp [S1, S2, S3, S12, S13, S23, S123]
    simpa [F1, F2, F3, Finset.union_assoc, Finset.inter_assoc, Finset.inter_left_comm,
      Finset.filter_inter, Finset.inter_filter, Finset.inter_self, Finset.filter_filter,
      and_assoc, and_left_comm, and_right_comm, add_comm, add_left_comm, add_assoc] using
      (sum_add_sum_add_sum (A := F1) (B := F2) (C := F3) (f := fun r : ℕ => (1 : ℝ) / r))
  have hsum2 : (S1 + S2 + S3) - (S12 + S13 + S23) ≤ ppower_rec_sum A := by
    have h123nonneg : 0 ≤ S123 := by
      dsimp [S123]
      refine Finset.sum_nonneg ?_
      intro i hi
      rw [one_div_nonneg]
      exact Nat.cast_nonneg i
    have hunion_le :
        (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) ≤ ppower_rec_sum A := by
      rw [ppower_rec_sum]
      push_cast
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro q hq
        rw [Finset.mem_union, Finset.mem_union] at hq
        rcases hq with hq | hq
        · rcases hq with hq | hq
          · exact Finset.mem_of_mem_filter q hq
          · exact Finset.mem_of_mem_filter q hq
        · exact Finset.mem_of_mem_filter q hq
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    calc
      (S1 + S2 + S3) - (S12 + S13 + S23) =
          ((F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) + S12 + S13 + S23 - S123) -
            (S12 + S13 + S23) := by rw [hunion]
      _ ≤ (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) := by
          nlinarith
      _ ≤ ppower_rec_sum A := hunion_le
  have hsum3 :
      S12 + S23 + S13 ≤
        (((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500)) * log (log N) := by
    have h12 :
        S12 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S12, F1, F2]
      refine le_trans ?_ (le_of_lt (hrecN (f x2) (f x1) h21 hclose21))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
            rw [Finset.mem_range]
            exact lt_of_le_of_lt
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
              (by
                rw [← Finset.mem_range]
                exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    have h23 :
        S23 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S23, F2, F3]
      refine le_trans ?_ (le_of_lt (hrecN (f x3) (f x2) h32 hclose32))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
            rw [Finset.mem_range]
            exact lt_of_le_of_lt
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
              (by
                rw [← Finset.mem_range]
                exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    have h13 :
        S13 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S13, F1, F3]
      refine le_trans ?_ (le_of_lt (hrecN (f x3) (f x1) h31 hclose31))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
            rw [Finset.mem_range]
            exact lt_of_le_of_lt
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
              (by
                rw [← Finset.mem_range]
                exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    nlinarith
  have hsum5 : ¬ ((501 / 500 : ℝ) * log (log N) < ((102 : ℝ) / 100) * log (log N)) := by
    rw [not_lt]
    calc
      (((102 : ℝ) / 100) * log (log N)) ≤
          (3 * c - (((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500))) *
            log (log N) := by
              exact mul_le_mul_of_nonneg_right hnum (le_of_lt hlarge3)
      _ = 3 * c * log (log N) -
            ((((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500)) * log (log N)) := by
              ring
      _ ≤ (S1 + S2 + S3) - (S12 + S13 + S23) := by
              nlinarith [hsum1, hsum3]
      _ ≤ ppower_rec_sum A := hsum2
      _ ≤ (501 / 500 : ℝ) * log (log N) := hsum4
  apply hsum5
  exact mul_lt_mul_of_pos_right (by norm_num) hlarge3

theorem force_good_properties :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M ≤ N → (N : ℝ) ≤ M ^ 2 → 0 ∉ A →
      (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
      (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A q) →
      ((∃ B ⊆ A, rec_sum A ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N)) ∨
        good_condition A (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) ((M : ℝ) / log N)
          (M / (2 * (log N) ^ (1 / 100 : ℝ)))) := by
  classical
  let c := (35 : ℝ) / 100
  have hthirdpos : (0 : ℝ) < 1 / 3 := by
    norm_num1
  filter_upwards
    [ eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((2 : ℝ) / (1 / 2)))
    , yet_another_large_N
    , yet_another_large_N'
    , rec_pp_sum_close
    , find_good_x
    , explicit_mertens2
    , div_bound_useful_version hthirdpos ] with
    N hlarge hlarge0 hlarge4 hlargeNs hlarge5 hrecN hgoodx hmertens hdiv
    M A hA h0M hMN hNM h0A hMA hreg hrecA hreclocal
  dsimp at hlarge0
  have hlarge3 : 0 < log (log N) := by
    refine lt_of_lt_of_le ?_ hlarge4
    norm_num1
  have hlarge1 : 1 ≤ M * N ^ ((-2 : ℝ) / log (log N)) := by
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_trans zero_lt_one hlarge)
    have hexp : (2 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      have hlarge4' := hlarge4
      norm_num at hlarge4'
      refine (div_le_iff₀ hlarge3).2 ?_
      nlinarith
    have hpow : (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ M := by
      calc
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast le_of_lt hlarge) hexp
        _ ≤ M := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_iff.mpr ⟨le_of_lt h0M, hNM⟩
    have hneg : (-2 : ℝ) / log (log N) = -((2 : ℝ) / log (log N)) := by
      ring
    rw [hneg, Real.rpow_neg, div_eq_mul_inv]
    · exact (one_le_div (Real.rpow_pos_of_pos hNpos _)).2 hpow
    · exact Nat.cast_nonneg N
  have hlarge2 : M * N ^ ((-2 : ℝ) / log (log N)) ≤ N := by
    have hrpow : N ^ ((-2 : ℝ) / log (log N)) ≤ (1 : ℝ) := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast le_of_lt hlarge
      · apply div_nonpos_of_nonpos_of_nonneg
        · rw [neg_nonpos]
          exact zero_le_two
        · exact le_of_lt hlarge3
    calc
      _ ≤ M := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hrpow h0M.le
      _ ≤ N := hMN
  refine or_iff_not_imp_left.2 ?_
  intro hnoB
  rw [good_condition]
  intro t I hI
  refine or_iff_not_imp_left.2 ?_
  intro hP
  by_cases hzI : (0 : ℤ) ∈ I
  · refine ⟨0, hzI, ?_⟩
    intro q hq
    exact dvd_zero (q : ℤ)
  have hIcard0 :
      (I.card : ℤ) =
        ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
    exact force_good_properties_hIcard0 N M t I hI h0M
  have hIcardn0 : I.card ≠ 0 := by
    exact force_good_properties_hIcardn0 N M t I hI hlarge1
  have hIcard' : (I.card : ℝ) ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1 := by
    exact force_good_properties_hIcard' N M t I hIcard0
  have hIcard'' : (I.card : ℝ) ≤ 2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
    exact force_good_properties_hIcard'' N M I hIcard' hlarge1
  have hlarge9 :
      (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) <
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) := by
    exact force_good_properties_hlarge9 N M I hlarge h0M hlargeNs hIcard'' hIcardn0
  have hIclose' : ∀ x ∈ I, ∀ y ∈ I, (|x - y| : ℝ) ≤ N := by
    exact force_good_properties_hIclose' N M t I hI hlarge2
  have hIclose : ∀ x ∈ I, ∀ y ∈ I, Int.natAbs (x - y) ≤ N := by
    exact force_good_properties_hIclose N I hIclose'
  let A_I := A.filter fun n : ℕ => ∃ x ∈ I, (n : ℤ) ∣ x
  let D := interval_rare_ppowers I A (M / (2 * log N ^ ((1 : ℝ) / 100)))
  let E := (ppowers_in_set A).filter
    fun q : ℕ => 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q
  let K := M / (2 * log N ^ ((1 : ℝ) / 100))
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨x1, hx1⟩
    have hDE : D ⊆ E := by
      intro q hq
      rw [Finset.mem_filter]
      refine ⟨by simpa [interval_rare_ppowers] using
        (Finset.filter_subset _ (ppowers_in_set A) hq), ?_⟩
      refine good_d N M (1 / (2 * log N ^ ((1 : ℝ) / 100))) A hA h0M hMA ?_ I q ?_
      · intro q hq'
        rw [two_mul, one_div, ← inv_div_left, add_halves, ← Real.rpow_neg]
        · exact hreclocal q hq'
        · exact le_of_lt hlarge0
      · rw [← div_eq_mul_one_div]
        exact hq
    have hlocal :
        ∀ q ∈ E, ∃ x ∈ I, ((q : ℤ) ∣ x) ∧
          c * log (log N) ≤
            ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ x).sum
              (fun r : ℕ => (1 / r : ℝ)) := by
      intro q hq
      specialize hgoodx M A hA h0M hMN h0A hMA hreg t I q
        (Finset.mem_of_mem_filter q hq) hI
      apply hgoodx
      rw [Finset.mem_filter] at hq
      exact hq.2
    clear hgoodx
    choose! f hf using hlocal
    use f x1
    have hfcopy := hf
    have hfcopy2 := hf
    have hfcopy3 := hf
    specialize hf x1 (hDE hx1)
    refine ⟨hf.1, ?_⟩
    intro x2 hx2
    specialize hfcopy2 x2 (hDE hx2)
    have hclose : ∀ x ∈ E, ∀ y ∈ E, |(f x : ℝ) - f y| ≤ N := by
      intro q hq r hr
      have hfcopy' := hfcopy
      specialize hfcopy q hq
      specialize hfcopy' r hr
      apply @le_trans _ _ _
        (((⌊t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) -
          ⌈t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌉) N
      · apply two_in_Icc
        · rw [← hI]
          exact hfcopy.1
        · rw [← hI]
          exact hfcopy'.1
      · have hfloor :
            ((⌊t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) ≤
              t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2 := by
          exact Int.floor_le _
        have hceil :
            t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2 ≤
              (⌈t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌉ : ℤ) := by
          exact Int.le_ceil _
        nlinarith
    have hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N) := by
      refine le_trans ?_ hmertens
      rw [ppower_rec_sum]
      push_cast
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hr with ⟨a, ha, hr⟩
        rw [Finset.mem_filter] at hr
        refine ⟨?_, hr.2.1⟩
        exact lt_of_le_of_lt (Nat.divisor_le hr.1) (by
          rw [← Finset.mem_range]
          exact hA ha)
      · intro i _ _
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    by_cases htwoxs : f x2 = f x1
    · obtain hf' := hfcopy2.2.1
      rw [htwoxs] at hf'
      exact hf'
    · by_cases hthreexs : ∀ x ∈ E, f x = f x1 ∨ f x = f x2
      · exact
          force_good_properties_two_values_case
            N M c A A_I E I x1 x2 f hA h0A h0M hMA hrecA hlarge0 hlarge5 hlarge3
            (by norm_num1) hzI (by simpa using hP) hnoB hrecN hsum4 hlarge9 hdiv hIclose rfl rfl
            hfcopy (hDE hx1) (hDE hx2) (hclose x2 (hDE hx2) x1 (hDE hx1)) htwoxs hthreexs
      · rw [not_forall] at hthreexs
        rcases hthreexs with ⟨x3, hx3⟩
        rw [Classical.not_imp, not_or] at hx3
        specialize hfcopy3 x3 hx3.1
        exfalso
        let S1 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x1).sum (fun r => (1 : ℝ) / r)
        let S2 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x2).sum (fun r => (1 : ℝ) / r)
        let S3 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x3).sum (fun r => (1 : ℝ) / r)
        exact
          force_good_properties_three_values_case
            N c A x1 x2 x3 f hA hlarge3
            (by
              dsimp [c]
              norm_num1)
            hrecN hsum4 hf.2.2
            hfcopy2.2.2 hfcopy3.2.2 htwoxs hx3.2.2 hx3.2.1
            (hclose x2 (hDE hx2) x1 (hDE hx1)) (hclose x3 hx3.1 x2 (hDE hx2))
            (hclose x3 hx3.1 x1 (hDE hx1))
  · have hIne : I.Nonempty := by
      rw [hI, Finset.nonempty_Icc]
      rw [Int.ceil_le]
      have hfloor : t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 <
          (⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) := by
        exact Int.sub_one_lt_floor _
      have hgap :
          t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
            t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 := by
        nlinarith
      exact le_trans hgap (le_of_lt hfloor)
    rcases hIne with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro q hq
    exfalso
    apply hDne
    exact ⟨q, hq⟩

theorem force_good_properties2 :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M ≤ N → (N : ℝ) ≤ M ^ 2 → 0 ∉ A →
      (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
      (∀ q ∈ ppowers_in_set A, (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A q) →
      (ppower_rec_sum A : ℝ) ≤ (2 / 3) * log (log N) →
      good_condition A (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) ((M : ℝ) / log N)
        (M / (2 * (log N) ^ (1 / 100 : ℝ))) := by
  classical
  let c := (35 : ℝ) / 100
  filter_upwards
    [ eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((2 : ℝ) / (1 / 2)))
    , rec_pp_sum_close
    , find_good_x ] with
    N hlarge hlarge0 hlarge4 hrecN hgoodx M A hA h0M hMN hNM h0A hMA hreg hreclocal hpprecA
  dsimp at hlarge0
  have hlarge3 : 0 < log (log N) := by
    refine lt_of_lt_of_le ?_ hlarge4
    norm_num1
  have hlarge1 : 1 ≤ M * N ^ ((-2 : ℝ) / log (log N)) := by
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_trans zero_lt_one hlarge)
    have hexp : (2 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      have hlarge4' := hlarge4
      norm_num at hlarge4'
      refine (div_le_iff₀ hlarge3).2 ?_
      nlinarith
    have hpow :
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ M := by
      calc
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast le_of_lt hlarge) hexp
        _ ≤ M := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_iff.mpr ⟨le_of_lt h0M, hNM⟩
    have hneg : (-2 : ℝ) / log (log N) = -((2 : ℝ) / log (log N)) := by
      ring
    rw [hneg, Real.rpow_neg, div_eq_mul_inv]
    · exact (one_le_div (Real.rpow_pos_of_pos hNpos _)).2 hpow
    · exact Nat.cast_nonneg N
  have hlarge2 : M * N ^ ((-2 : ℝ) / log (log N)) ≤ N := by
    have hrpow : N ^ ((-2 : ℝ) / log (log N)) ≤ (1 : ℝ) := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast le_of_lt hlarge
      · apply div_nonpos_of_nonpos_of_nonneg
        · rw [neg_nonpos]
          exact zero_le_two
        · exact le_of_lt hlarge3
    calc
      _ ≤ M := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hrpow h0M.le
      _ ≤ N := hMN
  rw [good_condition]
  intro t I hI
  refine or_iff_not_imp_left.2 ?_
  intro hP
  let D := interval_rare_ppowers I A (M / (2 * log N ^ ((1 : ℝ) / 100)))
  let K := M / (2 * log N ^ ((1 : ℝ) / 100))
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨x1, hx1⟩
    have hlocal :
        ∀ q ∈ D, ∃ x ∈ I, ((q : ℤ) ∣ x) ∧
            ((35 : ℝ) / 100) * log (log N) ≤
            (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ x).sum
              fun r : ℕ => (1 / r : ℝ)) := by
      intro q hq
      specialize hgoodx M A hA h0M hMN h0A hMA hreg t I q
        (by simpa [interval_rare_ppowers] using
          (Finset.filter_subset _ (ppowers_in_set A) hq)) hI
      have hgoodq :
          (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) ≤
            rec_sum_local (A.filter fun n => ∃ x ∈ I, (n : ℤ) ∣ x) q := by
        refine good_d N M (1 / (2 * log N ^ ((1 : ℝ) / 100))) A hA h0M hMA ?_ I q ?_
        · intro q hq'
          rw [two_mul, one_div, ← inv_div_left, add_halves, ← Real.rpow_neg]
          · exact hreclocal q hq'
          · exact le_of_lt hlarge0
        · rw [← div_eq_mul_one_div]
          exact hq
      exact hgoodx hgoodq
    clear hgoodx
    choose! f hf using hlocal
    use f x1
    have hfcopy := hf
    specialize hf x1 hx1
    refine ⟨hf.1, ?_⟩
    intro q hq
    specialize hfcopy q hq
    by_cases htwoxs : f q = f x1
    · obtain hf' := hfcopy.2.1
      rw [htwoxs] at hf'
      exact hf'
    · exfalso
      let S1 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x1
      let S2 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f q
      let S12 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f q ∧ (n : ℤ) ∣ f x1
      have hfS1 : c * log (log N) ≤ S1.sum (fun r => (1 / r : ℝ)) := by
        simpa [S1, c] using hf.2.2
      have hfcopyS2 : c * log (log N) ≤ S2.sum (fun r => (1 / r : ℝ)) := by
        simpa [S2, c] using hfcopy.2.2
      have hsum1 :
          2 * c * log (log N) ≤
            S1.sum (fun r => (1 / r : ℝ)) + S2.sum (fun r => (1 / r : ℝ)) := by
        rw [two_mul, add_mul]
        exact add_le_add hfS1 hfcopyS2
      have hsum2 :
          S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) -
              S12.sum (fun r => (1 : ℝ) / r) ≤
            ppower_rec_sum A := by
        have hS12 : S1 ∩ S2 = S12 := by
          ext r
          simp [S1, S2, S12, and_left_comm, and_assoc, and_comm]
        have hEq :
            S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) -
                S12.sum (fun r => (1 : ℝ) / r) =
              (S1 ∪ S2).sum (fun r => (1 : ℝ) / r) := by
          rw [← hS12]
          linarith [Finset.sum_union_inter (s₁ := S1) (s₂ := S2) (f := fun r => (1 : ℝ) / r)]
        rw [ppower_rec_sum]
        push_cast
        rw [hEq]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro r hr
          rw [Finset.mem_union] at hr
          cases hr with
          | inl hr1 =>
              exact (Finset.mem_filter.mp hr1).1
          | inr hr2 =>
              exact (Finset.mem_filter.mp hr2).1
        · intro i _ _
          rw [one_div_nonneg]
          exact Nat.cast_nonneg i
      have hsum3 :
          S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) - ppower_rec_sum A ≤
            S12.sum (fun r => (1 : ℝ) / r) := by
        linarith
      have hsum4 :
          ((1 : ℝ) / 500) * log (log N) ≤
            S12.sum (fun r => (1 : ℝ) / r) := by
        have hsilly : c = 35 / 100 := by
          rfl
        nlinarith
      have hqx1close : |(f q : ℝ) - f x1| ≤ N := by
        apply @le_trans _ _ _
          (((⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) -
            ⌈t - M * N ^ ((-2 : ℝ) / log (log N)) / 2⌉) N
        · apply two_in_Icc
          · rw [← hI]
            exact hfcopy.1
          · rw [← hI]
            exact hf.1
        · have hfloor :
              ((⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) ≤
                t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 := by
            exact Int.floor_le _
          have hceil :
              t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
                (⌈t - M * N ^ ((-2 : ℝ) / log (log N)) / 2⌉ : ℤ) := by
            exact Int.le_ceil _
          nlinarith
      specialize hrecN (f q) (f x1) htwoxs hqx1close
      rw [lt_iff_not_ge] at hrecN
      apply hrecN
      refine le_trans hsum4 ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        simp only [S12, Finset.mem_filter] at hr
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1 with ⟨m, hm1, hm2⟩
        rw [Finset.mem_filter] at hm2
        rw [Finset.mem_filter]
        refine ⟨?_, hm2.2.1, hr.2⟩
        rw [Finset.mem_range]
        exact lt_of_le_of_lt (Nat.divisor_le hm2.1) (by
          rw [← Finset.mem_range]
          exact hA hm1)
      · intro i _ _
        exact div_nonneg zero_le_one (Nat.cast_nonneg i)
  · have hIne : I.Nonempty := by
      rw [hI, Finset.nonempty_Icc]
      rw [Int.ceil_le]
      have hfloor : t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 <
          (⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) := by
        exact Int.sub_one_lt_floor _
      have hgap :
          t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
            t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 := by
        nlinarith
      exact le_trans hgap (le_of_lt hfloor)
    rcases hIne with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro q hq
    exfalso
    apply hDne
    exact ⟨q, hq⟩

end UnitFractions
