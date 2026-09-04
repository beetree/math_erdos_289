module

public import SolveMath.Corpus.NumberTheory.UnitFractionSubsumResults.PruningLemmas

@[expose] public section

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter _root_.Finset Real
open _root_.Finset

lemma large_enough_Naux1_hreduce
    (N : ℕ) (hN6 : 0 < (N : ℝ)) (hN7 : 0 < log (log N)) (hN8 : 0 < log N) :
    (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
      ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
        (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
      (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) := by
  have hAiff :
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
            (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
        log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
    rw [← Real.log_le_log_iff
      (show 0 < (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) by positivity)
      (show 0 <
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) by
            positivity)]
    have hsq :
        (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) =
          (N : ℝ) ^ ((1 - (3 : ℝ) / log (log N)) * 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
      ring_nf
    rw [Real.log_mul
        (show (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ)) ≠ 0 by
          positivity)
        (show (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ≠ 0 by
          positivity)]
    rw [Real.log_div
        (Real.rpow_pos_of_pos hN6 _).ne'
        (show (2 * log N ^ (1 / 100 : ℝ)) ≠ 0 by positivity)]
    rw [Real.log_div
        (show (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) ≠ 0 by positivity)
        (show (16 * N ^ 2 * log N ^ 2 : ℝ) ≠ 0 by positivity)]
    have hlogDen1 :
        Real.log (16 * N ^ 2 * log N ^ 2 : ℝ) =
          Real.log 16 + 2 * Real.log N + 2 * Real.log (Real.log N) := by
      rw [show (16 * N ^ 2 * log N ^ 2 : ℝ) = 16 * ((N : ℝ) ^ 2 * log N ^ 2) by
        ring_nf]
      rw [Real.log_mul (show (16 : ℝ) ≠ 0 by norm_num)
        (show (N : ℝ) ^ 2 * log N ^ 2 ≠ 0 by positivity)]
      rw [Real.log_mul
        (show (N : ℝ) ^ 2 ≠ 0 by positivity)
        (show log N ^ 2 ≠ 0 by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, Real.log_rpow hN6, Real.log_rpow hN8]
      ring_nf
    have hlogDen2 :
        Real.log (2 * log N ^ (1 / 100 : ℝ)) =
          Real.log 2 + (1 / 100 : ℝ) * Real.log (Real.log N) := by
      rw [Real.log_mul
        (show (2 : ℝ) ≠ 0 by norm_num)
        (show log N ^ (1 / 100 : ℝ) ≠ 0 by positivity)]
      rw [Real.log_rpow hN8]
    rw [Real.log_rpow hN6, hsq, hlogDen1, hlogDen2]
    simp_rw [Real.log_rpow hN6]
    have hlog32 : Real.log (2 * 16 : ℝ) = Real.log 2 + Real.log 16 := by
      rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (16 : ℝ) ≠ 0 by norm_num)]
    constructor
    · intro h
      rw [hlog32] at *
      field_simp [hN7.ne'] at h ⊢
      ring_nf at h ⊢
      linarith
    · intro h
      rw [hlog32] at *
      field_simp [hN7.ne'] at h ⊢
      ring_nf at h ⊢
      linarith
  have hBiff :
      (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) ↔
        log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
    rw [← Real.log_le_log_iff
      (show 0 < (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) by positivity)
      (show 0 < (N : ℝ) ^ (1 / log (log N)) by positivity)]
    rw [Real.log_mul (show (2 * 16 : ℝ) ≠ 0 by norm_num)
      (Real.rpow_pos_of_pos hN8 _).ne']
    rw [Real.log_rpow hN8, Real.log_rpow hN6]
    constructor
    · intro h
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    · intro h
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  exact hAiff.trans hBiff.symm

lemma large_enough_Naux1 :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) := by
  let C : ℝ := (((2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ))) ^ ((1 : ℝ) / 2))
  have haux4 :=
    (isLittleO_log_id_atTop.bound <| by
      rw [one_div_pos]
      exact mul_pos zero_lt_two (Real.log_pos (show (1 : ℝ) < 2 * 16 by norm_num)))
  have haux5 :
      ∀ᶠ x : ℝ in atTop,
        ‖log x‖ ≤ (1 / C) * ‖x ^ ((1 : ℝ) / 2)‖ :=
    (isLittleO_log_rpow_atTop (half_pos zero_lt_one)).bound <| by
      rw [one_div_pos]
      dsimp [C]
      exact Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ)) by norm_num)
        _
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop ((128 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux4
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux5 ] with
    N hN1 hN2 hN3 hN3new4 hN3new5
  dsimp at hN1 hN2 hN3new4
  have hN4 : 1 < log (log N) := by
    linarith
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (128 : ℝ) ^ (500 : ℝ) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    exact lt_of_lt_of_le hpowpos hN2
  have hN12 : 2 * log (2 * 16) * log (log N) ≤ log N := by
    have habs : |log (log N)| ≤ (1 / (2 * log (2 * 16))) * |log N| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hN3new4
    rw [abs_of_nonneg hN7.le, abs_of_nonneg hN8.le] at habs
    have hconst : 0 < 2 * log (2 * 16) := by
      exact mul_pos zero_lt_two (Real.log_pos (by norm_num))
    have hdiv : log (log N) ≤ log N / (2 * log (2 * 16)) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habs
    have hmul : log (log N) * (2 * log (2 * 16)) ≤ log N := by
      exact (_root_.le_div_iff₀ hconst).mp hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hN13 :
      C * log (log N) ≤ log N ^ ((1 : ℝ) / 2) := by
    have habs :
        |log (log N)| ≤ (1 / C) * |log N ^ ((1 : ℝ) / 2)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hN3new5
    rw [abs_of_nonneg hN7.le, abs_of_nonneg (by positivity)] at habs
    have hconst : 0 < C := by
      dsimp [C]
      positivity
    have hdiv :
        log (log N) ≤ log N ^ ((1 : ℝ) / 2) / C := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habs
    have hmul : log (log N) * C ≤ log N ^ ((1 : ℝ) / 2) := by
      exact (_root_.le_div_iff₀ hconst).mp hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hC_sq : C * C = 2 * (2 + (1 / 100 : ℝ)) := by
    dsimp [C]
    have hbase : 0 < (2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ)) := by positivity
    rw [← Real.rpow_add hbase]
    norm_num
  have hreduce :
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
        (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) := by
    exact large_enough_Naux1_hreduce N hN6 hN7 hN8
  rw [hreduce]
  rw [← Real.log_le_log_iff
    (show 0 < (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) by positivity)
    (show 0 < (N : ℝ) ^ (1 / log (log N)) by positivity)]
  rw [Real.log_mul (show (2 * 16 : ℝ) ≠ 0 by norm_num) (Real.rpow_pos_of_pos hN8 _).ne',
    Real.log_rpow hN8, Real.log_rpow hN6]
  have hfirst :
      log (2 * 16) ≤ (1 / 2 : ℝ) * (log N / log (log N)) := by
    have htmp : 2 * log (2 * 16) * log (log N) ≤ log N := hN12
    have hpos : 0 < log (log N) := hN7
    have htmp' : 2 * log (2 * 16) ≤ log N / log (log N) := by
      exact (_root_.le_div_iff₀ hpos).2 <| by simpa [mul_assoc] using htmp
    nlinarith
  have hsecond :
      (2 + 1 / 100 : ℝ) * log (log N) ≤ (1 / 2 : ℝ) * (log N / log (log N)) := by
    have hsq : 2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 ≤ log N := by
      have hmul :=
        mul_le_mul hN13 hN13
          (show 0 ≤ C * log (log N) by positivity)
          (show 0 ≤ log N ^ ((1 : ℝ) / 2) by positivity)
      have hsimp :
          (C * log (log N)) * (C * log (log N)) =
            2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 := by
        calc
          (C * log (log N)) * (C * log (log N)) =
              (C * C) * (log (log N) * log (log N)) := by ring
          _ = 2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 := by
              rw [hC_sq]
              ring_nf
      have hsimp' : (log N ^ ((1 : ℝ) / 2)) * (log N ^ ((1 : ℝ) / 2)) = log N := by
        rw [← Real.rpow_add hN8]
        norm_num
      calc
        2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 = (C * log (log N)) * (C * log (log N)) := by
          symm
          exact hsimp
        _ ≤ (log N ^ ((1 : ℝ) / 2)) * (log N ^ ((1 : ℝ) / 2)) := hmul
        _ = log N := hsimp'
    have htmp' : 2 * (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
      exact (_root_.le_div_iff₀ hN7).2 <| by
        simpa [mul_assoc, pow_two] using hsq
    nlinarith
  calc
    log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤
        (1 / 2 : ℝ) * (log N / log (log N)) + (1 / 2 : ℝ) * (log N / log (log N)) := by
          exact add_le_add hfirst hsecond
    _ = log N / log (log N) := by ring
    _ = (1 / log (log N)) * log N := by ring

lemma large_enough_Naux2 :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
          c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤
          (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) -
            1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  intro c hc
  have haux :=
    (isLittleO_log_rpow_atTop (half_pos zero_lt_one)).bound (show 0 < (1 : ℝ) by norm_num)
  have haux2 := (isLittleO_log_rpow_atTop zero_lt_one).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (6 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
    , eventually_ge_atTop (64 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux
    , tendsto_natCast_atTop_atTop.eventually haux2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (-log c / (7 - 1 / 500))) ] with
    N hN1 hN2 hN3 hNnew hNnew2 hNnew3
  dsimp at hN1 hN2 hNnew3
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    linarith
  have hN9 : log (log N) ≤ log N ^ ((1 : ℝ) / 2) := by
    have habs : |log (log N)| ≤ (1 : ℝ) * |log N ^ ((1 : ℝ) / 2)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hNnew
    rw [abs_of_nonneg (le_of_lt hN7), abs_of_nonneg (by positivity), one_mul] at habs
    exact habs
  have hN10 : log N ≤ N := by
    have habs : |log N| ≤ (1 : ℝ) * |(N : ℝ) ^ (1 : ℝ)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hNnew2
    rw [abs_of_nonneg (le_of_lt hN8), abs_of_nonneg (by positivity), one_mul, Real.rpow_one] at habs
    exact habs
  constructor
  · have hmain :
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) * (log N) ^ (1 / 500 : ℝ) ≤
          c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
      rw [← Real.log_le_log_iff (show 0 < (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) *
          (log N) ^ (1 / 500 : ℝ) by positivity)
        (show 0 < c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity)]
      rw [Real.log_mul (Real.rpow_pos_of_pos hN6 _).ne' (Real.rpow_pos_of_pos hN8 _).ne',
        Real.log_mul hc.ne' (Real.rpow_pos_of_pos hN6 _).ne', Real.log_rpow hN6,
        Real.log_rpow hN8, Real.log_rpow hN6]
      have hcN : -(7 - (1 : ℝ) / 500) * log (log N) ≤ log c := by
        have ha : 0 < (7 - (1 : ℝ) / 500) := by norm_num
        have htmp : -log c ≤ log (log N) * (7 - (1 : ℝ) / 500) := by
          exact (_root_.div_le_iff₀ ha).mp hNnew3
        nlinarith
      have hsqmul : log (log N) * log (log N) ≤ log N := by
        have hsq' :=
          mul_le_mul hN9 hN9
            (show 0 ≤ log (log N) by linarith)
            (show 0 ≤ log N ^ ((1 : ℝ) / 2) by positivity)
        have hlog : log N ^ ((1 : ℝ) / 2) * log N ^ ((1 : ℝ) / 2) = log N := by
          rw [← Real.rpow_add hN8]
          norm_num
        calc
          log (log N) * log (log N) ≤ log N ^ ((1 : ℝ) / 2) * log N ^ ((1 : ℝ) / 2) := by
            simpa [pow_two] using hsq'
          _ = log N := hlog
      have hdiv : log (log N) ≤ log N / log (log N) := by
        exact (_root_.le_div_iff₀ hN7).2 hsqmul
      have hfrac : -(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N) ≤ log c := by
        have hstep :
            -(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N) ≤
              -(7 : ℝ) * log (log N) + (1 / 500 : ℝ) * log (log N) := by
          nlinarith
        linarith
      have hadd := add_le_add_right hfrac ((1 - (1 : ℝ) / log (log N)) * log N)
      have hrew :
          (-(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N)) +
              ((1 - (1 : ℝ) / log (log N)) * log N) =
            (1 - (8 : ℝ) / log (log N)) * log N + (1 / 500 : ℝ) * log (log N) := by
        field_simp [hN7.ne']
        ring
      have hrew' :
          ((1 - (1 : ℝ) / log (log N)) * log N) +
              (-(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N)) =
            (1 - (8 : ℝ) / log (log N)) * log N + (1 / 500 : ℝ) * log (log N) := by
        simpa [add_assoc, add_left_comm, add_comm] using hrew
      rw [hrew'] at hadd
      simpa [add_assoc, add_left_comm, add_comm] using hadd
    exact (le_div_iff₀ (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)).mpr hmain
  · refine le_trans (b := (7 : ℝ) / (log N ^ ((1 : ℝ) / 500))) ?_ ?_
    · refine (_root_.le_div_iff₀ (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)).2 ?_
      rw [← Real.rpow_add hN8]
      have hpow : log N ^ (-(1 / 101 : ℝ) + (1 / 500 : ℝ)) ≤ (1 : ℝ) := by
        apply Real.rpow_le_one_of_one_le_of_nonpos hN2
        · norm_num
      linarith
    · rw [le_sub_iff_add_le]
      have hlogpow : log N ^ ((1 : ℝ) / 500) ≤ (N : ℝ) ^ ((1 : ℝ) / 500) := by
        exact Real.rpow_le_rpow (le_of_lt hN8) hN10 (by norm_num : 0 ≤ (1 : ℝ) / 500)
      have hNexp : (N : ℝ) ^ ((1 : ℝ) / 500) ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
        apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5)
        have hrec : 1 / log (log N) ≤ (1 : ℝ) / 6 := by
          exact one_div_le_one_div_of_le (by norm_num : 0 < (6 : ℝ)) hN1
        nlinarith
      have hInv :
          1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤
            1 / (log N ^ ((1 : ℝ) / 500)) := by
        exact one_div_le_one_div_of_le (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)
          (le_trans hlogpow hNexp)
      have hDne : log N ^ ((1 : ℝ) / 500) ≠ 0 := by positivity
      calc
        (7 : ℝ) / (log N ^ ((1 : ℝ) / 500)) + 1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤
            (7 : ℝ) / (log N ^ ((1 : ℝ) / 500)) + 1 / (log N ^ ((1 : ℝ) / 500)) := by
              exact add_le_add le_rfl hInv
        _ = (2 : ℝ) / (log N ^ ((1 : ℝ) / 500) / 4) := by
              field_simp [hDne]
              norm_num

lemma large_enough_Naux :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      let M := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
      let L := M / (2 * log N ^ (1 / 100 : ℝ))
      let T := M / log N
      let ε := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
      let ε' := (log N) ^ (-(1 / 100 : ℝ))
      let K := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
      ε ≤ ε' →
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) - 1 / M := by
  intro c hc
  have hlargeaux1 := large_enough_Naux1
  have hlargeaux2 := large_enough_Naux2 c hc
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop ((128 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , hlargeaux2
    , hlargeaux1 ] with
    N hN1 hN2 hN3 hotheraux hnec
  dsimp at hN1 hN2
  have hN4 : 1 < log (log N) := by
    refine lt_of_lt_of_le ?_ hN1
    norm_num1
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num1 : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (128 : ℝ) ^ (500 : ℝ) := by
      positivity
    exact lt_of_lt_of_le hpowpos hN2
  dsimp
  intro hT3
  constructor
  · rw [← div_le_iff₀ (show 0 < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity)]
    rw [← Real.rpow_sub hN6]
    have hexp :
        (1 - (8 : ℝ) / log (log N)) - (1 - (1 : ℝ) / log (log N)) =
          (-7 : ℝ) / log (log N) := by
      field_simp [hN7.ne']
      ring
    rw [hexp]
    refine le_trans ?_ hT3
    refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) ?_
    exact (div_le_div_iff_of_pos_right hN7).2 (by norm_num)
  constructor
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnec
  constructor
  · refine le_trans
        (b :=
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ)) *
            ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 /
              (16 * (N : ℝ) ^ 2 * log N ^ 2)) ?_ ?_
    · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnec
    · have hstep :
          (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
              ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) /
            (16 * (N : ℝ) ^ 2 * log N ^ 2) ≤
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / log N) *
              ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) /
            ((N : ℝ) ^ 2 * log N) := by
        rw [div_le_div_iff₀
          (show 0 < 16 * (N : ℝ) ^ 2 * log N ^ 2 by positivity)
          (show 0 < (N : ℝ) ^ 2 * log N by positivity)]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hEq1 :
            (N : ℝ) ^ (1 - (1 : ℝ) * (log (log N))⁻¹) *
                (2 * log N ^ (1 / 100 : ℝ))⁻¹ *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                ((N : ℝ) ^ 2 * log N) =
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (N : ℝ) ^ 2) *
              ((2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N) := by
          ring_nf
        have hEq2 :
            (N : ℝ) ^ (1 - (1 : ℝ) * (log (log N))⁻¹) / log N *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (16 * (N : ℝ) ^ 2 * log N ^ 2) =
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (N : ℝ) ^ 2) *
              ((log N)⁻¹ * 16 * log N ^ 2) := by
          rw [div_eq_mul_inv]
          ring_nf
        rw [hEq1, hEq2]
        have hcommon_nonneg :
            0 ≤
              ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                  (N : ℝ) ^ 2 := by
          positivity
        have hscalar :
            (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N ≤ (log N)⁻¹ * 16 * log N ^ 2 := by
          have h128 : (1 : ℝ) ≤ (128 : ℝ) ^ (500 : ℝ) := by
            apply one_le_rpow
            · norm_num
            · norm_num
          have hlogpow_ge_one : 1 ≤ log N ^ (1 / 100 : ℝ) := by
            apply one_le_rpow
            · exact le_trans h128 hN2
            · norm_num
          have hfac : 1 ≤ 2 * log N ^ (1 / 100 : ℝ) := by
            nlinarith
          have hleft :
              (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N = log N / (2 * log N ^ (1 / 100 : ℝ)) := by
            calc
              (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N =
                  log N * (2 * log N ^ (1 / 100 : ℝ))⁻¹ := by ac_rfl
              _ = log N / (2 * log N ^ (1 / 100 : ℝ)) := by
                  symm
                  rw [div_eq_mul_inv]
          have hright :
              (log N)⁻¹ * 16 * log N ^ 2 = (16 * log N ^ 2) / log N := by
            calc
              (log N)⁻¹ * 16 * log N ^ 2 = 16 * log N ^ 2 * (log N)⁻¹ := by ac_rfl
              _ = (16 * log N ^ 2) / log N := by rw [div_eq_mul_inv]
          rw [hleft, hright]
          refine (div_le_div_iff₀ (show 0 < 2 * log N ^ (1 / 100 : ℝ) by positivity) hN8).2 ?_
          calc
            log N * log N = log N ^ 2 := by ring
            _ ≤ 16 * log N ^ 2 := by
              simpa [one_mul] using
                mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 16 by norm_num)
                  (show 0 ≤ log N ^ 2 by positivity)
            _ ≤ (16 * log N ^ 2) * (2 * log N ^ (1 / 100 : ℝ)) := by
              simpa [mul_one] using
                mul_le_mul_of_nonneg_left hfac (show 0 ≤ 16 * log N ^ 2 by positivity)
        exact mul_le_mul_of_nonneg_left hscalar hcommon_nonneg
      simpa using hstep
  · exact hotheraux

lemma large_enough_N_hTp
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN2 : (192 : ℝ) ^ (500 : ℝ) ≤ log N)
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (_hN7 : 0 < log (log N))
    (hN8 : 0 < log N) :
    192 * (log N) ^ (1 / 500 : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  have h500 : (0 : ℝ) < 500 := by norm_num
  have h5002 : (0 : ℝ) < 500 / 2 := by norm_num
  have hlog_nonneg : 0 ≤ log N := le_of_lt hN8
  have haux :
      192 * (log N) ^ (1 / 500 : ℝ) ≤
        (log N) ^ (1 / 500 : ℝ) * (log N) ^ (1 / 500 : ℝ) := by
    have h192 : (192 : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) := by
      rw [← Real.rpow_le_rpow_iff (show 0 ≤ (192 : ℝ) by norm_num)
        (show 0 ≤ (log N) ^ (1 / 500 : ℝ) by positivity) h500]
      rw [← Real.rpow_mul hlog_nonneg, one_div_mul_cancel (show (500 : ℝ) ≠ 0 by norm_num),
        Real.rpow_one]
      exact hN2
    exact mul_le_mul_of_nonneg_right h192 (show 0 ≤ (log N) ^ (1 / 500 : ℝ) by positivity)
  refine lt_of_le_of_lt haux ?_
  rw [← Real.rpow_add hN8]
  refine (Real.rpow_lt_rpow_iff
    (show 0 ≤ (log N) ^ (1 / 500 + 1 / 500 : ℝ) by positivity)
    (show 0 ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity) h5002).1 ?_
  rw [← Real.rpow_mul hlog_nonneg]
  norm_num
  refine lt_of_le_of_lt (Real.log_le_sub_one_of_pos hN6) ?_
  refine lt_of_lt_of_le (sub_one_lt (N : ℝ)) ?_
  have hrightEq :
      ((N : ℝ) ^ (1 - (log (log N))⁻¹)) ^ (250 : ℕ) =
        (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
    norm_num
  have hdiv : (log (log N))⁻¹ ≤ 1 / 6 := by
    have h6 : (0 : ℝ) < 6 := by linarith
    simpa [one_div] using
      (one_div_le_one_div_of_le h6 hN1)
  have hpow :
      (N : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
    have hpow' : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) ?_
      nlinarith
    simpa using hpow'
  exact le_trans hpow hrightEq.ge

lemma large_enough_N_hT1
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN10 : log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) :
    3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
  have hstep :
      3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        3 * (log N) ^ (-(1 / 100 : ℝ)) * ((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := by
    gcongr
  calc
    3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        3 * (log N) ^ (-(1 / 100 : ℝ)) * ((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := hstep
    _ = 2 * ((log N) ^ (-(1 / 100 : ℝ)) * (log N) ^ (3 / 500 : ℝ)) := by ring
    _ = 2 * (log N) ^ ((-(1 / 100 : ℝ)) + 3 / 500) := by
      rw [← Real.rpow_add hN8]
    _ = 2 * (log N) ^ (-(1 / 250 : ℝ)) := by
      congr 2
      norm_num
    _ = 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
      rw [div_eq_mul_inv]
      congr 1
      calc
        (log N) ^ (-(1 / 250 : ℝ)) = ((log N) ^ (1 / 250 : ℝ))⁻¹ := by
          exact Real.rpow_neg hN8.le (1 / 250 : ℝ)
        _ = (((log N) ^ (1 / 500 : ℝ)) ^ 2)⁻¹ := by
          congr 1
          calc
            (log N) ^ (1 / 250 : ℝ) = (log N) ^ ((1 / 500 : ℝ) + 1 / 500) := by
              congr 2
              norm_num
            _ = ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
              rw [pow_two, ← Real.rpow_add hN8]

lemma large_enough_N_hT2
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN11 : 2 * log (log N) ≤ (log N) ^ (1 / 200 : ℝ)) :
    2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) := by
  have hpow_nonneg : 0 ≤ (log N) ^ (-(1 / 100 : ℝ)) := by positivity
  have hstep :
      2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        (log N) ^ (1 / 200 : ℝ) * (log N) ^ (-(1 / 100 : ℝ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hN11 hpow_nonneg
  refine hstep.trans ?_
  rw [← Real.rpow_add hN8]
  norm_num

lemma large_enough_N_hT3
    (N : ℕ)
    (hN2 : (192 : ℝ) ^ (500 : ℝ) ≤ log N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N))
    (hN8 : 0 < log N)
    (hN10 : log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) :
    (N : ℝ) ^ (-(5 : ℝ) / log (log N)) ≤ (log N) ^ (-(1 / 100 : ℝ)) := by
  have hlog_ge_one : (1 : ℝ) ≤ log N := by
    refine le_trans ?_ hN2
    apply one_le_rpow
    · norm_num
    · norm_num
  have hsq :
      log (log N) ^ (2 : ℕ) ≤ 500 * log N := by
    calc
      log (log N) ^ (2 : ℕ) ≤ (((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) ^ (2 : ℕ)) := by
        nlinarith [hN10]
      _ = (4 / 9 : ℝ) * ((log N) ^ (3 / 500 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := by ring
      _ = (4 / 9 : ℝ) * (log N) ^ ((3 / 500 : ℝ) + 3 / 500) := by
        rw [← Real.rpow_add hN8]
      _ = (4 / 9 : ℝ) * (log N) ^ (3 / 250 : ℝ) := by
        congr 2
        norm_num
      _ ≤ (4 / 9 : ℝ) * log N := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hexp : (3 / 250 : ℝ) ≤ 1 := by norm_num
        simpa using Real.rpow_le_rpow_of_exponent_le hlog_ge_one hexp
      _ ≤ 500 * log N := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (4 / 9 : ℝ) ≤ 500) (le_of_lt hN8)
  have hlogineq : (1 / 100 : ℝ) * log (log N) ≤ 5 * log N / log (log N) := by
    rw [le_div_iff₀ hN7]
    nlinarith [hsq]
  rw [← Real.log_le_log_iff (show 0 < (N : ℝ) ^ (-(5 : ℝ) / log (log N)) by positivity)
    (show 0 < (log N) ^ (-(1 / 100 : ℝ)) by positivity)]
  rw [Real.log_rpow hN6, Real.log_rpow hN8]
  have hlogineq' : (1 / 100 : ℝ) * log (log N) ≤ (5 / log (log N)) * log N := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlogineq
  have hneg :
      -((5 / log (log N)) * log N) ≤ -((1 / 100 : ℝ) * log (log N)) := by
    linarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hneg

lemma large_enough_N_hMε
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N)) :
    1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) <
      (N : ℝ) ^ (-(5 : ℝ) / log (log N)) * log (log N) := by
  have hN4 : 1 < log (log N) := by
    linarith
  have hexp_nonneg : 0 ≤ (1 : ℝ) - (6 : ℝ) / log (log N) := by
    rw [sub_nonneg, div_le_one hN7]
    simpa using hN1
  have hpow_ge_one : 1 ≤ (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    refine one_le_rpow (le_of_lt hN5) hexp_nonneg
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    positivity
  have hmain : 1 < log (log N) * (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    nlinarith
  have hexp :
      (-(5 : ℝ) / log (log N)) + (1 - (1 : ℝ) / log (log N)) =
        (1 : ℝ) - (6 : ℝ) / log (log N) := by
    ring
  rw [one_div, inv_lt_iff_one_lt_mul₀ (Real.rpow_pos_of_pos hN6 _)]
  rw [mul_assoc]
  rw [mul_left_comm ((N : ℝ) ^ (-(5 : ℝ) / log (log N))) (log (log N))
    ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)))]
  rw [← mul_assoc]
  calc
    1 < log (log N) * (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := hmain
    _ = log (log N) *
          ((N : ℝ) ^ (-(5 : ℝ) / log (log N)) *
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) := by
          rw [← Real.rpow_add hN6, hexp]
    _ = log (log N) * (N : ℝ) ^ (-(5 : ℝ) / log (log N)) *
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
          rw [mul_assoc]

lemma large_enough_N_hKlower
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN3 : 64 ≤ N)
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N))
    (hN8 : 0 < log N) :
    8 ≤ (N : ℝ) ^ (1 - (3 : ℝ) / log (log N)) := by
  have _ : 0 < log N := hN8
  have hhalf : (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_le_rpow_iff (show 0 ≤ (8 : ℝ) by norm_num)
      (Real.rpow_nonneg (le_of_lt hN6) ((1 : ℝ) / 2)) (show (0 : ℝ) < 2 by norm_num)]
    rw [← Real.rpow_mul (le_of_lt hN6)]
    norm_num
    exact_mod_cast hN3
  have hexp : (1 : ℝ) / 2 ≤ 1 - (3 : ℝ) / log (log N) := by
    have hdiv : (3 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ hN7]
      nlinarith
    nlinarith
  exact hhalf.trans <| Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp

lemma large_enough_N_hKM
    (N : ℕ)
    (hN5 : (1 : ℝ) < N)
    (hN7 : 0 < log (log N)) :
    (N : ℝ) ^ (1 - (3 : ℝ) / log (log N)) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  apply Real.rpow_lt_rpow_of_exponent_lt hN5
  have hdiv : (1 : ℝ) / log (log N) < (3 : ℝ) / log (log N) := by
    rw [div_lt_div_iff₀ hN7 hN7]
    nlinarith
  nlinarith

lemma large_enough_N_hsum
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ))
    (hT : 4 * (log N) ^ (1 / 500 : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) :
    3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) +
        1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
      1 / (2 * (log N) ^ (1 / 500 : ℝ)) := by
  have hquarter_pos : 0 < 4 * (log N) ^ (1 / 500 : ℝ) := by positivity
  have hfirst :
      3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) ≤
        1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
    rw [_root_.le_div_iff₀ hquarter_pos]
    calc
      3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) *
          (4 * (log N) ^ (1 / 500 : ℝ)) =
        24 * ((log N) ^ (-(1 / 100 : ℝ)) * (log N) ^ (1 / 500 : ℝ)) * log (log N) := by
          ring
      _ = 24 * (log N) ^ ((-(1 / 100 : ℝ)) + 1 / 500) * log (log N) := by
        rw [← Real.rpow_add hN8]
      _ = 24 * (log N) ^ (-(1 / 125 : ℝ)) * log (log N) := by
        congr 2
        norm_num
      _ = (24 * log (log N)) / (log N) ^ (1 / 125 : ℝ) := by
        rw [div_eq_mul_inv, Real.rpow_neg hN8.le]
        ring
      _ ≤ 1 := by
        rw [div_le_iff₀ (show 0 < (log N) ^ (1 / 125 : ℝ) by positivity)]
        simpa [one_mul] using hN9
  have hsecond :
      1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
        1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
    exact one_div_le_one_div_of_le hquarter_pos hT.le
  calc
    3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) +
        1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
      1 / (4 * (log N) ^ (1 / 500 : ℝ)) + 1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
        exact add_le_add hfirst hsecond
    _ = 1 / (2 * (log N) ^ (1 / 500 : ℝ)) := by
      have hPne : (log N) ^ (1 / 500 : ℝ) ≠ 0 := by positivity
      field_simp [hPne]
      norm_num

lemma large_enough_N_honeOverM
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN5 : (1 : ℝ) < N)
    (hN8 : 0 < log N)
    (_hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ)) :
    1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) <
      (log N) ^ (-(1 / 100 : ℝ)) * log (log N) := by
  have hN6 : 0 < (N : ℝ) := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN4 : 1 < log (log N) := by
    linarith
  have hTq :
      (log N) ^ (1 / 100 : ℝ) <
        (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
    have h100 : (0 : ℝ) < 100 := by
      norm_num
    refine (Real.rpow_lt_rpow_iff
      (show 0 ≤ (log N) ^ (1 / 100 : ℝ) by positivity)
      (show 0 ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity) h100).1 ?_
    rw [← Real.rpow_mul hN8.le]
    norm_num
    refine lt_of_le_of_lt (Real.log_le_sub_one_of_pos hN6) ?_
    refine lt_of_lt_of_le (sub_one_lt (N : ℝ)) ?_
    have hdiv : (1 : ℝ) / log (log N) ≤ (1 : ℝ) / 6 := by
      have h6 : (0 : ℝ) < 6 := by
        norm_num
      exact one_div_le_one_div_of_le h6 hN1
    have hbound : (log (log N))⁻¹ ≤ (99 : ℝ) / 100 := by
      have haux : (1 : ℝ) / 6 ≤ (99 : ℝ) / 100 := by
        norm_num
      have hdiv' : (log (log N))⁻¹ ≤ (1 : ℝ) / 6 := by
        simpa [one_div] using hdiv
      exact hdiv'.trans haux
    have hexp : (1 : ℝ) ≤ (1 - (log (log N))⁻¹) * (100 : ℝ) := by
      nlinarith
    have hpow :
        (N : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (100 : ℝ)) := by
      have hpow' :
          (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (100 : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp
      simpa using hpow'
    exact le_trans hpow <| by
      apply le_of_eq
      symm
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
      congr 2
  have hratio :
      1 <
        (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 100 : ℝ) := by
    exact (one_lt_div_iff).2 <| Or.inl ⟨show 0 < (log N) ^ (1 / 100 : ℝ) by positivity, hTq⟩
  rw [Real.rpow_neg hN8.le, one_div]
  rw [inv_lt_iff_one_lt_mul₀ (Real.rpow_pos_of_pos hN6 _)]
  calc
    1 <
        log (log N) *
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 100 : ℝ)) :=
      one_lt_mul_of_lt_of_le hN4 hratio.le
    _ = log (log N) *
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) *
            ((log N) ^ (1 / 100 : ℝ))⁻¹) := by
          rw [div_eq_mul_inv]
    _ = ((log N) ^ (1 / 100 : ℝ))⁻¹ * log (log N) *
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
          ac_rfl

end UnitFractions
