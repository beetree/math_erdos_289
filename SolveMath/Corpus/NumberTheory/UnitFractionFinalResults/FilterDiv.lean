module

public import SolveMath.Corpus.NumberTheory.UnitFractionFinalResults.PrimeCountingSieve

@[expose] public section

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter _root_.Finset Real
open _root_.Finset

attribute [local instance] Classical.propDecidable

lemma plogp_tail_bound (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ,
      0 < c ∧
        ∀ᶠ N in (atTop : Filter ℕ),
          ∀ z : ℝ,
            0 ≤ log (log ⌊z⌋₊) →
              ((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => a / (log (x / 4) * x)) ≤
                c * log (log ⌊z⌋₊) / log ((N : ℝ) / 4) := by
  obtain ⟨c₁, hmertens⟩ := Filter.eventually_atTop.mp explicit_mertens
  let c : ℝ := a * 2
  refine ⟨c, mul_pos ha zero_lt_two, ?_⟩
  filter_upwards [eventually_gt_atTop 4, eventually_ge_atTop c₁] with N h4N hcN
  have h0Nnat : 0 < N := by omega
  have h0N : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h0Nnat
  have hlogN : 0 < log ((N : ℝ) / 4) := by
    refine Real.log_pos ?_
    rw [one_lt_div zero_lt_four]
    exact_mod_cast h4N
  intro z hz'
  by_cases hz : (N : ℝ) ≤ z
  · have hNz : N ≤ ⌊z⌋₊ := by
      rw [Nat.le_floor_iff' (Nat.ne_of_gt h0Nnat)]
      exact hz
    calc
      ((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => a / (log (x / 4) * x)) ≤
          ((Icc N ⌊z⌋₊).filter Nat.Prime).sum
            (fun x => (a / log ((N : ℝ) / 4)) * (1 / x : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
        rcases Finset.mem_Icc.mp hpIcc with ⟨hpN, hpz⟩
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
        have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpN
        have hlogp : 0 < log ((p : ℝ) / 4) := by
          refine Real.log_pos ?_
          rw [one_lt_div zero_lt_four]
          exact_mod_cast lt_of_lt_of_le h4N hpN
        have hlogNp : log ((N : ℝ) / 4) ≤ log ((p : ℝ) / 4) := by
          refine Real.log_le_log (div_pos h0N zero_lt_four) ?_
          exact div_le_div_of_nonneg_right hNp zero_lt_four.le
        have hrecip :
            1 / log ((p : ℝ) / 4) ≤ 1 / log ((N : ℝ) / 4) :=
          one_div_le_one_div_of_le hlogN hlogNp
        have hdiv :=
          mul_le_mul_of_nonneg_left hrecip (div_nonneg ha.le hp0.le)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      _ = (a / log ((N : ℝ) / 4)) *
            (((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => (1 / x : ℝ))) := by
        rw [← Finset.mul_sum]
      _ ≤ (a / log ((N : ℝ) / 4)) *
            ((((range (⌊z⌋₊ + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ha.le hlogN.le)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqPrime⟩
          rcases Finset.mem_Icc.mp hqIcc with ⟨_, hqz⟩
          exact
            Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hqz), hqPrime.isPrimePow⟩
        · intro n _ _
          exact one_div_nonneg.2 (Nat.cast_nonneg n)
      _ ≤ (a / log ((N : ℝ) / 4)) * (2 * log (log ⌊z⌋₊)) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ha.le hlogN.le)
        exact hmertens ⌊z⌋₊ (le_trans hcN hNz)
      _ = c * log (log ⌊z⌋₊) / log ((N : ℝ) / 4) := by
        dsimp [c]
        ring
  · have hIcc : Icc N ⌊z⌋₊ = ∅ := by
      refine Finset.Icc_eq_empty_of_lt ?_
      exact (Nat.floor_lt' (Nat.ne_of_gt h0Nnat)).2 (lt_of_not_ge hz)
    rw [hIcc, Finset.filter_empty, Finset.sum_empty]
    refine div_nonneg ?_ hlogN.le
    exact mul_nonneg (by
      dsimp [c]
      positivity) hz'

lemma filter_div_aux (a b c d : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∃ y z w : ℝ,
      2 ≤ y ∧
        16 ≤ w ∧
          0 < z ∧
            1 < z ∧
              4 * y + 4 ≤ z ∧
                a ≤ y ∧
                  d ≤ y ∧
                    log w / log z ≤ b ∧
                      ((Icc ⌈w⌉₊ ⌊z⌋₊).filter Nat.Prime).sum
                          (fun x => log y / (log (x / 4) * x)) ≤
                        c := by
  let y : ℝ := max 2 (max a d)
  have hlogy : 0 < log y := by
    refine Real.log_pos ?_
    exact lt_of_lt_of_le one_lt_two (le_max_left _ _)
  obtain ⟨C₁, h0C₁, htail⟩ := plogp_tail_bound (log y) hlogy
  rw [Filter.eventually_atTop] at htail
  obtain ⟨C₂', htail'⟩ := htail
  let C₂ : ℝ := max 1 C₂'
  let ε : ℝ := c * b / (2 * C₁)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have haux := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound hε
  have haux' := Real.tendsto_log_atTop.eventually haux
  rw [Filter.eventually_atTop] at haux'
  obtain ⟨C₃, haux'⟩ := haux'
  let z : ℝ :=
    max (exp (log 4 * 2 / b))
      (max C₃
        (max 3
          (max (4 * y + 4)
            (max (exp (exp (log (16 / 4) * c / C₁)) + 1)
              (exp (exp (log (C₂ / 4) * c / C₁)) + 1)))))
  let w : ℝ := 4 * exp (C₁ * log (log ⌊z⌋₊) / c)
  have hz₁ : exp (log 4 * 2 / b) ≤ z := by
    exact le_max_left _ _
  have hz₂ : C₃ ≤ z := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hz₄' : 3 ≤ z := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hz₄ : 2 < z := by
    refine lt_of_lt_of_le ?_ hz₄'
    norm_num
  have hz₅ : exp 1 < z := by
    refine lt_of_lt_of_le ?_ hz₄'
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hz₆ : 4 * y + 4 ≤ z := by
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hzfloor : z - 1 ≤ ⌊z⌋₊ := by
    rw [sub_le_iff_le_add]
    exact le_of_lt (Nat.lt_floor_add_one _)
  have hz₃ : 1 ≤ z := le_trans one_le_two (le_of_lt hz₄)
  have hz₀ : 0 < z := lt_of_lt_of_le zero_lt_one hz₃
  have hz₈' : exp (exp (log (16 / 4) * c / C₁)) + 1 ≤ z := by
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hz₉' : exp (exp (log (C₂ / 4) * c / C₁)) + 1 ≤ z := by
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hz₈ : log (16 / 4) * c / C₁ ≤ log (log ⌊z⌋₊) := by
    rw [← exp_le_exp, Real.exp_log, ← exp_le_exp, Real.exp_log]
    · refine le_trans ?_ hzfloor
      rw [le_sub_iff_add_le]
      exact hz₈'
    · exact_mod_cast Nat.floor_pos.mpr hz₃
    · refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      rw [lt_sub_iff_add_lt]
      linarith
  have hz₉ : log (C₂ / 4) * c / C₁ ≤ log (log ⌊z⌋₊) := by
    rw [← exp_le_exp, Real.exp_log, ← exp_le_exp, Real.exp_log]
    · refine le_trans ?_ hzfloor
      rw [le_sub_iff_add_le]
      exact hz₉'
    · exact_mod_cast Nat.floor_pos.mpr hz₃
    · refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      rw [lt_sub_iff_add_lt]
      linarith
  have hz₇ : 0 ≤ log (log ⌊z⌋₊) := by
    refine le_trans ?_ hz₈
    refine div_nonneg ?_ h0C₁.le
    refine mul_nonneg ?_ hc.le
    exact Real.log_nonneg (by norm_num)
  have hzw : exp (log w / b) ≤ z := by
    have hlogz : 0 < log z := Real.log_pos (lt_trans one_lt_two hz₄)
    have hloglogz : log (log z) ≤ ε * log z := by
      specialize haux' z hz₂
      have hloglogz_pos : 0 < log (log z) := by
        refine Real.log_pos ?_
        rw [← Real.exp_lt_exp, Real.exp_log hz₀]
        exact hz₅
      rw [Real.norm_eq_abs, abs_of_pos hloglogz_pos, Real.rpow_one, Real.norm_eq_abs,
        abs_of_pos hlogz] at haux'
      exact haux'
    have hlogfloor_pos : 0 < log ⌊z⌋₊ := by
      refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      linarith
    have hloglogfloor_le : log (log ⌊z⌋₊) ≤ log (log z) := by
      refine Real.log_le_log hlogfloor_pos ?_
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast Nat.floor_pos.mpr hz₃
      · exact_mod_cast Nat.floor_le hz₀.le
    have hfirst' : log 4 * 2 / b ≤ log z := by
      rw [← Real.exp_le_exp, Real.exp_log hz₀]
      exact hz₁
    have hfirst : log 4 / b ≤ log z / 2 := by
      have hfirst'' : (log 4 * 2 / b) / 2 ≤ log z / 2 := by
        exact div_le_div_of_nonneg_right hfirst' zero_le_two
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfirst''
    have hsecond' : log (log ⌊z⌋₊) ≤ ε * log z := by
      exact le_trans hloglogfloor_le hloglogz
    have hsecond :
        C₁ * log (log ⌊z⌋₊) / c / b ≤ log z / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_left hsecond' (show 0 ≤ C₁ / c / b by positivity)
      calc
        C₁ * log (log ⌊z⌋₊) / c / b = (C₁ / c / b) * log (log ⌊z⌋₊) := by ring
        _ ≤ (C₁ / c / b) * (ε * log z) := by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = log z / 2 := by
          dsimp [ε]
          field_simp [h0C₁.ne', hc.ne', hb.ne']
    have hlogw :
        log w / b ≤ log z := by
      rw [show log w = log 4 + C₁ * log (log ⌊z⌋₊) / c by
          rw [show w = 4 * exp (C₁ * log (log ⌊z⌋₊) / c) by rfl,
            Real.log_mul zero_lt_four.ne' (Real.exp_ne_zero _), Real.log_exp],
        add_div]
      have hsum : log 4 / b + (C₁ * log (log ⌊z⌋₊) / c) / b ≤ log z / 2 + log z / 2 := by
        exact add_le_add hfirst hsecond
      simpa [add_halves] using hsum
    rw [← Real.exp_log hz₀]
    exact Real.exp_le_exp.mpr hlogw
  have h16w : 16 ≤ w := by
    have hmain : log (16 / 4) ≤ C₁ * log (log ⌊z⌋₊) / c := by
      have hmul := mul_le_mul_of_nonneg_left hz₈ (show 0 ≤ C₁ / c by positivity)
      calc
        log (16 / 4) = (C₁ / c) * (log (16 / 4) * c / C₁) := by
          field_simp [h0C₁.ne', hc.ne']
        _ ≤ (C₁ / c) * log (log ⌊z⌋₊) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = C₁ * log (log ⌊z⌋₊) / c := by ring
    have hexp : (16 : ℝ) / 4 ≤ exp (C₁ * log (log ⌊z⌋₊) / c) := by
      simpa [Real.exp_log (by norm_num : 0 < (16 : ℝ) / 4)] using Real.exp_le_exp.mpr hmain
    calc
      (16 : ℝ) = 4 * ((16 : ℝ) / 4) := by norm_num
      _ ≤ 4 * exp (C₁ * log (log ⌊z⌋₊) / c) := by
        exact mul_le_mul_of_nonneg_left hexp zero_le_four
      _ = w := by rfl
  have hC₂w : C₂ ≤ w := by
    have hC₂ : (0 : ℝ) < C₂ := by
      dsimp [C₂]
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hmain : log (C₂ / 4) ≤ C₁ * log (log ⌊z⌋₊) / c := by
      have hmul := mul_le_mul_of_nonneg_left hz₉ (show 0 ≤ C₁ / c by positivity)
      calc
        log (C₂ / 4) = (C₁ / c) * (log (C₂ / 4) * c / C₁) := by
          field_simp [h0C₁.ne', hc.ne']
        _ ≤ (C₁ / c) * log (log ⌊z⌋₊) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = C₁ * log (log ⌊z⌋₊) / c := by ring
    have hexp : C₂ / 4 ≤ exp (C₁ * log (log ⌊z⌋₊) / c) := by
      simpa [Real.exp_log (div_pos hC₂ zero_lt_four)] using Real.exp_le_exp.mpr hmain
    calc
      C₂ = 4 * (C₂ / 4) := by field_simp [zero_lt_four.ne']
      _ ≤ 4 * exp (C₁ * log (log ⌊z⌋₊) / c) := by
        exact mul_le_mul_of_nonneg_left hexp zero_le_four
      _ = w := by rfl
  have h0w' : (1 : ℝ) < ⌈w⌉₊ / 4 := by
    rw [lt_div_iff₀ zero_lt_four]
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    refine lt_of_lt_of_le ?_ h16w
    norm_num
  refine ⟨y, z, w, le_max_left _ _, h16w, hz₀, lt_trans one_lt_two hz₄, hz₆,
    le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _), ?_, ?_⟩
  · have hlogwz : log w / b ≤ log z := by
      have htmp : exp (log w / b) ≤ exp (log z) := by
        simpa [Real.exp_log hz₀] using hzw
      exact Real.exp_le_exp.mp htmp
    refine (div_le_iff₀ (Real.log_pos (lt_trans one_lt_two hz₄))).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using (div_le_iff₀ hb).mp hlogwz
  · have h₁ : C₂' ≤ ⌈w⌉₊ := by
      have h₁r : (C₂' : ℝ) ≤ ⌈w⌉₊ := by
        exact le_trans (le_max_right _ _) (le_trans hC₂w (Nat.le_ceil w))
      exact_mod_cast h₁r
    refine le_trans (htail' ⌈w⌉₊ h₁ z hz₇) ?_
    have hlogceil : C₁ * log (log ⌊z⌋₊) / c ≤ log (⌈w⌉₊ / 4) := by
      rw [← Real.exp_le_exp, Real.exp_log (lt_trans zero_lt_one h0w')]
      calc
        exp (C₁ * log (log ⌊z⌋₊) / c) = w / 4 := by
          dsimp [w]
          field_simp
        _ ≤ ⌈w⌉₊ / 4 := by
          exact div_le_div_of_nonneg_right (Nat.le_ceil w) zero_le_four
    have hnum : C₁ * log (log ⌊z⌋₊) / log (⌈w⌉₊ / 4) ≤ c := by
      refine (div_le_iff₀ (Real.log_pos h0w')).2 ?_
      have hmul := mul_le_mul_of_nonneg_left hlogceil hc.le
      calc
        C₁ * log (log ⌊z⌋₊) = c * (C₁ * log (log ⌊z⌋₊) / c) := by
          field_simp [hc.ne']
        _ ≤ c * log (⌈w⌉₊ / 4) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hnum

lemma filter_div (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        4 * y + 4 ≤ z ∧
          0 < z ∧
            2 / (1 / (5 * D * 2) * D) ≤ y ∧
              2 / (1 / (5 * D * 2)) ≤ y ∧
                ∀ᶠ N in (atTop : Filter ℕ),
                  ∀ A ⊆ range N,
                    ((A.filter fun n =>
                          ¬ ∃ d₁ d₂ : ℕ,
                              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧
                                4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
                      ℝ) ≤
                      (N : ℝ) / (5 * D) := by
  rcases sieve_lemma_prec' with ⟨C, c, h0C, h0c, hsieve⟩
  have haux1 : 0 < (1 / (10 * D)) / C := by
    refine div_pos ?_ h0C
    rw [one_div_pos]
    refine mul_pos ?_ hD
    norm_num
  have haux2 : 0 < (1 / (20 * D)) / C := by
    refine div_pos ?_ h0C
    rw [one_div_pos]
    refine mul_pos ?_ hD
    norm_num
  rw [Filter.eventually_atTop] at hsieve
  rcases hsieve with ⟨T, hsieve⟩
  rcases
      (filter_div_aux (2 / (1 / (5 * D * 2) * D)) ((1 / (10 * D)) / C) ((1 / (20 * D)) / C)
          (2 / (1 / (5 * D * 2))) haux1 haux2) with
    ⟨y, z, w, h2y, h16w, h0z, h1z, hyz, hDy, hDy', hwzD', hzsum⟩
  have hwzD : C * (log w / log z) ≤ 1 / (10 * D) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (le_div_iff₀ h0C).mp hwzD'
  have h2w : 2 ≤ w := by
    refine le_trans ?_ h16w
    norm_num
  have h1y : 1 ≤ y := le_trans one_le_two h2y
  have h0zc : (0 : ℝ) < ⌊z⌋₊ := by
    exact_mod_cast Nat.floor_pos.mpr (le_of_lt h1z)
  refine ⟨y, z, h1y, hyz, h0z, hDy, hDy', ?_⟩
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((T : ℝ) * ⌊z⌋₊))
    , tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop
          ((((Icc ⌈w⌉₊ ⌊z⌋₊).filter Nat.Prime).sum
              (fun x => C * (log y / log (x / 4) * 1))) *
            (20 * D)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((4 : ℝ) * ⌊z⌋₊ / c + log ⌊z⌋₊))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (z / c))
    , eventually_ge_atTop T ] with N h0N hTzN hweirdN hlogN1 hlogN2 hlarge
  intro A hA
  have hAcard :
      ((A.filter fun n =>
            ¬ ∃ d₁ d₂ : ℕ,
                d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
        ℝ) ≤
        (((range N).filter fun n =>
              ¬ ∃ d₁ d₂ : ℕ,
                  d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
          ℝ) := by
    norm_num
    exact Finset.card_le_card (Finset.filter_subset_filter _ hA)
  refine le_trans hAcard ?_
  have hz' : z ≤ c * log (N : ℝ) := by
    rw [div_le_iff₀ h0c] at hlogN2
    simpa [mul_comm] using hlogN2
  let X :=
    (range N).filter fun n =>
      ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < w ∨ z < p
  let Y :=
    fun m =>
      (range N).filter fun n =>
        m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p
  have hXbound : (X.card : ℝ) ≤ C * (log w / log z) * N := by
    exact hsieve N hlarge w z h2w h1z hz'
  have hYlocbound :
      ∀ m : ℕ,
        16 ≤ m →
          (m : ℝ) / 4 ≤ c * log ⌈(N : ℝ) / m⌉₊ →
            T ≤ ⌈(N : ℝ) / m⌉₊ →
              ((Y m).card : ℝ) ≤ C * (log y / log ((m : ℝ) / 4)) * (N / m + 1) := by
    intro m h16m hm hTm
    have h0m : 0 < m := by
      refine lt_of_lt_of_le ?_ h16m
      norm_num
    have h0m' : (0 : ℝ) < m := by exact_mod_cast h0m
    have h1m' : 1 < (m : ℝ) / 4 := by
      have hm16 : (16 : ℝ) ≤ m := by exact_mod_cast h16m
      nlinarith
    have hcoeff_nonneg : 0 ≤ C * (log y / log ((m : ℝ) / 4)) := by
      refine mul_nonneg h0C.le ?_
      refine div_nonneg ?_ (Real.log_pos h1m').le
      exact Real.log_nonneg (le_trans one_le_two h2y)
    have hcard :
        (Y m).card ≤
          ((range ⌈(N : ℝ) / m⌉₊).filter fun n =>
              ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p).card := by
      refine
        Finset.card_le_card_of_injOn
          (fun i => i / m)
          ?_
          ?_
      · intro n hn
        change n ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at hn
        change
          n / m ∈
            (range ⌈(N : ℝ) / m⌉₊).filter
              (fun n => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p)
        rw [Finset.mem_filter, Finset.mem_range] at hn ⊢
        refine ⟨?_, ?_⟩
        · rw [Nat.lt_ceil, Nat.cast_div hn.2.1 (by exact_mod_cast h0m.ne')]
          exact div_lt_div_of_pos_right (by exact_mod_cast hn.1) h0m'
        · intro p hp hpnm
          rcases hn.2.2 p hp (dvd_trans hpnm (Nat.div_dvd_of_dvd hn.2.1)) with hpy | hmp
          · exact Or.inl hpy
          · right
            rw [div_lt_iff₀ zero_lt_four]
            simpa [mul_comm] using hmp
      · intro a ha b hb hab
        change a ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at ha
        change b ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at hb
        rw [Finset.mem_filter] at ha hb
        have ha' : a = (a / m) * m := by
          exact (Nat.div_eq_iff_eq_mul_left h0m ha.2.1).1 rfl
        have hb' : b = (b / m) * m := by
          exact (Nat.div_eq_iff_eq_mul_left h0m hb.2.1).1 rfl
        rw [ha', hb']
        exact congrArg (fun t => t * m) hab
    have hsieve' :
        (((range ⌈(N : ℝ) / m⌉₊).filter fun n =>
              ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p).card :
          ℝ) ≤
          C * (log y / log ((m : ℝ) / 4)) * ⌈(N : ℝ) / m⌉₊ := by
      exact hsieve ⌈(N : ℝ) / m⌉₊ hTm y ((m : ℝ) / 4) h2y h1m' hm
    refine (Nat.cast_le.2 hcard).trans ?_
    have hceil : (⌈(N : ℝ) / m⌉₊ : ℝ) ≤ N / m + 1 := by
      exact le_of_lt (Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) / m by positivity))
    exact hsieve'.trans (mul_le_mul_of_nonneg_left hceil hcoeff_nonneg)
  let Y' := ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r).biUnion fun p => Y p
  have hcover :
      ((range N).filter fun n =>
          ¬ ∃ d₁ d₂ : ℕ,
              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z) ⊆ X ∪ Y' := by
    intro n hn
    by_cases hXin : n ∈ X
    · exact Finset.mem_union.mpr (Or.inl hXin)
    · have hn_range : n ∈ range N := (Finset.mem_filter.mp hn).1
      have hn_forbid :
          ¬ ∃ d₁ d₂ : ℕ,
              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z :=
        (Finset.mem_filter.mp hn).2
      have hnotX :
          ¬ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < w ∨ z < p := by
        intro hprop
        exact hXin (Finset.mem_filter.mpr ⟨hn_range, hprop⟩)
      rw [Finset.mem_union, Finset.mem_biUnion]
      right
      rw [not_forall] at hnotX
      rcases hnotX with ⟨p, hp⟩
      rw [Classical.not_imp, Classical.not_imp, not_or, not_lt, not_lt] at hp
      refine ⟨p, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, hp.1⟩
        · exact Nat.ceil_le.mpr hp.2.2.1
        · exact (Nat.le_floor_iff' hp.1.ne_zero).mpr hp.2.2.2
      · rw [Finset.mem_filter]
        refine ⟨hn_range, hp.2.1, ?_⟩
        intro q hq hqn
        by_cases hqy : y ≤ q
        · right
          have hp4q : (p : ℝ) < 4 * q := by
            by_contra hp4q
            have h4qp : 4 * q ≤ p := by exact_mod_cast not_lt.mp hp4q
            exact hn_forbid ⟨q, p, hqn, hp.2.1, hqy, h4qp, hp.2.2.2⟩
          exact hp4q
        · left
          exact lt_of_not_ge hqy
  calc
    ((((range N).filter fun n =>
            ¬ ∃ d₁ d₂ : ℕ,
                d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
        ℝ)) ≤ ((X ∪ Y').card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
    _ ≤ (X.card : ℝ) + (Y'.card : ℝ) := by
      exact_mod_cast Finset.card_union_le X Y'
    _ ≤ C * (log w / log z) * N + (Y'.card : ℝ) := by
      rw [add_le_add_iff_right]
      exact hXbound
    _ ≤
        (C * (log w / log z) * N +
          Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
            (fun p => ((Y p).card : ℝ))) := by
      rw [add_le_add_iff_left]
      exact_mod_cast Finset.card_biUnion_le
    _ ≤
        (C * (log w / log z) * N +
          Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
            (fun p => C * (log y / log (p / 4)) * (N / p + 1))) := by
      rw [add_le_add_iff_left]
      refine Finset.sum_le_sum ?_
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      have h16p : 16 ≤ p := by
        have h16ceil : 16 ≤ ⌈w⌉₊ := by
          have h16ceilR : (16 : ℝ) ≤ ⌈w⌉₊ := le_trans h16w (Nat.le_ceil w)
          exact_mod_cast h16ceilR
        exact le_trans h16ceil hp.1.1
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos hp.2
      refine hYlocbound p h16p ?_ ?_
      · have hp_le_floor : (p : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast hp.1.2
        have hfloorlog_div : (4 : ℝ) * ⌊z⌋₊ / c ≤ log ((N : ℝ) / ⌊z⌋₊) := by
          rw [Real.log_div h0N.ne' h0zc.ne', le_sub_iff_add_le]
          exact hlogN1
        have hfloorlog : (4 : ℝ) * ⌊z⌋₊ ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          rw [div_le_iff₀ h0c] at hfloorlog_div
          simpa [mul_comm, mul_left_comm, mul_assoc] using hfloorlog_div
        have hfloor_le : (⌊z⌋₊ : ℝ) ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          have hfloor_nonneg : (0 : ℝ) ≤ ⌊z⌋₊ := by positivity
          nlinarith
        have hp4_le : (p : ℝ) / 4 ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          have hp4_le_floor : (p : ℝ) / 4 ≤ ⌊z⌋₊ := by
            nlinarith
          exact le_trans hp4_le_floor hfloor_le
        have hquot : (N : ℝ) / ⌊z⌋₊ ≤ (N : ℝ) / p := by
          exact div_le_div_of_nonneg_left h0N.le hp_pos hp_le_floor
        have hlogquot : log ((N : ℝ) / ⌊z⌋₊) ≤ log ((N : ℝ) / p) := by
          exact Real.log_le_log (div_pos h0N h0zc) hquot
        have hlogceil : log ((N : ℝ) / p) ≤ log ⌈(N : ℝ) / p⌉₊ := by
          refine Real.log_le_log (div_pos h0N hp_pos) ?_
          exact Nat.le_ceil _
        exact le_trans hp4_le (mul_le_mul_of_nonneg_left (le_trans hlogquot hlogceil) h0c.le)
      · rw [← Nat.cast_le (α := ℝ)]
        refine le_trans ?_ (Nat.le_ceil _)
        by_cases h0T : (0 : ℝ) < T
        · rw [le_div_iff₀ hp_pos]
          refine le_trans ?_ hTzN
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hp.1.2) h0T.le
        · exact (le_of_not_gt h0T).trans (by positivity)
    _ ≤ (N : ℝ) / (10 * D) + (N : ℝ) / (10 * D) := by
      refine add_le_add ?_ ?_
      · have htmp := mul_le_mul_of_nonneg_right hwzD h0N.le
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      · simp_rw [mul_assoc, mul_add]
        rw [Finset.sum_add_distrib]
        have hsum20 :
            Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                (fun p => C * (log y / log (p / 4)) * (N / p)) +
              Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                (fun p => C * (log y / log (p / 4)) * 1) ≤
              (N : ℝ) / (20 * D) + (N : ℝ) / (20 * D) := by
          refine add_le_add ?_ ?_
          · have hzsumC :
                C *
                    Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                      (fun p => log y / (log (p / 4) * p)) ≤
                  1 / (20 * D) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using (le_div_iff₀ h0C).mp hzsum
            have hEq :
                Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => C * (log y / log (p / 4)) * (N / p)) =
                  (N : ℝ) *
                    (C *
                      Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                        (fun p => log y / (log (p / 4) * p))) := by
              calc
                Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => C * (log y / log (p / 4)) * (N / p)) =
                  Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => (N : ℝ) * (C * (log y / (log (p / 4) * p)))) := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      have hp0 : p ≠ 0 := (Nat.Prime.pos (Finset.mem_filter.mp hp).2).ne'
                      field_simp [hp0]
                _ = (N : ℝ) *
                    Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                      (fun p => C * (log y / (log (p / 4) * p))) := by
                      rw [Finset.mul_sum]
                _ = (N : ℝ) *
                    (C *
                      Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                        (fun p => log y / (log (p / 4) * p))) := by
                      rw [← Finset.mul_sum]
            rw [hEq]
            have htmp := mul_le_mul_of_nonneg_left hzsumC h0N.le
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
          · refine (le_div_iff₀ ?_).2 ?_
            · refine mul_pos ?_ hD
              norm_num
            · simpa [mul_assoc] using hweirdN
        have hsum10 : (N : ℝ) / (D * 20) + (N : ℝ) / (D * 20) = (N : ℝ) / (D * 10) := by
          field_simp [hD.ne']
          ring
        simpa [mul_assoc, mul_left_comm, mul_comm, hsum10] using hsum20
    _ = (N : ℝ) / (5 * D) := by
      field_simp [hD.ne']
      ring

lemma turan_primes_estimate :
    ∃ C : ℝ,
      ∀ᶠ N in (atTop : Filter ℕ),
        (Icc 1 N).sum (fun n => ((ω n : ℝ) - log (log (N : ℝ))) ^ 2) ≤
          C * (N : ℝ) * log (log (N : ℝ)) := by
  rcases sum_prime_counting with ⟨C1, hsum⟩
  rcases sum_prime_counting_sq with ⟨C2, hsumsq⟩
  let C : ℝ := C2 + 2 * C1
  refine ⟨C, ?_⟩
  filter_upwards
    [ hsum
    , hsumsq
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with N hlargeSum hlargeSumSq hlargeN
  have hcardIcc : (Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  let L : ℝ := log (log (N : ℝ))
  let S1 : ℝ := (Icc 1 N).sum fun x => (ω x : ℝ)
  let S2 : ℝ := (Icc 1 N).sum fun x => (ω x : ℝ) ^ 2
  have hsum' : (N : ℝ) * L - C1 * N ≤ S1 := by
    simpa [L, S1, mul_assoc, mul_left_comm, mul_comm] using hlargeSum
  have hsumsq' : S2 ≤ (N : ℝ) * L ^ 2 + C2 * N * L := by
    simpa [L, S2, mul_assoc, mul_left_comm, mul_comm] using hlargeSumSq
  have hmul :
      (2 * L) * ((N : ℝ) * L - C1 * N) ≤ (2 * L) * S1 := by
    refine mul_le_mul_of_nonneg_left hsum' ?_
    positivity
  have hexpand :
      (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) =
        S2 - 2 * L * S1 + (N : ℝ) * L ^ 2 := by
    simp_rw [sub_sq, S1, S2]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcardIcc]
    ring
  rw [hexpand]
  dsimp [C]
  nlinarith

lemma filter_regular (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N in (atTop : Filter ℕ),
      ∀ A ⊆ range N,
        ((A.filter fun n : ℕ =>
              n ≠ 0 ∧
                ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
                    (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))).card :
          ℝ) ≤
          (N : ℝ) / D := by
  rcases turan_primes_estimate with ⟨C, hturan⟩
  have h100 : (0 : ℝ) < 1 / 100 := by norm_num
  filter_upwards
    [ hturan
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (C / (1 / 100) / (1 / D * (1 / 100))))
    , tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ)) ] with
      N hNturan hlargeN hlargeN2 hlargeN3
  intro A hA
  by_contra h
  rw [not_le] at h
  let A' :=
    A.filter fun n : ℕ =>
      n ≠ 0 ∧
        ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
            (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))
  let L : ℝ := log (log (N : ℝ))
  let ε : ℝ := (1 / 100 : ℝ) * L
  have hcontr : C * (N : ℝ) * L < (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
    have hstep1 : C * (N : ℝ) * L ≤ ((N : ℝ) / D) * ε ^ 2 := by
      have htmp := hlargeN2
      dsimp [L] at htmp
      have hpos1 : 0 < (1 / D * (1 / 100 : ℝ)) := by positivity
      have hpos2 : 0 < (1 / 100 : ℝ) := by norm_num
      rw [div_le_iff₀ hpos1, div_le_iff₀ hpos2] at htmp
      have hNL_nonneg : 0 ≤ (N : ℝ) * L := mul_nonneg hlargeN3.le hlargeN.le
      calc
        C * (N : ℝ) * L = C * ((N : ℝ) * L) := by ring
        _ ≤ (L * (1 / D * (1 / 100 : ℝ)) * (1 / 100 : ℝ)) * ((N : ℝ) * L) := by
          exact mul_le_mul_of_nonneg_right htmp hNL_nonneg
        _ = ((N : ℝ) / D) * ε ^ 2 := by
          dsimp [ε]
          ring
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos <| by
      dsimp [ε]
      refine mul_pos ?_ hlargeN
      norm_num
    have hstep2 : ((N : ℝ) / D) * ε ^ 2 < (A'.card : ℝ) * ε ^ 2 :=
      mul_lt_mul_of_pos_right h hεsq
    have hstep3 : (A'.card : ℝ) * ε ^ 2 ≤ A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
      calc
        (A'.card : ℝ) * ε ^ 2 = A'.sum (fun _ => ε ^ 2) := by simp [nsmul_eq_mul]
        _ ≤ A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          rw [Finset.mem_filter] at hn
          by_cases hlow : ((99 : ℝ) / 100) * L ≤ ω n
          · have hhigh : 2 * L < (ω n : ℝ) := by
              apply lt_of_not_ge
              intro hupper
              exact hn.2.2 ⟨by simpa using hlow, by simpa using hupper⟩
            have hεle : ε ≤ (ω n : ℝ) - L := by
              dsimp [ε]
              nlinarith
            have hε0 : 0 ≤ ε := by
              dsimp [ε]
              positivity
            have hdiff0 : 0 ≤ (ω n : ℝ) - L := le_trans hε0 hεle
            have hsquare : ε ^ 2 ≤ ((ω n : ℝ) - L) ^ 2 := by
              nlinarith [hεle, hε0, hdiff0]
            simpa using hsquare
          · have hεle : ε ≤ L - ω n := by
              have hlow' : (ω n : ℝ) < (99 : ℝ) / 100 * L := lt_of_not_ge hlow
              dsimp [ε]
              nlinarith
            have hε0 : 0 ≤ ε := by
              dsimp [ε]
              positivity
            have hdiff0 : 0 ≤ L - ω n := le_trans hε0 hεle
            have hsquare : ε ^ 2 ≤ (L - ω n) ^ 2 := by
              nlinarith [hεle, hε0, hdiff0]
            have hsame : (L - ω n) ^ 2 = ((ω n : ℝ) - L) ^ 2 := by ring
            exact hsame ▸ hsquare
    have hstep4 : A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) ≤
        (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
          intro hbad
          rw [hbad, Finset.mem_filter] at hm
          exact hm.2.1 rfl
        · have htempy := hA ((Finset.filter_subset _ _) hm)
          rw [Finset.mem_range] at htempy
          exact le_of_lt htempy
      · intro n _ _
        exact sq_nonneg _
    exact lt_of_lt_of_le (lt_of_le_of_lt hstep1 hstep2) (le_trans hstep3 hstep4)
  exact (not_lt_of_ge (by simpa [L] using hNturan)) hcontr


end UnitFractions
