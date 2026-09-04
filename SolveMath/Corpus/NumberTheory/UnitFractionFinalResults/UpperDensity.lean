module

public import SolveMath.Corpus.NumberTheory.UnitFractionFinalResults.FilterDiv
public import Mathlib.Data.Int.Lemmas

@[expose] public section

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter _root_.Finset Real
open _root_.Finset

attribute [local instance] Classical.propDecidable

lemma log_helper (y : ℝ) (h : 0 < y) (h'' : y ≤ 1 / 2) : -2 * y ≤ log (1 - y) := by
  have hy1 : y < 1 := lt_of_le_of_lt h'' one_half_lt_one
  have hloginv : log ((1 - y)⁻¹) ≤ 2 * y := by
    refine le_trans (Real.log_le_sub_one_of_pos (inv_pos.2 (sub_pos.2 hy1))) ?_
    have hyinv_le : (1 - y)⁻¹ ≤ 2 := by
      have htwo : 2 ≤ 1 / y := by
        rw [le_div_iff₀ h]
        linarith
      simpa [one_div, inv_inv, h.ne'] using sub_one_div_inv_le_two (a := 1 / y) htwo
    have hy_nonneg : 0 ≤ y := h.le
    have hy1_ne : 1 - y ≠ 0 := sub_ne_zero.mpr (ne_of_lt hy1).symm
    calc
      (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by
        field_simp [hy1_ne]
        ring_nf
      _ ≤ y * 2 := mul_le_mul_of_nonneg_left hyinv_le hy_nonneg
      _ = 2 * y := by ring
  have hneglog : -log (1 - y) ≤ 2 * y := by
    simpa [Real.log_inv] using hloginv
  linarith

lemma diff_mertens_sum_hlarge4 {N : ℕ}
    (hlogN : 0 < log (N : ℝ))
    (hloglogN : 0 < log (log (N : ℝ)))
    (hlarge5 : ‖log ((log ∘ Nat.cast) N)‖ ≤ (1 / 8 : ℝ) * ‖((log ∘ Nat.cast) N) ^ (1 : ℝ)‖) :
    log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ) := by
  have hmain : log (log (N : ℝ)) ≤ (1 / 8 : ℝ) * log (N : ℝ) := by
    simpa [Function.comp, Real.norm_eq_abs, abs_of_pos hloglogN, abs_of_nonneg hlogN.le,
      Real.rpow_one] using hlarge5
  nlinarith

lemma diff_mertens_sum_hsumM {N : ℕ} {b c M : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (hlogN : 0 < log (N : ℝ))
    (h8loglogN : 8 < log (log (N : ℝ)))
    (hlarge2' :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹) :
    log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
        c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹ ≤
      (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
  have h0N : 0 < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by
      intro hN
      subst hN
      norm_num at hlogN)
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  have hfactor_pos : 0 < (1 : ℝ) - 8 / log (log (N : ℝ)) := by
    rw [sub_pos, div_lt_one h0loglogN]
    exact h8loglogN
  have hlogM :
      log M = (1 - 8 / log (log (N : ℝ))) * log (N : ℝ) := by
    rw [hM, Real.log_rpow h0N]
  have hloglogM :
      log (log M) = log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) := by
    rw [hlogM, Real.log_mul hfactor_pos.ne' hlogN.ne']
  have hlower := sub_le_of_abs_sub_le_left hlarge2'
  rw [hloglogM, hlogM] at hlower
  exact hlower

lemma diff_mertens_sum_hstep1 {N : ℕ} {M : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h8loglogN : 8 < log (log (N : ℝ))) :
    ((range N).filter fun (r : ℕ) =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
        (fun q => (q : ℝ)⁻¹) ≤
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
        (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
  let A : Finset ℕ := (Finset.Icc 1 N).filter IsPrimePow
  let B : Finset ℕ := (Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow
  let S : Finset ℕ :=
    (range N).filter fun r : ℕ =>
      IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)
  have hN0 : N ≠ 0 := by
    intro hN
    subst hN
    norm_num at h8loglogN
  have h1leN : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  have hMleN : M ≤ (N : ℝ) := by
    rw [hM]
    calc
      (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) ≤ (N : ℝ) ^ (1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le h1leN ?_
        have hnonneg : 0 ≤ 8 / log (log (N : ℝ)) := by positivity
        linarith
      _ = (N : ℝ) := by simp
  have hfloorMleN : ⌊M⌋₊ ≤ N := Nat.floor_le_of_le hMleN
  have hBsubA : B ⊆ A := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqpp⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, hqM⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_Icc.mpr ⟨hq1, le_trans hqM hfloorMleN⟩, hqpp⟩
  have hSsub : S ⊆ A \ B := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqrange, hqprop⟩
    rcases hqprop with ⟨hqpp, hMq⟩
    have hqA : q ∈ A := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨
        Finset.mem_Icc.mpr
          ⟨Nat.succ_le_of_lt hqpp.pos, le_of_lt (Finset.mem_range.mp hqrange)⟩,
        hqpp
      ⟩
    have hqnotB : q ∉ B := by
      intro hqB
      rcases Finset.mem_filter.mp hqB with ⟨hqIcc, _hqpp⟩
      rcases Finset.mem_Icc.mp hqIcc with ⟨_hq1, hqM⟩
      have hfloorMltq : ⌊M⌋₊ < q := by
        exact (Nat.floor_lt' (Nat.ne_of_gt hqpp.pos)).2 (by simpa [hM] using hMq)
      exact not_lt_of_ge hqM hfloorMltq
    exact Finset.mem_sdiff.mpr ⟨hqA, hqnotB⟩
  have hsum_le : S.sum (fun q => (q : ℝ)⁻¹) ≤ (A \ B).sum (fun q => (q : ℝ)⁻¹) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hSsub ?_
    intro q _hq _hnot
    have hq_nonneg : 0 ≤ (q : ℝ) := by
      exact_mod_cast Nat.zero_le q
    exact inv_nonneg.2 hq_nonneg
  calc
    ((range N).filter fun (r : ℕ) =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
        (fun q => (q : ℝ)⁻¹) = S.sum (fun q => (q : ℝ)⁻¹) := by
          rfl
    _ ≤ (A \ B).sum (fun q => (q : ℝ)⁻¹) := hsum_le
    _ = A.sum (fun q => (q : ℝ)⁻¹) - B.sum (fun q => (q : ℝ)⁻¹) := by
      exact Finset.sum_sdiff_eq_sub hBsubA
    _ = (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
      rfl

lemma diff_mertens_sum_hstep4 {N : ℕ} {b c C : ℝ}
    (hC : C = c / 2 + 16)
    (h0c : 0 < c)
    (hlogN : 0 < log (N : ℝ))
    (hloglogN : 0 < log (log (N : ℝ)))
    (h8loglogN : 8 < log (log (N : ℝ)))
    (h16loglogN : 16 ≤ log (log (N : ℝ)))
    (hlarge4 : log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ)) :
    c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
        (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) ≤
      C / log (log (N : ℝ)) := by
  let L : ℝ := log (log (N : ℝ))
  let X : ℝ := log (N : ℝ)
  have hL : 0 < L := hloglogN
  have hX : 0 < X := hlogN
  have hy_pos : 0 < 8 / L := by
    positivity
  have hy_le : 8 / L ≤ (1 / 2 : ℝ) := by
    field_simp [hL.ne']
    nlinarith
  have hone_sub_pos : 0 < 1 - 8 / L := by
    rw [sub_pos]
    exact (div_lt_one hL).2 h8loglogN
  have hlog_term : -log (1 - 8 / L) ≤ 16 / L := by
    have htmp := log_helper (y := 8 / L) hy_pos hy_le
    have htmp' : -log (1 - 8 / L) ≤ 2 * (8 / L) := by
      linarith
    convert htmp' using 1
    ring_nf
  have hX_ge : 8 * L ≤ X := by
    nlinarith
  have hterm1 : c * X⁻¹ ≤ c / (8 * L) := by
    rw [div_eq_mul_inv]
    have h_inv : X⁻¹ ≤ (8 * L)⁻¹ := by
      have h8L_pos : 0 < 8 * L := by positivity
      simpa [one_div] using one_div_le_one_div_of_le h8L_pos hX_ge
    refine mul_le_mul_of_nonneg_left ?_ h0c.le
    exact h_inv
  have hprod_ge : 4 * L ≤ (1 - 8 / L) * X := by
    have hhalf_le : (1 / 2 : ℝ) ≤ 1 - 8 / L := by
      nlinarith
    have hhalfX : 4 * L ≤ (1 / 2 : ℝ) * X := by
      nlinarith
    have hhalfX_le : (1 / 2 : ℝ) * X ≤ (1 - 8 / L) * X := by
      exact mul_le_mul_of_nonneg_right hhalf_le hX.le
    exact le_trans hhalfX hhalfX_le
  have hterm2 : c * (((1 - 8 / L) * X)⁻¹) ≤ c / (4 * L) := by
    rw [div_eq_mul_inv]
    have hprod_pos : 0 < (1 - 8 / L) * X := mul_pos hone_sub_pos hX
    have h4L_pos : 0 < 4 * L := by positivity
    have h_inv : ((1 - 8 / L) * X)⁻¹ ≤ (4 * L)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le h4L_pos hprod_ge
    refine mul_le_mul_of_nonneg_left ?_ h0c.le
    exact h_inv
  have hsum_c : c * X⁻¹ + c * (((1 - 8 / L) * X)⁻¹) ≤ c / (2 * L) := by
    have hsum' := add_le_add hterm1 hterm2
    refine hsum'.trans ?_
    field_simp [hL.ne']
    nlinarith
  have hleft :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) =
        c * X⁻¹ - log (1 - 8 / L) + c * (((1 - 8 / L) * X)⁻¹) := by
    simp [L, X, abs_of_pos hX, abs_of_pos (mul_pos hone_sub_pos hX)]
    ring
  have hright : c / (2 * L) + 16 / L = C / log (log (N : ℝ)) := by
    change c / (2 * L) + 16 / L = C / L
    rw [hC]
    field_simp [hL.ne']
  calc
    c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
        (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) =
      c * X⁻¹ - log (1 - 8 / L) + c * (((1 - 8 / L) * X)⁻¹) := hleft
    _ ≤ c / (2 * L) + 16 / L := by
      nlinarith [hsum_c, hlog_term]
    _ = C / log (log (N : ℝ)) := hright

lemma diff_mertens_sum :
    ∃ c : ℝ,
      ∀ᶠ N in (atTop : Filter ℕ),
        ((range N).filter fun (r : ℕ) =>
              IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => (q : ℝ)⁻¹) ≤
          c / log (log (N : ℝ)) := by
  obtain ⟨b, hppr'⟩ := prime_power_reciprocal
  obtain ⟨c, h0c, hppr⟩ := hppr'.exists_pos
  let C : ℝ := c / 2 + 16
  refine ⟨C, ?_⟩
  have haux :=
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
      (show 0 < (1 : ℝ) / 8 by norm_num)
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually hppr.bound
    , (tendsto_pow_rec_loglog_spec_at_top.comp tendsto_natCast_atTop_atTop).eventually hppr.bound
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (8 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (16 : ℝ))
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux ] with
    N h0N hlarge1 hlarge2 hlogN hloglogN h8loglogN h16loglogN hlarge5
  let M : ℝ := (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))
  have hlarge4 : log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ) := by
    exact diff_mertens_sum_hlarge4 hlogN hloglogN hlarge5
  have hlarge1' :
      |(((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log (N : ℝ)) + b)| ≤
        c * |log (N : ℝ)|⁻¹ := by
    simpa [Nat.floor_natCast, norm_inv, norm_eq_abs] using hlarge1
  have hlarge2' :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹ := by
    simpa [M, norm_inv, norm_eq_abs] using hlarge2
  have hsumN :
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) := by
    have htmp := sub_le_of_abs_sub_le_right hlarge1'
    linarith
  have hsumM :
      log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹ ≤
        (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact diff_mertens_sum_hsumM (N := N) (b := b) (c := c) (M := M) rfl hlogN h8loglogN hlarge2'
  have hstep1 :
      ((range N).filter fun (r : ℕ) =>
            IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
          (fun q => (q : ℝ)⁻¹) ≤
        (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact diff_mertens_sum_hstep1 (N := N) (M := M) rfl h8loglogN
  have hstep2 :
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact sub_le_sub_right hsumN _
  have hstep3 :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) := by
    exact sub_le_sub_left hsumM _
  have hstep4 :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) ≤
        C / log (log (N : ℝ)) := by
    exact
      diff_mertens_sum_hstep4 (N := N) (b := b) (c := c) (C := C) rfl h0c hlogN hloglogN
        h8loglogN h16loglogN hlarge4
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

lemma filter_smooth (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N in (atTop : Filter ℕ),
      ∀ A ⊆ range N,
        ((A.filter fun (n : ℕ) =>
              ∃ q : ℕ,
                IsPrimePow q ∧
                  (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
          ℝ) ≤
          (N : ℝ) / D := by
  obtain ⟨c, hdiff⟩ := diff_mertens_sum
  filter_upwards [hdiff,
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (D * 2)),
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (0 : ℝ)),
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (c / (1 / (2 * D)))),
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_gt_atTop (0 : ℝ))] with
    N hdiff' hlarge1 hlarge2 hlarge3 hlarge4 hlarge5
  intro A hA
  let A' := A.erase 0
  have hlocal : ∀ q ∈ range N, 1 ≤ q → (A'.filter fun n => q ∣ n).card ≤ N / q := by
    intro q hq h1q
    calc
      (A'.filter fun n => q ∣ n).card ≤ ((Icc 1 N).filter fun n => q ∣ n).card := by
        refine Finset.card_le_card ?_
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        refine ⟨?_, hn.2⟩
        have hnA : n ∈ A := (Finset.mem_erase.mp hn.1).2
        have hnN := hA hnA
        rw [Finset.mem_range] at hnN
        rw [Finset.mem_Icc]
        refine ⟨?_, le_of_lt hnN⟩
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finset.mem_erase.mp hn.1).1)
      _ = N / q := count_multiples h1q
  have hlocal' : ∀ q ∈ range N, 1 ≤ q → ((A'.filter fun n => q ∣ n).card : ℝ) ≤ (N : ℝ) / q := by
    intro q hq h1q
    exact le_trans (by exact_mod_cast hlocal q hq h1q) Nat.cast_div_le
  calc
    ((A.filter fun n =>
        ∃ q : ℕ,
          IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
        ℝ) ≤
        (((A'.filter fun n =>
            ∃ q : ℕ,
              IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
          ℝ) + 1) := by
      exact_mod_cast (show
        (A.filter fun n =>
            ∃ q : ℕ,
              IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card ≤
          (A'.filter fun n =>
              ∃ q : ℕ,
                IsPrimePow q ∧
                  (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                  q ∣ n).card + 1 by
        rw [show A' = A.erase 0 by rfl, filter_erase]
        refine le_trans (Finset.card_le_card (Finset.insert_erase_subset 0 _)) ?_
        exact Finset.card_insert_le _ _)
    _ ≤
        (((range N).filter fun r : ℕ =>
              IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => ((A'.filter fun n => q ∣ n).card : ℝ))) + 1 := by
      rw [add_le_add_iff_right]
      have hdecomp :
          A'.filter
              (fun n =>
                ∃ q : ℕ,
                  IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n) ⊆
            ((range N).filter fun r : ℕ =>
                IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).biUnion
              (fun q => A'.filter fun n => q ∣ n) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_biUnion]
        rcases hn.2 with ⟨q, hqpp, hqlarge, hqdiv⟩
        refine ⟨q, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨?_, hqpp, hqlarge⟩
          rw [Finset.mem_range]
          have hnA : n ∈ A := (Finset.mem_erase.mp hn.1).2
          have hnN := hA hnA
          rw [Finset.mem_range] at hnN
          refine lt_of_le_of_lt ?_ hnN
          exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Finset.mem_erase.mp hn.1).1) hqdiv
        · rw [Finset.mem_filter]
          exact ⟨hn.1, hqdiv⟩
      have hcard :
          (A'.filter
              (fun n =>
                ∃ q : ℕ,
                  IsPrimePow q ∧
                    (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                    q ∣ n)).card ≤
            (((range N).filter fun r : ℕ =>
                  IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (A'.filter fun n => q ∣ n).card)) := by
        refine (Finset.card_le_card hdecomp).trans ?_
        simpa using (Finset.card_biUnion_le (s := (range N).filter fun r : ℕ =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ))
          (t := fun q => A'.filter fun n => q ∣ n))
      exact_mod_cast hcard
    _ ≤
        (N : ℝ) *
            (((range N).filter fun r : ℕ =>
                  IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (1 : ℝ) / q)) +
          1 := by
      rw [add_le_add_iff_right, mul_sum]
      refine Finset.sum_le_sum ?_
      intro q hq
      rw [← div_eq_mul_one_div]
      rw [Finset.mem_filter] at hq
      exact hlocal' q hq.1 (le_of_lt (IsPrimePow.one_lt hq.2.1))
    _ ≤ (N : ℝ) / (2 * D) + 1 := by
      rw [add_le_add_iff_right, div_eq_mul_one_div (N : ℝ)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc
        ((range N).filter fun r : ℕ =>
            IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => (1 : ℝ) / q) =
            ((range N).filter fun r : ℕ =>
                IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (q : ℝ)⁻¹) := by
          simp_rw [one_div]
        _ ≤ c / log (log (N : ℝ)) := hdiff'
        _ ≤ 1 / (2 * D) := by
          simp_rw [one_div]
          have htmp := (div_le_iff₀ (by
            rw [one_div_pos]
            exact mul_pos zero_lt_two hD)).mp hlarge4
          have htmp' : c ≤ (1 / (2 * D)) * log (log (N : ℝ)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
          simpa [Function.comp, one_div, mul_comm, mul_left_comm, mul_assoc] using
            (div_le_iff₀ hlarge5).2 htmp'
    _ ≤ (N : ℝ) / D := by
      have hhalf : 1 ≤ (N : ℝ) / (2 * D) := by
        rw [one_le_div (by positivity)]
        simpa [mul_comm] using hlarge2
      calc
        (N : ℝ) / (2 * D) + 1 ≤ (N : ℝ) / (2 * D) + (N : ℝ) / (2 * D) := by
          simpa [add_comm] using add_le_add_left hhalf ((N : ℝ) / (2 * D))
        _ = (N : ℝ) / D := by
          field_simp [hD.ne']
          ring

lemma final_large_N (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        4 * y + 4 ≤ z ∧
          0 < z ∧
            Filter.Eventually
              (fun N : ℕ =>
                (0 : ℝ) < N ∧
                  (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + 1 < (N : ℝ) / (5 * D) ∧
                    (∀ A ⊆ range N,
                      ((A.filter fun (n : ℕ) =>
                            ∃ q : ℕ,
                              IsPrimePow q ∧
                                (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                                  q ∣ n).card :
                        ℝ) ≤
                        (N : ℝ) / (5 * D)) ∧
                      (∀ A ⊆ range N,
                        ((A.filter fun n : ℕ =>
                              n ≠ 0 ∧
                                ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
                                    (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))).card :
                          ℝ) ≤
                          (N : ℝ) / (5 * D)) ∧
                        (∀ A ⊆ range N,
                          ((A.filter fun n =>
                                ¬ ∃ d₁ d₂ : ℕ,
                                    d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧
                                      4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
                            ℝ) ≤
                            (N : ℝ) / (5 * D)) ∧
                          z ≤ log (N : ℝ) ^ ((1 : ℝ) / 500) ∧
                            (2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200))) * (N : ℝ) ≤
                              (N : ℝ) / (5 * D))
              atTop := by
  rcases filter_div D hD with ⟨y, z, h1y, hyz, h0z, hChelp, hChelp', hfilterdiv⟩
  refine ⟨y, z, h1y, hyz, h0z, ?_⟩
  have h5D : 0 < 5 * D := by
    refine mul_pos ?_ hD
    norm_num
  have h1pos : (0 : ℝ) < 1 := by norm_num
  filter_upwards
    [ eventually_gt_atTop 0
    , filter_smooth (5 * D) h5D
    , filter_regular (5 * D) h5D
    , hfilterdiv
    , tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2 * (5 * D)))
    , ((tendsto_pow_rec_log_log_at_top h1pos).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (5 * D * 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (z ^ (500 : ℝ)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((1 / (1 / (5 * D) / 2)) ^ (200 : ℝ))) ] with
      N hlarge hsmooth hregular hdiv hlarge2 hlarge3 hlarge4 hlarge5 hlarge6
  dsimp at hlarge3 hlarge4 hlarge5 hlarge6
  refine ⟨by exact_mod_cast hlarge, ?_, hsmooth, hregular, hdiv, ?_, ?_⟩
  · calc
      (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + 1 <
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + ((N : ℝ) / (5 * D)) / 2 := by
            have hlt : 1 < ((N : ℝ) / (5 * D)) / 2 := by
              refine (_root_.lt_div_iff₀ zero_lt_two).2 ?_
              refine (_root_.lt_div_iff₀ h5D).2 ?_
              simpa [mul_assoc, mul_left_comm, mul_comm] using hlarge2
            nlinarith
      _ ≤ (N : ℝ) / (5 * D) := by
        have hNpos : 0 < (N : ℝ) := by exact_mod_cast hlarge
        have hpow :
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) ≤ ((N : ℝ) / (5 * D)) / 2 := by
          have hfacpos : 0 < 5 * D * 2 := by positivity
          have hrecip :
              (N : ℝ) ^ (-(1 / log (log (N : ℝ)))) ≤ 1 / (5 * D * 2) := by
            rw [Real.rpow_neg hNpos.le, ← one_div]
            exact one_div_le_one_div_of_le hfacpos hlarge3
          calc
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) =
                (N : ℝ) ^ (-(1 / log (log (N : ℝ)))) * (N : ℝ) := by
                  rw [sub_eq_add_neg, add_comm, Real.rpow_add_one hNpos.ne']
            _ ≤ (1 / (5 * D * 2)) * (N : ℝ) := by
              exact mul_le_mul_of_nonneg_right hrecip (show 0 ≤ (N : ℝ) by exact hNpos.le)
            _ = ((N : ℝ) / (5 * D)) / 2 := by
              field_simp [hD.ne']
        calc
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + ((N : ℝ) / (5 * D)) / 2 ≤
              ((N : ℝ) / (5 * D)) / 2 + ((N : ℝ) / (5 * D)) / 2 := by
                exact add_le_add hpow le_rfl
          _ = (N : ℝ) / (5 * D) := by ring
  · have h500 : (0 : ℝ) < 500 := by norm_num
    rw [← Real.rpow_le_rpow_iff _ _ h500, ← Real.rpow_mul, one_div_mul_cancel, Real.rpow_one]
    · exact hlarge4
    · norm_num
    · exact le_of_lt hlarge5
    · exact le_of_lt h0z
    · exact Real.rpow_nonneg (le_of_lt hlarge5) _
  · have hNpos : 0 < (N : ℝ) := by exact_mod_cast hlarge
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one h1y
    have hterm1 : 2 / y ≤ (1 / (5 * D)) / 2 := by
      have hterm1' : 2 / y ≤ 1 / (5 * D * 2) := by
        refine (_root_.div_le_iff₀ hypos).2 ?_
        have hc : 2 ≤ y * (1 / (5 * D * 2)) := by
          exact (_root_.div_le_iff₀ (show 0 < 1 / (5 * D * 2) by positivity)).1 hChelp'
        simpa [mul_comm] using hc
      calc
        2 / y ≤ 1 / (5 * D * 2) := hterm1'
        _ = (1 / (5 * D)) / 2 := by
          field_simp [hD.ne']
    have hterm2 : log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ (1 / (5 * D)) / 2 := by
      rw [Real.rpow_neg hlarge5.le, ← one_div]
      have hroot :
          1 / (1 / (5 * D) / 2) ≤ log (N : ℝ) ^ ((1 : ℝ) / 200) := by
        have h200 : (0 : ℝ) < 200 := by norm_num
        rw [← Real.rpow_le_rpow_iff _ _ h200, ← Real.rpow_mul, one_div_mul_cancel, Real.rpow_one]
        · exact hlarge6
        · norm_num
        · exact le_of_lt hlarge5
        · rw [one_div_nonneg]
          refine div_nonneg ?_ zero_le_two
          rw [one_div_nonneg]
          refine mul_nonneg ?_ hD.le
          norm_num
        · exact Real.rpow_nonneg hlarge5.le _
      have hrootpos : 0 < 1 / (1 / (5 * D) / 2) := by positivity
      calc
        1 / (log (N : ℝ) ^ ((1 : ℝ) / 200)) ≤ 1 / (1 / (1 / (5 * D) / 2)) :=
            one_div_le_one_div_of_le hrootpos hroot
        _ = (1 / (5 * D)) / 2 := by
          field_simp [hD.ne']
    have hsum : 2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ 1 / (5 * D) := by
      calc
        2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤
            (1 / (5 * D)) / 2 + (1 / (5 * D)) / 2 := by
              exact add_le_add hterm1 hterm2
        _ = 1 / (5 * D) := by rw [add_halves]
    calc
      (2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200))) * (N : ℝ) ≤ (1 / (5 * D)) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hsum hNpos.le
      _ = (N : ℝ) / (5 * D) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm]

theorem unit_fractions_upper_density' (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        0 ≤ z ∧
          ∀ A : Set ℕ,
            upper_density A > 1 / D →
              ∃ d ∈ Icc ⌈y⌉₊ ⌊z⌋₊,
                ∃ S : Finset ℕ,
                  (S : Set ℕ) ⊆ A ∧ S.sum (fun n => (1 / n : ℚ)) = 1 / d := by
  rcases final_large_N D hD with ⟨y, z, h1y, hyz, h0z, hfinal⟩
  refine ⟨y, z, h1y, le_of_lt h0z, ?_⟩
  intro A hA
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hfinal.and technical_prop)
  obtain ⟨N, hNN0, hAcard⟩ := frequently_atTop'.1 (frequently_nat_of hA) N0
  have hlargeN := (hN0 N (le_of_lt hNN0)).1
  have htech := (hN0 N (le_of_lt hNN0)).2
  dsimp at hlargeN
  have hzN := hlargeN.2.2.2.2.2.1
  have hyN := hlargeN.2.2.2.2.2.2
  let A' := (range N).filter fun n : ℕ => n ∈ A
  have hA'card : (N : ℝ) / D < A'.card := by
    have hNpos : 0 < (N : ℝ) := hlargeN.1
    have hAcard' : 1 / D < A'.card / N := by
      simpa [A'] using hAcard
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (lt_div_iff₀ hNpos).1 hAcard'
  let M := (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))
  let A0 := A'.filter fun n : ℕ => (n : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))
  have hA0card : (A0.card : ℝ) < (N : ℝ) / (5 * D) := by
    calc
      (A0.card : ℝ) ≤ ((range ⌈(N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))⌉₊).card : ℝ) := by
        norm_cast
        refine Finset.card_le_card ?_
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_range, Nat.lt_ceil]
        exact hn.2
      _ < (N : ℝ) / (5 * D) := by
        rw [Finset.card_range]
        refine lt_trans (Nat.ceil_lt_add_one ?_) hlargeN.2.1
        exact Real.rpow_nonneg (le_of_lt hlargeN.1) _
  let A1 := A'.filter fun n ↦ ∃ q : ℕ, IsPrimePow q ∧ M < q ∧ q ∣ n
  have hA1card : (A1.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A2 := A'.filter fun n ↦
    n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))
  have hA2card : (A2.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A3 := A'.filter fun n ↦
    ¬ ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ ((d₂ : ℝ) ≤ z)
  have hA3card : (A3.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A'' := A' \ (A0 ∪ A1 ∪ A2 ∪ A3)
  have hUnionSub : A0 ∪ A1 ∪ A2 ∪ A3 ⊆ A' := by
    intro n hn
    rcases Finset.mem_union.mp hn with h012 | h3
    · rcases Finset.mem_union.mp h012 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · exact (Finset.mem_filter.mp h0).1
        · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h2).1
    · exact (Finset.mem_filter.mp h3).1
  have hA''card : (N : ℝ) / (5 * D) ≤ A''.card := by
    let x : ℝ := (N : ℝ) / (5 * D)
    have hA'card5 : 5 * x < A'.card := by
      dsimp [x]
      have hx : 5 * ((N : ℝ) / (5 * D)) = (N : ℝ) / D := by
        field_simp [hD.ne']
      rw [hx]
      exact hA'card
    have hsum4 : ((A0 ∪ A1 ∪ A2 ∪ A3).card : ℝ) ≤ 4 * x := by
      calc
        ((A0 ∪ A1 ∪ A2 ∪ A3).card : ℝ) ≤ (A0.card + A1.card + A2.card + A3.card : ℕ) := by
          norm_cast
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [add_le_add_iff_right]
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [add_le_add_iff_right]
          exact Finset.card_union_le _ _
        _ ≤ 4 * x := by
          have hA0le : (A0.card : ℝ) ≤ x := le_of_lt hA0card
          dsimp [x] at hA0le hA1card hA2card hA3card ⊢
          push_cast
          nlinarith
    calc
      x ≤ (A'.card : ℝ) - (x + x + (x + x)) := by
        have hx4 : x + x + (x + x) = 4 * x := by ring
        rw [hx4]
        nlinarith
      _ ≤ (A'.card : ℝ) - (A0 ∪ A1 ∪ A2 ∪ A3).card := by
        dsimp [x] at hsum4 ⊢
        linarith
      _ ≤ A''.card := by
        dsimp [A'']
        rw [Finset.card_sdiff_of_subset hUnionSub]
        exact_mod_cast Int.le_natCast_sub A'.card (A0 ∪ A1 ∪ A2 ∪ A3).card
  clear hA'card hA0card hA1card hA2card hA3card
  have hnotA0 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A0 := by
    intro n hn hn0
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl hn0
  have hnotA1 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A1 := by
    intro n hn hn1
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr hn1
  have hnotA2 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A2 := by
    intro n hn hn2
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr hn2
  have hnotA3 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A3 := by
    intro n hn hn3
    exact (Finset.mem_sdiff.mp hn).2 <| Finset.mem_union.mpr <| Or.inr hn3
  have h0A'' : 0 ∉ A'' := by
    intro hz
    exact hnotA0 hz <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, by
      simpa using (Real.rpow_pos_of_pos hlargeN.1 (1 - (1 : ℝ) / log (log (N : ℝ))))⟩
  have hA''N : ∀ n ∈ A'', n < N := by
    intro n hn
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hn
    exact hn.1.1
  have hstep : ∃ S ⊆ A'', ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z) ∧ rec_sum S = 1 / d := by
    refine htech A'' ?_ y z h1y hyz hzN h0A'' ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_range]
      exact lt_of_lt_of_le (hA''N n hn) (Nat.le_succ N)
    · intro n hn
      rw [← not_lt]
      intro hbad
      exact hnotA0 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, hbad⟩
    · calc
        2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ (A''.card : ℝ) / N := by
          rw [le_div_iff₀ hlargeN.1]
          refine le_trans hyN hA''card
        _ ≤ rec_sum A'' := by
          rw [Finset.card_eq_sum_ones, rec_sum]
          push_cast
          rw [Finset.sum_div]
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnle : (n : ℝ) ≤ N := by
            exact_mod_cast Nat.le_of_lt (hA''N n hn)
          have hn0 : n ≠ 0 := by
            intro hzn
            exact h0A'' (hzn ▸ hn)
          have hnpos : 0 < (n : ℝ) := by
            exact Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hn0)
          exact one_div_le_one_div_of_le hnpos hnle
    · intro n hn
      by_contra hbad
      exact hnotA3 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, hbad⟩
    · intro n hn
      rw [is_smooth]
      intro q hq hqn
      rw [← not_lt]
      intro hbad
      exact hnotA1 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, ⟨q, hq, hbad, hqn⟩⟩
    · rw [arith_regular]
      intro n hn
      by_contra hbad
      have hn0 : n ≠ 0 := by
        intro hz
        exact h0A'' (hz ▸ hn)
      exact hnotA2 hn <| Finset.mem_filter.mpr ⟨by
        rw [Finset.mem_sdiff] at hn
        exact hn.1, ⟨hn0, hbad⟩⟩
  clear htech
  rcases hstep with ⟨S, hS, d, hyd, hdz, hrecd⟩
  refine ⟨d, ?_, S, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · exact Nat.ceil_le.mpr hyd
    · exact (Nat.le_floor_iff (le_of_lt h0z)).mpr hdz
  · intro s hs
    have hs' := hS hs
    rw [Finset.mem_sdiff, Finset.mem_filter] at hs'
    exact hs'.1.2
  · rw [rec_sum] at hrecd
    exact hrecd

theorem unit_fractions_upper_density (A : Set ℕ) (hA : upper_density A > 0) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ S.sum (fun n => (1 / n : ℚ)) = 1 := by
  classical
  let D := 2 / upper_density A
  have hD : 0 < D := div_pos zero_lt_two hA
  have hDA : 1 / D < upper_density A := by
    rw [show D = 2 / upper_density A by rfl, one_div_div]
    exact half_lt_self hA
  rcases unit_fractions_upper_density' D hD with ⟨y, z, h1y, h0z, hupp⟩
  let M := (Finset.Icc ⌈y⌉₊ ⌊z⌋₊).sum fun d => d
  let good_set : Finset (Finset ℕ) → Prop := fun S =>
    (∀ s ∈ S, (s : Set ℕ) ⊆ A) ∧
      (S : Set (Finset ℕ)).PairwiseDisjoint id ∧
        ∀ s, ∃ d : ℕ, s ∈ S → y ≤ d ∧ (d : ℝ) ≤ z ∧ rec_sum s = 1 / d
  let P : ℕ → Prop := fun k => ∃ S : Finset (Finset ℕ), S.card = k ∧ good_set S
  let k : ℕ := Nat.findGreatest P (M + 1)
  have P0 : P 0 := by
    refine ⟨∅, ?_⟩
    simp [good_set]
  have Pk : P k := by
    dsimp [k]
    exact Nat.findGreatest_spec (P := P) (Nat.zero_le _) P0
  obtain ⟨S, hk, hS₁, hS₂, hS₃⟩ := Pk
  choose d' hd'₁ hd'₂ hd'₃ using hS₃
  let t : ℕ → ℕ := fun d => (S.filter fun s => d' s = d).card
  by_cases h : ∃ d : ℕ, 0 < d ∧ d ≤ t d
  · obtain ⟨d, d_pos, ht⟩ := h
    obtain ⟨T', hT', hd₂⟩ := Finset.exists_subset_card_eq (s := S.filter fun s => d' s = d) ht
    have hT'S : T' ⊆ S := hT'.trans (Finset.filter_subset _ _)
    refine ⟨T'.biUnion id, ?_, ?_⟩
    · intro n hn
      rcases Finset.mem_biUnion.mp hn with ⟨s, hsT, hns⟩
      exact hS₁ s (hT'S hsT) hns
    · change rec_sum (T'.biUnion id) = 1
      rw [rec_sum_bUnion_disjoint (hS₂.subset hT'S)]
      have hsumT : T'.sum rec_sum = T'.sum (fun _ : Finset ℕ => (1 : ℚ) / d) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [(Finset.mem_filter.mp (hT' hi)).2] using (hd'₃ i (hT'S hi))
      rw [hsumT, Finset.sum_const, hd₂, nsmul_eq_mul]
      field_simp [show (d : ℚ) ≠ 0 by exact_mod_cast d_pos.ne']
  · exfalso
    have hcount : ∀ d : ℕ, 0 < d → t d < d := by
      intro d hd
      by_contra hdt
      exact h ⟨d, hd, le_of_not_gt hdt⟩
    let A' : Set ℕ := A \ (S.biUnion id : Set ℕ)
    have hDA' : 1 / D < upper_density A' := by
      have hpres : upper_density A = upper_density A' := by
        dsimp [A']
        simpa using (upper_density_preserved (A := A) (S := S.biUnion id))
      rw [← hpres]
      exact hDA
    specialize hupp A' hDA'
    rcases hupp with ⟨d, hd, S', hS'₁, hS'₂⟩
    have hd' : y ≤ d ∧ (d : ℝ) ≤ z := by
      rw [Finset.mem_Icc] at hd
      refine ⟨?_, ?_⟩
      · exact le_trans (Nat.le_ceil y) (by exact_mod_cast hd.1)
      · exact le_trans (by exact_mod_cast hd.2) (Nat.floor_le h0z)
    have h1d : 1 ≤ d := by
      have : (1 : ℝ) ≤ d := le_trans h1y hd'.1
      exact_mod_cast this
    have hAS : Disjoint A' (S.biUnion id : Set ℕ) := by
      dsimp [A']
      simpa using (disjoint_sdiff_self_left : Disjoint (A \ (S.biUnion id : Set ℕ))
        (S.biUnion id : Set ℕ))
    have hS'A : (S' : Set ℕ) ⊆ A := by
      intro n hn
      exact (hS'₁ hn).1
    have hS'' : ∀ s ∈ S, Disjoint S' s := by
      intro s hs
      rw [← Finset.disjoint_coe]
      exact Disjoint.mono hS'₁ (Finset.subset_biUnion_of_mem id hs) hAS
    have hS''' : S' ∉ S := by
      intro hs
      exact (nonempty_of_rec_sum_recip h1d hS'₂).ne_empty (disjoint_self.mp (hS'' _ hs))
    have hPk1 : P (k + 1) := by
      refine ⟨insert S' S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hS''', hk]
      · refine ⟨?_, ?_, ?_⟩
        · intro s hs
          rcases Finset.mem_insert.mp hs with rfl | hs
          · exact hS'A
          · exact hS₁ s hs
        · simpa [Set.pairwiseDisjoint_insert_of_notMem hS''', hS₂] using fun s hs =>
            hS'' _ hs
        · intro s
          rcases eq_or_ne s S' with rfl | hs
          · exact ⟨d, fun _ => ⟨hd'.1, hd'.2, hS'₂⟩⟩
          · refine ⟨d' s, fun hs' => ?_⟩
            have hsS : s ∈ S := Finset.mem_of_mem_insert_of_ne hs' hs
            exact ⟨hd'₁ _ hsS, hd'₂ _ hsS, hd'₃ _ hsS⟩
    have hk_bound : k + 1 ≤ M + 1 := by
      rw [← hk, add_le_add_iff_right]
      have hSdecomp :
          (Finset.Icc ⌈y⌉₊ ⌊z⌋₊).biUnion (fun d => S.filter fun s => d' s = d) = S := by
        refine Finset.biUnion_filter_eq_of_maps_to ?_
        intro n hn
        rw [Finset.mem_Icc]
        refine ⟨Nat.ceil_le.mpr (hd'₁ n hn), (Nat.le_floor_iff h0z).mpr (hd'₂ n hn)⟩
      rw [← hSdecomp]
      refine le_trans Finset.card_biUnion_le ?_
      refine Finset.sum_le_sum ?_
      intro d hd
      have hd' : d ∈ Finset.Icc ⌈y⌉₊ ⌊z⌋₊ := hd
      rw [Finset.mem_Icc, Nat.ceil_le] at hd'
      exact
        le_of_lt
          (hcount d (by
            exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_trans h1y hd'.1))))
    have : k + 1 ≤ k := Nat.le_findGreatest hk_bound hPk1
    exact Nat.not_succ_le_self _ this


end UnitFractions
