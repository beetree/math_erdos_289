module

public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.Basic
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.ExponentialSums

@[expose] public section

namespace UnitFractions

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Real
open _root_.Finset

noncomputable section

lemma Function.Antiperiodic.abs_periodic {f : ℝ → ℝ} {c : ℝ}
    (h : Function.Antiperiodic f c) :
    Function.Periodic (abs ∘ f) c := by
  intro x
  simp [Function.comp, h x, abs_neg]

lemma abs_cos_periodic : Function.Periodic (fun i => |cos i|) π := by
  exact Function.Antiperiodic.abs_periodic Real.cos_antiperiodic

lemma abs_cos_period {x y n : ℤ} (h : x % n = y % n) :
    |cos (π * (x / n))| = |cos (π * (y / n))| := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp at h
    simp [h]
  have hdiv : n ∣ x - y := by
    rwa [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  obtain ⟨k, hk⟩ := hdiv
  rw [sub_eq_iff_eq_add'] at hk
  rw [hk, Int.cast_add, Int.cast_mul, add_div, mul_div_cancel_left₀]
  · rw [mul_add, mul_comm π k]
    exact abs_cos_periodic.int_mul k _
  · exact_mod_cast hn

lemma cos_prod_bound {A : Finset ℕ} {N : ℕ} (t : ℤ) (hA' : 0 ∉ A)
    (hA : ∀ n ∈ A, n ≤ N) (h' : ℕ → ℤ) (hh'₁ : ∀ n ∈ A, h' n % n = t % n)
    (hh'₂ : ∀ n ∈ A, (|h' n| : ℝ) ≤ n / 2) :
    cos_prod A t ≤ exp (- (2 / N ^ 2) * A.sum (fun n => h' n ^ 2)) := by
  rw [cos_prod]
  have hrhs :
      exp (- (2 / (N : ℝ) ^ 2) * ↑(A.sum fun n => h' n ^ 2)) =
        A.prod (fun n => exp (-(2 / (N : ℝ) ^ 2) * (h' n : ℝ) ^ 2)) := by
    rw [show -(2 / (N : ℝ) ^ 2) * ↑(A.sum fun n => h' n ^ 2) =
        A.sum (fun n => (-(2 / (N : ℝ) ^ 2) * (h' n : ℝ) ^ 2)) by
          rw [Int.cast_sum]
          rw [Finset.mul_sum]
          congr with n
          rw [Int.cast_pow]]
    rw [Real.exp_sum]
  rw [hrhs]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) ?_
  intro n hn
  have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA'
  rw [neg_mul, div_mul_comm, ← div_pow, ← mul_comm (2 : ℝ), mul_div_assoc,
    ← Int.cast_natCast n, abs_cos_period (hh'₁ _ hn).symm, Int.cast_natCast]
  apply (cos_bound_abs _).trans
  · have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn'
    have hNn : (n : ℝ) ≤ N := by
      exact_mod_cast hA _ hn
    have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le hn0 hNn
    apply Real.exp_le_exp.mpr
    have hcmp : 2 * ((h' n : ℝ) / N) ^ 2 ≤ 2 * ((h' n : ℝ) / n) ^ 2 := by
      have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        nlinarith
      field_simp [hn0.ne', hN0.ne']
      nlinarith [sq_nonneg ((h' n : ℝ)), hsq]
    linarith
  · have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn'
    rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh'₂ _ hn

lemma minor1_bound_aux :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K M T : ℝ} {A : Finset ℕ},
      8 ≤ M → 0 ∉ A → 0 < T →
      (∀ q ∈ ppowers_in_set A, ↑q ≤ (T * K ^ 2) / (N ^ 2 * log N)) →
        ↑(lcmA A) ≤ exp ((T * K ^ 2) / (4 * N ^ 2)) := by
  obtain ⟨C, hC₀, hC⟩ := smooth_lcm
  filter_upwards
    [ Filter.eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop (4 * C)) ] with N hN₁ hN' K M T A hM hA hT hA₄
  change 4 * C ≤ log N at hN'
  have hN₁' : (1 : ℝ) < N := by
    exact_mod_cast hN₁
  have h₁ : (0 : ℝ) < N ^ 2 := by
    exact pow_pos (zero_lt_one.trans hN₁') 2
  have hden : 0 < (N : ℝ) ^ 2 * log N := by
    exact mul_pos h₁ (Real.log_pos hN₁')
  refine (hC _ (div_nonneg ?_ hden.le) _ hA hA₄).trans ?_
  · exact mul_nonneg hT.le (sq_nonneg K)
  rw [exp_le_exp, mul_div_assoc',
    div_le_div_iff₀ hden (mul_pos (show (0 : ℝ) < 4 by norm_num) h₁), mul_right_comm,
    mul_comm (T * K ^ 2), mul_comm _ (log N), ← mul_assoc C, mul_assoc, mul_assoc (log N),
    mul_comm C]
  exact mul_le_mul_of_nonneg_right hN' (mul_nonneg h₁.le (mul_nonneg hT.le (sq_nonneg K)))

lemma exists_representative (t : ℤ) {n : ℕ} (hn : n ≠ 0) :
    ∃ tn : ℤ, tn % n = t % n ∧ |tn| ≤ n / 2 := by
  refine ⟨Int.bmod t n, ?_, ?_⟩
  · exact
      (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
        (Int.emod_eq_zero_of_dvd Int.dvd_bmod_sub_self)
  · refine abs_le.mpr ?_
    constructor
    · simpa using Int.le_bmod (x := t) (m := n) (Nat.pos_of_ne_zero hn)
    · have hlt : Int.bmod t n < (n + 1) / 2 :=
        Int.bmod_lt (x := t) (m := n) (Nat.pos_of_ne_zero hn)
      omega

lemma missing_bridge_sum {A : Finset ℕ} {t : ℤ} {K M : ℝ} {I : Finset ℤ} {tn : ℕ → ℤ}
    (hK : 0 < K) (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (htn₁ : ∀ n : ℕ, n ∈ A → tn n % ↑n = t % ↑n)
    (hI' : M ≤ ((A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ)) :
    M * (K ^ 2 / 4) ≤ A.sum (fun n => (tn n : ℝ) ^ 2) := by
  let A' := A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)
  have hsubset : A' ⊆ A := Finset.filter_subset _ _
  refine
    le_trans ?_
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => sq_nonneg _)
  have hcard : M * (K ^ 2 / 4) ≤ (A'.card : ℝ) * (K ^ 2 / 4) := by
    exact mul_le_mul_of_nonneg_right hI' (by positivity)
  refine hcard.trans ?_
  calc
    (A'.card : ℝ) * (K ^ 2 / 4) = A'.sum (fun _ : ℕ => K ^ 2 / 4) := by
      simp [nsmul_eq_mul]
    _ ≤ A'.sum (fun n => (tn n : ℝ) ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hnA : n ∈ A := (Finset.mem_filter.mp hn).1
      have hnodvd : ∀ x ∈ I, ¬ ((n : ℤ) ∣ x) := (Finset.mem_filter.mp hn).2
      have hnotlt : ¬ |(tn n : ℝ)| < K / 2 := by
        intro hi
        have hi' := abs_lt.mp hi
        have hx : t - tn n ∈ I := by
          rw [hI, Finset.mem_Icc]
          constructor
          · refine Int.ceil_le.mpr ?_
            have hleft : (t : ℝ) - K / 2 < (t : ℝ) - (tn n : ℝ) := by
              linarith
            exact le_of_lt (by simpa using hleft)
          · refine Int.le_floor.mpr ?_
            have hright : (t : ℝ) - (tn n : ℝ) < (t : ℝ) + K / 2 := by
              linarith
            exact le_of_lt (by simpa using hright)
        have hcontra := hnodvd _ hx
        rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero, eq_comm] at hcontra
        exact hcontra (htn₁ _ hnA)
      have habs : K / 2 ≤ |(tn n : ℝ)| := not_lt.mp hnotlt
      have hk2 : 0 ≤ K / 2 := by linarith
      calc
        K ^ 2 / 4 = (K / 2) ^ 2 := by ring
        _ ≤ |(tn n : ℝ)| ^ 2 := by
          nlinarith [habs, abs_nonneg (tn n : ℝ)]
        _ = (tn n : ℝ) ^ 2 := by rw [sq_abs]

lemma missing_bridge (A : Finset ℕ) {N : ℕ} {t : ℤ} {K M : ℝ} (hA' : 0 ∉ A)
    (hA : ∀ n ∈ A, n ≤ N) {I : Finset ℤ} (hK : 0 < K)
    (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (hI' : M ≤ ((A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ)) :
    cos_prod A t ≤ exp (- (M * K ^ 2 / (2 * N ^ 2))) := by
  have hrepr : ∀ n : ℕ, ∃ tn : ℤ, n ∈ A → tn % n = t % n ∧ |tn| ≤ n / 2 := by
    intro n
    by_cases hn : n ∈ A
    · have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA'
      obtain ⟨tn, htn₁, htn₂⟩ := exists_representative t hn'
      exact ⟨tn, fun _ => ⟨htn₁, htn₂⟩⟩
    · refine ⟨0, ?_⟩
      simp [hn]
  choose tn htn₁ htn₂ using hrepr
  refine (cos_prod_bound (A := A) (N := N) t hA' hA tn htn₁ ?_).trans ?_
  · intro n hn
    have hz : |tn n| ≤ n / 2 := htn₂ n hn
    have hzInt : (((tn n).natAbs : ℕ) : ℤ) ≤ (n / 2 : ℕ) := by
      have hz' := hz
      rw [Int.abs_eq_natAbs] at hz'
      exact hz'
    have hzReal : (((tn n).natAbs : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast hzInt
    have hzReal' : |((tn n : ℤ) : ℝ)| ≤ ((n / 2 : ℕ) : ℝ) := by
      simpa [Int.cast_abs] using hzReal
    exact hzReal'.trans Nat.cast_div_le
  · have hsum : M * (K ^ 2 / 4) ≤ A.sum (fun n => (tn n : ℝ) ^ 2) :=
      missing_bridge_sum hK hI htn₁ hI'
    have hsum' : M * (K ^ 2 / 4) ≤ ↑(A.sum fun n => tn n ^ 2) := by
      simpa [Int.cast_sum, Int.cast_pow] using hsum
    have hmul :
        -((2 : ℝ) / N ^ 2) * ↑(A.sum fun n => tn n ^ 2) ≤
          -((2 : ℝ) / N ^ 2) * (M * (K ^ 2 / 4)) := by
      exact mul_le_mul_of_nonpos_left hsum'
        (neg_nonpos.2 (div_nonneg zero_le_two (sq_nonneg (N : ℝ))))
    refine (Real.exp_le_exp.mpr hmul).trans_eq ?_
    congr 1
    ring

lemma minor1_bound :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K M T : ℝ} (k : ℕ) {A : Finset ℕ},
      8 ≤ M → A.Nonempty → (∀ n ∈ A, M ≤ ↑n) → 0 < K → 0 < T →
      (∀ n ∈ A, n ≤ N) →
      (∀ q ∈ ppowers_in_set A, ↑q ≤ (T * K ^ 2) / (N ^ 2 * log N)) →
        (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
  filter_upwards [minor1_bound_aux] with N hNaux K M T k A hM hAne hLower hK hT hUpper hSmooth
  have hA0 : 0 ∉ A := by
    intro h0
    have : M ≤ 0 := by simpa using hLower 0 h0
    linarith
  suffices hpoint :
      ∀ h ∈ minor_arc₁ A k K T, cos_prod A (h * k) ≤ ((lcmA A : ℝ) ^ 2)⁻¹ by
    have hsum :
        (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤
          ((minor_arc₁ A k K T).card : ℝ) * (((lcmA A : ℝ) ^ 2)⁻¹) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (minor_arc₁ A k K T) (fun h => cos_prod A (h * k))
          (((lcmA A : ℝ) ^ 2)⁻¹) hpoint)
    refine hsum.trans ?_
    have hjsubset : j A ⊆ valid_sum_range (lcmA A) := by
      intro x hx
      rw [j, Finset.mem_erase] at hx
      exact hx.2
    have hcard : ((minor_arc₁ A k K T).card : ℝ) ≤ lcmA A := by
      exact_mod_cast
        (Finset.card_le_card ((Finset.filter_subset _ _).trans Finset.sdiff_subset)).trans
          ((Finset.card_le_card hjsubset).trans_eq
            (by simp [valid_sum_range, dumb_subtraction_thing]))
    have hlcmge : (8 : ℝ) ≤ lcmA A := by
      obtain ⟨n, hn⟩ := hAne
      have hnle : (8 : ℝ) ≤ n := hM.trans (hLower n hn)
      exact hnle.trans (by
        exact_mod_cast Nat.le_of_dvd
          (Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff (s := A) (f := id)).2
            (by intro x hx hx0; exact hA0 (hx0 ▸ hx))) )
          (Finset.dvd_lcm hn))
    have hlcm0 : (lcmA A : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.lcm_ne_zero_iff (s := A) (f := id)).2
        (by intro x hx hx0; exact hA0 (hx0 ▸ hx))
    calc
      ((minor_arc₁ A k K T).card : ℝ) * (((lcmA A : ℝ) ^ 2)⁻¹)
          = ((minor_arc₁ A k K T).card : ℝ) / (lcmA A : ℝ) ^ 2 := by
              rw [div_eq_mul_inv]
      _ ≤ (lcmA A : ℝ) / (lcmA A : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hcard (sq_nonneg _)
      _ = 1 / (lcmA A : ℝ) := by
        field_simp [hlcm0]
      _ ≤ 1 / 8 := by
        exact one_div_le_one_div_of_le (by norm_num) hlcmge
      _ = (8 : ℝ)⁻¹ := by norm_num
  intro h hh
  rw [minor_arc₁, Finset.mem_filter] at hh
  have hI : I h K k =
      Finset.Icc ⌈((h * k : ℤ) : ℝ) - K / 2⌉ ⌊((h * k : ℤ) : ℝ) + K / 2⌋ := by
    simp [I, integer_range]
  refine (missing_bridge (A := A) (N := N) (t := h * k) hA0 hUpper hK hI hh.2).trans ?_
  have hlcm0 : (lcmA A : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.lcm_ne_zero_iff (s := A) (f := id)).2
      (by intro x hx hx0; exact hA0 (hx0 ▸ hx))
  have hlcmpos : 0 < (lcmA A : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff (s := A) (f := id)).2
      (by intro x hx hx0; exact hA0 (hx0 ▸ hx)))
  rw [Real.exp_neg]
  refine (inv_le_inv₀ (Real.exp_pos _) (sq_pos_iff.2 hlcm0)).2 ?_
  refine (pow_le_pow_left₀ hlcmpos.le (hNaux hM hA0 hT hSmooth) 2).trans ?_
  refine le_of_eq ?_
  rw [sq, ← Real.exp_add]
  congr 1
  ring_nf

lemma prod_swapping {A : Finset ℕ} (x : ℕ → ℝ) :
    A.prod
        (fun n => ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).prod (fun _ => x n)) =
      (ppowers_in_set A).prod (fun q => (local_part A q).prod x) := by
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  simp only [← Finset.prod_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr local_part_subset]

lemma minor2_ind_bound_part_one {N : ℕ} {A : Finset ℕ} {t : ℤ}
    (hA : 0 ∉ A) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N) :
    cos_prod A t ≤
      (ppowers_in_set A).prod (fun q => (cos_prod (local_part A q) t) ^ (2 * log N)⁻¹) := by
  let Q_ : ℕ → Finset ℕ :=
    fun n ↦ (ppowers_in_set A).filter (fun q => n ∈ local_part A q)
  have hq : ∀ n ∈ A, ((Q_ n).card : ℝ) ≤ 2 * log N := by
    intro n hn
    have hn0 : n ≠ 0 := ne_of_mem_of_not_mem hn hA
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlogn_nonneg : 0 ≤ log n := by
      exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0))
    have htriv : ((Q_ n).card : ℝ) ≤ log n / log 2 := by
      simpa [Q_] using (triv_q_bound hA n)
    refine htriv.trans ?_
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul ?_ (Real.log_le_log hnpos (by exact_mod_cast hA' n hn)) hlogn_nonneg
      zero_le_two
    have hhalf : (1 / 2 : ℝ) ≤ log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
    simpa [one_div] using ((one_div_le (Real.log_pos one_lt_two) zero_lt_two).2 hhalf)
  simp only [cos_prod]
  have hrewrite :
      (ppowers_in_set A).prod
          (fun q => (∏ n ∈ local_part A q, |cos (π * t / n)|) ^ (2 * log N)⁻¹) =
        (ppowers_in_set A).prod
          (fun q => ∏ n ∈ local_part A q, |cos (π * t / n)| ^ (2 * log N)⁻¹) := by
    refine Finset.prod_congr rfl ?_
    intro q hq'
    symm
    exact Real.finsetProd_rpow _ _ (fun n hn ↦ abs_nonneg _) _
  rw [hrewrite, ← prod_swapping]
  change ∏ n ∈ A, |cos (π * t / n)| ≤
    ∏ n ∈ A, ∏ _x ∈ Q_ n, |cos (π * t / n)| ^ (2 * log N)⁻¹
  simp_rw [Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) ?_
  intro n hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  refine Real.self_le_rpow_of_le_one (abs_nonneg _) (abs_cos_le_one _) ?_
  rw [← div_eq_inv_mul]
  refine (div_le_one ?_).2 (hq n hn)
  exact mul_pos zero_lt_two (Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN))

lemma minor2_ind_bound {N : ℕ} {A : Finset ℕ} {t : ℤ} {K L : ℝ} (I : Finset ℤ)
    (hA : 0 ∉ A) (hK : 0 < K) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N)
    (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (hq : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2)) :
    cos_prod A t ≤ N ^ (-4 * (ppowers_in_set A \ interval_rare_ppowers I A L).card : ℝ) := by
  refine (minor2_ind_bound_part_one hA hA' hN).trans ?_
  rw [← Finset.prod_sdiff (interval_rare_ppowers_subset I L)]
  suffices hq' :
      ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
        cos_prod (local_part A q) t ≤ (N : ℝ) ^ (-8 * log N) by
    have hq'' :
        ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
          cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ (N : ℝ) ^ (-4 : ℝ) := by
      intro q hq
      have hlogpos : 0 < log (N : ℝ) := by
        exact Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
      calc
        cos_prod (local_part A q) t ^ (2 * log N)⁻¹
            ≤ ((N : ℝ) ^ (-8 * log N)) ^ (2 * log N)⁻¹ :=
              Real.rpow_le_rpow (Finset.prod_nonneg fun _ _ => abs_nonneg _) (hq' q hq)
                (inv_nonneg.2 <| mul_nonneg zero_le_two <|
                  Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hN)))
        _ = (N : ℝ) ^ (-4 : ℝ) := by
            rw [← Real.rpow_mul (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N)]
            congr 2
            field_simp [hlogpos.ne']
            ring
    have hq''' :
        ∀ q ∈ interval_rare_ppowers I A L,
          cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ 1 := by
      intro q hq
      apply Real.rpow_le_one (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        (Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => abs_cos_le_one _))
      rw [inv_nonneg]
      exact mul_nonneg zero_le_two <| Real.log_nonneg <| by
        rw [Nat.one_le_cast]
        exact one_le_two.trans hN
    have hprod₁ :
        ∏ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
            cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤
          ∏ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L, (N : ℝ) ^ (-4 : ℝ) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro q hq
        exact Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) _
      · intro q hq
        exact hq'' q hq
    have hprod₂ :
        ∏ q ∈ interval_rare_ppowers I A L, cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤
          ∏ q ∈ interval_rare_ppowers I A L, (1 : ℝ) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro q hq
        exact Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) _
      · intro q hq
        exact hq''' q hq
    refine (mul_le_mul hprod₁ hprod₂ ?_ ?_).trans ?_
    · exact Finset.prod_nonneg fun i hi ↦
        Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) _
    · exact
        Finset.prod_nonneg fun i hi ↦
          Real.rpow_nonneg (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N) _
    · rw [Finset.prod_const, Finset.prod_const_one, mul_one, ← Real.rpow_natCast,
        ← Real.rpow_mul (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N)]
  intro q hq'
  have hqmem : q ∈ ppowers_in_set A := (Finset.mem_sdiff.mp hq').1
  have hqnot : q ∉ interval_rare_ppowers I A L := (Finset.mem_sdiff.mp hq').2
  have hqcount :
      L / q ≤
        (((local_part A q).filter
            fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ) := by
    let : DecidableEq ℤ := Classical.decEq ℤ
    let sZ : Finset ℤ := (local_part A q).image (fun n : ℕ => (n : ℤ))
    have hcardeq :
        (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) =
          (((local_part A q).filter
              fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ) := by
      dsimp [sZ]
      rw [Finset.filter_image, Finset.card_image_of_injective _ Nat.cast_injective]
    by_contra hlt
    apply hqnot
    rw [interval_rare_ppowers, Finset.mem_filter]
    have hlt' :
        (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) < L / q := by
      rw [hcardeq]
      exact not_le.mp hlt
    simpa [sZ, Finset.bind_def, Finset.pure_def, Finset.biUnion_singleton] using
      (show q ∈ ppowers_in_set A ∧
          (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) < L / q from
        ⟨hqmem, hlt'⟩)
  refine (missing_bridge (A := local_part A q) (M := L / q) (zero_mem_local_part_iff hA)
    (fun _ hn ↦ hA' _ (filter_subset _ _ hn)) hK hI hqcount).trans ?_
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast zero_lt_two.trans_le hN
  have hlogpos : 0 < log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
  rw [← Real.le_log_iff_exp_le (Real.rpow_pos_of_pos hN0 _), Real.log_rpow hN0]
  have hqpos : 0 < (q : ℝ) := by
    rw [Nat.cast_pos]
    rw [mem_ppowers_in_set] at hqmem
    exact hqmem.1.pos
  have hqbound : (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) := hq q hqmem
  have hqbound' : 16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2 * q ≤ L * K ^ 2 := by
    have hden' : 0 < 16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2 := by positivity
    have hmul : q * (16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2) ≤ L * K ^ 2 := by
      exact (_root_.le_div_iff₀ hden').1 hqbound
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hmain : 8 * log (N : ℝ) * log (N : ℝ) ≤ L * K ^ 2 / (2 * N ^ 2 * q) := by
    have hden : 0 < 2 * (N : ℝ) ^ 2 * q := by positivity
    refine (_root_.le_div_iff₀ hden).2 ?_
    nlinarith [hqbound', sq_nonneg (log (N : ℝ))]
  have hdiv : L / q * K ^ 2 / (2 * N ^ 2) = L * K ^ 2 / (2 * N ^ 2 * q) := by
    field_simp [hqpos.ne']
  rw [hdiv]
  nlinarith [hmain]

lemma powerset_sum_pow' {α : Type*} [DecidableEq α] {s : Finset α} {x : ℝ} :
    s.powerset.sum (fun t => x ^ (s \ t).card) = (1 + x) ^ s.card := by
  calc
    s.powerset.sum (fun t => x ^ (s \ t).card) = s.powerset.sum (fun t => x ^ t.card) := by
      refine Finset.sum_bij' (i := fun t _ => s \ t) (j := fun t _ => s \ t) ?_ ?_ ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_powerset.2 (Finset.sdiff_subset : s \ t ⊆ s)
      · intro t ht
        exact Finset.mem_powerset.2 (Finset.sdiff_subset : s \ t ⊆ s)
      · intro t ht
        exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 ht)
      · intro t ht
        exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 ht)
      · intro t ht
        rfl
    _ = (1 + x) ^ s.card := by
      simpa using (Finset.prod_one_add (s := s) (f := fun _ : α => x)).symm

lemma lcm_Q {A : Finset ℕ} (hA : 0 ∉ A) : lcmA (ppowers_in_set A) = lcmA A := by
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd_iff.2 ?_
    intro i hi
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff i).1 (mem_ppowers_in_set.1 hi).1
    rw [mem_ppowers_in_set' hp hk.ne'] at hi
    obtain ⟨n, hn, rfl⟩ := hi
    exact (Nat.ordProj_dvd _ _).trans (Finset.dvd_lcm hn)
  · refine Finset.lcm_dvd_iff.2 ?_
    intro n hn
    have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    have hpow : p ^ n.factorization p ∣ lcmA (ppowers_in_set A) := by
      by_cases hnp : n.factorization p = 0
      · simp [hnp]
      · apply Finset.dvd_lcm
        rw [mem_ppowers_in_set' hp hnp]
        exact ⟨n, hn, rfl⟩
    by_cases hk : k = 0
    · simp [hk]
    · exact (pow_dvd_pow _ ((hp.pow_dvd_iff_le_factorization hn').1 hpk)).trans hpow

lemma d_strict_subset {K L δ : ℝ} {k : ℕ} {A : Finset ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (z : ∀ h ∈ minor_arc₂ A k K δ,
      ∃ x ∈ I h K k, ↑(lcmA (interval_rare_ppowers (I h K k) A L)) ∣ x) :
    (minor_arc₂ A k K δ).filter
        (fun h => interval_rare_ppowers (I h K k) A L ⊂ ppowers_in_set A) =
      minor_arc₂ A k K δ := by
  ext h
  constructor
  · intro hh
    exact (Finset.mem_filter.mp hh).1
  · intro hh
    rw [Finset.mem_filter]
    refine ⟨hh, (Finset.ssubset_iff_subset_ne.2 ?_)⟩
    refine ⟨by simpa [interval_rare_ppowers] using
      (Finset.filter_subset _ (ppowers_in_set A)), ?_⟩
    intro hEq
    have hhminor : h ∈ minor_arc₂ A k K δ := hh
    rw [minor_arc₂, Finset.mem_sdiff] at hh
    rcases hh with ⟨hh, _⟩
    rcases Finset.mem_sdiff.mp hh with ⟨hj, hmajor⟩
    rcases z h hhminor with ⟨x, hxI, hdivx⟩
    rw [hEq, lcm_Q hA] at hdivx
    rcases hdivx with ⟨t, rfl⟩
    have hxI' : (|h * k - t * lcmA A| : ℝ) ≤ K / 2 := by
      have hxI'' := (mem_I' (h := h) (K := K) (k := k) (z := (lcmA A : ℤ) * t)).1 hxI
      simpa [Int.cast_mul, mul_comm, mul_left_comm, mul_assoc, abs_sub_comm] using hxI''
    apply hmajor
    rw [major_arc, Finset.mem_filter]
    exact ⟨hj, ⟨t, (mem_major_arc_at' hk h).2 ⟨hj, hxI'⟩⟩⟩

lemma Finset.cast_lcm {x : Finset ℕ} : ((x.lcm id : ℕ) : ℤ) = x.lcm (fun n => (n : ℤ)) := by
  classical
  refine Finset.induction_on x ?_ ?_
  · simp
  · intro a s ha hs
    simpa only [Finset.lcm_insert, id_eq] using
      hs ▸ (by rfl)

lemma cast_lcm_dvd {x : Finset ℕ} {z : ℤ} (h : ∀ i ∈ x, ↑i ∣ z) :
    ↑(lcmA x) ∣ z := by
  rw [Finset.cast_lcm]
  exact Finset.lcm_dvd h

lemma ssubsets_subset_powerset {α : Type*} [DecidableEq α] {s : Finset α} :
    s.ssubsets ⊆ s.powerset :=
  fun _ ht => Finset.mem_powerset.2 (Finset.mem_ssubsets.1 ht).1

lemma thing_le_four {N : ℕ} : ((N : ℝ)⁻¹ + 1) ^ N ≤ 4 := by
  rcases eq_or_ne N 0 with rfl | hN
  · norm_num
  · refine le_trans ?_ (Real.exp_one_lt_d9.le.trans (by norm_num))
    refine (pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp ((N : ℝ)⁻¹)) N).trans ?_
    rw [← Real.exp_nat_mul ((N : ℝ)⁻¹) N]
    simp [hN]

lemma ppowers_in_set_le {N : ℕ} {A : Finset ℕ} (hA' : ∀ n : ℕ, n ∈ A → n ≤ N) :
    ∀ q ∈ ppowers_in_set A, 1 ≤ q ∧ q ≤ N := by
  intro q hq
  rcases Finset.mem_biUnion.mp hq with ⟨n, hnA, hq⟩
  rw [Finset.mem_filter, Nat.mem_divisors] at hq
  rcases hq with ⟨⟨hqdiv, hn0⟩, hpp, _⟩
  constructor
  · exact hpp.one_lt.le
  · exact (Nat.le_of_dvd hn0.bot_lt hqdiv).trans (hA' n hnA)

lemma minor2_bound_end {k : ℕ} {A : Finset ℕ} (N : ℕ) (hN : 2 ≤ N) (hkN : k ≤ N / 192)
    (hA' : ∀ n : ℕ, n ∈ A → n ≤ N) :
    6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).ssubsets.sum
          (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card) ≤
      8⁻¹ := by
  have hcard : (ppowers_in_set A).card ≤ N := by
    suffices hsubset : ppowers_in_set A ⊆ Finset.Icc 1 N by
      calc
        (ppowers_in_set A).card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsubset
        _ = N := by
          rw [Nat.card_Icc]
          omega
    intro x hx
    simpa [Finset.mem_Icc] using ppowers_in_set_le hA' x hx
  calc
    6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).ssubsets.sum (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card)
        ≤
      6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).powerset.sum
          (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact Finset.sum_le_sum_of_subset_of_nonneg
              (ssubsets_subset_powerset (s := ppowers_in_set A))
              (fun _ _ _ ↦ pow_nonneg (by positivity) _)
          · positivity
    _ = 6 * (k : ℝ) * (N : ℝ)⁻¹ * (1 + (N : ℝ)⁻¹) ^ (ppowers_in_set A).card := by
          rw [powerset_sum_pow' (s := ppowers_in_set A) (x := (N : ℝ)⁻¹), add_comm]
    _ ≤ 6 * (k : ℝ) * (N : ℝ)⁻¹ * 4 := by
          have hbase : (1 : ℝ) ≤ 1 + (N : ℝ)⁻¹ := by
            nlinarith [show 0 ≤ (N : ℝ)⁻¹ by positivity]
          have hfour : (1 + (N : ℝ)⁻¹) ^ N ≤ 4 := by
            simpa [add_comm] using (thing_le_four (N := N))
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact (pow_le_pow_right₀ hbase hcard).trans hfour
          · positivity
    _ ≤ 8⁻¹ := by
          have hkN' : (k : ℝ) ≤ (N : ℝ) / 192 := by
            calc
              (k : ℝ) ≤ ((N / 192 : ℕ) : ℝ) := by exact_mod_cast hkN
              _ ≤ (N : ℝ) / 192 := Nat.cast_div_le
          have hN' : 0 < (N : ℝ) := by
            exact_mod_cast zero_lt_two.trans_le hN
          calc
            6 * (k : ℝ) * (N : ℝ)⁻¹ * 4
                ≤ 6 * ((N : ℝ) / 192) * (N : ℝ)⁻¹ * 4 := by
                  gcongr
            _ = 8⁻¹ := by
                field_simp [hN'.ne']
                norm_num
