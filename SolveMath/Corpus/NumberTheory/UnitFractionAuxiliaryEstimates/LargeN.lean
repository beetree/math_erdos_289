module

public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.PrimePower
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace UnitFractions

open Filter Finset Real
open _root_.Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

open Classical

noncomputable section

theorem yet_another_large_N' :
    ∀ᶠ N : ℕ in atTop,
      1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) ≤
        log N ^ (-(1 / 101 : ℝ)) / 6 := by
  have haux :
      Asymptotics.IsLittleO atTop (fun x : ℝ ↦ log x) (fun x ↦ x ^ (1 / 10100 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10100)
  have hbound := haux.bound (show 0 < (1000 : ℝ) / 6012 by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hbound
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (12 ^ ((101 : ℝ) / 100)))
    ] with N hsmall h0logN hlogN
  rw [← add_halves (log N ^ (-(1 / 101 : ℝ)) / 6)]
  refine add_le_add ?_ ?_
  · have hpow : (12 : ℝ) ≤ log N ^ (100 / 101 : ℝ) := by
      have h :=
        Real.rpow_le_rpow
          (show 0 ≤ (12 : ℝ) ^ ((101 : ℝ) / 100) by positivity)
          hlogN
          (by norm_num : 0 ≤ (100 : ℝ) / 101)
      calc
        (12 : ℝ) = ((12 : ℝ) ^ ((101 : ℝ) / 100)) ^ ((100 : ℝ) / 101) := by
          rw [← Real.rpow_mul (by positivity : 0 ≤ (12 : ℝ))]
          norm_num
        _ ≤ log N ^ (100 / 101 : ℝ) := h
    have hmain : 12 * (1 / log N) ≤ log N ^ (-(1 / 101 : ℝ)) := by
      calc
        12 * (1 / log N) ≤ log N ^ (100 / 101 : ℝ) * (1 / log N) := by
          gcongr
        _ = log N ^ (-(1 / 101 : ℝ)) := by
          have hInv : (1 / log N) = log N ^ (-1 : ℝ) := by
            calc
              1 / log N = (log N)⁻¹ := by ring
              _ = log N ^ (-1 : ℝ) := by
                have htmp : log N ^ (-(1 : ℝ)) = (log N ^ (1 : ℝ))⁻¹ :=
                  Real.rpow_neg h0logN.le (1 : ℝ)
                simpa [Real.rpow_one] using htmp.symm
          rw [hInv]
          have hrpow0 :
              log N ^ (100 / 101 : ℝ) * log N ^ (-1 : ℝ) =
                log N ^ ((100 / 101 : ℝ) + (-1 : ℝ)) := by
            simpa [Function.comp] using
              (Real.rpow_add h0logN (100 / 101 : ℝ) (-1 : ℝ)).symm
          calc
            log N ^ (100 / 101 : ℝ) * log N ^ (-1 : ℝ) = log N ^ ((100 / 101 : ℝ) + (-1 : ℝ)) :=
              hrpow0
            _ = log N ^ (-(1 / 101 : ℝ)) := by congr 2; norm_num
    have h12 : (0 : ℝ) < 12 := by norm_num
    nlinarith
  · have hsmall' :
        log (log N) ≤ (1000 / 6012 : ℝ) * (log N ^ (1 / 10100 : ℝ)) := by
      have hnonnegLogLog : 0 ≤ log (log N) := by
        apply Real.log_nonneg
        have h12 : (1 : ℝ) ≤ 12 ^ ((101 : ℝ) / 100) := by
          have hbase : (1 : ℝ) ≤ 12 := by norm_num
          simpa using
            (Real.rpow_le_rpow (by positivity : 0 ≤ (1 : ℝ)) hbase
              (by norm_num : 0 ≤ ((101 : ℝ) / 100)))
        exact h12.trans hlogN
      have hnonnegPow : 0 ≤ log N ^ (1 / 10100 : ℝ) := by
        positivity
      have habs :
          |log (log N)| ≤ (1000 / 6012 : ℝ) * |log N ^ (1 / 10100 : ℝ)| := by
        simpa using hsmall
      rw [abs_of_nonneg hnonnegLogLog, abs_of_nonneg hnonnegPow] at habs
      exact habs
    calc
      (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N))
          = ((501 / 1000 : ℝ) * log (log N)) * (log N ^ ((1 : ℝ) / 100))⁻¹ := by
              field_simp
              ring
      _ ≤ ((501 / 1000 : ℝ) * ((1000 / 6012 : ℝ) * (log N ^ (1 / 10100 : ℝ)))) *
            (log N ^ ((1 : ℝ) / 100))⁻¹ := by
              gcongr
      _ = (1 / 12 : ℝ) * (log N ^ (1 / 10100 : ℝ) * (log N ^ ((1 : ℝ) / 100))⁻¹) := by
            ring
      _ = (1 / 12 : ℝ) * log N ^ (-(1 / 101 : ℝ)) := by
            have hInv : (log N ^ ((1 : ℝ) / 100))⁻¹ = log N ^ (-(1 / 100 : ℝ)) := by
              have htmp : log N ^ (-(1 / 100 : ℝ)) = (log N ^ ((1 : ℝ) / 100))⁻¹ :=
                Real.rpow_neg h0logN.le ((1 : ℝ) / 100)
              exact htmp.symm
            rw [hInv]
            congr 1
            have hrpow0 :
                log N ^ (1 / 10100 : ℝ) * log N ^ (-(1 / 100 : ℝ)) =
                  log N ^ ((1 / 10100 : ℝ) + (-(1 / 100 : ℝ))) := by
              simpa [Function.comp] using
                (Real.rpow_add h0logN (1 / 10100 : ℝ) (-(1 / 100 : ℝ))).symm
            calc
              log N ^ (1 / 10100 : ℝ) * log N ^ (-(1 / 100 : ℝ)) =
                  log N ^ ((1 / 10100 : ℝ) + (-(1 / 100 : ℝ))) := hrpow0
              _ = log N ^ (-(1 / 101 : ℝ)) := by congr 2; norm_num
      _ = log N ^ (-(1 / 101 : ℝ)) / 12 := by ring
      _ = log N ^ (-(1 / 101 : ℝ)) / 6 / 2 := by ring

theorem and_another_large_N (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, 2 * log (log N) + 1 ≤ (1 + ε ^ 2) ^ ((1 - ε) * log (log N)) := by
  let c : ℝ := (1 - ε) * log (1 + ε ^ 2)
  have hbase : 1 < 1 + ε ^ 2 := by
    rw [lt_add_iff_pos_right]
    exact sq_pos_of_pos h1
  have hεlt1 : ε < 1 := lt_trans h2 one_half_lt_one
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (sub_pos.mpr hεlt1) (Real.log_pos hbase)
  have haux := (isLittleO_log_rpow_atTop hc).bound (show 0 < (1 : ℝ) / 4 by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , (tendsto_coe_log_pow_at_top c hc).eventually (eventually_ge_atTop (2 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux ] with
    N hlogN hpow hsmall
  have h0logN : 0 < log N := by
    exact lt_trans zero_lt_one hlogN
  have h0loglogN : 0 < log (log N) := Real.log_pos hlogN
  have hsmall' : log (log N) ≤ (1 / 4 : ℝ) * (log N ^ c) := by
    have habs : |log (log N)| ≤ (1 / 4 : ℝ) * |log N ^ c| := by
      simpa [Function.comp, Real.norm_eq_abs] using hsmall
    rw [abs_of_pos h0loglogN, abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos h0logN _))] at habs
    exact habs
  have hconst : 1 ≤ (1 / 2 : ℝ) * (log N ^ c) := by
    have : (2 : ℝ) ≤ log N ^ c := hpow
    nlinarith
  have hmain : 2 * log (log N) + 1 ≤ log N ^ c := by
    have hlogpart : 2 * log (log N) ≤ (1 / 2 : ℝ) * (log N ^ c) := by
      nlinarith
    linarith
  have hrpow :
      (1 + ε ^ 2) ^ ((1 - ε) * log (log N)) = log N ^ c := by
    rw [Real.rpow_def_of_pos (show 0 < 1 + ε ^ 2 by positivity), Real.rpow_def_of_pos h0logN]
    dsimp [c]
    ring_nf
  simpa [hrpow] using hmain

theorem omega_mul_ppower {a q : ℕ} (hq : IsPrimePow q) : ω (q * a) ≤ 1 + ω a := by
  have hωq_nat : ω q = 1 := by
    rcases (isPrimePow_nat_iff q).1 hq with ⟨p, k, hp, hk, rfl⟩
    simpa using ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp hk.ne'
  have hωq : (ω q : ℝ) = 1 := by exact_mod_cast hωq_nat
  have hdivω : (ω ((q * a) / q) : ℝ) = ω a := by
    rw [Nat.mul_div_cancel_left _ hq.pos]
  have hsub : (ω (q * a) : ℝ) - ω q ≤ ω ((q * a) / q) := sub_le_omega_div (dvd_mul_right q a)
  have hreal : (ω (q * a) : ℝ) ≤ 1 + ω a := by
    calc
    (ω (q * a) : ℝ) ≤ ω q + ω ((q * a) / q) := by linarith
    _ = 1 + ω a := by rw [hωq, hdivω]
  exact_mod_cast hreal

theorem prime_pow_not_coprime_iff {a b : ℕ} (ha : IsPrimePow a) (hb : IsPrimePow b) :
    ¬ Nat.Coprime a b ↔
      ∃ p ka kb : ℕ, Nat.Prime p ∧ ka ≠ 0 ∧ kb ≠ 0 ∧ p ^ ka = a ∧ p ^ kb = b := by
  constructor
  · intro hab
    rcases (isPrimePow_nat_iff a).1 ha with ⟨p, k, hp, hk, hpa⟩
    rcases (isPrimePow_nat_iff b).1 hb with ⟨r, l, hr, hl, hrb⟩
    by_cases hpr : p = r
    · refine ⟨p, k, l, hp, hk.ne', hl.ne', hpa, ?_⟩
      simpa [hpr] using hrb
    · exfalso
      apply hab
      rw [← hpa, ← hrb]
      exact Nat.coprime_pow_primes k l hp hr hpr
  · rintro ⟨p, ka, kb, hp, hka, hkb, hpa, hpb⟩
    rw [Nat.Prime.not_coprime_iff_dvd]
    refine ⟨p, hp, ?_, ?_⟩
    · rw [← hpa]
      exact dvd_pow_self _ hka
    · rw [← hpb]
      exact dvd_pow_self _ hkb

theorem prime_pow_not_coprime_prod_iff {a : ℕ} {D : Finset ℕ} (ha : IsPrimePow a)
    (hD : ∀ d ∈ D, IsPrimePow d) :
    ¬ Nat.Coprime a (D.prod id) ↔
      ∃ p ka kd d : ℕ,
        d ∈ D ∧ Nat.Prime p ∧ ka ≠ 0 ∧ kd ≠ 0 ∧ p ^ ka = a ∧ p ^ kd = d := by
  rw [Nat.coprime_prod_right_iff]
  push Not
  constructor
  · rintro ⟨d, hdD, hnc⟩
    obtain ⟨p, ka, kd, hp, hka, hkd, hpa, hpd⟩ := (prime_pow_not_coprime_iff ha (hD d hdD)).mp hnc
    exact ⟨p, ka, kd, d, hdD, hp, hka, hkd, hpa, hpd⟩
  · rintro ⟨p, ka, kd, d, hdD, hp, hka, hkd, hpa, hpd⟩
    exact ⟨d, hdD, (prime_pow_not_coprime_iff ha (hD d hdD)).mpr ⟨p, ka, kd, hp, hka, hkd, hpa, hpd⟩⟩

theorem weighted_ph {s : Finset ℕ} {f w : ℕ → ℚ} {b : ℚ} (h0b : 0 < b)
    (hw : ∀ a : ℕ, a ∈ s → 0 ≤ w a)
    (hb : b ≤ s.sum (fun x : ℕ ↦ w x * f x)) :
    ∃ (y : ℕ) (_ : y ∈ s), b ≤ s.sum (fun x : ℕ ↦ w x) * f y := by
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    rw [hs, Finset.sum_empty] at hb
    exact (not_le_of_gt h0b) hb
  by_contra h
  push Not at h
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s f hsne
  have hylt : s.sum (fun x : ℕ ↦ w x) * f y < b := h y hys
  have hsumle : s.sum (fun x : ℕ ↦ w x * f x) ≤ s.sum (fun x : ℕ ↦ w x) * f y := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mul_le_mul_of_nonneg_left (hy n hn) (hw n hn)
  exact (not_lt_of_ge hb) (lt_of_le_of_lt hsumle hylt)

theorem eq_iff_ppowers_dvd (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a = b ↔
      (∀ q, q ∣ a → IsPrimePow q → Nat.Coprime q (a / q) → q ∣ b) ∧
        ∀ q, q ∣ b → IsPrimePow q → Nat.Coprime q (b / q) → q ∣ a := by
  constructor
  · rintro rfl
    exact ⟨fun _ hq _ _ => hq, fun _ hq _ _ => hq⟩
  · rintro ⟨hab, hba⟩
    exact Nat.dvd_antisymm
      ((dvd_iff_ppowers_dvd' a b ha).2 fun q hq hq' => hab q hq hq'.1 hq'.2)
      ((dvd_iff_ppowers_dvd' b a hb).2 fun q hq hq' => hba q hq hq'.1 hq'.2)

theorem is_prime_pow_dvd_prod {n : ℕ} {D : Finset ℕ}
    (hD : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Nat.Coprime a b) (hn : IsPrimePow n) :
    n ∣ D.prod id ↔ ∃ d, d ∈ D ∧ n ∣ d := by
  refine ⟨?_, fun ⟨d, hd, hnd⟩ => hnd.trans (Finset.dvd_prod_of_mem id hd)⟩
  induction D using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Nat.dvd_one]
      intro h
      exact (hn.ne_one h).elim
  | @insert q D hqD hDind =>
      intro h
      rw [Finset.prod_insert hqD] at h
      have hnec : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Nat.Coprime a b := fun a ha b hb hab =>
        hD a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
      have hcop : Nat.Coprime q (D.prod id) := by
        rw [Nat.coprime_prod_right_iff]
        exact fun d hd => hD q (Finset.mem_insert_self q D) d (Finset.mem_insert_of_mem hd)
          fun hEq => hqD (hEq ▸ hd)
      rcases (hcop.isPrimePow_dvd_mul hn).mp h with hq | hD'
      · exact ⟨q, Finset.mem_insert_self q D, hq⟩
      · obtain ⟨d, hd1, hd2⟩ := hDind hnec hD'
        exact ⟨d, Finset.mem_insert_of_mem hd1, hd2⟩

theorem prime_pow_dvd_prime_pow {a b : ℕ} (ha : IsPrimePow a) (hb : IsPrimePow b) :
    a ∣ b ↔ ∃ p k l : ℕ, Nat.Prime p ∧ 0 < k ∧ k ≤ l ∧ p ^ k = a ∧ p ^ l = b := by
  constructor
  · intro hab
    rcases (isPrimePow_nat_iff b).1 hb with ⟨r, l, hr, hl, hrb⟩
    rw [← hrb, Nat.dvd_prime_pow hr] at hab
    obtain ⟨k, hkl, h⟩ := hab
    have hk0 : k ≠ 0 := fun hk => ha.ne_one (by rw [h, hk, pow_zero])
    exact ⟨r, k, l, hr, Nat.pos_of_ne_zero hk0, hkl, h.symm, hrb⟩
  · rintro ⟨p, k, l, hp, _hk, hkl, hpa, hpb⟩
    rw [← hpa, ← hpb]
    exact pow_dvd_pow _ hkl

theorem prime_pow_dvd_prod_prime_pow {a : ℕ} {D : Finset ℕ} (ha : IsPrimePow a)
    (hD1 : ∀ a₁ ∈ D, ∀ b ∈ D, a₁ ≠ b → Nat.Coprime a₁ b) (hD2 : ∀ d ∈ D, IsPrimePow d) :
    a ∣ D.prod id → Nat.Coprime a (D.prod id / a) → a ∈ D := by
  intro haD hacop
  by_cases hprod0 : D.prod id = 0
  · rw [hprod0, Nat.zero_div, Nat.coprime_zero_right] at hacop
    exact (ha.ne_one hacop).elim
  have haD' := haD
  rw [is_prime_pow_dvd_prod hD1 ha] at haD
  rcases haD with ⟨d, hd1, hd2⟩
  have hEq : a = d := by
    rw [prime_pow_dvd_prime_pow ha (hD2 d hd1)] at hd2
    rcases hd2 with ⟨p, k, l, hp, h0k, hkl, hpa, hpd⟩
    rw [← hpa, ← hpd]
    have hfac1 : k = (D.prod id).factorization p := by
      rw [← hpa] at haD'
      rw [← hpa] at hacop
      exact coprime_div_iff hp haD' (Nat.ne_zero_of_lt h0k) hacop
    have hfac2 : l ≤ (D.prod id).factorization p := by
      rw [← hp.pow_dvd_iff_le_factorization hprod0, hpd]
      exact Finset.dvd_prod_of_mem id hd1
    have hfac3 : k = l := le_antisymm hkl <| by
      rw [hfac1]
      exact hfac2
    rw [hfac3]
  rw [hEq]
  exact hd1

theorem my_sum_lemma {α β γ : Type*} [AddCommMonoid γ] [Preorder γ] [IsOrderedAddMonoid γ]
    {s : Finset α} {t : Finset β} (f : α → γ) (g : β → γ) (r : ∀ i ∈ s, β)
    (r_inj : ∀ a₁ a₂ ha₁ ha₂, r a₁ ha₁ = r a₂ ha₂ → a₁ = a₂)
    (hg : ∀ i ∈ t, 0 ≤ g i) (rt : ∀ a ha, r a ha ∈ t) (fr : ∀ a ha, g (r a ha) = f a) :
    s.sum f ≤ t.sum g := by
  classical
  have hEq :
      Finset.sum s.attach (fun i => f i) = Finset.sum s.attach (fun i => g (r i i.prop)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact (fr i i.prop).symm
  rw [← Finset.sum_attach, hEq, ← Finset.sum_image]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ q _ ↦ hg _ q
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    exact rt a a.prop
  · intro a₁ _ a₂ _ h
    exact Subtype.ext (r_inj _ _ _ _ h)

theorem card_bUnion_lt_card_mul_real {s : Finset ℤ} {f : ℤ → Finset ℕ} (m : ℝ)
    (h : ∀ a : ℤ, a ∈ s → ((f a).card : ℝ) < m) :
    s.Nonempty → ((s.biUnion f).card : ℝ) < s.card * m := by
  intro hs
  have hcard : (s.biUnion f).card ≤ Finset.sum s fun a => (f a).card := Finset.card_biUnion_le
  calc
    ((s.biUnion f).card : ℝ) ≤ Finset.sum s (fun a => ((f a).card : ℝ)) := by exact_mod_cast hcard
    _ < Finset.sum s (fun _ => m) := Finset.sum_lt_sum_of_nonempty hs h
    _ = s.card * m := by simp [nsmul_eq_mul]

theorem sum_add_sum_add_sum {A B C : Finset ℕ} {f : ℕ → ℝ} :
    A.sum f + B.sum f + C.sum f =
      (A ∪ B ∪ C).sum f + (A ∩ B).sum f + (A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f := by
  have hAB :
      A.sum f + B.sum f = (A ∪ B).sum f + (A ∩ B).sum f := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)).symm
  have hABC :
      (A ∪ B).sum f + C.sum f = (A ∪ B ∪ C).sum f + ((A ∪ B) ∩ C).sum f := by
    simpa [add_comm, add_left_comm, add_assoc, Finset.union_assoc] using
      (Finset.sum_union_inter (s₁ := A ∪ B) (s₂ := C) (f := f)).symm
  have hInter :
      ((A ∪ B) ∩ C).sum f = (A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f := by
    have h' := Finset.sum_union_inter (s₁ := A ∩ C) (s₂ := B ∩ C) (f := f)
    have hUnion : A ∩ C ∪ B ∩ C = (A ∪ B) ∩ C := by
      ext x
      simp [or_and_right]
    rw [hUnion] at h'
    have hEq : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
      ext x
      simp [and_left_comm]
    rw [hEq] at h'
    linarith
  calc
    A.sum f + B.sum f + C.sum f = ((A ∪ B).sum f + (A ∩ B).sum f) + C.sum f := by rw [hAB]
    _ = (A ∪ B).sum f + C.sum f + (A ∩ B).sum f := by ring
    _ = (A ∪ B ∪ C).sum f + ((A ∪ B) ∩ C).sum f + (A ∩ B).sum f := by rw [hABC]
    _ =
        (A ∪ B ∪ C).sum f +
          ((A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f) +
            (A ∩ B).sum f := by rw [hInter]
    _ = (A ∪ B ∪ C).sum f + (A ∩ B).sum f + (A ∩ C).sum f + (B ∩ C).sum f -
          (A ∩ B ∩ C).sum f := by ring

/-- The reciprocal sum of a union is at most the sum of the reciprocal sums. -/
theorem rec_sum_union_le {A B : Finset ℕ} : rec_sum (A ∪ B) ≤ rec_sum A + rec_sum B := by
  have hsub : A ∪ B ⊆ A ∪ B \ A := by
    intro n hn
    simp only [Finset.mem_union, Finset.mem_sdiff] at hn ⊢
    by_cases hnA : n ∈ A <;> tauto
  have h1 : (A ∪ B).sum (fun n ↦ (1 : ℚ) / n) ≤ (A ∪ B \ A).sum (fun n ↦ (1 : ℚ) / n) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ ↦ div_nonneg zero_le_one (by exact_mod_cast Nat.zero_le i))
  have h2 : (A ∪ B \ A).sum (fun n ↦ (1 : ℚ) / n) =
      A.sum (fun n ↦ (1 : ℚ) / n) + (B \ A).sum (fun n ↦ (1 : ℚ) / n) :=
    Finset.sum_union (Finset.disjoint_sdiff (s := A) (t := B))
  have h3 : (B \ A).sum (fun n ↦ (1 : ℚ) / n) ≤ B.sum (fun n ↦ (1 : ℚ) / n) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset (s := B) (t := A))
      (fun i _ _ ↦ div_nonneg zero_le_one (by exact_mod_cast Nat.zero_le i))
  calc
    rec_sum (A ∪ B) = (A ∪ B).sum (fun n ↦ (1 : ℚ) / n) := rfl
    _ ≤ (A ∪ B \ A).sum (fun n ↦ (1 : ℚ) / n) := h1
    _ = A.sum (fun n ↦ (1 : ℚ) / n) + (B \ A).sum (fun n ↦ (1 : ℚ) / n) := h2
    _ ≤ A.sum (fun n ↦ (1 : ℚ) / n) + B.sum (fun n ↦ (1 : ℚ) / n) := by gcongr
    _ = rec_sum A + rec_sum B := rfl

theorem rec_sum_le_three {A B C : Finset ℕ} :
    rec_sum (A ∪ B ∪ C) ≤ rec_sum A + rec_sum B + rec_sum C :=
  rec_sum_union_le.trans (by gcongr; exact rec_sum_union_le)

theorem nat_gcd_prod_le_diff {a b c : ℤ} (hab : a ≠ b) (hac : a ≠ c) :
    Nat.gcd (Int.natAbs a) (Int.natAbs (b * c)) ≤ Int.natAbs (a - b) * Int.natAbs (a - c) := by
  refine Nat.le_of_dvd ?_ ?_
  · rw [Nat.pos_iff_ne_zero]
    intro hz
    rw [mul_eq_zero, Int.natAbs_eq_zero, Int.natAbs_eq_zero, sub_eq_zero, sub_eq_zero] at hz
    rcases hz with hz | hz
    · exact hab hz
    · exact hac hz
  · rw [Int.natAbs_mul]
    refine dvd_trans (gcd_mul_dvd_mul_gcd _ _ _) ?_
    refine mul_dvd_mul ?_ ?_
    · rw [← Int.natCast_dvd]
      refine dvd_sub ?_ ?_
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
    · rw [← Int.natCast_dvd]
      refine dvd_sub ?_ ?_
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)

theorem triv_ε_estimate (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    1 - 2 * ε ≤ (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) := by
  let _ := hε2
  have hpos : 0 < 1 + ε ^ 2 := by positivity
  have hpos' : 1 + ε ^ 2 ≠ 0 := ne_of_gt hpos
  rw [div_eq_mul_inv, ← mul_assoc]
  field_simp [hpos']
  nlinarith [sq_nonneg ε, le_of_lt hε1]

theorem help_ε_estimate (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    log (1 - ε) * (1 - ε) ≤ -ε / 2 := by
  have h1ε : 0 < 1 - ε := by linarith
  calc
    log (1 - ε) * (1 - ε) ≤ ((1 - ε) - 1) * (1 - ε) := by
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt h1ε)
      simpa using Real.log_le_sub_one_of_pos h1ε
    _ = -ε * (1 - ε) := by ring
    _ ≤ -ε / 2 := by nlinarith

theorem floor_sub_ceil {x y z : ℝ} : (⌊z + x⌋ : ℝ) - ⌈z - y⌉ ≤ x + y := by
  calc
    (⌊z + x⌋ : ℝ) - ⌈z - y⌉ ≤ z + x - ⌈z - y⌉ := by
      gcongr
      exact Int.floor_le (z + x)
    _ ≤ z + x - (z - y) := by
      gcongr
      exact Int.le_ceil (z - y)
    _ = x + y := by ring

theorem useful_identity (i : ℕ) (h : (1 : ℝ) < i) :
    (1 : ℝ) + 1 / (i - 1) = |(1 - (i : ℝ)⁻¹)⁻¹| := by
  have hi0 : (0 : ℝ) < i := lt_trans zero_lt_one h
  have hineq : 0 ≤ (1 - (i : ℝ)⁻¹)⁻¹ := by
    apply inv_nonneg.mpr
    have hrewrite : 1 - (i : ℝ)⁻¹ = ((i : ℝ) - 1) / i := by
      field_simp [show (i : ℝ) ≠ 0 by linarith]
    rw [hrewrite]
    exact div_nonneg (by linarith) (le_of_lt hi0)
  rw [abs_of_nonneg hineq]
  field_simp [show (i : ℝ) ≠ 0 by linarith, show (i : ℝ) - 1 ≠ 0 by linarith]
  ring

theorem useful_exp_estimate : ((35 : ℝ) / 100) ≤ (1 - 2 * (2 / 99)) * Real.exp (-1) := by
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexp]
  nlinarith [Real.exp_one_lt_d9]

theorem rec_qsum_lower_bound (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ,
        log N ^ (-ε / 2) ≤ rec_sum A →
          (∀ n ∈ A, (1 - ε) * log (log N) ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * log (log N))) →
            (1 - 2 * ε) * Real.exp (-1) * log (log N) ≤
              (ppowers_in_set A).sum (fun q ↦ (1 / q : ℝ)) := by
  filter_upwards
    [ eventually_ge_atTop (0 : ℕ)
    , and_another_large_N ε hε1 hε2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ)) ] with
    N _ hlarge0 hlarge1 hlarge2 A hrecA hreg
  let L : ℝ := log (log N)
  let x : ℝ := (1 - ε) * L
  have hεlt1 : ε < 1 := lt_trans hε2 one_half_lt_one
  have h1ε : 0 < 1 - ε := sub_pos.mpr hεlt1
  have hL : 0 < L := by
    simpa [L] using hlarge1
  have hx : 0 < x := by
    dsimp [x]
    exact mul_pos h1ε hL
  have hreg' : ∀ n ∈ A, x ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * L) := by
    intro n hn
    simpa [x, L] using hreg n hn
  have h0A : 0 ∉ A := by
    intro h0
    have h0reg := hreg' 0 h0
    rw [ArithmeticFunction.cardDistinctFactors_zero] at h0reg
    exact (not_le_of_gt hx) (by simpa using h0reg.1)
  let S : ℝ := (ppowers_in_set A).sum (fun q ↦ (1 / q : ℝ))
  have hS : 0 < S := by
    have hAne : A.Nonempty := by
      by_contra hAne
      rw [Finset.not_nonempty_iff_eq_empty] at hAne
      simp [hAne, rec_sum] at hrecA
      have hlogN : 0 < log N := lt_of_lt_of_le zero_lt_one hlarge2
      have hpow : 0 < log N ^ (-ε / 2) := Real.rpow_pos_of_pos hlogN (-ε / 2)
      linarith
    rcases hAne with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      have h0reg := hreg' 0 (ha0 ▸ ha)
      rw [ArithmeticFunction.cardDistinctFactors_zero] at h0reg
      exact (not_le_of_gt hx) (by simpa using h0reg.1)
    have ha1 : a ≠ 1 := by
      intro ha1
      have h1reg := hreg' 1 (ha1 ▸ ha)
      rw [ArithmeticFunction.cardDistinctFactors_one] at h1reg
      exact (not_le_of_gt hx) (by simpa using h1reg.1)
    have ha2 : 2 ≤ a := by omega
    have hpp : (ppowers_in_set A).Nonempty := ppowers_in_set_nonempty ⟨a, ha, ha2⟩
    dsimp [S]
    refine Finset.sum_pos ?_ hpp
    intro q hq
    have hq0 : q ≠ 0 := by
      intro hq0
      rw [hq0] at hq
      exact zero_not_mem_ppowers_in_set hq
    rw [one_div_pos]
    exact_mod_cast Nat.pos_of_ne_zero hq0
  let D : ℝ := Real.exp (-1) * x
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (Real.exp_pos (-1)) hx
  by_cases hdone : x < S
  · have hcoef : (1 - 2 * ε) * Real.exp (-1) ≤ 1 - ε := by
      have hexp : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
        exact (le_of_lt Real.exp_neg_one_lt_d9).trans (by norm_num)
      nlinarith
    have hmain := mul_le_mul_of_nonneg_right hcoef (le_of_lt hL)
    simpa [S, x, L, mul_assoc, mul_left_comm, mul_comm] using hmain.trans (le_of_lt hdone)
  · have hSle : S ≤ x := not_lt.mp hdone
    let I : Finset ℕ := (Finset.range (⌊2 * L⌋₊ + 1)).filter (fun n : ℕ ↦ x ≤ n)
    have hrec_upper :
        rec_sum A ≤ I.sum (fun t ↦ S ^ t / Nat.factorial t) := by
      refine rec_sum_le_prod_sum h0A ?_
      intro n hn
      have hnreg := hreg' n hn
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hnreg.1⟩
      rw [Nat.lt_succ_iff]
      exact Nat.le_floor hnreg.2
    have hsum_upper :
        I.sum (fun t ↦ S ^ t / Nat.factorial t) ≤
          I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      rw [div_pow]
      have hpow_pos : 0 < S ^ t := pow_pos hS t
      have hfac_pos : 0 < (t.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos t
      have hden_pos : 0 < (((t : ℝ) * Real.exp (-1)) ^ t) := by
        cases t with
        | zero =>
            simp
        | succ t =>
            have hbase : 0 < (((Nat.succ t : ℕ) : ℝ) * Real.exp (-1)) := by positivity
            exact pow_pos hbase _
      exact (div_le_div_iff_of_pos_left hpow_pos hfac_pos hden_pos).2 (factorial_bound t)
    have hpointwise :
        ∀ t ∈ I, (S / (t * Real.exp (-1))) ^ t ≤ (S / D) ^ x := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      simpa [D, x, mul_assoc, mul_left_comm, mul_comm] using
        (helpful_decreasing_bound hS ht'.2 hSle)
    have hsum_card :
        I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) ≤ (I.card : ℝ) * (S / D) ^ x := by
      have h := Finset.sum_le_card_nsmul I (fun t ↦ (S / (t * Real.exp (-1))) ^ t) ((S / D) ^ x)
        (fun t ht ↦ hpointwise t ht)
      simpa [nsmul_eq_mul] using h
    have hIcard_nat : I.card ≤ (Finset.range (⌊2 * L⌋₊ + 1)).card := by
      simpa [I] using
        (Finset.card_filter_le (s := Finset.range (⌊2 * L⌋₊ + 1)) (p := fun n : ℕ ↦ x ≤ n))
    have hIcard :
        (I.card : ℝ) ≤ (1 + ε ^ 2) ^ x := by
      calc
        (I.card : ℝ) ≤ ((Finset.range (⌊2 * L⌋₊ + 1)).card : ℝ) := by
          exact_mod_cast hIcard_nat
        _ = (⌊2 * L⌋₊ : ℝ) + 1 := by simp
        _ ≤ 2 * L + 1 := by
          have hfloor : (⌊2 * L⌋₊ : ℝ) ≤ 2 * L := Nat.floor_le (by positivity)
          linarith
        _ ≤ (1 + ε ^ 2) ^ x := by
          simpa [x, L] using hlarge0
    have hrec_bound :
        log N ^ (-ε / 2) ≤ (1 + ε ^ 2) ^ x * (S / D) ^ x := by
      have hpow_nonneg : 0 ≤ (S / D) ^ x := by positivity
      calc
        log N ^ (-ε / 2) ≤ rec_sum A := hrecA
        _ ≤ I.sum (fun t ↦ S ^ t / Nat.factorial t) := hrec_upper
        _ ≤ I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) := hsum_upper
        _ ≤ (I.card : ℝ) * (S / D) ^ x := hsum_card
        _ ≤ (1 + ε ^ 2) ^ x * (S / D) ^ x := by
          exact mul_le_mul_of_nonneg_right hIcard hpow_nonneg
    have hleft :
        (1 - ε) ^ x ≤ log N ^ (-ε / 2) := by
      have hEq : (1 - ε) ^ x = log N ^ (log (1 - ε) * (1 - ε)) := by
        dsimp [x, L]
        nth_rewrite 1 [← Real.exp_log h1ε]
        rw [← Real.exp_mul, ← mul_assoc, mul_comm _ (log (log N)), Real.exp_mul,
          Real.exp_log]
        exact lt_of_lt_of_le zero_lt_one hlarge2
      rw [hEq]
      refine Real.rpow_le_rpow_of_exponent_le hlarge2 ?_
      exact help_ε_estimate ε hε1 hε2
    have hbase_nonneg : 0 ≤ (1 - ε) / (1 + ε ^ 2) := by
      exact div_nonneg (le_of_lt h1ε) (by positivity)
    have hright_nonneg : 0 ≤ S / D := by
      exact div_nonneg (le_of_lt hS) (le_of_lt hD)
    have hbase :
        (1 - ε) / (1 + ε ^ 2) ≤ S / D := by
      rw [← Real.rpow_le_rpow_iff hbase_nonneg hright_nonneg hx]
      have hfac_pos : 0 < (1 + ε ^ 2) ^ x := Real.rpow_pos_of_pos (by positivity) x
      calc
        ((1 - ε) / (1 + ε ^ 2)) ^ x = (1 - ε) ^ x / (1 + ε ^ 2) ^ x := by
          rw [Real.div_rpow (le_of_lt h1ε) (by positivity)]
        _ ≤ log N ^ (-ε / 2) / (1 + ε ^ 2) ^ x := by
          exact (div_le_div_iff_of_pos_right hfac_pos).2 hleft
        _ ≤ (S / D) ^ x := by
          rw [div_le_iff₀ hfac_pos]
          simpa [mul_assoc, mul_left_comm, mul_comm] using hrec_bound
    have hmid : ((1 - ε) / (1 + ε ^ 2)) * D ≤ S := by
      exact (le_div_iff₀ hD).mp hbase
    have htriv :
        (1 - 2 * ε) * Real.exp (-1) * L ≤
          (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) * Real.exp (-1) * L := by
      have hcoef := triv_ε_estimate ε hε1 hε2
      have hEL_nonneg : 0 ≤ Real.exp (-1) * L := by
        exact mul_nonneg (le_of_lt (Real.exp_pos (-1))) (le_of_lt hL)
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hcoef hEL_nonneg
    have hmid' :
        (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) * Real.exp (-1) * L ≤ S := by
      simpa [D, x, L, mul_assoc, mul_left_comm, mul_comm] using hmid
    simpa [S, L] using htriv.trans hmid'


end

end UnitFractions
