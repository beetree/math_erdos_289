module

public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.Basic
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

@[expose] public section

namespace UnitFractions

open Filter Finset Real
open _root_.Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

open Classical

noncomputable section

theorem prime_power_recip_downward_bound (A : Finset ℕ) (ha : ∀ q ∈ A, IsPrimePow q)
    (N : ℕ) (hN : A.card ≤ ((range N).filter IsPrimePow).card) :
    A.sum (fun q ↦ (1 : ℝ) / q) ≤ ((range N).filter IsPrimePow).sum (fun q ↦ (1 : ℝ) / q) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [Finset.sum_empty]
    refine Finset.sum_nonneg ?_
    simp
  let a := A.max' hA
  let choices : Finset (Finset ℕ) :=
    (((range (a + 1)).filter IsPrimePow).powerset.filter fun B =>
      B.card ≤ ((range N).filter IsPrimePow).card)
  have hAc : A ∈ choices := by
    simp only [choices, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range,
      Nat.lt_add_one_iff]
    exact ⟨fun b hb ↦ ⟨Finset.le_max' _ _ hb, ha _ hb⟩, hN⟩
  by_cases haN : a < N
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun a' ha' => ?_) ?_
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨(Finset.le_max' _ _ ha').trans_lt haN, ha _ ha'⟩
    · simp
  have haN : N ≤ a := Nat.le_of_not_gt haN
  have hchoices : choices.Nonempty := ⟨A, hAc⟩
  obtain ⟨B, hB, hB'⟩ := Finset.exists_max_image choices
    (fun B ↦ B.sum fun q ↦ (1 : ℝ) / q) hchoices
  simp only [choices, Finset.mem_filter, Finset.mem_powerset] at hB
  suffices hEq : (range N).filter IsPrimePow = B by
    rw [hEq]
    exact hB' _ hAc
  suffices hsub : (range N).filter IsPrimePow ⊆ B by
    exact Finset.eq_of_subset_of_card_le hsub hB.2
  by_contra h
  have hBpp : ∀ a : ℕ, a ∈ B → IsPrimePow a := by
    intro x hx
    exact (Finset.mem_filter.mp (hB.1 hx)).2
  rcases this_condition_here hBpp hB.2 h with
    ⟨r, hr, hr', hr'', a', ha', hra'⟩ | hssub
  · have hr''' : r ∉ B.erase a' := fun hrB ↦ hr' (Finset.erase_subset _ _ hrB)
    let B' := (B.erase a').cons r hr'''
    have hra : r ≤ a := hra'.le.trans <| by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (hB.1 ha')).1)
    have hB'' : B' ∈ choices := by
      simp only [choices, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · change (B.erase a').cons r hr''' ⊆ (range (a + 1)).filter IsPrimePow
        rw [Finset.cons_subset]
        constructor
        · rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
          exact ⟨hra, hr''⟩
        · exact (Finset.erase_subset _ _).trans hB.1
      · change ((B.erase a').cons r hr''').card ≤ ((range N).filter IsPrimePow).card
        have hcard :
            ((B.erase a').cons r hr''').card = B.card := by
          rw [Finset.card_cons, Finset.card_erase_of_mem ha',
            Nat.sub_add_cancel (Finset.card_pos.mpr ⟨a', ha'⟩)]
        exact hcard.symm ▸ hB.2
    have hmax := hB' B' hB''
    rw [Finset.sum_cons, ← Finset.add_sum_erase _ _ ha', add_le_add_iff_right] at hmax
    exact (not_le_of_gt hra') <| Nat.cast_le.mp <|
      le_of_one_div_le_one_div (by exact_mod_cast hr''.pos) hmax
  · obtain ⟨b, hb, hb'⟩ := Finset.ssubset_iff_exists_cons_subset.mp hssub
    let B' := B.cons b hb
    have hB'' : B' ∈ choices := by
      simp only [choices, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · change B.cons b hb ⊆ (range (a + 1)).filter IsPrimePow
        rw [Finset.cons_subset]
        constructor
        · have hbmem := hb' (Finset.mem_cons_self b B)
          rw [Finset.mem_filter, Finset.mem_range] at hbmem
          rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff] at ⊢
          exact ⟨hbmem.1.le.trans haN, hbmem.2⟩
        · intro x hx
          have hxmem := hb' (Finset.mem_cons_of_mem hx)
          rw [Finset.mem_filter, Finset.mem_range] at hxmem
          rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff] at ⊢
          exact ⟨hxmem.1.le.trans haN, hxmem.2⟩
      · change (B.cons b hb).card ≤ ((range N).filter IsPrimePow).card
        exact Finset.card_le_card hb'
    have hmax := hB' _ hB''
    rw [Finset.sum_cons, add_le_iff_nonpos_left, one_div_nonpos, ← Nat.cast_zero, Nat.cast_le,
      le_zero_iff] at hmax
    have hbmem : b ∈ (range N).filter IsPrimePow := hb' (Finset.mem_cons_self b B)
    exact (Finset.mem_filter.mp hbmem).2.pos.ne' hmax

theorem Omega_eq_card_prime_pow_divisors {n : ℕ} (hn : n ≠ 0) :
    Ω n = (n.divisors.filter IsPrimePow).card := by
  revert hn
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ n
  · intro p k hp hk hpk
    rw [Nat.divisors_prime_pow hp, ArithmeticFunction.cardFactors_apply_prime_pow hp]
    have hfilter :
        (Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩
          (Finset.range (k + 1))).filter IsPrimePow =
          Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Finset.Ico 1 (k + 1)) := by
      rw [Finset.filter_map]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply, Finset.mem_Ico]
      refine ⟨fun ⟨hik, hpp⟩ ↦ ⟨Nat.pos_of_ne_zero fun hi0 ↦
          not_isPrimePow_one (by simpa [hi0] using hpp), hik⟩,
        fun ⟨hi1, hik⟩ ↦
          ⟨hik, (isPrimePow_pow_iff (Nat.one_le_iff_ne_zero.mp hi1)).2 hp.isPrimePow⟩⟩
    rw [hfilter, Finset.card_map, Nat.card_Ico]
    omega
  · simp
  · simp [Finset.filter_singleton, not_isPrimePow_one]
  · intro a b ha hb hab haI hbI hab0
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [Nat.mul_divisors_filter_prime_pow hab, Finset.filter_union,
      ArithmeticFunction.cardFactors_mul ha0 hb0, haI ha0, hbI hb0,
      Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro d hdA hdB
    have hda : d ∣ a := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdA).1
    have hdb : d ∣ b := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdB).1
    have hd1 : d = 1 := Nat.eq_one_of_dvd_coprimes hab hda hdb
    exact (not_isPrimePow_one <| hd1 ▸ (Finset.mem_filter.mp hdA).2).elim

theorem rec_pp_sum_close :
    ∀ᶠ N : ℕ in atTop,
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
                (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N) := by
  filter_upwards
    [ eventually_gt_atTop 0
    , such_large_N_wow
    , (weird_floor_sq_tendsto_at_top.comp tendsto_natCast_atTop_atTop).eventually
        prime_counting_lower_bound_explicit
    , (weird_floor_sq_tendsto_at_top.comp tendsto_natCast_atTop_atTop).eventually
        explicit_mertens ] with N hlarge0 hlarge1 hprimes hmertens x y hxy hxyN
  let m := Int.natAbs (x - y)
  let M := Ω m
  let T := ⌈Real.logb 2 N⌉₊ ^ 2
  have hm : m ≠ 0 := by
    rwa [Int.natAbs_ne_zero, sub_ne_zero]
  have hMT : M ≤ ((Finset.range (T + 1)).filter IsPrimePow).card := by
    calc
      M ≤ ⌊Real.logb 2 m⌋₊ := card_factors_le_log
      _ ≤ ⌊Real.sqrt T⌋₊ := by
        refine Nat.le_floor ?_
        have hlogm_nonneg : 0 ≤ Real.logb 2 m := by
          exact Real.logb_nonneg one_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hm)
        refine le_trans (Nat.floor_le hlogm_nonneg) ?_
        calc
          Real.logb 2 m ≤ Real.logb 2 N := by
            rw [nat_cast_diff_issue] at hxyN
            exact Real.logb_le_logb_of_le one_lt_two
              (by exact_mod_cast Nat.pos_of_ne_zero hm) hxyN
          _ ≤ Real.sqrt T := by
            dsimp [T]
            push_cast
            rw [Real.sqrt_sq]
            · exact_mod_cast Nat.le_ceil (Real.logb 2 N)
            · positivity
      _ ≤ ((Finset.Icc 1 T).filter Nat.Prime).card := hprimes
      _ ≤ ((Finset.range (T + 1)).filter IsPrimePow).card := by
        refine Finset.card_le_card ?_
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Icc] at hp
        rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
        exact ⟨hp.1.2, hp.2.isPrimePow⟩
  calc
    ((range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
        (fun q : ℕ ↦ (1 : ℝ) / q) ≤
      ((Finset.range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ n ∣ m)).sum
        (fun q : ℕ ↦ (1 : ℝ) / q) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro q hq
            rw [Finset.mem_filter] at hq
            rw [Finset.mem_filter]
            refine ⟨hq.1, hq.2.1, ?_⟩
            exact Int.natCast_dvd_natCast.mp <| by
              simpa [m] using Int.dvd_natAbs.mpr (dvd_sub hq.2.2.1 hq.2.2.2)
          · intro q _ _
            positivity
    _ ≤ ((Finset.range (T + 1)).filter IsPrimePow).sum (fun q : ℕ ↦ (1 : ℝ) / q) := by
          refine prime_power_recip_downward_bound _ ?_ _ ?_
          · intro q hq
            exact (Finset.mem_filter.mp hq).2.1
          · have hcard :
                ((Finset.range (N + 1)).filter fun n : ℕ ↦ IsPrimePow n ∧ n ∣ m).card ≤ Ω m := by
              rw [Omega_eq_card_prime_pow_divisors hm]
              refine Finset.card_le_card ?_
              intro x hx
              rcases Finset.mem_filter.mp hx with ⟨_, hxpp, hxdvd⟩
              refine Finset.mem_filter.mpr ?_
              constructor
              · rw [Nat.mem_divisors]
                exact ⟨hxdvd, hm⟩
              · exact hxpp
            exact hcard.trans hMT
    _ < ((1 : ℝ) / 500) * log (log N) := by
          refine lt_of_le_of_lt hmertens ?_
          dsimp [T]
          push_cast
          exact hlarge1

theorem ppowers_count_eq_prime_count {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.filter fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card =
      (n.divisors.filter Nat.Prime).card := by
  let f : ℕ → ℕ := fun p ↦ p ^ n.factorization p
  have h₁ :
      n.divisors.filter (fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)) =
        (n.divisors.filter Nat.Prime).image f := by
    ext r
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro ha
      have hdivr : r ∣ n := Nat.dvd_of_mem_divisors ha.1
      rcases (isPrimePow_nat_iff r).1 ha.2.1 with ⟨p, k, hp, hk, hpk⟩
      have hdivpk : p ^ k ∣ n := by simpa [hpk] using hdivr
      have hcop : Nat.Coprime (p ^ k) (n / p ^ k) := by simpa [hpk] using ha.2.2
      refine ⟨p, ?_, ?_⟩
      · rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨dvd_trans (dvd_pow_self _ hk.ne') hdivpk, hn⟩, hp⟩
      · dsimp [f]
        rw [← hpk, (coprime_div_iff hp hdivpk hk.ne' hcop).symm]
    · rintro ⟨p, hp, hpa⟩
      subst r
      rcases Finset.mem_filter.mp hp with ⟨hpDiv, hpPrime⟩
      have hpdvd : p ∣ n := Nat.dvd_of_mem_divisors hpDiv
      have h0fac : 0 < n.factorization p := hpPrime.factorization_pos_of_dvd hn hpdvd
      refine ⟨?_, hpPrime.isPrimePow.pow h0fac.ne', ?_⟩
      · rw [Nat.mem_divisors]
        exact ⟨Nat.ordProj_dvd n p, hn⟩
      · have : n.factorization p = n.factorization p := rfl
        rw [← factorization_eq_iff hpPrime h0fac.ne'] at this
        exact this.2
  rw [h₁]
  refine Finset.card_image_of_injOn ?_
  intro p₁ hp₁ p₂ hp₂ hps
  rcases Finset.mem_filter.mp hp₁ with ⟨hp₁div, hp₁prime⟩
  rcases Finset.mem_filter.mp hp₂ with ⟨hp₂div, hp₂prime⟩
  exact eq_of_prime_pow_eq (Nat.prime_iff.mp hp₁prime) (Nat.prime_iff.mp hp₂prime)
    (hp₁prime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_divisors hp₁div)) hps

theorem omega_count_eq_ppowers {n : ℕ} :
    (n.divisors.filter fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card = ω n := by
  by_cases hn0 : n = 0
  · rw [hn0]
    simp
  · rw [ppowers_count_eq_prime_count hn0]
    have hEq : n.divisors.filter Nat.Prime = n.primeFactors := by
      ext q
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors_of_ne_zero hn0]
      constructor
      · intro h
        exact ⟨h.2, h.1.1⟩
      · intro h
        exact ⟨⟨h.2, hn0⟩, h.1⟩
    rw [hEq, ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

theorem factorial_bound (t : ℕ) : ((t : ℝ) * exp (-1)) ^ t ≤ t.factorial := by
  have hpoweq : ((t : ℝ) * exp (-1)) ^ t = ((t : ℝ) / exp 1) ^ t := by
    rw [div_eq_mul_inv, Real.exp_neg]
  rw [hpoweq]
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · simp [h0]
  · have hone : (1 : ℝ) ≤ √(2 * Real.pi * t) := by
      rw [Real.one_le_sqrt]
      nlinarith [Real.pi_gt_three, show (1 : ℝ) ≤ (t : ℝ) by exact_mod_cast h0]
    calc ((t : ℝ) / exp 1) ^ t ≤ √(2 * Real.pi * t) * ((t : ℝ) / exp 1) ^ t :=
          le_mul_of_one_le_left (by positivity) hone
      _ ≤ t.factorial := Stirling.le_factorial_stirling t

theorem helpful_decreasing_bound {x y : ℝ} {n : ℕ} (h0y : 0 < y) (hn : x ≤ n) (hy : y ≤ x) :
    (y / (n * exp (-1))) ^ n ≤ (y / (x * exp (-1))) ^ x := by
  have hx0 : 0 < x := lt_of_lt_of_le h0y hy
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le hx0 hn
  have hnexp : 0 < (n * exp (-1)) := mul_pos hn0 (exp_pos (-1))
  have hxexp : 0 < x * exp (-1) := mul_pos hx0 (exp_pos (-1))
  have hleft : 0 < y / (n * exp (-1)) := div_pos h0y hnexp
  have hright : 0 < y / (x * exp (-1)) := div_pos h0y hxexp
  let f : ℝ → ℝ := fun t ↦ (log y + 1) * t - t * log t
  have hderiv : ∀ t, t ≠ 0 → deriv f t = log y - log t := by
    intro t ht
    have hsub := deriv_fun_sub
      (f := fun s : ℝ ↦ (log y + 1) * s)
      (g := fun s : ℝ ↦ s * log s)
      (x := t)
      ((differentiableAt_const _).mul differentiableAt_id)
      (differentiableAt_id.mul (differentiableAt_log ht))
    have hlin : deriv (fun s : ℝ ↦ (log y + 1) * s) t = log y + 1 := by
      simp
    calc
      deriv f t =
          deriv (fun s : ℝ ↦ (log y + 1) * s) t - deriv (fun s : ℝ ↦ s * log s) t := by
        simpa [f] using hsub
      _ = (log y + 1) - (log t + 1) := by rw [hlin, Real.deriv_mul_log ht]
      _ = log y - log t := by ring
  have hcont : ContinuousOn f (Set.Ici y) := by
    refine ContinuousOn.sub ?_ ?_
    · exact (continuous_const.mul continuous_id).continuousOn
    · refine ContinuousOn.mul continuous_id.continuousOn ?_
      refine Real.continuousOn_log.mono ?_
      intro z hz
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le h0y hz)
  have hdiff : DifferentiableOn ℝ f (interior (Set.Ici y)) := by
    intro z hz
    rw [interior_Ici, Set.mem_Ioi] at hz
    dsimp [f]
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub ?_ ?_
    · exact (differentiableAt_const _).mul differentiableAt_id
    · exact differentiableAt_id.mul (differentiableAt_log (ne_of_gt (lt_trans h0y hz)))
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici y) hcont hdiff
    (fun z hz ↦ by
      rw [interior_Ici, Set.mem_Ioi] at hz
      rw [hderiv z (ne_of_gt (lt_trans h0y hz)), sub_nonpos]
      exact Real.log_le_log h0y (le_of_lt hz))
  have hxIci : x ∈ Set.Ici y := by
    rw [Set.mem_Ici]
    exact hy
  have hnIci : (n : ℝ) ∈ Set.Ici y := by
    rw [Set.mem_Ici]
    exact le_trans hy hn
  specialize hanti hxIci hnIci hn
  have hleft' : (y / (n * exp (-1))) ^ n = Real.exp (f n) := by
    calc
      (y / (n * exp (-1))) ^ n = (Real.exp (Real.log (y / (n * exp (-1))))) ^ n := by
        rw [Real.exp_log hleft]
      _ = Real.exp ((n : ℝ) * Real.log (y / (n * exp (-1)))) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (f n) := by
        congr 1
        rw [Real.log_div (ne_of_gt h0y) (ne_of_gt hnexp),
          Real.log_mul (ne_of_gt hn0) (ne_of_gt (exp_pos (-1))), Real.log_exp]
        dsimp [f]
        ring
  have hright' : (y / (x * exp (-1))) ^ x = Real.exp (f x) := by
    rw [Real.rpow_def_of_pos hright]
    congr 1
    rw [Real.log_div (ne_of_gt h0y) (ne_of_gt hxexp),
      Real.log_mul (ne_of_gt hx0) (ne_of_gt (exp_pos (-1))), Real.log_exp]
    dsimp [f]
    ring
  rw [hleft', hright']
  exact (Real.exp_le_exp).2 hanti

theorem sub_le_omega_div {a b : ℕ} (h : b ∣ a) : (ω a : ℝ) - ω b ≤ ω (a / b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 0 := by simpa using h
    simp
  have hnat : ω a ≤ ω b + ω (a / b) := by
    simp only [ArithmeticFunction.cardDistinctFactors_apply]
    obtain ⟨k, rfl⟩ := h
    have hk0 : k ≠ 0 := by
      intro hk0
      simp [hk0] at ha
    have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [Nat.mul_div_cancel_left _ hb, add_comm, ← List.length_append]
    apply List.Subperm.length_le
    refine (List.nodup_dedup _).subperm ?_
    intro x hx
    rw [List.mem_dedup, Nat.mem_primeFactorsList_mul hb.ne' hk.ne'] at hx
    simpa [or_comm] using hx
  rw [sub_le_iff_le_add, add_comm]
  exact_mod_cast hnat

theorem omega_div_le {a b : ℕ} (h : b ∣ a) : ω (a / b) ≤ ω a := by
  obtain ⟨k, rfl⟩ := h
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  simp only [ArithmeticFunction.cardDistinctFactors_apply, Nat.mul_div_cancel_left _ hb]
  refine (List.nodup_dedup _).subperm ?_ |>.length_le
  intro t ht
  rw [List.mem_dedup, Nat.mem_primeFactorsList_mul hb.ne' hk]
  exact Or.inr (List.mem_dedup.mp ht)

theorem div_bound_useful_version {ε : ℝ} (hε1 : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ, n ≤ N ^ 2 → (ArithmeticFunction.sigma 0 n : ℝ) ≤
        N ^ (2 * Real.log 2 / log (log (N : ℝ)) * (1 + ε)) := by
  let c : ℝ := ε / 2
  have hc : 0 < c := half_pos hε1
  have hhelp0 : 1 ≤ 2 * Real.log 2 * (1 + ε) := by
    have hbase : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    calc
      1 ≤ 2 * Real.log 2 := hbase
      _ ≤ 2 * Real.log 2 * (1 + ε) := by
        have hpos : 0 ≤ 2 * Real.log 2 := le_of_lt (mul_pos zero_lt_two (Real.log_pos one_lt_two))
        nlinarith
  have hhelp : 0 < 2 * Real.log 2 * (1 + ε) := lt_of_lt_of_le zero_lt_one hhelp0
  have hhelp2 : 0 < (1 + ε) / (1 + c) := by
    refine div_pos (add_pos zero_lt_one hε1) (add_pos zero_lt_one hc)
  have hboundc : 0 < (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) := by
    refine div_pos ?_ hhelp2
    rw [sub_pos, one_lt_div]
    · simpa [c] using half_lt_self hε1
    · exact add_pos zero_lt_one hc
  have haux := (isLittleO_log_id_atTop).bound hboundc
  have hdiv := divisor_bound hc
  rw [Filter.eventually_atTop] at hdiv
  rcases hdiv with ⟨M, hdiv⟩
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    , ((tendsto_pow_rec_log_log_at_top hhelp).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (M : ℝ))
    , ((tendsto_pow_rec_log_log_at_top hhelp).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (Real.exp 1))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with
    N h1N hN hN' hlarge h0logN h0loglogN h0logloglogN
  intro n hn
  let X : ℝ := N ^ (2 * Real.log 2 / log (log (N : ℝ)) * (1 + ε))
  have hXhelp : X = N ^ (2 * Real.log 2 * (1 + ε) / log (log (N : ℝ))) := by
    dsimp [X]
    rw [div_eq_mul_inv]
    ring_nf
  have hMX : (M : ℝ) ≤ X := by
    rw [hXhelp]
    exact hN
  have heX : Real.exp 1 ≤ X := by
    rw [hXhelp]
    exact hN'
  have h1X : 1 < X := by
    exact lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) heX
  have hlogX : 0 < log X := Real.log_pos h1X
  by_cases hnbig : (n : ℝ) ≤ X
  · exact (trivial_divisor_bound.trans hnbig)
  rw [not_le] at hnbig
  have hloglogn' : 0 < log (log n) := by
    refine Real.log_pos ?_
    rw [Real.lt_log_iff_exp_lt]
    · exact lt_of_le_of_lt heX hnbig
    · exact lt_trans (lt_trans zero_lt_one h1X) hnbig
  have hloglogn : 0 ≤ log (log n) := le_of_lt hloglogn'
  have hnM : (M : ℝ) ≤ n := le_trans hMX (le_of_lt hnbig)
  refine le_trans (hdiv n ?_) ?_
  · exact_mod_cast hnM
  transitivity ((N : ℝ) ^ 2) ^ (Real.log 2 / log (log ↑n) * (1 + c))
  · refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact_mod_cast Nat.zero_le n
    · exact_mod_cast hn
    · refine mul_nonneg ?_ ?_
      · exact div_nonneg (Real.log_nonneg one_le_two) hloglogn
      · exact add_nonneg zero_le_one (le_of_lt hc)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast Nat.zero_le N)]
    have hlarge' :
        log (log (log N)) ≤
          (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) * log (log N) := by
      have htmp : |log (log (log N))| ≤
          (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) * |log (log N)| := by
        simpa [Function.comp, Real.norm_eq_abs] using hlarge
      rw [show |log (log (log N))| = log (log (log N)) by exact abs_of_pos h0logloglogN] at htmp
      rw [show |log (log N)| = log (log N) by exact abs_of_pos h0loglogN] at htmp
      exact htmp
    have hcoef :
        (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) = 1 - (1 + c) / (1 + ε) := by
      field_simp [hhelp2.ne']
    have hconst : 0 ≤ log (2 * Real.log 2 * (1 + ε)) := Real.log_nonneg hhelp0
    have hlogXeq :
        log (log X) =
          log (2 * Real.log 2 * (1 + ε)) + log (log N) - log (log (log N)) := by
      rw [hXhelp, Real.log_rpow (lt_of_lt_of_le zero_lt_one h1N)]
      have hcalc :
          2 * Real.log 2 * (1 + ε) / log (log N) * log N =
            (2 * Real.log 2 * (1 + ε) * log N) / log (log N) := by
        ring
      rw [hcalc, Real.log_div, Real.log_mul]
      · exact ne_of_gt hhelp
      · exact ne_of_gt h0logN
      · exact ne_of_gt (mul_pos hhelp h0logN)
      · exact ne_of_gt h0loglogN
    have hXmain : ((1 + c) / (1 + ε)) * log (log N) ≤ log (log X) := by
      rw [hlogXeq]
      rw [hcoef] at hlarge'
      nlinarith [hconst, hlarge']
    have hXlog : log (log X) ≤ log (log n) := by
      refine Real.log_le_log hlogX ?_
      exact Real.log_le_log (lt_trans zero_lt_one h1X) (le_of_lt hnbig)
    have hmain : ((1 + c) / (1 + ε)) * log (log N) ≤ log (log n) :=
      le_trans hXmain hXlog
    have hfrac' : (1 + c) / log (log n) ≤ (1 + ε) / log (log N) := by
      have hεpos : 0 < 1 + ε := add_pos zero_lt_one hε1
      have hmain'' :
          ((1 + c) / (1 + ε)) * log (log N) * (1 + ε) ≤ log (log n) * (1 + ε) := by
        exact mul_le_mul_of_nonneg_right hmain (le_of_lt hεpos)
      have hmain' : (1 + c) * log (log N) ≤ (1 + ε) * log (log n) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hεpos.ne'] using hmain''
      exact (div_le_div_iff₀ hloglogn' h0loglogN).2 hmain'
    have hfrac :
        Real.log 2 / log (log ↑n) * (1 + c) ≤
          Real.log 2 / log (log ↑N) * (1 + ε) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hfrac' (le_of_lt (Real.log_pos one_lt_two))
    have hpowbound :
        (N : ℝ) ^ (2 * (Real.log 2 / log (log ↑n) * (1 + c))) ≤
          (N : ℝ) ^ (2 * (Real.log 2 / log (log ↑N) * (1 + ε))) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact_mod_cast h1N
      · exact mul_le_mul_of_nonneg_left hfrac zero_le_two
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpowbound

theorem another_large_N (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      1 / c / 2 ≤ log (log (log N)) ∧
        2 ^ ((100 : ℝ) / 99) ≤ log N ∧
        4 * log (log (log N)) ≤ log (log N) ∧
        log 2 < log (log (log N)) ∧
        log N ^ (-((2 : ℝ) / 99) / 2) ≤
          C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) /
            log N ^ ((2 : ℝ) / ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) ∧
        (1 - 2 / 99) * log (log N) +
            (1 + 5 / log (⌊(log (log N)) / (2 * log (log (log N)))⌋₊) * log (log N)) ≤
          (99 / 100 : ℝ) * log (log N) := by
  let _ := hc
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 4 by norm_num))
  have haux2 := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 3960000 by norm_num))
  have haux3 := (Real.isLittleO_log_id_atTop.bound <| by
    have hden : 0 < ((Real.exp 10000 + 1) * 2 : ℝ) := by
      positivity
    exact one_div_pos.2 hden)
  have hhelp : 0 < (1 : ℝ) / 10000 := by
    norm_num
  filter_upwards
    [ (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux3
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((2 : ℝ) ^ ((100 : ℝ) / 99)))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_ge_atTop (1 / c / 2))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (log 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (1000 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ))
    , ((tendsto_rpow_atTop hhelp).comp
          (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((C / 2)⁻¹)) ] with
    N hlarge hlarge2 hlarge3 h0logN h1logN hlogN hlogloglogN' hlogloglogN h0loglogN hloglogN
      h0logloglogN hlargepow
  dsimp at hlargepow
  have h0logN_real : 0 < log N := by
    simpa [Function.comp] using h0logN
  have h1logN_real : 1 ≤ log N := by
    simpa [Function.comp] using h1logN
  have h0loglogN_real : 0 < log (log N) := by
    simpa [Function.comp] using h0loglogN
  have hloglogN_real : (1000 : ℝ) ≤ log (log N) := by
    simpa [Function.comp] using hloglogN
  have h0logloglogN_real : 0 < log (log (log N)) := by
    simpa [Function.comp] using h0logloglogN
  let x : ℝ := (log (log N)) / (2 * log (log (log N)))
  let F : ℝ := ⌊x⌋₊
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (le_of_lt h0loglogN_real)
      (mul_nonneg zero_le_two (le_of_lt h0logloglogN_real))
  have hlarge_abs : |log (log (log N))| ≤ (1 / 4 : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge
  have hlarge2_abs : |log (log (log N))| ≤ (1 / 3960000 : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge2
  have hlarge3_abs :
      |log (log (log N))| ≤ (1 / ((Real.exp 10000 + 1) * 2) : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge3
  have hlarge' : log (log (log N)) ≤ (1 / 4 : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge_abs
    exact hlarge_abs
  have hlarge2' : log (log (log N)) ≤ (1 / 3960000 : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge2_abs
    exact hlarge2_abs
  have hlarge3' : log (log (log N)) ≤ (1 / ((Real.exp 10000 + 1) * 2) : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge3_abs
    exact hlarge3_abs
  have hx_exp : Real.exp 10000 + 1 ≤ x := by
    dsimp [x]
    refine (_root_.le_div_iff₀ ?_).2 ?_
    · positivity
    have hmul : log (log (log N)) * ((Real.exp 10000 + 1) * 2) ≤ log (log N) := by
      refine (_root_.le_div_iff₀ (by positivity)).mp ?_
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlarge3'
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hhelp2 : Real.exp 10000 ≤ F := by
    change Real.exp 10000 ≤ (⌊x⌋₊ : ℝ)
    rw [natCast_floor_eq_intCast_floor hx_nonneg]
    have hfloor : x - 1 < ((⌊x⌋ : ℤ) : ℝ) := by
      exact_mod_cast (Int.sub_one_lt_floor x)
    linarith
  have hF_pos : 0 < F := lt_of_lt_of_le (Real.exp_pos 10000) hhelp2
  have hx_big : (1980000 : ℝ) ≤ x := by
    dsimp [x]
    refine (_root_.le_div_iff₀ ?_).2 ?_
    · positivity
    have hmul0 : log (log (log N)) * 3960000 ≤ log (log N) := by
      refine (_root_.le_div_iff₀ (by positivity)).mp ?_
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlarge2'
    nlinarith
  have hF_big_nat : 1980000 ≤ ⌊x⌋₊ := by
    rw [Nat.le_floor_iff hx_nonneg]
    exact hx_big
  have hF_big : (1980000 : ℝ) ≤ F := by
    change (1980000 : ℝ) ≤ (⌊x⌋₊ : ℝ)
    exact_mod_cast hF_big_nat
  refine ⟨hlogloglogN', hlogN, ?_, hlogloglogN, ?_, ?_⟩
  · nlinarith
  · change log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ (2 / F)
    have htwo_div_F : 2 / F ≤ 2 / (1980000 : ℝ) := by
      have hone_div : 1 / F ≤ 1 / (1980000 : ℝ) := by
        simpa using one_div_le_one_div_of_le (show 0 < (1980000 : ℝ) by positivity) hF_big
      have hmul := mul_le_mul_of_nonneg_left hone_div (show 0 ≤ (2 : ℝ) by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hexp : -((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F ≤ -((1 : ℝ) / 10000) := by
      nlinarith
    have hpow_small : log N ^ (-((1 : ℝ) / 10000)) ≤ C / 2 := by
      rw [Real.rpow_neg (le_of_lt h0logN_real)]
      exact (inv_le_comm₀ (Real.rpow_pos_of_pos h0logN_real _) (div_pos hC zero_lt_two)).2 hlargepow
    have hpow_mid : log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) ≤ C / 2 := by
      exact (Real.rpow_le_rpow_of_exponent_le h1logN_real hexp).trans hpow_small
    have hmain : log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
        log N ^ (2 / F) ≤ C := by
      have hmul := mul_le_mul_of_nonneg_left hpow_mid (show 0 ≤ (2 : ℝ) by positivity)
      have hrewrite :
          2 * log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
            log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
              log N ^ (2 / F) := by
        calc
          2 * log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
              2 * (log N ^ (-((2 : ℝ) / 99) / 2) *
                (log N ^ ((1 : ℝ) / 100) * log N ^ (2 / F))) := by
                  rw [show (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
                      (-((2 : ℝ) / 99) / 2) + ((1 : ℝ) / 100 + 2 / F) by ring,
                    Real.rpow_add h0logN_real, Real.rpow_add h0logN_real]
          _ = log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
                log N ^ (2 / F) := by ring
      rw [hrewrite] at hmul
      linarith
    refine (_root_.le_div_iff₀ (Real.rpow_pos_of_pos h0logN_real _)).2 ?_
    have hmain' : log N ^ (-((2 : ℝ) / 99) / 2) * log N ^ (2 / F) *
        (2 * log N ^ ((1 : ℝ) / 100)) ≤ C := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
    have hafter : log N ^ (-((2 : ℝ) / 99) / 2) * log N ^ (2 / F) ≤
        C * (2 * log N ^ ((1 : ℝ) / 100))⁻¹ := by
      exact (le_mul_inv_iff₀ (mul_pos zero_lt_two (Real.rpow_pos_of_pos h0logN_real _))).2 hmain'
    simpa [one_div] using hafter
  · change (1 - 2 / 99) * log (log N) + (1 + 5 / log F * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N)
    have hone : 1 ≤ (1 / 1000 : ℝ) * log (log N) := by
      nlinarith
    have hlogF : (10000 : ℝ) ≤ log F := by
      simpa using Real.log_le_log (Real.exp_pos 10000) hhelp2
    have hdiv : 5 / log F ≤ (5 : ℝ) / 10000 := by
      have hone_div : 1 / log F ≤ 1 / (10000 : ℝ) := by
        simpa using one_div_le_one_div_of_le (show 0 < (10000 : ℝ) by positivity) hlogF
      have hmul := mul_le_mul_of_nonneg_left hone_div (show 0 ≤ (5 : ℝ) by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      (1 - 2 / 99) * log (log N) + (1 + 5 / log F * log (log N)) ≤
          ((97 : ℝ) / 99) * log (log N) + (1 / 1000) * log (log N) + (5 / 10000) * log (log N) := by
            rw [add_assoc]
            refine add_le_add ?_ ?_
            · norm_num
            · refine add_le_add hone ?_
              exact mul_le_mul_of_nonneg_right hdiv (le_of_lt h0loglogN)
      _ ≤ (99 / 100 : ℝ) * log (log N) := by
        have hcoef : ((97 : ℝ) / 99) + 1 / 1000 + 5 / 10000 ≤ 99 / 100 := by norm_num
        simpa [left_distrib, right_distrib, add_assoc, add_left_comm, add_comm, mul_add] using
          mul_le_mul_of_nonneg_right hcoef (le_of_lt h0loglogN_real)

theorem yet_another_large_N :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) * N ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) <
        log N ^ (-((1 : ℝ) / 101)) / 6 := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 3 by norm_num))
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (log (6 * 2) / (1 - 1 / 101)))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_ge_atTop (-log (2 + -(2 * log 2) * (1 + 1 / 3))))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ))
    , ((Real.tendsto_exp_div_pow_atTop 3).comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (1 : ℝ)) ] with
    N h0N hlarge h0logN hloglogN hlogloglogN h0loglogN h0logloglogN hcube
  have hhelp : 0 < 2 + -(2 * log 2) * (1 + 1 / 3) := by
    have hlog2 : log 2 < (3 / 4 : ℝ) := by
      exact lt_trans Real.log_two_lt_d9 (by norm_num)
    nlinarith
  rw [_root_.lt_div_iff₀' (show (0 : ℝ) < 6 by norm_num), ← mul_assoc]
  apply (Real.log_lt_log_iff
    (mul_pos (mul_pos (by norm_num : 0 < (6 : ℝ)) zero_lt_two) (Real.rpow_pos_of_pos h0N _))
    (Real.rpow_pos_of_pos h0logN _)).1
  rw [Real.log_rpow h0logN,
    Real.log_mul (by norm_num : (6 : ℝ) * 2 ≠ 0) (Real.rpow_pos_of_pos h0N _).ne', neg_mul,
    lt_neg, neg_add, Real.log_rpow h0N, ← sub_eq_neg_add, lt_sub_iff_add_lt, ← neg_mul, neg_add,
    ← neg_div, neg_neg, ← neg_mul, ← neg_div]
  have hlog12 : log (6 * 2) < (1 - 1 / 101 : ℝ) * log (log N) := by
    have hcoef : 0 < (1 - 1 / 101 : ℝ) := by norm_num
    have := (_root_.div_lt_iff₀ hcoef).1 hloglogN
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hcinv : 1 / log (log N) ≤ 2 + -(2 * log 2) * (1 + 1 / 3) := by
    have hrecip : (2 + -(2 * log 2) * (1 + 1 / 3))⁻¹ ≤ log (log N) := by
      calc
        (2 + -(2 * log 2) * (1 + 1 / 3))⁻¹ = Real.exp (-log (2 + -(2 * log 2) * (1 + 1 / 3))) := by
          rw [Real.exp_neg, Real.exp_log hhelp]
        _ ≤ Real.exp (log (log (log N))) := Real.exp_le_exp.mpr hlogloglogN
        _ = log (log N) := by simpa [Function.comp] using (Real.exp_log h0loglogN)
    have hmul : 1 ≤ (2 + -(2 * log 2) * (1 + 1 / 3)) * log (log N) := by
      have := (inv_le_iff_one_le_mul₀ hhelp).1 hrecip
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have := (_root_.div_le_iff₀ h0loglogN).2 <|
      by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
  have hcube' : log (log N) < log N / (log (log N)) ^ 2 := by
    have hcube'' : (log (log N)) ^ 3 < log N := by
      have hcube0 : 1 < log N / (log (log N)) ^ 3 := by
        calc
          1 < Real.exp (log (log N)) / (log (log N)) ^ 3 := by simpa [Function.comp] using hcube
          _ = log N / (log (log N)) ^ 3 := by
            simpa [Function.comp] using
              congrArg (fun t => t / (log (log N)) ^ 3) (Real.exp_log h0logN)
      have := (_root_.lt_div_iff₀ (show 0 < (log (log N)) ^ 3 by positivity)).1 hcube0
      simpa [pow_succ, pow_two, mul_assoc] using this
    refine (_root_.lt_div_iff₀ (show 0 < (log (log N)) ^ 2 by positivity)).2 ?_
    simpa [pow_succ, pow_two, mul_assoc] using hcube''
  have hcoeff :
      2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3) =
        (2 + -(2 * log 2) * (1 + 1 / 3)) / log (log N) := by
    field_simp [h0loglogN.ne']
  have hrhs :
      log (log N) <
        (2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3)) * log N := by
    rw [hcoeff, div_eq_mul_inv, mul_assoc]
    have hmul :
        log N / (log (log N)) ^ 2 ≤
          (2 + -(2 * log 2) * (1 + 1 / 3)) * (log N * (log (log N))⁻¹) := by
      have hrewrite :
          log N / (log (log N)) ^ 2 = (1 / log (log N)) * (log N * (log (log N))⁻¹) := by
        field_simp [h0loglogN.ne']
      rw [hrewrite]
      have htmp := mul_le_mul_of_nonneg_right hcinv (by positivity : 0 ≤ log N * (log (log N))⁻¹)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
    exact lt_of_lt_of_le hcube' <|
      by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    (1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) + log (6 * 2) <
        (1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) +
          (1 - 1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) := by
      simpa [Function.comp] using add_lt_add_left hlog12 ((1 / 101 : ℝ) * log ((log ∘ Nat.cast) N))
    _ = log (log N) := by
      simp [Function.comp]
      ring
    _ < (2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3)) * log N := hrhs


end

end UnitFractions
