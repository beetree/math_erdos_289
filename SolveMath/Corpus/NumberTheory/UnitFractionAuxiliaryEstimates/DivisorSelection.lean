module

public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.ReciprocalSums
public import Mathlib.NumberTheory.Divisors

@[expose] public section

namespace UnitFractions

open Filter Finset Real
open _root_.Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

open Classical

noncomputable section

theorem find_good_d_aux2 :
    ∀ᶠ N : ℕ in atTop,
      ∀ M : ℝ,
        ∀ k : ℕ,
          ∀ A ⊆ range (N + 1),
            0 < M →
              M ≤ N →
                1 ≤ k →
                  (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k))) →
                    ∀ q ∈ ppowers_in_set A,
                      ∀ n ∈ local_part A q,
                        ∃ d ∈
                            (range (N + 1)).filter
                              (fun d : ℕ ↦
                                (∀ r : ℕ,
                                    IsPrimePow r →
                                      r ∣ d →
                                        Nat.Coprime r (d / r) →
                                          Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r ∧ r ≤ N) ∧
                                  M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < (q * d : ℝ) ∧
                                    q * d ≤ N),
                          (q * d ∣ n) ∧ Nat.Coprime (q * d) (n / (q * d)) := by
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with
    N hlargeN M k A hA hM hMN hk hAreg q hq n hn
  have hqpp : IsPrimePow q := by
    rw [mem_ppowers_in_set] at hq
    exact hq.1
  have hN : 0 < N := by
    exact lt_trans zero_lt_one hlargeN
  let Q : Finset ℕ :=
    n.divisors.filter fun r ↦
      IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
        Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r
  let d : ℕ := Q.prod id
  have memQ {r : ℕ} :
      r ∈ Q ↔
        r ∈ n.divisors ∧ IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
          Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r := by
    simp [Q]
  have hnz : n ≠ 0 := by
    intro hnz2
    rw [local_part, hnz2] at hn
    have htemp := hAreg 0 (Finset.mem_of_mem_filter 0 hn)
    exact (not_le_of_gt hM) (by exact_mod_cast htemp.1)
  have hnN : n ≤ N := by
    have hnA : n ∈ A := Finset.mem_of_mem_filter n hn
    have hnRange : n ∈ range (N + 1) := hA hnA
    exact Nat.lt_succ_iff.mp (by simpa [Finset.mem_range] using hnRange)
  have hQcoprime :
      ∀ a ∈ n.divisors.filter (fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)),
        ∀ b ∈ n.divisors.filter (fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)),
          a ≠ b → Nat.Coprime a b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    by_contra h
    rw [prime_pow_not_coprime_iff ha.2.1 hb.2.1] at h
    rcases h with ⟨p, ka, kb, hp, hka, hkb, hpa, hpb⟩
    apply hab
    rw [← hpa, ← hpb]
    refine congrArg (fun t : ℕ => p ^ t) ?_
    calc
      ka = n.factorization p := by
        apply coprime_div_iff hp
        · rw [hpa]
          exact Nat.dvd_of_mem_divisors ha.1
        · exact hka
        · rw [hpa]
          exact ha.2.2
      _ = kb := by
        refine Eq.symm ?_
        apply coprime_div_iff hp
        · rw [hpb]
          exact Nat.dvd_of_mem_divisors hb.1
        · exact hkb
        · rw [hpb]
          exact hb.2.2
  have hqmem : q ∈ n.divisors.filter (fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)) := by
    rw [local_part, Finset.mem_filter] at hn
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hn.2.1, hnz⟩, hqpp, hn.2.2⟩
  have hqdcop : Nat.Coprime q d := by
    rw [Nat.coprime_prod_right_iff]
    intro i hi
    exact hQcoprime q hqmem i
      (Finset.mem_filter.mpr ⟨(memQ.mp hi).1, (memQ.mp hi).2.1, (memQ.mp hi).2.2.1⟩)
      ((memQ.mp hi).2.2.2.1).symm
  have hqd : q * d ∣ n := by
    rw [dvd_iff_ppowers_dvd]
    intro r hr1 hr2
    rcases (hqdcop.isPrimePow_dvd_mul hr2).mp hr1 with hrq | hrd
    · rw [local_part, Finset.mem_filter] at hn
      exact dvd_trans hrq hn.2.1
    · rw [is_prime_pow_dvd_prod ?_ hr2] at hrd
      · rcases hrd with ⟨t, ht, hrt⟩
        exact dvd_trans hrt (Nat.dvd_of_mem_divisors (memQ.mp ht).1)
      · intro a ha b hb hab
        refine hQcoprime _ ?_ _ ?_ hab
        · exact Finset.mem_filter.mpr ⟨(memQ.mp ha).1, (memQ.mp ha).2.1, (memQ.mp ha).2.2.1⟩
        · exact Finset.mem_filter.mpr ⟨(memQ.mp hb).1, (memQ.mp hb).2.1, (memQ.mp hb).2.2.1⟩
  have hdupp : q * d ≤ N := by
    refine le_trans (Nat.le_of_dvd ?_ hqd) hnN
    have : (0 : ℝ) < n := by
      refine lt_of_lt_of_le hM ?_
      exact (hAreg n (Finset.mem_of_mem_filter n hn)).1
    exact_mod_cast this
  let Q' : Finset ℕ :=
    n.divisors.filter fun r ↦
      IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
        (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))
  have memQ' {r : ℕ} :
      r ∈ Q' ↔
        r ∈ n.divisors ∧ IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
          (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k)) := by
    simp [Q']
  have hQ'dcop : Nat.Coprime q (Q'.prod id) := by
    rw [Nat.coprime_prod_right_iff]
    intro i hi
    exact hQcoprime q hqmem i
      (Finset.mem_filter.mpr ⟨(memQ'.mp hi).1, (memQ'.mp hi).2.1, (memQ'.mp hi).2.2.1⟩)
      ((memQ'.mp hi).2.2.2.1).symm
  have hQ'qd : Nat.Coprime (q * d) (Q'.prod id) := by
    apply Nat.Coprime.symm
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.symm hQ'dcop
    · rw [Nat.coprime_prod_left_iff]
      have hd : d = Q.prod id := rfl
      simp_rw [hd, Nat.coprime_prod_right_iff, id]
      intro a ha b hb
      refine hQcoprime _ ?_ _ ?_ ?_
      · exact Finset.mem_filter.mpr ⟨(memQ'.mp ha).1, (memQ'.mp ha).2.1, (memQ'.mp ha).2.2.1⟩
      · exact Finset.mem_filter.mpr ⟨(memQ.mp hb).1, (memQ.mp hb).2.1, (memQ.mp hb).2.2.1⟩
      · intro hab
        have ha' := memQ'.mp ha
        have hb' := memQ.mp hb
        rw [hab] at ha'
        have hbnge : ¬ ((b : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))) := by
          exact (lt_iff_not_ge).mp hb'.2.2.2.2
        exact hbnge ha'.2.2.2.2
  have hnqd : n = (Q'.prod id) * q * d := by
    rw [eq_iff_ppowers_dvd n ((Q'.prod id) * q * d) hnz ?_]
    · constructor
      · intro r hr1 hr2 hr3
        by_cases hrq : r = q
        · rw [mul_assoc, hrq]
          exact dvd_trans (dvd_mul_right q d) <|
            dvd_mul_of_dvd_right (dvd_refl (q * d)) (Q'.prod id)
        · by_cases hrsize : (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))
          · have hrmem : r ∈ Q' := by
              exact memQ'.mpr
                ⟨by simpa [Nat.mem_divisors] using And.intro hr1 hnz, hr2, hr3, hrq, hrsize⟩
            exact dvd_trans (Finset.dvd_prod_of_mem id hrmem) <|
              dvd_mul_of_dvd_left (dvd_mul_right (Q'.prod id) q) d
          · have hrmem : r ∈ Q := by
              rw [← lt_iff_not_ge] at hrsize
              exact memQ.mpr
                ⟨by simpa [Nat.mem_divisors] using And.intro hr1 hnz, hr2, hr3, hrq, hrsize⟩
            have hrd' : r ∣ q * d := by
              have : r ∣ Q.prod id := Finset.dvd_prod_of_mem id hrmem
              simpa [d, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                dvd_trans this (dvd_mul_right (Q.prod id) q)
            exact dvd_trans hrd' <| by
              simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
                dvd_mul_right (q * d) (Q'.prod id)
      · intro r hr1 hr2 hr3
        have hr1' : r ∣ (Q'.prod id) * (q * d) := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hr1
        rcases (Nat.Coprime.symm hQ'qd).isPrimePow_dvd_mul hr2 |>.mp hr1' with hw1 | hw2
        · rw [is_prime_pow_dvd_prod ?_ hr2] at hw1
          · rcases hw1 with ⟨t, ht, hwt⟩
            exact dvd_trans hwt (Nat.dvd_of_mem_divisors (memQ'.mp ht).1)
          · intro a ha b hb hab
            refine hQcoprime _ ?_ _ ?_ hab
            · exact Finset.mem_filter.mpr ⟨(memQ'.mp ha).1, (memQ'.mp ha).2.1, (memQ'.mp ha).2.2.1⟩
            · exact Finset.mem_filter.mpr ⟨(memQ'.mp hb).1, (memQ'.mp hb).2.1, (memQ'.mp hb).2.2.1⟩
        · rcases (hqdcop.isPrimePow_dvd_mul hr2).mp hw2 with hw3 | hw4
          · rw [local_part, Finset.mem_filter] at hn
            exact dvd_trans hw3 hn.2.1
          · exact dvd_trans hw4 (dvd_trans (dvd_mul_left _ _) hqd)
    · have hQ'ne : Q'.prod id ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro r hr
        exact Nat.ne_of_gt <| Nat.succ_le_iff.mp (memQ'.mp hr).2.1.pos
      have hqd0 : q * d ≠ 0 := by
        intro hbad
        apply hnz
        rw [hbad, zero_dvd_iff] at hqd
        exact hqd
      simpa [Nat.mul_assoc] using Nat.mul_ne_zero hQ'ne hqd0
  refine ⟨d, ?_, hqd, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      refine le_trans ?_ hdupp
      exact Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero <| by
        intro h
        rw [h] at hq
        exact zero_not_mem_ppowers_in_set hq)
    · refine ⟨?_, ?_, hdupp⟩
      · intro r hr1 hr2 hr3
        have hrQ : r ∈ Q := by
          refine prime_pow_dvd_prod_prime_pow hr1 ?_ ?_ hr2 hr3
          · intro a ha b hb hab
            by_contra h
            have ha' := memQ.mp ha
            have hb' := memQ.mp hb
            have h' := (prime_pow_not_coprime_iff ha'.2.1 hb'.2.1).mp h
            rcases h' with ⟨p, k, l, hp, hk, hl, hpa, hpb⟩
            have hafac : n.factorization p = k := by
              rw [← factorization_eq_iff hp hk, hpa]
              exact ⟨Nat.dvd_of_mem_divisors ha'.1, ha'.2.2.1⟩
            have hbfac : n.factorization p = l := by
              rw [← factorization_eq_iff hp hl, hpb]
              exact ⟨Nat.dvd_of_mem_divisors hb'.1, hb'.2.2.1⟩
            apply hab
            rw [← hpa, ← hpb, ← hafac, ← hbfac]
          · intro t ht
            exact (memQ.mp ht).2.1
        refine ⟨(memQ.mp hrQ).2.2.2.2, ?_⟩
        exact le_trans (Nat.divisor_le (memQ.mp hrQ).1) hnN
      · have hstep :
            M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) ≤
              (n : ℝ) * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
            exact mul_le_mul_of_nonneg_right
              ((hAreg n (Finset.mem_of_mem_filter n hn)).1) (le_of_lt (Real.exp_pos _))
        have hstep' : (n : ℝ) * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < (q : ℝ) * d := by
          rw [hnqd]
          push_cast
          rw [← Nat.cast_prod]
          have hmul :
              ((((Q'.prod id : ℕ) : ℝ) * (q : ℝ) * (d : ℝ)) *
                Real.exp (-log N ^ ((1 : ℝ) - 1 / k))) =
                ((((Q'.prod id : ℕ) : ℝ) *
                Real.exp (-log N ^ ((1 : ℝ) - 1 / k))) * ((q : ℝ) * d)) := by
            ring
          rw [hmul]
          have hqd0' : q * d ≠ 0 := by
            intro hzero
            rw [hzero, zero_dvd_iff] at hqd
            exact hnz hqd
          have hqdpos : 0 < (q : ℝ) * d := by
            exact_mod_cast Nat.pos_of_ne_zero hqd0'
          rw [mul_comm]
          apply mul_lt_of_lt_one_right hqdpos
          · rw [exp_neg, ← one_div, mul_one_div, div_lt_one]
            · calc
              (((Q'.prod id : ℕ) : ℝ)) = Q'.prod (fun i ↦ (i : ℝ)) := by
                simp
              _ ≤ (Real.exp (log N ^ ((1 : ℝ) - 2 / k))) ^ Q'.card := by
                calc
                  Q'.prod (fun i ↦ (i : ℝ)) ≤
                      Q'.prod (fun _ ↦ Real.exp (log N ^ ((1 : ℝ) - 2 / k))) :=
                    Finset.prod_le_prod (fun i _ ↦ Nat.cast_nonneg i)
                      (fun i hi ↦ (memQ'.mp hi).2.2.2.2)
                  _ = (Real.exp (log N ^ ((1 : ℝ) - 2 / k))) ^ Q'.card := by simp
              _ < (Real.exp (log N ^ ((1 : ℝ) - 2 / k))) ^ (log N ^ ((1 : ℝ) / k)) := by
                rw [← Real.rpow_natCast]
                apply Real.rpow_lt_rpow_of_exponent_lt
                · rw [one_lt_exp_iff]
                  apply Real.rpow_pos_of_pos
                  exact Real.log_pos (by exact_mod_cast hlargeN)
                · calc
                    (Q'.card : ℝ) ≤
                        (n.divisors.filter fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card := by
                          have hsubset : Q' ⊆ n.divisors.filter fun r ↦
                              IsPrimePow r ∧ Nat.Coprime r (n / r) := by
                            intro r hr
                            exact Finset.mem_filter.mpr
                              ⟨(memQ'.mp hr).1, (memQ'.mp hr).2.1, (memQ'.mp hr).2.2.1⟩
                          exact_mod_cast Finset.card_le_card hsubset
                    _ = (ω n : ℝ) := by
                      norm_num [omega_count_eq_ppowers]
                    _ < log N ^ ((1 : ℝ) / k) := by
                      rw [local_part] at hn
                      exact (hAreg n (Finset.mem_of_mem_filter n hn)).2
              _ = Real.exp (log N ^ ((1 : ℝ) - 1 / k)) := by
                rw [← Real.exp_mul, ← Real.rpow_add]
                · ring_nf
                exact Real.log_pos (by exact_mod_cast hlargeN)
            exact Real.exp_pos _
        exact lt_of_le_of_lt hstep hstep'
  · have hqd0 : q * d ≠ 0 := by
      intro hzero
      rw [hzero, zero_dvd_iff] at hqd
      exact hnz hqd
    have hquot : n / (q * d) = Q'.prod id := by
      rw [hnqd, Nat.mul_assoc]
      rw [Nat.mul_comm (Q'.prod id) (q * d)]
      exact Nat.mul_div_right (Q'.prod id) (Nat.pos_of_ne_zero hqd0)
    simpa [hquot] using hQ'qd

theorem find_good_d_hlarge2 {N : ℕ} (hlarge1 : 0 < log N) (hlarge'' : (16 : ℝ) ≤ log N) :
    4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1 := by
  have hsqrt : (4 : ℝ) ≤ log N ^ ((1 : ℝ) / 2) := by
    have hsqrt' : Real.sqrt (16 : ℝ) ≤ Real.sqrt (log N) := Real.sqrt_le_sqrt hlarge''
    norm_num [Real.sqrt_eq_rpow] at hsqrt' ⊢
    exact hsqrt'
  have hpowpos : 0 < log N ^ ((1 : ℝ) / 2) := by
    positivity
  have hlog0 : 0 ≤ log N := le_of_lt hlarge1
  calc
    4 * log N ^ (-((3 : ℝ) / 2) + 1) = 4 / log N ^ ((1 : ℝ) / 2) := by
      rw [show -((3 : ℝ) / 2) + 1 = -((1 : ℝ) / 2) by ring]
      rw [Real.rpow_neg hlog0, ← one_div]
      ring
    _ ≤ 1 := by
      exact (div_le_iff₀ hpowpos).2 (by simpa using hsqrt)

theorem find_good_d_hyN {N k : ℕ} (hlarge : 1 < log N) (hlarge' : 0 < N) (h1k : 1 < k) :
    Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < N := by
  have hexp : log N ^ ((1 : ℝ) - 2 / k) < log N ^ (1 : ℝ) := by
    refine Real.rpow_lt_rpow_of_exponent_lt hlarge ?_
    refine sub_lt_self 1 ?_
    refine div_pos zero_lt_two ?_
    exact_mod_cast (lt_trans zero_lt_one h1k)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hlarge'
  calc
    Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < Real.exp (log N) := by
      simpa using Real.exp_lt_exp.mpr hexp
    _ = N := by rw [Real.exp_log hNpos]

theorem find_good_d_hlocal2 {A : Finset ℕ} {q : ℕ} (D : Finset ℕ)
    (newLocal : ℕ → Finset ℕ)
    (hnewLocal :
      newLocal =
        fun d : ℕ ↦
          (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))))
    (haux2 : ∀ n ∈ local_part A q, ∃ d ∈ D, q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))) :
    local_part A q ⊆ D.biUnion newLocal := by
  subst newLocal
  intro n hn
  rw [Finset.mem_biUnion]
  rcases haux2 n hn with ⟨d, hd, hlocal⟩
  refine ⟨d, hd, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨hn, hlocal⟩

theorem find_good_d_hrecbound {A : Finset ℕ} {q : ℕ} (D : Finset ℕ)
    (newLocal : ℕ → Finset ℕ)
    (hnewLocal :
      newLocal =
        fun d : ℕ ↦
          (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))))
    (hlocal2 : local_part A q ⊆ D.biUnion newLocal) :
    rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
  subst newLocal
  rw [rec_sum_local]
  let s :=
    D.biUnion fun d ↦
      (local_part A q).filter fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))
  have h1 : (local_part A q).sum (fun n ↦ (q : ℚ) / n) ≤ s.sum (fun n ↦ (q : ℚ) / n) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hlocal2 (by
      intro i _ _
      positivity)
  have h2 :
      s.sum (fun n ↦ (q : ℚ) / n) ≤
        D.sum (fun d ↦
          ((local_part A q).filter fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))).sum
            (fun n ↦ (q : ℚ) / n)) := by
    dsimp [s]
    refine sum_bUnion_le_sum_of_nonneg ?_
    intro i _
    positivity
  exact le_trans h1 h2

theorem find_good_d_hDnotzero {M u : ℝ} {q : ℕ} {D : Finset ℕ}
    (hzM : 0 < M) (hu : 0 < u) (hDu : ∀ d ∈ D, M * u < q * d) :
    ∀ d ∈ D, d ≠ 0 := fun d hd hd0 =>
  absurd (by simpa [hd0] using hDu d hd) (not_lt.mpr (mul_pos hzM hu).le)

theorem find_good_d_hbound1 {C1 c y ω0 : ℝ} {N q k : ℕ} {A D1 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hC1 : 0 < C1) (hc : c = (1 / 2 : ℝ) / Real.log (max C1 2))
    (hy : y = Real.exp (log N ^ ((1 : ℝ) - 2 / k)))
    (hkN : (k : ℝ) ≤ c * log (log N)) (hlarge1 : 0 < log N)
    (hlarge2 : 4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1) (h1k : 1 < k) (h0k : (0 : ℝ) < k)
    (hω0 : ω0 = (5 / log k) * log (log N)) (hsumq : 1 / log N ≤ rec_sum_local A q)
    (hωD1 : ∀ d ∈ D1, ω0 ≤ (ω d : ℝ))
    (haux1 : ∀ d ∈ D1, (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤ 2 * log N / d)
    (hrec1bound : D1.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C1 * |log N| / |log y|) ^ k) :
    ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
      (rec_sum_local A q : ℝ) / 2 := by
  let C2 : ℝ := max C1 2
  have hC2 : 1 < C2 := lt_of_lt_of_le one_lt_two (le_max_right C1 2)
  have h1y : 1 < y := by
    rw [hy, Real.one_lt_exp_iff]
    exact Real.rpow_pos_of_pos hlarge1 _
  have hfac_nonneg : 0 ≤ 2 * log N := by positivity
  have hkpow_nonneg : 0 ≤ (k : ℝ) ^ (-ω0) := le_of_lt (Real.rpow_pos_of_pos h0k _)
  calc
    ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ)
        = D1.sum (fun d ↦ (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) := by
          rw [Rat.cast_sum]
    _ ≤ D1.sum (fun d ↦ 2 * log N / d) := by
          refine Finset.sum_le_sum ?_
          intro d hd
          exact haux1 d hd
    _ = 2 * log N * D1.sum (fun d ↦ (1 : ℝ) / d) := by
      rw [mul_sum]
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [div_eq_mul_one_div]
    _ ≤ 2 * log N * D1.sum (fun d ↦ (k : ℝ) ^ (-ω0) * (((k : ℝ) ^ ω d) / d)) := by
      apply mul_le_mul_of_nonneg_left
      · refine Finset.sum_le_sum ?_
        intro d hd
        have hkge : 1 ≤ (k : ℝ) ^ (-ω0) * (k : ℝ) ^ ω d := by
          rw [← Real.rpow_natCast, ← Real.rpow_add]
          · apply one_le_rpow
            · exact_mod_cast (le_of_lt h1k)
            · linarith [hωD1 d hd]
          · exact h0k
        calc
          (1 : ℝ) / d = 1 * (1 / d) := by ring
          _ ≤ ((k : ℝ) ^ (-ω0) * (k : ℝ) ^ ω d) * (1 / d) := by
            exact mul_le_mul_of_nonneg_right hkge (by
              rw [one_div_nonneg]
              exact_mod_cast Nat.cast_nonneg d)
          _ = (k : ℝ) ^ (-ω0) * (((k : ℝ) ^ ω d) / d) := by
            rw [div_eq_mul_one_div]
            ring
      · exact hfac_nonneg
    _ = 2 * log N * (k : ℝ) ^ (-ω0) * D1.sum (fun d ↦ ((k : ℝ) ^ ω d / d)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * log N * (k : ℝ) ^ (-ω0) * (C1 * |log N| / |log y|) ^ k := by
      exact mul_le_mul_of_nonneg_left hrec1bound (mul_nonneg hfac_nonneg hkpow_nonneg)
    _ = 2 * (log N ^ (-2 : ℝ)) * C1 ^ k := by
      have hkpow :
          (k : ℝ) ^ (-ω0) = log N ^ (-5 : ℝ) := by
        have hlogk : 0 < Real.log k := by
          exact Real.log_pos (by exact_mod_cast h1k)
        calc
          (k : ℝ) ^ (-ω0) = Real.exp (Real.log k * (-ω0)) := by
            rw [Real.rpow_def_of_pos h0k]
          _ = Real.exp (-5 * log (log N)) := by
            rw [hω0]
            field_simp [ne_of_gt hlogk]
          _ = Real.exp (log (log N) * (-5 : ℝ)) := by ring_nf
          _ = (Real.exp (log (log N))) ^ (-5 : ℝ) := by rw [Real.exp_mul]
          _ = log N ^ (-5 : ℝ) := by rw [Real.exp_log hlarge1]
      have hyabs : |log y| = log N ^ ((1 : ℝ) - 2 / k) := by
        rw [hy, Real.log_exp, abs_eq_self.mpr]
        exact le_of_lt (Real.rpow_pos_of_pos hlarge1 _)
      have hquot : log N / log N ^ ((1 : ℝ) - (2 : ℝ) / k) = log N ^ ((2 : ℝ) / k) := by
        nth_rewrite 1 [← Real.rpow_one (log N)]
        rw [← Real.rpow_sub hlarge1 (1 : ℝ) ((1 : ℝ) - (2 : ℝ) / k)]
        have hEq : (1 : ℝ) - ((1 : ℝ) - (2 : ℝ) / k) = (2 : ℝ) / k := by
          field_simp [ne_of_gt h0k]
          ring
        rw [hEq]
      have hpowLog : (log N ^ (((2 : ℝ) / k))) ^ k = log N ^ (2 : ℝ) := by
        have hk2 : (((2 : ℝ) / k)) * k = 2 := by
          field_simp [ne_of_gt h0k]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hlarge1.le, hk2]
      have hpowFinal : log N * log N ^ (-5 : ℝ) * log N ^ (2 : ℝ) = log N ^ (-2 : ℝ) := by
        nth_rewrite 1 [← Real.rpow_one (log N)]
        rw [← Real.rpow_add hlarge1, ← Real.rpow_add hlarge1]
        norm_num
      rw [hkpow, abs_eq_self.mpr hlarge1.le, hyabs, mul_div_assoc, hquot, mul_pow]
      change
        2 * log N * log N ^ (-5 : ℝ) * (C1 ^ k * (log N ^ (((2 : ℝ) / k))) ^ k) =
          2 * log N ^ (-2 : ℝ) * C1 ^ k
      rw [hpowLog]
      calc
        2 * log N * log N ^ (-5 : ℝ) * (C1 ^ k * log N ^ (2 : ℝ))
            = 2 * (log N * log N ^ (-5 : ℝ) * log N ^ (2 : ℝ)) * C1 ^ k := by
              ring
        _ = 2 * (log N ^ (-2 : ℝ)) * C1 ^ k := by rw [hpowFinal]
    _ ≤ 2 * (log N ^ (-2 : ℝ)) * C2 ^ k := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (le_of_lt hC1) (le_max_left C1 2) _
      · positivity
    _ ≤ 2 * (log N ^ (-2 : ℝ)) * (log N ^ (Real.log C2 * c)) := by
      apply mul_le_mul_of_nonneg_left
      · rw [← Real.rpow_natCast]
        refine (Real.le_rpow_iff_log_le
          (Real.rpow_pos_of_pos (show 0 < C2 by linarith) _) hlarge1).2 ?_
        rw [Real.log_rpow (show 0 < C2 by linarith), mul_comm (k : ℝ), mul_assoc]
        exact mul_le_mul_of_nonneg_left hkN (Real.log_pos hC2).le
      · positivity
    _ = 2 * (log N ^ (-(3 / 2 : ℝ))) := by
      rw [hc, show Real.log C2 = Real.log (max C1 2) by rfl]
      rw [mul_assoc, ← Real.rpow_add hlarge1]
      have hlogne : Real.log (max C1 2) ≠ 0 := ne_of_gt (Real.log_pos hC2)
      congr 1
      field_simp [hlogne]
      ring_nf
    _ ≤ (1 / log N) / 2 := by
      rw [le_div_iff₀ zero_lt_two, le_div_iff₀ hlarge1]
      calc
        2 * log N ^ (-(3 / 2 : ℝ)) * 2 * log N
            = 4 * log N ^ (-((3 : ℝ) / 2) + 1) := by
              rw [show (2 : ℝ) * log N ^ (-(3 / 2 : ℝ)) * 2 * log N =
                4 * (log N ^ (-(3 / 2 : ℝ)) * log N) by ring]
              nth_rewrite 2 [show (log N : ℝ) = log N ^ (1 : ℝ) by rw [Real.rpow_one]]
              rw [← Real.rpow_add hlarge1]
        _ ≤ 1 := hlarge2
    _ ≤ ((rec_sum_local A q : ℝ) / 2) := by
      have hhalf :
          (1 / log N) * (1 / 2 : ℝ) ≤ (rec_sum_local A q : ℝ) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hsumq (show (0 : ℝ) ≤ 1 / 2 by positivity)
      calc
        (1 / log N) / 2 = (1 / log N) * (1 / 2 : ℝ) := by ring
        _ ≤ (rec_sum_local A q : ℝ) * (1 / 2 : ℝ) := hhalf
        _ = (rec_sum_local A q : ℝ) / 2 := by ring

theorem find_good_d_hbound2 {ω0 : ℝ} {A : Finset ℕ} {q : ℕ} {D D1 D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hD1 : D1 = D.filter (fun d ↦ ω0 ≤ (ω d : ℝ)))
    (hD2 : D2 = D.filter (fun d ↦ (ω d : ℝ) < ω0))
    (hrecbound : rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)))
    (hbound1 :
      ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
        (rec_sum_local A q : ℝ) / 2) :
    (rec_sum_local A q : ℚ) / 2 ≤
      D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
  have hDD : D = D1 ∪ D2 := by
    rw [hD1, hD2]
    simpa [not_le] using (Finset.filter_union_filter_not_eq (fun d ↦ ω0 ≤ (ω d : ℝ)) D).symm
  have hdisj : Disjoint D1 D2 := by
    rw [hD1, hD2]
    simpa [not_le] using Finset.disjoint_filter_filter_not D D (fun d ↦ ω0 ≤ (ω d : ℝ))
  have hsum :
      D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) =
        D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) +
          D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
    rw [hDD, Finset.sum_union hdisj]
  have hbound1' :
      (D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) ≤ rec_sum_local A q / 2 := by
    exact_mod_cast hbound1
  linarith [hrecbound, hsum, hbound1']

theorem find_good_d_hbound3 {A : Finset ℕ} {q : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hbound2 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)))
    (hDnotzero : ∀ d ∈ D2, d ≠ 0) :
    (rec_sum_local A q : ℚ) / 2 ≤
      D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) := by
  apply le_trans hbound2
  refine Finset.sum_le_sum ?_
  intro d hd
  rw [mul_sum]
  refine Finset.sum_le_sum ?_
  intro n hn
  apply le_of_eq
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast hDnotzero d hd
  field_simp [hd0]

theorem find_good_d_hbound4 {C1 C : ℝ} {N k : ℕ} {y : ℝ} {D2 : Finset ℕ}
    (hC' : C1 = 1 / (C * 2)) (hy : y = Real.exp (log N ^ ((1 : ℝ) - 2 / k)))
    (hlarge1 : 0 < log N)
    (hrec2bound :
      D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) ≤ (C1 * |log N| / |log y|) ^ 1) :
    D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2) := by
  calc
    D2.sum (fun d ↦ (1 / d : ℝ)) = D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp
    _ ≤ (C1 * |log N| / |log y|) ^ 1 := hrec2bound
    _ = C1 * log N ^ ((2 : ℝ) / k) := by
      have hy1 : 1 < y := by
        rw [hy, Real.one_lt_exp_iff]
        exact Real.rpow_pos_of_pos hlarge1 _
      rw [pow_one, abs_eq_self.mpr (le_of_lt hlarge1),
        abs_eq_self.mpr (le_of_lt (Real.log_pos hy1)),
        hy, Real.log_exp]
      rw [mul_div_assoc]
      have hdiv :
          log N / log N ^ ((1 : ℝ) - 2 / k) = (log N ^ (1 : ℝ)) ^ ((2 : ℝ) / k) := by
        calc
          log N / log N ^ ((1 : ℝ) - 2 / k)
              = log N ^ (1 : ℝ) / log N ^ ((1 : ℝ) - 2 / k) := by rw [Real.rpow_one]
          _ = log N ^ ((1 : ℝ) - ((1 : ℝ) - 2 / k)) := by rw [← Real.rpow_sub hlarge1]
          _ = log N ^ ((2 : ℝ) / k) := by ring_nf
          _ = (log N ^ (1 : ℝ)) ^ ((2 : ℝ) / k) := by
            rw [← Real.rpow_mul (le_of_lt hlarge1)]
            ring_nf
      simpa [Real.rpow_one] using congrArg (fun t => C1 * t) hdiv
    _ = log N ^ ((2 : ℝ) / k) / (C * 2) := by
      rw [mul_comm C1, ← mul_one_div, hC']
      ring


end

end UnitFractions
