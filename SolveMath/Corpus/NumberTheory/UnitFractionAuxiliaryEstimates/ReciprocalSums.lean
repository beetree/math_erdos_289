module

public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.LargeN
public import SolveMath.Corpus.NumberTheory.ReciprocalComparison
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

namespace UnitFractions

open Filter Finset Real
open _root_.Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

noncomputable section

theorem useful_rec_aux1 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ N k : ℕ,
          1 ≤ k →
            ((range (N + 1)).filter Nat.Prime).prod
                (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) ≤
              C ^ k := by
  have haux :
      ∃ C : ℝ,
        0 < C ∧
          ∀ N : ℕ,
            ((range (N + 1)).filter Nat.Prime).prod
                (fun p ↦ ((1 : ℝ) + 1 / (p * (p - 1)))) ≤ C := by
    have ht : ∀ n : ℕ,
        log (1 + 1 / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 2 * (1 / (n : ℝ) ^ (2 : ℝ)) := by
      intro n
      by_cases h0 : n = 0
      · subst h0
        simp [zero_pow]
      by_cases h1 : n = 1
      · subst h1
        simp
      have h2 : 2 ≤ n := by omega
      have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_trans zero_lt_one h2)
      have hn1_pos : 0 < (n : ℝ) - 1 := by
        have hn_gt : (1 : ℝ) < n := by
          exact_mod_cast (lt_of_lt_of_le one_lt_two h2)
        linarith
      have hlog :
          log (1 + 1 / ((n : ℝ) * ((n : ℝ) - 1))) ≤
            1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
        have hpos : 0 < 1 + 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
          exact add_pos zero_lt_one (one_div_pos.2 (mul_pos hn_pos hn1_pos))
        simpa using (Real.log_le_sub_one_of_pos hpos)
      have hdiv : 1 / ((n : ℝ) - 1) ≤ 2 / (n : ℝ) := by
        apply one_div_sub_one_of_two_le
        exact_mod_cast h2
      have h_inv :
          1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 * (1 / (n : ℝ) ^ (2 : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hdiv (one_div_nonneg.2 hn_pos.le)
        simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
      exact hlog.trans h_inv
    have hsummable :
        Summable (fun n : ℕ => (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))) := by
      exact (summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 2)).mul_left 2
    refine ⟨Real.exp (∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))), Real.exp_pos _, ?_⟩
    intro N
    let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
    have hs_log :
        log (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ≤
          ∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ)) := by
      rw [Real.log_prod]
      · refine le_trans (Finset.sum_le_sum fun i hi ↦ ht i) ?_
        exact hsummable.sum_le_tsum s (fun _ _ ↦ by positivity)
      · intro i hi
        have hip := (Finset.mem_filter.mp hi).2
        have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
          have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
          have hi1_pos : 0 < (i : ℝ) - 1 := by
            have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
            linarith
          exact mul_pos hi_pos hi1_pos
        have hpos : 0 < (1 : ℝ) + 1 / ((i : ℝ) * ((i : ℝ) - 1)) := by
          exact add_pos zero_lt_one (one_div_pos.2 hden)
        exact hpos.ne'
    have hs_pos : 0 < s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
      apply Finset.prod_pos
      intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      exact add_pos zero_lt_one (one_div_pos.2 hden)
    have hexp :
        Real.exp (log (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))))) ≤
          Real.exp (∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))) := by
      exact Real.exp_le_exp.mpr hs_log
    rw [Real.exp_log hs_pos] at hexp
    simpa [s] using hexp
  rcases haux with ⟨C, hC, hN⟩
  refine ⟨C, hC, ?_⟩
  intro N k hk
  let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
  change s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ C ^ k
  have hprod :
      s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ^ k)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Nat.le_of_lt hip.one_lt)
        linarith
      have hden_nonneg : 0 ≤ (i : ℝ) * ((i : ℝ) - 1) := by
        exact mul_nonneg (by exact_mod_cast Nat.zero_le i) hi1_nonneg
      exact add_nonneg zero_le_one (div_nonneg (by exact_mod_cast Nat.zero_le k) hden_nonneg)
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hden_pos : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      have hden_nonneg : 0 ≤ (1 : ℝ) / ((i : ℝ) * ((i : ℝ) - 1)) := by
        exact one_div_nonneg.2 hden_pos.le
      have hstep :=
        one_add_mul_le_pow (by linarith) k (a := (1 : ℝ) / ((i : ℝ) * ((i : ℝ) - 1)))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  have hs_nonneg : 0 ≤ s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
    exact le_of_lt <| Finset.prod_pos fun i hi ↦ by
      have hip := (Finset.mem_filter.mp hi).2
      have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      exact add_pos zero_lt_one (one_div_pos.2 hden)
  have hN' : s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ C := by
    simpa [s] using hN N
  have hpow : (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ^ k ≤ C ^ k := by
    exact pow_le_pow_left₀ hs_nonneg hN' k
  calc
    s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ^ k)) := hprod
    _ = (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ^ k := by
      simpa using (Finset.prod_pow s k (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))))
    _ ≤ C ^ k := hpow

theorem useful_rec_aux3 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ N : ℕ,
            1 < y →
              y < N →
                ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
                    (fun p ↦ ((1 : ℝ) + 1 / (p - 1))) ≤
                  C * |log N| / |log y| := by
  rcases weak_mertens_third_upper_all with ⟨u, hu, hupp⟩
  rcases weak_mertens_third_lower_all with ⟨l, hl, hlow⟩
  refine ⟨u / l, div_pos hu hl, ?_⟩
  intro y N hy hyN
  let f : ℕ → ℝ := fun p ↦ (1 + 1 / (p - 1) : ℝ)
  let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
  let t : Finset ℕ := (range (N + 1)).filter fun n ↦ Nat.Prime n ∧ (n : ℝ) ≤ y
  let u' : Finset ℕ := (range (N + 1)).filter fun n ↦ Nat.Prime n ∧ y < n
  let fy : Finset ℕ := (Icc 1 ⌊y⌋₊).filter Nat.Prime
  have hf_eq : ∀ p : ℕ, Nat.Prime p → f p = (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    calc
      f p = |(1 - (p : ℝ)⁻¹)⁻¹| := useful_identity p hp1
      _ = (1 - (p : ℝ)⁻¹)⁻¹ := by
        refine abs_of_nonneg ?_
        exact (inv_pos.mpr (sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1))).le
  have hs_eq : s.prod f = partial_euler_product N := by
    rw [partial_euler_product]
    have hs' : s = (Icc 1 N).filter Nat.Prime := by
      ext n
      change n ∈ (range (N + 1)).filter Nat.Prime ↔ n ∈ (Icc 1 N).filter Nat.Prime
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨hn, hp⟩
        exact ⟨⟨hp.one_lt.le, Nat.lt_succ_iff.mp hn⟩, hp⟩
      · rintro ⟨⟨_, hn⟩, hp⟩
        exact ⟨Nat.lt_succ_of_le hn, hp⟩
    rw [hs']
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hf_eq p (Finset.mem_filter.mp hp).2
  have hfy_eq : fy.prod f = partial_euler_product ⌊y⌋₊ := by
    rw [partial_euler_product]
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hf_eq p (Finset.mem_filter.mp hp).2
  have ht_subset : t ⊆ s := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnr, hnp⟩
    exact Finset.mem_filter.mpr ⟨hnr, hnp.1⟩
  have hsdiff : s \ t = u' := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_sdiff.mp hn with ⟨hsn, hnt⟩
      rcases Finset.mem_filter.mp hsn with ⟨hnr, hnp⟩
      refine Finset.mem_filter.mpr ⟨hnr, hnp, ?_⟩
      by_contra hny
      exact hnt <| Finset.mem_filter.mpr ⟨hnr, ⟨hnp, le_of_not_gt hny⟩⟩
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnr, hnp, hny⟩
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hnr, hnp⟩, ?_⟩
      intro hnt
      exact not_lt_of_ge (Finset.mem_filter.mp hnt).2.2 hny
  have hfy_subset : fy ⊆ t := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxprime⟩
    rcases Finset.mem_Icc.mp hxIcc with ⟨hx1, hx2⟩
    have hxy : (x : ℝ) ≤ y := by
      rw [← Nat.le_floor_iff]
      · exact hx2
      · exact le_trans zero_le_one (le_of_lt hy)
    have hxN : x ≤ N := by
      exact_mod_cast le_trans hxy (le_of_lt hyN)
    refine Finset.mem_filter.mpr ?_
    exact ⟨by simpa [Finset.mem_range, Nat.lt_succ_iff] using hxN, ⟨hxprime, hxy⟩⟩
  have ht_nonneg : ∀ i ∈ t, 0 ≤ f i := by
    intro i hi
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 ≤ (i : ℝ) - 1 := sub_nonneg.mpr <| by exact_mod_cast hip.one_lt.le
    exact add_nonneg zero_le_one (div_nonneg zero_le_one hsub)
  have ht_one : ∀ i ∈ t, i ∉ fy → 1 ≤ f i := by
    intro i hi hif
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 ≤ (i : ℝ) - 1 := sub_nonneg.mpr <| by exact_mod_cast hip.one_lt.le
    exact le_add_of_nonneg_right (div_nonneg zero_le_one hsub)
  have hlow_prod : partial_euler_product ⌊y⌋₊ ≤ t.prod f := by
    calc
      partial_euler_product ⌊y⌋₊ = fy.prod f := hfy_eq.symm
      _ ≤ t.prod f :=
        Finset.prod_le_prod_of_subset_of_one_le hfy_subset
          (fun i hi ↦ ht_nonneg i (hfy_subset hi)) ht_one
  have hNnat : 2 ≤ N := by
    have : 1 < N := by exact_mod_cast (lt_trans hy hyN)
    omega
  have hupp' : partial_euler_product N ≤ u * |log N| := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one partial_euler_trivial_lower_bound)]
      using hupp (N : ℝ) (by exact_mod_cast hNnat)
  have hlow' : l * |log y| ≤ partial_euler_product ⌊y⌋₊ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one partial_euler_trivial_lower_bound)]
      using hlow y (le_of_lt hy)
  have hden : l * |log y| ≤ t.prod f := hlow'.trans hlow_prod
  have hnum_nonneg : 0 ≤ s.prod f := by
    rw [hs_eq]
    exact le_trans zero_le_one partial_euler_trivial_lower_bound
  have ht_pos : 0 < t.prod f := by
    refine Finset.prod_pos ?_
    intro i hi
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 < (i : ℝ) - 1 := sub_pos.mpr <| by exact_mod_cast hip.one_lt
    exact add_pos zero_lt_one (one_div_pos.mpr hsub)
  have hylog_pos : 0 < |log y| := by
    rw [abs_of_pos (Real.log_pos hy)]
    exact Real.log_pos hy
  have hmain :
      s.prod f / t.prod f ≤ (u * |log N|) / (l * |log y|) := by
    refine (div_le_div_of_nonneg_left hnum_nonneg (mul_pos hl hylog_pos) hden).trans ?_
    exact div_le_div_of_nonneg_right (hs_eq ▸ hupp') (mul_nonneg (le_of_lt hl) (abs_nonneg _))
  have hrewrite :
      (u * |log N|) / (l * |log y|) = (u / l) * |log N| / |log y| := by
    field_simp [hl.ne', abs_ne_zero.mpr (Real.log_pos hy).ne']
  calc
    ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))
        = u'.prod f := by simp [u', f]
    _ = s.prod f / t.prod f := by
          rw [← hsdiff]
          apply (eq_div_iff ht_pos.ne').2
          simpa using (Finset.prod_sdiff (f := f) ht_subset)
    _ ≤ (u * |log N|) / (l * |log y|) := hmain
    _ = (u / l) * |log N| / |log y| := hrewrite

theorem useful_rec_aux2 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ N k : ℕ,
            1 ≤ k →
              1 < y →
                y < N →
                  ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
                      (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
                    (C * |log N| / |log y|) ^ k := by
  rcases useful_rec_aux3 with ⟨C, hC, hN⟩
  refine ⟨C, hC, ?_⟩
  intro y N k hk hy hyN
  specialize hN y N hy hyN
  let s : Finset ℕ := (range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)
  change s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤ (C * |log N| / |log y|) ^ k
  have hprod :
      s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / (p - 1)) ^ k)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        exact sub_nonneg.mpr (by exact_mod_cast hip.one_lt.le)
      exact add_nonneg zero_le_one (div_nonneg (by exact_mod_cast Nat.zero_le k) hi1_nonneg)
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        exact sub_nonneg.mpr (by exact_mod_cast hip.one_lt.le)
      have hden_nonneg : 0 ≤ (1 : ℝ) / ((i : ℝ) - 1) := by
        exact one_div_nonneg.2 hi1_nonneg
      have hstep := one_add_mul_le_pow (by linarith) k (a := (1 : ℝ) / ((i : ℝ) - 1))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  have hs_nonneg : 0 ≤ s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1))) := by
    exact le_of_lt <| Finset.prod_pos fun i hi ↦ by
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_pos : 0 < (i : ℝ) - 1 := by
        exact sub_pos.mpr (by exact_mod_cast hip.one_lt)
      exact add_pos zero_lt_one (one_div_pos.2 hi1_pos)
  have hpow :
      (s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))) ^ k ≤ (C * |log N| / |log y|) ^ k := by
    exact pow_le_pow_left₀ hs_nonneg hN k
  calc
    s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / (p - 1)) ^ k)) := hprod
    _ = (s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))) ^ k := by
      simpa using (Finset.prod_pow s k (fun p ↦ ((1 : ℝ) + 1 / (p - 1))))
    _ ≤ (C * |log N| / |log y|) ^ k := hpow

theorem hcongr_thing {α β : Type*} (f g : α → β) :
    ∀ (p q : α → Prop),
      p = q →
        HEq (fun x (_ : p x) ↦ f x) (fun x (_ : q x) ↦ g x) →
          ∀ x, p x → f x = g x := by
  intro p q hpq h x hx
  subst hpq
  exact congrFun₂ (eq_of_heq h) x hx

theorem prod_one_add' {D : Finset ℕ} (hD : 0 ∉ D) (f : ArithmeticFunction ℝ)
    (hf' : f.IsMultiplicative) (hf'' : ∀ i, 0 ≤ f i) :
    D.sum f ≤
      (D.biUnion fun n ↦ n.primeFactorsList.toFinset).prod
        (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum f) := by
  classical
  rw [Finset.prod_one_add]
  simp only [Finset.prod_sum]
  rw [Finset.sum_sigma']
  refine my_sum_lemma
      (f := f)
      (g := fun x : Σ x : Finset ℕ, ∀ a ∈ x, ℕ =>
        ∏ x_1 ∈ x.1.attach, f (x.2 x_1 x_1.prop))
      (r := fun d hd ↦ ⟨d.primeFactors, fun p hp ↦ p ^ d.factorization p⟩)
      ?_ ?_ ?_ ?_
  · intro d₁ d₂ hd₁ hd₂ h
    simp only [Sigma.mk.inj_iff] at h
    have hpow :
        ∀ p ∈ d₁.primeFactors, p ^ d₁.factorization p = p ^ d₂.factorization p := by
      intro p hp
      have hmem : (fun x ↦ x ∈ d₁.primeFactors) = fun x ↦ x ∈ d₂.primeFactors := by
        ext x
        rw [h.1]
      exact hcongr_thing _ _ _ _ hmem h.2 p hp
    apply Nat.eq_of_factorization_eq
    · exact ne_of_mem_of_not_mem hd₁ hD
    · exact ne_of_mem_of_not_mem hd₂ hD
    intro p
    by_cases hp : p ∈ d₁.primeFactors
    · apply Nat.pow_right_injective (Nat.prime_of_mem_primeFactors hp).two_le
      exact hpow p hp
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rwa [hp, eq_comm, ← Finsupp.notMem_support_iff, Nat.support_factorization, ← h.1,
        ← Nat.support_factorization, Finsupp.notMem_support_iff]
  · intro i hi
    apply Finset.prod_nonneg
    intro j hj
    exact hf'' _
  · intro d hd
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_pi, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨d, hd, hx⟩
    intro a had
    have hd₀ : d ≠ 0 := ne_of_mem_of_not_mem hd hD
    have hfac : d.factorization a ≠ 0 := by
      rwa [← Finsupp.mem_support_iff, Nat.support_factorization]
    have had' : a.Prime ∧ a ∣ d := (Nat.mem_primeFactors_of_ne_zero hd₀).1 had
    rw [mem_ppowers_in_set' had'.1 hfac]
    exact ⟨⟨_, hd, rfl⟩, dvd_pow_self _ hfac⟩
  · intro d hd
    rw [Finset.prod_attach d.primeFactors (fun y ↦ f (y ^ d.factorization y))]
    rw [(hf'.map_prod _ _ _).symm]
    · congr 1
      rw [← Nat.support_factorization]
      change d.factorization.prod (· ^ ·) = d
      rw [Nat.prod_factorization_pow_eq_self]
      exact ne_of_mem_of_not_mem hd hD
    · intro p₁ hp₁ p₂ hp₂ hneq
      exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp₁)
        (Nat.prime_of_mem_primeFactors hp₂) hneq

theorem dvd_prime_powers {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (hS : ∀ x ∈ S, IsPrimePow x) :
    ∃ m,
      S.filter (fun q ↦ p ∣ q) ⊆
        Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Ico 1 m) := by
  rcases S.eq_empty_or_nonempty with rfl | hS'
  · refine ⟨1, by simp⟩
  refine ⟨S.max' hS' + 1, ?_⟩
  intro x hx
  obtain ⟨p', k, hp', hk, rfl⟩ := (isPrimePow_nat_iff x).1 (hS x (Finset.filter_subset _ _ hx))
  simp only [Finset.mem_filter] at hx
  have hpp : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp').1 (hp.dvd_of_dvd_pow hx.2)
  subst p'
  refine Finset.mem_map.2 ⟨k, ?_, rfl⟩
  simp only [Finset.mem_Ico]
  constructor
  · exact hk
  · exact lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
      ((Finset.le_max' _ _ hx.1).trans (Nat.le_succ _))

theorem dvd_prime_powers' {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (hS : ∀ x ∈ S, IsPrimePow x)
    (hSp : p ∉ S) :
    ∃ m,
      S.filter (fun q ↦ p ∣ q) ⊆
        Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Ico 2 m) := by
  obtain ⟨m, hm⟩ := dvd_prime_powers hp S hS
  refine ⟨m, ?_⟩
  intro x hx
  rcases Finset.mem_map.1 (hm hx) with ⟨n, hn, rfl⟩
  have hn1 : n ≠ 1 := by
    intro hn1
    apply hSp
    simpa [hn1] using hx
  refine Finset.mem_map.2 ⟨n, ?_, rfl⟩
  simp only [Finset.mem_Ico] at hn ⊢
  omega

theorem useful_rec_aux4' (y : ℝ) (k N : ℕ) (D : Finset ℕ) (hD' : 0 ∉ D)
    (hD : ∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) :
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
      ((range (N + 1)).filter Nat.Prime).prod (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) *
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ (1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹))) := by
  have h₁ :
      D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
        (D.biUnion fun n ↦ n.primeFactorsList.toFinset).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q)) := by
    let f : ArithmeticFunction ℝ := ⟨fun d ↦ (k : ℝ) ^ ω d / d, by simp⟩
    have hf' : f.IsMultiplicative := by
      refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.2 ⟨by simp [f], ?_⟩
      intro m n hm hn hmn
      change (k : ℝ) ^ ω (m * n) / ((m * n : ℕ) : ℝ) =
        ((k : ℝ) ^ ω m / (m : ℝ)) * ((k : ℝ) ^ ω n / (n : ℝ))
      rw [ArithmeticFunction.cardDistinctFactors_mul hmn, div_mul_div_comm, Nat.cast_mul, pow_add]
    have hf'' : ∀ i, 0 ≤ f i := by
      intro i
      exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    refine (prod_one_add' hD' f hf' hf'').trans_eq ?_
    refine Finset.prod_congr rfl ?_
    intro p hp
    rw [add_right_inj]
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hωq : ω q = 1 := by
      rw [Finset.mem_filter] at hq
      rw [mem_ppowers_in_set] at hq
      exact ArithmeticFunction.cardDistinctFactors_eq_one_iff.mpr hq.1.1
    simp [f, hωq]
  have hsubset :
      D.biUnion (fun n ↦ n.primeFactorsList.toFinset) ⊆
        (Finset.range (N + 1)).filter Nat.Prime := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨d, hd, hxd⟩
    have hdx : x ∈ d.primeFactors := by
      simpa using hxd
    have hd'' : d.factorization x ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hdx
    have hxN : x ≤ N := by
      exact (Nat.le_self_pow hd'' x).trans <|
        (hD (x ^ d.factorization x) (mem_ppowers_in_set'' hd hd'')).2
    refine Finset.mem_filter.mpr ⟨?_, Nat.prime_of_mem_primeFactors hdx⟩
    show x ∈ Finset.range (N + 1)
    simpa [Finset.mem_range] using Nat.lt_succ_of_le hxN
  have h₃ :
      ∀ i,
        (0 : ℝ) ≤ ((ppowers_in_set D).filter (fun q ↦ i ∣ q)).sum (fun q ↦ (k : ℝ) / q) := by
    intro i
    refine Finset.sum_nonneg ?_
    intro q hq
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply h₁.trans
  refine (Finset.prod_le_prod_of_subset_of_one_le hsubset ?_ ?_).trans ?_
  · intro i hi
    exact add_nonneg zero_le_one (h₃ i)
  · intro i _ _
    exact le_add_of_nonneg_right (h₃ i)
  rw [← Finset.prod_filter_mul_prod_filter_not ((range (N + 1)).filter Nat.Prime) (fun n ↦ y < n),
    mul_comm]
  have hleft₁ :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q))
        ≤
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      exact add_nonneg zero_le_one (h₃ i)
    · simp only [Finset.mem_filter, not_lt, and_imp, Finset.mem_range, Nat.lt_succ_iff,
        add_le_add_iff_left, div_eq_mul_inv, ← mul_sum]
      intro p hpN hp hpy
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      obtain ⟨m, hm⟩ := dvd_prime_powers' hp (ppowers_in_set D)
        (by
          intro x hx
          exact (mem_ppowers_in_set.mp hx).1)
        (fun h ↦ not_lt_of_ge hpy (hD _ h).1)
      refine
        (Finset.sum_le_sum_of_subset_of_nonneg hm
          (fun i _ _ ↦ inv_nonneg.2 (Nat.cast_nonneg _))).trans ?_
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Nat.cast_pow, ← inv_pow]
      refine
        (geom_sum_Ico_le_of_lt_one (inv_nonneg.2 (Nat.cast_nonneg p))
          ((inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt))).trans_eq ?_
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
      field_simp [pow_two, hp0, hp1]
  have hleft₂ :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤
      ((range (N + 1)).filter Nat.Prime).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) := by
    exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
      (fun i hi ↦ by
        rw [mul_comm]
        exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) my_mul_thing))
      (fun i _ _ ↦ by
        rw [mul_comm]
        exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) my_mul_thing))
  have hright :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ y < (n : ℝ))).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q))
        ≤
      (((range (N + 1)).filter (fun n : ℕ ↦ Nat.Prime n ∧ y < (n : ℝ)))).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := by
    rw [Finset.filter_filter]
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      exact add_nonneg zero_le_one (h₃ i)
    · simp only [Finset.mem_filter, and_imp, Finset.mem_range, Nat.lt_succ_iff, add_le_add_iff_left,
        div_eq_mul_inv, ← mul_sum]
      intro p hpN hp hpy
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      obtain ⟨m, hm⟩ := dvd_prime_powers hp (ppowers_in_set D)
        (by
          intro x hx
          exact (mem_ppowers_in_set.mp hx).1)
      refine
        (Finset.sum_le_sum_of_subset_of_nonneg hm
          (fun i _ _ ↦ inv_nonneg.2 (Nat.cast_nonneg _))).trans ?_
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Nat.cast_pow, ← inv_pow]
      refine
        (geom_sum_Ico_le_of_lt_one (inv_nonneg.2 (Nat.cast_nonneg p))
          ((inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt))).trans_eq ?_
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
      field_simp [hp0, hp1]
  refine mul_le_mul (hleft₁.trans hleft₂) hright (Finset.prod_nonneg ?_) (Finset.prod_nonneg ?_)
  · intro i hi
    exact add_nonneg zero_le_one (h₃ i)
  · intro i hi
    rw [mul_comm]
    exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) my_mul_thing)

theorem useful_rec_aux4 (y : ℝ) (k N : ℕ) (D : Finset ℕ)
    (hD : ∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) :
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
      ((range (N + 1)).filter Nat.Prime).prod (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) *
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ (1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹))) := by
  by_cases h0 : 0 ∈ D
  · have hD' : 0 ∉ D.erase 0 := by simp
    rw [← Finset.sum_erase_add _ _ h0, Nat.cast_zero, div_zero, add_zero]
    apply useful_rec_aux4' y k N _ hD'
    rwa [ppowers_in_set_erase_zero]
  · exact useful_rec_aux4' y k N D h0 hD

theorem useful_rec_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ k N : ℕ,
            ∀ D : Finset ℕ,
              (1 < y →
                y < N →
                  1 ≤ k →
                    (∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) →
                      D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C * |log N| / |log y|) ^ k) := by
  rcases useful_rec_aux1 with ⟨C₁, hC₁, haux₁⟩
  rcases useful_rec_aux2 with ⟨C₂, hC₂, haux₂⟩
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro y k N D hy hyN hk hD
  have hmain := useful_rec_aux4 y k N D hD
  have hleft :
      ((range (N + 1)).filter Nat.Prime).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        C₁ ^ k := haux₁ N k hk
  have hright :
      ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) ≤
        (C₂ * |log N| / |log y|) ^ k := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haux₂ y N k hk hy hyN
  have hright_nonneg :
      0 ≤
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
    have hp1_nonneg : 0 ≤ (p : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast hp'.one_lt.le)
    exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hp1_nonneg))
  have hCpow_nonneg : 0 ≤ C₁ ^ k := by
    exact pow_nonneg hC₁.le _
  have hmul :
      ((range (N + 1)).filter Nat.Prime).prod
            (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) *
          ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
            (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) ≤
        C₁ ^ k * (C₂ * |log N| / |log y|) ^ k := by
    exact mul_le_mul hleft hright hright_nonneg hCpow_nonneg
  calc
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
        ((range (N + 1)).filter Nat.Prime).prod
            (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) *
          ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
            (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := hmain
    _ ≤ C₁ ^ k * (C₂ * |log N| / |log y|) ^ k := hmul
    _ = ((C₁ * C₂) * |log N| / |log y|) ^ k := by
      rw [← mul_pow]
      congr 1
      ring

open Classical in
theorem find_good_d_aux1 :
    ∀ᶠ N : ℕ in atTop,
      ∀ M u y : ℝ,
        ∀ q : ℕ,
          ∀ A ⊆ range (N + 1),
            0 < M →
              M ≤ N →
                0 ≤ u →
                  ∀ d ∈
                      (range (N + 1)).filter
                        (fun d : ℕ ↦
                          (∀ r : ℕ, IsPrimePow r → r ∣ d → Nat.Coprime r (d / r) → y < r ∧ r ≤ N) ∧
                            M * u < (q * d : ℝ) ∧ q * d ≤ N),
                    ((((local_part A q).filter
                          (fun n ↦ (q * d) ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
                        (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤
                      2 * log N / d := by
  filter_upwards [eventually_ge_atTop 0, harmonic_sum_bound_two] with N hN hharmonic
  intro M u y q A hA hM hMN hu d hd
  let X :=
    (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))
  have hdlt : M * u < (q * d : ℝ) := (Finset.mem_filter.mp hd).2.2.1
  have hDnotzero : d ≠ 0 := by
    intro hzd
    subst hzd
    have hdlt' : M * u < 0 := by simpa using hdlt
    exact (not_lt_of_ge (mul_nonneg hM.le hu)) hdlt'
  have hqd_pos : 0 < (q * d : ℝ) := lt_of_le_of_lt (mul_nonneg hM.le hu) hdlt
  have hqd0 : (q * d : ℝ) ≠ 0 := ne_of_gt hqd_pos
  have hrectrivialaux :
      X.sum (fun n ↦ (q : ℚ) / n) ≤
        ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℚ) / n) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      exact ⟨hA ((Finset.filter_subset _ _ : local_part A q ⊆ A) hx.1), hx.2.1⟩
    · intro i _ _
      exact div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg i)
  have hrectrivial' :
      (((X.sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) ≤
        ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) := by
    calc
      (((X.sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) ≤
          ((((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) := by
        exact_mod_cast hrectrivialaux
      _ = ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) := by
        rw [Rat.cast_sum]
        push_cast
        rfl
  have hrectrivial'' :
      ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) ≤
        (1 / d : ℝ) *
          (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) := by
    let g : ℕ → ℕ := fun n ↦ n / (q * d)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum_of_injOn g ?_ ?_ ?_ ?_
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      calc
        a = (q * d) * g a := by simp [g, Nat.mul_div_cancel' ha.2]
        _ = (q * d) * g b := by rw [hab]
        _ = b := by simp [g, Nat.mul_div_cancel' hb.2]
    · intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨a, ha, rfl⟩ := hn
      rw [Finset.mem_filter] at ha
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr <|
          lt_of_le_of_lt (Nat.div_le_self _ _) (Finset.mem_range.mp ha.1)
      · dsimp [g]
        simpa [Nat.mul_div_cancel' ha.2] using Nat.lt_succ_iff.mp (Finset.mem_range.mp ha.1)
    · intro n hn
      rw [Finset.mem_filter] at hn
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hDnotzero
      have hqd0' : ((q * d : ℕ) : ℝ) ≠ 0 := by
        simpa [Nat.cast_mul] using hqd0
      have hcast : (g n : ℝ) = (n : ℝ) / (q * d : ℕ) := by
        dsimp [g]
        rw [Nat.cast_div hn.2 hqd0']
      rw [hcast, Nat.cast_mul, one_div_mul_one_div, mul_div, one_div_div, mul_comm (q : ℝ),
        mul_div_mul_left _ _ hd0]
    · intro n hn _
      exact mul_nonneg (one_div_nonneg.2 (Nat.cast_nonneg d)) (one_div_nonneg.2 (Nat.cast_nonneg n))
  have hrectrivial''' :
      ((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum (fun m ↦ (1 : ℝ) / m) ≤
        (range (N + 1)).sum (fun n ↦ (1 : ℝ) / n) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
      one_div_nonneg.2 (Nat.cast_nonneg i)
  have hfinal :
      (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) ≤
        2 * log N / d := by
    have hstep1 :
        (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) ≤
          (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) := by
      exact mul_le_mul_of_nonneg_left hrectrivial''' (one_div_nonneg.2 (Nat.cast_nonneg d))
    have hstep2 :
        (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) ≤ (1 / d : ℝ) * (2 * log N) := by
      exact mul_le_mul_of_nonneg_left hharmonic (one_div_nonneg.2 (Nat.cast_nonneg d))
    calc
      (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m)
          ≤ (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) := hstep1
      _ ≤ (1 / d : ℝ) * (2 * log N) := hstep2
      _ = 2 * log N / d := by ring
  simpa [X] using hrectrivial'.trans (hrectrivial''.trans hfinal)

open Classical in

end

end UnitFractions
