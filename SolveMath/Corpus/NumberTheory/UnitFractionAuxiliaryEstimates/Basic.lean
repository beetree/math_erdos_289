module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import SolveMath.Corpus.NumberTheory.UnitFractionDensities
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.TendstoLogCoeTop
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.PartialSummation
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.DivisorBound₁
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.AbsVonMangoldtDiv
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.PrimeReciprocalEq
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.WeakMertensThirdUpper

@[expose] public section


namespace UnitFractions

open Filter Finset Real
open _root_.Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

open Classical

noncomputable section

/-!
This file ports the statement surface of the old `src/aux_lemmas.lean`.

Several results from the Lean 3 file are now available directly in Mathlib 4, sometimes under
slightly different names. In particular, this file mainly re-exports or lightly repackages:

* `tendsto_mul_exp_add_div_pow_atTop`
* `tendsto_nat_ceil_atTop`
* `Nat.dvd_iff_prime_pow_dvd_dvd`
* `ArithmeticFunction.sigma_zero_apply`
* the harmonic-series asymptotics around `Real.eulerMascheroniConstant`

The remaining declarations below are included for API coverage.
-/

theorem tendsto_mul_add_div_pow_log_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (b * x + c) / log x ^ n) atTop atTop :=
  ((tendsto_mul_exp_add_div_pow_atTop b c n hb).comp tendsto_log_atTop).congr' <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Real.exp_log hx]

theorem tendsto_pow_rec_log_log_at_top {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ (c / Real.log (Real.log x))) atTop atTop := by
  have haux : Tendsto (fun x : ℝ => c * x / Real.log x) atTop atTop := by
    simpa [pow_one, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_mul_add_div_pow_log_at_top c 0 1 hc
  refine ((tendsto_exp_atTop.comp haux).comp tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Function.comp, Real.rpow_def_of_pos hx, div_eq_mul_inv, mul_assoc, mul_left_comm]

theorem weird_floor_sq_tendsto_at_top :
    Tendsto (fun x : ℝ => ⌈Real.logb 2 x⌉₊ ^ 2) atTop atTop :=
  (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by decide)).comp
    (tendsto_nat_ceil_atTop.comp (Real.tendsto_logb_atTop one_lt_two))

theorem tendsto_pow_at_top_of {f g : ℝ → ℝ} {l : Filter ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l atTop) :
    Tendsto (fun x : ℝ => g x ^ f x) l atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log (g x)) l atTop := tendsto_log_atTop.comp hg
  have hf' : ∀ᶠ x in l, c / 2 ≤ f x := by
    exact (hf.eventually (Ioi_mem_nhds (show c / 2 < c by linarith))).mono fun _ hx => le_of_lt hx
  have hmul : Tendsto (fun x : ℝ => Real.log (g x) * f x) l atTop := by
    have hbase : Tendsto (fun x : ℝ => (c / 2) * Real.log (g x)) l atTop :=
      Tendsto.const_mul_atTop (show 0 < c / 2 by linarith) hlog
    refine tendsto_atTop_mono' _ ?_ hbase
    filter_upwards [hf', hg.eventually_gt_atTop (1 : ℝ)] with x hx hxg
    have hxlog : 0 ≤ Real.log (g x) := le_of_lt (Real.log_pos hxg)
    nlinarith
  refine (tendsto_exp_atTop.comp hmul).congr' ?_
  filter_upwards [hg.eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Function.comp, Real.rpow_def_of_pos hx, mul_comm]

theorem tendsto_pow_rec_loglog_spec_at_top :
    Tendsto (fun x : ℝ => x ^ ((1 : ℝ) - 8 / Real.log (Real.log x))) atTop atTop := by
  refine tendsto_pow_at_top_of zero_lt_one ?_ tendsto_id
  have hzero : Tendsto (fun x : ℝ => (8 : ℝ) / Real.log (Real.log x)) atTop (𝓝 0) := by
    exact
      (show Tendsto (fun _ : ℝ => (8 : ℝ)) atTop (𝓝 8) from tendsto_const_nhds).div_atTop
        (tendsto_log_atTop.comp tendsto_log_atTop)
  simpa using tendsto_const_nhds.sub hzero

section

variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]

theorem sum_bUnion_le_sum_of_nonneg {f : ℕ → M} {s : Finset ℕ} {t : ℕ → Finset ℕ}
    (hf : ∀ x ∈ s.biUnion t, 0 ≤ f x) :
    (s.biUnion t).sum f ≤ ∑ x ∈ s, ∑ i ∈ t x, f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert n s hns hs =>
      have hunion :
          (insert n s).biUnion t = s.biUnion t ∪ (t n \ s.biUnion t) := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
          rcases Finset.mem_insert.mp hm with rfl | hm
          · by_cases hxs : x ∈ s.biUnion t
            · exact Finset.mem_union.mpr <| Or.inl hxs
            · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨hxm, hxs⟩
          · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_biUnion.mpr ⟨m, hm, hxm⟩
        · intro hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
            exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_insert_of_mem hm, hxm⟩
          · exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_insert_self n s, (Finset.mem_sdiff.mp hx).1⟩
      have hf' : ∀ x ∈ s.biUnion t, 0 ≤ f x := by
        intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
        exact hf x <| Finset.mem_biUnion.mpr ⟨m, Finset.mem_insert_of_mem hm, hxm⟩
      rw [hunion, Finset.sum_union Finset.disjoint_sdiff, Finset.sum_insert hns, add_comm]
      have htail :
          Finset.sum (t n \ s.biUnion t) f ≤ Finset.sum (t n) f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_
        intro x hx _
        exact hf x <| Finset.mem_biUnion.mpr ⟨n, Finset.mem_insert_self n s, hx⟩
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add (hs hf') htail

end

theorem nat_cast_diff_issue {x y : ℤ} : (|x - y| : ℝ) = Int.natAbs (x - y) := by
  rw [← Int.cast_sub, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

theorem harmonic_sum_bound_two :
    ∀ᶠ N in (atTop : Filter ℕ), (Finset.sum (range (N + 1)) fun n => (1 : ℝ) / n) ≤
      2 * Real.log N := by
  filter_upwards [eventually_ge_atTop 6] with N hN
  have hN0 : N ≠ 0 := by omega
  have hsum : Finset.sum (range (N + 1)) (fun n => (1 : ℝ) / n) = ((harmonic N : ℚ) : ℝ) := by
    have h1N : 1 ≤ N + 1 := by omega
    rw [← Finset.sum_range_add_sum_Ico _ h1N]
    rw [Finset.Ico_add_one_right_eq_Icc]
    simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hseq :
      (((harmonic N : ℚ) : ℝ) - Real.log N) = Real.eulerMascheroniSeq' N := by
    simp [Real.eulerMascheroniSeq', hN0]
  have hsmall : (((harmonic N : ℚ) : ℝ) - Real.log N) < 2 / 3 := by
    rw [hseq]
    exact (Real.strictAnti_eulerMascheroniSeq'.antitone (by omega)).trans_lt
      Real.eulerMascheroniSeq'_six_lt_two_thirds
  have hlog : (2 / 3 : ℝ) ≤ Real.log N := by
    have h2N : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
    have hlog2 : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (show 0 < (2 : ℝ) by norm_num) h2N
    linarith [Real.log_two_gt_d9]
  rw [hsum]
  have : (((harmonic N : ℚ) : ℝ)) ≤ Real.log N + 2 / 3 := by linarith
  refine this.trans ?_
  linarith

theorem sum_le_card_mul_real {A : Finset ℕ} {M : ℝ} {f : ℕ → ℝ}
    (h : ∀ n ∈ A, f n ≤ M) :
    A.sum f ≤ A.card * M := by
  simpa [nsmul_eq_mul] using (Finset.sum_le_card_nsmul A f M h)

theorem two_in_Icc {a b x y : ℤ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (|x - y| : ℝ) ≤ b - a := by
  rcases Finset.mem_Icc.mp hx with ⟨hax, hxb⟩
  rcases Finset.mem_Icc.mp hy with ⟨hay, hyb⟩
  have habs : |x - y| ≤ b - a := by
    refine abs_le.mpr ?_
    constructor <;> linarith
  exact_mod_cast habs

theorem two_in_Icc' {a b x y : ℤ} (I : Finset ℤ) (hI : I = Icc a b) (hx : x ∈ I) (hy : y ∈ I) :
    (|x - y| : ℝ) ≤ b - a := by
  rw [hI] at hx hy
  exact two_in_Icc hx hy

theorem dvd_iff_ppowers_dvd (d n : ℕ) :
    d ∣ n ↔ ∀ q, q ∣ d → IsPrimePow q → q ∣ n := by
  constructor
  · intro hdn q hqd _hq
    exact dvd_trans hqd hdn
  · intro h
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpkd
    by_cases hk : k = 0
    · simp [hk]
    · exact h (p ^ k) hpkd (hp.isPrimePow.pow hk)

theorem dvd_iff_ppowers_dvd' (d n : ℕ) (hd : d ≠ 0) :
    d ∣ n ↔ ∀ q, q ∣ d → (IsPrimePow q ∧ Nat.Coprime q (d / q)) → q ∣ n := by
  constructor
  · intro hdn q hqd _hq
    exact dvd_trans hqd hdn
  · intro h
    rw [dvd_iff_ppowers_dvd]
    intro q hqd hq
    rcases (isPrimePow_nat_iff q).1 hq with ⟨p, k, hp, hk, rfl⟩
    let r := p ^ d.factorization p
    have hk' : k ≤ d.factorization p := by
      exact (hp.pow_dvd_iff_le_factorization hd).1 hqd
    have hfac : d.factorization p ≠ 0 := by
      exact Nat.ne_zero_of_lt (lt_of_lt_of_le hk hk')
    apply dvd_trans (pow_dvd_pow _ hk')
    apply h r (by simpa [r] using Nat.ordProj_dvd d p)
    dsimp [r]
    exact ⟨hp.isPrimePow.pow hfac, (factorization_eq_iff (n := d) hp hfac).2 rfl |>.2⟩

theorem rec_sum_le_card_div {A : Finset ℕ} {M : ℝ} (hM : 0 < M) (h : ∀ n ∈ A, M ≤ (n : ℝ)) :
    (rec_sum A : ℝ) ≤ A.card / M := by
  have hsum : (rec_sum A : ℝ) = Finset.sum A (fun n => (1 : ℝ) / n) := by
    simp [rec_sum]
  calc
    (rec_sum A : ℝ) = Finset.sum A (fun n => (1 : ℝ) / n) := hsum
    _ ≤ A.card * (1 / M) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul A (fun n => (1 : ℝ) / n) (1 / M)
          (fun n hn => one_div_le_one_div_of_le hM (h n hn)))
    _ = A.card / M := by simp [div_eq_mul_inv]

theorem tendsto_coe_log_pow_at_top (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℕ => Real.log x ^ c) atTop atTop := by
  exact (tendsto_rpow_atTop hc).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem one_lt_four : (1 : ℝ) < 4 := by norm_num

/-!
Compatibility declarations from the remainder of `src/aux_lemmas.lean`.

Theorems already available directly from Mathlib, such as `sum_pow`, `sum_pow'`, and
`sum_add_sum`, are not duplicated here.
-/

theorem prime_counting_lower_bound_explicit :
    ∀ᶠ N : ℕ in atTop, ⌊Real.sqrt (N : ℝ)⌋₊ ≤ ((Icc 1 N).filter Nat.Prime).card := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 4 by norm_num))
  obtain ⟨c, hc₀, hcheb⟩ := chebyshev_first_all
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((1 / c) ^ (4 : ℝ)))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with N hlarge hlogN h2N hcN hloglogN
  have hlogN' : 0 < Real.log N := by simpa [Function.comp] using hlogN
  have hloglogN' : 0 < Real.log (Real.log N) := by simpa [Function.comp] using hloglogN
  have h0N : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_two h2N
  have hcheb' : c * (N : ℝ) ≤ Chebyshev.theta N := by
    have := hcheb (N : ℝ) h2N
    rw [Real.norm_of_nonneg (show 0 ≤ (N : ℝ) by positivity),
      Real.norm_of_nonneg (Chebyshev.theta_nonneg (N : ℝ))] at this
    simpa using this
  have htriv : Chebyshev.theta N ≤ (π N : ℝ) * Real.log N := by
    simpa using (chebyshev_first_trivial_bound (N : ℝ))
  rw [← prime_counting_eq_card_primes]
  refine Nat.floor_le_of_le ?_
  refine le_of_mul_le_mul_right ?_ hlogN'
  refine le_trans ?_ <| le_trans hcheb' htriv
  refine (Real.log_le_log_iff (mul_pos (Real.sqrt_pos.2 h0N) hlogN')
    (mul_pos hc₀ h0N)).mp ?_
  rw [Real.log_mul (Real.sqrt_pos.2 h0N).ne' hlogN'.ne', Real.sqrt_eq_rpow,
    Real.log_rpow h0N, Real.log_mul hc₀.ne' (show (N : ℝ) ≠ 0 by positivity)]
  have hlargeAbs : |Real.log (Real.log N)| ≤ (1 / 4 : ℝ) * |Real.log N| := by
    simpa [Function.comp, Real.norm_eq_abs] using hlarge
  have hlarge' : Real.log (Real.log N) ≤ (1 / 4 : ℝ) * Real.log N := by
    rw [abs_of_pos hloglogN', abs_of_pos hlogN'] at hlargeAbs
    exact hlargeAbs
  have hcN' : Real.log (1 / c) ≤ (1 / 4 : ℝ) * Real.log N := by
    have hlog := Real.log_le_log (show 0 < (1 / c) ^ (4 : ℝ) by positivity) hcN
    rw [Real.log_rpow (one_div_pos.mpr hc₀)] at hlog
    nlinarith
  have hc' : Real.log c = -Real.log (1 / c) := by rw [one_div, Real.log_inv, neg_neg]
  linarith [hlarge', hcN', hc']

theorem something_like_this {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (A B : Finset ι)
    (hA : A.card = B.card) :
    (∑ g : B ≃ A, ∏ j : B, f (g j)) = B.card.factorial * A.prod f := by
  rw [Finset.sum_congr rfl]
  · rw [Finset.sum_const, nsmul_eq_mul]
    congr 2
    let e : B ≃ A := Fintype.equivOfCardEq (by simpa using hA.symm)
    simpa [e] using Fintype.card_equiv e
  · intro g _
    rw [← Finset.prod_coe_sort A]
    exact Fintype.prod_equiv g _ _ (fun x ↦ rfl)

theorem my_function_aux {n : ℕ} :
    (((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  rw [Finsupp.sum, Multiset.count_sum']
  simp only [Multiset.count_singleton]
  rw [← Finset.card_filter]
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  simp only [Finset.mem_filter] at ha hb
  have hpa : Nat.Prime a := Nat.prime_of_mem_primeFactors <| by
    simpa [Nat.support_factorization] using ha.1
  have hpb : Nat.Prime b := Nat.prime_of_mem_primeFactors <| by
    simpa [Nat.support_factorization] using hb.1
  apply eq_of_prime_pow_eq (Nat.prime_iff.mp hpa) (Nat.prime_iff.mp hpb)
  · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha.1)
  · exact ha.2.symm.trans hb.2

def my_function (n : ℕ) : Finset ℕ :=
  ((((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).toFinset)

theorem card_my_function {n : ℕ} : (my_function n).card = ω n := by
  calc
    (my_function n).card =
        (((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).card := by
          exact Multiset.toFinset_card_of_nodup my_function_aux
    _ = n.factorization.support.card := by
      rw [Finsupp.sum, Multiset.card_sum]
      simp
    _ = n.primeFactors.card := by rw [Nat.support_factorization]
    _ = ω n := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]
      exact Multiset.card_toFinset (m := (n.primeFactorsList : Multiset ℕ))

theorem prod_my_function {n : ℕ} (hn : n ≠ 0) :
    (my_function n).prod id = n := by
  rw [← Finset.prod_val, my_function, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr my_function_aux,
    Finsupp.sum, Multiset.prod_sum]
  simp only [Multiset.prod_singleton]
  exact Nat.prod_factorization_pow_eq_self hn

theorem my_function_injective {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    my_function n = my_function m → n = m := by
  intro h
  rw [← prod_my_function hn, h, prod_my_function hm]

theorem rec_sum_le_prod_sum_aux {A : Finset ℕ} (t : ℕ) (hA : 0 ∉ A) :
    (A.filter (fun n : ℕ ↦ ω n = t)).sum (fun i ↦ (1 : ℝ) / i) ≤
      ((ppowers_in_set A).powersetCard t).sum fun x ↦ x.prod (fun n ↦ (1 : ℝ) / n) := by
  have hsubset :
      (A.filter fun n : ℕ ↦ ω n = t).image my_function ⊆ (ppowers_in_set A).powersetCard t := by
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨n, hn, rfl⟩
    rw [Finset.mem_powersetCard]
    constructor
    · intro m hm
      simp only [my_function, Multiset.mem_toFinset, Finsupp.sum, Multiset.mem_sum,
        Multiset.mem_singleton] at hm
      rcases hm with ⟨a, ha, rfl⟩
      rw [mem_ppowers_in_set']
      · exact ⟨n, (Finset.mem_filter.mp hn).1, rfl⟩
      · exact Nat.prime_of_mem_primeFactors <| by simpa [Nat.support_factorization] using ha
      · exact Finsupp.mem_support_iff.mp ha
    · exact (card_my_function (n := n)).trans ((Finset.mem_filter.mp hn).2)
  have himage :
      (A.filter (fun n : ℕ ↦ ω n = t)).sum (fun i ↦ (1 : ℝ) / i) =
        ((A.filter fun n : ℕ ↦ ω n = t).image my_function).sum
          (fun x ↦ x.prod (fun n ↦ (1 : ℝ) / n)) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro x hx
      simp only [one_div]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
      exact (congrArg (fun z : ℕ => ((z : ℝ) : ℝ)⁻¹)
        (prod_my_function (ne_of_mem_of_not_mem (Finset.mem_filter.mp hx).1 hA))).symm
    · intro x hx y hy hxy
      exact my_function_injective (ne_of_mem_of_not_mem (Finset.mem_filter.mp hx).1 hA)
        (ne_of_mem_of_not_mem (Finset.mem_filter.mp hy).1 hA) hxy
  rw [himage]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
  intro i _ _
  refine Finset.prod_nonneg ?_
  intro j _
  rw [one_div]
  exact inv_nonneg.mpr (by positivity : 0 ≤ (j : ℝ))

theorem rec_sum_le_prod_sum {A : Finset ℕ} (hA₀ : 0 ∉ A) {I : Finset ℕ}
    (hI : ∀ n ∈ A, ω n ∈ I) :
    (rec_sum A : ℝ) ≤
      I.sum (fun t ↦ ((ppowers_in_set A).sum fun q ↦ (1 / q : ℝ)) ^ t / Nat.factorial t) := by
  classical
  let w : ℕ → ℝ := fun q ↦ (1 : ℝ) / q
  have hpowcard :
      ∀ s : Finset ℕ, ∀ t : ℕ,
        (s.powersetCard t).sum (fun x ↦ x.prod w) ≤ (s.sum w) ^ t / Nat.factorial t := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro t
      cases t with
      | zero =>
          simp [w, Finset.powersetCard_zero]
      | succ t =>
          rw [Finset.powersetCard_eq_empty.mpr (Nat.succ_pos t)]
          simp [w]
    · intro a s ha hs t
      cases t with
      | zero =>
          simp [w, ha, Finset.powersetCard_zero]
      | succ t =>
          have hdisj :
              Disjoint (s.powersetCard t.succ) ((s.powersetCard t).image (insert a)) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_image.mp hx2 with ⟨y, hy, rfl⟩
            have hxsub : insert a y ⊆ s := (Finset.mem_powersetCard.mp hx1).1
            exact ha (hxsub (by simp))
          have hy_not : ∀ y ∈ s.powersetCard t, a ∉ y := by
            intro y hy hay
            exact ha ((Finset.mem_powersetCard.mp hy).1 hay)
          rw [Finset.powersetCard_succ_insert ha t, Finset.sum_union hdisj, Finset.sum_image]
          swap
          · intro y hy z hz h
            apply Finset.ext
            intro b
            by_cases hb : b = a
            · subst hb
              simp [hy_not y hy, hy_not z hz]
            · have hmem := congrArg (fun s : Finset ℕ => b ∈ s) h
              simpa [hb] using hmem
          have hins :
              ∑ y ∈ s.powersetCard t, (insert a y).prod w =
                w a * ∑ y ∈ s.powersetCard t, y.prod w := by
            calc
              ∑ y ∈ s.powersetCard t, (insert a y).prod w =
                  ∑ y ∈ s.powersetCard t, w a * y.prod w := by
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    rw [Finset.prod_insert (hy_not y hy)]
              _ = w a * ∑ y ∈ s.powersetCard t, y.prod w := by
                    rw [← Finset.mul_sum]
          have hwa_nonneg : 0 ≤ w a := by
            rw [one_div_nonneg]
            exact_mod_cast Nat.zero_le a
          have hs_nonneg : 0 ≤ s.sum w := by
            refine Finset.sum_nonneg ?_
            intro i hi
            rw [one_div_nonneg]
            exact_mod_cast Nat.zero_le i
          rw [hins]
          have hmain :
              (s.powersetCard t.succ).sum (fun x ↦ x.prod w) +
                  w a * ∑ x ∈ s.powersetCard t, x.prod w ≤
                (s.sum w) ^ t.succ / Nat.factorial t.succ +
                  w a * ((s.sum w) ^ t / Nat.factorial t) := by
            exact add_le_add (hs t.succ) (mul_le_mul_of_nonneg_left (hs t) hwa_nonneg)
          refine le_trans hmain ?_
          have hbinom :
              (s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t ≤
                (s.sum w + w a) ^ t.succ := by
            by_cases hsum : s.sum w = 0
            · rw [hsum]
              cases t with
              | zero => simp
              | succ t => simp [hwa_nonneg]
            · have hsum0 : 0 < s.sum w := lt_of_le_of_ne hs_nonneg (by simpa [eq_comm] using hsum)
              have hratio :
                  -2 ≤ w a / s.sum w := by
                have hratio0 : 0 ≤ w a / s.sum w := div_nonneg hwa_nonneg hs_nonneg
                linarith
              have hpow :
                  (s.sum w) ^ t.succ * (1 + (t.succ : ℝ) * (w a / s.sum w)) ≤
                    (s.sum w) ^ t.succ * (1 + w a / s.sum w) ^ t.succ := by
                exact
                  mul_le_mul_of_nonneg_left (one_add_mul_le_pow hratio t.succ)
                    (pow_nonneg hs_nonneg _)
              calc
                (s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t =
                    (s.sum w) ^ t.succ * (1 + (t.succ : ℝ) * (w a / s.sum w)) := by
                      rw [pow_succ']
                      field_simp [hsum]
                _ ≤ (s.sum w) ^ t.succ * (1 + w a / s.sum w) ^ t.succ := hpow
                _ = (s.sum w * (1 + w a / s.sum w)) ^ t.succ := by rw [mul_pow]
                _ = (s.sum w + w a) ^ t.succ := by
                  congr 1
                  field_simp [hsum]
          have hfact :
              (s.sum w) ^ t.succ / Nat.factorial t.succ + w a * ((s.sum w) ^ t / Nat.factorial t) =
                ((s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t) /
                  Nat.factorial t.succ := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            field_simp [show (Nat.factorial t : ℝ) ≠ 0 by positivity]
          rw [hfact]
          have hdiv :
              ((s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t) / Nat.factorial t.succ ≤
                (s.sum w + w a) ^ t.succ / Nat.factorial t.succ :=
            div_le_div_of_nonneg_right hbinom (by positivity)
          refine hdiv.trans_eq ?_
          simp [Finset.sum_insert, ha, w, add_comm]
  rw [rec_sum]
  push_cast
  have hA : I.biUnion (fun t ↦ A.filter fun n : ℕ ↦ ω n = t) = A := by
    simpa using
      (Finset.biUnion_filter_eq_of_maps_to (s := A) (t := I) (f := fun n : ℕ ↦ ω n) hI)
  nth_rewrite 1 [← hA]
  refine le_trans (sum_bUnion_le_sum_of_nonneg ?_) ?_
  · intro n hn
    rw [one_div_nonneg]
    exact_mod_cast Nat.zero_le n
  refine Finset.sum_le_sum ?_
  intro t ht
  refine le_trans (rec_sum_le_prod_sum_aux t hA₀) ?_
  simpa [w] using hpowcard (ppowers_in_set A) t

theorem such_large_N_wow :
    ∀ᶠ N : ℕ in atTop, 2 * log (log (⌈Real.logb 2 N⌉₊ ^ 2)) < (1 / 500 : ℝ) * log (log N) := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 8000 by norm_num))
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((2 / log 2 : ℝ)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (log 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (exp (exp (2 * log ((2 : ℕ) : ℝ))) * log 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (Real.sqrt 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (1500 * log 2 * 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        haux ] with
    N h1N h1logN hlogN' hlog2logN hcomplogN hsqrtlogN hloglogN hlarge1
  have h0logN : 0 < log N := by
    exact lt_trans zero_lt_one h1logN
  have h0loglogN : 0 < log (log N) := by
    refine lt_trans ?_ hloglogN
    refine mul_pos ?_ zero_lt_two
    refine mul_pos ?_ (log_pos one_lt_two)
    norm_num1
  have h2000 : (0 : ℝ) < 1500 := by norm_num1
  have hhelper : (⌈Real.logb 2 N⌉₊ : ℝ) ≤ log N ^ 2 := by
    refine le_trans (le_of_lt (Nat.ceil_lt_add_one ?_)) ?_
    · exact Real.logb_nonneg one_lt_two h1N
    rw [← add_halves (log N ^ 2)]
    refine add_le_add ?_ ?_
    · rw [Real.logb]
      rw [div_eq_mul_inv]
      have htmp : (log 2)⁻¹ ≤ log N / 2 := by
        rw [le_div_iff₀ zero_lt_two]
        simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlogN'
      calc
        log N * (log 2)⁻¹ ≤ log N * (log N / 2) := by gcongr
        _ = log N ^ 2 / 2 := by ring
    · rw [le_div_iff₀, one_mul, ← Real.sqrt_le_left]
      · exact hsqrtlogN
      · exact le_of_lt h0logN
      · exact zero_lt_two
  have hhelper2 : (1 : ℝ) < ⌈Real.logb 2 N⌉₊ := by
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    rw [Real.logb, one_lt_div (log_pos one_lt_two)]
    · exact hlog2logN
  have hhelper3 : exp (exp (2 * log ↑2)) < ⌈Real.logb 2 N⌉₊ := by
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    rw [Real.logb, lt_div_iff₀ (log_pos one_lt_two)]
    exact hcomplogN
  have hloglogN' : 1500 * log 2 * 2 < log (log N) := by
    simpa [Function.comp] using hloglogN
  have hhelperR : (⌈Real.logb 2 N⌉₊ : ℝ) ≤ log N ^ (2 : ℝ) := by
    simpa [Real.rpow_natCast] using hhelper
  have hlogceil :
      log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log 2 + log (log (log N)) := by
    have hinner :
        log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log (log (log N ^ (2 : ℝ))) := by
      refine Real.log_le_log (log_pos hhelper2) ?_
      exact Real.log_le_log (lt_trans zero_lt_one hhelper2) hhelperR
    calc
      log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log (log (log N ^ (2 : ℝ))) := hinner
      _ = log 2 + log (log (log N)) := by
        rw [Real.log_rpow h0logN, Real.log_mul two_ne_zero h0loglogN.ne']
  have hlarge1' : |log (log (log N))| ≤ (1 / 8000 : ℝ) * |log (log N)| := by
    simpa [Function.comp, Real.norm_eq_abs] using hlarge1
  have hbigconst : (1 : ℝ) < 1500 * log 2 * 2 := by
    nlinarith [Real.log_two_gt_d9]
  have h0logloglogN : 0 < log (log (log N)) := by
    refine Real.log_pos ?_
    exact lt_trans hbigconst hloglogN'
  rw [← Real.rpow_natCast, Real.log_rpow (lt_trans zero_lt_one hhelper2)]
  have hmul :
      log ((2 : ℝ) * log (⌈Real.logb 2 N⌉₊ : ℝ)) =
        log 2 + log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
    rw [Real.log_mul two_ne_zero (log_pos hhelper2).ne']
  change 2 * log ((2 : ℝ) * log (⌈Real.logb 2 N⌉₊ : ℝ)) < (1 / 500 : ℝ) * log (log N)
  rw [hmul, mul_add]
  have hstep1 :
      2 * log 2 + 2 * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) <
        (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
    have haux' : 2 * log 2 < log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
      refine (lt_log_iff_exp_lt (log_pos hhelper2)).2 ?_
      refine (lt_log_iff_exp_lt (lt_trans zero_lt_one hhelper2)).2 ?_
      exact hhelper3
    linarith
  have hstep2 :
      (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) < (1 / 500 : ℝ) * log (log N) := by
    have hconst : 3 * log 2 < (1 / 1000 : ℝ) * log (log N) := by
      nlinarith
    have hsmall :
        3 * log (log (log N)) ≤ (1 / 1000 : ℝ) * log (log N) := by
      rw [abs_of_pos h0logloglogN, abs_of_pos h0loglogN] at hlarge1'
      have : log (log (log N)) ≤ (1 / 8000 : ℝ) * log (log N) := hlarge1'
      linarith
    calc
      (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ))
          = 3 * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by ring
      _ ≤ 3 * (log 2 + log (log (log N))) := by gcongr
      _ < (1 / 500 : ℝ) * log (log N) := by linarith
  exact lt_trans hstep1 hstep2

theorem range_succ_filter_isPrimePow_eq_Icc_filter (N : ℕ) :
    (range (N + 1)).filter IsPrimePow = (Icc 1 N).filter IsPrimePow := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hn, hpp⟩
    exact ⟨⟨(Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hpp.ne_zero, hpp.ne_one⟩).le, hn⟩, hpp⟩
  · rintro ⟨⟨_, hn⟩, hpp⟩
    exact ⟨hn, hpp⟩

theorem explicit_mertens_ge {K : ℝ} (hK : 1 < K) :
    ∀ᶠ N : ℕ in atTop,
      (((range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ) ≤ K * log (log N) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨c, hc₀, hc⟩ := hb.exists_pos
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (c : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((b + 1) / (K - 1)))
    , tendsto_natCast_atTop_atTop.eventually hc.bound ] with N hN₁ hN₂ hN₃
  dsimp at hN₁ hN₂
  have hN₄ : 0 < log N := hc₀.trans_le hN₁
  simp_rw [norm_inv, ← div_eq_mul_inv, ← one_div, norm_eq_abs, abs_of_nonneg hN₄.le,
    Nat.floor_natCast]
    at hN₃
  have hdiv : c / log N ≤ 1 := by
    rw [div_le_iff₀ hN₄]
    linarith
  have hmain := sub_le_iff_le_add.1 (sub_le_of_abs_sub_le_right (hN₃.trans hdiv))
  rw [range_succ_filter_isPrimePow_eq_Icc_filter]
  refine hmain.trans (show log (log N) + b + 1 ≤ K * log (log N) by
    rw [div_le_iff₀ (show (0:ℝ) < K - 1 by linarith)] at hN₂
    nlinarith)

theorem explicit_mertens :
    ∀ᶠ N : ℕ in atTop,
      (((range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ) ≤ 2 * log (log N) :=
  explicit_mertens_ge (K := 2) one_lt_two

theorem card_factors_le_log {n : ℕ} : Ω n ≤ ⌊Real.logb 2 n⌋₊ := by
  by_cases hn : n = 0
  · simp [hn]
  have h0n : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : 2 ^ Ω n ≤ n := by
    rw [ArithmeticFunction.cardFactors_apply]
    calc
      2 ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
        List.pow_card_le_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
      _ = n := Nat.prod_primeFactorsList hn
  exact Nat.le_floor <| (Real.le_logb_iff_rpow_le one_lt_two h0n).2 <| by
    simpa [Real.rpow_natCast] using (show ((2 : ℕ) ^ Ω n : ℝ) ≤ n by exact_mod_cast hpow)

theorem this_condition_here {p : ℕ → Prop} [DecidablePred p] {A : Finset ℕ}
    (hA : ∀ a ∈ A, p a) {N : ℕ} (hN : A.card ≤ ((range N).filter p).card)
    (h : ¬ (range N).filter p ⊆ A) :
    (∃ r < N, r ∉ A ∧ p r ∧ ∃ a ∈ A, r < a) ∨ A ⊂ (range N).filter p := by
  let _ := hN
  have h₁ : (((range N).filter p) \ A).Nonempty := by
    rwa [Finset.sdiff_nonempty]
  rw [or_iff_not_imp_right]
  intro h₂
  have h₂ : (A \ ((range N).filter p)).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h'
    exact h₂ ⟨h', h⟩
  obtain ⟨r, hr⟩ := h₁
  obtain ⟨a, ha⟩ := h₂
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hr
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_and', not_lt] at ha
  exact ⟨r, hr.1.1, hr.2, hr.1.2, a, ha.1, hr.1.1.trans_le (ha.2 (hA _ ha.1))⟩


end

end UnitFractions
