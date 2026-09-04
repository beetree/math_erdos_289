module

public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.PrimeReciprocalEq

@[expose] public section

noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped Classical ArithmeticFunction ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open scoped Chebyshev Nat.Prime Topology




lemma weak_mertens_third_upper_all :
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 2 ≤ x → ‖partial_euler_product (⌊x⌋₊)‖ ≤ c * ‖log x‖ := by
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_upper.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨c₁, hc₁⟩ := hc
  refine ⟨max c (2 ^ c₁ / Real.log 2), lt_max_of_lt_left hc₀, fun x hx ↦ ?_⟩
  rcases le_total c₁ x with h | h
  · exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
    norm_of_nonneg (Real.log_nonneg (one_le_two.trans hx))]
  have hpow : (2 : ℝ) ^ π ⌊x⌋₊ ≤ 2 ^ c₁ := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have hpi : (π ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℕ) := by
      exact_mod_cast (prime_counting_le_self ⌊x⌋₊)
    exact le_trans hpi ((Nat.floor_le (zero_le_two.trans hx)).trans h)
  have hupper : 2 ^ c₁ ≤ max c (2 ^ c₁ / Real.log 2) * Real.log x := by
    calc
      2 ^ c₁ = (2 ^ c₁ / Real.log 2) * Real.log 2 := by
        field_simp [(Real.log_pos one_lt_two).ne']
      _ ≤ max c (2 ^ c₁ / Real.log 2) * Real.log x := by
        refine mul_le_mul (le_max_right _ _) (Real.log_le_log zero_lt_two hx)
          (Real.log_nonneg one_le_two) ?_
        exact le_trans (by positivity : 0 ≤ 2 ^ c₁ / Real.log 2) (le_max_right _ _)
  exact (partial_euler_trivial_upper_bound.trans hpow).trans hupper

lemma weak_mertens_third_lower_all :
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 1 ≤ x → c * ‖log x‖ ≤ ‖partial_euler_product (⌊x⌋₊)‖ := by
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_lower.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨c₁, hc₁⟩ := hc
  let c' := max c (Real.log c₁)
  have hc' : 0 < c' := lt_max_of_lt_left hc₀
  refine ⟨c'⁻¹, inv_pos.2 hc', fun x hx ↦ ?_⟩
  rcases le_total c₁ x with h | h
  · rw [inv_mul_le_iff₀ hc']
    exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_of_nonneg (Real.log_nonneg hx),
    norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound)]
  have hlog : Real.log x ≤ c' := by
    exact le_trans (Real.log_le_log (zero_lt_one.trans_le hx) h) (le_max_right _ _)
  have hone : c'⁻¹ * Real.log x ≤ 1 := by
    rw [inv_mul_le_iff₀ hc', mul_one]
    exact hlog
  exact hone.trans (partial_euler_trivial_lower_bound (n := ⌊x⌋₊))

lemma two_pow_card_distinct_divisors_le_divisor_count {n : ℕ} (hn : n ≠ 0) :
  2 ^ ω n ≤ ArithmeticFunction.sigma 0 n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    divisor_function_exact hn, Finsupp.prod, Nat.support_factorization]
  refine Finset.pow_card_le_prod _ _ _ ?_
  intro p hp
  have hp0 : 0 < n.factorization p :=
    Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  omega

lemma mul_eq_mul_iff {a b c d : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbd : b ≤ d) :
  a * b = c * d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    rcases hac.eq_or_lt with rfl | hac'
    · exact ⟨rfl, Nat.mul_left_cancel ha (show a * b = a * d by simpa using h)⟩
    rcases hbd.eq_or_lt with rfl | hbd'
    · exact ⟨Nat.mul_right_cancel hb (show a * b = c * b by simpa using h), rfl⟩
    exact False.elim <| (mul_lt_mul'' hac' hbd' ha.le hb.le).ne h
  · rintro ⟨rfl, rfl⟩
    rfl

lemma divisor_count_eq_pow_iff_squarefree {n : ℕ} :
  ArithmeticFunction.sigma 0 n = 2 ^ ω n ↔ Squarefree n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    divisor_function_exact hn, Finsupp.prod, Nat.support_factorization, ← Finset.prod_const,
    Nat.squarefree_iff_factorization_le_one hn, eq_comm]
  rw [Finset.prod_eq_prod_iff_of_le']
  · constructor
    · intro h p
      by_cases hp : p ∈ n.factorization.support
      · have hpEq : 2 = n.factorization p + 1 := h p hp
        omega
      · rw [Finsupp.notMem_support_iff.mp hp]
        exact Nat.zero_le 1
    · intro h p hp
      have hp0 : 0 < n.factorization p :=
        Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
      have hp1 : n.factorization p ≤ 1 := h p
      omega
  · intro _ _
    exact zero_lt_two
  · intro p hp
    have hp0 : 0 < n.factorization p :=
      Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
    omega

lemma tendsto_primorial_at_top :
  Tendsto primorial atTop atTop := by
  apply primorial_monotone.tendsto_atTop_atTop
  intro a
  obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes a
  refine ⟨p, hp₁.trans ?_⟩
  exact Nat.le_of_dvd (primorial_pos _) hp₂.dvd_primorial

lemma primorial_three : primorial 3 = 6 := by
  decide

lemma two_le_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ≤ primorial n := by
  rw [← primorial_two]
  exact primorial_monotone hn

lemma squarefree_prime_prod {ι : Type*} {s : Finset ι} (f : ι → ℕ)
    (hs : ∀ i ∈ s, (f i).Prime) (hf : Set.InjOn f (s : Set ι)) :
  Squarefree (s.prod f) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun i hi j hj hij => Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (hs i hi) (hs j hj)).2 fun hEq => hij (hf hi hj hEq))
    (fun i hi => (hs i hi).squarefree)

lemma divisor_lower_bound_aux (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ n : ℕ in atTop,
      1 / log (log (n : ℝ)) * (1 - ε) ≤ 1 / (log (log (n : ℝ)) - c) := by
  suffices hmain :
      ∀ᶠ x : ℝ in atTop, 1 / x * (1 - ε) ≤ 1 / (x - c) by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually hmain
  filter_upwards [eventually_ge_atTop (c + -c / ε), eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop c] with x hx hx' hx''
  have hx0 : 0 < x - c := sub_pos_of_lt hx''
  have haux : ε * c - c ≤ ε * x := by
    have := mul_le_mul_of_nonneg_left hx hε.le
    simpa [sub_eq_add_neg, mul_add, mul_div_cancel₀ _ hε.ne'] using this
  have hmul : (1 - ε) * (x - c) ≤ x := by
    nlinarith
  have hmid : 1 - ε ≤ x / (x - c) := (le_div_iff₀ hx0).2 hmul
  have hleft : 1 / x * (1 - ε) = (1 - ε) / x := by ring
  rw [hleft]
  exact (div_le_iff₀ hx').2 <| by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmid

lemma factors_primorial {n : ℕ} :
  (primorial n).primeFactorsList = (List.range (n + 1)).filter Nat.Prime := by
  have hrange : (List.range (n + 1)).Nodup := by
    simpa using (List.nodup_range : (List.range (n + 1)).Nodup)
  have hnodup : ((List.range (n + 1)).filter Nat.Prime).Nodup := hrange.filter _
  have htf :
      ((List.range (n + 1)).filter Nat.Prime).toFinset =
        (Finset.range (n + 1)).filter Nat.Prime := by
    ext x
    simp
  have hprod : ((List.range (n + 1)).filter Nat.Prime).prod = primorial n := by
    calc
      ((List.range (n + 1)).filter Nat.Prime).prod
          = ((List.range (n + 1)).filter Nat.Prime).toFinset.prod id := by
              simpa using (List.prod_toFinset id hnodup).symm
      _ = primorial n := by
            rw [htf, primorial]
            rfl
  refine
    ((Nat.primeFactorsList_unique hprod (fun p hp => by
        simpa using (List.mem_filter.mp hp).2)).eq_of_pairwise' ?_
      (Nat.primeFactorsList_sorted _).pairwise).symm
  have hpair : List.Pairwise (fun a b : ℕ => a ≤ b) (List.range (n + 1)) := by
    simpa using (List.sortedLT_range (n + 1)).pairwise.imp (@Nat.le_of_lt)
  exact hpair.sublist List.filter_sublist

lemma factors_to_finset_primorial {n : ℕ} :
  (primorial n).primeFactorsList.toFinset = (Finset.range (n + 1)).filter Nat.Prime := by
  rw [factors_primorial, ← List.filter_toFinset, List.toFinset_range]

lemma card_distinct_factors_primorial {n : ℕ} : ω (primorial n) = π n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    factors_to_finset_primorial, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

lemma card_factors_primorial {n : ℕ} : Ω (primorial n) = π n := by
  rw [← card_distinct_factors_primorial, eq_comm,
    ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree (primorial_pos _).ne']
  exact squarefree_primorial _

lemma le_log_sigma_zero_primorial :
  ∃ c : ℝ, ∀ p, 2 ≤ p →
    (log (primorial p : ℝ) * Real.log 2) / (log (log (primorial p : ℝ)) - c) ≤
      Real.log (ArithmeticFunction.sigma 0 (primorial p)) := by
  obtain ⟨c, hc₀, hc⟩ := chebyshev_first_all
  refine ⟨Real.log c, ?_⟩
  intro p hp
  have hp₁ : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₂ : 0 < (p : ℝ) := zero_lt_two.trans_le hp₁
  have hp₃ : 0 < Chebyshev.theta p := Chebyshev.theta_pos hp₁
  have htheta : log (primorial p : ℝ) = Chebyshev.theta p := by
    simpa [Chebyshev.theta] using (Chebyshev.theta_eq_log_primorial (p : ℝ)).symm
  have hpow : ((2 : ℝ) ^ ω (primorial p)) = (2 : ℝ) ^ ((ω (primorial p) : ℝ)) := by
    rw [← Real.rpow_natCast]
  rw [divisor_count_eq_pow_iff_squarefree.2 (squarefree_primorial _), Nat.cast_pow, Nat.cast_two,
    hpow, Real.log_rpow (by positivity), card_distinct_factors_primorial, htheta]
  have h₁ : Chebyshev.theta p ≤ π p * log (p : ℝ) := by
    simpa using chebyshev_first_trivial_bound (p : ℝ)
  have hcp : c * (p : ℝ) ≤ Chebyshev.theta p := by
    simpa [Real.norm_of_nonneg hp₂.le, Real.norm_of_nonneg hp₃.le] using hc (p : ℝ) hp₁
  have h₂ : log (p : ℝ) ≤ log (Chebyshev.theta p) - Real.log c := by
    have hlog := Real.log_le_log (mul_pos hc₀ hp₂) hcp
    rw [Real.log_mul hc₀.ne' hp₂.ne'] at hlog
    linarith
  have h₃ : 0 < log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hp)
  have h₄ : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg one_le_two
  have h₅ : (0 : ℝ) ≤ π p := Nat.cast_nonneg (π p)
  have hden : 0 < log (Chebyshev.theta p) - Real.log c := by
    linarith
  refine (div_le_iff₀ hden).2 ?_
  calc
    Chebyshev.theta p * Real.log 2 ≤ (π p * log (p : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h₁ h₄
    _ ≤ (π p * (log (Chebyshev.theta p) - Real.log c)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ h₅) h₄
    _ = π p * Real.log 2 * (log (Chebyshev.theta p) - Real.log c) := by ring

lemma one_le_sigma {k n : ℕ} (hn : n ≠ 0) : 1 ≤ ArithmeticFunction.sigma k n := by
  simpa [ArithmeticFunction.sigma_apply] using
    (Finset.single_le_sum
      (f := fun d : ℕ ↦ d ^ k)
      (fun d _ => Nat.zero_le _)
      (by simp [hn] : 1 ∈ n.divisors))

lemma divisor_lower_bound_log {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in atTop,
      (Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) := by
  obtain ⟨c, hc⟩ := le_log_sigma_zero_primorial
  have hmain :
      ∃ᶠ n : ℕ in atTop,
        log (n : ℝ) * Real.log 2 / (log (log (n : ℝ)) - c) ≤
          log (ArithmeticFunction.sigma 0 n : ℝ) := by
    exact tendsto_primorial_at_top.frequently (eventually_atTop.2 ⟨2, hc⟩).frequently
  apply (hmain.and_eventually (divisor_lower_bound_aux c hε)).mp
  simp only [and_imp]
  filter_upwards [eventually_ge_atTop 1] with n hn₀ hn₁ hn₂
  apply hn₁.trans'
  rw [mul_div_assoc, mul_comm (log (n : ℝ))]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (Nat.one_le_cast.2 hn₀))
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hn₂ (Real.log_nonneg one_le_two)

lemma divisor_lower_bound {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 - ε)) ≤
        ArithmeticFunction.sigma 0 n := by
  apply (divisor_lower_bound_log hε).mp
  filter_upwards [eventually_ge_atTop 1] with n hn₀ hn₁
  have hn₀' : 0 < n := hn₀
  have hn₀'' : (0 : ℝ) < n := by exact_mod_cast hn₀'
  have hsigma : (0 : ℝ) < ArithmeticFunction.sigma 0 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn₀'.ne'
  have hlog :
      log ((n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 - ε))) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) := by
    simpa [Real.log_rpow hn₀''] using hn₁
  exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hn₀'' _) hsigma).1 hlog

lemma cobounded_of_frequently {α : Type*} [ConditionallyCompleteLattice α]
  {f : Filter α} (c : α) (hc : ∃ᶠ x in f, c ≤ x) :
  Filter.IsCobounded (· ≤ ·) f := by
  refine ⟨c, ?_⟩
  intro d hd
  obtain ⟨x, hxc, hxd⟩ := (hc.and_eventually hd).exists
  exact hxc.trans hxd

lemma Limsup_eq_of_eventually_of_frequently {f : Filter ℝ} (c : ℝ)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c + ε)
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c - ε ≤ x) :
  limsup id f = c := by
  have hb : f.IsBounded (· ≤ ·) := ⟨c + 1, upper 1 zero_lt_one⟩
  have hb' : f.IsBoundedUnder (· ≤ ·) id := by
    simpa [Filter.IsBoundedUnder]
      using hb
  have hc : f.IsCobounded (· ≤ ·) :=
    cobounded_of_frequently (c - 1) (by simpa using lower 1 zero_lt_one)
  have hc' : f.IsCoboundedUnder (· ≤ ·) id := by
    simpa [Filter.IsCoboundedUnder]
      using hc
  apply le_antisymm
  · rw [le_iff_forall_pos_le_add]
    intro ε hε
    simpa using (limsup_le_of_le (u := id) (f := f) (a := c + ε) hc' (upper ε hε))
  · rw [le_iff_forall_pos_le_add]
    intro ε hε
    rw [← sub_le_iff_le_add]
    simpa using (le_limsup_of_frequently_le (u := id) (f := f) (a := c - ε) (lower ε hε) hb')

lemma Limsup_eq_of_eventually_of_frequently_mul {f : Filter ℝ} {c : ℝ} (hc : 0 ≤ c)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c * (1 + ε))
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c * (1 - ε) ≤ x) :
  limsup id f = c := by
  rcases hc.eq_or_lt with rfl | hc'
  · refine Limsup_eq_of_eventually_of_frequently 0 (fun ε hε => ?_) (fun ε hε => ?_)
    · apply Filter.EventuallyLE.trans (upper 1 zero_lt_one)
        (Filter.Eventually.of_forall fun x => ?_)
      linarith [hε.le]
    · apply (lower 1 zero_lt_one).mono
      intro x hx
      linarith [hε.le]
  · apply Limsup_eq_of_eventually_of_frequently
    · intro ε hε
      refine (upper (ε / c) (div_pos hε hc')).mono ?_
      intro x hx
      calc
        x ≤ c * (1 + ε / c) := hx
        _ = c + ε := by
          field_simp [hc'.ne']
    · intro ε hε
      refine (lower (ε / c) (div_pos hε hc')).mono ?_
      intro x hx
      calc
        c - ε = c * (1 - ε / c) := by
          field_simp [hc'.ne']
        _ ≤ x := hx

lemma divisor_limsup :
  atTop.limsup
      (fun n : ℕ ↦
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)) =
    log (2 : ℝ) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have l := Real.tendsto_log_atTop
  refine Limsup_eq_of_eventually_of_frequently_mul
    (f := Filter.map
      (fun n : ℕ ↦
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ))
      atTop)
    (Real.log_nonneg one_le_two) ?_ ?_
  · intro ε hε
    change ∀ᶠ n : ℕ in atTop,
      log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ) ≤
        Real.log 2 * (1 + ε)
    filter_upwards [divisor_bound hε, eventually_gt_atTop 0, h (eventually_gt_atTop 0),
      h <| l <| eventually_gt_atTop 0, h <| l <| l <| eventually_gt_atTop 0] with
      n hn hn₀ hn₁ hn₂ hn₃
    dsimp at hn₁ hn₂ hn₃
    have hlog : log (ArithmeticFunction.sigma 0 n : ℝ) ≤
        log ((n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε))) := by
      exact Real.log_le_log (by exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn₀.ne') hn
    have hlog' : log (ArithmeticFunction.sigma 0 n : ℝ) ≤
        (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ) := by
      simpa [Real.log_rpow hn₁] using hlog
    refine (div_le_iff₀ hn₂).2 ?_
    have hmul := mul_le_mul_of_nonneg_right hlog' hn₃.le
    have hEq :
        ((Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ)) * log (log (n : ℝ)) =
          Real.log 2 * (1 + ε) * log (n : ℝ) := by
      field_simp [hn₃.ne']
    calc
      log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ))
          ≤ ((Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ)) *
              log (log (n : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = Real.log 2 * (1 + ε) * log (n : ℝ) := hEq
  · intro ε hε
    change ∃ᶠ n : ℕ in atTop,
      Real.log 2 * (1 - ε) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)
    refine (divisor_lower_bound_log hε).mp ?_
    filter_upwards [eventually_gt_atTop 0, h (eventually_gt_atTop 0),
      h <| l <| eventually_gt_atTop 0, h <| l <| l <| eventually_gt_atTop 0] with
      n hn₀ hn₁ hn₂ hn₃
    dsimp at hn₁ hn₂ hn₃
    intro hn
    refine (le_div_iff₀ hn₂).2 ?_
    have hmul := mul_le_mul_of_nonneg_right hn hn₃.le
    have hEq :
        Real.log 2 * (1 - ε) * log (n : ℝ) =
          ((Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ)) *
            log (log (n : ℝ)) := by
      field_simp [hn₃.ne']
    calc
      Real.log 2 * (1 - ε) * log (n : ℝ) =
          ((Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ)) *
            log (log (n : ℝ)) := hEq
      _ ≤ log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
