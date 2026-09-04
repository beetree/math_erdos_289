module

public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.DivisorBound1
public import SolveMath.Corpus.NumberTheory.MertensTheorems

@[expose] public section


noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped Classical ArithmeticFunction ArithmeticFunction.omega ArithmeticFunction.Omega
  BigOperators Chebyshev Nat.Prime Topology

lemma abs_von_mangoldt_div_self_sub_log_div_self_le {x : ℝ} :
  |∑ n ∈ Icc 1 (⌊x⌋₊), Λ n / (n : ℝ) -
      ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p / (p : ℝ)| ≤
    ∑ n ∈ Icc 1 (⌊x⌋₊), (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have h₁ : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) =
      ∑ n ∈ filter IsPrimePow (Icc 1 ⌊x⌋₊), Λ n / (n : ℝ) := by
    symm
    refine Finset.sum_filter_of_ne ?_
    intro n hn hne
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp <| by
      intro hΛ
      exact hne (by simp [hΛ])
  have h₂ : ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ) =
      prime_summatory (fun p ↦ Λ p / (p : ℝ)) 1 x := by
    rw [prime_summatory]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [h₁, h₂, prime_proper_powers]
  refine (abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨-, hpPrime⟩ := hp
  refine (abs_sum_le_sum_abs _ _).trans ?_
  simp only [Nat.cast_pow]
  have hsum :
      (∑ k ∈ Icc 2 ⌊log x / Real.log p⌋₊, |Λ (p ^ k) / (p ^ k : ℝ)|) =
        ∑ k ∈ Icc 2 ⌊log x / Real.log p⌋₊, Λ p / (p ^ k : ℝ) := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_pow
        ((zero_lt_two.trans_le (Finset.mem_Icc.mp hk).1).ne'), abs_div,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_pow, Nat.abs_cast]
  rw [hsum, ArithmeticFunction.vonMangoldt_apply_prime hpPrime,
    show Finset.Icc 2 ⌊log x / Real.log p⌋₊ = Finset.Ico 2 (⌊log x / Real.log p⌋₊ + 1) by
      ext i
      simp]
  simp only [div_eq_mul_inv, ← mul_sum, ← inv_pow]
  refine le_trans ?_ (log_div_sq_sub_le (by exact_mod_cast hpPrime.one_lt))
  refine mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one ?_ ?_) ?_
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hpPrime.one_lt)
  · exact Real.log_nonneg (by exact_mod_cast hpPrime.one_le)

lemma is_O_von_mangoldt_div_self_sub_log_div_self :
  Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ -
        ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p * (p : ℝ)⁻¹)
    (fun _ : ℝ ↦ (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, norm_one, mul_one]
  have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have heqprime : ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p * (p : ℝ)⁻¹ =
      ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹ := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  have hlower : (0 : ℝ) ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ -
      ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹ := by
    rw [sub_nonneg, ← heqprime]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ ↦ mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (inv_nonneg.2 (Nat.cast_nonneg _)))
  have hΛeq : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ) := by
    rw [hset]; simp [div_eq_mul_inv]
  have hbridge : ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / (p : ℝ) := by
    rw [hset, Finset.sum_filter, ← Mertens.sum_prime_eq' ⌊x⌋₊]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp [Mertens.primeFun, div_eq_mul_inv]
  have hupper :
      ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ -
        ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹ ≤ Mertens.E₁ := by
    rw [hΛeq, hbridge]
    linarith [Mertens.sum_vonMangoldt_le_sum_prime_add_E₁ hx]
  rw [abs_of_nonneg hlower]
  linarith [Mertens.E₁_le]

lemma summatory_log_sub :
  Asymptotics.IsBigO atTop
    (fun x ↦
      (∑ n ∈ Icc 1 (⌊x⌋₊), log (n : ℝ)) -
        x * ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹)
    (fun x ↦ x) := by
  have hbound : ∀ x : ℝ, 0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, log (n : ℝ)) - x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ)| ≤
        ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n := by
    intro x hx
    rw [← summatory, ← von_mangoldt_summatory hx le_rfl, mul_sum, summatory,
      ← Finset.sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp only [mul_div_left_comm x, abs_sub_comm, ← mul_sub, abs_mul,
      ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg, Int.self_sub_floor, Int.fract_nonneg]
    refine Finset.sum_le_sum fun n hn ↦ ?_
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (Int.fract_lt_one _).le
  refine Asymptotics.IsBigO.trans ?_ chebyshev_upper
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [one_mul, norm_eq_abs, chebyshev_second_eq_summatory,
    norm_of_nonneg (summatory_nonneg _ _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg))]
  exact hbound x hx

lemma is_O_von_mangoldt_div_self :
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦ ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ - log x)
    (fun _ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨log 4 + 1 + log 2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [Real.norm_eq_abs, norm_one, mul_one]
  have hN : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hxfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hfloorx1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hΛeq : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ) := by
    rw [hset]; simp [div_eq_mul_inv]
  have hmain := Mertens.abs_sum_vonMangoldt_div_sub_log_le_nat hN
  rw [abs_le] at hmain
  have h1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hN
  have hxpos : (0 : ℝ) < x := by linarith
  have hfloorpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by linarith
  have h2floor : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith
  have hlog_mono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    (Real.log_le_log_iff hfloorpos hxpos).mpr hxfloor
  have hlog_gap : Real.log x ≤ Real.log (⌊x⌋₊ : ℝ) + Real.log 2 := by
    have hstep : Real.log x ≤ Real.log (2 * (⌊x⌋₊ : ℝ)) :=
      (Real.log_le_log_iff hxpos (by positivity)).mpr h2floor
    rwa [Real.log_mul (by norm_num) (by positivity), add_comm] at hstep
  have hlog2nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [hΛeq, abs_le]
  constructor <;> linarith [hmain.1, hmain.2, hlog_mono, hlog_gap]

lemma prime_summatory_one_eq_prime_summatory_two {M : Type*} [AddCommMonoid M] (a : ℕ → M) :
  prime_summatory a 1 = prime_summatory a 2 := by
  ext x
  simp only [prime_summatory]
  refine Finset.sum_congr (Finset.ext fun n ↦ ?_) fun _ _ ↦ rfl
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun ⟨⟨_, h2⟩, hp⟩ ↦ ⟨⟨hp.two_le, h2⟩, hp⟩, fun ⟨⟨h1, h2⟩, hp⟩ ↦ ⟨⟨one_le_two.trans h1, h2⟩, hp⟩⟩

lemma log_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ Real.log p / p) 1 x - log x)
    (fun _ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨3 + Real.log 2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  simp only [Real.norm_eq_abs, norm_one, mul_one]
  have hxnn : (0 : ℝ) ≤ x := by linarith
  have hN : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have h1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hN
  have hxfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxnn
  have hfloorx1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hbridge : prime_summatory (fun p ↦ Real.log p / p) 1 x
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p := by
    show ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log n / n
        = ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p
    have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hset, Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun n _ ↦ ?_) (Mertens.sum_prime_eq' ⌊x⌋₊)
    rfl
  have hmain := Mertens.abs_sum_prime_log_div_sub_log_le_nat hN
  rw [abs_le] at hmain
  have hxpos : (0 : ℝ) < x := by linarith
  have hfloorpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by linarith
  have h2floor : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith
  have hlog_mono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    (Real.log_le_log_iff hfloorpos hxpos).mpr hxfloor
  have hlog_gap : Real.log x ≤ Real.log (⌊x⌋₊ : ℝ) + Real.log 2 := by
    have hstep : Real.log x ≤ Real.log (2 * (⌊x⌋₊ : ℝ)) :=
      (Real.log_le_log_iff hxpos (by positivity)).mpr h2floor
    rwa [Real.log_mul (by norm_num) (by positivity), add_comm] at hstep
  rw [hbridge, abs_le]
  constructor <;> linarith [hmain.1, hmain.2, hlog_mono, hlog_gap]

lemma prime_counting_le_self (x : ℕ) : π x ≤ x := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Ioc_zero]
  simpa using Finset.card_filter_le (Finset.Ioc 0 x) Nat.Prime

lemma chebyshev_first_eq_prime_summatory :
  Chebyshev.theta = prime_summatory (fun n ↦ Real.log n) 1 := by
  ext x
  rw [Chebyshev.theta_eq_sum_Icc, prime_summatory]
  congr 1

lemma chebyshev_first_trivial_bound (x : ℝ) :
  Chebyshev.theta x ≤ π ⌊x⌋₊ * log x := by
  by_cases hx : x ≤ 0
  · rw [Chebyshev.theta_eq_zero_of_lt_two (lt_of_le_of_lt hx (by norm_num : (0 : ℝ) < 2))]
    simp [Nat.floor_eq_zero.2 (hx.trans_lt zero_lt_one)]
  · have hx0 : 0 < x := lt_of_not_ge hx
    rw [chebyshev_first_eq_prime_summatory, prime_summatory, prime_counting_eq_card_primes,
      ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ (log x) ?_
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    have hyle : (y : ℝ) ≤ x := by
      exact le_trans (by exact_mod_cast hy.1.2) (Nat.floor_le hx0.le)
    exact Real.log_le_log (show 0 < (y : ℝ) by exact_mod_cast hy.2.pos) hyle

lemma prime_counting_eq_prime_summatory {x : ℕ} :
  π x = prime_summatory (fun _ ↦ 1) 1 x := by
  simp [prime_summatory, prime_counting_eq_card_primes]

lemma prime_counting_eq_prime_summatory' {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) = prime_summatory (fun _ ↦ (1 : ℝ)) 1 x := by
  simp [prime_summatory, prime_counting_eq_card_primes]

lemma chebyshev_first_sub_prime_counting_mul_log_eq {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) * log x - Chebyshev.theta x = ∫ t in Icc 1 x, π ⌊t⌋₊ * t⁻¹ := by
  have hmul :
      (fun n : ℕ ↦ ite (Nat.Prime n) (Real.log n : ℝ) 0) =
        fun n : ℕ ↦ ite (Nat.Prime n) (1 : ℝ) 0 * Real.log n := by
    funext n
    rw [boole_mul]
  simp only [chebyshev_first_eq_prime_summatory, prime_summatory_eq_summatory,
    prime_counting_eq_prime_summatory']
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', hmul,
    partial_summation_cont' (fun n ↦ ite (Nat.Prime n) (1 : ℝ) 0) Real.log (fun y ↦ y⁻¹)
      one_ne_zero (fun y hy ↦ hasDerivAt_log <| by
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        intro hzero
        rw [hzero] at hy'
        norm_num at hy')
      (by
        refine ContinuousOn.inv₀ continuousOn_id ?_
        intro y hy hzero
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        rw [hzero] at hy'
        norm_num at hy') x, Nat.cast_one]

lemma is_O_chebyshev_first_sub_prime_counting_mul_log :
  Asymptotics.IsBigO atTop
    (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x - Chebyshev.theta x) id := by
  simp only [chebyshev_first_sub_prime_counting_mul_log_eq]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx.le
  change ‖∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹‖ ≤ 1 * ‖x‖
  rw [one_mul, Real.norm_of_nonneg hx0]
  have b₁ : ∀ y : ℝ, 1 ≤ y → 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹ := by
    intro y hy
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (by linarith))
  have b₃ :
      (fun a : ℝ ↦ (π ⌊a⌋₊ : ℝ) * a⁻¹) ≤ᵐ[volume.restrict (Icc 1 x)] fun _ : ℝ ↦ (1 : ℝ) := by
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), (π ⌊y⌋₊ : ℝ) * y⁻¹ ≤ 1
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ by
      rw [← div_eq_mul_inv]
      have hy0 : 0 < y := by linarith [hy.1]
      rw [div_le_one hy0]
      simpa using
        le_trans (Nat.cast_le.2 (prime_counting_le_self _))
          (Nat.floor_le (zero_le_one.trans hy.1))
  have hnonneg :
      0 ≤ ∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹ := by
    refine integral_nonneg_of_ae ?_
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  rw [norm_eq_abs, abs_of_nonneg hnonneg]
  refine (integral_mono_of_nonneg ?_ (by simp) b₃).trans ?_
  · change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  · have hconst : ∫ _ in Icc 1 x, (1 : ℝ) = x - 1 := by
      simp [hx.le]
    rw [hconst]
    linarith

lemma is_O_prime_counting_div_log :
  Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ)) (fun x ↦ x / log x) := by
  have h :
      Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) id := by
    refine (is_O_chebyshev_first_sub_prime_counting_mul_log.add chebyshev_first_upper).congr_left ?_
    intro x
    ring
  refine (Asymptotics.IsBigO.mul h (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_assoc, mul_inv_cancel₀ (Real.log_pos hx).ne', mul_one]
  · filter_upwards with x
    simp [div_eq_mul_inv]

lemma prime_counting_le_const_mul_div_log :
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, (π (⌊x⌋₊) : ℝ) ≤ c * ‖x / Real.log x‖ := by
  obtain ⟨c₀, hc₀, hc₀'⟩ := is_O_prime_counting_div_log.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc₀'
  obtain ⟨c₁, hc₁⟩ := hc₀'
  refine ⟨max c₀ c₁, lt_max_of_lt_left hc₀, ?_⟩
  intro x
  have hmax : 0 < max c₀ c₁ := lt_max_of_lt_left hc₀
  have hc₁' :
      ∀ y : ℝ, c₁ ≤ y → ‖(π ⌊y⌋₊ : ℝ)‖ ≤ c₀ * ‖y / Real.log y‖ := by
    intro y hy
    exact hc₁ y hy
  simp only [Real.norm_natCast] at hc₁'
  rcases le_total c₁ x with hx₀ | hx₀
  · exact (hc₁' x hx₀).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rcases lt_trichotomy x 1 with hx₁ | rfl | hx₁
  · rw [Nat.floor_eq_zero.2 hx₁, Nat.primeCounting_zero, Nat.cast_zero]
    exact mul_nonneg (le_max_of_le_left hc₀.le) (norm_nonneg _)
  · simp
  refine (Nat.cast_le.2 (prime_counting_le_self ⌊x⌋₊)).trans ?_
  refine (((Nat.floor_le (zero_le_one.trans hx₁.le)).trans hx₀).trans (le_max_right c₀ c₁)).trans ?_
  rw [le_mul_iff_one_le_right hmax, norm_div, Real.norm_of_nonneg (Real.log_nonneg hx₁.le),
    Real.norm_of_nonneg (zero_le_one.trans hx₁.le), one_le_div (Real.log_pos hx₁)]
  exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans hx₁)).trans (by simp)

lemma chebyshev_second_sub_chebyshev_first_eq {x : ℝ} (hx : 2 ≤ x) :
  Chebyshev.psi x - Chebyshev.theta x ≤ x ^ (1 / 2 : ℝ) * (log x)^2 := by
  rw [Chebyshev.psi_eq_theta_add_sum_theta hx, add_tsub_cancel_left]
  refine (Finset.sum_le_card_nsmul _ _ ((1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * log x) ?_).trans ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hpow : x ^ (1 / k : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (one_le_two.trans hx)
      refine one_div_le_one_div_of_le zero_lt_two hk'
    apply (Chebyshev.theta_mono hpow).trans
    refine (Chebyshev.theta_le_psi _).trans ?_
    refine (chebyshev_trivial_upper (one_le_rpow (one_le_two.trans hx) (by positivity))).trans ?_
    rw [Real.log_rpow (zero_lt_two.trans_le hx)]
    ring_nf
    exact le_rfl
  · have hcard :
        ((Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊).card : ℝ) ≤ Real.log x / Real.log 2 := by
      let m : ℕ := ⌊Real.log x / Real.log 2⌋₊
      refine le_trans ?_ (Nat.floor_le ?_)
      · exact_mod_cast (by simp [Nat.card_Icc] : (Finset.Icc 2 m).card ≤ m)
      · exact div_nonneg (Real.log_nonneg (one_le_two.trans hx)) (Real.log_pos one_lt_two).le
    rw [nsmul_eq_mul]
    refine (mul_le_mul_of_nonneg_right hcard ?_).trans ?_
    · exact
        mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (Real.log_nonneg (one_le_two.trans hx))
    have hconst : (1 / 2 : ℝ) / Real.log 2 ≤ 1 := by
      rw [div_le_iff₀ (Real.log_pos one_lt_two)]
      linarith [Real.log_two_gt_d9]
    have hfac :
        (Real.log x / Real.log 2) * ((1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * Real.log x) =
          ((1 / 2 : ℝ) / Real.log 2) * (x ^ (1 / 2 : ℝ) * (Real.log x)^2) := by
      field_simp [(Real.log_pos one_lt_two).ne']
    rw [hfac]
    refine (mul_le_mul_of_nonneg_right hconst ?_).trans ?_
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · simp

lemma chebyshev_first_two : Chebyshev.theta 2 = Real.log 2 := by
  rw [chebyshev_first_eq_prime_summatory, prime_summatory]
  norm_num [show (Finset.Icc 1 2).filter Nat.Prime = ({2} : Finset ℕ) by decide]

lemma chebyshev_first_trivial_lower : ∀ x, 2 ≤ x → 0.5 ≤ Chebyshev.theta x := by
  intro x hx
  have hmono : Chebyshev.theta 2 ≤ Chebyshev.theta x := Chebyshev.theta_mono hx
  rw [chebyshev_first_two] at hmono
  linarith [Real.log_two_gt_d9]

lemma chebyshev_first_lower : Asymptotics.IsBigO atTop id Chebyshev.theta := by
  have hdiffO :
      Asymptotics.IsBigO atTop
        (fun x ↦ Chebyshev.psi x - Chebyshev.theta x)
        (fun x ↦ x ^ (1 / 2 : ℝ) * (log x)^2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hnonneg₁ : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
      exact sub_nonneg_of_le (Chebyshev.theta_le_psi x)
    have hnonneg₂ : 0 ≤ x ^ (1 / 2 : ℝ) * (log x)^2 := by
      exact mul_nonneg (by positivity) (sq_nonneg _)
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hnonneg₁, Real.norm_eq_abs, abs_of_nonneg hnonneg₂]
    exact chebyshev_second_sub_chebyshev_first_eq hx
  have hdiff :
      Asymptotics.IsLittleO atTop
        (fun x ↦ Chebyshev.psi x - Chebyshev.theta x) id := by
    refine hdiffO.trans_isLittleO ?_
    have ht : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x)^2) (fun x ↦ x ^ (1 / 2 : ℝ)) := by
      refine ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).pow two_pos).congr' ?_ ?_
      · filter_upwards with x using by simp [sq]
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        rw [← Real.rpow_two, ← Real.rpow_mul hx]
        congr 1
        ring
    refine ((isBigO_refl (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) atTop).mul_isLittleO ht).congr' ?_ ?_
    · filter_upwards with x using by rfl
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx, add_halves, Real.rpow_one]
      rfl
  have haux := hdiff.symm.trans_isBigO chebyshev_lower
  exact (chebyshev_lower.trans haux.right_isBigO_add).congr_right (fun x ↦ by ring)

lemma chebyshev_first_all :
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * ‖x‖ ≤ ‖Chebyshev.theta x‖ := by
  obtain ⟨c₀, hc₀, h⟩ := chebyshev_first_lower.exists_pos
  obtain ⟨X, hX⟩ := eventually_atTop.1 h.bound
  let c : ℝ := max c₀ (2 * X)
  have hc : 0 < c := lt_max_of_lt_left hc₀
  refine ⟨c⁻¹, inv_pos.2 hc, ?_⟩
  intro x hx
  rw [inv_mul_le_iff₀ hc]
  rcases le_total X x with hx' | hx'
  · exact (hX x hx').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [Real.norm_of_nonneg (Chebyshev.theta_nonneg x), Real.norm_of_nonneg (zero_le_two.trans hx)]
  have hhalf : (1 / 2 : ℝ) ≤ Chebyshev.theta x := by
    have hlow := chebyshev_first_trivial_lower x hx
    norm_num at hlow ⊢
    exact hlow
  refine hx'.trans ?_
  rw [show X = (2 * X) * (1 / 2 : ℝ) by ring]
  exact
    (mul_le_mul (le_max_right c₀ (2 * X)) hhalf (by norm_num) hc.le)


lemma is_O_div_log_prime_counting :
  Asymptotics.IsBigO atTop (fun x ↦ x / log x) (fun x ↦ (π ⌊x⌋₊ : ℝ)) := by
  have hθ :
      Asymptotics.IsBigO atTop Chebyshev.theta
        (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with x
    rw [one_mul, Real.norm_of_nonneg (Chebyshev.theta_nonneg x), Real.norm_eq_abs]
    exact (chebyshev_first_trivial_bound x).trans (le_abs_self _)
  refine ((chebyshev_first_lower.trans hθ).mul
    (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards with x using by simp [id, div_eq_mul_inv]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_inv_cancel_right₀ (Real.log_pos hx).ne']

def prime_log_div_sum_error (x : ℝ) : ℝ :=
  prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x

lemma prime_summatory_log_mul_inv_eq :
  prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 2 = log + prime_log_div_sum_error := by
  ext x
  rw [Pi.add_apply, prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two]
  ring

lemma is_O_prime_log_div_sum_error :
    Asymptotics.IsBigO atTop prime_log_div_sum_error (fun _ ↦ (1 : ℝ)) := log_reciprocal

@[fun_prop] lemma measurable_prime_log_div_sum_error :
  Measurable prime_log_div_sum_error := by
  change Measurable fun x ↦ prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x
  simp only [prime_summatory_one_eq_prime_summatory_two, prime_summatory_eq_summatory]
  measurability

def prime_reciprocal_integral : ℝ :=
  ∫ x in Ioi 2, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹

theorem continuousOn_inv_mul_rpow_log (p : ℝ) :
    ContinuousOn (fun x : ℝ ↦ (x * Real.log x ^ p)⁻¹) (Set.Ioi 1) := by
  refine (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).rpow_const ?_)).inv₀ ?_
  · exact fun x hx hzero ↦ by rw [hzero] at hx; norm_num at hx
  · exact fun x hx ↦ Or.inl (Real.log_pos hx).ne'
  · exact fun x hx ↦
      mul_ne_zero (zero_lt_one.trans hx).ne' (rpow_pos_of_pos (Real.log_pos hx) p).ne'

lemma my_func_continuous_on : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi 1) := by
  simpa [Real.rpow_two] using continuousOn_inv_mul_rpow_log 2

lemma hasDerivAt_inv_log {y : ℝ} (hy : 1 < y) :
    HasDerivAt (fun x ↦ (log x)⁻¹) (-(y * log y ^ 2)⁻¹) y := by
  have h := (Real.hasDerivAt_log (zero_lt_one.trans hy).ne').inv (Real.log_pos hy).ne'
  rwa [mul_inv, ← div_eq_mul_inv, ← neg_div]

lemma hasDerivAt_neg_inv_log {y : ℝ} (hy : 1 < y) :
    HasDerivAt (fun x ↦ -(log x)⁻¹) ((y * log y ^ 2)⁻¹) y := by
  have h := (hasDerivAt_inv_log hy).neg
  rwa [neg_neg] at h

lemma integral_inv_self_mul_log_sq {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log b)⁻¹ := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ - (log x)⁻¹) ((y * log y ^ 2)⁻¹) y :=
    fun y hy ↦ hasDerivAt_neg_inv_log ((lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1)
  have hcont : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.uIcc a b) := by
    exact my_func_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont),
    neg_sub_neg]

lemma integrable_on_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (g := fun x ↦ -(log x)⁻¹)
    (fun x hx ↦ hasDerivAt_neg_inv_log (ha.trans_le hx))
    (fun x hx ↦ inv_nonneg.2 (mul_nonneg (zero_le_one.trans (ha.le.trans hx.le)) (sq_nonneg _)))
    (by simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).neg)

lemma integrableOn_my_func_Ici {a : ℝ} (ha : 1 < a) :
  IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici a) :=
  (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 (integrable_on_my_func_Ioi ha)

lemma integral_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  ∫ x in Ioi a, (x * log x ^ 2)⁻¹ = (log a)⁻¹ := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := a) (g := fun x ↦ -(log x)⁻¹)
    (fun x hx ↦ hasDerivAt_neg_inv_log (ha.trans_le hx))
    (fun x hx ↦ inv_nonneg.2 (mul_nonneg (zero_le_one.trans (ha.le.trans hx.le)) (sq_nonneg _)))
    (show Tendsto (fun x ↦ -(log x)⁻¹) atTop (𝓝 0) by
      simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).neg)
  simpa using h

lemma my_func2_continuous_on : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Ioi 1) := by
  simpa [Real.rpow_one] using continuousOn_inv_mul_rpow_log 1

lemma integral_inv_self_mul_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x)⁻¹ = log (log b) - log (log a) := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ log (log x)) ((y * log y)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    rw [mul_inv, ← div_eq_mul_inv]
    exact (Real.hasDerivAt_log (by linarith)).log (Real.log_pos hy1).ne'
  have hcont : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.uIcc a b) := by
    exact my_func2_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont)]

lemma integrable_on_prime_log_div_sum_error :
  IntegrableOn (fun x ↦ prime_log_div_sum_error x * (x * log x ^ 2)⁻¹) (Ici 2) := by
  obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
    (atTop_basis' 2).mem_iff.1 hc
  have hsplit : Ici (2 : ℝ) = Ico 2 k ∪ Ici k := by
    rw [Ico_union_Ici_eq_Ici hk₂]
  rw [hsplit]
  have hlog : ContinuousOn log (Icc 2 k) := by
    refine Real.continuousOn_log.mono ?_
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hlog' : ContinuousOn (fun i : ℝ ↦ (i * log i ^ 2)⁻¹) (Icc 2 k) :=
    my_func_continuous_on.mono fun y hy ↦ one_lt_two.trans_le hy.1
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_congr_set_ae Ico_ae_eq_Icc).2 ?_
    simp only [prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two,
      prime_summatory_eq_summatory, sub_mul]
    refine (partial_summation_integrable _ (ContinuousOn.integrableOn_Icc hlog')).sub ?_
    exact (hlog.mul hlog').integrableOn_Icc
  · have hbound :
        ∀ᵐ x : ℝ ∂volume.restrict (Ici k),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ ‖c * (x * log x ^ 2)⁻¹‖ := by
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul, norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ hx) (norm_nonneg _)).trans ?_
      have hcnorm : c * |(1 : ℝ)| ≤ ‖c‖ := by
        simp [Real.norm_eq_abs, le_abs_self]
      exact mul_le_mul_of_nonneg_right hcnorm (norm_nonneg _)
    refine Integrable.mono (g := fun x ↦ c * (x * log x ^ 2)⁻¹) ?_
      (Measurable.aestronglyMeasurable <| by measurability) hbound
    exact (integrableOn_my_func_Ici (one_lt_two.trans_le hk₂)).const_mul c
