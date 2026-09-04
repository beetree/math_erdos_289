module

public import SolveMath.Corpus.NumberTheory.AbelSummatoryPrimeRestriction
public import SolveMath.Corpus.NumberTheory.ChebyshevPsiLogHarmonicBound
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-! # Asymptotics of the prime-reciprocal sum

`prime_log_div_sum_error x = ∑_{p ≤ x} log p / p - log x` is bounded (Mertens' second theorem,
the `O(1)` step). Integrating it against `1 / (t log² t)` and applying partial summation gives
`meissel_mertens`, the constant in `∑_{p ≤ x} 1/p = log log x + M + O(1 / log x)`. -/

namespace MeisselMertensConstantAsymptotic

noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set Topology
open scoped ArithmeticFunction Nat.Prime
open AbelSummatoryPrimeRestriction ChebyshevPsiLogHarmonicBound

def prime_log_div_sum_error (x : ℝ) : ℝ := by
  exact prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x


lemma prime_summatory_log_mul_inv_eq :
  prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 2 = log + prime_log_div_sum_error := by
  ext x
  rw [Pi.add_apply, prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two]
  ring


lemma is_O_prime_log_div_sum_error :
    Asymptotics.IsBigO atTop prime_log_div_sum_error (fun _ ↦ (1 : ℝ)) := by
  exact log_reciprocal

@[fun_prop] lemma measurable_prime_log_div_sum_error :
  Measurable prime_log_div_sum_error := by
  change Measurable fun x ↦ prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x
  simp only [prime_summatory_one_eq_prime_summatory_two, prime_summatory_eq_summatory]
  measurability


def prime_reciprocal_integral : ℝ := by
  exact ∫ x in Ioi 2, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹


lemma invSelfMulLogSq_continuousOn_Ioi_one : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (pow_ne_zero 2 (Real.log_pos hx').ne')


lemma integral_inv_self_mul_log_sq {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log b)⁻¹ := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ - (log x)⁻¹) ((y * log y ^ 2)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    have hrewrite : (y * log y ^ 2)⁻¹ = -((-y⁻¹) / (log y)^2) := by
      rw [neg_div, neg_neg, div_eq_mul_inv, mul_inv]
    rw [hrewrite]
    exact ((Real.hasDerivAt_log (by linarith)).inv (Real.log_pos hy1).ne').neg
  have hcont : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.uIcc a b) := by
    exact invSelfMulLogSq_continuousOn_Ioi_one.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont),
    neg_sub_neg]


lemma integral_Ioi_my_func_tendsto_aux {a : ℝ} (ha : 1 < a)
  {ι : Type*} {b : ι → ℝ} {l : Filter ι} (hb : Tendsto b l atTop) :
  Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 (log a)⁻¹) := by
  suffices h :
      Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 ((log a)⁻¹ - 0)) by
    simpa using h
  have hEq :
      ∀ᶠ i in l, ∫ x in a..b i, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log (b i))⁻¹ := by
    filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hi
    rw [integral_inv_self_mul_log_sq ha (ha.trans_le hi)]
  rw [tendsto_congr' hEq]
  exact (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hb)).const_sub _


lemma integrable_on_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi a) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (log a)⁻¹ a (fun x ↦ ?_) tendsto_id ?_
  · by_cases hx : a ≤ x
    · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact invSelfMulLogSq_continuousOn_Ioi_one.mono fun y hy ↦ ha.trans_le hy.1
    · simp [Set.Ioc_eq_empty_of_le (le_of_not_ge hx)]
  · refine (integral_Ioi_my_func_tendsto_aux ha tendsto_id).congr' ?_
    filter_upwards [eventually_gt_atTop a] with x hx
    have hax : a ≤ x := le_of_lt hx
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    have hy' : y ∈ Set.Icc a x := by simpa [Set.uIcc_of_le hax] using hy
    rw [Real.norm_of_nonneg]
    exact inv_nonneg.2 (mul_nonneg (le_trans (by linarith) hy'.1) (sq_nonneg _))


lemma integral_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  ∫ x in Ioi a, (x * log x ^ 2)⁻¹ = (log a)⁻¹ := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi a (integrable_on_my_func_Ioi ha) tendsto_id)
    (integral_Ioi_my_func_tendsto_aux ha tendsto_id)


lemma invSelfMulLog_continuousOn_Ioi_one : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul (Real.continuousOn_log.mono ?_)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (Real.log_pos hx').ne'


lemma integral_inv_self_mul_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x)⁻¹ = log (log b) - log (log a) := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ log (log x)) ((y * log y)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    rw [mul_inv, ← div_eq_mul_inv]
    exact (Real.hasDerivAt_log (by linarith)).log (Real.log_pos hy1).ne'
  have hcont : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.uIcc a b) := by
    exact invSelfMulLog_continuousOn_Ioi_one.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont)]


lemma integrable_on_prime_log_div_sum_error :
  IntegrableOn (fun x ↦ prime_log_div_sum_error x * (x * log x ^ 2)⁻¹) (Ici 2) := by
  obtain ⟨c, hcpos, hcO⟩ := is_O_prime_log_div_sum_error.exists_pos
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
    (atTop_basis' 2).mem_iff.1 hcO.bound
  have hsplit : Ici (2 : ℝ) = Ico 2 k ∪ Ici k := by
    rw [Ico_union_Ici_eq_Ici hk₂]
  rw [hsplit]
  have hlog : ContinuousOn log (Icc 2 k) := by
    refine Real.continuousOn_log.mono ?_
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hlog' : ContinuousOn (fun i : ℝ ↦ (i * log i ^ 2)⁻¹) (Icc 2 k) := by
    refine (continuousOn_id.mul (hlog.pow 2)).inv₀ ?_
    intro y hy
    have hy2 : 2 ≤ y := hy.1
    have hy0 : 0 < y := by linarith
    exact mul_ne_zero hy0.ne' (pow_ne_zero _ (Real.log_pos (by linarith)).ne')
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
        simp [Real.norm_eq_abs, abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_right hcnorm (norm_nonneg _)
    refine Integrable.mono (g := fun x ↦ c * (x * log x ^ 2)⁻¹) ?_
      (Measurable.aestronglyMeasurable <| by measurability) hbound
    have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici k) := by
      refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
      exact integrable_on_my_func_Ioi (one_lt_two.trans_le hk₂)
    exact hbase.const_mul c


lemma prime_reciprocal_eq {x : ℝ} (hx : 2 ≤ x) :
  prime_summatory (fun p ↦ (p : ℝ)⁻¹) 2 x -
    (log (log x) + (1 - log (Real.log 2) + prime_reciprocal_integral))
    = prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2) := by
  let a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n * (n : ℝ)⁻¹ else 0
  let f : ℝ → ℝ := fun x ↦ (log x)⁻¹
  let f' : ℝ → ℝ := fun x ↦ (-x⁻¹) / log x ^ 2
  have hdiff : ∀ i ∈ Ici (2 : ℝ), HasDerivAt f (f' i) i := by
    intro i hi
    rw [show f = fun x ↦ (Real.log x)⁻¹ by rfl, show f' i = (-i⁻¹) / log i ^ 2 by rfl]
    have hi2 : (2 : ℝ) ≤ i := hi
    have hi0 : i ≠ 0 := by linarith
    have hi1 : 1 < i := by linarith
    exact (Real.hasDerivAt_log hi0).inv (ne_of_gt (Real.log_pos hi1))
  have hne : ∀ y : ℝ, y ∈ Ici (2 : ℝ) → y ≠ 0 := by
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hcont : ContinuousOn f' (Ici (2 : ℝ)) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_inv₀.mono hne).neg
    · exact (Real.continuousOn_log.mono hne).pow _
    · intro y hy
      exact pow_ne_zero _ (Real.log_pos (one_lt_two.trans_le hy)).ne'
  have hps := partial_summation_cont' a f f' two_ne_zero hdiff hcont x
  rw [sub_eq_iff_eq_add]
  convert hps using 1
  · rw [prime_summatory_eq_summatory]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hpy : y.Prime
    · have hy1 : (1 : ℝ) < y := by
        rw [Nat.one_lt_cast, ← Nat.succ_le_iff]
        exact (Finset.mem_Icc.mp hy).1
      simp [a, f, hpy]
      field_simp [(show (y : ℝ) ≠ 0 by positivity), (Real.log_pos hy1).ne']
    · simp [a, hpy]
  · rw [← prime_summatory_eq_summatory, prime_summatory_log_mul_inv_eq]
    rw [prime_reciprocal_integral]
    simp only [div_eq_mul_inv, Pi.add_apply, add_mul, f', f, neg_mul, mul_neg, integral_neg,
      sub_neg_eq_add, ← mul_inv]
    have h₁ :
        Integrable (fun a ↦ (a * Real.log a)⁻¹)
          (volume.restrict (Icc (((2 : ℕ) : ℝ)) x)) := by
      exact (invSelfMulLog_continuousOn_Ioi_one.mono fun y hy ↦ one_lt_two.trans_le hy.1).integrableOn_Icc
    have hEq :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, Real.log a * (a * Real.log a ^ 2)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Icc (((2 : ℕ) : ℝ)) x, (a * Real.log a)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro y hy
      dsimp
      rw [mul_inv, mul_inv, mul_left_comm, ← div_eq_mul_inv, sq, div_self_mul_self']
    have hErrIcc :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Ioc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      convert
        (integral_Icc_eq_integral_Ioc
          (f := fun a : ℝ ↦ prime_log_div_sum_error a * (a * log a ^ 2)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
        using 1
    have hErrTail :
        ∫ t in Ici x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      convert
        (integral_Ici_eq_integral_Ioi
          (f := fun t : ℝ ↦ prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
          (x := x) (μ := volume))
        using 1
    have hInvIcc :
        ∫ t in Icc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ =
          ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ := by
      simpa using
        (integral_Icc_eq_integral_Ioc (f := fun t : ℝ ↦ (t * log t)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
    have hInv :
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = log (log x) - log (log 2) := by
      calc
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = ∫ t in (2 : ℝ)..x, (t * log t)⁻¹ := by
          symm
          exact intervalIntegral.integral_of_le (f := fun t : ℝ ↦ (t * log t)⁻¹) hx
        _ = log (log x) - log (log 2) := by
          simpa using integral_inv_self_mul_log one_lt_two (one_lt_two.trans_le hx)
    have hUnion :
        ∫ t in Ioi (2 : ℝ), prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          (∫ t in Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
            ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      simpa [Ioc_union_Ioi_eq_Ioi hx, add_assoc] using
        (setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
          (integrable_on_prime_log_div_sum_error.mono_set
            (Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self))
          (integrable_on_prime_log_div_sum_error.mono_set <| by
            intro y hy
            exact hx.trans hy.le) :
          ∫ t in Set.Ioc (2 : ℝ) x ∪ Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
            (∫ t in Set.Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
              ∫ t in Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
    rw [mul_inv_cancel₀ (Real.log_pos (one_lt_two.trans_le hx)).ne', hEq,
      integral_add h₁ (integrable_on_prime_log_div_sum_error.mono_set Icc_subset_Ici_self),
      hInvIcc, hInv, hErrIcc, hErrTail, hUnion]
    ring_nf


lemma prime_reciprocal_error :
  Asymptotics.IsBigO atTop (fun x ↦ prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2)) (fun x ↦ (log x)⁻¹) := by
  simp only [div_eq_mul_inv]
  refine Asymptotics.IsBigO.sub ?_ ?_
  · refine (is_O_prime_log_div_sum_error.mul (isBigO_refl _ _)).trans ?_
    simpa using isBigO_refl (fun x : ℝ ↦ (log x)⁻¹) atTop
  · obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound
    obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
      (atTop_basis' 2).mem_iff.1 hc
    have hbound :
        ∀ y, k ≤ y → ∀ᵐ x : ℝ ∂volume.restrict (Ici y),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ c * (x * log x ^ 2)⁻¹ := by
      intro y hy
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ (hy.trans hx)) (norm_nonneg _)).trans ?_
      rw [norm_eq_abs, abs_one, mul_one, norm_eq_abs, abs_inv, abs_mul, abs_sq, abs_of_nonneg]
      exact zero_le_two.trans (hk₂.trans (hy.trans hx))
    have hI :
        Asymptotics.IsBigO atTop
          (fun y ↦ ∫ x in Ici y, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹)
          (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop k] with y hy
      apply (norm_integral_le_integral_norm _).trans
      rw [norm_eq_abs, one_mul]
      refine le_trans ?_ (le_abs_self _)
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
        ?_ (hbound _ hy)
      have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici y) := by
        refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
        exact integrable_on_my_func_Ioi (one_lt_two.trans_le (hk₂.trans hy))
      exact hbase.const_mul c
    have hEq :
        (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) =ᶠ[atTop] fun y ↦ c * (log y)⁻¹ := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_my_func_Ioi hy]
    exact hI.trans_eventuallyEq hEq |>.trans (Asymptotics.isBigO_const_mul_self c _ _)


def meissel_mertens : ℝ := by
  exact 1 - log (Real.log 2) + prime_reciprocal_integral


lemma prime_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - (log (log x) + meissel_mertens))
    (fun x ↦ (log x)⁻¹) := by
  refine prime_reciprocal_error.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [prime_summatory_one_eq_prime_summatory_two, meissel_mertens, ← prime_reciprocal_eq hx]


lemma mul_add_one_inv (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x + 1 ≠ 0) :
  (x * (x + 1))⁻¹ = x⁻¹ - (x + 1)⁻¹ := by
  field_simp [hx₀, hx₁]
  ring


lemma sum_thing_has_sum (k : ℕ) :
    HasSum (fun n : ℕ ↦ ((n + k + 1) * (n + k + 2) : ℝ)⁻¹) ((k + 1 : ℝ)⁻¹) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => inv_nonneg.2 (by positivity))]
  have htel :
      ∀ i : ℕ,
        ((i + k + 1 : ℝ) * (i + k + 2))⁻¹ =
          (↑(i + (k + 1)) : ℝ)⁻¹ - (↑(i + 1 + (k + 1)) : ℝ)⁻¹ := by
    intro i
    simp only [Nat.cast_add_one, Nat.cast_add, add_right_comm (i : ℝ) 1, ← add_assoc]
    convert mul_add_one_inv (i + k + 1) ?_ ?_ using 2
    · norm_num [add_assoc]
    · exact_mod_cast Nat.succ_ne_zero (i + k)
    · exact_mod_cast Nat.succ_ne_zero (i + k + 1)
  simp only [htel, Finset.sum_range_sub', zero_add, Nat.cast_add_one]
  simpa using
    (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat (k + 1))).const_sub
      ((k + 1 : ℝ)⁻¹)


lemma sum_thing'_has_sum : HasSum (fun n : ℕ ↦ ((n - 1) * n : ℝ)⁻¹) 1 := by
  refine (hasSum_nat_add_iff' 2).1 ?_
  have hzero :
      (∑ i ∈ Finset.range 2, (((i : ℝ) - 1) * (i : ℝ))⁻¹) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hzero]
  norm_num
  have hbase :
      HasSum (fun n : ℕ ↦ ((↑n + ↑0 + 1) * (↑n + ↑0 + 2) : ℝ)⁻¹) 1 := by
    simpa using sum_thing_has_sum 0
  refine HasSum.congr_fun hbase ?_
  intro n
  have hn2 : (↑n + 2 : ℝ) ≠ 0 := by positivity
  have hn1 : (↑n + 2 - 1 : ℝ) ≠ 0 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  field_simp [hn1, hn2, Nat.cast_add]
  ring


lemma sum_thing'''_has_sum {k : ℕ} (hk : 1 ≤ k) :
  HasSum (fun n : ℕ ↦ ((n + k) * (n + k + 1) : ℝ)⁻¹) ((k : ℝ)⁻¹) := by
  convert sum_thing_has_sum (k - 1) using 1
  · ext n
    rw [add_assoc, add_assoc, Nat.cast_sub hk, Nat.cast_one, sub_add_cancel, add_sub, sub_add]
    norm_num [add_assoc]
  · simp [hk]


lemma inv_natSubOne_mul_self_nonneg : ∀ {n : ℕ}, (0 : ℝ) ≤ (((n - 1) * n : ℝ)⁻¹) := by
  intro n
  exact inv_nonneg.2 natSubOne_mul_self_nonneg


lemma is_O_partial_of_bound {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ range (⌊x⌋₊ + 1), f i - c)
    (fun x ↦ x⁻¹) := by
  have hf'' : Summable f := (sum_thing'_has_sum.summable).of_nonneg_of_le hf' hf
  refine ⟨tsum f, (Asymptotics.IsBigO.of_bound 2 ?_).symm⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx' : 1 ≤ ⌊x⌋₊ := by
    rwa [Nat.le_floor_iff' one_ne_zero, Nat.cast_one]
  have hx'' : (1 : ℝ) ≤ ⌊x⌋₊ := by simpa
  rw [← Summable.sum_add_tsum_nat_add _ hf'', add_tsub_cancel_left, norm_inv,
    norm_of_nonneg (tsum_nonneg fun i ↦ hf' (i + _)), norm_of_nonneg (zero_le_one.trans hx)]
  transitivity (⌊x⌋₊ : ℝ)⁻¹
  · refine hasSum_le (fun n ↦ ?_) ((summable_nat_add_iff _).2 hf'').hasSum
      (sum_thing'''_has_sum hx')
    have hsub : (↑n : ℝ) + (↑⌊x⌋₊ + 1) - 1 = ↑n + ↑⌊x⌋₊ := by ring
    simpa [Nat.cast_add, Nat.cast_add_one, add_assoc, add_left_comm, add_comm, mul_comm,
      mul_left_comm, mul_assoc, hsub] using hf (n + (⌊x⌋₊ + 1))
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := zero_lt_one.trans_le hx''
  field_simp [hxpos.ne', hfloorpos.ne']
  nlinarith [Nat.lt_floor_add_one x]


lemma is_O_partial_of_bound' {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ Icc 1 ⌊x⌋₊, f i - c)
    (fun x ↦ x⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_partial_of_bound hf hf'
  refine ⟨c, hc.congr_left ?_⟩
  intro x
  have hIco : Finset.Ico 0 (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    simpa using (Finset.Ico_succ_right_eq_Icc 0 ⌊x⌋₊)
  rw [Finset.range_eq_Ico, hIco, Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · have h0 : f 0 = 0 := ((hf' 0).antisymm (by simpa using hf 0)).symm
    simp [h0]
  · simp



end

end MeisselMertensConstantAsymptotic
