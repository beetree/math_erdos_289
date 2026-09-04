module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-! # Summatory functions and partial summation

`summatory a k x` is `∑ k ≤ n ≤ x, a n` for `a : ℕ → M`, and `prime_summatory` restricts the
sum to primes. `partial_summation` is Abel's partial summation formula, relating a weighted
sum `∑ a n * f n` to `summatory a` integrated against `f'`. -/

namespace AbelSummatoryPrimeRestriction

noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped ArithmeticFunction Nat.Prime

variable {M : Type*} [AddCommMonoid M]

def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n


theorem summatory_nat (a : ℕ → M) (k n : ℕ) :
    summatory a k n = ∑ i ∈ Finset.Icc k n, a i := by
  simp [summatory]


theorem summatory_eq_floor (a : ℕ → M) {k : ℕ} (x : ℝ) :
    summatory a k x = summatory a k ⌊x⌋₊ := by
  rw [summatory, summatory, Nat.floor_natCast]


/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ p ≤ x, a p`
where `p` ranges over primes.
-/
def prime_summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ (Finset.Icc k ⌊x⌋₊).filter Nat.Prime, a n


theorem prime_summatory_eq_summatory (a : ℕ → M) :
    prime_summatory a = summatory (fun n => if n.Prime then a n else 0) := by
  ext k x
  simp [prime_summatory, summatory, Finset.sum_filter]



theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  Real.strictMonoOn_log.monotoneOn (by simpa) (by simpa using lt_of_lt_of_le hx hxy) hxy


theorem von_mangoldt_upper {n : ℕ} : Λ n ≤ log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log


abbrev chebyshev_first : ℝ → ℝ := Chebyshev.theta

abbrev chebyshev_second : ℝ → ℝ := Chebyshev.psi



theorem prime_counting_eq_card_primes {x : ℕ} :
    π x = ((Finset.Icc 1 x).filter Nat.Prime).card := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (x + 1)]
  congr 1
  ext p
  simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.lt_succ_iff, and_assoc]
  constructor
  · rintro ⟨hp1, hp2⟩
    exact ⟨hp2.one_le, hp1, hp2⟩
  · rintro ⟨hp1, hp2, hp3⟩
    exact ⟨hp2, hp3⟩


def partial_euler_product (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹

@[simp] theorem partial_euler_product_zero : partial_euler_product 0 = 1 := by
  simp [partial_euler_product]


theorem partial_euler_trivial_lower_bound {n : ℕ} : 1 ≤ partial_euler_product n := by
  refine Finset.one_le_prod ?_
  intro p hp
  simp only [mem_filter] at hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
  exact (one_le_inv₀ hpos).2 (by nlinarith [inv_nonneg.2 (show 0 ≤ (p : ℝ) by positivity)])


theorem natSubOne_mul_self_nonneg : ∀ {n : ℕ}, (0 : ℝ) ≤ (n - 1) * n
  | 0 => by norm_num
  | n + 1 => by
      simpa using (show (0 : ℝ) ≤ (n : ℝ) * (n + 1) by positivity)


variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)


lemma summatory_eq_of_lt_one {k : ℕ} {x : ℝ} (hk : k ≠ 0) (hx : x < k) :
  summatory a k x = 0 := by
  rw [summatory, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
  exact (Nat.floor_lt' hk).2 hx


lemma abs_summatory_le_sum {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M)
    {k : ℕ} {x : ℝ} :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k (⌊x⌋₊), ‖a i‖ := by
  simpa [summatory] using
    (norm_sum_le (s := Finset.Icc k (⌊x⌋₊)) (f := fun i => a i))


lemma summatory_const_one {x : ℝ} :
  summatory (fun _ ↦ (1 : ℝ)) 1 x = (⌊x⌋₊ : ℝ) := by
  simp [summatory]

@[simp] lemma summatory_self {M : Type*} [AddCommMonoid M] {a : ℕ → M} {k : ℕ} :
  summatory a k k = a k := by
  simp [summatory]


lemma summatory_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] (a : ℕ → M)
    (x : ℝ) (k : ℕ) (ha : ∀ (i : ℕ), 0 ≤ a i) :
  0 ≤ summatory a k x := by
  rw [summatory]
  exact Finset.sum_nonneg (fun i _ ↦ ha i)


lemma summatory_monotone_of_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]
    (a : ℕ → M)
  (k : ℕ)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  Monotone (summatory a k) := by
  intro i j hij
  rw [summatory, summatory]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hij)
  · intro n _ _; exact ha n


lemma abs_summatory_bound {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M) (k z : ℕ)
  {x : ℝ} (hx : x ≤ z) :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k z, ‖a i‖ := by
  exact (abs_summatory_le_sum a).trans <|
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_of_le hx))
      (by intro i _ _; exact norm_nonneg _)

@[fun_prop] lemma measurable_summatory {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
  {k : ℕ} {a : ℕ → M} :
  Measurable (summatory a k) := by
  change Measurable ((fun y ↦ ∑ i ∈ Finset.Icc k y, a i) ∘ Nat.floor)
  exact measurable_from_nat.comp Nat.measurable_floor




lemma partial_summation_integrable {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    {f : ℝ → 𝕜} {x y : ℝ} {k : ℕ} (hf' : IntegrableOn f (Icc x y)) :
  IntegrableOn (summatory a k * f) (Icc x y) := by
  let b := ∑ i ∈ Finset.Icc k ⌈y⌉₊, ‖a i‖
  have hsmul : IntegrableOn (b • f) (Icc x y) := Integrable.smul b hf'
  refine hsmul.integrable.mono ?_ ?_
  · exact measurable_summatory.aestronglyMeasurable.mul hf'.1
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_)
      (norm_nonneg _)
    · exact hz.2.trans (Nat.le_ceil y)
    · rw [Real.norm_eq_abs]
      exact le_abs_self b


theorem partial_summation {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  by_cases h : x < k
  · rw [Icc_eq_empty_of_lt h, Measure.restrict_empty, integral_zero_measure, sub_zero,
      summatory_eq_of_lt_one (a := fun n ↦ a n * f n) hk h,
      summatory_eq_of_lt_one (a := a) hk h, zero_mul]
  · have hle : (k : ℝ) ≤ x := le_of_not_gt h
    have hx : k ≤ ⌊x⌋₊ := by rwa [Nat.le_floor_iff' hk]
    let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
    have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) x)] deriv f := by
      change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) x)), f' t = deriv f t
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall ?_
      intro t ht
      exact (hf t ht).deriv.symm
    have habel := sum_mul_eq_sub_sub_integral_mul (c := c) (f := f)
      (show 0 ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k) hle
      (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
    rw [Nat.floor_natCast] at habel
    have hc_partial : ∀ t : ℝ, (∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) = summatory a k t := by
      intro t
      calc
        ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = ∑ i ∈ Finset.Icc k ⌊t⌋₊, c i := by
          symm
          refine Finset.sum_subset ?_ ?_
          · intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            exact ⟨Nat.zero_le _, hi.2⟩
          · intro i hi0 hi
            have hi0' := Finset.mem_Icc.mp hi0
            have hki : ¬ k ≤ i := by
              intro hk
              exact hi (Finset.mem_Icc.mpr ⟨hk, hi0'.2⟩)
            simp [c, hki]
        _ = ∑ i ∈ Finset.Icc k ⌊t⌋₊, a i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
          simp [c, hk]
        _ = summatory a k t := by rw [summatory]
    have hsum :
        ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k ⌊x⌋₊, f n * c n := by
      rw [show Finset.Icc k ⌊x⌋₊ = (Finset.Ioc k ⌊x⌋₊).cons k Finset.left_notMem_Ioc by
        simpa using (Finset.Icc_eq_cons_Ioc hx)]
      rw [Finset.sum_cons]
      have htail :
          ∑ n ∈ Finset.Ioc k ⌊x⌋₊, a n * f n =
            ∑ n ∈ Finset.Ioc k ⌊x⌋₊, if k ≤ n then a n * f n else 0 := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
        simp [hk]
      simp [c, mul_comm, htail]
    have hcongr :
        ∀ᵐ t ∂volume,
          t ∈ Set.Ioc (k : ℝ) x →
            deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, mul_comm]
    have hIocIcc :
        (∫ t in Set.Ioc (k : ℝ) x, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
          ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
      rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
        setIntegral_congr_set Ioc_ae_eq_Icc]
    have hc_k : ∑ i ∈ Finset.Icc 0 k, c i = summatory a k k := by
      simpa using hc_partial (k : ℝ)
    rw [summatory, hsum, habel, hc_partial x, hc_k, summatory_self, hIocIcc]
    simp [c, mul_comm]
    ring


theorem partial_summation_cont {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk hf hf'.integrableOn_Icc


theorem partial_summation_cont' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    (f f' : ℝ → 𝕜) {k : ℕ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Ici k)) (x : ℝ) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation_cont _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono Icc_subset_Ici_self)


lemma fract_mul_integrable {f : ℝ → ℝ} (s : Set ℝ)
  (hf' : IntegrableOn f s) :
  IntegrableOn (Int.fract * f) s := by
  refine Integrable.mono hf' ?_ (Filter.Eventually.of_forall ?_)
  · exact measurable_fract.aestronglyMeasurable.mul hf'.1
  · intro x
    simp only [norm_mul, Pi.mul_apply, norm_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le


lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  Asymptotics.IsBigOWith 1 atTop (fun (x : ℝ) ↦ Int.fract x * f x) f := by
  apply Asymptotics.IsBigOWith.of_bound (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [one_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one x).le


lemma summatory_log_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ log i) 1 x - (x * log x - x) =
    1 + ((∫ t in 1..x, Int.fract t * t⁻¹) - Int.fract x * log x) := by
  rw [intervalIntegral.integral_of_le hx]
  have diff : ∀ i ∈ Ici (1 : ℝ), HasDerivAt log (i⁻¹) i := by
    intro i hi
    exact Real.hasDerivAt_log (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Ici 1) := by
    refine ContinuousOn.inv₀ (f := fun x : ℝ ↦ x) (s := Ici 1) continuousOn_id ?_
    intro x hx
    exact (zero_lt_one.trans_le hx).ne'
  have ps := partial_summation_cont' (fun _ ↦ (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont) x
  simp only [one_mul] at ps
  simp only [ps, integral_Icc_eq_integral_Ioc]
  clear ps
  rw [summatory_const_one, natCast_floor_eq_intCast_floor (zero_le_one.trans hx),
    ← Int.self_sub_fract, sub_mul, sub_sub (x * log x), sub_sub_sub_cancel_left,
    sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← add_assoc, sub_add_cancel, Nat.cast_one,
    ← integral_add]
  · have hEqOn :
        EqOn (fun _ : ℝ ↦ (1 : ℝ))
          (fun y : ℝ ↦ Int.fract y * y⁻¹ + summatory (fun _ ↦ (1 : ℝ)) 1 y * y⁻¹) (Ioc 1 x) := by
      intro y hy
      have hy' : 0 < y := zero_lt_one.trans hy.1
      have hs : summatory (fun _ ↦ (1 : ℝ)) 1 y = (⌊y⌋ : ℝ) := by
        simpa [natCast_floor_eq_intCast_floor hy'.le] using (summatory_const_one (x := y))
      dsimp
      rw [hs]
      have hyinv : y * y⁻¹ = (1 : ℝ) := by
        field_simp [hy'.ne']
      calc
        (1 : ℝ) = y * y⁻¹ := by simpa using hyinv.symm
        _ = (Int.fract y + (⌊y⌋ : ℝ)) * y⁻¹ := by
          rw [Int.fract_add_floor]
        _ = Int.fract y * y⁻¹ + (⌊y⌋ : ℝ) * y⁻¹ := by ring
    rw [← integral_one, intervalIntegral.integral_of_le hx,
      setIntegral_congr_fun measurableSet_Ioc hEqOn]
  · refine fract_mul_integrable _ ?_
    exact (cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact
      (partial_summation_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc)).mono_set
        Ioc_subset_Icc_self


lemma is_o_const_of_tendsto_at_top (f : ℝ → ℝ) (l : Filter ℝ) (h : Tendsto f l atTop)
    (c : ℝ) :
  Asymptotics.IsLittleO l (fun _ : ℝ ↦ c) f := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hbound : ∀ᶠ x : ℝ in atTop, ‖c‖ ≤ ε * ‖x‖ := by
    filter_upwards [eventually_ge_atTop (‖c‖ * ε⁻¹), eventually_ge_atTop (0 : ℝ)] with x hx₁ hx₂
    rw [norm_of_nonneg hx₂]
    calc
      ‖c‖ = ε * (‖c‖ * ε⁻¹) := by
        field_simp [hε.ne']
      _ ≤ ε * x := mul_le_mul_of_nonneg_left hx₁ hε.le
  exact h.eventually hbound


lemma is_o_one_log (c : ℝ) : Asymptotics.IsLittleO atTop (fun _ : ℝ ↦ c) log := by
  exact is_o_const_of_tendsto_at_top _ _ Real.tendsto_log_atTop _


lemma summatory_log {c : ℝ} (hc : 2 < c) :
  Asymptotics.IsBigOWith c atTop
    (fun x ↦ summatory (fun i ↦ log i) 1 x - (x * log x - x))
    (fun x ↦ log x) := by
  have f₁ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ Int.fract x * log x) log :=
    is_O_with_one_fract_mul _
  have f₂ : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (1 : ℝ)) log := is_o_one_log _
  have f₃ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ ∫ t in 1..x, Int.fract t * t⁻¹) log := by
    simp only [Asymptotics.isBigOWith_iff, eventually_atTop, one_mul]
    refine ⟨1, ?_⟩
    intro x hx
    rw [norm_of_nonneg (Real.log_nonneg hx), norm_of_nonneg, ← div_one x,
      ← integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    · have h₁ : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume 1 x := by
        simpa [one_div] using
          (intervalIntegral.intervalIntegrable_one_div (μ := volume)
            (fun y hy => by
              rw [uIcc_of_le hx] at hy
              exact (zero_lt_one.trans_le hy.1).ne')
            continuousOn_id)
      have hInvOn : IntegrableOn (fun u : ℝ ↦ u⁻¹) (Icc 1 x) := by
        rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        exact h₁
      have hfract :
          IntervalIntegrable (fun y : ℝ ↦ Int.fract y * y⁻¹) volume 1 x := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        change IntegrableOn (Int.fract * fun y : ℝ ↦ y⁻¹) (Icc 1 x)
        exact fract_mul_integrable (s := Icc 1 x) hInvOn
      have h₂ : ∀ y ∈ Icc 1 x, Int.fract y * y⁻¹ ≤ y⁻¹ := by
        intro y hy
        refine mul_le_of_le_one_left (inv_nonneg.2 (zero_le_one.trans hy.1)) (Int.fract_lt_one _).le
      exact intervalIntegral.integral_mono_on (μ := volume) hx hfract h₁ h₂
    · refine intervalIntegral.integral_nonneg hx ?_
      intro y hy
      exact mul_nonneg (Int.fract_nonneg _) (inv_nonneg.2 (zero_le_one.trans hy.1))
  refine (f₂.add_isBigOWith (f₃.sub f₁) ?_).congr' rfl ?_ Filter.EventuallyEq.rfl
  · norm_num [hc]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simpa using (summatory_log_aux hx).symm


lemma summatory_mul_floor_eq_summatory_sum_divisors {x y : ℝ}
  (hy : 0 ≤ x) (xy : x ≤ y) (f : ℕ → ℝ) :
  summatory (fun n ↦ f n * ⌊x / n⌋) 1 y =
    summatory (fun n ↦ ∑ i ∈ n.divisors, f i) 1 x := by
  simp_rw [summatory, ← natCast_floor_eq_intCast_floor (div_nonneg hy (Nat.cast_nonneg _)),
    ← summatory_const_one, summatory, Finset.mul_sum, mul_one]
  calc
    ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, ∑ j ∈ Finset.Icc 1 ⌊x / i⌋₊, f i
      = ∑ i ∈ Finset.Icc 1 ⌊y⌋₊,
          ∑ n ∈ (Finset.Icc 1 ⌊x / i⌋₊).image (fun j => i * j), f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            refine Finset.sum_image ?_
            intro a ha b hb hab
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            exact Nat.eq_of_mul_eq_mul_left (Nat.succ_le_iff.mp hi1) hab
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ i ∈ n.divisors, f i := by
          refine Finset.sum_comm'
            (t := fun i : ℕ => (Finset.Icc 1 ⌊x / i⌋₊).image fun j : ℕ => i * j)
            (t' := (Finset.Icc 1 ⌊x⌋₊ : Finset ℕ)) (s' := fun n : ℕ => n.divisors)
            (f := fun i (_n : ℕ) => f i) ?_
          intro i n
          constructor
          · rintro ⟨hi, hn⟩
            rw [Finset.mem_image] at hn
            rcases hn with ⟨j, hj, rfl⟩
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).1
                  ((Finset.mem_Icc.mp hj).2)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := by
              have hmul : (i : ℝ) * j ≤ (i : ℝ) * (x / i) :=
                mul_le_mul_of_nonneg_left hjx (show 0 ≤ (i : ℝ) by positivity)
              have hdiv : (i : ℝ) * (x / i) = x := by
                field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp hi1))]
              simpa [Nat.cast_mul, hdiv] using hmul
            have hi_ne : i ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hi1)
            have hj_ne : j ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hj1)
            have hij_ne : i * j ≠ 0 := Nat.mul_ne_zero hi_ne hj_ne
            refine ⟨?_, ?_⟩
            · rw [Nat.mem_divisors]
              exact ⟨dvd_mul_right i j, hij_ne⟩
            · rw [Finset.mem_Icc]
              exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hij_ne),
                (Nat.le_floor_iff hy).2 hxij⟩
          · rintro ⟨hin, hn⟩
            rw [Nat.mem_divisors] at hin
            rcases hin with ⟨⟨j, rfl⟩, hij_ne⟩
            have hi_ne : i ≠ 0 := by
              intro hi0
              exact hij_ne (by simp [hi0])
            have hj_ne : j ≠ 0 := by
              intro hj0
              exact hij_ne (by simp [hj0])
            have hi1 : 1 ≤ i := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hi_ne)
            have hj1 : 1 ≤ j := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hj_ne)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := (Nat.le_floor_iff hy).1 (Finset.mem_Icc.mp hn).2
            have hix : (i : ℝ) ≤ x := by
              exact
                le_trans
                  (by
                    exact_mod_cast Nat.le_mul_of_pos_right i
                      (Nat.pos_iff_ne_zero.mpr hj_ne))
                  hxij
            have hiy : (i : ℝ) ≤ y := le_trans hix xy
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (le_div_iff₀ (Nat.cast_pos.2 hi1)).2
                  (by simpa [Nat.cast_mul, mul_comm] using hxij)
            refine ⟨Finset.mem_Icc.mpr ⟨hi1, (Nat.le_floor_iff (hy.trans xy)).2 hiy⟩, ?_⟩
            rw [Finset.mem_image]
            exact ⟨j, Finset.mem_Icc.mpr ⟨hj1,
              (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).2 hjx⟩, rfl⟩



end

end AbelSummatoryPrimeRestriction
