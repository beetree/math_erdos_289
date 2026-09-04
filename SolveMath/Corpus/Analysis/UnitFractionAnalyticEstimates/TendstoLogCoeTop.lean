module

public import SolveMath.Corpus.Analysis.RPowIntegralEstimates
public import SolveMath.Corpus.NumberTheory.PrimeCountingIccCard
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.PSeries


@[expose] public section

noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped ArithmeticFunction ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open scoped Chebyshev Nat.Prime Topology

/-!
This file contains the Lean 4 statement port of the old Lean 3
`for_mathlib/basic_estimates` file.

When a result already exists upstream in Mathlib 4, this file prefers the
Mathlib version instead of reintroducing a duplicate local theorem.
-/


theorem tendsto_log_log_coe_at_top : Tendsto (fun x : ℕ => log (log (x : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

section Summatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ n ≤ x, a n`.
-/
def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n

theorem summatory_nat (a : ℕ → M) (k n : ℕ) :
    summatory a k n = ∑ i ∈ Finset.Icc k n, a i := by
  simp [summatory]

theorem summatory_eq_floor (a : ℕ → M) {k : ℕ} (x : ℝ) :
    summatory a k x = summatory a k ⌊x⌋₊ := by
  rw [summatory, summatory, Nat.floor_natCast]

end Summatory

section PrimeSummatory

variable {M : Type*} [AddCommMonoid M]

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

end PrimeSummatory

def euler_mascheroni : ℝ := 1 - ∫ t in Ioi 1, Int.fract t * (t ^ 2)⁻¹

theorem log_lt_self {x : ℝ} (hx : 0 < x) : log x < x :=
  by nlinarith [log_le_sub_one_of_pos hx]

theorem prime_counting_eq_card_primes {x : ℕ} :
    π x = ((Finset.Icc 1 x).filter Nat.Prime).card :=
  (DisjointResidueFamilyExtremals.primeCounting_eq_card_Icc_filter_prime x).symm

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

theorem trivial_divisor_bound {n : ℕ} : (ArithmeticFunction.sigma 0 n : ℝ) ≤ n := by
  exact_mod_cast (show ArithmeticFunction.sigma 0 n ≤ n by
    rw [ArithmeticFunction.sigma_zero_apply]
    exact Nat.card_divisors_le_self n)

theorem my_mul_thing {n : ℕ} : (0 : ℝ) ≤ (n - 1) * n := by
  rcases Nat.eq_zero_or_pos n with h | h <;> [simp [h]; nlinarith [show (1:ℝ) ≤ n by exact_mod_cast h]]

section SummatoryExtra

variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)

lemma summatory_eq_of_Ico {n k : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a k x = summatory a k n := by
  rw [summatory_eq_floor (a := a) (k := k) x, Nat.floor_eq_on_Ico n x hx]

lemma summatory_eq_of_lt_one {k : ℕ} {x : ℝ} (hk : k ≠ 0) (hx : x < k) :
  summatory a k x = 0 := by
  rw [summatory, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
  exact (Nat.floor_lt' hk).2 hx

lemma summatory_zero_eq_of_lt {x : ℝ} (hx : x < 1) :
  summatory a 0 x = a 0 := by
  rw [summatory_eq_floor (a := a) (k := 0) x, Nat.floor_eq_zero.mpr hx, summatory_nat]
  simp

@[simp] lemma summatory_zero {k : ℕ} (hk : k ≠ 0) : summatory a k 0 = 0 := by
  have hk' : (0 : ℝ) < k := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hk
  exact summatory_eq_of_lt_one (a := a) hk hk'

@[simp] lemma summatory_self {k : ℕ} : summatory a k k = a k := by
  simp [summatory]

@[simp] lemma summatory_one : summatory a 1 1 = a 1 := by
  simp [summatory]

lemma summatory_succ (k n : ℕ) (hk : k ≤ n + 1) :
  summatory a k (n+1) = a (n + 1) + summatory a k n := by
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by exact_mod_cast rfl]
  rw [summatory_nat, summatory_nat]
  have hIcc : Finset.Icc k (n + 1) = insert (n + 1) (Finset.Icc k n) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert]
  · intro hmem
    exact Nat.not_succ_le_self n (Finset.mem_Icc.mp hmem).2

lemma summatory_succ_sub {M : Type*} [AddCommGroup M] (a : ℕ → M) (k : ℕ) (n : ℕ)
  (hk : k ≤ n + 1) :
  a (n + 1) = summatory a k (n + 1) - summatory a k n := by
  rw [summatory_succ (a := a) k n hk, add_sub_cancel_right]

lemma summatory_eq_sub {M : Type*} [AddCommGroup M] (a : ℕ → M) :
  ∀ n, n ≠ 0 → a n = summatory a 1 n - summatory a 1 (n - 1) := by
  intro n hn
  cases n with
  | zero =>
      cases hn rfl
  | succ n =>
      simpa using summatory_succ_sub (a := a) 1 n (by omega)

lemma abs_summatory_le_sum {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M)
    {k : ℕ} {x : ℝ} :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k (⌊x⌋₊), ‖a i‖ := by
  simpa [summatory] using
    (norm_sum_le (s := Finset.Icc k (⌊x⌋₊)) (f := fun i => a i))

lemma summatory_const_one {x : ℝ} :
  summatory (fun _ ↦ (1 : ℝ)) 1 x = (⌊x⌋₊ : ℝ) := by
  simp [summatory]

lemma summatory_nonneg' {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] {a : ℕ → M}
    (k : ℕ) (x : ℝ) (ha : ∀ (i : ℕ), k ≤ i → (i : ℝ) ≤ x → 0 ≤ a i)
    (hk : k ≠ 0) :
  0 ≤ summatory a k x := by
  rw [summatory]
  refine Finset.sum_nonneg ?_
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hi0 : i ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_iff_ne_zero.mpr hk) hi.1)
  exact ha i hi.1 ((Nat.le_floor_iff' hi0).1 hi.2)

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

end SummatoryExtra

namespace ArithmeticFunction



end ArithmeticFunction

namespace Finset

lemma prod_eq_prod_iff_of_le' {ι : Type*}
  {s : Finset ι} {f g : ι → ℕ} (hf : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i ≤ g i) :
  ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  constructor
  · intro hprod i hi
    apply le_antisymm (h i hi)
    by_contra hne
    have hlt : f i < g i := lt_of_le_of_ne (h i hi) fun hEq ↦ hne (hEq ▸ le_rfl)
    exact (Finset.prod_lt_prod hf h ⟨i, hi, hlt⟩).ne hprod
  · intro hall
    exact Finset.prod_congr rfl fun i hi ↦ hall i hi

end Finset

namespace Nat

@[simp] lemma floor_two {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] :
  ⌊(2 : R)⌋₊ = 2 := by
  simp


end Nat

lemma partial_summation_integrable {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    {f : ℝ → 𝕜} {x y : ℝ} {k : ℕ} (hf' : IntegrableOn f (Icc x y)) :
  IntegrableOn (summatory a k * f) (Icc x y) := by
  refine hf'.bdd_mul (c := ∑ i ∈ Finset.Icc k ⌈y⌉₊, ‖a i‖)
    measurable_summatory.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall fun z hz ↦
    abs_summatory_bound a k ⌈y⌉₊ (hz.2.trans (Nat.le_ceil y))

theorem partial_summation_nat {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  {k : ℕ} {N : ℕ} (hN : k ≤ N)
  (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i) (hf' : IntegrableOn f' (Icc k N)) :
  ∑ n ∈ Finset.Icc k N, a n * f n =
    summatory a k N * f N - ∫ t in Icc (k : ℝ) N, summatory a k t * f' t := by
  let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
  have hc_sum :
      ∑ n ∈ Finset.Icc k N, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k N, f n * c n := by
    rw [show Finset.Icc k N = (Finset.Ioc k N).cons k Finset.left_notMem_Ioc by
      simpa using (Finset.Icc_eq_cons_Ioc hN)]
    rw [Finset.sum_cons]
    have htail :
        ∑ n ∈ Finset.Ioc k N, a n * f n =
          ∑ n ∈ Finset.Ioc k N, if k ≤ n then a n * f n else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
      simp [hk]
    simp [c, mul_comm, htail]
  have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) N)] deriv f := by
    change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) N)), f' t = deriv f t
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall ?_
    intro t ht
    exact (hf t ht).deriv.symm
  have hc_abel := sum_mul_eq_sub_sub_integral_mul' (c := c) (f := f) hN
    (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
  have hc_partial : ∀ n, (∑ i ∈ Finset.Icc 0 n, c i) = summatory a k n := by
    intro n
    calc
      ∑ i ∈ Finset.Icc 0 n, c i = ∑ i ∈ Finset.Icc k n, c i := by
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
      _ = ∑ i ∈ Finset.Icc k n, a i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
        simp [c, hk]
      _ = summatory a k n := by rw [← summatory_nat]
  have hcongr :
      ∀ᵐ t ∂volume,
        t ∈ Set.Ioc (k : ℝ) N →
          deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, summatory_eq_floor (a := a) (k := k) t,
      mul_comm]
  have hIocIcc :
      (∫ t in Set.Ioc (k : ℝ) N, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
        ∫ t in Set.Icc (k : ℝ) N, summatory a k t * f' t := by
    rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
      setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [hc_sum, hc_abel, hc_partial, hc_partial, summatory_self, hIocIcc]
  simp [c, mul_comm]
  ring
