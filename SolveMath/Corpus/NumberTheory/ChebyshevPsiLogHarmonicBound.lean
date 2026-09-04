module

public import SolveMath.Corpus.NumberTheory.AbelSummatoryPrimeRestriction
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Field.GeomSum

@[expose] public section

/-! # Chebyshev-function and von Mangoldt estimates

Bounds relating the Chebyshev `psi` function to its summatory-function representation,
Chebyshev's classical linear upper bound `chebyshev_second = O(x)`, and the estimate that
`∑_{n ≤ x} Λ n / n` and `log x` differ by `O(1)`. -/

namespace ChebyshevPsiLogHarmonicBound

noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped ArithmeticFunction Nat.Prime
open AbelSummatoryPrimeRestriction

/-- Splitting off the smallest element of a nonempty-from-below closed interval of naturals. -/
theorem Finset.Icc_eq_insert_Icc_succ {a b : ℕ} (h : a ≤ b) :
    Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
  simpa using (Finset.insert_Icc_succ_left_eq_Icc h).symm

lemma von_mangoldt_summatory {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
  summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 y = summatory (fun n ↦ Real.log n) 1 x := by
  simpa using
    (summatory_mul_floor_eq_summatory_sum_divisors hx xy (fun n => Λ n)).trans <| by
      simp_rw [ArithmeticFunction.vonMangoldt_sum]


lemma helpful_floor_identity2 {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x < 2) :
  ⌊x⌋ - 2 * ⌊x/2⌋ = 1 := by
  have h₁ : ⌊x⌋ = 1 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using hx₁, by simpa [one_add_one_eq_two] using hx₂⟩
  have h₂ : ⌊x / 2⌋ = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
    constructor <;> linarith
  rw [h₁, h₂]
  simp


lemma helpful_floor_identity3 {x : ℝ} :
  2 * ⌊x/2⌋ ≤ ⌊x⌋ := by
  have h₄ : (2 * ⌊x / 2⌋ : Int) - 1 < ⌊x⌋ := by
    exact_mod_cast (show (2 : ℝ) * ⌊x / 2⌋ - 1 < ⌊x⌋ by
      linarith [Int.floor_le (x / 2), Int.sub_one_lt_floor x])
  exact Int.sub_one_lt_iff.mp h₄


def chebyshev_error (x : ℝ) : ℝ := by
  exact
    (summatory (fun i ↦ Real.log i) 1 x - (x * log x - x)) -
      2 * (summatory (fun i ↦ Real.log i) 1 (x / 2) - (x / 2 * log (x / 2) - x / 2))


lemma von_mangoldt_floor_sum {x : ℝ} (hx₀ : 0 < x) :
  summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x =
    Real.log 2 * x + chebyshev_error x := by
  have hhalf :
      summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Real.log n) 1 (x / 2) := by
    rw [show summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Λ n * ⌊(x / 2) / n⌋) 1 x by
          rw [summatory]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [div_right_comm]]
    exact von_mangoldt_summatory (div_nonneg hx₀.le zero_le_two) (half_le_self hx₀.le)
  have hx2 : (2 : ℝ) * (x / 2) = x := by
    simpa using (mul_div_cancel₀ x two_ne_zero)
  calc
    summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x
      = summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 x -
          2 * summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x := by
            rw [summatory, summatory, summatory, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = summatory (fun n ↦ Real.log n) 1 x - 2 * summatory (fun n ↦ Real.log n) 1 (x / 2) := by
          rw [von_mangoldt_summatory hx₀.le le_rfl, hhalf]
    _ = Real.log 2 * x + chebyshev_error x := by
          rw [chebyshev_error, mul_sub, Real.log_div hx₀.ne' two_ne_zero, mul_sub, hx2]
          ring


def chebyshev_first' (x : ℝ) : ℝ := by
  exact ∑ n ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, Real.log n


def chebyshev_second' (x : ℝ) : ℝ := by
  exact Finset.sum (Finset.range ⌊x⌋₊) fun n => Λ n


lemma chebyshev_second_nonneg : 0 ≤ chebyshev_second := by
  intro x
  exact Chebyshev.psi_nonneg x


lemma chebyshev_second_eq_summatory : chebyshev_second = summatory Λ 1 := by
  ext x
  change Chebyshev.psi x = summatory (⇑Λ) 1 x
  rw [Chebyshev.psi_eq_sum_Icc, summatory]
  rw [Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · simp
  · simp

@[simp] lemma chebyshev_first_zero : chebyshev_first 0 = 0 := by
  exact Chebyshev.theta_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_second_zero : chebyshev_second 0 = 0 := by
  exact Chebyshev.psi_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_first'_zero : chebyshev_first' 0 = 0 := by
  simp [chebyshev_first']

@[simp] lemma chebyshev_second'_zero : chebyshev_second' 0 = 0 := by
  simp [chebyshev_second']


lemma chebyshev_upper_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_second x - chebyshev_second (x / 2) - Real.log 2 * x ≤ chebyshev_error x := by
  rw [sub_le_iff_le_add', ← von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory]
  have hs : Finset.Icc 1 ⌊x / 2⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (half_le_self hx.le))
  rw [summatory, ← Finset.sum_sdiff hs, add_sub_cancel_right]
  refine (Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_)
  · simp_rw [Finset.mem_sdiff, Finset.mem_Icc, and_imp, not_and, not_le, Nat.le_floor_iff hx.le,
      Nat.floor_lt (div_nonneg hx.le zero_le_two), Nat.succ_le_iff]
    intro i hi₁ hi₂ hi₃
    replace hi₃ := hi₃ hi₁
    have hge1 : 1 ≤ x / i := by
      refine (one_le_div₀ ?_).2 hi₂
      exact_mod_cast hi₁
    have hlt2 : x / i < 2 := by
      have hi_pos : (0 : ℝ) < i := by
        exact_mod_cast hi₁
      have hmul : x < 2 * i := by
        linarith
      exact (div_lt_iff₀ hi_pos).2 (by simpa [mul_comm] using hmul)
    have hEq : (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) = 1 := by
      exact_mod_cast (helpful_floor_identity2 (x := x / i) hge1 hlt2)
    rw [hEq, mul_one]
  · intro i _ _
    have hcoeff' : (2 : ℝ) * ↑⌊x / ↑i / 2⌋ ≤ ↑⌊x / ↑i⌋ := by
      exact_mod_cast (helpful_floor_identity3 (x := x / i))
    have hcoeff : 0 ≤ (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) := by
      linarith
    simpa [mul_sub, mul_assoc, mul_left_comm, mul_comm] using
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hcoeff)


lemma chebyshev_error_O :
  Asymptotics.IsBigO atTop chebyshev_error log := by
  have h23 : (2 : ℝ) < 3 := by norm_num
  refine (summatory_log h23).isBigO.sub ?_
  refine (((summatory_log h23).isBigO.comp_tendsto
    (tendsto_id.atTop_div_const zero_lt_two)).const_mul_left 2).trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxhalf : 1 ≤ x / 2 := by linarith
  have hxlog : log (x / 2) ≤ log x := log_le_log_of_le (by linarith) (by linarith)
  simpa [Function.comp_apply, one_mul, norm_of_nonneg (log_nonneg hxhalf),
    norm_of_nonneg (log_nonneg (one_le_two.trans hx))] using hxlog


lemma chebyshev_trivial_upper_nat (n : ℕ) :
  chebyshev_second n ≤ n * Real.log n := by
  rw [chebyshev_second_eq_summatory, summatory_nat, ← nsmul_eq_mul]
  refine (Finset.sum_le_card_nsmul _ _ (Real.log n) ?_).trans ?_
  · intro i hi
    apply von_mangoldt_upper.trans
    simp only [Finset.mem_Icc] at hi
    exact log_le_log_of_le (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
  · simp


lemma chebyshev_trivial_upper {x : ℝ} (hx : 1 ≤ x) :
  chebyshev_second x ≤ x * log x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← chebyshev_second_eq_summatory]
  refine (chebyshev_trivial_upper_nat _).trans ?_
  refine mul_le_mul (Nat.floor_le hx₀.le)
    ?_ (log_nonneg (by
      have : (1 : ℝ) ≤ ⌊x⌋₊ := by
        exact_mod_cast (Nat.one_le_floor_iff x).2 hx
      exact this)) hx₀.le
  · exact log_le_log_of_le (by
      have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := by
        exact_mod_cast (Nat.floor_pos.mpr hx)
      exact hfloorpos) (Nat.floor_le hx₀.le)


lemma chebyshev_upper_inductive {c : ℝ} (hc : Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧ ∀ x : ℕ, chebyshev_second x ≤ 2 * c * x + C * log C := by
  have h₁ := (chebyshev_error_O.trans_isLittleO isLittleO_log_id_atTop).bound (sub_pos_of_lt hc)
  obtain ⟨C₀, hC₀⟩ := Filter.eventually_atTop.mp h₁
  let C : ℝ := max 1 C₀
  refine ⟨C, le_max_left _ _, ?_⟩
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn : (n : ℝ) ≤ C
  · rw [chebyshev_second_eq_summatory]
    refine
      (summatory_monotone_of_nonneg _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg) hn).trans
        ?_
    rw [← chebyshev_second_eq_summatory]
    refine (chebyshev_trivial_upper (le_max_left _ _)).trans ?_
    refine le_add_of_nonneg_left (mul_nonneg ?_ (Nat.cast_nonneg _))
    exact mul_nonneg zero_le_two ((Real.log_nonneg one_le_two).trans hc.le)
  · have hn : C < n := lt_of_not_ge hn
    have hn' : 0 < n := by
      refine Nat.succ_le_iff.mp ?_
      exact Nat.one_le_cast.mp ((le_max_left _ _).trans hn.le)
    have h₁ := chebyshev_upper_aux (Nat.cast_pos.mpr hn')
    rw [sub_sub, sub_le_iff_le_add] at h₁
    apply h₁.trans
    rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← Nat.cast_two,
      Nat.floor_div_eq_div, Nat.cast_two, ← add_assoc]
    have h₃ := hC₀ (n : ℝ) ((le_max_right _ _).trans hn.le)
    rw [Real.norm_eq_abs] at h₃
    replace h₃ := le_of_abs_le h₃
    have h₂ := ih (n / 2) (Nat.div_lt_self hn' one_lt_two)
    rw [← chebyshev_second_eq_summatory]
    have hsum :
        chebyshev_error (n : ℝ) + chebyshev_second (n / 2 : ℕ) + Real.log 2 * (n : ℝ) ≤
          (c - Real.log 2) * ‖(n : ℝ)‖ + (2 * c * (n / 2 : ℕ) + C * log C) +
            Real.log 2 * (n : ℝ) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_right (add_le_add h₃ h₂) (Real.log 2 * (n : ℝ))
    refine hsum.trans ?_
    have hc0 : 0 ≤ c := (Real.log_nonneg one_le_two).trans hc.le
    have hdiv : ((n / 2 : ℕ) : ℝ) ≤ n / 2 := Nat.cast_div_le
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    nlinarith


lemma chebyshev_upper_real {c : ℝ} (hc : 2 * Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧
    Asymptotics.IsBigOWith 1 atTop chebyshev_second (fun x ↦ c * x + C * log C) := by
  have hc' : Real.log 2 < c / 2 := by
    nlinarith
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_inductive hc'
  refine ⟨C, hC₁, ?_⟩
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨0, ?_⟩
  intro x hx
  rw [Real.norm_of_nonneg (chebyshev_second_nonneg x), chebyshev_second_eq_summatory,
    summatory_eq_floor, ← chebyshev_second_eq_summatory, one_mul]
  refine (hC ⌊x⌋₊).trans (le_trans ?_ (le_abs_self _))
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 ≤ c := by nlinarith
  have hmul : c * (⌊x⌋₊ : ℝ) ≤ c * x := mul_le_mul_of_nonneg_left hfloor hc0
  have hEq : 2 * (c / 2) * (⌊x⌋₊ : ℝ) = c * (⌊x⌋₊ : ℝ) := by ring
  simpa [hEq, add_assoc, add_left_comm, add_comm] using add_le_add_right hmul (C * log C)


lemma chebyshev_upper_explicit {c : ℝ} (hc : 2 * Real.log 2 < c) :
  Asymptotics.IsBigOWith c atTop chebyshev_second id := by
  let c' : ℝ := Real.log 2 + c / 2
  have hc'₁ : c' < c := by
    dsimp [c']
    nlinarith
  have hc'₂ : 2 * Real.log 2 < c' := by
    dsimp [c']
    nlinarith
  have hc'₀ : 0 ≤ c' := by
    dsimp [c']
    nlinarith [Real.log_nonneg one_le_two, hc]
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_real hc'₂
  have hconst : (fun _ : ℝ ↦ C * log C) =o[atTop] id := by
    exact (isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop)
  have hmain : Asymptotics.IsBigOWith c atTop (fun x ↦ c' * x + C * log C) id := by
    have hc'₁' : ‖c'‖ < c := by
      simpa [Real.norm_of_nonneg hc'₀] using hc'₁
    simpa [c'] using
      (Asymptotics.isBigOWith_const_mul_self c' id atTop).add_isLittleO hconst hc'₁'
  exact (hC.trans hmain zero_le_one).congr_const (one_mul c)


lemma chebyshev_upper : Asymptotics.IsBigO atTop chebyshev_second id := by
  exact (chebyshev_upper_explicit (lt_add_one _)).isBigO


lemma is_O_sum_one_of_summable {f : ℕ → ℝ} (hf : Summable f) :
  Asymptotics.IsBigO atTop (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
    (fun _ ↦ (1 : ℝ)) := by
  simpa using hf.hasSum.tendsto_sum_nat.isBigO_one ℝ


lemma log_le_thing {x : ℝ} (hx : 1 ≤ x) :
  log x ≤ x^(1/2 : ℝ) - x^(-1/2 : ℝ) := by
  set f : ℝ → ℝ := log
  set g : ℝ → ℝ := fun x ↦ x^(1 / 2 : ℝ) - x^(-1 / 2 : ℝ)
  set f' : ℝ → ℝ := Inv.inv
  set g' : ℝ → ℝ := fun x ↦ 1 / 2 * x^(-3 / 2 : ℝ) + 1 / 2 * x^(-1 / 2 : ℝ)
  suffices h : ∀ y ∈ Icc (1 : ℝ) x, f y ≤ g y by
    exact h x ⟨hx, le_rfl⟩
  have f_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt f (f' y) (Ici y) y := by
    intro y hy
    exact (hasDerivAt_log (zero_lt_one.trans_le hy.1).ne').hasDerivWithinAt
  have g_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt g (g' y) (Ici y) y := by
    intro y hy
    have hy' : 0 < y := zero_lt_one.trans_le hy.1
    change HasDerivWithinAt _ (_ + _) _ _
    rw [add_comm, ← sub_neg_eq_add, neg_mul_eq_neg_mul]
    refine HasDerivWithinAt.sub ?_ ?_
    · have hpow : (2⁻¹ : ℝ) - 1 = -1 / 2 := by norm_num
      simpa [Set.Ici, id, one_mul, hpow] using
        ((hasDerivWithinAt_id y (Set.Ici y)).rpow_const
          (p := (1 / 2 : ℝ)) (Or.inl hy'.ne'))
    · have hpow : (-1 / 2 : ℝ) - 1 = -3 / 2 := by norm_num
      have hpow' : (-2⁻¹ : ℝ) - 1 = -3 / 2 := by norm_num
      have hcoef : (-1 / 2 : ℝ) = -2⁻¹ := by norm_num
      have hderiv :=
        ((hasDerivWithinAt_id y (Set.Ici y)).rpow_const
          (p := (-1 / 2 : ℝ)) (Or.inl hy'.ne'))
      simpa [Set.Ici, id, one_mul, hpow, hpow', hcoef, neg_mul, mul_assoc] using hderiv
  have hmain :=
    image_le_of_deriv_right_le_deriv_boundary
      (f := f) (f' := f') (a := 1) (b := x)
      (continuousOn_log.mono fun y hy ↦ (zero_lt_one.trans_le hy.1).ne')
      f_deriv
      (by simp [f])
      ((continuousOn_id.rpow_const (by simp)).sub
        (continuousOn_id.rpow_const fun y hy ↦ Or.inl (zero_lt_one.trans_le hy.1).ne'))
      g_deriv
      (by
        intro y hy
        dsimp [f', g']
        rw [← mul_add, mul_comm, ← div_eq_mul_one_div,
          le_div_iff₀ (show (0 : ℝ) < 2 by norm_num), ← sub_nonneg, ← Real.rpow_neg_one]
        convert sq_nonneg (y^(-1 / 4 : ℝ) - y^(-3 / 4 : ℝ)) using 1
        have hy' : 0 < y := zero_lt_one.trans_le hy.1
        rw [sub_sq, ← Real.rpow_natCast, ← Real.rpow_natCast, Nat.cast_two,
          ← Real.rpow_mul hy'.le, mul_assoc, ← Real.rpow_add hy', ← Real.rpow_mul hy'.le]
        norm_num
        ring)
  intro y hy
  exact hmain hy


lemma log_div_sq_sub_le {x : ℝ} (hx : 1 < x) :
  log x * ((x⁻¹)^2 / (1 - x⁻¹)) ≤ x^(-3/2 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx' : x ≠ 0 := hx0.ne'
  have hden : 0 < x * (x - 1) := by nlinarith
  have hrewrite : (x⁻¹)^2 / (1 - x⁻¹) = 1 / (x * (x - 1)) := by
    field_simp [hx']
  rw [hrewrite, ← div_eq_mul_one_div]
  rw [div_le_iff₀ hden]
  calc
    log x ≤ x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ) := log_le_thing hx.le
    _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by
      have hx1 : x ^ (-3 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
        calc
          x ^ (-3 / 2 : ℝ) * x = x ^ (-3 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-3 / 2 : ℝ) 1]; norm_num
      have hx2 : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
        calc
          x ^ (-1 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-1 / 2 : ℝ) 1]; norm_num
      calc
        x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ)
            = x ^ (-1 / 2 : ℝ) * x - x ^ (-1 / 2 : ℝ) := by rw [hx2]
        _ = x ^ (-1 / 2 : ℝ) * (x - 1) := by ring
        _ = (x ^ (-3 / 2 : ℝ) * x) * (x - 1) := by rw [hx1]
        _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by ring

lemma sum_prime_powers' {M : Type*} [AddCommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.sum_sigma', eq_comm]
  refine Finset.sum_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp


lemma sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [sum_prime_powers']
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.sum_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

theorem geom_sum_Ico'_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α} (hx₀ : 0 ≤ x) (hx₁ : x < 1) {m n : ℕ} (_hmn : m ≤ n) :
  ∑ i ∈ Finset.Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  exact geom_sum_Ico_le_of_lt_one hx₀ hx₁


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
      ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p / (p : ℝ) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [h₁, h₂, sum_prime_powers, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  simp only [Finset.mem_Icc, Nat.cast_pow, and_imp]
  intro p hp₁ hp₂
  split_ifs with hp
  · have hp₃ : (p : ℝ) ≤ x := (Nat.le_floor_iff' hp.ne_zero).1 hp₂
    have hInsert :
        insert 1 (filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊)) =
          filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 1 ⌊x⌋₊) := by
      rw [Finset.Icc_eq_insert_Icc_succ (hp₁.trans hp₂), filter_insert, pow_one, if_pos]
      exact hp₃
    have hnotmem : 1 ∉ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊) := by
      simp
    rw [← hInsert, Finset.sum_insert hnotmem, add_comm, pow_one, pow_one]
    have hcancel :
        (∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ)) +
            Λ p / (p : ℝ) - Λ p / (p : ℝ) =
          ∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ) := by
      ring
    rw [hcancel]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans ?_
    · intro i hi hmem
      exact abs_nonneg _
    have hsum :
        (∑ i ∈ Icc 2 ⌊x⌋₊, |Λ (p ^ i) / (p ^ i : ℝ)|) =
          ∑ i ∈ Icc 2 ⌊x⌋₊, Λ p / (p ^ i : ℝ) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [ArithmeticFunction.vonMangoldt_apply_pow
          ((zero_lt_two.trans_le (Finset.mem_Icc.mp hk).1).ne'), abs_div,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_pow, Nat.abs_cast]
    rw [hsum, ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp only [div_eq_mul_inv, ← mul_sum, ← inv_pow]
    refine le_trans ?_ (log_div_sq_sub_le (by exact_mod_cast hp.one_lt))
    rw [show Finset.Icc 2 ⌊x⌋₊ = Finset.Ico 2 (⌊x⌋₊ + 1) by
      ext i
      simp]
    refine mul_le_mul_of_nonneg_left (geom_sum_Ico'_le ?_ ?_ ?_) ?_
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    · exact Nat.succ_le_succ (hp₁.trans hp₂)
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · rw [abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _


lemma is_O_von_mangoldt_div_self_sub_log_div_self :
  Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ -
        ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p * (p : ℝ)⁻¹)
    (fun _ : ℝ ↦ (1 : ℝ)) := by
  let g : ℝ → ℝ := fun x ↦ Finset.sum (range (⌊x⌋₊ + 1)) (fun n ↦ (n : ℝ) ^ (-3 / 2 : ℝ))
  have hbound : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ)‖ ≤ ‖g x‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_von_mangoldt_div_self_sub_log_div_self_le (x := x)).trans ?_
    refine le_trans ?_ (le_abs_self _)
    dsimp [g]
    rw [range_eq_Ico]
    exact Finset.sum_mono_set_of_nonneg (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Icc_subset_Icc_left zero_le_one)
  have hbound' : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹‖ ≤ 1 * ‖g x‖ := by
    intro x
    simpa [g, div_eq_mul_inv, one_mul] using hbound x
  refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall hbound')).trans ?_
  refine (is_O_sum_one_of_summable ((Real.summable_nat_rpow).2 (by norm_num))).comp_tendsto ?_
  exact (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop


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
  suffices h :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦ x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ - x * log x)
        (fun x ↦ x) by
    refine ((isBigO_refl (fun x : ℝ ↦ x⁻¹) atTop).mul h).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← mul_sub, inv_mul_cancel_left₀ hx.ne']
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [inv_mul_cancel₀ hx.ne']
  refine summatory_log_sub.symm.triangle ?_
  have h₁ := (summatory_log (lt_add_one 2)).isBigO
  refine ((h₁.trans isLittleO_log_id_atTop.isBigO).sub (isBigO_refl _ _)).congr_left ?_
  intro x
  dsimp [summatory]
  ring


lemma prime_summatory_one_eq_prime_summatory_two {M : Type*} [AddCommMonoid M] (a : ℕ → M) :
  prime_summatory a 1 = prime_summatory a 2 := by
  ext x
  rw [prime_summatory, prime_summatory]
  refine (Finset.sum_subset_zero_on_sdiff
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_left one_le_two))
    (fun y hy => ?_) (fun _ _ => rfl)).symm
  rcases Finset.mem_sdiff.mp hy with ⟨hy1, hy2⟩
  rcases Finset.mem_filter.mp hy1 with ⟨hyIcc, hyPrime⟩
  exact False.elim <| hy2 <|
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hyPrime.two_le, (Finset.mem_Icc.mp hyIcc).2⟩, hyPrime⟩


lemma log_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ Real.log p / p) 1 x - log x)
    (fun _ ↦ (1 : ℝ)) := by
  exact is_O_von_mangoldt_div_self_sub_log_div_self.symm.triangle is_O_von_mangoldt_div_self


lemma prime_counting_le_self (x : ℕ) : π x ≤ x := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have :
      (Finset.range (x + 1)).filter Nat.Prime ⊆ Finset.Ioc 0 x := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_Ioc.mpr ⟨hn.2.pos, Nat.lt_succ_iff.mp hn.1⟩
  exact (Finset.card_le_card this).trans (by simp)



end

end ChebyshevPsiLogHarmonicBound
