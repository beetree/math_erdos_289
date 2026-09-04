module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import SolveMath.Corpus.NumberTheory.UnitFractionDensities
public import SolveMath.Corpus.NumberTheory.UnitFractionSubsumResults.Basic
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.Basic
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.ExponentialSums
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.MajorArcs
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.CircleMethod
public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.Basic
public import SolveMath.Corpus.NumberTheory.ReciprocalSumLiuSawhneySupport.SmoothPrimePowerFactorization

@[expose] public section


namespace PrimePowerLCMTelescope



/-!
# LCM increments and the small-prime-power telescope

For a prime power `q = p ^ e`, the least common multiple of `1, ..., q`
acquires exactly one new factor `p` at `q`.  At every other positive integer
the least common multiple is unchanged.  These two facts turn the cost of
Martin's small-prime-power eliminations into an exact telescoping sum.
-/

open Filter Finset Asymptotics
open SmoothPrimePowerFactorization
open scoped BigOperators Topology

noncomputable section

/-- A finite set of positive naturals has nonzero LCM. -/
lemma lcm_ne_zero_of_zero_not_mem {A : Finset ℕ} (hA : 0 ∉ A) : A.lcm id ≠ 0 := by
  rw [Finset.lcm_ne_zero_iff]
  simpa using hA

/-- Alias for the Chebyshev psi function used in the rough-counting estimates. -/
abbrev chebyshev_second : ℝ → ℝ := Chebyshev.psi

lemma chebyshev_second_nonneg (x : ℝ) : 0 ≤ chebyshev_second x :=
  Chebyshev.psi_nonneg x

/-- Reciprocal sums are nonnegative. -/
lemma rec_sum_nonneg (A : Finset ℕ) : 0 ≤ UnitFractions.rec_sum A := by
  simpa [UnitFractions.rec_sum] using
    Finset.sum_nonneg (fun (i : ℕ) _ => div_nonneg zero_le_one (show (0 : ℚ) ≤ (i : ℚ) by exact_mod_cast Nat.zero_le i))

/-- Logarithm of the natural embedding tends to infinity. -/
lemma tendsto_log_coe_at_top :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private lemma prime_log_pow_sub_one {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    p.log (p ^ e - 1) = e - 1 := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    have hexp : e - 1 < e := Nat.sub_lt hepos (by omega)
    have hpows : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt hexp
    omega
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    have hexp : e - 1 + 1 = e := by omega
    rw [hexp]
    exact Nat.sub_lt (pow_pos hp.pos e) (by omega)

private lemma prime_log_pow_eq_log_pred_of_ne {p e r : ℕ}
    (hp : p.Prime) (he : e ≠ 0) (hr : r.Prime) (hrp : r ≠ p) :
    r.log (p ^ e) = r.log (p ^ e - 1) := by
  have hq2 : 2 ≤ p ^ e := by
    exact IsPrimePow.two_le (hp.isPrimePow.pow he)
  have hpred : p ^ e - 1 ≠ 0 := by omega
  have hsucc : p ^ e - 1 + 1 = p ^ e := by omega
  symm
  rw [← hsucc]
  apply (Nat.log_eq_log_succ_iff hr.one_lt hpred).2
  intro hpow
  rw [hsucc] at hpow
  have hlog : r.log (p ^ e) ≠ 0 := by
    intro hz
    simp [hz] at hpow
    omega
  have hrdiv : r ∣ p ^ e := by
    rw [← hpow]
    exact dvd_pow_self r hlog
  exact hrp (Nat.prime_eq_prime_of_dvd_pow hr hp hrdiv)

/-- At a prime power `p ^ e`, the initial LCM acquires exactly one new factor
`p`. -/
theorem initialLcm_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    initialLcm (p ^ e) = p * initialLcm (p ^ e - 1) := by
  apply Nat.eq_of_factorization_eq
  · simp [initialLcm]
  · exact mul_ne_zero hp.ne_zero (by simp [initialLcm])
  · intro r
    by_cases hr : r.Prime
    · rw [show initialLcm (p ^ e) = Nat.lcmUpto (p ^ e) by rfl]
      rw [show initialLcm (p ^ e - 1) = Nat.lcmUpto (p ^ e - 1) by rfl]
      rw [Nat.factorization_lcmUpto (p ^ e) hr,
        Nat.factorization_mul hp.ne_zero (Nat.lcmUpto_ne_zero (p ^ e - 1))]
      simp only [Finsupp.add_apply]
      rw [Nat.factorization_lcmUpto (p ^ e - 1) hr]
      by_cases hrp : r = p
      · subst r
        rw [Nat.log_pow hp.one_lt, prime_log_pow_sub_one hp he]
        simp [hp]
        omega
      · rw [prime_log_pow_eq_log_pred_of_ne hp he hr hrp]
        simp [hp.factorization, hrp]
    · simp [Nat.factorization_eq_zero_of_not_prime, hr]

/-- Away from prime powers, adjoining the right endpoint does not change the
initial LCM. -/
theorem initialLcm_eq_pred_of_not_isPrimePow {q : ℕ} (hq : ¬ IsPrimePow q) :
    initialLcm q = initialLcm (q - 1) := by
  by_cases hq0 : q = 0
  · subst q
    simp [initialLcm]
  by_cases hq1 : q = 1
  · subst q
    simp [initialLcm]
  have hq2 : 2 ≤ q := by omega
  have hpred : q - 1 ≠ 0 := by omega
  have hsucc : q - 1 + 1 = q := by omega
  apply Nat.eq_of_factorization_eq
  · simp [initialLcm]
  · simp [initialLcm]
  · intro r
    by_cases hr : r.Prime
    · rw [show initialLcm q = Nat.lcmUpto q by rfl]
      rw [show initialLcm (q - 1) = Nat.lcmUpto (q - 1) by rfl]
      rw [Nat.factorization_lcmUpto q hr,
        Nat.factorization_lcmUpto (q - 1) hr]
      symm
      rw [← hsucc]
      apply (Nat.log_eq_log_succ_iff hr.one_lt hpred).2
      intro hpow
      rw [hsucc] at hpow
      have hlog : r.log q ≠ 0 := by
        intro hz
        simp [hz] at hpow
        omega
      apply hq
      rw [← hpow]
      exact hr.isPrimePow.pow hlog
    · simp [Nat.factorization_eq_zero_of_not_prime, hr]

/-- The LCM increment at `p ^ e` is equivalently a difference of two unit
fractions. -/
theorem prime_pow_cost_identity {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    (((p - 1 : ℕ) : ℚ) / initialLcm (p ^ e)) =
      (1 : ℚ) / initialLcm (p ^ e - 1) -
        (1 : ℚ) / initialLcm (p ^ e) := by
  rw [initialLcm_prime_pow hp he]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hL0 : (initialLcm (p ^ e - 1) : ℚ) ≠ 0 := by
    exact_mod_cast (show initialLcm (p ^ e - 1) ≠ 0 by simp [initialLcm])
  push_cast [Nat.cast_sub hp.one_le]
  field_simp

/-- The cost attached to a prime power.  It will only be summed at arguments
which satisfy `IsPrimePow`. -/
def primePowerCost (q : ℕ) : ℚ :=
  ((q.minFac - 1 : ℕ) : ℚ) / initialLcm q

/-- The accumulated cost of the prime powers at most `lo`. -/
def smallPrimePowerCost (lo : ℕ) : ℚ :=
  (primePowersUpTo lo).sum primePowerCost

lemma primePowerCost_eq_sub {q : ℕ} (hq : IsPrimePow q) :
    primePowerCost q =
      (1 : ℚ) / initialLcm (q - 1) - (1 : ℚ) / initialLcm q := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp hq
  simpa [primePowerCost, hp.pow_minFac (ne_of_gt he)] using
    prime_pow_cost_identity hp (ne_of_gt he)

private lemma primePowersUpTo_eq_insert_pred {q : ℕ} (hq : IsPrimePow q) :
    primePowersUpTo q = insert q (primePowersUpTo (q - 1)) := by
  have hqnot : q ∉ primePowersUpTo (q - 1) := by
    intro hmem
    have hle := (mem_primePowersUpTo.mp hmem).2
    have hqpos := hq.pos
    omega
  ext t
  simp only [mem_primePowersUpTo, Finset.mem_insert]
  constructor
  · rintro ⟨htpp, htq⟩
    by_cases ht : t = q
    · exact Or.inl ht
    · exact Or.inr ⟨htpp, by omega⟩
  · rintro (rfl | ⟨htpp, htq⟩)
    · exact ⟨hq, le_rfl⟩
    · exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩

private lemma primePowersUpTo_eq_pred {q : ℕ} (hq : ¬ IsPrimePow q) :
    primePowersUpTo q = primePowersUpTo (q - 1) := by
  ext t
  simp only [mem_primePowersUpTo]
  constructor
  · rintro ⟨htpp, htq⟩
    exact ⟨htpp, by
      by_cases ht : t = q
      · exact False.elim (hq (ht ▸ htpp))
      · omega⟩
  · rintro ⟨htpp, htq⟩
    exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩

/-- Exact telescope for all small-prime-power costs. -/
theorem smallPrimePowerCost_eq (lo : ℕ) :
    smallPrimePowerCost lo =
      1 - (1 : ℚ) / initialLcm lo := by
  induction lo with
  | zero => simp [smallPrimePowerCost, primePowersUpTo, initialLcm]
  | succ n ih =>
      by_cases hq : IsPrimePow (n + 1)
      · have hnot : n + 1 ∉ primePowersUpTo n := by
          rw [mem_primePowersUpTo]
          omega
        have hset : primePowersUpTo (n + 1) =
            insert (n + 1) (primePowersUpTo n) := by
          simpa only [Nat.add_sub_cancel] using primePowersUpTo_eq_insert_pred hq
        rw [smallPrimePowerCost, hset, Finset.sum_insert hnot]
        rw [← smallPrimePowerCost, ih, primePowerCost_eq_sub hq]
        simp only [Nat.add_sub_cancel]
        ring
      · have hset : primePowersUpTo (n + 1) = primePowersUpTo n := by
          simpa only [Nat.add_sub_cancel] using primePowersUpTo_eq_pred hq
        rw [smallPrimePowerCost, hset]
        rw [← smallPrimePowerCost, ih,
          initialLcm_eq_pred_of_not_isPrimePow hq]
        simp only [Nat.add_sub_cancel]

/-- The one-step form of the telescope, arranged for direct use in a strong
induction which descends from a prime power `q` to a value below `q`. -/
theorem primePowerCost_add_smallPrimePowerCost_pred {q : ℕ}
    (hq : IsPrimePow q) :
    primePowerCost q + smallPrimePowerCost (q - 1) =
      smallPrimePowerCost q := by
  rw [primePowerCost_eq_sub hq, smallPrimePowerCost_eq,
    smallPrimePowerCost_eq]
  ring

lemma primePowerCost_nonneg (q : ℕ) : 0 ≤ primePowerCost q := by
  rw [primePowerCost]
  exact div_nonneg (by positivity) (by positivity)

theorem smallPrimePowerCost_mono : Monotone smallPrimePowerCost := by
  intro x y hxy
  rw [smallPrimePowerCost, smallPrimePowerCost]
  exact Finset.sum_le_sum_of_subset_of_nonneg (primePowersUpTo_mono hxy)
    (fun q _ _ ↦ primePowerCost_nonneg q)

/-- Budget inequality for a strict descent `q' < q`. -/
theorem primePowerCost_add_smallPrimePowerCost_of_lt {q' q : ℕ}
    (hq' : q' < q) (hq : IsPrimePow q) :
    primePowerCost q + smallPrimePowerCost q' ≤
      smallPrimePowerCost q := by
  calc
    primePowerCost q + smallPrimePowerCost q' ≤
        primePowerCost q + smallPrimePowerCost (q - 1) := by
      have hmono : smallPrimePowerCost q' ≤ smallPrimePowerCost (q - 1) :=
        smallPrimePowerCost_mono (show q' ≤ q - 1 by omega)
      linarith
    _ = smallPrimePowerCost q :=
      primePowerCost_add_smallPrimePowerCost_pred hq

/-- The total small-prime-power cost is strictly less than one. -/
theorem smallPrimePowerCost_lt_one (lo : ℕ) :
    smallPrimePowerCost lo < 1 := by
  rw [smallPrimePowerCost_eq]
  have hLpos : (0 : ℚ) < initialLcm lo := by
    exact_mod_cast (Nat.pos_of_ne_zero (by simp [initialLcm] : initialLcm lo ≠ 0))
  have hinvpos : (0 : ℚ) < 1 / initialLcm lo := div_pos zero_lt_one hLpos
  linarith

/-- Any collection of distinct prime powers below the cutoff has total cost
strictly below one.  This is the subset form useful when a descent visits only
some of the available prime powers. -/
theorem sum_primePowerCost_lt_one {A : Finset ℕ} {lo : ℕ}
    (hA : A ⊆ primePowersUpTo lo) :
    A.sum primePowerCost < 1 := by
  have hle : A.sum primePowerCost ≤ smallPrimePowerCost lo := by
    rw [smallPrimePowerCost]
    exact Finset.sum_le_sum_of_subset_of_nonneg hA
      (fun q _ _ ↦ primePowerCost_nonneg q)
  exact hle.trans_lt (smallPrimePowerCost_lt_one lo)

end




/-!
# Exact finite correction and cardinality padding

This file isolates the algebraic part of Martin's exact-correction argument for
the small-prime-power stage.  All reciprocal sums here are rational.  The
analytic construction converts its error into a rational number, so this loses
no information and makes divisibility arguments available.

The final quantitative bound on the largest denominator requires Martin's
prime-power elimination lemmas.  The results below provide the exact
telescoping identity, the odd-prime inverse-pair construction, and the
displayed-fraction cancellation identities used by those lemmas.
-/

open Finset
open scoped BigOperators

noncomputable section

/-- The elementary two-term split used to increase the cardinality of an
Egyptian representation by one. -/
theorem unitFraction_split (n : ℕ) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + 1 : ℕ) + 1 / (n * (n + 1) : ℕ) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hn10 : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- A finite version of the telescoping split.

For `m = 1` this is `unitFraction_split`.  In Martin's padding step it replaces
one denominator `n` by `m + 1` unit fractions while preserving the sum.
-/
theorem unitFraction_telescoping (n m : ℕ) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + m : ℕ) +
      ∑ j ∈ range m, (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) := by
  have hterm : ∀ j : ℕ,
      (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) =
        1 / (n + j : ℕ) - 1 / (n + j + 1 : ℕ) := by
    intro j
    have hj : (0 : ℚ) < n + j := by exact_mod_cast Nat.add_pos_left hn j
    have hj1 : (0 : ℚ) < n + j + 1 := by positivity
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  have htel := sum_range_sub' (fun j : ℕ ↦ (1 : ℚ) / (n + j : ℕ)) m
  simpa [Nat.add_assoc] using congrArg (fun x : ℚ ↦ 1 / (n + m : ℕ) + x) htel.symm

/-! ## The inverse-pair core of the odd-prime case -/

/-- Over a prime field of cardinality at least five, every residue is a sum
of the inverses of two distinct units.

This is the finite-field core of Martin's odd prime-power inverse-pair lemma.
The three excluded inverse residues are `0`, `c`, and `c / 2`: avoiding them
ensures that both summands are nonzero and different. -/
theorem exists_distinct_inverse_pair_mod_prime (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (c : ZMod p) :
    ∃ x y : ZMod p,
      IsUnit x ∧ IsUnit y ∧ x ≠ y ∧ x⁻¹ + y⁻¹ = c := by
  let _ : Fact p.Prime := ⟨hp⟩
  let bad : Finset (ZMod p) := {0, c, c / 2}
  have hbadcard : bad.card ≤ 3 := by
    exact Finset.card_le_three
  have hbadne : bad ≠ univ := by
    intro hbad
    have hcard : bad.card = p := by
      rw [hbad]
      simp
    omega
  have hnotall : ¬ ∀ u : ZMod p, u ∈ bad := by
    intro hall
    exact hbadne (Finset.eq_univ_iff_forall.mpr hall)
  push Not at hnotall
  obtain ⟨u, hu⟩ := hnotall
  have hu0 : u ≠ 0 := by
    intro h
    apply hu
    simp [bad, h]
  have huc : u ≠ c := by
    intro h
    apply hu
    simp [bad, h]
  have huhalf : u ≠ c / 2 := by
    intro h
    apply hu
    simp [bad, h]
  let v : ZMod p := c - u
  have hv0 : v ≠ 0 := by
    intro h
    apply huc
    dsimp [v] at h
    exact sub_eq_zero.mp h |>.symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have huv : u ≠ v := by
    intro huv
    apply huhalf
    rw [eq_div_iff htwo]
    dsimp [v] at huv
    have hc : u + u = c := by
      calc
        u + u = (c - u) + u := congrArg (fun z : ZMod p ↦ z + u) huv
        _ = c := by ring
    calc
      u * 2 = u + u := by ring
      _ = c := hc
  refine ⟨u⁻¹, v⁻¹, (isUnit_iff_ne_zero.mpr ?_),
    (isUnit_iff_ne_zero.mpr ?_), ?_, ?_⟩
  · simpa using (inv_ne_zero hu0)
  · simpa using (inv_ne_zero hv0)
  · exact fun h ↦ huv (inv_inj.mp h)
  · simp [v]

/-- Source-faithful pigeonhole core of Martin's Lemma 14 for primes at least
five.  The numbers `s,t` are the small positive complements of the desired
integers near a prime power. -/
theorem exists_inverse_pair_complements (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (a : ZMod p) :
    ∃ s t : ℕ,
      1 ≤ s ∧ s ≤ (p + 3) / 2 ∧
      1 ≤ t ∧ t ≤ (p + 3) / 2 ∧
      s ≠ t ∧
      (-((s : ℕ) : ZMod p))⁻¹ + (-((t : ℕ) : ZMod p))⁻¹ = a := by
  let _ : Fact p.Prime := ⟨hp⟩
  let h : ℕ := (p + 3) / 2
  let D : Finset ℕ := Icc 1 h
  let f : ℕ → ZMod p := fun s ↦ (-((s : ℕ) : ZMod p))⁻¹
  let A : Finset (ZMod p) := D.image f
  let B : Finset (ZMod p) := A.image fun x ↦ a - x
  have hpne2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hpne2
  have heven : Even (p + 3) := by
    rcases hpodd with ⟨w, hw⟩
    refine ⟨w + 2, ?_⟩
    omega
  have htwoh : 2 * h = p + 3 := by
    exact Nat.two_mul_div_two_of_even heven
  have hltp : h < p := by
    dsimp [h]
    omega
  have hDcard : D.card = h := by
    simp [D]
  have hfinj : Set.InjOn f D := by
    intro s hs t ht hst
    have hsD := Finset.mem_Icc.mp hs
    have htD := Finset.mem_Icc.mp ht
    have hcast : (s : ZMod p) = (t : ZMod p) := by
      apply neg_injective
      exact inv_inj.mp hst
    have hmod : s ≡ t [MOD p] :=
      (ZMod.natCast_eq_natCast_iff s t p).mp hcast
    exact hmod.eq_of_lt_of_lt (hsD.2.trans_lt hltp) (htD.2.trans_lt hltp)
  have hAcard : A.card = h := by
    change (D.image f).card = h
    rw [Finset.card_image_iff.mpr hfinj, hDcard]
  have hBcard : B.card = h := by
    change (A.image (fun x ↦ a - x)).card = h
    rw [Finset.card_image_iff.mpr, hAcard]
    intro x _ y _ hxy
    exact sub_right_injective hxy
  have hunion : (A ∪ B).card ≤ p := by
    simpa [ZMod.card] using Finset.card_le_univ (A ∪ B)
  have hinter : 3 ≤ (A ∩ B).card := by
    have hcount := Finset.card_inter_add_card_union A B
    rw [hAcard, hBcard] at hcount
    omega
  have hexists : ∃ r ∈ A ∩ B, r ≠ a / 2 := by
    by_contra hnone
    push Not at hnone
    have hsub : A ∩ B ⊆ {a / 2} := by
      intro r hr
      simpa using hnone r hr
    have hsmall := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hsmall
    omega
  obtain ⟨r, hr, hrhalf⟩ := hexists
  obtain ⟨s, hsD, hsr⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hr).1
  obtain ⟨x, hxA, hxr⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hr).2
  obtain ⟨t, htD, htx⟩ := Finset.mem_image.mp hxA
  have hsum : f s + f t = a := by
    rw [hsr, htx]
    exact ((sub_eq_iff_eq_add).mp hxr).symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have hst : s ≠ t := by
    intro hst
    subst t
    have hfxr : f s = r := hsr
    have hfx : f s = x := htx
    apply hrhalf
    rw [← hfxr, ← hfx] at hxr
    rw [← hfxr, eq_div_iff htwo, mul_two]
    exact ((sub_eq_iff_eq_add).mp hxr).symm
  rcases Finset.mem_Icc.mp hsD with ⟨hs1, hsh⟩
  rcases Finset.mem_Icc.mp htD with ⟨ht1, hth⟩
  exact ⟨s, t, hs1, hsh, ht1, hth, hst, hsum⟩

/-- Martin's Lemma 14 for prime powers whose underlying prime is at least
five.  The inverse congruence is modulo `p`, exactly as used to remove one
power of `p` from the reduced denominator. -/
theorem martin_lemma14_of_five_le {p ν : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hν : 0 < ν) (a : ZMod p) :
    ∃ m₁ m₂ : ℕ,
      (p ^ ν - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < p ^ ν ∧
      ¬ p ∣ m₁ * m₂ ∧
      ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹) = a := by
  obtain ⟨s, t, hs1, hsh, ht1, hth, hst, hsum⟩ :=
    exists_inverse_pair_complements p hp hp5 a
  let q : ℕ := p ^ ν
  let h : ℕ := (p + 3) / 2
  have hp0 : 0 < p := hp.pos
  have hpq : p ≤ q := by
    dsimp [q]
    exact Nat.le_pow hν
  have hq5 : 5 ≤ q := hp5.trans hpq
  have htwoh : 2 * h = p + 3 := by
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have heven : Even (p + 3) := by
      rcases hpodd with ⟨w, hw⟩
      exact ⟨w + 2, by omega⟩
    exact Nat.two_mul_div_two_of_even heven
  have hhp : h < p := by
    dsimp [h]
    omega
  have hsq : s ≤ q := hsh.trans ((le_of_lt hhp).trans hpq)
  have htq : t ≤ q := hth.trans ((le_of_lt hhp).trans hpq)
  have hqh : h ≤ q := (le_of_lt hhp).trans hpq
  have hlower : (q - 3) / 2 ≤ q - h := by
    omega
  have hqdiv : p ∣ q := by
    dsimp [q]
    exact dvd_pow_self p (Nat.ne_zero_of_lt hν)
  have hnotdvd_s : ¬ p ∣ q - s := by
    intro hdiff
    have hps : p ∣ s := by
      rw [Nat.dvd_add_iff_left hdiff]
      rw [show s + (q - s) = q by omega]
      exact hqdiv
    have hple : p ≤ s := Nat.le_of_dvd (by omega) hps
    omega
  have hnotdvd_t : ¬ p ∣ q - t := by
    intro hdiff
    have hpt : p ∣ t := by
      rw [Nat.dvd_add_iff_left hdiff]
      rw [show t + (q - t) = q by omega]
      exact hqdiv
    have hple : p ≤ t := Nat.le_of_dvd (by omega) hpt
    omega
  have hqcast : (q : ZMod p) = 0 := by
    apply (ZMod.natCast_eq_zero_iff q p).mpr
    exact hqdiv
  have hinv_s : (((q - s : ℕ) : ZMod p)⁻¹) = (-((s : ℕ) : ZMod p))⁻¹ := by
    rw [Nat.cast_sub hsq, hqcast, zero_sub]
  have hinv_t : (((q - t : ℕ) : ZMod p)⁻¹) = (-((t : ℕ) : ZMod p))⁻¹ := by
    rw [Nat.cast_sub htq, hqcast, zero_sub]
  rcases lt_or_gt_of_ne hst with hstlt | htslt
  · refine ⟨q - t, q - s, ?_, ?_, ?_, ?_, ?_⟩
    · exact hlower.trans (Nat.sub_le_sub_left hth q)
    · omega
    · omega
    · intro hdvd
      rcases (hp.dvd_mul.mp hdvd) with hdvd | hdvd
      · exact hnotdvd_t hdvd
      · exact hnotdvd_s hdvd
    · rw [hinv_t, hinv_s, add_comm]
      exact hsum
  · refine ⟨q - s, q - t, ?_, ?_, ?_, ?_, ?_⟩
    · exact hlower.trans (Nat.sub_le_sub_left hsh q)
    · omega
    · omega
    · intro hdvd
      rcases (hp.dvd_mul.mp hdvd) with hdvd | hdvd
      · exact hnotdvd_s hdvd
      · exact hnotdvd_t hdvd
    · rw [hinv_s, hinv_t]
      exact hsum

/-! ## Displayed-fraction cancellation -/

/-- If a common natural factor divides both the displayed numerator and
denominator of a rational, then the reduced denominator divides the displayed
denominator after that factor is cancelled.

This is the bridge from the modular numerator congruence in Martin's Lemmas
15 and 16 to strict descent of the reduced denominator's prime-power part. -/
theorem rat_den_dvd_div_of_eq_divInt {r : ℚ} {a : ℤ} {b p : ℕ}
    (hb : b ≠ 0) (hp : p ≠ 0) (hpb : p ∣ b)
    (hpa : (p : ℤ) ∣ a) (hr : r = Rat.divInt a b) :
    r.den ∣ b / p := by
  obtain ⟨b', rfl⟩ := hpb
  obtain ⟨a', ha'⟩ := hpa
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hrepr : r = Rat.divInt a' b' := by
    rw [hr, ha']
    push_cast
    exact Rat.divInt_mul_left hpZ
  rw [hrepr]
  have hdenZ : (((Rat.divInt a' b').den : ℕ) : ℤ) ∣ (b' : ℤ) :=
    Rat.den_dvd a' b'
  have hden : (Rat.divInt a' b').den ∣ b' := by
    exact_mod_cast hdenZ
  simpa [hp] using hden

/-- Subtracting the two unit fractions used in the odd prime-power step,
written over the displayed denominator `r.den * m₁ * m₂`.

The hypothesis `q ∣ r.den` is exactly the branch in which Lemma 15 performs
a correction.  This form exposes the numerator on which its congruence
argument proves divisibility by the underlying prime. -/
theorem sub_two_unitFractions_eq_divInt (r : ℚ) (q m₁ m₂ : ℕ)
    (hq : q ≠ 0) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)
    (hqd : q ∣ r.den) :
    r - (1 : ℚ) / (q * m₁ : ℕ) - (1 : ℚ) / (q * m₂ : ℕ) =
      Rat.divInt
        (r.num * (m₁ * m₂ : ℕ) -
          ((r.den / q) * (m₁ + m₂) : ℕ))
        (r.den * m₁ * m₂) := by
  let d : ℕ := r.den / q
  change r - (1 : ℚ) / (q * m₁ : ℕ) - (1 : ℚ) / (q * m₂ : ℕ) =
    Rat.divInt
      (r.num * (m₁ * m₂ : ℕ) - (d * (m₁ + m₂) : ℕ))
      (r.den * m₁ * m₂)
  have hden : q * d = r.den := Nat.mul_div_cancel' hqd
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hm₁Q : (m₁ : ℚ) ≠ 0 := by exact_mod_cast hm₁
  have hm₂Q : (m₂ : ℚ) ≠ 0 := by exact_mod_cast hm₂
  have hrdenQ : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hdenQ : (q : ℚ) * d = r.den := by
    exact_mod_cast hden
  rw [Rat.divInt_eq_div]
  nth_rewrite 1 [← Rat.num_div_den r]
  push_cast
  field_simp
  rw [← hdenQ]
  ring

/-- A representation whose denominators are above `A.sup id` is disjoint from
the finite set `A`. -/
theorem disjoint_of_sup_lt {A E : Finset ℕ}
    (hE : ∀ e ∈ E, A.sup id < e) : Disjoint A E := by
  rw [Finset.disjoint_left]
  intro a haA haE
  have hale : a ≤ A.sup id := Finset.le_sup (f := id) haA
  exact (not_lt_of_ge hale) (hE a haE)

/-- Joining an approximate representation to a disjoint exact correction adds
both reciprocal sums and cardinalities. -/
theorem union_correction {A E : Finset ℕ} (hdisj : Disjoint A E) :
    UnitFractions.rec_sum (A ∪ E) =
        UnitFractions.rec_sum A + UnitFractions.rec_sum E ∧
      (A ∪ E).card = A.card + E.card := by
  exact ⟨UnitFractions.rec_sum_disjoint hdisj, Finset.card_union_of_disjoint hdisj⟩

end




/-!
# Martin's two-inverse lemma

This file gives the source-faithful form of Lemma 14 in Greg Martin's
*Denser Egyptian fractions*.  If the odd prime power `q = p ^ ν` is at
least five, then every residue modulo its underlying prime is a sum of the
inverses of two distinct integers in `[(q - 3) / 2, q)`.

The prime-three case is the separate explicit construction from the paper.
For primes at least five we reuse the finite pigeonhole proof from the
exact-correction development.
-/

private theorem martin_lemma14_three {q ν : ℕ} (hν : 0 < ν)
    (hqpow : q = 3 ^ ν) (hq5 : 5 ≤ q) (a : ZMod 3) :
    ∃ m₁ m₂ : ℕ,
      (q - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < q ∧
      ¬ 3 ∣ m₁ * m₂ ∧
      ((m₁ : ZMod 3)⁻¹ + (m₂ : ZMod 3)⁻¹) = a := by
  have hν2 : 2 ≤ ν := by
    by_contra h
    have hν1 : ν = 1 := by omega
    subst ν
    norm_num [hqpow] at hq5
  have hq9 : 9 ≤ q := by
    rw [hqpow]
    exact Nat.pow_le_pow_right (n := 3) (by omega) hν2
  have hqdiv : 3 ∣ q := by
    rw [hqpow]
    exact dvd_pow_self 3 (Nat.ne_zero_of_lt hν)
  have hqcast : (q : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff q 3).2 hqdiv
  have hthree : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  have hinv_two : ((2 : ZMod 3)⁻¹) = 2 := by
    apply ZMod.inv_eq_of_mul_eq_one
    linear_combination hthree
  have hneg_one : (-((1 : ℕ) : ZMod 3)) = 2 := by
    linear_combination -hthree
  have hneg_two : (-((2 : ℕ) : ZMod 3)) = 1 := by
    linear_combination -hthree
  have hneg_four : (-((4 : ℕ) : ZMod 3)) = 2 := by
    linear_combination -2 * hthree
  have hneg_five : (-((5 : ℕ) : ZMod 3)) = 1 := by
    linear_combination -2 * hthree
  fin_cases a
  · refine ⟨q - 2, q - 1, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 2) * (q - 1) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 2) * (q - 1)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((2 : ℕ) : ZMod 3))⁻¹ + (-((1 : ℕ) : ZMod 3))⁻¹ = 0
      simp only [hneg_two, hneg_one, ZMod.inv_one, hinv_two]
      exact hthree
  · refine ⟨q - 4, q - 1, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 4) * (q - 1) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 4) * (q - 1)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 4 := (ZMod.natCast_eq_zero_iff 4 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((4 : ℕ) : ZMod 3))⁻¹ + (-((1 : ℕ) : ZMod 3))⁻¹ = 1
      simp only [hneg_four, hneg_one, hinv_two]
      linear_combination hthree
  · refine ⟨q - 5, q - 2, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 5) * (q - 2) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 5) * (q - 2)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 10 := (ZMod.natCast_eq_zero_iff 10 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((5 : ℕ) : ZMod 3))⁻¹ + (-((2 : ℕ) : ZMod 3))⁻¹ = 2
      simp only [hneg_five, hneg_two, ZMod.inv_one]
      ring

/--
Martin's Lemma 14.  The congruence in the conclusion is modulo the underlying
prime `p`, rather than modulo the prime power `q`.
-/
theorem martin_lemma14 {p q ν : ℕ} (hp : p.Prime) (hν : 0 < ν)
    (hqpow : q = p ^ ν) (hqodd : Odd q) (hq5 : 5 ≤ q) (a : ZMod p) :
    ∃ m₁ m₂ : ℕ,
      (q - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < q ∧
      ¬ p ∣ m₁ * m₂ ∧
      ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹) = a := by
  by_cases hp3 : p = 3
  · subst p
    exact martin_lemma14_three hν hqpow hq5 a
  · have hp2 : p ≠ 2 := by
      intro hp2
      subst p
      have htwo_dvd : 2 ∣ q := by
        rw [hqpow]
        exact dvd_pow_self 2 (Nat.ne_zero_of_lt hν)
      exact (Nat.not_even_iff_odd.mpr hqodd) (even_iff_two_dvd.mpr htwo_dvd)
    have hp5 : 5 ≤ p := by
      have hp_one := hp.one_lt
      have hp_odd := hp.odd_of_ne_two hp2
      rcases hp_odd with ⟨k, hk⟩
      omega
    simpa [hqpow] using
      (PrimePowerLCMTelescope.martin_lemma14_of_five_le hp hp5 hν a)





/-!
# Martin's prime-power elimination lemma

This file formalizes the bounded two-term (or one-term at the prime `2`)
denominator correction used in the exact-correction stage of the small-prime-
power argument.
-/

open Finset
open scoped BigOperators

noncomputable section

/-- Every exact prime-power part of an LCM is already an exact part of one of
the two inputs.  The exponent in an LCM is the maximum of the two exponents. -/
lemma primePowerParts_lcm_subset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primePowerParts (Nat.lcm a b) ⊆ primePowerParts a ∪ primePowerParts b := by
  intro q hq
  rcases (mem_primePowerParts (Nat.lcm_ne_zero ha hb)).mp hq with
    ⟨hqpp, hqdiv, hqcop⟩
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, k, hp, hk, rfl⟩
  have hlcmfac : (Nat.lcm a b).factorization p = k :=
    (UnitFractions.factorization_eq_iff hp (ne_of_gt hk)).mp ⟨hqdiv, hqcop⟩
  rw [Nat.factorization_lcm ha hb, Finsupp.sup_apply] at hlcmfac
  have hcases : a.factorization p = k ∨ b.factorization p = k := by
    omega
  rw [Finset.mem_union]
  rcases hcases with hafac | hbfac
  · left
    apply (mem_primePowerParts ha).mpr
    exact ⟨hp.isPrimePow.pow (ne_of_gt hk),
      (UnitFractions.factorization_eq_iff hp (ne_of_gt hk)).mpr hafac⟩
  · right
    apply (mem_primePowerParts hb).mpr
    exact ⟨hp.isPrimePow.pow (ne_of_gt hk),
      (UnitFractions.factorization_eq_iff hp (ne_of_gt hk)).mpr hbfac⟩

/-- Taking an LCM preserves a common upper bound for exact prime-power parts. -/
lemma largestPrimePowerPart_lcm_le {a b y : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha_bound : largestPrimePowerPart a ≤ y)
    (hb_bound : largestPrimePowerPart b ≤ y) :
    largestPrimePowerPart (Nat.lcm a b) ≤ y := by
  rw [largestPrimePowerPart_le_iff] at ha_bound hb_bound ⊢
  intro q hq
  rcases Finset.mem_union.mp (primePowerParts_lcm_subset ha hb hq) with hqa | hqb
  · exact ha_bound q hqa
  · exact hb_bound q hqb

/-- A positive prime power is its own largest exact prime-power part. -/
lemma largestPrimePowerPart_primePower {q : ℕ} (hq : IsPrimePow q) :
    largestPrimePowerPart q = q := by
  apply le_antisymm largestPrimePowerPart_le
  apply le_largestPrimePowerPart
  apply (mem_primePowerParts hq.ne_zero).mpr
  refine ⟨hq, dvd_rfl, ?_⟩
  rw [Nat.div_self hq.pos]
  exact (Nat.coprime_one_right_iff q).mpr trivial

/-- Multiplying a prime power by a smaller coprime factor leaves that prime
power as the largest exact prime-power part. -/
lemma largestPrimePowerPart_mul_eq_left {q m : ℕ} (hq : IsPrimePow q)
    (hm : m < q) (hcop : Nat.Coprime q m) :
    largestPrimePowerPart (q * m) = q := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hm0 : m ≠ 0 := by
    intro hm0
    subst m
    simp at hcop
    exact hq.ne_one hcop
  have hmul : Nat.lcm q m = q * m := hcop.lcm_eq_mul
  have hle : largestPrimePowerPart (q * m) ≤ q := by
    rw [← hmul]
    apply largestPrimePowerPart_lcm_le hq0 hm0
    · exact (largestPrimePowerPart_primePower hq).le
    · exact largestPrimePowerPart_le.trans (Nat.le_of_lt hm)
  apply le_antisymm hle
  apply le_largestPrimePowerPart
  apply (mem_primePowerParts (mul_ne_zero hq0 hm0)).mpr
  refine ⟨hq, dvd_mul_right q m, ?_⟩
  simpa [Nat.mul_div_cancel_left _ hq.pos] using hcop

/-- If the first input has no exact prime-power part larger than the prime
power `q`, then `q` is an exact part of its LCM with `q`. -/
lemma primePower_mem_parts_lcm_right {a q : ℕ} (ha : a ≠ 0)
    (hq : IsPrimePow q) (ha_bound : largestPrimePowerPart a ≤ q) :
    q ∈ primePowerParts (Nat.lcm a q) := by
  rcases (isPrimePow_nat_iff q).mp hq with ⟨p, ν, hp, hν, rfl⟩
  have hfac_le : a.factorization p ≤ ν := by
    by_cases hfac0 : a.factorization p = 0
    · omega
    · have hpart : p ^ a.factorization p ∈ primePowerParts a := by
        apply (mem_primePowerParts ha).mpr
        exact ⟨hp.isPrimePow.pow hfac0,
          (UnitFractions.factorization_eq_iff hp hfac0).mpr rfl⟩
      have hpw_le : p ^ a.factorization p ≤ p ^ ν :=
        (le_largestPrimePowerPart hpart).trans ha_bound
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpw_le
  have hlcm0 : Nat.lcm a (p ^ ν) ≠ 0 :=
    Nat.lcm_ne_zero ha (pow_ne_zero _ hp.ne_zero)
  apply (mem_primePowerParts hlcm0).mpr
  refine ⟨hp.isPrimePow.pow (ne_of_gt hν), ?_⟩
  apply (UnitFractions.factorization_eq_iff hp (ne_of_gt hν)).mpr
  rw [Nat.factorization_lcm ha (pow_ne_zero _ hp.ne_zero),
    Finsupp.sup_apply, hp.factorization_pow]
  simp [hfac_le]

/-- If all exact parts are at most `q`, but `q` itself does not divide the
integer, then the largest exact part is strictly smaller than `q`. -/
lemma largestPrimePowerPart_lt_of_le_of_not_dvd {n q : ℕ}
    (hq : IsPrimePow q) (hbound : largestPrimePowerPart n ≤ q)
    (hnotdvd : ¬ q ∣ n) : largestPrimePowerPart n < q := by
  by_cases hn : n < 2
  · have hempty : primePowerParts n = ∅ := primePowerParts_empty_iff.mpr hn
    simp [largestPrimePowerPart, hempty, hq.pos]
  · have hn2 : 2 ≤ n := Nat.le_of_not_gt hn
    have hmem := largestPrimePowerPart_mem hn2
    have hne : largestPrimePowerPart n ≠ q := by
      intro heq
      have hspec := (mem_primePowerParts (by omega)).mp hmem
      exact hnotdvd (heq ▸ hspec.2.1)
    omega

/-- Exact prime-power parts can only decrease on passing to a divisor. -/
lemma largestPrimePowerPart_le_of_dvd {a b : ℕ} (hb : b ≠ 0)
    (hab : a ∣ b) : largestPrimePowerPart a ≤ largestPrimePowerPart b := by
  rw [largestPrimePowerPart_le_iff]
  intro q hqa
  rcases (mem_primePowerParts (fun ha ↦ hb (zero_dvd_iff.mp (ha ▸ hab)))).mp hqa with
    ⟨hqpp, hqdiva, hqcop⟩
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, k, hp, hk, rfl⟩
  have hafac : a.factorization p = k :=
    (UnitFractions.factorization_eq_iff hp (ne_of_gt hk)).mp ⟨hqdiva, hqcop⟩
  have hfac_le : a.factorization p ≤ b.factorization p := by
    exact (Nat.factorization_le_iff_dvd
      (fun ha ↦ hb (zero_dvd_iff.mp (ha ▸ hab))) hb).mpr hab p
  let K := b.factorization p
  have hK : K ≠ 0 := by
    dsimp [K]
    omega
  have hpart : p ^ K ∈ primePowerParts b := by
    apply (mem_primePowerParts hb).mpr
    exact ⟨hp.isPrimePow.pow hK,
      (UnitFractions.factorization_eq_iff hp hK).mpr rfl⟩
  calc
    p ^ k ≤ p ^ K := Nat.pow_le_pow_right hp.pos (by simpa [K, hafac] using hfac_le)
    _ ≤ largestPrimePowerPart b := le_largestPrimePowerPart hpart

/-- A finite LCM has bounded exact prime-power parts when every member does. -/
lemma largestPrimePowerPart_finset_lcm_le {A : Finset ℕ} {q : ℕ}
    (hzero : 0 ∉ A) (hA : ∀ n ∈ A, largestPrimePowerPart n ≤ q) :
    largestPrimePowerPart (A.lcm id) ≤ q := by
  induction A using Finset.induction with
  | empty =>
      have hparts : primePowerParts 1 = ∅ := primePowerParts_empty_iff.mpr (by omega)
      simp [largestPrimePowerPart, hparts]
  | @insert n A hn ih =>
      have hn0 : n ≠ 0 := by
        intro hn0
        exact hzero (hn0 ▸ Finset.mem_insert_self n A)
      have hA0 : 0 ∉ A := fun h ↦ hzero (Finset.mem_insert_of_mem h)
      rw [Finset.lcm_insert]
      apply largestPrimePowerPart_lcm_le hn0 (lcm_ne_zero_of_zero_not_mem hA0)
      · exact hA n (Finset.mem_insert_self n A)
      · apply ih hA0
        intro m hm
        exact hA m (Finset.mem_insert_of_mem hm)

/-- The residual denominator remains `q`-smooth after subtracting a finite
sum whose displayed denominators all have largest exact part `q`. -/
lemma residual_largestPrimePowerPart_le (q : ℕ) (r : ℚ) (U : Finset ℕ)
    (hq : IsPrimePow q) (hr : largestPrimePowerPart r.den ≤ q)
    (hU : ∀ n ∈ U, largestPrimePowerPart n = q) :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q := by
  have hzero : 0 ∉ U := by
    intro h0
    have hz := hU 0 h0
    simp [largestPrimePowerPart, primePowerParts] at hz
    exact hq.ne_zero hz.symm
  have hlcm0 : U.lcm id ≠ 0 := lcm_ne_zero_of_zero_not_mem hzero
  have hUlcm : largestPrimePowerPart (U.lcm id) ≤ q := by
    apply largestPrimePowerPart_finset_lcm_le hzero
    intro n hn
    rw [hU n hn]
  let L := Nat.lcm r.den (U.lcm id)
  have hL0 : L ≠ 0 := Nat.lcm_ne_zero r.den_ne_zero hlcm0
  have hLbound : largestPrimePowerPart L ≤ q :=
    largestPrimePowerPart_lcm_le r.den_ne_zero hlcm0 hr hUlcm
  have hrec : (UnitFractions.rec_sum U).den ∣ U.lcm id :=
    recSum_den_dvd_lcm U
  have hden : (r - UnitFractions.rec_sum U).den ∣ L := by
    exact (Rat.sub_den_dvd_lcm r (UnitFractions.rec_sum U)).trans
      (lcm_dvd_lcm dvd_rfl hrec)
  exact (largestPrimePowerPart_le_of_dvd hL0 hden).trans hLbound

/-- Put a rational and two unit fractions over a common displayed
denominator.  The LCM applications below take `D = lcm r.den q`. -/
lemma two_term_residual_eq_divInt (r : ℚ) (q m₁ m₂ D : ℕ)
    (hq : q ≠ 0) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hD0 : D ≠ 0)
    (hdenD : r.den ∣ D) (hqD : q ∣ D) :
    r - ((1 : ℚ) / (q * m₁) + 1 / (q * m₂)) =
      Rat.divInt
        (r.num * (D / r.den : ℕ) * m₁ * m₂ -
          ((D / q : ℕ) * (m₁ + m₂) : ℕ))
        (D * m₁ * m₂ : ℕ) := by
  have hden0 : r.den ≠ 0 := r.den_ne_zero
  have hDden : r.den * (D / r.den) = D := Nat.mul_div_cancel' hdenD
  have hDq : q * (D / q) = D := Nat.mul_div_cancel' hqD
  have hDdenQ : (r.den : ℚ) * (D / r.den : ℕ) = D := by exact_mod_cast hDden
  have hDqQ : (q : ℚ) * (D / q : ℕ) = D := by exact_mod_cast hDq
  have hcastDen : (D : ℚ) / r.den = (D / r.den : ℕ) := by
    rw [div_eq_iff]
    · exact_mod_cast hDden.symm.trans (mul_comm _ _)
    · exact_mod_cast hden0
  have hcastQ : (D : ℚ) / q = (D / q : ℕ) := by
    rw [div_eq_iff]
    · exact_mod_cast hDq.symm.trans (mul_comm _ _)
    · exact_mod_cast hq
  rw [Rat.divInt_eq_div]
  nth_rw 1 [← r.num_div_den]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_add]
  field_simp
  simp only [Int.cast_add, Int.cast_natCast]
  ring_nf at hDdenQ hDqQ ⊢
  rw [hDdenQ]
  linear_combination ((r.den : ℚ) * m₁ + r.den * m₂) * hDqQ

/-- One-term version of the displayed-denominator identity. -/
lemma one_term_residual_eq_divInt (r : ℚ) (q m : ℕ)
    (hq : q ≠ 0) (hm : m ≠ 0) (hqd : q ∣ r.den) :
    r - (1 : ℚ) / (q * m : ℕ) =
      Rat.divInt (r.num * m - (r.den / q : ℕ)) (r.den * m) := by
  let d := r.den / q
  change r - (1 : ℚ) / (q * m : ℕ) =
    Rat.divInt (r.num * m - (d : ℕ)) (r.den * m)
  have hden : q * d = r.den := Nat.mul_div_cancel' hqd
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hdenQ : (q : ℚ) * d = r.den := by exact_mod_cast hden
  rw [Rat.divInt_eq_div]
  nth_rw 1 [← r.num_div_den]
  push_cast
  field_simp
  rw [← hdenQ]
  ring

/-- Cancelling one copy of the underlying prime from a displayed denominator
whose exact `p`-part is `p^ν` makes that prime power cease to divide. -/
lemma primePow_not_dvd_mul_div_prime {p ν q D m : ℕ} (hp : p.Prime)
    (hν : 0 < ν) (hq : q = p ^ ν) (hpart : q ∈ primePowerParts D)
    (hpm : ¬ p ∣ m) : ¬ q ∣ (D * m) / p := by
  subst q
  have hD0 : D ≠ 0 := by
    intro h
    subst D
    simp [primePowerParts] at hpart
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    exact hpm (dvd_zero p)
  have hDfac : D.factorization p = ν := by
    have hs := (mem_primePowerParts hD0).mp hpart
    exact (UnitFractions.factorization_eq_iff hp (ne_of_gt hν)).mp hs.2
  have hpD : p ∣ D := by
    exact (dvd_pow_self p (ne_of_gt hν)).trans ((mem_primePowerParts hD0).mp hpart).2.1
  have hpDm : p ∣ D * m := hpD.trans (dvd_mul_right D m)
  have hDm0 : D * m ≠ 0 := mul_ne_zero hD0 hm0
  have hB0 : (D * m) / p ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hDm0.bot_lt hpDm) hp.pos)
  have hfac : ((D * m) / p).factorization p = ν - 1 := by
    rw [Nat.factorization_div hpDm]
    simp [Nat.factorization_mul hD0 hm0, hDfac,
      Nat.factorization_eq_zero_of_not_dvd hpm, hp.factorization_self]
  intro hdvd
  have hνle : ν ≤ ((D * m) / p).factorization p :=
    (hp.pow_dvd_iff_le_factorization hB0).mp hdvd
  rw [hfac] at hνle
  omega

/-- Martin's prime-power elimination step.  The inequalities
`q^2 ≤ 5*n` and `n ≤ q^2` are the integral form of
`n ∈ [q^2/5,q^2]`. -/
theorem exists_elimination_set (q : ℕ) (hqpp : IsPrimePow q) (hq4 : 4 ≤ q)
    (r : ℚ) (hr : largestPrimePowerPart r.den ≤ q) :
    ∃ U : Finset ℕ,
      (∀ n ∈ U, q ^ 2 ≤ 5 * n ∧ n ≤ q ^ 2) ∧
      (Odd q → U.card = 2) ∧
      (Even q → U.card ≤ 1) ∧
      (∀ n ∈ U, largestPrimePowerPart n = q) ∧
      largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, ν, hp, hν, hqpow⟩
  let _ : Fact p.Prime := ⟨hp⟩
  have hq0 : q ≠ 0 := hqpp.ne_zero
  by_cases hqodd : Odd q
  · have hq5 : 5 ≤ q := by
      rcases hqodd with ⟨k, hk⟩
      omega
    let D := Nat.lcm r.den q
    have hD0 : D ≠ 0 := Nat.lcm_ne_zero r.den_ne_zero hq0
    have hdenD : r.den ∣ D := Nat.dvd_lcm_left _ _
    have hqD : q ∣ D := Nat.dvd_lcm_right _ _
    have hDpart : q ∈ primePowerParts D :=
      primePower_mem_parts_lcm_right r.den_ne_zero hqpp hr
    have hDspec := (mem_primePowerParts hD0).mp hDpart
    have hpq : p ∣ q := by
      rw [← hqpow]
      exact dvd_pow_self p (ne_of_gt hν)
    have hpe : ¬ p ∣ D / q := by
      exact hp.coprime_iff_not_dvd.mp
        (Nat.Coprime.of_dvd_left hpq hDspec.2.2)
    let C : ℤ := r.num * (D / r.den : ℕ)
    let a : ZMod p := (C : ZMod p) * ((D / q : ℕ) : ZMod p)⁻¹
    obtain ⟨m₁, m₂, hm₁lo, hm₁m₂, hm₂q, hpm, hinv⟩ :=
      martin_lemma14 hp hν hqpow.symm hqodd hq5 a
    have hm₁pos : 0 < m₁ := by
      have : 1 ≤ (q - 3) / 2 := by omega
      omega
    have hm₂pos : 0 < m₂ := hm₁pos.trans hm₁m₂
    have hpm₁ : ¬ p ∣ m₁ := fun h ↦ hpm (h.trans (dvd_mul_right m₁ m₂))
    have hpm₂ : ¬ p ∣ m₂ := fun h ↦ hpm (h.trans (dvd_mul_left m₂ m₁))
    have hcop₁ : Nat.Coprime q m₁ := by
      rw [← hqpow]
      exact (hp.coprime_pow_of_not_dvd hpm₁).symm
    have hcop₂ : Nat.Coprime q m₂ := by
      rw [← hqpow]
      exact (hp.coprime_pow_of_not_dvd hpm₂).symm
    let n₁ := q * m₁
    let n₂ := q * m₂
    have hn₁ne : n₁ ≠ n₂ := by
      dsimp [n₁, n₂]
      intro h
      exact (Nat.ne_of_lt hm₁m₂) (mul_left_cancel₀ hq0 h)
    let U : Finset ℕ := {n₁, n₂}
    have hn₁largest : largestPrimePowerPart n₁ = q := by
      exact largestPrimePowerPart_mul_eq_left hqpp (hm₁m₂.trans hm₂q) hcop₁
    have hn₂largest : largestPrimePowerPart n₂ = q := by
      exact largestPrimePowerPart_mul_eq_left hqpp hm₂q hcop₂
    have hUlargest : ∀ n ∈ U, largestPrimePowerPart n = q := by
      intro n hn
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · exact hn₁largest
      · exact hn₂largest
    have hinterval : ∀ n ∈ U, q ^ 2 ≤ 5 * n ∧ n ≤ q ^ 2 := by
      have hbase : q ≤ 5 * ((q - 3) / 2) := by
        obtain ⟨t, ht⟩ := hqodd
        omega
      have hqm₁ : q ≤ 5 * m₁ :=
        hbase.trans (Nat.mul_le_mul_left 5 hm₁lo)
      have hqm₂ : q ≤ 5 * m₂ := hqm₁.trans (Nat.mul_le_mul_left 5 hm₁m₂.le)
      intro n hn
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · dsimp [n₁]
        constructor <;> nlinarith
      · dsimp [n₂]
        constructor <;> nlinarith
    let z : ℤ := C * m₁ * m₂ - ((D / q) * (m₁ + m₂) : ℕ)
    have hecast : ((D / q : ℕ) : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpe
    have hm₁cast : (m₁ : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpm₁
    have hm₂cast : (m₂ : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpm₂
    have hzcast : (z : ZMod p) = 0 := by
      simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, Nat.cast_mul,
        Nat.cast_add]
      calc
        (C : ZMod p) * m₁ * m₂ -
            (D / q : ℕ) * ((m₁ : ZMod p) + (m₂ : ZMod p)) =
            (D / q : ℕ) * m₁ * m₂ *
              ((C : ZMod p) * ((D / q : ℕ) : ZMod p)⁻¹ -
                ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹)) := by
                  field_simp
                  ring
        _ = 0 := by rw [hinv]; simp [a]
    have hpz : (p : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzcast
    have hrepr : r - UnitFractions.rec_sum U =
        Rat.divInt z (D * m₁ * m₂) := by
      have hraw := two_term_residual_eq_divInt r q m₁ m₂ D hq0
        (ne_of_gt hm₁pos) (ne_of_gt hm₂pos) hD0 hdenD hqD
      dsimp [z, C]
      simpa [U, n₁, n₂, UnitFractions.rec_sum, hn₁ne, sub_eq_add_neg,
        add_assoc] using hraw
    have hpB : p ∣ D * m₁ * m₂ := by
      exact (hpq.trans hDspec.2.1).trans
        (dvd_mul_of_dvd_left (dvd_mul_right D m₁) m₂)
    have hdenDiv : (r - UnitFractions.rec_sum U).den ∣
        (D * (m₁ * m₂)) / p := by
      have := rat_den_dvd_div_of_eq_divInt
        (r := r - UnitFractions.rec_sum U) (a := z)
        (b := D * m₁ * m₂) (p := p)
        (mul_ne_zero (mul_ne_zero hD0 (ne_of_gt hm₁pos)) (ne_of_gt hm₂pos)) hp.ne_zero hpB hpz hrepr
      simpa [mul_assoc] using this
    have hqnotB : ¬ q ∣ (D * (m₁ * m₂)) / p :=
      primePow_not_dvd_mul_div_prime hp hν hqpow.symm hDpart hpm
    have hqnotden : ¬ q ∣ (r - UnitFractions.rec_sum U).den :=
      fun h ↦ hqnotB (h.trans hdenDiv)
    have hresle : largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q :=
      residual_largestPrimePowerPart_le q r U hqpp hr hUlargest
    refine ⟨U, hinterval, ?_, ?_, hUlargest,
      largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hresle hqnotden⟩
    · intro _
      simp [U, hn₁ne]
    · intro heven
      exact ((Nat.not_even_iff_odd.mpr hqodd) heven).elim
  · have hqeven : Even q := Nat.not_odd_iff_even.mp hqodd
    by_cases hqd : q ∣ r.den
    · -- The even correction is the single denominator `q(q-1)`.
      have hp2 : p = 2 := by
        rcases hp.eq_two_or_odd' with hp2 | hpodd
        · exact hp2
        · exfalso
          apply hqodd
          rw [← hqpow]
          exact hpodd.pow
      subst p
      have hqpow2 : q = 2 ^ ν := hqpow.symm
      have h2q : 2 ∣ q := by
        rw [hqpow2]
        exact dvd_pow_self 2 (ne_of_gt hν)
      let m := q - 1
      have hmpos : 0 < m := by dsimp [m]; omega
      have hcop : Nat.Coprime q m := by
        apply (Nat.coprime_sub_self_left (Nat.sub_le q 1)).mp
        have hsub : q - (q - 1) = 1 := by omega
        rw [hsub]
        exact (Nat.coprime_one_left_iff (q - 1)).mpr trivial
      have h2m : ¬ 2 ∣ m := by
        exact Nat.prime_two.coprime_iff_not_dvd.mp
          (Nat.Coprime.of_dvd_left h2q hcop)
      let n := q * m
      let U : Finset ℕ := {n}
      have hnlargest : largestPrimePowerPart n = q := by
        apply largestPrimePowerPart_mul_eq_left hqpp
        · dsimp [m]
          omega
        · exact hcop
      have hUlargest : ∀ x ∈ U, largestPrimePowerPart x = q := by
        intro x hx
        have hx' : x = n := by simpa [U] using hx
        rw [hx']
        exact hnlargest
      have hinterval : ∀ x ∈ U, q ^ 2 ≤ 5 * x ∧ x ≤ q ^ 2 := by
        intro x hx
        have hx' : x = n := by simpa [U] using hx
        subst x
        dsimp [n, m]
        constructor
        · have hsmall : q ≤ 5 * (q - 1) := by omega
          have := Nat.mul_le_mul_left q hsmall
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
        · have := Nat.mul_le_mul_left q (Nat.sub_le q 1)
          simpa [pow_two] using this
      have hlcm : Nat.lcm r.den q = r.den := by
        apply Nat.dvd_antisymm
        · exact Nat.lcm_dvd dvd_rfl hqd
        · exact Nat.dvd_lcm_left _ _
      have hdenpart : q ∈ primePowerParts r.den := by
        have h := primePower_mem_parts_lcm_right r.den_ne_zero hqpp hr
        rwa [hlcm] at h
      have hdenspec := (mem_primePowerParts r.den_ne_zero).mp hdenpart
      have h2den : 2 ∣ r.den := h2q.trans hqd
      have hnumcop : Nat.Coprime 2 r.num.natAbs :=
        Nat.Coprime.of_dvd_left h2den r.reduced.symm
      have hquotcop : Nat.Coprime 2 (r.den / q) :=
        Nat.Coprime.of_dvd_left h2q hdenspec.2.2
      have hnumcast : (r.num : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact fun hdiv ↦ (Nat.prime_two.coprime_iff_not_dvd.mp hnumcop)
          (Int.natCast_dvd.mp hdiv)
      have hmcast : (m : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact h2m
      have hquotcast : ((r.den / q : ℕ) : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact Nat.prime_two.coprime_iff_not_dvd.mp hquotcop
      have hnum1 : (r.num : ZMod 2) = 1 := Fin.eq_one_of_ne_zero _ hnumcast
      have hm1 : (m : ZMod 2) = 1 := Fin.eq_one_of_ne_zero _ hmcast
      have hquot1 : ((r.den / q : ℕ) : ZMod 2) = 1 :=
        Fin.eq_one_of_ne_zero _ hquotcast
      let z : ℤ := r.num * m - (r.den / q : ℕ)
      have hzcast : (z : ZMod 2) = 0 := by
        simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        rw [hnum1, hm1, hquot1]
        ring
      have h2z : (2 : ℤ) ∣ z :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp hzcast
      have hrepr : r - UnitFractions.rec_sum U =
          Rat.divInt z (r.den * m) := by
        have hraw := one_term_residual_eq_divInt r q m hq0 (ne_of_gt hmpos) hqd
        dsimp [z]
        simpa [U, n, UnitFractions.rec_sum] using hraw
      have h2B : 2 ∣ r.den * m := h2den.trans (dvd_mul_right r.den m)
      have hdenDiv : (r - UnitFractions.rec_sum U).den ∣ (r.den * m) / 2 :=
        rat_den_dvd_div_of_eq_divInt
          (r := r - UnitFractions.rec_sum U) (a := z) (b := r.den * m) (p := 2)
          (mul_ne_zero r.den_ne_zero (ne_of_gt hmpos)) (by norm_num) h2B h2z hrepr
      have hqnotB : ¬ q ∣ (r.den * m) / 2 :=
        primePow_not_dvd_mul_div_prime Nat.prime_two hν hqpow2 hdenpart h2m
      have hqnotden : ¬ q ∣ (r - UnitFractions.rec_sum U).den :=
        fun h ↦ hqnotB (h.trans hdenDiv)
      have hresle : largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q :=
        residual_largestPrimePowerPart_le q r U hqpp hr hUlargest
      refine ⟨U, hinterval, ?_, ?_, hUlargest,
        largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hresle hqnotden⟩
      · intro h
        exact (hqodd h).elim
      · intro _
        simp [U]
    · refine ⟨∅, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · intro h
        exact (hqodd h).elim
      · simp
      · simp
      · simpa using largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hr hqd


end




/-!
# Martin's small-prime-power elimination lemma

This file formalizes the elementary LCM step used for the small prime powers
in Martin's exact correction.  If `q = p ^ e` is the largest exact
prime-power part of the reduced denominator of a rational `r`, we subtract a
single unit fraction whose denominator is `lcm(1,...,q) / a`, where
`1 ≤ a ≤ p - 1`.  The residue `a` is chosen so that reduction cancels one
additional factor of `p`; all other prime-power parts were already strictly
smaller than `q`.
-/

open Finset
open scoped BigOperators

noncomputable section

/-- A prime power dividing `lcm(1,...,y)` is at most `y`. -/
lemma isPrimePow_le_of_dvd_initialLcm {y t : ℕ} (ht : IsPrimePow t)
    (htL : t ∣ initialLcm y) : t ≤ y := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 ht
  have hL0 : initialLcm y ≠ 0 := by
    simp [initialLcm]
  have hkL : k ≤ (initialLcm y).factorization p :=
    (hp.pow_dvd_iff_le_factorization hL0).1 htL
  have hfac : (initialLcm y).factorization p =
      (Icc 1 y).sup (fun a ↦ a.factorization p) := by
    rw [initialLcm]
    simpa only [id_eq] using
      (Finset.factorization_lcm
        (s := Icc 1 y) (f := id) (by
          intro a ha
          exact Nat.ne_of_gt (Finset.mem_Icc.mp ha).1) p)
  rw [hfac] at hkL
  have hIcc : (Icc 1 y).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hkL
    omega
  obtain ⟨a, ha, hsup⟩ :=
    Finset.exists_mem_eq_sup (s := Icc 1 y)
      (f := fun a ↦ a.factorization p) hIcc
  rw [hsup] at hkL
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp ha).1
  have hpa : p ^ k ∣ a := (hp.pow_dvd_iff_le_factorization ha0).2 hkL
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hpa).trans (Finset.mem_Icc.mp ha).2

/-- Every exact prime-power part of the initial LCM is at most its endpoint. -/
lemma initialLcm_primePowerSmooth (y : ℕ) :
    PrimePowerSmooth y (initialLcm y) := by
  have hL0 : initialLcm y ≠ 0 := by simp [initialLcm]
  intro t ht
  exact isPrimePow_le_of_dvd_initialLcm
    ((mem_primePowerParts hL0).mp ht).1
    ((mem_primePowerParts hL0).mp ht).2.1

/-- If all exact prime-power parts of `d` are at most `y`, then `d` divides
`lcm(1,...,y)`. -/
lemma dvd_initialLcm_of_primePowerSmooth {d y : ℕ} (hd : d ≠ 0)
    (hdy : PrimePowerSmooth y d) : d ∣ initialLcm y := by
  have hparts : (primePowerParts d).lcm id ∣ initialLcm y := by
    apply Finset.lcm_dvd
    intro t ht
    exact (Finset.dvd_lcm (s := Icc 1 y) (f := id)
      (Finset.mem_Icc.mpr
        ⟨le_of_lt ((mem_primePowerParts hd).mp ht).1.one_lt, hdy t ht⟩))
  have hpartsEq : (primePowerParts d).lcm id = d := by
    calc
      (primePowerParts d).lcm id =
          UnitFractions.lcmA (UnitFractions.ppowers_in_set {d}) := by
            rw [primePowerParts_eq_ppowers_in_singleton]
      _ = UnitFractions.lcmA ({d} : Finset ℕ) :=
        UnitFractions.lcm_Q (by simpa using hd.symm)
      _ = d := by simp [UnitFractions.lcmA]
  rwa [hpartsEq] at hparts

/-- At the endpoint `q = p^e`, the `p`-part of `lcm(1,...,q)` is exactly
`q`. -/
lemma primePower_mem_initialLcm_parts {p e q : ℕ} (hp : p.Prime)
    (he : 0 < e) (hq : q = p ^ e) :
    q ∈ primePowerParts (initialLcm q) := by
  subst q
  have hqpp : IsPrimePow (p ^ e) := ⟨p, e, hp.prime, he, rfl⟩
  have hqmem : p ^ e ∈ Icc 1 (p ^ e) := by
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, le_rfl⟩
  have hqL : p ^ e ∣ initialLcm (p ^ e) :=
    Finset.dvd_lcm (s := Icc 1 (p ^ e)) (f := id) hqmem
  rw [mem_primePowerParts (by simp [initialLcm])]
  refine ⟨hqpp, hqL, ?_⟩
  rw [Nat.coprime_pow_left_iff he, hp.coprime_iff_not_dvd]
  intro hpdiv
  have hsuccDiv : p ^ (e + 1) ∣ initialLcm (p ^ e) := by
    rw [pow_succ]
    exact Nat.mul_dvd_of_dvd_div hqL hpdiv
  have hle := isPrimePow_le_of_dvd_initialLcm
    (show IsPrimePow (p ^ (e + 1)) from
      ⟨p, e + 1, hp.prime, Nat.succ_pos e, rfl⟩) hsuccDiv
  exact (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self e))) hle

/-- Dividing the endpoint LCM by its base prime removes the only possible
exact prime-power part of size `q = p^e`. -/
lemma largestPrimePowerPart_lt_of_dvd_initialLcm_div_prime
    {p e q d : ℕ} (hp : p.Prime) (he : 0 < e) (hq : q = p ^ e)
    (hd : d ∣ initialLcm q / p) :
    largestPrimePowerPart d < q := by
  subst q
  have hpq : p ∣ p ^ e := dvd_pow_self p (ne_of_gt he)
  have hqL : p ^ e ∣ initialLcm (p ^ e) :=
    Finset.dvd_lcm (s := Icc 1 (p ^ e)) (f := id)
      (Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, le_rfl⟩)
  have hpL : p ∣ initialLcm (p ^ e) := hpq.trans hqL
  have hbound : PrimePowerSmooth (p ^ e - 1) d := by
    intro t ht
    have hd0 : d ≠ 0 := by
      intro hzero
      subst d
      simp [primePowerParts] at ht
    have htSpec := (mem_primePowerParts hd0).mp ht
    have htLdiv : t ∣ initialLcm (p ^ e) / p := htSpec.2.1.trans hd
    have htL : t ∣ initialLcm (p ^ e) :=
      htLdiv.trans (Nat.div_dvd_of_dvd hpL)
    have htle : t ≤ p ^ e :=
      isPrimePow_le_of_dvd_initialLcm htSpec.1 htL
    have htne : t ≠ p ^ e := by
      intro hteq
      subst t
      have hsuccDiv : p ^ (e + 1) ∣ initialLcm (p ^ e) := by
        simpa [pow_succ, mul_comm] using
          (Nat.mul_dvd_of_dvd_div hpL htLdiv)
      have hle := isPrimePow_le_of_dvd_initialLcm
        (show IsPrimePow (p ^ (e + 1)) from
          ⟨p, e + 1, hp.prime, Nat.succ_pos e, rfl⟩) hsuccDiv
      exact (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self e))) hle
    omega
  have hle : largestPrimePowerPart d ≤ p ^ e - 1 :=
    largestPrimePowerPart_le_iff.mpr hbound
  have hqpos : 0 < p ^ e := pow_pos hp.pos e
  omega

/-- Martin's Lemma 16 (the small-prime-power step).

The returned numerator `a` is the least positive residue of
`r.num * (L / r.den)` modulo `p`, and the unit-fraction denominator is
`n = L / a`, where `L = lcm(1,...,q)`. -/
theorem smallPrimePower_elimination (r : ℚ) {p e q : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q = p ^ e)
    (hqmax : q = largestPrimePowerPart r.den) :
    ∃ a n : ℕ,
      1 ≤ a ∧ a ≤ p - 1 ∧ Nat.Coprime p a ∧
      a ∣ initialLcm q ∧ n = initialLcm q / a ∧
      initialLcm q / (p - 1) ≤ n ∧
      q ∣ n ∧ q ∈ primePowerParts n ∧
      PrimePowerSmooth q n ∧ largestPrimePowerPart n = q ∧
      largestPrimePowerPart (r - (1 : ℚ) / n).den < q := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hqpp : IsPrimePow q := by
    subst q
    exact ⟨p, e, hp.prime, he, rfl⟩
  have hqpos : 0 < q := hqpp.pos
  have hqleDen : q ≤ r.den := by
    rw [hqmax]
    exact largestPrimePowerPart_le
  have hden2 : 2 ≤ r.den := hqpp.two_le.trans hqleDen
  have hqDen : q ∈ primePowerParts r.den := by
    rw [hqmax]
    exact largestPrimePowerPart_mem hden2
  have hdenSmooth : PrimePowerSmooth q r.den := by
    rw [← largestPrimePowerPart_le_iff, ← hqmax]
  have hdenL : r.den ∣ initialLcm q :=
    dvd_initialLcm_of_primePowerSmooth r.den_ne_zero hdenSmooth
  have hqLpart : q ∈ primePowerParts (initialLcm q) :=
    primePower_mem_initialLcm_parts hp he hq
  have hLpos : 0 < initialLcm q :=
    Nat.pos_of_ne_zero (by simp [initialLcm])
  have hqDenSpec := (mem_primePowerParts r.den_ne_zero).mp hqDen
  have hqLSpec := (mem_primePowerParts (by simp [initialLcm])).mp hqLpart
  have hpq : p ∣ q := by
    subst q
    exact dvd_pow_self p (ne_of_gt he)
  have hpDen : p ∣ r.den := hpq.trans hqDenSpec.2.1
  have hpNumCoprime : Nat.Coprime p r.num.natAbs :=
    Nat.Coprime.of_dvd_left hpDen r.reduced.symm
  have hratioDvd : initialLcm q / r.den ∣ initialLcm q / q :=
    Nat.div_dvd_div_left hdenL hqDenSpec.2.1
  have hpRatioCoprime : Nat.Coprime p (initialLcm q / r.den) := by
    have hpLquot : Nat.Coprime p (initialLcm q / q) :=
      Nat.Coprime.of_dvd_left hpq hqLSpec.2.2
    exact Nat.Coprime.of_dvd_right hratioDvd hpLquot
  have hnumCast : (r.num : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hdiv ↦ (hp.coprime_iff_not_dvd.mp hpNumCoprime)
      (Int.natCast_dvd.mp hdiv)
  have hratioCast : ((initialLcm q / r.den : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hpRatioCoprime
  let u : ZMod p :=
    (r.num : ZMod p) * ((initialLcm q / r.den : ℕ) : ZMod p)
  have hu : u ≠ 0 := mul_ne_zero hnumCast hratioCast
  let a : ℕ := u.val
  have haPos : 0 < a := ZMod.val_pos.mpr hu
  have haLt : a < p := ZMod.val_lt u
  have haLe : a ≤ p - 1 := by omega
  have hpa : Nat.Coprime p a := by
    rw [hp.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt haPos haLt
  have hpLeq : p ≤ q := by
    rw [hq]
    exact Nat.le_self_pow (ne_of_gt he) p
  have haq : a ≤ q := (le_of_lt haLt).trans hpLeq
  have haL : a ∣ initialLcm q := by
    exact Finset.dvd_lcm (s := Icc 1 q) (f := id)
      (Finset.mem_Icc.mpr ⟨haPos, haq⟩)
  let n : ℕ := initialLcm q / a
  have hnEq : n = initialLcm q / a := rfl
  have hlower : initialLcm q / (p - 1) ≤ n := by
    rw [hnEq]
    exact Nat.div_le_div le_rfl haLe (ne_of_gt haPos)
  have haqCoprime : Nat.Coprime a q := by
    rw [hq]
    exact hpa.symm.pow_right e
  have haLquot : a ∣ initialLcm q / q := by
    rw [← haqCoprime.dvd_mul_right]
    simpa [Nat.mul_div_cancel' hqLSpec.2.1, mul_comm] using haL
  have hnFactor : n = q * ((initialLcm q / q) / a) := by
    rw [hnEq, ← Nat.mul_div_assoc q haLquot, Nat.mul_div_cancel' hqLSpec.2.1]
  have hqN : q ∣ n := hnFactor.symm ▸ dvd_mul_right q _
  have hqNquot : n / q = (initialLcm q / q) / a := by
    rw [hnFactor, Nat.mul_div_cancel_left _ hqpos]
  have hqNcoprime : Nat.Coprime q (n / q) := by
    rw [hqNquot]
    exact Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd haLquot) hqLSpec.2.2
  have hqNpart : q ∈ primePowerParts n := by
    have hn0 : n ≠ 0 := by
      exact Nat.ne_of_gt
        (Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos)
    exact (mem_primePowerParts hn0).mpr ⟨hqpp, hqN, hqNcoprime⟩
  have hnSmooth : PrimePowerSmooth q n := by
    intro t ht
    have hn0 : n ≠ 0 := by
      exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos)
    have htSpec := (mem_primePowerParts hn0).mp ht
    exact isPrimePow_le_of_dvd_initialLcm htSpec.1
      (htSpec.2.1.trans (Nat.div_dvd_of_dvd haL))
  have hnLargest : largestPrimePowerPart n = q := by
    apply Nat.le_antisymm
    · exact largestPrimePowerPart_le_iff.mpr hnSmooth
    · exact le_largestPrimePowerPart hqNpart
  let m : ℕ := initialLcm q / r.den
  let z : ℤ := r.num * (m : ℤ) - a
  have hzCast : (z : ZMod p) = 0 := by
    simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [show (a : ZMod p) = u by exact ZMod.natCast_zmod_val u]
    simp [u, m]
  have hpz : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzCast
  have hresidual : r - (1 : ℚ) / n = Rat.divInt z (initialLcm q) := by
    rw [Rat.divInt_eq_div]
    change r - (1 : ℚ) / n = (z : ℚ) / (initialLcm q : ℚ)
    have hzRat : (z : ℚ) = (r.num : ℚ) * (m : ℚ) - (a : ℚ) := by
      simp [z]
    rw [hzRat]
    nth_rewrite 1 [← Rat.num_div_den r]
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt haPos)
    rw [hnEq, Nat.cast_div haL haQ]
    have hLdecomp : (initialLcm q : ℚ) =
        (r.den : ℚ) * (m : ℕ) := by
      dsimp [m]
      exact_mod_cast (Nat.mul_div_cancel' hdenL).symm
    have hmPos : 0 < m := by
      dsimp [m]
      exact Nat.div_pos (Nat.le_of_dvd hLpos hdenL) r.den_pos
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hmPos)
    have hdQ : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [hLdecomp]
    field_simp [haQ, hmQ, hdQ]
  have hpL : p ∣ initialLcm q := hpq.trans hqLSpec.2.1
  have hresDen : (r - (1 : ℚ) / n).den ∣ initialLcm q / p :=
    rat_den_dvd_div_of_eq_divInt (ne_of_gt hLpos) hp.ne_zero hpL hpz hresidual
  have hdescent :
      largestPrimePowerPart (r - (1 : ℚ) / n).den < q :=
    largestPrimePowerPart_lt_of_dvd_initialLcm_div_prime hp he hq hresDen
  exact ⟨a, n, haPos, haLe, hpa, haL, hnEq, hlower, hqN, hqNpart,
    hnSmooth, hnLargest, hdescent⟩

/-- Uniform exponential form of Martin's Lemma 16.  The constant comes from
the formalized estimate `lcm(1,...,y) ≤ exp(C y)`; it is independent of the
rational, the prime, and the exponent. -/
theorem exists_uniform_smallPrimePower_elimination_exp_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℚ) (p e q : ℕ), p.Prime → 0 < e → q = p ^ e →
        q = largestPrimePowerPart r.den →
        ∃ a n : ℕ,
          0 < n ∧ 1 ≤ a ∧ a ≤ p - 1 ∧ Nat.Coprime p a ∧
          a ∣ initialLcm q ∧ n = initialLcm q / a ∧
          initialLcm q / (p - 1) ≤ n ∧
          q ∈ primePowerParts n ∧ largestPrimePowerPart n = q ∧
          largestPrimePowerPart (r - (1 : ℚ) / n).den < q ∧
          (n : ℝ) ≤ Real.exp (C * q) := by
  obtain ⟨C, hCpos, hC⟩ := exists_initialLcm_le_exp
  refine ⟨C, hCpos, ?_⟩
  intro r p e q hp he hq hqmax
  obtain ⟨a, n, haPos, haLe, hpa, haL, hnEq, hlower, hqN, hqNpart,
      hnSmooth, hnLargest, hdescent⟩ :=
    smallPrimePower_elimination r hp he hq hqmax
  have hnPos : 0 < n := by
    rw [hnEq]
    exact Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (by simp [initialLcm])) haL) haPos
  have hnLNat : n ≤ initialLcm q := by
    rw [hnEq]
    exact Nat.div_le_self _ _
  have hnL : (n : ℝ) ≤ initialLcm q := by exact_mod_cast hnLNat
  exact ⟨a, n, hnPos, haPos, haLe, hpa, haL, hnEq, hlower, hqNpart,
    hnLargest, hdescent, hnL.trans (hC q)⟩

end




/-!
# Rough-denominator counting

This file isolates the finite union bound in Martin's Lemma 9.  An integer whose
largest exact prime-power part exceeds `y` is a multiple of a prime power in
`(y,x]`.  Consequently its count, and its reciprocal mass in an interval bounded
away from zero, are controlled by the reciprocal mass of those prime powers.

The last section combines this finite estimate with the prime-power Mertens
estimate already proved in `UnitFractions.ForMathlib.BasicEstimates`.  It is
phrased for a general moving cutoff.  In particular it applies as soon as one
has the elementary logarithmic calculation for `y = x / log(x)^A`.
-/

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Prime powers in the half-open interval `(y,x]`. -/
def largePrimePowers (x y : ℕ) : Finset ℕ :=
  (Icc (y + 1) x).filter IsPrimePow

/-- Integers in `[L,x]` whose largest exact prime-power part is larger than `y`. -/
def roughNumbersIn (L x y : ℕ) : Finset ℕ :=
  (Icc L x).filter fun n ↦ y < largestPrimePowerPart n

/-- Multiples of `q` in `[1,x]`. -/
def multiplesUpTo (x q : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n ↦ q ∣ n

/-- Reciprocal mass of the prime powers in `(y,x]`. -/
def primePowerReciprocalTail (x y : ℕ) : ℝ :=
  ∑ q ∈ largePrimePowers x y, (q : ℝ)⁻¹

/-- Reciprocal mass of a finite set of natural numbers. -/
def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (n : ℝ)⁻¹

/-- The prime-power Mertens summatory function. -/
def primePowerReciprocalUpTo (x : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 x).filter IsPrimePow, (q : ℝ)⁻¹

/-- Martin's standard logarithmic cutoff, rounded down to a natural number. -/
def logPowerCutoff (A x : ℕ) : ℕ :=
  ⌊(x : ℝ) / Real.log (x : ℝ) ^ A⌋₊

/-- Natural left endpoint of a terminal interval `[alpha*x,x]`. -/
def proportionalLeftEndpoint (α : ℝ) (x : ℕ) : ℕ :=
  ⌈α * x⌉₊

@[simp] lemma mem_largePrimePowers {x y q : ℕ} :
    q ∈ largePrimePowers x y ↔ y < q ∧ q ≤ x ∧ IsPrimePow q := by
  simp only [largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hyq, hqx⟩, hq⟩
    exact ⟨Nat.lt_of_succ_le hyq, hqx, hq⟩
  · rintro ⟨hyq, hqx, hq⟩
    exact ⟨⟨hyq, hqx⟩, hq⟩

@[simp] lemma mem_roughNumbersIn {L x y n : ℕ} :
    n ∈ roughNumbersIn L x y ↔ L ≤ n ∧ n ≤ x ∧ y < largestPrimePowerPart n := by
  simp [roughNumbersIn, and_assoc]

@[simp] lemma mem_multiplesUpTo {x q n : ℕ} :
    n ∈ multiplesUpTo x q ↔ 1 ≤ n ∧ n ≤ x ∧ q ∣ n := by
  simp [multiplesUpTo, and_assoc]

lemma reciprocalMass_nonneg (A : Finset ℕ) : 0 ≤ reciprocalMass A := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

lemma primePowerReciprocalTail_nonneg (x y : ℕ) :
    0 ≤ primePowerReciprocalTail x y := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Every rough integer is covered by the multiples of its largest exact
prime-power part. -/
lemma roughNumbersIn_subset_biUnion (L x y : ℕ) :
    roughNumbersIn L x y ⊆
      (largePrimePowers x y).biUnion (multiplesUpTo x) := by
  intro n hn
  rw [mem_roughNumbersIn] at hn
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnlt : n < 2 := Nat.lt_of_not_ge h
    have hempty : primePowerParts n = ∅ := primePowerParts_empty_iff.mpr hnlt
    have hz : largestPrimePowerPart n = 0 := by
      simp [largestPrimePowerPart, hempty]
    omega
  let q := largestPrimePowerPart n
  have hqmem : q ∈ primePowerParts n := largestPrimePowerPart_mem hn2
  have hqspec := (mem_primePowerParts (by omega : n ≠ 0)).mp hqmem
  rw [Finset.mem_biUnion]
  refine ⟨q, ?_, ?_⟩
  · rw [mem_largePrimePowers]
    exact ⟨hn.2.2, largestPrimePowerPart_le.trans hn.2.1, hqspec.1⟩
  · rw [mem_multiplesUpTo]
    exact ⟨by omega, hn.2.1, hqspec.2.1⟩

/-- The number of rough integers is at most the sum of the numbers of multiples
of the relevant prime powers. -/
lemma roughNumbersIn_card_le_sum_div (L x y : ℕ) :
    (roughNumbersIn L x y).card ≤
      ∑ q ∈ largePrimePowers x y, x / q := by
  calc
    (roughNumbersIn L x y).card ≤
        ((largePrimePowers x y).biUnion (multiplesUpTo x)).card :=
      Finset.card_le_card (roughNumbersIn_subset_biUnion L x y)
    _ ≤ ∑ q ∈ largePrimePowers x y, (multiplesUpTo x q).card :=
      Finset.card_biUnion_le
    _ = ∑ q ∈ largePrimePowers x y, x / q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq1 : 1 ≤ q := le_of_lt ((mem_largePrimePowers.mp hq).2.2.one_lt)
      exact UnitFractions.count_multiples hq1

/-- Real-valued form of the union bound. -/
lemma roughNumbersIn_card_le_mul_tail (L x y : ℕ) :
    ((roughNumbersIn L x y).card : ℝ) ≤
      (x : ℝ) * primePowerReciprocalTail x y := by
  have hcast :
      ((↑(∑ q ∈ largePrimePowers x y, x / q) : ℕ) : ℝ) =
        ∑ q ∈ largePrimePowers x y, ((x / q : ℕ) : ℝ) := by
    norm_cast
  calc
    ((roughNumbersIn L x y).card : ℝ) ≤
        (↑(∑ q ∈ largePrimePowers x y, x / q) : ℕ) := by
      exact_mod_cast roughNumbersIn_card_le_sum_div L x y
    _ = ∑ q ∈ largePrimePowers x y, ((x / q : ℕ) : ℝ) := hcast
    _ ≤ ∑ q ∈ largePrimePowers x y, (x : ℝ) / q := by
      apply Finset.sum_le_sum
      intro q hq
      exact Nat.cast_div_le
    _ = (x : ℝ) * primePowerReciprocalTail x y := by
      simp only [primePowerReciprocalTail, div_eq_mul_inv, Finset.mul_sum]

/-- On an interval with positive left endpoint, reciprocal mass is bounded by
cardinality divided by that endpoint. -/
lemma reciprocalMass_le_card_div {A : Finset ℕ} {L : ℕ} (hL : 1 ≤ L)
    (hA : ∀ n ∈ A, L ≤ n) :
    reciprocalMass A ≤ (A.card : ℝ) / L := by
  calc
    reciprocalMass A ≤ ∑ n ∈ A, (L : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hL.trans (hA n hn)
      have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
      have hLn : (L : ℝ) ≤ n := by exact_mod_cast hA n hn
      exact (inv_le_inv₀ hnpos hLpos).2 hLn
    _ = (A.card : ℝ) / L := by
      simp [div_eq_mul_inv, nsmul_eq_mul]

/-- Reciprocal-mass version of the rough-number union bound. -/
lemma roughNumbersIn_reciprocalMass_le (L x y : ℕ) (hL : 1 ≤ L) :
    reciprocalMass (roughNumbersIn L x y) ≤
      ((x : ℝ) / L) * primePowerReciprocalTail x y := by
  calc
    reciprocalMass (roughNumbersIn L x y) ≤
        ((roughNumbersIn L x y).card : ℝ) / L := by
      apply reciprocalMass_le_card_div hL
      intro n hn
      exact (mem_roughNumbersIn.mp hn).1
    _ ≤ ((x : ℝ) * primePowerReciprocalTail x y) / L := by
      exact div_le_div_of_nonneg_right (roughNumbersIn_card_le_mul_tail L x y)
        (Nat.cast_nonneg L)
    _ = ((x : ℝ) / L) * primePowerReciprocalTail x y := by ring

/-- The tail is the difference of the two prime-power Mertens sums. -/
lemma primePowerReciprocalTail_eq_sub {x y : ℕ} (hyx : y ≤ x) :
    primePowerReciprocalTail x y =
      primePowerReciprocalUpTo x - primePowerReciprocalUpTo y := by
  let A := (Icc 1 x).filter IsPrimePow
  let B := (Icc 1 y).filter IsPrimePow
  have hBA : B ⊆ A := by
    intro q hq
    simp only [B, A, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans hyx⟩, hq.2⟩
  change (∑ q ∈ largePrimePowers x y, (q : ℝ)⁻¹) =
    (∑ q ∈ A, (q : ℝ)⁻¹) - ∑ q ∈ B, (q : ℝ)⁻¹
  rw [← Finset.sum_sdiff hBA]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr
  · ext q
    simp only [largePrimePowers, A, B, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hyq, hqx⟩, hqpp⟩
      refine ⟨⟨⟨(le_of_lt hqpp.one_lt), hqx⟩, hqpp⟩, ?_⟩
      intro hqy
      omega
    · rintro ⟨⟨⟨hq1, hqx⟩, hqpp⟩, hnot⟩
      refine ⟨⟨?_, hqx⟩, hqpp⟩
      by_contra hyq
      apply hnot
      exact ⟨⟨hq1, Nat.le_of_not_gt hyq⟩, hqpp⟩
  · intro q hq
    rfl

/-- The error term in the prime-power Mertens formula tends to zero along the
natural numbers. -/
lemma exists_primePowerReciprocalUpTo_error_tendsto_zero :
    ∃ b : ℝ,
      Tendsto
        (fun x : ℕ ↦
          primePowerReciprocalUpTo x - (Real.log (Real.log (x : ℝ)) + b))
        atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  refine ⟨b, ?_⟩
  have hb' := hb.comp_tendsto tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun x : ℕ ↦ (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top
  have hzero := hb'.trans_tendsto hinv
  simpa [Function.comp_def, primePowerReciprocalUpTo, Nat.floor_natCast] using hzero

/-! ## The cutoff `x / log(x)^A` -/

lemma logPowerScale_tendsto_atTop (A : ℕ) :
    Tendsto (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ A) atTop atTop := by
  have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
    (1 : ℝ) 0 A zero_lt_one).comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h

lemma logPowerCutoff_tendsto_atTop (A : ℕ) :
    Tendsto (logPowerCutoff A) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (logPowerScale_tendsto_atTop A)

lemma logPowerCutoff_eventually_le (A : ℕ) :
    ∀ᶠ x : ℕ in atTop, logPowerCutoff A x ≤ x := by
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
  try simp only [Set.mem_ofPred_eq] at hx
  have hden : (1 : ℝ) ≤ Real.log (x : ℝ) ^ A := one_le_pow₀ hx
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hscale0 : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ A :=
    div_nonneg hx0 (zero_le_one.trans hden)
  have hfloor : (logPowerCutoff A x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ A := by
    exact Nat.floor_le hscale0
  have hscale : (x : ℝ) / Real.log (x : ℝ) ^ A ≤ x :=
    div_le_self hx0 hden
  exact_mod_cast hfloor.trans hscale

lemma proportionalLeftEndpoint_eventually_one_le {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop, 1 ≤ proportionalLeftEndpoint α x := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [proportionalLeftEndpoint, Nat.one_le_ceil_iff]
  exact mul_pos hα (by exact_mod_cast hx)

lemma proportionalLeftEndpoint_eventually_ratio_le_inv {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / proportionalLeftEndpoint α x ≤ α⁻¹ := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hceilpos : (0 : ℝ) < proportionalLeftEndpoint α x := by
    exact_mod_cast (Nat.ceil_pos.mpr (mul_pos hα hxpos))
  rw [div_le_iff₀ hceilpos, inv_mul_eq_div, le_div_iff₀ hα]
  simpa [proportionalLeftEndpoint, mul_comm] using Nat.le_ceil (α * (x : ℝ))

lemma loglog_div_log_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      atTop (𝓝 0) := by
  have h := (IsLittleO.tendsto_div_nhds_zero
    Real.isLittleO_log_id_atTop).comp tendsto_log_coe_at_top
  simpa [id, Function.comp_def] using h

lemma logPowerCutoff_ratio_tendsto_one (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (logPowerCutoff A x : ℝ) /
          ((x : ℝ) / Real.log (x : ℝ) ^ A))
      atTop (𝓝 1) := by
  exact tendsto_nat_floor_div_atTop.comp (logPowerScale_tendsto_atTop A)

lemma log_logPowerCutoff_ratio_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log
        ((logPowerCutoff A x : ℝ) /
          ((x : ℝ) / Real.log (x : ℝ) ^ A)))
      atTop (𝓝 0) := by
  have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuousAt_log one_ne_zero).tendsto
  exact hcont.comp (logPowerCutoff_ratio_tendsto_one A)

lemma log_logPowerCutoff_div_log_tendsto_one (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log (logPowerCutoff A x : ℝ) /
        Real.log (x : ℝ)) atTop (𝓝 1) := by
  let scale : ℕ → ℝ := fun x ↦ (x : ℝ) / Real.log (x : ℝ) ^ A
  let ratio : ℕ → ℝ := fun x ↦ (logPowerCutoff A x : ℝ) / scale x
  have hratio : Tendsto ratio atTop (𝓝 1) := by
    simpa [ratio, scale] using logPowerCutoff_ratio_tendsto_one A
  have hlogratio : Tendsto (fun x ↦ Real.log (ratio x)) atTop (𝓝 0) := by
    simpa [ratio, scale] using log_logPowerCutoff_ratio_tendsto_zero A
  have hlogratio_div : Tendsto
      (fun x : ℕ ↦ Real.log (ratio x) / Real.log (x : ℝ)) atTop (𝓝 0) :=
    hlogratio.div_atTop tendsto_log_coe_at_top
  have hmain : Tendsto
      (fun x : ℕ ↦
        1 - (A : ℝ) *
          (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) +
          Real.log (ratio x) / Real.log (x : ℝ)) atTop (𝓝 1) := by
    have hmiddle : Tendsto
        (fun x : ℕ ↦ -(A : ℝ) *
          (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)))
        atTop (𝓝 0) := by
      simpa using (loglog_div_log_tendsto_zero.const_mul (-(A : ℝ)))
    simpa [sub_eq_add_neg] using
      (tendsto_const_nhds.add hmiddle).add hlogratio_div
  apply hmain.congr'
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
      (logPowerScale_tendsto_atTop A).eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds zero_lt_one)] with x hlogx hxone hscale hratioPos
  try simp only [Set.mem_ofPred_eq] at hlogx hxone hscale hratioPos
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans hxone
  have hlogne : Real.log (x : ℝ) ≠ 0 := (ne_of_gt hlogx)
  have hpowpos : 0 < Real.log (x : ℝ) ^ A := pow_pos hlogx A
  have hscalene : scale x ≠ 0 := (ne_of_gt hscale)
  have hratione : ratio x ≠ 0 := (ne_of_gt hratioPos)
  have hcutoff : (logPowerCutoff A x : ℝ) = ratio x * scale x := by
    dsimp [ratio]
    exact (div_mul_cancel₀ _ hscalene).symm
  rw [hcutoff, Real.log_mul hratione hscalene]
  dsimp [scale]
  rw [Real.log_div (ne_of_gt hxpos) (pow_ne_zero A hlogne), Real.log_pow]
  field_simp
  ring

lemma logPowerCutoff_loglog_sub_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (logPowerCutoff A x : ℝ)))
      atTop (𝓝 0) := by
  have hratio := log_logPowerCutoff_div_log_tendsto_one A
  have hlogratio : Tendsto
      (fun x : ℕ ↦ Real.log
        (Real.log (logPowerCutoff A x : ℝ) / Real.log (x : ℝ)))
      atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  have hneg := hlogratio.neg
  have hneg0 : Tendsto
      (fun x : ℕ ↦ -Real.log
        (Real.log (logPowerCutoff A x : ℝ) / Real.log (x : ℝ)))
      atTop (𝓝 0) := by simpa using hneg
  apply hneg0.congr'
  have hlogCutoffTop : Tendsto
      (fun x : ℕ ↦ Real.log (logPowerCutoff A x : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (logPowerCutoff_tendsto_atTop A))
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hlogCutoffTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hcut
  try simp only [Set.mem_ofPred_eq] at hx hcut
  rw [Real.log_div (ne_of_gt hcut) (ne_of_gt hx)]
  ring

/-- A moving prime-power tail tends to zero whenever both endpoints tend to
infinity and their logarithmic logarithms become equal.  This is the exact
analytic interface needed for cutoffs such as `x / log(x)^A`. -/
lemma primePowerReciprocalTail_tendsto_zero {y : ℕ → ℕ}
    (hy_le : ∀ᶠ x in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ ↦ primePowerReciprocalTail x (y x)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_primePowerReciprocalUpTo_error_tendsto_zero
  have hby := hb.comp hy_top
  have hsum := hlog.add (hb.sub hby)
  have hsum0 : Tendsto
      (fun x : ℕ ↦
        Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y x : ℝ)) +
          ((primePowerReciprocalUpTo x - (Real.log (Real.log (x : ℝ)) + b)) -
            (primePowerReciprocalUpTo (y x) -
              (Real.log (Real.log (y x : ℝ)) + b)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hsum
  apply hsum0.congr'
  filter_upwards [hy_le] with x hyx
  rw [primePowerReciprocalTail_eq_sub hyx]
  ring

/-- The three moving-cutoff facts used when specializing Martin's union bound. -/
theorem logPowerCutoff_spec (A : ℕ) :
    (∀ᶠ x : ℕ in atTop, logPowerCutoff A x ≤ x) ∧
      Tendsto (logPowerCutoff A) atTop atTop ∧
      Tendsto
        (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
          Real.log (Real.log (logPowerCutoff A x : ℝ)))
        atTop (𝓝 0) :=
  ⟨logPowerCutoff_eventually_le A, logPowerCutoff_tendsto_atTop A,
    logPowerCutoff_loglog_sub_tendsto_zero A⟩

lemma primePowerReciprocalTail_logPowerCutoff_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ primePowerReciprocalTail x (logPowerCutoff A x))
      atTop (𝓝 0) := by
  exact primePowerReciprocalTail_tendsto_zero
    (logPowerCutoff_eventually_le A)
    (logPowerCutoff_tendsto_atTop A)
    (logPowerCutoff_loglog_sub_tendsto_zero A)

/-- Epsilon form of Martin's rough-count estimate.  The exceptional set has
`o(x)` elements under the moving-cutoff hypotheses. -/
lemma roughNumbersIn_card_isLittleO {y : ℕ → ℕ}
    (hy_le : ∀ᶠ x in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    (fun x : ℕ ↦ ((roughNumbersIn 1 x (y x)).card : ℝ))
      =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  have htail := primePowerReciprocalTail_tendsto_zero hy_le hy_top hlog
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have heps : ∀ᶠ x in atTop, primePowerReciprocalTail x (y x) ≤ ε :=
    (htail.eventually (Iio_mem_nhds hε)).mono fun _ h ↦ (le_of_lt h)
  filter_upwards [heps] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    ((roughNumbersIn 1 x (y x)).card : ℝ) ≤
        (x : ℝ) * primePowerReciprocalTail x (y x) :=
      roughNumbersIn_card_le_mul_tail 1 x (y x)
    _ ≤ (x : ℝ) * ε := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg x)
    _ = ε * (x : ℝ) := by ring

lemma roughNumbersIn_logPowerCutoff_card_isLittleO (A : ℕ) :
    (fun x : ℕ ↦
      ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ))
      =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  exact roughNumbersIn_card_isLittleO
    (logPowerCutoff_eventually_le A)
    (logPowerCutoff_tendsto_atTop A)
    (logPowerCutoff_loglog_sub_tendsto_zero A)

/-- Reciprocal mass tends to zero in any family of terminal intervals whose
left endpoint remains a fixed positive proportion of the right endpoint. -/
lemma roughNumbersIn_reciprocalMass_tendsto_zero
    {L y : ℕ → ℕ} {C : ℝ}
    (hL : ∀ᶠ x : ℕ in atTop, 1 ≤ L x)
    (hratio : ∀ᶠ x : ℕ in atTop, (x : ℝ) / L x ≤ C)
    (hy_le : ∀ᶠ x : ℕ in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass (roughNumbersIn (L x) x (y x)))
      atTop (𝓝 0) := by
  have htail := primePowerReciprocalTail_tendsto_zero hy_le hy_top hlog
  have hupper : Tendsto
      (fun x : ℕ ↦ C * primePowerReciprocalTail x (y x)) atTop (𝓝 0) := by
    simpa using htail.const_mul C
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · filter_upwards [hL, hratio] with x hLx hrat
    calc
      reciprocalMass (roughNumbersIn (L x) x (y x)) ≤
          ((x : ℝ) / L x) * primePowerReciprocalTail x (y x) :=
        roughNumbersIn_reciprocalMass_le (L x) x (y x) hLx
      _ ≤ C * primePowerReciprocalTail x (y x) :=
        mul_le_mul_of_nonneg_right hrat (primePowerReciprocalTail_nonneg _ _)
  · exact hupper

/-- Concrete reciprocal-mass form for Martin's interval
`[ceil(alpha*x),x]` and logarithmic prime-power cutoff. -/
lemma roughNumbersIn_logPowerCutoff_reciprocalMass_tendsto_zero
    (A : ℕ) {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (roughNumbersIn (proportionalLeftEndpoint α x) x
          (logPowerCutoff A x)))
      atTop (𝓝 0) := by
  exact roughNumbersIn_reciprocalMass_tendsto_zero
    (proportionalLeftEndpoint_eventually_one_le hα)
    (proportionalLeftEndpoint_eventually_ratio_le_inv hα)
    (logPowerCutoff_eventually_le A)
    (logPowerCutoff_tendsto_atTop A)
    (logPowerCutoff_loglog_sub_tendsto_zero A)

/-! ## A quantitative logarithmic-cutoff estimate -/

/-- The inverse square root of the natural logarithm tends to zero. -/
lemma inv_sqrt_log_tendsto_zero :
    Tendsto (fun x : ℕ ↦ (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_log_coe_at_top)

/-- `log log x` is negligible compared with `sqrt (log x)`. -/
lemma loglog_div_sqrt_log_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) /
        Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0) := by
  have h := (IsLittleO.tendsto_div_nhds_zero
    (isLittleO_log_rpow_atTop
      (show (0 : ℝ) < 1 / 2 by norm_num))).comp
        tendsto_log_coe_at_top
  simpa [Function.comp_def, Real.sqrt_eq_rpow] using h

/-- The logarithm of `floor (x / log(x)^A)` is eventually at least half of
`log x`.  The fixed factor `1/2` absorbs the floor, while
`A * log log x = o(log x)`. -/
lemma logPowerCutoff_eventually_log_half_le (A : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) / 2 ≤
        Real.log (logPowerCutoff A x : ℝ) := by
  have hinvlog : Tendsto (fun x : ℕ ↦ (Real.log (x : ℝ))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top
  have hsmall : Tendsto
      (fun x : ℕ ↦
        (A : ℝ) *
            (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) +
          Real.log 2 * (Real.log (x : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using
      (loglog_div_log_tendsto_zero.const_mul (A : ℝ)).add
        (hinvlog.const_mul (Real.log 2))
  have hratio := logPowerCutoff_ratio_tendsto_one A
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ)),
      hsmall.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
      hratio.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with x hlog hsmallx hratiox
  try simp only [Set.mem_ofPred_eq] at hlog hsmallx hratiox
  have hxpos : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp (zero_lt_one.trans hlog))
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans hlog
  have hpowpos : 0 < Real.log (x : ℝ) ^ A := pow_pos hlogpos A
  have hscale : 0 < (x : ℝ) / Real.log (x : ℝ) ^ A :=
    div_pos hxpos hpowpos
  have hcutoffLower :
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ A) <
        (logPowerCutoff A x : ℝ) := by
    rwa [lt_div_iff₀ hscale] at hratiox
  have hlogLower := Real.log_le_log
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hscale) (le_of_lt hcutoffLower)
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hcutoffLogLower :
      Real.log (x : ℝ) - (A : ℝ) * Real.log (Real.log (x : ℝ)) -
          Real.log 2 ≤ Real.log (logPowerCutoff A x : ℝ) := by
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (ne_of_gt hscale),
      Real.log_div (ne_of_gt hxpos) (pow_ne_zero A (ne_of_gt hlogpos)), Real.log_pow,
      hloghalf] at hlogLower
    linarith
  have hsmallx' :
      (A : ℝ) * Real.log (Real.log (x : ℝ)) + Real.log 2 <
        Real.log (x : ℝ) / 2 := by
    have heq : (A : ℝ) *
          (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) +
          Real.log 2 * (Real.log (x : ℝ))⁻¹ =
        ((A : ℝ) * Real.log (Real.log (x : ℝ)) + Real.log 2) /
          Real.log (x : ℝ) := by field_simp
    rw [heq, div_lt_iff₀ hlogpos] at hsmallx
    nlinarith
  linarith

/-- Quantitative lower expansion for the logarithm of the cutoff. -/
lemma logPowerCutoff_eventually_log_sub_le (A : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) -
          (A : ℝ) * Real.log (Real.log (x : ℝ)) - Real.log 2 ≤
        Real.log (logPowerCutoff A x : ℝ) := by
  have hratio := logPowerCutoff_ratio_tendsto_one A
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with x hlog hratiox
  try simp only [Set.mem_ofPred_eq] at hlog hratiox
  have hxpos : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp hlog)
  have hpowpos : 0 < Real.log (x : ℝ) ^ A := pow_pos hlog A
  have hscale : 0 < (x : ℝ) / Real.log (x : ℝ) ^ A :=
    div_pos hxpos hpowpos
  have hcutoffLower :
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ A) <
        (logPowerCutoff A x : ℝ) := by
    rwa [lt_div_iff₀ hscale] at hratiox
  have hlogLower := Real.log_le_log
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hscale) (le_of_lt hcutoffLower)
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (ne_of_gt hscale),
    Real.log_div (ne_of_gt hxpos) (pow_ne_zero A (ne_of_gt hlog)), Real.log_pow,
    hloghalf] at hlogLower
  linarith

/-- The main logarithmic difference in the prime-power Mertens formula is
`o(1 / sqrt(log x))` for a fixed logarithmic-power cutoff. -/
lemma logPowerCutoff_loglog_sub_mul_sqrt_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (Real.log (Real.log (x : ℝ)) -
            Real.log (Real.log (logPowerCutoff A x : ℝ))) *
          Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun x : ℕ ↦
        2 * (A : ℝ) *
            (Real.log (Real.log (x : ℝ)) /
              Real.sqrt (Real.log (x : ℝ))) +
          2 * Real.log 2 * (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (loglog_div_sqrt_log_tendsto_zero.const_mul (2 * (A : ℝ))).add
        (inv_sqrt_log_tendsto_zero.const_mul (2 * Real.log 2))
  apply squeeze_zero'
  · filter_upwards
      [logPowerCutoff_eventually_le A,
        logPowerCutoff_eventually_log_half_le A,
        (logPowerCutoff_tendsto_atTop A).eventually (eventually_ge_atTop 1),
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
        with x hcutle hhalf hcutone hlog
    try simp only [Set.mem_ofPred_eq] at hcutone hlog
    have hcutpos : (0 : ℝ) < logPowerCutoff A x := by exact_mod_cast hcutone
    have hcutlogle : Real.log (logPowerCutoff A x : ℝ) ≤
        Real.log (x : ℝ) := by
      exact Real.log_le_log hcutpos (by exact_mod_cast hcutle)
    have hcutlogpos : 0 < Real.log (logPowerCutoff A x : ℝ) :=
      (half_pos hlog).trans_le hhalf
    have hloglogle :
        Real.log (Real.log (logPowerCutoff A x : ℝ)) ≤
          Real.log (Real.log (x : ℝ)) :=
      Real.log_le_log hcutlogpos hcutlogle
    exact mul_nonneg (sub_nonneg.mpr hloglogle)
      (Real.sqrt_nonneg _)
  · filter_upwards
      [logPowerCutoff_eventually_le A,
        logPowerCutoff_eventually_log_half_le A,
        logPowerCutoff_eventually_log_sub_le A,
        (logPowerCutoff_tendsto_atTop A).eventually (eventually_ge_atTop 1),
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))]
        with x hcutle hhalf hlower hcutone hlog
    try simp only [Set.mem_ofPred_eq] at hcutone hlog
    let X : ℝ := Real.log (x : ℝ)
    let Y : ℝ := Real.log (logPowerCutoff A x : ℝ)
    let D : ℝ := (A : ℝ) * Real.log X + Real.log 2
    have hX : 0 < X := zero_lt_one.trans hlog
    have hlogX : 0 < Real.log X := Real.log_pos hlog
    have hYhalf : X / 2 ≤ Y := by simpa [X, Y] using hhalf
    have hY : 0 < Y := (half_pos hX).trans_le hYhalf
    have hcutpos : (0 : ℝ) < logPowerCutoff A x := by exact_mod_cast hcutone
    have hYX : Y ≤ X := by
      dsimp [X, Y]
      exact Real.log_le_log hcutpos (by exact_mod_cast hcutle)
    have hdiff : X - Y ≤ D := by
      dsimp [X, Y, D] at hlower ⊢
      linarith
    have hD : 0 ≤ D := by
      dsimp [D]
      positivity
    have hlogratio : Real.log X - Real.log Y ≤ 2 * D / X := by
      rw [← Real.log_div (ne_of_gt hX) (ne_of_gt hY)]
      calc
        Real.log (X / Y) ≤ X / Y - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hX hY)
        _ = (X - Y) / Y := by field_simp
        _ ≤ D / Y := div_le_div_of_nonneg_right hdiff (le_of_lt hY)
        _ ≤ D / (X / 2) :=
          div_le_div_of_nonneg_left hD (half_pos hX) hYhalf
        _ = 2 * D / X := by field_simp
    have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
    calc
      (Real.log (Real.log (x : ℝ)) -
            Real.log (Real.log (logPowerCutoff A x : ℝ))) *
          Real.sqrt (Real.log (x : ℝ)) =
          (Real.log X - Real.log Y) * Real.sqrt X := by rfl
      _ ≤ (2 * D / X) * Real.sqrt X :=
        mul_le_mul_of_nonneg_right hlogratio (Real.sqrt_nonneg X)
      _ = 2 * (A : ℝ) * (Real.log X / Real.sqrt X) +
          2 * Real.log 2 * (Real.sqrt X)⁻¹ := by
        dsimp [D]
        field_simp [(ne_of_gt hsqrt), (ne_of_gt hX)]
        rw [Real.sq_sqrt (le_of_lt hX)]
  · exact hupper

/-- Quantitative prime-power Mertens tail.  For every fixed logarithmic-power
cutoff, the reciprocal tail is `o(1 / sqrt(log x))`. -/
lemma primePowerReciprocalTail_logPowerCutoff_mul_sqrt_tendsto_zero
    (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        primePowerReciprocalTail x (logPowerCutoff A x) *
          Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨c, hc, hcbound⟩ := hb.exists_pos
  have hboundX := tendsto_natCast_atTop_atTop.eventually hcbound.bound
  have hboundY :=
    (tendsto_natCast_atTop_atTop.comp (logPowerCutoff_tendsto_atTop A)).eventually
      hcbound.bound
  have hmain := logPowerCutoff_loglog_sub_mul_sqrt_tendsto_zero A
  have hupper : Tendsto
      (fun x : ℕ ↦
        (Real.log (Real.log (x : ℝ)) -
            Real.log (Real.log (logPowerCutoff A x : ℝ))) *
            Real.sqrt (Real.log (x : ℝ)) +
          3 * c * (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      atTop (𝓝 0) := by
    simpa [mul_assoc] using hmain.add
      (inv_sqrt_log_tendsto_zero.const_mul (3 * c))
  apply squeeze_zero' (g := fun x : ℕ ↦
    (Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (logPowerCutoff A x : ℝ))) *
        Real.sqrt (Real.log (x : ℝ)) +
      3 * c * (Real.sqrt (Real.log (x : ℝ)))⁻¹)
  · filter_upwards with x
    exact mul_nonneg (primePowerReciprocalTail_nonneg _ _)
      (Real.sqrt_nonneg _)
  · filter_upwards
      [logPowerCutoff_eventually_le A,
        logPowerCutoff_eventually_log_half_le A,
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
        hboundX, hboundY]
      with x hcutle hhalf hlog hxbound hybound
    try simp only [Set.mem_ofPred_eq] at hlog hxbound hybound
    let X : ℝ := Real.log (x : ℝ)
    let Y : ℝ := Real.log (logPowerCutoff A x : ℝ)
    let S : ℝ := Real.sqrt X
    let ex : ℝ := primePowerReciprocalUpTo x -
      (Real.log X + b)
    let ey : ℝ := primePowerReciprocalUpTo (logPowerCutoff A x) -
      (Real.log Y + b)
    have hX : 0 < X := by simpa [X] using hlog
    have hYhalf : X / 2 ≤ Y := by simpa [X, Y] using hhalf
    have hY : 0 < Y := (half_pos hX).trans_le hYhalf
    have hS : 0 < S := by simpa [S] using Real.sqrt_pos.2 hX
    have hSsq : S ^ 2 = X := by
      simpa [S] using Real.sq_sqrt (le_of_lt hX)
    have hex : |ex| ≤ c / X := by
      simpa [ex, X, primePowerReciprocalUpTo, Function.comp_def,
        Nat.floor_natCast, norm_inv, Real.norm_eq_abs, abs_of_pos hX,
        div_eq_mul_inv] using hxbound
    have hey : |ey| ≤ c / Y := by
      simpa [ey, Y, primePowerReciprocalUpTo, Function.comp_def,
        Nat.floor_natCast, norm_inv, Real.norm_eq_abs, abs_of_pos hY,
        div_eq_mul_inv] using hybound
    have hexS : |ex| * S ≤ c * S⁻¹ := by
      calc
        |ex| * S ≤ (c / X) * S :=
          mul_le_mul_of_nonneg_right hex (le_of_lt hS)
        _ = c * S⁻¹ := by
          field_simp [(ne_of_gt hX), (ne_of_gt hS)]
          nlinarith
    have hcY : c / Y ≤ 2 * c / X := by
      calc
        c / Y ≤ c / (X / 2) :=
          div_le_div_of_nonneg_left (le_of_lt hc) (half_pos hX) hYhalf
        _ = 2 * c / X := by field_simp
    have heyS : |ey| * S ≤ 2 * c * S⁻¹ := by
      calc
        |ey| * S ≤ (c / Y) * S :=
          mul_le_mul_of_nonneg_right hey (le_of_lt hS)
        _ ≤ (2 * c / X) * S :=
          mul_le_mul_of_nonneg_right hcY (le_of_lt hS)
        _ = 2 * c * S⁻¹ := by
          field_simp [(ne_of_gt hX), (ne_of_gt hS)]
          nlinarith
    have herr : (|ex| + |ey|) * S ≤ 3 * c * S⁻¹ := by
      rw [add_mul]
      calc
        |ex| * S + |ey| * S ≤ c * S⁻¹ + 2 * c * S⁻¹ :=
          add_le_add hexS heyS
        _ = 3 * c * S⁻¹ := by ring
    have htail :
        primePowerReciprocalTail x (logPowerCutoff A x) =
          (Real.log X - Real.log Y) + ex - ey := by
      rw [primePowerReciprocalTail_eq_sub hcutle]
      dsimp [ex, ey]
      ring
    rw [htail]
    calc
      ((Real.log X - Real.log Y) + ex - ey) * S ≤
          ((Real.log X - Real.log Y) + |ex| + |ey|) * S := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hS)
        linarith [le_abs_self ex, neg_le_abs ey]
      _ = (Real.log X - Real.log Y) * S + (|ex| + |ey|) * S := by ring
      _ ≤ (Real.log X - Real.log Y) * S + 3 * c * S⁻¹ :=
        add_le_add_right herr _
  · exact hupper

/-- The rough-number count, divided by `x` and multiplied by `sqrt(log x)`,
tends to zero. -/
lemma roughNumbersIn_logPowerCutoff_card_div_mul_sqrt_tendsto_zero
    (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) / (x : ℝ)) *
          Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (g := fun x : ℕ ↦
      primePowerReciprocalTail x (logPowerCutoff A x) *
        Real.sqrt (Real.log (x : ℝ)))
  · filter_upwards with x
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hratio :
        ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) / (x : ℝ) ≤
          primePowerReciprocalTail x (logPowerCutoff A x) := by
      rw [div_le_iff₀ hxR]
      simpa [mul_comm] using
        roughNumbersIn_card_le_mul_tail 1 x (logPowerCutoff A x)
    exact mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _)
  · exact primePowerReciprocalTail_logPowerCutoff_mul_sqrt_tendsto_zero A

/-- Ratio form requested by the last-crossing argument: the rough density is
little-oh of `1 / sqrt(log x)`. -/
theorem roughNumbersIn_logPowerCutoff_card_div_inv_sqrt_tendsto_zero
    (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) / (x : ℝ)) /
          (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      atTop (𝓝 0) := by
  have h := roughNumbersIn_logPowerCutoff_card_div_mul_sqrt_tendsto_zero A
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  field_simp [(ne_of_gt hsqrt)]

/-- Asymptotic notation for the quantitative rough-count estimate. -/
theorem roughNumbersIn_logPowerCutoff_card_isLittleO_div_sqrt
    (A : ℕ) :
    (fun x : ℕ ↦
      ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ))
      =o[atTop]
        (fun x : ℕ ↦ (x : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
  have hratio : Tendsto
      (fun x : ℕ ↦
        ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) /
          ((x : ℝ) / Real.sqrt (Real.log (x : ℝ))))
      atTop (𝓝 0) := by
    have h := roughNumbersIn_logPowerCutoff_card_div_mul_sqrt_tendsto_zero A
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
    field_simp [(ne_of_gt hxR), (ne_of_gt hsqrt)]
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2 hratio
  filter_upwards [eventually_ge_atTop 2] with x hx
  intro hzero
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  exact ((div_ne_zero (ne_of_gt hxR) (ne_of_gt hsqrt)) hzero).elim

/-- In particular, eventually the rough count is at most
`x / sqrt(log x)`. -/
theorem eventually_roughNumbersIn_logPowerCutoff_card_le_div_sqrt
    (A : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) ≤
        (x : ℝ) / Real.sqrt (Real.log (x : ℝ)) := by
  have hsmall :=
    (roughNumbersIn_logPowerCutoff_card_div_mul_sqrt_tendsto_zero A).eventually
      (Iio_mem_nhds zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 2] with x hsmallx hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  rw [div_mul_eq_mul_div, div_lt_iff₀ hxR] at hsmallx
  rw [le_div_iff₀ hsqrt]
  simpa using (le_of_lt hsmallx)

/-! ## Square tails for the exact-correction stage -/

/-- The elementary telescoping majorant `1/n^2 <= 1/(n-1)-1/n`. -/
lemma inv_sq_le_inv_pred_sub_inv {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) ^ 2)⁻¹ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpredR : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsub : (n : ℝ) - 1 ≠ 0 := by nlinarith
  have heq : ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ =
      ((n : ℝ) * (n - 1 : ℕ))⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp [(ne_of_gt hnR), (ne_of_gt hpredR), hnsub]
    ring
  rw [heq]
  refine (inv_le_inv₀ (sq_pos_of_pos hnR) (mul_pos hnR hpredR)).2 ?_
  nlinarith [show ((n - 1 : ℕ) : ℝ) ≤ n by exact_mod_cast (by omega : n - 1 ≤ n)]

/-- The finite integer square tail above `L` is at most `1/L`. -/
lemma sum_Icc_inv_sq_le_inv (L X : ℕ) (hL : 1 ≤ L) :
    (∑ n ∈ Icc (L + 1) X, ((n : ℝ) ^ 2)⁻¹) ≤ (L : ℝ)⁻¹ := by
  by_cases hLX : L < X
  · have hrewrite :
        (∑ n ∈ Icc (L + 1) X, ((n : ℝ) ^ 2)⁻¹) =
          ∑ i ∈ range (X - L), ((((L + i + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      have hsets : Icc (L + 1) X = Ico (L + 1) (X + 1) := by
        ext n
        simp
      rw [hsets, Finset.sum_Ico_eq_sum_range]
      have hlen : X + 1 - (L + 1) = X - L := by omega
      rw [hlen]
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      omega
    rw [hrewrite]
    calc
      (∑ i ∈ range (X - L), ((((L + i + 1 : ℕ) : ℝ) ^ 2)⁻¹)) ≤
          ∑ i ∈ range (X - L),
            (((L + i : ℕ) : ℝ)⁻¹ - ((L + i + 1 : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Nat.add_assoc] using
          (inv_sq_le_inv_pred_sub_inv (n := L + i + 1) (by omega))
      _ = (L : ℝ)⁻¹ - (X : ℝ)⁻¹ := by
        change (range (X - L)).sum (fun i ↦
          (fun j : ℕ ↦ ((L + j : ℕ) : ℝ)⁻¹) i -
            (fun j : ℕ ↦ ((L + j : ℕ) : ℝ)⁻¹) (i + 1)) = _
        rw [Finset.sum_range_sub']
        simp [Nat.add_sub_of_le (le_of_lt hLX)]
      _ ≤ (L : ℝ)⁻¹ := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg X))
  · have hempty : Icc (L + 1) X = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    simp [hempty, inv_nonneg.mpr (show (0 : ℝ) ≤ L by positivity)]

/-- Square reciprocal mass of prime powers in `(L,X]`. -/
def primePowerSquareTail (X L : ℕ) : ℝ :=
  ∑ q ∈ largePrimePowers X L, ((q : ℝ) ^ 2)⁻¹

/-- A logarithmically dilated intermediate cutoff. -/
def logDilate (L : ℕ) : ℕ :=
  L * ⌈Real.log (L : ℝ)⌉₊

/-- The small-prime/large-prime transition used by Martin's exact correction. -/
def naturalLogCutoff (y : ℕ) : ℕ :=
  ⌊Real.log (y : ℝ)⌋₊

lemma primePowerSquareTail_nonneg (X L : ℕ) :
    0 ≤ primePowerSquareTail X L := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (sq_nonneg _)

/-- Split a square tail at an intermediate point `U`.  Below `U` one gains a
factor `1/L` against the Mertens tail; above `U` the full integer square tail
costs only `1/U`. -/
lemma primePowerSquareTail_le_split (X L U : ℕ) (hL : 1 ≤ L) (hU : 1 ≤ U) :
    primePowerSquareTail X L ≤
      (L : ℝ)⁻¹ * primePowerReciprocalTail U L + (U : ℝ)⁻¹ := by
  let S := largePrimePowers X L
  have hsplit :
      primePowerSquareTail X L =
        ∑ q ∈ S.filter (fun q ↦ q ≤ U), ((q : ℝ) ^ 2)⁻¹ +
          ∑ q ∈ S.filter (fun q ↦ U < q), ((q : ℝ) ^ 2)⁻¹ := by
    change (∑ q ∈ S, ((q : ℝ) ^ 2)⁻¹) = _
    rw [← Finset.sum_filter_add_sum_filter_not S (fun q ↦ q ≤ U)]
    simp only [not_le]
  rw [hsplit]
  apply add_le_add
  · calc
      (∑ q ∈ S.filter (fun q ↦ q ≤ U), ((q : ℝ) ^ 2)⁻¹) ≤
          ∑ q ∈ S.filter (fun q ↦ q ≤ U),
            (L : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro q hq
        have hLq : L ≤ q := by
          rcases Finset.mem_filter.mp hq with ⟨hqS, -⟩
          exact le_of_lt ((mem_largePrimePowers.mp hqS).1)
        have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hL.trans hLq
        rw [show ((q : ℝ) ^ 2)⁻¹ = (q : ℝ)⁻¹ * (q : ℝ)⁻¹ by
          rw [sq, mul_inv]]
        exact mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ hqpos hLpos).2 (by exact_mod_cast hLq))
          (inv_nonneg.mpr (le_of_lt hqpos))
      _ ≤ ∑ q ∈ largePrimePowers U L,
          (L : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqS, hqU⟩
          rw [mem_largePrimePowers] at hqS ⊢
          exact ⟨hqS.1, hqU, hqS.2.2⟩
        · intro q hq hqnot
          positivity
      _ = (L : ℝ)⁻¹ * primePowerReciprocalTail U L := by
        simp [primePowerReciprocalTail, Finset.mul_sum]
  · calc
      (∑ q ∈ S.filter (fun q ↦ U < q), ((q : ℝ) ^ 2)⁻¹) ≤
          ∑ q ∈ Icc (U + 1) X, ((q : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqS, hUq⟩
          rw [Finset.mem_Icc]
          exact ⟨hUq, (mem_largePrimePowers.mp hqS).2.1⟩
        · intro q hq hqnot
          positivity
      _ ≤ (U : ℝ)⁻¹ := by
        exact sum_Icc_inv_sq_le_inv U X hU

/-- Moving-endpoint form of the prime-power Mertens tail. -/
lemma primePowerReciprocalTail_between_tendsto_zero {L U : ℕ → ℕ}
    (hLU : ∀ᶠ n : ℕ in atTop, L n ≤ U n)
    (hLtop : Tendsto L atTop atTop)
    (hlog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (U n : ℝ)) -
        Real.log (Real.log (L n : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ primePowerReciprocalTail (U n) (L n)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_primePowerReciprocalUpTo_error_tendsto_zero
  have hUtop : Tendsto U atTop atTop := by
    exact tendsto_atTop_mono' atTop hLU hLtop
  have hbL := hb.comp hLtop
  have hbU := hb.comp hUtop
  have hsum := hlog.add (hbU.sub hbL)
  have hsum0 : Tendsto
      (fun n : ℕ ↦
        Real.log (Real.log (U n : ℝ)) - Real.log (Real.log (L n : ℝ)) +
          ((primePowerReciprocalUpTo (U n) -
              (Real.log (Real.log (U n : ℝ)) + b)) -
            (primePowerReciprocalUpTo (L n) -
              (Real.log (Real.log (L n : ℝ)) + b)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hsum
  apply hsum0.congr'
  filter_upwards [hLU] with n hle
  rw [primePowerReciprocalTail_eq_sub hle]
  ring

lemma logDilate_eventually_one_le :
    ∀ᶠ L : ℕ in atTop, 1 ≤ logDilate L := by
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with L hL hlog
  try simp only [Set.mem_ofPred_eq] at hlog
  exact Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (Nat.one_le_iff_ne_zero.mp hL)
      (Nat.one_le_iff_ne_zero.mp (Nat.one_le_ceil_iff.mpr hlog)))

lemma eventually_le_logDilate :
    ∀ᶠ L : ℕ in atTop, L ≤ logDilate L := by
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with L hlog
  try simp only [Set.mem_ofPred_eq] at hlog
  exact Nat.le_mul_of_pos_right L (Nat.ceil_pos.mpr hlog)

lemma logDilate_tendsto_atTop : Tendsto logDilate atTop atTop := by
  exact tendsto_atTop_mono' atTop eventually_le_logDilate tendsto_id

lemma ceil_log_ratio_tendsto_one :
    Tendsto
      (fun L : ℕ ↦ (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
  exact tendsto_nat_ceil_div_atTop.comp tendsto_log_coe_at_top

lemma log_ceil_log_div_log_tendsto_zero :
    Tendsto
      (fun L : ℕ ↦ Real.log (⌈Real.log (L : ℝ)⌉₊ : ℝ) /
        Real.log (L : ℝ)) atTop (𝓝 0) := by
  let ratio : ℕ → ℝ := fun L ↦
    (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ)
  have hratio : Tendsto ratio atTop (𝓝 1) := by
    simpa [ratio] using ceil_log_ratio_tendsto_one
  have hlogratio : Tendsto (fun L ↦ Real.log (ratio L)) atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  have hlogratioDiv : Tendsto
      (fun L ↦ Real.log (ratio L) / Real.log (L : ℝ)) atTop (𝓝 0) :=
    hlogratio.div_atTop tendsto_log_coe_at_top
  have hsum := hlogratioDiv.add loglog_div_log_tendsto_zero
  have hsum0 : Tendsto
      (fun L : ℕ ↦ Real.log (ratio L) / Real.log (L : ℝ) +
        Real.log (Real.log (L : ℝ)) / Real.log (L : ℝ))
      atTop (𝓝 0) := by simpa using hsum
  apply hsum0.congr'
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds zero_lt_one)] with L hlog hrat
  try simp only [Set.mem_ofPred_eq] at hlog hrat
  have hceilpos : (0 : ℝ) < ⌈Real.log (L : ℝ)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr hlog
  have heq : (⌈Real.log (L : ℝ)⌉₊ : ℝ) = ratio L * Real.log (L : ℝ) := by
    dsimp [ratio]
    exact (div_mul_cancel₀ _ (ne_of_gt hlog)).symm
  rw [heq]
  have hlogmul : Real.log (ratio L * Real.log (L : ℝ)) =
      Real.log (ratio L) + Real.log (Real.log (L : ℝ)) :=
    Real.log_mul (ne_of_gt hrat) (ne_of_gt hlog)
  rw [hlogmul]
  field_simp [ne_of_gt hlog]
  try ring

lemma log_logDilate_div_log_tendsto_one :
    Tendsto
      (fun L : ℕ ↦ Real.log (logDilate L : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
  have hmain : Tendsto
      (fun L : ℕ ↦ (1 : ℝ) +
        Real.log (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add log_ceil_log_div_log_tendsto_zero)
  apply hmain.congr'
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with L hL hlog
  try simp only [Set.mem_ofPred_eq] at hlog
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hceil : 0 < ⌈Real.log (L : ℝ)⌉₊ := Nat.ceil_pos.mpr hlog
  rw [logDilate, Nat.cast_mul,
    Real.log_mul (ne_of_gt hLR) (by exact_mod_cast (ne_of_gt hceil))]
  field_simp [ne_of_gt hlog]
  try ring

lemma logDilate_loglog_sub_tendsto_zero :
    Tendsto
      (fun L : ℕ ↦ Real.log (Real.log (logDilate L : ℝ)) -
        Real.log (Real.log (L : ℝ))) atTop (𝓝 0) := by
  have hratio := log_logDilate_div_log_tendsto_one
  have hlogratio : Tendsto
      (fun L : ℕ ↦ Real.log
        (Real.log (logDilate L : ℝ) / Real.log (L : ℝ)))
      atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  apply hlogratio.congr'
  have hlogDilateTop : Tendsto (fun L ↦ Real.log (logDilate L : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp logDilate_tendsto_atTop)
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hlogDilateTop.eventually (eventually_gt_atTop (0 : ℝ))] with L hL hU
  try simp only [Set.mem_ofPred_eq] at hL hU
  rw [Real.log_div (ne_of_gt hU) (ne_of_gt hL)]

lemma logDilate_ratio_tendsto_zero :
    Tendsto (fun L : ℕ ↦ (L : ℝ) / logDilate L) atTop (𝓝 0) := by
  have hceilTop : Tendsto (fun L : ℕ ↦ (⌈Real.log (L : ℝ)⌉₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_ceil_atTop.comp tendsto_log_coe_at_top)
  have hinv := tendsto_inv_atTop_zero.comp hceilTop
  apply hinv.congr'
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with L hL hlog
  try simp only [Set.mem_ofPred_eq] at hlog
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have hceil : (⌈Real.log (L : ℝ)⌉₊ : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.ceil_pos.mpr hlog))
  simp only [logDilate, Nat.cast_mul]
  dsimp [Function.comp_def]
  field_simp [hLR, hceil]

lemma naturalLogCutoff_tendsto_atTop :
    Tendsto naturalLogCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp tendsto_log_coe_at_top

lemma primePowerSquareTail_scaled_tendsto_zero
    {X L U : ℕ → ℕ}
    (hLone : ∀ᶠ n : ℕ in atTop, 1 ≤ L n)
    (hUone : ∀ᶠ n : ℕ in atTop, 1 ≤ U n)
    (hLU : ∀ᶠ n : ℕ in atTop, L n ≤ U n)
    (hLtop : Tendsto L atTop atTop)
    (hlog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (U n : ℝ)) -
        Real.log (Real.log (L n : ℝ))) atTop (𝓝 0))
    (hratio : Tendsto (fun n : ℕ ↦ (L n : ℝ) / U n) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦ (L n : ℝ) * primePowerSquareTail (X n) (L n))
      atTop (𝓝 0) := by
  have hpp := primePowerReciprocalTail_between_tendsto_zero hLU hLtop hlog
  have hupper : Tendsto
      (fun n : ℕ ↦ primePowerReciprocalTail (U n) (L n) +
        (L n : ℝ) / U n) atTop (𝓝 0) := by
    simpa using hpp.add hratio
  apply squeeze_zero'
  · filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _) (primePowerSquareTail_nonneg _ _)
  · filter_upwards [hLone, hUone] with n hLn hUn
    have hLpos : (0 : ℝ) < L n := by exact_mod_cast hLn
    calc
      (L n : ℝ) * primePowerSquareTail (X n) (L n) ≤
          (L n : ℝ) *
            ((L n : ℝ)⁻¹ * primePowerReciprocalTail (U n) (L n) +
              (U n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (primePowerSquareTail_le_split (X n) (L n) (U n) hLn hUn)
          (Nat.cast_nonneg _)
      _ = primePowerReciprocalTail (U n) (L n) + (L n : ℝ) / U n := by
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hLpos), one_mul]
        rfl
  · exact hupper

lemma primePowerSquareTail_nat_scaled_tendsto_zero (X : ℕ → ℕ) :
    Tendsto (fun L : ℕ ↦ (L : ℝ) * primePowerSquareTail (X L) L)
      atTop (𝓝 0) := by
  exact primePowerSquareTail_scaled_tendsto_zero
    (eventually_ge_atTop 1)
    logDilate_eventually_one_le
    eventually_le_logDilate
    tendsto_id
    logDilate_loglog_sub_tendsto_zero
    logDilate_ratio_tendsto_zero

lemma naturalLogCutoff_ratio_tendsto_one :
    Tendsto
      (fun y : ℕ ↦ (naturalLogCutoff y : ℝ) / Real.log (y : ℝ))
      atTop (𝓝 1) := by
  exact tendsto_nat_floor_div_atTop.comp tendsto_log_coe_at_top

/-- Proposition 7 square-cost estimate in limit form.  Multiplying the finite
prime-power square tail above `floor(log y)` by `log y` still tends to zero. -/
theorem ten_mul_primePowerSquareTail_mul_log_tendsto_zero :
    Tendsto
      (fun y : ℕ ↦
        10 * primePowerSquareTail y (naturalLogCutoff y) * Real.log (y : ℝ))
      atTop (𝓝 0) := by
  let L := naturalLogCutoff
  let U : ℕ → ℕ := fun y ↦ logDilate (L y)
  have hLtop : Tendsto L atTop atTop := naturalLogCutoff_tendsto_atTop
  have hscaled : Tendsto
      (fun y : ℕ ↦ (L y : ℝ) * primePowerSquareTail y (L y))
      atTop (𝓝 0) := by
    apply primePowerSquareTail_scaled_tendsto_zero
    · exact hLtop.eventually (eventually_ge_atTop 1)
    · exact logDilate_eventually_one_le.filter_mono hLtop
    · exact eventually_le_logDilate.filter_mono hLtop
    · exact hLtop
    · exact logDilate_loglog_sub_tendsto_zero.comp hLtop
    · exact logDilate_ratio_tendsto_zero.comp hLtop
  have hreverse : Tendsto
      (fun y : ℕ ↦ Real.log (y : ℝ) / (L y : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto
        (fun y : ℕ ↦ ((naturalLogCutoff y : ℝ) / Real.log (y : ℝ))⁻¹)
        atTop (𝓝 (1⁻¹ : ℝ)) :=
      naturalLogCutoff_ratio_tendsto_one.inv₀ one_ne_zero
    have hinv1 : Tendsto
        (fun y : ℕ ↦ ((naturalLogCutoff y : ℝ) / Real.log (y : ℝ))⁻¹)
        atTop (𝓝 1) := by
      norm_num at hinv ⊢
      exact hinv
    have heq : (fun y : ℕ ↦ ((naturalLogCutoff y : ℝ) / Real.log (y : ℝ))⁻¹) =ᶠ[atTop]
        (fun y : ℕ ↦ Real.log (y : ℝ) / (L y : ℝ)) := by
      have hLpos := hLtop.eventually (eventually_ge_atTop 1)
      have hlogpos := tendsto_log_coe_at_top.eventually
        (eventually_gt_atTop (0 : ℝ))
      apply (hLpos.and hlogpos).mono
      intro y hy
      rcases hy with ⟨hLy, hlogy⟩
      have hLyne : (L y : ℝ) ≠ 0 := by exact_mod_cast (by omega : L y ≠ 0)
      have hlogne : Real.log (y : ℝ) ≠ 0 := ne_of_gt hlogy
      dsimp [L]
      field_simp
    exact hinv1.congr' heq
  have hprod := hreverse.mul hscaled
  have hprod0 : Tendsto
      (fun y : ℕ ↦ Real.log (y : ℝ) *
        primePowerSquareTail y (L y)) atTop (𝓝 0) := by
    have hprod' : Tendsto
        (fun y : ℕ ↦ Real.log (y : ℝ) / (L y : ℝ) *
          ((L y : ℝ) * primePowerSquareTail y (L y)))
        atTop (𝓝 0) := by simpa using hprod
    apply hprod'.congr'
    filter_upwards
      [hLtop.eventually (eventually_ge_atTop 1)] with y hLy
    try simp only [Set.mem_ofPred_eq] at hLy
    have hLne : (L y : ℝ) ≠ 0 := by exact_mod_cast (by omega : L y ≠ 0)
    field_simp
  simpa [L, mul_assoc, mul_comm, mul_left_comm] using hprod0.const_mul 10

/-- Epsilon form consumed by the exact-correction recursion. -/
theorem eventually_ten_mul_primePowerSquareTail_lt_div_log
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop,
      10 * primePowerSquareTail y (naturalLogCutoff y) <
        c / Real.log (y : ℝ) := by
  have hsmall := ten_mul_primePowerSquareTail_mul_log_tendsto_zero.eventually
    (Metric.ball_mem_nhds 0 hc)
  filter_upwards
    [hsmall,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with y hy hlog
  try simp only [Set.mem_ofPred_eq] at hy hlog
  rw [dist_zero_right, Real.norm_eq_abs] at hy
  rw [lt_div_iff₀ hlog]
  exact (le_abs_self _).trans_lt hy

/-- The weighted square tail in the literal finite-sum form used by the recursion. -/
lemma ten_mul_primePowerSquareTail_eq_sum (X L : ℕ) :
    10 * primePowerSquareTail X L =
      ∑ q ∈ largePrimePowers X L, 10 / (q : ℝ) ^ 2 := by
  simp [primePowerSquareTail, Finset.mul_sum, div_eq_mul_inv]

/-- Direct finite-sum form of the Proposition 7 square-cost estimate. -/
theorem eventually_sum_ten_div_primePower_sq_lt_div_log
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop,
      (∑ q ∈ largePrimePowers y (naturalLogCutoff y), 10 / (q : ℝ) ^ 2) <
        c / Real.log (y : ℝ) := by
  filter_upwards [eventually_ten_mul_primePowerSquareTail_lt_div_log hc] with y hy
  rw [← ten_mul_primePowerSquareTail_eq_sum]
  exact hy

end




/-!
# Martin's Proposition 7: descent and cardinality bookkeeping

This file contains the part of Proposition 7 which is independent of the
congruence calculations in Lemmas 15 and 16.  An `EliminationStep` records the
output of either lemma.  Its new rational has a strictly smaller largest exact
prime-power part, and every denominator introduced at the step is tagged by
the part which was eliminated.  Strong induction then proves termination,
pairwise distinctness of all denominators, and the bound `2 * piStar y` on the
number of terms.

The final section proves the finite-set bookkeeping for Martin's telescoping
padding operation.  Replacing the largest denominator `n` by `m + 1` larger
denominators increases the cardinality by exactly `m`, preserves the reciprocal
sum, and gives an explicit square bound for every new denominator.
-/

open Finset
open scoped BigOperators

noncomputable section

lemma initialLcm_mono {x y : ℕ} (hxy : x ≤ y) :
    initialLcm x ≤ initialLcm y := by
  have hdiv : initialLcm x ∣ initialLcm y := by
    apply Finset.lcm_dvd
    intro n hn
    exact Finset.dvd_lcm (s := Icc 1 y) (f := id)
      (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hxy⟩)
  have hpos : 0 < initialLcm y := Nat.pos_of_ne_zero (by simp [initialLcm])
  exact Nat.le_of_dvd hpos hdiv

/-! ## Strict growth of the prime-power counting function -/

/-- Passing a prime-power endpoint strictly increases `piStar`. -/
lemma piStar_lt_of_lt_of_isPrimePow {x q : ℕ} (hxq : x < q)
    (hq : IsPrimePow q) : piStar x < piStar q := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨primePowersUpTo_mono (le_of_lt hxq), ?_⟩
  intro heq
  have hqmem : q ∈ primePowersUpTo q := mem_primePowersUpTo.mpr ⟨hq, le_rfl⟩
  have : q ∈ primePowersUpTo x := heq.symm ▸ hqmem
  exact (not_le_of_gt hxq) (mem_primePowersUpTo.mp this).2

lemma piStar_eq_succ_pred_of_isPrimePow {q : ℕ} (hq : IsPrimePow q) :
    piStar q = piStar (q - 1) + 1 := by
  have hqpos : 0 < q := hq.pos
  have hqnot : q ∉ primePowersUpTo (q - 1) := by
    intro hmem
    have hle := (mem_primePowersUpTo.mp hmem).2
    omega
  have heq : primePowersUpTo q = insert q (primePowersUpTo (q - 1)) := by
    ext t
    rw [mem_primePowersUpTo]
    simp only [Finset.mem_insert, mem_primePowersUpTo]
    constructor
    · rintro ⟨htpp, htq⟩
      by_cases ht : t = q
      · exact Or.inl ht
      · exact Or.inr ⟨htpp, by omega⟩
    · rintro (rfl | ⟨htpp, htq⟩)
      · exact ⟨hq, le_rfl⟩
      · exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩
  rw [piStar, piStar, heq, Finset.card_insert_of_notMem hqnot]

lemma piStar_eq_pred_of_not_isPrimePow {q : ℕ} (hq : ¬ IsPrimePow q) :
    piStar q = piStar (q - 1) := by
  have heq : primePowersUpTo q = primePowersUpTo (q - 1) := by
    ext t
    rw [mem_primePowersUpTo, mem_primePowersUpTo]
    constructor
    · rintro ⟨htpp, htq⟩
      exact ⟨htpp, by
        by_cases ht : t = q
        · exact False.elim (hq (ht ▸ htpp))
        · have htpos := htpp.pos
          omega⟩
    · rintro ⟨htpp, htq⟩
      exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩
  change (primePowersUpTo q).card = (primePowersUpTo (q - 1)).card
  exact congrArg Finset.card heq

/-! ## A generic Lemma 15/16 step -/

/--
The common output needed from Martin's Lemmas 15 and 16 at a rational `r`.

The concrete lemmas additionally provide interval and exponential estimates.
Those estimates imply `le_bound`; the recursion itself needs only the fields
below.  `tagged` is what makes denominators introduced at different stages
automatically distinct.
-/
structure EliminationStep (B : ℕ) (r : ℚ) (U : Finset ℕ) : Prop where
  card_le_two : U.card ≤ 2
  zero_not_mem : 0 ∉ U
  le_bound : ∀ n ∈ U, n ≤ B
  tagged : ∀ n ∈ U,
    largestPrimePowerPart n = largestPrimePowerPart r.den
  descends :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den <
      largestPrimePowerPart r.den

/-- Lemma 16 supplies the concrete current-factor step below `lo`.  The sole
numerical input is the source bound `initialLcm lo ≤ B`. -/
theorem exists_eliminationStep_of_lemma16
    (B lo : ℕ) (hL : initialLcm lo ≤ B)
    (r : ℚ) (hden : r.den ≠ 1)
    (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ U : Finset ℕ, EliminationStep B r U := by
  have hden2 : 2 ≤ r.den := by
    have := r.den_pos
    omega
  let q := largestPrimePowerPart r.den
  have hqpp : IsPrimePow q := (largestPrimePowerPart_spec hden2).1
  obtain ⟨p, e, hp, he, hqpow⟩ := (isPrimePow_nat_iff q).mp hqpp
  obtain ⟨a, n, haPos, haLe, hpa, haL, hnEq, hnLower, hqN, hqNpart,
      hnSmooth, hnLargest, hdesc⟩ :=
    smallPrimePower_elimination (p := p) (e := e) (q := q)
      r hp he hqpow.symm rfl
  have hnPos : 0 < n := by
    rw [hnEq]
    have hLpos : 0 < initialLcm q :=
      Nat.pos_of_ne_zero (by simp [initialLcm])
    exact Nat.div_pos
      (Nat.le_of_dvd hLpos haL) haPos
  have hnLeLq : n ≤ initialLcm q := by
    rw [hnEq]
    exact Nat.div_le_self _ _
  have hnB : n ≤ B :=
    hnLeLq.trans ((initialLcm_mono hrlo).trans hL)
  refine ⟨{n}, ?_⟩
  refine
    { card_le_two := by simp
      zero_not_mem := by
        simp only [Finset.mem_singleton]
        exact (ne_of_gt hnPos).symm
      le_bound := ?_
      tagged := ?_
      descends := ?_ }
  · intro m hm
    simp only [Finset.mem_singleton] at hm
    subst m
    exact hnB
  · intro m hm
    simp only [Finset.mem_singleton] at hm
    subst m
    exact hnLargest
  · simpa [UnitFractions.rec_sum] using hdesc

/-- A Lemma 16 step together with its exact share of the telescoping
reciprocal budget. -/
structure SmallEliminationStep (B : ℕ) (r : ℚ) (U : Finset ℕ) : Prop
    extends EliminationStep B r U where
  card_le_one : U.card ≤ 1
  rec_sum_le_cost : UnitFractions.rec_sum U ≤
    primePowerCost (largestPrimePowerPart r.den)

theorem exists_smallEliminationStep_of_lemma16
    (B lo : ℕ) (hL : initialLcm lo ≤ B)
    (r : ℚ) (hden : r.den ≠ 1)
    (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ U : Finset ℕ, SmallEliminationStep B r U := by
  have hden2 : 2 ≤ r.den := by
    have := r.den_pos
    omega
  let q := largestPrimePowerPart r.den
  have hqpp : IsPrimePow q := (largestPrimePowerPart_spec hden2).1
  obtain ⟨p, e, hp, he, hqpow⟩ := (isPrimePow_nat_iff q).mp hqpp
  obtain ⟨a, n, haPos, haLe, hpa, haL, hnEq, hnLower, hqN, hqNpart,
      hnSmooth, hnLargest, hdesc⟩ :=
    smallPrimePower_elimination (p := p) (e := e) (q := q)
      r hp he hqpow.symm rfl
  have hLpos : 0 < initialLcm q :=
    Nat.pos_of_ne_zero (by simp [initialLcm])
  have hnPos : 0 < n := by
    rw [hnEq]
    exact Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos
  have hnLeLq : n ≤ initialLcm q := by
    rw [hnEq]
    exact Nat.div_le_self _ _
  have hnB : n ≤ B :=
    hnLeLq.trans ((initialLcm_mono hrlo).trans hL)
  have hunitEq : (1 : ℚ) / n = (a : ℚ) / initialLcm q := by
    rw [hnEq, Nat.cast_div_charZero haL]
    have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hLQ : (initialLcm q : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt hLpos)
    field_simp [haQ, hLQ]
  have hcost : (1 : ℚ) / n ≤ primePowerCost q := by
    have hmin : q.minFac = p := by
      rw [← hqpow, hp.pow_minFac (ne_of_gt he)]
    rw [hunitEq, primePowerCost, hmin]
    exact (div_le_div_iff_of_pos_right (by exact_mod_cast hLpos)).2
      (by exact_mod_cast haLe)
  refine ⟨{n}, ?_⟩
  refine
    { toEliminationStep :=
        { card_le_two := by simp
          zero_not_mem := by simpa using hnPos.ne
          le_bound := by
            intro m hm
            simp only [Finset.mem_singleton] at hm
            subst m
            exact hnB
          tagged := by
            intro m hm
            simp only [Finset.mem_singleton] at hm
            subst m
            exact hnLargest
          descends := by simpa [UnitFractions.rec_sum] using hdesc }
      card_le_one := by simp
      rec_sum_le_cost := by simpa [UnitFractions.rec_sum, q] using hcost }

/--
The result of running all elimination steps.  The final residual is an integer;
`tag_le` remembers enough information to prove disjointness at the preceding
recursive stage.
-/
structure EliminationResult (B : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ 2 * piStar (largestPrimePowerPart r.den)
  tag_le : ∀ n ∈ E,
    largestPrimePowerPart n ≤ largestPrimePowerPart r.den
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z

/-- The Lemma 16 descent with the reciprocal cost retained.  Since Lemma 16
adds one denominator at each visited prime power, its cost is bounded by the
exact LCM telescope below the initial largest part. -/
structure SmallEliminationResult (B : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ piStar (largestPrimePowerPart r.den)
  tag_le : ∀ n ∈ E,
    largestPrimePowerPart n ≤ largestPrimePowerPart r.den
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z
  rec_sum_le_cost : UnitFractions.rec_sum E ≤
    smallPrimePowerCost (largestPrimePowerPart r.den)

/-- Complete current-factor Lemma 16 descent, including Martin's telescoping
budget. -/
theorem exists_smallEliminationResult_of_lemma16
    (B lo : ℕ) (hL : initialLcm lo ≤ B)
    (r : ℚ) (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ E : Finset ℕ, SmallEliminationResult B r E := by
  suffices hmain : ∀ q : ℕ, ∀ s : ℚ,
      largestPrimePowerPart s.den = q → q ≤ lo →
        ∃ E : Finset ℕ, SmallEliminationResult B s E by
    exact hmain (largestPrimePowerPart r.den) r rfl hrlo
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro s hqeq hqlo
      by_cases hden : s.den = 1
      · refine ⟨∅, ?_⟩
        refine
          { zero_not_mem := by simp
            le_bound := by simp
            card_le := by simp
            tag_le := by simp
            residual_isInt := ?_
            rec_sum_le_cost := ?_ }
        · simpa using isInt_of_primePowerParts_empty
            ((den_eq_one_iff_primePowerParts_empty s).mp hden)
        · simp only [UnitFractions.rec_sum, Finset.sum_empty]
          rw [smallPrimePowerCost]
          exact Finset.sum_nonneg fun t _ ↦
            primePowerCost_nonneg t
      · obtain ⟨U, hU⟩ :=
          exists_smallEliminationStep_of_lemma16 B lo hL s hden
            (hqeq.trans_le hqlo)
        let s' : ℚ := s - UnitFractions.rec_sum U
        have hdesc : largestPrimePowerPart s'.den < q := by
          simpa [s', hqeq] using hU.descends
        obtain ⟨E, hE⟩ := ih (largestPrimePowerPart s'.den) hdesc s' rfl
          ((le_of_lt hdesc).trans hqlo)
        have hden2 : 2 ≤ s.den := by
          have := s.den_pos
          omega
        have hqpp : IsPrimePow q := by
          rw [← hqeq]
          exact (largestPrimePowerPart_spec hden2).1
        have hpi : piStar (largestPrimePowerPart s'.den) < piStar q :=
          piStar_lt_of_lt_of_isPrimePow hdesc hqpp
        have hdisjoint : Disjoint U E := by
          rw [Finset.disjoint_left]
          intro n hnU hnE
          have htagU : largestPrimePowerPart n = q := by
            simpa [hqeq] using hU.tagged n hnU
          have htagE := hE.tag_le n hnE
          omega
        refine ⟨U ∪ E, ?_⟩
        refine
          { zero_not_mem := ?_
            le_bound := ?_
            card_le := ?_
            tag_le := ?_
            residual_isInt := ?_
            rec_sum_le_cost := ?_ }
        · simpa only [Finset.mem_union, not_or] using
            ⟨hU.zero_not_mem, hE.zero_not_mem⟩
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · exact hU.le_bound n hnU
          · exact hE.le_bound n hnE
        · rw [Finset.card_union_of_disjoint hdisjoint]
          calc
            U.card + E.card ≤ 1 + piStar (largestPrimePowerPart s'.den) :=
              Nat.add_le_add hU.card_le_one hE.card_le
            _ ≤ piStar q := by omega
            _ = piStar (largestPrimePowerPart s.den) := by rw [hqeq]
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · rw [hU.tagged n hnU, hqeq]
          · exact (hE.tag_le n hnE).trans (le_of_lt hdesc) |>.trans_eq hqeq.symm
        · obtain ⟨z, hz⟩ := hE.residual_isInt
          refine ⟨z, ?_⟩
          rw [UnitFractions.rec_sum_disjoint hdisjoint]
          dsimp [s'] at hz
          linarith
        · rw [UnitFractions.rec_sum_disjoint hdisjoint]
          calc
            UnitFractions.rec_sum U + UnitFractions.rec_sum E ≤
                primePowerCost q +
                  smallPrimePowerCost
                    (largestPrimePowerPart s'.den) := by
              exact add_le_add (by simpa [hqeq] using hU.rec_sum_le_cost)
                hE.rec_sum_le_cost
            _ ≤ smallPrimePowerCost q :=
              primePowerCost_add_smallPrimePowerCost_of_lt
                hdesc hqpp
            _ = smallPrimePowerCost
                (largestPrimePowerPart s.den) := by rw [hqeq]

/-- A rational integer of absolute value less than one is zero. -/
lemma eq_zero_of_isInt_of_abs_lt_one {r : ℚ} (hint : ∃ z : ℤ, r = z)
    (hr : |r| < 1) : r = 0 := by
  obtain ⟨z, rfl⟩ := hint
  have hz : |z| < 1 := by exact_mod_cast hr
  have hznonneg : 0 ≤ |z| := abs_nonneg z
  have habs : |z| = 0 := by omega
  simp only [abs_eq_zero] at habs
  simp [habs]

/-- The terminal integer residual is zero as soon as the independent size
estimate places it in `(-1,1)`. -/
lemma EliminationResult.residual_eq_zero {B : ℕ} {r : ℚ} {E : Finset ℕ}
    (h : EliminationResult B r E)
    (hsmall : |r - UnitFractions.rec_sum E| < 1) :
    r - UnitFractions.rec_sum E = 0 :=
  eq_zero_of_isInt_of_abs_lt_one h.residual_isInt hsmall

/--
Well-founded prime-power elimination.

The argument `step` is an ordinary theorem argument.  Supplying the concrete
Lemma 15 branch above the logarithmic cutoff and the Lemma 16 branch below it
therefore introduces no new declaration-level assumption.
-/
theorem exists_eliminationResult
    (B : ℕ)
    (step : ∀ r : ℚ, r.den ≠ 1 →
      ∃ U : Finset ℕ, EliminationStep B r U)
    (r : ℚ) :
    ∃ E : Finset ℕ, EliminationResult B r E := by
  suffices hmain : ∀ q : ℕ, ∀ r : ℚ,
      largestPrimePowerPart r.den = q →
        ∃ E : Finset ℕ, EliminationResult B r E by
    exact hmain (largestPrimePowerPart r.den) r rfl
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro r hqeq
      by_cases hden : r.den = 1
      · refine ⟨∅, ?_⟩
        refine
          { zero_not_mem := by simp
            le_bound := by simp
            card_le := by simp
            tag_le := by simp
            residual_isInt := ?_ }
        have hempty : primePowerParts r.den = ∅ :=
          (den_eq_one_iff_primePowerParts_empty r).mp hden
        simpa using isInt_of_primePowerParts_empty (r := r) hempty
      · obtain ⟨U, hU⟩ := step r hden
        let r' : ℚ := r - UnitFractions.rec_sum U
        have hdesc : largestPrimePowerPart r'.den < q := by
          simpa [r', hqeq] using hU.descends
        obtain ⟨E, hE⟩ := ih (largestPrimePowerPart r'.den) hdesc r' rfl
        have hden2 : 2 ≤ r.den := by
          have := r.den_pos
          omega
        have hqpp : IsPrimePow q := by
          rw [← hqeq]
          exact (largestPrimePowerPart_spec hden2).1
        have hpi : piStar (largestPrimePowerPart r'.den) < piStar q :=
          piStar_lt_of_lt_of_isPrimePow hdesc hqpp
        have hdisjoint : Disjoint U E := by
          rw [Finset.disjoint_left]
          intro n hnU hnE
          have htagU : largestPrimePowerPart n = q := by
            simpa [hqeq] using hU.tagged n hnU
          have htagE : largestPrimePowerPart n ≤
              largestPrimePowerPart r'.den := hE.tag_le n hnE
          omega
        refine ⟨U ∪ E, ?_⟩
        refine
          { zero_not_mem := ?_
            le_bound := ?_
            card_le := ?_
            tag_le := ?_
            residual_isInt := ?_ }
        · simpa only [Finset.mem_union, not_or] using
            ⟨hU.zero_not_mem, hE.zero_not_mem⟩
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · exact hU.le_bound n hnU
          · exact hE.le_bound n hnE
        · rw [Finset.card_union_of_disjoint hdisjoint]
          calc
            U.card + E.card ≤ 2 + 2 * piStar (largestPrimePowerPart r'.den) :=
              Nat.add_le_add hU.card_le_two hE.card_le
            _ ≤ 2 * piStar q := by omega
            _ = 2 * piStar (largestPrimePowerPart r.den) := by rw [hqeq]
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · rw [hU.tagged n hnU, hqeq]
          · exact (hE.tag_le n hnE).trans (le_of_lt hdesc) |>.trans_eq hqeq.symm
        · obtain ⟨z, hz⟩ := hE.residual_isInt
          refine ⟨z, ?_⟩
          rw [UnitFractions.rec_sum_disjoint hdisjoint]
          dsimp [r'] at hz
          linarith

/-- A version whose cardinality and tags are bounded by any ambient cutoff
`y` containing the initial largest prime-power part. -/
theorem exists_eliminationResult_le
    (B y : ℕ)
    (step : ∀ r : ℚ, r.den ≠ 1 →
      ∃ U : Finset ℕ, EliminationStep B r U)
    (r : ℚ) (hr : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ,
      0 ∉ E ∧
      (∀ n ∈ E, n ≤ B) ∧
      E.card ≤ 2 * piStar y ∧
      (∀ n ∈ E, largestPrimePowerPart n ≤ y) ∧
      ∃ z : ℤ, r - UnitFractions.rec_sum E = z := by
  obtain ⟨E, hE⟩ := exists_eliminationResult B step r
  refine ⟨E, hE.zero_not_mem, hE.le_bound, ?_, ?_, hE.residual_isInt⟩
  · exact hE.card_le.trans (Nat.mul_le_mul_left 2 (piStar_mono hr))
  · intro n hn
    exact (hE.tag_le n hn).trans hr

/-- The current-factor recursion when the concrete Lemma 16 step is available
only below an ambient cutoff. -/
theorem exists_eliminationResult_below
    (B lo : ℕ)
    (step : ∀ r : ℚ, r.den ≠ 1 →
      largestPrimePowerPart r.den ≤ lo →
        ∃ U : Finset ℕ, EliminationStep B r U)
    (r : ℚ) (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ E : Finset ℕ, EliminationResult B r E := by
  suffices hmain : ∀ q : ℕ, ∀ r : ℚ,
      largestPrimePowerPart r.den = q → q ≤ lo →
        ∃ E : Finset ℕ, EliminationResult B r E by
    exact hmain (largestPrimePowerPart r.den) r rfl hrlo
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro r hqeq hqlo
      by_cases hden : r.den = 1
      · refine ⟨∅, ?_⟩
        refine
          { zero_not_mem := by simp
            le_bound := by simp
            card_le := by simp
            tag_le := by simp
            residual_isInt := ?_ }
        simpa using isInt_of_primePowerParts_empty
          ((den_eq_one_iff_primePowerParts_empty r).mp hden)
      · obtain ⟨U, hU⟩ := step r hden (hqeq.trans_le hqlo)
        let r' : ℚ := r - UnitFractions.rec_sum U
        have hdesc : largestPrimePowerPart r'.den < q := by
          simpa [r', hqeq] using hU.descends
        obtain ⟨E, hE⟩ := ih (largestPrimePowerPart r'.den) hdesc r' rfl
          ((le_of_lt hdesc).trans hqlo)
        have hden2 : 2 ≤ r.den := by
          have := r.den_pos
          omega
        have hqpp : IsPrimePow q := by
          rw [← hqeq]
          exact (largestPrimePowerPart_spec hden2).1
        have hpi : piStar (largestPrimePowerPart r'.den) < piStar q :=
          piStar_lt_of_lt_of_isPrimePow hdesc hqpp
        have hdisjoint : Disjoint U E := by
          rw [Finset.disjoint_left]
          intro n hnU hnE
          have htagU : largestPrimePowerPart n = q := by
            simpa [hqeq] using hU.tagged n hnU
          have htagE := hE.tag_le n hnE
          omega
        refine ⟨U ∪ E, ?_⟩
        refine
          { zero_not_mem := ?_
            le_bound := ?_
            card_le := ?_
            tag_le := ?_
            residual_isInt := ?_ }
        · simpa only [Finset.mem_union, not_or] using
            ⟨hU.zero_not_mem, hE.zero_not_mem⟩
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · exact hU.le_bound n hnU
          · exact hE.le_bound n hnE
        · rw [Finset.card_union_of_disjoint hdisjoint]
          calc
            U.card + E.card ≤
                2 + 2 * piStar (largestPrimePowerPart r'.den) :=
              Nat.add_le_add hU.card_le_two hE.card_le
            _ ≤ 2 * piStar q := by omega
            _ = 2 * piStar (largestPrimePowerPart r.den) := by rw [hqeq]
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · rw [hU.tagged n hnU, hqeq]
          · exact (hE.tag_le n hnE).trans (le_of_lt hdesc) |>.trans_eq hqeq.symm
        · obtain ⟨z, hz⟩ := hE.residual_isInt
          refine ⟨z, ?_⟩
          rw [UnitFractions.rec_sum_disjoint hdisjoint]
          dsimp [r'] at hz
          linarith

/-! ## Scheduling Lemma 15 through all large prime powers -/

/-- The output of Lemma 15 when it is run at a scheduled prime power `q`.
Unlike `EliminationStep`, the scheduled `q` need not currently occur in the
reduced denominator. -/
structure ScheduledStep (r : ℚ) (q : ℕ) (U : Finset ℕ) : Prop where
  card_le_two : U.card ≤ 2
  card_eq_two_of_odd : Odd q → U.card = 2
  zero_not_mem : 0 ∉ U
  tagged : ∀ n ∈ U, largestPrimePowerPart n = q
  lower : ∀ n ∈ U, q ^ 2 ≤ 5 * n
  upper : ∀ n ∈ U, n ≤ q ^ 2
  descends :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q

/-- The total reciprocal majorant charged to the prime-power stages in
`(lo,q]`.  Each Lemma 15 stage costs at most `10/t^2`. -/
def largeSquareCost (lo q : ℕ) : ℝ :=
  ∑ t ∈ largePrimePowers q lo, 10 / (t : ℝ) ^ 2

lemma largePrimePowers_succ_of_isPrimePow {lo q : ℕ} (hloq : lo < q)
    (hq : IsPrimePow q) :
    largePrimePowers q lo =
      insert q (largePrimePowers (q - 1) lo) := by
  ext t
  simp only [largePrimePowers, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    by_cases htq : t = q
    · exact Or.inl htq
    · exact Or.inr ⟨⟨hlt, by omega⟩, htpp⟩
  · rintro (rfl | ⟨⟨hlt, htle⟩, htpp⟩)
    · exact ⟨⟨by omega, le_rfl⟩, hq⟩
    · exact ⟨⟨hlt, htle.trans (Nat.sub_le q 1)⟩, htpp⟩

lemma largePrimePowers_pred_of_not_isPrimePow {lo q : ℕ}
    (hq : ¬ IsPrimePow q) :
    largePrimePowers q lo =
      largePrimePowers (q - 1) lo := by
  ext t
  simp only [largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    exact ⟨⟨hlt, by
      by_cases htq : t = q
      · exact False.elim (hq (htq ▸ htpp))
      · omega⟩, htpp⟩
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    exact ⟨⟨hlt, htle.trans (Nat.sub_le q 1)⟩, htpp⟩

lemma largeSquareCost_succ_of_isPrimePow {lo q : ℕ} (hloq : lo < q)
    (hq : IsPrimePow q) :
    largeSquareCost lo q = largeSquareCost lo (q - 1) + 10 / (q : ℝ) ^ 2 := by
  rw [largeSquareCost, largeSquareCost,
    largePrimePowers_succ_of_isPrimePow hloq hq]
  have hnot : q ∉ largePrimePowers (q - 1) lo := by
    rw [largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [Finset.sum_insert hnot]
  ring

lemma largeSquareCost_pred_of_not_isPrimePow {lo q : ℕ}
    (hq : ¬ IsPrimePow q) :
    largeSquareCost lo q = largeSquareCost lo (q - 1) := by
  simp only [largeSquareCost,
    largePrimePowers_pred_of_not_isPrimePow hq]

lemma ScheduledStep.rec_sum_le_cost {r : ℚ} {q : ℕ} {U : Finset ℕ}
    (hq : IsPrimePow q) (h : ScheduledStep r q U) :
    (UnitFractions.rec_sum U : ℝ) ≤ 10 / (q : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hterm : ∀ n ∈ U, (1 : ℝ) / n ≤ 5 / (q : ℝ) ^ 2 := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (Nat.pos_of_ne_zero (fun hn0 ↦ h.zero_not_mem (hn0 ▸ hn)))
    rw [div_le_div_iff₀ hnpos (sq_pos_of_pos hqpos)]
    norm_num
    exact_mod_cast h.lower n hn
  rw [UnitFractions.rec_sum]
  push_cast
  calc
    (∑ n ∈ U, (1 : ℝ) / n) ≤ U.card * (5 / (q : ℝ) ^ 2) := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul U (fun n ↦ (1 : ℝ) / n)
        (5 / (q : ℝ) ^ 2) hterm
    _ ≤ 2 * (5 / (q : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h.card_le_two)
        (div_nonneg (by positivity) (sq_nonneg _))
    _ = 10 / (q : ℝ) ^ 2 := by ring

/-- The concrete scheduled step supplied by Martin's Lemma 15. -/
theorem exists_scheduledStep_of_lemma15
    (q : ℕ) (hqpp : IsPrimePow q) (hq4 : 4 ≤ q)
    (r : ℚ) (hr : largestPrimePowerPart r.den ≤ q) :
    ∃ U : Finset ℕ, ScheduledStep r q U := by
  obtain ⟨U, hinterval, hodd, heven, htag, hdesc⟩ :=
    exists_elimination_set q hqpp hq4 r hr
  have hcard : U.card ≤ 2 := by
    rcases Nat.even_or_odd q with hqeven | hqodd
    · exact (heven hqeven).trans (by omega)
    · rw [hodd hqodd]
  have hzero : 0 ∉ U := by
    intro h0
    have hlower := (hinterval 0 h0).1
    have hqpos := hqpp.pos
    norm_num at hlower
    omega
  exact ⟨U,
    { card_le_two := hcard
      card_eq_two_of_odd := hodd
      zero_not_mem := hzero
      tagged := htag
      lower := fun n hn ↦ (hinterval n hn).1
      upper := fun n hn ↦ (hinterval n hn).2
      descends := hdesc }⟩

/-- The result of processing every prime power in `(lo,q]`, in decreasing
order. -/
structure ScheduledResult (lo q : ℕ) (r : ℚ)
    (E : Finset ℕ) (s : ℚ) : Prop where
  zero_not_mem : 0 ∉ E
  card_le : E.card ≤ 2 * (piStar q - piStar lo)
  tag_range : ∀ n ∈ E,
    lo < largestPrimePowerPart n ∧ largestPrimePowerPart n ≤ q
  denominator_range : ∀ n ∈ E,
    largestPrimePowerPart n ^ 2 ≤ 5 * n ∧
      n ≤ largestPrimePowerPart n ^ 2
  residual_eq : s = r - UnitFractions.rec_sum E
  residual_smooth : largestPrimePowerPart s.den ≤ lo
  rec_sum_le_cost : (UnitFractions.rec_sum E : ℝ) ≤ largeSquareCost lo q
  odd_stage : ∀ t, lo < t → t ≤ q → IsPrimePow t → Odd t →
    ∃ U ⊆ E, U.card = 2 ∧
      ∀ n ∈ U, largestPrimePowerPart n = t

/--
Run Lemma 15 at every large prime power, including prime powers which do not
occur in the current reduced denominator.  This is the source-faithful
schedule responsible for the eventual near-exact term count.
-/
theorem exists_scheduledResult
    (lo : ℕ) (hlo : 1 ≤ lo)
    (step : ∀ q : ℕ, ∀ r : ℚ, lo < q → IsPrimePow q →
      largestPrimePowerPart r.den ≤ q →
        ∃ U : Finset ℕ, ScheduledStep r q U)
    (q : ℕ) (r : ℚ) (hrq : largestPrimePowerPart r.den ≤ q) :
    ∃ E : Finset ℕ, ∃ s : ℚ, ScheduledResult lo q r E s := by
  induction q using Nat.strong_induction_on generalizing r with
  | h q ih =>
      by_cases hqlo : q ≤ lo
      · refine ⟨∅, r, ?_⟩
        refine
          { zero_not_mem := by simp
            card_le := by
              simp only [Finset.card_empty, zero_le]
            tag_range := by simp
            denominator_range := by simp
            residual_eq := by simp
            residual_smooth := hrq.trans hqlo
            rec_sum_le_cost := by
              simp only [UnitFractions.rec_sum, Finset.sum_empty, Rat.cast_zero]
              exact Finset.sum_nonneg fun _ _ ↦
                div_nonneg (by positivity) (sq_nonneg _)
            odd_stage := ?_ }
        intro t hlot htq
        omega
      · have hloq : lo < q := Nat.lt_of_not_ge hqlo
        by_cases hqpp : IsPrimePow q
        · obtain ⟨U, hU⟩ := step q r hloq hqpp hrq
          let r' : ℚ := r - UnitFractions.rec_sum U
          have hdesc : largestPrimePowerPart r'.den < q := by
            simpa [r'] using hU.descends
          obtain ⟨E, s, hE⟩ := ih (q - 1) (by omega) r' (by omega)
          have hdisjoint : Disjoint U E := by
            rw [Finset.disjoint_left]
            intro n hnU hnE
            have htagU := hU.tagged n hnU
            have htagE := (hE.tag_range n hnE).2
            omega
          refine ⟨U ∪ E, s, ?_⟩
          refine
            { zero_not_mem := ?_
              card_le := ?_
              tag_range := ?_
              denominator_range := ?_
              residual_eq := ?_
              residual_smooth := hE.residual_smooth
              rec_sum_le_cost := ?_
              odd_stage := ?_ }
          · simpa only [Finset.mem_union, not_or] using
              ⟨hU.zero_not_mem, hE.zero_not_mem⟩
          · rw [Finset.card_union_of_disjoint hdisjoint]
            calc
              U.card + E.card ≤ 2 + 2 * (piStar (q - 1) - piStar lo) :=
                Nat.add_le_add hU.card_le_two hE.card_le
              _ = 2 * (piStar q - piStar lo) := by
                have hloPred : lo ≤ q - 1 := by omega
                have hpiLo : piStar lo ≤ piStar (q - 1) := piStar_mono hloPred
                rw [piStar_eq_succ_pred_of_isPrimePow hqpp]
                omega
          · intro n hn
            rcases Finset.mem_union.mp hn with hnU | hnE
            · rw [hU.tagged n hnU]
              exact ⟨hloq, le_rfl⟩
            · have hnrange := hE.tag_range n hnE
              exact ⟨hnrange.1, hnrange.2.trans (Nat.sub_le q 1)⟩
          · intro n hn
            rcases Finset.mem_union.mp hn with hnU | hnE
            · rw [hU.tagged n hnU]
              exact ⟨hU.lower n hnU, hU.upper n hnU⟩
            · exact hE.denominator_range n hnE
          · rw [hE.residual_eq, UnitFractions.rec_sum_disjoint hdisjoint]
            dsimp [r']
            ring
          · rw [UnitFractions.rec_sum_disjoint hdisjoint, Rat.cast_add,
              largeSquareCost_succ_of_isPrimePow hloq hqpp]
            nlinarith [hU.rec_sum_le_cost hqpp, hE.rec_sum_le_cost]
          · intro t hlot htq htpp htodd
            rcases lt_or_eq_of_le htq with htlt | rfl
            · obtain ⟨V, hVE, hVcard, hVtag⟩ :=
                hE.odd_stage t hlot (by omega) htpp htodd
              exact ⟨V, hVE.trans subset_union_right, hVcard, hVtag⟩
            · exact ⟨U, subset_union_left, hU.card_eq_two_of_odd htodd, hU.tagged⟩
        · have hnext : largestPrimePowerPart r.den ≤ q - 1 := by
            by_contra hnot
            have heq : largestPrimePowerPart r.den = q := by omega
            have hden2 : 2 ≤ r.den := by
              have hpartle := largestPrimePowerPart_le (n := r.den)
              omega
            exact hqpp (heq ▸ (largestPrimePowerPart_spec hden2).1)
          obtain ⟨E, s, hE⟩ := ih (q - 1) (by omega) r hnext
          refine ⟨E, s, ?_⟩
          refine
            { zero_not_mem := hE.zero_not_mem
              card_le := ?_
              tag_range := ?_
              denominator_range := hE.denominator_range
              residual_eq := hE.residual_eq
              residual_smooth := hE.residual_smooth
              rec_sum_le_cost := by
                simpa [largeSquareCost_pred_of_not_isPrimePow hqpp] using
                  hE.rec_sum_le_cost
              odd_stage := ?_ }
          · simpa [piStar_eq_pred_of_not_isPrimePow hqpp] using hE.card_le
          · intro n hn
            have hnrange := hE.tag_range n hn
            exact ⟨hnrange.1, hnrange.2.trans (Nat.sub_le q 1)⟩
          · intro t hlot htq htpp htodd
            have htlt : t < q := lt_of_le_of_ne htq (fun heq ↦ hqpp (heq ▸ htpp))
            exact hE.odd_stage t hlot (by omega) htpp htodd

/-! ## Mixed Lemma 15 / Lemma 16 recursion -/

/-- The complete preliminary correction before the final cardinality padding
step. -/
structure PreliminaryResult (B lo y : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ 2 * piStar y
  tag_le : ∀ n ∈ E, largestPrimePowerPart n ≤ y
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z
  odd_large_stage : ∀ t, lo < t → t ≤ y → IsPrimePow t → Odd t →
    ∃ U ⊆ E, U.card = 2 ∧
      (∀ n ∈ U, largestPrimePowerPart n = t) ∧
      ∀ n ∈ U, t ^ 2 ≤ 5 * n

lemma PreliminaryResult.residual_eq_zero {B lo y : ℕ} {r : ℚ}
    {E : Finset ℕ} (h : PreliminaryResult B lo y r E)
    (hsmall : |r - UnitFractions.rec_sum E| < 1) :
    r - UnitFractions.rec_sum E = 0 :=
  eq_zero_of_isInt_of_abs_lt_one h.residual_isInt hsmall

/--
Assemble the large scheduled Lemma 15 recursion and the remaining current-
factor Lemma 16 recursion.  Both inputs are ordinary theorem arguments; the
concrete Proposition 7 theorem supplies them from the two proved lemmas.
-/
theorem exists_preliminaryResult
    (B lo y : ℕ) (hlo : 1 ≤ lo) (hloy : lo ≤ y) (hyB : y ^ 2 ≤ B)
    (largeStep : ∀ q : ℕ, ∀ r : ℚ, lo < q → IsPrimePow q →
      largestPrimePowerPart r.den ≤ q →
        ∃ U : Finset ℕ, ScheduledStep r q U)
    (smallStep : ∀ r : ℚ, r.den ≠ 1 →
      largestPrimePowerPart r.den ≤ lo →
        ∃ U : Finset ℕ, EliminationStep B r U)
    (r : ℚ) (hry : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ, PreliminaryResult B lo y r E := by
  obtain ⟨A, s, hA⟩ := exists_scheduledResult lo hlo largeStep y r hry
  obtain ⟨C, hC⟩ :=
    exists_eliminationResult_below B lo smallStep s hA.residual_smooth
  have hdisjoint : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro n hnA hnC
    have hnAlo := (hA.tag_range n hnA).1
    have hnCle := (hC.tag_le n hnC).trans hA.residual_smooth
    omega
  refine ⟨A ∪ C, ?_⟩
  refine
    { zero_not_mem := ?_
      le_bound := ?_
      card_le := ?_
      tag_le := ?_
      residual_isInt := ?_
      odd_large_stage := ?_ }
  · simpa only [Finset.mem_union, not_or] using
      ⟨hA.zero_not_mem, hC.zero_not_mem⟩
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.denominator_range n hnA).2.trans
        (Nat.pow_le_pow_left (hA.tag_range n hnA).2 2) |>.trans hyB
    · exact hC.le_bound n hnC
  · rw [Finset.card_union_of_disjoint hdisjoint]
    calc
      A.card + C.card ≤
          2 * (piStar y - piStar lo) +
            2 * piStar (largestPrimePowerPart s.den) :=
        Nat.add_le_add hA.card_le hC.card_le
      _ ≤ 2 * (piStar y - piStar lo) + 2 * piStar lo := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_left 2 (piStar_mono hA.residual_smooth)) _
      _ = 2 * piStar y := by
        have hpile : piStar lo ≤ piStar y := piStar_mono hloy
        omega
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.tag_range n hnA).2
    · exact (hC.tag_le n hnC).trans hA.residual_smooth |>.trans hloy
  · obtain ⟨z, hz⟩ := hC.residual_isInt
    refine ⟨z, ?_⟩
    rw [UnitFractions.rec_sum_disjoint hdisjoint]
    linarith [hA.residual_eq]
  · intro t hlot hty htpp htodd
    obtain ⟨U, hUA, hUcard, hUtag⟩ := hA.odd_stage t hlot hty htpp htodd
    refine ⟨U, hUA.trans subset_union_left, hUcard, hUtag, ?_⟩
    intro n hn
    have hden := hA.denominator_range n (hUA hn)
    simpa [hUtag n hn] using hden.1

/-- The preliminary correction instantiated with the proved versions of
Martin's Lemmas 15 and 16.  The remaining hypotheses are only the explicit
cutoff and size inequalities used in Proposition 7. -/
theorem exists_preliminaryResult_of_lemmas
    (lo y : ℕ) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hL : initialLcm lo ≤ y ^ 2)
    (r : ℚ) (hry : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ, PreliminaryResult (y ^ 2) lo y r E := by
  apply exists_preliminaryResult (y ^ 2) lo y (by omega) hloy le_rfl
  · intro q s hloq hqpp hs
    exact exists_scheduledStep_of_lemma15 q hqpp (by omega) s hs
  · exact exists_eliminationStep_of_lemma16 (y ^ 2) lo hL
  · exact hry

/-- A preliminary correction carrying the quantitative estimate needed to
show that its terminal integer is zero. -/
structure BudgetedPreliminaryResult (lo y : ℕ) (r : ℚ)
    (E : Finset ℕ) : Prop extends PreliminaryResult (y ^ 2) lo y r E where
  rec_sum_lt : (UnitFractions.rec_sum E : ℝ) < 1 + largeSquareCost lo y

/-- Lemmas 15 and 16, combined with the exact small-prime-power telescope. -/
theorem exists_budgetedPreliminaryResult_of_lemmas
    (lo y : ℕ) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hL : initialLcm lo ≤ y ^ 2)
    (r : ℚ) (hry : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ, BudgetedPreliminaryResult lo y r E := by
  obtain ⟨A, s, hA⟩ := exists_scheduledResult lo (by omega)
    (fun q t hloq hqpp ht ↦
      exists_scheduledStep_of_lemma15 q hqpp (by omega) t ht)
    y r hry
  obtain ⟨C, hC⟩ :=
    exists_smallEliminationResult_of_lemma16 (y ^ 2) lo hL s
      hA.residual_smooth
  have hdisjoint : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro n hnA hnC
    have hnAlo := (hA.tag_range n hnA).1
    have hnCle := (hC.tag_le n hnC).trans hA.residual_smooth
    omega
  refine ⟨A ∪ C, ?_⟩
  refine
    { toPreliminaryResult :=
        { zero_not_mem := by
            simpa only [Finset.mem_union, not_or] using
              ⟨hA.zero_not_mem, hC.zero_not_mem⟩
          le_bound := ?_
          card_le := ?_
          tag_le := ?_
          residual_isInt := ?_
          odd_large_stage := ?_ }
      rec_sum_lt := ?_ }
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.denominator_range n hnA).2.trans
        (Nat.pow_le_pow_left (hA.tag_range n hnA).2 2)
    · exact hC.le_bound n hnC
  · rw [Finset.card_union_of_disjoint hdisjoint]
    calc
      A.card + C.card ≤
          2 * (piStar y - piStar lo) +
            piStar (largestPrimePowerPart s.den) :=
        Nat.add_le_add hA.card_le hC.card_le
      _ ≤ 2 * (piStar y - piStar lo) + piStar lo := by
        exact Nat.add_le_add_left (piStar_mono hA.residual_smooth) _
      _ ≤ 2 * (piStar y - piStar lo) + 2 * piStar lo := by omega
      _ = 2 * piStar y := by
        have hpile : piStar lo ≤ piStar y := piStar_mono hloy
        omega
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.tag_range n hnA).2
    · exact (hC.tag_le n hnC).trans hA.residual_smooth |>.trans hloy
  · obtain ⟨z, hz⟩ := hC.residual_isInt
    refine ⟨z, ?_⟩
    rw [UnitFractions.rec_sum_disjoint hdisjoint]
    linarith [hA.residual_eq]
  · intro t hlot hty htpp htodd
    obtain ⟨U, hUA, hUcard, hUtag⟩ :=
      hA.odd_stage t hlot hty htpp htodd
    refine ⟨U, hUA.trans subset_union_left, hUcard, hUtag, ?_⟩
    intro n hn
    have hden := hA.denominator_range n (hUA hn)
    simpa [hUtag n hn] using hden.1
  · have hCltQ : UnitFractions.rec_sum C < 1 :=
      hC.rec_sum_le_cost.trans_lt
        (smallPrimePowerCost_lt_one _)
    have hClt : (UnitFractions.rec_sum C : ℝ) < 1 := by
      exact_mod_cast hCltQ
    rw [UnitFractions.rec_sum_disjoint hdisjoint, Rat.cast_add]
    linarith [hA.rec_sum_le_cost]

/-! ## Telescoping padding -/

/-- The denominators in the telescoping replacement of `1/n`. -/
def paddingTerms (n m : ℕ) : Finset ℕ :=
  {n + m} ∪ (Finset.range m).image (fun j ↦ (n + j) * (n + j + 1))

lemma paddingProduct_strictMono (n : ℕ) (hn : 0 < n) :
    StrictMono (fun j : ℕ ↦ (n + j) * (n + j + 1)) := by
  intro a b hab
  nlinarith [Nat.add_pos_left hn a, Nat.add_pos_left hn b]

lemma paddingTerms_product_gt {n m j : ℕ} (hn : 0 < n) (_hj : j < m) :
    n < (n + j) * (n + j + 1) := by
  nlinarith [Nat.add_pos_left hn j]

lemma paddingTerms_product_le {n m j : ℕ} (hj : j < m) :
    (n + j) * (n + j + 1) ≤ (n + m) ^ 2 := by
  have h1 : n + j + 1 ≤ n + m := by omega
  have h2 : n + j ≤ n + m := by omega
  nlinarith

/-- The telescoping replacement has exactly `m + 1` distinct denominators.
The condition `m < n` prevents the linear denominator `n+m` from colliding
with a quadratic denominator. -/
lemma card_paddingTerms (n m : ℕ) (hn : 0 < n) (hm : m < n) :
    (paddingTerms n m).card = m + 1 := by
  have hinj : Set.InjOn (fun j : ℕ ↦ (n + j) * (n + j + 1)) (Finset.range m) :=
    (paddingProduct_strictMono n hn).injective.injOn
  have hcardImage : ((Finset.range m).image
      (fun j ↦ (n + j) * (n + j + 1))).card = m := by
    rw [Finset.card_image_iff.mpr hinj]
    simp
  have hnotmem : n + m ∉ (Finset.range m).image
      (fun j ↦ (n + j) * (n + j + 1)) := by
    intro hmem
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
    have hjm : j < m := Finset.mem_range.mp hj
    have hquad : 2 * n ≤ (n + j) * (n + j + 1) := by
      nlinarith [Nat.add_pos_left hn j]
    have hlin : n + m < 2 * n := by omega
    omega
  rw [paddingTerms, Finset.card_union_of_disjoint]
  · simp [hcardImage, Nat.add_comm]
  · simpa [Finset.disjoint_left] using hnotmem

lemma zero_not_mem_paddingTerms {n m : ℕ} (hn : 0 < n) :
    0 ∉ paddingTerms n m := by
  rw [paddingTerms, Finset.mem_union, not_or]
  refine ⟨?_, ?_⟩
  · intro h
    simp only [Finset.mem_singleton] at h
    omega
  simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
  intro j hj
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.add_pos_left hn j) (by omega))

lemma mem_paddingTerms_le_square {n m a : ℕ} (ha : a ∈ paddingTerms n m) :
    a ≤ (n + m) ^ 2 := by
  rcases Finset.mem_union.mp ha with ha | ha
  · simp only [Finset.mem_singleton] at ha
    subst a
    nlinarith
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact paddingTerms_product_le (Finset.mem_range.mp hj)

lemma paddingTerms_above {n m a : ℕ} (hn : 0 < n) (hm : 0 < m)
    (ha : a ∈ paddingTerms n m) : n < a := by
  rcases Finset.mem_union.mp ha with ha | ha
  · have heq : a = n + m := Finset.mem_singleton.mp ha
    omega
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact paddingTerms_product_gt hn (Finset.mem_range.mp hj)

/-- The reciprocal sum of all padding terms is exactly the original unit
fraction. -/
lemma rec_sum_paddingTerms (n m : ℕ) (hn : 0 < n) (hm : m < n) :
    UnitFractions.rec_sum (paddingTerms n m) = (1 : ℚ) / n := by
  have hdisj : Disjoint ({n + m} : Finset ℕ)
      ((Finset.range m).image (fun j ↦ (n + j) * (n + j + 1))) := by
    rw [Finset.disjoint_left]
    intro a ha haImage
    simp only [Finset.mem_singleton] at ha
    subst a
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp haImage
    have hjm : j < m := Finset.mem_range.mp hj
    have hquad : 2 * n ≤ (n + j) * (n + j + 1) := by
      nlinarith [Nat.add_pos_left hn j]
    have hlin : n + m < 2 * n := by omega
    omega
  rw [paddingTerms, UnitFractions.rec_sum_disjoint hdisj]
  simp only [UnitFractions.rec_sum, Finset.sum_singleton]
  have himage :
      ∑ a ∈ (Finset.range m).image (fun j ↦ (n + j) * (n + j + 1)),
          (1 : ℚ) / a =
        ∑ j ∈ Finset.range m, (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact (paddingProduct_strictMono n hn).injective hab
  rw [himage]
  exact (unitFraction_telescoping n m hn).symm

/-- Replace the largest member of `A` by the telescoping padding set. -/
def padAt (A : Finset ℕ) (n m : ℕ) : Finset ℕ :=
  A.erase n ∪ paddingTerms n m

/--
Source-faithful exact-cardinality padding interface.

If `n` is the largest denominator of a nonempty positive finite set and the
required deficit `m` is smaller than `n`, then `padAt A n m` has exactly
`A.card + m` members, has the same reciprocal sum, remains positive, and all
its denominators are at most `(n+m)^2`.
-/
theorem padAt_spec {A : Finset ℕ} {n m : ℕ}
    (hnA : n ∈ A) (hnmax : ∀ a ∈ A, a ≤ n)
    (hzero : 0 ∉ A) (hm : m < n) :
    (padAt A n m).card = A.card + m ∧
      UnitFractions.rec_sum (padAt A n m) = UnitFractions.rec_sum A ∧
      0 ∉ padAt A n m ∧
      ∀ a ∈ padAt A n m, a ≤ (n + m) ^ 2 := by
  have hn : 0 < n := by
    have : n ≠ 0 := by
      intro hn0
      exact hzero (hn0 ▸ hnA)
    omega
  have hdisj : Disjoint (A.erase n) (paddingTerms n m) := by
    rw [Finset.disjoint_left]
    intro a haA haP
    have han : a ≤ n := hnmax a (Finset.mem_of_mem_erase haA)
    rcases eq_or_lt_of_le (Nat.zero_le m) with hm0 | hmpos
    · subst m
      simp [paddingTerms] at haP
      subst a
      simp at haA
    · exact (not_lt_of_ge han) (paddingTerms_above hn hmpos haP)
  have hcardErase : (A.erase n).card = A.card - 1 := by
    rw [Finset.card_erase_of_mem hnA]
  have hsumErase : UnitFractions.rec_sum (A.erase n) + (1 : ℚ) / n =
      UnitFractions.rec_sum A := by
    simpa [UnitFractions.rec_sum] using
      (Finset.sum_erase_add (s := A) (f := fun a : ℕ ↦ (1 : ℚ) / a) hnA)
  have hcardPos : 0 < A.card := Finset.card_pos.mpr ⟨n, hnA⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [padAt, Finset.card_union_of_disjoint hdisj, hcardErase,
      card_paddingTerms n m hn hm]
    omega
  · rw [padAt, UnitFractions.rec_sum_disjoint hdisj,
      rec_sum_paddingTerms n m hn hm]
    exact hsumErase
  · rw [padAt, Finset.mem_union, not_or]
    exact ⟨fun h ↦ hzero (Finset.mem_of_mem_erase h), zero_not_mem_paddingTerms hn⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with haA | haP
    · have han : a ≤ n := hnmax a (Finset.mem_of_mem_erase haA)
      calc
        a ≤ n := han
        _ ≤ (n + m) ^ 2 := by nlinarith
    · exact mem_paddingTerms_le_square haP

/-- Padding directly to a prescribed target cardinality. -/
theorem exists_padded_to_card {A : Finset ℕ} {n K : ℕ}
    (hnA : n ∈ A) (hnmax : ∀ a ∈ A, a ≤ n)
    (hzero : 0 ∉ A) (hcard : A.card ≤ K)
    (hdeficit : K - A.card < n) :
    ∃ E : Finset ℕ,
      E.card = K ∧
      UnitFractions.rec_sum E = UnitFractions.rec_sum A ∧
      0 ∉ E ∧
      ∀ a ∈ E, a ≤ (n + (K - A.card)) ^ 2 := by
  let m := K - A.card
  refine ⟨padAt A n m, ?_⟩
  obtain ⟨hcardPad, hsumPad, hzeroPad, hboundPad⟩ :=
    padAt_spec hnA hnmax hzero hdeficit
  refine ⟨?_, hsumPad, hzeroPad, hboundPad⟩
  dsimp [m] at hcardPad ⊢
  omega

/-! ## Final padding bound -/

/--
Turn a preliminary exact correction into the exact cardinality
`2 * piStar y`.  Bertrand's postulate supplies an odd prime in `(y/2,y]`;
the scheduled Lemma 15 stage at that prime provides a denominator large enough
to absorb the entire cardinality deficit.  The square estimate from
`padAt_spec` is then at most `2*y^4`.
-/
theorem exists_exactCard_of_preliminary
    {lo y : ℕ} {r : ℚ} {A : Finset ℕ}
    (hy : 40 ≤ y) (hlo : lo < y / 2)
    (hA : PreliminaryResult (y ^ 2) lo y r A)
    (hsmall : |r - UnitFractions.rec_sum A| < 1) :
    ∃ E : Finset ℕ,
      E.card = 2 * piStar y ∧
      UnitFractions.rec_sum E = r ∧
      0 ∉ E ∧
      ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  have hyhalf : y / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hyhp, hpyle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (y / 2) hyhalf
  have hpy : p ≤ y := hpyle.trans (by omega)
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpp : IsPrimePow p := ⟨p, 1, hp.prime, by omega, by simp⟩
  obtain ⟨U, hUA, hUcard, hUtag, hUlower⟩ :=
    hA.odd_large_stage p (hlo.trans hyhp) hpy hpp hpodd
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n, hnU⟩ := hUne
  have hnA : n ∈ A := hUA hnU
  have hAne : A.Nonempty := ⟨n, hnA⟩
  let N : ℕ := A.max' hAne
  have hnN : n ≤ N := by
    exact Finset.le_max' A n hnA
  have hNmem : N ∈ A := Finset.max'_mem A hAne
  have hNmax : ∀ a ∈ A, a ≤ N := by
    intro a ha
    exact Finset.le_max' A a ha
  have hNupper : N ≤ y ^ 2 := hA.le_bound N hNmem
  let K : ℕ := 2 * piStar y
  let d : ℕ := K - A.card
  have hcardAK : A.card ≤ K := by
    simpa [K] using hA.card_le
  have hKle : K ≤ 2 * y := by
    dsimp [K]
    exact Nat.mul_le_mul_left 2 (piStar_le y)
  have hdle : d ≤ 2 * y := by
    exact (Nat.sub_le K A.card).trans hKle
  have hyhalfBound : y ≤ 2 * (y / 2) + 1 := by omega
  have hpSq : 10 * y < p ^ 2 := by
    nlinarith
  have hpn : p ^ 2 ≤ 5 * n := hUlower n hnU
  have hnlarge : 2 * y < n := by nlinarith
  have hdN : d < N := hdle.trans_lt (hnlarge.trans_le hnN)
  obtain ⟨E, hEcard, hEsum, hEzero, hEbound⟩ :=
    exists_padded_to_card hNmem hNmax hA.zero_not_mem hcardAK hdN
  have hAsum : UnitFractions.rec_sum A = r := by
    have hz := hA.residual_eq_zero hsmall
    linarith
  have hsumBound : N + d ≤ y ^ 2 + 2 * y := Nat.add_le_add hNupper hdle
  have hfour : 4 * (N + d) ≤ 5 * y ^ 2 := by
    nlinarith [show 8 * y ≤ y ^ 2 by nlinarith]
  have hsquare : (N + d) ^ 2 ≤ 2 * y ^ 4 := by
    nlinarith [sq_nonneg (4 * (N + d)), sq_nonneg (5 * y ^ 2)]
  refine ⟨E, ?_, ?_, hEzero, ?_⟩
  · simpa [K] using hEcard
  · exact hEsum.trans hAsum
  · intro a ha
    exact (hEbound a ha).trans (by simpa [N, d] using hsquare)

/-- Converting a Chebyshev bound at a cutoff into the concrete `y^2` LCM
bound required by the small-prime-power construction. -/
lemma initialLcm_le_sq_of_chebyshev {lo y : ℕ} (hy : 1 ≤ y)
    (hlo : (lo : ℝ) ≤ Real.log (y : ℝ))
    (hpsi : chebyshev_second (lo : ℝ) ≤ 2 * (lo : ℝ)) :
    initialLcm lo ≤ y ^ 2 := by
  have hLpos : (0 : ℝ) < initialLcm lo := by
    exact_mod_cast
      (Nat.pos_of_ne_zero (by simp [initialLcm] : initialLcm lo ≠ 0))
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy)
  have hlogL : Real.log (initialLcm lo : ℝ) =
      chebyshev_second (lo : ℝ) := by
    change Real.log (Nat.lcmUpto lo : ℝ) = Chebyshev.psi (lo : ℝ)
    exact (Chebyshev.psi_eq_log_lcmUpto lo).symm
  have hlogle : Real.log (initialLcm lo : ℝ) ≤
      2 * Real.log (y : ℝ) := by
    rw [hlogL]
    linarith
  have hexp := Real.exp_le_exp.mpr hlogle
  rw [Real.exp_log hLpos] at hexp
  have hrhs : Real.exp (2 * Real.log (y : ℝ)) = (y : ℝ) ^ 2 := by
    rw [show 2 * Real.log (y : ℝ) =
      Real.log (y : ℝ) + Real.log (y : ℝ) by ring,
      Real.exp_add, Real.exp_log hypos]
    ring
  rw [hrhs] at hexp
  exact_mod_cast hexp

/-- A convenient elementary cutoff separation used by the eventual wrapper. -/
lemma log_lt_quarter_natCast (y : ℕ) (hy : 40 ≤ y) :
    Real.log (y : ℝ) < (y : ℝ) / 4 := by
  have hyR : (0 : ℝ) < y := by positivity
  have hdiv : 0 < (y : ℝ) / 8 := div_pos hyR (by norm_num)
  have hbase := Real.log_le_sub_one_of_pos hdiv
  have hlog2 : Real.log (2 : ℝ) < 1 := by
    nlinarith [Real.log_two_lt_d9]
  have hlog8 : Real.log (8 : ℝ) < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hdecomp : Real.log (y : ℝ) =
      Real.log 8 + Real.log ((y : ℝ) / 8) := by
    rw [Real.log_div (ne_of_gt hyR) (by norm_num : (8 : ℝ) ≠ 0)]
    linarith
  rw [hdecomp]
  have hyR40 : (40 : ℝ) ≤ y := by exact_mod_cast hy
  nlinarith

lemma naturalLogCutoff_lt_half (y : ℕ) (hy : 40 ≤ y) :
    naturalLogCutoff y < y / 2 := by
  have hy1 : 1 ≤ y := by omega
  have hlognonneg : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy1)
  have hfloor : ((naturalLogCutoff y : ℕ) : ℝ) ≤
      Real.log (y : ℝ) := Nat.floor_le hlognonneg
  have hlog := log_lt_quarter_natCast y hy
  have hnat : y < 4 * (y / 2) := by omega
  have hreal : (y : ℝ) < 4 * ((y / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hquarter : (y : ℝ) / 4 < ((y / 2 : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast hfloor.trans_lt (hlog.trans hquarter)

/-- Finite, quantitative form of Martin's Proposition 7.  The positive
constant `c` is arbitrary; the source's `1/log y` is the case `c = 1`, while
the upper-bound assembly uses `c = 1/6` to absorb the fifth-root floor. -/
theorem proposition7_of_cutoff
    {c : ℝ} (_hc : 0 < c) {lo y : ℕ} {r : ℚ}
    (hy : 40 ≤ y) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hlohalf : lo < y / 2) (hL : initialLcm lo ≤ y ^ 2)
    (hry : largestPrimePowerPart r.den ≤ y)
    (hrLower : c / Real.log (y : ℝ) < (r : ℝ))
    (hrUpper : (r : ℝ) < 1)
    (htail : largeSquareCost lo y < c / Real.log (y : ℝ)) :
    ∃ E : Finset ℕ,
      E.card = 2 * piStar y ∧
      UnitFractions.rec_sum E = r ∧
      0 ∉ E ∧
      ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  obtain ⟨A, hA⟩ :=
    exists_budgetedPreliminaryResult_of_lemmas lo y hlo hloy hL r hry
  have hsumlt : (UnitFractions.rec_sum A : ℝ) < 1 + (r : ℝ) := by
    linarith [hA.rec_sum_lt]
  have hsum_nonnegQ : 0 ≤ UnitFractions.rec_sum A :=
    rec_sum_nonneg A
  have hsum_nonneg : (0 : ℝ) ≤ UnitFractions.rec_sum A := by
    exact_mod_cast hsum_nonnegQ
  have hresLower : (-1 : ℝ) < (r : ℝ) - UnitFractions.rec_sum A := by
    linarith
  have hresUpper : (r : ℝ) - UnitFractions.rec_sum A < 1 := by
    linarith
  have hsmallR : |(r : ℝ) - UnitFractions.rec_sum A| < 1 :=
    (abs_lt).2 ⟨hresLower, hresUpper⟩
  have hsmall : |r - UnitFractions.rec_sum A| < (1 : ℚ) := by
    exact_mod_cast hsmallR
  exact exists_exactCard_of_preliminary hy hlohalf hA.toPreliminaryResult hsmall

end




/-!
# The terminal mass estimate in Martin's Proposition 7

The correction has two parts.  The large-prime-power stages have total mass
`o(1 / log y)` by the square-tail estimate in `RoughCounts`.  At a small
prime-power stage `q = p^e`, the initial least common multiple acquires exactly
the factor `p`.  Thus the costs `(p-1)/lcm(1,...,q)` telescope and their total
is strictly less than one.

This file also packages the numerical facts for Martin's choice
`lo = floor(log y)`.  The exported theorem has no hypothesis supplying a mass
bound: that bound is obtained here from the two proved estimates above.
-/

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

open SmoothPrimePowerFactorization

/-! ## The exact small-prime-power telescope -/

/-- At a prime power, division by the newly acquired prime factor recovers the
preceding initial LCM.  This is the pointwise identity behind the ordered
prime-power telescope. -/
theorem initialLcm_div_minFac_eq_pred {q : ℕ} (hq : IsPrimePow q) :
    initialLcm q / q.minFac = initialLcm (q - 1) := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp hq
  rw [initialLcm_prime_pow hp (ne_of_gt he), hp.pow_minFac (ne_of_gt he)]
  exact Nat.mul_div_right _ hp.pos

/-- The sum of the small-stage costs is the exact endpoint difference. -/
theorem small_prime_power_mass_telescope (lo : ℕ) :
    (∑ q ∈ primePowersUpTo lo,
        ((q.minFac - 1 : ℕ) : ℚ) / initialLcm q) =
      1 - (1 : ℚ) / initialLcm lo := by
  change smallPrimePowerCost lo =
    1 - (1 : ℚ) / initialLcm lo
  exact smallPrimePowerCost_eq lo

/-- In particular, all small-prime-power correction terms cost less than one. -/
theorem small_prime_power_mass_lt_one (lo : ℕ) :
    (∑ q ∈ primePowersUpTo lo,
        ((q.minFac - 1 : ℕ) : ℚ) / initialLcm q) < 1 := by
  change smallPrimePowerCost lo < 1
  exact smallPrimePowerCost_lt_one lo

/-! ## Numerical facts at `lo = floor(log y)` -/

private lemma log_four_lt_two : Real.log 4 < 2 := by
  rw [Real.log_four_eq]
  have hlog2 : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
      Real.exp_one_gt_two
  linarith

/-- The explicit Chebyshev estimate gives `psi(n) ≤ 2n` eventually. -/
theorem eventually_psi_nat_le_two_mul :
    ∀ᶠ n : ℕ in atTop, Chebyshev.psi (n : ℝ) ≤ 2 * n := by
  let ε : ℝ := (2 - Real.log 4) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [log_four_lt_two]
  have hsmall :=
    (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).bound hε
  filter_upwards
    [eventually_ge_atTop 1,
      hsmall.filter_mono tendsto_natCast_atTop_atTop] with n hn hlog
  replace hlog : ‖Real.log (n : ℝ)‖ ≤ ε * ‖(n : ℝ) ^ ((1 : ℝ) / 2)‖ := by simpa using hlog
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n := by
    rw [sq_sqrt]
    positivity
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hsqrtnonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hrpow : (n : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt n := by
    exact (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hnormLog : ‖Real.log (n : ℝ)‖ = Real.log n :=
    Real.norm_of_nonneg hlognonneg
  have hnormSqrt : ‖(n : ℝ) ^ ((1 : ℝ) / 2)‖ = Real.sqrt n := by
    rw [hrpow, Real.norm_of_nonneg hsqrtnonneg]
  rw [hnormLog, hnormSqrt] at hlog
  have herror :
      2 * Real.sqrt (n : ℝ) * Real.log n ≤
        (2 - Real.log 4) * n := by
    calc
      2 * Real.sqrt (n : ℝ) * Real.log n ≤
          2 * Real.sqrt (n : ℝ) *
            (((2 - Real.log 4) / 2) * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left (by simpa [ε] using hlog)
          (mul_nonneg (by norm_num) hsqrtnonneg)
      _ = (2 - Real.log 4) * (Real.sqrt n) ^ 2 := by ring
      _ = (2 - Real.log 4) * n := by rw [hsqrt]
  calc
    Chebyshev.psi (n : ℝ) ≤
        Real.log 4 * n + 2 * Real.sqrt n * Real.log n :=
      Chebyshev.psi_le hnR
    _ ≤ 2 * n := by linarith

/-- Consequently `lcm(1,...,n) ≤ exp(2n)` eventually. -/
theorem eventually_initialLcm_le_exp_two_mul :
    ∀ᶠ n : ℕ in atTop,
      (initialLcm n : ℝ) ≤ Real.exp (2 * n) := by
  filter_upwards [eventually_psi_nat_le_two_mul] with n hn
  have hpos : (0 : ℝ) < initialLcm n := by
    exact_mod_cast (Nat.lcmUpto_pos n)
  have hlog : Real.log (initialLcm n : ℝ) ≤ 2 * n := by
    change Real.log (Nat.lcmUpto n : ℝ) ≤ 2 * (n : ℝ)
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    exact hn
  have := Real.exp_monotone hlog
  simpa [Real.exp_log hpos] using this

/-- At the logarithmic cutoff, the LCM needed by Lemma 16 is eventually at
most `y²`. -/
theorem eventually_initialLcm_naturalLogCutoff_le_sq :
    ∀ᶠ y : ℕ in atTop,
      initialLcm (naturalLogCutoff y) ≤ y ^ 2 := by
  have hLcm := eventually_psi_nat_le_two_mul.filter_mono
    naturalLogCutoff_tendsto_atTop
  filter_upwards
    [hLcm,
      eventually_ge_atTop 2,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with y hLcm hy hlog
  try simp only [Set.mem_ofPred_eq] at hlog
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hfloor : (naturalLogCutoff y : ℝ) ≤ Real.log (y : ℝ) := by
    exact Nat.floor_le (le_of_lt hlog)
  exact initialLcm_le_sq_of_chebyshev (by omega) hfloor hLcm

lemma eventually_naturalLogCutoff_le_self :
    ∀ᶠ y : ℕ in atTop, naturalLogCutoff y ≤ y := by
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with y hy hlog
  try simp only [Set.mem_ofPred_eq] at hlog
  have hfloor : (naturalLogCutoff y : ℝ) ≤ Real.log (y : ℝ) :=
    Nat.floor_le (le_of_lt hlog)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogLe : Real.log (y : ℝ) ≤ y := by
    linarith [Real.log_le_sub_one_of_pos hypos]
  exact_mod_cast hfloor.trans hlogLe

lemma eventually_naturalLogCutoff_lt_half :
    ∀ᶠ y : ℕ in atTop, naturalLogCutoff y < y / 2 := by
  filter_upwards [eventually_ge_atTop 40] with y hy
  have hlog := log_lt_quarter_natCast y hy
  have hlognonneg : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hfloor : (naturalLogCutoff y : ℝ) ≤ Real.log (y : ℝ) :=
    Nat.floor_le hlognonneg
  have hfourR : (4 * naturalLogCutoff y : ℕ) < (y : ℝ) := by
    push_cast
    nlinarith
  have hfour : 4 * naturalLogCutoff y < y := by exact_mod_cast hfourR
  omega

/-! ## Eventual mass and exact correction -/

/-- The complete preliminary correction has reciprocal mass below
`1 + c/log y`, with no assumed mass estimate. -/
theorem eventually_exists_budgeted_preliminary
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop, ∀ r : ℚ,
      largestPrimePowerPart r.den ≤ y →
      ∃ E : Finset ℕ,
        BudgetedPreliminaryResult
          (naturalLogCutoff y) y r E ∧
        (UnitFractions.rec_sum E : ℝ) <
          1 + c / Real.log (y : ℝ) := by
  filter_upwards
    [naturalLogCutoff_tendsto_atTop.eventually (eventually_ge_atTop 3),
      eventually_naturalLogCutoff_le_self,
      eventually_initialLcm_naturalLogCutoff_le_sq,
      eventually_sum_ten_div_primePower_sq_lt_div_log hc] with y hlo hloy hL htail
  try simp only [Set.mem_ofPred_eq] at hlo
  intro r hry
  obtain ⟨E, hE⟩ :=
    exists_budgetedPreliminaryResult_of_lemmas
      (naturalLogCutoff y) y hlo hloy hL r hry
  refine ⟨E, hE, ?_⟩
  calc
    (UnitFractions.rec_sum E : ℝ) <
        1 + largeSquareCost (naturalLogCutoff y) y :=
      hE.rec_sum_lt
    _ ≤ 1 + c / Real.log (y : ℝ) := by
      simp only [largeSquareCost]
      linarith

/-- If the input residual is larger than the large-stage error and is below
one, the integer left by the preliminary correction lies in `(-1,1)`. -/
theorem terminal_residual_abs_lt_one
    {c : ℝ} {y : ℕ} {r : ℚ} {E : Finset ℕ}
    (hrLower : c / Real.log (y : ℝ) < (r : ℝ))
    (hrUpper : (r : ℝ) < 1)
    (hmass : (UnitFractions.rec_sum E : ℝ) <
      1 + c / Real.log (y : ℝ)) :
    |r - UnitFractions.rec_sum E| < (1 : ℚ) := by
  have hsumQ : 0 ≤ UnitFractions.rec_sum E := rec_sum_nonneg E
  have hsum : (0 : ℝ) ≤ UnitFractions.rec_sum E := by exact_mod_cast hsumQ
  have hlower : (-1 : ℝ) <
      (r : ℝ) - UnitFractions.rec_sum E := by linarith
  have hupper : (r : ℝ) - UnitFractions.rec_sum E < 1 := by linarith
  have habs : |(r : ℝ) - UnitFractions.rec_sum E| < 1 :=
    (abs_lt).2 ⟨hlower, hupper⟩
  exact_mod_cast habs

/-- Eventual, source-faithful Proposition 7.  It instantiates the cutoff,
proves the LCM and mass bounds internally, and returns exactly `2*piStar y`
distinct unit fractions. -/
theorem eventually_proposition7
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop, ∀ r : ℚ,
      largestPrimePowerPart r.den ≤ y →
      c / Real.log (y : ℝ) < (r : ℝ) →
      (r : ℝ) < 1 →
      ∃ E : Finset ℕ,
        E.card = 2 * piStar y ∧
        UnitFractions.rec_sum E = r ∧
        0 ∉ E ∧
        ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  filter_upwards
    [eventually_ge_atTop 40,
      naturalLogCutoff_tendsto_atTop.eventually (eventually_ge_atTop 3),
      eventually_naturalLogCutoff_le_self,
      eventually_naturalLogCutoff_lt_half,
      eventually_initialLcm_naturalLogCutoff_le_sq,
      eventually_sum_ten_div_primePower_sq_lt_div_log hc] with y hy hlo hloy hlohalf hL htail
  try simp only [Set.mem_ofPred_eq] at hlo
  intro r hry hrLower hrUpper
  exact proposition7_of_cutoff hc hy hlo hloy hlohalf hL hry
    hrLower hrUpper htail

end



end PrimePowerLCMTelescope

end
