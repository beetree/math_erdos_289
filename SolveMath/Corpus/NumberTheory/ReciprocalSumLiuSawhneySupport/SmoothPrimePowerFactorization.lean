module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Combinatorics.Additive.SubsetSum
public import Mathlib.Data.ZMod.ValMinAbs
public import SolveMath.Corpus.NumberTheory.UnitFractionDensities
public import SolveMath.Corpus.NumberTheory.UnitFractionSubsumResults.Basic
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.Basic
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.ExponentialSums
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.MajorArcs
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.CircleMethod
public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.Basic

@[expose] public section


namespace SmoothPrimePowerFactorization



/-!
# Smooth prime-power factorization for denominator clearing

Martin's denominator-elimination argument measures an integer by its largest
*exact* prime-power part: if `p ^ e ∣ n` but `p ^ (e + 1) ∤ n`, the relevant
part is `p ^ e`.  Equivalently, it is a prime power `q ∣ n` for which
`q` is coprime to `n / q`.

This file packages that notion, the counting function `π⋆`, elementary linear
bounds for `π⋆`, reduced-rational denominator descent, and the exponential LCM
bound already available in the unit-fractions development.
-/

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The exact prime-power parts of `n`.  For example, the parts of
`12 = 2^2 * 3` are `4` and `3`, rather than `2`, `4`, and `3`. -/
def primePowerParts (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun q ↦ IsPrimePow q ∧ Nat.Coprime q (n / q)

/-- Martin's `P*(n)`, with the harmless convention `P*(0) = P*(1) = 0`. -/
def largestPrimePowerPart (n : ℕ) : ℕ :=
  (primePowerParts n).sup id

/-- A natural-number formulation of smoothness in terms of exact prime-power
parts. -/
def PrimePowerSmooth (y n : ℕ) : Prop :=
  ∀ q ∈ primePowerParts n, q ≤ y

/-- The finite set of prime powers in `[2,y]`. -/
def primePowersUpTo (y : ℕ) : Finset ℕ :=
  (Icc 2 y).filter IsPrimePow

/-- Martin's prime-power counting function `π*(y)`. -/
def piStar (y : ℕ) : ℕ :=
  (primePowersUpTo y).card

/-- `lcm(1,2,...,y)`. -/
def initialLcm (y : ℕ) : ℕ :=
  (Icc 1 y).lcm id

lemma mem_primePowerParts {n q : ℕ} (hn : n ≠ 0) :
    q ∈ primePowerParts n ↔
      IsPrimePow q ∧ q ∣ n ∧ Nat.Coprime q (n / q) := by
  simp [primePowerParts, Nat.mem_divisors, hn, and_left_comm]

lemma primePowerParts_eq_ppowers_in_singleton (n : ℕ) :
    primePowerParts n = UnitFractions.ppowers_in_set {n} := by
  ext q
  by_cases hn : n = 0
  · subst n
    have hzero : UnitFractions.ppowers_in_set ({0} : Finset ℕ) = ∅ := by
      rw [show ({0} : Finset ℕ) = insert 0 ∅ by simp]
      rw [UnitFractions.ppowers_in_set_insert_zero]
      simp [UnitFractions.ppowers_in_set]
    rw [hzero]
    simp [primePowerParts]
  · constructor
    · intro hq
      rcases (mem_primePowerParts hn).mp hq with ⟨hqpp, hqdiv, hqcop⟩
      rw [UnitFractions.mem_ppowers_in_set]
      refine ⟨hqpp, ⟨n, ?_⟩⟩
      exact (UnitFractions.mem_local_part n).mpr ⟨by simp, hqdiv, hqcop⟩
    · intro hq
      rcases UnitFractions.mem_ppowers_in_set.mp hq with ⟨hqpp, ⟨m, hm⟩⟩
      rcases (UnitFractions.mem_local_part m).mp hm with ⟨hm, hqdiv, hqcop⟩
      simp only [Finset.mem_singleton] at hm
      subst m
      exact (mem_primePowerParts hn).mpr ⟨hqpp, hqdiv, hqcop⟩

lemma primePowerParts_nonempty {n : ℕ} (hn : 2 ≤ n) :
    (primePowerParts n).Nonempty := by
  rw [primePowerParts_eq_ppowers_in_singleton]
  exact UnitFractions.ppowers_in_set_nonempty ⟨n, by simp, hn⟩

lemma primePowerParts_empty_iff {n : ℕ} :
    primePowerParts n = ∅ ↔ n < 2 := by
  constructor
  · intro h
    by_contra hn
    exact (primePowerParts_nonempty (Nat.le_of_not_gt hn)).ne_empty h
  · intro hn
    interval_cases n <;> simp [primePowerParts, not_isPrimePow_one]

lemma le_largestPrimePowerPart {n q : ℕ} (hq : q ∈ primePowerParts n) :
    q ≤ largestPrimePowerPart n := by
  exact Finset.le_sup (f := id) hq

lemma largestPrimePowerPart_le_iff {n y : ℕ} :
    largestPrimePowerPart n ≤ y ↔ PrimePowerSmooth y n := by
  simp [largestPrimePowerPart, PrimePowerSmooth, Finset.sup_le_iff]

lemma largestPrimePowerPart_mem {n : ℕ} (hn : 2 ≤ n) :
    largestPrimePowerPart n ∈ primePowerParts n := by
  have hs : (primePowerParts n).sup id ∈ id '' (primePowerParts n : Set ℕ) :=
    Finset.sup_mem_of_nonempty (f := id) (primePowerParts_nonempty hn)
  rcases hs with ⟨q, hq, hqeq⟩
  simpa [largestPrimePowerPart] using hqeq ▸ hq

lemma largestPrimePowerPart_spec {n : ℕ} (hn : 2 ≤ n) :
    IsPrimePow (largestPrimePowerPart n) ∧
      largestPrimePowerPart n ∣ n ∧
      Nat.Coprime (largestPrimePowerPart n) (n / largestPrimePowerPart n) := by
  exact (mem_primePowerParts (by omega)).mp (largestPrimePowerPart_mem hn)

lemma one_lt_largestPrimePowerPart {n : ℕ} (hn : 2 ≤ n) :
    1 < largestPrimePowerPart n :=
  (largestPrimePowerPart_spec hn).1.one_lt

lemma largestPrimePowerPart_le {n : ℕ} : largestPrimePowerPart n ≤ n := by
  rw [largestPrimePowerPart_le_iff]
  intro q hq
  by_cases hn : n = 0
  · subst n
    simp [primePowerParts] at hq
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((mem_primePowerParts hn).mp hq).2.1

lemma primePowerSmooth_mono {x y n : ℕ} (hxy : x ≤ y)
    (h : PrimePowerSmooth x n) : PrimePowerSmooth y n := by
  intro q hq
  exact (h q hq).trans hxy

lemma primePowerSmooth_self (n : ℕ) : PrimePowerSmooth n n := by
  rw [← largestPrimePowerPart_le_iff]
  exact largestPrimePowerPart_le

@[simp] lemma mem_primePowersUpTo {y q : ℕ} :
    q ∈ primePowersUpTo y ↔ IsPrimePow q ∧ q ≤ y := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hqpp⟩
    exact ⟨hqpp, (Finset.mem_Icc.mp hqIcc).2⟩
  · rintro ⟨hqpp, hqy⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqpp.one_lt, hqy⟩, hqpp⟩

lemma primePowersUpTo_mono : Monotone primePowersUpTo := by
  intro x y hxy q hq
  rw [mem_primePowersUpTo] at hq ⊢
  exact ⟨hq.1, hq.2.trans hxy⟩

lemma piStar_mono : Monotone piStar := by
  intro x y hxy
  exact Finset.card_le_card (primePowersUpTo_mono hxy)

lemma piStar_le (y : ℕ) : piStar y ≤ y := by
  calc
    piStar y ≤ (Icc 2 y).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ y := by simp

/-- The elementary estimate `π*(y) = O(y)`.  Martin only needs that the exact
correction consumes a sublinear number of terms for a much smaller argument;
this coarse bound is a convenient universally valid API. -/
lemma piStar_isBigO :
    (fun y : ℕ ↦ (piStar y : ℝ)) =O[atTop] (fun y : ℕ ↦ (y : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun y ↦ ?_)
  simpa only [Real.norm_natCast, norm_one, one_mul] using
    (show (piStar y : ℝ) ≤ y by exact_mod_cast piStar_le y)

lemma den_pos (r : ℚ) : 0 < r.den := r.den_pos

/-- A proper divisor of a reduced denominator is strictly smaller. -/
lemma den_lt_of_dvd_of_ne {r s : ℚ} (hdiv : s.den ∣ r.den)
    (hne : s.den ≠ r.den) : s.den < r.den :=
  Nat.lt_of_le_of_ne (Nat.le_of_dvd r.den_pos hdiv) hne

/-- Once a prime-power part `q` of a denominator has been eliminated, any new
reduced denominator dividing `r.den / q` is strictly smaller. -/
lemma den_lt_of_primePower_elimination {r s : ℚ} {q : ℕ}
    (hq : q ∈ primePowerParts r.den) (hdiv : s.den ∣ r.den / q) :
    s.den < r.den := by
  have hr0 : r.den ≠ 0 := r.den_ne_zero
  have hqspec := (mem_primePowerParts hr0).mp hq
  have hquot : r.den / q < r.den := Nat.div_lt_self r.den_pos hqspec.1.one_lt
  exact (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd r.den_pos hqspec.2.1)
    hqspec.1.pos) hdiv).trans_lt hquot

lemma den_eq_one_iff_primePowerParts_empty (r : ℚ) :
    r.den = 1 ↔ primePowerParts r.den = ∅ := by
  rw [primePowerParts_empty_iff]
  have := r.den_pos
  omega

lemma exists_primePowerPart_of_den_ne_one {r : ℚ} (hr : r.den ≠ 1) :
    ∃ q ∈ primePowerParts r.den, IsPrimePow q ∧ q ∣ r.den := by
  have hden : 2 ≤ r.den := by
    have := r.den_pos
    omega
  obtain ⟨q, hq⟩ := primePowerParts_nonempty hden
  exact ⟨q, hq, (mem_primePowerParts r.den_ne_zero).mp hq |>.1,
    (mem_primePowerParts r.den_ne_zero).mp hq |>.2.1⟩

/-- If no exact prime-power part remains, the reduced rational is an integer. -/
lemma isInt_of_primePowerParts_empty {r : ℚ}
    (h : primePowerParts r.den = ∅) : ∃ z : ℤ, r = z := by
  have hden : r.den = 1 := (den_eq_one_iff_primePowerParts_empty r).2 h
  exact ⟨r.num, (Rat.den_eq_one_iff r).mp hden |>.symm⟩

/-- The reduced denominator of a finite unit-fraction sum divides the LCM of
its displayed denominators. -/
lemma recSum_den_dvd_lcm (A : Finset ℕ) :
    (UnitFractions.rec_sum A).den ∣ A.lcm id := by
  refine (Rat.den_sum_dvd_lcm_den A (fun n ↦ (1 : ℚ) / n)).trans ?_
  apply Finset.lcm_dvd
  intro n hn
  have hden : ((1 : ℚ) / n).den ∣ n := by
    have hdenZ : ((Rat.divInt 1 (n : ℤ)).den : ℤ) ∣ (n : ℤ) :=
      Rat.den_dvd 1 (n : ℤ)
    have heq : Rat.divInt 1 (n : ℤ) = (1 : ℚ) / n := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [heq] at hdenZ
    exact_mod_cast hdenZ
  exact hden.trans (Finset.dvd_lcm hn)

lemma primePowerPart_of_recSum_den_dvd_lcm {A : Finset ℕ} {q : ℕ}
    (hq : q ∈ primePowerParts (UnitFractions.rec_sum A).den) :
    q ∣ A.lcm id := by
  exact ((mem_primePowerParts (UnitFractions.rec_sum A).den_ne_zero).mp hq).2.1.trans
    (recSum_den_dvd_lcm A)

lemma zero_not_mem_Icc_one (y : ℕ) : 0 ∉ Icc 1 y := by simp

lemma ppowers_in_initial_interval_le (y : ℕ) {q : ℕ}
    (hq : q ∈ UnitFractions.ppowers_in_set (Icc 1 y)) : q ≤ y := by
  rw [UnitFractions.mem_ppowers_in_set] at hq
  obtain ⟨n, hn⟩ := hq.2
  rcases (UnitFractions.mem_local_part n).mp hn with ⟨hnIcc, hqdiv, _⟩
  exact (Nat.le_of_dvd (Finset.mem_Icc.mp hnIcc).1 hqdiv).trans
    (Finset.mem_Icc.mp hnIcc).2

/-- A reusable exponential bound for `lcm(1,...,y)`. -/
lemma exists_initialLcm_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ,
      (initialLcm y : ℝ) ≤ Real.exp (C * y) := by
  obtain ⟨C, hC, hbound⟩ := UnitFractions.smooth_lcm
  refine ⟨C, hC, fun y ↦ ?_⟩
  change (↑((Icc 1 y).lcm (id : ℕ → ℕ)) : ℝ) ≤ Real.exp (C * y)
  apply hbound y (by positivity) (Icc 1 y) (zero_not_mem_Icc_one y)
  intro q hq
  exact_mod_cast ppowers_in_initial_interval_le y hq

end




/-!
# The modular subset-sum core of Martin's construction

This file isolates the finite cyclic-group argument used when eliminating a
prime-power factor from the denominator of a residual rational number.  The
objects being added are the inverses of the auxiliary denominators modulo the
prime power.

The first result below is the Cauchy--Davenport--Chowla branch of Martin's
subset-sum lemma: at least `n - 1` invertible residues modulo `n`, with the
choices indexed separately even when residues repeat, represent every residue
as a subset sum.  Keeping the indices separate is essential in the application
to distinct Egyptian-fraction denominators.
-/

open scoped BigOperators
open Finset

noncomputable section

/-- The least-absolute-value representative of `h / m (mod n)`. -/
def centeredInverse (n h m : ℕ) : ℤ :=
  ((h : ZMod n) * (m : ZMod n)⁻¹).valMinAbs

/-- A finite fiber-counting lemma used in the pigeonhole part of Martin's
inverse-dispersion argument. -/
theorem card_le_card_mul_of_fiber_bound {α β : Type*} [DecidableEq α]
    [Fintype β] [DecidableEq β] (S : Finset α) (bucket : α → β) (D : ℕ)
    (hfiber : ∀ b : β, (S.filter fun x ↦ bucket x = b).card ≤ D) :
    S.card ≤ Fintype.card β * D := by
  rw [card_eq_sum_card_fiberwise (t := univ) (f := bucket) (by simp)]
  calc
    ∑ b ∈ (univ : Finset β), (S.filter fun x ↦ bucket x = b).card
        ≤ ∑ _b ∈ (univ : Finset β), D := by
          exact sum_le_sum fun b _ ↦ hfiber b
    _ = Fintype.card β * D := by simp

/-- Exact finite form of the pigeonhole conclusion in Martin's modular
inverse-dispersion lemma.  The `bucket` is the integer
`(m * r_m - h) / n`; its source-specific fiber bound comes from counting
divisors with exactly `k` distinct prime factors. -/
theorem centeredInverse_dispersion_of_fiber_bound
    (n h R L D : ℕ) (M : Finset ℕ) (bucket : ℕ → Fin L)
    (hfiber : ∀ b : Fin L,
      ((M.filter fun m ↦ (centeredInverse n h m).natAbs ≤ R).filter
        fun m ↦ bucket m = b).card ≤ D)
    (hhalf : 2 * (L * D) ≤ M.card) :
    M.card ≤ 2 * (M.filter fun m ↦ R < (centeredInverse n h m).natAbs).card := by
  let bad := M.filter fun m ↦ (centeredInverse n h m).natAbs ≤ R
  have hbad : bad.card ≤ L * D := by
    have h := card_le_card_mul_of_fiber_bound bad bucket D hfiber
    simpa using h
  have hpartition := card_filter_add_card_filter_not
    (s := M) (p := fun m ↦ (centeredInverse n h m).natAbs ≤ R)
  change bad.card + (M.filter fun m ↦ ¬ (centeredInverse n h m).natAbs ≤ R).card =
    M.card at hpartition
  have hgood :
      (M.filter fun m ↦ ¬ (centeredInverse n h m).natAbs ≤ R).card =
        (M.filter fun m ↦ R < (centeredInverse n h m).natAbs).card := by
    congr 1
    ext m
    simp
  rw [hgood] at hpartition
  omega

/-- Powerset product expansion: summing over all subsets gives the product of
one-plus factors. This identity is used in the Fourier transform of the inverse
subset-sum counting function. -/
lemma sum_powerset_prod {ι : Type*} (I : Finset ι) (x : ι → ℂ) :
    ∑ K ∈ I.powerset, ∏ k ∈ K, x k = ∏ i ∈ I, (1 + x i) := by
  rw [Finset.prod_one_add]

/-- Multiplicity of a residue among all indexed inverse subset sums, embedded
in `ℂ` for Fourier inversion. -/
def inverseSubsetMass (n : ℕ) (M : Finset ℕ) (a : ZMod n) : ℂ :=
  ∑ K ∈ M.powerset,
    if K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a then 1 else 0

theorem inverseSubsetMass_eq_card (n : ℕ) (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a =
      ((M.powerset.filter fun K ↦
        K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a).card : ℂ) := by
  rw [inverseSubsetMass, ← sum_filter]
  simp

theorem inverseSubsetMass_ne_zero_iff (n : ℕ) (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a ≠ 0 ↔
      ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  rw [inverseSubsetMass_eq_card]
  simp

/-- The Fourier transform of the inverse-subset multiplicity is Martin's
product `∏ (1 + e_n(-h / m))`. -/
theorem dft_inverseSubsetMass {n : ℕ} [NeZero n] (M : Finset ℕ) (h : ZMod n) :
    ZMod.dft (inverseSubsetMass n M) h =
      M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, inverseSubsetMass]
  simp_rw [Finset.mul_sum]
  rw [sum_comm]
  simp only [mul_ite, mul_one, mul_zero]
  have hinner (K : Finset ℕ) :
      (∑ j : ZMod n, if K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = j then
        ZMod.stdAddChar (-(j * h)) else 0) =
          ZMod.stdAddChar (-(K.sum (fun m ↦ ((m : ZMod n)⁻¹)) * h)) := by
    let s := K.sum (fun m ↦ ((m : ZMod n)⁻¹))
    change (∑ j : ZMod n, if s = j then ZMod.stdAddChar (-(j * h)) else 0) = _
    have hfun :
        (fun j : ZMod n ↦ if s = j then ZMod.stdAddChar (-(j * h)) else 0) =
          fun j ↦ if j = s then ZMod.stdAddChar (-(j * h)) else 0 := by
      funext j
      by_cases heq : s = j
      · rw [if_pos heq, if_pos heq.symm]
      · rw [if_neg heq, if_neg (fun hjs ↦ heq hjs.symm)]
    rw [hfun]
    simp [s]
  have hchar (K : Finset ℕ) :
      ZMod.stdAddChar (-(K.sum (fun m ↦ ((m : ZMod n)⁻¹)) * h)) =
        K.prod fun m ↦ ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)) := by
    induction K using Finset.induction with
    | empty => simp
    | @insert m K hm ih =>
        rw [sum_insert hm, prod_insert hm, ← ih, ← AddChar.map_add_eq_mul]
        congr 1
        ring
  simp_rw [hinner, hchar]
  exact sum_powerset_prod M _

/-- Fourier inversion formula for the exact subset count. -/
theorem inverseSubsetMass_fourier {n : ℕ} [NeZero n] (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a =
      (n : ℂ)⁻¹ * ∑ h : ZMod n,
        ZMod.stdAddChar (h * a) *
          (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))) := by
  have hinv := congr_fun (ZMod.dft.symm_apply_apply (inverseSubsetMass n M)) a
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul, dft_inverseSubsetMass] at hinv
  exact hinv.symm

/-- Contribution of all nonzero frequencies in the inverse-subset Fourier
formula. -/
def inverseSubsetFourierError (n : ℕ) [NeZero n] (M : Finset ℕ) (a : ZMod n) : ℂ :=
  ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
    ZMod.stdAddChar (h * a) *
      (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))

/-- If the nonzero Fourier modes have total norm smaller than the zero mode,
then every prescribed residue has an inverse subset-sum representation. -/
theorem inverse_subset_sum_surjective_of_fourier_error {n : ℕ} [NeZero n]
    (M : Finset ℕ) (a : ZMod n)
    (herror : ‖inverseSubsetFourierError n M a‖ < (2 : ℝ) ^ M.card) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply (inverseSubsetMass_ne_zero_iff n M a).mp
  rw [inverseSubsetMass_fourier]
  apply mul_ne_zero
  · exact inv_ne_zero (by exact_mod_cast NeZero.ne n)
  · have hsplit :
        (∑ h : ZMod n,
          ZMod.stdAddChar (h * a) *
            (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))) =
          (2 : ℂ) ^ M.card + inverseSubsetFourierError n M a := by
        change (∑ h : ZMod n,
          ZMod.stdAddChar (h * a) *
            (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))) =
          (2 : ℂ) ^ M.card +
            ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
              ZMod.stdAddChar (h * a) *
                (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))
        rw [← sum_erase_add _ _ (mem_univ (0 : ZMod n))]
        rw [add_comm]
        congr 1
        simp
        norm_num
    rw [hsplit]
    intro hzero
    have herr_eq : inverseSubsetFourierError n M a = -((2 : ℂ) ^ M.card) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_comm] using hzero
    have hnorm : ‖inverseSubsetFourierError n M a‖ = (2 : ℝ) ^ M.card := by
      rw [herr_eq, norm_neg, norm_pow]
      norm_num
    linarith

/-- Pointwise Fourier coefficient control implies the total-error hypothesis.
This is the exact analytic interface used after Martin's inverse-dispersion
estimate bounds each nonzero product. -/
theorem inverse_subset_sum_surjective_of_fourier_bound {n : ℕ} [NeZero n]
    (M : Finset ℕ) (a : ZMod n) (E : ℝ)
    (hcoeff : ∀ h : ZMod n, h ≠ 0 →
      ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤ E)
    (hdom : ((n - 1 : ℕ) : ℝ) * E < (2 : ℝ) ^ M.card) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply inverse_subset_sum_surjective_of_fourier_error M a
  calc
    ‖inverseSubsetFourierError n M a‖
        ≤ ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
            ‖ZMod.stdAddChar (h * a) *
              (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))‖ :=
          by
            simpa only [inverseSubsetFourierError] using
              norm_sum_le (univ.erase 0 : Finset (ZMod n)) (fun h ↦
                ZMod.stdAddChar (h * a) *
                  (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))))
    _ ≤ ∑ _h ∈ (univ.erase 0 : Finset (ZMod n)), E := by
          apply sum_le_sum
          intro h hh
          rw [norm_mul, AddChar.norm_apply, one_mul]
          exact hcoeff h (ne_of_mem_erase hh)
    _ = ((n - 1 : ℕ) : ℝ) * E := by
          rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ (0 : ZMod n)), card_univ,
            ZMod.card]
    _ < (2 : ℝ) ^ M.card := hdom

/-- Residues obtained by summing inverses of a subset of the indexed integers. -/
def inverseSubsetSums (n : ℕ) (M : Finset ℕ) : Finset (ZMod n) :=
  M.powerset.image fun K : Finset ℕ ↦ K.sum fun m ↦ ((m : ZMod n)⁻¹)

@[simp] theorem inverseSubsetSums_empty (n : ℕ) : inverseSubsetSums n ∅ = {0} := by
  simp [inverseSubsetSums]

theorem mem_inverseSubsetSums_iff {n : ℕ} {M : Finset ℕ} {a : ZMod n} :
    a ∈ inverseSubsetSums n M ↔
      ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  simp [inverseSubsetSums]

theorem inverseSubsetSums_insert {n m : ℕ} {M : Finset ℕ} (hm : m ∉ M) :
    inverseSubsetSums n (insert m M) =
      inverseSubsetSums n M ∪
        (inverseSubsetSums n M).image (fun x ↦ ((m : ZMod n)⁻¹) + x) := by
  ext a
  constructor
  · intro ha
    obtain ⟨K, hK, rfl⟩ := mem_inverseSubsetSums_iff.mp ha
    by_cases hmem : m ∈ K
    · rw [mem_union]
      right
      refine mem_image.mpr ⟨(K.erase m).sum (fun x ↦ ((x : ZMod n)⁻¹)), ?_, ?_⟩
      · apply mem_inverseSubsetSums_iff.mpr
        refine ⟨K.erase m, ?_, rfl⟩
        intro x hx
        have hxK : x ∈ K := mem_of_mem_erase hx
        have hxInsert := hK hxK
        rcases mem_insert.mp hxInsert with hxm | hxM
        · exact False.elim ((ne_of_mem_erase hx) hxm)
        · exact hxM
      · simpa [add_comm] using sum_erase_add K (fun x ↦ ((x : ZMod n)⁻¹)) hmem
    · rw [mem_union]
      left
      apply mem_inverseSubsetSums_iff.mpr
      refine ⟨K, ?_, rfl⟩
      intro x hx
      rcases mem_insert.mp (hK hx) with hxm | hxM
      · exact False.elim (hmem (hxm ▸ hx))
      · exact hxM
  · intro ha
    rw [mem_union] at ha
    rcases ha with ha | ha
    · obtain ⟨K, hK, rfl⟩ := mem_inverseSubsetSums_iff.mp ha
      apply mem_inverseSubsetSums_iff.mpr
      exact ⟨K, hK.trans (subset_insert m M), rfl⟩
    · obtain ⟨x, hx, hxa⟩ := mem_image.mp ha
      obtain ⟨K, hK, hxK⟩ := mem_inverseSubsetSums_iff.mp hx
      apply mem_inverseSubsetSums_iff.mpr
      refine ⟨insert m K, ?_, ?_⟩
      · exact insert_subset_insert m hK
      · rw [sum_insert]
        · rw [hxK, hxa]
        · exact fun h ↦ hm (hK h)

/-- An invertible residue additively generates the cyclic group `ZMod n`. -/
theorem nsmul_unit_hits {n : ℕ} [NeZero n] {u y : ZMod n} (hu : IsUnit u) :
    ∃ k : ℕ, k • u = y := by
  let k : ℕ := (y * u⁻¹).val
  refine ⟨k, ?_⟩
  simp only [nsmul_eq_mul]
  rw [show (k : ZMod n) = y * u⁻¹ by simp [k]]
  rw [mul_assoc, ZMod.inv_mul_of_unit u hu, mul_one]

/-- A nonempty proper subset cannot be stable under translation by a unit. -/
theorem unit_translate_not_subset {n : ℕ} [NeZero n] {u : ZMod n}
    (hu : IsUnit u) {A : Finset (ZMod n)} (hzero : 0 ∈ A) (hproper : A ≠ univ) :
    ¬ A.image (fun x ↦ u + x) ⊆ A := by
  intro hstable
  have hnsmul : ∀ k : ℕ, k • u ∈ A := by
    intro k
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
        apply hstable
        exact mem_image.mpr ⟨k • u, ih, by
          simp only [nsmul_eq_mul, Nat.cast_succ]
          ring⟩
  apply hproper
  apply eq_univ_of_forall
  intro y
  obtain ⟨k, hk⟩ := nsmul_unit_hits (y := y) hu
  rw [← hk]
  exact hnsmul k

theorem card_lt_card_union_unit_translate {n : ℕ} [NeZero n] {u : ZMod n}
    (hu : IsUnit u) {A : Finset (ZMod n)} (hzero : 0 ∈ A)
    (hcard : A.card < n) :
    A.card < (A ∪ A.image (fun x ↦ u + x)).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, ?_⟩
  intro heq
  have hproper : A ≠ univ := by
    intro hA
    have : A.card = n := by simp [hA]
    omega
  exact unit_translate_not_subset hu hzero hproper (by
    intro x hx
    have hx' : x ∈ A ∪ A.image (fun z ↦ u + z) := mem_union_right A hx
    rw [← heq] at hx'
    exact hx')

/-- Quantitative Chowla growth for the indexed inverse subset sums. -/
theorem min_card_succ_le_card_inverseSubsetSums (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n) :
    min (M.card + 1) n ≤ (inverseSubsetSums n M).card := by
  induction M using Finset.induction with
  | empty => simp
  | @insert m M hm ih =>
      have hcoprimeM : ∀ x ∈ M, Nat.Coprime x n :=
        fun x hx ↦ hcoprime x (mem_insert_of_mem hx)
      have hcm := ih hcoprimeM
      rw [inverseSubsetSums_insert hm]
      have hunit0 : IsUnit (m : ZMod n) :=
        (ZMod.isUnit_iff_coprime m n).mpr (hcoprime m (mem_insert_self m M))
      have hunit : IsUnit ((m : ZMod n)⁻¹) :=
        isUnit_of_dvd_one ⟨(m : ZMod n), (ZMod.inv_mul_of_unit (m : ZMod n) hunit0).symm⟩
      have hzero : 0 ∈ inverseSubsetSums n M := by
        apply mem_inverseSubsetSums_iff.mpr
        exact ⟨∅, empty_subset _, by simp⟩
      by_cases hfull : n ≤ (inverseSubsetSums n M).card
      · have heq : (inverseSubsetSums n M).card = n := by
          apply le_antisymm
          · simpa [ZMod.card] using card_le_univ (inverseSubsetSums n M)
          · exact hfull
        have hset : inverseSubsetSums n M = univ := by
          apply eq_univ_of_card
          simpa [ZMod.card] using heq
        rw [hset, Finset.union_eq_left.mpr (subset_univ _), card_univ, ZMod.card]
        simp only [card_insert_of_notMem hm]
        omega
      · have hlt : (inverseSubsetSums n M).card < n := Nat.lt_of_not_ge hfull
        have hgrowth := card_lt_card_union_unit_translate hunit hzero hlt
        simp only [card_insert_of_notMem hm]
        omega

/-- If the indexed set has at least `n - 1` elements, every residue modulo
`n` is a sum of inverses of a subset.  Martin invokes the slightly weaker
hypothesis `n ≤ M.card` in this branch. -/
theorem inverse_subset_sum_surjective (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n)
    (hcard : n ≤ M.card + 1) (a : ZMod n) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  have hle := min_card_succ_le_card_inverseSubsetSums n M hcoprime
  have hcount : n ≤ (inverseSubsetSums n M).card := by
    simpa [min_eq_right hcard] using hle
  have hall : inverseSubsetSums n M = univ := by
    apply eq_univ_of_card
    apply le_antisymm
    · simpa [ZMod.card] using card_le_univ (inverseSubsetSums n M)
    · rw [ZMod.card]
      exact hcount
  apply mem_inverseSubsetSums_iff.mp
  simp [hall]

/-- Martin's stated large-cardinality branch, with the paper's hypothesis
`n ≤ |M|` rather than the slightly sharper cutoff proved above. -/
theorem inverse_subset_sum_surjective_of_card (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n)
    (hcard : n ≤ M.card) (a : ZMod n) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply inverse_subset_sum_surjective n M hcoprime (a := a)
  omega

/-- Prime-power specialization of the modular elimination step.  It is enough
to check that the underlying prime divides none of the auxiliary factors. -/
theorem primePower_inverse_subset_sum_surjective {p ν : ℕ} (hp : p.Prime)
    (M : Finset ℕ) (hnotdvd : ∀ m ∈ M, ¬ p ∣ m)
    (hcard : p ^ ν ≤ M.card + 1) (a : ZMod (p ^ ν)) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod (p ^ ν))⁻¹)) = a := by
  let _ : NeZero (p ^ ν) := ⟨pow_ne_zero ν hp.ne_zero⟩
  apply inverse_subset_sum_surjective (p ^ ν) M (a := a) ?_ hcard
  intro m hm
  exact hp.coprime_pow_of_not_dvd (hnotdvd m hm)

/-- The exact hypothesis used when Martin dismisses the `|M| ≥ q` case of
the large-prime-power elimination lemma. -/
theorem primePower_inverse_subset_sum_surjective_of_card {p ν : ℕ} (hp : p.Prime)
    (M : Finset ℕ) (hnotdvd : ∀ m ∈ M, ¬ p ∣ m)
    (hcard : p ^ ν ≤ M.card) (a : ZMod (p ^ ν)) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod (p ^ ν))⁻¹)) = a := by
  apply primePower_inverse_subset_sum_surjective hp M hnotdvd (a := a)
  omega

end




/-!
# Good denominators and exact denominator clearing

This file packages the finite arithmetic objects in the Liu--Sawhney lower
bound.  Their notion of smoothness bounds every *exact prime-power part* of a
denominator, rather than only its prime divisors.  We use the prime-power
infrastructure developed above for that distinction.

For integer cutoffs `M ≤ N` and `S`, `goodDenominators N M S` is the set

`{n ∈ [M,N] : P*(n) ≤ S, max_p v_p(n) ≤ floor(5 log log N),
                    Ω(n) ≤ floor(10 log log N)}`.

The common denominator `smoothLcm S` is `lcm(1,...,S)`.  The main results
below prove that every good denominator divides it, every reciprocal sum over
good denominators has reduced denominator dividing it, and clearing
denominators gives the expected integer identity.  The last section records
the exact prime-power factorization and double-counting identities used in
the minor-arc argument.
-/

open Finset Real
open scoped ArithmeticFunction.Omega BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Liu--Sawhney's bound `floor (5 log log N)` for the largest exponent in a
prime factorization. -/
def exponentBound (N : ℕ) : ℕ :=
  ⌊5 * Real.log (Real.log (N : ℝ))⌋₊

/-- Liu--Sawhney's bound `floor (10 log log N)` for the total number of prime
factors, counted with multiplicity. -/
def factorBound (N : ℕ) : ℕ :=
  ⌊10 * Real.log (Real.log (N : ℝ))⌋₊

/-- The largest exponent appearing in the prime factorization of `n`, with
value zero at `n = 0,1`. -/
def maxPrimeExponent (n : ℕ) : ℕ :=
  n.factorization.support.sup fun p ↦ n.factorization p

/-- The finite good set in the simplified Liu--Sawhney proposition. -/
def goodDenominators (N M S : ℕ) : Finset ℕ :=
  (Icc M N).filter fun n ↦
    PrimePowerSmooth S n ∧
      maxPrimeExponent n ≤ exponentBound N ∧
      Ω n ≤ factorBound N

/-- All prime powers at most the smoothness cutoff. -/
abbrev smoothPrimePowers (S : ℕ) : Finset ℕ := primePowersUpTo S

/-- The common denominator `Q(S) = lcm(1,2,...,S)`. -/
abbrev smoothLcm (S : ℕ) : ℕ := initialLcm S

/-- The subfamily of `A` consisting of multiples of `d`; this is the source's
notation `A_d`. -/
def divisiblePart (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  A.filter fun n ↦ d ∣ n

/-- The exact `q`-part of `A`: denominators whose full prime-power part at
the prime below `q` is exactly `q`.  This is the local decomposition already
used throughout the unit-fraction library. -/
abbrev exactLocalPart (A : Finset ℕ) (q : ℕ) : Finset ℕ :=
  UnitFractions.local_part A q

@[simp] lemma mem_goodDenominators {N M S n : ℕ} :
    n ∈ goodDenominators N M S ↔
      M ≤ n ∧ n ≤ N ∧ PrimePowerSmooth S n ∧
        maxPrimeExponent n ≤ exponentBound N ∧
        Ω n ≤ factorBound N := by
  simp [goodDenominators, and_assoc]

@[simp] lemma mem_divisiblePart {A : Finset ℕ} {d n : ℕ} :
    n ∈ divisiblePart A d ↔ n ∈ A ∧ d ∣ n := by
  simp [divisiblePart]

@[simp] lemma mem_exactLocalPart {A : Finset ℕ} {q n : ℕ} :
    n ∈ exactLocalPart A q ↔
      n ∈ A ∧ q ∣ n ∧ Nat.Coprime q (n / q) :=
  UnitFractions.mem_local_part n

lemma exactLocalPart_subset_divisiblePart (A : Finset ℕ) (q : ℕ) :
    exactLocalPart A q ⊆ divisiblePart A q := by
  intro n hn
  exact mem_divisiblePart.mpr ⟨(mem_exactLocalPart.mp hn).1,
    (mem_exactLocalPart.mp hn).2.1⟩

lemma card_exactLocalPart_le_divisiblePart (A : Finset ℕ) (q : ℕ) :
    (exactLocalPart A q).card ≤ (divisiblePart A q).card :=
  Finset.card_le_card (exactLocalPart_subset_divisiblePart A q)

lemma goodDenominators_subset_Icc (N M S : ℕ) :
    goodDenominators N M S ⊆ Icc M N :=
  filter_subset _ _

lemma goodDenominator_pos {N M S n : ℕ} (hM : 1 ≤ M)
    (hn : n ∈ goodDenominators N M S) : 0 < n := by
  exact (hM.trans (mem_goodDenominators.mp hn).1).trans_lt' Nat.zero_lt_one

lemma goodDenominator_smooth {N M S n : ℕ}
    (hn : n ∈ goodDenominators N M S) : PrimePowerSmooth S n :=
  (mem_goodDenominators.mp hn).2.2.1

lemma goodDenominator_factorBound {N M S n : ℕ}
    (hn : n ∈ goodDenominators N M S) :
    Ω n ≤ factorBound N :=
  (mem_goodDenominators.mp hn).2.2.2.2

lemma goodDenominator_exponentBound {N M S n : ℕ}
    (hn : n ∈ goodDenominators N M S) :
    maxPrimeExponent n ≤ exponentBound N :=
  (mem_goodDenominators.mp hn).2.2.2.1

/-! ## Exact prime-power factorization -/

/-- The exact prime-power parts of a nonzero integer have LCM equal to the
integer itself. -/
lemma lcm_primePowerParts {n : ℕ} (hn : n ≠ 0) :
    (primePowerParts n).lcm id = n := by
  rw [primePowerParts_eq_ppowers_in_singleton]
  calc
    UnitFractions.lcmA (UnitFractions.ppowers_in_set {n}) =
        UnitFractions.lcmA ({n} : Finset ℕ) :=
      UnitFractions.lcm_Q (by simpa using hn.symm)
    _ = n := by simp [UnitFractions.lcmA]

/-- Every exact prime-power part of a smooth integer occurs among the prime
powers up to the smoothness cutoff. -/
lemma primePowerParts_subset_smoothPrimePowers {S n : ℕ}
    (hn : PrimePowerSmooth S n) :
    primePowerParts n ⊆ smoothPrimePowers S := by
  intro q hq
  exact mem_primePowersUpTo.mpr
    ⟨((mem_primePowerParts (by rintro rfl; simp [primePowerParts] at hq)).mp hq).1,
      hn q hq⟩

/-- The number of exact prime-power parts is at most `Ω(n)`.  This is the
finite multiplicity budget used when factors are assigned to denominators. -/
lemma card_primePowerParts_le_Omega {n : ℕ} (hn : n ≠ 0) :
    (primePowerParts n).card ≤ Ω n := by
  rw [UnitFractions.Omega_eq_card_prime_pow_divisors hn]
  exact Finset.card_le_card fun q hq ↦ by
    rw [primePowerParts, mem_filter] at hq
    exact mem_filter.mpr ⟨hq.1, hq.2.1⟩

/-- Each individual prime exponent is bounded by the total multiplicity
`Ω(n)`. -/
lemma factorization_le_Omega (n p : ℕ) :
    n.factorization p ≤ Ω n := by
  by_cases hp : p ∈ n.factorization.support
  · rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
    exact Finset.single_le_sum (fun q hq ↦ Nat.zero_le (n.factorization q)) hp
  · rw [Finsupp.notMem_support_iff.mp hp]
    exact Nat.zero_le _

lemma maxPrimeExponent_le_Omega (n : ℕ) :
    maxPrimeExponent n ≤ Ω n := by
  rw [maxPrimeExponent, Finset.sup_le_iff]
  intro p hp
  exact factorization_le_Omega n p

/-- A good denominator has at most `factorBound N` exact prime-power parts. -/
lemma card_primePowerParts_good_le {N M S n : ℕ} (hM : 1 ≤ M)
    (hn : n ∈ goodDenominators N M S) :
    (primePowerParts n).card ≤ factorBound N := by
  exact (card_primePowerParts_le_Omega (goodDenominator_pos hM hn).ne').trans
    (goodDenominator_factorBound hn)

/-- Exact prime-power parts are precisely the nonempty local components of a
singleton denominator. -/
lemma mem_primePowerParts_iff {n q : ℕ} :
    q ∈ primePowerParts n ↔
      IsPrimePow q ∧ (exactLocalPart {n} q).Nonempty := by
  rw [primePowerParts_eq_ppowers_in_singleton,
    UnitFractions.mem_ppowers_in_set]

/-- The prime powers occurring exactly in some member of `A` are the union
of the exact prime-power factorizations of its members. -/
lemma ppowersInSet_eq_biUnion_primePowerParts (A : Finset ℕ) :
    UnitFractions.ppowers_in_set A = A.biUnion primePowerParts := by
  rfl

/-! ## The common LCM and exact denominator clearing -/

/-- A nonzero prime-power-smooth integer divides `Q(S)`. -/
lemma dvd_smoothLcm_of_smooth {S n : ℕ} (hn0 : n ≠ 0)
    (hn : PrimePowerSmooth S n) : n ∣ smoothLcm S := by
  have hparts : (primePowerParts n).lcm id ∣ smoothLcm S := by
    apply Finset.lcm_dvd
    intro q hq
    exact Finset.dvd_lcm (s := Icc 1 S) (f := id)
      (Finset.mem_Icc.mpr
        ⟨((mem_primePowerParts hn0).mp hq).1.one_lt.le, hn q hq⟩)
  rwa [lcm_primePowerParts hn0] at hparts

lemma goodDenominator_dvd_smoothLcm {N M S n : ℕ} (hM : 1 ≤ M)
    (hn : n ∈ goodDenominators N M S) : n ∣ smoothLcm S :=
  dvd_smoothLcm_of_smooth (goodDenominator_pos hM hn).ne'
    (goodDenominator_smooth hn)

/-- The two source descriptions of `Q(S)` agree: it is both the LCM of all
prime powers at most `S` and `lcm(1,...,S)`. -/
lemma smoothPrimePowers_eq_ppowersInInterval (S : ℕ) :
    smoothPrimePowers S = UnitFractions.ppowers_in_set (Icc 1 S) := by
  ext q
  rw [mem_primePowersUpTo, UnitFractions.mem_ppowers_in_set]
  constructor
  · rintro ⟨hqpp, hqS⟩
    refine ⟨hqpp, ⟨q, (UnitFractions.mem_local_part q).mpr ?_⟩⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hqpp.one_lt.le, hqS⟩, dvd_rfl,
      by rw [Nat.div_self hqpp.pos]; exact Nat.coprime_one_right q⟩
  · rintro ⟨hqpp, ⟨n, hn⟩⟩
    rcases (UnitFractions.mem_local_part n).mp hn with ⟨hnIcc, hqn, -⟩
    exact ⟨hqpp, (Nat.le_of_dvd (Finset.mem_Icc.mp hnIcc).1 hqn).trans
      (Finset.mem_Icc.mp hnIcc).2⟩

lemma lcm_smoothPrimePowers (S : ℕ) :
    (smoothPrimePowers S).lcm id = smoothLcm S := by
  rw [smoothPrimePowers_eq_ppowersInInterval]
  change UnitFractions.lcmA (UnitFractions.ppowers_in_set (Icc 1 S)) =
    UnitFractions.lcmA (Icc 1 S)
  exact UnitFractions.lcm_Q (by simp)

/-- The LCM of any family of good denominators divides the common smooth LCM. -/
lemma lcm_dvd_smoothLcm {N M S : ℕ} {A : Finset ℕ} (hM : 1 ≤ M)
    (hA : A ⊆ goodDenominators N M S) : A.lcm id ∣ smoothLcm S := by
  apply Finset.lcm_dvd
  intro n hn
  exact goodDenominator_dvd_smoothLcm hM (hA hn)

/-- The reduced denominator of a reciprocal sum over good denominators
divides `Q(S)`. -/
lemma recSum_den_dvd_smoothLcm {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    (UnitFractions.rec_sum A).den ∣ smoothLcm S :=
  (recSum_den_dvd_lcm A).trans (lcm_dvd_smoothLcm hM hA)

/-- Clearing one reciprocal denominator inside `Q(S)`. -/
lemma smoothLcm_mul_one_div {S n : ℕ} (hn0 : n ≠ 0)
    (hn : n ∣ smoothLcm S) :
    (smoothLcm S : ℚ) * ((1 : ℚ) / n) = (smoothLcm S / n : ℕ) := by
  field_simp [hn0]
  exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_mul_cancel hn).symm)

/-- Exact denominator-clearing identity for an arbitrary smooth finite set. -/
lemma smoothLcm_mul_recSum {S : ℕ} {A : Finset ℕ} (hA0 : 0 ∉ A)
    (hA : ∀ n ∈ A, n ∣ smoothLcm S) :
    (smoothLcm S : ℚ) * UnitFractions.rec_sum A =
      ∑ n ∈ A, ((smoothLcm S / n : ℕ) : ℚ) := by
  rw [UnitFractions.rec_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact smoothLcm_mul_one_div (fun hn0 ↦ hA0 (hn0 ▸ hn)) (hA n hn)

/-- Exact denominator clearing specialized to a subfamily of the good set. -/
lemma smoothLcm_mul_recSum_good {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    (smoothLcm S : ℚ) * UnitFractions.rec_sum A =
      ∑ n ∈ A, ((smoothLcm S / n : ℕ) : ℚ) := by
  apply smoothLcm_mul_recSum
  · intro h0
    have := goodDenominator_pos hM (hA h0)
    omega
  · intro n hn
    exact goodDenominator_dvd_smoothLcm hM (hA hn)

/-! ## Prime-power divisor incidence and double counting -/

/-- The prime-power divisors of `n`, including all intermediate powers.  For
nonzero `n` its cardinality is exactly `Ω(n)`. -/
def primePowerDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter IsPrimePow

@[simp] lemma mem_primePowerDivisors {n q : ℕ} (hn : n ≠ 0) :
    q ∈ primePowerDivisors n ↔ IsPrimePow q ∧ q ∣ n := by
  simp [primePowerDivisors, Nat.mem_divisors, hn, and_comm]

lemma card_primePowerDivisors {n : ℕ} (hn : n ≠ 0) :
    (primePowerDivisors n).card = Ω n := by
  exact (UnitFractions.Omega_eq_card_prime_pow_divisors hn).symm

/-- Smoothness of exact prime-power parts bounds every prime-power divisor. -/
lemma primePowerDivisor_le_of_smooth {S n q : ℕ} (hn0 : n ≠ 0)
    (hn : PrimePowerSmooth S n) (hqpp : IsPrimePow q) (hqn : q ∣ n) : q ≤ S := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hqpp
  have hfac : k ≤ n.factorization p :=
    (hp.pow_dvd_iff_le_factorization hn0).mp hqn
  have hfac0 : n.factorization p ≠ 0 := by omega
  have hexact : p ^ n.factorization p ∈ primePowerParts n := by
    rw [primePowerParts_eq_ppowers_in_singleton,
      UnitFractions.mem_ppowers_in_set' hp hfac0]
    exact ⟨n, by simp⟩
  exact (Nat.pow_le_pow_right hp.pos hfac).trans (hn _ hexact)

lemma primePowerDivisors_subset_smoothPrimePowers {S n : ℕ} (hn0 : n ≠ 0)
    (hn : PrimePowerSmooth S n) :
    primePowerDivisors n ⊆ smoothPrimePowers S := by
  intro q hq
  rw [mem_primePowerDivisors hn0] at hq
  exact mem_primePowersUpTo.mpr
    ⟨hq.1, primePowerDivisor_le_of_smooth hn0 hn hq.1 hq.2⟩

/-- Incidence double counting: summing the sizes of `A_q` over all prime
powers up to `S` counts each nonzero smooth `n ∈ A` exactly `Ω(n)` times. -/
lemma sum_card_divisiblePart_eq_sum_Omega {S : ℕ} {A : Finset ℕ}
    (hA0 : 0 ∉ A) (hAsmooth : ∀ n ∈ A, PrimePowerSmooth S n) :
    ∑ q ∈ smoothPrimePowers S, (divisiblePart A q).card =
      ∑ n ∈ A, Ω n := by
  calc
    ∑ q ∈ smoothPrimePowers S, (divisiblePart A q).card =
        ∑ q ∈ smoothPrimePowers S, ∑ n ∈ A, if q ∣ n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [divisiblePart]
    _ = ∑ n ∈ A, ∑ q ∈ smoothPrimePowers S, if q ∣ n then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ A, Ω n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := fun hn0 ↦ hA0 (hn0 ▸ hn)
      calc
        (∑ q ∈ smoothPrimePowers S, if q ∣ n then (1 : ℕ) else 0) =
            (primePowerDivisors n).card := by
          rw [Finset.sum_boole]
          apply congrArg Finset.card
          ext q
          rw [mem_filter, mem_primePowerDivisors hn0, mem_primePowersUpTo]
          constructor
          · rintro ⟨⟨hqpp, _⟩, hqn⟩
            exact ⟨hqpp, hqn⟩
          · rintro ⟨hqpp, hqn⟩
            exact ⟨⟨hqpp, primePowerDivisor_le_of_smooth hn0
              (hAsmooth n hn) hqpp hqn⟩, hqn⟩
        _ = Ω n := card_primePowerDivisors hn0

/-- The total number of prime-power incidences in a subfamily of the good set
is at most the source's multiplicity budget. -/
lemma sum_card_divisiblePart_good_le {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    ∑ q ∈ smoothPrimePowers S, (divisiblePart A q).card ≤
      A.card * factorBound N := by
  rw [sum_card_divisiblePart_eq_sum_Omega
    (fun h0 ↦ (goodDenominator_pos hM (hA h0)).ne' rfl)
    (fun n hn ↦ goodDenominator_smooth (hA hn))]
  exact Finset.sum_le_card_nsmul A (fun n ↦ Ω n)
    (factorBound N) fun n hn ↦ goodDenominator_factorBound (hA hn)

/-! ## LCM decomposition for omitted prime powers -/

/-- Omitting prime powers from the LCM costs at most their product.  This is
the exact divisibility statement behind the minor-arc frequency count. -/
lemma smoothLcm_dvd_complement_prod_mul_lcm {S : ℕ} {D : Finset ℕ}
    (_hD : D ⊆ smoothPrimePowers S) :
    smoothLcm S ∣ (smoothPrimePowers S \ D).prod id * D.lcm id := by
  rw [← lcm_smoothPrimePowers]
  apply Finset.lcm_dvd
  intro q hq
  by_cases hqD : q ∈ D
  · exact dvd_mul_of_dvd_right (Finset.dvd_lcm hqD) _
  · exact dvd_mul_of_dvd_left
      (dvd_prod_of_mem id (Finset.mem_sdiff.mpr ⟨hq, hqD⟩)) _

end



end SmoothPrimePowerFactorization

end
