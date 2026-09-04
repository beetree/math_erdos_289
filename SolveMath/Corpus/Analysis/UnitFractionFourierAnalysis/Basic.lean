module

public import SolveMath.Corpus.NumberTheory.UnitFractionDensities
public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.Basic
public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.PrimePower
public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.LargeN
public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.ReciprocalSums
public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.DivisorSelection
public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.FinalEstimates
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.TendstoLogCoeTop
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.PartialSummation
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.DivisorBound1
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.AbsVonMangoldtDiv
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.PrimeReciprocalEq
public import SolveMath.Corpus.Analysis.UnitFractionAnalyticEstimates.WeakMertensThirdUpper
public import SolveMath.Corpus.Analysis.AdditiveCharacterGeometricSums
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

@[expose] public section


namespace UnitFractions

open scoped BigOperators
open Real Finset
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

/-!
This file ports the declaration surface of `src/fourier.lean`.

Mathlib 4 already provides much of the analytic API used here, especially the complex
exponential/trigonometric identities around:

* `Complex.exp_int_mul_two_pi_mul_I`
* `Complex.exp_ofReal_mul_I_re`
* `Complex.norm_exp_ofReal_mul_I`
* `Complex.two_cos`
-/

/-- Lean 3 used a local notation `[A]` for `A.lcm id`; we use an explicit alias in Lean 4. -/
abbrev lcmA (A : Finset ℕ) : ℕ := A.lcm id

/-- Def 4.1 -/
def integer_count (A : Finset ℕ) (k : ℕ) : ℕ := by
  classical
  exact (A.powerset.filter fun S => ∃ d : ℤ, rec_sum S * k = d).card

/-- Useful for def 4.2 and in other statements. -/
def valid_sum_range (t : ℕ) : Finset ℤ :=
  Finset.Ioc ((-(t : ℤ)) / 2) ((t : ℤ) / 2)

/-- Implementation lemma. -/
lemma dumb_subtraction_thing (t : ℕ) : ((t : ℤ) / 2 - -(t : ℤ) / 2) = t := by
  omega

lemma of_mem_valid_sum_range {t : ℕ} {h : ℤ} :
    h ∈ valid_sum_range t → |(h : ℝ)| ≤ (t : ℝ) / 2 := by
  rw [valid_sum_range, Finset.mem_Ioc, and_imp, Int.ediv_lt_iff_lt_mul zero_lt_two,
    Int.le_ediv_iff_mul_le zero_lt_two]
  intro h₁ h₂
  have h₁r : (-(t : ℝ)) < (h : ℝ) * 2 := by
    exact_mod_cast h₁
  have h₂r : (h : ℝ) * 2 ≤ (t : ℝ) := by
    exact_mod_cast h₂
  refine abs_le.mpr ?_
  constructor <;> linarith

lemma zero_mem_valid_sum_range {t : ℕ} (ht : t ≠ 0) : (0 : ℤ) ∈ valid_sum_range t := by
  rw [valid_sum_range, Finset.mem_Ioc]
  have ht' : (0 : ℤ) < t := by
    exact_mod_cast Nat.pos_of_ne_zero ht
  constructor
  · omega
  · positivity

/-- Def 4.2. -/
def j (A : Finset ℕ) : Finset ℤ :=
  (valid_sum_range (A.lcm id)).erase 0

lemma mem_j (A : Finset ℕ) (h : ℤ) :
    h ∈ j A ↔
      h ≠ 0 ∧
        (-((A.lcm id : ℕ) : ℤ)) / 2 < h ∧ h ≤ ((A.lcm id : ℕ) : ℤ) / 2 := by
  simp [j, valid_sum_range]

lemma bound_of_mem_j (A : Finset ℕ) (h : ℤ) (h' : h ∈ j A) :
    |(h : ℝ)| ≤ ((A.lcm id : ℕ) : ℝ) / 2 := by
  rw [j, Finset.mem_erase] at h'
  simpa using of_mem_valid_sum_range h'.2

/-- Def 4.3. -/
def cos_prod (B : Finset ℕ) (t : ℤ) : ℝ :=
  B.prod fun n => |Real.cos (π * t / n)|

/-- Def 4.4 part one. -/
def major_arc_at (A : Finset ℕ) (k : ℕ) (K : ℝ) (t : ℤ) : Finset ℤ :=
  (j A).filter fun h => |(h : ℝ) - t * (A.lcm id) / k| ≤ K / (2 * k)

lemma mem_major_arc_at {A : Finset ℕ} {k : ℕ} {K : ℝ} {t : ℤ} (i : ℤ) :
    i ∈ major_arc_at A k K t ↔
      i ∈ j A ∧ |(i : ℝ) - t * (A.lcm id) / k| ≤ K / (2 * k) := by
  simp [major_arc_at]

lemma major_arc_at_of_neg {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hk : k ≠ 0) (hK : K < 0) (t : ℤ) :
    major_arc_at A k K t = ∅ := by
  ext i
  constructor
  · intro hi
    have hden : 0 < 2 * (k : ℝ) := by
      positivity
    have hneg : K / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos hK hden
    rw [mem_major_arc_at] at hi
    exfalso
    have habs : 0 ≤ |(i : ℝ) - t * (A.lcm id) / k| := abs_nonneg _
    linarith
  · intro hi
    exact False.elim (Finset.notMem_empty i hi)

/-- Def 4.4 part two. -/
def major_arc (A : Finset ℕ) (k : ℕ) (K : ℝ) : Finset ℤ := by
  classical
  exact (j A).filter fun h => ∃ t : ℤ, h ∈ major_arc_at A k K t

def e (x : ℝ) : ℂ :=
  AdditiveCharacterGeometricSums.additiveCharacter x

lemma e_add {x y : ℝ} : e (x + y) = e x * e y := by
  simp [e, AdditiveCharacterGeometricSums.additiveCharacter, add_mul, Complex.exp_add, mul_add,
    mul_left_comm, mul_comm]

lemma e_int (z : ℤ) : e z = 1 := by
  simpa [e, AdditiveCharacterGeometricSums.additiveCharacter, mul_assoc, mul_left_comm, mul_comm]
    using Complex.exp_int_mul_two_pi_mul_I z

lemma mem_major_arc_at' {A : Finset ℕ} {k : ℕ} {K : ℝ} {t : ℤ} (hk : k ≠ 0) (i : ℤ) :
    i ∈ major_arc_at A k K t ↔ i ∈ j A ∧ (|i * k - t * lcmA A| : ℝ) ≤ K / 2 := by
  rw [mem_major_arc_at]
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have habs :
      |(i : ℝ) - t * (lcmA A : ℝ) / k| * (k : ℝ) = (|i * k - t * lcmA A| : ℝ) := by
    calc
      |(i : ℝ) - t * (lcmA A : ℝ) / k| * (k : ℝ)
          = |(i : ℝ) - t * (lcmA A : ℝ) / k| * |(k : ℝ)| := by
              rw [abs_of_pos hkpos]
      _ = |((i : ℝ) - t * (lcmA A : ℝ) / k) * k| := by
            rw [← abs_mul]
      _ = |((i * (k : ℤ) - t * (lcmA A : ℤ) : ℤ) : ℝ)| := by
            congr 1
            field_simp [hk0]
            push_cast
            ring
      _ = (|i * (k : ℤ) - t * (lcmA A : ℤ)| : ℝ) := by
            simp
  have hdiv : K / (2 * (k : ℝ)) = (K / 2) / k := by
    field_simp [hk0]
  have hmuldiv : (K / (2 * (k : ℝ))) * (k : ℝ) = K / 2 := by
    field_simp [hk0]
  constructor
  · rintro ⟨hi, hK⟩
    refine ⟨hi, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hK hkpos.le
    rwa [habs, hmuldiv] at hmul
  · rintro ⟨hi, hK⟩
    refine ⟨hi, ?_⟩
    rw [hdiv]
    apply (le_div_iff₀ hkpos).2
    rwa [habs]

lemma j_sdiff_major_arc {A k K} :
    j A \ major_arc A k K = (j A).filter (fun h => ∀ t, h ∉ major_arc_at A k K t) := by
  classical
  ext h
  constructor
  · intro hh
    rcases Finset.mem_sdiff.mp hh with ⟨hj, hmajor⟩
    rw [Finset.mem_filter]
    refine ⟨hj, ?_⟩
    intro t ht
    apply hmajor
    rw [major_arc, Finset.mem_filter]
    exact ⟨hj, ⟨t, ht⟩⟩
  · intro hh
    rcases Finset.mem_filter.mp hh with ⟨hj, hmajor⟩
    refine Finset.mem_sdiff.mpr ⟨hj, ?_⟩
    intro hm
    rw [major_arc, Finset.mem_filter] at hm
    rcases hm with ⟨_, ⟨t, ht⟩⟩
    exact hmajor t ht

/-- Centred at `x`, width `2 * y`. -/
def integer_range (x y : ℝ) : Finset ℤ := Finset.Icc ⌈x - y⌉ ⌊x + y⌋

lemma mem_integer_range_iff {x y : ℝ} {z : ℤ} :
    z ∈ integer_range x y ↔ |x - z| ≤ y := by
  rw [integer_range, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hz1, hz2⟩
    constructor
    · have h1 : x - y ≤ (z : ℝ) := Int.ceil_le.mp hz1
      have h2 : (z : ℝ) ≤ x + y := Int.le_floor.mp hz2
      linarith
    · have h1 : x - y ≤ (z : ℝ) := Int.ceil_le.mp hz1
      have h2 : (z : ℝ) ≤ x + y := Int.le_floor.mp hz2
      linarith
  · rintro ⟨hz1, hz2⟩
    constructor
    · exact Int.ceil_le.mpr (by linarith)
    · exact Int.le_floor.mpr (by linarith)

lemma card_integer_range_le {x y : ℝ} (hy : 0 ≤ y) :
    ↑(integer_range x y).card ≤ 2 * y + 1 := by
  have hnonneg : 0 ≤ ⌊x + y⌋ + 1 - ⌈x - y⌉ :=
    sub_nonneg.mpr (Int.ceil_le.mpr (by
      have := Int.lt_floor_add_one (x + y); push_cast; linarith))
  calc
    ↑(integer_range x y).card = ((⌊x + y⌋ + 1 - ⌈x - y⌉ : ℤ) : ℝ) := by
      rw [integer_range, Int.card_Icc]
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    _ = (⌊x + y⌋ : ℝ) + 1 - ⌈x - y⌉ := by norm_num
    _ ≤ 2 * y + 1 := by
      have hfc : (⌊x + y⌋ : ℝ) - ⌈x - y⌉ ≤ y + y := by
        simpa using (floor_sub_ceil (z := x) (x := y) (y := y))
      linarith

def my_range (x : ℝ) : Finset ℤ := integer_range 0 x

lemma mem_my_range_iff {x : ℝ} {y : ℤ} :
    y ∈ my_range x ↔ |(y : ℝ)| ≤ x := by
  simpa [my_range] using (mem_integer_range_iff (x := 0) (y := x) (z := y))

def my_range' (A : Finset ℕ) (k : ℕ) (K : ℝ) : Finset ℤ :=
  my_range ((K / (2 * (k : ℝ)) + (lcmA A : ℝ) / 2) / |(lcmA A : ℝ) / k|)

def I (h : ℤ) (K : ℝ) (k : ℕ) : Finset ℤ := integer_range (h * k) (K / 2)

lemma mem_I' {h : ℤ} {K : ℝ} {k : ℕ} {z : ℤ} :
    z ∈ I h K k ↔ |(h * k : ℝ) - z| ≤ K / 2 := by
  simpa [I] using
    (mem_integer_range_iff (x := (h * k : ℝ)) (y := K / 2) (z := z))

lemma card_I_le {h K k} (hK : (0 : ℝ) ≤ K) : ↑(I h K k).card ≤ K + 1 := by
  calc
    ↑(I h K k).card ≤ 2 * (K / 2) + 1 := by
      simpa [I] using
        (card_integer_range_le (x := (h * k : ℝ)) (y := K / 2)
          (by exact div_nonneg hK (by positivity)))
    _ = K + 1 := by ring

/-- Def 4.5. -/
def minor_arc₁ (A : Finset ℕ) (k : ℕ) (K : ℝ) (δ : ℝ) : Finset ℤ :=
  (j A \ major_arc A k K).filter fun h =>
    δ ≤ (A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card

def minor_arc₂ (A : Finset ℕ) (k : ℕ) (K : ℝ) (δ : ℝ) : Finset ℤ :=
  (j A \ major_arc A k K) \ minor_arc₁ A k K δ

lemma major_arc_eq_union {A k K} (hA : 0 ∉ A) (hk : k ≠ 0) :
    major_arc A k K = (my_range' A k K).biUnion (major_arc_at A k K) := by
  classical
  ext h
  constructor
  · intro hh
    rw [major_arc, Finset.mem_filter] at hh
    rcases hh with ⟨hj, t, ht⟩
    rw [Finset.mem_biUnion]
    refine ⟨t, ?_, ht⟩
    rw [my_range', mem_my_range_iff]
    have hlcm0 : ((lcmA A : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.lcm_ne_zero_iff (s := A) (f := id)).2
        (by intro x hx hx0; exact hA (hx0 ▸ hx))
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast hk
    have hden : 0 < |(lcmA A : ℝ) / k| := by
      exact abs_pos.mpr (div_ne_zero hlcm0 hk0)
    have hvalid : |(h : ℝ)| ≤ (lcmA A : ℝ) / 2 := bound_of_mem_j A h hj
    have harc : |(h : ℝ) - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) :=
      (mem_major_arc_at h).mp ht |>.2
    have harc' : |(h : ℝ) - (t : ℝ) * ((lcmA A : ℝ) / k)| ≤ K / (2 * k) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using harc
    apply (le_div_iff₀ hden).2
    calc
      |(t : ℝ)| * |(lcmA A : ℝ) / k| = |(t : ℝ) * ((lcmA A : ℝ) / k)| := by
        rw [abs_mul]
      _ = |((t : ℝ) * ((lcmA A : ℝ) / k) - h) + h| := by
        congr 1
        ring
      _ ≤ |(t : ℝ) * ((lcmA A : ℝ) / k) - h| + |(h : ℝ)| := abs_add_le _ _
      _ = |(h : ℝ) - (t : ℝ) * ((lcmA A : ℝ) / k)| + |(h : ℝ)| := by
        rw [abs_sub_comm]
      _ ≤ K / (2 * k) + (lcmA A : ℝ) / 2 := add_le_add harc' hvalid
  · intro hh
    rw [Finset.mem_biUnion] at hh
    rcases hh with ⟨t, -, ht⟩
    rw [major_arc, Finset.mem_filter]
    exact ⟨(mem_major_arc_at h).mp ht |>.1, ⟨t, ht⟩⟩

lemma minor_arc₂_eq {A k K δ} :
    minor_arc₂ A k K δ =
      ((j A \ major_arc A k K).filter fun h =>
        ↑(A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card < δ) := by
  ext h
  constructor
  · intro hh
    rw [minor_arc₂, Finset.mem_sdiff] at hh
    rcases hh with ⟨hs, hnot⟩
    rw [Finset.mem_filter]
    refine ⟨hs, ?_⟩
    by_contra hge
    apply hnot
    rw [minor_arc₁, Finset.mem_filter]
    exact ⟨hs, le_of_not_gt hge⟩
  · intro hh
    rw [Finset.mem_filter] at hh
    rcases hh with ⟨hs, hlt⟩
    rw [minor_arc₂, Finset.mem_sdiff]
    refine ⟨hs, ?_⟩
    intro hm
    rw [minor_arc₁, Finset.mem_filter] at hm
    exact (not_le.mpr hlt) hm.2

lemma e_eq_one_iff (x : ℝ) :
    e x = 1 ↔ ∃ z : ℤ, x = z := by
  constructor
  · intro hx
    unfold e AdditiveCharacterGeometricSums.additiveCharacter at hx
    obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp hx
    refine ⟨z, ?_⟩
    have hxz : (x : ℂ) = z := by
      apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
      linear_combination hz
    simpa using congrArg Complex.re hxz
  · rintro ⟨z, rfl⟩
    simpa using e_int z

lemma one_add_e (x : ℝ) : 1 + e x = 2 * e (x / 2) * cos (π * x) := by
  have hzero : e (-x / 2) * e (x / 2) = 1 := by
    calc
      e (-x / 2) * e (x / 2) = e 0 := by
        simpa [show -x / 2 + x / 2 = 0 by ring] using
          (e_add (x := -x / 2) (y := x / 2)).symm
      _ = 1 := by
        simpa [e, AdditiveCharacterGeometricSums.additiveCharacter] using Complex.exp_zero
  have hsplit : e x = e (x / 2) * e (x / 2) := by
    simpa [show x / 2 + x / 2 = x by ring] using
      (e_add (x := x / 2) (y := x / 2))
  have hhalf : e (x / 2) = Complex.exp ((x * π) * Complex.I) := by
    simp [e, AdditiveCharacterGeometricSums.additiveCharacter, mul_left_comm, mul_comm, two_mul]
  have hnegHalf : e (-x / 2) = Complex.exp (-(x * π) * Complex.I) := by
    simp [e, AdditiveCharacterGeometricSums.additiveCharacter, mul_left_comm, mul_comm, two_mul]
  calc
    1 + e x = e (-x / 2) * e (x / 2) + e (x / 2) * e (x / 2) := by
      rw [hzero, hsplit]
    _ = e (x / 2) * (e (-x / 2) + e (x / 2)) := by ring
    _ = e (x / 2) *
        (Complex.exp (-(x * π) * Complex.I) + Complex.exp ((x * π) * Complex.I)) := by
      congr 1
      rw [hnegHalf, hhalf]
    _ = e (x / 2) * (2 * cos (π * x)) := by
      congr 1
      simpa [Complex.ofReal_cos, mul_comm, add_comm] using
        (Complex.two_cos (x * π : ℂ)).symm
    _ = 2 * e (x / 2) * cos (π * x) := by ring

lemma abs_one_add_e (x : ℝ) :
    ‖1 + e x‖ = 2 * |cos (π * x)| := by
  rw [one_add_e]
  rw [norm_mul, norm_mul,
    (show ‖e (x / 2)‖ = 1 by
      simpa [e, AdditiveCharacterGeometricSums.additiveCharacter, mul_assoc, mul_left_comm,
        mul_comm] using Complex.norm_exp_ofReal_mul_I ((x / 2) * (2 * Real.pi)))]
  norm_num
  simpa [Complex.ofReal_cos] using
    (RCLike.norm_ofReal (K := ℂ) (r := Real.cos (π * x)))

/-- Lemma 4.6. Note `r` in this statement is different to the `r` in the written proof. -/
lemma orthogonality {n m : ℕ} {r s : ℤ} (hm : m ≠ 0) {I : Finset ℤ}
    (hI : I = Finset.Ioc r s) (hrs₁ : r < s) (hrs₂ : I.card = m) :
    I.sum (fun h => e (h * n / m)) * (1 / m) = if m ∣ n then (1 : ℂ) else 0 := by
  classical
  have _ : r < s := hrs₁
  have hmℝ : (m : ℝ) ≠ 0 := by
    exact_mod_cast hm
  have hmℂ : (m : ℂ) ≠ 0 := by
    exact_mod_cast hm
  have hcardI : I.card = (s - r).toNat := by
    rw [hI, Int.card_Ioc]
  have hcard : (s - r).toNat = m := hcardI.symm.trans hrs₂
  by_cases hmn : m ∣ n
  · obtain ⟨k, rfl⟩ := hmn
    rw [ite_eq_left (dvd_mul_right m k)]
    have hterm : ∀ h : ℤ, e (h * (((m * k : ℕ) : ℝ)) / m) = 1 := by
      intro h
      calc
        e (h * (((m * k : ℕ) : ℝ)) / m) = e ((h : ℝ) * k) := by
          congr 1
          field_simp [hmℝ]
          rw [Nat.cast_mul]
          ring
        _ = e (h * k : ℤ) := by
          congr 1
          push_cast
          rfl
        _ = 1 := e_int (h * k)
    have hsum : I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) = m := by
      calc
        I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) = I.sum (fun _ => (1 : ℂ)) := by
          apply Finset.sum_congr rfl
          intro h hh
          exact hterm h
        _ = m := by simp [hrs₂]
    calc
      I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) * (1 / m) = (m : ℂ) * (1 / m) := by
        rw [hsum]
      _ = 1 := by simp [one_div, hmℂ]
  · rw [ite_eq_right hmn]
    let x : ℝ := (n : ℝ) / m
    let ξ : ℂ := e x
    have hpow : ∀ i : ℕ, e ((i : ℝ) * x) = ξ ^ i := by
      intro i
      induction i with
      | zero =>
          simpa [ξ, e, AdditiveCharacterGeometricSums.additiveCharacter] using Complex.exp_zero
      | succ i ih =>
          calc
            e (((i + 1 : ℕ) : ℝ) * x) = e (x + (i : ℝ) * x) := by
              congr 1
              rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
            _ = e x * e ((i : ℝ) * x) := e_add
            _ = ξ * ξ ^ i := by simp [ξ, ih]
            _ = ξ ^ (i + 1) := by rw [pow_succ, mul_comm]
    have hξm : ξ ^ m = 1 := by
      rw [← hpow m]
      dsimp [x]
      rw [show (m : ℝ) * ((n : ℝ) / m) = n by
        field_simp [hmℝ]]
      simpa [e, AdditiveCharacterGeometricSums.additiveCharacter, mul_assoc, mul_left_comm,
        mul_comm] using Complex.exp_nat_mul_two_pi_mul_I n
    have hξ_ne : ξ ≠ 1 := by
      intro hξ
      apply hmn
      obtain ⟨z, hz⟩ := (e_eq_one_iff x).mp (by simpa [ξ] using hξ)
      have hnz : (n : ℝ) = z * m := by
        calc
          (n : ℝ) = x * m := by
            dsimp [x]
            field_simp [hmℝ]
          _ = z * m := by rw [hz]
      have hnz' : (n : ℤ) = z * m := by
        exact_mod_cast hnz
      exact Int.natCast_dvd_natCast.mp ⟨z, by simpa [mul_comm] using hnz'⟩
    have hsum :
        I.sum (fun h => e (h * n / m)) =
          e ((((r + 1 : ℤ) : ℝ) * n / m)) * ∑ i ∈ range m, ξ ^ i := by
      rw [hI, Int.Ioc_eq_finset_map, Finset.sum_map]
      simp_rw [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
      rw [hcard]
      have hsplit :
          ∑ i ∈ range m, e (((r + 1 + (i : ℤ) : ℤ) * n / m)) =
            ∑ i ∈ range m, e ((((r + 1 : ℤ) : ℝ) * n / m)) * ξ ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        have harg :
            (((r + 1 + (i : ℤ) : ℤ) : ℝ) * n / m) =
              (((r + 1 : ℤ) : ℝ) * n / m) + (i : ℝ) * x := by
          dsimp [x]
          push_cast
          ring
        rw [harg, e_add, hpow i]
      rw [hsplit, ← Finset.mul_sum]
    have hgeom0 : ∑ i ∈ range m, ξ ^ i = 0 := by
      have hmul : (∑ i ∈ range m, ξ ^ i) * (ξ - 1) = 0 := by
        simpa [hξm] using (geom_sum_mul ξ m)
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hξ_ne)
    calc
      I.sum (fun h => e (h * n / m)) * (1 / m) =
          (e ((((r + 1 : ℤ) : ℝ) * n / m)) * ∑ i ∈ range m, ξ ^ i) * (1 / m) := by
            rw [hsum]
      _ = 0 := by simp [hgeom0]

theorem Nat.lcm_smallest {a b d : ℕ} (hda : a ∣ d) (hdb : b ∣ d)
    (hd : ∀ e : ℕ, a ∣ e → b ∣ e → d ∣ e) : d = a.lcm b := by
  apply Nat.dvd_antisymm
  · exact hd _ (Nat.dvd_lcm_left a b) (Nat.dvd_lcm_right a b)
  · exact Nat.lcm_dvd hda hdb

lemma Finset.support_sup {α β : Type*} {f : α → β →₀ ℕ} (s : Finset α) :
    (s.sup f).support = s.biUnion (fun a => (f a).support) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sup_empty, Finset.biUnion_empty, bot_eq_zero]
    simp
  · intro a s _ ih
    rw [Finset.sup_insert, Finsupp.support_sup, ih, Finset.biUnion_insert]

lemma smooth_lcm_aux {X : ℕ} {A : Finset ℕ} (hX₀ : X ≠ 0)
    (hX : ∀ q ∈ ppowers_in_set A, q ≤ X) (hA : 0 ∉ A) :
    lcmA A ≤ X ^ Nat.primeCounting X := by
  have hlcm0 : lcmA A ≠ 0 := (Finset.lcm_ne_zero_iff (s := A) (f := id)).2
    (by intro x hx hx0; exact hA (hx0 ▸ hx))
  have hprimecount : ((Finset.Icc 1 X).filter Nat.Prime).card = Nat.primeCounting X := by
    simpa [Nat.primeCounting] using (prime_counting_eq_card_primes (x := X)).symm
  have hpow_mem :
      ∀ p ∈ (lcmA A).primeFactors, p ^ (lcmA A).factorization p ∈ ppowers_in_set A := by
    intro p hp
    have hp' : p ∈ (lcmA A).factorization.support := by
      simpa [Nat.support_factorization] using hp
    have hfac0 : (lcmA A).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfac :
        (lcmA A).factorization p = A.sup (fun a => a.factorization p) := by
      exact Finset.factorization_lcm (f := id) (s := A)
        (by intro k hk hk0; exact hA (hk0 ▸ hk)) p
    have hAne : A.Nonempty := by
      by_contra hAempty
      rw [Finset.not_nonempty_iff_eq_empty] at hAempty
      simp [hAempty] at hp
    rcases Finset.exists_mem_eq_sup A hAne (fun a => a.factorization p) with ⟨a, haA, hsup⟩
    refine (mem_ppowers_in_set' hpprime hfac0).2 ⟨a, haA, ?_⟩
    rw [← hsup, ← hfac]
  have hcard :
      (lcmA A).primeFactors.card ≤ Nat.primeCounting X := by
    have hsubset : (lcmA A).primeFactors ⊆ (Finset.Icc 1 X).filter Nat.Prime := by
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp' : p ∈ (lcmA A).factorization.support := by
        simpa [Nat.support_factorization] using hp
      have hfac0 : (lcmA A).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
      have hpow_le : p ^ (lcmA A).factorization p ≤ X := hX _ (hpow_mem p hp)
      have hp_le : p ≤ X := (Nat.le_self_pow hfac0 p).trans hpow_le
      exact Finset.mem_filter.mpr ⟨by simp [hpprime.one_le, hp_le], hpprime⟩
    rw [← hprimecount]
    exact Finset.card_le_card hsubset
  calc
    lcmA A = (lcmA A).primeFactors.prod (fun p => p ^ (lcmA A).factorization p) := by
      symm
      exact Nat.prod_factorization_pow_eq_self hlcm0
    _ ≤ (lcmA A).primeFactors.prod (fun _ => X) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        exact hX (p ^ (lcmA A).factorization p) (hpow_mem p hp)
    _ = X ^ (lcmA A).primeFactors.card := by simp
    _ ≤ X ^ Nat.primeCounting X := by
      exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hX₀) hcard

/-- Lemma 4.8. -/
lemma smooth_lcm :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 ≤ X →
      ∀ A : Finset ℕ, 0 ∉ A → (∀ q ∈ ppowers_in_set A, ↑q ≤ X) →
        ↑(lcmA A) ≤ exp (C * X) := by
  obtain ⟨c, hc, hprime⟩ := prime_counting_le_const_mul_div_log
  refine ⟨c, hc, ?_⟩
  intro X hX₀ A hA hAX
  by_cases hX : X ≤ 1
  · have hppow : ppowers_in_set A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hqX : (q : ℝ) ≤ 1 := (hAX q hq).trans hX
      rw [mem_ppowers_in_set] at hq
      have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.1.one_lt
      exact not_le_of_gt hq1 hqX
    have hlcm : lcmA A = 1 := by
      simpa [lcmA] using ppowers_in_set_eq_empty' hppow hA
    rw [hlcm, Nat.cast_one]
    simpa using Real.one_le_exp (mul_nonneg hc.le hX₀)
  · have hX' : 1 < X := lt_of_not_ge hX
    have hfloor0 : ⌊X⌋₊ ≠ 0 := by
      simp [Nat.floor_eq_zero, not_lt, hX'.le]
    refine
      (Nat.cast_le.2
        (smooth_lcm_aux hfloor0 (fun q hq ↦ Nat.le_floor (hAX q hq)) hA)).trans ?_
    simp only [Nat.cast_pow]
    refine (pow_le_pow_left₀ (by positivity) (Nat.floor_le hX₀) _).trans ?_
    have hdiv_nonneg : 0 ≤ X / Real.log X := by
      exact div_nonneg hX₀ (Real.log_nonneg hX'.le)
    have hX₁ : (Nat.primeCounting ⌊X⌋₊ : ℝ) ≤ c * (X / Real.log X) := by
      simpa [Real.norm_of_nonneg hdiv_nonneg] using hprime X
    have hpowpos : 0 < X ^ Nat.primeCounting ⌊X⌋₊ := by
      exact pow_pos (zero_lt_one.trans hX') _
    rwa [← Real.log_le_iff_le_exp hpowpos, ← Real.rpow_natCast,
      Real.log_rpow (zero_lt_one.trans hX'), ← _root_.le_div_iff₀ (Real.log_pos hX'),
      mul_div_assoc]

lemma jordan_apply {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : 2 * x ≤ sin (π * x) := by
  have hπx_nonneg : 0 ≤ π * x := mul_nonneg Real.pi_pos.le hx
  have hπx_le : π * x ≤ π / 2 := by
    nlinarith [hx', Real.pi_pos]
  simpa [div_eq_mul_inv, mul_assoc, Real.pi_ne_zero] using
    (Real.mul_le_sin (x := π * x) hπx_nonneg hπx_le)

/-- Lemma 4.9. -/
lemma cos_bound {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    |cos (π * x)| ≤ exp (-(2 * x ^ 2)) := by
  have hcos_nonneg : 0 ≤ cos (π * x) := by
    refine Real.cos_nonneg_of_mem_Icc ?_
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [hx', Real.pi_pos]
  rw [abs_of_nonneg hcos_nonneg]
  have hπx : |π * x| ≤ π := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hx)]
    nlinarith [hx', Real.pi_pos]
  have hcos :
      cos (π * x) ≤ 1 - 2 * x ^ 2 := by
    calc
      cos (π * x) ≤ 1 - 2 / π ^ 2 * (π * x) ^ 2 := Real.cos_le_one_sub_mul_cos_sq hπx
      _ = 1 - 2 * x ^ 2 := by
        field_simp [pow_two, Real.pi_ne_zero]
  have hexp : 1 - 2 * x ^ 2 ≤ exp (-(2 * x ^ 2)) := by
    simpa using Real.one_sub_le_exp_neg (2 * x ^ 2)
  exact hcos.trans hexp

lemma cos_bound_abs {x : ℝ} (hx' : |x| ≤ 1 / 2) :
    |cos (π * x)| ≤ exp (-(2 * x ^ 2)) := by
  rcases le_or_gt 0 x with hx | hx
  · exact cos_bound hx (by simpa [abs_of_nonneg hx] using hx')
  · have hxneg : 0 ≤ -x := by linarith
    have hxneg' : -x ≤ 1 / 2 := by
      have hxabs : |-x| ≤ 1 / 2 := by simpa [abs_neg] using hx'
      simpa [abs_of_nonneg hxneg] using hxabs
    have h := cos_bound hxneg hxneg'
    simpa [neg_mul, Real.cos_neg, pow_two] using h
