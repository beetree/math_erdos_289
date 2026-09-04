import Erdos289.External
import Erdos289.ExternalBridge
import Erdos289.ErdosTuran

set_option maxHeartbeats 1000000

/-!
# Equidistribution of modular inverses (Lemma 1, part B)

This file proves `equidist_inverse'`, the "uniform discrepancy justification" paragraph of
Section 2 of `erdos_289_full_proof.pdf` (lines 135-148), from the two external inputs
`Erdos289.bourgain_garaev` and `Erdos289.erdos_turan_weak`.

The definitions `rOf'` / `invCand'` are verbatim copies of `Erdos289.rOf` / `Erdos289.invCand`
(now in `Erdos289/Lemma1Basic.lean`); those files are not imported here, to keep the two
developments independent, so the names differ only by the prime.  Everything except the two
definitions and the final theorem lives in the auxiliary namespace `Erdos289.EquidistAux`,
to avoid clashes with the parallel developments in `Erdos289/Lemma1Equidist{B,C}.lean`.
-/

namespace Erdos289
namespace Equidist

open Finset Filter Topology
open scoped BigOperators

/-- The companion `r`-value for `t` at modulus `U`: the canonical representative in `[0, U)`
of `t⁻¹ mod U`.  (Copy of `Erdos289.rOf`.) -/
def rOf' (U t : ℕ) : ℕ := ((t : ZMod U)⁻¹).val

/-- The set of `t` in `(T₁, T₂]`, coprime to `U`, whose inverse mod `U` lands in the residue
interval `[α, α+ℓ)`.  (Copy of `Erdos289.invCand`.) -/
def invCand' (U T₁ T₂ α ℓ : ℕ) : Finset ℕ :=
  (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U ∧ rOf' U t ∈ Finset.Ico α (α + ℓ))

namespace EquidistAux

/-! ## Basic facts about the additive character `e` -/

/-- The additive character has modulus one. -/
theorem norm_e (m : ℕ) (x : ℤ) : ‖e m x‖ = 1 := by
  have h : e m x = Complex.exp (((2 * Real.pi * x / m : ℝ) : ℂ) * Complex.I) := by
    unfold e
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- `e m` only depends on its argument modulo `m`. -/
theorem e_modEq (m : ℕ) {x y : ℤ} (h : (m : ℤ) ∣ y - x) : e m x = e m y := by
  obtain ⟨k, hk⟩ := h
  have hy : y = x + (m : ℤ) * k := by linarith
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero, zero_mul, add_zero] at hy
    rw [hy]
  · have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    unfold e
    rw [hy]
    have hsplit : (2 * (Real.pi : ℂ) * Complex.I * ((x + (m : ℤ) * k : ℤ) : ℂ) / (m : ℕ))
        = 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) / (m : ℕ)
            + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Reduction of the modulus: if `U = g * m` and `h = g * b`, then `e_U(h x) = e_m(b x)`. -/
theorem e_reduce {U g m : ℕ} (hg : 0 < g) (hm : 0 < m) (hU : U = g * m)
    {h b : ℕ} (hh : h = g * b) (x : ℤ) : e U ((h : ℤ) * x) = e m ((b : ℤ) * x) := by
  subst hU; subst hh
  unfold e
  congr 1
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  field_simp

/-! ## Basic facts about inverses in `ZMod` -/

/-- Inverses of units in `ZMod n` are multiplicative. -/
theorem zmod_mul_inv {n : ℕ} {a b : ZMod n} (ha : IsUnit a) (hb : IsUnit b) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  refine ZMod.inv_eq_of_mul_eq_one n _ _ ?_
  calc (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
    _ = 1 := by rw [ZMod.mul_inv_of_unit a ha, ZMod.mul_inv_of_unit b hb, one_mul]

/-- The natural-number representative `rOf' U t` really does represent `t⁻¹` in `ZMod U`. -/
theorem rOf'_cast (U t : ℕ) [NeZero U] : ((rOf' U t : ℕ) : ZMod U) = ((t : ℕ) : ZMod U)⁻¹ := by
  simp [rOf']

/-- The inverse modulo `U` reduces to the inverse modulo any divisor `m` of `U`. -/
theorem inv_reduce {U m t : ℕ} (hm : 0 < m) (hdvd : m ∣ U) (hcop : Nat.Coprime t U) :
    ((rOf' U t : ℕ) : ZMod m) = ((t : ℕ) : ZMod m)⁻¹ := by
  have : NeZero m := ⟨hm.ne'⟩
  have hval : ((rOf' U t * t : ℕ) : ZMod U) = ((1 : ℕ) : ZMod U) := by
    push_cast
    exact ZMod.val_inv_mul hcop
  have hmod : rOf' U t * t ≡ 1 [MOD U] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hval
  have hmod' : rOf' U t * t ≡ 1 [MOD m] := hmod.of_dvd hdvd
  have hval' : ((rOf' U t * t : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod'
  push_cast at hval'
  refine (ZMod.inv_eq_of_mul_eq_one m _ _ ?_).symm
  rw [mul_comm]
  exact hval'

/-- Consequently `rOf' U t` and `rOf' m t` agree modulo `m`, for `m ∣ U`. -/
theorem rOf'_dvd_sub {U m t : ℕ} (hm : 0 < m) (hdvd : m ∣ U) (hcop : Nat.Coprime t U) :
    (m : ℤ) ∣ (rOf' m t : ℤ) - (rOf' U t : ℤ) := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [rOf'_cast m t, inv_reduce hm hdvd hcop, sub_self]

/-! ## Counting integers coprime to `U` in an interval -/

/-- Coprimality to `U` is exactly avoidance of all prime factors of `U`. -/
theorem coprime_iff_forall_primeFactors {t U : ℕ} (hU : U ≠ 0) :
    Nat.Coprime t U ↔ ∀ P ∈ U.primeFactors, ¬ P ∣ t := by
  constructor
  · intro hcop P hP hdvd
    exact Nat.Prime.not_coprime_iff_dvd.2
      ⟨P, Nat.prime_of_mem_primeFactors hP, hdvd, Nat.dvd_of_mem_primeFactors hP⟩ hcop
  · intro h
    by_contra hcop
    obtain ⟨P, hP, hPt, hPU⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcop
    exact h P (Nat.mem_primeFactors.2 ⟨hP, hPU, hU⟩) hPt

/-- The number of multiples of `A` in `(T₁, T₂]`, as a difference of two quotients. -/
theorem card_multiples_Ioc (A T₁ T₂ : ℕ) (hT : T₁ ≤ T₂) :
    ((Finset.Ioc T₁ T₂).filter (fun t => A ∣ t)).card + T₁ / A = T₂ / A := by
  have hsplit : Finset.Ioc 0 T₁ ∪ Finset.Ioc T₁ T₂ = Finset.Ioc 0 T₂ :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hT
  have hdisj : Disjoint ((Finset.Ioc 0 T₁).filter (fun t => A ∣ t))
      ((Finset.Ioc T₁ T₂).filter (fun t => A ∣ t)) :=
    Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le (le_refl T₁))
  have h := congrArg (fun s : Finset ℕ => (s.filter (fun t => A ∣ t)).card) hsplit
  simp only [Finset.filter_union] at h
  rw [Finset.card_union_of_disjoint hdisj, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at h
  omega

/-- The number of multiples of `A` in `(T₁, T₂]` is within `1` of `(T₂ - T₁)/A`. -/
theorem card_multiples_approx (A T₁ T₂ : ℕ) (hA : 0 < A) (hT : T₁ ≤ T₂) :
    |((((Finset.Ioc T₁ T₂).filter (fun t => A ∣ t)).card : ℝ)) - ((T₂ - T₁ : ℕ) : ℝ) / A| ≤ 1 := by
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hkey := card_multiples_Ioc A T₁ T₂ hT
  have e1 : (A : ℝ) * ((T₁ / A : ℕ) : ℝ) + ((T₁ % A : ℕ) : ℝ) = (T₁ : ℝ) := by
    have := Nat.div_add_mod T₁ A
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
  have e2 : (A : ℝ) * ((T₂ / A : ℕ) : ℝ) + ((T₂ % A : ℕ) : ℝ) = (T₂ : ℝ) := by
    have := Nat.div_add_mod T₂ A
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
  have hcR : ((((Finset.Ioc T₁ T₂).filter (fun t => A ∣ t)).card : ℝ)) + ((T₁ / A : ℕ) : ℝ)
      = ((T₂ / A : ℕ) : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hkey
  have hsub : ((T₂ - T₁ : ℕ) : ℝ) = (T₂ : ℝ) - (T₁ : ℝ) := by
    rw [Nat.cast_sub hT]
  have hm1 : ((T₁ % A : ℕ) : ℝ) < (A : ℝ) := by exact_mod_cast Nat.mod_lt _ hA
  have hm2 : ((T₂ % A : ℕ) : ℝ) < (A : ℝ) := by exact_mod_cast Nat.mod_lt _ hA
  have hm1' : (0 : ℝ) ≤ ((T₁ % A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm2' : (0 : ℝ) ≤ ((T₂ % A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrw : ((((Finset.Ioc T₁ T₂).filter (fun t => A ∣ t)).card : ℝ)) - ((T₂ - T₁ : ℕ) : ℝ) / A
      = (((T₁ % A : ℕ) : ℝ) - ((T₂ % A : ℕ) : ℝ)) / A := by
    rw [hsub]
    field_simp
    nlinarith [e1, e2, hcR]
  rw [hrw, abs_div, abs_of_pos hAR, div_le_one hAR, abs_le]
  constructor <;> linarith

/-- The count of `t ∈ (T₁, T₂]` coprime to `U` is within an absolute constant of
`φ(U)/U · (T₂ - T₁)`, provided `U` has at most two prime factors. -/
theorem coprime_count_approx {U : ℕ} (hU : 0 < U) (hcard : U.primeFactors.card ≤ 2)
    {T₁ T₂ : ℕ} (hT : T₁ ≤ T₂) :
    |((((Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)).card : ℝ))
      - (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ)| ≤ 3 := by
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have hSc : ((Finset.Ioc T₁ T₂).card : ℝ) = ((T₂ - T₁ : ℕ) : ℝ) := by
    rw [Nat.card_Ioc]
  have hcases : U.primeFactors.card = 0 ∨ U.primeFactors.card = 1 ∨ U.primeFactors.card = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · -- `U = 1`
    have : U = 0 ∨ U = 1 := Nat.primeFactors_eq_empty.1 (Finset.card_eq_zero.1 h0)
    have hU1 : U = 1 := by omega
    subst hU1
    simp only [Nat.coprime_one_right_eq_true, Finset.filter_true_of_mem, implies_true,
      Nat.totient_one, Nat.cast_one, div_one, one_mul]
    rw [hSc, sub_self, abs_zero]
    norm_num
  · -- one prime factor
    obtain ⟨P, hpf⟩ := Finset.card_eq_one.1 h1
    have hPmem : P ∈ U.primeFactors := by rw [hpf]; exact Finset.mem_singleton_self P
    have hP : P.Prime := Nat.prime_of_mem_primeFactors hPmem
    have hP1 : 1 ≤ P := hP.one_lt.le
    have hPpos : 0 < P := hP.pos
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
    have htot : Nat.totient U * P = U * (P - 1) := by
      have h := Nat.totient_mul_prod_primeFactors U
      rw [hpf] at h
      simpa using h
    have htotR : (Nat.totient U : ℝ) * (P : ℝ) = (U : ℝ) * ((P : ℝ) - 1) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) htot
      push_cast [Nat.cast_sub hP1] at h
      exact h
    have hdens : (Nat.totient U : ℝ) / (U : ℝ) = ((P : ℝ) - 1) / (P : ℝ) := by
      rw [div_eq_div_iff hU0.ne' hPR.ne']
      linarith
    have hfe : (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)
        = (Finset.Ioc T₁ T₂).filter (fun t => ¬ P ∣ t) := by
      apply Finset.filter_congr
      intro t _
      rw [coprime_iff_forall_primeFactors hU.ne', hpf]
      simp
    have hcardF : (((Finset.Ioc T₁ T₂).filter (fun t => ¬ P ∣ t)).card : ℝ)
        + (((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t)).card : ℝ) = ((T₂ - T₁ : ℕ) : ℝ) := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      have hle : ((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t)).card ≤ (Finset.Ioc T₁ T₂).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rw [Nat.cast_sub hle, hSc]
      ring
    have happrox := card_multiples_approx P T₁ T₂ hPpos hT
    rw [hfe, hdens]
    rw [abs_le] at happrox ⊢
    have hfield : ((P : ℝ) - 1) / (P : ℝ) * ((T₂ - T₁ : ℕ) : ℝ)
        = ((T₂ - T₁ : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / (P : ℝ) := by
      field_simp
    rw [hfield]
    constructor <;> linarith [happrox.1, happrox.2, hcardF]
  · -- two prime factors
    obtain ⟨P, Q, hPQ, hpf⟩ := Finset.card_eq_two.1 h2
    have hPmem : P ∈ U.primeFactors := by rw [hpf]; simp
    have hQmem : Q ∈ U.primeFactors := by rw [hpf]; simp
    have hP : P.Prime := Nat.prime_of_mem_primeFactors hPmem
    have hQ : Q.Prime := Nat.prime_of_mem_primeFactors hQmem
    have hPpos : 0 < P := hP.pos
    have hQpos : 0 < Q := hQ.pos
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
    have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
    have hcopPQ : Nat.Coprime P Q := (Nat.coprime_primes hP hQ).2 hPQ
    have htot : Nat.totient U * (P * Q) = U * ((P - 1) * (Q - 1)) := by
      have h := Nat.totient_mul_prod_primeFactors U
      rw [hpf, Finset.prod_pair hPQ, Finset.prod_pair hPQ] at h
      exact h
    have htotR : (Nat.totient U : ℝ) * ((P : ℝ) * (Q : ℝ))
        = (U : ℝ) * (((P : ℝ) - 1) * ((Q : ℝ) - 1)) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) htot
      push_cast [Nat.cast_sub hP.one_lt.le, Nat.cast_sub hQ.one_lt.le] at h
      exact h
    have hdens : (Nat.totient U : ℝ) / (U : ℝ)
        = (((P : ℝ) - 1) * ((Q : ℝ) - 1)) / ((P : ℝ) * (Q : ℝ)) := by
      rw [div_eq_div_iff hU0.ne' (by positivity)]
      linarith
    have hfe : (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)
        = (Finset.Ioc T₁ T₂).filter (fun t => ¬ (P ∣ t ∨ Q ∣ t)) := by
      apply Finset.filter_congr
      intro t _
      rw [coprime_iff_forall_primeFactors hU.ne', hpf]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro h; exact ⟨h P (Or.inl rfl), h Q (Or.inr rfl)⟩
      · rintro ⟨h1, h2⟩ x (rfl | rfl) <;> assumption
    have hinter : ((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t))
        ∩ ((Finset.Ioc T₁ T₂).filter (fun t => Q ∣ t))
        = (Finset.Ioc T₁ T₂).filter (fun t => P * Q ∣ t) := by
      rw [← Finset.filter_and]
      apply Finset.filter_congr
      intro t _
      constructor
      · rintro ⟨h1, h2⟩; exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopPQ h1 h2
      · intro h; exact ⟨dvd_trans (Dvd.intro Q rfl) h, dvd_trans (Dvd.intro_left P rfl) h⟩
    have hunion : ((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t ∨ Q ∣ t)).card
        + ((Finset.Ioc T₁ T₂).filter (fun t => P * Q ∣ t)).card
        = ((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t)).card
          + ((Finset.Ioc T₁ T₂).filter (fun t => Q ∣ t)).card := by
      rw [Finset.filter_or, ← hinter]
      exact Finset.card_union_add_card_inter _ _
    have hcardF : (((Finset.Ioc T₁ T₂).filter (fun t => ¬ (P ∣ t ∨ Q ∣ t))).card : ℝ)
        + (((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t ∨ Q ∣ t)).card : ℝ)
        = ((T₂ - T₁ : ℕ) : ℝ) := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      have hle : ((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t ∨ Q ∣ t)).card
          ≤ (Finset.Ioc T₁ T₂).card := Finset.card_le_card (Finset.filter_subset _ _)
      rw [Nat.cast_sub hle, hSc]
      ring
    have hunionR : (((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t ∨ Q ∣ t)).card : ℝ)
        + (((Finset.Ioc T₁ T₂).filter (fun t => P * Q ∣ t)).card : ℝ)
        = (((Finset.Ioc T₁ T₂).filter (fun t => P ∣ t)).card : ℝ)
          + (((Finset.Ioc T₁ T₂).filter (fun t => Q ∣ t)).card : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hunion
    have hAP := card_multiples_approx P T₁ T₂ hPpos hT
    have hAQ := card_multiples_approx Q T₁ T₂ hQpos hT
    have hAPQ := card_multiples_approx (P * Q) T₁ T₂ (Nat.mul_pos hPpos hQpos) hT
    rw [hfe, hdens]
    rw [abs_le] at hAP hAQ hAPQ ⊢
    have hfield : (((P : ℝ) - 1) * ((Q : ℝ) - 1)) / ((P : ℝ) * (Q : ℝ)) * ((T₂ - T₁ : ℕ) : ℝ)
        = ((T₂ - T₁ : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / (P : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / (Q : ℝ)
          + ((T₂ - T₁ : ℕ) : ℝ) / ((P : ℝ) * (Q : ℝ)) := by
      field_simp
      ring
    have hPQcast : (((P * Q : ℕ)) : ℝ) = (P : ℝ) * (Q : ℝ) := by push_cast; ring
    rw [hPQcast] at hAPQ
    rw [hfield]
    constructor <;> linarith [hAP.1, hAP.2, hAQ.1, hAQ.2, hAPQ.1, hAPQ.2, hcardF, hunionR]

/-! ## Kloosterman prefix sums and the Bourgain-Garaev bound -/

/-- The short Kloosterman-type prefix sum appearing in `bourgain_garaev`. -/
noncomputable def kloos (m b T : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 T).filter (fun n => Nat.Coprime n m), e m (b * ((n : ZMod m)⁻¹).val)

theorem kloos_eq (m b T : ℕ) :
    kloos m b T = ∑ n ∈ (Finset.Icc 1 T).filter (fun n => Nat.Coprime n m),
      e m ((b : ℤ) * ((rOf' m n : ℕ) : ℤ)) := rfl

/-- Two integers with the same residue give the same value of the additive character. -/
theorem e_eq_of_zmod {m : ℕ} (hm : 0 < m) {x y : ℤ} (h : ((x : ZMod m)) = ((y : ZMod m))) :
    e m x = e m y := by
  have : NeZero m := ⟨hm.ne'⟩
  refine e_modEq m ?_
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h, sub_self]

/-- The trivial bound on a Kloosterman prefix sum, together with `bourgain_garaev`: the
prefix sums of length `T < m` are `δ T + m ^ c`, the second term covering the short
prefixes `T ≤ m ^ c` to which Bourgain-Garaev does not apply. -/
theorem prefix_bound {c δ : ℝ} {m : ℕ}
    (hBG : ∀ N : ℕ, (m : ℝ) ^ c < (N : ℝ) → (N : ℝ) < (m : ℝ) → ∀ a : ℕ, Nat.Coprime a m →
        ‖kloos m a N‖ ≤ δ * (N : ℝ))
    {T : ℕ} (hT : (T : ℝ) < (m : ℝ)) {b : ℕ} (hb : Nat.Coprime b m) (hδ : 0 ≤ δ) :
    ‖kloos m b T‖ ≤ δ * (T : ℝ) + (m : ℝ) ^ c := by
  have hmc : (0 : ℝ) ≤ (m : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hcase : (m : ℝ) ^ c < (T : ℝ)
  · have := hBG T hcase hT b hb
    linarith
  · push Not at hcase
    have htriv : ‖kloos m b T‖ ≤ (T : ℝ) := by
      calc ‖kloos m b T‖
          ≤ ∑ n ∈ (Finset.Icc 1 T).filter (fun n => Nat.Coprime n m),
              ‖e m (b * ((n : ZMod m)⁻¹).val)‖ := norm_sum_le _ _
        _ = (((Finset.Icc 1 T).filter (fun n => Nat.Coprime n m)).card : ℝ) := by
              simp [norm_e]
        _ ≤ ((Finset.Icc 1 T).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = (T : ℝ) := by rw [Nat.card_Icc]; simp
    have : (0 : ℝ) ≤ δ * (T : ℝ) := by positivity
    linarith

/-! ## Reducing the modulus in the exponential sum -/

/-- Replacing the modulus `U` by `m = U / (h, U)` and the frequency `h` by `b = h / (h, U)`
in the sum of `e_U(h t⁻¹)` over any set of `t` coprime to `U`. -/
theorem sum_reduce {U g m h b : ℕ} (hg : 0 < g) (hm : 0 < m) (hU : U = g * m) (hh : h = g * b)
    (S : Finset ℕ) (hScop : ∀ t ∈ S, Nat.Coprime t U) :
    ∑ t ∈ S, e U ((h : ℤ) * ((rOf' U t : ℕ) : ℤ))
      = ∑ t ∈ S, e m ((b : ℤ) * ((rOf' m t : ℕ) : ℤ)) := by
  have hmU : m ∣ U := ⟨g, by rw [hU]; ring⟩
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [e_reduce hg hm hU hh]
  refine e_eq_of_zmod hm ?_
  have : NeZero m := ⟨hm.ne'⟩
  push_cast
  rw [rOf'_cast m t, inv_reduce hm hmU (hScop t ht)]

/-! ## The parity substitution `t = 2u` -/

/-- The frequency `b · 2⁻¹ mod m`. -/
noncomputable def halfCoef (m b : ℕ) : ℕ := (((b : ℕ) : ZMod m) * ((2 : ℕ) : ZMod m)⁻¹).val

theorem halfCoef_coprime {m b : ℕ} (hm : 0 < m) (h2 : Nat.Coprime 2 m) (hb : Nat.Coprime b m) :
    Nat.Coprime (halfCoef m b) m := by
  have : NeZero m := ⟨hm.ne'⟩
  have hbu : IsUnit ((b : ℕ) : ZMod m) := (ZMod.isUnit_iff_coprime b m).2 hb
  have h2u : IsUnit (((2 : ℕ) : ZMod m)) := (ZMod.isUnit_iff_coprime 2 m).2 h2
  have h2iu : IsUnit (((2 : ℕ) : ZMod m)⁻¹) :=
    isUnit_iff_exists.2 ⟨((2 : ℕ) : ZMod m), ZMod.inv_mul_of_unit _ h2u,
      ZMod.mul_inv_of_unit _ h2u⟩
  have hu : IsUnit (((b : ℕ) : ZMod m) * ((2 : ℕ) : ZMod m)⁻¹) := hbu.mul h2iu
  have := ZMod.val_coe_unit_coprime hu.unit
  rwa [IsUnit.unit_spec] at this

/-- Substituting `t = 2u`: the phase becomes `e_m(b 2⁻¹ u⁻¹)`, again with a unit frequency. -/
theorem e_half {m b u : ℕ} (hm : 0 < m) (h2 : Nat.Coprime 2 m) (hu : Nat.Coprime u m) :
    e m ((b : ℤ) * ((rOf' m (2 * u) : ℕ) : ℤ))
      = e m ((halfCoef m b : ℤ) * ((rOf' m u : ℕ) : ℤ)) := by
  have : NeZero m := ⟨hm.ne'⟩
  refine e_eq_of_zmod hm ?_
  have h2u : IsUnit (((2 : ℕ) : ZMod m)) := (ZMod.isUnit_iff_coprime 2 m).2 h2
  have huu : IsUnit ((u : ℕ) : ZMod m) := (ZMod.isUnit_iff_coprime u m).2 hu
  have hcast : (((2 * u : ℕ)) : ZMod m) = ((2 : ℕ) : ZMod m) * ((u : ℕ) : ZMod m) := by
    push_cast; ring
  have hhalf : ((halfCoef m b : ℕ) : ZMod m) = ((b : ℕ) : ZMod m) * ((2 : ℕ) : ZMod m)⁻¹ := by
    simp [halfCoef]
  push_cast
  rw [rOf'_cast m (2 * u), rOf'_cast m u, hcast, zmod_mul_inv h2u huu]
  push_cast at hhalf ⊢
  rw [hhalf]
  ring

/-- The even part of a prefix sum is again a Kloosterman prefix sum, of half the length. -/
theorem sum_even_part {m b T : ℕ} (hm : 0 < m) (h2 : Nat.Coprime 2 m) :
    ∑ t ∈ (Finset.Icc 1 T).filter (fun t => Nat.Coprime t m ∧ 2 ∣ t),
        e m ((b : ℤ) * ((rOf' m t : ℕ) : ℤ))
      = kloos m (halfCoef m b) (T / 2) := by
  have himg : (Finset.Icc 1 T).filter (fun t => Nat.Coprime t m ∧ 2 ∣ t)
      = ((Finset.Icc 1 (T / 2)).filter (fun u => Nat.Coprime u m)).image (fun u => 2 * u) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨ht1, ht2⟩, hcop, k, rfl⟩
      refine ⟨k, ⟨⟨by omega, ?_⟩, ?_⟩, rfl⟩
      · exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
      · exact Nat.Coprime.coprime_dvd_left (dvd_mul_left k 2) hcop
    · rintro ⟨u, ⟨⟨hu1, hu2⟩, hucop⟩, rfl⟩
      have : 2 * u ≤ T := by
        have := (Nat.le_div_iff_mul_le (k := 2) (by norm_num)).1 hu2
        omega
      exact ⟨⟨by omega, this⟩, Nat.Coprime.mul_left h2 hucop, ⟨u, rfl⟩⟩
  rw [himg, Finset.sum_image (by intro x _ y _ hxy; dsimp only at hxy; omega), kloos_eq]
  refine Finset.sum_congr rfl fun u hu => ?_
  exact e_half hm h2 (Finset.mem_filter.1 hu).2

/-! ## Splitting an interval sum into two prefix sums -/

theorem sum_Ioc_split (F : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] {T₁ T₂ : ℕ} (hT : T₁ ≤ T₂) :
    ∑ t ∈ (Finset.Ioc T₁ T₂).filter P, F t
      = (∑ t ∈ (Finset.Icc 1 T₂).filter P, F t) - ∑ t ∈ (Finset.Icc 1 T₁).filter P, F t := by
  have hIcc : ∀ T : ℕ, Finset.Icc 1 T = Finset.Ioc 0 T := by
    intro T; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, hIcc]
  have hsplit : Finset.Ioc 0 T₁ ∪ Finset.Ioc T₁ T₂ = Finset.Ioc 0 T₂ :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hT
  have hdisj : Disjoint ((Finset.Ioc 0 T₁).filter P) ((Finset.Ioc T₁ T₂).filter P) :=
    Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le (le_refl T₁))
  have h := congrArg (fun s : Finset ℕ => ∑ t ∈ s.filter P, F t) hsplit
  simp only [Finset.filter_union] at h
  rw [Finset.sum_union hdisj] at h
  rw [← h]
  ring

/-! ## The full prefix bound, including the parity subtraction -/

/-- Bound for a prefix sum `∑_{t ≤ T, (t,U)=1} e_U(h t⁻¹)` after reduction to the modulus
`m = U/(h,U)` and frequency `b = h/(h,U)`.  In the case where the unit condition modulo `U`
is strictly stronger than the one modulo `m` (namely `U` even but `m` odd), the even terms
are subtracted off, which produces a second Kloosterman prefix sum of half the length by the
substitution `t = 2u`; hence the factor `2`. -/
theorem prefix_full_bound {c δ : ℝ} (hδ : 0 ≤ δ) {U m g b h T : ℕ}
    (hg : 0 < g) (hm : 0 < m) (hU : U = g * m) (hh : h = g * b)
    (hbcop : Nat.Coprime b m)
    (hBG : ∀ N : ℕ, (m : ℝ) ^ c < (N : ℝ) → (N : ℝ) < (m : ℝ) → ∀ a : ℕ, Nat.Coprime a m →
        ‖kloos m a N‖ ≤ δ * (N : ℝ))
    (hTm : (T : ℝ) < (m : ℝ))
    (hcase : (∀ t : ℕ, Nat.Coprime t U ↔ Nat.Coprime t m) ∨
      (¬ (2 ∣ m) ∧ ∀ t : ℕ, Nat.Coprime t U ↔ (Nat.Coprime t m ∧ ¬ (2 ∣ t)))) :
    ‖∑ t ∈ (Finset.Icc 1 T).filter (fun t => Nat.Coprime t U),
        e U ((h : ℤ) * ((rOf' U t : ℕ) : ℤ))‖ ≤ 2 * (δ * (T : ℝ) + (m : ℝ) ^ c) := by
  have hmc : (0 : ℝ) ≤ (m : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
  have hδT : (0 : ℝ) ≤ δ * (T : ℝ) := mul_nonneg hδ hT0
  rw [sum_reduce hg hm hU hh _ (fun t ht => (Finset.mem_filter.1 ht).2)]
  rcases hcase with hA | ⟨h2m, hB⟩
  · have hfe : (Finset.Icc 1 T).filter (fun t => Nat.Coprime t U)
        = (Finset.Icc 1 T).filter (fun t => Nat.Coprime t m) :=
      Finset.filter_congr (fun t _ => hA t)
    rw [hfe, ← kloos_eq]
    have := prefix_bound hBG hTm hbcop hδ
    linarith
  · have h2cop : Nat.Coprime 2 m := (Nat.prime_two.coprime_iff_not_dvd).2 h2m
    have hfe : (Finset.Icc 1 T).filter (fun t => Nat.Coprime t U)
        = ((Finset.Icc 1 T).filter (fun t => Nat.Coprime t m)).filter (fun t => ¬ (2 ∣ t)) := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr (fun t _ => hB t)
    rw [hfe]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      ((Finset.Icc 1 T).filter (fun t => Nat.Coprime t m)) (fun t => 2 ∣ t)
      (fun t => e m ((b : ℤ) * ((rOf' m t : ℕ) : ℤ)))
    have heven : ∑ t ∈ ((Finset.Icc 1 T).filter (fun t => Nat.Coprime t m)).filter
          (fun t => 2 ∣ t), e m ((b : ℤ) * ((rOf' m t : ℕ) : ℤ))
        = kloos m (halfCoef m b) (T / 2) := by
      rw [Finset.filter_filter]
      exact sum_even_part hm h2cop
    have hodd : ∑ t ∈ ((Finset.Icc 1 T).filter (fun t => Nat.Coprime t m)).filter
          (fun t => ¬ (2 ∣ t)), e m ((b : ℤ) * ((rOf' m t : ℕ) : ℤ))
        = kloos m b T - kloos m (halfCoef m b) (T / 2) := by
      rw [kloos_eq, ← heven, ← hsplit]
      ring
    rw [hodd]
    have hb1 := prefix_bound hBG hTm hbcop hδ
    have hhalfle : ((T / 2 : ℕ) : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast Nat.div_le_self T 2
    have hb2 := prefix_bound hBG (lt_of_le_of_lt hhalfle hTm)
      (halfCoef_coprime hm h2cop hbcop) hδ
    have hstep : ‖kloos m b T - kloos m (halfCoef m b) (T / 2)‖
        ≤ ‖kloos m b T‖ + ‖kloos m (halfCoef m b) (T / 2)‖ := norm_sub_le _ _
    have hδhalf : δ * ((T / 2 : ℕ) : ℝ) ≤ δ * (T : ℝ) := by
      exact mul_le_mul_of_nonneg_left hhalfle hδ
    linarith

/-! ## Classification of the unit condition after reduction -/

/-- If all prime factors of `U` lie in `{2, p}` and the divisor `m` of `U` still has `p` as a
prime factor, then coprimality to `U` either agrees with coprimality to `m`, or (when `U` is
even and `m` is odd) is coprimality to `m` together with oddness. -/
theorem coprime_case {U m p : ℕ} (hU : 0 < U) (hm : 0 < m) (hmU : m ∣ U)
    (hsub : U.primeFactors ⊆ {2, p}) (hpm : p ∣ m) (hp : p.Prime) :
    (∀ t : ℕ, Nat.Coprime t U ↔ Nat.Coprime t m) ∨
    (¬ (2 ∣ m) ∧ ∀ t : ℕ, Nat.Coprime t U ↔ (Nat.Coprime t m ∧ ¬ (2 ∣ t))) := by
  have hpfm : m.primeFactors ⊆ U.primeFactors := Nat.primeFactors_mono hmU hU.ne'
  have hpmem : p ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpm, hm.ne'⟩
  by_cases hcase2 : 2 ∣ U ∧ ¬ (2 ∣ m)
  · refine Or.inr ⟨hcase2.2, fun t => ?_⟩
    have h2U : (2 : ℕ) ∈ U.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, hcase2.1, hU.ne'⟩
    rw [coprime_iff_forall_primeFactors hU.ne', coprime_iff_forall_primeFactors hm.ne']
    constructor
    · intro hall
      exact ⟨fun P hP => hall P (hpfm hP), hall 2 h2U⟩
    · rintro ⟨h1, h2⟩ P hP
      rcases Finset.mem_insert.1 (hsub hP) with rfl | hPp
      · exact h2
      · rw [Finset.mem_singleton] at hPp
        subst hPp
        exact h1 P hpmem
  · refine Or.inl (fun t => ?_)
    rw [coprime_iff_forall_primeFactors hU.ne', coprime_iff_forall_primeFactors hm.ne']
    constructor
    · intro hall P hP
      exact hall P (hpfm hP)
    · intro hall P hP
      rcases Finset.mem_insert.1 (hsub hP) with rfl | hPp
      · have h2U : (2 : ℕ) ∣ U := Nat.dvd_of_mem_primeFactors hP
        have h2m : (2 : ℕ) ∣ m := by tauto
        exact hall 2 (Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2m, hm.ne'⟩)
      · rw [Finset.mem_singleton] at hPp
        subst hPp
        exact hall P hpmem

/-! ## Analytic helpers -/

theorem tendsto_natRpow {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto (fun q : ℕ => (q : ℝ) ^ β) atTop atTop :=
  (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop

theorem ev_five_rpow_lt {ε : ℝ} (_hε0 : 0 < ε) (hε1 : ε < 1) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ q : ℕ in atTop, 5 * (q : ℝ) ^ ε < (q : ℝ) / K := by
  filter_upwards [(tendsto_natRpow (show (0:ℝ) < 1 - ε by linarith)).eventually_ge_atTop (6 * K),
    eventually_gt_atTop 0] with q hq hq0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hpos : (0 : ℝ) < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hqR ε
  have hsplit : (q : ℝ) ^ ε * (q : ℝ) ^ (1 - ε) = (q : ℝ) := by
    rw [← Real.rpow_add hqR, show ε + (1 - ε) = (1 : ℝ) by ring, Real.rpow_one]
  rw [lt_div_iff₀ hK]
  calc 5 * (q : ℝ) ^ ε * K < 6 * K * (q : ℝ) ^ ε := by nlinarith [mul_pos hpos hK]
    _ ≤ (q : ℝ) ^ (1 - ε) * (q : ℝ) ^ ε := mul_le_mul_of_nonneg_right hq hpos.le
    _ = (q : ℝ) := by rw [mul_comm]; exact hsplit

theorem ev_rpow_quarter {ε : ℝ} (hε0 : 0 < ε) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    ∀ᶠ q : ℕ in atTop, A * (q : ℝ) ^ (ε / 4) ≤ B * (q : ℝ) ^ ε := by
  filter_upwards [(tendsto_natRpow (show (0:ℝ) < 3 * ε / 4 by linarith)).eventually_ge_atTop
      (A / B + 1), eventually_gt_atTop 0] with q hq hq0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hpos : (0 : ℝ) < (q : ℝ) ^ (ε / 4) := Real.rpow_pos_of_pos hqR _
  have hsplit : (q : ℝ) ^ (ε / 4) * (q : ℝ) ^ (3 * ε / 4) = (q : ℝ) ^ ε := by
    rw [← Real.rpow_add hqR, show ε / 4 + 3 * ε / 4 = ε by ring]
  have hAB : A ≤ B * (q : ℝ) ^ (3 * ε / 4) := by
    have h1 : A / B ≤ (q : ℝ) ^ (3 * ε / 4) := by linarith
    rw [div_le_iff₀ hB] at h1
    linarith
  calc A * (q : ℝ) ^ (ε / 4) ≤ (B * (q : ℝ) ^ (3 * ε / 4)) * (q : ℝ) ^ (ε / 4) :=
        mul_le_mul_of_nonneg_right hAB hpos.le
    _ = B * ((q : ℝ) ^ (ε / 4) * (q : ℝ) ^ (3 * ε / 4)) := by ring
    _ = B * (q : ℝ) ^ ε := by rw [hsplit]

theorem ev_const_le {ε : ℝ} (hε0 : 0 < ε) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    ∀ᶠ q : ℕ in atTop, A ≤ B * (q : ℝ) ^ ε := by
  filter_upwards [(tendsto_natRpow hε0).eventually_ge_atTop (A / B + 1)] with q hq
  have h1 : A / B ≤ (q : ℝ) ^ ε := by linarith
  rw [div_le_iff₀ hB] at h1
  linarith

end EquidistAux

open EquidistAux

/-! ## The main equidistribution statement -/

/-- **Equidistribution of modular inverses** (paper §2, lines 135-148).  For a prime power
`q = p ^ a`, a modulus `U ∈ {q, 2q, 4q, 4pq}`, an interval `(T₁, T₂]` with `T₂ ≤ 5 q^ε`, and a
residue interval `[α, α+ℓ) ⊆ [0, U)`, the number of `t ∈ (T₁, T₂]` coprime to `U` whose inverse
mod `U` lies in `[α, α+ℓ)` matches the expected count `φ(U)/U · (T₂-T₁) · ℓ/U` up to `o(q^ε)`,
uniformly in all of the data.  Proved from `bourgain_garaev` and `erdos_turan_weak`. -/
theorem equidist_inverse' (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ p a : ℕ, p.Prime → 0 < a → q = p ^ a →
      ∀ U : ℕ, U = q ∨ U = 2 * q ∨ U = 4 * q ∨ U = 4 * p * q →
        ∀ T₁ T₂ : ℕ, T₁ ≤ T₂ → (T₂ : ℝ) ≤ 5 * (q : ℝ) ^ ε →
          ∀ α ℓ : ℕ, α + ℓ ≤ U →
            |((invCand' U T₁ T₂ α ℓ).card : ℝ)
                - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ)) * (ℓ : ℝ) / (U : ℝ)|
              ≤ κ * (q : ℝ) ^ ε := by
  obtain ⟨C, hCpos, hET⟩ := erdos_turan_weak
  obtain ⟨c₀, hc₀pos, hBG0⟩ := bourgain_garaev
  intro κ hκ
  have hCne : C ≠ 0 := hCpos.ne'
  -- the Bourgain-Garaev exponent
  set c : ℝ := min (c₀ / 2) (ε / 8) with hcdef
  have hcpos : 0 < c := lt_min (by linarith) (by linarith)
  have hclt : c < c₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcle : c ≤ ε / 8 := min_le_right _ _
  -- the (fixed) Erdos-Turan cutoff
  set H : ℕ := (⌈30 * C / κ⌉₊ + 1) ^ 2 with hHdef
  have hHpos : 0 < H := pow_pos (Nat.succ_pos _) 2
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  have hHne : (H : ℝ) ≠ 0 := hHR.ne'
  -- `H` is a perfect square, so its square root is the integer `⌈30 C / κ⌉₊ + 1`
  have hsqrtH : Real.sqrt (H : ℝ) = (⌈30 * C / κ⌉₊ : ℝ) + 1 := by
    have h2 : ((H : ℕ) : ℝ) = ((⌈30 * C / κ⌉₊ : ℝ) + 1) ^ 2 := by
      rw [hHdef]; push_cast; ring
    rw [h2, Real.sqrt_sq (by positivity)]
  have hsqrtHpos : (0 : ℝ) < Real.sqrt (H : ℝ) := by rw [hsqrtH]; positivity
  have hH30 : 30 * C ≤ κ * Real.sqrt (H : ℝ) := by
    have h1 : 30 * C / κ ≤ (⌈30 * C / κ⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : 30 * C / κ ≤ Real.sqrt (H : ℝ) := by rw [hsqrtH]; linarith
    rw [div_le_iff₀ hκ] at h3
    linarith
  -- the Bourgain-Garaev tolerance
  set δ : ℝ := κ / (120 * C * (H : ℝ)) with hδdef
  have hδpos : 0 < δ := by positivity
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 (hBG0 c hcpos hclt δ hδpos)
  filter_upwards [eventually_ge_atTop (H * m₀), eventually_gt_atTop H, eventually_gt_atTop 0,
    ev_five_rpow_lt hε0 hε1 hHR,
    ev_rpow_quarter hε0 (16 * C * (H : ℝ)) (show (0:ℝ) < κ / 6 by positivity),
    ev_const_le hε0 3 (show (0:ℝ) < κ / 6 by positivity)] with q hqm0 hqH hq0 hq1 hq2 hq3
  intro p a hp ha hqpa U hU T₁ T₂ hT hT2 α ℓ hαℓ
  -- elementary facts about `q`, `p` and `U`
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hqeps : (0 : ℝ) < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hqR ε
  have hple : p ≤ q := by rw [hqpa]; exact le_self_pow₀ hp.one_lt.le ha.ne'
  have hpR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hple
  have hqdvdU : q ∣ U := by
    rcases hU with rfl | rfl | rfl | rfl
    exacts [dvd_rfl, ⟨2, by ring⟩, ⟨4, by ring⟩, ⟨4 * p, by ring⟩]
  have hUpos : 0 < U := by
    rcases hU with rfl | rfl | rfl | rfl
    · exact hq0
    · omega
    · omega
    · exact Nat.mul_pos (Nat.mul_pos (by norm_num) hp.pos) hq0
  have hUR : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hUpos
  have hUleR : (U : ℝ) ≤ 4 * (q : ℝ) * (q : ℝ) := by
    rcases hU with rfl | rfl | rfl | rfl <;> push_cast <;> nlinarith
  have hpfq : q.primeFactors = {p} := by
    rw [hqpa, Nat.primeFactors_pow p ha.ne', hp.primeFactors]
  have hpf2 : (2 : ℕ).primeFactors = {2} := Nat.prime_two.primeFactors
  have hpf4 : (4 : ℕ).primeFactors = {2} := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_pow 2 (by norm_num), hpf2]
  have hpfU : U.primeFactors ⊆ {2, p} := by
    rcases hU with rfl | rfl | rfl | rfl
    · rw [hpfq]; intro y hy; simp only [Finset.mem_singleton] at hy; simp [hy]
    · rw [Nat.primeFactors_mul (by norm_num) hq0.ne', hpf2, hpfq]
      intro y hy; simp only [Finset.mem_union, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> simp
    · rw [Nat.primeFactors_mul (by norm_num) hq0.ne', hpf4, hpfq]
      intro y hy; simp only [Finset.mem_union, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> simp
    · rw [Nat.primeFactors_mul (Nat.mul_ne_zero (by norm_num) hp.pos.ne') hq0.ne',
        Nat.primeFactors_mul (by norm_num) hp.pos.ne', hpf4, hp.primeFactors, hpfq]
      intro y hy
      simp only [Finset.mem_union, Finset.mem_singleton] at hy
      rcases hy with (rfl | rfl) | rfl <;> simp
  have hcardU : U.primeFactors.card ≤ 2 :=
    le_trans (Finset.card_le_card hpfU) (le_trans (Finset.card_insert_le _ _) (by simp))
  -- the enumeration of the coprime `t`'s
  set Sc : Finset ℕ := (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U) with hScdef
  obtain ⟨N, hN⟩ : ∃ N, Sc.card = N := ⟨_, rfl⟩
  set f : Fin N ↪o ℕ := Sc.orderEmbOfFin hN with hfdef
  set x : Fin N → ZMod U := fun j => (((f j : ℕ) : ZMod U))⁻¹ with hxdef
  have hmapSc : Finset.map f.toEmbedding Finset.univ = Sc := by
    rw [hfdef]; exact Finset.map_orderEmbOfFin_univ Sc hN
  have hcount : (Finset.univ.filter (fun j : Fin N => (x j).val ∈ Finset.Ico α (α + ℓ))).card
      = (invCand' U T₁ T₂ α ℓ).card := by
    have h1 : invCand' U T₁ T₂ α ℓ = Sc.filter (fun t => rOf' U t ∈ Finset.Ico α (α + ℓ)) := by
      rw [hScdef, Finset.filter_filter]
      rfl
    rw [h1, ← hmapSc, Finset.filter_map, Finset.card_map]
    rfl
  have hsum : ∀ h : ℕ, (∑ j : Fin N, e U ((h : ℤ) * (((x j).val : ℕ) : ℤ)))
      = ∑ t ∈ Sc, e U ((h : ℤ) * ((rOf' U t : ℕ) : ℤ)) := by
    intro h
    rw [← hmapSc, Finset.sum_map]
    rfl
  have hETq := hET U hUpos N x H hHpos α ℓ hαℓ
  rw [hcount] at hETq
  -- bound on each nonzero Fourier coefficient
  have hSh : ∀ h ∈ Finset.Icc 1 H,
      ‖∑ j : Fin N, e U ((h : ℤ) * (((x j).val : ℕ) : ℤ))‖
        ≤ 20 * δ * (q : ℝ) ^ ε + 16 * (q : ℝ) ^ (ε / 4) := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    obtain ⟨hh1, hh2⟩ := hh
    rw [hsum h, hScdef]
    have hgpos : 0 < Nat.gcd h U := Nat.gcd_pos_of_pos_left U hh1
    set g : ℕ := Nat.gcd h U with hgdef
    set m : ℕ := U / g with hmdef
    set b : ℕ := h / g with hbdef
    have hUgm : U = g * m := (Nat.mul_div_cancel' (Nat.gcd_dvd_right h U)).symm
    have hhgb : h = g * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_left h U)).symm
    have hbcop : Nat.Coprime b m := Nat.coprime_div_gcd_div_gcd hgpos
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, Nat.mul_zero] at hUgm; omega
      · exact h0
    have hmU : m ∣ U := ⟨g, by rw [hUgm]; ring⟩
    have hgleH : g ≤ H := le_trans (Nat.le_of_dvd hh1 (Nat.gcd_dvd_left h U)) hh2
    have hpm : p ∣ m := by
      by_contra hpmn
      have hcop : Nat.Coprime (p ^ a) m := Nat.Coprime.pow_left a ((hp.coprime_iff_not_dvd).2 hpmn)
      have hdvd : p ^ a ∣ g * m := by rw [← hUgm, ← hqpa]; exact hqdvdU
      have hdg : p ^ a ∣ g := hcop.dvd_of_dvd_mul_right hdvd
      have hqg : q ≤ g := Nat.le_of_dvd hgpos (by rw [hqpa]; exact hdg)
      omega
    have hUleHm : U ≤ H * m := by rw [hUgm]; exact Nat.mul_le_mul_right m hgleH
    have hqleHm : q ≤ H * m := le_trans (Nat.le_of_dvd hUpos hqdvdU) hUleHm
    have hm0 : m₀ ≤ m := by
      by_contra hlt
      push Not at hlt
      have : H * m < H * m₀ := (Nat.mul_lt_mul_left hHpos).2 hlt
      omega
    have hmqH : (q : ℝ) / (H : ℝ) ≤ (m : ℝ) := by
      have h1 : (q : ℝ) ≤ (H : ℝ) * (m : ℝ) := by exact_mod_cast hqleHm
      rw [div_le_iff₀ hHR]; linarith
    have hT2m : (T₂ : ℝ) < (m : ℝ) := lt_of_le_of_lt hT2 (lt_of_lt_of_le hq1 hmqH)
    have hT1m : (T₁ : ℝ) < (m : ℝ) := lt_of_le_of_lt (by exact_mod_cast hT) hT2m
    have hBGm := hm₀ m hm0
    have hcase := coprime_case hUpos hmpos hmU hpfU hpm hp
    have hmleR : (m : ℝ) ≤ 4 * (q : ℝ) * (q : ℝ) :=
      le_trans (by exact_mod_cast Nat.le_of_dvd hUpos hmU) hUleR
    have hbase : (1 : ℝ) ≤ 4 * (q : ℝ) * (q : ℝ) := by nlinarith
    have hmc4 : (m : ℝ) ^ c ≤ 4 * (q : ℝ) ^ (ε / 4) := by
      have h1 : (m : ℝ) ^ c ≤ (4 * (q : ℝ) * (q : ℝ)) ^ c :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hmleR hcpos.le
      have h2 : (4 * (q : ℝ) * (q : ℝ)) ^ c ≤ (4 * (q : ℝ) * (q : ℝ)) ^ (ε / 8) :=
        Real.rpow_le_rpow_of_exponent_le hbase hcle
      have h3 : (4 * (q : ℝ) * (q : ℝ)) ^ (ε / 8) = (4 : ℝ) ^ (ε / 8) * (q : ℝ) ^ (ε / 4) := by
        rw [show 4 * (q : ℝ) * (q : ℝ) = 4 * ((q : ℝ) * (q : ℝ)) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        rw [show (q : ℝ) * (q : ℝ) = (q : ℝ) ^ (2 : ℝ) by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
        rw [← Real.rpow_mul hqR.le]
        congr 1
        ring
      have h4 : (4 : ℝ) ^ (ε / 8) ≤ 4 := by
        have h5 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 4 by norm_num)
          (show ε / 8 ≤ 1 by linarith)
        rwa [Real.rpow_one] at h5
      have h5 : (0 : ℝ) ≤ (q : ℝ) ^ (ε / 4) := (Real.rpow_pos_of_pos hqR _).le
      nlinarith [h1, h2, h3, h4, h5]
    rw [sum_Ioc_split _ _ hT]
    have hb2 := prefix_full_bound (T := T₂) hδpos.le hgpos hmpos hUgm hhgb hbcop hBGm hT2m hcase
    have hb1 := prefix_full_bound (T := T₁) hδpos.le hgpos hmpos hUgm hhgb hbcop hBGm hT1m hcase
    have hstep := norm_sub_le
      (∑ t ∈ (Finset.Icc 1 T₂).filter (fun t => Nat.Coprime t U),
        e U ((h : ℤ) * ((rOf' U t : ℕ) : ℤ)))
      (∑ t ∈ (Finset.Icc 1 T₁).filter (fun t => Nat.Coprime t U),
        e U ((h : ℤ) * ((rOf' U t : ℕ) : ℤ)))
    have hT1le : (T₁ : ℝ) ≤ (T₂ : ℝ) := by exact_mod_cast hT
    have hδT2 : δ * (T₂ : ℝ) ≤ δ * (5 * (q : ℝ) ^ ε) := mul_le_mul_of_nonneg_left hT2 hδpos.le
    have hδT1 : δ * (T₁ : ℝ) ≤ δ * (T₂ : ℝ) := mul_le_mul_of_nonneg_left hT1le hδpos.le
    linarith
  -- summing over the cutoff range
  have hSumBd : (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
      ‖∑ j : Fin N, e U ((h : ℤ) * (((x j).val : ℕ) : ℤ))‖)
      ≤ (H : ℝ) * (20 * δ * (q : ℝ) ^ ε + 16 * (q : ℝ) ^ (ε / 4)) := by
    have hterm : ∀ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
        ‖∑ j : Fin N, e U ((h : ℤ) * (((x j).val : ℕ) : ℤ))‖
        ≤ 20 * δ * (q : ℝ) ^ ε + 16 * (q : ℝ) ^ (ε / 4) := by
      intro h hh
      have h1 : (1 : ℝ) / (h : ℝ) ≤ 1 := by
        rw [Finset.mem_Icc] at hh
        have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh.1
        rw [div_le_one (by linarith)]
        linarith
      have h2 := hSh h hh
      have h3 : (0 : ℝ) ≤ ‖∑ j : Fin N, e U ((h : ℤ) * (((x j).val : ℕ) : ℤ))‖ := norm_nonneg _
      nlinarith
    calc (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
          ‖∑ j : Fin N, e U ((h : ℤ) * (((x j).val : ℕ) : ℤ))‖)
        ≤ ∑ _h ∈ Finset.Icc 1 H, (20 * δ * (q : ℝ) ^ ε + 16 * (q : ℝ) ^ (ε / 4)) :=
          Finset.sum_le_sum hterm
      _ = (H : ℝ) * (20 * δ * (q : ℝ) ^ ε + 16 * (q : ℝ) ^ (ε / 4)) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          norm_num
  -- the counting error
  have hNle : (N : ℝ) ≤ 5 * (q : ℝ) ^ ε := by
    have h1 : N ≤ T₂ := by
      rw [← hN, hScdef]
      calc ((Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)).card
          ≤ (Finset.Ioc T₁ T₂).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = T₂ - T₁ := Nat.card_Ioc _ _
        _ ≤ T₂ := Nat.sub_le _ _
    have h2 : (N : ℝ) ≤ (T₂ : ℝ) := by exact_mod_cast h1
    linarith
  have hccN : |(N : ℝ) - (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ)| ≤ 3 := by
    rw [← hN, hScdef]
    exact coprime_count_approx hUpos hcardU hT
  have hℓU : (ℓ : ℝ) / (U : ℝ) ≤ 1 := by
    rw [div_le_one hUR]
    exact_mod_cast le_trans (Nat.le_add_left ℓ α) hαℓ
  have hℓUnn : (0 : ℝ) ≤ (ℓ : ℝ) / (U : ℝ) := by positivity
  have habs2 : |(N : ℝ) * (ℓ : ℝ) / (U : ℝ)
      - (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ) * (ℓ : ℝ) / (U : ℝ)| ≤ 3 := by
    have hd : (N : ℝ) * (ℓ : ℝ) / (U : ℝ)
        - (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ) * (ℓ : ℝ) / (U : ℝ)
        = ((N : ℝ) - (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ))
          * ((ℓ : ℝ) / (U : ℝ)) := by ring
    rw [hd, abs_mul, abs_of_nonneg hℓUnn]
    calc |(N : ℝ) - (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ)| * ((ℓ : ℝ) / (U : ℝ))
        ≤ 3 * 1 := mul_le_mul hccN hℓU hℓUnn (by norm_num)
      _ = 3 := by norm_num
  -- final bookkeeping
  have hterm1 : C * ((N : ℝ) / Real.sqrt (H : ℝ)) ≤ κ / 6 * (q : ℝ) ^ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hsqrtHpos]
    have h1 : C * (N : ℝ) ≤ C * (5 * (q : ℝ) ^ ε) := mul_le_mul_of_nonneg_left hNle hCpos.le
    have h2 : 5 * C ≤ κ * Real.sqrt (H : ℝ) / 6 := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hqeps.le
    linarith
  have hCH : C * ((H : ℝ) * (20 * δ)) = κ / 6 := by
    rw [hδdef]; field_simp; ring
  have hterm2 : C * ((H : ℝ) * (20 * δ * (q : ℝ) ^ ε + 16 * (q : ℝ) ^ (ε / 4)))
      ≤ κ / 6 * (q : ℝ) ^ ε + κ / 6 * (q : ℝ) ^ ε := by
    have hrw : C * ((H : ℝ) * (20 * δ * (q : ℝ) ^ ε + 16 * (q : ℝ) ^ (ε / 4)))
        = (C * ((H : ℝ) * (20 * δ))) * (q : ℝ) ^ ε
          + (16 * C * (H : ℝ)) * (q : ℝ) ^ (ε / 4) := by ring
    rw [hrw, hCH]
    linarith [hq2]
  have hCSum := mul_le_mul_of_nonneg_left hSumBd hCpos.le
  calc |((invCand' U T₁ T₂ α ℓ).card : ℝ)
        - (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ) * (ℓ : ℝ) / (U : ℝ)|
      ≤ |((invCand' U T₁ T₂ α ℓ).card : ℝ) - (N : ℝ) * (ℓ : ℝ) / (U : ℝ)|
        + |(N : ℝ) * (ℓ : ℝ) / (U : ℝ)
          - (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ) * (ℓ : ℝ) / (U : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ κ * (q : ℝ) ^ ε := by
        have hsplit : C * ((N : ℝ) / Real.sqrt (H : ℝ)
            + ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
              ‖∑ j : Fin N, e U ((h : ℤ) * (((x j).val : ℕ) : ℤ))‖)
            = C * ((N : ℝ) / Real.sqrt (H : ℝ))
              + C * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
                ‖∑ j : Fin N, e U ((h : ℤ) * (((x j).val : ℕ) : ℤ))‖) := by ring
        rw [hsplit] at hETq
        linarith

end Equidist
end Erdos289
