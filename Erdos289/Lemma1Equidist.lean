import Erdos289.External
import Erdos289.ErdosTuran

set_option maxHeartbeats 1000000

/-!
# Equidistribution of modular inverses (Lemma 1, part B)

This file proves `equidist_inverse'`, the "uniform discrepancy justification" paragraph of
Section 2 of `erdos_289_full_proof.pdf` (lines 135-148), from the two external inputs
`Erdos289.bourgain_garaev` and `Erdos289.erdos_turan`.

The definitions `rOf'` / `invCand'` are verbatim copies of `Erdos289.rOf` / `Erdos289.invCand`
from `Erdos289/Lemma1.lean` (that file is not imported here, to keep the two developments
independent; the names differ only by the prime).
-/

namespace Erdos289

open Finset Filter Topology
open scoped BigOperators

/-- The companion `r`-value for `t` at modulus `U`: the canonical representative in `[0, U)`
of `t⁻¹ mod U`.  (Copy of `Erdos289.rOf`.) -/
def rOf' (U t : ℕ) : ℕ := ((t : ZMod U)⁻¹).val

/-- The set of `t` in `(T₁, T₂]`, coprime to `U`, whose inverse mod `U` lands in the residue
interval `[α, α+ℓ)`.  (Copy of `Erdos289.invCand`.) -/
def invCand' (U T₁ T₂ α ℓ : ℕ) : Finset ℕ :=
  (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U ∧ rOf' U t ∈ Finset.Ico α (α + ℓ))

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
  haveI : NeZero m := ⟨hm.ne'⟩
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
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [rOf'_cast m t, inv_reduce hm hdvd hcop, sub_self]

end Erdos289
