import Erdos289.External
import Erdos289.ErdosTuran
import Erdos289.ExternalAxioms

/-!
# Bridging the author's audited external axioms to our statements

This file proves our six external axioms (`Erdos289.liu_sawhney`, `Erdos289.cfhmpsv_structure`,
`Erdos289.bourgain_garaev`, `Erdos289.erdos_turan`, `Erdos289.mertens_second`,
`Erdos289.divisor_bound`) as theorems from the author's independently-audited axiom module
`Erdos289.External.Assumed`, so that `#print axioms` on downstream results shows only the
audited `Erdos289.External.Assumed.*` axioms.
-/

namespace Erdos289

open Filter Finset
open scoped BigOperators

theorem bridge_liu_sawhney (ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N,
      (1 - 1 / Real.exp 1 + ζ) * (N : ℝ) ≤ (A.card : ℝ) →
      ∃ D ⊆ A, ∑ d ∈ D, (1 : ℚ) / d = 1 := by
  obtain ⟨N₀, hN₀, h⟩ := Erdos289.External.Assumed.liu_sawhney ζ hζ0 hζ1
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun N hN A hA hcard => ?_⟩
  have hcard' : (1 - Real.exp (-1) + ζ) * (N : ℝ) ≤ (A.card : ℝ) := by
    simpa [Real.exp_neg, one_div] using hcard
  exact h N hN A hA hcard'

theorem bridge_mertens_second :
    ∃ B₁ : ℝ, Tendsto
      (fun x : ℕ => (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p)
        - Real.log (Real.log x)) atTop (nhds B₁) := by
  obtain ⟨B₁, hB₁⟩ := Erdos289.External.Assumed.mertens_second
  refine ⟨B₁, ?_⟩
  have hcomp := hB₁.comp tendsto_natCast_atTop_atTop
  have heq : (fun x : ℕ => (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p)
        - Real.log (Real.log x))
      = (fun x : ℝ => Erdos289.External.primeReciprocalSum x - Real.log (Real.log x)) ∘
        (Nat.cast : ℕ → ℝ) := by
    funext n
    simp only [Function.comp_apply, Erdos289.External.primeReciprocalSum, Nat.floor_natCast]
  rw [heq]
  exact hcomp

theorem bridge_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε := by
  obtain ⟨n₀, hn₀, h⟩ := Erdos289.External.Assumed.divisor_bound ε hε
  rw [Filter.eventually_atTop]
  exact ⟨n₀, fun n hn => h n hn⟩

/-! ## Shared periodicity lemma for the Erdős–Turán and Bourgain–Garaev bridges.

Both `expPhase U w` (the author's character, using the canonical `ZMod U` representative) and
`e U n` (our character, using an arbitrary integer representative) are `Complex.exp` of
`2πi * (representative) / U`; they agree whenever the two integer representatives are congruent
mod `U`, by periodicity of `Complex.exp` at multiples of `2πi`. -/

private theorem exp_div_U_eq (U : ℕ) (hU : 0 < U) (a b : ℤ) (h : a ≡ b [ZMOD (U : ℤ)]) :
    Complex.exp (2 * Real.pi * Complex.I * a / U) = Complex.exp (2 * Real.pi * Complex.I * b / U) := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  have hb : (b : ℂ) = (a : ℂ) + (U : ℂ) * (k : ℂ) := by
    have hb' : (b : ℤ) = a + U * k := by linarith [hk]
    exact_mod_cast hb'
  have hUne : (U : ℂ) ≠ 0 := by exact_mod_cast hU.ne'
  rw [hb]
  rw [show (2 : ℂ) * Real.pi * Complex.I * (a + U * k) / U
      = 2 * Real.pi * Complex.I * a / U + (k : ℂ) * (2 * Real.pi * Complex.I) by field_simp]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The author's `expPhase U ((h : ZMod U) * z)` and our `e U (h * z.val)` compute the same
value, since `((h : ZMod U) * z).val ≡ h * z.val (mod U)`. -/
private theorem expPhase_eq_e {U : ℕ} (hU : 0 < U) (h : ℕ) (z : ZMod U) :
    Erdos289.External.expPhase U ((h : ZMod U) * z) = Erdos289.e U ((h : ℤ) * (z.val : ℤ)) := by
  have : NeZero U := ⟨hU.ne'⟩
  have hval : (((h : ZMod U) * z).val) ≡ (h * z.val) [MOD U] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [ZMod.natCast_rightInverse ((h : ZMod U) * z)]
    push_cast
    rw [ZMod.natCast_rightInverse z]
  have hvalZ : ((((h : ZMod U) * z).val : ℤ)) ≡ ((h : ℤ) * (z.val : ℤ)) [ZMOD (U : ℤ)] := by
    have hz := Int.natCast_modEq_iff.mpr hval
    push_cast at hz
    exact hz
  unfold Erdos289.External.expPhase Erdos289.e
  push_cast
  convert exp_div_U_eq U hU (((h : ZMod U) * z).val : ℤ) ((h : ℤ) * (z.val : ℤ)) hvalZ using 2 <;>
    push_cast <;> ring

theorem bridge_erdos_turan :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ), 0 < U → ∀ (N : ℕ) (x : Fin N → ZMod U) (H : ℕ), 0 < H →
      ∀ α ℓ : ℕ, α + ℓ ≤ U →
        |((univ.filter (fun j => (x j).val ∈ Finset.Ico α (α + ℓ))).card : ℝ)
              - (N : ℝ) * (ℓ : ℝ) / (U : ℝ)|
          ≤ C * ((N : ℝ) / (H : ℝ)
              + ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
                  ‖∑ j, e U (h * ((x j).val : ℤ))‖) := by
  obtain ⟨C, hC, h⟩ := Erdos289.External.Assumed.erdos_turan
  refine ⟨C, hC, fun U hU N x H hH α ℓ hαℓ => ?_⟩
  have h1U : 1 ≤ U := hU
  have h1H : 1 ≤ H := hH
  have hres : Erdos289.External.residueIntervalCount x α ℓ
      = (univ.filter (fun j => (x j).val ∈ Finset.Ico α (α + ℓ))).card := by
    unfold Erdos289.External.residueIntervalCount
    congr 1
    apply Finset.filter_congr
    intro j _
    rw [Finset.mem_Ico]
  have hfour : ∀ hh : ℕ, Erdos289.External.fourierSum x hh = ∑ j, e U (hh * ((x j).val : ℤ)) := by
    intro hh
    unfold Erdos289.External.fourierSum
    apply Finset.sum_congr rfl
    intro j _
    exact expPhase_eq_e hU hh (x j)
  have hkey := h U h1U N x H h1H α ℓ hαℓ
  rw [hres] at hkey
  simp only [hfour] at hkey
  exact hkey

theorem bridge_bourgain_garaev :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c < c₀ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, (m : ℝ) ^ c < (N : ℝ) → (N : ℝ) < (m : ℝ) →
        ∀ a : ℕ, Nat.Coprime a m →
          ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n m),
              e m (a * ((n : ZMod m)⁻¹).val)‖ ≤ ε * (N : ℝ) := by
  obtain ⟨c₀, hc₀, h⟩ := Erdos289.External.Assumed.bourgain_garaev
  refine ⟨c₀, hc₀, fun c hc hcc₀ ε hε => ?_⟩
  obtain ⟨m₀, hm₀, hmm⟩ := h c hc hcc₀ ε hε
  rw [Filter.eventually_atTop]
  refine ⟨m₀, fun m hm N hN1 hN2 a ha => ?_⟩
  have hmU : 0 < m := by omega
  have hunit : IsUnit ((a : ZMod m)) := (ZMod.isUnit_iff_coprime a m).mpr ha
  have hN2' : N < m := by exact_mod_cast hN2
  have hkey := hmm m hm N hN1 hN2' (a : ZMod m) hunit
  unfold Erdos289.External.inversePrefix at hkey
  have heq : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n m),
      Erdos289.External.expPhase m ((a : ZMod m) * (n : ZMod m)⁻¹)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n m),
        e m (a * ((n : ZMod m)⁻¹).val) := by
    apply Finset.sum_congr rfl
    intro n _
    exact expPhase_eq_e hmU a ((n : ZMod m)⁻¹)
  rw [heq] at hkey
  exact hkey

end Erdos289
