import Erdos289.Descent
import Erdos289.Lemma1
import Erdos289.Lemma3

/-!
# Existence of correction data

Lemmas 1, 3 and 5 (with `ε = 1/10`) provide, for every sufficiently large cutoff `L`,
the data `CorrectionData` used by the correction procedure.
-/

namespace Erdos289

/-- Correction data exists for every sufficiently large cutoff `L`
(from Lemmas 1, 3 and 5 with `ε = 1/10`). -/
theorem correctionData_exists : ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → ∃ C : CorrectionData, C.L = L := by
  classical
  obtain ⟨Q₁, hQ₁⟩ := lemma1 (1 / 10) (by norm_num) (by norm_num) (1 / 80) (by norm_num)
  obtain ⟨Q₃, hQ₃⟩ := lemma3 (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨L₅, hL₅⟩ := lemma5
  refine ⟨max (max Q₁ Q₃) L₅, fun L hL => ?_⟩
  have hQ₁L : Q₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hQ₃L : Q₃ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL₅L : L₅ ≤ L := (le_max_right _ _).trans hL
  obtain ⟨A⟩ := hL₅ L hL₅L
  -- The core existence statement for the fiber `I q`, for a single prime power `q > L`.
  have key : ∀ q : ℕ, IsPrimePow q → L < q →
      ∃ I : Finset ℕ,
        (∀ m ∈ I, (q : ℝ) ^ ((1 : ℝ) / 10) ≤ m ∧ (m : ℝ) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 10)) ∧
        (∀ m ∈ I, Nat.Coprime m q) ∧
        (∀ m ∈ I, 4 ∣ q * m) ∧
        (∀ m ∈ I, Powersmooth (q / 2) (q * m + 1)) ∧
        (∀ r : ZMod q, ∃ S ⊆ I, S.card ≤ s q ∧ ∑ i ∈ S, ((i : ZMod q)⁻¹) = r) := by
    intro q hq hLq
    have hq' := hq
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff q).1 hq
    have hQ1pa : Q₁ ≤ p ^ a := hQ₁L.trans hLq.le
    have hQ3pa : Q₃ ≤ p ^ a := hQ₃L.trans hLq.le
    obtain ⟨I, hI_range, hI_card, hI_prop⟩ := hQ₁ p a hp ha hQ1pa
    have hI_coprime : ∀ m ∈ I, Nat.Coprime m (p ^ a) :=
      fun m hm => (hp.coprime_iff_not_dvd.2 (hI_prop m hm).1).symm.pow_right a
    refine ⟨I, hI_range, hI_coprime, fun m hm => (hI_prop m hm).2.1,
        fun m hm => (hI_prop m hm).2.2, fun r => ?_⟩
    have hcard : ((p ^ a : ℕ) : ℝ) ^ (7 * (1 / 10 : ℝ) / 8) ≤ I.card := by
      have hexp : (7 * (1 / 10 : ℝ) / 8) = (1 / 10 - 1 / 80 : ℝ) := by norm_num
      rw [hexp]; exact hI_card
    obtain ⟨S, hS_sub, hS_card, hS_sum⟩ :=
      hQ₃ (p ^ a) hq' hQ3pa I hI_range hI_coprime hcard r
    refine ⟨S, hS_sub, ?_, hS_sum⟩
    have hexp2 : (1 / 10 : ℝ) / 2 = (1 : ℝ) / 20 := by norm_num
    rw [hexp2] at hS_card
    exact Nat.le_floor hS_card
  -- Package `key` into a genuine function `ℕ → Finset ℕ` using classical choice.
  let Ifun : ℕ → Finset ℕ :=
    fun q => if h : IsPrimePow q ∧ L < q then Classical.choose (key q h.1 h.2) else ∅
  have hIfun_spec : ∀ q, IsPrimePow q → L < q →
      (∀ m ∈ Ifun q, (q : ℝ) ^ ((1 : ℝ) / 10) ≤ m ∧ (m : ℝ) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 10)) ∧
      (∀ m ∈ Ifun q, Nat.Coprime m q) ∧
      (∀ m ∈ Ifun q, 4 ∣ q * m) ∧
      (∀ m ∈ Ifun q, Powersmooth (q / 2) (q * m + 1)) ∧
      (∀ r : ZMod q, ∃ S ⊆ Ifun q, S.card ≤ s q ∧ ∑ i ∈ S, ((i : ZMod q)⁻¹) = r) := by
    intro q hq hLq
    have hEq : Ifun q = Classical.choose (key q hq hLq) :=
      dite_eq_left_of_eq_true (eq_true ⟨hq, hLq⟩)
    rw [hEq]
    exact Classical.choose_spec (key q hq hLq)
  refine ⟨⟨L, A, Ifun, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · exact fun q hq hLq m hm => (hIfun_spec q hq hLq).1 m hm
  · exact fun q hq hLq m hm => (hIfun_spec q hq hLq).2.1 m hm
  · exact fun q hq hLq m hm => (hIfun_spec q hq hLq).2.2.1 m hm
  · exact fun q hq hLq m hm => (hIfun_spec q hq hLq).2.2.2.1 m hm
  · exact fun q hq hLq r => (hIfun_spec q hq hLq).2.2.2.2 r

end Erdos289
