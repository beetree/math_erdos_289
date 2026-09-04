import Erdos289.DescentS
import Erdos289.SignedF1
import Erdos289.SignedF2
import Erdos289.SignedD1
import Erdos289.Lemma5S
import Erdos289.Lemma3
import Erdos289.SignedTail

/-!
# Correction data exists (`correctionDataS_exists`), assembled from Lemmas F1, F2, D1, 5S, 3

This file assembles `Erdos289.CorrectionDataS ((1 : ℝ) / 10)` for every sufficiently large
cutoff `L` and every `H ≥ L`, from:

* Lemma F1 (`Erdos289.lemmaF1`): individually valid signed fibers of size
  `≥ q^ε / (8 V(q))`.
* Lemma F2 (`Erdos289.lemmaF2`): thinning a family of large fibers to a quarter of their size
  while keeping all retained pairs mutually separated.
* Lemma 5S (`Erdos289.lemma5S`): existence of an auxiliary family avoiding the enlarged
  endpoint set.
* Lemma 3, wide form (`Erdos289.lemma3_wide`): the covering lemma for multipliers in
  `(0, 8 q^ε]`.
* The eventual smallness of the divisor envelope (`Erdos289.Eenv_le_eventually`,
  `Erdos289.SignedD1G.venv_le`).

This file proves `Erdos289.correctionDataS_exists` in full; it is the correction-data input
consumed by `Erdos289.descentS` (`Erdos289/DescentS.lean`) and by the assembly
(`Erdos289/AssemblyS2.lean`).
-/

namespace Erdos289

open Finset Filter

/-- A trivially valid signed fiber with no multipliers, used as a default value outside the
range where Lemma F1 applies. -/
def SignedFiber.empty (ε : ℝ) (q : ℕ) : SignedFiber ε q where
  I := ∅
  σ := fun _ => 1
  sign := by simp
  lower := by simp
  upper := by simp
  lt := by simp
  coprime := by simp
  two_le := by simp
  smooth := by simp
  four := by simp
  slot_inj := by
    intro a ha _b _hb _
    simp at ha

/-- **Correction data exists** for every sufficiently large cutoff `L` and every `H ≥ L`
(from Lemmas F1, F2, D1, `lemma5S`, and `lemma3_wide` with `C = 8`, all at `ε = 1/10`). -/
theorem correctionDataS_exists :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → ∀ H, L ≤ H →
      ∃ C : CorrectionDataS ((1 : ℝ) / 10), C.L = L ∧ C.H = H := by
  classical
  set ε : ℝ := (1 : ℝ) / 10 with hεdef
  have hε0 : (0 : ℝ) < ε := by rw [hεdef]; norm_num
  have hε1 : ε < 1 := by rw [hεdef]; norm_num
  -- Lemma F1.
  obtain ⟨Q₁, hQ₁⟩ := lemmaF1 ε hε0 hε1
  -- Lemma F2.
  obtain ⟨L₂, hL₂⟩ := lemmaF2 ε hε0 hε1
  -- Lemma 5S.
  obtain ⟨L₃, hL₃⟩ := lemma5S ε hε0 hε1
  -- Lemma 3, wide form, with C = 8.
  obtain ⟨Q₄, hQ₄⟩ := lemma3_wide ε hε0 hε1 8 (by norm_num)
  -- The divisor envelope `Eenv ε q ≤ q ^ (1/40)` eventually.
  obtain ⟨Q₅, hQ₅⟩ :=
    Filter.eventually_atTop.mp (Eenv_le_eventually ε hε0 hε1 ((1 : ℝ) / 40) (by norm_num))
  -- `8 * Venv ε q ≤ q ^ (ε / 16)` eventually.
  have hVenvBound : ∀ᶠ q : ℕ in Filter.atTop, 8 * (Venv ε q : ℝ) ≤ (q : ℝ) ^ (ε / 16) := by
    have h1 := SignedD1G.venv_le ε hε0 (ε / 32) (div_pos hε0 (by norm_num))
    have h2 := SignedTail.eventually_rpow_dominates (ε / 32) (ε / 16) 8 0
      (div_pos hε0 (by norm_num)) (by linarith [hε0])
    filter_upwards [h1, h2] with q hV hD
    have hstep : 8 * (Venv ε q : ℝ) ≤ 8 * (q : ℝ) ^ (ε / 32) := by nlinarith [hV]
    linarith [hstep, hD]
  obtain ⟨Q₆, hQ₆⟩ := Filter.eventually_atTop.mp hVenvBound
  refine ⟨Q₁ + L₂ + L₃ + Q₄ + Q₅ + Q₆, fun L hL H hLH => ?_⟩
  have hLQ₁ : Q₁ ≤ L := by omega
  have hLL₂ : L₂ ≤ L := by omega
  have hLL₃ : L₃ ≤ L := by omega
  have hLQ₄ : Q₄ ≤ L := by omega
  have hLQ₅ : Q₅ ≤ L := by omega
  have hLQ₆ : Q₆ ≤ L := by omega
  -- The signed fibers: from Lemma F1 when available, empty otherwise.
  let F : (q : ℕ) → SignedFiber ε q := fun q =>
    if h : IsPrimePow q ∧ Q₁ ≤ q then (hQ₁ q h.1 h.2).choose else SignedFiber.empty ε q
  -- For `q` prime power with `L < q`, the fiber count is at least `q ^ (15 ε / 16)`.
  have hFcard : ∀ q : ℕ, IsPrimePow q → L < q → (q : ℝ) ^ (15 * ε / 16) ≤ ((F q).I.card : ℝ) := by
    intro q hpp hLq
    have hq1 : Q₁ ≤ q := le_trans hLQ₁ hLq.le
    have hq6 : Q₆ ≤ q := le_trans hLQ₆ hLq.le
    have hq2 : 2 ≤ q := hpp.two_le
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hVbound : 8 * (Venv ε q : ℝ) ≤ (q : ℝ) ^ (ε / 16) := hQ₆ q hq6
    have hV1 : (1 : ℝ) ≤ (Venv ε q : ℝ) := by
      exact_mod_cast SignedD1G.one_le_Venv ε hε0 (show 1 ≤ q by omega)
    have hdenpos : (0 : ℝ) < 8 * (Venv ε q : ℝ) := by linarith [hV1]
    have hkey : (q : ℝ) ^ (15 * ε / 16) * (8 * (Venv ε q : ℝ)) ≤ (q : ℝ) ^ ε := by
      calc (q : ℝ) ^ (15 * ε / 16) * (8 * (Venv ε q : ℝ))
          ≤ (q : ℝ) ^ (15 * ε / 16) * (q : ℝ) ^ (ε / 16) :=
            mul_le_mul_of_nonneg_left hVbound (Real.rpow_nonneg hqpos.le _)
        _ = (q : ℝ) ^ ε := by
            rw [← Real.rpow_add hqpos]; congr 1; ring
    have hgoal : (q : ℝ) ^ (15 * ε / 16) ≤ (q : ℝ) ^ ε / (8 * (Venv ε q : ℝ)) := by
      rw [le_div_iff₀ hdenpos]; exact hkey
    have hFeq : F q = (hQ₁ q hpp hq1).choose :=
      dite_eq_left_of_eq_true (eq_true ⟨hpp, hq1⟩)
    rw [hFeq]
    exact le_trans hgoal (hQ₁ q hpp hq1).choose_spec
  -- Lemma F2: retained fibers `J q`, pairwise separated.
  obtain ⟨J, hJ_sub, hJ_quarter, hJ_sep⟩ :=
    hL₂ L hLL₂ H hLH F (fun q hpp hLq _hqH => hFcard q hpp hLq)
  -- The retained count is at least `q ^ (7 ε / 8)`.
  have hJ_card : ∀ q, IsPrimePow q → L < q → q ≤ H → (q : ℝ) ^ (7 * ε / 8) ≤ ((J q).card : ℝ) := by
    intro q hpp hLq hqH
    have hFc := hFcard q hpp hLq
    have hq4 := hJ_quarter q hpp hLq hqH
    have hq6 : Q₆ ≤ q := le_trans hLQ₆ hLq.le
    have hq2 : 2 ≤ q := hpp.two_le
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hVbound : 8 * (Venv ε q : ℝ) ≤ (q : ℝ) ^ (ε / 16) := hQ₆ q hq6
    have hV1 : (1 : ℝ) ≤ (Venv ε q : ℝ) := by
      exact_mod_cast SignedD1G.one_le_Venv ε hε0 (show 1 ≤ q by omega)
    have h4 : (4 : ℝ) ≤ (q : ℝ) ^ (ε / 16) := by linarith [hVbound, hV1]
    have hkey : 4 * (q : ℝ) ^ (7 * ε / 8) ≤ (q : ℝ) ^ (15 * ε / 16) := by
      calc 4 * (q : ℝ) ^ (7 * ε / 8)
          ≤ (q : ℝ) ^ (ε / 16) * (q : ℝ) ^ (7 * ε / 8) :=
            mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hqpos.le _)
        _ = (q : ℝ) ^ (15 * ε / 16) := by
            rw [← Real.rpow_add hqpos]; congr 1; ring
    have hq4' : ((F q).I.card : ℝ) ≤ 4 * ((J q).card : ℝ) := by linarith [hq4]
    have hcomb : 4 * (q : ℝ) ^ (7 * ε / 8) ≤ 4 * ((J q).card : ℝ) := by
      linarith [hkey, hFc, hq4']
    linarith [hcomb]
  -- Covering, via Lemma 3 (wide form, `C = 8`).
  have hcover : ∀ q, IsPrimePow q → L < q → q ≤ H → ∀ r : ZMod q,
      ∃ S ⊆ J q, S.card ≤ s q ∧ ∑ i ∈ S, ((i : ZMod q)⁻¹) = r := by
    intro q hpp hLq hqH r
    have hq2 : 2 ≤ q := hpp.two_le
    have hq4 : Q₄ ≤ q := le_trans hLQ₄ hLq.le
    have hI1 : ∀ i ∈ J q, 0 < i ∧ (i : ℝ) ≤ 8 * (q : ℝ) ^ ε := by
      intro i hi
      have hiF : i ∈ (F q).I := hJ_sub q hi
      have hlow := (F q).lower i hiF
      have hup := (F q).upper i hiF
      have hRpos : (0 : ℝ) < Rq ε q := SignedD1G.Rq_pos ε hε0 hq2
      have hipos : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le hRpos hlow
      exact ⟨by exact_mod_cast hipos, hup⟩
    have hI2 : ∀ i ∈ J q, Nat.Coprime i q := fun i hi => (F q).coprime i (hJ_sub q hi)
    have hI3 : (q : ℝ) ^ (7 * ε / 8) ≤ ((J q).card : ℝ) := hJ_card q hpp hLq hqH
    obtain ⟨S, hSsub, hScard, hSsum⟩ := hQ₄ q hpp hq4 (J q) hI1 hI2 hI3 r
    refine ⟨S, hSsub, ?_, hSsum⟩
    have heq : ε / 2 = (1 : ℝ) / 20 := by rw [hεdef]; norm_num
    rw [heq] at hScard
    exact Nat.le_floor hScard
  -- The divisor envelope is small beyond the cutoff.
  have hE_small : ∀ q, IsPrimePow q → L < q → Eenv ε q ≤ (q : ℝ) ^ ((1 : ℝ) / 40) := by
    intro q hpp hLq
    exact hQ₅ q (le_trans hLQ₅ hLq.le)
  -- The auxiliary family, from Lemma 5S.
  obtain ⟨A⟩ := hL₃ L hLL₃
  exact ⟨⟨L, H, hLH, A, F, J, hJ_sub, hJ_card, hJ_sep, hcover, hE_small⟩, rfl, rfl⟩

end Erdos289
