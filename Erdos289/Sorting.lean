import Erdos289.Defs

/-!
# Sorting a `GoodFamily` into the nonadjacent `Statement` form

This file proves `GoodFamily.statement`, converting the existence of a `GoodFamily k`
(a finset of `k` pairwise-separated intervals) into the sorted-sequence form `Statement k`.
-/

namespace Erdos289

open Finset

/-- Any interval occurring in a `GoodFamily` has `lo ≤ hi`. -/
lemma GoodFamily.lo_le_hi {k : ℕ} (G : GoodFamily k) {I : Iv} (hI : I ∈ G.F) :
    I.lo ≤ I.hi := by
  have := G.len I hI
  omega

/-- Distinct intervals in a `GoodFamily` have distinct left endpoints: `Iv.lo` is injective
on `G.F`. -/
lemma GoodFamily.lo_injOn {k : ℕ} (G : GoodFamily k) :
    Set.InjOn Iv.lo (G.F : Set Iv) := by
  intro I hI J hJ hlo
  simp only [Finset.mem_coe] at hI hJ
  by_contra hne
  have hsep := G.sep I hI J hJ hne
  have hIlen := G.len I hI
  have hJlen := G.len J hJ
  unfold Iv.Sep at hsep
  omega

theorem GoodFamily.statement {k : ℕ} (G : GoodFamily k) : Statement k := by
  classical
  -- The set of left endpoints of the intervals in `G.F`.
  set A : Finset ℕ := G.F.image Iv.lo with hA_def
  have hAcard : A.card = k := by
    rw [hA_def, Finset.card_image_of_injOn G.lo_injOn, G.card_eq]
  -- The order embedding enumerating `A` in increasing order.
  set e : Fin k ↪o ℕ := A.orderEmbOfFin hAcard with he_def
  have hmem : ∀ i : Fin k, e i ∈ A := fun i => Finset.orderEmbOfFin_mem A hAcard i
  have hex : ∀ i : Fin k, ∃ I ∈ G.F, Iv.lo I = e i := by
    intro i
    have h := hmem i
    rw [hA_def, Finset.mem_image] at h
    exact h
  -- For each `i`, choose the (unique) interval of `G.F` whose left endpoint is `e i`.
  choose Ic hIcF hIclo using hex
  have hai : ∀ i, Iv.lo (Ic i) = e i := hIclo
  have hIcInj : Function.Injective Ic := by
    intro i j hij
    have : e i = e j := by rw [← hIclo i, ← hIclo j, hij]
    exact e.injective this
  refine ⟨fun i => e i, fun i => (Ic i).hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1 ≤ a i
    intro i
    dsimp only
    rw [← hai i]
    exact G.one_le (Ic i) (hIcF i)
  · -- a i ≤ b i
    intro i
    dsimp only
    rw [← hai i]
    exact G.lo_le_hi (hIcF i)
  · -- b i ≤ 20 * k
    intro i
    dsimp only
    exact G.le_bound (Ic i) (hIcF i)
  · -- b i + 1 - a i = 2 ∨ = 3
    intro i
    dsimp only
    rw [← hai i]
    exact G.len (Ic i) (hIcF i)
  · -- consecutive separation
    intro i j hij
    dsimp only at hij ⊢
    have hlt : i < j := Fin.lt_def.mpr (by omega)
    have haij : e i < e j := e.lt_iff_lt.mpr hlt
    have hne : Ic i ≠ Ic j := by
      intro heq
      rw [← hai i, ← hai j, heq] at haij
      exact lt_irrefl _ haij
    have hsep := G.sep (Ic i) (hIcF i) (Ic j) (hIcF j) hne
    have hlei : Iv.lo (Ic i) ≤ (Ic i).hi := G.lo_le_hi (hIcF i)
    have hlej : Iv.lo (Ic j) ≤ (Ic j).hi := G.lo_le_hi (hIcF j)
    unfold Iv.Sep at hsep
    rw [hai i] at hlei
    rw [hai j] at hlej hsep
    rw [hai i] at hsep
    omega
  · -- sum equality
    have hsurj : Set.SurjOn Ic (↑(Finset.univ : Finset (Fin k))) (↑G.F) := by
      intro I hI
      rw [Finset.mem_coe] at hI
      have hIloA : Iv.lo I ∈ A := by
        rw [hA_def, Finset.mem_image]
        exact ⟨I, hI, rfl⟩
      have hIloA' : Iv.lo I ∈ Finset.image e Finset.univ := by
        rw [Finset.image_orderEmbOfFin_univ A hAcard]
        exact hIloA
      obtain ⟨i, -, hei⟩ := Finset.mem_image.mp hIloA'
      have hlo_eq : Iv.lo (Ic i) = Iv.lo I := by rw [hai i, hei]
      have hIc_eq : Ic i = I :=
        G.lo_injOn (Finset.mem_coe.mpr (hIcF i)) (Finset.mem_coe.mpr hI) hlo_eq
      exact ⟨i, Finset.mem_coe.mpr (Finset.mem_univ i), hIc_eq⟩
    have hstep : ∀ i ∈ (Finset.univ : Finset (Fin k)), mass (e i) ((Ic i).hi) = Iv.mass (Ic i) := by
      intro i _
      show Erdos289.mass (e i) ((Ic i).hi) = Erdos289.mass (Ic i).lo (Ic i).hi
      rw [hai i]
    calc ∑ i, mass (e i) ((Ic i).hi)
        = ∑ I ∈ G.F, Iv.mass I := by
          apply Finset.sum_nbij Ic (fun i _ => hIcF i) (hIcInj.injOn) hsurj hstep
      _ = 1 := G.sum_eq
