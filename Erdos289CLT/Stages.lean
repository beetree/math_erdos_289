import Erdos289CLT.Transfer
import Erdos289CLT.Hall
import Erdos289CLT.Counts

/-!
# Enlarging the residue group and the count range (paper §4)

`choose_pools`: Hall's theorem assigns `3 s(q)` distinct centres to every prime-power
stage `q ∈ (B, X]` (a centre belongs to at most three stages).
`iterate_transfer`: iterating `transfer` over all levels `B < n ≤ X` (trivial step at
non-prime-powers, where `G_n` does not change) produces a family at level `X` with
count interval `[u₀ + Ucount B X, v₀ + 2 Ucount B X]`.
-/

namespace Erdos289.CLT

open Finset

theorem choose_pools (B X : ℕ) (cand : ℕ → Finset ℕ)
    (hdeg : ∀ q, IsPrimePow q → B < q → q ≤ X → 9 * s q ≤ (cand q).card)
    (hmult : ∀ a q, IsPrimePow q → B < q → q ≤ X → a ∈ cand q →
      lpp (a - 1) = q ∨ lpp a = q ∨ lpp (a + 1) = q) :
    ∃ chosen : ℕ → Finset ℕ,
      (∀ q, IsPrimePow q → B < q → q ≤ X → chosen q ⊆ cand q ∧ (chosen q).card = 3 * s q) ∧
      ∀ q q', q ≠ q' → Disjoint (chosen q) (chosen q') := by
  classical
  set stages : Finset ℕ := (Finset.Ioc B X).filter IsPrimePow with hstages
  have hmem_stages : ∀ q, q ∈ stages ↔ IsPrimePow q ∧ B < q ∧ q ≤ X := by
    intro q
    simp only [hstages, Finset.mem_filter, Finset.mem_Ioc]
    tauto
  have hdeg' : ∀ q ∈ stages, 3 * (3 * s q) ≤ (cand q).card := by
    intro q hq
    obtain ⟨hpp, hBq, hqX⟩ := (hmem_stages q).mp hq
    have := hdeg q hpp hBq hqX
    omega
  have hmult' : ∀ a : ℕ, (stages.filter (fun q => a ∈ cand q)).card ≤ 3 := by
    intro a
    have hsub : stages.filter (fun q => a ∈ cand q) ⊆
        ({lpp (a - 1), lpp a, lpp (a + 1)} : Finset ℕ) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqs, hqa⟩ := hq
      obtain ⟨hpp, hBq, hqX⟩ := (hmem_stages q).mp hqs
      have := hmult a q hpp hBq hqX hqa
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    calc (stages.filter (fun q => a ∈ cand q)).card
        ≤ ({lpp (a - 1), lpp a, lpp (a + 1)} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 3 := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
          simp
  obtain ⟨chosen', hchosen'_sub, hchosen'_disj⟩ :=
    hall_stages stages cand (fun q => 3 * s q) 3 (by norm_num) hdeg' hmult'
  refine ⟨fun q => if q ∈ stages then chosen' q else ∅, ?_, ?_⟩
  · intro q hpp hBq hqX
    have hqs : q ∈ stages := (hmem_stages q).mpr ⟨hpp, hBq, hqX⟩
    simp only [hqs, if_true]
    exact hchosen'_sub q hqs
  · intro q q' hqq'
    by_cases hqs : q ∈ stages <;> by_cases hqs' : q' ∈ stages <;>
      simp only [hqs, hqs', if_true, if_false]
    · exact hchosen'_disj q hqs q' hqs' hqq'
    · simp
    · simp
    · simp

private theorem iterate_transfer_aux (B X : ℕ) (hBX : B ≤ X) (hB : 1 ≤ B)
    (hBpow : B = 2 ^ Nat.log 2 B)
    (Fm₀ : Fam) (h₀n : Fm₀.n = B) (h₀w : Fm₀.u + 2 * s B ≤ Fm₀.v)
    (pool : ℕ → Finset Iv)
    (hcard : ∀ q, IsPrimePow q → B < q → q ≤ X → (pool q).card = 3 * s q)
    (hpair : ∀ q, ∀ I ∈ pool q, 2 ≤ I.lo ∧ I.hi = I.lo + 1)
    (hsep : ∀ q q', ∀ I ∈ pool q, ∀ J ∈ pool q', I ≠ J → Iv.Sep I J)
    (hdisj : ∀ q q', q ≠ q' → Disjoint (pool q) (pool q'))
    (hsep_old : ∀ q, ∀ I ∈ Fm₀.supp, ∀ J ∈ pool q, Iv.Sep I J)
    (hG : ∀ q, ∀ J ∈ pool q, InG q J.mass)
    (hcover : ∀ q, IsPrimePow q → B < q → q ≤ X → ∀ T ⊆ pool q, T.card = s q →
      ∀ z : ℚ, InG q z → ∃ Cs ⊆ T, InG (q - 1) (z - ∑ J ∈ Cs, J.mass)) :
    ∀ n, B ≤ n → n ≤ X → ∃ Fm : Fam, Fm.β = Fm₀.β ∧ Fm.n = n ∧ Fm.S = Fm₀.S ∧
      Fm.u = Fm₀.u + Ucount B n ∧ Fm.v = Fm₀.v + 2 * Ucount B n ∧
      Fm.bound = Fm₀.bound + ∑ q ∈ (Finset.Ioc B n).filter IsPrimePow, ∑ J ∈ pool q, J.mass ∧
      Fm.supp = Fm₀.supp ∪ ((Finset.Ioc B n).filter IsPrimePow).biUnion pool := by
  intro n hBn
  induction n, hBn using Nat.le_induction with
  | base =>
    intro _
    refine ⟨Fm₀, rfl, h₀n, rfl, ?_, ?_, ?_, ?_⟩
    · simp [Ucount]
    · simp [Ucount]
    · simp
    · simp
  | succ n hBn ih =>
    intro hn1X
    have hnX : n ≤ X := by omega
    obtain ⟨Fm, hFmβ, hFmn, hFmS, hFmu, hFmv, hFmbound, hFmsupp⟩ := ih hnX
    by_cases hpp : IsPrimePow (n + 1)
    · -- prime-power step: split `pool (n+1)` into `cover` (size `s (n+1)`) and `further`.
      have hBq : B < n + 1 := by omega
      have hqX : n + 1 ≤ X := hn1X
      have hcardq : (pool (n + 1)).card = 3 * s (n + 1) := hcard (n + 1) hpp hBq hqX
      have hslecard : s (n + 1) ≤ (pool (n + 1)).card := by omega
      obtain ⟨cover, hcoversub, hcovercard⟩ := Finset.exists_subset_card_eq hslecard
      set further := pool (n + 1) \ cover with hfurther
      have hunion : cover ∪ further = pool (n + 1) := Finset.union_sdiff_of_subset hcoversub
      have hdisjcf : Disjoint cover further := Finset.disjoint_sdiff
      have hfurthercard : further.card = 2 * s (n + 1) := by
        have := Finset.card_sdiff_of_subset hcoversub
        rw [← hfurther] at this
        omega
      have hpair' : ∀ I ∈ cover ∪ further, 2 ≤ I.lo ∧ I.hi = I.lo + 1 := by
        rw [hunion]; exact hpair (n + 1)
      have hsep' : ∀ I ∈ cover ∪ further, ∀ J ∈ cover ∪ further, I ≠ J → Iv.Sep I J := by
        rw [hunion]; exact hsep (n + 1) (n + 1)
      have hG' : ∀ J ∈ cover ∪ further, InG (n + 1) J.mass := by
        rw [hunion]; exact hG (n + 1)
      have hsep_old' : ∀ I ∈ Fm.supp, ∀ J ∈ cover ∪ further, Iv.Sep I J := by
        intro I hI J hJ
        rw [hunion] at hJ
        rw [hFmsupp] at hI
        rcases Finset.mem_union.mp hI with hI0 | hIold
        · exact hsep_old (n + 1) I hI0 J hJ
        · obtain ⟨q', hq's, hIq'⟩ := Finset.mem_biUnion.mp hIold
          obtain ⟨_, _, hq'n⟩ := Finset.mem_filter.mp hq's |>.imp_left Finset.mem_Ioc.mp
          have hq'ne : q' ≠ n + 1 := by
            rw [Finset.mem_filter, Finset.mem_Ioc] at hq's
            omega
          have hIJ : I ≠ J := by
            rintro rfl
            exact (Finset.disjoint_left.mp (hdisj q' (n + 1) hq'ne) hIq') hJ
          exact hsep (q') (n + 1) I hIq' J hJ hIJ
      have hcover' : ∀ z : ℚ, InG (n + 1) z →
          ∃ Cs ⊆ cover, InG Fm.n (z - ∑ J ∈ Cs, J.mass) := by
        intro z hz
        have := hcover (n + 1) hpp hBq hqX cover hcoversub hcovercard z hz
        rwa [hFmn]
      have hwidth' : Fm.u + cover.card ≤ Fm.v := by
        have hswidth : s (n + 1) ≤ 2 * s B + Ucount B n := s_succ_le_width hB hBpow hBn
        rw [hFmu, hFmv, hcovercard]
        omega
      obtain ⟨Fm', hFm'β, hFm'n, hFm'u, hFm'v, hFm'supp, hFm'S, hFm'bound⟩ :=
        transfer Fm (n' := n + 1) (by omega) cover further hdisjcf hpair' hsep' hsep_old' hG'
          hcover' hwidth'
      refine ⟨Fm', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hFm'β, hFmβ]
      · rw [hFm'n]
      · rw [hFm'S, hFmS]
      · rw [hFm'u, hFmu, hcovercard, Ucount_succ_of_isPrimePow hBn hpp]; ring
      · rw [hFm'v, hFmv, hfurthercard, Ucount_succ_of_isPrimePow hBn hpp]; ring
      · have hmem : (n + 1) ∉ (Finset.Ioc B n).filter IsPrimePow := by
          simp [Finset.mem_filter]
        have hfset : (Finset.Ioc B (n + 1)).filter IsPrimePow =
            insert (n + 1) ((Finset.Ioc B n).filter IsPrimePow) := by
          rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hBn, Finset.filter_insert, if_pos hpp]
        rw [hFm'bound, hFmbound, hfset, Finset.sum_insert hmem, hunion]
        ring
      · have hmem : (n + 1) ∉ (Finset.Ioc B n).filter IsPrimePow := by
          simp [Finset.mem_filter]
        have hfset : (Finset.Ioc B (n + 1)).filter IsPrimePow =
            insert (n + 1) ((Finset.Ioc B n).filter IsPrimePow) := by
          rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hBn, Finset.filter_insert, if_pos hpp]
        rw [hFm'supp, hFmsupp, hfset, Finset.biUnion_insert, hunion]
        ext I
        simp only [Finset.mem_union]
        tauto
    · -- non-prime-power step: `G_{n+1} = G_n`, nothing changes.
      have hcover' : ∀ z : ℚ, InG (n + 1) z →
          ∃ Cs ⊆ (∅ : Finset Iv), InG Fm.n (z - ∑ J ∈ Cs, J.mass) := by
        intro z hz
        refine ⟨∅, subset_rfl, ?_⟩
        rw [hFmn, Finset.sum_empty, sub_zero]
        exact (InG_succ_iff_of_not_isPrimePow hpp).mp hz
      have hwidth' : Fm.u + (∅ : Finset Iv).card ≤ Fm.v := by
        rw [hFmu, hFmv]
        simp only [Finset.card_empty, add_zero]
        have hsB : 0 ≤ 2 * s B := by omega
        omega
      obtain ⟨Fm', hFm'β, hFm'n, hFm'u, hFm'v, hFm'supp, hFm'S, hFm'bound⟩ :=
        transfer Fm (n' := n + 1) (by omega) (∅ : Finset Iv) (∅ : Finset Iv)
          (by simp) (by simp) (by simp) (by simp) (by simp) hcover' hwidth'
      have hfset : (Finset.Ioc B (n + 1)).filter IsPrimePow =
          (Finset.Ioc B n).filter IsPrimePow := by
        rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hBn, Finset.filter_insert, if_neg hpp]
      refine ⟨Fm', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hFm'β, hFmβ]
      · rw [hFm'n]
      · rw [hFm'S, hFmS]
      · rw [hFm'u, hFmu, Ucount_succ_of_not_isPrimePow hBn hpp]; simp
      · rw [hFm'v, hFmv, Ucount_succ_of_not_isPrimePow hBn hpp]; simp
      · rw [hFm'bound, hFmbound, hfset]
        simp
      · rw [hFm'supp, hFmsupp, hfset]
        simp

theorem iterate_transfer (B X : ℕ) (hBX : B ≤ X) (hB : 1 ≤ B) (hBpow : B = 2 ^ Nat.log 2 B)
    (Fm₀ : Fam) (h₀n : Fm₀.n = B) (h₀w : Fm₀.u + 2 * s B ≤ Fm₀.v)
    (pool : ℕ → Finset Iv)
    (hcard : ∀ q, IsPrimePow q → B < q → q ≤ X → (pool q).card = 3 * s q)
    (hpair : ∀ q, ∀ I ∈ pool q, 2 ≤ I.lo ∧ I.hi = I.lo + 1)
    (hsep : ∀ q q', ∀ I ∈ pool q, ∀ J ∈ pool q', I ≠ J → Iv.Sep I J)
    (hdisj : ∀ q q', q ≠ q' → Disjoint (pool q) (pool q'))
    (hsep_old : ∀ q, ∀ I ∈ Fm₀.supp, ∀ J ∈ pool q, Iv.Sep I J)
    (hG : ∀ q, ∀ J ∈ pool q, InG q J.mass)
    (hcover : ∀ q, IsPrimePow q → B < q → q ≤ X → ∀ T ⊆ pool q, T.card = s q →
      ∀ z : ℚ, InG q z → ∃ Cs ⊆ T, InG (q - 1) (z - ∑ J ∈ Cs, J.mass)) :
    ∃ Fm : Fam, Fm.β = Fm₀.β ∧ Fm.n = X ∧ Fm.S = Fm₀.S ∧
      Fm.u = Fm₀.u + Ucount B X ∧ Fm.v = Fm₀.v + 2 * Ucount B X ∧
      Fm.bound = Fm₀.bound + ∑ q ∈ (Finset.Ioc B X).filter IsPrimePow, ∑ J ∈ pool q, J.mass := by
  obtain ⟨Fm, hβ, hn, hS, hu, hv, hbound, _⟩ :=
    iterate_transfer_aux B X hBX hB hBpow Fm₀ h₀n h₀w pool hcard hpair hsep hdisj hsep_old hG
      hcover X hBX (le_refl X)
  exact ⟨Fm, hβ, hn, hS, hu, hv, hbound⟩

end Erdos289.CLT
