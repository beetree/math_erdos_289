import Erdos289.Defs

namespace Erdos289

theorem exists_step_le_of_bounded_increments {f : ℕ → ℚ} {n : ℕ} {τ Δ : ℚ}
    (h0 : f 0 ≤ τ) (hn : τ < f n) (hstep : ∀ i, i < n → f (i + 1) - f i ≤ Δ) :
    ∃ i, i < n ∧ τ - Δ ≤ f i ∧ f i ≤ τ := by
  classical
  have hex : ∃ j, τ < f j := ⟨n, hn⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀spec : τ < f j₀ := Nat.find_spec hex
  have hj₀le : j₀ ≤ n := Nat.find_min' hex hn
  have hj₀pos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · exfalso; rw [h] at hj₀spec; linarith
    · exact h
  refine ⟨j₀ - 1, ?_, ?_, ?_⟩
  · omega
  · have hstep' := hstep (j₀ - 1) (by omega)
    have heq : j₀ - 1 + 1 = j₀ := by omega
    rw [heq] at hstep'
    linarith
  · have hnot : ¬ τ < f (j₀ - 1) := Nat.find_min hex (by omega)
    linarith [not_lt.mp hnot]

/-! ### Helper lemmas about `List.take` and `List.toFinset`, used to build the swap chain. -/

private lemma card_take_toFinset {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {i : ℕ} (hi : i ≤ l.length) : (l.take i).toFinset.card = i := by
  have hnodup : (l.take i).Nodup := List.Nodup.sublist (List.take_sublist i l) hl
  rw [List.toFinset_card_of_nodup hnodup, List.length_take]
  omega

private lemma take_toFinset_subset {α : Type*} [DecidableEq α] (l : List α) (i : ℕ) :
    (l.take i).toFinset ⊆ l.toFinset := by
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  exact List.take_subset i l hx

private lemma notMem_take_toFinset {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {i : ℕ} (hi : i < l.length) : l[i] ∉ (l.take i).toFinset := by
  have hnodup : (l.take (i + 1)).Nodup := List.Nodup.sublist (List.take_sublist (i + 1) l) hl
  rw [List.take_succ_eq_append_getElem hi, List.nodup_append] at hnodup
  intro hmem
  rw [List.mem_toFinset] at hmem
  exact absurd rfl (hnodup.2.2 l[i] hmem l[i] (List.mem_singleton_self _))

private lemma take_succ_toFinset {α : Type*} [DecidableEq α] {l : List α} (_hl : l.Nodup)
    {i : ℕ} (hi : i < l.length) :
    (l.take (i + 1)).toFinset = insert l[i] (l.take i).toFinset := by
  apply Finset.ext
  intro x
  rw [List.take_succ_eq_append_getElem hi]
  simp only [List.mem_toFinset, List.mem_append, List.mem_singleton, Finset.mem_insert]
  tauto

/-- Concrete finset swap-chain version: given a small set `A` disjoint from a large reservoir
`Far`, we can find a set `S` of the target size `M` obtained from `A` by swapping in elements of
`Far`, whose reciprocal mass lands in the window `(τ - Δ, τ]`. -/
theorem exists_subset_card_mass {α : Type*} [DecidableEq α] (A Far : Finset α) (μ : α → ℚ) (M : ℕ) (τ Δ : ℚ)
    (hdisj : Disjoint A Far) (hA : A.card < M) (hFar : M ≤ Far.card)
    (hfar_small : ∀ T ⊆ Far, T.card = M → ∑ x ∈ T, μ x ≤ τ)
    (hbig : ∀ T ⊆ Far, T.card = M - A.card → τ < ∑ x ∈ A, μ x + ∑ x ∈ T, μ x)
    (hswap : ∀ a ∈ A, ∀ b ∈ Far, μ a - μ b ≤ Δ) :
    ∃ S ⊆ A ∪ Far, S.card = M ∧ τ - Δ ≤ ∑ x ∈ S, μ x ∧ ∑ x ∈ S, μ x ≤ τ := by
  classical
  obtain ⟨T0, hT0sub, hT0card⟩ := Finset.exists_subset_card_eq hFar
  set r := A.card with hr_def
  have hr_lt_M : r < M := hA
  set la := A.toList with hla_def
  set lt := T0.toList with hlt_def
  have hla_nodup : la.Nodup := A.nodup_toList
  have hla_toFinset : la.toFinset = A := A.toList_toFinset
  have hla_length : la.length = r := A.length_toList
  have hlt_nodup : lt.Nodup := T0.nodup_toList
  have hlt_toFinset : lt.toFinset = T0 := T0.toList_toFinset
  have hlt_length : lt.length = M := by rw [T0.length_toList, hT0card]
  set lb := lt.take r with hlb_def
  have hlb_length : lb.length = r := by
    rw [hlb_def, List.length_take, hlt_length]; omega
  have hlb_nodup : lb.Nodup := List.Nodup.sublist (List.take_sublist r lt) hlt_nodup
  have hlb_toFinset_subset_T0 : lb.toFinset ⊆ T0 := by
    rw [hlb_def, ← hlt_toFinset]; exact take_toFinset_subset lt r
  have hlb_toFinset_subset_Far : lb.toFinset ⊆ Far := hlb_toFinset_subset_T0.trans hT0sub
  -- The swap-chain reciprocal-mass function.
  set f : ℕ → ℚ := fun i => ∑ x ∈ (la.take i).toFinset ∪ (T0 \ (lb.take i).toFinset), μ x with hf_def
  -- Basic subset/disjointness facts for `i ≤ r`.
  have hBsub : ∀ i, (la.take i).toFinset ⊆ A := fun i => hla_toFinset ▸ take_toFinset_subset la i
  have hCsub : ∀ i, (lb.take i).toFinset ⊆ T0 := fun i => by
    rw [hlb_def]
    exact (take_toFinset_subset lb i).trans hlb_toFinset_subset_T0
  have hDisj : ∀ i, Disjoint ((la.take i).toFinset) (T0 \ (lb.take i).toFinset) := fun i =>
    Disjoint.mono (hBsub i) (Finset.sdiff_subset.trans hT0sub) hdisj
  have hCcard : ∀ i, i ≤ r → (lb.take i).toFinset.card = i := fun i _ =>
    card_take_toFinset hlb_nodup (by rw [hlb_length]; omega)
  -- f 0 ≤ τ
  have hf0 : f 0 ≤ τ := by
    have : f 0 = ∑ x ∈ T0, μ x := by simp [hf_def]
    rw [this]
    exact hfar_small T0 hT0sub hT0card
  have hla_take_r : la.take r = la := by
    apply List.take_of_length_le; rw [hla_length]
  have hlb_take_r : lb.take r = lb := by
    apply List.take_of_length_le; rw [hlb_length]
  have hlb_toFinset_card : lb.toFinset.card = r := by
    rw [List.toFinset_card_of_nodup hlb_nodup, hlb_length]
  have hDisjR : Disjoint A (T0 \ lb.toFinset) :=
    hdisj.mono_right (Finset.sdiff_subset.trans hT0sub)
  have hfr : τ < f r := by
    have heq : f r = ∑ x ∈ A, μ x + ∑ x ∈ (T0 \ lb.toFinset), μ x := by
      simp only [hf_def, hla_take_r, hlb_take_r, hla_toFinset]
      exact Finset.sum_union hDisjR
    rw [heq]
    apply hbig
    · exact Finset.sdiff_subset.trans hT0sub
    · rw [Finset.card_sdiff_of_subset hlb_toFinset_subset_T0, hT0card, hlb_toFinset_card]
  have hstep : ∀ i, i < r → f (i + 1) - f i ≤ Δ := by
    intro i hi
    have hi' : i < la.length := by rw [hla_length]; exact hi
    have hi'' : i < lb.length := by rw [hlb_length]; exact hi
    have hstepB : (la.take (i + 1)).toFinset = insert la[i] (la.take i).toFinset :=
      take_succ_toFinset hla_nodup hi'
    have hnotBmem : la[i] ∉ (la.take i).toFinset := notMem_take_toFinset hla_nodup hi'
    have hstepC : (lb.take (i + 1)).toFinset = insert lb[i] (lb.take i).toFinset :=
      take_succ_toFinset hlb_nodup hi''
    have hnotCmem : lb[i] ∉ (lb.take i).toFinset := notMem_take_toFinset hlb_nodup hi''
    have hlaimem : la[i] ∈ A := by
      rw [← hla_toFinset, List.mem_toFinset]; exact List.getElem_mem hi'
    have hlbi_in_T0 : lb[i] ∈ T0 :=
      hlb_toFinset_subset_T0 (List.mem_toFinset.mpr (List.getElem_mem hi''))
    have hlbimem : lb[i] ∈ Far := hT0sub hlbi_in_T0
    have hlbimemT0C : lb[i] ∈ T0 \ (lb.take i).toFinset :=
      Finset.mem_sdiff.mpr ⟨hlbi_in_T0, hnotCmem⟩
    have hf_i : f i = ∑ x ∈ (la.take i).toFinset, μ x + ∑ x ∈ (T0 \ (lb.take i).toFinset), μ x := by
      simp only [hf_def]; exact Finset.sum_union (hDisj i)
    have hf_i1 : f (i + 1) = ∑ x ∈ (la.take (i + 1)).toFinset, μ x
        + ∑ x ∈ (T0 \ (lb.take (i + 1)).toFinset), μ x := by
      simp only [hf_def]; exact Finset.sum_union (hDisj (i + 1))
    have hsdiff_insert : T0 \ (lb.take (i + 1)).toFinset
        = (T0 \ (lb.take i).toFinset).erase lb[i] := by
      rw [hstepC, Finset.sdiff_insert]
    have hsumB : ∑ x ∈ (la.take (i + 1)).toFinset, μ x
        = μ la[i] + ∑ x ∈ (la.take i).toFinset, μ x := by
      rw [hstepB, Finset.sum_insert hnotBmem]
    have hsumC : ∑ x ∈ (T0 \ (lb.take i).toFinset), μ x
        = μ lb[i] + ∑ x ∈ (T0 \ (lb.take (i + 1)).toFinset), μ x := by
      rw [hsdiff_insert]
      exact (Finset.add_sum_erase (T0 \ (lb.take i).toFinset) μ hlbimemT0C).symm
    have hswap' := hswap la[i] hlaimem lb[i] hlbimem
    rw [hf_i, hf_i1]
    linarith [hsumB, hsumC]
  obtain ⟨i, hir, hlow, hhigh⟩ := exists_step_le_of_bounded_increments hf0 hfr hstep
  have hile : i ≤ r := hir.le
  have hBi_sub : (la.take i).toFinset ⊆ A := hBsub i
  have hCi_sub : (lb.take i).toFinset ⊆ T0 := hCsub i
  have hBi_card : (la.take i).toFinset.card = i := card_take_toFinset hla_nodup (by rw [hla_length]; omega)
  have hCi_card : (lb.take i).toFinset.card = i := hCcard i hile
  refine ⟨(la.take i).toFinset ∪ (T0 \ (lb.take i).toFinset), ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (hBi_sub hx)
    · exact Finset.mem_union_right _ (hT0sub (Finset.mem_sdiff.mp hx).1)
  · rw [Finset.card_union_of_disjoint (hDisj i), Finset.card_sdiff_of_subset hCi_sub,
      hT0card, hCi_card, hBi_card]
    omega
  · exact hlow
  · exact hhigh

end Erdos289
