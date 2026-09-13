import Erdos289CLT.Basic

/-!
# Assigning centres to stages (paper §4, marriage theorem)

Each stage `q` has a candidate set `cand q` of centres with `k * quota q ≤ |cand q|`,
and every centre belongs to at most `k` stages.  Hall's theorem (applied to
`quota q` copies of each stage) assigns each stage `quota q` of its candidates,
with no centre used twice.
-/

namespace Erdos289.CLT

open Finset

theorem hall_stages {ι : Type*} [DecidableEq ι] (stages : Finset ι) (cand : ι → Finset ℕ)
    (quota : ι → ℕ) (k : ℕ) (hk : 0 < k)
    (hdeg : ∀ q ∈ stages, k * quota q ≤ (cand q).card)
    (hmult : ∀ a : ℕ, (stages.filter (fun q => a ∈ cand q)).card ≤ k) :
    ∃ chosen : ι → Finset ℕ, (∀ q ∈ stages, chosen q ⊆ cand q ∧ (chosen q).card = quota q) ∧
      ∀ q ∈ stages, ∀ q' ∈ stages, q ≠ q' → Disjoint (chosen q) (chosen q') := by
  classical
  -- The index type: one copy `(q, b)` of stage `q` for each `b < quota q`, `q ∈ stages`.
  set pairs : Finset (ι × ℕ) :=
    stages.biUnion (fun q => (Finset.range (quota q)).image (fun b => (q, b))) with hpairs
  have hmem_pairs : ∀ x : ι × ℕ, x ∈ pairs ↔ x.1 ∈ stages ∧ x.2 < quota x.1 := by
    rintro ⟨a, b⟩
    simp only [hpairs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨q, hq, c, hc, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
      exact ⟨hq, hc⟩
    · rintro ⟨ha, hb⟩
      exact ⟨a, ha, b, hb, rfl⟩
  let t : {x // x ∈ pairs} → Finset ℕ := fun p => cand p.1.1
  have hall : ∀ s : Finset {x // x ∈ pairs}, s.card ≤ (s.biUnion t).card := by
    intro s
    set S : Finset ι := s.image (fun p => (p.1 : ι × ℕ).1) with hS
    have hSsub : S ⊆ stages := by
      intro q hq
      rw [hS, Finset.mem_image] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ((hmem_pairs p.1).mp p.2).1
    have hbiUnion : s.biUnion t = S.biUnion cand := by
      rw [hS, Finset.image_biUnion]
    -- (1) `s.card ≤ ∑ q ∈ S, quota q`
    have hs_le : s.card ≤ ∑ q ∈ S, quota q := by
      rw [Finset.card_eq_sum_card_image (fun p : {x // x ∈ pairs} => (p.1 : ι × ℕ).1) s, ← hS]
      apply Finset.sum_le_sum
      intro q _
      have hinj : Set.InjOn (fun p : {x // x ∈ pairs} => (p.1 : ι × ℕ).2)
          (s.filter (fun p => (p.1 : ι × ℕ).1 = q)) := by
        intro p hp p' hp' heq
        simp only [Finset.mem_coe, Finset.mem_filter] at hp hp'
        apply Subtype.ext
        exact Prod.ext (hp.2.trans hp'.2.symm) heq
      have hmaps : ∀ p ∈ s.filter (fun p => (p.1 : ι × ℕ).1 = q),
          (fun p : {x // x ∈ pairs} => (p.1 : ι × ℕ).2) p ∈ Finset.range (quota q) := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        rw [Finset.mem_range, ← hp.2]
        exact ((hmem_pairs p.1).mp p.2).2
      have := Finset.card_le_card_of_injOn _ hmaps hinj
      simpa using this
    -- (2) double counting: `∑ q ∈ S, quota q ≤ (S.biUnion cand).card`
    have hdc : ∑ q ∈ S, (cand q).card
        = ∑ a ∈ S.biUnion cand, (S.filter (fun q => a ∈ cand q)).card := by
      simp_rw [Finset.card_eq_sum_ones]
      exact Finset.sum_comm' (by
        intro x y
        simp only [Finset.mem_filter, Finset.mem_biUnion]
        tauto)
    have hcount : ∑ q ∈ S, quota q ≤ (S.biUnion cand).card := by
      have hmul : k * (∑ q ∈ S, quota q) ≤ k * (S.biUnion cand).card := by
        calc k * ∑ q ∈ S, quota q = ∑ q ∈ S, k * quota q := by rw [Finset.mul_sum]
        _ ≤ ∑ q ∈ S, (cand q).card := Finset.sum_le_sum (fun q hq => hdeg q (hSsub hq))
        _ = ∑ a ∈ S.biUnion cand, (S.filter (fun q => a ∈ cand q)).card := hdc
        _ ≤ ∑ _a ∈ S.biUnion cand, k := Finset.sum_le_sum (fun a _ =>
              le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hSsub)) (hmult a))
        _ = k * (S.biUnion cand).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      exact Nat.le_of_mul_le_mul_left hmul hk
    calc s.card ≤ ∑ q ∈ S, quota q := hs_le
    _ ≤ (S.biUnion cand).card := hcount
    _ = (s.biUnion t).card := by rw [hbiUnion]
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  -- Assemble `chosen` from the matching `f`.
  let filterQ : ι → Finset {x // x ∈ pairs} := fun q => Finset.univ.filter (fun p => (p.1 : ι × ℕ).1 = q)
  have hfilterQ : ∀ q, filterQ q = Finset.univ.filter (fun p => (p.1 : ι × ℕ).1 = q) := fun _ => rfl
  have hcard_filterQ : ∀ q ∈ stages, (filterQ q).card = quota q := by
    intro q hq
    rw [← Finset.card_range (quota q)]
    refine Finset.card_bij'
      (i := fun p (_ : p ∈ filterQ q) => (p.1 : ι × ℕ).2)
      (j := fun b (hb : b ∈ Finset.range (quota q)) =>
        (⟨(q, b), (hmem_pairs (q, b)).mpr ⟨hq, Finset.mem_range.mp hb⟩⟩ : {x // x ∈ pairs}))
      (hi := ?_) (hj := ?_) (left_inv := ?_) (right_inv := ?_)
    · intro p hp
      simp only [hfilterQ, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [Finset.mem_range, ← hp]
      exact ((hmem_pairs p.1).mp p.2).2
    · intro b hb
      simp only [hfilterQ, Finset.mem_filter, Finset.mem_univ, true_and]
    · intro p hp
      simp only [hfilterQ, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      apply Subtype.ext
      exact Prod.ext hp.symm rfl
    · intro b hb
      rfl
  let chosen : ι → Finset ℕ := fun q => (filterQ q).image f
  have hchosen : ∀ q, chosen q = (filterQ q).image f := fun _ => rfl
  refine ⟨chosen, ?_, ?_⟩
  · intro q hq
    constructor
    · intro a ha
      rw [hchosen, Finset.mem_image] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      have hpq : (p.1 : ι × ℕ).1 = q := by
        simp only [hfilterQ, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp
      have := hf_mem p
      rwa [show t p = cand (p.1 : ι × ℕ).1 from rfl, hpq] at this
    · rw [hchosen, Finset.card_image_of_injOn (hf_inj.injOn), hcard_filterQ q hq]
  · intro q hq q' hq' hqq'
    have hdisj : Disjoint (filterQ q) (filterQ q') := by
      rw [hfilterQ, hfilterQ, Finset.disjoint_filter]
      intro p _ hpq
      rw [hpq]
      exact hqq'
    have := (Finset.disjoint_image hf_inj).mpr hdisj
    rw [hchosen, hchosen]
    exact this

end Erdos289.CLT
