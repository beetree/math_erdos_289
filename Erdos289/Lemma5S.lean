import Erdos289.SignedDefs
import Erdos289.SignedD1
import Erdos289.Lemma5
import Erdos289.Lemma4

/-!
# Lemma 5 (signed variant): auxiliary pairs avoiding the enlarged endpoint set

Adaptation of `Erdos289/Lemma5.lean` to the signed correction fibers of
`docs/elementary_replacements.md` (Sections 3-4). The only structural change from `AuxFamily` is
that the `sep_corr` field (separation from `PstarPairs L`) is replaced by `AuxFamilyS.avoid`
(distance more than two from every element of the enlarged endpoint set `PstarSigned ε L`).

Density of `PstarSigned ε L` (Lemma D1 of the replacement document) is not proved here: it is
being proved in parallel in `Erdos289/SignedD1.lean`. We take it as a hypothesis `hD1`, prove the
construction lemma `lemma5S_of` and the density corollary `USigned_density` from it, and only
assemble the unconditional `lemma5S` if `SignedD1.lean` compiles.
-/

set_option maxHeartbeats 4000000

namespace Erdos289.Lemma5S

open Finset Erdos289

/-- `PstarSigned` shrinks as the cutoff `L` increases: a larger cutoff imposes a stronger
requirement `L < q` on the prime power label. -/
theorem PstarSigned_subset (ε : ℝ) {L L' : ℕ} (hL : L ≤ L') :
    PstarSigned ε L' ⊆ PstarSigned ε L := by
  rintro n ⟨q, m, hqpp, hLq, hm1, hm2, hn⟩
  exact ⟨q, m, hqpp, lt_of_le_of_lt hL hLq, hm1, hm2, hn⟩

/-- The density hypothesis on the enlarged endpoint set `PstarSigned ε L` (Lemma D1 of
`docs/elementary_replacements.md`), taken as a hypothesis pending `Erdos289/SignedD1.lean`. -/
abbrev hD1Type (ε : ℝ) : Prop := ∀ L : ℕ, ∀ κ : ℝ, 0 < κ →
    ∀ᶠ X : ℕ in Filter.atTop, ((PstarSigned ε L ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * (X : ℝ)

/-- The mathematical core of the signed Lemma 5, analogous to `stage_exists`: for `q` a large
enough prime power (larger than a fixed threshold `Q₀`, independent of `L`), given that all
earlier stages `Prev q'` (`q' < q`) have cardinality at most `s q'`, there is a stage-`q` finset
`T` of exactly `s q` pairs meeting all the requirements of `AuxFamilyS.F` at `q`, avoiding
`PstarSigned ε L` by distance two and separated from all earlier stages.

The threshold `Q₀` is extracted from `hD1 0`, using that `PstarSigned ε L ⊆ PstarSigned ε 0` for
every `L`, so that `Q₀` does not depend on `L`. -/
theorem stage_existsS (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε) :
    ∃ Q₀ : ℕ, ∀ L q : ℕ, L < q → Q₀ ≤ q → IsPrimePow q →
      ∀ Prev : ℕ → Finset ℕ, (∀ q' < q, (Prev q').card ≤ s q') →
      ∃ T : Finset ℕ,
        T.card = s q ∧
        (∀ a ∈ T, (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a) ∧
        (∀ a ∈ T, ((a + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10)) ∧
        (∀ a ∈ T, 4 ∣ a) ∧
        (∀ a ∈ T, Powersmooth (q / 2) a) ∧
        (∀ a ∈ T, Powersmooth (q / 2) (a + 1)) ∧
        (∀ a ∈ T, ∀ n ∈ PstarSigned ε L, n + 2 < a ∨ a + 2 < n) ∧
        (∀ q' < q, ∀ a ∈ T, ∀ a' ∈ Prev q', Iv.Sep (Iv.pair a) (Iv.pair a')) := by
  classical
  obtain ⟨η, hηpos, X₀, hX₀⟩ := lemma4 (10 / 11) 1 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (1 / 1000) (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hD1 0 (1 / 1500) (by norm_num))
  obtain ⟨Q1, hQ1pos, hQ1⟩ := exists_ge_rpow_ge X₀ ((11 : ℝ) / 10) (by norm_num)
  obtain ⟨Q2, hQ2pos, hQ2⟩ := exists_ge_rpow_ge (120 : ℝ) ((11 : ℝ) / 10) (by norm_num)
  obtain ⟨Q3, hQ3pos, hQ3⟩ :=
    rpow_dominated (1 - (11 / 10) * η) 1 (by linarith) (1 / 4) (by norm_num)
  obtain ⟨Q5, hQ5pos, hQ5⟩ := exists_ge_rpow_ge (N : ℝ) ((11 : ℝ) / 10) (by norm_num)
  obtain ⟨Q6, hQ6pos, hQ6⟩ :=
    rpow_dominated ((21 : ℝ) / 20) ((22 : ℝ) / 20) (by norm_num) (0.002) (by norm_num)
  obtain ⟨Q7, hQ7pos, hQ7⟩ :=
    rpow_dominated ((1 : ℝ) / 20) ((22 : ℝ) / 20) (by norm_num) (0.01) (by norm_num)
  set Q0real : ℝ := max (max (max Q1 Q2) (max Q3 Q5)) (max (max Q6 Q7) 4) with hQ0realdef
  refine ⟨⌈Q0real⌉₊ + 1, fun L q hLq hQq hqpp Prev hPrev => ?_⟩
  have hqRge : Q0real ≤ (q : ℝ) := by
    have h1 : Q0real ≤ (⌈Q0real⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Q0real⌉₊ + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hQq
    push_cast at h2
    linarith
  have hQ1' : X₀ ≤ (q : ℝ) ^ ((11 : ℝ) / 10) := hQ1 q (by
    calc Q1 ≤ max Q1 Q2 := le_max_left _ _
    _ ≤ max (max Q1 Q2) (max Q3 Q5) := le_max_left _ _
    _ ≤ Q0real := le_max_left _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ2' : (120 : ℝ) ≤ (q : ℝ) ^ ((11 : ℝ) / 10) := hQ2 q (by
    calc Q2 ≤ max Q1 Q2 := le_max_right _ _
    _ ≤ max (max Q1 Q2) (max Q3 Q5) := le_max_left _ _
    _ ≤ Q0real := le_max_left _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ3' : (q:ℝ) ^ (1 - (11 / 10) * η) ≤ (1 / 4) * (q:ℝ) ^ (1:ℝ) := hQ3 q (by
    calc Q3 ≤ max Q3 Q5 := le_max_left _ _
    _ ≤ max (max Q1 Q2) (max Q3 Q5) := le_max_right _ _
    _ ≤ Q0real := le_max_left _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ5' : (N:ℝ) ≤ (q:ℝ) ^ ((11:ℝ)/10) := hQ5 q (by
    calc Q5 ≤ max Q3 Q5 := le_max_right _ _
    _ ≤ max (max Q1 Q2) (max Q3 Q5) := le_max_right _ _
    _ ≤ Q0real := le_max_left _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ6' : (q:ℝ) ^ ((21:ℝ)/20) ≤ 0.002 * (q:ℝ) ^ ((22:ℝ)/20) := hQ6 q (by
    calc Q6 ≤ max Q6 Q7 := le_max_left _ _
    _ ≤ max (max Q6 Q7) 4 := le_max_left _ _
    _ ≤ Q0real := le_max_right _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ7' : (q:ℝ) ^ ((1:ℝ)/20) ≤ 0.01 * (q:ℝ) ^ ((22:ℝ)/20) := hQ7 q (by
    calc Q7 ≤ max Q6 Q7 := le_max_right _ _
    _ ≤ max (max Q6 Q7) 4 := le_max_left _ _
    _ ≤ Q0real := le_max_right _ _
    _ ≤ (q:ℝ) := hqRge)
  have hqge4 : (4:ℝ) ≤ (q:ℝ) := by
    calc (4:ℝ) ≤ max (max Q6 Q7) 4 := le_max_right _ _
    _ ≤ Q0real := le_max_right _ _
    _ ≤ (q:ℝ) := hqRge
  have hqRpos : (0:ℝ) < (q:ℝ) := by linarith
  set X : ℝ := (q:ℝ) ^ ((11:ℝ)/10) with hXdef
  have hXpos : 0 < X := Real.rpow_pos_of_pos hqRpos _
  have hXge120 : (120:ℝ) ≤ X := hQ2'
  -- Window bound for `y := q/2` inside `[X^(θ-η), X^(θ+η)]`.
  have hqdiv2_ge : (q:ℝ)/2 - 1 ≤ ((q/2:ℕ):ℝ) := by
    have hkey : 2*(q/2) + 1 ≥ q := by omega
    have hcast : (q:ℝ) ≤ 2*((q/2:ℕ):ℝ) + 1 := by exact_mod_cast hkey
    linarith
  have hqdiv2_le : ((q/2:ℕ):ℝ) ≤ (q:ℝ)/2 := Nat.cast_div_le
  have hXthetalo_eq : X ^ ((10:ℝ)/11 - η) = (q:ℝ) ^ (1 - (11/10)*η) := by
    rw [hXdef, ← Real.rpow_mul hqRpos.le]
    congr 1
    ring
  have hXthetahi_eq : X ^ ((10:ℝ)/11 + η) = (q:ℝ) ^ (1 + (11/10)*η) := by
    rw [hXdef, ← Real.rpow_mul hqRpos.le]
    congr 1
    ring
  have hwindow_lo : X ^ ((10:ℝ)/11 - η) ≤ ((q/2:ℕ):ℝ) := by
    rw [hXthetalo_eq]
    have hQ3copy := hQ3'
    rw [Real.rpow_one] at hQ3copy
    have hstep : (1/4:ℝ)*(q:ℝ) ≤ (q:ℝ)/2 - 1 := by linarith [hqge4]
    calc (q:ℝ) ^ (1 - (11/10)*η) ≤ (1/4)*(q:ℝ) := hQ3copy
      _ ≤ (q:ℝ)/2 - 1 := hstep
      _ ≤ ((q/2:ℕ):ℝ) := hqdiv2_ge
  have hwindow_hi : ((q/2:ℕ):ℝ) ≤ X ^ ((10:ℝ)/11 + η) := by
    rw [hXthetahi_eq]
    have hexp : (1:ℝ) ≤ 1 + (11/10)*η := by nlinarith [hηpos]
    have hbase : (1:ℝ) ≤ (q:ℝ) := by linarith [hqge4]
    have h1 : (q:ℝ) ≤ (q:ℝ) ^ (1 + (11/10)*η) := by
      calc (q:ℝ) = (q:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ (q:ℝ)^(1+(11/10)*η) := Real.rpow_le_rpow_of_exponent_le hbase hexp
    linarith [hqdiv2_le]
  -- The candidate range `[A, B]` and the multiples-of-4 candidates `Cand`.
  set A : ℕ := ⌈X⌉₊ with hAdef
  set B : ℕ := ⌊2*X⌋₊ with hBdef
  have hA_ge : X ≤ (A:ℝ) := Nat.le_ceil _
  have hA_lt : (A:ℝ) < X + 1 := Nat.ceil_lt_add_one hXpos.le
  have hB_le : (B:ℝ) ≤ 2*X := Nat.floor_le (by positivity)
  have hB_gt : 2*X < (B:ℝ) + 1 := Nat.lt_floor_add_one _
  have hBge200 : (200:ℝ) ≤ (B:ℝ) := by nlinarith [hB_gt, hXge120]
  set k1 : ℕ := ⌈(A:ℝ)/4⌉₊ with hk1def
  set k2 : ℕ := ⌊((B-1:ℕ):ℝ)/4⌋₊ with hk2def
  have hk1_lt : (k1:ℝ) < (A:ℝ)/4 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk1_ge : (A:ℝ)/4 ≤ (k1:ℝ) := Nat.le_ceil _
  have hk2_gt : ((B-1:ℕ):ℝ)/4 - 1 < (k2:ℝ) := by
    have h := Nat.lt_floor_add_one (((B-1:ℕ):ℝ)/4)
    linarith
  have hk2_le : (k2:ℝ) ≤ ((B-1:ℕ):ℝ)/4 := Nat.floor_le (by positivity)
  set Cand : Finset ℕ := (Finset.Icc k1 k2).image (fun k => 4*k) with hCanddef
  have hinj4 : Function.Injective (fun k : ℕ => 4 * k) := by
    intro a b h
    simp only at h
    omega
  have hCand_card : Cand.card = k2 + 1 - k1 := by
    rw [hCanddef, Finset.card_image_of_injective _ hinj4, Nat.card_Icc]
  have hCand_card_real : (Cand.card:ℝ) ≥ X/4 - 2 := by
    rw [hCand_card]
    have h1 := nat_sub_cast_ge k1 k2
    have hBsub1 := nat_sub_one_cast_ge B
    have e1 : (k2:ℝ) > X/2 - 3/2 := by nlinarith [hk2_gt, hBsub1, hB_gt]
    have e2 : (k1:ℝ) < X/4 + 5/4 := by nlinarith [hk1_lt, hA_lt]
    nlinarith [h1, e1, e2]
  have hCandsub : ∀ a ∈ Cand, a + 1 ≤ B ∧ A ≤ a ∧ 4 ∣ a := by
    intro a ha
    rw [hCanddef, Finset.mem_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    simp only [Finset.mem_Icc] at hk
    have h4k2 : 4*k2 ≤ B - 1 := by
      have hr : (4*k2:ℝ) ≤ ((B-1:ℕ):ℝ) := by nlinarith [hk2_le]
      exact_mod_cast hr
    have hAk1 : A ≤ 4*k1 := by
      have hr : (A:ℝ) ≤ 4*(k1:ℝ) := by nlinarith [hk1_ge]
      exact_mod_cast hr
    refine ⟨?_, ?_, ⟨k, rfl⟩⟩
    · have hBge : (200:ℕ) ≤ B := by exact_mod_cast hBge200
      omega
    · omega
  set y : ℕ := q/2 with hydef
  -- Non-`y`-powersmooth candidates, via `lemma4`.
  have hNeq : notSmooth y 1 2 X = (Finset.Icc A B).filter (fun n => ¬ Powersmooth y n) := by
    unfold notSmooth
    rw [one_mul, ← hAdef, ← hBdef]
  have hNcard : ((notSmooth y 1 2 X).card : ℝ) ≤ (Real.log (11/10) + 1/1000) * X := by
    have hraw := hX₀ X hQ1' y hwindow_lo hwindow_hi
    have heq : ((2:ℝ)-1)*Real.log (1/(10/11)) + 1/1000 = Real.log ((11:ℝ)/10) + 1/1000 := by
      norm_num
    rwa [heq] at hraw
  have hlog1110 : Real.log ((11:ℝ)/10) ≤ 1/10 := by
    have h0 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/10 by norm_num)
    linarith [h0]
  set BadSmooth : Finset ℕ := Cand.filter (fun a => ¬ Powersmooth y a ∨ ¬ Powersmooth y (a+1))
    with hBadSmoothdef
  have hBadSmooth_le : BadSmooth.card ≤ 2 * (notSmooth y 1 2 X).card := by
    have hsub1 : Cand.filter (fun a => ¬ Powersmooth y a) ⊆ notSmooth y 1 2 X := by
      intro a ha
      simp only [Finset.mem_filter] at ha
      obtain ⟨haC, hns⟩ := ha
      obtain ⟨ha1, ha2, _⟩ := hCandsub a haC
      rw [hNeq]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨ha2, by omega⟩, hns⟩
    have hsub2 : (Cand.filter (fun a => ¬ Powersmooth y (a+1))).card ≤ (notSmooth y 1 2 X).card := by
      have hmap : (Cand.filter (fun a => ¬ Powersmooth y (a+1))).image (·+1)
          ⊆ notSmooth y 1 2 X := by
        intro n hn
        simp only [Finset.mem_image, Finset.mem_filter] at hn
        obtain ⟨a, ⟨haC, hns⟩, rfl⟩ := hn
        obtain ⟨ha1, ha2, _⟩ := hCandsub a haC
        rw [hNeq]
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, ha1⟩, hns⟩
      have hinjsucc : Function.Injective (fun a : ℕ => a + 1) := by
        intro a b h; simp only at h; omega
      have hcardeq : ((Cand.filter (fun a => ¬ Powersmooth y (a+1))).image (·+1)).card
          = (Cand.filter (fun a => ¬ Powersmooth y (a+1))).card :=
        Finset.card_image_of_injective _ hinjsucc
      calc (Cand.filter (fun a => ¬ Powersmooth y (a+1))).card
          = ((Cand.filter (fun a => ¬ Powersmooth y (a+1))).image (·+1)).card := hcardeq.symm
        _ ≤ (notSmooth y 1 2 X).card := Finset.card_le_card hmap
    have hBadsub : BadSmooth ⊆ (Cand.filter (fun a => ¬ Powersmooth y a))
        ∪ (Cand.filter (fun a => ¬ Powersmooth y (a+1))) := by
      intro a ha
      rw [hBadSmoothdef, Finset.mem_filter] at ha
      obtain ⟨haC, hor⟩ := ha
      rcases hor with h|h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haC, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haC, h⟩)
    calc BadSmooth.card
        ≤ ((Cand.filter (fun a => ¬ Powersmooth y a))
            ∪ (Cand.filter (fun a => ¬ Powersmooth y (a+1)))).card := Finset.card_le_card hBadsub
      _ ≤ (Cand.filter (fun a => ¬ Powersmooth y a)).card
          + (Cand.filter (fun a => ¬ Powersmooth y (a+1))).card := Finset.card_union_le _ _
      _ ≤ (notSmooth y 1 2 X).card + (notSmooth y 1 2 X).card :=
          Nat.add_le_add (Finset.card_le_card hsub1) hsub2
      _ = 2 * (notSmooth y 1 2 X).card := by ring
  have hBadSmooth_realle : (BadSmooth.card:ℝ) ≤ 0.202 * X := by
    have h1 : (BadSmooth.card:ℝ) ≤ 2*((notSmooth y 1 2 X).card:ℝ) := by exact_mod_cast hBadSmooth_le
    nlinarith [hNcard, hlog1110, h1]
  -- Candidates near a possible signed correction endpoint (`PstarSigned ε L`).
  have hNleX : (N:ℝ) ≤ X := by rw [hXdef]; exact hQ5'
  have hNleB2 : N ≤ B + 2 := by
    have h1 : (N:ℝ) < (B:ℝ) + 2 := by linarith [hNleX, hB_gt, hXpos]
    have h2 : (N:ℝ) < ((B+2:ℕ):ℝ) := by push_cast; linarith [h1]
    exact_mod_cast h2.le
  have hPstar0_le : ((PstarSigned ε 0 ∩ Set.Icc 1 (B+2)).ncard:ℝ) ≤ (1/1500)*((B+2:ℕ):ℝ) :=
    hN (B+2) hNleB2
  have hfinPstarS : (PstarSigned ε L ∩ Set.Icc 1 (B+2)).Finite :=
    Set.Finite.subset (Set.finite_Icc 1 (B+2)) Set.inter_subset_right
  set PstarFinS : Finset ℕ := hfinPstarS.toFinset with hPstarFinSdef
  have hPstarFinS_card : (PstarFinS.card:ℝ) ≤ (1/1500)*((B+2:ℕ):ℝ) := by
    have heq : PstarFinS.card = (PstarSigned ε L ∩ Set.Icc 1 (B+2)).ncard := by
      rw [hPstarFinSdef, ← Set.ncard_eq_toFinset_card _ hfinPstarS]
    rw [heq]
    have hsub : PstarSigned ε L ∩ Set.Icc 1 (B+2) ⊆ PstarSigned ε 0 ∩ Set.Icc 1 (B+2) :=
      Set.inter_subset_inter_left _ (PstarSigned_subset ε (Nat.zero_le L))
    have hfin0 : (PstarSigned ε 0 ∩ Set.Icc 1 (B+2)).Finite :=
      Set.Finite.subset (Set.finite_Icc 1 (B+2)) Set.inter_subset_right
    have hle : (PstarSigned ε L ∩ Set.Icc 1 (B+2)).ncard
        ≤ (PstarSigned ε 0 ∩ Set.Icc 1 (B+2)).ncard := Set.ncard_le_ncard hsub hfin0
    have hleR : ((PstarSigned ε L ∩ Set.Icc 1 (B+2)).ncard:ℝ)
        ≤ ((PstarSigned ε 0 ∩ Set.Icc 1 (B+2)).ncard:ℝ) := by exact_mod_cast hle
    linarith [hleR, hPstar0_le]
  set BadPstarS : Finset ℕ := Cand.filter (fun a => ∃ n ∈ PstarFinS, a ≤ n+2 ∧ n ≤ a+2)
    with hBadPstarSdef
  have hBadPstarS_le : BadPstarS.card ≤ 5 * PstarFinS.card := by
    rw [hBadPstarSdef]
    have h := card_near_le Cand PstarFinS 2
    omega
  have hBadPstarS_realle : (BadPstarS.card:ℝ) ≤ 0.01*X := by
    have h1 : (BadPstarS.card:ℝ) ≤ 5*(PstarFinS.card:ℝ) := by exact_mod_cast hBadPstarS_le
    have hB2le3X : ((B+2:ℕ):ℝ) ≤ 3*X := by push_cast; nlinarith [hB_le, hXge120]
    nlinarith [h1, hPstarFinS_card, hB2le3X]
  -- Candidates near an earlier reserved stage.
  set ReservedFin : Finset ℕ := (Finset.range q).biUnion (fun q' => Prev q') with hResFindef
  have hResFin_card_le : (ReservedFin.card:ℝ) ≤ (q:ℝ)^((21:ℝ)/20) := by
    have hstep0 : ReservedFin.card ≤ ∑ q' ∈ Finset.range q, (Prev q').card := by
      rw [hResFindef]; exact Finset.card_biUnion_le
    have hstep1 : (ReservedFin.card:ℝ) ≤ ∑ q' ∈ Finset.range q, ((Prev q').card:ℝ) := by
      exact_mod_cast hstep0
    have hstep2 : (∑ q' ∈ Finset.range q, ((Prev q').card:ℝ))
        ≤ ∑ q' ∈ Finset.range q, (s q' : ℝ) := by
      apply Finset.sum_le_sum
      intro q' hq'
      exact_mod_cast hPrev q' (Finset.mem_range.mp hq')
    have hstep3 : (∑ q' ∈ Finset.range q, (s q':ℝ))
        ≤ ∑ _q' ∈ Finset.range q, (q:ℝ)^((1:ℝ)/20) := by
      apply Finset.sum_le_sum
      intro q' hq'
      have hq'q : q' < q := Finset.mem_range.mp hq'
      have h1 : (s q':ℝ) ≤ (q':ℝ)^((1:ℝ)/20) := Nat.floor_le (by positivity)
      have h2 : (q':ℝ)^((1:ℝ)/20) ≤ (q:ℝ)^((1:ℝ)/20) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hq'q.le) (by norm_num)
      linarith
    have hstep4 : (∑ _q' ∈ Finset.range q, (q:ℝ)^((1:ℝ)/20)) = (q:ℝ)*(q:ℝ)^((1:ℝ)/20) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hstep5 : (q:ℝ)^((21:ℝ)/20) = (q:ℝ)*(q:ℝ)^((1:ℝ)/20) := by
      rw [show (21:ℝ)/20 = 1 + (1:ℝ)/20 by norm_num, Real.rpow_add hqRpos, Real.rpow_one]
    linarith [hstep1, hstep2, hstep3, hstep4, hstep5]
  set BadReserved : Finset ℕ := Cand.filter (fun a => ∃ n ∈ ReservedFin, a ≤ n+2 ∧ n ≤ a+2)
    with hBadReserveddef
  have hBadReserved_le : BadReserved.card ≤ 5 * ReservedFin.card := by
    rw [hBadReserveddef]
    have h := card_near_le Cand ReservedFin 2
    omega
  have hBadReserved_realle : (BadReserved.card:ℝ) ≤ 0.01*X := by
    have h1 : (BadReserved.card:ℝ) ≤ 5*(ReservedFin.card:ℝ) := by exact_mod_cast hBadReserved_le
    have hXeq22 : X = (q:ℝ)^((22:ℝ)/20) := by rw [hXdef]; norm_num
    have h2 : (ReservedFin.card:ℝ) ≤ 0.002*X := by
      calc (ReservedFin.card:ℝ) ≤ (q:ℝ)^((21:ℝ)/20) := hResFin_card_le
        _ ≤ 0.002*(q:ℝ)^((22:ℝ)/20) := hQ6'
        _ = 0.002*X := by rw [hXeq22]
    linarith [h1, h2]
  have hsq_le : (s q:ℝ) ≤ 0.01*X := by
    have hXeq22 : X = (q:ℝ)^((22:ℝ)/20) := by rw [hXdef]; norm_num
    have h1 : (s q:ℝ) ≤ (q:ℝ)^((1:ℝ)/20) := Nat.floor_le (by positivity)
    calc (s q:ℝ) ≤ (q:ℝ)^((1:ℝ)/20) := h1
      _ ≤ 0.01*(q:ℝ)^((22:ℝ)/20) := hQ7'
      _ = 0.01*X := by rw [hXeq22]
  -- Assemble the surviving candidates and extract a subfamily of size `s q`.
  set GoodCand : Finset ℕ := Cand \ (BadSmooth ∪ BadPstarS ∪ BadReserved) with hGoodCanddef
  have hGoodCand_ge : Cand.card ≤ GoodCand.card + (BadSmooth ∪ BadPstarS ∪ BadReserved).card := by
    rw [hGoodCanddef]; exact Finset.card_le_card_sdiff_add_card
  have hUnion_le : (BadSmooth ∪ BadPstarS ∪ BadReserved).card
      ≤ BadSmooth.card + BadPstarS.card + BadReserved.card := by
    calc (BadSmooth ∪ BadPstarS ∪ BadReserved).card
        ≤ (BadSmooth ∪ BadPstarS).card + BadReserved.card := Finset.card_union_le _ _
      _ ≤ (BadSmooth.card + BadPstarS.card) + BadReserved.card := by
          have := Finset.card_union_le BadSmooth BadPstarS
          omega
      _ = BadSmooth.card + BadPstarS.card + BadReserved.card := by ring
  have hGoodCand_realge : (GoodCand.card:ℝ) ≥ X/100 := by
    have h1 : (Cand.card:ℝ) ≤ (GoodCand.card:ℝ) + ((BadSmooth ∪ BadPstarS ∪ BadReserved).card:ℝ) := by
      exact_mod_cast hGoodCand_ge
    have h2 : ((BadSmooth ∪ BadPstarS ∪ BadReserved).card:ℝ)
        ≤ (BadSmooth.card:ℝ)+(BadPstarS.card:ℝ)+(BadReserved.card:ℝ) := by
      exact_mod_cast hUnion_le
    nlinarith [hCand_card_real, h1, h2, hBadSmooth_realle, hBadPstarS_realle, hBadReserved_realle,
      hXge120]
  have hGoodCand_ge_sq : s q ≤ GoodCand.card := by
    have h1 : (s q:ℝ) ≤ (GoodCand.card:ℝ) := by linarith [hGoodCand_realge, hsq_le]
    exact_mod_cast h1
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hGoodCand_ge_sq
  have hGoodCand_mem : ∀ a ∈ GoodCand, a ∈ Cand ∧ a ∉ BadSmooth ∧ a ∉ BadPstarS ∧ a ∉ BadReserved := by
    intro a ha
    rw [hGoodCanddef] at ha
    simp only [Finset.mem_sdiff, Finset.mem_union] at ha
    tauto
  refine ⟨T, hTcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨haC, _, _, _⟩ := hGoodCand_mem a (hTsub ha)
    obtain ⟨_, ha2, _⟩ := hCandsub a haC
    calc X ≤ (A:ℝ) := hA_ge
      _ ≤ (a:ℝ) := by exact_mod_cast ha2
  · intro a ha
    obtain ⟨haC, _, _, _⟩ := hGoodCand_mem a (hTsub ha)
    obtain ⟨ha1, _, _⟩ := hCandsub a haC
    calc ((a+1:ℕ):ℝ) ≤ (B:ℝ) := by exact_mod_cast ha1
      _ ≤ 2*X := hB_le
  · intro a ha
    obtain ⟨haC, _, _, _⟩ := hGoodCand_mem a (hTsub ha)
    exact (hCandsub a haC).2.2
  · intro a ha
    obtain ⟨haC, hBS, _, _⟩ := hGoodCand_mem a (hTsub ha)
    by_contra hns
    apply hBS
    rw [hBadSmoothdef]
    exact Finset.mem_filter.mpr ⟨haC, Or.inl hns⟩
  · intro a ha
    obtain ⟨haC, hBS, _, _⟩ := hGoodCand_mem a (hTsub ha)
    by_contra hns
    apply hBS
    rw [hBadSmoothdef]
    exact Finset.mem_filter.mpr ⟨haC, Or.inr hns⟩
  · intro a ha n hn
    obtain ⟨haC, _, hBP, _⟩ := hGoodCand_mem a (hTsub ha)
    obtain ⟨ha1, ha2, _⟩ := hCandsub a haC
    have haXR : X ≤ (a:ℝ) := hA_ge.trans (by exact_mod_cast ha2)
    have ha120 : (120:ℕ) ≤ a := by
      have h : (120:ℝ) ≤ (a:ℝ) := hXge120.trans haXR
      exact_mod_cast h
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · left; omega
    · by_cases hcase : n ≤ B + 2
      · have hnPstarFinS : n ∈ PstarFinS := by
          rw [hPstarFinSdef, Set.Finite.mem_toFinset]
          exact ⟨hn, Set.mem_Icc.mpr ⟨hnpos, hcase⟩⟩
        by_contra hcon
        push Not at hcon
        apply hBP
        rw [hBadPstarSdef]
        exact Finset.mem_filter.mpr ⟨haC, n, hnPstarFinS, by omega⟩
      · push Not at hcase
        right; omega
  · intro q' hq'lt a ha a' ha'
    obtain ⟨haC, _, _, hBR⟩ := hGoodCand_mem a (hTsub ha)
    have ha'Res : a' ∈ ReservedFin := by
      rw [hResFindef]
      exact Finset.mem_biUnion.mpr ⟨q', Finset.mem_range.mpr hq'lt, ha'⟩
    have hnotnear : ¬(a ≤ a'+2 ∧ a' ≤ a+2) := by
      intro hcon
      apply hBR
      rw [hBadReserveddef]
      exact Finset.mem_filter.mpr ⟨haC, a', ha'Res, hcon⟩
    unfold Iv.Sep Iv.pair
    simp only
    omega

/-- A fixed threshold witnessing `stage_existsS`, used uniformly for every cutoff `L`. -/
noncomputable def stageQ₀S (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε) : ℕ :=
  (stage_existsS ε hε0 hε1 hD1).choose

theorem stageQ₀S_spec (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε) :
    ∀ L q : ℕ, L < q → stageQ₀S ε hε0 hε1 hD1 ≤ q → IsPrimePow q →
    ∀ Prev : ℕ → Finset ℕ, (∀ q' < q, (Prev q').card ≤ s q') →
    ∃ T : Finset ℕ,
      T.card = s q ∧
      (∀ a ∈ T, (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a) ∧
      (∀ a ∈ T, ((a + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10)) ∧
      (∀ a ∈ T, 4 ∣ a) ∧
      (∀ a ∈ T, Powersmooth (q / 2) a) ∧
      (∀ a ∈ T, Powersmooth (q / 2) (a + 1)) ∧
      (∀ a ∈ T, ∀ n ∈ PstarSigned ε L, n + 2 < a ∨ a + 2 < n) ∧
      (∀ q' < q, ∀ a ∈ T, ∀ a' ∈ Prev q', Iv.Sep (Iv.pair a) (Iv.pair a')) :=
  (stage_existsS ε hε0 hε1 hD1).choose_spec

/-- The recursive construction of the signed auxiliary family: `FconstrS L q` processes prime
powers `q > max L (stageQ₀S ε hε0 hε1 hD1)` in increasing order, each stage choosing its finset
via `stageQ₀S_spec` relative to (a safety-truncated copy of) all strictly earlier stages. -/
noncomputable def FconstrS (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε)
    (L : ℕ) (q : ℕ) : Finset ℕ :=
  Nat.strongRecOn q (fun q ih =>
    if h : IsPrimePow q ∧ L < q ∧ stageQ₀S ε hε0 hε1 hD1 ≤ q then
      Classical.choose (stageQ₀S_spec ε hε0 hε1 hD1 L q h.2.1 h.2.2 h.1
        (fun q' => if hlt : q' < q then (if (ih q' hlt).card ≤ s q' then ih q' hlt else ∅) else ∅)
        (fun q' hq' => by
          rw [dite_eq_left_of_eq_true (eq_true hq')]
          exact truncate_card_le (ih q' hq') (s q')))
    else ∅)

theorem FconstrS_eq (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε) (L q : ℕ) :
    FconstrS ε hε0 hε1 hD1 L q =
      if h : IsPrimePow q ∧ L < q ∧ stageQ₀S ε hε0 hε1 hD1 ≤ q then
        Classical.choose (stageQ₀S_spec ε hε0 hε1 hD1 L q h.2.1 h.2.2 h.1
          (fun q' => if _hlt : q' < q then
              (if (FconstrS ε hε0 hε1 hD1 L q').card ≤ s q' then FconstrS ε hε0 hε1 hD1 L q' else ∅)
              else ∅)
          (fun q' hq' => by
            rw [dite_eq_left_of_eq_true (eq_true hq')]
            exact truncate_card_le (FconstrS ε hε0 hε1 hD1 L q') (s q')))
      else ∅ := by
  conv_lhs => rw [FconstrS]
  exact WellFounded.fix_eq Nat.lt_wfRel.wf _ q

theorem FconstrS_card_le (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε) (L q : ℕ) :
    (FconstrS ε hε0 hε1 hD1 L q).card ≤ s q := by
  rw [FconstrS_eq ε hε0 hε1 hD1]
  split
  · next h =>
    exact (Classical.choose_spec (stageQ₀S_spec ε hε0 hε1 hD1 L q h.2.1 h.2.2 h.1
      (fun q' => if hlt : q' < q then
          (if (FconstrS ε hε0 hε1 hD1 L q').card ≤ s q' then FconstrS ε hε0 hε1 hD1 L q' else ∅)
          else ∅)
      (fun q' hq' => by
        rw [dite_eq_left_of_eq_true (eq_true hq')]
        exact truncate_card_le (FconstrS ε hε0 hε1 hD1 L q') (s q')))).1.le
  · simp

/-- The main specification of `FconstrS L q` at a valid stage. -/
theorem FconstrS_spec (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε)
    (L q : ℕ) (hqpp : IsPrimePow q) (hLq : L < q)
    (hQq : stageQ₀S ε hε0 hε1 hD1 ≤ q) :
    (FconstrS ε hε0 hε1 hD1 L q).card = s q ∧
    (∀ a ∈ FconstrS ε hε0 hε1 hD1 L q, (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a) ∧
    (∀ a ∈ FconstrS ε hε0 hε1 hD1 L q, ((a + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10)) ∧
    (∀ a ∈ FconstrS ε hε0 hε1 hD1 L q, 4 ∣ a) ∧
    (∀ a ∈ FconstrS ε hε0 hε1 hD1 L q, Powersmooth (q / 2) a) ∧
    (∀ a ∈ FconstrS ε hε0 hε1 hD1 L q, Powersmooth (q / 2) (a + 1)) ∧
    (∀ a ∈ FconstrS ε hε0 hε1 hD1 L q, ∀ n ∈ PstarSigned ε L, n + 2 < a ∨ a + 2 < n) ∧
    (∀ q' < q, ∀ a ∈ FconstrS ε hε0 hε1 hD1 L q, ∀ a' ∈ FconstrS ε hε0 hε1 hD1 L q',
      Iv.Sep (Iv.pair a) (Iv.pair a')) := by
  have hraw := Classical.choose_spec (stageQ₀S_spec ε hε0 hε1 hD1 L q hLq hQq hqpp
    (fun q' => if hlt : q' < q then
        (if (FconstrS ε hε0 hε1 hD1 L q').card ≤ s q' then FconstrS ε hε0 hε1 hD1 L q' else ∅)
        else ∅)
    (fun q' hq' => by
      rw [dite_eq_left_of_eq_true (eq_true hq')]
      exact truncate_card_le (FconstrS ε hε0 hε1 hD1 L q') (s q')))
  have heq : FconstrS ε hε0 hε1 hD1 L q = Classical.choose (stageQ₀S_spec ε hε0 hε1 hD1 L q hLq hQq hqpp
      (fun q' => if hlt : q' < q then
          (if (FconstrS ε hε0 hε1 hD1 L q').card ≤ s q' then FconstrS ε hε0 hε1 hD1 L q' else ∅)
          else ∅)
      (fun q' hq' => by
        rw [dite_eq_left_of_eq_true (eq_true hq')]
        exact truncate_card_le (FconstrS ε hε0 hε1 hD1 L q') (s q'))) := by
    rw [FconstrS_eq ε hε0 hε1 hD1]
    rw [dite_eq_left_of_eq_true (eq_true (⟨hqpp, hLq, hQq⟩ :
      IsPrimePow q ∧ L < q ∧ stageQ₀S ε hε0 hε1 hD1 ≤ q))]
  rw [← heq] at hraw
  obtain ⟨hcard, hlower, hupper, hdvd, hsmoothlo, hsmoothhi, havoid, hsepaux⟩ := hraw
  refine ⟨hcard, hlower, hupper, hdvd, hsmoothlo, hsmoothhi, havoid, ?_⟩
  intro q' hq'lt a ha a' ha'
  have htrunc : (if hlt : q' < q then
      (if (FconstrS ε hε0 hε1 hD1 L q').card ≤ s q' then FconstrS ε hε0 hε1 hD1 L q' else ∅)
      else ∅) = FconstrS ε hε0 hε1 hD1 L q' := by
    rw [dite_eq_left_of_eq_true (eq_true hq'lt),
      ite_eq_left_of_eq_true _ _ (eq_true (FconstrS_card_le ε hε0 hε1 hD1 L q'))]
  rw [← htrunc] at ha'
  exact hsepaux q' hq'lt a ha a' ha'

/-- If `FconstrS L q` is nonempty, `q` must have already reached the threshold
`stageQ₀S ε hε0 hε1 hD1`. -/
theorem FconstrS_mem_imp (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε)
    (L q a : ℕ) (_hqpp : IsPrimePow q) (_hLq : L < q)
    (ha : a ∈ FconstrS ε hε0 hε1 hD1 L q) : stageQ₀S ε hε0 hε1 hD1 ≤ q := by
  by_contra hQq
  have hempty : FconstrS ε hε0 hε1 hD1 L q = ∅ := by
    rw [FconstrS_eq ε hε0 hε1 hD1, dite_eq_right_of_eq_false (eq_false (fun h => hQq h.2.2))]
  rw [hempty] at ha
  exact absurd ha (Finset.notMem_empty a)

/-- `|F* ∩ [1, X]| = O(X^(21/22))` for the signed construction (same argument as
`Fconstr_count`, independent of the `avoid` field). -/
theorem FconstrS_count (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD1 : hD1Type ε) (L : ℕ) :
    ∃ C : ℝ, ∀ X : ℕ,
      ((Fstar L (FconstrS ε hε0 hε1 hD1 L) ∩ Set.Icc 1 X).ncard : ℝ) ≤ C * (X:ℝ)^((21:ℝ)/22) := by
  refine ⟨100, fun X => ?_⟩
  rcases Nat.eq_zero_or_pos X with hX0 | hXpos
  · subst hX0
    simp
  have hXposR : (0:ℝ) < (X:ℝ) := by exact_mod_cast hXpos
  set Y : ℕ := ⌈(X:ℝ)^((10:ℝ)/11)⌉₊ with hYdef
  set FX : Finset ℕ := ((Finset.Icc 1 Y).filter (fun q => IsPrimePow q)).biUnion
      (fun q => (FconstrS ε hε0 hε1 hD1 L q).biUnion (fun a => ({a, a+1} : Finset ℕ)))
    with hFXdef
  have hsub : Fstar L (FconstrS ε hε0 hε1 hD1 L) ∩ Set.Icc 1 X ⊆ (FX : Set ℕ) := by
    rintro n ⟨⟨q, hqpp, hLq, a, ha, hn⟩, hn1, hnX⟩
    have hQq : stageQ₀S ε hε0 hε1 hD1 ≤ q := FconstrS_mem_imp ε hε0 hε1 hD1 L q a hqpp hLq ha
    have hlower := (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq hQq).2.1 a ha
    have hqle : q ≤ Y := by
      have hqX : (q:ℝ)^((11:ℝ)/10) ≤ (X:ℝ) := by
        rcases hn with h | h
        · rw [h] at hnX; exact hlower.trans (by exact_mod_cast hnX)
        · rw [h] at hnX
          have hle1 : (a:ℝ) ≤ ((a+1:ℕ):ℝ) := by push_cast; linarith
          exact hlower.trans (hle1.trans (by exact_mod_cast hnX))
      have hqR : (q:ℝ) ≤ (X:ℝ)^((10:ℝ)/11) := by
        have h1 := Real.rpow_le_rpow (by positivity) hqX (by norm_num : (0:ℝ) ≤ (10:ℝ)/11)
        rwa [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (q:ℝ)),
          show (11:ℝ)/10*((10:ℝ)/11) = 1 by norm_num, Real.rpow_one] at h1
      exact_mod_cast hqR.trans (Nat.le_ceil _)
    have hqmem : q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hqpp.pos, hqle⟩, hqpp⟩
    rw [hFXdef]
    refine Finset.mem_biUnion.mpr ⟨q, hqmem, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
    rcases hn with h | h <;> simp [h]
  have hncard_le : ((Fstar L (FconstrS ε hε0 hε1 hD1 L) ∩ Set.Icc 1 X).ncard:ℝ) ≤ (FX.card:ℝ) := by
    have hle : (Fstar L (FconstrS ε hε0 hε1 hD1 L) ∩ Set.Icc 1 X).ncard ≤ FX.card := by
      have h := Set.ncard_le_ncard hsub
      rwa [Set.ncard_coe_finset] at h
    exact_mod_cast hle
  have hstep1 : FX.card ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
      ((FconstrS ε hε0 hε1 hD1 L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card := by
    rw [hFXdef]; exact Finset.card_biUnion_le
  have hstep2 : ∀ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
      ((FconstrS ε hε0 hε1 hD1 L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card
        ≤ 2*(FconstrS ε hε0 hε1 hD1 L q).card := by
    intro q _
    calc ((FconstrS ε hε0 hε1 hD1 L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card
        ≤ ∑ a ∈ FconstrS ε hε0 hε1 hD1 L q, ({a,a+1}:Finset ℕ).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ FconstrS ε hε0 hε1 hD1 L q, 2 :=
          Finset.sum_le_sum (fun a _ => le_trans (Finset.card_insert_le _ _) (by simp))
      _ = 2*(FconstrS ε hε0 hε1 hD1 L q).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hstep3 : ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
      ((FconstrS ε hε0 hε1 hD1 L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card
      ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), 2*(FconstrS ε hε0 hε1 hD1 L q).card :=
    Finset.sum_le_sum hstep2
  have hstep5 : ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (FconstrS ε hε0 hε1 hD1 L q).card
      ≤ ∑ q ∈ (Finset.Icc 1 Y).filter IsPrimePow, s q :=
    Finset.sum_le_sum (fun q _ => FconstrS_card_le ε hε0 hε1 hD1 L q)
  have hstep6 : (∑ q ∈ (Finset.Icc 1 Y).filter IsPrimePow, (s q:ℕ) : ℝ) ≤ (Y:ℝ)^((21:ℝ)/20) := by
    have h := sum_rpow_le 0 Y
    simp only [zero_add] at h
    push_cast at h
    exact h
  have hFXcard_le : (FX.card:ℝ) ≤ 2 * (Y:ℝ)^((21:ℝ)/20) := by
    have hn : FX.card
        ≤ 2 * ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (FconstrS ε hε0 hε1 hD1 L q).card := by
      calc FX.card
          ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
              ((FconstrS ε hε0 hε1 hD1 L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card := hstep1
        _ ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), 2*(FconstrS ε hε0 hε1 hD1 L q).card :=
            hstep3
        _ = 2 * ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (FconstrS ε hε0 hε1 hD1 L q).card := by
            rw [Finset.mul_sum]
    have hcast : (FX.card:ℝ) ≤ 2*(∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
        (FconstrS ε hε0 hε1 hD1 L q).card : ℝ) := by exact_mod_cast hn
    have hcast2 : (∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (FconstrS ε hε0 hε1 hD1 L q).card : ℝ)
        ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (s q :ℝ) := by exact_mod_cast hstep5
    linarith [hcast, hcast2, hstep6]
  have hX1 : (1:ℝ) ≤ (X:ℝ)^((10:ℝ)/11) := Real.one_le_rpow (by exact_mod_cast hXpos) (by norm_num)
  have hYle : (Y:ℝ) < (X:ℝ)^((10:ℝ)/11) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hYle2 : (Y:ℝ) ≤ 2*(X:ℝ)^((10:ℝ)/11) := by linarith [hYle, hX1]
  have hYpow_le : (Y:ℝ)^((21:ℝ)/20) ≤ (2*(X:ℝ)^((10:ℝ)/11))^((21:ℝ)/20) :=
    Real.rpow_le_rpow (by positivity) hYle2 (by norm_num)
  have heq2 : (2*(X:ℝ)^((10:ℝ)/11))^((21:ℝ)/20) = 2^((21:ℝ)/20) * (X:ℝ)^((21:ℝ)/22) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity : (0:ℝ)≤(X:ℝ))]
    norm_num
  have h2pow_le : (2:ℝ)^((21:ℝ)/20) ≤ 40 := by
    calc (2:ℝ)^((21:ℝ)/20) ≤ (2:ℝ)^(2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
      _ ≤ 40 := by norm_num
  have hfinal : (Y:ℝ)^((21:ℝ)/20) ≤ 40*(X:ℝ)^((21:ℝ)/22) := by
    calc (Y:ℝ)^((21:ℝ)/20) ≤ (2*(X:ℝ)^((10:ℝ)/11))^((21:ℝ)/20) := hYpow_le
      _ = 2^((21:ℝ)/20) * (X:ℝ)^((21:ℝ)/22) := heq2
      _ ≤ 40*(X:ℝ)^((21:ℝ)/22) := by
          apply mul_le_mul_of_nonneg_right h2pow_le (by positivity)
  linarith [hncard_le, hFXcard_le, hfinal]

end Erdos289.Lemma5S

namespace Erdos289

open Erdos289.Lemma5S

/-- **Lemma 5, signed variant**: for every sufficiently large `L` a signed auxiliary family
exists, given the density bound `hD1` on the enlarged endpoint set `PstarSigned ε L` (Lemma D1 of
`docs/elementary_replacements.md`, proved separately in `Erdos289/SignedD1.lean`). -/
theorem lemma5S_of (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hD1 : ∀ L : ℕ, ∀ κ : ℝ, 0 < κ →
      ∀ᶠ X : ℕ in Filter.atTop, ((PstarSigned ε L ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * (X : ℝ)) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → Nonempty (AuxFamilyS ε L) := by
  refine ⟨stageQ₀S ε hε0 hε1 hD1, fun L hL =>
    ⟨⟨FconstrS ε hε0 hε1 hD1 L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · intro q hqpp hLq
    exact (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).1
  · intro q hqpp hLq
    exact (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).2.1
  · intro q hqpp hLq
    exact (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).2.2.1
  · intro q hqpp hLq
    exact (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).2.2.2.1
  · intro q hqpp hLq
    exact (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).2.2.2.2.1
  · intro q hqpp hLq
    exact (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).2.2.2.2.2.1
  · intro q q' hqpp hLq hq'pp hLq' a ha a' ha' hne
    rcases lt_trichotomy q q' with hlt | heq | hgt
    · have h7 := (FconstrS_spec ε hε0 hε1 hD1 L q' hq'pp hLq' (le_trans hL hLq'.le)).2.2.2.2.2.2.2
      exact (h7 q hlt a' ha' a ha).symm
    · subst heq
      have hdvd := (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).2.2.2.1
      have hane : a ≠ a' := fun hcon => hne (by rw [hcon])
      exact sep_pair_of_four_dvd (hdvd a ha) (hdvd a' ha') hane
    · have h7 := (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).2.2.2.2.2.2.2
      exact h7 q' hgt a ha a' ha'
  · intro q hqpp hLq a ha n hn
    exact (FconstrS_spec ε hε0 hε1 hD1 L q hqpp hLq (le_trans hL hLq.le)).2.2.2.2.2.2.1 a ha n hn
  · exact FconstrS_count ε hε0 hε1 hD1 L

/-- **(4.5)-type density bound, signed variant**: `|U ∩ [1, X]| = o(X)` for the protected set
`USigned = PstarSigned ε L ∪ Fstar L A.F`, from the density hypothesis `hD1` on `PstarSigned ε L`
(for this fixed `L`) together with the auxiliary family's `O(X^(21/22))` bound `A.count`
(`X^(21/22) = o(X)`). -/
theorem USigned_density (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (L : ℕ) (A : AuxFamilyS ε L)
    (hD1 : ∀ κ : ℝ, 0 < κ →
      ∀ᶠ X : ℕ in Filter.atTop, ((PstarSigned ε L ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * (X : ℝ)) :
    ∀ κ : ℝ, 0 < κ →
      ∀ᶠ X : ℕ in Filter.atTop, ((USigned ε L A ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * (X : ℝ) := by
  intro κ hκ
  obtain ⟨C, hC⟩ := A.count
  set C' : ℝ := max C 0 + 1 with hC'def
  have hC'pos : 0 < C' := by positivity
  have hCle : ∀ X : ℕ, ((Fstar L A.F ∩ Set.Icc 1 X).ncard : ℝ) ≤ C' * (X:ℝ)^((21:ℝ)/22) := by
    intro X
    have hraw := hC X
    have hmono : C * (X:ℝ)^((21:ℝ)/22) ≤ C' * (X:ℝ)^((21:ℝ)/22) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [le_max_left C 0]
    linarith [hraw, hmono]
  obtain ⟨Q, hQpos, hQ⟩ := rpow_dominated ((21:ℝ)/22) 1 (by norm_num) (κ/(2*C')) (by positivity)
  have hev1 : ∀ᶠ X : ℕ in Filter.atTop, ((PstarSigned ε L ∩ Set.Icc 1 X).ncard : ℝ) ≤ (κ/2)*(X:ℝ) :=
    hD1 (κ/2) (by linarith)
  have hev2 : ∀ᶠ X : ℕ in Filter.atTop, Q ≤ (X:ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈Q⌉₊ + 1, fun X hX => ?_⟩
    have h1 : ⌈Q⌉₊ ≤ X := by omega
    have h2 : (⌈Q⌉₊:ℝ) ≤ (X:ℝ) := by exact_mod_cast h1
    linarith [Nat.le_ceil Q]
  filter_upwards [hev1, hev2] with X hX1 hX2
  have hQX : (X:ℝ)^((21:ℝ)/22) ≤ (κ/(2*C')) * (X:ℝ)^(1:ℝ) := hQ X hX2
  have hQX' : (X:ℝ)^((21:ℝ)/22) ≤ (κ/(2*C')) * (X:ℝ) := by rw [Real.rpow_one] at hQX; exact hQX
  have hFstarle : ((Fstar L A.F ∩ Set.Icc 1 X).ncard:ℝ) ≤ (κ/2)*(X:ℝ) := by
    calc ((Fstar L A.F ∩ Set.Icc 1 X).ncard:ℝ) ≤ C' * (X:ℝ)^((21:ℝ)/22) := hCle X
      _ ≤ C' * ((κ/(2*C'))*(X:ℝ)) := by apply mul_le_mul_of_nonneg_left hQX' (by positivity)
      _ = (κ/2)*(X:ℝ) := by
          field_simp [ne_of_gt hC'pos]
  have hUeq : USigned ε L A ∩ Set.Icc 1 X
      = (PstarSigned ε L ∩ Set.Icc 1 X) ∪ (Fstar L A.F ∩ Set.Icc 1 X) := by
    rw [USigned, Set.union_inter_distrib_right]
  have hcardle : (USigned ε L A ∩ Set.Icc 1 X).ncard
      ≤ (PstarSigned ε L ∩ Set.Icc 1 X).ncard + (Fstar L A.F ∩ Set.Icc 1 X).ncard := by
    rw [hUeq]; exact Set.ncard_union_le _ _
  have hcardleR : ((USigned ε L A ∩ Set.Icc 1 X).ncard:ℝ)
      ≤ ((PstarSigned ε L ∩ Set.Icc 1 X).ncard:ℝ) + ((Fstar L A.F ∩ Set.Icc 1 X).ncard:ℝ) := by
    exact_mod_cast hcardle
  linarith [hcardleR, hX1, hFstarle]

/-- **Lemma 5, signed version**: for every sufficiently large cutoff an auxiliary family avoiding
the enlarged endpoint set exists. -/
theorem lemma5S (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → Nonempty (AuxFamilyS ε L) :=
  lemma5S_of ε hε0 hε1 (fun L => lemmaD1 ε hε0 hε1 L)

end Erdos289
