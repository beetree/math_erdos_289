import Erdos289.Defs
import Erdos289.Lemma4
import Erdos289.Core
import Erdos289.Greedy
import Erdos289.Harmonic

/-!
# Section 6: exactly the required number of main pairs

Main pairs are pairs `[a, a+1]` with `3 ∣ a`, both endpoints `Q`-powersmooth, lying either in the
near range `[k/1024, k]` or in the far band `[4k, 20k]`. For any prescribed count `M = k - o(k)`
and target `τ ∈ (1/2, 1)` one can choose exactly `M` such pairs with total mass in
`[τ - 2048/k, τ]`.
-/

namespace Erdos289

open Finset

/-- A main-pair candidate for the parameter `k`: start divisible by `3`, both endpoints
`Q`-powersmooth, located in the near range or the far band. -/
def IsMainPair (k : ℕ) (I : Iv) : Prop :=
  ∃ a : ℕ, I = Iv.pair a ∧ 3 ∣ a ∧ Powersmooth (Q k) a ∧ Powersmooth (Q k) (a + 1) ∧
    (((k : ℝ) / 1024 ≤ a ∧ ((a + 1 : ℕ) : ℝ) ≤ k) ∨ (4 * (k : ℝ) ≤ a ∧ ((a + 1 : ℕ) : ℝ) ≤ 20 * k))

/-! ## Counting grid pair starts spoiled by non-powersmoothness -/

/-- If elements of `S` are pairwise "3-separated" then at most `Bad.card` of them have
`a ∈ Bad ∨ a + 1 ∈ Bad` (each bad integer spoils at most one candidate pair). -/
lemma good_ge_card_sub' (S Bad : Finset ℕ)
    (hsep : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a + 1 < a' ∨ a' + 1 < a) :
    S.card - Bad.card ≤ (S.filter (fun a => a ∉ Bad ∧ a + 1 ∉ Bad)).card := by
  classical
  set Spoiled := S.filter (fun a => a ∈ Bad ∨ a + 1 ∈ Bad) with hSpoiled_def
  have hgood_eq : S.filter (fun a => a ∉ Bad ∧ a + 1 ∉ Bad) = S \ Spoiled := by
    ext a
    simp only [mem_filter, mem_sdiff, hSpoiled_def, mem_filter]
    tauto
  have hSpoiled_sub : Spoiled ⊆ S := filter_subset _ _
  have hcard_good : (S.filter (fun a => a ∉ Bad ∧ a + 1 ∉ Bad)).card = S.card - Spoiled.card := by
    rw [hgood_eq, Finset.card_sdiff_of_subset hSpoiled_sub]
  have hSpoiled_le : Spoiled.card ≤ Bad.card := by
    set f : ℕ → ℕ := fun a => if a ∈ Bad then a else a + 1 with hf_def
    have hmap : ∀ a ∈ Spoiled, f a ∈ Bad := by
      intro a ha
      simp only [hSpoiled_def, mem_filter] at ha
      obtain ⟨haS, hor⟩ := ha
      rcases hor with h | h
      · simp [hf_def, h]
      · by_cases hb : a ∈ Bad
        · simp [hf_def, hb]
        · simp [hf_def, hb, h]
    have hinj : Set.InjOn f (Spoiled : Set ℕ) := by
      intro a ha a' ha' heq
      by_contra hne
      have haS : a ∈ S := hSpoiled_sub ha
      have ha'S : a' ∈ S := hSpoiled_sub ha'
      have hsep' := hsep a haS a' ha'S hne
      have hfa : f a = a ∨ f a = a + 1 := by simp only [hf_def]; split_ifs <;> simp
      have hfa' : f a' = a' ∨ f a' = a' + 1 := by simp only [hf_def]; split_ifs <;> simp
      rcases hsep' with h | h <;> rcases hfa with h1 | h1 <;> rcases hfa' with h2 | h2 <;> omega
    exact Finset.card_le_card_of_injOn f hmap hinj
  omega

/-- Exact count of multiples of `3` in `Icc A B`. -/
lemma card_mult3_Icc (A B : ℕ) :
    ((Icc A B).filter (fun n => 3 ∣ n)).card = B / 3 + 1 - (A + 2) / 3 := by
  have heq : (Icc A B).filter (fun n => 3 ∣ n) = (Icc ((A + 2) / 3) (B / 3)).image (fun m => 3 * m) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hA, hB⟩, m, hm⟩
      exact ⟨m, ⟨by omega, by omega⟩, hm.symm⟩
    · rintro ⟨m, ⟨hlo, hhi⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, m, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (mul_right_injective₀ (by norm_num))]
  rw [Nat.card_Icc]

open Classical in
/-- Grid pair starts (multiples of `3`) in `[L, U]`, fully `y`-powersmooth. -/
noncomputable def gridGood (y : ℕ) (L U : ℕ) : Finset ℕ :=
  (Icc L U).filter (fun n => 3 ∣ n ∧ n + 1 ≤ U ∧ Powersmooth y n ∧ Powersmooth y (n + 1))

/-- The central counting lemma: given `lemma4`'s bound on the number of non-`y`-powersmooth
integers in `[a*k, b*k]`, the count of fully powersmooth grid pair starts in
`[⌈a*k⌉₊, ⌊b*k⌋₊]` is bounded below. -/
lemma gridGood_card_ge (y : ℕ) (a b : ℝ) (k : ℕ) (E : ℝ) (L U : ℕ) (ha : 0 ≤ a)
    (hL : L = ⌈a * (k:ℝ)⌉₊) (hU : U = ⌊b * (k:ℝ)⌋₊) (hU1 : 1 ≤ U)
    (hcard : ((notSmooth y a b k).card : ℝ) ≤ E) :
    ((U:ℝ) - L - 5) / 3 - E ≤ ((gridGood y L U).card : ℝ) := by
  classical
  set allMult := (Icc L (U - 1)).filter (fun n => 3 ∣ n) with hallMult_def
  have hgood_eq : gridGood y L U = allMult.filter
      (fun n => n ∉ notSmooth y a b k ∧ n + 1 ∉ notSmooth y a b k) := by
    ext n
    have hnotSmooth : ∀ m, m ∈ Icc L U → (m ∈ notSmooth y a b k ↔ ¬ Powersmooth y m) := by
      intro m hm
      rw [hL, hU] at hm
      simp only [notSmooth, mem_filter]
      tauto
    simp only [gridGood, hallMult_def, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hLn, hnU⟩, h3, hn1U, hp, hp1⟩
      have hmem : n ∈ Icc L U := mem_Icc.mpr ⟨hLn, hnU⟩
      have hmem1 : n + 1 ∈ Icc L U := mem_Icc.mpr ⟨by omega, hn1U⟩
      refine ⟨⟨⟨hLn, by omega⟩, h3⟩, ?_, ?_⟩
      · rw [hnotSmooth n hmem]; exact fun h => h hp
      · rw [hnotSmooth (n+1) hmem1]; exact fun h => h hp1
    · rintro ⟨⟨⟨hLn, hnU1⟩, h3⟩, hn, hn1⟩
      have hnU : n ≤ U := by omega
      have hn1U : n + 1 ≤ U := by omega
      have hmem : n ∈ Icc L U := mem_Icc.mpr ⟨hLn, hnU⟩
      have hmem1 : n + 1 ∈ Icc L U := mem_Icc.mpr ⟨by omega, hn1U⟩
      rw [hnotSmooth n hmem] at hn
      rw [hnotSmooth (n+1) hmem1] at hn1
      exact ⟨⟨hLn, hnU⟩, h3, hn1U, not_not.mp hn, not_not.mp hn1⟩
  have hsep : ∀ n ∈ allMult, ∀ n' ∈ allMult, n ≠ n' → n + 1 < n' ∨ n' + 1 < n := by
    intro n hn n' hn' hne
    simp only [hallMult_def, mem_filter] at hn hn'
    obtain ⟨_, h3⟩ := hn
    obtain ⟨_, h3'⟩ := hn'
    omega
  have hspoil := good_ge_card_sub' allMult (notSmooth y a b k) hsep
  rw [← hgood_eq] at hspoil
  have hcard_allMult : allMult.card = (U - 1) / 3 + 1 - (L + 2) / 3 := by
    rw [hallMult_def, card_mult3_Icc]
  have hLreal : (L : ℝ) ≤ a * k + 1 := by
    rw [hL]; exact le_of_lt (Nat.ceil_lt_add_one (mul_nonneg ha (Nat.cast_nonneg k)))
  have hUreal : (U : ℝ) ≥ b * k - 1 := by
    rw [hU]
    have := Nat.lt_floor_add_one (b * (k:ℝ))
    linarith
  have nat_div_cast_ge : ∀ n d : ℕ, 0 < d → (n:ℝ)/d - 1 ≤ ((n/d:ℕ):ℝ) := by
    intro n d hd
    have hlt : n < d * (n / d) + d := by
      have hmod : n % d < d := Nat.mod_lt n hd
      have heq : d * (n / d) + n % d = n := Nat.div_add_mod n d
      omega
    have h2 : (n:ℝ) < ((n / d:ℕ):ℝ) * d + d := by
      have : (n:ℝ) < (d:ℝ) * ((n/d:ℕ):ℝ) + d := by exact_mod_cast hlt
      linarith
    have h3 : (n:ℝ)/d < ((n/d:ℕ):ℝ) + 1 := by
      rw [div_lt_iff₀ (by exact_mod_cast hd)]
      linarith
    linarith
  have nat_sub_cast_ge : ∀ x y : ℕ, (x:ℝ) - y ≤ ((x - y : ℕ):ℝ) := by
    intro x y
    by_cases h : y ≤ x
    · rw [Nat.cast_sub h]
    · push_neg at h
      rw [Nat.sub_eq_zero_of_le h.le]
      have : (x:ℝ) ≤ y := by exact_mod_cast h.le
      push_cast
      linarith
  have hX : ((U:ℝ) - 1) / 3 ≤ (((U - 1) / 3 : ℕ) : ℝ) + 1 := by
    have h1 : (U:ℝ) - 1 = ((U - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hU1]; push_cast; ring
    rw [h1]
    have h2 := nat_div_cast_ge (U - 1) 3 (by norm_num)
    linarith
  have hY : (((L + 2) / 3 : ℕ) : ℝ) ≤ ((L:ℝ) + 2) / 3 := by
    calc (((L + 2) / 3 : ℕ) : ℝ) ≤ ((L + 2 : ℕ):ℝ) / 3 := Nat.cast_div_le
      _ = ((L:ℝ) + 2) / 3 := by push_cast; ring
  have hallMult_real : ((U:ℝ) - L - 3) / 3 ≤ (allMult.card : ℝ) := by
    rw [hcard_allMult]
    have h1 := nat_sub_cast_ge ((U - 1) / 3 + 1) ((L + 2) / 3)
    have h2 : (((U - 1) / 3 + 1 : ℕ) : ℝ) = (((U - 1) / 3 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2] at h1
    linarith
  have hgood_real : (allMult.card : ℝ) - (notSmooth y a b k).card ≤ (gridGood y L U).card := by
    have h1 := nat_sub_cast_ge allMult.card (notSmooth y a b k).card
    have h2 : ((allMult.card - (notSmooth y a b k).card : ℕ) : ℝ) ≤ ((gridGood y L U).card : ℝ) := by
      exact_mod_cast hspoil
    linarith
  linarith [hallMult_real, hgood_real, hcard, hLreal, hUreal]

/-! ## Mass of a band of grid pairs -/

/-- If `G`'s elements are confined to a dyadic band `[t, 2t]`, its total pair-mass is at least
`G.card * 2/(2t+1)`. -/
lemma mass_ge_of_band (G : Finset ℕ) (t : ℚ) (ht : 0 < t)
    (hlo : ∀ a ∈ G, t ≤ (a:ℚ)) (hhi : ∀ a ∈ G, (a:ℚ) ≤ 2*t) :
    (G.card : ℚ) * (2 / (2*t+1)) ≤ ∑ a ∈ G, w a := by
  have h := Finset.card_nsmul_le_sum G w (2 / (2*t+1)) ?_
  · rwa [nsmul_eq_mul] at h
  · intro a ha
    have hage : t ≤ (a:ℚ) := hlo a ha
    have hale : (a:ℚ) ≤ 2*t := hhi a ha
    have ha0 : (0:ℚ) < a := by linarith
    have ha0' : 0 < a := by exact_mod_cast ha0
    have h1 := w_ge ha0'
    have hxpos : (0:ℚ) < a + 1 := by linarith
    have hxle : (a:ℚ) + 1 ≤ 2*t+1 := by linarith
    have h2 : (1:ℚ)/(2*t+1) ≤ 1/((a:ℚ)+1) := one_div_le_one_div_of_le hxpos hxle
    have h3 : (2:ℚ)/(2*t+1) ≤ 2/((a:ℚ)+1) := by
      have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℚ) ≤ 2)
      rwa [mul_one_div, mul_one_div] at this
    linarith

/-! ## The density constant `γ = 1/3 - log(5/4)` -/

/-- `γ = 1/3 - log(5/4)`, the density constant from Lemma 4 / (6.1) of the paper. -/
noncomputable def gam : ℝ := 1/3 - Real.log (5/4)

lemma log54_lt : Real.log (5/4 : ℝ) < 2235/10000 := by
  have h5 := Real.log_five_lt_d9
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := Real.log_four_eq
  have heq : Real.log (5/4 : ℝ) = Real.log 5 - Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  rw [heq, h4]
  nlinarith [h5, h2]

/-- `γ > 0.109`, giving `(6.2)`: `10γ > 1` and `16γ > 1`. -/
lemma gam_gt : (109/1000 : ℝ) < gam := by
  unfold gam; linarith [log54_lt]

/-! ## `Q k` tracks `k^(4/5)` -/

lemma Q_upper (k : ℕ) (η : ℝ) (hη : 0 ≤ η) (hk : 1 ≤ k) :
    (Q k : ℝ) ≤ (k:ℝ) ^ ((4:ℝ)/5 + η) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h1 : (Q k : ℝ) ≤ (k:ℝ) ^ ((4:ℝ)/5) := Nat.floor_le (by positivity)
  have h2 : (k:ℝ) ^ ((4:ℝ)/5) ≤ (k:ℝ) ^ ((4:ℝ)/5 + η) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  linarith

lemma Q_lower (η : ℝ) (hη : 0 < η) :
    ∃ X : ℝ, ∀ k : ℕ, X ≤ (k:ℝ) → (k:ℝ) ^ ((4:ℝ)/5 - η) ≤ (Q k : ℝ) := by
  use max 3 (2 ^ (1/η))
  intro k hk
  have hk3 : (3:ℝ) ≤ (k:ℝ) := le_trans (le_max_left _ _) hk
  have hk2η : (2:ℝ) ^ (1/η) ≤ (k:ℝ) := le_trans (le_max_right _ _) hk
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by linarith
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have key : (k:ℝ) ^ ((4:ℝ)/5 - η) + 1 ≤ (k:ℝ) ^ ((4:ℝ)/5) := by
    by_cases hη45 : η ≤ (4:ℝ)/5
    · have hkη : (2:ℝ) ≤ (k:ℝ) ^ η := by
        have step : ((2:ℝ) ^ (1/η)) ^ η ≤ (k:ℝ) ^ η :=
          Real.rpow_le_rpow (by positivity) hk2η hη.le
        have heq : ((2:ℝ) ^ (1/η)) ^ η = 2 := by
          rw [← Real.rpow_mul (by norm_num)]
          rw [one_div, inv_mul_cancel₀ (ne_of_gt hη)]
          simp
        rwa [heq] at step
      have h1 : (1:ℝ) ≤ (k:ℝ) ^ ((4:ℝ)/5 - η) := Real.one_le_rpow hk1 (by linarith)
      have hsplit : (k:ℝ) ^ ((4:ℝ)/5) = (k:ℝ) ^ ((4:ℝ)/5 - η) * (k:ℝ) ^ η := by
        rw [← Real.rpow_add hkpos]; ring_nf
      rw [hsplit]
      nlinarith
    · push_neg at hη45
      have h1 : (k:ℝ) ^ ((4:ℝ)/5 - η) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith)
      have h2 : (2:ℝ) ≤ (k:ℝ) ^ ((4:ℝ)/5) := by
        have hmono : (3:ℝ) ^ ((4:ℝ)/5) ≤ (k:ℝ) ^ ((4:ℝ)/5) :=
          Real.rpow_le_rpow (by norm_num) hk3 (by norm_num)
        have h3 : (2:ℝ) ≤ (3:ℝ) ^ ((4:ℝ)/5) := by
          rw [← Real.rpow_le_rpow_iff (by norm_num : (0:ℝ) ≤ 2)
            (by positivity : (0:ℝ) ≤ (3:ℝ) ^ ((4:ℝ)/5)) (show (0:ℝ) < 5 by norm_num)]
          have heq : ((3:ℝ) ^ ((4:ℝ)/5)) ^ (5:ℝ) = 3 ^ (4:ℝ) := by
            rw [← Real.rpow_mul (by norm_num)]; norm_num
          rw [heq, show (2:ℝ)^(5:ℝ) = 32 by
              rw [show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num,
            show (3:ℝ)^(4:ℝ) = 81 by
              rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num]
          norm_num
        linarith
      linarith
  have hfloor : (k:ℝ) ^ ((4:ℝ)/5) < (Q k : ℝ) + 1 := Nat.lt_floor_add_one _
  linarith

/-! ## Band and far-band supply -/

/-- For a rational band-scale `a>0` and slack `ε∈(0,γ)`, for large enough `k`, there is a finset
of `Q k`-powersmooth grid pair starts confined to `[a*k, 2*a*k]` whose total reciprocal mass is
at least `γ - ε`. -/
lemma bandData (a : ℚ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) (hεγ : ε < gam) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ G : Finset ℕ,
        (∀ n ∈ G, 3 ∣ n ∧ Powersmooth (Q k) n ∧ Powersmooth (Q k) (n + 1) ∧
          a * (k:ℚ) ≤ (n:ℚ) ∧ (n:ℚ) + 1 ≤ 2 * (a * (k:ℚ))) ∧
        (gam - ε ≤ ((∑ n ∈ G, w n : ℚ) : ℝ)) := by
  classical
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  set ε1 : ℝ := ε/2 with hε1_def
  have hε1_pos : 0 < ε1 := by positivity
  have hab : (a:ℝ) < 2*(a:ℝ) := by linarith
  obtain ⟨η, hη_pos, X₀, hX₀⟩ :=
    lemma4 (4/5) (a:ℝ) (2*(a:ℝ)) (by norm_num) (by norm_num) haR hab (ε1 * (a:ℝ)) (by positivity)
  obtain ⟨XQ, hXQ⟩ := Q_lower η hη_pos
  set D : ℝ := 7/3 with hD_def
  set C : ℝ := gam + 2*D with hC_def
  set kthresh : ℝ := C/ε1 with hkthresh_def
  set k₀ : ℕ := max (max ⌈X₀⌉₊ ⌈XQ⌉₊) (max ⌈kthresh / (a:ℝ)⌉₊ ⌈1/(a:ℝ)⌉₊) + 1 with hk₀_def
  refine ⟨k₀, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by
    have : 1 ≤ k₀ := by omega
    omega
  have hkR1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  have hkX₀ : X₀ ≤ (k:ℝ) := by
    have h1 : ⌈X₀⌉₊ ≤ k₀ := by omega
    have h2 : (⌈X₀⌉₊ : ℝ) ≤ (k:ℝ) := by
      have := h1.trans hk
      exact_mod_cast this
    exact le_trans (Nat.le_ceil X₀) h2
  have hkXQ : XQ ≤ (k:ℝ) := by
    have h1 : ⌈XQ⌉₊ ≤ k₀ := by omega
    have h2 : (⌈XQ⌉₊ : ℝ) ≤ (k:ℝ) := by
      have := h1.trans hk
      exact_mod_cast this
    exact le_trans (Nat.le_ceil XQ) h2
  have hkthresh_le : kthresh ≤ (a:ℝ) * (k:ℝ) := by
    have h1 : ⌈kthresh / (a:ℝ)⌉₊ ≤ k₀ := by omega
    have h2 : (⌈kthresh / (a:ℝ)⌉₊ : ℝ) ≤ (k:ℝ) := by
      have := h1.trans hk
      exact_mod_cast this
    have h3 : kthresh / (a:ℝ) ≤ (k:ℝ) := le_trans (Nat.le_ceil _) h2
    rw [div_le_iff₀ haR] at h3
    linarith
  have hk_a_ge1 : 1/(a:ℝ) ≤ (k:ℝ) := by
    have h1 : ⌈1/(a:ℝ)⌉₊ ≤ k₀ := by omega
    have h2 : (⌈1/(a:ℝ)⌉₊ : ℝ) ≤ (k:ℝ) := by
      have := h1.trans hk
      exact_mod_cast this
    exact le_trans (Nat.le_ceil _) h2
  have hak_ge1 : (1:ℝ) ≤ (a:ℝ)*(k:ℝ) := by
    rw [div_le_iff₀ haR] at hk_a_ge1
    linarith
  have hQ_lo : (k:ℝ) ^ ((4:ℝ)/5 - η) ≤ (Q k : ℝ) := hXQ k hkXQ
  have hQ_hi : (Q k : ℝ) ≤ (k:ℝ) ^ ((4:ℝ)/5 + η) := Q_upper k η hη_pos.le hk1
  have hnotsmooth := hX₀ (k:ℝ) hkX₀ (Q k) hQ_lo hQ_hi
  set E : ℝ := ((2*(a:ℝ) - (a:ℝ)) * Real.log (1/(4/5)) + ε1 * (a:ℝ)) * (k:ℝ) with hE_def
  set L : ℕ := ⌈(a:ℝ) * (k:ℝ)⌉₊ with hL_def
  set U : ℕ := ⌊2*(a:ℝ) * (k:ℝ)⌋₊ with hU_def
  have hU1 : 1 ≤ U := by
    rw [hU_def, Nat.one_le_floor_iff]
    linarith
  have hcardE : ((notSmooth (Q k) (a:ℝ) (2*(a:ℝ)) k).card : ℝ) ≤ E := hnotsmooth
  have hcount := gridGood_card_ge (Q k) (a:ℝ) (2*(a:ℝ)) k E L U haR.le rfl rfl hU1 hcardE
  set G := gridGood (Q k) L U with hG_def
  have hLreal : (L : ℝ) ≤ (a:ℝ) * k + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (mul_nonneg haR.le (Nat.cast_nonneg k)))
  have hUreal : (U : ℝ) ≥ 2*(a:ℝ) * k - 1 := by
    have := Nat.lt_floor_add_one (2*(a:ℝ) * (k:ℝ))
    linarith
  have hE_eq : E = (a:ℝ) * (Real.log (5/4) + ε1) * (k:ℝ) := by
    rw [hE_def]
    have h1 : (1:ℝ)/(4/5) = 5/4 := by norm_num
    rw [h1]; ring
  have hcountR : (a:ℝ)*(k:ℝ)*(gam - ε1) - D ≤ (G.card : ℝ) := by
    have hstepA : ((2*(a:ℝ)*(k:ℝ)-1)-((a:ℝ)*(k:ℝ)+1)-5)/3 - E ≤ ((U:ℝ) - L - 5)/3 - E := by
      linarith [hLreal, hUreal]
    have hstepB : ((2*(a:ℝ)*(k:ℝ)-1)-((a:ℝ)*(k:ℝ)+1)-5)/3 - E = (a:ℝ)*(k:ℝ)*(gam-ε1) - D := by
      rw [hE_eq, hD_def]; unfold gam; ring
    have hfinal := hstepA.trans hcount
    rw [hstepB] at hfinal
    exact hfinal
  refine ⟨G, ?_, ?_⟩
  · intro n hn
    simp only [hG_def, gridGood, mem_filter, mem_Icc] at hn
    obtain ⟨⟨hLn, hnU⟩, h3, hn1U, hp, hp1⟩ := hn
    refine ⟨h3, hp, hp1, ?_, ?_⟩
    · have h1 : (a:ℝ) * (k:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
      have h2 : (L:ℝ) ≤ (n:ℝ) := by exact_mod_cast hLn
      have h3' : (a:ℝ)*(k:ℝ) ≤ (n:ℝ) := le_trans h1 h2
      exact_mod_cast h3'
    · have h1 : (U:ℝ) ≤ 2*((a:ℝ)*(k:ℝ)) := by rw [← mul_assoc]; exact Nat.floor_le (by positivity)
      have h2 : (n:ℝ) + 1 ≤ (U:ℝ) := by exact_mod_cast hn1U
      have h3' : (n:ℝ) + 1 ≤ 2*((a:ℝ)*(k:ℝ)) := le_trans h2 h1
      exact_mod_cast h3'
  · have ht : (0:ℚ) < a*(k:ℚ) := by positivity
    have hlo : ∀ n ∈ G, a*(k:ℚ) ≤ (n:ℚ) := by
      intro n hn
      simp only [hG_def, gridGood, mem_filter, mem_Icc] at hn
      have h1 : (a:ℝ) * (k:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
      have h2 : (L:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1.1
      have h3' : (a:ℝ)*(k:ℝ) ≤ (n:ℝ) := le_trans h1 h2
      exact_mod_cast h3'
    have hhi : ∀ n ∈ G, (n:ℚ) ≤ 2*(a*(k:ℚ)) := by
      intro n hn
      simp only [hG_def, gridGood, mem_filter, mem_Icc] at hn
      have h1 : (U:ℝ) ≤ 2*((a:ℝ)*(k:ℝ)) := by rw [← mul_assoc]; exact Nat.floor_le (by positivity)
      have h2 : (n:ℝ) ≤ (U:ℝ) := by exact_mod_cast hn.1.2
      have h3' : (n:ℝ) ≤ 2*((a:ℝ)*(k:ℝ)) := le_trans h2 h1
      exact_mod_cast h3'
    have hmass := mass_ge_of_band G (a*(k:ℚ)) ht hlo hhi
    have hmassR : ((G.card:ℚ):ℝ) * (2/(2*((a:ℝ)*(k:ℝ))+1)) ≤ (((∑ n ∈ G, w n : ℚ) : ℝ)) := by
      have hcast : ((G.card:ℚ):ℝ) * (2/(2*((a*(k:ℚ):ℚ):ℝ)+1)) ≤ (((∑ n ∈ G, w n : ℚ):ℝ)) := by
        exact_mod_cast hmass
      have heqcast : ((a*(k:ℚ):ℚ):ℝ) = (a:ℝ)*(k:ℝ) := by push_cast; ring
      rw [heqcast] at hcast
      exact hcast
    have hGcardR : (G.card:ℝ) = ((G.card:ℚ):ℝ) := by push_cast; ring
    rw [← hGcardR] at hmassR
    set x := (a:ℝ)*(k:ℝ) with hx_def
    have hxpos : 0 < x := by rw [hx_def]; positivity
    have hfinal : (x*(gam-ε1) - D) * (2/(2*x+1)) ≥ gam - ε := by
      rw [ge_iff_le, show (x*(gam-ε1) - D) * (2/(2*x+1)) = (2*(x*(gam-ε1)-D))/(2*x+1) by ring,
        le_div_iff₀ (by linarith : (0:ℝ) < 2*x+1)]
      have hxk : kthresh ≤ x := hkthresh_le
      rw [hkthresh_def] at hxk
      rw [div_le_iff₀ hε1_pos] at hxk
      have : C ≤ ε1 * (2*x+1) := by nlinarith [hxk, hε1_pos, hxpos]
      nlinarith [this]
    have hchain : gam - ε ≤ (G.card:ℝ) * (2/(2*x+1)) := by
      have h1 := hcountR
      have h2 : (x*(gam-ε1) - D) ≤ (G.card:ℝ) := by rw [hx_def]; linarith [h1]
      have h3 : (x*(gam-ε1) - D) * (2/(2*x+1)) ≤ (G.card:ℝ) * (2/(2*x+1)) := by
        apply mul_le_mul_of_nonneg_right h2
        positivity
      linarith [hfinal, h3]
    linarith [hchain, hmassR]

/-- Far-band supply: for large `k`, the fully-powersmooth grid pairs with starts in `[4k, 20k]`
number at least `k` (hence at least any `M ≤ k`). -/
lemma farData :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ G : Finset ℕ, (k:ℝ) ≤ (G.card : ℝ) ∧
        (∀ n ∈ G, 3 ∣ n ∧ Powersmooth (Q k) n ∧ Powersmooth (Q k) (n + 1) ∧
          (4:ℚ) * (k:ℚ) ≤ (n:ℚ) ∧ (n:ℚ) + 1 ≤ 20 * (k:ℚ)) := by
  classical
  obtain ⟨η, hη_pos, X₀, hX₀⟩ :=
    lemma4 (4/5) 4 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (1/10) (by norm_num)
  obtain ⟨XQ, hXQ⟩ := Q_lower η hη_pos
  set k₀ : ℕ := max (max ⌈X₀⌉₊ ⌈XQ⌉₊) 10 + 1 with hk₀_def
  refine ⟨k₀, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have hk10 : 10 ≤ k := by omega
  have hkR1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  have hkX₀ : X₀ ≤ (k:ℝ) := by
    have h1 : ⌈X₀⌉₊ ≤ k₀ := by omega
    have h2 : (⌈X₀⌉₊ : ℝ) ≤ (k:ℝ) := by exact_mod_cast h1.trans hk
    exact le_trans (Nat.le_ceil X₀) h2
  have hkXQ : XQ ≤ (k:ℝ) := by
    have h1 : ⌈XQ⌉₊ ≤ k₀ := by omega
    have h2 : (⌈XQ⌉₊ : ℝ) ≤ (k:ℝ) := by exact_mod_cast h1.trans hk
    exact le_trans (Nat.le_ceil XQ) h2
  have hQ_lo : (k:ℝ) ^ ((4:ℝ)/5 - η) ≤ (Q k : ℝ) := hXQ k hkXQ
  have hQ_hi : (Q k : ℝ) ≤ (k:ℝ) ^ ((4:ℝ)/5 + η) := Q_upper k η hη_pos.le hk1
  have hnotsmooth := hX₀ (k:ℝ) hkX₀ (Q k) hQ_lo hQ_hi
  set E : ℝ := ((20 - 4:ℝ) * Real.log (1/(4/5)) + 1/10) * (k:ℝ) with hE_def
  set L : ℕ := ⌈(4:ℝ) * (k:ℝ)⌉₊ with hL_def
  set U : ℕ := ⌊(20:ℝ) * (k:ℝ)⌋₊ with hU_def
  have hU1 : 1 ≤ U := by
    rw [hU_def, Nat.one_le_floor_iff]; linarith
  have hcardE : ((notSmooth (Q k) (4:ℝ) 20 k).card : ℝ) ≤ E := hnotsmooth
  have hcount := gridGood_card_ge (Q k) 4 20 k E L U (by norm_num) rfl rfl hU1 hcardE
  set G := gridGood (Q k) L U with hG_def
  have hLreal : (L : ℝ) ≤ 4 * (k:ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hUreal : (U : ℝ) ≥ 20 * (k:ℝ) - 1 := by
    have := Nat.lt_floor_add_one ((20:ℝ) * (k:ℝ))
    linarith
  have hE_eq : E = 16 * Real.log (5/4) * (k:ℝ) + (k:ℝ)/10 := by
    rw [hE_def]
    have h1 : (1:ℝ)/(4/5) = 5/4 := by norm_num
    rw [h1]; ring
  have hcountR : (k:ℝ) ≤ (G.card : ℝ) := by
    have hstepA : ((20*(k:ℝ)-1)-(4*(k:ℝ)+1)-5)/3 - E ≤ ((U:ℝ) - L - 5)/3 - E := by
      linarith [hLreal, hUreal]
    have hstepB : ((20*(k:ℝ)-1)-(4*(k:ℝ)+1)-5)/3 - E = 16*(k:ℝ)*gam - (7/3) - (k:ℝ)/10 := by
      rw [hE_eq]; unfold gam; ring
    have hkey := hstepA.trans hcount
    rw [hstepB] at hkey
    have hkpos : (0:ℝ) < (k:ℝ) := by linarith
    have hgamk : (k:ℝ) * (109/1000) < (k:ℝ) * gam := by
      apply mul_lt_mul_of_pos_left gam_gt hkpos
    have hk10R : (10:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk10
    nlinarith [hkey, hgamk, hk10R]
  refine ⟨G, hcountR, ?_⟩
  intro n hn
  simp only [hG_def, gridGood, mem_filter, mem_Icc] at hn
  obtain ⟨⟨hLn, hnU⟩, h3, hn1U, hp, hp1⟩ := hn
  refine ⟨h3, hp, hp1, ?_, ?_⟩
  · have h1 : (4:ℝ) * (k:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
    have h2 : (L:ℝ) ≤ (n:ℝ) := by exact_mod_cast hLn
    have h3' : (4:ℝ)*(k:ℝ) ≤ (n:ℝ) := le_trans h1 h2
    exact_mod_cast h3'
  · have h1 : (U:ℝ) ≤ 20*(k:ℝ) := Nat.floor_le (by positivity)
    have h2 : (n:ℝ) + 1 ≤ (U:ℝ) := by exact_mod_cast hn1U
    have h3' : (n:ℝ) + 1 ≤ 20*(k:ℝ) := le_trans h2 h1
    exact_mod_cast h3'

/-- Two distinct multiples of `3` are always separated by at least one unused integer. -/
lemma sep_of_mult3 {a a' : ℕ} (h3 : 3 ∣ a) (h3' : 3 ∣ a') (hne : a ≠ a') :
    a + 1 + 1 < a' ∨ a' + 1 + 1 < a := by omega

/-- Combining step for the ten dyadic near-bands: if `A`'s elements are all `≥ a*k` (`a` being
the smallest band-scale used so far) and `G`'s elements lie in `[a'*k, 2*a'*k] = [a'*k, a*k]`
(`a = 2*a'`, the next smaller band), then `A` and `G` are disjoint and `A ∪ G`'s elements are
all `≥ a'*k`. -/
lemma bandStep (k : ℕ) (a a' : ℚ) (ha' : 0 < a') (hrel : a = 2*a')
    (A G : Finset ℕ)
    (hlbA : ∀ n ∈ A, a * (k:ℚ) ≤ (n:ℚ))
    (hG : ∀ n ∈ G, a' * (k:ℚ) ≤ (n:ℚ) ∧ (n:ℚ) + 1 ≤ 2 * (a' * (k:ℚ))) :
    Disjoint A G ∧ ∀ n ∈ A ∪ G, a' * (k:ℚ) ≤ (n:ℚ) := by
  constructor
  · rw [Finset.disjoint_left]
    intro n hnA hnG
    have h1 := hlbA n hnA
    have h2 := (hG n hnG).2
    rw [hrel] at h1
    linarith [h1, h2]
  · intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · have h1 := hlbA n h
      rw [hrel] at h1
      nlinarith [h1, ha']
    · exact (hG n h).1

set_option maxHeartbeats 4000000 in
/-- **Section 6** of the paper, packaged. -/
theorem mainPairs :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ M : ℕ, k / 2 ≤ M → M ≤ k → ∀ τ : ℚ, 1 / 2 < τ → τ < 1 →
      ∃ P : Finset Iv, P.card = M ∧ (∀ I ∈ P, IsMainPair k I) ∧
        (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
        τ - 2048 / k ≤ ∑ I ∈ P, I.mass ∧ ∑ I ∈ P, I.mass ≤ τ := by
  classical
  have hεpos : (0:ℝ) < 1/200 := by norm_num
  have hεγ : (1/200:ℝ) < gam := by linarith [gam_gt]
  obtain ⟨k1, hk1⟩ := bandData (1/2) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k2, hk2⟩ := bandData (1/4) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k3, hk3⟩ := bandData (1/8) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k4, hk4⟩ := bandData (1/16) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k5, hk5⟩ := bandData (1/32) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k6, hk6⟩ := bandData (1/64) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k7, hk7⟩ := bandData (1/128) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k8, hk8⟩ := bandData (1/256) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k9, hk9⟩ := bandData (1/512) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨k10, hk10⟩ := bandData (1/1024) (by norm_num) (1/200) hεpos hεγ
  obtain ⟨kf, hkf⟩ := farData
  refine ⟨max (max (max (max k1 k2) (max k3 k4)) (max (max k5 k6) (max k7 k8)))
      (max (max k9 k10) kf) + 2000, fun k hk M hM1 hM2 τ hτ1 hτ2 => ?_⟩
  have hk1' : k1 ≤ k := by omega
  have hk2' : k2 ≤ k := by omega
  have hk3' : k3 ≤ k := by omega
  have hk4' : k4 ≤ k := by omega
  have hk5' : k5 ≤ k := by omega
  have hk6' : k6 ≤ k := by omega
  have hk7' : k7 ≤ k := by omega
  have hk8' : k8 ≤ k := by omega
  have hk9' : k9 ≤ k := by omega
  have hk10' : k10 ≤ k := by omega
  have hkf' : kf ≤ k := by omega
  have hk2000 : 2000 ≤ k := by omega
  obtain ⟨G1, hG1m, hG1s⟩ := hk1 k hk1'
  obtain ⟨G2, hG2m, hG2s⟩ := hk2 k hk2'
  obtain ⟨G3, hG3m, hG3s⟩ := hk3 k hk3'
  obtain ⟨G4, hG4m, hG4s⟩ := hk4 k hk4'
  obtain ⟨G5, hG5m, hG5s⟩ := hk5 k hk5'
  obtain ⟨G6, hG6m, hG6s⟩ := hk6 k hk6'
  obtain ⟨G7, hG7m, hG7s⟩ := hk7 k hk7'
  obtain ⟨G8, hG8m, hG8s⟩ := hk8 k hk8'
  obtain ⟨G9, hG9m, hG9s⟩ := hk9 k hk9'
  obtain ⟨G10, hG10m, hG10s⟩ := hk10 k hk10'
  obtain ⟨Gf, hGfc, hGfm⟩ := hkf k hkf'
  -- incremental disjoint union of the ten near bands
  have hlb1 : ∀ n ∈ G1, (1/2:ℚ) * (k:ℚ) ≤ (n:ℚ) := fun n hn => (hG1m n hn).2.2.2.1
  have hstep2 := bandStep k (1/2) (1/4) (by norm_num) (by norm_num) G1 G2 hlb1
    (fun n hn => ⟨(hG2m n hn).2.2.2.1, (hG2m n hn).2.2.2.2⟩)
  have hstep3 := bandStep k (1/4) (1/8) (by norm_num) (by norm_num) (G1 ∪ G2) G3 hstep2.2
    (fun n hn => ⟨(hG3m n hn).2.2.2.1, (hG3m n hn).2.2.2.2⟩)
  have hstep4 := bandStep k (1/8) (1/16) (by norm_num) (by norm_num) (G1 ∪ G2 ∪ G3) G4 hstep3.2
    (fun n hn => ⟨(hG4m n hn).2.2.2.1, (hG4m n hn).2.2.2.2⟩)
  have hstep5 := bandStep k (1/16) (1/32) (by norm_num) (by norm_num) (G1 ∪ G2 ∪ G3 ∪ G4) G5 hstep4.2
    (fun n hn => ⟨(hG5m n hn).2.2.2.1, (hG5m n hn).2.2.2.2⟩)
  have hstep6 := bandStep k (1/32) (1/64) (by norm_num) (by norm_num) (G1 ∪ G2 ∪ G3 ∪ G4 ∪ G5) G6 hstep5.2
    (fun n hn => ⟨(hG6m n hn).2.2.2.1, (hG6m n hn).2.2.2.2⟩)
  have hstep7 := bandStep k (1/64) (1/128) (by norm_num) (by norm_num) (G1 ∪ G2 ∪ G3 ∪ G4 ∪ G5 ∪ G6) G7 hstep6.2
    (fun n hn => ⟨(hG7m n hn).2.2.2.1, (hG7m n hn).2.2.2.2⟩)
  have hstep8 := bandStep k (1/128) (1/256) (by norm_num) (by norm_num) (G1 ∪ G2 ∪ G3 ∪ G4 ∪ G5 ∪ G6 ∪ G7) G8 hstep7.2
    (fun n hn => ⟨(hG8m n hn).2.2.2.1, (hG8m n hn).2.2.2.2⟩)
  have hstep9 := bandStep k (1/256) (1/512) (by norm_num) (by norm_num) (G1 ∪ G2 ∪ G3 ∪ G4 ∪ G5 ∪ G6 ∪ G7 ∪ G8) G9 hstep8.2
    (fun n hn => ⟨(hG9m n hn).2.2.2.1, (hG9m n hn).2.2.2.2⟩)
  have hstep10 := bandStep k (1/512) (1/1024) (by norm_num) (by norm_num)
    (G1 ∪ G2 ∪ G3 ∪ G4 ∪ G5 ∪ G6 ∪ G7 ∪ G8 ∪ G9) G10 hstep9.2
    (fun n hn => ⟨(hG10m n hn).2.2.2.1, (hG10m n hn).2.2.2.2⟩)
  set A : Finset ℕ := G1 ∪ G2 ∪ G3 ∪ G4 ∪ G5 ∪ G6 ∪ G7 ∪ G8 ∪ G9 ∪ G10 with hA_def
  have hAlb : ∀ n ∈ A, (1/1024:ℚ) * (k:ℚ) ≤ (n:ℚ) := hstep10.2
  -- disjoint-union sum decomposition
  have hAsum : ∑ n ∈ A, w n =
      ∑ n ∈ G1, w n + ∑ n ∈ G2, w n + ∑ n ∈ G3, w n + ∑ n ∈ G4, w n + ∑ n ∈ G5, w n +
      ∑ n ∈ G6, w n + ∑ n ∈ G7, w n + ∑ n ∈ G8, w n + ∑ n ∈ G9, w n + ∑ n ∈ G10, w n := by
    rw [hA_def]
    rw [Finset.sum_union hstep10.1, Finset.sum_union hstep9.1, Finset.sum_union hstep8.1,
      Finset.sum_union hstep7.1, Finset.sum_union hstep6.1, Finset.sum_union hstep5.1,
      Finset.sum_union hstep4.1, Finset.sum_union hstep3.1, Finset.sum_union hstep2.1]
  have hAmass_gt1 : (1:ℝ) < ((∑ n ∈ A, w n : ℚ) : ℝ) := by
    have hcast : ((∑ n ∈ A, w n : ℚ) : ℝ) =
        ((∑ n ∈ G1, w n : ℚ):ℝ) + ((∑ n ∈ G2, w n : ℚ):ℝ) + ((∑ n ∈ G3, w n : ℚ):ℝ) +
        ((∑ n ∈ G4, w n : ℚ):ℝ) + ((∑ n ∈ G5, w n : ℚ):ℝ) + ((∑ n ∈ G6, w n : ℚ):ℝ) +
        ((∑ n ∈ G7, w n : ℚ):ℝ) + ((∑ n ∈ G8, w n : ℚ):ℝ) + ((∑ n ∈ G9, w n : ℚ):ℝ) +
        ((∑ n ∈ G10, w n : ℚ):ℝ) := by
      rw [hAsum]; push_cast; ring
    rw [hcast]
    have h1 := gam_gt
    linarith [hG1s, hG2s, hG3s, hG4s, hG5s, hG6s, hG7s, hG8s, hG9s, hG10s]
  have hAcard_bound : A.card < M := by
    have hsub : A ⊆ (Icc 0 (k-1)).filter (fun n => 3 ∣ n) := by
      intro n hn
      simp only [hA_def, Finset.mem_union] at hn
      simp only [mem_filter, mem_Icc]
      rcases hn with ((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG1m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG1m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG2m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG2m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG3m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG3m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG4m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG4m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG5m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG5m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG6m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG6m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG7m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG7m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG8m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG8m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG9m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG9m n h).1⟩
      · exact ⟨⟨Nat.zero_le _, by
          have hb := (hG10m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
          have : n < k := by exact_mod_cast hb2
          omega⟩, (hG10m n h).1⟩
    have hcard_le : A.card ≤ (k-1) / 3 + 1 - (0 + 2) / 3 := by
      have := Finset.card_le_card hsub
      rwa [card_mult3_Icc] at this
    omega
  have hAupper : ∀ n ∈ A, n < k := by
    intro n hn
    simp only [hA_def, Finset.mem_union] at hn
    rcases hn with ((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h
    · have hb := (hG1m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG2m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG3m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG4m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG5m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG6m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG7m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG8m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG9m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
    · have hb := (hG10m n h).2.2.2.2; have hb2 : (n:ℚ) < (k:ℚ) := by linarith
      exact_mod_cast hb2
  have hAgrid : ∀ n ∈ A, 3 ∣ n ∧ Powersmooth (Q k) n ∧ Powersmooth (Q k) (n + 1) := by
    intro n hn
    simp only [hA_def, Finset.mem_union] at hn
    rcases hn with ((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h
    · exact ⟨(hG1m n h).1, (hG1m n h).2.1, (hG1m n h).2.2.1⟩
    · exact ⟨(hG2m n h).1, (hG2m n h).2.1, (hG2m n h).2.2.1⟩
    · exact ⟨(hG3m n h).1, (hG3m n h).2.1, (hG3m n h).2.2.1⟩
    · exact ⟨(hG4m n h).1, (hG4m n h).2.1, (hG4m n h).2.2.1⟩
    · exact ⟨(hG5m n h).1, (hG5m n h).2.1, (hG5m n h).2.2.1⟩
    · exact ⟨(hG6m n h).1, (hG6m n h).2.1, (hG6m n h).2.2.1⟩
    · exact ⟨(hG7m n h).1, (hG7m n h).2.1, (hG7m n h).2.2.1⟩
    · exact ⟨(hG8m n h).1, (hG8m n h).2.1, (hG8m n h).2.2.1⟩
    · exact ⟨(hG9m n h).1, (hG9m n h).2.1, (hG9m n h).2.2.1⟩
    · exact ⟨(hG10m n h).1, (hG10m n h).2.1, (hG10m n h).2.2.1⟩
  have hDisjAFar : Disjoint A Gf := by
    rw [Finset.disjoint_left]
    intro n hnA hnGf
    have h1 := hAupper n hnA
    have h2 := (hGfm n hnGf).2.2.2.1
    have h1' : (n:ℚ) < (k:ℚ) := by exact_mod_cast h1
    linarith
  have hFarCard : M ≤ Gf.card := by
    have h1 : (M:ℝ) ≤ (k:ℝ) := by exact_mod_cast hM2
    have h2 : (k:ℝ) ≤ (Gf.card:ℝ) := hGfc
    have : (M:ℝ) ≤ (Gf.card:ℝ) := le_trans h1 h2
    exact_mod_cast this
  have hkpos : (0:ℚ) < (k:ℚ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hfar_small : ∀ T ⊆ Gf, T.card = M → ∑ x ∈ T, w x ≤ τ := by
    intro T hTsub hTcard
    have hbound : ∀ n ∈ T, w n ≤ 1/(2*(k:ℚ)) := by
      intro n hn
      have hnGf := hTsub hn
      have h4k := (hGfm n hnGf).2.2.2.1
      have hn0 : 0 < n := by
        have : (0:ℚ) < (n:ℚ) := by linarith
        exact_mod_cast this
      have h1 := w_le hn0
      have h2 : (2:ℚ)/n ≤ 1/(2*(k:ℚ)) := by
        rw [div_le_div_iff₀ (by exact_mod_cast hn0) (by positivity)]
        nlinarith [h4k]
      linarith
    have hsum : ∑ n ∈ T, w n ≤ (T.card:ℚ) * (1/(2*(k:ℚ))) :=
      Finset.sum_le_card_nsmul T w (1/(2*(k:ℚ))) hbound |>.trans_eq (by rw [nsmul_eq_mul])
    rw [hTcard] at hsum
    have hMk : (M:ℚ) ≤ (k:ℚ) := by exact_mod_cast hM2
    have : (M:ℚ) * (1/(2*(k:ℚ))) ≤ (1:ℚ)/2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hMk]
    linarith [hsum, this, hτ1]
  have hbig : ∀ T ⊆ Gf, T.card = M - A.card → τ < ∑ x ∈ A, w x + ∑ x ∈ T, w x := by
    intro T hTsub hTcard
    have hTnonneg : 0 ≤ ∑ x ∈ T, w x := by
      apply Finset.sum_nonneg
      intro n hn
      have hnGf := hTsub hn
      have h4k := (hGfm n hnGf).2.2.2.1
      have hn0 : 0 < n := by
        have : (0:ℚ) < (n:ℚ) := by linarith
        exact_mod_cast this
      have := w_ge hn0
      have hpos : (0:ℚ) < (n:ℚ) + 1 := by positivity
      have : (0:ℚ) < 2/((n:ℚ)+1) := by positivity
      linarith
    have hA1 : (1:ℚ) < ∑ x ∈ A, w x := by exact_mod_cast hAmass_gt1
    linarith [hA1, hTnonneg, hτ2]
  have hswap : ∀ a ∈ A, ∀ b ∈ Gf, w a - w b ≤ 2048/(k:ℚ) := by
    intro a ha b hb
    have h1024 := hAlb a ha
    have ha0 : 0 < a := by
      have : (0:ℚ) < (a:ℚ) := by
        have : (0:ℚ) < (1/1024:ℚ) * (k:ℚ) := by positivity
        linarith
      exact_mod_cast this
    have hwa := w_le ha0
    have h2 : (2:ℚ)/a ≤ 2048/(k:ℚ) := by
      rw [div_le_div_iff₀ (by exact_mod_cast ha0) hkpos]
      nlinarith [h1024]
    have hb0 : 0 < b := by
      have hb4k := (hGfm b hb).2.2.2.1
      have : (0:ℚ) < (b:ℚ) := by linarith
      exact_mod_cast this
    have hwb : 0 < w b := by
      have hge := w_ge hb0
      have hpos2 : (0:ℚ) < 2/((b:ℚ)+1) := by positivity
      linarith
    linarith [hwa, h2, hwb]
  obtain ⟨S, hSsub, hScard, hSlow, hShigh⟩ :=
    exists_subset_card_mass A Gf w M τ (2048/(k:ℚ)) hDisjAFar hAcard_bound hFarCard
      hfar_small hbig hswap
  have hpairInj : Function.Injective Iv.pair := by
    intro a b hab
    have := congrArg Iv.lo hab
    simpa [Iv.pair] using this
  have hSmain : ∀ a ∈ S, IsMainPair k (Iv.pair a) := by
    intro a ha
    rcases Finset.mem_union.mp (hSsub ha) with haA | haGf
    · obtain ⟨h3, hp, hp1⟩ := hAgrid a haA
      have hlo := hAlb a haA
      have hup := hAupper a haA
      refine ⟨a, rfl, h3, hp, hp1, Or.inl ⟨?_, ?_⟩⟩
      · have hlo' : (1/1024 : ℝ) * (k:ℝ) ≤ (a:ℝ) := by
          have hc := (Rat.cast_le (K := ℝ)).mpr hlo
          push_cast at hc
          linarith
        linarith
      · have hup' : a + 1 ≤ k := by omega
        exact_mod_cast hup'
    · obtain ⟨h3, hp, hp1, hlo, hhi⟩ := hGfm a haGf
      refine ⟨a, rfl, h3, hp, hp1, Or.inr ⟨?_, ?_⟩⟩
      · exact_mod_cast hlo
      · exact_mod_cast hhi
  refine ⟨S.image Iv.pair, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective S hpairInj, hScard]
  · intro I hI
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hI
    exact hSmain a ha
  · intro I hI J hJ hIJ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hJ
    have hne : a ≠ a' := fun h => hIJ (by rw [h])
    have h3 : 3 ∣ a := by
      rcases Finset.mem_union.mp (hSsub ha) with haA | haGf
      · exact (hAgrid a haA).1
      · exact (hGfm a haGf).1
    have h3' : 3 ∣ a' := by
      rcases Finset.mem_union.mp (hSsub ha') with haA | haGf
      · exact (hAgrid a' haA).1
      · exact (hGfm a' haGf).1
    show a + 1 + 1 < a' ∨ a' + 1 + 1 < a
    exact sep_of_mult3 h3 h3' hne
  · have hmasseq : ∑ I ∈ S.image Iv.pair, I.mass = ∑ a ∈ S, w a := by
      rw [Finset.sum_image (fun a _ b _ h => hpairInj h)]
      exact Finset.sum_congr rfl (fun a _ => mass_pair a)
    rw [hmasseq]; exact hSlow
  · have hmasseq : ∑ I ∈ S.image Iv.pair, I.mass = ∑ a ∈ S, w a := by
      rw [Finset.sum_image (fun a _ b _ h => hpairInj h)]
      exact Finset.sum_congr rfl (fun a _ => mass_pair a)
    rw [hmasseq]; exact hShigh

end Erdos289
